import argparse
import json
import signal
import threading
import time
from collections import deque
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

import websocket

DEFAULT_URL = "ws://dev.spsejecna.net:20716/ws"
DEFAULT_NICK = "mara"

INITIAL_SEND_INTERVAL = 1.08  # Bezpečný rozestup mezi zprávami (s rezervou pro síť)
MIN_ACK_GAP = 1.05            # Minimální odstup od posledního potvrzení ze serveru
HEARTBEAT_INTERVAL = 7.0      # Aplikační ping (server odpojuje až po 10 s)
CONFIRM_TIMEOUT = 8.0         # Timeout pro potvrzení tahu serverem (s)
BACKOFF_DELAYS = [2, 4, 8, 16, 30]
MAX_RECONNECT_ATTEMPTS = 25

MAX_BANK_POCKET_SIZE = 25     # Větší prázdnou plochu raději zavřeme hned (ochrana proti spawnu)

Coord = Tuple[int, int]


@dataclass
class PendingMove:
    x: int
    y: int
    sent_at: float
    was_first_spawn: bool


@dataclass
class BotState:
    lock: threading.Lock = field(default_factory=threading.Lock)
    ws_open: bool = False
    need_join: bool = False
    confirmed_nick: Optional[str] = None
    has_state: bool = False

    width: int = 40
    height: int = 40
    cells: Dict[Coord, str] = field(default_factory=dict)
    online_players: Dict[str, bool] = field(default_factory=dict)

    round_num: Optional[int] = None
    round_state: str = "waiting"
    round_ends_at_ms: Optional[int] = None

    pending_move: Optional[PendingMove] = None
    last_sent_type: Optional[str] = None
    last_send_mono: float = 0.0
    last_ack_mono: float = 0.0
    last_ping_mono: float = 0.0
    backoff_until_mono: float = 0.0
    send_interval: float = INITIAL_SEND_INTERVAL

    # Aktuální stavební plán obvodu
    plan_perimeter: List[Coord] = field(default_factory=list)
    plan_start_owned: int = 0
    plan_active: bool = False
    last_bank_log_mono: float = 0.0

    # Řízení běhu a fatálních chyb
    fatal_error: Optional[str] = None
    force_reconnect: bool = False
    successful_handshake: bool = False


class ArenaClient:
    def __init__(self, url: str, nick: str):
        self.url = url
        self.requested_nick = nick
        self.state = BotState()
        self.stop_event = threading.Event()
        self.ws: Optional[websocket.WebSocketApp] = None

    def log(self, tag: str, message: str) -> None:
        ts = time.strftime("%H:%M:%S")
        print(f"[{ts}] [{tag}] {message}", flush=True)

    # --- POMOCNÉ FUNKCE NAD MAPOU ---

    def _my_cells_unlocked(self) -> Set[Coord]:
        nick = self.state.confirmed_nick
        if not nick:
            return set()
        return {pos for pos, owner in self.state.cells.items() if owner == nick}

    def _neighbors(self, x: int, y: int) -> List[Coord]:
        res = []
        for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            nx, ny = x + dx, y + dy
            if 0 <= nx < self.state.width and 0 <= ny < self.state.height:
                res.append((nx, ny))
        return res

    def _count_own_neighbors(self, pos: Coord, my_cells: Set[Coord]) -> int:
        return sum(1 for nb in self._neighbors(pos[0], pos[1]) if nb in my_cells)

    def _is_free(self, pos: Coord) -> bool:
        return not self.state.cells.get(pos)

    def _clear_plan_unlocked(self) -> None:
        self.state.plan_perimeter.clear()
        self.state.plan_start_owned = 0
        self.state.plan_active = False

    def _update_players_online_unlocked(self, players_list: Optional[list]) -> None:
        if not isinstance(players_list, list):
            return
        for p in players_list:
            nick = p.get("nick")
            if nick:
                self.state.online_players[nick] = bool(p.get("online", True))

    def _update_round_unlocked(self, round_obj: Optional[dict]) -> None:
        if not isinstance(round_obj, dict):
            return
        new_n = round_obj.get("n")
        new_state = round_obj.get("state", self.state.round_state)
        ends_at = round_obj.get("endsAt")

        if new_n is not None and self.state.round_num is not None and new_n != self.state.round_num:
            self.log("KOLO", f"Změna kola {self.state.round_num} -> {new_n}. Zahazuji plán a čekám na state.")
            self.state.cells.clear()
            self.state.pending_move = None
            self.state.has_state = False
            self._clear_plan_unlocked()

        if new_n is not None:
            self.state.round_num = new_n
        if new_state != self.state.round_state:
            self.log("KOLO", f"Kolo {self.state.round_num}: stav změněn na '{new_state}'.")
        self.state.round_state = new_state
        if ends_at is not None:
            self.state.round_ends_at_ms = int(ends_at)

    # --- DETEKCE BEZPEČNÝCH REZERV (BANKOVÁNÍ POLÍ) ---

    def _analyze_safe_banked_cells(
        self, my_cells: Set[Coord], active_enemies: Set[Coord]
    ) -> Tuple[Set[Coord], Set[Coord]]:
        """
        Rozdělí prázdné kapsy za našimi liniemi na:
        1) safe_banked: 100% uzavřené našimi kostkami, bez soupeřů a bez tlaku na ochrannou zeď
                        -> necháme si je až na konec kola!
        2) threatened_banked: uzavřené kapsy, u jejichž zdi se ale objevil aktivní soupeř
                              -> okamžitě je vybereme, než soupeř prorazí!
        """
        my_nick = self.state.confirmed_nick
        visited: Set[Coord] = set()
        safe_banked: Set[Coord] = set()
        threatened_banked: Set[Coord] = set()

        for y in range(self.state.height):
            for x in range(self.state.width):
                start = (x, y)
                if start in visited or not self._is_free(start):
                    continue

                # Prohledáme souvislou prázdnou oblast
                comp: Set[Coord] = {start}
                queue = deque([start])
                visited.add(start)
                touches_enemy = False
                border_own_cells: Set[Coord] = set()

                while queue:
                    cx, cy = queue.popleft()
                    for nx, ny in self._neighbors(cx, cy):
                        nb = (nx, ny)
                        owner = self.state.cells.get(nb, "")
                        if owner == "":
                            if nb not in visited:
                                visited.add(nb)
                                comp.add(nb)
                                queue.append(nb)
                        elif owner == my_nick:
                            border_own_cells.add(nb)
                        else:
                            touches_enemy = True

                # Kapsa je pod naší kontrolou jen tehdy, když se jí nedotýká žádný soupeř
                if not touches_enemy and border_own_cells and len(comp) <= MAX_BANK_POCKET_SIZE:
                    # Zkontrolujeme, jestli nějaký online soupeř netlačí na ochrannou zeď kapsy
                    wall_under_attack = any(
                        nb in active_enemies
                        for wx, wy in border_own_cells
                        for nb in self._neighbors(wx, wy)
                    )
                    if wall_under_attack:
                        threatened_banked |= comp
                    else:
                        safe_banked |= comp

        return safe_banked, threatened_banked

    # --- ZPRACOVÁNÍ PŘÍCHOZÍCH ZPRÁV ---

    def on_open(self, ws) -> None:
        with self.state.lock:
            self.state.ws_open = True
            self.state.need_join = True
            self.state.confirmed_nick = None
            self.state.has_state = False
            self.state.pending_move = None
            self.state.last_ack_mono = 0.0
            self._clear_plan_unlocked()
        self.log("SPOJENÍ", f"Připojeno k {self.url}")

    def on_close(self, ws, close_status_code, close_msg) -> None:
        with self.state.lock:
            self.state.ws_open = False
            self.state.need_join = False
        reason = f"kód={close_status_code}, důvod='{close_msg}'" if close_status_code else "ukončeno"
        self.log("SPOJENÍ", f"Odpojeno ({reason})")
        if close_msg and any(w in str(close_msg).lower() for w in ("ban", "nick", "forbidden")):
            with self.state.lock:
                self.state.fatal_error = f"Server ukončil spojení: {close_msg}"

    def on_error(self, ws, error) -> None:
        if not self.stop_event.is_set():
            self.log("CHYBA-WS", f"Chyba socketu: {error}")

    def on_message(self, ws, raw_message: str) -> None:
        try:
            msg = json.loads(raw_message)
        except json.JSONDecodeError:
            self.log("CHYBA", f"Neplatný JSON ze serveru: {raw_message[:120]}")
            return

        msg_type = msg.get("t")
        now_mono = time.monotonic()

        with self.state.lock:
            if msg_type == "welcome":
                confirmed = msg.get("nick") or self.requested_nick
                self.state.confirmed_nick = confirmed
                color = msg.get("color", "neznámá")
                self.log("PŘIHLÁŠENÍ", f"Potvrzena přezdívka '{confirmed}' (barva: {color})")

            elif msg_type == "state":
                self.state.width = int(msg.get("w", 40))
                self.state.height = int(msg.get("h", 40))
                self.state.cells.clear()
                for item in msg.get("cells", []):
                    owner = item.get("owner")
                    if owner:
                        self.state.cells[(int(item["x"]), int(item["y"]))] = owner

                self._update_players_online_unlocked(msg.get("players"))
                self._update_round_unlocked(msg.get("round"))
                self.state.has_state = True
                if self.state.confirmed_nick:
                    self.state.successful_handshake = True

                my_count = len(self._my_cells_unlocked())
                self.log(
                    "MAPA",
                    f"Načten snímek {self.state.width}x{self.state.height} | "
                    f"kolo={self.state.round_num} ({self.state.round_state}) | "
                    f"moje pole={my_count}"
                )

            elif msg_type == "player":
                p_nick = msg.get("nick")
                if p_nick:
                    self.state.online_players[p_nick] = bool(msg.get("online", True))

            elif msg_type == "cell":
                x, y = int(msg["x"]), int(msg["y"])
                owner = msg.get("owner") or ""
                if owner:
                    self.state.cells[(x, y)] = owner
                else:
                    self.state.cells.pop((x, y), None)

                self._check_move_confirmation_unlocked((x, y), owner, now_mono)

            elif msg_type == "capture":
                capturer = msg.get("nick", "")
                gained = msg.get("gained", 0)
                if "cells" in msg and isinstance(msg["cells"], list):
                    for item in msg["cells"]:
                        cx, cy = int(item["x"]), int(item["y"])
                        c_owner = item.get("owner") or capturer
                        if c_owner:
                            self.state.cells[(cx, cy)] = c_owner
                        else:
                            self.state.cells.pop((cx, cy), None)
                        self._check_move_confirmation_unlocked((cx, cy), c_owner, now_mono)

                if capturer == self.state.confirmed_nick:
                    stolen = sum(msg.get("from", {}).values()) if isinstance(msg.get("from"), dict) else 0
                    total_now = len(self._my_cells_unlocked())
                    self.log("ZÁBOR", f"Obklíčeno +{gained} polí (ukradeno: {stolen}) | Celkem: {total_now}")

            elif msg_type in ("round", "scores"):
                self._update_round_unlocked(msg.get("round"))
                self._update_players_online_unlocked(msg.get("players"))

            elif msg_type == "result":
                self.state.round_state = "finished"
                self.state.pending_move = None
                self._clear_plan_unlocked()
                players = msg.get("players", [])
                winner = f"{players[0]['nick']} ({players[0]['cells']})" if players else "neznámý"
                self.log("KOLO", f"Kolo {msg.get('n', self.state.round_num)} skončilo. Vítěz: {winner}")

            elif msg_type == "error":
                err_text = (
                    msg.get("msg")
                    or msg.get("message")
                    or msg.get("error")
                    or msg.get("reason")
                    or str(msg.get("code", "neznámá chyba"))
                )
                self.log("CHYBA-SERVER", f"Server hlásí: {err_text}")
                self.state.last_ack_mono = now_mono

                retry_ms = msg.get("retryAfterMs") or msg.get("retry_after_ms")
                if retry_ms is not None:
                    wait_s = max(0.5, float(retry_ms) / 1000.0)
                    self.state.backoff_until_mono = max(self.state.backoff_until_mono, now_mono + wait_s)
                    self.log("ČEKÁNÍ", f"Server vyžaduje pauzu {wait_s:.2f} s")

                lower_err = str(err_text).lower()
                if any(w in lower_err for w in ("ban", "banned", "invalid nick", "nick taken", "nick rejected")):
                    self.state.fatal_error = f"Fatální chyba přihlášení/účtu: {err_text}"
                    return

                if "slow down" in lower_err or "rate" in lower_err:
                    self.state.send_interval = min(1.35, self.state.send_interval + 0.03)
                    self.state.backoff_until_mono = max(self.state.backoff_until_mono, now_mono + 0.65)
                    if self.state.pending_move is not None and self.state.last_sent_type == "place":
                        pm = self.state.pending_move
                        self.log(
                            "TEMPO",
                            f"Tah ({pm.x}, {pm.y}) zpomalen -> zopakuji za 0.65 s "
                            f"(nový interval {self.state.send_interval:.2f} s)"
                        )
                        self.state.pending_move = None
                    return

                if self.state.pending_move is not None and self.state.last_sent_type == "place":
                    pm = self.state.pending_move
                    self.log("TAH-ODMÍTNUT", f"Tah ({pm.x}, {pm.y}) odmítnut ({err_text}), přepočítávám plán.")
                    self.state.pending_move = None
                    self._clear_plan_unlocked()

    def _check_move_confirmation_unlocked(self, pos: Coord, owner: str, now_mono: float) -> None:
        pm = self.state.pending_move
        nick = self.state.confirmed_nick
        if not pm or not nick or owner != nick:
            return

        if pm.was_first_spawn or (pm.x, pm.y) == pos:
            dt = now_mono - pm.sent_at
            self.state.last_ack_mono = now_mono
            self.log("TAH-OK", f"Potvrzena kostka na {pos} (odezva {dt:.2f} s)")
            self.state.pending_move = None

    # --- STRATEGIE PRO ČTVERCE, BANKOVÁNÍ A ÚTOK ---

    def _build_rectangle_perimeter(self, x0: int, y0: int, w: int, h: int) -> List[Coord]:
        perim: List[Coord] = []
        for x in range(x0, x0 + w):
            perim.append((x, y0))
        for y in range(y0 + 1, y0 + h):
            perim.append((x0 + w - 1, y))
        for x in range(x0 + w - 2, x0 - 1, -1):
            perim.append((x, y0 + h - 1))
        for y in range(y0 + h - 2, y0, -1):
            perim.append((x0, y))
        return perim

    def _remaining_round_seconds(self) -> Optional[float]:
        if self.state.round_ends_at_ms is None:
            return None
        now_ms = time.time() * 1000.0
        return max(0.0, (self.state.round_ends_at_ms - now_ms) / 1000.0)

    def _active_enemy_set(self) -> Set[Coord]:
        nick = self.state.confirmed_nick
        return {
            pos for pos, owner in self.state.cells.items()
            if owner and owner != nick and self.state.online_players.get(owner, True)
        }

    def _pick_defensive_perimeter_step(self, reachable: List[Coord], active_enemies: Set[Coord]) -> Coord:
        if len(reachable) == 1 or not active_enemies:
            return reachable[0]

        def min_dist_to_enemy(p: Coord) -> int:
            px, py = p
            return min(abs(px - ex) + abs(py - ey) for ex, ey in active_enemies)

        return min(reachable, key=min_dist_to_enemy)

    def _find_best_perimeter_plan(
        self,
        my_cells: Set[Coord],
        safe_banked: Set[Coord],
        max_side: int = 7,
    ) -> List[Coord]:
        best_perim: List[Coord] = []
        best_score = -1.0
        rem_sec = self._remaining_round_seconds()
        my_nick = self.state.confirmed_nick
        active_enemies = self._active_enemy_set()

        anchors = list(my_cells)
        if len(anchors) > 90:
            anchors = anchors[:: max(1, len(anchors) // 90)]

        tested_rects: Set[Tuple[int, int, int, int]] = set()
        step_cost_sec = self.state.send_interval * 1.25

        for ax, ay in anchors:
            for side_w in range(3, max_side + 1):
                for side_h in range(3, max_side + 1):
                    for x0 in (ax, ax - side_w + 1):
                        for y0 in (ay, ay - side_h + 1):
                            if x0 < 0 or y0 < 0 or x0 + side_w > self.state.width or y0 + side_h > self.state.height:
                                continue
                            rect_key = (x0, y0, side_w, side_h)
                            if rect_key in tested_rects:
                                continue
                            tested_rects.add(rect_key)

                            perim = self._build_rectangle_perimeter(x0, y0, side_w, side_h)
                            perim_set = set(perim)

                            owned_on_perim = sum(1 for p in perim if p in my_cells)
                            if owned_on_perim == 0:
                                continue

                            blocked_perim = False
                            missing_cells: List[Coord] = []
                            for p in perim:
                                owner = self.state.cells.get(p, "")
                                if owner == "":
                                    missing_cells.append(p)
                                elif owner != my_nick:
                                    blocked_perim = True
                                    break
                            missing_moves = len(missing_cells)
                            if blocked_perim or missing_moves == 0:
                                continue

                            # Pokud celý plán jen vyplňuje bezpečnou banku za našimi zády, přeskočíme ho
                            if all(p in safe_banked for p in missing_cells):
                                continue

                            if rem_sec is not None and missing_moves * step_cost_sec > rem_sec:
                                continue

                            threatened_walls = sum(
                                1 for mx, my in missing_cells
                                if any(nb in active_enemies for nb in self._neighbors(mx, my))
                            )

                            interior_value = 0.0
                            interior_gain_count = 0
                            for ix in range(x0 + 1, x0 + side_w - 1):
                                for iy in range(y0 + 1, y0 + side_h - 1):
                                    if (ix, iy) in perim_set:
                                        continue
                                    owner = self.state.cells.get((ix, iy), "")
                                    if owner == "":
                                        interior_value += 1.0
                                        interior_gain_count += 1
                                    elif owner != my_nick:
                                        interior_gain_count += 1
                                        if not self.state.online_players.get(owner, True):
                                            interior_value += 3.5
                                        else:
                                            interior_value += 2.6

                            if interior_gain_count == 0:
                                continue

                            roi = interior_value / missing_moves
                            wall_reuse_bonus = 1.0 + (owned_on_perim / len(perim)) * 0.9
                            danger_factor = 1.0 / (1.0 + threatened_walls * 0.65)
                            score = roi * wall_reuse_bonus * danger_factor

                            if score > best_score:
                                best_score = score
                                best_perim = perim

        return best_perim

    def _find_shark_assault_move(self, my_cells: Set[Coord]) -> Optional[Coord]:
        my_nick = self.state.confirmed_nick
        best_target: Optional[Coord] = None
        best_score = -1.0

        candidates: Set[Coord] = set()
        for mx, my in my_cells:
            for nb in self._neighbors(mx, my):
                if nb not in my_cells:
                    candidates.add(nb)

        for pos in candidates:
            owner = self.state.cells.get(pos, "")
            own_nb = self._count_own_neighbors(pos, my_cells)

            if owner != "" and own_nb >= 3:
                is_offline = not self.state.online_players.get(owner, True)
                score = 120.0 if is_offline else 90.0

                simulated_my = my_cells | {pos}
                for nb in self._neighbors(pos[0], pos[1]):
                    nb_owner = self.state.cells.get(nb, "")
                    if nb_owner not in ("", my_nick) and nb not in simulated_my:
                        if self._count_own_neighbors(nb, simulated_my) >= 3:
                            score += 45.0

                if score > best_score:
                    best_score = score
                    best_target = pos

        return best_target

    def _pick_bank_harvest_move(
        self, my_cells: Set[Coord], target_pool: Set[Coord]
    ) -> Optional[Coord]:
        """Vybere nejdostupnější políčko z bezpečné rezervy (nejvíce vlastních sousedů)."""
        best_cell: Optional[Coord] = None
        best_own_nb = -1
        for pos in target_pool:
            if self._is_free(pos):
                own_nb = self._count_own_neighbors(pos, my_cells)
                if own_nb >= 1 and own_nb > best_own_nb:
                    best_own_nb = own_nb
                    best_cell = pos
        return best_cell

    def _choose_next_move_unlocked(self) -> Optional[Tuple[Coord, bool, str]]:
        my_cells = self._my_cells_unlocked()
        active_enemies = self._active_enemy_set()

        # 1. První kostka
        if not my_cells:
            self._clear_plan_unlocked()
            for margin in (4, 1, 0):
                for y in range(margin, self.state.height - margin):
                    for x in range(margin, self.state.width - margin):
                        if self._is_free((x, y)):
                            return (x, y), True, "START"
            return None

        # Zjistíme, kolik polí máme bezpečně zazděných v bance a jestli některé není v ohrožení
        safe_banked, threatened_banked = self._analyze_safe_banked_cells(my_cells, active_enemies)
        rem_sec = self._remaining_round_seconds()

        # 1b. Okamžitá záchrana rezervy, pokud soupeř přitlačil na ochrannou zeď
        if threatened_banked:
            rescue = self._pick_bank_harvest_move(my_cells, threatened_banked)
            if rescue is not None:
                self._clear_plan_unlocked()
                return rescue, False, "BANKA-ZÁCHRANA"

        # 1c. Finále kola: vybereme uloženou banku včas před vypršením času
        if safe_banked and rem_sec is not None:
            needed_sec = len(safe_banked) * (self.state.send_interval * 1.18) + 12.0
            if rem_sec <= max(35.0, needed_sec):
                cash_in = self._pick_bank_harvest_move(my_cells, safe_banked)
                if cash_in is not None:
                    self._clear_plan_unlocked()
                    return cash_in, False, f"BANKA-FINÁLE ({len(safe_banked)})"

        # 2. Kontrola rozestavěného obvodu
        if self.state.plan_active and self.state.plan_perimeter:
            enemy_on_plan = any(
                self.state.cells.get(p, "") not in ("", self.state.confirmed_nick)
                for p in self.state.plan_perimeter
            )
            missing_on_plan = [p for p in self.state.plan_perimeter if self._is_free(p)]

            if not missing_on_plan:
                gained_net = len(my_cells) - self.state.plan_start_owned
                self.log("PLÁN", f"Obvod dokončen! Čistý přírůstek vlastních polí: +{max(0, gained_net)}")
                self._clear_plan_unlocked()
            elif enemy_on_plan:
                self.log("PLÁN", "Soupeř narušil plánovaný obvod, hledám nový.")
                self._clear_plan_unlocked()
            else:
                if len(missing_on_plan) > 3:
                    threat_close = any(
                        nb in active_enemies
                        for mx, my in missing_on_plan
                        for nb in self._neighbors(mx, my)
                    )
                    if threat_close:
                        quick_perim = self._find_best_perimeter_plan(my_cells, safe_banked, max_side=4)
                        if quick_perim and len([p for p in quick_perim if self._is_free(p)]) < len(missing_on_plan):
                            self.log("OBRANA", "Nepřítel blízko zdi -> zkracuji obvod pro rychlé uzavření!")
                            self.state.plan_perimeter = quick_perim
                            self.state.plan_start_owned = len(my_cells)
                            missing_on_plan = [p for p in quick_perim if self._is_free(p)]

                reachable = [p for p in missing_on_plan if self._count_own_neighbors(p, my_cells) >= 1]
                if reachable:
                    chosen = self._pick_defensive_perimeter_step(reachable, active_enemies)
                    return chosen, False, "OBVOD"
                else:
                    self.log("PLÁN", "Obvod ztratil návaznost na vlastní pole, přepočítávám.")
                    self._clear_plan_unlocked()

        # 3. Hledání nového výhodného obvodu (ignoruje čistě bankovní pole)
        new_perim = self._find_best_perimeter_plan(my_cells, safe_banked, max_side=7)
        if new_perim:
            missing = [p for p in new_perim if self._is_free(p)]
            reachable = [p for p in missing if self._count_own_neighbors(p, my_cells) >= 1]
            if reachable:
                self.state.plan_perimeter = new_perim
                self.state.plan_start_owned = len(my_cells)
                self.state.plan_active = True
                self.log(
                    "PLÁN",
                    f"Nový obvod ({len(new_perim)} polí celkem, {len(missing)} chybí postavit) "
                    f"od {new_perim[0]}"
                )
                chosen = self._pick_defensive_perimeter_step(reachable, active_enemies)
                return chosen, False, "OBVOD"

        # 4. Útočný dominový režim (krádež cizích kostek s >= 3 sousedy)
        shark_move = self._find_shark_assault_move(my_cells)
        if shark_move is not None:
            return shark_move, False, "ŽRALOK-ÚTOK"

        # 5. Expanze na otevřené frontě (bezpečnou banku zatím necháváme na později!)
        best_fallback: Optional[Coord] = None
        best_fallback_score = -1.0
        my_nick = self.state.confirmed_nick

        for mx, my in my_cells:
            for nb in self._neighbors(mx, my):
                if self._is_free(nb) and nb not in safe_banked:
                    open_neighbors = sum(
                        1 for n2 in self._neighbors(nb[0], nb[1])
                        if self._is_free(n2) and n2 not in safe_banked
                    )
                    setup_steal_bonus = 0.0
                    simulated_my = my_cells | {nb}
                    for n2 in self._neighbors(nb[0], nb[1]):
                        n2_owner = self.state.cells.get(n2, "")
                        if n2_owner not in ("", my_nick):
                            if self._count_own_neighbors(n2, simulated_my) >= 3:
                                setup_steal_bonus += 4.0

                    score = open_neighbors + setup_steal_bonus
                    if score > best_fallback_score:
                        best_fallback_score = score
                        best_fallback = nb

        if best_fallback is not None:
            now_mono = time.monotonic()
            if safe_banked and now_mono - self.state.last_bank_log_mono > 20.0:
                self.state.last_bank_log_mono = now_mono
                self.log("BANKA", f"Šetřím {len(safe_banked)} jistých polí na později, expanduji na frontě.")
            return best_fallback, False, "VOLNÝ-KROK"

        # 6. Pokud na frontě už nic nezbývá, vybereme uloženou banku
        if safe_banked:
            harvest = self._pick_bank_harvest_move(my_cells, safe_banked)
            if harvest is not None:
                return harvest, False, f"BANKA-SKLIZEŇ ({len(safe_banked)})"

        return None

    # --- JEDINÁ ODESÍLACÍ SMYČKA A HEARTBEAT ---

    def _send_json_unlocked(self, payload: dict, now_mono: float) -> bool:
        if not self.ws or not self.state.ws_open:
            return False
        try:
            self.ws.send(json.dumps(payload, separators=(",", ":")))
            self.state.last_send_mono = now_mono
            self.state.last_sent_type = payload.get("t")
            if payload.get("t") == "ping":
                self.state.last_ping_mono = now_mono
            return True
        except Exception as exc:
            self.log("CHYBA-SEND", f"Odeslání selhalo: {exc}")
            self.state.ws_open = False
            return False

    def _run_session_loop(self) -> None:
        while not self.stop_event.is_set():
            now_mono = time.monotonic()
            sleep_time = 0.04

            with self.state.lock:
                if self.state.fatal_error or self.state.force_reconnect or not self.state.ws_open:
                    break

                if self.state.pending_move is not None:
                    waited = now_mono - self.state.pending_move.sent_at
                    if waited >= CONFIRM_TIMEOUT:
                        pm = self.state.pending_move
                        self.log(
                            "TIMEOUT",
                            f"Tah ({pm.x}, {pm.y}) nebyl potvrzen do {CONFIRM_TIMEOUT:.0f} s. "
                            "Obnovuji stav mapy novým připojením."
                        )
                        self.state.pending_move = None
                        self._clear_plan_unlocked()
                        self.state.force_reconnect = True
                        break

                since_last_send = now_mono - self.state.last_send_mono
                since_last_ack = now_mono - self.state.last_ack_mono
                since_last_ping = now_mono - self.state.last_ping_mono

                ready_to_send = (
                    since_last_send >= self.state.send_interval
                    and since_last_ack >= MIN_ACK_GAP
                    and now_mono >= self.state.backoff_until_mono
                )

                if ready_to_send:
                    if self.state.need_join:
                        if self._send_json_unlocked({"t": "join", "nick": self.requested_nick}, now_mono):
                            self.state.need_join = False
                            self.state.last_ping_mono = now_mono
                            self.log("PŘIHLÁŠENÍ", f"Odeslán join pro '{self.requested_nick}'")

                    elif since_last_ping >= (HEARTBEAT_INTERVAL - self.state.send_interval):
                        self._send_json_unlocked({"t": "ping"}, now_mono)

                    elif (
                        self.state.confirmed_nick is not None
                        and self.state.has_state
                        and self.state.round_state == "running"
                        and self.state.pending_move is None
                    ):
                        decision = self._choose_next_move_unlocked()
                        if decision is not None:
                            (tx, ty), is_first, mode = decision
                            if self._send_json_unlocked({"t": "place", "x": tx, "y": ty}, now_mono):
                                self.state.pending_move = PendingMove(
                                    x=tx,
                                    y=ty,
                                    sent_at=now_mono,
                                    was_first_spawn=is_first,
                                )
                                self.log("TAH-ODESLÁN", f"[{mode}] place ({tx}, {ty})")

            time.sleep(sleep_time)

    # --- HLAVNÍ SMYČKA S EXPONENCIÁLNÍM RECONNECTEM ---

    def run(self) -> None:
        attempt = 0

        while not self.stop_event.is_set():
            with self.state.lock:
                if self.state.fatal_error:
                    self.log("STOP", self.state.fatal_error)
                    break
                self.state.force_reconnect = False
                self.state.successful_handshake = False

            self.ws = websocket.WebSocketApp(
                self.url,
                on_open=self.on_open,
                on_message=self.on_message,
                on_error=self.on_error,
                on_close=self.on_close,
            )

            ws_thread = threading.Thread(
                target=self.ws.run_forever,
                kwargs={"ping_interval": 0},
                daemon=True,
            )
            ws_thread.start()

            connect_deadline = time.monotonic() + 5.0
            while not self.stop_event.is_set() and time.monotonic() < connect_deadline:
                with self.state.lock:
                    if self.state.ws_open or self.state.fatal_error:
                        break
                time.sleep(0.05)

            self._run_session_loop()

            try:
                self.ws.close()
            except Exception:
                pass
            ws_thread.join(timeout=2.0)

            if self.stop_event.is_set():
                break

            with self.state.lock:
                if self.state.fatal_error:
                    self.log("STOP", self.state.fatal_error)
                    break
                if self.state.successful_handshake:
                    attempt = 0

            attempt += 1
            if attempt > MAX_RECONNECT_ATTEMPTS:
                self.log("STOP", f"Vyčerpán maximální počet pokusů o připojení ({MAX_RECONNECT_ATTEMPTS}).")
                break

            delay = BACKOFF_DELAYS[min(attempt - 1, len(BACKOFF_DELAYS) - 1)]
            self.log("RECONNECT", f"Pokus {attempt}/{MAX_RECONNECT_ATTEMPTS} za {delay} s...")
            end_wait = time.monotonic() + delay
            while not self.stop_event.is_set() and time.monotonic() < end_wait:
                time.sleep(0.1)

        self.log("KONEC", "Klient byl čistě ukončen.")


def main() -> None:
    parser = argparse.ArgumentParser(description="WS Aréna - autonomní klient s bankováním")
    parser.add_argument("--nick", default=DEFAULT_NICK, help="Přezdívka hráče")
    parser.add_argument("--url", default=DEFAULT_URL, help="WebSocket URL serveru")
    args = parser.parse_args()

    client = ArenaClient(url=args.url, nick=args.nick)

    def handle_sigint(signum, frame):
        client.log("SIGNÁL", "Zachyceno Ctrl+C, ukončuji spojení...")
        client.stop_event.set()
        if client.ws:
            try:
                client.ws.close()
            except Exception:
                pass

    signal.signal(signal.SIGINT, handle_sigint)
    client.run()


if __name__ == "__main__":
    main()