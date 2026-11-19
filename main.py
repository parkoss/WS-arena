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

ENDGAME_SAFETY_BUFFER_SEC = 14.0  # Časová rezerva před koncem kola pro vybrání bublin

Coord = Tuple[int, int]


@dataclass
class PendingMove:
    x: int
    y: int
    sent_at: float
    was_first_spawn: bool


@dataclass
class SealedBubble:
    cells: Set[Coord]          # Všechna prázdná pole uvnitř bubliny
    trigger_cells: List[Coord] # Okrajová pole, jejichž zaplněním server vybarví zbytek
    value: int                 # Celkový zisk polí po uzavření


@dataclass
class OpenGateRing:
    gate: Coord                # Jediná chybějící kostka k uzavření velkého okruhu
    interior_value: int        # Počet polí uvnitř, která se po položení brány vybarví
    enemy_distance: int        # Vzdálenost nejbližšího aktivního soupeře od brány


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
    server_clock_skew_ms: float = 0.0

    pending_move: Optional[PendingMove] = None
    last_sent_type: Optional[str] = None
    last_send_mono: float = 0.0
    last_ack_mono: float = 0.0
    last_ping_mono: float = 0.0
    backoff_until_mono: float = 0.0
    send_interval: float = INITIAL_SEND_INTERVAL

    # Aktuální stavební plán velké bubliny / okruhu
    plan_walls: List[Coord] = field(default_factory=list)
    plan_gate: Optional[Coord] = None     # Volitelná 1-políčková brána u středového okruhu
    plan_label: str = ""
    plan_expected_gain: int = 0
    plan_start_owned: int = 0
    plan_active: bool = False

    last_status_log_mono: float = 0.0

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

    def _is_map_border(self, pos: Coord) -> bool:
        x, y = pos
        return x == 0 or x == self.state.width - 1 or y == 0 or y == self.state.height - 1

    def _count_own_neighbors(self, pos: Coord, my_cells: Set[Coord]) -> int:
        return sum(1 for nb in self._neighbors(pos[0], pos[1]) if nb in my_cells)

    def _is_free(self, pos: Coord) -> bool:
        return not self.state.cells.get(pos)

    def _clear_plan_unlocked(self) -> None:
        self.state.plan_walls.clear()
        self.state.plan_gate = None
        self.state.plan_label = ""
        self.state.plan_expected_gain = 0
        self.state.plan_start_owned = 0
        self.state.plan_active = False

    def _remaining_round_seconds(self) -> Optional[float]:
        if self.state.round_ends_at_ms is None:
            return None
        now_ms = time.time() * 1000.0 + self.state.server_clock_skew_ms
        return max(0.0, (self.state.round_ends_at_ms - now_ms) / 1000.0)

    def _effective_seconds_per_move(self) -> float:
        # Zahrnuje rozestup tahů i pravidelný aplikační heartbeat ping
        ping_overhead = HEARTBEAT_INTERVAL / max(1.0, (HEARTBEAT_INTERVAL - self.state.send_interval))
        return self.state.send_interval * (ping_overhead / (ping_overhead - 1.0)) * 1.06

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

    # --- DETEKCE UZAVŘENÝCH VELKÝCH BUBLIN A OTEVŘENÝCH BRAN ---

    def _detect_sealed_bubbles(
        self, my_cells: Set[Coord], active_enemies: Set[Coord]
    ) -> Tuple[List[SealedBubble], List[SealedBubble]]:
        """
        Najde všechny prázdné oblasti opřené o okraj mapy, které jsou ze všech vnitřních stran
        100% uzavřené našimi stěnami (žádný soupeř uvnitř ani na hranici).
        Vrátí (bezpecne_bubliny, ohrozene_bubliny) seřazené od největší po nejmenší.
        """
        my_nick = self.state.confirmed_nick
        visited: Set[Coord] = set()
        safe_bubbles: List[SealedBubble] = []
        threatened_bubbles: List[SealedBubble] = []

        for y in range(self.state.height):
            for x in range(self.state.width):
                start = (x, y)
                if start in visited or not self._is_free(start):
                    continue

                comp: Set[Coord] = {start}
                queue = deque([start])
                visited.add(start)
                touches_enemy = False
                border_own_walls: Set[Coord] = set()

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
                            border_own_walls.add(nb)
                        else:
                            touches_enemy = True

                # Bublina je bezpečně zamčená jen tehdy, když se jí nedotýká žádný soupeř
                # a není to celá prázdná mapa (limit max 45 % plochy)
                max_bubble_area = int(self.state.width * self.state.height * 0.45)
                if not touches_enemy and border_own_walls and 1 <= len(comp) <= max_bubble_area:
                    # K jejímu kompletnímu vybarvení stačí zaplnit její buňky na okraji mapy!
                    triggers = [p for p in comp if self._is_map_border(p)]
                    if not triggers:
                        continue

                    bubble = SealedBubble(
                        cells=comp,
                        trigger_cells=triggers,
                        value=len(comp),
                    )
                    wall_threatened = any(
                        nb in active_enemies
                        for wx, wy in border_own_walls
                        for nb in self._neighbors(wx, wy)
                    )
                    if wall_threatened:
                        threatened_bubbles.append(bubble)
                    else:
                        safe_bubbles.append(bubble)

        safe_bubbles.sort(key=lambda b: b.value, reverse=True)
        threatened_bubbles.sort(key=lambda b: b.value, reverse=True)
        return safe_bubbles, threatened_bubbles

    def _detect_open_gate_rings(
        self, my_cells: Set[Coord], active_enemies: Set[Coord]
    ) -> List[OpenGateRing]:
        """
        Najde prázdná pole sousedící s naším územím, jejichž jediným položením
        se uzavře velká vnitřní oblast (>= 8 polí) bez dotyku okraje mapy.
        """
        rings: List[OpenGateRing] = []
        candidates: Set[Coord] = set()
        for mx, my in my_cells:
            for nb in self._neighbors(mx, my):
                if self._is_free(nb) and self._count_own_neighbors(nb, my_cells) >= 2:
                    candidates.add(nb)

        for gate in candidates:
            sim_my = my_cells | {gate}
            checked: Set[Coord] = set()
            captured_total = 0

            for sx, sy in self._neighbors(gate[0], gate[1]):
                if (sx, sy) in sim_my or (sx, sy) in checked:
                    continue

                q = deque([(sx, sy)])
                comp = {(sx, sy)}
                touches_edge = False

                while q:
                    cx, cy = q.popleft()
                    if self._is_map_border((cx, cy)):
                        touches_edge = True
                    for nx, ny in self._neighbors(cx, cy):
                        if (nx, ny) not in sim_my and (nx, ny) not in comp:
                            comp.add((nx, ny))
                            q.append((nx, ny))

                checked |= comp
                if not touches_edge:
                    captured_total += len(comp)

            if captured_total >= 8:
                dist = 999
                if active_enemies:
                    gx, gy = gate
                    dist = min(abs(gx - ex) + abs(gy - ey) for ex, ey in active_enemies)
                rings.append(OpenGateRing(gate=gate, interior_value=captured_total, enemy_distance=dist))

        rings.sort(key=lambda r: r.interior_value, reverse=True)
        return rings

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
                rem = self._remaining_round_seconds()
                rem_txt = f"{rem:.0f}s" if rem is not None else "?"
                self.log(
                    "MAPA",
                    f"Načten snímek {self.state.width}x{self.state.height} | "
                    f"kolo={self.state.round_num} ({self.state.round_state}, zbývá {rem_txt}) | "
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
                    self.log("ZÁBOR", f"Praskla bublina! +{gained} polí (ukradeno: {stolen}) | Celkem: {total_now}")

            elif msg_type in ("round", "scores"):
                if "now" in msg and msg["now"] is not None:
                    self.state.server_clock_skew_ms = float(msg["now"]) - (time.time() * 1000.0)
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
                            f"(interval {self.state.send_interval:.2f} s)"
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

    # --- GENERÁTOR VELKÝCH BUBLIN (ROHOVÉ L, OKRAJOVÉ U, STŘEDOVÉ MEGA-OKRUHY) ---

    def _active_enemy_set(self) -> Set[Coord]:
        nick = self.state.confirmed_nick
        return {
            pos for pos, owner in self.state.cells.items()
            if owner and owner != nick and self.state.online_players.get(owner, True)
        }

    def _pick_defensive_wall_step(self, reachable: List[Coord], active_enemies: Set[Coord]) -> Coord:
        if len(reachable) == 1 or not active_enemies:
            return reachable[0]

        def min_dist(p: Coord) -> int:
            px, py = p
            return min(abs(px - ex) + abs(py - ey) for ex, ey in active_enemies)

        return min(reachable, key=min_dist)

    def _evaluate_interior_value(self, cells_to_check: List[Coord], my_cells: Set[Coord]) -> Tuple[float, int]:
        """Spočítá bodovou hodnotu a počet polí uvnitř bubliny."""
        my_nick = self.state.confirmed_nick
        val = 0.0
        count = 0
        for pos in cells_to_check:
            if pos in my_cells:
                continue
            owner = self.state.cells.get(pos, "")
            if owner == "":
                val += 1.0
                count += 1
            elif owner != my_nick:
                count += 1
                if not self.state.online_players.get(owner, True):
                    val += 3.2
                else:
                    val += 2.4
        return val, count

    def _find_best_macro_bubble_plan(
        self,
        my_cells: Set[Coord],
        already_banked_cells: Set[Coord],
        existing_trigger_moves: int,
    ) -> Optional[Tuple[List[Coord], Optional[Coord], str, int]]:
        """
        Hledá největší a nejvýhodnější bubliny na mapě:
        1) Rohové L-bubliny (2 stěny od okraje k okraji -> zamknou obří roh)
        2) Okrajové U-bubliny (3 stěny opřené o okraj mapy -> zamknou velký sektor)
        3) Velké středové okruhy (6x6 až 13x13 s 1-políčkovou spouští)
        4) Menší obdélníky (3x3 až 5x5) jako záloha
        Vrátí (seznam_zdi, volitelna_spoust_brana, popis, ocekavany_zisk) nebo None.
        """
        W, H = self.state.width, self.state.height
        my_nick = self.state.confirmed_nick
        active_enemies = self._active_enemy_set()
        rem_sec = self._remaining_round_seconds()
        sec_per_move = self._effective_seconds_per_move()

        best_plan: Optional[Tuple[List[Coord], Optional[Coord], str, int]] = None
        best_score = -1.0

        def consider_candidate(
            walls: List[Coord],
            interior_cells: List[Coord],
            trigger_count_after: int,
            label: str,
            keep_open_gate: bool = False,
        ) -> None:
            nonlocal best_plan, best_score

            # Musí navazovat na naše stávající území
            if not any(w in my_cells or self._count_own_neighbors(w, my_cells) >= 1 for w in walls):
                return

            # Zeď nesmí narazit na soupeře ani vést skrz už zamčenou banku
            missing_walls: List[Coord] = []
            owned_walls = 0
            for w in walls:
                owner = self.state.cells.get(w, "")
                if owner == my_nick:
                    owned_walls += 1
                elif owner == "":
                    if w in already_banked_cells:
                        return
                    missing_walls.append(w)
                else:
                    return

            if not missing_walls:
                return

            # U středového okruhu s bránou necháme poslední kostku jako spoušť (stavíme o 1 méně)
            build_moves = len(missing_walls) - 1 if (keep_open_gate and len(missing_walls) >= 4) else len(missing_walls)
            if build_moves <= 0:
                return

            # Časová kontrola: stihneme postavit tuto bublinu A pak vybrat všechny bubliny do konce kola?
            total_future_triggers = existing_trigger_moves + trigger_count_after
            if rem_sec is not None:
                needed_total_sec = (build_moves + total_future_triggers) * sec_per_move + ENDGAME_SAFETY_BUFFER_SEC
                if needed_total_sec > rem_sec:
                    return

            # Ohodnocení vnitřku (musí mít alespoň nějaká nová pole)
            filtered_interior = [p for p in interior_cells if p not in already_banked_cells]
            interior_val, interior_count = self._evaluate_interior_value(filtered_interior, my_cells)
            if interior_count < 3:
                return

            # Penalizace zdí těsně vedle online soupeřů
            threatened = sum(
                1 for mx, my in missing_walls
                if any(nb in active_enemies for nb in self._neighbors(mx, my))
            )

            # Nelineární odměna (yield ** 1.35) nutí bota upřednostnit VELKÉ bubliny před malými
            wall_reuse = 1.0 + (owned_walls / max(1, len(walls))) * 0.7
            danger_div = 1.0 + threatened * 0.75
            score = ((interior_val ** 1.35) / build_moves) * wall_reuse / danger_div

            if score > best_score:
                best_score = score
                best_plan = (walls, None, label, interior_count)

        # --- TYP A: ROHOVÉ L-BUBLINY (nejefektivnější tvar na mapě!) ---
        # Rohy: (0,0), (W-1,0), (0,H-1), (W-1,H-1)
        for bw in range(6, 18):
            for bh in range(6, 18):
                # 1. Levý horní roh (0,0) -> zeď (0, bh) .. (bw, bh) .. (bw, 0)
                if bw < W and bh < H:
                    walls = [(x, bh) for x in range(0, bw + 1)] + [(bw, y) for y in range(bh - 1, -1, -1)]
                    interior = [(x, y) for x in range(0, bw) for y in range(0, bh)]
                    triggers = bw + bh - 1  # okrajové buňky na x=0 a y=0
                    consider_candidate(walls, interior, triggers, f"ROHOVÁ L-BUBLINA {bw}x{bh}")

                # 2. Pravý horní roh (W-1, 0) -> zeď (W-1, bh) .. (W-1-bw, bh) .. (W-1-bw, 0)
                x_wall = W - 1 - bw
                if x_wall >= 0 and bh < H:
                    walls = [(x, bh) for x in range(W - 1, x_wall - 1, -1)] + [(x_wall, y) for y in range(bh - 1, -1, -1)]
                    interior = [(x, y) for x in range(x_wall + 1, W) for y in range(0, bh)]
                    triggers = bw + bh - 1
                    consider_candidate(walls, interior, triggers, f"ROHOVÁ L-BUBLINA {bw}x{bh}")

                # 3. Levý dolní roh (0, H-1) -> zeď (0, H-1-bh) .. (bw, H-1-bh) .. (bw, H-1)
                y_wall = H - 1 - bh
                if bw < W and y_wall >= 0:
                    walls = [(x, y_wall) for x in range(0, bw + 1)] + [(bw, y) for y in range(y_wall + 1, H)]
                    interior = [(x, y) for x in range(0, bw) for y in range(y_wall + 1, H)]
                    triggers = bw + bh - 1
                    consider_candidate(walls, interior, triggers, f"ROHOVÁ L-BUBLINA {bw}x{bh}")

                # 4. Pravý dolní roh (W-1, H-1)
                if x_wall >= 0 and y_wall >= 0:
                    walls = [(x, y_wall) for x in range(W - 1, x_wall - 1, -1)] + [(x_wall, y) for y in range(y_wall + 1, H)]
                    interior = [(x, y) for x in range(x_wall + 1, W) for y in range(y_wall + 1, H)]
                    triggers = bw + bh - 1
                    consider_candidate(walls, interior, triggers, f"ROHOVÁ L-BUBLINA {bw}x{bh}")

        # --- TYP B: OKRAJOVÉ U-BUBLINY (opřené o jednu ze 4 stran mapy) ---
        # Vybereme jen kotevní body blízko okrajů mapy (do vzdálenosti 15 polí), aby hledání bylo bleskové
        edge_anchors = [
            (ax, ay) for (ax, ay) in my_cells
            if ax <= 15 or ax >= W - 16 or ay <= 15 or ay >= H - 16
        ]
        if len(edge_anchors) > 50:
            edge_anchors = edge_anchors[:: max(1, len(edge_anchors) // 50)]

        seen_u: Set[Tuple[str, int, int, int]] = set()
        for ax, ay in edge_anchors:
            for depth in range(5, 15):
                for span in range(6, 16):
                    # Levá hrana x=0
                    if depth < W:
                        for y0 in (ay, ay - span + 1):
                            y1 = y0 + span - 1
                            if 0 <= y0 and y1 < H and ("L", y0, y1, depth) not in seen_u:
                                seen_u.add(("L", y0, y1, depth))
                                walls = (
                                    [(x, y0) for x in range(0, depth + 1)]
                                    + [(depth, y) for y in range(y0 + 1, y1)]
                                    + [(x, y1) for x in range(depth, -1, -1)]
                                )
                                interior = [(x, y) for x in range(0, depth) for y in range(y0 + 1, y1)]
                                consider_candidate(walls, interior, span - 2, f"OKRAJOVÁ U-BUBLINA {depth}x{span}")

                    # Pravá hrana x=W-1
                    x_in = W - 1 - depth
                    if x_in >= 0:
                        for y0 in (ay, ay - span + 1):
                            y1 = y0 + span - 1
                            if 0 <= y0 and y1 < H and ("R", y0, y1, depth) not in seen_u:
                                seen_u.add(("R", y0, y1, depth))
                                walls = (
                                    [(x, y0) for x in range(W - 1, x_in - 1, -1)]
                                    + [(x_in, y) for y in range(y0 + 1, y1)]
                                    + [(x, y1) for x in range(x_in, W)]
                                )
                                interior = [(x, y) for x in range(x_in + 1, W) for y in range(y0 + 1, y1)]
                                consider_candidate(walls, interior, span - 2, f"OKRAJOVÁ U-BUBLINA {depth}x{span}")

                    # Horní hrana y=0
                    if depth < H:
                        for x0 in (ax, ax - span + 1):
                            x1 = x0 + span - 1
                            if 0 <= x0 and x1 < W and ("T", x0, x1, depth) not in seen_u:
                                seen_u.add(("T", x0, x1, depth))
                                walls = (
                                    [(x0, y) for y in range(0, depth + 1)]
                                    + [(x, depth) for x in range(x0 + 1, x1)]
                                    + [(x1, y) for y in range(depth, -1, -1)]
                                )
                                interior = [(x, y) for x in range(x0 + 1, x1) for y in range(0, depth)]
                                consider_candidate(walls, interior, span - 2, f"OKRAJOVÁ U-BUBLINA {span}x{depth}")

                    # Dolní hrana y=H-1
                    y_in = H - 1 - depth
                    if y_in >= 0:
                        for x0 in (ax, ax - span + 1):
                            x1 = x0 + span - 1
                            if 0 <= x0 and x1 < W and ("B", x0, x1, depth) not in seen_u:
                                seen_u.add(("B", x0, x1, depth))
                                walls = (
                                    [(x0, y) for y in range(H - 1, y_in - 1, -1)]
                                    + [(x, y_in) for x in range(x0 + 1, x1)]
                                    + [(x1, y) for y in range(y_in, H)]
                                )
                                interior = [(x, y) for x in range(x0 + 1, x1) for y in range(y_in + 1, H)]
                                consider_candidate(walls, interior, span - 2, f"OKRAJOVÁ U-BUBLINA {span}x{depth}")

        # --- TYP C: VELKÉ STŘEDOVÉ OKRUHY (6x6 až 12x12) + ZÁLOŽNÍ MENŠÍ (4x4 až 5x5) ---
        anchors = list(my_cells)
        if len(anchors) > 70:
            anchors = anchors[:: max(1, len(anchors) // 70)]

        seen_rects: Set[Tuple[int, int, int, int]] = set()
        for ax, ay in anchors:
            for rw in range(4, 13):
                for rh in range(4, 13):
                    for x0 in (ax, ax - rw + 1):
                        for y0 in (ay, ay - rh + 1):
                            if x0 < 0 or y0 < 0 or x0 + rw > W or y0 + rh > H:
                                continue
                            if (x0, y0, rw, rh) in seen_rects:
                                continue
                            seen_rects.add((x0, y0, rw, rh))

                            walls = (
                                [(x, y0) for x in range(x0, x0 + rw)]
                                + [(x0 + rw - 1, y) for y in range(y0 + 1, y0 + rh)]
                                + [(x, y0 + rh - 1) for x in range(x0 + rw - 2, x0 - 1, -1)]
                                + [(x0, y) for y in range(y0 + rh - 2, y0, -1)]
                            )
                            interior = [
                                (x, y) for x in range(x0 + 1, x0 + rw - 1)
                                for y in range(y0 + 1, y0 + rh - 1)
                            ]
                            is_big_ring = (rw >= 6 and rh >= 6)
                            label = f"MEGA-OKRUH {rw}x{rh}" if is_big_ring else f"OKRUH {rw}x{rh}"
                            consider_candidate(
                                walls,
                                interior,
                                trigger_count_after=(1 if is_big_ring else 0),
                                label=label,
                                keep_open_gate=is_big_ring,
                            )

        return best_plan

    def _find_shark_assault_move(self, my_cells: Set[Coord]) -> Optional[Coord]:
        """Útočný režim: přebírá cizí kostky s >= 3 vlastními sousedy (dominový efekt)."""
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

    def _pick_trigger_move_for_bubbles(
        self, my_cells: Set[Coord], bubbles: List[SealedBubble]
    ) -> Optional[Tuple[Coord, SealedBubble]]:
        """Vybere dosažitelnou spouštěcí kostku z největší uložené bubliny."""
        for bubble in bubbles:  # Již seřazeno od největší po nejmenší
            reachable = [
                p for p in bubble.trigger_cells
                if self._is_free(p) and self._count_own_neighbors(p, my_cells) >= 1
            ]
            if reachable:
                # Preferujeme kostku s více vlastními sousedy pro plynulý postup podél okraje
                reachable.sort(key=lambda p: self._count_own_neighbors(p, my_cells), reverse=True)
                return reachable[0], bubble
        return None

    def _choose_next_move_unlocked(self) -> Optional[Tuple[Coord, bool, str]]:
        my_cells = self._my_cells_unlocked()
        active_enemies = self._active_enemy_set()
        rem_sec = self._remaining_round_seconds()
        sec_per_move = self._effective_seconds_per_move()

        # 1. Startovní kostka
        if not my_cells:
            self._clear_plan_unlocked()
            for margin in (4, 1, 0):
                for y in range(margin, self.state.height - margin):
                    for x in range(margin, self.state.width - margin):
                        if self._is_free((x, y)):
                            return (x, y), True, "START"
            return None

        # 2. Analýza všech uložených velkých bublin a otevřených bran
        safe_bubbles, threatened_bubbles = self._detect_sealed_bubbles(my_cells, active_enemies)
        open_rings = self._detect_open_gate_rings(my_cells, active_enemies)

        all_banked_cells: Set[Coord] = set()
        for b in safe_bubbles + threatened_bubbles:
            all_banked_cells |= b.cells

        total_banked_value = sum(b.value for b in safe_bubbles) + sum(r.interior_value for r in open_rings)
        total_trigger_moves = sum(len(b.trigger_cells) for b in safe_bubbles) + len(open_rings)
        time_needed_to_pop = total_trigger_moves * sec_per_move + ENDGAME_SAFETY_BUFFER_SEC

        # 2a. Okamžitá obrana: pokud soupeř tlačí na zeď bubliny nebo se blíží k otevřené bráně okruhu!
        if threatened_bubbles:
            pick = self._pick_trigger_move_for_bubbles(my_cells, threatened_bubbles)
            if pick is not None:
                pos, b = pick
                self._clear_plan_unlocked()
                return pos, False, f"BUBLINA-OBRANA (+{b.value})"

        for ring in open_rings:
            if ring.enemy_distance <= 3:
                self._clear_plan_unlocked()
                return ring.gate, False, f"BRÁNA-ZAVŘÍT (+{ring.interior_value})"

        # 2b. ČASOVÝ SPOUŠTĚČ: Víme, kolik zbývá času -> včas začneme velké bubliny vyplňovat!
        if total_trigger_moves > 0 and rem_sec is not None and rem_sec <= time_needed_to_pop:
            self._clear_plan_unlocked()
            # Rozhodneme, jestli je výhodnější prasknout největší okrajovou bublinu nebo středový okruh
            best_bubble_pick = self._pick_trigger_move_for_bubbles(my_cells, safe_bubbles)
            best_ring = open_rings[0] if open_rings else None

            if best_bubble_pick and best_ring:
                b_pos, b_obj = best_bubble_pick
                if best_ring.interior_value >= b_obj.value:
                    return best_ring.gate, False, f"FINÁLE-BRÁNA (+{best_ring.interior_value}, zbývá {rem_sec:.0f}s)"
                return b_pos, False, f"FINÁLE-BUBLINA (+{b_obj.value}, zbývá {rem_sec:.0f}s)"
            elif best_ring:
                return best_ring.gate, False, f"FINÁLE-BRÁNA (+{best_ring.interior_value}, zbývá {rem_sec:.0f}s)"
            elif best_bubble_pick:
                b_pos, b_obj = best_bubble_pick
                return b_pos, False, f"FINÁLE-BUBLINA (+{b_obj.value}, zbývá {rem_sec:.0f}s)"

        # Periodický přehled o stavu banky v logu
        now_mono = time.monotonic()
        if total_banked_value > 0 and now_mono - self.state.last_status_log_mono >= 18.0:
            self.state.last_status_log_mono = now_mono
            rem_txt = f"{rem_sec:.0f}s" if rem_sec is not None else "?"
            self.log(
                "BUBLINA-BANKA",
                f"Uloženo ~{total_banked_value} polí v {len(safe_bubbles) + len(open_rings)} bublinách "
                f"(vyplnění zabere ~{time_needed_to_pop:.0f}s, do konce kola zbývá {rem_txt})"
            )

        # 3. Pokračování ve stavbě rozpracované velké bubliny
        if self.state.plan_active and self.state.plan_walls:
            enemy_on_wall = any(
                self.state.cells.get(p, "") not in ("", self.state.confirmed_nick)
                for p in self.state.plan_walls
            )
            missing_walls = [p for p in self.state.plan_walls if self._is_free(p)]

            # U velkého středového okruhu záměrně necháme poslední 1 kostku jako bránu (pokud nehrozí nepřítel)
            is_central_ring = "MEGA-OKRUH" in self.state.plan_label
            if not missing_walls or (is_central_ring and len(missing_walls) == 1):
                self.log(
                    "BUBLINA-HOTOVO",
                    f"{self.state.plan_label} postavena! Rezerva (~{self.state.plan_expected_gain} polí) uložena na konec."
                )
                self._clear_plan_unlocked()
            elif enemy_on_wall:
                self.log("BUBLINA-PLÁN", "Soupeř narušil stavbu bubliny, hledám novou velkou oblast.")
                self._clear_plan_unlocked()
            else:
                # Kontrola, jestli ještě stihneme bublinu dostavět i vybrat před koncem kola
                if rem_sec is not None:
                    needed = (len(missing_walls) + total_trigger_moves + 4) * sec_per_move + ENDGAME_SAFETY_BUFFER_SEC
                    if needed > rem_sec:
                        self.log("BUBLINA-PLÁN", "Málo času na dokončení velké stěny -> přecházím na menší/finále.")
                        self._clear_plan_unlocked()

                if self.state.plan_active:
                    reachable = [p for p in missing_walls if self._count_own_neighbors(p, my_cells) >= 1]
                    if reachable:
                        chosen = self._pick_defensive_wall_step(reachable, active_enemies)
                        return chosen, False, self.state.plan_label
                    else:
                        self._clear_plan_unlocked()

        # 4. Naplánování nové velké bubliny (Rohová L -> Okrajová U -> Velký středový okruh)
        new_plan = self._find_best_macro_bubble_plan(my_cells, all_banked_cells, total_trigger_moves)
        if new_plan is not None:
            walls, gate, label, expected_gain = new_plan
            missing = [p for p in walls if self._is_free(p)]
            reachable = [p for p in missing if self._count_own_neighbors(p, my_cells) >= 1]
            if reachable:
                self.state.plan_walls = walls
                self.state.plan_gate = gate
                self.state.plan_label = label
                self.state.plan_expected_gain = expected_gain
                self.state.plan_start_owned = len(my_cells)
                self.state.plan_active = True
                self.log(
                    "BUBLINA-PLÁN",
                    f"Zahajuji {label}: {len(missing)} tahů zdi -> zamkne ~{expected_gain} polí!"
                )
                chosen = self._pick_defensive_wall_step(reachable, active_enemies)
                return chosen, False, label

        # 5. Útočný dominový režim (krádež cizích kostek s >= 3 sousedy)
        shark_move = self._find_shark_assault_move(my_cells)
        if shark_move is not None:
            return shark_move, False, "ŽRALOK-ÚTOK"

        # 6. Expanze směrem k volnému prostoru / k okrajům mapy (nevyplňujeme uloženou banku!)
        best_step: Optional[Coord] = None
        best_step_score = -1.0
        my_nick = self.state.confirmed_nick

        for mx, my in my_cells:
            for nb in self._neighbors(mx, my):
                if self._is_free(nb) and nb not in all_banked_cells:
                    open_nb = sum(
                        1 for n2 in self._neighbors(nb[0], nb[1])
                        if self._is_free(n2) and n2 not in all_banked_cells
                    )
                    steal_setup = 0.0
                    sim_my = my_cells | {nb}
                    for n2 in self._neighbors(nb[0], nb[1]):
                        n2_owner = self.state.cells.get(n2, "")
                        if n2_owner not in ("", my_nick) and self._count_own_neighbors(n2, sim_my) >= 3:
                            steal_setup += 4.5

                    score = open_nb + steal_setup
                    if score > best_step_score:
                        best_step_score = score
                        best_step = nb

        if best_step is not None:
            return best_step, False, "EXPANZE"

        # 7. Pokud už na mapě není kam expandovat, začneme vybírat uložené bubliny
        if open_rings:
            return open_rings[0].gate, False, f"SKLIZEŇ-BRÁNA (+{open_rings[0].interior_value})"
        if safe_bubbles:
            pick = self._pick_trigger_move_for_bubbles(my_cells, safe_bubbles)
            if pick is not None:
                pos, b = pick
                return pos, False, f"SKLIZEŇ-BUBLINA (+{b.value})"

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
    parser = argparse.ArgumentParser(description="WS Aréna - makro-bubliny a časované finále")
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