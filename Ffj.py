from __future__ import annotations
import json
import sys
import time
import threading
import random
import logging
import math
import re
from collections import defaultdict, deque
from datetime import datetime
from urllib.parse import urlparse, parse_qs
from typing import Any, Dict, Tuple, Optional, List, Union

import pytz
import requests
import websocket
from rich.console import Console, Group
from rich.table import Table
from rich.panel import Panel
from rich.live import Live
from rich.align import Align
from rich.rule import Rule
from rich.text import Text
from rich import box
from rich.layout import Layout

# -------------------- CONFIG & GLOBALS --------------------
console = Console()
tz = pytz.timezone("Asia/Ho_Chi_Minh")

logger = logging.getLogger("escape_vip_ai_rebuild_v50")
logger.setLevel(logging.INFO)
logger.addHandler(logging.FileHandler("escape_vip_ai_rebuild_v50.log", encoding="utf-8"))

BET_API_URL = "https://api.escapemaster.net/escape_game/bet"
WS_URL = "wss://api.escapemaster.net/escape_master/ws"
WALLET_API_URL = "https://wallet.3games.io/api/wallet/user_asset"

HTTP = requests.Session()
try:
    from requests.adapters import HTTPAdapter
    from urllib3.util.retry import Retry
    adapter = HTTPAdapter(
        pool_connections=20, pool_maxsize=50,
        max_retries=Retry(total=3, backoff_factor=0.2,
                          status_forcelist=(500, 502, 503, 504))
    )
    HTTP.mount("https://", adapter)
    HTTP.mount("http://", adapter)
except Exception:
    pass

ROOM_NAMES = {
    1: "📦 Nhà kho", 2: "🪑 Phòng họp", 3: "👔 Phòng giám đốc", 4: "💬 Phòng trò chuyện",
    5: "🎥 Phòng giám sát", 6: "🏢 Văn phòng", 7: "💰 Phòng tài vụ", 8: "👥 Phòng nhân sự"
}
ROOM_ORDER = [1, 2, 3, 4, 5, 6, 7, 8]

USER_ID: Optional[int] = None
SECRET_KEY: Optional[str] = None
issue_id: Optional[int] = None
issue_start_ts: Optional[float] = None
count_down: Optional[int] = None
killed_room: Optional[int] = None
round_index: int = 0

room_state: Dict[int, Dict[str, Any]] = {r: {"players": 0, "bet": 0} for r in ROOM_ORDER}
room_stats: Dict[int, Dict[str, Any]] = {
    r: {"kills": 0, "survives": 0, "last_kill_round": None, "last_players": 0, "last_bet": 0, "historical_bpp": deque(maxlen=50)} 
    for r in ROOM_ORDER
}

predicted_room: Optional[int] = None
last_killed_room: Optional[int] = None
prediction_locked: bool = False

game_kill_history: deque = deque(maxlen=50)
game_kill_pattern_tracker: Dict[str, Any] = {
    "kill_counts": defaultdict(int),
    "kill_seq": deque(maxlen=10),
    "last_kill_ts": time.time(),
    "consecutive_kills": defaultdict(int),
    "volatility_index": 0.5,
    "ml_confidence": 0.0,
    "market_regime": "NORMAL",
}

# V5.0: Advanced tracking variables
ml_confidence: float = 0.0
volatility_index: float = 0.5
trend_direction: str = "NEUTRAL"
correlation_matrix: Dict[int, Dict[int, float]] = {}
performance_score: float = 0.0
kelly_percentage: float = 0.15
consecutive_kill_streak: Dict[int, int] = defaultdict(int)

current_build: Optional[float] = None
current_usdt: Optional[float] = None
current_world: Optional[float] = None
last_balance_ts: Optional[float] = None
last_balance_val: Optional[float] = None
starting_balance: Optional[float] = None
cumulative_profit: float = 0.0

win_streak: int = 0
lose_streak: int = 0
max_win_streak: int = 0
max_lose_streak: int = 0

auto_bet_enabled: bool = True
base_bet: float = 1.0
multiplier: float = 2.0
current_bet: Optional[float] = None
run_mode: str = "AUTO"

bet_rounds_before_skip: int = 0
_rounds_placed_since_skip: int = 0
skip_next_round_flag: bool = False

bet_history: deque = deque(maxlen=500)
bet_sent_for_issue: set = set()

pause_after_losses: int = 0
_skip_rounds_remaining: int = 0
profit_target: Optional[float] = None
stop_when_profit_reached: bool = False
stop_loss_target: Optional[float] = None
stop_when_loss_reached: bool = False
stop_flag: bool = False

ui_state: str = "IDLE"
analysis_start_ts: Optional[float] = None
analysis_blur: bool = False
last_msg_ts: float = time.time()
last_balance_fetch_ts: float = 0.0
BALANCE_POLL_INTERVAL: float = 4.0
_ws: Dict[str, Any] = {"ws": None}

SELECTION_CONFIG = {
    "max_bet_allowed": float("inf"),
    "max_players_allowed": 9999,
    "avoid_last_kill": True,
    "max_recent_kills": 3,
    "min_survive_rate": 0.55,
    "bet_management_strategy": "MARTINGALE",
    "bpp_trap_low": 500.0,
    "bpp_trap_high": 4000.0,
}

SELECTION_MODES = {
    "DEVILMODE": "SUPERIOR DEVIL - V5.0 ML ENHANCED"
}
settings = {"algo": "DEVILMODE"}

_spinner = ["🌀", "🌐", "🔷", "🌀", "🌐", "🔷"]
_num_re = re.compile(r"-?\d+[\d,]*\.?\d*")

MAIN_COLOR = "blue"
ACCENT_COLOR = "dark_blue"
TEXT_COLOR = "bold white"
SUCCESS_COLOR = "bold #00ff00"
FAILURE_COLOR = "bold #ff0000"
PENDING_COLOR = "bold #add8e6"
GOLD_COLOR = "bold #ffd700"

# -------------------- UTILITIES --------------------

def log_debug(msg: str) -> None:
    try:
        logger.debug(msg)
    except Exception:
        pass

def _parse_number(x: Any) -> Optional[float]:
    if x is None:
        return None
    if isinstance(x, (int, float)):
        return float(x)
    s = str(x)
    m = _num_re.search(s)
    if not m:
        return None
    token = m.group(0).replace(",", "")
    try:
        return float(token)
    except Exception:
        return None

def human_ts() -> str:
    return datetime.now(tz).strftime("%Y-%m-%d %H:%M:%S")

def safe_input(prompt: str, default: Any = None, cast: Optional[type] = None) -> Any:
    try:
        s = input(prompt).strip()
    except EOFError:
        return default
    if s == "":
        return default
    if cast:
        try:
            return cast(s)
        except Exception:
            return default
    return s

def add_notification(message: str, level: str = "INFO"):
    logger.info(f"[{level}] {message}")

# -------------------- BALANCE PARSING & FETCH --------------------

def _parse_balance_from_json(j: Dict[str, Any]) -> Tuple[Optional[float], Optional[float], Optional[float]]:
    if not isinstance(j, dict):
        return None, None, None
    build = None
    world = None
    usdt = None
    data = j.get("data") if isinstance(j.get("data"), dict) else j
    if isinstance(data, dict):
        cwallet = data.get("cwallet") if isinstance(data.get("cwallet"), dict) else None
        if cwallet:
            for key in ("ctoken_contribute", "ctoken", "build", "balance", "amount"):
                if key in cwallet and build is None:
                    build = _parse_number(cwallet.get(key))
        for k in ("build", "ctoken", "ctoken_contribute"):
            if build is None and k in data:
                build = _parse_number(data.get(k))
        for k in ("usdt", "kusdt", "usdt_balance"):
            if usdt is None and k in data:
                usdt = _parse_number(data.get(k))
        for k in ("world", "xworld"):
            if world is None and k in data:
                world = _parse_number(data.get(k))
    found = []
    def walk(o: Any, path=""):
        if isinstance(o, dict):
            for kk, vv in o.items():
                nk = (path + "." + str(kk)).strip(".")
                if isinstance(vv, (dict, list)):
                    walk(vv, nk)
                else:
                    n = _parse_number(vv)
                    if n is not None:
                        found.append((nk.lower(), n))
        elif isinstance(o, list):
            for idx, it in enumerate(o):
                walk(it, f"{path}[{idx}]")
    walk(j)
    for k, n in found:
        if build is None and any(x in k for x in ("ctoken", "build", "contribute", "balance")):
            build = n
        if usdt is None and "usdt" in k:
            usdt = n
        if world is None and any(x in k for x in ("world", "xworld")):
            world = n
    return build, world, usdt

def balance_headers_for(uid: Optional[int] = None, secret: Optional[str] = None) -> Dict[str, str]:
    h = {
        "accept": "*/*",
        "accept-language": "vi,en;q=0.9",
        "cache-control": "no-cache",
        "country-code": "vn",
        "origin": "https://xworld.info",
        "pragma": "no-cache",
        "referer": "https://xworld.info/",
        "user-agent": "Mozilla/5.0 (Linux; Android 6.0; Nexus 5) AppleWebKit/537.36 "
                      "(KHTML, like Gecko) Chrome/137.0.0.0 Mobile Safari/537.36",
        "user-login": "login_v2",
        "xb-language": "vi-VN",
    }
    if uid is not None:
        h["user-id"] = str(uid)
    if secret:
        h["user-secret-key"] = str(secret)
    return h

def fetch_balances_3games(retries: int = 2, timeout: int = 6, params: Optional[Dict[str, str]] = None, uid: Optional[int] = None, secret: Optional[str] = None) -> Tuple[Optional[float], Optional[float], Optional[float]]:
    global current_build, current_usdt, current_world, last_balance_ts, starting_balance, last_balance_val, cumulative_profit
    uid = uid or USER_ID
    secret = secret or SECRET_KEY
    payload = {"user_id": int(uid) if uid is not None else None, "source": "home"}
    attempt = 0
    while attempt <= retries:
        attempt += 1
        try:
            r = HTTP.post(WALLET_API_URL, json=payload, headers=balance_headers_for(uid, secret), timeout=timeout)
            r.raise_for_status()
            j = r.json()
            build, world, usdt = _parse_balance_from_json(j)
            if build is not None:
                if last_balance_val is None:
                    starting_balance = build
                    last_balance_val = build
                else:
                    delta = float(build) - float(last_balance_val)
                    if abs(delta) > 0.000001:
                        cumulative_profit += delta
                        last_balance_val = build
                current_build = build
            if usdt is not None:
                current_usdt = usdt
            if world is not None:
                current_world = world
            last_balance_ts = time.time()
            return current_build, current_world, current_usdt
        except Exception as e:
            log_debug(f"wallet fetch attempt {attempt} error: {e}")
            time.sleep(min(0.6 * attempt, 2))
    return current_build, current_world, current_usdt

# -------------------- SUPERIOR DEVIL V4 SELECTION (GIỮ NGUYÊN) --------------------

def _room_features(rid: int) -> Dict[str, float]:
    global game_kill_history, round_index, room_state, room_stats, last_killed_room, game_kill_pattern_tracker
    
    st = room_state.get(rid, {})
    stats = room_stats.get(rid, {})
    
    players = float(st.get("players", 0))
    bet = float(st.get("bet", 0))
    bet_per_player = (bet / players) if players > 0 else 0.0

    kill_count = float(stats.get("kills", 0))
    survive_count = float(stats.get("survives", 0))
    
    total_rounds = kill_count + survive_count
    kill_rate = (kill_count + 1.0) / (total_rounds + 2.0) if total_rounds > 0 else 0.5
    survive_score = 1.0 - kill_rate

    all_players = sum(r.get("players", 0) for r in room_state.values())
    all_bet = sum(r.get("bet", 0) for r in room_state.values())
    
    players_norm = players / max(1.0, all_players)
    bet_norm = bet / max(1.0, all_bet)
    contrarian_score = 1.0 - (players_norm + bet_norm) / 2.0 

    recent_pen = 0.0
    for i, rec in enumerate(reversed(list(bet_history))):
        if i >= 10: break
        if rec.get("room") == rid and rec.get("result") == "Thua":
            recent_pen += 0.15 * (1.0 / (i + 1))
    
    last_pen = 0.0
    if last_killed_room == rid and SELECTION_CONFIG.get("avoid_last_kill", True):
        last_pen = 0.45 

    total_rounds_stats = sum(r['kills'] + r['survives'] for r in room_stats.values())
    safety_score = 0.5
    if total_rounds_stats > 0:
        safety_score = 1.0 - (kill_count / max(1, total_rounds_stats / 8))

    last_kill_round = stats.get("last_kill_round")
    cold_room_score = 0.0
    min_rounds_safe = 10.0
    if last_kill_round is None:
        cold_room_score = 1.0
    else:
        delta = round_index - last_kill_round
        cold_room_score = min(1.0, delta / min_rounds_safe)

    recent_kills = game_kill_history.count(rid)
    freq_penalty = min(1.0, recent_kills / SELECTION_CONFIG.get("max_recent_kills", 3.0))

    bpp_score = 0.0
    min_h = SELECTION_CONFIG.get("bpp_trap_low", 500.0)
    max_h = SELECTION_CONFIG.get("bpp_trap_high", 4000.0)
    
    if bet_per_player < min_h:
        bpp_score = max(0.0, bet_per_player / min_h)
    elif bet_per_player > max_h:
        bpp_score = max(0.0, 1.0 - (bet_per_player - max_h) / max_h) 
    else:
        bpp_score = 1.0
        
    historical_bpp_deq = stats.get("historical_bpp")
    bpp_deviation_penalty = 0.0
    if historical_bpp_deq and len(historical_bpp_deq) >= 5:
        avg_bpp = sum(historical_bpp_deq) / len(historical_bpp_deq)
        if avg_bpp > 100 and bet_per_player > avg_bpp * 1.5:
             bpp_deviation_penalty = min(1.0, (bet_per_player - avg_bpp * 1.5) / avg_bpp)
        elif avg_bpp > 100 and bet_per_player < avg_bpp * 0.5:
             bpp_deviation_penalty = min(1.0, (avg_bpp * 0.5 - bet_per_player) / avg_bpp)
             
    pattern_penalty = 0.0
    kill_seq = game_kill_pattern_tracker.get("kill_seq", deque())
    
    if len(kill_seq) >= 3:
        if rid == kill_seq[-3] and rid != kill_seq[-2]:
             pattern_penalty = max(pattern_penalty, 0.6)
        if len(kill_seq) == 5 and all(r == rid for r in kill_seq):
             pattern_penalty = max(pattern_penalty, 0.9)

    avg_bpp_all = all_bet / max(1.0, all_players)
    bpp_relative_score = 1.0 - abs(bet_per_player - avg_bpp_all) / max(1.0, avg_bpp_all * 2)
        
    return {
        "players": players, "bet": bet, "bet_per_player": bet_per_player,
        "players_norm": players_norm, "bet_norm": bet_norm,
        "contrarian_score": contrarian_score,
        "kill_rate": kill_rate, "survive_score": survive_score,
        "safety_score": safety_score,
        "recent_pen": recent_pen, "last_pen": last_pen,
        "cold_room_score": cold_room_score,
        "freq_penalty": freq_penalty,
        "bpp_score": bpp_score,
        "bpp_deviation_penalty": bpp_deviation_penalty,
        "pattern_penalty": pattern_penalty,
        "bpp_relative_score": bpp_relative_score,
    }

def choose_room_devilmode() -> Tuple[int, str]:
    global game_kill_history, round_index, room_state, room_stats, last_killed_room
    
    log_debug("--- SUPERIOR DEVIL V4 PRE-COMPUTATION ---")
    features = {}
    
    all_players = sum(r.get("players", 0) for r in room_state.values())
    all_bet = sum(r.get("bet", 0) for r in room_state.values())
    avg_players = all_players / max(1, len(ROOM_ORDER))
    avg_bet = all_bet / max(1, len(ROOM_ORDER))
    avg_bpp_all = all_bet / max(1, all_players)

    player_ranks_sorted = sorted(ROOM_ORDER, key=lambda r: room_state[r].get("players", 0), reverse=True)
    bet_ranks_sorted = sorted(ROOM_ORDER, key=lambda r: room_state[r].get("bet", 0), reverse=True)
    
    recent_10_kills = list(game_kill_history)[-10:]
    low_zone_kills = sum(1 for k in recent_10_kills if k in [1, 2, 3, 4])
    high_zone_kills = sum(1 for k in recent_10_kills if k in [5, 6, 7, 8])

    market_state = "STABLE"
    max_players_in_room = 0
    if all_players > 0:
        max_players_in_room = max(r.get("players", 0) for r in room_state.values())
        player_concentration = max_players_in_room / all_players
        if player_concentration > 0.35:
            market_state = "CONCENTRATED"
        elif player_concentration < 0.2 and avg_bpp_all < 1000:
             market_state = "FEARFUL"
    log_debug(f"V4 Market State: {market_state}")

    for r in ROOM_ORDER:
        f = _room_features(r)
        f['player_rank'] = player_ranks_sorted.index(r) + 1
        f['bet_rank'] = bet_ranks_sorted.index(r) + 1
        
        whale_bpp_threshold = max(3000.0, avg_bpp_all * 5.0)
        f['whale_trap_score'] = 0.0
        if 0 < f['players'] <= 3 and f['bet_per_player'] > whale_bpp_threshold:
            f['whale_trap_score'] = 1.0
        
        f['decoy_trap_score'] = 1.0 if f['player_rank'] in [2, 3] else 0.0
        
        f['zone_penalty'] = 0.0
        my_zone = 'low' if r <= 4 else 'high'
        if my_zone == 'low' and low_zone_kills > high_zone_kills:
            f['zone_penalty'] = min(1.0, (low_zone_kills - high_zone_kills) / 5.0)
        elif my_zone == 'high' and high_zone_kills > low_zone_kills:
            f['zone_penalty'] = min(1.0, (high_zone_kills - low_zone_kills) / 5.0)

        features[r] = f

    filtered_cand = []
    for r in ROOM_ORDER:
        f = features[r]
        if SELECTION_CONFIG.get("avoid_last_kill", True) and last_killed_room == r:
            log_debug(f"Filter R{r}: Last killed")
            continue
        if f["survive_score"] < SELECTION_CONFIG.get("min_survive_rate", 0.55):
            log_debug(f"Filter R{r}: Low survive rate")
            continue
        if (f["players"] > avg_players * 1.8) and (f["bet"] > avg_bet * 1.8):
            log_debug(f"Filter R{r}: Overcrowded")
            continue
        if f["freq_penalty"] > 0.8:
            log_debug(f"Filter R{r}: High kill freq")
            continue
        if f["bpp_score"] < 0.3:
            log_debug(f"Filter R{r}: Bad BPP")
            continue
        if f["bpp_deviation_penalty"] > 0.5:
            log_debug(f"Filter R{r}: BPP deviation")
            continue
        if f["pattern_penalty"] > 0.5:
            log_debug(f"Filter R{r}: Pattern penalty")
            continue
        if f['whale_trap_score'] > 0.5:
            log_debug(f"Filter R{r}: Whale trap")
            continue
        if f['zone_penalty'] > 0.8:
            log_debug(f"Filter R{r}: Hot zone")
            continue
        filtered_cand.append(r)

    if not filtered_cand:
        log_debug("All rooms filtered. Fallback")
        fallback_scores = {r: _room_features(r)["kill_rate"] for r in ROOM_ORDER if r != last_killed_room}
        if not fallback_scores:
             fallback_scores = {r: _room_features(r)["kill_rate"] for r in ROOM_ORDER}
        best_room = min(fallback_scores.items(), key=lambda x: x[1])[0]
        return best_room, "FALLBACK"

    weights = {
        "safety_contrarian": 1.5, "safety_bpp_health": 1.2, "safety_cold_room": 1.0,
        "safety_survive_hist": 0.5, "safety_bpp_relative": 0.3,
        "trap_decoy": 2.5, "trap_whale": 2.5, "trap_bpp_dev": 1.5,
        "trap_freq": 1.5, "trap_pattern": 1.2, "trap_zone": 1.0, "trap_last_kill": 0.8,
    }
    
    if market_state == "CONCENTRATED":
        weights["trap_decoy"] *= 1.5
        weights["trap_bpp_dev"] *= 1.3
    elif market_state == "FEARFUL":
        weights["safety_contrarian"] *= 1.4
        weights["safety_cold_room"] *= 1.2

    agg_scores = {r: 0.0 for r in filtered_cand}
    log_debug(f"Scoring (Candidates: {filtered_cand})")
    
    for r in filtered_cand:
        f = features[r]
        safety_score = 0.0
        safety_score += weights["safety_contrarian"] * f["contrarian_score"]
        safety_score += weights["safety_bpp_health"] * f["bpp_score"]
        safety_score += weights["safety_cold_room"] * f["cold_room_score"]
        safety_score += weights["safety_survive_hist"] * f["survive_score"]
        safety_score += weights["safety_bpp_relative"] * f["bpp_relative_score"]
        
        trap_score = 0.0
        trap_score += weights["trap_decoy"] * f["decoy_trap_score"]
        trap_score += weights["trap_whale"] * f["whale_trap_score"]
        trap_score += weights["trap_bpp_dev"] * f["bpp_deviation_penalty"]
        trap_score += weights["trap_freq"] * f["freq_penalty"]
        trap_score += weights["trap_pattern"] * f["pattern_penalty"]
        trap_score += weights["trap_zone"] * f["zone_penalty"]
        trap_score += weights["trap_last_kill"] * f["last_pen"]

        final_score = safety_score - trap_score
        agg_scores[r] = final_score
        log_debug(f"Room {r}: Safety={safety_score:.3f}, Trap={trap_score:.3f} -> FINAL={final_score:.3f}")

    ranked = sorted(agg_scores.items(), key=lambda kv: (-kv[1], kv[0]))
    
    if len(ranked) < 2:
        best_room = ranked[0][0]
        log_debug(f"FINAL: R{best_room}")
        return best_room, "V4_SINGLE"

    best_cand = ranked[0]
    second_cand = ranked[1]
    third_cand = ranked[2] if len(ranked) > 2 else None

    score_diff_percent = (best_cand[1] - second_cand[1]) / max(0.01, abs(best_cand[1]))
    
    if score_diff_percent < 0.15:
        log_debug(f"Tsunami: Close scores R{best_cand[0]} and R{second_cand[0]}")
        f1 = features[best_cand[0]]
        f2 = features[second_cand[0]]
        zone1 = 'low' if best_cand[0] <= 4 else 'high'
        zone2 = 'low' if second_cand[0] <= 4 else 'high'
        player_diff_percent = abs(f1['players'] - f2['players']) / max(1, (f1['players'] + f2['players']) / 2)
        
        if zone1 == zone2 and player_diff_percent < 0.4:
            log_debug(f"Split trap detected")
            if third_cand:
                f3 = features[third_cand[0]]
                zone3 = 'low' if third_cand[0] <= 4 else 'high'
                if zone3 != zone1 and third_cand[1] > max(0, best_cand[1] * 0.5):
                    log_debug(f"Pivot to R{third_cand[0]}")
                    return third_cand[0], "V4_PIVOT"

    log_debug(f"FINAL: R{best_cand[0]}")
    return best_cand[0], "V4"

# -------------------- BETTING HELPERS --------------------

def api_headers() -> Dict[str, str]:
    return {
        "content-type": "application/json",
        "user-agent": "Mozilla/5.0",
        "user-id": str(USER_ID) if USER_ID else "",
        "user-secret-key": SECRET_KEY if SECRET_KEY else ""
    }

def place_bet_http(issue: int, room_id: int, amount: float) -> dict:
    payload = {"asset_type": "BUILD", "user_id": USER_ID, "room_id": int(room_id), "bet_amount": float(amount)}
    try:
        r = HTTP.post(BET_API_URL, headers=api_headers(), json=payload, timeout=6)
        try:
            return r.json()
        except Exception:
            return {"raw": r.text, "http_status": r.status_code}
    except Exception as e:
        return {"error": str(e)}

def record_bet(issue: int, room_id: int, amount: float, resp: dict, algo_used: Optional[str] = None) -> dict:
    now = datetime.now(tz).strftime("%H:%M:%S")
    rec = {
        "issue": issue, "room": room_id, "amount": float(amount), 
        "time": now, "resp": resp, "result": "Đang", 
        "algo": algo_used, "delta": 0.0, "win_streak": win_streak, 
        "lose_streak": lose_streak,
        "killed_room_id": None
    }
    bet_history.append(rec)
    return rec

def place_bet_async(issue: int, room_id: int, amount: float, algo_used: Optional[str] = None) -> None:
    def worker():
        console.print(f"[{PENDING_COLOR}]Đang đặt {amount:,.4f} BUILD -> PHÒNG_{room_id} (v{issue}) — Thuật toán: {algo_used}[/]")
        time.sleep(random.uniform(0.02, 0.25))
        res = place_bet_http(issue_id, room_id, amount)
        rec = record_bet(issue_id, room_id, amount, res, algo_used=algo_used)
        
        if isinstance(res, dict) and (res.get("msg") == "ok" or res.get("code") == 0 or res.get("status") in ("ok", 1) or "success" in str(res).lower()):
            bet_sent_for_issue.add(issue_id)
            console.print(f"[{SUCCESS_COLOR}]✅ Đặt thành công {amount:,.4f} BUILD vào PHÒNG_{room_id} (v{issue_id}).[/]")
        else:
            console.print(f"[{FAILURE_COLOR}]❌ Đặt lỗi v{issue_id}: {res}[/]")
            
    threading.Thread(target=worker, daemon=True).start()

# -------------------- LOCK & AUTO-BET --------------------

def lock_prediction_if_needed(force: bool = False) -> None:
    global prediction_locked, predicted_room, ui_state, current_bet, _rounds_placed_since_skip, skip_next_round_flag, _skip_rounds_remaining, win_streak, lose_streak
    global current_build, auto_bet_enabled
    
    if stop_flag:
        return
    if prediction_locked and not force:
        return
    if issue_id is None:
        return
        
    prediction_locked = True
    ui_state = "PREDICTED"
    
    chosen, algo_used = choose_room_devilmode()
    predicted_room = chosen
    
    if _skip_rounds_remaining > 0:
        console.print(f"[{ACCENT_COLOR}]⏸️ Đang nghỉ sau khi thua... Còn lại {_skip_rounds_remaining} ván.[/]")
        _skip_rounds_remaining -= 1
        prediction_locked = True 
        return
        
    if run_mode == "AUTO" and not skip_next_round_flag:
        
        if not auto_bet_enabled:
            console.print(f"[{PENDING_COLOR}]ℹ️ AI DỰ ĐOÁN: PHÒNG {predicted_room} (Chế độ OFF - Không đặt cược)[/]")
            return

        bld, _, _ = fetch_balances_3games(params={"userId": str(USER_ID)} if USER_ID else None)
        if bld is None:
            console.print(f"[{ACCENT_COLOR}]⚠️ Không lấy được số dư trước khi đặt — bỏ qua đặt ván này.[/]")
            prediction_locked = False
            return
            
        if current_bet is None:
            current_bet = base_bet
        
        strategy = SELECTION_CONFIG.get("bet_management_strategy", "MARTINGALE")
        if strategy == "ANTI-MARTINGALE":
            if win_streak > 0:
                current_bet = base_bet + (base_bet * 0.1 * win_streak) 
            else:
                current_bet = base_bet
                
        if current_bet < base_bet:
            current_bet = base_bet

        amt = float(current_bet)
        
        if amt <= 0 or amt > current_build:
            console.print(f"[{FAILURE_COLOR}]⚠️ Số tiền đặt không hợp lệ ({amt:,.4f} > {current_build:,.4f}). Bỏ qua.[/]")
            prediction_locked = False
            return
        
        place_bet_async(issue_id, predicted_room, amt, algo_used=algo_used)
        _rounds_placed_since_skip += 1
        
        if bet_rounds_before_skip > 0 and _rounds_placed_since_skip >= bet_rounds_before_skip:
            skip_next_round_flag = True
            _rounds_placed_since_skip = 0
            
    elif skip_next_round_flag:
        console.print(f"[{ACCENT_COLOR}]⏸️ TẠM DỪNG THEO DÕI SÁT THỦ (Cấu hình SKIP: Chống soi)[/]")
        skip_next_round_flag = False
