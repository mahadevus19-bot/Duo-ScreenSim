"""Standalone anchor-day equity screener.

Run:
    python daily_anchor_screener.py
    python daily_anchor_screener.py --date 2026-07-28
    python daily_anchor_screener.py --limit 25  # quick smoke test

This script is intentionally standalone for reuse by another system. Edit the
API key and filter section below without touching TradeEdge runtime config.
"""

from __future__ import annotations

import argparse
import math
import os
import re
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from pathlib import Path
from typing import Any
from zoneinfo import ZoneInfo

import requests
from openpyxl import Workbook
from openpyxl.utils import get_column_letter
from openpyxl.styles import Alignment, Border, Font, PatternFill, Side


# =============================================================================
# API KEY SECTION - another system can edit this block
# =============================================================================
POLYGON_API_KEY = "lY6QCPwj45_gLpmgsMEXDhREerAUVgoE"  # Example: "YOUR_POLYGON_OR_MASSIVE_API_KEY"
ENV_API_KEY_NAME = ""
API_BASE_URL = "https://api.massive.com"


# =============================================================================
# FILTER SECTION - edit values here
# Use M/B/T notation for large numbers: "500M", "1B", "1T".
# =============================================================================
FILTERS = {
    "ANCHOR_DATE": "",              # Blank = today from 9:30 AM ET on trading days, otherwise last completed trading date
    "MCAP_MIN": "100B",
    "MCAP_MAX": "500B",
    "MIN_VOLUME": "1M",
    "MIN_PRICE": 2,
    "MIN_ATR10": 3,                
    "MIN_RSI14": 45,
    "MIN_MOMENTUM_SCORE": 60,
    "PPO>SIGNAL": False,
    "PPO_CROSS": False,
}

MAX_WORKERS = 30
# Keep enough history so EMA-based PPO/Signal are stable and match charting tools.
HISTORY_CALENDAR_DAYS = 520
HTTP_CONNECT_TIMEOUT = 6
HTTP_READ_TIMEOUT = 15
HTTP_RETRIES = 3
OUTPUT_DIR = Path("daily screener")
COLOR_ENABLED = not os.getenv("NO_COLOR")
COLORS = {
    "reset": "\033[0m",
    "bold": "\033[1m",
    "blue": "\033[94m",
    "cyan": "\033[96m",
    "green": "\033[92m",
    "yellow": "\033[93m",
    "red": "\033[91m",
    "magenta": "\033[95m",
}


FULL_MARKET_HOLIDAYS = {
    "2024-01-01", "2024-01-15", "2024-02-19", "2024-03-29", "2024-05-27",
    "2024-06-19", "2024-07-04", "2024-09-02", "2024-11-28", "2024-12-25",
    "2025-01-01", "2025-01-20", "2025-02-17", "2025-04-18", "2025-05-26",
    "2025-06-19", "2025-07-04", "2025-09-01", "2025-11-27", "2025-12-25",
    "2026-01-01", "2026-01-19", "2026-02-16", "2026-04-03", "2026-05-25",
    "2026-06-19", "2026-07-03", "2026-09-07", "2026-11-26", "2026-12-25",
    "2027-01-01", "2027-01-18", "2027-02-15", "2027-04-15", "2027-05-31",
    "2027-06-18", "2027-07-05", "2027-09-06", "2027-11-25", "2027-12-24",
}


@dataclass(frozen=True)
class ScreenerConfig:
    anchor_date: str
    anchor_note: str | None
    mcap_min: float
    mcap_max: float
    min_volume: float
    min_price: float
    min_atr10: float
    min_rsi14: float
    min_momentum_score: float
    require_ppo_gt_signal: bool
    require_ppo_cross: bool


def parse_large_number(value: Any) -> float:
    """Parse values like 2, 1M, 1.5B, 1T into raw numbers."""
    if isinstance(value, (int, float)):
        return float(value)
    raw = str(value).strip().replace(",", "").replace("$", "")
    if not raw:
        raise ValueError("Blank numeric filter value")
    match = re.fullmatch(r"([+-]?\d+(?:\.\d+)?)\s*([KkMmBbTt]?)", raw)
    if not match:
        raise ValueError(f"Invalid large number: {value!r}")
    number = float(match.group(1))
    suffix = match.group(2).upper()
    multiplier = {"": 1.0, "K": 1_000.0, "M": 1_000_000.0, "B": 1_000_000_000.0, "T": 1_000_000_000_000.0}[suffix]
    return number * multiplier


def format_large_number(value: float | None) -> str:
    if value is None or not math.isfinite(float(value)):
        return ""

    def trim_decimal(text: str) -> str:
        return text.rstrip("0").rstrip(".")

    value = float(value)
    abs_value = abs(value)
    if abs_value >= 1_000_000_000_000:
        return f"{trim_decimal(f'{value / 1_000_000_000_000:.2f}')}T"
    if abs_value >= 1_000_000_000:
        return f"{trim_decimal(f'{value / 1_000_000_000:.2f}')}B"
    if abs_value >= 1_000_000:
        return f"{trim_decimal(f'{value / 1_000_000:.2f}')}M"
    if abs_value >= 1_000:
        return f"{trim_decimal(f'{value / 1_000:.2f}')}K"
    return trim_decimal(f"{value:.2f}")


def format_filter_number(value: float) -> str:
    return str(int(value)) if float(value).is_integer() else f"{value:.2f}"


def parse_bool(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if value is None:
        return False
    return str(value).strip().lower() in {"1", "true", "yes", "y", "on"}


def color_text(value: Any, color: str) -> str:
    text = str(value)
    if not COLOR_ENABLED:
        return text
    return f"{COLORS[color]}{text}{COLORS['reset']}"


def load_api_key() -> str:
    if POLYGON_API_KEY.strip():
        return POLYGON_API_KEY.strip()
    env_value = os.getenv(ENV_API_KEY_NAME, "").strip()
    if env_value:
        return env_value
    env_file = Path(".env")
    if env_file.exists():
        for line in env_file.read_text(encoding="utf-8").splitlines():
            if line.startswith(f"{ENV_API_KEY_NAME}="):
                value = line.split("=", 1)[1].strip()
                if value:
                    return value
    raise RuntimeError(
        f"Missing API key. Set POLYGON_API_KEY in this file, environment variable {ENV_API_KEY_NAME}, or .env."
    )


def is_trading_day(day: date) -> bool:
    return day.weekday() < 5 and day.isoformat() not in FULL_MARKET_HOLIDAYS


def previous_trading_date(day: date) -> date:
    day -= timedelta(days=1)
    while not is_trading_day(day):
        day -= timedelta(days=1)
    return day


def default_anchor_date(now_et: datetime | None = None) -> str:
    now_et = now_et or datetime.now(ZoneInfo("America/New_York"))
    day = now_et.date()
    if is_trading_day(day) and (now_et.hour, now_et.minute) >= (9, 30):
        return day.isoformat()
    return previous_trading_date(day).isoformat()


def last_completed_trading_date() -> str:
    now_et = datetime.now(ZoneInfo("America/New_York"))
    return previous_trading_date(now_et.date()).isoformat()


def normalize_anchor_date(anchor: str) -> tuple[str, str | None]:
    requested = datetime.strptime(anchor, "%Y-%m-%d").date()
    if is_trading_day(requested):
        return requested.isoformat(), None
    resolved = previous_trading_date(requested)
    reason = "weekend day" if requested.weekday() >= 5 else "market holiday"
    note = (
        f"{requested.isoformat()} is a {reason}, running for previous trading day "
        f"{resolved.isoformat()}."
    )
    return resolved.isoformat(), note


def build_config(anchor_override: str | None = None) -> ScreenerConfig:
    anchor = anchor_override or str(FILTERS.get("ANCHOR_DATE") or "").strip() or default_anchor_date()
    normalized_anchor, anchor_note = normalize_anchor_date(anchor)
    return ScreenerConfig(
        anchor_date=normalized_anchor,
        anchor_note=anchor_note,
        mcap_min=parse_large_number(FILTERS["MCAP_MIN"]),
        mcap_max=parse_large_number(FILTERS["MCAP_MAX"]),
        min_volume=parse_large_number(FILTERS["MIN_VOLUME"]),
        min_price=float(FILTERS["MIN_PRICE"]),
        min_atr10=float(FILTERS["MIN_ATR10"]),
        min_rsi14=float(FILTERS["MIN_RSI14"]),
        min_momentum_score=float(FILTERS.get("MIN_MOMENTUM_SCORE", 60)),
        require_ppo_gt_signal=bool(FILTERS.get("PPO>SIGNAL", False)),
        require_ppo_cross=bool(FILTERS.get("PPO_CROSS", False)),
    )


def build_config_from_values(
    anchor_date: str | None = None,
    mcap_min: Any | None = None,
    mcap_max: Any | None = None,
    min_volume: Any | None = None,
    min_price: Any | None = None,
    min_atr10: Any | None = None,
    min_rsi14: Any | None = None,
    min_momentum_score: Any | None = None,
    require_ppo_gt_signal: Any | None = None,
    require_ppo_cross: Any | None = None,
    require_macd_gt_signal: Any | None = None,
    require_macd_cross: Any | None = None,
) -> ScreenerConfig:
    anchor = str(anchor_date or FILTERS.get("ANCHOR_DATE") or "").strip() or default_anchor_date()
    normalized_anchor, anchor_note = normalize_anchor_date(anchor)
    effective_ppo_gt_signal = require_ppo_gt_signal if require_ppo_gt_signal is not None else require_macd_gt_signal
    if effective_ppo_gt_signal is None:
        effective_ppo_gt_signal = FILTERS.get("PPO>SIGNAL", False)
    effective_ppo_cross = require_ppo_cross if require_ppo_cross is not None else require_macd_cross
    if effective_ppo_cross is None:
        effective_ppo_cross = FILTERS.get("PPO_CROSS", False)

    return ScreenerConfig(
        anchor_date=normalized_anchor,
        anchor_note=anchor_note,
        mcap_min=parse_large_number(FILTERS["MCAP_MIN"] if mcap_min is None else mcap_min),
        mcap_max=parse_large_number(FILTERS["MCAP_MAX"] if mcap_max is None else mcap_max),
        min_volume=parse_large_number(FILTERS["MIN_VOLUME"] if min_volume is None else min_volume),
        min_price=float(FILTERS["MIN_PRICE"] if min_price is None else min_price),
        min_atr10=float(FILTERS["MIN_ATR10"] if min_atr10 is None else min_atr10),
        min_rsi14=float(FILTERS["MIN_RSI14"] if min_rsi14 is None else min_rsi14),
        min_momentum_score=float(FILTERS.get("MIN_MOMENTUM_SCORE", 60) if min_momentum_score is None else min_momentum_score),
        require_ppo_gt_signal=parse_bool(effective_ppo_gt_signal),
        require_ppo_cross=parse_bool(effective_ppo_cross),
    )


class PolygonSession:
    def __init__(self, api_key: str):
        self.api_key = api_key
        self.session = requests.Session()

    def get_json(self, url: str, params: dict[str, Any] | None = None, retries: int = HTTP_RETRIES) -> dict[str, Any]:
        params = dict(params or {})
        params["apiKey"] = self.api_key
        for attempt in range(retries):
            try:
                response = self.session.get(url, params=params, timeout=(HTTP_CONNECT_TIMEOUT, HTTP_READ_TIMEOUT))
                if response.status_code in {429, 500, 502, 503, 504}:
                    time.sleep(min(2 ** attempt, 6))
                    continue
                if response.status_code != 200:
                    return {}
                return response.json() or {}
            except requests.RequestException:
                time.sleep(min(2 ** attempt, 6))
        return {}

    def fetch_grouped_daily(self, anchor_date: str) -> dict[str, dict[str, float]]:
        url = f"{API_BASE_URL}/v2/aggs/grouped/locale/us/market/stocks/{anchor_date}"
        payload = self.get_json(url, {"adjusted": "true"})
        out: dict[str, dict[str, float]] = {}
        for bar in payload.get("results") or []:
            ticker = bar.get("T")
            close = bar.get("c")
            if not ticker or close is None:
                continue
            out[str(ticker).upper()] = {
                "open": float(bar.get("o") or 0.0),
                "high": float(bar.get("h") or 0.0),
                "low": float(bar.get("l") or 0.0),
                "close": float(close),
                "volume": float(bar.get("v") or 0.0),
            }
        return out

    def fetch_reference(self, ticker: str, anchor_date: str) -> dict[str, Any]:
        url = f"{API_BASE_URL}/v3/reference/tickers/{ticker}"
        dated_reference = self.get_json(url, {"date": anchor_date}).get("results") or {}
        dated_shares = dated_reference.get("weighted_shares_outstanding") or dated_reference.get("share_class_shares_outstanding")
        has_dated_market_cap = isinstance(dated_shares, (int, float)) and dated_shares > 0
        has_dated_market_cap = has_dated_market_cap or isinstance(dated_reference.get("market_cap"), (int, float))
        if has_dated_market_cap:
            return dated_reference

        current_reference = self.get_json(url, {}).get("results") or {}
        if not dated_reference:
            return current_reference
        merged_reference = dict(current_reference)
        merged_reference.update({key: value for key, value in dated_reference.items() if value not in (None, "")})
        return merged_reference

    def fetch_daily_history(self, ticker: str, anchor_date: str) -> list[dict[str, float]]:
        end = datetime.strptime(anchor_date, "%Y-%m-%d").date()
        start = end - timedelta(days=HISTORY_CALENDAR_DAYS)
        url = f"{API_BASE_URL}/v2/aggs/ticker/{ticker}/range/1/day/{start.isoformat()}/{anchor_date}"
        payload = self.get_json(url, {"adjusted": "true", "sort": "asc", "limit": 50000})
        bars = []
        for bar in payload.get("results") or []:
            try:
                bars.append({
                    "open": float(bar["o"]),
                    "high": float(bar["h"]),
                    "low": float(bar["l"]),
                    "close": float(bar["c"]),
                    "volume": float(bar.get("v") or 0.0),
                })
            except (KeyError, TypeError, ValueError):
                continue
        return bars

    def fetch_ema21(self, ticker: str, anchor_date: str) -> float | None:
        url = f"{API_BASE_URL}/v1/indicators/ema/{ticker}"
        payload = self.get_json(url, {
            "timespan": "day",
            "adjusted": "true",
            "window": 21,
            "series_type": "close",
            "order": "desc",
            "limit": 1,
            "timestamp.lte": anchor_date,
        })
        values = (payload.get("results") or {}).get("values") or []
        if values and values[0].get("value") is not None:
            return float(values[0]["value"])
        return None


def calculate_atr(bars: list[dict[str, float]], period: int = 10) -> float | None:
    if len(bars) < period + 1:
        return None
    true_ranges = []
    for index in range(1, len(bars)):
        high = bars[index]["high"]
        low = bars[index]["low"]
        prev_close = bars[index - 1]["close"]
        true_ranges.append(max(high - low, abs(high - prev_close), abs(low - prev_close)))
    if len(true_ranges) < period:
        return None
    atr = sum(true_ranges[:period]) / period
    for true_range in true_ranges[period:]:
        atr = ((atr * (period - 1)) + true_range) / period
    return atr


def calculate_simple_atr(bars: list[dict[str, float]], period: int = 10) -> float | None:
    if len(bars) < period + 1:
        return None
    recent_bars = bars[-(period + 1):]
    true_ranges = []
    for index in range(1, len(recent_bars)):
        high = recent_bars[index]["high"]
        low = recent_bars[index]["low"]
        prev_close = recent_bars[index - 1]["close"]
        true_ranges.append(max(high - low, abs(high - prev_close), abs(low - prev_close)))
    return sum(true_ranges) / period if len(true_ranges) == period else None


# Breakout lookback windows in trading days, ordered longest first so the most
# significant label wins when a bar tops several windows at once.
BREAKOUT_LOOKBACKS = [
    ("1Y high", 252),
    ("6M high", 126),
    ("3M high", 63),
    ("2M high", 42),
    ("1M high", 21),
    ("10D high", 10),
    ("5D high", 5),
]
NO_BREAKOUT_COMMENT = "Below 5D high"


def calculate_breakout_comment(bars: list[dict[str, float]], price: float) -> str:
    """Label the longest lookback window whose prior highs are below the anchor price.
    Windows exclude the anchor bar itself."""
    if price is None or price <= 0 or len(bars) < 2:
        return NO_BREAKOUT_COMMENT
    prior_highs = [float(bar["high"]) for bar in bars[:-1]]
    if not prior_highs:
        return NO_BREAKOUT_COMMENT
    for label, window in BREAKOUT_LOOKBACKS:
        if len(prior_highs) < window:
            continue
        if price > max(prior_highs[-window:]):
            return label
    return NO_BREAKOUT_COMMENT


def calculate_ema_value(values: list[float], period: int) -> float | None:
    if not values:
        return None
    if len(values) < period:
        return values[-1]
    current = sum(values[:period]) / period
    multiplier = 2 / (period + 1)
    for value in values[period:]:
        current = (value - current) * multiplier + current
    return current


def determine_daily_closing_position(price: float, prev_close: float, ema21: float, atr10: float) -> str:
    u1 = ema21 + atr10
    u2 = ema21 + 2 * atr10
    u3 = ema21 + 3 * atr10
    u4 = ema21 + 4 * atr10
    u5 = ema21 + 5 * atr10
    u6 = ema21 + 6 * atr10
    u7 = ema21 + 7 * atr10
    l1 = ema21 - atr10
    l2 = ema21 - 2 * atr10
    l3 = ema21 - 3 * atr10
    l4 = ema21 - 4 * atr10
    l5 = ema21 - 5 * atr10
    l6 = ema21 - 6 * atr10
    l7 = ema21 - 7 * atr10

    direction = "Up" if price >= prev_close else "Down"
    if price > u7:
        zone = ">U7"
    elif price > u6:
        zone = "U6-U7"
    elif price > u5:
        zone = "U5-U6"
    elif price > u4:
        zone = "U4-U5"
    elif price > u3:
        zone = "U3-U4"
    elif price > u2:
        zone = "U2-U3"
    elif price > u1:
        zone = "U1-U2"
    elif price > ema21:
        zone = "Mid-U1"
    elif price > l1:
        zone = "Mid-L1"
    elif price > l2:
        zone = "L1-L2"
    elif price > l3:
        zone = "L2-L3"
    elif price > l4:
        zone = "L3-L4"
    elif price > l5:
        zone = "L4-L5"
    elif price > l6:
        zone = "L5-L6"
    elif price > l7:
        zone = "L6-L7"
    else:
        zone = "<L7"
    return f"{direction} & {zone}"


def calculate_daily_closing_position(bars: list[dict[str, float]], close: float, ema21: float | None) -> str | None:
    if len(bars) < 12:
        return None
    recent_bars = bars[-30:]
    closes = [bar["close"] for bar in recent_bars]
    if math.isclose(closes[-1], close, rel_tol=0.0001, abs_tol=0.01):
        prev_close = closes[-2]
        price = closes[-1]
    else:
        prev_close = closes[-1]
        price = close
        closes = [*closes, close]
    if ema21 is None:
        ema21 = calculate_ema_value(closes, 21)
    atr10 = calculate_atr(recent_bars, 10)
    if ema21 is None or atr10 is None or atr10 <= 0:
        return None
    return determine_daily_closing_position(price, prev_close, ema21, atr10)


def ema(values: list[float], period: int) -> list[float | None]:
    out: list[float | None] = [None] * len(values)
    if len(values) < period:
        return out
    current = sum(values[:period]) / period
    out[period - 1] = current
    multiplier = 2 / (period + 1)
    for index in range(period, len(values)):
        current = (values[index] - current) * multiplier + current
        out[index] = current
    return out


def compute_percentiles(values: list[float | None]) -> list[float | None]:
    valid = [(idx, float(v)) for idx, v in enumerate(values) if v is not None and math.isfinite(float(v))]
    if not valid:
        return [None] * len(values)
    if len(valid) == 1:
        res = [None] * len(values)
        res[valid[0][0]] = 100.0
        return res
    sorted_valid = sorted(valid, key=lambda item: item[1])
    n = len(sorted_valid)
    ranks: dict[int, float] = {}
    i = 0
    while i < n:
        j = i
        while j < n and math.isclose(sorted_valid[j][1], sorted_valid[i][1], rel_tol=1e-9, abs_tol=1e-12):
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        pct = (avg_rank / n) * 100.0
        for k in range(i, j):
            ranks[sorted_valid[k][0]] = pct
        i = j
    result: list[float | None] = [None] * len(values)
    for idx, pct in ranks.items():
        result[idx] = pct
    return result


def calculate_roc(bars: list[dict[str, float]], period: int) -> float | None:
    if len(bars) < period + 1:
        return None
    curr_close = float(bars[-1].get("close") or 0.0)
    prev_close = float(bars[-(period + 1)].get("close") or 0.0)
    if prev_close <= 0:
        return None
    return ((curr_close / prev_close) - 1.0) * 100.0


def calculate_ppo_recent(bars: list[dict[str, float]]) -> tuple[float | None, float | None, float | None, float | None, float | None]:
    closes = [bar["close"] for bar in bars]
    if len(closes) < 35:
        return None, None, None, None, None
    ema12 = ema(closes, 12)
    ema26 = ema(closes, 26)
    ppo_values: list[float] = []
    for fast, slow in zip(ema12, ema26):
        if fast is None or slow is None or slow == 0:
            continue
        ppo_values.append(((fast - slow) / slow) * 100.0)
    if len(ppo_values) < 9:
        return None, None, None, None, None
    signal_values = ema(ppo_values, 9)
    signal = signal_values[-1]
    if signal is None:
        return None, None, None, None, None
    ppo_line = ppo_values[-1]
    histogram = ppo_line - signal
    previous_histogram = None
    if len(ppo_values) >= 2 and len(signal_values) >= 2 and signal_values[-2] is not None:
        previous_histogram = ppo_values[-2] - signal_values[-2]
    ppo_hist_slope_3d = None
    if len(ppo_values) >= 4 and len(signal_values) >= 4 and signal_values[-4] is not None:
        hist_t3 = ppo_values[-4] - signal_values[-4]
        ppo_hist_slope_3d = histogram - hist_t3
    return ppo_line, signal, histogram, previous_histogram, ppo_hist_slope_3d


def calculate_ppo(bars: list[dict[str, float]]) -> tuple[float | None, float | None, float | None]:
    ppo_line, signal, histogram, _previous_histogram, _slope_3d = calculate_ppo_recent(bars)
    return ppo_line, signal, histogram


def calculate_rsi(bars: list[dict[str, float]], period: int = 14) -> float | None:
    closes = [bar["close"] for bar in bars]
    if len(closes) < period + 1:
        return None

    gains = []
    losses = []
    for index in range(1, period + 1):
        change = closes[index] - closes[index - 1]
        gains.append(max(change, 0.0))
        losses.append(max(-change, 0.0))

    avg_gain = sum(gains) / period
    avg_loss = sum(losses) / period
    for index in range(period + 1, len(closes)):
        change = closes[index] - closes[index - 1]
        gain = max(change, 0.0)
        loss = max(-change, 0.0)
        avg_gain = ((avg_gain * (period - 1)) + gain) / period
        avg_loss = ((avg_loss * (period - 1)) + loss) / period

    if avg_loss == 0:
        return 100.0
    rs = avg_gain / avg_loss
    return 100 - (100 / (1 + rs))


def calculate_drop_from_high_pct(day_high: float, close: float) -> float | None:
    if day_high <= 0 and close <= 0:
        return None
    effective_high = max(day_high, close)
    if effective_high <= 0:
        return None
    drop = (close - effective_high) / effective_high
    return 0.0 if abs(drop) < 1e-6 else min(0.0, drop)


def calculate_daily_change_pct(bars: list[dict[str, float]], close: float) -> float | None:
    if len(bars) < 2:
        return None
    if math.isclose(bars[-1]["close"], close, rel_tol=0.0001, abs_tol=0.01):
        prev_close = bars[-2]["close"]
    else:
        prev_close = bars[-1]["close"]
    if prev_close <= 0:
        return None
    return (close - prev_close) / prev_close


def calculate_sma_value(bars: list[dict[str, float]], period: int) -> float | None:
    if len(bars) < period:
        return None
    closes = [float(bar["close"]) for bar in bars[-period:]]
    return sum(closes) / period


def calculate_rvol(today_volume: float, bars: list[dict[str, float]], lookback: int = 20) -> float | None:
    if today_volume <= 0 or len(bars) < lookback + 1:
        return None

    # bars are ascending and include the anchor-day bar at the end for this flow,
    # so RVOL average must use the 20 sessions before the anchor day.
    volume_window = bars[-(lookback + 1):-1]

    avg_volume = sum(float(bar.get("volume") or 0.0) for bar in volume_window) / lookback
    if avg_volume <= 0:
        return None

    return today_volume / avg_volume


def enrich_candidate(
    ticker: str,
    bar: dict[str, float],
    config: ScreenerConfig,
    polygon: PolygonSession,
    reference: dict[str, Any] | None = None,
    spy_roc20: float | None = 0.0,
) -> tuple[dict[str, Any] | None, str]:
    if reference is None:
        reference = polygon.fetch_reference(ticker, config.anchor_date)
    ticker_type = str(reference.get("type") or "").upper()
    if ticker_type and ticker_type != "CS":
        return None, "COMMON_STOCK"

    shares = reference.get("weighted_shares_outstanding") or reference.get("share_class_shares_outstanding")
    market_cap = None
    if isinstance(shares, (int, float)) and shares > 0:
        market_cap = float(shares) * bar["close"]
    elif isinstance(reference.get("market_cap"), (int, float)):
        market_cap = float(reference["market_cap"])

    if market_cap is None or market_cap < config.mcap_min or market_cap > config.mcap_max:
        return None, "MCAP"

    history = polygon.fetch_daily_history(ticker, config.anchor_date)
    atr10 = calculate_simple_atr(history, 10)
    atr10_pct = (atr10 / bar["close"] * 100) if atr10 is not None and bar["close"] > 0 else None
    if atr10_pct is None or atr10_pct < config.min_atr10:
        return None, "ATR10"

    rsi14 = calculate_rsi(history, 14)
    if rsi14 is None or rsi14 < config.min_rsi14:
        return None, "RSI14"

    daily_change_pct = calculate_daily_change_pct(history, bar["close"])
    bar_high = float(bar.get("high") or 0.0)
    if bar_high <= 0 and history:
        bar_high = float(history[-1].get("high") or 0.0)
    drop_from_high_pct = calculate_drop_from_high_pct(bar_high, bar["close"])
    rvol = calculate_rvol(bar["volume"], history, 20)
    rvol_prev20_volumes = [float(item.get("volume") or 0.0) for item in reversed(history[-21:-1])] if len(history) >= 21 else []

    ppo_line, signal_line, histogram, previous_histogram, ppo_hist_slope_3d = calculate_ppo_recent(history)
    if ppo_line is None or signal_line is None or histogram is None:
        return None, "PPO_DATA"
    ppo_gt_signal = ppo_line > signal_line
    ppo_cross = previous_histogram is not None and previous_histogram < 0 and histogram > 0

    roc10 = calculate_roc(history, 10)
    roc20 = calculate_roc(history, 20)
    rs20 = (roc20 - spy_roc20) if roc20 is not None and spy_roc20 is not None else None

    # Reuse local history to avoid one extra EMA API call per candidate.
    ema21 = calculate_ema_value([item["close"] for item in history], 21)
    daily_closing_position = calculate_daily_closing_position(history, bar["close"], ema21)
    comment = calculate_breakout_comment(history, bar["close"])
    sma4 = calculate_sma_value(history, 4)
    sma9 = calculate_sma_value(history, 9)
    sma18 = calculate_sma_value(history, 18)
    triple_ma_bullish = sma4 is not None and sma9 is not None and sma18 is not None and sma4 > sma9 > sma18

    return {
        "TICKER": ticker,
        "ANCHOR_DATE": config.anchor_date,
        "PRICE": bar["close"],
        "VOLUME": bar["volume"],
        "RVOL": rvol,
        "RVOL_PREV20_VOLUMES": rvol_prev20_volumes,
        "MCAP": market_cap,
        "DAILY_CHANGE_%": daily_change_pct,
        "DROP_FROM_HIGH_%": drop_from_high_pct,
        "RSI14": rsi14,
        "10DV": atr10_pct,
        "DAILY_CLOSING_POSITION": daily_closing_position,
        "PPO": ppo_line,
        "PPO_SIGNAL": signal_line,
        "PPO_HISTOGRAM": histogram,
        "PPO_HIST_SLOPE_3D": ppo_hist_slope_3d,
        "ROC10": roc10,
        "ROC20": roc20,
        "RS20": rs20,
        "RVOL20": rvol,
        "PPO_GT_SIGNAL": ppo_gt_signal,
        "PPO_CROSS": ppo_cross,
        "SMA4": sma4,
        "SMA9": sma9,
        "SMA18": sma18,
        "TRIPLE_MA_BULLISH": triple_ma_bullish,
        "COMMENT": comment,
    }, "PASS"


def run_screener(config: ScreenerConfig, limit: int | None = None) -> list[dict[str, Any]]:
    api_key = load_api_key()
    polygon = PolygonSession(api_key)
    print(f"Fetching grouped daily bars for {config.anchor_date}...")
    grouped = polygon.fetch_grouped_daily(config.anchor_date)
    if not grouped:
        raise RuntimeError(f"No grouped daily bars returned for {config.anchor_date}")

    DROP_INFO_COLUMN = 86

    def format_filter_line(filter_number: int, label: str, selected: int, input_count: int, kept_label: str = "carry forward") -> str:
        evicted = max(input_count - selected, 0)
        evicted_pct = (evicted / input_count) if input_count else 0.0
        dropped_color = "red" if evicted else "green"
        dropped_pct_text = color_text(f"{evicted_pct:.0%}", "bold")
        left_plain = f"Filter {filter_number} - {label}: {selected:,} {kept_label}, {evicted:,} evicted"
        gap = max(1, DROP_INFO_COLUMN - len(left_plain))
        return (
            f"{color_text(f'Filter {filter_number}', 'bold')} - {color_text(label, 'cyan')}: "
            f"{color_text(f'{selected:,} {kept_label}', 'green')}, "
            f"{color_text(f'{evicted:,} evicted', dropped_color)} "
            f"{' ' * gap}"
            f"[down {dropped_pct_text} dropped]"
        )

    def format_check_line(label: str, selected: int, input_count: int, kept_label: str = "carry forward", prefix: str = "Check") -> str:
        evicted = max(input_count - selected, 0)
        evicted_pct = (evicted / input_count) if input_count else 0.0
        dropped_color = "red" if evicted else "green"
        dropped_pct_text = color_text(f"{evicted_pct:.0%}", "bold")
        left_plain = f"{prefix} - {label}: {selected:,} {kept_label}, {evicted:,} evicted"
        gap = max(1, DROP_INFO_COLUMN - len(left_plain))
        return (
            f"{color_text(prefix, 'bold')} - {color_text(label, 'cyan')}: "
            f"{color_text(f'{selected:,} {kept_label}', 'green')}, "
            f"{color_text(f'{evicted:,} evicted', dropped_color)} "
            f"{' ' * gap}"
            f"[down {dropped_pct_text} dropped]"
        )

    def progress_bar(done: int, total: int, width: int = 30) -> str:
        if total <= 0:
            return f"[{' ' * width}]"
        filled = min(width, max(0, round((done / total) * width)))
        return f"[{color_text('.' * filled, 'green')}{' ' * (width - filled)}]"

    total_stocks = len(grouped)
    reference_by_ticker: dict[str, dict[str, Any]] = {}
    prefilter_errors = 0

    print(f"{color_text('Total stocks returned:', 'bold')} {color_text(f'{total_stocks:,}', 'blue')}")
    grouped_candidates = sorted(grouped.items(), key=lambda item: item[0])

    price_candidates = [
        (ticker, bar)
        for ticker, bar in grouped_candidates
        if bar["close"] >= config.min_price
    ]
    cheap_candidates = [(ticker, bar) for ticker, bar in price_candidates if bar["volume"] >= config.min_volume]
    cheap_candidates.sort(key=lambda item: item[0])
    print(format_filter_line(1, f"Price >= {format_filter_number(config.min_price)}", len(price_candidates), len(grouped_candidates)))
    print(format_filter_line(2, f"Volume >= {format_large_number(config.min_volume)}", len(cheap_candidates), len(price_candidates)))
    if limit:
        print(color_text(f"Quick-smoke limit applied before API-heavy filters: {limit:,} candidates", "yellow"))
        cheap_candidates = cheap_candidates[:limit]

    common_candidates: list[tuple[str, dict[str, float]]] = []
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        future_map = {
            executor.submit(polygon.fetch_reference, ticker, config.anchor_date): (ticker, bar)
            for ticker, bar in cheap_candidates
        }
        for done, future in enumerate(as_completed(future_map), start=1):
            ticker, bar = future_map[future]
            try:
                reference = future.result()
            except Exception as exc:
                prefilter_errors += 1
                reference = {}
                print(color_text(f"Warning: {ticker} reference failed: {exc}", "red"))
            ticker_type = str(reference.get("type") or "").upper()
            if ticker_type and ticker_type != "CS":
                continue
            reference_by_ticker[ticker] = reference
            common_candidates.append((ticker, bar))
            if done % 100 == 0 or done == len(future_map):
                print(f"\r{color_text('Pre-filtering common stocks', 'magenta')} {progress_bar(done, len(future_map))}", end="", flush=True)
    if cheap_candidates:
        print()
    if prefilter_errors:
        print(f"  {color_text(f'Reference errors during pre-filter: {prefilter_errors:,}', 'red')}")
    print(format_check_line("Common stocks", len(common_candidates), len(cheap_candidates), prefix="Pre-filter"))

    # Fetch SPY historical closes for RS20 benchmark calculation
    spy_history = polygon.fetch_daily_history("SPY", config.anchor_date)
    spy_closes = [float(bar["close"]) for bar in spy_history] if spy_history else []
    if len(spy_closes) >= 21 and spy_closes[-21] > 0:
        spy_roc20 = ((spy_closes[-1] / spy_closes[-21]) - 1.0) * 100.0
    else:
        spy_roc20 = 0.0

    raw_candidates: list[dict[str, Any]] = []
    filter_counts = {
        "COMMON_STOCK": 0,
        "MCAP": 0,
        "ATR10": 0,
        "RSI14": 0,
        "PPO_DATA": 0,
        "MOMENTUM_SCORE": 0,
        "PPO>SIGNAL": 0,
        "PPO_CROSS": 0,
        "ERROR": 0,
        "PASS": 0,
    }
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        future_map = {
            executor.submit(enrich_candidate, ticker, bar, config, polygon, reference_by_ticker.get(ticker), spy_roc20): ticker
            for ticker, bar in common_candidates
        }
        for done, future in enumerate(as_completed(future_map), start=1):
            ticker = future_map[future]
            try:
                row, status = future.result()
                filter_counts[status] += 1
                if row:
                    raw_candidates.append(row)
            except Exception as exc:
                filter_counts["ERROR"] += 1
                print(color_text(f"Warning: {ticker} failed: {exc}", "red"))
            if done % 100 == 0 or done == len(future_map):
                print(f"\r{color_text('Applying filters', 'magenta')} {progress_bar(done, len(future_map))}", end="", flush=True)
    if future_map:
        print()

    # Calculate cross-sectional percentiles and Momentum Score across all enriched candidates
    rows: list[dict[str, Any]] = []
    if raw_candidates:
        ppo_hist_pcts = compute_percentiles([c.get("PPO_HISTOGRAM") for c in raw_candidates])
        ppo_slope_pcts = compute_percentiles([c.get("PPO_HIST_SLOPE_3D") for c in raw_candidates])
        roc10_pcts = compute_percentiles([c.get("ROC10") for c in raw_candidates])
        roc20_pcts = compute_percentiles([c.get("ROC20") for c in raw_candidates])
        rs20_pcts = compute_percentiles([c.get("RS20") for c in raw_candidates])
        rvol_pcts = compute_percentiles([c.get("RVOL20") for c in raw_candidates])

        for idx, candidate in enumerate(raw_candidates):
            p_hist = ppo_hist_pcts[idx] if ppo_hist_pcts[idx] is not None else 50.0
            p_slope = ppo_slope_pcts[idx] if ppo_slope_pcts[idx] is not None else 50.0
            p_roc10 = roc10_pcts[idx] if roc10_pcts[idx] is not None else 50.0
            p_roc20 = roc20_pcts[idx] if roc20_pcts[idx] is not None else 50.0
            p_rs20 = rs20_pcts[idx] if rs20_pcts[idx] is not None else 50.0
            p_rvol = rvol_pcts[idx] if rvol_pcts[idx] is not None else 50.0

            m_score = (
                p_hist * 0.20
                + p_slope * 0.25
                + p_roc10 * 0.15
                + p_roc20 * 0.15
                + p_rs20 * 0.15
                + p_rvol * 0.10
            )
            score_val = round(max(0.0, min(100.0, m_score)), 1)
            candidate["MOMENTUM_SCORE"] = score_val
            candidate["MOMENTUM_COMPONENTS"] = {
                "ppo_histogram": candidate.get("PPO_HISTOGRAM"),
                "ppo_histogram_pct": round(p_hist, 1),
                "ppo_hist_slope_3d": candidate.get("PPO_HIST_SLOPE_3D"),
                "ppo_hist_slope_3d_pct": round(p_slope, 1),
                "roc10": candidate.get("ROC10"),
                "roc10_pct": round(p_roc10, 1),
                "roc20": candidate.get("ROC20"),
                "roc20_pct": round(p_roc20, 1),
                "rs20": candidate.get("RS20"),
                "rs20_pct": round(p_rs20, 1),
                "rvol20": candidate.get("RVOL20"),
                "rvol20_pct": round(p_rvol, 1),
            }

            if config.min_momentum_score is not None and score_val < config.min_momentum_score:
                filter_counts["MOMENTUM_SCORE"] += 1
                continue
            if config.require_ppo_gt_signal and not candidate.get("PPO_GT_SIGNAL"):
                filter_counts["PPO>SIGNAL"] += 1
                continue
            if config.require_ppo_cross and not candidate.get("PPO_CROSS"):
                filter_counts["PPO_CROSS"] += 1
                continue
            rows.append(candidate)

    reference_pool = len(common_candidates) - filter_counts["ERROR"]
    common_stock_passed = reference_pool - filter_counts["COMMON_STOCK"]
    mcap_passed = common_stock_passed - filter_counts["MCAP"]
    atr_passed = mcap_passed - filter_counts["ATR10"]
    rsi_passed = atr_passed - filter_counts["RSI14"]
    ppo_data_passed = rsi_passed - filter_counts["PPO_DATA"]
    momentum_passed = ppo_data_passed - filter_counts["MOMENTUM_SCORE"]
    ppo_signal_passed = momentum_passed - filter_counts["PPO>SIGNAL"]
    ppo_cross_passed = ppo_signal_passed - filter_counts["PPO_CROSS"]
    ppo_filter_label = "PPO>SIGNAL" if config.require_ppo_gt_signal else "PPO>SIGNAL skipped"
    ppo_cross_label = "PPO Cross" if config.require_ppo_cross else "PPO Cross skipped"
    if filter_counts["ERROR"]:
        error_text = f"API/data errors: {filter_counts['ERROR']:,}"
        print(color_text(error_text, 'red'))
    print(
        format_filter_line(3, f"MCAP {format_large_number(config.mcap_min)}-{format_large_number(config.mcap_max)}", mcap_passed, common_stock_passed)
    )
    print(format_filter_line(4, f"10D Velocity% >= {format_filter_number(config.min_atr10)}", atr_passed, mcap_passed))
    print(format_filter_line(5, f"RSI14 >= {format_filter_number(config.min_rsi14)}", rsi_passed, atr_passed))
    print(format_check_line("PPO data available", ppo_data_passed, rsi_passed))
    print(format_filter_line(6, f"Momentum Score >= {format_filter_number(config.min_momentum_score)}", momentum_passed, ppo_data_passed))
    print(format_filter_line(7, ppo_filter_label, ppo_signal_passed, momentum_passed, "standing"))
    final_filter_line = format_filter_line(8, ppo_cross_label, ppo_cross_passed, ppo_signal_passed, "standing")
    print(final_filter_line)
    visible_line = re.sub(r"\033\[[0-9;]*m", "", final_filter_line)
    print("-" * len(visible_line))

    rows.sort(key=lambda row: (row.get("MOMENTUM_SCORE") if row.get("MOMENTUM_SCORE") is not None else -999.0), reverse=True)
    return rows


def write_xlsx(rows: list[dict[str, Any]], config: ScreenerConfig) -> Path:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    anchor_day = datetime.strptime(config.anchor_date, "%Y-%m-%d")
    run_time_et = datetime.now(ZoneInfo("America/New_York"))
    anchor_label = anchor_day.strftime("%d %b")
    run_stamp = run_time_et.strftime("%d %b %Y %I;%M %p")
    output_name = f"Anchor Date {anchor_label} ({run_stamp}).xlsx"
    output_path = OUTPUT_DIR / output_name

    columns = [
        ("Ticker", "TICKER"),
        ("Anchor Date", "ANCHOR_DATE"),
        ("Momentum Score", "MOMENTUM_SCORE"),
        ("Price", "PRICE"),
        ("Volume", "VOLUME"),
        ("Rvol", "RVOL"),
        ("Mcap", "MCAP"),
        ("Change%", "DAILY_CHANGE_%"),
        ("Drop from high", "DROP_FROM_HIGH_%"),
        ("RSI14", "RSI14"),
        ("10DV", "10DV"),
        ("Closing Position", "DAILY_CLOSING_POSITION"),
        ("PPO", "PPO"),
        ("Signal", "PPO_SIGNAL"),
        ("Histogram", "PPO_HISTOGRAM"),
        ("PPO > Signal", "PPO_GT_SIGNAL"),
        ("PPO Cross", "PPO_CROSS"),
        ("Comment", "COMMENT"),
    ]

    wb = Workbook()
    ws = wb.active
    ws.title = "Master List"

    ws.append([header for header, _ in columns])
    header_fill = PatternFill("solid", fgColor="000000")
    positive_fill = PatternFill("solid", fgColor="D9EAD3")
    negative_fill = PatternFill("solid", fgColor="F4CCCC")
    neutral_fill = PatternFill("solid", fgColor="FFF2CC")
    amber_fill = PatternFill("solid", fgColor="FCE5CD")
    ticker_fill = PatternFill("solid", fgColor="D9EAF7")
    header_border = Border(
        left=Side(style="thin", color="FFFFFF"),
        right=Side(style="thin", color="FFFFFF"),
        top=Side(style="thin", color="FFFFFF"),
        bottom=Side(style="thin", color="FFFFFF"),
    )
    ws.row_dimensions[1].height = 67.5
    for cell in ws[1]:
        cell.font = Font(name="Calibri", size=10, color="FFD966", bold=True)
        cell.fill = header_fill
        cell.border = header_border
        cell.alignment = Alignment(horizontal="center", vertical="center", wrap_text=True)

    for row in rows:
        ws.append([row.get(key) for _, key in columns])

    for row in ws.iter_rows(min_row=2):
        for cell in row:
            cell.alignment = Alignment(horizontal="center", vertical="center")
        row[2].number_format = "0.0"
        row[3].number_format = "$0.##"
        row[4].number_format = '[>=1000000000]0.##,,,"B";[>=1000000]0.##,,"M";#,##0'
        row[5].number_format = "0.##"
        row[6].number_format = '[>=1000000000]$0.##,,,"B";[>=1000000]$0.##,,"M";$#,##0'
        row[7].number_format = "0.##%"
        row[8].number_format = "0.##%"
        row[9].number_format = "0.##"
        row[10].number_format = "0.##%"
        row[12].number_format = "0.##"
        row[13].number_format = "0.##"
        row[14].number_format = "0.##"
        row[0].font = Font(name="Calibri", size=10, bold=True, color="1F3864")
        row[0].fill = ticker_fill
        if isinstance(row[5].value, (int, float)):
            row[5].font = Font(name="Calibri", size=10, color="008000" if row[5].value > 0 else "C00000")
            row[5].fill = positive_fill if row[5].value > 0 else negative_fill if row[5].value < 0 else neutral_fill
        if isinstance(row[7].value, (int, float)):
            row[7].font = Font(name="Calibri", size=10, color="008000" if row[7].value > 0 else "C00000")
            row[7].fill = positive_fill if row[7].value > 0 else negative_fill if row[7].value < 0 else neutral_fill
        if isinstance(row[8].value, (int, float)) and row[8].value < -0.005:
            row[8].font = Font(name="Calibri", size=10, color="C00000")
            row[8].fill = negative_fill
        if isinstance(row[9].value, (int, float)):
            row[9].fill = positive_fill if row[9].value >= 60 else negative_fill if row[9].value <= 40 else neutral_fill

    def format_compact_number(value: float, decimals: int = 2) -> str:
        return f"{value:.{decimals}f}".rstrip("0").rstrip(".")

    def display_text_for_width(value: Any, key: str) -> str:
        def trim_decimal(text: str) -> str:
            return text.rstrip("0").rstrip(".")

        if value is None:
            return ""
        if key == "PRICE" and isinstance(value, (int, float)):
            return f"${trim_decimal(f'{value:.2f}') }".strip()
        if key in {"VOLUME", "MCAP"} and isinstance(value, (int, float)):
            return format_large_number(float(value))
        if key in {"RVOL", "RVOL20"} and isinstance(value, (int, float)):
            return trim_decimal(f"{value:.2f}")
        if key in {"DAILY_CHANGE_%", "DROP_FROM_HIGH_%"} and isinstance(value, (int, float)):
            return f"{trim_decimal(f'{value * 100:.2f}')}%"
        if key in {"MOMENTUM_SCORE", "RSI14", "PPO", "PPO_SIGNAL", "PPO_HISTOGRAM", "ROC10", "ROC20", "RS20"} and isinstance(value, (int, float)):
            return trim_decimal(f"{value:.2f}")
        if key in {"PPO_GT_SIGNAL", "PPO_CROSS", "TRIPLE_MA_BULLISH"} and isinstance(value, bool):
            return "TRUE" if value else "FALSE"
        return str(value)

    # Compact auto-fit widths based on displayed values (not raw Python values).
    for col_idx, (header, key) in enumerate(columns, start=1):
        max_len = len(header)
        for row in rows:
            text = display_text_for_width(row.get(key), key)
            if text:
                max_len = max(max_len, len(text))
        col_letter = get_column_letter(col_idx)
        ws.column_dimensions[col_letter].width = min(max(max_len + 2, 8), 20)
    ws.freeze_panes = "A2"
    ws.auto_filter.ref = ws.dimensions

    # RVOL validation tab: top 3 tickers from Master List by highest RVOL.
    ws_rvol = wb.create_sheet("rvol")
    ws_rvol.column_dimensions["A"].width = 28
    ws_rvol.column_dimensions["B"].width = 22

    rvol_header_fill = PatternFill("solid", fgColor="000000")
    rvol_title_fill = PatternFill("solid", fgColor="D9EAF7")
    rvol_label_fill = PatternFill("solid", fgColor="F2F2F2")
    rvol_value_fill = PatternFill("solid", fgColor="FFFCEB")
    rvol_border = Border(
        left=Side(style="thin", color="D9D9D9"),
        right=Side(style="thin", color="D9D9D9"),
        top=Side(style="thin", color="D9D9D9"),
        bottom=Side(style="thin", color="D9D9D9"),
    )

    ranked_rows = [row for row in rows if isinstance(row.get("RVOL"), (int, float))]
    ranked_rows.sort(key=lambda item: float(item.get("RVOL") or float("-inf")), reverse=True)
    top_rows = ranked_rows[:3]

    ws_rvol["A2"] = "Top 3"
    ws_rvol["A2"].font = Font(name="Calibri", size=11, bold=True, color="FFD966")
    ws_rvol["A2"].fill = rvol_header_fill
    ws_rvol["A2"].border = rvol_border
    ws_rvol["A2"].alignment = Alignment(horizontal="center", vertical="center")
    ws_rvol["B2"] = ",".join(str(row.get("TICKER") or "") for row in top_rows)
    ws_rvol["B2"].font = Font(name="Calibri", size=11, bold=True, color="FFD966")
    ws_rvol["B2"].fill = rvol_header_fill
    ws_rvol["B2"].border = rvol_border
    ws_rvol["B2"].alignment = Alignment(horizontal="center", vertical="center")

    if top_rows:
        start_row = 4
        for top_row in top_rows:
            ticker = str(top_row.get("TICKER") or "")
            ws_rvol.cell(row=start_row, column=1, value=f"{ticker} volume validation")
            ws_rvol.cell(row=start_row, column=1).font = Font(name="Calibri", size=11, bold=True, color="1F3864")
            ws_rvol.cell(row=start_row, column=1).fill = rvol_title_fill
            ws_rvol.cell(row=start_row, column=1).border = rvol_border
            ws_rvol.cell(row=start_row, column=1).alignment = Alignment(horizontal="left", vertical="center")
            ws_rvol.merge_cells(start_row=start_row, start_column=1, end_row=start_row, end_column=2)

            prev20_volumes = top_row.get("RVOL_PREV20_VOLUMES") or []
            day_row = start_row + 1

            if len(prev20_volumes) == 20:
                for day_offset, volume in enumerate(prev20_volumes, start=1):
                    ws_rvol.cell(row=day_row, column=1, value=f"Day -{day_offset}")
                    ws_rvol.cell(row=day_row, column=2, value=format_large_number(float(volume)))
                    ws_rvol.cell(row=day_row, column=1).fill = rvol_label_fill
                    ws_rvol.cell(row=day_row, column=2).fill = rvol_value_fill
                    ws_rvol.cell(row=day_row, column=1).border = rvol_border
                    ws_rvol.cell(row=day_row, column=2).border = rvol_border
                    ws_rvol.cell(row=day_row, column=1).alignment = Alignment(horizontal="center", vertical="center")
                    ws_rvol.cell(row=day_row, column=2).alignment = Alignment(horizontal="center", vertical="center")
                    day_row += 1

                avg_20_volume = sum(float(volume) for volume in prev20_volumes) / 20
                ws_rvol.cell(row=day_row, column=1, value="Average of 20 days")
                ws_rvol.cell(row=day_row, column=2, value=format_large_number(avg_20_volume))
                ws_rvol.cell(row=day_row, column=1).font = Font(name="Calibri", size=11, bold=True)
                ws_rvol.cell(row=day_row, column=2).font = Font(name="Calibri", size=11, bold=True)
                ws_rvol.cell(row=day_row, column=1).fill = rvol_title_fill
                ws_rvol.cell(row=day_row, column=2).fill = rvol_title_fill
                ws_rvol.cell(row=day_row, column=1).border = rvol_border
                ws_rvol.cell(row=day_row, column=2).border = rvol_border
                ws_rvol.cell(row=day_row, column=1).alignment = Alignment(horizontal="center", vertical="center")
                ws_rvol.cell(row=day_row, column=2).alignment = Alignment(horizontal="center", vertical="center")
                day_row += 1
            else:
                ws_rvol.cell(row=day_row, column=1, value="Not enough history for 20-day validation")
                ws_rvol.cell(row=day_row, column=1).font = Font(name="Calibri", size=11, bold=True, color="C00000")
                ws_rvol.cell(row=day_row, column=1).fill = rvol_title_fill
                ws_rvol.cell(row=day_row, column=1).border = rvol_border
                ws_rvol.cell(row=day_row, column=1).alignment = Alignment(horizontal="left", vertical="center")
                ws_rvol.merge_cells(start_row=day_row, start_column=1, end_row=day_row, end_column=2)
                day_row += 1

            ws_rvol.cell(row=day_row, column=1, value="anchor date volume")
            ws_rvol.cell(row=day_row, column=2, value=format_large_number(float(top_row.get("VOLUME") or 0.0)))
            ws_rvol.cell(row=day_row, column=1).font = Font(name="Calibri", size=11, bold=True)
            ws_rvol.cell(row=day_row, column=2).font = Font(name="Calibri", size=11, bold=True)
            ws_rvol.cell(row=day_row, column=1).fill = rvol_title_fill
            ws_rvol.cell(row=day_row, column=2).fill = rvol_title_fill
            ws_rvol.cell(row=day_row, column=1).border = rvol_border
            ws_rvol.cell(row=day_row, column=2).border = rvol_border
            ws_rvol.cell(row=day_row, column=1).alignment = Alignment(horizontal="center", vertical="center")
            ws_rvol.cell(row=day_row, column=2).alignment = Alignment(horizontal="center", vertical="center")
            day_row += 1

            ws_rvol.cell(row=day_row, column=1, value="Final RVOL")
            ws_rvol.cell(row=day_row, column=2, value=format_compact_number(float(top_row.get("RVOL") or 0.0)))
            ws_rvol.cell(row=day_row, column=1).font = Font(name="Calibri", size=11, bold=True, color="FFFFFF")
            ws_rvol.cell(row=day_row, column=2).font = Font(name="Calibri", size=11, bold=True, color="FFFFFF")
            ws_rvol.cell(row=day_row, column=1).fill = PatternFill("solid", fgColor="1F3864")
            ws_rvol.cell(row=day_row, column=2).fill = PatternFill("solid", fgColor="1F3864")
            ws_rvol.cell(row=day_row, column=1).border = rvol_border
            ws_rvol.cell(row=day_row, column=2).border = rvol_border
            ws_rvol.cell(row=day_row, column=1).alignment = Alignment(horizontal="center", vertical="center")
            ws_rvol.cell(row=day_row, column=2).alignment = Alignment(horizontal="center", vertical="center")

            start_row = day_row + 2
    else:
        ws_rvol["A4"] = "No RVOL rows available for validation."
        ws_rvol["A4"].font = Font(name="Calibri", size=11, bold=True, color="C00000")

    wb.save(output_path)
    return output_path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run standalone daily anchor screener")
    parser.add_argument("--date", dest="anchor_date", help="Anchor date YYYY-MM-DD. If omitted, script prompts and defaults to latest completed trading day.")
    parser.add_argument("--limit", type=int, help="Limit cheap-filter candidates for quick smoke tests.")
    return parser.parse_args()


def get_anchor_date_from_user(cli_anchor_date: str | None) -> str:
    if cli_anchor_date:
        return cli_anchor_date

    default_date = default_anchor_date()
    while True:
        user_value = input(f"Enter anchor date (YYYY-MM-DD) [default: {default_date}]: ").strip()
        selected_date = user_value or default_date
        try:
            normalize_anchor_date(selected_date)
            return selected_date
        except ValueError:
            print(color_text("Invalid date format. Use YYYY-MM-DD.", "red"))


def main() -> None:
    started_at = time.perf_counter()
    args = parse_args()
    selected_anchor_date = get_anchor_date_from_user(args.anchor_date)
    config = build_config(selected_anchor_date)
    print(color_text("Daily Anchor Screener", "bold"))
    if config.anchor_note:
        print(f"{color_text('Note:', 'yellow')} {color_text(config.anchor_note, 'yellow')}")
    print(f"{color_text('Anchor Date:', 'cyan')} {color_text(config.anchor_date, 'blue')}")
    print(color_text("Filters:", "cyan"))
    filter_rows = [
        ("MCAP", f"{format_large_number(config.mcap_min)}-{format_large_number(config.mcap_max)}", "yellow"),
        ("Volume", f">= {format_large_number(config.min_volume)}", "yellow"),
        ("Price", f">= {format_filter_number(config.min_price)}", "yellow"),
        ("10D Velocity%", f">= {format_filter_number(config.min_atr10)}", "yellow"),
        ("RSI14", f">= {format_filter_number(config.min_rsi14)}", "yellow"),
        ("Momentum Min", f">= {format_filter_number(config.min_momentum_score)}", "yellow"),
        ("PPO>SIGNAL", str(config.require_ppo_gt_signal), "green" if config.require_ppo_gt_signal else "yellow"),
        ("PPO Cross", str(config.require_ppo_cross), "green" if config.require_ppo_cross else "yellow"),
    ]
    headers = [name for name, _, _ in filter_rows]
    values_plain = [value for _, value, _ in filter_rows]
    values_colored = [color_text(value, color) for _, value, color in filter_rows]
    col_widths = [max(len(header), len(value)) for header, value in zip(headers, values_plain)]

    def render_row(plain_cells: list[str], styled_cells: list[str]) -> str:
        cells = []
        for plain, styled, width in zip(plain_cells, styled_cells, col_widths):
            cells.append(styled + (" " * (width - len(plain))))
        return "  | " + " | ".join(cells) + " |"

    border = "  +-" + "-+-".join("-" * width for width in col_widths) + "-+"
    header_row = render_row(headers, [color_text(header, "bold") for header in headers])
    value_row = render_row(values_plain, values_colored)

    print(border)
    print(header_row)
    print(border)
    print(value_row)
    print(border)
    rows = run_screener(config, args.limit)
    output_path = write_xlsx(rows, config)
    elapsed_seconds = time.perf_counter() - started_at
    print(f"{color_text('Output file', 'bold')} - {color_text(output_path, 'cyan')}")
    print(f"{color_text('Processing time', 'bold')} - {color_text(f'{elapsed_seconds:.2f} seconds', 'yellow')}")


if __name__ == "__main__":
    main()
