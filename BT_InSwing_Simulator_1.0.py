"""
In-Swing Portfolio Simulator
- Multi-day tracking from entry date to computed exit date
- Entry price is the 15:50 close on entry date (or latest bar before 15:50)
- Exit uses the T3 3:50 PM close, where T0 is the normalized entry trading day
- Symbol chart shows 10-minute candles with session-only axis (9:30-16:00 ET)
"""

import os
import re
import shutil
import copy
import json
import argparse
import html
import importlib.util
import io
import math
import mimetypes
import sys
import threading
import webbrowser
from datetime import date, datetime, time, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from time import perf_counter
from urllib.parse import parse_qs, quote, unquote, urlparse
from zoneinfo import ZoneInfo

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import pandas as pd
import requests
from matplotlib.lines import Line2D
from matplotlib.offsetbox import AnnotationBbox, DrawingArea, TextArea, VPacker
from matplotlib.patches import Circle, FancyBboxPatch, Rectangle
from matplotlib.ticker import FuncFormatter, MultipleLocator

try:
    from PIL import Image

    PIL_AVAILABLE = True
except Exception:
    PIL_AVAILABLE = False

try:
    from rich.console import Console
    from rich.panel import Panel

    RICH_AVAILABLE = True
    console = Console()
except Exception:
    RICH_AVAILABLE = False
    console = None

# ============================================================================
# CONFIGURATION
# ============================================================================

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

INITIAL_CAPITAL = 250000
PORTFOLIO_TARGET = 0.08
PORTFOLIO_STOP_LOSS = -0.05

BAR_MINUTES = 10
ENTRY_HOUR = 15
ENTRY_MINUTE = 50
EXIT_HOUR = 15
EXIT_MINUTE = 50
LIVE_REFRESH_START = time(9, 30)
LIVE_REFRESH_END = time(16, 0)

# Optional prompt defaults
CONFIG_INSWING_TICKERS = [ "AAPL","TSLA","AMZN", "GOOG","NVDA","MSFT","META"]
CONFIG_ENTRY_DATE = ""
HEADER_LOGO_SOURCE = os.path.join(SCRIPT_DIR, "static", "nras-logo.png")
REPORTS_ROOT = os.path.join(SCRIPT_DIR, "reports")
REPORT_METADATA_FOLDER_NAME = "meta data"
BENCHMARK_TICKERS = ["SPY", "QQQ", "IWM"]
BENCHMARK_COLORS = {"SPY": "#111827", "QQQ": "#7c3aed", "IWM": "#ea580c"}
SHOW_CHART_ANCHOR_LATEST_OVERLAY = False
MAX_SIMULATOR_TICKERS = 20
DAILY_CHART_PPO_WARMUP_CALENDAR_DAYS = 1200
WATCHLIST_CANDLE_UP_COLOR = "#4ade80"
WATCHLIST_CANDLE_DOWN_COLOR = "#ff334a"
STOCK_LINE_COLORS = [
    "#073bd6", "#0f9f55", "#dc2626", "#0891b2", "#be185d", "#4b5563",
    "#16a34a", "#f43f5e", "#0ea5e9", "#84cc16", "#14b8a6", "#e11d48",
    "#65a30d", "#0284c7", "#64748b", "#22c55e", "#db2777", "#2563eb",
    "#0f766e", "#b91c1c", "#0369a1", "#15803d", "#475569", "#06b6d4",
]

# ----------------------------------------------------------------------------
# Shared UI theme layer (finviz typography + palette), injected into every
# <style> block rendered by this app. Layout/structure is untouched.
# ----------------------------------------------------------------------------
FINVIZ_THEME_CSS = """
    @font-face { font-family: 'IBM Plex Sans'; font-style: normal; font-weight: 100 900; font-display: swap; size-adjust: 105%; src: local('IBM Plex Sans'), url('/app-static/ibm-plex-sans-latin-wght-normal.woff2') format('woff2'); }
    @font-face { font-family: 'IBM Plex Sans'; font-style: italic; font-weight: 100 900; font-display: swap; size-adjust: 105%; src: local('IBM Plex Sans Italic'), url('/app-static/ibm-plex-sans-latin-wght-italic.woff2') format('woff2'); }
    @font-face { font-family: 'IBM Plex Sans Fallback'; src: local('Arial'); ascent-override: 101%; descent-override: 27%; line-gap-override: 0%; size-adjust: 105%; }
    :root {
        color-scheme: light;
        --fv-font-sans: 'IBM Plex Sans', 'IBM Plex Sans Fallback', Arial, sans-serif;
        --fv-white: #ffffff;
        --fv-gray-50: #f3f3f5; --fv-gray-100: #dedfe5; --fv-gray-200: #c3c6d0;
        --fv-gray-300: #a3a8b9; --fv-gray-400: #868ea5; --fv-gray-500: #676f85;
        --fv-gray-600: #4c5263; --fv-gray-700: #353945; --fv-gray-750: #2c303b;
        --fv-gray-800: #22262f; --fv-gray-900: #14161d;
        --fv-blue-50: #ebf4fe; --fv-blue-100: #cae2fc; --fv-blue-200: #9bcbfa;
        --fv-blue-400: #2f91ef; --fv-blue-500: #306dca;
        --fv-green-50: #e7f7e8; --fv-green-100: #beeac1; --fv-green-200: #86d895;
        --fv-green-400: #00a449; --fv-green-500: #19803d;
        --fv-red-50: #fef0f0; --fv-red-100: #fcd6d6; --fv-red-200: #fbb4b4; --fv-red-500: #d91e2b;
        --fv-yellow-50: #fdf2df; --fv-yellow-100: #fcdc86; --fv-yellow-200: #f3c736;
        --fv-yellow-300: #cda30b; --fv-yellow-400: #b08900; --fv-yellow-500: #8b6a00;
    }
    html, body, button, input, select, textarea, table, summary, details {
        font-family: var(--fv-font-sans);
        -webkit-font-smoothing: antialiased;
        -moz-osx-font-smoothing: grayscale;
    }
    tbody tr:nth-child(2n) { background: #f3f3f5; }
    tbody tr:hover { background: #e9eaee; }
    /* Neutralise the UA's blue for checkboxes, focus rings and selection. */
    input, select, textarea, button { accent-color: #4c5263; }
    :focus-visible { outline: 2px solid #676f85; outline-offset: 1px; }
    ::selection { background: #c3c6d0; color: #14161d; }

    /* ------------------------------------------------------------------
       Theme switch control (shown in page headers, works in both themes)
       ------------------------------------------------------------------ */
    .header-right { justify-self: end; display: inline-flex; align-items: center; gap: 14px; min-width: 0; }
    .theme-switch { display: inline-flex; align-items: center; gap: 6px; cursor: pointer; user-select: none; color: rgba(255,255,255,0.85); font-size: 10.5px; font-weight: 700; white-space: nowrap; }
    .theme-switch input { position: absolute; opacity: 0; pointer-events: none; }
    .theme-switch-track { position: relative; width: 30px; height: 16px; border-radius: 999px; background: rgba(255,255,255,0.25); transition: background 0.2s; }
    .theme-switch-track::after { content: ''; position: absolute; top: 2px; left: 2px; width: 12px; height: 12px; border-radius: 50%; background: #ffffff; transition: transform 0.2s, background 0.2s; }
    .theme-switch input:checked + .theme-switch-track { background: #00c853; }
    .theme-switch input:checked + .theme-switch-track::after { transform: translateX(14px); background: #06130b; }

    /* ------------------------------------------------------------------
       App dark theme (BlockTrade-inspired palette)
       Surfaces: #080B0D / #111715 / #1A1F1C / #232927  Border: #2E3431
       Text: #F2F4F3 / #A8B2AD  Accents: green #00C853, red #FF5252,
       amber #FFC107, blue #2962FF
       ------------------------------------------------------------------ */
    /* Card/section header band: single knob used by every header rule below
       (screener cards, watchlist, saved reports, history, chart modal). */
    body.dark-theme { color-scheme: dark; background: #080b0d; color: #f2f4f3; --card-head-bg: radial-gradient(circle at 18% 0%, rgba(255,255,255,0.08), transparent 42%), linear-gradient(135deg, #050607 0%, #171b1f 48%, #050607 100%); --card-head-border: rgba(255,255,255,0.12); }
    body.dark-theme tbody tr:nth-child(2n) { background: #141917; }
    body.dark-theme tbody tr:hover { background: #1d2421; }
    body.dark-theme input, body.dark-theme select, body.dark-theme textarea, body.dark-theme button { accent-color: #00c853; }
    body.dark-theme :focus-visible { outline-color: #00c853; }
    body.dark-theme ::selection { background: #00c853; color: #06130b; }
    body.dark-theme input[type="text"], body.dark-theme input[type="date"], body.dark-theme input[type="search"], body.dark-theme select, body.dark-theme textarea { background: #1a1f1c; border-color: #2e3431; color: #f2f4f3; }
    body.dark-theme input::placeholder { color: #6c7570; }
    body.dark-theme input[type="date"]::-webkit-calendar-picker-indicator { filter: invert(1); }

    /* Header / navigation */
    body.dark-theme .header { background: radial-gradient(circle at 14% 0%, rgba(0,200,83,0.20), transparent 34%), linear-gradient(90deg, #020a07 0%, #052214 42%, #020a07 100%); border: 0; border-bottom: 1px solid rgba(0,200,83,0.18); box-shadow: none; }
    body.dark-theme .brand-logo { filter: brightness(0) saturate(100%) invert(77%) sepia(69%) saturate(814%) hue-rotate(359deg) brightness(101%) contrast(95%) drop-shadow(0 0 10px rgba(243,199,54,0.24)); opacity: 0.98; }
    body.dark-theme .report-title { color: #ffffff; text-shadow: none; }
    body.dark-theme .report-subtitle { color: #ffffff; opacity: 0.82; }
    body.dark-theme .live-clock { color: #ffffff; }
    body.dark-theme .live-clock span { color: #f2f4f3; }
    body.dark-theme .theme-switch { color: #ffffff; }
    body.dark-theme .tabs { background: rgba(0,0,0,0.26); border-color: rgba(163,230,53,0.16); box-shadow: inset 0 1px 0 rgba(255,255,255,0.05), 0 0 18px rgba(0,200,83,0.08); }
    body.dark-theme .tabs button { color: rgba(255,255,255,0.82); }
    body.dark-theme .tabs button:hover { background: rgba(255,255,255,0.08); color: #ffffff; }
    body.dark-theme .tabs button.active { background: linear-gradient(135deg, #00c853, #059669); color: #06130b; box-shadow: 0 0 0 1px rgba(163,230,53,0.52), 0 0 22px rgba(0,200,83,0.42); }
    body.dark-theme .tabs button:disabled, body.dark-theme .tabs button.disabled-tab { color: rgba(255,255,255,0.24); }

    /* Cards / panels */
    body.dark-theme .card, body.dark-theme details.card { background: #111715; border-color: #2e3431; box-shadow: 0 14px 34px rgba(0,0,0,0.5); }
    /* Card headers: clearly distinct band — lighter surface, separator line and
       a green accent edge so sections read at a glance. */
    body.dark-theme .card h2, body.dark-theme .card-title-row, body.dark-theme details.card summary { background: var(--card-head-bg); color: #f2f4f3; border-bottom: 1px solid var(--card-head-border); box-shadow: inset 3px 0 0 #f3c736, inset 0 1px 0 rgba(255,255,255,0.08), 0 8px 24px rgba(0,0,0,0.26); }
    body.dark-theme .card-title-row h2 { background: none; border-bottom: 0; box-shadow: none; }
    body.dark-theme label span { color: #a8b2ad; }
    body.dark-theme .checkbox-row { color: #f2f4f3; }
    body.dark-theme .primary { background: #00c853; color: #06130b; }
    body.dark-theme .primary:disabled { background: #23292b; color: #6c7570; opacity: 1; }
    body.dark-theme .secondary { background: #1a1f1c; border-color: #2e3431; color: #f2f4f3; }
    body.dark-theme .secondary:disabled { opacity: 0.4; }
    body.dark-theme .message { background: #221d0c; color: #ffc107; border-color: #4a3f14; }
    body.dark-theme .message.success { background: #10201a; color: #9fe8c0; border-color: #1f4732; }
    body.dark-theme .screener-progress-track { background: #1a1f1c; border-color: #2e3431; box-shadow: inset 1px 1px 2px rgba(0,0,0,0.6); }
    body.dark-theme .screener-progress-fill { background: repeating-linear-gradient(90deg, #00c853 0 8px, #1a1f1c 8px 10px); }

    /* Tables */
    body.dark-theme .table-wrap { border-top-color: #2e3431; }
    body.dark-theme th { background: #1a201d; color: #e5efe9; }
    body.dark-theme td { border-top-color: #232927; }
    body.dark-theme td.daily-change-positive { color: #00c853; }
    body.dark-theme td.daily-change-negative { color: #ff5252; }
    body.dark-theme td[class*="screener-change-"],
    body.dark-theme td[class*="screener-drop-"],
    body.dark-theme td[class*="screener-rvol-"],
    body.dark-theme td[class*="screener-position-"],
    body.dark-theme td[class*="screener-comment-"] { color: #f8fafc; font-weight: 700; }
    body.dark-theme td.screener-change-pos-1 { background: #0b3f25; }
    body.dark-theme td.screener-change-pos-2 { background: #075f35; }
    body.dark-theme td.screener-change-pos-3 { background: #008a48; }
    body.dark-theme td.screener-change-pos-4 { background: #00ad5a; }
    body.dark-theme td.screener-change-pos-5 { background: #007a3e; }
    body.dark-theme td.screener-change-neg-1 { background: #4a1b1f; }
    body.dark-theme td.screener-change-neg-2 { background: #6b2228; }
    body.dark-theme td.screener-change-neg-3 { background: #8f252c; }
    body.dark-theme td.screener-change-neg-4 { background: #b91c1c; }
    body.dark-theme td.screener-change-neg-5 { background: #7f1d1d; }
    body.dark-theme td.screener-drop-1 { background: #4a1b1f; color: #fca5a5; }
    body.dark-theme td.screener-drop-2 { background: #6b2228; color: #fca5a5; }
    body.dark-theme td.screener-drop-3 { background: #8f252c; color: #fee2e2; }
    body.dark-theme td.screener-drop-4 { background: #b91c1c; color: #ffffff; }
    body.dark-theme td.screener-drop-5 { background: #7f1d1d; color: #ffffff; }
    body.dark-theme td.screener-rvol-1 { background: #dbeafe; color: #1e3a5f; }
    body.dark-theme td.screener-rvol-2 { background: #93c5fd; color: #102a43; }
    body.dark-theme td.screener-rvol-3 { background: #2563eb; color: #ffffff; }
    body.dark-theme td.screener-rvol-4 { background: #1d4ed8; color: #ffffff; }
    body.dark-theme td.screener-rvol-5 { background: #1e3a8a; color: #ffffff; }
    body.dark-theme td.screener-position-pos-1 { background: #0b3f25; }
    body.dark-theme td.screener-position-pos-2 { background: #075f35; }
    body.dark-theme td.screener-position-pos-3 { background: #008a48; }
    body.dark-theme td.screener-position-pos-4 { background: #00ad5a; }
    body.dark-theme td.screener-position-pos-5 { background: #007a3e; }
    body.dark-theme td.screener-position-neg-1 { background: #4a1b1f; }
    body.dark-theme td.screener-position-neg-2 { background: #6b2228; }
    body.dark-theme td.screener-position-neg-3 { background: #8f252c; }
    body.dark-theme td.screener-position-neg-4 { background: #b91c1c; }
    body.dark-theme td.screener-position-neg-5 { background: #7f1d1d; }
    body.dark-theme td.screener-bool-yes { color: #4ade80; font-weight: 800; }
    body.dark-theme td.screener-bool-no { color: #ff5252; font-weight: 800; }
    body.dark-theme td.screener-comment-below { background: #303746; color: #cbd5e1; }
    body.dark-theme td.screener-comment-5d { background: #365314; }
    body.dark-theme td.screener-comment-10d { background: #3f6212; }
    body.dark-theme td.screener-comment-1m { background: #166534; }
    body.dark-theme td.screener-comment-2m { background: #047857; }
    body.dark-theme td.screener-comment-3m { background: #0f766e; }
    body.dark-theme td.screener-comment-6m { background: #065f46; }
    body.dark-theme td.screener-comment-1y { background: #b08900; color: #06130b; }
    body.dark-theme td.screener-score-high { color: #4ade80; }
    body.dark-theme td.screener-score-mid { color: #f2f4f3; }
    body.dark-theme td.screener-score-low { color: #ff7b7b; }
    body.dark-theme td.screener-momentum-positive,
    body.dark-theme td.screener-rsi-pos-1 { color: #4ade80; font-weight: 700; }
    body.dark-theme td.screener-momentum-negative,
    body.dark-theme td.screener-rsi-neg-1 { color: #ff7b7b; font-weight: 700; }
    body.dark-theme td.screener-rsi-pos-2 { color: #22c55e; font-weight: 800; }
    body.dark-theme td.screener-rsi-pos-3 { color: #00c853; font-weight: 900; }
    body.dark-theme td.screener-rsi-neg-2 { color: #ff5252; font-weight: 800; }
    body.dark-theme td.screener-rsi-neg-3 { color: #ef4444; font-weight: 900; }
    body.dark-theme td.screener-comment-ath { color: #00c853; }
    body.dark-theme .result-toolbar { background: #141917; border-color: #2e3431; box-shadow: none; }
    body.dark-theme .selection-count, body.dark-theme .pagination { color: #f2f4f3; }
    body.dark-theme .ticker-chart-link { color: #58a6ff; }
    body.dark-theme .ticker-chart-link:hover { color: #82bfff; }

    /* Screener controls row */
    body.dark-theme .sim-controls { background: #111715; border-bottom-color: #2e3431; }
    body.dark-theme .entry-date-text { color: #f2f4f3; }
    body.dark-theme .sim-search input { background-color: #1a1f1c; border-color: #2e3431; color: #f2f4f3; }
    body.dark-theme .sim-search input:focus { border-color: #00c853; box-shadow: 0 0 0 3px rgba(0,200,83,0.22); }
    body.dark-theme .refine-inline-button { background: #1a1f1c; border-color: #2e3431; color: #f2f4f3; }
    body.dark-theme .refine-inline-count, body.dark-theme .refine-summary-count { background: #00c853; color: #06130b; }
    body.dark-theme .selected-stock-summary { background: #1a1f1c; color: #a8b2ad; }
    body.dark-theme .selected-stock-summary.has-selection { background: #10301f; color: #7ce3a8; }

    /* Refine results */
    body.dark-theme .refine-body { background: #111715; border-top-color: #2e3431; }
    body.dark-theme .refine-label { color: #a8b2ad; }
    body.dark-theme .refine-num-row input { background: #1a1f1c; border-color: #2e3431; color: #f2f4f3; }
    body.dark-theme .refine-string-btn { background: #1a1f1c; border-color: #2e3431; color: #f2f4f3; }
    body.dark-theme .refine-string-panel { background: #1a1f1c; border-color: #2e3431; box-shadow: 0 8px 18px rgba(0,0,0,0.6); }
    body.dark-theme .refine-string-select-all-row { border-bottom-color: #2e3431; }
    body.dark-theme .refine-string-opt { color: #f2f4f3; }
    body.dark-theme .refine-string-clear { background: #1a1f1c; border-top-color: #2e3431; color: #a8b2ad; }
    body.dark-theme .refine-chip { background: #1a1f1c; border-color: #2e3431; color: #f2f4f3; }
    body.dark-theme .refine-active-row { color: #a8b2ad; }
    body.dark-theme .refine-link-clear { color: #58a6ff; }
    body.dark-theme .refine-action-buttons .refine-clear-btn { background: #1a1f1c; border-color: #2e3431; color: #f2f4f3; }
    body.dark-theme .refine-action-buttons .refine-apply-btn { background: #00c853; color: #06130b; }
    body.dark-theme .refine-empty-note { color: #6c7570; }

    /* Watchlist */
    body.dark-theme .watchlist-card { background: #111715; }
    body.dark-theme .watchlist-card-title-row { background: var(--card-head-bg); border-bottom: 1px solid var(--card-head-border); box-shadow: inset 3px 0 0 #f3c736, inset 0 1px 0 rgba(255,255,255,0.08), 0 8px 24px rgba(0,0,0,0.26); }
    body.dark-theme .watchlist-table th { background: #111715; color: #a8b2ad; }
    body.dark-theme .watchlist-table td { border-top-color: #232927; }
    body.dark-theme .watchlist-table-wrap { border-right-color: #2e3431; }
    body.dark-theme .watchlist-ticker-btn { color: #58a6ff; }
    body.dark-theme .watchlist-ticker-btn.active { color: #ffc107; }
    body.dark-theme .watchlist-chart-toolbar { background: #141917; border-bottom-color: #2e3431; }
    body.dark-theme .watchlist-forward-toggle { color: #f2f4f3; }
    body.dark-theme .watchlist-chart-body { background: #111715; }
    body.dark-theme .watchlist-chart-placeholder { color: #6c7570; }
    body.dark-theme .watchlist-run-button:disabled { background: #23292b; color: #6c7570; }
    body.dark-theme .watchlist-run-button.processing,
    body.dark-theme .watchlist-run-button.processing:disabled { background: linear-gradient(90deg, #d4af37 0 var(--run-progress), #23292b var(--run-progress) 100%); color: #111111; cursor: wait; }
    body.dark-theme .watchlist-run-button.report-ready { border-color: rgba(0,200,83,0.5); background: linear-gradient(135deg, #17d16b, #00c853); color: #06130b; box-shadow: 0 6px 16px rgba(0,0,0,0.4); }

    /* Saved reports & history */
    body.dark-theme .saved-report-section, body.dark-theme .section { background: #111715; border-color: #2e3431; box-shadow: 0 14px 34px rgba(0,0,0,0.5); }
    body.dark-theme .saved-report-section h1, body.dark-theme .section h1 { background: var(--card-head-bg); border-bottom: 1px solid var(--card-head-border); box-shadow: inset 3px 0 0 #00c853; }
    body.dark-theme .report-card { background: #1a1f1c; border-color: #2e3431; box-shadow: 0 6px 18px rgba(0,0,0,0.4); }
    body.dark-theme .report-card h2 { color: #f2f4f3; }
    body.dark-theme .report-card p { color: #a8b2ad; }
    body.dark-theme .badge.live { background: #10301f; color: #7ce3a8; border-color: #1f4732; }
    body.dark-theme .badge.muted { background: #1a1f1c; color: #a8b2ad; border-color: #2e3431; }
    body.dark-theme .status { color: #f2f4f3; }
    body.dark-theme .dates { color: #a8b2ad; }
    body.dark-theme .open { background: #00c853; color: #06130b; }
    body.dark-theme .open.live-action { background: #1a1f1c; color: #f2f4f3; border: 1px solid #2e3431; }
    body.dark-theme .empty { color: #6c7570; }
    body.dark-theme .back { background: #1a1f1c; color: #f2f4f3; border: 1px solid #2e3431; }
    body.dark-theme .history-title { background: var(--card-head-bg); border-bottom: 1px solid var(--card-head-border); box-shadow: inset 3px 0 0 #f3c736, inset 0 1px 0 rgba(255,255,255,0.08), 0 8px 24px rgba(0,0,0,0.26); }
    body.dark-theme .history-grid { background: #111715; border-color: #2e3431; box-shadow: 0 14px 34px rgba(0,0,0,0.5); }
    body.dark-theme .history-card { background: #1a1f1c; border-color: #2e3431; box-shadow: 0 6px 16px rgba(0,0,0,0.4); }
    body.dark-theme .history-ticker { color: #58a6ff; }
    body.dark-theme .history-change.up { background: #00c853; color: #06130b; }
    body.dark-theme .history-change.down { background: #ff5252; color: #16090a; }
    body.dark-theme .history-date, body.dark-theme .history-footer { color: #a8b2ad; }
    body.dark-theme .history-values span { background: #232927; color: #f2f4f3; }
    body.dark-theme .history-values em { color: #a8b2ad; }
    body.dark-theme .history-empty { background: #111715; border-color: #2e3431; color: #6c7570; }

    /* Report viewer (dashboard) */
    body.dark-theme .portfolio-subtabs-wrap { background: #0e1210; border-bottom-color: #232927; box-shadow: none; }
    body.dark-theme .portfolio-subtabs { background: #1a1f1c; border-color: #2e3431; box-shadow: none; }
    body.dark-theme .portfolio-subtabs button { color: #a8b2ad; }
    body.dark-theme .portfolio-subtabs button:hover { background: #232927; color: #f2f4f3; }
    body.dark-theme .portfolio-subtabs button.active { background: #00c853; color: #06130b; box-shadow: none; }
    body.dark-theme img { border-color: #2e3431; }
    body.dark-theme .replay-chart { border-color: #2e3431; }
    /* Static report chart PNGs (Account View / All Stocks / Individual Stocks)
       are rendered on a white canvas at report time. In dark mode, invert the
       canvas to dark while hue-rotating so chart colors stay recognizable.
       This also covers previously saved reports with no dark variants. */
    body.dark-theme .fit-image,
    body.dark-theme .single-stock-image,
    body.dark-theme .replay-chart { filter: invert(0.92) hue-rotate(180deg); }
    body.dark-theme .stock-button { background: #1a1f1c; color: #58a6ff; border-color: #2e3431; box-shadow: none; }
    body.dark-theme .stock-button:hover { background: #232927; color: #82bfff; }
    body.dark-theme .stock-button.active { background: #00c853; color: #06130b; }
    body.dark-theme .replay-button { background: #1a1f1c; color: #f2f4f3; }
    body.dark-theme .replay-button:hover { background: #232927; }
    body.dark-theme .replay-button.active { background: #ff5252; color: #16090a; }
    body.dark-theme .live-refresh-banner { background: #1a1f1c; color: #f2f4f3; box-shadow: 0 8px 18px rgba(0,0,0,0.5); }
    body.dark-theme .live-refresh-banner strong { color: #ffc107; }
    body.dark-theme .live-refresh-banner span { color: #a8b2ad; }
    body.dark-theme .screener-report { background: #111715; border-color: #2e3431; box-shadow: 0 14px 34px rgba(0,0,0,0.5); }
    body.dark-theme .screener-summary { background: var(--card-head-bg); border-bottom: 1px solid var(--card-head-border); box-shadow: inset 3px 0 0 #f3c736, inset 0 1px 0 rgba(255,255,255,0.08), 0 8px 24px rgba(0,0,0,0.26); }
    body.dark-theme .screener-kicker { color: #ffc107; }
    body.dark-theme .selected-ticker-list { background: rgba(255,255,255,0.07); }
    body.dark-theme .screener-filters { background: #111715; border-bottom-color: #2e3431; }
    body.dark-theme .screener-filter { background: #1a1f1c; border-color: #2e3431; }
    body.dark-theme .screener-filter span { color: #a8b2ad; }
    body.dark-theme .screener-filter strong { color: #f2f4f3; }
    body.dark-theme .screener-table th { background: #1a201d; color: #e5efe9; }
    body.dark-theme .screener-table td { border-top-color: #232927; }
    body.dark-theme .screener-table td.screener-comment-ath { color: #00c853; }
    body.dark-theme .screener-table tr.selected td:not([class*="screener-change-"]):not([class*="screener-drop-"]):not([class*="screener-rvol-"]):not([class*="screener-position-"]):not([class*="screener-comment-"]) { background: #10301f; }
    body.dark-theme .screener-table tr.selected td[class*="screener-change-"],
    body.dark-theme .screener-table tr.selected td[class*="screener-drop-"],
    body.dark-theme .screener-table tr.selected td[class*="screener-rvol-"],
    body.dark-theme .screener-table tr.selected td[class*="screener-position-"],
    body.dark-theme .screener-table tr.selected td[class*="screener-comment-"] { box-shadow: inset 0 0 0 999px rgba(255,255,255,0.04); }
    body.dark-theme .report-notes { background: #141917; border-top-color: #2e3431; }
    body.dark-theme .report-notes h3 { color: #f2f4f3; }
    body.dark-theme .report-notes-status { color: #a8b2ad; }
    body.dark-theme .report-notes textarea { background: #1a1f1c; border-color: #2e3431; color: #f2f4f3; }
    body.dark-theme .report-notes textarea:focus { border-color: #00c853; box-shadow: 0 0 0 3px rgba(0,200,83,0.18); }

    /* Chart modal */
    body.dark-theme .chart-modal { background: rgba(0,0,0,0.72); }
    body.dark-theme .chart-modal-card { background: #111715; border-color: #2e3431; }
    body.dark-theme .chart-modal-header { background: var(--card-head-bg); border-bottom: 1px solid var(--card-head-border); box-shadow: inset 3px 0 0 #00c853; }
    body.dark-theme .chart-modal-body img { background: #ffffff; border-color: #2e3431; }

    /* Chart popout page */
    body.dark-theme .top { background: #0e1210; color: #f2f4f3; }
    body.dark-theme .tv { background: #1a1f1c; color: #f2f4f3; }
    body.dark-theme .tv:hover { background: #232927; }
    body.dark-theme .nav { background: rgba(255,255,255,0.06); border-color: #2e3431; color: #a8b2ad; }
    body.dark-theme .nav:hover:not(:disabled) { background: rgba(255,255,255,0.14); }
    body.dark-theme .label { background: #141917; color: #a8b2ad; border-bottom-color: #2e3431; }
    body.dark-theme .chart-shell, body.dark-theme .spinner { background: #1b202b; color: #a8b2ad; }
    body.dark-theme .wrap .card img { background: #1b202b; }

    /* Report/dashboard buttons and pills */
    body.dark-theme .dashboard-ready { background: #1a1f1c; border-color: #2e3431; color: #f2f4f3; box-shadow: 0 5px 13px rgba(0,0,0,0.4); }
    body.dark-theme .dashboard-ready:hover { background: #232927; }
"""

# mimetypes has no reliable webfont entries on Windows, so serve them explicitly.
STATIC_CONTENT_TYPES = {".woff2": "font/woff2", ".woff": "font/woff", ".ttf": "font/ttf", ".js": "text/javascript"}

# ----------------------------------------------------------------------------
# Shared dark-theme boot script. Included right after <body> on every page so
# the persisted theme applies before first paint and the header switch stays
# in sync across tabs/pages/reports.
# ----------------------------------------------------------------------------
DUO_THEME_BOOT_SCRIPT = """
<script>
(function () {
    function isDarkStored() {
        try { return localStorage.getItem('duoDarkTheme') === '1'; } catch (error) { return false; }
    }
    function syncToggle(dark) {
        var toggle = document.getElementById('appThemeToggle');
        if (toggle) { toggle.checked = dark; }
    }
    if (isDarkStored()) {
        document.body.classList.add('dark-theme');
    }
    window.duoIsDarkTheme = function () {
        return document.body.classList.contains('dark-theme');
    };
    window.duoSetDarkTheme = function (enabled) {
        var dark = Boolean(enabled);
        document.body.classList.toggle('dark-theme', dark);
        try { localStorage.setItem('duoDarkTheme', dark ? '1' : '0'); } catch (error) {}
        syncToggle(dark);
        document.dispatchEvent(new CustomEvent('duothemechange', { detail: { dark: dark } }));
    };
    document.addEventListener('DOMContentLoaded', function () {
        syncToggle(window.duoIsDarkTheme());
    });
})();
</script>
"""

# Reusable header switch markup (placed next to the clock at top right).
DUO_THEME_TOGGLE_HTML = """
<label class="theme-switch" title="Toggle dark theme">
    <input type="checkbox" id="appThemeToggle" onchange="duoSetDarkTheme(this.checked)">
    <span class="theme-switch-track" aria-hidden="true"></span>
    <span>Dark</span>
</label>
"""


# ============================================================================
# LOGGING HELPERS
# ============================================================================


def log_section(title: str):
    if RICH_AVAILABLE:
        console.print(Panel.fit(title, style="bold cyan"))
    else:
        print("=" * 80)
        print(title)
        print("=" * 80)


def log_info(message: str):
    if RICH_AVAILABLE:
        console.print(f"[bold cyan]INFO[/bold cyan] {message}")
    else:
        print(f"[INFO] {message}")


def log_success(message: str):
    if RICH_AVAILABLE:
        console.print(f"[bold green]OK[/bold green] {message}")
    else:
        print(f"[OK] {message}")


def log_warn(message: str):
    if RICH_AVAILABLE:
        console.print(f"[bold yellow]WARN[/bold yellow] {message}")
    else:
        print(f"[WARN] {message}")


def log_error(message: str):
    if RICH_AVAILABLE:
        console.print(f"[bold red]ERROR[/bold red] {message}")
    else:
        print(f"[ERROR] {message}")


def open_file_in_default_app(path: str) -> None:
    if os.name == "nt":
        os.startfile(os.path.abspath(path))
        return
    raise RuntimeError("Automatic dashboard opening is only configured for Windows.")


# ============================================================================
# CORE HELPERS
# ============================================================================


def read_polygon_key() -> str:
    env_path = os.path.join(SCRIPT_DIR, ".env")
    with open(env_path, "r", encoding="utf-8") as f:
        for line in f:
            if line.startswith("POLYGON_API_KEY="):
                return line.split("=", 1)[1].strip()
    raise ValueError(f"POLYGON_API_KEY not found in {env_path}")


def parse_tickers(raw: str):
    return [t.strip().upper() for t in re.split(r"[,\s\t\n]+", raw) if t.strip()]


def format_tickers(tickers) -> str:
    return ", ".join(sorted({str(ticker).strip().upper() for ticker in tickers if str(ticker).strip()}))


def load_daily_screener_module():
    screener_path = os.path.join(SCRIPT_DIR, "daily_anchor_screener.py")
    if not os.path.exists(screener_path):
        raise FileNotFoundError(f"Daily screener script not found: {screener_path}")
    spec = importlib.util.spec_from_file_location("daily_anchor_screener", screener_path)
    if spec is None or spec.loader is None:
        raise ImportError(f"Unable to load daily screener script: {screener_path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def parse_entry_date(raw: str) -> date:
    cleaned = re.sub(r"\b(\d{1,2})(st|nd|rd|th)\b", r"\1", raw.strip(), flags=re.IGNORECASE)
    formats = [
        "%Y-%m-%d",
        "%d %b %Y",
        "%d %B %Y",
        "%b %d %Y",
        "%B %d %Y",
        "%d-%b-%Y",
        "%d-%B-%Y",
        "%b-%d-%Y",
        "%B-%d-%Y",
    ]
    for fmt in formats:
        try:
            return datetime.strptime(cleaned, fmt).date()
        except ValueError:
            continue
    raise ValueError(f"Invalid entry date: {raw}. Use YYYY-MM-DD, e.g. 2026-08-05, or a month-name format like Aug 5 2026.")


MARKET_HOLIDAYS = {
    "2024-01-01", "2024-01-15", "2024-02-19", "2024-03-29", "2024-05-27",
    "2024-06-19", "2024-07-04", "2024-09-02", "2024-11-28", "2024-12-25",
    "2025-01-01", "2025-01-20", "2025-02-17", "2025-04-18", "2025-05-26",
    "2025-06-19", "2025-07-04", "2025-09-01", "2025-11-27", "2025-12-25",
    "2026-01-01", "2026-01-19", "2026-02-16", "2026-04-03", "2026-05-25",
    "2026-06-19", "2026-07-03", "2026-09-07", "2026-11-26", "2026-12-25",
    "2027-01-01", "2027-01-18", "2027-02-15", "2027-04-15", "2027-05-31",
    "2027-06-18", "2027-07-05", "2027-09-06", "2027-11-25", "2027-12-24",
}


def is_trading_day(value: date) -> bool:
    if value.weekday() >= 5:
        return False
    return value.strftime("%Y-%m-%d") not in MARKET_HOLIDAYS


def get_latest_closed_trading_day(base_date: date):
    candidate = base_date
    while not is_trading_day(candidate):
        candidate -= timedelta(days=1)
    return candidate


def get_nth_previous_trading_day(base_date: date, n: int):
    candidate = base_date
    found = 0
    while found < n:
        candidate -= timedelta(days=1)
        if is_trading_day(candidate):
            found += 1
    return candidate


def get_nth_next_trading_day(base_date: date, n: int):
    candidate = base_date
    found = 0
    while found < n:
        candidate += timedelta(days=1)
        if is_trading_day(candidate):
            found += 1
    return candidate


def build_trading_days(start_dt: date, end_dt: date):
    days = []
    cur = start_dt
    while cur <= end_dt:
        if is_trading_day(cur):
            days.append(cur)
        cur += timedelta(days=1)
    return days


def get_report_live_status(entry_date_obj: date, end_date_obj: date, now_et: datetime | None = None) -> dict:
    now_et = now_et or datetime.now(ZoneInfo("America/New_York"))
    today = now_et.date()
    trading_days = build_trading_days(entry_date_obj, end_date_obj)
    live_sessions = [(index, trading_day) for index, trading_day in enumerate(trading_days) if 1 <= index <= 3]

    current_session = next(((index, trading_day) for index, trading_day in live_sessions if trading_day == today), None)
    if current_session and now_et.time() <= LIVE_REFRESH_END:
        session_index, _session_day = current_session
        live_session = f"T{session_index}"
        if now_et.time() < LIVE_REFRESH_START:
            status = f"Live eligible - Today is {live_session}; live fetch starts at 9:30 AM ET"
        else:
            status = f"Live eligible - Today is {live_session}"
        return {"live_eligible": True, "live_session": live_session, "status": status}

    future_session = next(((index, trading_day) for index, trading_day in live_sessions if trading_day > today), None)
    if future_session:
        session_index, session_day = future_session
        live_session = f"T{session_index}"
        return {
            "live_eligible": True,
            "live_session": live_session,
            "status": f"Live eligible - {live_session} starts {session_day:%a %d %b %Y}",
        }

    if current_session:
        session_index, _session_day = current_session
        return {"live_eligible": False, "live_session": f"T{session_index}", "status": "Completed"}

    if today > end_date_obj:
        status = "Completed"
    elif today < entry_date_obj:
        status = "Upcoming"
    elif today in trading_days:
        session_index = trading_days.index(today)
        status = "T0 today - live starts from T1" if session_index == 0 else "Completed"
    else:
        status = "Historical"

    return {"live_eligible": False, "live_session": "", "status": status}


def get_live_refresh_context(entry_date_str: str, end_date_str: str, now_et: datetime | None = None) -> dict[str, str] | None:
    now_et = now_et or datetime.now(ZoneInfo("America/New_York"))
    if not (LIVE_REFRESH_START <= now_et.time() <= LIVE_REFRESH_END):
        return None

    entry_date_obj = datetime.strptime(entry_date_str, "%Y-%m-%d").date()
    end_date_obj = datetime.strptime(end_date_str, "%Y-%m-%d").date()
    trading_days = build_trading_days(entry_date_obj, end_date_obj)
    today = now_et.date()
    if today not in trading_days:
        return None

    session_index = trading_days.index(today)
    if session_index == 0 or session_index > 3:
        return None

    return {
        "session": f"T{session_index}",
        "date": today.strftime("%a %d %b %Y"),
    }


def fetch_minute_data(ticker: str, start_date: str, end_date: str, api_key: str, interval_minutes: int) -> pd.DataFrame:
    url = (
        f"https://api.massive.com/v2/aggs/ticker/{ticker}/range/{interval_minutes}/minute/"
        f"{start_date}/{end_date}?adjusted=true&sort=asc&limit=50000&apiKey={api_key}"
    )
    response = requests.get(url, timeout=60)
    payload = response.json()

    if "results" not in payload or not payload["results"]:
        return pd.DataFrame()

    df = pd.DataFrame(payload["results"])
    df["timestamp"] = (
        pd.to_datetime(df["t"], unit="ms", utc=True)
        .dt.tz_convert("US/Eastern")
        .dt.tz_localize(None)
    )

    df = df.rename(
        columns={
            "o": "open",
            "h": "high",
            "l": "low",
            "c": "close",
            "v": "volume",
            "vw": "vwap",
            "n": "transactions",
        }
    )

    keep_cols = ["timestamp", "open", "high", "low", "close", "volume", "vwap", "transactions"]
    df = df[keep_cols].copy()

    minutes_since_midnight = df["timestamp"].dt.hour * 60 + df["timestamp"].dt.minute
    df = df[(minutes_since_midnight >= 570) & (minutes_since_midnight <= 960)].copy()
    df["trade_date"] = df["timestamp"].dt.date

    for col in ["open", "high", "low", "close", "vwap", "volume", "transactions"]:
        df[col] = pd.to_numeric(df[col], errors="coerce")

    return df.sort_values("timestamp").reset_index(drop=True)


def fetch_10min_data(ticker: str, start_date: str, end_date: str, api_key: str) -> pd.DataFrame:
    return fetch_minute_data(ticker, start_date, end_date, api_key, BAR_MINUTES)


def fetch_daily_data(ticker: str, start_date: str, end_date: str, api_key: str) -> pd.DataFrame:
    url = (
        f"https://api.massive.com/v2/aggs/ticker/{ticker}/range/1/day/"
        f"{start_date}/{end_date}?adjusted=true&sort=asc&limit=50000&apiKey={api_key}"
    )
    response = requests.get(url, timeout=60)
    payload = response.json()
    if "results" not in payload or not payload["results"]:
        return pd.DataFrame()

    df = pd.DataFrame(payload["results"])
    df["date"] = pd.to_datetime(df["t"], unit="ms", utc=True).dt.tz_convert("US/Eastern").dt.date
    df = df.rename(
        columns={
            "o": "open",
            "h": "high",
            "l": "low",
            "c": "close",
            "v": "volume",
        }
    )
    keep_cols = ["date", "open", "high", "low", "close", "volume"]
    df = df[keep_cols].copy()
    for col in ["open", "high", "low", "close", "volume"]:
        df[col] = pd.to_numeric(df[col], errors="coerce")
    return df.dropna(subset=["close"]).sort_values("date").reset_index(drop=True)


def load_daily_chart_dataset(ticker: str, anchor_date: str = "", compact: bool = False, forward: bool = False) -> dict:
    """Fetch daily OHLCV and compute the EMA21/Keltner/PPO series shared by the
    PNG renderer and the interactive chart JSON payload."""
    ticker = ticker.strip().upper()
    if not re.fullmatch(r"[A-Z0-9.\-]{1,12}", ticker):
        raise ValueError(f"Invalid ticker: {ticker!r}")

    api_key = read_polygon_key()
    end_day = datetime.now(ZoneInfo("America/New_York")).date()
    anchor_day = None
    if anchor_date:
        anchor_day = datetime.strptime(anchor_date, "%Y-%m-%d").date()
        if anchor_day < end_day and forward:
            end_day = min(get_nth_next_trading_day(anchor_day, 15), end_day)
        else:
            end_day = anchor_day
    # Use a deeper warm-up window so EMA-based PPO/Signal align with charting tools
    # that compute indicators from much longer history.
    start_day = end_day - timedelta(days=DAILY_CHART_PPO_WARMUP_CALENDAR_DAYS)
    df = fetch_daily_data(ticker, start_day.isoformat(), end_day.isoformat(), api_key)
    if df.empty:
        raise ValueError(f"No daily data returned for {ticker}")

    chart_df = df.rename(
        columns={"date": "Date", "open": "Open", "high": "High", "low": "Low", "close": "Close", "volume": "Volume"}
    )
    chart_df["Date"] = pd.to_datetime(chart_df["Date"])
    chart_df = chart_df.set_index("Date")
    chart_df = chart_df[["Open", "High", "Low", "Close", "Volume"]].astype(float)

    n_display = 132
    ema21_full = chart_df["Close"].ewm(span=21, adjust=False).mean()
    previous_close = chart_df["Close"].shift(1)
    true_range = pd.concat(
        [
            chart_df["High"] - chart_df["Low"],
            (chart_df["High"] - previous_close).abs(),
            (chart_df["Low"] - previous_close).abs(),
        ],
        axis=1,
    ).max(axis=1)
    atr10_full = true_range.ewm(alpha=1 / 10, adjust=False).mean()
    kc_u1_full = ema21_full + atr10_full
    kc_l1_full = ema21_full - atr10_full
    kc_u2_full = ema21_full + 2 * atr10_full
    kc_l2_full = ema21_full - 2 * atr10_full
    kc_u3_full = ema21_full + 3 * atr10_full
    kc_l3_full = ema21_full - 3 * atr10_full
    kc_u4_full = ema21_full + 4 * atr10_full
    kc_l4_full = ema21_full - 4 * atr10_full
    kc_u5_full = ema21_full + 5 * atr10_full
    kc_l5_full = ema21_full - 5 * atr10_full
    sma4_full = chart_df["Close"].rolling(window=4, min_periods=4).mean()
    sma9_full = chart_df["Close"].rolling(window=9, min_periods=9).mean()
    sma18_full = chart_df["Close"].rolling(window=18, min_periods=18).mean()

    close = chart_df["Close"]
    ema12 = close.ewm(span=12, adjust=False).mean()
    ema26 = close.ewm(span=26, adjust=False).mean()
    ppo_full = ((ema12 - ema26) / ema26) * 100.0
    signal_full = ppo_full.ewm(span=9, adjust=False).mean()
    histogram_full = ppo_full - signal_full

    anchor_index = None
    if anchor_day is not None:
        anchor_ts = pd.Timestamp(anchor_day)
        prior_or_anchor = chart_df.index[chart_df.index <= anchor_ts]
        if len(prior_or_anchor):
            anchor_index = chart_df.index.get_loc(prior_or_anchor[-1])
    if anchor_index is None:
        anchor_index = len(chart_df) - 1
    extension_count = max(0, len(chart_df) - anchor_index - 1)
    start_index = max(0, anchor_index - n_display + 1)
    visible_slice = slice(start_index, len(chart_df))
    visible_anchor_index = anchor_index - start_index
    show_anchor_latest_overlay = SHOW_CHART_ANCHOR_LATEST_OVERLAY and extension_count > 0

    def trim(series: pd.Series) -> pd.Series:
        return series.iloc[visible_slice]

    chart_df = chart_df.iloc[visible_slice]
    ema21 = trim(ema21_full)
    kc_u1 = trim(kc_u1_full)
    kc_l1 = trim(kc_l1_full)
    kc_u2 = trim(kc_u2_full)
    kc_l2 = trim(kc_l2_full)
    kc_u3 = trim(kc_u3_full)
    kc_l3 = trim(kc_l3_full)
    kc_u4 = trim(kc_u4_full)
    kc_l4 = trim(kc_l4_full)
    kc_u5 = trim(kc_u5_full)
    kc_l5 = trim(kc_l5_full)
    ppo = trim(ppo_full)
    signal = trim(signal_full)
    histogram = trim(histogram_full)
    sma4 = trim(sma4_full)
    sma9 = trim(sma9_full)
    sma18 = trim(sma18_full)
    hist_rising = histogram.diff() > 0
    hist_pos_strong = histogram.where((histogram >= 0) & hist_rising)
    hist_pos_light = histogram.where((histogram >= 0) & ~hist_rising)
    hist_neg_strong = histogram.where((histogram < 0) & ~hist_rising)
    hist_neg_light = histogram.where((histogram < 0) & hist_rising)

    return {
        "ticker": ticker,
        "chart_df": chart_df,
        "ema21": ema21,
        "kc_upper": [kc_u1, kc_u2, kc_u3, kc_u4, kc_u5],
        "kc_lower": [kc_l1, kc_l2, kc_l3, kc_l4, kc_l5],
        "ppo": ppo,
        "signal": signal,
        "histogram": histogram,
        "sma4": sma4,
        "sma9": sma9,
        "sma18": sma18,
        "hist_pos_strong": hist_pos_strong,
        "hist_pos_light": hist_pos_light,
        "hist_neg_strong": hist_neg_strong,
        "hist_neg_light": hist_neg_light,
        "visible_anchor_index": visible_anchor_index,
        "extension_count": extension_count,
        "show_anchor_latest_overlay": show_anchor_latest_overlay,
    }


def build_daily_ppo_chart_png(ticker: str, anchor_date: str = "", compact: bool = False, dark: bool = False, forward: bool = False) -> bytes:
    import mplfinance as mpf

    dataset = load_daily_chart_dataset(ticker, anchor_date, compact, forward)
    ticker = dataset["ticker"]
    chart_df = dataset["chart_df"]
    ema21 = dataset["ema21"]
    kc_u1, kc_u2, kc_u3, kc_u4, kc_u5 = dataset["kc_upper"]
    kc_l1, kc_l2, kc_l3, kc_l4, kc_l5 = dataset["kc_lower"]
    ppo = dataset["ppo"]
    signal = dataset["signal"]
    histogram = dataset["histogram"]
    hist_pos_strong = dataset["hist_pos_strong"]
    hist_pos_light = dataset["hist_pos_light"]
    hist_neg_strong = dataset["hist_neg_strong"]
    hist_neg_light = dataset["hist_neg_light"]
    visible_anchor_index = dataset["visible_anchor_index"]
    extension_count = dataset["extension_count"]
    show_anchor_latest_overlay = dataset["show_anchor_latest_overlay"]

    kc_upper_series = [kc_u1, kc_u2, kc_u3, kc_u4, kc_u5]
    kc_lower_series = [kc_l1, kc_l2, kc_l3, kc_l4, kc_l5]
    kc_upper_colors = ["#00ACC1", "#0097A7", "#00838F", "#006064", "#00474D"]
    kc_lower_colors = ["#EF5350", "#E53935", "#C62828", "#B71C1C", "#7F0000"]
    last_close = float(chart_df["Close"].iloc[-1])
    mid_value = float(ema21.iloc[-1])
    upper_count = 3
    lower_count = 3

    apds = [
        mpf.make_addplot(ema21, color="#2962FF", width=0.9),
        *[
            mpf.make_addplot(kc_upper_series[index], color=kc_upper_colors[index], width=0.8, linestyle="-", alpha=0.75)
            for index in range(upper_count)
        ],
        *[
            mpf.make_addplot(kc_lower_series[index], color=kc_lower_colors[index], width=0.8, linestyle="-", alpha=0.75)
            for index in range(lower_count)
        ],
        mpf.make_addplot(ppo, panel=2, color="#2962FF", width=1.44, secondary_y=False),
        mpf.make_addplot(signal, panel=2, color="#FF9800", width=1.31, secondary_y=False),
    ]
    hist_bar_defs = [
        (hist_pos_strong, "#26a69a", 0.95),
        (hist_pos_light, "#b2dfdb", 0.95),
        (hist_neg_strong, "#ef5350", 0.95),
        (hist_neg_light, "#ffcdd2", 0.95),
    ]
    for hist_series, hist_color, hist_alpha in hist_bar_defs:
        if hist_series.notna().any():
            apds.append(
                mpf.make_addplot(
                    hist_series,
                    panel=2,
                    type="bar",
                    color=hist_color,
                    alpha=hist_alpha,
                    secondary_y=False,
                )
            )

    chart_face = "#202530" if dark else "#ffffff"
    figure_face = "#1b202b" if dark else "#ffffff"
    axis_text_color = "#cbd5e1" if dark else "#111827"
    date_text_color = "#cbd5e1" if dark else "#333333"
    spine_color = "#303746" if dark else "#dddddd"
    grid_color = chart_face if compact else ("#2b3240" if dark else "#f0f0f0")
    market_colors = mpf.make_marketcolors(
        up=chart_face if dark else "#ffffff",
        down=chart_face if dark else "#000000",
        wick={"up": chart_face if dark else "#000000", "down": chart_face if dark else "#000000"},
        edge={"up": chart_face if dark else "#000000", "down": chart_face if dark else "#000000"},
        volume={
            "up": (0 / 255, 169 / 255, 157 / 255, 0.58) if dark else (8 / 255, 153 / 255, 129 / 255, 0.55),
            "down": (255 / 255, 51 / 255, 74 / 255, 0.58) if dark else (242 / 255, 54 / 255, 69 / 255, 0.55),
        },
    )
    style = mpf.make_mpf_style(
        marketcolors=market_colors,
        facecolor=chart_face,
        figcolor=figure_face,
        gridcolor=grid_color,
        gridstyle="-",
        rc={
            "axes.grid": not compact,
            "axes.spines.top": False,
            "axes.spines.left": False,
            "axes.spines.right": True,
            "axes.spines.bottom": True,
            "axes.edgecolor": spine_color,
            "font.family": "sans-serif",
            "font.size": 8,
            "xtick.color": date_text_color,
            "ytick.color": axis_text_color,
            "xtick.labelsize": 8,
            "ytick.labelsize": 11,
            "ytick.right": True,
            "ytick.left": False,
            "ytick.labelright": True,
            "ytick.labelleft": False,
            "text.color": axis_text_color,
        },
    )

    panel_ratios = (4.4, 0.78, 1.35) if compact else (6.4, 1.2, 2.2)
    figsize = (16.5, 6.65) if compact else (16.5, 10)
    fig, axes = mpf.plot(
        chart_df,
        type="candle",
        style=style,
        volume=True,
        addplot=apds,
        panel_ratios=panel_ratios,
        returnfig=True,
        figsize=figsize,
        title="",
        datetime_format="%b %d",
        xrotation=90,
        tight_layout=True,
        update_width_config={"candle_linewidth": 0.85},
    )

    for axis in fig.axes:
        axis.spines["left"].set_visible(False)
        axis.spines["top"].set_visible(False)
        axis.spines["right"].set_color(spine_color)
        axis.spines["bottom"].set_color(spine_color)
        axis.set_facecolor(chart_face)
        if compact:
            axis.grid(False)
        axis.yaxis.tick_right()
        axis.yaxis.set_label_position("right")
        axis.set_ylabel("")
        axis.tick_params(axis="y", which="both", left=False, right=True, labelright=True, labelleft=False, colors=axis_text_color, length=3, width=0.7, labelsize=11, pad=6)
        axis.tick_params(axis="x", colors=date_text_color, length=3, width=0.7, labelsize=8)

    seen_positions = set()
    for axis in fig.axes:
        pos_key = tuple(round(value, 3) for value in axis.get_position().bounds)
        if pos_key in seen_positions:
            axis.set_yticklabels([])
            axis.tick_params(axis="y", which="both", left=False, right=False, labelleft=False, labelright=False)
        seen_positions.add(pos_key)

    ax_price = fig.axes[0]
    ax_ppo = fig.axes[-2] if len(fig.axes) >= 4 else None
    if dark:
        previous_visible_close = chart_df["Close"].shift(1)
        previous_visible_close.iloc[0] = chart_df["Open"].iloc[0]
        candle_width = 0.58
        min_body_height = max((float(chart_df["High"].max()) - float(chart_df["Low"].min())) * 0.0015, 1e-6)
        for index, (_, row) in enumerate(chart_df.iterrows()):
            open_value = float(row["Open"])
            high_value = float(row["High"])
            low_value = float(row["Low"])
            close_value = float(row["Close"])
            previous_close = float(previous_visible_close.iloc[index])
            candle_color = WATCHLIST_CANDLE_UP_COLOR if close_value >= previous_close else WATCHLIST_CANDLE_DOWN_COLOR
            is_hollow = close_value >= open_value
            body_bottom = min(open_value, close_value)
            body_height = max(abs(close_value - open_value), min_body_height)
            if abs(close_value - open_value) < min_body_height:
                body_bottom -= min_body_height / 2
            ax_price.vlines(index, low_value, high_value, color=candle_color, linewidth=0.75, zorder=8)
            ax_price.add_patch(
                Rectangle(
                    (index - candle_width / 2, body_bottom),
                    candle_width,
                    body_height,
                    facecolor=chart_face if is_hollow else candle_color,
                    edgecolor=candle_color,
                    linewidth=0.75,
                    zorder=9,
                )
            )
    ax_price.text(
        0.5,
        0.18,
        ticker,
        transform=ax_price.transAxes,
        ha="center",
        va="center",
        fontsize=50 if compact else 67,
        fontweight="800",
        color="#ffffff" if dark else "#353945",
        alpha=0.044 if dark else 0.054,
        zorder=1,
    )
    last_close = float(chart_df["Close"].iloc[-1])
    last_open = float(chart_df["Open"].iloc[-1])
    price_color = "#089981" if last_close >= last_open else "#f23645"
    x_index = range(len(chart_df))
    if last_close >= mid_value:
        ax_price.fill_between(x_index, ema21.values, kc_u1.values, color="#00ACC1", alpha=0.075, zorder=0)
        ax_price.fill_between(x_index, kc_l1.values, ema21.values, color="#EF5350", alpha=0.0375, zorder=0)
    else:
        ax_price.fill_between(x_index, kc_l1.values, ema21.values, color="#EF5350", alpha=0.075, zorder=0)
        ax_price.fill_between(x_index, ema21.values, kc_u1.values, color="#00ACC1", alpha=0.0375, zorder=0)

    y_min_visible, y_max_visible = ax_price.get_ylim()
    kc_label_defs = [(ema21, "Mid", "#2962FF", 1.0)]
    kc_label_defs.extend((series, f"U{index + 1}", kc_upper_colors[index], 0.90) for index, series in enumerate(kc_upper_series[:upper_count]))
    kc_label_defs.extend((series, f"L{index + 1}", kc_lower_colors[index], 0.90) for index, series in enumerate(kc_lower_series[:lower_count]))
    for series, label, color, alpha in kc_label_defs:
        y_value = float(series.iloc[-1])
        if y_min_visible <= y_value <= y_max_visible:
            ax_price.annotate(
                label,
                xy=(1.0, y_value),
                xycoords=("axes fraction", "data"),
                xytext=(42, 0),
                textcoords="offset points",
                ha="left",
                va="center",
                fontsize=7.5,
                fontweight="700",
                color=color,
                alpha=alpha,
                clip_on=False,
            )

    anchor_close = float(chart_df["Close"].iloc[visible_anchor_index])
    anchor_high = float(chart_df["High"].iloc[visible_anchor_index])
    anchor_low = float(chart_df["Low"].iloc[visible_anchor_index])
    latest_high = float(chart_df["High"].iloc[-1])
    y_min_current, y_max_current = ax_price.get_ylim()
    y_range = max(1e-9, float(y_max_current - y_min_current))
    anchor_star_y = anchor_low - (y_range * 0.04)
    anchor_upper_star_y = anchor_high + (y_range * 0.04)
    latest_star_y = latest_high + (y_range * 0.04)
    new_y_min = min(y_min_current, anchor_star_y - (y_range * 0.02))
    new_y_max = max(y_max_current, anchor_upper_star_y + (y_range * 0.02), latest_star_y + (y_range * 0.02))
    if new_y_min < y_min_current or new_y_max > y_max_current:
        ax_price.set_ylim(new_y_min, new_y_max)
    ax_price.scatter(
        [visible_anchor_index],
        [anchor_star_y],
        marker="*",
        s=110,
        color="#f5c842",
        edgecolors="#7a5b00",
        linewidths=0.6,
        zorder=6,
    )
    ax_price.scatter(
        [visible_anchor_index],
        [anchor_upper_star_y],
        marker="*",
        s=110,
        color="#f5c842",
        edgecolors="#7a5b00",
        linewidths=0.6,
        zorder=6,
    )

    latest_x_start = max(0, min(visible_anchor_index, len(chart_df) - 1))
    latest_x_end = len(chart_df) - 0.5
    latest_line_color = "#16a34a" if last_close > anchor_close else "#dc2626"
    if show_anchor_latest_overlay and latest_x_end >= latest_x_start:
        if show_anchor_latest_overlay and abs(last_close - anchor_close) > 1e-9:
            ax_price.fill_between(
                [latest_x_start, latest_x_end],
                [anchor_close, anchor_close],
                [last_close, last_close],
                color=latest_line_color,
                alpha=0.045,
                zorder=2,
            )
        ax_price.plot(
            [latest_x_start, latest_x_end],
            [last_close, last_close],
            color=latest_line_color,
            linewidth=1.0,
            linestyle="-",
            alpha=0.95,
            zorder=3,
        )
        if anchor_close != 0:
            y_min_current, y_max_current = ax_price.get_ylim()
            y_range = max(1e-9, float(y_max_current - y_min_current))
            if last_close > anchor_close:
                label_y = min(y_max_current - (y_range * 0.015), last_close + (y_range * 0.02))
                label_va = "bottom"
            else:
                label_y = max(y_min_current + (y_range * 0.015), last_close - (y_range * 0.02))
                label_va = "top"
            delta_pct = ((last_close - anchor_close) / anchor_close) * 100.0
            label_x = max(latest_x_start + 0.25, (len(chart_df) - 1) - 2)
            ax_price.annotate(
                f"{delta_pct:+.1f}%",
                xy=(label_x, label_y),
                xytext=(0, 0),
                textcoords="offset points",
                ha="right",
                va=label_va,
                fontsize=12,
                fontweight="700",
                color="#ffffff",
                bbox={"boxstyle": "round,pad=0.3", "facecolor": latest_line_color, "edgecolor": "none", "alpha": 0.95},
                zorder=6,
                clip_on=False,
            )
    ax_price.annotate(
        f" {last_close:.2f} ",
        xy=(1.0, last_close),
        xycoords=("axes fraction", "data"),
        xytext=(4, 0),
        textcoords="offset points",
        ha="left",
        va="center",
        fontsize=8,
        fontweight="bold",
        color="#ffffff",
        zorder=5,
        bbox={"boxstyle": "round,pad=0.25", "facecolor": price_color, "edgecolor": "none", "alpha": 0.95},
        clip_on=False,
    )

    volume_axis = fig.axes[2] if len(fig.axes) > 2 else None
    if volume_axis is not None:
        volume_axis.set_facecolor("#242a36" if dark else "#f4f7fb")
        volume_axis.spines["top"].set_visible(True)
        volume_axis.spines["top"].set_color("#303746" if dark else "#cbd5e1")
        volume_axis.spines["top"].set_linewidth(0.9)
        volume_axis.tick_params(axis="y", labelsize=10, pad=6)
        volume_axis.yaxis.set_major_formatter(
            FuncFormatter(lambda value, _: f"{value / 1e6:.0f}M" if value >= 1e6 else f"{value / 1e3:.0f}K" if value >= 1e3 else str(int(value)))
        )
        for patch in volume_axis.patches:
            width = patch.get_width()
            new_width = width * 0.75
            patch.set_x(patch.get_x() + (width - new_width) / 2)
            patch.set_width(new_width)
            patch.set_edgecolor("none")

    if ax_ppo is not None:
        all_ppo_values = pd.concat([ppo, signal, histogram]).dropna()
        if len(all_ppo_values):
            y_low = float(all_ppo_values.min())
            y_high = float(all_ppo_values.max())
            margin = max(abs(y_low), abs(y_high), 1e-9) * 0.14
            ax_ppo.set_ylim(y_low - margin, y_high + margin)
        ax_ppo.tick_params(axis="y", labelsize=10, pad=6)
        ax_ppo.axhline(0, color="#6b7280" if dark else "#bbbbbb", linewidth=0.9, zorder=2)
        ax_ppo.text(0.01, 0.95, "PPO (12, 26, 9)", transform=ax_ppo.transAxes, fontsize=8, color="#2962FF", va="top", ha="left", alpha=0.9)
        if len(chart_df) and pd.notna(ppo.iloc[-1]) and pd.notna(signal.iloc[-1]):
            ppo_last = float(ppo.iloc[-1])
            signal_last = float(signal.iloc[-1])
            relation = "PPO > Signal" if ppo_last > signal_last else "PPO < Signal" if ppo_last < signal_last else "PPO = Signal"
            ax_ppo.text(
                0.01,
                0.86,
                f"Blue(PPO): {ppo_last:.2f}%  Orange(Signal): {signal_last:.2f}%  [{relation}]",
                transform=ax_ppo.transAxes,
                fontsize=7.5,
                color="#475569" if not dark else "#94a3b8",
                va="top",
                ha="left",
                alpha=0.95,
            )
            last_x = len(chart_df) - 1
            ax_ppo.scatter([last_x], [ppo_last], s=23, color="#2962FF", zorder=5)
            ax_ppo.scatter([last_x], [signal_last], s=23, color="#FF9800", zorder=5)

    bottom_axis = sorted(fig.axes, key=lambda axis: axis.get_position().y0)[0]
    dates = list(chart_df.index)
    tick_positions = []
    tick_labels = []
    for index, date_value in enumerate(dates):
        if not tick_positions or dates[tick_positions[-1]].month != date_value.month:
            tick_labels.append(f"{date_value.strftime('%b')} {date_value.day}")
        else:
            tick_labels.append(str(date_value.day))
        tick_positions.append(index)
    max_labels = 28
    if len(tick_positions) > max_labels:
        step = max(1, round(len(tick_positions) / max_labels))
        tick_positions = tick_positions[::step]
        tick_labels = tick_labels[::step]
    bottom_axis.set_xticks(tick_positions)
    bottom_axis.set_xticklabels(tick_labels, rotation=0, ha="center", fontsize=8, color=date_text_color)

    fig.patch.set_linewidth(1.8)
    fig.patch.set_edgecolor("#303746" if dark else "#aaaaaa")

    buffer = io.BytesIO()
    fig.savefig(buffer, format="png", dpi=190, bbox_inches="tight", facecolor=fig.get_facecolor())
    plt.close(fig)
    return buffer.getvalue()


def build_daily_chart_json_payload(ticker: str, anchor_date: str = "", compact: bool = False, forward: bool = False) -> dict:
    """Serialize the daily chart dataset so the browser can render a fully
    interactive chart (crosshair, zoom, live values) instead of a static PNG."""
    dataset = load_daily_chart_dataset(ticker, anchor_date, compact, forward)
    chart_df = dataset["chart_df"]

    def line_points(series: pd.Series, digits: int = 6) -> list[dict]:
        return [
            {"time": ts.strftime("%Y-%m-%d"), "value": round(float(value), digits)}
            for ts, value in series.items()
            if pd.notna(value)
        ]

    candles = []
    volume = []
    for ts, row in chart_df.iterrows():
        day = ts.strftime("%Y-%m-%d")
        candles.append(
            {
                "time": day,
                "open": round(float(row["Open"]), 4),
                "high": round(float(row["High"]), 4),
                "low": round(float(row["Low"]), 4),
                "close": round(float(row["Close"]), 4),
            }
        )
        volume.append({"time": day, "value": float(row["Volume"])})

    triple_ma = []
    sma4_series = dataset["sma4"]
    sma9_series = dataset["sma9"]
    sma18_series = dataset["sma18"]
    for ts in chart_df.index:
        sma4_value = sma4_series.loc[ts]
        sma9_value = sma9_series.loc[ts]
        sma18_value = sma18_series.loc[ts]
        aligned = (
            pd.notna(sma4_value)
            and pd.notna(sma9_value)
            and pd.notna(sma18_value)
            and float(sma4_value) > float(sma9_value) > float(sma18_value)
        )
        triple_ma.append({"time": ts.strftime("%Y-%m-%d"), "value": 1, "aligned": bool(aligned)})

    anchor_idx = int(dataset["visible_anchor_index"])
    anchor_time = chart_df.index[anchor_idx].strftime("%Y-%m-%d") if len(chart_df) else ""
    return {
        "ticker": dataset["ticker"],
        "anchor": anchor_date or "",
        "anchorTime": anchor_time,
        "forward": bool(forward),
        "extensionCount": int(dataset["extension_count"]),
        "lastClose": float(chart_df["Close"].iloc[-1]),
        "anchorClose": float(chart_df["Close"].iloc[anchor_idx]),
        "candles": candles,
        "volume": volume,
        "ema21": line_points(dataset["ema21"], 4),
        "kcUpper": [line_points(series, 4) for series in dataset["kc_upper"][:3]],
        "kcLower": [line_points(series, 4) for series in dataset["kc_lower"][:3]],
        "ppo": line_points(dataset["ppo"]),
        "signal": line_points(dataset["signal"]),
        "histogram": line_points(dataset["histogram"]),
        "sma4": line_points(dataset["sma4"], 4),
        "sma9": line_points(dataset["sma9"], 4),
        "sma18": line_points(dataset["sma18"], 4),
        "tripleMa": triple_ma,
    }


def get_cached_daily_chart_json_payload(ticker: str, anchor_date: str = "", compact: bool = False, forward: bool = False) -> dict:
    cache_key = (str(ticker or "").strip().upper(), str(anchor_date or "").strip(), bool(compact), bool(forward))
    with DAILY_CHART_JSON_CACHE_LOCK:
        cached_payload = DAILY_CHART_JSON_CACHE.get(cache_key)
        if cached_payload is not None:
            return copy.deepcopy(cached_payload)
    payload = build_daily_chart_json_payload(ticker, anchor_date, compact, forward)
    with DAILY_CHART_JSON_CACHE_LOCK:
        if len(DAILY_CHART_JSON_CACHE) >= DAILY_CHART_JSON_CACHE_LIMIT:
            DAILY_CHART_JSON_CACHE.pop(next(iter(DAILY_CHART_JSON_CACHE)))
        DAILY_CHART_JSON_CACHE[cache_key] = copy.deepcopy(payload)
    return payload


DUO_CHART_LIB_JS = r"""
/* Duo interactive chart renderer — TradingView Lightweight Charts v5. */
(function () {
  'use strict';

  var KC_UP_COLORS = ['#00ACC1', '#0097A7', '#00838F'];
  var KC_DOWN_COLORS = ['#EF5350', '#E53935', '#C62828'];
  var CHART_DATA_CACHE = new Map();

  function palette(dark) {
    return dark ? {
      bg: '#1b202b', text: '#cbd5e1', grid: '#2b3240', border: '#303746',
      crosshair: '#8d97ad', zeroLine: '#6b7280',
      up: '#4ade80', down: '#ff334a',
      volUp: 'rgba(74,222,128,0.45)', volDown: 'rgba(255,51,74,0.45)',
      histUp: '#26a69a', histUpLight: '#b2dfdb',
      histDown: '#ef5350', histDownLight: '#ffcdd2',
      chipBg: 'rgba(53, 57, 69, 0.95)', chipBorder: 'rgba(255, 255, 255, 0.16)', chipText: '#cbd5e1',
      legendBg: 'rgba(53, 57, 69, 0.95)', legendBorder: '#303746'
    } : {
      bg: '#ffffff', text: '#353945', grid: '#f0f0f0', border: '#dedfe5',
      crosshair: '#9aa3b8', zeroLine: '#bbbbbb',
      up: '#089981', down: '#f23645',
      volUp: 'rgba(8,153,129,0.4)', volDown: 'rgba(242,54,69,0.4)',
      histUp: '#26a69a', histUpLight: '#b2dfdb',
      histDown: '#ef5350', histDownLight: '#ffcdd2',
      chipBg: 'rgba(76, 82, 99, 0.95)', chipBorder: 'rgba(255, 255, 255, 0.20)', chipText: '#f3f3f5',
      legendBg: 'rgba(76, 82, 99, 0.95)', legendBorder: '#dedfe5'
    };
  }

  function fmt(v, digits) {
    return (v === null || v === undefined || isNaN(v)) ? '—' : Number(v).toFixed(digits === undefined ? 2 : digits);
  }

  function fmtVol(v) {
    if (v === null || v === undefined || isNaN(v)) return '—';
    if (v >= 1e9) return (v / 1e9).toFixed(2) + 'B';
    if (v >= 1e6) return (v / 1e6).toFixed(2) + 'M';
    if (v >= 1e3) return (v / 1e3).toFixed(1) + 'K';
    return String(Math.round(v));
  }

  function ensureStyle() {
    if (document.getElementById('duo-chart-lib-style')) return;
    var style = document.createElement('style');
    style.id = 'duo-chart-lib-style';
    style.textContent =
      '.duo-chart-status{display:flex;align-items:center;justify-content:center;width:100%;height:100%;min-height:140px;color:#868ea5;font-size:12px;letter-spacing:.3px;}' +
      '.duo-chart-root{position:relative;width:100%;height:100%;}' +
      // Lightweight Charts lays its panes out with an internal <table>, and the
      // host app styles bare table/td elements (table{width:100%},
      // td:first-child{width:70px}, borders, padding, row striping). Those rules
      // leak in and reserve a phantom ~70px first column for the hidden left
      // price scale, which pushes every series to the right and leaves a dead
      // strip between the ticker column and the first bar. Neutralise them for
      // everything inside the chart root.
      '.duo-chart-root table{width:auto;border-collapse:separate;border-spacing:0;font-size:inherit;}' +
      '.duo-chart-root table tr,.duo-chart-root table td,.duo-chart-root table th{background:none;border:0;padding:0;margin:0;text-align:left;vertical-align:top;white-space:normal;width:auto;}' +
      '.duo-chart-root table td:first-child,.duo-chart-root table th:first-child{width:auto;text-align:left;}' +
      '.duo-chart-root table tbody tr,.duo-chart-root table tbody tr:hover{background:none;}' +
      '.duo-chart-watermark{position:absolute;inset:0;display:flex;align-items:center;justify-content:center;pointer-events:none;z-index:1;font-family:"IBM Plex Sans",system-ui,sans-serif;font-weight:700;white-space:nowrap;font-variant-numeric:tabular-nums;user-select:none;}' +
      '.duo-chart-legend{position:absolute;top:6px;left:8px;z-index:5;display:flex;flex-wrap:wrap;align-items:center;gap:6px;pointer-events:none;font:11px/1.35 "IBM Plex Sans",system-ui,sans-serif;font-variant-numeric:tabular-nums;user-select:none;}' +
      '.duo-chart-legend.in-toolbar{position:static;top:auto;left:auto;z-index:auto;flex-wrap:nowrap;}' +
      '.duo-chart-chip{display:inline-flex;align-items:center;gap:5px;padding:3px 8px;border-radius:5px;border:1px solid transparent;white-space:nowrap;box-shadow:0 2px 6px rgba(0,0,0,0.18);backdrop-filter:blur(4px);pointer-events:none;}' +
      '.duo-chart-legend.in-toolbar .duo-chart-chip{font-size:11.5px;padding:2px 6px;line-height:1.25;box-shadow:none;}';
    document.head.appendChild(style);
  }

  function chartOptions(p, compact) {
    return {
      autoSize: true,
      layout: {
        background: { type: 'solid', color: p.bg },
        textColor: p.text,
        fontSize: compact ? 10 : 12,
        attributionLogo: false
      },
      grid: {
        vertLines: { color: p.grid, visible: false },
        horzLines: { color: p.grid, visible: false }
      },
      rightPriceScale: { borderColor: p.border, minimumWidth: compact ? 56 : 72 },
      timeScale: { borderColor: p.border, rightOffset: compact ? 0 : 4, timeVisible: false },
      crosshair: {
        mode: LightweightCharts.CrosshairMode.Normal,
        vertLine: { color: p.crosshair, width: 1, style: LightweightCharts.LineStyle.Dashed, labelBackgroundColor: p.crosshair },
        horzLine: { color: p.crosshair, width: 1, style: LightweightCharts.LineStyle.Dashed, labelBackgroundColor: p.crosshair }
      }
    };
  }

  function mount(container, opts) {
    if (!window.LightweightCharts) {
      return Promise.reject(new Error('Interactive chart library failed to load.'));
    }
    ensureStyle();
    if (container.__duoChartHandle) {
      container.__duoChartHandle.destroy();
      container.__duoChartHandle = null;
    }
    container.innerHTML = '<div class="duo-chart-status">Loading chart…</div>';

    var params = new URLSearchParams();
    params.set('ticker', opts.ticker);
    if (opts.anchor) params.set('anchor', opts.anchor);
    if (opts.compact) params.set('compact', 'watchlist');
    if (opts.forward) params.set('forward', '1');
    var cacheKey = [String(opts.ticker || '').toUpperCase(), opts.anchor || '', opts.compact ? 'watchlist' : 'full', opts.forward ? 'forward' : 'anchor'].join('|');

    var dataPromise = CHART_DATA_CACHE.get(cacheKey);
    if (!dataPromise) {
      dataPromise = fetch('/ticker-data?' + params.toString(), { cache: 'no-store' }).then(function (resp) {
        if (!resp.ok) {
          return resp.json().catch(function () { return {}; }).then(function (body) {
            throw new Error((body && body.error) || 'Chart unavailable');
          });
        }
        return resp.json();
      }).catch(function (err) {
        CHART_DATA_CACHE.delete(cacheKey);
        throw err;
      });
      CHART_DATA_CACHE.set(cacheKey, dataPromise);
    }

    return dataPromise.then(function (data) {
      container.innerHTML = '';
      var root = document.createElement('div');
      root.className = 'duo-chart-root';
      container.appendChild(root);

      var compact = !!opts.compact;
      var dark = !!opts.dark;
      var p = palette(dark);
      var chart = LightweightCharts.createChart(root, chartOptions(p, compact));

      var candleSeries = chart.addSeries(LightweightCharts.CandlestickSeries, {
        upColor: p.up, downColor: p.down,
        wickUpColor: p.up, wickDownColor: p.down,
        borderUpColor: p.up, borderDownColor: p.down,
        priceFormat: { type: 'price', precision: 2, minMove: 0.01 }
      }, 0);
      // Pull price action toward the top so candles fill the pane vertically
      // instead of leaving dead space above the bands. Compact (watchlist)
      // pane is shorter; legend is now a small overlay chip so it doesn't
      // need extra top clearance.
      candleSeries.priceScale().applyOptions({ scaleMargins: { top: 0, bottom: 0 } });
      // TradingView hollow candles: body hollow when close >= open, filled when close < open.
      // Dark theme: green/red by close vs previous close. Light theme: plain white/black.
      function paintCandles(pal) {
        candleSeries.setData(data.candles.map(function (c, i) {
          var hollow = c.close >= c.open;
          if (!dark) {
            return {
              time: c.time, open: c.open, high: c.high, low: c.low, close: c.close,
              color: hollow ? '#ffffff' : '#000000',
              borderColor: '#000000',
              wickColor: '#000000'
            };
          }
          var prevClose = i > 0 ? data.candles[i - 1].close : c.open;
          var col = c.close >= prevClose ? pal.up : pal.down;
          return {
            time: c.time, open: c.open, high: c.high, low: c.low, close: c.close,
            color: hollow ? 'rgba(0,0,0,0)' : col,
            borderColor: col,
            wickColor: col
          };
        }));
      }
      paintCandles(p);

      var volumeSeries = chart.addSeries(LightweightCharts.HistogramSeries, {
        priceScaleId: 'duo-volume',
        priceFormat: { type: 'volume' },
        lastValueVisible: false,
        priceLineVisible: false
      }, 0);
      volumeSeries.priceScale().applyOptions({ scaleMargins: { top: compact ? 0.84 : 0.84, bottom: 0 } });

      function paintVolume(pal) {
        volumeSeries.setData(data.volume.map(function (v, i) {
          var c = data.candles[i];
          return { time: v.time, value: v.value, color: (c && c.close >= c.open) ? pal.volUp : pal.volDown };
        }));
      }
      paintVolume(p);

      var overlayOpts = { lineWidth: 1, priceLineVisible: false, lastValueVisible: false, crosshairMarkerVisible: false };
      var kcOverlayOpts = Object.assign({ autoscaleInfoProvider: function () { return null; } }, overlayOpts);
      var emaSeries = chart.addSeries(LightweightCharts.LineSeries, Object.assign({ color: '#2962FF' }, kcOverlayOpts), 0);
      emaSeries.setData(data.ema21);
      (data.kcUpper || []).forEach(function (pts, i) {
        var s = chart.addSeries(LightweightCharts.LineSeries, Object.assign({ color: KC_UP_COLORS[i] || KC_UP_COLORS[0] }, kcOverlayOpts), 0);
        s.setData(pts);
      });
      (data.kcLower || []).forEach(function (pts, i) {
        var s = chart.addSeries(LightweightCharts.LineSeries, Object.assign({ color: KC_DOWN_COLORS[i] || KC_DOWN_COLORS[0] }, kcOverlayOpts), 0);
        s.setData(pts);
      });

      if (data.anchorTime) {
        LightweightCharts.createSeriesMarkers(candleSeries, [
          { time: data.anchorTime, position: 'aboveBar', color: '#f5c842', shape: 'circle', text: '★', size: 0.5 },
          { time: data.anchorTime, position: 'belowBar', color: '#f5c842', shape: 'arrowUp', text: '', size: 0.5 }
        ]);
      }

      // Big, faint ticker watermark over the candles (TradingView-style).
      // Appended AFTER the chart element so it paints above the chart's opaque
      // background canvas (inserting it first leaves it hidden behind the chart).
      var watermark = document.createElement('div');
      watermark.className = 'duo-chart-watermark';
      root.appendChild(watermark);

      function paintWatermark(pal, price) {
        var paneH = root.clientHeight || 0;
        watermark.style.fontSize = Math.max(28, Math.round(paneH * (compact ? 0.18 : 0.13))) + 'px';
        watermark.style.color = pal.text;
        watermark.style.opacity = dark ? '0.07' : '0.09';
        watermark.textContent = data.ticker;
      }
      paintWatermark(p, data.candles.length ? data.candles[data.candles.length - 1].close : null);

      var lastCandle = data.candles.length ? data.candles[data.candles.length - 1] : null;
      var lastPriceLine = null;
      if (lastCandle) {
        lastPriceLine = candleSeries.createPriceLine({
          price: lastCandle.close,
          color: lastCandle.close >= lastCandle.open ? p.up : p.down,
          lineWidth: 1,
          lineStyle: LightweightCharts.LineStyle.Dashed,
          axisLabelVisible: true,
          title: ''
        });
      }

      var histSeries = chart.addSeries(LightweightCharts.HistogramSeries, {
        priceFormat: { type: 'price', precision: 3, minMove: 0.001 },
        lastValueVisible: false,
        priceLineVisible: false
      }, 1);
      // TradingView PPO momentum shading: strong shade while momentum builds,
      // pale shade when it fades (rising below zero = fading red = pale pink).
      function histBarColor(pal, value, prevValue) {
        var growing = prevValue === null || value > prevValue;
        if (value >= 0) return growing ? pal.histUp : pal.histUpLight;
        return growing ? pal.histDownLight : pal.histDown;
      }
      var histIndexByTime = {};
      (data.histogram || []).forEach(function (h, i) { histIndexByTime[h.time] = i; });
      var candleIndexByTime = {};
      data.candles.forEach(function (c, i) { candleIndexByTime[c.time] = i; });
      function lineValueAt(points, time) {
        if (time === null || time === undefined) return null;
        for (var i = 0; i < (points || []).length; i++) {
          if (points[i] && points[i].time === time) return points[i].value;
        }
        return null;
      }
      // v5 crosshair events return time as a BusinessDay object ({year, month, day})
      // for daily bars, not the 'yyyy-mm-dd' string used in the payload.
      function timeKey(t) {
        if (typeof t === 'string') return t;
        if (t && typeof t === 'object') {
          var mm = ('0' + t.month).slice(-2);
          var dd = ('0' + t.day).slice(-2);
          return t.year + '-' + mm + '-' + dd;
        }
        if (typeof t === 'number') {
          var d = new Date(t * 1000);
          return d.getUTCFullYear() + '-' + ('0' + (d.getUTCMonth() + 1)).slice(-2) + '-' + ('0' + d.getUTCDate()).slice(-2);
        }
        return null;
      }
      function histColorAt(pal, time) {
        var i = histIndexByTime[time];
        if (i === undefined) return pal.text;
        return histBarColor(pal, data.histogram[i].value, i > 0 ? data.histogram[i - 1].value : null);
      }
      function paintHistogram(pal) {
        histSeries.setData((data.histogram || []).map(function (h, i) {
          var prev = i > 0 ? data.histogram[i - 1].value : null;
          return { time: h.time, value: h.value, color: histBarColor(pal, h.value, prev) };
        }));
      }
      paintHistogram(p);
      var tripleMaSeries = chart.addSeries(LightweightCharts.HistogramSeries, {
        priceScaleId: 'duo-triple-ma',
        lastValueVisible: false,
        priceLineVisible: false,
        base: 0,
        priceFormat: { type: 'price', precision: 0, minMove: 1 }
      }, 1);
      function paintTripleMaStrip(pal) {
        tripleMaSeries.setData((data.tripleMa || []).map(function (point) {
          return {
            time: point.time,
            value: 1,
            color: point.aligned ? pal.up : pal.down
          };
        }));
      }
      paintTripleMaStrip(p);
      tripleMaSeries.priceScale().applyOptions({
        visible: false,
        scaleMargins: { top: 0.94, bottom: 0.01 }
      });
      var ppoSeries = chart.addSeries(LightweightCharts.LineSeries, Object.assign({ color: '#2962FF', lineWidth: compact ? 1.25 : 2.5 }, { priceLineVisible: false, lastValueVisible: false }), 1);
      ppoSeries.setData(data.ppo || []);
      var signalSeries = chart.addSeries(LightweightCharts.LineSeries, Object.assign({ color: '#FF9800', lineWidth: 1.25 }, { priceLineVisible: false, lastValueVisible: false }), 1);
      signalSeries.setData(data.signal || []);
      function lastLinePoint(points) {
        for (var i = (points || []).length - 1; i >= 0; i--) {
          if (points[i] && points[i].time && Number.isFinite(Number(points[i].value))) return points[i];
        }
        return null;
      }
      var ppoLastPoint = lastLinePoint(data.ppo);
      var signalLastPoint = lastLinePoint(data.signal);
      if (ppoLastPoint) {
        LightweightCharts.createSeriesMarkers(ppoSeries, [{
          time: ppoLastPoint.time, position: 'inBar', color: '#2962FF', shape: 'circle', text: '', size: 0.4
        }]);
      }
      if (signalLastPoint) {
        LightweightCharts.createSeriesMarkers(signalSeries, [{
          time: signalLastPoint.time, position: 'inBar', color: '#FF9800', shape: 'circle', text: '', size: 0.4
        }]);
      }
      var zeroLine = ppoSeries.createPriceLine({
        price: 0, color: p.zeroLine, lineWidth: 1,
        lineStyle: LightweightCharts.LineStyle.Solid, axisLabelVisible: false, title: ''
      });
      ppoSeries.priceScale().applyOptions({ scaleMargins: { top: 0, bottom: 0 } });

      var panes = chart.panes();
      if (panes.length > 1) {
        if (panes[0].setStretchFactor) panes[0].setStretchFactor(compact ? 2.8 : 2.8);
        if (panes[1].setStretchFactor) panes[1].setStretchFactor(1);
      }

      var legendHost = opts.legendHost || null;
      var legend = document.createElement('div');
      legend.className = 'duo-chart-legend' + (legendHost ? ' in-toolbar' : '');
      if (legendHost) {
        legendHost.innerHTML = '';
        legendHost.appendChild(legend);
      } else {
        root.appendChild(legend);
      }

      function paintLegend(pal, candle, vol, ppoVal, signalVal, histVal, histTime, candleTime, sma4Val, sma9Val, sma18Val) {
        var idx = (candleTime !== null && candleTime !== undefined) ? candleIndexByTime[candleTime] : undefined;
        var prevClose = (idx !== undefined && idx > 0) ? data.candles[idx - 1].close : (candle ? candle.open : null);
        var dir = candle && prevClose !== null ? (candle.close >= prevClose ? 1 : -1) : 1;
        var cc = dir >= 0 ? '#4ade80' : '#ff6b7a';
        var chg = (candle && prevClose) ? ((candle.close - prevClose) / prevClose) * 100 : null;
        var histColor = (histTime !== null && histTime !== undefined) ? histColorAt(pal, histTime) : ((histVal || 0) >= 0 ? pal.up : pal.down);
        var boxStyle = 'background:' + pal.chipBg + ';border-color:' + pal.chipBorder + ';color:' + pal.chipText + ';';

        var chip1 = candle
          ? '<div class="duo-chart-chip" style="' + boxStyle + '">' +
              '<span style="color:#ffffff;font-weight:700">' + data.ticker + '</span>' +
              ' · <span style="opacity:0.75">O</span> <b style="color:' + cc + '">' + fmt(candle.open) + '</b>' +
              ' <span style="opacity:0.75">H</span> <b style="color:' + cc + '">' + fmt(candle.high) + '</b>' +
              ' <span style="opacity:0.75">L</span> <b style="color:' + cc + '">' + fmt(candle.low) + '</b>' +
              ' <span style="opacity:0.75">C</span> <b style="color:' + cc + '">' + fmt(candle.close) + '</b>' +
              (chg === null ? '' : ' <b style="color:' + cc + '">' + (chg >= 0 ? '+' : '') + fmt(chg) + '%</b>') +
              ' · <span style="opacity:0.75">Vol</span> <b style="color:#ffffff">' + fmtVol(vol) + '</b>' +
            '</div>'
          : '';

        var chip2 =
          '<div class="duo-chart-chip" style="' + boxStyle + '">' +
            '<span style="opacity:0.75">MA4</span> <b style="color:#4ade80">' + fmt(sma4Val) + '</b>' +
            '&nbsp; <span style="opacity:0.75">MA9</span> <b style="color:#facc15">' + fmt(sma9Val) + '</b>' +
            '&nbsp; <span style="opacity:0.75">MA18</span> <b style="color:#c084fc">' + fmt(sma18Val) + '</b>' +
          '</div>';

        var chip3 =
          '<div class="duo-chart-chip" style="' + boxStyle + '">' +
            '<span style="opacity:0.75">PPO</span> <b style="color:#60a5fa">' + fmt(ppoVal, 2) + '</b>' +
            '&nbsp; <span style="opacity:0.75">Signal</span> <b style="color:#fb923c">' + fmt(signalVal, 2) + '</b>' +
            '&nbsp; <span style="opacity:0.75">Hist</span> <b style="color:' + histColor + '">' + fmt(histVal, 2) + '</b>' +
          '</div>';

        legend.innerHTML = chip1 + chip2 + chip3;
        if (compact) {{
          var chips = legend.querySelectorAll('.duo-chart-chip');
          for (var i = 0; i < chips.length; i++) {
            chips[i].style.fontSize = '11.5px';
            chips[i].style.padding = '2px 6px';
            chips[i].style.gap = '4px';
          }
        }}
      }

      function lastOf(points) { return points && points.length ? points[points.length - 1].value : null; }

      function showDefaultLegend() {
        var lastHist = data.histogram && data.histogram.length ? data.histogram[data.histogram.length - 1] : null;
        paintLegend(palette(dark), lastCandle, data.volume.length ? data.volume[data.volume.length - 1].value : null,
          lastOf(data.ppo), lastOf(data.signal), lastOf(data.histogram), lastHist ? lastHist.time : null,
          lastCandle ? lastCandle.time : null, lastOf(data.sma4), lastOf(data.sma9), lastOf(data.sma18));
        paintWatermark(palette(dark), lastCandle ? lastCandle.close : null);
      }
      showDefaultLegend();

      chart.subscribeCrosshairMove(function (param) {
        if (!param || !param.time || !param.seriesData) { showDefaultLegend(); return; }
        var candle = param.seriesData.get(candleSeries);
        if (!candle) { showDefaultLegend(); return; }
        var vol = param.seriesData.get(volumeSeries);
        var m = param.seriesData.get(ppoSeries);
        var s = param.seriesData.get(signalSeries);
        var h = param.seriesData.get(histSeries);
        var tkey = timeKey(param.time);
        paintLegend(palette(dark), candle, vol ? vol.value : null, m ? m.value : null, s ? s.value : null, h ? h.value : null, tkey, tkey,
          lineValueAt(data.sma4, tkey), lineValueAt(data.sma9, tkey), lineValueAt(data.sma18, tkey));
        paintWatermark(palette(dark), candle ? candle.close : null);
      });

      // Let the time scale derive bar spacing itself so the series spans the
      // full plot, starting flush against the left pane border. Setting
      // barSpacing by hand double-sourced the layout: it was measured from the
      // root width, which also covers the right price scale, so the bars needed
      // more room than the plot actually had and got pushed off the left edge.
      function refit() {
        chart.timeScale().fitContent();
      }
      refit();

      // Keep the plot fitted when the container is resized after mount
      // (e.g. watchlist panel settling), until the user pans/zooms manually.
      var userInteracted = false;
      function markInteracted() { userInteracted = true; }
      root.addEventListener('wheel', markInteracted, { passive: true });
      root.addEventListener('mousedown', markInteracted);
      root.addEventListener('touchstart', markInteracted, { passive: true });
      var fitObserver = null;
      if (typeof ResizeObserver !== 'undefined') {
        fitObserver = new ResizeObserver(function () {
          if (!userInteracted) refit();
        });
        fitObserver.observe(root);
      }

      var handle = {
        setTheme: function (nextDark) {
          dark = !!nextDark;
          var np = palette(dark);
          chart.applyOptions(chartOptions(np, compact));
          paintCandles(np);
          paintVolume(np);
          paintHistogram(np);
          if (lastPriceLine && lastCandle) {
            lastPriceLine.applyOptions({ color: lastCandle.close >= lastCandle.open ? np.up : np.down });
          }
          zeroLine.applyOptions({ color: np.zeroLine });
          showDefaultLegend();
          refit();
        },
        destroy: function () {
          if (fitObserver) { try { fitObserver.disconnect(); } catch (e) {} }
          if (legendHost && legend.parentNode === legendHost) {
            legendHost.innerHTML = '';
          }
          try { chart.remove(); } catch (e) {}
          if (container.__duoChartHandle === handle) container.__duoChartHandle = null;
        },
        data: data,
        chart: chart
      };
      container.__duoChartHandle = handle;
      return handle;
    }).catch(function (err) {
      if (!container.__duoChartHandle) {
        container.innerHTML = '<div class="duo-chart-status">⚠ ' + String(err && err.message ? err.message : 'Chart unavailable') + '</div>';
      }
      throw err;
    });
  }

  window.DuoCharts = { mount: mount };
})();
"""


def render_chart_popout_page(ticker: str, tickers: list[str] | None = None, anchor_date: str = "", forward: bool = False) -> str:
    safe_ticker = re.sub(r"[^A-Za-z0-9.\-]", "", ticker or "").upper()[:12]
    if not safe_ticker:
        raise ValueError("Invalid ticker")

    nav_tickers = []
    seen = set()
    for item in tickers or []:
        safe_item = re.sub(r"[^A-Za-z0-9.\-]", "", item or "").upper()[:12]
        if safe_item and safe_item not in seen:
            nav_tickers.append(safe_item)
            seen.add(safe_item)
    if safe_ticker not in seen:
        nav_tickers.insert(0, safe_ticker)

    nav_index = nav_tickers.index(safe_ticker)
    nav_count = len(nav_tickers)
    nav_prev = nav_tickers[(nav_index - 1) % nav_count] if nav_count > 1 else ""
    nav_next = nav_tickers[(nav_index + 1) % nav_count] if nav_count > 1 else ""
    nav_pos = f"{nav_index + 1}/{nav_count}" if nav_count > 1 else ""
    nav_prev_html = f'<button class="nav" onclick="navTo(PREV)" title="Previous: {html.escape(nav_prev)}">&#8249;</button>' if nav_prev else ""
    nav_next_html = f'<button class="nav" onclick="navTo(NEXT)" title="Next: {html.escape(nav_next)}">&#8250;</button>' if nav_next else ""
    nav_pos_html = f'<span class="navpos">{html.escape(nav_pos)}</span>' if nav_pos else ""
    safe_anchor = re.sub(r"[^0-9\-]", "", anchor_date or "")[:10]
    if safe_anchor:
        datetime.strptime(safe_anchor, "%Y-%m-%d")
    tickers_payload = json.dumps(nav_tickers, allow_nan=False)
    ticker_payload = json.dumps(safe_ticker)
    prev_payload = json.dumps(nav_prev)
    next_payload = json.dumps(nav_next)
    anchor_payload = json.dumps(safe_anchor)
    forward_payload = "true" if forward else "false"
    cache_buster = int(datetime.now().timestamp() * 1000)
    anchor_qs = f"&anchor={safe_anchor}" if safe_anchor else ""
    mode_label = f"Daily + PPO{f' | Anchor {safe_anchor}' if safe_anchor else ''}"

    return f"""<!doctype html>
<html>
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{html.escape(safe_ticker)} | Daily + PPO</title>
  <style>
{FINVIZ_THEME_CSS}
    :root {{ color-scheme: light; }}
    body {{ margin:0; font-family:var(--fv-font-sans); background:#f3f3f5; color:#22262f; }}
    .top {{ position:sticky; top:0; z-index:5; display:flex; align-items:center; gap:12px; padding:8px 14px; background:#4c5263; color:#f3f3f5; flex-wrap:wrap; }}
    .sym {{ font-size:16px; font-weight:600; letter-spacing:.4px; color:#ffffff; white-space:nowrap; }}
    .mode {{ font-size:12px; font-weight:500; color:#ffffff; white-space:nowrap; }}
    .nav {{ border:1px solid rgba(255,255,255,.25); cursor:pointer; background:rgba(255,255,255,.08); color:#dedfe5; width:26px; height:26px; border-radius:50%; font-size:16px; line-height:1; display:inline-flex; align-items:center; justify-content:center; padding:0 0 2px; }}
    .nav:hover:not(:disabled) {{ background:rgba(255,255,255,.20); }}
    .navpos {{ font-size:11px; font-weight:500; color:#ffffff; white-space:nowrap; font-variant-numeric:tabular-nums; }}
    .spacer {{ flex:1; }}
    .forward-toggle {{ display:inline-flex; align-items:center; gap:7px; padding:5px 10px; border:1px solid rgba(255,255,255,.25); border-radius:999px; color:#ffffff; font-size:12px; font-weight:700; white-space:nowrap; user-select:none; cursor:pointer; }}
    .forward-toggle input {{ margin:0; }}
    .tv {{ text-decoration:none; color:#ffffff; background:#4c5263; padding:5px 11px; border-radius:999px; font-size:12px; font-weight:500; white-space:nowrap; }}
    .tv:hover {{ background:#353945; }}
    .wrap {{ padding:6px 8px; }}
    .card {{ background:#fff; border:1px solid #dedfe5; border-radius:8px; overflow:hidden; box-shadow:0 2px 10px rgba(0,0,0,.08); }}
    .chart-shell {{ position:relative; height:calc(100vh - 54px); min-height:580px; background:#ffffff; overflow:hidden; }}
    body.dark-theme .chart-shell {{ background:#1b202b; }}
    #chartContainer {{ width:100%; height:100%; }}
  </style>
</head>
<body>
{DUO_THEME_BOOT_SCRIPT}
  <div class="top">
    {nav_prev_html}
    <span class="sym">{html.escape(safe_ticker)}</span>
    {nav_next_html}
    {nav_pos_html}
    <span class="mode">{html.escape(mode_label)}</span>
    <span class="spacer"></span>
    <label class="forward-toggle"><input id="forwardViewToggle" type="checkbox"{' checked' if forward else ''}> Forward View</label>
{DUO_THEME_TOGGLE_HTML}
    <a class="tv" href="https://www.tradingview.com/chart/?symbol={html.escape(safe_ticker)}" target="_blank" rel="noopener noreferrer">&#x2197;&nbsp;TradingView</a>
  </div>
  <div class="wrap">
    <div class="card">
      <div class="chart-shell">
        <div id="chartContainer"></div>
      </div>
    </div>
  </div>
  <script src="/app-static/lightweight-charts.standalone.production.js?v=5.0.9"></script>
  <script src="/chart-lib.js?v={cache_buster}"></script>
  <script>
    const TICKER = {ticker_payload};
    const TICKERS = {tickers_payload};
    const PREV = {prev_payload};
    const NEXT = {next_payload};
    const ANCHOR = {anchor_payload};
    let FORWARD_VIEW = {forward_payload};

    const container = document.getElementById('chartContainer');
    let chartHandle = null;
    const forwardToggle = document.getElementById('forwardViewToggle');
    async function loadChart(dark) {{
      if (chartHandle) {{
        chartHandle.destroy();
        chartHandle = null;
      }}
      try {{
        chartHandle = await DuoCharts.mount(container, {{ ticker: TICKER, anchor: ANCHOR, compact: false, dark: dark, forward: FORWARD_VIEW }});
      }} catch (err) {{
        container.innerHTML = '<div class="duo-chart-status">⚠ ' + ((err && err.message) || 'Chart unavailable') + '</div>';
      }}
    }}
    loadChart(document.body.classList.contains('dark-theme'));
    forwardToggle.addEventListener('change', () => {{
      FORWARD_VIEW = forwardToggle.checked;
      loadChart(document.body.classList.contains('dark-theme'));
    }});
    document.addEventListener('duothemechange', (event) => {{
      if (chartHandle) {{
        chartHandle.setTheme(Boolean(event.detail && event.detail.dark));
      }} else {{
        loadChart(Boolean(event.detail && event.detail.dark));
      }}
    }});

    function fallbackUrl(tk) {{
      const qs = new URLSearchParams();
      qs.set('ticker', tk);
      if (TICKERS.length) qs.set('tickers', TICKERS.join(','));
      if (ANCHOR) qs.set('anchor', ANCHOR);
      if (FORWARD_VIEW) qs.set('forward', '1');
      return '/chart-popout?' + qs.toString();
    }}

    function navTo(tk) {{
      if (!tk) return;
      let url = null;
      try {{
        if (window.opener && !window.opener.closed && typeof window.opener.screenSimChartPopoutUrl === 'function') {{
          url = window.opener.screenSimChartPopoutUrl(tk, ANCHOR, FORWARD_VIEW, TICKERS);
        }}
      }} catch (e) {{}}
      location.href = url || fallbackUrl(tk);
    }}

    document.addEventListener('keydown', (event) => {{
      if (event.key === 'ArrowLeft') navTo(PREV);
      else if (event.key === 'ArrowRight') navTo(NEXT);
    }});
  </script>
</body>
</html>"""


def apply_entry_close_1min_window(df: pd.DataFrame, ticker: str, entry_date_str: str, api_key: str) -> pd.DataFrame:
    entry_window_start = datetime.strptime(f"{entry_date_str} {ENTRY_HOUR:02d}:{ENTRY_MINUTE:02d}", "%Y-%m-%d %H:%M")
    entry_window_end = datetime.strptime(f"{entry_date_str} 16:00", "%Y-%m-%d %H:%M")

    one_min_df = fetch_minute_data(ticker, entry_date_str, entry_date_str, api_key, 1)
    if one_min_df.empty:
        return df

    one_min_df = one_min_df[
        (one_min_df["timestamp"] >= entry_window_start)
        & (one_min_df["timestamp"] <= entry_window_end)
    ].copy()
    if one_min_df.empty:
        return df

    base_df = df[
        ~(
            (df["timestamp"] >= entry_window_start)
            & (df["timestamp"] <= entry_window_end)
        )
    ].copy()
    return pd.concat([base_df, one_min_df], ignore_index=True).drop_duplicates(subset=["timestamp"], keep="last").sort_values("timestamp").reset_index(drop=True)


def apply_exact_1min_close(df: pd.DataFrame, ticker: str, target_date_str: str, target_time: time, api_key: str) -> pd.DataFrame:
    target_ts = datetime.strptime(f"{target_date_str} {target_time:%H:%M}", "%Y-%m-%d %H:%M")
    one_min_df = fetch_minute_data(ticker, target_date_str, target_date_str, api_key, 1)
    if one_min_df.empty:
        return df

    exact_row = one_min_df[one_min_df["timestamp"] == target_ts].copy()
    if exact_row.empty:
        return df

    base_df = df[df["timestamp"] != target_ts].copy()
    return pd.concat([base_df, exact_row], ignore_index=True).drop_duplicates(subset=["timestamp"], keep="last").sort_values("timestamp").reset_index(drop=True)


# ============================================================================
# PLOTTING HELPERS (SESSION-ONLY AXIS)
# ============================================================================

SESSION_SEPARATOR_COLOR = "#b3b8bd"
SESSION_BAND_COLOR = "#142a34"
SESSION_BAND_FONT_COLOR = "#ffffff"
SESSION_BAND_HEIGHT = 0.028
SESSION_BAND_FONT_SIZE = 11.4
Y_AXIS_LABEL_COLOR = "#132b37"
Y_AXIS_LABEL_FONT_SIZE = 9.5
METRIC_TITLE_FONT = 9
METRIC_VALUE_FONT = 14
METRIC_SUBTITLE_FONT = 8
SESSION_SEPARATOR_SHIFT = 0.3
SESSION_INTERDAY_GAP = 0.6


def add_session_index(df: pd.DataFrame, expected_trading_days=None, start_times_by_day=None) -> pd.DataFrame:
    out = df.sort_values("timestamp").copy().reset_index(drop=True)
    out["timestamp"] = pd.to_datetime(out["timestamp"])
    out["session_date"] = out["timestamp"].dt.date
    out["session_time"] = out["timestamp"].dt.strftime("%H:%M")
    out["__is_tbd_session"] = False

    if expected_trading_days:
        present_timestamps = set(out["timestamp"].dropna().tolist())
        placeholder_rows = []
        for trading_day in expected_trading_days:
            session_start = start_times_by_day.get(trading_day, time(9, 30)) if start_times_by_day else time(9, 30)
            session_dt = datetime.combine(trading_day, session_start)
            session_end = datetime.combine(trading_day, time(16, 0))
            while session_dt <= session_end:
                if session_dt in present_timestamps:
                    session_dt += timedelta(minutes=BAR_MINUTES)
                    continue
                row = {}
                row["timestamp"] = session_dt
                row["session_date"] = trading_day
                row["session_time"] = session_dt.strftime("%H:%M")
                row["__is_tbd_session"] = True
                placeholder_rows.append(row)
                session_dt += timedelta(minutes=BAR_MINUTES)
        if placeholder_rows:
            placeholder_df = pd.DataFrame(placeholder_rows).reindex(columns=out.columns)
            out = pd.concat([out, placeholder_df], ignore_index=True)

    out = out.sort_values("timestamp").reset_index(drop=True)

    # Add a small x-gap between trading sessions so the boundary separator
    # is visually separated from both the previous 16:00 candle and next 09:30 candle.
    x_idx = []
    cursor = 0.0
    prev_session_date = None
    for row in out.itertuples(index=False):
        cur_session_date = row.session_date
        if prev_session_date is not None and cur_session_date != prev_session_date:
            cursor += SESSION_INTERDAY_GAP
        x_idx.append(cursor)
        cursor += 1.0
        prev_session_date = cur_session_date
    out["x_idx"] = x_idx
    return out


def add_date_separators_session(ax, df: pd.DataFrame, linewidth: float = 1.35):
    if df.empty:
        return

    dates = list(pd.unique(df["session_date"]))
    for i, d in enumerate(dates):
        first_x = float(df.loc[df["session_date"] == d, "x_idx"].iloc[0])
        if i != 0:
            # Draw a single clear separator line between sessions.
            ax.axvline(first_x - 0.5 - SESSION_SEPARATOR_SHIFT, color=SESSION_SEPARATOR_COLOR, linestyle="-", linewidth=linewidth, alpha=0.95, zorder=4)
            ax.text(
                first_x,
                1.01,
                d.strftime("%b %d"),
                transform=ax.get_xaxis_transform(),
                ha="left",
                va="bottom",
                fontsize=8,
                color=SESSION_SEPARATOR_COLOR,
                clip_on=False,
            )


def _add_sun_marker(ax, x_value: float, y_value: float, color: str = "#142a34"):
    drawing = DrawingArea(11, 11, 0, 0)
    drawing.add_artist(Circle((5.5, 5.5), 2.2, facecolor="none", edgecolor=color, linewidth=1.0))
    for x1, y1, x2, y2 in [
        (5.5, 0.9, 5.5, 2.4),
        (5.5, 8.6, 5.5, 10.1),
        (0.9, 5.5, 2.4, 5.5),
        (8.6, 5.5, 10.1, 5.5),
        (2.3, 2.3, 3.4, 3.4),
        (7.6, 7.6, 8.7, 8.7),
        (2.3, 8.7, 3.4, 7.6),
        (7.6, 3.4, 8.7, 2.3),
    ]:
        drawing.add_artist(Line2D([x1, x2], [y1, y2], color=color, linewidth=0.8, solid_capstyle="round"))
    ax.add_artist(AnnotationBbox(drawing, (x_value, y_value), xycoords=("data", "axes fraction"), frameon=False, box_alignment=(0.5, 0.5), pad=0, zorder=20))


def _add_moon_marker(ax, x_value: float, y_value: float, color: str = "#142a34"):
    drawing = DrawingArea(11, 11, 0, 0)
    drawing.add_artist(Circle((5.5, 5.5), 3.6, facecolor=color, edgecolor=color, linewidth=0))
    drawing.add_artist(Circle((7.0, 6.2), 3.7, facecolor="#ffffff", edgecolor="#ffffff", linewidth=0))
    drawing.add_artist(Circle((5.5, 5.5), 3.6, facecolor="none", edgecolor=color, linewidth=0.8))
    ax.add_artist(AnnotationBbox(drawing, (x_value, y_value), xycoords=("data", "axes fraction"), frameon=False, box_alignment=(0.5, 0.5), pad=0, zorder=20))


def add_session_day_night_markers(band_ax, df: pd.DataFrame, entry_ts=None, show_entry_window_label: bool = False):
    if df.empty:
        return

    entry_date = pd.to_datetime(entry_ts).date() if entry_ts is not None else None
    for session_date in pd.unique(df["session_date"]):
        day_df = df[df["session_date"] == session_date]
        start_x = float(day_df["x_idx"].min()) - 0.5
        end_x = float(day_df["x_idx"].max()) + 0.5
        span = max(end_x - start_x, 1.0)
        _add_sun_marker(band_ax, start_x + span * 0.035, -0.48)
        moon_x = end_x - span * 0.035
        _add_moon_marker(band_ax, moon_x, -0.48)
        if show_entry_window_label and entry_date == session_date:
            label_x = end_x - span * 0.015
            band_ax.text(
                label_x,
                -1.05,
                "Last 10 mins\n on 1-min chart",
                transform=band_ax.get_xaxis_transform(),
                ha="right",
                va="top",
                fontsize=7.2,
                color="#142a34",
                weight="bold",
                linespacing=1.08,
                bbox={"boxstyle": "round,pad=0.24", "facecolor": "#ffffff", "edgecolor": "#b7c2cc", "linewidth": 0.8, "alpha": 0.96},
                clip_on=False,
                zorder=21,
            )


def add_bottom_session_dates(ax, df: pd.DataFrame):
    if df.empty:
        return

    for session_date, day_df in df.groupby("session_date", sort=True):
        start_x = float(day_df["x_idx"].min())
        end_x = float(day_df["x_idx"].max())
        mid_x = (start_x + end_x) / 2.0
        ax.text(
            mid_x,
            -0.14,
            session_date.strftime("%Y-%m-%d"),
            transform=ax.get_xaxis_transform(),
            ha="center",
            va="top",
            fontsize=9,
            color=SESSION_SEPARATOR_COLOR,
            clip_on=False,
        )


def format_display_date(value: date) -> str:
    return value.strftime("%a %b %d, %Y")


def format_file_date_range(start_value: date, end_value: date) -> str:
    if start_value.year == end_value.year:
        return f"{start_value:%d %B}-{end_value:%d %b %Y}"
    return f"{start_value:%d %B %Y}-{end_value:%d %b %Y}"


def format_dashboard_date_range(start_value: date, end_value: date) -> str:
    if start_value.year == end_value.year and start_value.month == end_value.month:
        return f"{start_value:%d}-{end_value:%d %b %Y}"
    if start_value.year == end_value.year:
        return f"{start_value:%d %b}-{end_value:%d %b %Y}"
    return f"{start_value:%d %b %Y}-{end_value:%d %b %Y}"


def format_session_band_date(value: date, is_entry_date: bool = False, is_tbd: bool = False, session_index=None) -> str:
    t_suffix = f" (T{session_index})" if session_index is not None else ""
    if is_entry_date:
        return f"{value:%a} {value:%b} {value:%d}{t_suffix}"
    return f"{format_display_date(value)}{t_suffix}"


def add_entry_window_focus(ax, df: pd.DataFrame, entry_ts):
    if entry_ts is None or df.empty:
        return

    entry_day = pd.to_datetime(entry_ts).date()
    day_df = df[(df["session_date"] == entry_day) & (~df.get("__is_tbd_session", False).fillna(False))].copy()
    if day_df.empty:
        return

    start_label = f"{ENTRY_HOUR:02d}:{ENTRY_MINUTE:02d}"
    start_rows = day_df[day_df["session_time"] == start_label]
    end_rows = day_df[day_df["session_time"] == "16:00"]
    window_start = datetime.combine(entry_day, time(ENTRY_HOUR, ENTRY_MINUTE))
    window_end = datetime.combine(entry_day, time(16, 0))
    window_rows = day_df[(day_df["timestamp"] >= window_start) & (day_df["timestamp"] <= window_end)].copy()
    if window_rows.empty and (start_rows.empty or end_rows.empty):
        return

    if not window_rows.empty:
        x_start = float(window_rows["x_idx"].min())
        x_end = float(window_rows["x_idx"].max())
    else:
        x_start = float(start_rows.iloc[0]["x_idx"])
        x_end = float(end_rows.iloc[-1]["x_idx"])
    if x_end <= x_start:
        return

    # Subtle highlight for the 15:50-16:00 decision window.
    ax.axvspan(x_start - 0.5, x_end + 0.5, color="#e5e7eb", alpha=0.46, zorder=1.5)

    existing_ticks = list(ax.get_xticks())
    existing_labels = [tick.get_text() for tick in ax.get_xticklabels()]
    tick_pairs = []
    for pos, label in zip(existing_ticks, existing_labels):
        # Replace any pre-existing ticks inside the 15:50-16:00 focus window
        # so labels (especially 16:00) are not duplicated.
        if (x_start - 0.5) <= float(pos) <= (x_end + 0.5):
            continue
        tick_pairs.append((float(pos), label))

    base_dt = window_start
    for i in range(11):
        pos = x_start + (x_end - x_start) * (i / 10.0)
        label = (base_dt + timedelta(minutes=i)).strftime("%H:%M") if i % 2 == 0 else ""
        tick_pairs.append((pos, label))

    tick_pairs.sort(key=lambda item: item[0])
    ax.set_xticks([p for p, _ in tick_pairs])
    ax.set_xticklabels([l for _, l in tick_pairs], rotation=45, ha="right", va="top")


def add_tbd_session_watermarks(ax, df: pd.DataFrame):
    if df.empty or "__is_tbd_session" not in df.columns:
        return

    for session_date, day_df in df.groupby("session_date", sort=True):
        if not bool(day_df["__is_tbd_session"].fillna(False).all()):
            continue
        start_x = float(day_df["x_idx"].min()) - 0.5
        end_x = float(day_df["x_idx"].max()) + 0.5
        ax.axvspan(start_x, end_x, color="#e7edf5", alpha=0.88, zorder=1)
        ax.text(
            (start_x + end_x) / 2.0,
            0.52,
            "TBD",
            transform=ax.get_xaxis_transform(),
            ha="center",
            va="center",
            fontsize=54,
            color="#64748b",
            alpha=0.28,
            weight="bold",
            zorder=8,
        )


def add_metric_tile(fig, x, y, w, h, title, value, color="#0b3fbf", subtitle=None, title_font=9, value_font=14, subtitle_font=8, text_positions=None, title_color="#172554", subtitle_color="#64748b", title_weight="normal", subtitle_weight="normal"):
    tile = FancyBboxPatch(
        (x, y),
        w,
        h,
        transform=fig.transFigure,
        boxstyle="round,pad=0.008,rounding_size=0.006",
        facecolor="#ffffff",
        edgecolor="#dbe6f4",
        linewidth=1.0,
        zorder=10,
    )
    fig.patches.append(tile)
    title_pos, value_pos, subtitle_pos = text_positions or (0.66, 0.33, 0.10)
    fig.text(x + w / 2, y + h * title_pos, title, ha="center", va="center", fontsize=title_font, color=title_color, weight=title_weight, zorder=11)
    fig.text(x + w / 2, y + h * value_pos, value, ha="center", va="center", fontsize=value_font, color=color, weight="bold", zorder=11)
    if subtitle:
        fig.text(x + w / 2, y + h * subtitle_pos, subtitle, ha="center", va="center", fontsize=subtitle_font, color=subtitle_color, weight=subtitle_weight, zorder=11)


def lighten_hex_color(hex_color: str, amount: float = 0.20) -> str:
    color = hex_color.lstrip("#")
    red = int(color[0:2], 16)
    green = int(color[2:4], 16)
    blue = int(color[4:6], 16)
    red = round(red + (255 - red) * amount)
    green = round(green + (255 - green) * amount)
    blue = round(blue + (255 - blue) * amount)
    return f"#{red:02x}{green:02x}{blue:02x}"


def darken_hex_color(hex_color: str, amount: float = 0.25) -> str:
    color = hex_color.lstrip("#")
    red = round(int(color[0:2], 16) * (1 - amount))
    green = round(int(color[2:4], 16) * (1 - amount))
    blue = round(int(color[4:6], 16) * (1 - amount))
    return f"#{red:02x}{green:02x}{blue:02x}"


def draw_metric_tiles_header(fig, text, x, y, w, font_size=9, color="#172554"):
    fig.text(
        x + w / 2,
        y,
        text,
        ha="center",
        va="center",
        fontsize=font_size * 1.08,
        color=color,
        fontweight="bold",
        zorder=11,
    )


def draw_right_metric_tiles(fig, metrics, x=0.885, start_y=0.855, w=0.10, h=0.064, gap=0.012, header=None, header_font=9, title_font=METRIC_TITLE_FONT, value_font=METRIC_VALUE_FONT, subtitle_font=METRIC_SUBTITLE_FONT, text_positions=None, header_gap_multiplier=1.7, title_color="#172554", subtitle_color="#64748b", header_color="#172554", title_weight="normal", subtitle_weight="normal"):
    if header:
        draw_metric_tiles_header(fig, header, x, start_y + h + gap * header_gap_multiplier, w, font_size=header_font, color=header_color)
    for idx, metric in enumerate(metrics):
        y = start_y - idx * (h + gap)
        add_metric_tile(fig, x, y, w, h, metric["title"], metric["value"], metric["color"], metric.get("subtitle"), title_font=title_font, value_font=value_font, subtitle_font=subtitle_font, text_positions=text_positions, title_color=title_color, subtitle_color=subtitle_color, title_weight=title_weight, subtitle_weight=subtitle_weight)


def draw_right_panel_box(fig, x, y, w, h, title, title_font=8.2):
    box = FancyBboxPatch(
        (x, y),
        w,
        h,
        transform=fig.transFigure,
        boxstyle="round,pad=0.006,rounding_size=0.004",
        facecolor="#ffffff",
        edgecolor="#dbe6f4",
        linewidth=1.0,
        zorder=10,
    )
    fig.patches.append(box)
    fig.text(x + w / 2, y + h - 0.024, title, ha="center", va="center", fontsize=title_font, color="#172554", weight="bold", zorder=11)


def draw_benchmark_performance_box(fig, metrics, period_label: str, x=0.895, y=0.735, w=0.0935, h=0.185, show_dash_rows: bool = False):
    if not metrics:
        return
    draw_right_panel_box(fig, x, y, w, h, "", title_font=9.0)
    fig.text(x + w / 2, y + h - 0.022, "Benchmark Summary", ha="center", va="center", fontsize=9.7, color="#172554", weight="bold", zorder=11)
    fig.text(x + w / 2, y + h - 0.043, f"Performance {period_label}", ha="center", va="center", fontsize=8.1, color="#64748b", weight="bold", zorder=11)
    row_count = len(metrics) * 2 if show_dash_rows else len(metrics)
    group_gap = 0.010 if show_dash_rows else 0.0
    row_gap = (h - 0.070 - group_gap * max(len(metrics) - 1, 0)) / max(row_count, 1)
    top_y = y + h - 0.071
    row_idx = 0
    for metric_idx, metric in enumerate(metrics):
        group_offset = group_gap * metric_idx
        row_y = top_y - row_idx * row_gap - group_offset
        fig.text(x + 0.009, row_y, metric["title"], ha="left", va="center", fontsize=10.6, color=metric["color"], weight="bold", zorder=11)
        fig.text(x + w - 0.009, row_y, metric["value"], ha="right", va="center", fontsize=11.1, color=metric["color"], weight="bold", zorder=11)
        row_idx += 1
        if show_dash_rows:
            dash_y = top_y - row_idx * row_gap - group_offset
            fig.text(x + 0.009, dash_y, f"{metric['title']} Line", ha="left", va="center", fontsize=7.8, color=metric["color"], weight="normal", zorder=11)
            fig.lines.append(
                Line2D(
                    [x + w - 0.035, x + w - 0.009],
                    [dash_y, dash_y],
                    transform=fig.transFigure,
                    color=metric["color"],
                    linewidth=1.0,
                    linestyle=(0, (4, 2)),
                    zorder=11,
                )
            )
            row_idx += 1


def draw_stock_performance_table(fig, metrics, x=0.895, y=0.155, w=0.0935, h=0.525):
    if not metrics:
        return
    fig.text(x + w / 2, y + h + 0.032, "Stock Performance (T0 - T3)", ha="center", va="center", fontsize=9.0, color="#172554", weight="bold", zorder=13)
    draw_right_panel_box(fig, x, y, w, h, "", title_font=9.0)
    header_y = y + h - 0.028
    fig.text(x + 0.009, header_y, "Ticker", ha="left", va="center", fontsize=9.6, color="#172554", weight="bold", zorder=11)
    fig.text(x + w - 0.009, header_y, "P&L (%)", ha="right", va="center", fontsize=9.6, color="#172554", weight="bold", zorder=11)
    display_metrics = metrics
    compact_row_h = min(0.030, (h - 0.070) / max(len(display_metrics), 1))
    first_row_y = header_y - max(0.020, compact_row_h * 0.95)
    row_font = max(6.1, min(8.8, compact_row_h * 295))
    for idx, metric in enumerate(display_metrics):
        row_y = first_row_y - idx * compact_row_h
        if idx > 0:
            fig.lines.append(Line2D([x + 0.007, x + w - 0.007], [row_y + compact_row_h * 0.45, row_y + compact_row_h * 0.45], transform=fig.transFigure, color="#e5edf7", linewidth=0.6, zorder=11))
        fig.text(x + 0.009, row_y, metric["title"], ha="left", va="center", fontsize=row_font * 1.15, color="#172554", zorder=11)
        fig.text(x + w - 0.009, row_y, metric["value"], ha="right", va="center", fontsize=row_font * 1.15, color=metric["color"], weight="bold", zorder=11)


def get_stock_performance_table_height(metric_count: int) -> float:
    return min(0.595, max(0.145, 0.080 + metric_count * 0.034))


def draw_report_context_box(fig, entry_date_str: str, end_date_str: str, x=0.865, y=0.210, w=0.10, h=0.075):
    entry_date = datetime.strptime(entry_date_str, "%Y-%m-%d").date()
    end_date = datetime.strptime(end_date_str, "%Y-%m-%d").date()
    fig.text(x + w / 2, y + h * 0.70, f"{format_display_date(entry_date)} -", ha="center", va="center", fontsize=8.2, color="#172554", weight="bold", zorder=11)
    fig.text(x + w / 2, y + h * 0.47, format_display_date(end_date), ha="center", va="center", fontsize=8.2, color="#172554", weight="bold", zorder=11)
    fig.text(x + w / 2, y + h * 0.20, f"{BAR_MINUTES}-minute bars | Entry {ENTRY_HOUR:02d}:{ENTRY_MINUTE:02d} ET", ha="center", va="center", fontsize=6.9, color="#64748b", weight="bold", zorder=11)


def add_portfolio_eod_pct_labels(ax, df: pd.DataFrame):
    plot_df = df[~df.get("__is_tbd_session", False).fillna(False)].copy()
    if plot_df.empty:
        return

    grouped_days = list(plot_df.groupby("session_date", sort=True))
    for idx, (_session_date, day_df) in enumerate(grouped_days):
        last_row = day_df.iloc[-1]
        end_x = float(last_row["x_idx"])
        end_pct = float(last_row["net_portfolio_pct_change"])
        label_color = "#0f9f55" if end_pct >= 0 else "#dc2626"
        is_final_session = idx == len(grouped_days) - 1
        ax.text(
            end_x + (0.60 if is_final_session else 0.16),
            end_pct - (0.45 if is_final_session else 0.0),
            f"{end_pct:+.2f}%",
            ha="left",
            va="center",
            fontsize=7.3,
            color=label_color,
            weight="bold",
            bbox={"boxstyle": "round,pad=0.18", "facecolor": "#ffffff", "edgecolor": label_color, "linewidth": 0.85, "alpha": 0.96},
            zorder=12,
            clip_on=False,
        )


def draw_metric_tiles_grid(fig, metrics, x=0.875, start_y=0.855, w=0.052, h=0.046, x_gap=0.008, y_gap=0.008, columns=2, header=None):
    rows = (len(metrics) + columns - 1) // columns
    if header:
        total_w = columns * w + (columns - 1) * x_gap
        draw_metric_tiles_header(fig, header, x, start_y + h + y_gap * 1.7, total_w)
    for idx, metric in enumerate(metrics):
        col = idx // rows
        row = idx % rows
        add_metric_tile(
            fig,
            x + col * (w + x_gap),
            start_y - row * (h + y_gap),
            w,
            h,
            metric["title"],
            metric["value"],
            metric["color"],
            metric.get("subtitle"),
            title_font=7,
            value_font=10,
            subtitle_font=6,
        )


def add_portfolio_exit_time_annotation(ax, df: pd.DataFrame):
    exit_label = f"{EXIT_HOUR:02d}:{EXIT_MINUTE:02d}"
    exit_rows = df[df["session_time"] == exit_label].copy()
    if exit_rows.empty:
        return

    exit_row = exit_rows.sort_values("timestamp").iloc[-1]
    if bool(exit_row.get("__is_tbd_session", False)):
        return
    x_value = float(exit_row["x_idx"])
    y_series = df[~df.get("__is_tbd_session", False).fillna(False)]["net_portfolio_pct_change"].dropna()
    if y_series.empty:
        return

    y_value = float(y_series.iloc[-1])
    ax.annotate(
        "Exit\n3:50 PM",
        xy=(x_value, y_value),
        xytext=(-10, 28),
        textcoords="offset points",
        ha="right",
        va="bottom",
        fontsize=8.0,
        color="#111827",
        weight="bold",
        arrowprops={"arrowstyle": "->", "color": "#111827", "linewidth": 0.9},
        bbox={"boxstyle": "round,pad=0.18", "facecolor": "#ffffff", "edgecolor": "#111827", "linewidth": 0.7, "alpha": 0.96},
        zorder=14,
    )


def add_portfolio_high_low_annotations(ax, df: pd.DataFrame, x_min: float, x_max: float, y_low: float, y_high: float):
    plot_df = df[~df.get("__is_tbd_session", False).fillna(False)].copy()
    if plot_df.empty or "net_portfolio_pct_change" not in plot_df.columns:
        return

    pct_series = plot_df["net_portfolio_pct_change"].astype(float).dropna()
    if pct_series.empty:
        return

    high_row = plot_df.loc[pct_series.idxmax()]
    low_row = plot_df.loc[pct_series.idxmin()]
    session_boundaries = [
        float(day_df["x_idx"].min()) - 0.5
        for idx, (_session_date, day_df) in enumerate(plot_df.groupby("session_date", sort=True))
        if idx > 0 and not day_df.empty
    ]
    x_span = max(x_max - x_min, 1.0)
    y_span = max(y_high - y_low, 1.0)

    for label, row, color, preferred_direction in (
        ("Highest High", high_row, "#0f9f55", "down"),
        ("Lowest Low", low_row, "#dc2626", "up"),
    ):
        x_value = float(row["x_idx"])
        pct_value = float(row["net_portfolio_pct_change"])
        nearest_boundary = min(session_boundaries, key=lambda boundary: abs(boundary - x_value)) if session_boundaries else None
        if nearest_boundary is not None and abs(nearest_boundary - x_value) <= max(x_span * 0.025, 1.5):
            x_offset = 58 if x_value >= nearest_boundary else -58
        elif x_value > x_min + x_span * 0.72:
            x_offset = -58
        else:
            x_offset = 58

        if preferred_direction == "down":
            y_offset = -34 if pct_value > y_high - y_span * 0.22 else 28
        else:
            y_offset = 34 if pct_value < y_low + y_span * 0.22 else -30

        box_alignment = (
            0.0 if x_offset > 0 else 1.0,
            1.0 if y_offset < 0 else 0.0,
        )
        label_box = TextArea(label, textprops={"color": "#111827", "fontsize": 7.8, "fontweight": "bold", "ha": "center"})
        pct_box = TextArea(f"{pct_value:+.2f}%", textprops={"color": "#111827", "fontsize": 7.8, "fontweight": "bold", "ha": "center"})
        packed_label = VPacker(children=[label_box, pct_box], align="center", pad=0, sep=1)
        annotation = AnnotationBbox(
            packed_label,
            (x_value, pct_value),
            xybox=(x_offset, y_offset),
            xycoords="data",
            boxcoords="offset points",
            box_alignment=box_alignment,
            frameon=True,
            bboxprops={"boxstyle": "round,pad=0.18", "facecolor": "#ffffff", "edgecolor": "#111827", "linewidth": 0.7, "alpha": 0.96},
            arrowprops={"arrowstyle": "->", "color": "#111827", "linewidth": 0.9},
        )
        annotation.set_zorder(14)
        ax.add_artist(annotation)


def plot_signed_line_segments(ax, x_values: pd.Series, y_values: pd.Series, positive_color: str, negative_color: str, linewidth: float = 1.5, zorder: int = 5):
    points = [(float(x), float(y)) for x, y in zip(x_values, y_values) if not pd.isna(x) and not pd.isna(y)]
    if len(points) < 2:
        if points:
            x, y = points[0]
            ax.scatter([x], [y], s=10, color=positive_color if y >= 0 else negative_color, zorder=zorder)
        return

    for (x1, y1), (x2, y2) in zip(points[:-1], points[1:]):
        if y1 == 0 or y2 == 0 or (y1 >= 0 and y2 >= 0) or (y1 < 0 and y2 < 0):
            color = positive_color if (y1 + y2) / 2 >= 0 else negative_color
            ax.plot([x1, x2], [y1, y2], color=color, linewidth=linewidth, zorder=zorder)
            continue

        crossing_x = x1 + (0 - y1) * (x2 - x1) / (y2 - y1)
        first_color = positive_color if y1 >= 0 else negative_color
        second_color = positive_color if y2 >= 0 else negative_color
        ax.plot([x1, crossing_x], [y1, 0], color=first_color, linewidth=linewidth, zorder=zorder)
        ax.plot([crossing_x, x2], [0, y2], color=second_color, linewidth=linewidth, zorder=zorder)


def draw_threshold_marker(ax, x_max: float, y_low: float, y_high: float, threshold: float, color: str, label: str, direction: str):
    y_span = max(y_high - y_low, 1.0)
    if y_low <= threshold <= y_high:
        base_y = threshold
        gap = max(y_span * 0.005, 0.01)
        thin_y = base_y
        thick_y = base_y - gap if direction == "up" else base_y + gap
    elif direction == "up":
        thin_y = y_high - max(y_span * 0.012, 0.02)
        gap = max(y_span * 0.005, 0.01)
        thick_y = thin_y - gap
    else:
        thin_y = y_low + max(y_span * 0.012, 0.02)
        gap = max(y_span * 0.005, 0.01)
        thick_y = thin_y + gap

    ax.axhline(thin_y, color=color, linestyle="--", linewidth=1.0, alpha=0.75, zorder=4)
    ax.axhline(thick_y, color=color, linestyle="-", linewidth=2.4, alpha=0.82, zorder=4)
    label_y = thick_y - gap * 1.8 if direction == "up" else thick_y + gap * 1.8
    va = "top" if direction == "up" else "bottom"
    arrow = "up" if direction == "up" else "down"
    ax.text(
        x_max - 0.7,
        label_y,
        f"{label} {threshold:.2f}% {arrow}",
        ha="right",
        va=va,
        fontsize=8.05,
        color=color,
        weight="bold",
        bbox={"boxstyle": "round,pad=0.16", "facecolor": "#ffffff", "edgecolor": color, "linewidth": 0.7, "alpha": 0.94},
        zorder=13,
    )


def copy_header_logo(source_path: str, output_folder: str) -> str:
    logo_name = "nras-logo-transparent.png"
    output_path = os.path.join(output_folder, "static", logo_name)
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    if not PIL_AVAILABLE:
        shutil.copyfile(source_path, output_path)
        return os.path.relpath(output_path, output_folder).replace("\\", "/")

    gold = (255, 232, 96)
    image = Image.open(source_path).convert("RGBA")
    pixels = image.load()
    for y in range(image.height):
        for x in range(image.width):
            red, green, blue, alpha = pixels[x, y]
            if alpha == 0 or (red > 238 and green > 238 and blue > 238):
                pixels[x, y] = (255, 255, 255, 0)
                continue
            ink_strength = max(0.25, 1.0 - ((red + green + blue) / 765.0))
            pixels[x, y] = (gold[0], gold[1], gold[2], int(alpha * min(1.0, ink_strength * 2.7)))
    image.save(output_path)
    return os.path.relpath(output_path, output_folder).replace("\\", "/")


def get_benchmark_metrics(benchmark_line_data: list[tuple[str, pd.DataFrame]]) -> list[dict]:
    benchmark_by_ticker = {ticker: stock_df for ticker, stock_df in benchmark_line_data}
    benchmark_metrics = []
    for ticker in BENCHMARK_TICKERS:
        stock_df = benchmark_by_ticker.get(ticker)
        if stock_df is None:
            continue
        plot_stock_df = stock_df[~stock_df.get("__is_tbd_session", False).fillna(False)].copy()
        if plot_stock_df.empty:
            continue
        final_pct = float(plot_stock_df["pnl_pct"].astype(float).iloc[-1])
        benchmark_metrics.append({"title": ticker, "value": f"{final_pct:+.2f}%", "color": BENCHMARK_COLORS.get(ticker, "#111827"), "subtitle": "Dashed"})
    return benchmark_metrics


def add_latest_session_end_dot(ax, plot_df: pd.DataFrame, y_column: str, color: str, size: int = 18):
    grouped_days = [(session_date, day_df) for session_date, day_df in plot_df.groupby("session_date", sort=True) if not day_df.empty]
    if len(grouped_days) <= 1:
        return
    _session_date, latest_day_df = grouped_days[-1]
    last_row = latest_day_df.iloc[-1]
    ax.scatter([last_row["x_idx"]], [last_row[y_column]], s=size, color=color, edgecolor="#ffffff", linewidth=0.65, zorder=10)


def format_accounting_dollars(value: float) -> str:
    if value < 0:
        return f"(${abs(value):,.0f})"
    return f"${value:,.0f}"


def render_portfolio_chart(portfolio_plot_df: pd.DataFrame, portfolio_chart_path: str, entry_date_str: str, end_date_str: str, final_pct: float, final_value: float, starting_value: float, benchmark_line_data: list[tuple[str, pd.DataFrame]] | None = None, stock_count: int | None = None, allocation_per_stock: float | None = None):
    plot_rows = portfolio_plot_df[~portfolio_plot_df.get("__is_tbd_session", False).fillna(False)].copy()
    p_pct = plot_rows["net_portfolio_pct_change"].astype(float)
    target_pct = PORTFOLIO_TARGET * 100
    stop_pct = PORTFOLIO_STOP_LOSS * 100
    max_runup = float(p_pct.max())
    max_drawdown = float((p_pct - p_pct.cummax()).min())
    net_pnl_dollars = final_value - starting_value

    fig = plt.figure(figsize=(20, 9), facecolor="#f8fbff")
    fig.suptitle("")

    chart_left = 0.045
    chart_bottom = 0.12
    chart_width = 0.79
    chart_height = 0.80
    band_height = SESSION_BAND_HEIGHT

    ax = fig.add_axes([chart_left, chart_bottom, chart_width, chart_height], facecolor="#ffffff", zorder=5)
    band_ax = fig.add_axes([chart_left, chart_bottom + chart_height, chart_width, band_height], sharex=ax, facecolor=SESSION_BAND_COLOR, zorder=6)

    x = plot_rows["x_idx"].astype(float)
    x_min = float(x.min()) - 0.5
    x_max = float(portfolio_plot_df["x_idx"].astype(float).max()) + 0.5
    y_low = min(float(p_pct.min()), 0.0) - 1.0
    y_high = max(float(p_pct.max()), 0.0) + 1.0
    plot_signed_line_segments(ax, x, p_pct, "#073bd6", "#dc2626", linewidth=1.18, zorder=5)
    add_portfolio_eod_pct_labels(ax, portfolio_plot_df)
    add_portfolio_exit_time_annotation(ax, portfolio_plot_df)
    ax.fill_between(x, p_pct, 0, where=p_pct >= 0, interpolate=True, color="#dceeff", alpha=0.82, zorder=2)
    ax.fill_between(x, p_pct, 0, where=p_pct < 0, interpolate=True, color="#fecaca", alpha=0.72, zorder=2)

    ax.axhline(0, color="#94a3b8", linestyle="--", linewidth=1.0, alpha=0.65)
    draw_threshold_marker(ax, x_max, y_low, y_high, stop_pct, "#ff4d4d", "Stop", "down")
    draw_threshold_marker(ax, x_max, y_low, y_high, target_pct, "#2fbf71", "Target", "up")

    add_tbd_session_watermarks(ax, portfolio_plot_df)
    add_date_separators_session(ax, portfolio_plot_df, linewidth=2.0)
    set_intraday_ticks(ax, portfolio_plot_df)

    ax.set_xlim(x_min, x_max)
    ax.set_ylim(y_low, y_high)
    add_portfolio_high_low_annotations(ax, portfolio_plot_df, x_min, x_max, y_low, y_high)
    ax.set_ylabel(
        " PORTFOLIO CHANGE % ",
        fontsize=Y_AXIS_LABEL_FONT_SIZE,
        color=Y_AXIS_LABEL_COLOR,
        fontweight="normal",
        labelpad=7,
        bbox={"boxstyle": "round,pad=0.28", "facecolor": "none", "edgecolor": Y_AXIS_LABEL_COLOR, "linewidth": 1.0, "alpha": 0.95},
    )
    ax.yaxis.set_major_formatter(FuncFormatter(lambda value, _: f"{value:.0f}%"))
    ax.grid(axis="y", color="#d9e2ef", linestyle="--", linewidth=0.8, alpha=0.75)
    ax.grid(axis="x", alpha=0)
    ax.tick_params(axis="x", labelsize=8, rotation=45, colors="#172554")
    ax.tick_params(axis="y", labelsize=12, colors="#172554")
    for spine in ax.spines.values():
        spine.set_color("#dbe6f4")

    dates = list(pd.unique(portfolio_plot_df["session_date"]))
    for idx, session_date in enumerate(dates):
        day_df = portfolio_plot_df[portfolio_plot_df["session_date"] == session_date]
        start_x = float(day_df["x_idx"].min()) - 0.5
        end_x = float(day_df["x_idx"].max()) + 0.5
        band_ax.axvspan(start_x, end_x, color=SESSION_BAND_COLOR, alpha=1.0)
        is_tbd = bool(day_df.get("__is_tbd_session", False).fillna(False).all())
        font_size = SESSION_BAND_FONT_SIZE * 0.90 if idx == 0 else SESSION_BAND_FONT_SIZE
        band_ax.text((start_x + end_x) / 2.0, 0.5, format_session_band_date(session_date, idx == 0, is_tbd=is_tbd, session_index=idx), color=SESSION_BAND_FONT_COLOR, fontsize=font_size, weight="bold", ha="center", va="center", clip_on=False)
        if idx != 0:
            boundary_x = start_x
            band_ax.axvline(boundary_x - SESSION_SEPARATOR_SHIFT, color=SESSION_SEPARATOR_COLOR, linewidth=2.125, alpha=1.0)
            ax.axvline(boundary_x - SESSION_SEPARATOR_SHIFT, color=SESSION_SEPARATOR_COLOR, linewidth=2.125, alpha=0.95, zorder=7)
    band_ax.set_xlim(x_min, x_max)
    band_ax.set_ylim(0, 1)
    add_session_day_night_markers(band_ax, portfolio_plot_df)
    band_ax.axis("off")

    session_count = len(dates)
    pnl_color = "#0f9f55" if final_pct >= 0 else "#dc2626"
    summary_metrics = [
        {"title": "Starting Capital", "value": f"${starting_value:,.0f}", "color": "#0284c7", "subtitle": "Baseline"},
        {"title": "Ending Value", "value": f"${final_value:,.0f}", "color": pnl_color, "subtitle": "Final Equity"},
        *([{"title": "Stocks", "value": str(stock_count), "color": "#0891b2", "subtitle": f"${allocation_per_stock:,.0f} each"}] if stock_count is not None and allocation_per_stock is not None else []),
        {"title": "Total Sessions", "value": str(session_count), "color": "#123ad6", "subtitle": "Trading Days"},
        {"title": "Max Run-up", "value": f"{max_runup:+.2f}%", "color": "#0f9f55", "subtitle": "Peak Gain"},
        {"title": "Max Drawdown", "value": f"{max_drawdown:+.2f}%", "color": "#dc2626", "subtitle": "From Peak"},
        {"title": "Stop Loss", "value": f"{stop_pct:.2f}%", "color": "#dc2626", "subtitle": "Threshold"},
        {"title": "Target", "value": f"{target_pct:.2f}%", "color": "#0f9f55", "subtitle": "Threshold"},
        {"title": "Net P&L $", "value": format_accounting_dollars(net_pnl_dollars), "color": pnl_color, "subtitle": "Absolute"},
        {"title": "Net P&L", "value": f"{final_pct:+.2f}%", "color": pnl_color, "subtitle": "End of Period"},
    ]
    draw_right_metric_tiles(fig, summary_metrics, x=0.865, h=0.052, gap=0.007, header="Portfolio Summary", title_font=7.9, value_font=12.7, subtitle_font=7.5, text_positions=(0.77, 0.43, 0.16), header_gap_multiplier=3.2, title_color="#111827", subtitle_color="#111827", header_color="#111827", title_weight="bold", subtitle_weight="bold")
    draw_benchmark_performance_box(fig, get_benchmark_metrics(benchmark_line_data or []), f"T0-T{max(session_count - 1, 0)}", x=0.865, y=0.125, w=0.10, h=0.165)
    draw_report_context_box(fig, entry_date_str, end_date_str, y=0.035)

    plt.savefig(portfolio_chart_path, dpi=150, bbox_inches="tight", facecolor=fig.get_facecolor())
    plt.close(fig)


def render_stock_line_chart(ticker: str, stock_plot_df: pd.DataFrame, stock_chart_path: str, entry_date_str: str, end_date_str: str, entry_price: float, exit_price: float):
        p_pct = stock_plot_df["pnl_pct"].astype(float)
        final_pct = float(p_pct.iloc[-1])
        max_runup = float(p_pct.max())
        max_drawdown = float((p_pct - p_pct.cummax()).min())

        fig = plt.figure(figsize=(20, 9), facecolor="#f8fbff")
        chart_left = 0.045
        chart_bottom = 0.12
        chart_width = 0.79
        chart_height = 0.80
        band_height = SESSION_BAND_HEIGHT

        line_metrics = [
            {"title": ticker, "value": f"{final_pct:+.2f}%", "color": "#0f9f55" if final_pct >= 0 else "#dc2626", "subtitle": "Final P&L"},
            {"title": "Max Run-up", "value": f"{max_runup:+.2f}%", "color": "#0f9f55", "subtitle": "Peak"},
            {"title": "Max Drawdown", "value": f"{max_drawdown:+.2f}%", "color": "#dc2626", "subtitle": "From Peak"},
        ]
        draw_right_metric_tiles(fig, line_metrics, start_y=0.78, header="Stock Summary")

        ax = fig.add_axes([chart_left, chart_bottom, chart_width, chart_height], facecolor="#ffffff", zorder=5)
        band_ax = fig.add_axes([chart_left, chart_bottom + chart_height, chart_width, band_height], sharex=ax, facecolor=SESSION_BAND_COLOR, zorder=6)

        x = stock_plot_df["x_idx"].astype(float)
        x_min = float(x.min()) - 0.5
        x_max = float(x.max()) + 0.5
        ax.plot(x, p_pct, color="#073bd6", linewidth=1.5, label=f"{ticker} % Change", zorder=5)
        ax.fill_between(x, p_pct, 0, where=p_pct >= 0, interpolate=True, color="#dceeff", alpha=0.82, zorder=2)
        ax.fill_between(x, p_pct, 0, where=p_pct < 0, interpolate=True, color="#fecaca", alpha=0.72, zorder=2)
        ax.axhline(0, color="#94a3b8", linestyle="--", linewidth=1.0, alpha=0.75)

        add_date_separators_session(ax, stock_plot_df, linewidth=2.0)
        set_intraday_ticks(ax, stock_plot_df)

        y_low = min(float(p_pct.min()) - 1, -1)
        y_high = max(float(p_pct.max()) + 1, 1)
        ax.set_xlim(x_min, x_max)
        ax.set_ylim(y_low, y_high)
        ax.set_ylabel(
            " STOCK CHANGE % ",
            fontsize=Y_AXIS_LABEL_FONT_SIZE,
            color=Y_AXIS_LABEL_COLOR,
            fontweight="normal",
            labelpad=7,
            bbox={"boxstyle": "round,pad=0.28", "facecolor": "none", "edgecolor": Y_AXIS_LABEL_COLOR, "linewidth": 1.0, "alpha": 0.95},
        )
        ax.yaxis.set_major_formatter(FuncFormatter(lambda value, _: f"{value:.0f}%"))
        ax.grid(axis="y", color="#d9e2ef", linestyle="--", linewidth=0.8, alpha=0.75)
        ax.grid(axis="x", alpha=0)
        ax.tick_params(axis="x", labelsize=8, rotation=45, colors="#172554")
        ax.tick_params(axis="y", labelsize=12, colors="#172554")
        for spine in ax.spines.values():
                spine.set_color("#dbe6f4")

        dates = list(pd.unique(stock_plot_df["session_date"]))
        for idx, session_date in enumerate(dates):
                day_df = stock_plot_df[stock_plot_df["session_date"] == session_date]
                start_x = float(day_df["x_idx"].min()) - 0.5
                end_x = float(day_df["x_idx"].max()) + 0.5
                band_ax.axvspan(start_x, end_x, color=SESSION_BAND_COLOR, alpha=1.0)
                band_ax.text((start_x + end_x) / 2.0, 0.5, format_session_band_date(session_date, idx == 0, session_index=idx), color=SESSION_BAND_FONT_COLOR, fontsize=SESSION_BAND_FONT_SIZE, weight="bold", ha="center", va="center", clip_on=False)
                if idx != 0:
                        band_ax.axvline(start_x - SESSION_SEPARATOR_SHIFT, color=SESSION_SEPARATOR_COLOR, linewidth=2.125, alpha=1.0)
                        ax.axvline(start_x - SESSION_SEPARATOR_SHIFT, color=SESSION_SEPARATOR_COLOR, linewidth=2.125, alpha=0.95, zorder=7)
        band_ax.set_xlim(x_min, x_max)
        band_ax.set_ylim(0, 1)
        add_session_day_night_markers(band_ax, stock_plot_df)
        band_ax.axis("off")

        plt.savefig(stock_chart_path, dpi=150, bbox_inches="tight", facecolor=fig.get_facecolor())
        plt.close(fig)


def render_all_stock_lines_chart(stock_line_data: list[tuple[str, pd.DataFrame]], all_stocks_chart_path: str, entry_date_str: str, end_date_str: str, benchmark_line_data: list[tuple[str, pd.DataFrame]] | None = None, replay_x_idx: float | None = None):
    benchmark_line_data = benchmark_line_data or []
    benchmark_by_ticker = {ticker: stock_df for ticker, stock_df in benchmark_line_data}
    regular_stock_line_data = [(ticker, stock_df) for ticker, stock_df in stock_line_data if ticker not in benchmark_by_ticker]
    reference_source = regular_stock_line_data or benchmark_line_data
    if not reference_source:
        return

    fig = plt.figure(figsize=(20, 9), facecolor="#f8fbff")
    ax = fig.add_axes([0.045, 0.12, 0.79, 0.80], facecolor="#ffffff")
    band_ax = fig.add_axes([0.045, 0.92, 0.79, SESSION_BAND_HEIGHT], sharex=ax, facecolor=SESSION_BAND_COLOR)

    colors = STOCK_LINE_COLORS
    all_y = []
    line_end_labels = []
    reference_df = reference_source[0][1]
    for idx, (ticker, stock_df) in enumerate(regular_stock_line_data):
        plot_stock_df = stock_df[~stock_df.get("__is_tbd_session", False).fillna(False)].copy()
        if plot_stock_df.empty:
            continue
        all_y.extend(plot_stock_df["pnl_pct"].astype(float).tolist())
        visible_stock_df = plot_stock_df if replay_x_idx is None else plot_stock_df[plot_stock_df["x_idx"].astype(float) <= replay_x_idx].copy()
        if visible_stock_df.empty:
            continue
        p_pct = visible_stock_df["pnl_pct"].astype(float)
        line_color = lighten_hex_color(colors[idx % len(colors)], 0.20)
        ax.plot(visible_stock_df["x_idx"], p_pct, linewidth=1.05, color=line_color, label=f"{ticker} ({p_pct.iloc[-1]:+.2f}%)")
        add_latest_session_end_dot(ax, visible_stock_df, "pnl_pct", line_color, size=18)
        line_end_labels.append((ticker, float(visible_stock_df["x_idx"].iloc[-1]), float(p_pct.iloc[-1]), line_color))

    benchmark_metrics = []
    for ticker in BENCHMARK_TICKERS:
        stock_df = benchmark_by_ticker.get(ticker)
        if stock_df is None:
            continue
        plot_stock_df = stock_df[~stock_df.get("__is_tbd_session", False).fillna(False)].copy()
        if plot_stock_df.empty:
            continue
        all_y.extend(plot_stock_df["pnl_pct"].astype(float).tolist())
        visible_stock_df = plot_stock_df if replay_x_idx is None else plot_stock_df[plot_stock_df["x_idx"].astype(float) <= replay_x_idx].copy()
        if visible_stock_df.empty:
            continue
        p_pct = visible_stock_df["pnl_pct"].astype(float)
        line_color = BENCHMARK_COLORS.get(ticker, "#111827")
        ax.plot(
            visible_stock_df["x_idx"],
            p_pct,
            linewidth=1.6,
            linestyle=(0, (5, 3)),
            color=line_color,
            alpha=0.98,
            label=f"{ticker} Benchmark ({p_pct.iloc[-1]:+.2f}%)",
            zorder=9,
        )
        add_latest_session_end_dot(ax, visible_stock_df, "pnl_pct", line_color, size=20)
    if replay_x_idx is None:
        benchmark_metrics = get_benchmark_metrics(benchmark_line_data)
    else:
        benchmark_metrics = get_benchmark_metrics([(ticker, stock_df[stock_df["x_idx"].astype(float) <= replay_x_idx].copy()) for ticker, stock_df in benchmark_line_data])

    stock_metrics = []
    for idx, (ticker, stock_df) in enumerate(regular_stock_line_data):
        plot_stock_df = stock_df[~stock_df.get("__is_tbd_session", False).fillna(False)].copy()
        if plot_stock_df.empty:
            continue
        visible_stock_df = plot_stock_df if replay_x_idx is None else plot_stock_df[plot_stock_df["x_idx"].astype(float) <= replay_x_idx].copy()
        if visible_stock_df.empty:
            continue
        final_pnl_pct = float(visible_stock_df["pnl_pct"].astype(float).iloc[-1])
        stock_metrics.append({"title": ticker, "value": f"{final_pnl_pct:+.2f}%", "color": colors[idx % len(colors)], "subtitle": "Final P&L", "value_num": final_pnl_pct})

    stock_metrics.sort(key=lambda item: item["value_num"], reverse=True)
    for metric in stock_metrics:
        metric.pop("value_num", None)
    if not all_y:
        plt.close(fig)
        return

    x_values = reference_df["x_idx"].astype(float)
    x_min = float(x_values.min()) - 0.5
    x_max = float(x_values.max()) + 0.5
    y_min = min(all_y) - 1
    y_max = max(all_y) + 1
    label_x_offsets = [0.16, 4]
    ax.axhline(0, color="#94a3b8", linestyle="--", linewidth=1.0, alpha=0.75)
    add_tbd_session_watermarks(ax, reference_df)
    add_date_separators_session(ax, reference_df, linewidth=2.0)
    set_intraday_ticks(ax, reference_df)
    ax.set_xlim(x_min, x_max + 1.70)
    ax.set_ylim(y_min, y_max)

    # Pack labels in a lane; very close final returns can share a row.
    sorted_labels = sorted(line_end_labels, key=lambda item: item[2], reverse=True)
    placed_rows = []
    min_gap = max((y_max - y_min) * 0.020, 0.11)
    same_row_pct_tolerance = 0.25
    for ticker, last_x, last_y, line_color in sorted_labels:
        display_pct = round(last_y, 2)
        display_y = last_y
        if (
            placed_rows
            and abs(placed_rows[-1]["display_pct"] - display_pct) <= same_row_pct_tolerance
            and placed_rows[-1]["count"] < 2
        ):
            row_idx = len(placed_rows) - 1
            display_y = placed_rows[row_idx]["y"]
            column_idx = placed_rows[row_idx]["count"]
            placed_rows[row_idx]["count"] += 1
        else:
            if placed_rows and placed_rows[-1]["y"] - display_y < min_gap:
                display_y = placed_rows[-1]["y"] - min_gap
            column_idx = 0
            placed_rows.append({"y": display_y, "count": 1, "display_pct": display_pct})
            row_idx = len(placed_rows) - 1
        placed_rows[row_idx].setdefault("labels", []).append((ticker, last_x, line_color, column_idx))

    if placed_rows:
        overflow = (y_min + min_gap * 0.5) - placed_rows[-1]["y"]
        if overflow > 0:
            for row in placed_rows:
                row["y"] += overflow

    for row in placed_rows:
        for ticker, _last_x, line_color, column_idx in row.get("labels", []):
            label_text = ax.text(
                x_max + label_x_offsets[column_idx],
                row["y"],
                ticker,
                ha="left",
                va="center",
                fontsize=8.2,
                color="#ffffff",
                weight="bold",
                bbox={
                    "boxstyle": "round,pad=0.15",
                    "facecolor": darken_hex_color(line_color, 0.45),
                    "edgecolor": darken_hex_color(line_color, 0.45),
                    "linewidth": 0.35,
                    "alpha": 0.96,
                },
                clip_on=False,
                zorder=12,
            )
    ax.set_ylabel(
        " ALL STOCKS PLOTTING (%) ",
        fontsize=Y_AXIS_LABEL_FONT_SIZE,
        color=Y_AXIS_LABEL_COLOR,
        fontweight="normal",
        labelpad=7,
        bbox={"boxstyle": "round,pad=0.28", "facecolor": "none", "edgecolor": Y_AXIS_LABEL_COLOR, "linewidth": 1.0, "alpha": 0.95},
    )
    ax.yaxis.set_major_locator(MultipleLocator(2.0))
    ax.yaxis.set_minor_locator(MultipleLocator(1.0))
    ax.yaxis.set_major_formatter(FuncFormatter(lambda value, _: f"{value:.0f}%"))
    ax.grid(axis="y", which="major", color="#d9e2ef", linestyle="--", linewidth=0.8, alpha=0.75)
    ax.grid(axis="y", which="minor", color="#d9e2ef", linestyle="--", linewidth=0.65, alpha=0.55)
    ax.grid(axis="x", alpha=0)
    ax.tick_params(axis="x", labelsize=8, rotation=45, colors="#172554")
    ax.tick_params(axis="y", labelsize=12, colors="#172554")
    for spine in ax.spines.values():
        spine.set_color("#dbe6f4")

    dates = list(pd.unique(reference_df["session_date"]))
    for idx, session_date in enumerate(dates):
        day_df = reference_df[reference_df["session_date"] == session_date]
        start_x = float(day_df["x_idx"].min()) - 0.5
        end_x = float(day_df["x_idx"].max()) + 0.5
        band_ax.axvspan(start_x, end_x, color=SESSION_BAND_COLOR, alpha=1.0)
        is_tbd = bool(day_df.get("__is_tbd_session", False).fillna(False).all())
        font_size = SESSION_BAND_FONT_SIZE * 0.90 if idx == 0 else SESSION_BAND_FONT_SIZE
        band_ax.text((start_x + end_x) / 2.0, 0.5, format_session_band_date(session_date, idx == 0, is_tbd=is_tbd, session_index=idx), color=SESSION_BAND_FONT_COLOR, fontsize=font_size, weight="bold", ha="center", va="center", clip_on=False)
        if idx != 0:
            band_ax.axvline(start_x - SESSION_SEPARATOR_SHIFT, color=SESSION_SEPARATOR_COLOR, linewidth=2.125, alpha=1.0)
            ax.axvline(start_x - SESSION_SEPARATOR_SHIFT, color=SESSION_SEPARATOR_COLOR, linewidth=2.125, alpha=0.95, zorder=7)
    band_ax.set_xlim(x_min, x_max)
    band_ax.set_ylim(0, 1)
    add_session_day_night_markers(band_ax, reference_df)
    band_ax.axis("off")

    stock_table_h = get_stock_performance_table_height(len(stock_metrics))
    stock_table_y = 0.905 - stock_table_h
    if benchmark_metrics:
        benchmark_h = 0.165
        benchmark_gap = 0.045
        benchmark_y = max(0.095, stock_table_y - benchmark_gap - benchmark_h)
        draw_stock_performance_table(fig, stock_metrics, y=stock_table_y, h=stock_table_h)
        draw_benchmark_performance_box(fig, benchmark_metrics, f"T0-T{max(len(dates) - 1, 0)}", y=benchmark_y, show_dash_rows=True)
    else:
        draw_stock_performance_table(fig, stock_metrics, y=stock_table_y, h=stock_table_h)
    plt.savefig(all_stocks_chart_path, dpi=150, bbox_inches="tight", facecolor=fig.get_facecolor())
    plt.close(fig)


def render_stock_candle_report(ticker: str, df: pd.DataFrame, chart_path: str, entry_price: float, exit_price: float, entry_ts=None, exit_ts=None, benchmark_line_data: list[tuple[str, pd.DataFrame]] | None = None):
    fig = plt.figure(figsize=(20, 9), facecolor="#f8fbff")
    ax_pct = fig.add_axes([0.045, 0.12, 0.79, 0.80], facecolor="#ffffff")
    ax_price = ax_pct.twinx()
    ax_price.patch.set_alpha(0)
    band_ax = fig.add_axes([0.045, 0.92, 0.79, SESSION_BAND_HEIGHT], sharex=ax_pct, facecolor=SESSION_BAND_COLOR)

    entry_label = pd.to_datetime(entry_ts).strftime("%b %d %I:%M %p").replace(" 0", " ") if entry_ts is not None else "Entry"
    exit_label = pd.to_datetime(exit_ts).strftime("%b %d %I:%M %p").replace(" 0", " ") if exit_ts is not None else "Exit"

    x_values = df["x_idx"].astype(float)
    x_min = float(x_values.min()) - 0.5
    x_max = float(x_values.max()) + 0.5
    plot_df = df[~df.get("__is_tbd_session", False).fillna(False)].copy()
    p_pct = plot_df["pnl_pct"].astype(float)
    candles_df = plot_df[["timestamp", "open", "high", "low", "close", "x_idx", "session_date", "session_time"]].copy()

    ax_pct.axhline(0, color="#94a3b8", linestyle="--", linewidth=1.0, alpha=0.75, zorder=3)
    ax_pct.text(
        0.5,
        0.52,
        ticker,
        transform=ax_pct.transAxes,
        ha="center",
        va="center",
        fontsize=120,
        color="#172554",
        alpha=0.08,
        weight="bold",
        zorder=1,
    )
    plot_candlesticks(ax_price, candles_df)
    entry_x = x_min
    if entry_ts is not None:
        entry_ts_value = pd.to_datetime(entry_ts)
        entry_rows = plot_df[plot_df["timestamp"] == entry_ts_value]
        if entry_rows.empty:
            entry_rows = plot_df[plot_df["timestamp"] >= entry_ts_value].head(1)
        if entry_rows.empty:
            entry_rows = plot_df[plot_df["timestamp"] <= entry_ts_value].tail(1)
        if not entry_rows.empty:
            entry_x = float(entry_rows.iloc[0]["x_idx"])
    net_pct = ((exit_price - entry_price) / entry_price * 100) if entry_price else 0.0
    net_color = "#0f9f55" if net_pct >= 0 else "#dc2626"
    ax_price.hlines(entry_price, entry_x, x_max, color="#374151", linestyle="-", linewidth=1.6, alpha=0.9, label="Entry Price", zorder=5)
    ax_price.hlines(exit_price, entry_x, x_max, color=net_color, linestyle="-", linewidth=1.6, alpha=0.9, label="Exit Price", zorder=5)
    connector_color = "#111827"
    connector_df = df[~df.get("__is_tbd_session", False).fillna(False)].copy()
    exit_ts_value = pd.to_datetime(exit_ts) if exit_ts is not None else None
    exit_session_date = exit_ts_value.date() if exit_ts_value is not None else None
    exit_day_df = connector_df[connector_df["session_date"] == exit_session_date].copy() if exit_session_date is not None else pd.DataFrame()
    if not exit_day_df.empty:
        exit_day_df = exit_day_df.sort_values("timestamp").reset_index(drop=True)
        exact_exit_row = exit_day_df[exit_day_df["timestamp"] == exit_ts_value]
        if exact_exit_row.empty:
            exact_exit_row = exit_day_df[exit_day_df["timestamp"] <= exit_ts_value].tail(1)
        exit_row_position = int(exact_exit_row.index[-1]) if not exact_exit_row.empty else len(exit_day_df) - 1
        connector_row_position = max(0, exit_row_position - 5)
        connector_x = float(exit_day_df.iloc[connector_row_position]["x_idx"])
    elif not connector_df.empty:
        connector_df = connector_df.sort_values("timestamp").reset_index(drop=True)
        connector_x = float(connector_df.iloc[max(0, len(connector_df) - 6)]["x_idx"])
    else:
        connector_x = x_max - (x_max - x_min) * 0.12
    connector_label_y = (entry_price + exit_price) / 2.0
    ax_price.vlines(connector_x, entry_price, exit_price, color=connector_color, linewidth=1.5, alpha=0.95, zorder=8)
    ax_price.scatter([connector_x, connector_x], [entry_price, exit_price], s=28, color=connector_color, edgecolor="#ffffff", linewidth=0.8, zorder=9)
    ax_price.annotate(
        f" {net_pct:+.2f}% ",
        xy=(connector_x, connector_label_y),
        xytext=(8, 0),
        textcoords="offset points",
        ha="left",
        va="center",
        rotation=90,
        fontsize=9,
        color="#ffffff",
        weight="bold",
        bbox={"boxstyle": "round,pad=0.18", "facecolor": net_color, "edgecolor": net_color, "linewidth": 0.8, "alpha": 0.96},
        zorder=10,
    )

    y_low = min(float(p_pct.min()) - 0.75, -0.75)
    y_high = max(float(p_pct.max()) + 0.75, 0.75)
    ax_pct.set_xlim(x_min, x_max)
    ax_pct.set_ylim(y_low, y_high)
    ax_pct.set_ylabel(
        " CHANGE %",
        fontsize=Y_AXIS_LABEL_FONT_SIZE,
        color=Y_AXIS_LABEL_COLOR,
        fontweight="normal",
        labelpad=7,
        bbox={"boxstyle": "round,pad=0.28", "facecolor": "none", "edgecolor": Y_AXIS_LABEL_COLOR, "linewidth": 1.0, "alpha": 0.95},
    )
    ax_pct.yaxis.set_major_formatter(FuncFormatter(lambda value, _: f"{value:.0f}%"))
    ax_pct.grid(axis="y", color="#d9e2ef", linestyle="--", linewidth=0.8, alpha=0.75)
    ax_pct.grid(axis="x", alpha=0)
    ax_pct.tick_params(axis="x", labelsize=8, rotation=45, colors="#172554")
    ax_pct.tick_params(axis="y", labelsize=12, colors="#172554")
    ax_price.set_ylabel("")
    ax_price.tick_params(axis="y", labelsize=12, colors="#475569")
    ax_price.grid(False)

    add_tbd_session_watermarks(ax_pct, df)
    add_date_separators_session(ax_pct, df, linewidth=2.0)
    set_intraday_ticks(ax_pct, df)
    add_entry_window_focus(ax_pct, df, entry_ts)
    for ax in (ax_pct, ax_price):
        for spine in ax.spines.values():
            spine.set_color("#dbe6f4")

    trade_metrics = [
        {"title": "Entry Date", "value": entry_label, "color": "#3b82f6"},
        {"title": "Entry Price", "value": f"{entry_price:.2f}", "color": "#3b82f6"},
        {"title": "Exit Date", "value": exit_label, "color": "#a855f7"},
        {"title": "Exit Price", "value": f"{exit_price:.2f}", "color": "#a855f7"},
        {"title": "Net % Chg", "value": f"{net_pct:+.2f}%", "color": net_color},
    ]
    draw_right_metric_tiles(fig, trade_metrics, x=0.875, start_y=0.855, w=0.085, header="Trade Summary", title_font=METRIC_TITLE_FONT, value_font=11, subtitle_font=METRIC_SUBTITLE_FONT)

    dates = list(pd.unique(df["session_date"]))
    draw_benchmark_performance_box(fig, get_benchmark_metrics(benchmark_line_data or []), f"T0-T{max(len(dates) - 1, 0)}", x=0.875, y=0.335, w=0.085, h=0.165)
    for idx, session_date in enumerate(dates):
        day_df = df[df["session_date"] == session_date]
        start_x = float(day_df["x_idx"].min()) - 0.5
        end_x = float(day_df["x_idx"].max()) + 0.5
        band_ax.axvspan(start_x, end_x, color=SESSION_BAND_COLOR, alpha=1.0)
        is_tbd = bool(day_df.get("__is_tbd_session", False).fillna(False).all())
        band_ax.text((start_x + end_x) / 2.0, 0.5, format_session_band_date(session_date, idx == 0, is_tbd=is_tbd, session_index=idx), color=SESSION_BAND_FONT_COLOR, fontsize=SESSION_BAND_FONT_SIZE, weight="bold", ha="center", va="center", clip_on=False)
        if idx != 0:
            band_ax.axvline(start_x - SESSION_SEPARATOR_SHIFT, color=SESSION_SEPARATOR_COLOR, linewidth=2.125, alpha=1.0)
            ax_pct.axvline(start_x - SESSION_SEPARATOR_SHIFT, color=SESSION_SEPARATOR_COLOR, linewidth=2.125, alpha=0.95, zorder=7)
    band_ax.set_xlim(x_min, x_max)
    band_ax.set_ylim(0, 1)
    add_session_day_night_markers(band_ax, df, entry_ts=entry_ts, show_entry_window_label=True)
    band_ax.axis("off")

    plt.savefig(chart_path, dpi=150, bbox_inches="tight", facecolor=fig.get_facecolor())
    plt.close(fig)


def build_all_stocks_replay_payload(stock_line_data: list[tuple[str, pd.DataFrame]], benchmark_line_data: list[tuple[str, pd.DataFrame]] | None = None) -> dict:
        benchmark_line_data = benchmark_line_data or []
        benchmark_by_ticker = {ticker: stock_df for ticker, stock_df in benchmark_line_data}
        regular_stock_line_data = [(ticker, stock_df) for ticker, stock_df in stock_line_data if ticker not in benchmark_by_ticker]
        replay_sources = regular_stock_line_data + [(ticker, benchmark_by_ticker[ticker]) for ticker in BENCHMARK_TICKERS if ticker in benchmark_by_ticker]
        reference_source = regular_stock_line_data or benchmark_line_data
        if not replay_sources or not reference_source:
                return {"series": [], "frames": [], "sessions": [], "yMin": -1.0, "yMax": 1.0}

        series = []
        all_y = []
        all_x = []
        for idx, (ticker, stock_df) in enumerate(replay_sources):
                plot_stock_df = stock_df[~stock_df.get("__is_tbd_session", False).fillna(False)].copy()
                if plot_stock_df.empty:
                        continue
                is_benchmark = ticker in benchmark_by_ticker
                line_color = BENCHMARK_COLORS.get(ticker, "#111827") if is_benchmark else lighten_hex_color(STOCK_LINE_COLORS[idx % len(STOCK_LINE_COLORS)], 0.20)
                points = []
                for row in plot_stock_df.itertuples(index=False):
                        x_value = float(getattr(row, "x_idx"))
                        y_value = float(getattr(row, "pnl_pct"))
                        if pd.isna(x_value) or pd.isna(y_value):
                                continue
                        ts_value = getattr(row, "timestamp", None)
                        session_time = getattr(row, "session_time", "")
                        points.append({
                                "x": x_value,
                                "y": y_value,
                                "time": pd.to_datetime(ts_value).strftime("%Y-%m-%d %H:%M") if ts_value is not None and not pd.isna(ts_value) else str(session_time),
                        })
                        all_x.append(x_value)
                        all_y.append(y_value)
                if points:
                        series.append({"ticker": ticker, "color": line_color, "benchmark": is_benchmark, "points": points})

        if not series or not all_x or not all_y:
                return {"series": [], "frames": [], "sessions": [], "yMin": -1.0, "yMax": 1.0}

        reference_df = reference_source[0][1]
        sessions = []
        for idx, session_date in enumerate(pd.unique(reference_df["session_date"])):
                day_df = reference_df[reference_df["session_date"] == session_date]
                if day_df.empty:
                        continue
                is_tbd = bool(day_df.get("__is_tbd_session", False).fillna(False).all())
                sessions.append({
                        "start": float(day_df["x_idx"].min()) - 0.5,
                        "end": float(day_df["x_idx"].max()) + 0.5,
                        "label": format_session_band_date(session_date, idx == 0, is_tbd=is_tbd, session_index=idx),
                })

        y_min = min(all_y) - 1.0
        y_max = max(all_y) + 1.0
        if y_min == y_max:
                y_min -= 1.0
                y_max += 1.0

        return {
                "series": series,
                "frames": sorted(set(all_x)),
                "sessions": sessions,
                "xMin": min(all_x) - 0.5,
                "xMax": max(all_x) + 0.5,
                "yMin": y_min,
                "yMax": y_max,
        }


def format_dashboard_cell(value) -> str:
    if value is None:
        return ""
    if isinstance(value, bool):
        return "Yes" if value else "No"
    if isinstance(value, (int, float)):
        if abs(float(value)) >= 1_000_000_000_000:
            return f"{float(value) / 1_000_000_000_000:.2f}T"
        if abs(float(value)) >= 1_000_000_000:
            return f"{float(value) / 1_000_000_000:.2f}B"
        if abs(float(value)) >= 1_000_000:
            return f"{float(value) / 1_000_000:.2f}M"
        return f"{float(value):.2f}".rstrip("0").rstrip(".")
    return str(value)


SCREENER_TABLE_COLUMNS = [
    ("Ticker", "TICKER"),
    ("Anchor Date", "ANCHOR_DATE"),
    ("Price", "PRICE"),
    ("Volume", "VOLUME"),
    ("Rvol", "RVOL"),
    ("Mcap", "MCAP"),
    ("Change%", "DAILY_CHANGE_%"),
    ("Drop From High", "DROP_FROM_HIGH_%"),
    ("RSI14", "RSI14"),
    ("10D Velo", "10DV"),
    ("Closing Position", "DAILY_CLOSING_POSITION"),
    ("MACD", "MACD"),
    ("Signal", "MACD_SIGNAL"),
    ("Histogram", "MACD_HISTOGRAM"),
    ("MACD/P %", "MACD_PCT"),
    ("Hist/P %", "HIST_PCT"),
    ("Comment", "COMMENT"),
]

SCREENER_COMMENT_KEY = "COMMENT"
# Breakout labels, produced by the screener's real lookback-high logic
# (see calculate_breakout_comment in daily_anchor_screener.py).
SCREENER_COMMENT_LABELS = [
    "Below 5D high",
    "5D high",
    "10D high",
    "1M high",
    "2M high",
    "3M high",
    "6M high",
    "1Y high",
]
# Longest breakout gets the highlight treatment in the table.
SCREENER_COMMENT_STRONGEST = "1Y high"


def screener_column_class(key: str) -> str:
    safe_key = re.sub(r"[^a-z0-9]+", "-", str(key).lower()).strip("-")
    return f"screener-col-{safe_key}" if safe_key else ""


def screener_conditional_cell_class(key: str, value) -> str:
    if key == "DAILY_CLOSING_POSITION":
        zone = str(value or "").split("&")[-1].strip()
        zone_buckets = {
            ">U7": ("pos", 5),
            "U6-U7": ("pos", 5),
            "U5-U6": ("pos", 5),
            "U4-U5": ("pos", 4),
            "U3-U4": ("pos", 4),
            "U2-U3": ("pos", 3),
            "U1-U2": ("pos", 2),
            "Mid-U1": ("pos", 1),
            "Mid-L1": ("neg", 1),
            "L1-L2": ("neg", 2),
            "L2-L3": ("neg", 3),
            "L3-L4": ("neg", 4),
            "L4-L5": ("neg", 5),
            "L5-L6": ("neg", 5),
            "L6-L7": ("neg", 5),
            "<L7": ("neg", 5),
        }
        if zone in zone_buckets:
            direction, bucket = zone_buckets[zone]
            return f"screener-position-{direction}-{bucket}"
        return ""

    if key in {"PPO_GT_SIGNAL", "PPO_CROSS", "MACD_GT_SIGNAL", "MACD_CROSS", "TRIPLE_MA_BULLISH"}:
        if value is True:
            return "screener-bool-yes"
        if value is False:
            return "screener-bool-no"
        text_value = str(value or "").strip().lower()
        if text_value == "yes":
            return "screener-bool-yes"
        if text_value == "no":
            return "screener-bool-no"
        return ""

    if key == SCREENER_COMMENT_KEY:
        comment_classes = {
            "Below 5D high": "screener-comment-below",
            "5D high": "screener-comment-5d",
            "10D high": "screener-comment-10d",
            "1M high": "screener-comment-1m",
            "2M high": "screener-comment-2m",
            "3M high": "screener-comment-3m",
            "6M high": "screener-comment-6m",
            "1Y high": "screener-comment-1y",
        }
        return comment_classes.get(str(value or "").strip(), "")

    try:
        numeric_value = float(value)
    except (TypeError, ValueError):
        return ""

    if key == "RVOL":
        if numeric_value >= 20:
            return "screener-rvol-5"
        if numeric_value >= 10:
            return "screener-rvol-4"
        if numeric_value >= 5:
            return "screener-rvol-3"
        if numeric_value >= 2:
            return "screener-rvol-2"
        if numeric_value >= 1:
            return "screener-rvol-1"
        return ""

    if key in {"DAILY_CHANGE_%", "T0_T3_CHANGE_%"}:
        percent_value = numeric_value * 100 if key == "DAILY_CHANGE_%" else numeric_value
        abs_percent = abs(percent_value)
        if abs_percent < 0.01:
            return ""
        direction = "pos" if percent_value > 0 else "neg"
        if abs_percent >= 10:
            bucket = 5
        elif abs_percent >= 5:
            bucket = 4
        elif abs_percent >= 2:
            bucket = 3
        elif abs_percent >= 1:
            bucket = 2
        else:
            bucket = 1
        return f"screener-change-{direction}-{bucket}"

    if key == "DROP_FROM_HIGH_%":
        percent_value = numeric_value * 100
        abs_percent = abs(percent_value)
        if abs_percent < 0.50:
            return ""
        if abs_percent >= 10:
            bucket = 5
        elif abs_percent >= 7:
            bucket = 4
        elif abs_percent >= 4:
            bucket = 3
        elif abs_percent >= 2:
            bucket = 2
        else:
            bucket = 1
        return f"screener-drop-{bucket}"

    if key == "RSI14":
        if numeric_value < 30:
            return "screener-rsi-neg-3"
        if numeric_value < 40:
            return "screener-rsi-neg-2"
        if numeric_value < 45:
            return "screener-rsi-neg-1"
        if numeric_value >= 70:
            return "screener-rsi-pos-3"
        if numeric_value >= 55:
            return "screener-rsi-pos-2"
        return "screener-rsi-pos-1"

    if key == "MOMENTUM_SCORE":
        if numeric_value >= 80:
            return "screener-score-high"
        if numeric_value >= 60:
            return "screener-score-mid"
        return "screener-score-low"

    if key in {"PPO", "PPO_SIGNAL", "PPO_HISTOGRAM", "MACD", "MACD_SIGNAL", "MACD_HISTOGRAM", "MACD_PCT", "HIST_PCT"}:
        if math.isclose(numeric_value, 0.0, abs_tol=1e-12):
            return ""
        return "screener-momentum-positive" if numeric_value > 0 else "screener-momentum-negative"

    return ""


def format_screener_table_value(row: dict, key: str) -> str:
    if key == SCREENER_COMMENT_KEY:
        return str(row.get(SCREENER_COMMENT_KEY) or "")
    value = row.get(key)
    if value is None and key.startswith("MACD"):
        value = row.get(key.replace("MACD", "PPO"))
    if key in {"MACD_PCT", "HIST_PCT"}:
        if value is None:
            price = row.get("PRICE")
            num = row.get("MACD") if key == "MACD_PCT" else row.get("MACD_HISTOGRAM")
            try:
                if price and float(price) > 0 and num is not None:
                    value = (float(num) / float(price)) * 100.0
            except (TypeError, ValueError):
                value = None
        if isinstance(value, (int, float)):
            return f"{float(value):.2f}%"
        return ""
    if key in {"MACD", "MACD_SIGNAL", "MACD_HISTOGRAM", "PPO", "PPO_SIGNAL", "PPO_HISTOGRAM"} and isinstance(value, (int, float)):
        return f"{float(value):.2f}"
    if key in {"MACD_GT_SIGNAL", "MACD_CROSS", "PPO_GT_SIGNAL", "PPO_CROSS"}:
        return "Yes" if value else "No"
    if key == "MOMENTUM_SCORE" and isinstance(value, (int, float)):
        return f"{float(value):.1f}"
    if key == "10DV" and isinstance(value, (int, float)):
        return f"{float(value):.1f}%"
    if key in {"DAILY_CHANGE_%", "DROP_FROM_HIGH_%"} and isinstance(value, (int, float)):
        val = float(value) * 100
        if abs(val) < 0.005:
            val = 0.0
        return f"{val:.2f}%"
    if key == "T0_T3_CHANGE_%" and isinstance(value, (int, float)):
        return f"{float(value):+.2f}%"
    return format_dashboard_cell(value)


def format_screener_sort_value(row: dict, key: str) -> str:
    value = row.get(key)
    if isinstance(value, bool):
        return "1" if value else "0"
    if isinstance(value, (int, float)):
        return f"{float(value):.12g}"
    if value is None:
        return ""
    return str(value)


def json_safe_value(value):
    if value is None:
        return None
    try:
        if pd.isna(value):
            return None
    except (TypeError, ValueError):
        pass
    if isinstance(value, (str, int, float, bool)):
        return value
    if isinstance(value, (date, datetime)):
        return value.isoformat()
    return str(value)


def format_anchor_display_date(value: str) -> str:
    try:
        parsed = datetime.strptime(str(value), "%Y-%m-%d").date()
    except ValueError:
        return str(value)
    day = parsed.day
    suffix = "th" if 11 <= day % 100 <= 13 else {1: "st", 2: "nd", 3: "rd"}.get(day % 10, "th")
    return f"{day}{suffix} {parsed:%b} ({parsed:%a}) {parsed:%Y}"


def build_screener_rows_payload(rows: list[dict]) -> list[dict]:
    payload = []
    for row in rows:
        price = row.get("PRICE")
        if row.get("MACD_PCT") is None:
            macd = row.get("MACD") if row.get("MACD") is not None else row.get("PPO")
            try:
                if price and float(price) > 0 and macd is not None:
                    row["MACD_PCT"] = (float(macd) / float(price)) * 100.0
            except (TypeError, ValueError):
                pass
        if row.get("HIST_PCT") is None:
            hist = row.get("MACD_HISTOGRAM") if row.get("MACD_HISTOGRAM") is not None else row.get("PPO_HISTOGRAM")
            try:
                if price and float(price) > 0 and hist is not None:
                    row["HIST_PCT"] = (float(hist) / float(price)) * 100.0
            except (TypeError, ValueError):
                pass
        display = {key: format_screener_table_value(row, key) for _label, key in SCREENER_TABLE_COLUMNS}
        sort_values = {
            key: display[key] if key == SCREENER_COMMENT_KEY else json_safe_value(row.get(key, row.get(key.replace("MACD", "PPO")) if "MACD" in key else None))
            for _label, key in SCREENER_TABLE_COLUMNS
        }
        payload.append(
            {
                "ticker": str(row.get("TICKER") or "").upper(),
                "anchorDate": str(row.get("ANCHOR_DATE") or ""),
                "display": display,
                "sort": sort_values,
            }
        )
    return payload


def build_t0_t3_change_by_ticker(stock_line_data: list[tuple[str, pd.DataFrame]] | None) -> dict[str, float]:
    changes = {}
    for ticker, stock_df in stock_line_data or []:
        if stock_df is None or stock_df.empty:
            continue
        plot_stock_df = stock_df[~stock_df.get("__is_tbd_session", False).fillna(False)].copy()
        if plot_stock_df.empty or "pnl_pct" not in plot_stock_df.columns:
            continue
        changes[str(ticker).upper()] = float(plot_stock_df["pnl_pct"].astype(float).iloc[-1])
    return changes


def build_screener_panel_html(screener_context: dict | None, t0_t3_change_by_ticker: dict[str, float] | None = None) -> str:
    if not screener_context:
        return ""

    config = screener_context.get("config")
    rows = screener_context.get("rows") or []
    selected_tickers = set(screener_context.get("selected_tickers") or [])
    shortlisted_rows = [row for row in rows if str(row.get("TICKER") or "").upper() in selected_tickers]
    table_columns = list(SCREENER_TABLE_COLUMNS)
    t0_t3_change_by_ticker = t0_t3_change_by_ticker or {}
    if t0_t3_change_by_ticker:
        table_columns.append(("Change % (T0-T3)", "T0_T3_CHANGE_%"))
    selected_text = format_tickers(selected_tickers)
    anchor_date = html.escape(format_anchor_display_date(getattr(config, "anchor_date", "")))
    filters = [
        ("MCAP", f"{format_dashboard_cell(getattr(config, 'mcap_min', None))}-{format_dashboard_cell(getattr(config, 'mcap_max', None))}"),
        ("Volume", f">= {format_dashboard_cell(getattr(config, 'min_volume', None))}"),
        ("Price", f">= {format_dashboard_cell(getattr(config, 'min_price', None))}"),
        ("10D Velocity%", f">= {format_dashboard_cell(getattr(config, 'min_atr10', None))}"),
        ("RSI14", f">= {format_dashboard_cell(getattr(config, 'min_rsi14', None))}"),
        ("MACD>SIGNAL", "Yes" if getattr(config, "require_macd_gt_signal", getattr(config, "require_ppo_gt_signal", False)) else "No"),
        ("MACD Cross", "Yes" if getattr(config, "require_macd_cross", getattr(config, "require_ppo_cross", False)) else "No"),
    ]
    filter_cards = "\n".join(
        f'<div class="screener-filter"><span>{html.escape(label)}</span><strong>{html.escape(value)}</strong></div>'
        for label, value in filters
    )
    header_html = "".join(
        f'<th class="sortable {screener_column_class(key)}" data-sort-key="{html.escape(key)}" aria-sort="none">'
        f'<span class="th-inner"><span class="th-label">{html.escape(label)}</span>'
        f'<span class="sort-arrow" aria-hidden="true"></span></span></th>'
        for label, key in table_columns
    )
    body_rows = []
    for row in shortlisted_rows:
        ticker = str(row.get("TICKER") or "").upper()
        display_row = dict(row)
        price = display_row.get("PRICE")
        if display_row.get("MACD_PCT") is None:
            macd = display_row.get("MACD") if display_row.get("MACD") is not None else display_row.get("PPO")
            try:
                if price and float(price) > 0 and macd is not None:
                    display_row["MACD_PCT"] = (float(macd) / float(price)) * 100.0
            except (TypeError, ValueError):
                pass
        if display_row.get("HIST_PCT") is None:
            hist = display_row.get("MACD_HISTOGRAM") if display_row.get("MACD_HISTOGRAM") is not None else display_row.get("PPO_HISTOGRAM")
            try:
                if price and float(price) > 0 and hist is not None:
                    display_row["HIST_PCT"] = (float(hist) / float(price)) * 100.0
            except (TypeError, ValueError):
                pass
        if ticker in t0_t3_change_by_ticker:
            display_row["T0_T3_CHANGE_%"] = t0_t3_change_by_ticker[ticker]
        is_selected = ticker in selected_tickers
        cells = []
        for _label, key in table_columns:
            display_value = format_screener_table_value(display_row, key)
            column_class = screener_column_class(key)
            if key == "TICKER":
                safe_ticker = html.escape(ticker)
                safe_anchor_date = html.escape(str(display_row.get("ANCHOR_DATE") or getattr(config, "anchor_date", "")))
                sort_value = html.escape(format_screener_sort_value(display_row, key), quote=True)
                cells.append(
                    f'<td class="{column_class}" data-sort-value="{sort_value}"><button class="ticker-chart-link" type="button" '
                    f'onclick="openTickerChart(\'{safe_ticker}\', \'{safe_anchor_date}\')">{safe_ticker}</button></td>'
                )
            elif key == SCREENER_COMMENT_KEY:
                cell_classes = [column_class]
                conditional_class = screener_conditional_cell_class(key, display_value)
                if conditional_class:
                    cell_classes.append(conditional_class)
                sort_value = html.escape(format_screener_sort_value(display_row, key), quote=True)
                cells.append(f'<td class="{" ".join(cell_classes)}" data-sort-value="{sort_value}">{html.escape(display_value)}</td>')
            else:
                cell_classes = [column_class]
                conditional_class = screener_conditional_cell_class(key, display_row.get(key))
                if conditional_class:
                    cell_classes.append(conditional_class)
                sort_value = html.escape(format_screener_sort_value(display_row, key), quote=True)
                cells.append(f'<td class="{" ".join(cell_classes)}" data-sort-value="{sort_value}">{html.escape(display_value)}</td>')
        selected_class = " selected" if is_selected else ""
        body_rows.append(f'<tr class="{selected_class}">' + "".join(cells) + "</tr>")
    body_html = "\n".join(body_rows) if body_rows else f'<tr><td colspan="{len(table_columns)}">No selected stocks were found.</td></tr>'
    return f"""
    <section id="screener" class="panel active">
        <div class="screener-report">
            <div class="screener-summary">
                <div class="screener-heading">
                    <h2>Anchor Date {anchor_date}</h2>
                    <p>{len(shortlisted_rows):,} selected from {len(rows):,} scanner matches.</p>
                </div>
                <div class="selected-ticker-list">{html.escape(selected_text or 'No tickers selected')}</div>
            </div>
            <div class="screener-filters">{filter_cards}</div>
            <div class="screener-table-wrap">
                <table class="screener-table">
                    <thead><tr>{header_html}</tr></thead>
                    <tbody>{body_html}</tbody>
                </table>
            </div>
            <div class="report-notes">
                <div class="report-notes-head">
                    <h3>Report Notes</h3>
                    <span class="report-notes-status" id="selectedStocksNoteStatus">Autosaved in this browser</span>
                </div>
                <textarea id="selectedStocksNote" rows="4" placeholder="Add your notes, observations, or follow-up reminders for this saved report..."></textarea>
            </div>
        </div>
    </section>
"""


def format_history_30d_value(value: float | int | None, prefix: str = "", suffix: str = "") -> str:
    if value is None:
        return "N/A"
    return f"{prefix}{float(value):,.2f}{suffix}"


def build_shortlisted_history_30d_payload(api_key: str, tickers: list[str], entry_date_obj: date, positions: dict) -> list[dict]:
    today = get_latest_closed_trading_day(datetime.now(ZoneInfo("America/New_York")).date())
    end_date_obj = min(get_nth_next_trading_day(entry_date_obj, 30), today)
    if end_date_obj < entry_date_obj:
        end_date_obj = entry_date_obj

    history_rows = []
    for ticker in tickers:
        position = positions.get(ticker)
        if not position:
            continue
        try:
            daily_df = fetch_daily_data(ticker, entry_date_obj.isoformat(), end_date_obj.isoformat(), api_key)
        except Exception as exc:
            log_warn(f"30D Follow-Through skipped for {ticker}: {exc}")
            continue
        if daily_df.empty:
            continue

        daily_df = daily_df.copy()
        daily_df["date"] = pd.to_datetime(daily_df["date"]).dt.date
        daily_df = daily_df[(daily_df["date"] >= entry_date_obj) & (daily_df["date"] <= end_date_obj)].sort_values("date")
        if daily_df.empty:
            continue

        entry_price = float(position["entry_price"])
        low_price = float(daily_df["low"].astype(float).min())
        high_price = float(daily_df["high"].astype(float).max())
        last_row = daily_df.iloc[-1]
        last_close = float(last_row["close"])
        low_pct = ((low_price - entry_price) / entry_price) * 100.0 if entry_price else 0.0
        high_pct = ((high_price - entry_price) / entry_price) * 100.0 if entry_price else 0.0
        last_pct = ((last_close - entry_price) / entry_price) * 100.0 if entry_price else 0.0
        range_pct = ((high_price - low_price) / entry_price) * 100.0 if entry_price else 0.0
        range_span = max(high_price - low_price, 1e-9)
        entry_marker_pct = max(0.0, min(100.0, ((entry_price - low_price) / range_span) * 100.0))
        last_marker_pct = max(0.0, min(100.0, ((last_close - low_price) / range_span) * 100.0))
        history_rows.append(
            {
                "ticker": ticker,
                "entry_date": entry_date_obj.isoformat(),
                "end_date": last_row["date"].isoformat(),
                "days": int(len(daily_df)),
                "entry_price": entry_price,
                "low_price": low_price,
                "high_price": high_price,
                "last_close": last_close,
                "low_pct": low_pct,
                "high_pct": high_pct,
                "last_pct": last_pct,
                "range_pct": range_pct,
                "entry_marker_pct": entry_marker_pct,
                "last_marker_pct": last_marker_pct,
            }
        )

    return sorted(history_rows, key=lambda row: row["ticker"])


def build_shortlisted_history_30d_html(history_rows: list[dict]) -> str:
    if not history_rows:
        return """
    <section id="history-30d" class="panel">
        <div class="history-empty">30D Follow-Through will appear after daily history is available.</div>
    </section>
"""

    cards = []
    for row in history_rows:
        ticker = html.escape(row["ticker"])
        entry_date = html.escape(row["entry_date"])
        last_pct = float(row["last_pct"])
        last_tone = "up" if last_pct >= 0 else "down"
        cards.append(
            f"""
            <article class="history-card">
                <div class="history-card-head">
                    <button class="ticker-chart-link history-ticker" type="button" onclick="openTickerChart('{ticker}', '{entry_date}')">{ticker}</button>
                    <span class="history-change {last_tone}">{last_pct:+.2f}%</span>
                </div>
                <div class="history-date">{html.escape(row['entry_date'])} to {html.escape(row['end_date'])} · {int(row['days'])} trading days</div>
                <div class="history-range">
                    <span class="history-marker entry" style="left: {row['entry_marker_pct']:.2f}%"></span>
                    <span class="history-marker last" style="left: {row['last_marker_pct']:.2f}%"></span>
                </div>
                <div class="history-values">
                    <span><em>Low</em>{format_history_30d_value(row['low_price'], '$')}</span>
                    <span><em>Entry</em>{format_history_30d_value(row['entry_price'], '$')}</span>
                    <span><em>Last</em>{format_history_30d_value(row['last_close'], '$')}</span>
                    <span><em>High</em>{format_history_30d_value(row['high_price'], '$')}</span>
                </div>
                <div class="history-footer">
                    <span>Range {format_history_30d_value(row['range_pct'], suffix='%')}</span>
                    <span>Low {row['low_pct']:+.2f}% · High {row['high_pct']:+.2f}%</span>
                </div>
            </article>
"""
        )
    return f"""
    <section id="history-30d" class="panel">
        <div class="history-panel">
            <div class="history-title">
                <h2>30D Follow-Through</h2>
                <p>Daily price range from entry date through up to 30 trading days.</p>
            </div>
            <div class="history-grid">
                {''.join(cards)}
            </div>
        </div>
    </section>
"""


def write_stock_chart_viewer(output_folder: str, portfolio_chart_path: str, all_stocks_chart_path: str, stock_chart_paths: list[str], entry_date_str: str, end_date_str: str, stock_line_data: list[tuple[str, pd.DataFrame]] | None = None, benchmark_line_data: list[tuple[str, pd.DataFrame]] | None = None, screener_context: dict | None = None, live_state: dict | None = None, shortlisted_history_30d: list[dict] | None = None, report_run_suffix: str = "") -> str:
        def image_src(path: str) -> str:
            rel_path = os.path.relpath(path, output_folder).replace("\\", "/")
            return f"{rel_path}?v={int(os.path.getmtime(path))}"

        portfolio_image = image_src(portfolio_chart_path)
        all_stocks_image = image_src(all_stocks_chart_path)
        individual_images = [image_src(path) for path in stock_chart_paths]
        individual_chart_items = []
        for path, src in zip(stock_chart_paths, individual_images):
            name = os.path.basename(path)
            match = re.match(r"2_(.*?) Chart 10m", name)
            ticker = match.group(1) if match else os.path.splitext(name)[0]
            individual_chart_items.append({"ticker": ticker, "src": src})
        header_logo_image = ""
        if os.path.exists(HEADER_LOGO_SOURCE):
            header_logo_image = copy_header_logo(HEADER_LOGO_SOURCE, output_folder)
        date_range = format_dashboard_date_range(
            datetime.strptime(entry_date_str, "%Y-%m-%d").date(),
            datetime.strptime(end_date_str, "%Y-%m-%d").date(),
        )
        report_label = f"{date_range} {report_run_suffix}".strip()
        viewer_path = os.path.join(output_folder, f"Dashboard {report_label}.html")
        individual_buttons_html = "\n".join(
            f'            <button class="stock-button{" active" if idx == 0 else ""}" type="button" onclick="showStockChart({idx}, this)">{item["ticker"]}</button>'
            for idx, item in enumerate(individual_chart_items)
        )
        first_individual_image = individual_chart_items[0]["src"] if individual_chart_items else ""
        header_logo_html = f'<img class="brand-logo" src="{header_logo_image}" alt="NRAS Alpha">' if header_logo_image else ""
        replay_payload = json.dumps(build_all_stocks_replay_payload(stock_line_data or [], benchmark_line_data), allow_nan=False)
        individual_charts_payload = json.dumps(individual_chart_items, allow_nan=False)
        report_note_storage_key = json.dumps(f"duo-report-note:{os.path.basename(output_folder)}:{os.path.basename(viewer_path)}", allow_nan=False)
        report_note_rel_path = json.dumps(get_report_note_rel_path(viewer_path), allow_nan=False)
        t0_t3_change_by_ticker = build_t0_t3_change_by_ticker(stock_line_data)
        screener_panel_html = build_screener_panel_html(screener_context, t0_t3_change_by_ticker)
        history_panel_html = build_shortlisted_history_30d_html(shortlisted_history_30d or [])
        selected_panel_html = (
            screener_panel_html.replace('id="screener"', 'id="screened"').replace('class="panel"', 'class="panel active"', 1)
            if screener_context
            else '<section id="screened" class="panel active"><div class="history-empty">Selected Stocks are available when a dashboard is launched from screener results.</div></section>'
        )
        live_snapshot_payload = json.dumps(live_state or {}, allow_nan=False)
        live_refresh_html = (
            '<div class="live-refresh-banner" id="liveRefreshBanner">'
            'Live 1-min close: next update in '
            '<strong id="liveRefreshCountdown">60</strong>s'
            '<span id="liveRefreshSnapshot"></span>'
            '</div>'
        )
        html_text = f"""<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <title>In-Swing Report Viewer</title>
    <style>
{FINVIZ_THEME_CSS}
        body {{ margin: 0; background: #f3f3f5; color: #22262f; font-family: var(--fv-font-sans); }}
        .header {{ display: grid; grid-template-columns: minmax(220px, 1fr) auto minmax(220px, 1fr); align-items: center; gap: 16px; padding: 3px 18px; background: #353945; color: white; position: sticky; top: 0; z-index: 2; border-bottom: 1px solid rgba(255,255,255,0.14); }}
        .brand {{ justify-self: start; display: flex; align-items: center; gap: 9px; min-width: 0; }}
        .brand-logo {{ display: block; width: 108px; height: 52px; object-fit: contain; border: 0; border-radius: 0; background: transparent; filter: brightness(0) invert(1); }}
        .brand-text {{ display: block; min-width: 0; }}
        .report-title {{ display: block; font-size: 14px; line-height: 1.1; font-weight: 600; letter-spacing: 0; white-space: nowrap; }}
        .report-subtitle {{ display: block; margin-top: 3px; color: rgba(255,255,255,0.72); font-size: 12px; line-height: 1.2; white-space: nowrap; }}
        .live-clock {{ justify-self: end; color: #ffffff; font-size: 12px; font-weight: 600; text-align: right; white-space: nowrap; }}
        .live-clock span {{ display: inline-block; width: 92px; margin-top: 3px; color: rgba(255,255,255,0.68); font-size: 13px; font-weight: 600; font-variant-numeric: tabular-nums; text-align: right; }}
        .tabs {{ display: inline-flex; gap: 4px; align-items: center; justify-self: center; border-radius: 999px; padding: 4px; background: rgba(255,255,255,0.13); border: 1px solid rgba(255,255,255,0.20); box-shadow: inset 0 1px 0 rgba(255,255,255,0.08); }}
        button {{ border: none; background: transparent; color: rgba(255,255,255,0.76); min-width: 112px; padding: 10px 22px; border-radius: 999px; cursor: pointer; font-size: 10.5px; font-weight: 500; text-align: center; white-space: nowrap; opacity: 1; transition: background 0.2s, color 0.2s, box-shadow 0.2s; }}
        button:hover {{ background: rgba(255,255,255,0.08); color: #ffffff; }}
        button.active {{ background: #ffffff; color: #22262f; box-shadow: 0 8px 18px rgba(0,0,0,0.22); font-weight: 600; }}
        button:focus-visible {{ outline: 2px solid rgba(255,255,255,0.85); outline-offset: 2px; }}
        .portfolio-subtabs-wrap {{ display: flex; justify-content: center; padding: 3px 8px 2px; background: #f3f3f5; border-bottom: 1px solid #dedfe5; box-shadow: inset 0 1px 0 rgba(255,255,255,0.72); }}
        .portfolio-subtabs-wrap.hidden {{ display: none; }}
        .portfolio-subtabs {{ display: inline-flex; gap: 3px; padding: 2px; border: 1px solid #c3c6d0; border-radius: 999px; background: #ffffff; box-shadow: 0 4px 12px rgba(20,22,29,0.07); }}
        .portfolio-subtabs button {{ min-width: 108px; padding: 6px 14px; background: transparent; color: #353945; font-size: 11.2px; font-weight: 800; box-shadow: none; }}
        .portfolio-subtabs button:hover {{ background: #f3f3f5; color: #22262f; }}
        .portfolio-subtabs button.active {{ background: #4c5263; color: #ffffff; box-shadow: 0 5px 12px rgba(34,38,47,0.18); }}
        .panel {{ display: none; padding: 2px 8px 6px; }}
        .panel.active {{ display: block; }}
        .image-wrap {{ display: flex; justify-content: center; align-items: flex-start; width: 100%; margin-bottom: 6px; }}
        .all-stocks-stage {{ position: relative; display: flex; justify-content: center; width: 100%; max-width: 100%; }}
        .replay-button {{ position: absolute; top: 1.1%; right: 11.8%; z-index: 3; background: #4c5263; color: #ffffff; padding: 6px 12px; font-size: 8.8px; box-shadow: 0 5px 11px rgba(34,38,47,0.18); }}
        .replay-button:hover {{ background: #22262f; }}
        .replay-button.active {{ background: #d91e2b; color: #ffffff; }}
        .replay-status {{ position: absolute; width: 1px; height: 1px; overflow: hidden; clip: rect(0 0 0 0); }}
        .replay-wrap {{ display: none; justify-content: center; width: 100%; }}
        .replay-wrap.active {{ display: flex; }}
        .replay-chart {{ display: block; width: auto; max-width: 100%; height: calc(100vh - 86px); aspect-ratio: 20 / 9; background: #ffffff; border: 1px solid #c3c6d0; border-radius: 8px; }}
        img {{ background: white; border: 1px solid #c3c6d0; border-radius: 8px; }}
        .fit-image {{ max-width: 100%; max-height: calc(100vh - 86px); width: auto; height: auto; object-fit: contain; }}
        .fit-image.hidden {{ display: none; }}
        .stock-picker {{ display: flex; flex-wrap: wrap; justify-content: center; align-items: center; gap: 4px; margin: 0 auto 1px; max-width: 72%; }}
        .stock-button {{ min-width: auto; background: #ffffff; color: #306dca; border: 1px solid #c3c6d0; padding: 5px 10px; font-size: 9px; font-weight: 600; box-shadow: 0 2px 6px rgba(20,22,29,0.08); }}
        .stock-button:hover {{ background: #f3f3f5; color: #306dca; }}
        .stock-button.active {{ background: #4c5263; color: #ffffff; box-shadow: 0 6px 14px rgba(34,38,47,0.18); }}
        .single-stock-wrap {{ display: flex; justify-content: center; align-items: flex-start; width: 100%; }}
        .single-stock-image {{ max-width: 96%; max-height: calc(100vh - 118px); width: auto; height: auto; object-fit: contain; }}
        .live-refresh-banner {{ display: none; max-width: 760px; margin: 10px auto 2px; padding: 7px 14px; border-radius: 999px; background: #353945; color: #ffffff; box-shadow: 0 8px 18px rgba(20,22,29,0.18); font-size: 12px; font-weight: 700; text-align: center; }}
        .live-refresh-banner.active {{ display: block; }}
        .live-refresh-banner strong {{ display: inline-block; min-width: 18px; color: #fcdc86; font-variant-numeric: tabular-nums; }}
        .live-refresh-banner span {{ margin-left: 10px; color: #c3c6d0; font-variant-numeric: tabular-nums; }}
        .screener-report {{ width: min(1760px, calc(100vw - 56px)); max-width: none; margin: 16px auto 26px; background: #ffffff; border: 1px solid #dedfe5; border-radius: 14px; box-shadow: 0 14px 34px rgba(20,22,29,0.08); overflow: hidden; }}
        .screener-summary {{ display: flex; justify-content: space-between; gap: 14px; align-items: center; padding: 9px 18px; background: linear-gradient(135deg, #353945, #4c5263); color: #ffffff; }}
        .screener-heading {{ display: block; min-width: 0; }}
        .screener-summary h2 {{ margin: 0; font-size: 12px; line-height: 1.2; white-space: nowrap; }}
        .screener-summary p {{ margin: 3px 0 0; padding: 0; background: transparent; color: rgba(255,255,255,0.82); font-size: 11px; font-weight: 500; white-space: nowrap; }}
        .screener-kicker {{ color: #fcdc86; font-size: 10px; font-weight: 700; letter-spacing: 0.08em; text-transform: uppercase; }}
        .selected-ticker-list {{ max-width: 38%; padding: 7px 12px; border-radius: 12px; background: rgba(255,255,255,0.12); font-size: 12px; font-weight: 600; line-height: 1.25; }}
        .screener-filters {{ display: grid; grid-template-columns: repeat(7, minmax(112px, 1fr)); gap: 8px; padding: 9px 14px; background: #ffffff; border-bottom: 1px solid #dedfe5; }}
        .screener-filter {{ border: 1px solid #dedfe5; border-radius: 10px; padding: 6px 9px; background: #ffffff; }}
        .screener-filter span {{ display: block; color: #676f85; font-size: 9px; font-weight: 600; text-transform: uppercase; }}
        .screener-filter strong {{ display: block; margin-top: 1px; color: #22262f; font-size: 11.5px; }}
        .screener-table-wrap {{ overflow-y: auto; overflow-x: hidden; max-height: calc(100vh - 260px); }}
        .screener-table {{ width: 100%; table-layout: fixed; border-collapse: collapse; font-size: 11.8px; }}
        .screener-table th {{ position: sticky; top: 0; background: #4c5263; color: #ffffff; text-align: center; vertical-align: middle; padding: 9px 6px; white-space: normal; z-index: 1; }}
        .screener-table th.sortable {{ cursor: pointer; user-select: none; }}
        .screener-table th.sortable .th-inner {{ display: inline-flex; align-items: center; justify-content: center; gap: 5px; line-height: 1; }}
        .screener-table th.sortable .sort-arrow {{ width: 0; height: 0; flex: none; border-left: 3.5px solid transparent; border-right: 3.5px solid transparent; border-bottom: 4.5px solid currentColor; opacity: 0; transition: opacity 0.15s ease, transform 0.15s ease; }}
        .screener-table th.sortable:hover .sort-arrow {{ opacity: 0.4; }}
        .screener-table th.sortable.sort-asc .sort-arrow,
        .screener-table th.sortable.sort-desc .sort-arrow {{ opacity: 1; }}
        .screener-table th.sortable.sort-desc .sort-arrow {{ transform: rotate(180deg); }}
        .screener-table th:first-child, .screener-table td:first-child {{ text-align: center; }}
        .screener-table td {{ border-top: 1px solid #dedfe5; padding: 8px 6px; text-align: center; vertical-align: middle; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }}
        .screener-table th.screener-col-ticker, .screener-table td.screener-col-ticker {{ width: 4.5%; }}
        .screener-table th.screener-col-anchor-date, .screener-table td.screener-col-anchor-date {{ width: 6.5%; }}
        .screener-table th.screener-col-momentum-score, .screener-table td.screener-col-momentum-score {{ width: 5.2%; }}
        .screener-table th.screener-col-price, .screener-table td.screener-col-price {{ width: 4.6%; }}
        .screener-table th.screener-col-volume, .screener-table td.screener-col-volume {{ width: 5.0%; }}
        .screener-table th.screener-col-rvol, .screener-table td.screener-col-rvol {{ width: 4.0%; }}
        .screener-table th.screener-col-mcap, .screener-table td.screener-col-mcap {{ width: 5.2%; }}
        .screener-table th.screener-col-daily-change, .screener-table td.screener-col-daily-change {{ width: 5.0%; padding-left: 3px; padding-right: 3px; }}
        .screener-table th.screener-col-drop-from-high, .screener-table td.screener-col-drop-from-high {{ width: 6.2%; padding-left: 3px; padding-right: 3px; }}
        .screener-table th.screener-col-rsi14, .screener-table td.screener-col-rsi14 {{ width: 4.4%; }}
        .screener-table th.screener-col-10dv, .screener-table td.screener-col-10dv {{ width: 4.4%; }}
        .screener-table th.screener-col-daily-closing-position, .screener-table td.screener-col-daily-closing-position {{ width: 8.0%; padding-left: 5px; padding-right: 5px; }}
        .screener-table th.screener-col-ppo, .screener-table td.screener-col-ppo,
        .screener-table th.screener-col-macd, .screener-table td.screener-col-macd,
        .screener-table th.screener-col-ppo-signal, .screener-table td.screener-col-ppo-signal,
        .screener-table th.screener-col-macd-signal, .screener-table td.screener-col-macd-signal {{ width: 4.5%; }}
        .screener-table th.screener-col-ppo-histogram, .screener-table td.screener-col-ppo-histogram,
        .screener-table th.screener-col-macd-histogram, .screener-table td.screener-col-macd-histogram {{ width: 5.4%; }}
        .screener-table th.screener-col-macd-pct, .screener-table td.screener-col-macd-pct,
        .screener-table th.screener-col-hist-pct, .screener-table td.screener-col-hist-pct {{ width: 5.4%; }}
        .screener-table th.screener-col-ppo-gt-signal, .screener-table td.screener-col-ppo-gt-signal,
        .screener-table th.screener-col-macd-gt-signal, .screener-table td.screener-col-macd-gt-signal {{ width: 6.8%; }}
        .screener-table th.screener-col-ppo-cross, .screener-table td.screener-col-ppo-cross,
        .screener-table th.screener-col-macd-cross, .screener-table td.screener-col-macd-cross {{ width: 6.4%; }}
        .screener-table th.screener-col-triple-ma, .screener-table td.screener-col-triple-ma {{ width: 6.2%; }}
        .screener-table th.screener-col-comment, .screener-table td.screener-col-comment {{ width: 6.8%; }}
        .screener-table th.screener-col-t0-t3-change, .screener-table td.screener-col-t0-t3-change {{ width: 7.5%; padding-left: 4px; padding-right: 4px; }}
        .screener-table th.screener-col-t0-t3-change .th-label {{ white-space: normal; }}
        .screener-table td[class*="screener-change-"], .screener-table td[class*="screener-drop-"], .screener-table td[class*="screener-rvol-"], .screener-table td[class*="screener-position-"], .screener-table td[class*="screener-comment-"] {{ font-weight: 700; }}
        .screener-table td.screener-change-pos-1 {{ background: #dcfce7; color: #166534; }}
        .screener-table td.screener-change-pos-2 {{ background: #86efac; color: #14532d; }}
        .screener-table td.screener-change-pos-3 {{ background: #22c55e; color: #052e16; }}
        .screener-table td.screener-change-pos-4 {{ background: #16a34a; color: #ffffff; }}
        .screener-table td.screener-change-pos-5 {{ background: #15803d; color: #ffffff; }}
        .screener-table td.screener-change-neg-1 {{ background: #fee2e2; color: #991b1b; }}
        .screener-table td.screener-change-neg-2 {{ background: #fecaca; color: #7f1d1d; }}
        .screener-table td.screener-change-neg-3 {{ background: #fca5a5; color: #7f1d1d; }}
        .screener-table td.screener-change-neg-4 {{ background: #ef4444; color: #ffffff; }}
        .screener-table td.screener-change-neg-5 {{ background: #b91c1c; color: #ffffff; }}
        .screener-table td.screener-drop-1 {{ background: #fee2e2; color: #991b1b; }}
        .screener-table td.screener-drop-2 {{ background: #fecaca; color: #7f1d1d; }}
        .screener-table td.screener-drop-3 {{ background: #fca5a5; color: #7f1d1d; }}
        .screener-table td.screener-drop-4 {{ background: #ef4444; color: #ffffff; }}
        .screener-table td.screener-drop-5 {{ background: #b91c1c; color: #ffffff; }}
        .screener-table td.screener-rvol-1 {{ background: #dbeafe; color: #1e3a5f; }}
        .screener-table td.screener-rvol-2 {{ background: #bfdbfe; color: #1e3a5f; }}
        .screener-table td.screener-rvol-3 {{ background: #60a5fa; color: #0f172a; }}
        .screener-table td.screener-rvol-4 {{ background: #2563eb; color: #ffffff; }}
        .screener-table td.screener-rvol-5 {{ background: #1e40af; color: #ffffff; }}
        .screener-table td.screener-position-pos-1 {{ background: #dcfce7; color: #166534; }}
        .screener-table td.screener-position-pos-2 {{ background: #86efac; color: #14532d; }}
        .screener-table td.screener-position-pos-3 {{ background: #22c55e; color: #052e16; }}
        .screener-table td.screener-position-pos-4 {{ background: #16a34a; color: #ffffff; }}
        .screener-table td.screener-position-pos-5 {{ background: #15803d; color: #ffffff; }}
        .screener-table td.screener-position-neg-1 {{ background: #fee2e2; color: #991b1b; }}
        .screener-table td.screener-position-neg-2 {{ background: #fecaca; color: #7f1d1d; }}
        .screener-table td.screener-position-neg-3 {{ background: #fca5a5; color: #7f1d1d; }}
        .screener-table td.screener-position-neg-4 {{ background: #ef4444; color: #ffffff; }}
        .screener-table td.screener-position-neg-5 {{ background: #b91c1c; color: #ffffff; }}
        .screener-table td.screener-bool-yes {{ color: #16a34a; font-weight: 800; }}
        .screener-table td.screener-bool-no {{ color: #dc2626; font-weight: 800; }}
        .screener-table td.screener-comment-below {{ background: #e5e7eb; color: #4b5563; }}
        .screener-table td.screener-comment-5d {{ background: #d9f99d; color: #365314; }}
        .screener-table td.screener-comment-10d {{ background: #bef264; color: #365314; }}
        .screener-table td.screener-comment-1m {{ background: #86efac; color: #14532d; }}
        .screener-table td.screener-comment-2m {{ background: #34d399; color: #064e3b; }}
        .screener-table td.screener-comment-3m {{ background: #2dd4bf; color: #134e4a; }}
        .screener-table td.screener-score-high {{ color: #15803d; font-weight: 800; }}
        .screener-table td.screener-score-mid {{ color: #22262f; font-weight: 700; }}
        .screener-table td.screener-score-low {{ color: #b91c1c; font-weight: 700; }}
        .screener-table td.screener-comment-6m {{ background: #059669; color: #ffffff; }}
        .screener-table td.screener-comment-1y {{ background: #f3c736; color: #422006; }}
        .screener-table td.screener-momentum-positive, .screener-table td.screener-rsi-pos-1 {{ color: #16a34a; font-weight: 700; }}
        .screener-table td.screener-momentum-negative, .screener-table td.screener-rsi-neg-1 {{ color: #dc2626; font-weight: 700; }}
        .screener-table td.screener-rsi-pos-2 {{ color: #15803d; font-weight: 800; }}
        .screener-table td.screener-rsi-pos-3 {{ color: #166534; font-weight: 900; }}
        .screener-table td.screener-rsi-neg-2 {{ color: #b91c1c; font-weight: 800; }}
        .screener-table td.screener-rsi-neg-3 {{ color: #7f1d1d; font-weight: 900; }}
        .screener-table td.screener-comment-ath {{ color: #19803d; font-weight: 600; }}
        .screener-table tr.selected td:not([class*="screener-change-"]):not([class*="screener-drop-"]):not([class*="screener-rvol-"]):not([class*="screener-position-"]):not([class*="screener-comment-"]) {{ background: #ffffff; }}
        .screener-table tr.selected td[class*="screener-change-"], .screener-table tr.selected td[class*="screener-drop-"], .screener-table tr.selected td[class*="screener-rvol-"], .screener-table tr.selected td[class*="screener-position-"], .screener-table tr.selected td[class*="screener-comment-"] {{ box-shadow: inset 0 0 0 999px rgba(255,255,255,0.08); }}
        .report-notes {{ border-top: 1px solid #dedfe5; padding: 13px 18px 16px; background: #f8fafc; }}
        .report-notes-head {{ display: flex; align-items: baseline; justify-content: space-between; gap: 12px; margin-bottom: 8px; }}
        .report-notes h3 {{ margin: 0; color: #22262f; font-size: 13px; font-weight: 800; }}
        .report-notes-status {{ color: #676f85; font-size: 11px; font-weight: 700; }}
        .report-notes textarea {{ display: block; width: 100%; min-height: 92px; box-sizing: border-box; resize: vertical; border: 1px solid #c3c6d0; border-radius: 10px; padding: 10px 12px; background: #ffffff; color: #22262f; font: inherit; font-size: 12.5px; line-height: 1.45; }}
        .report-notes textarea:focus {{ border-color: #4c5263; box-shadow: 0 0 0 3px rgba(76,82,99,0.16); outline: none; }}
        .ticker-chart-link {{ border: none; background: transparent; color: #306dca; cursor: pointer; min-width: auto; padding: 0; font: inherit; font-weight: 600; text-decoration: none; }}
        .ticker-chart-link:hover {{ color: #2f91ef; text-decoration: underline; }}
        .history-panel {{ max-width: 1380px; margin: 16px auto 26px; }}
        .history-title {{ display: flex; align-items: end; justify-content: space-between; gap: 12px; padding: 14px 18px; border-radius: 14px 14px 0 0; background: linear-gradient(135deg, #353945, #4c5263); color: #ffffff; }}
        .history-title h2 {{ margin: 0; font-size: 15px; }}
        .history-title p {{ margin: 0; color: rgba(255,255,255,0.76); font-size: 12px; font-weight: 600; }}
        .history-grid {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(310px, 1fr)); gap: 12px; padding: 14px; background: #ffffff; border: 1px solid #dedfe5; border-top: 0; border-radius: 0 0 14px 14px; box-shadow: 0 14px 34px rgba(20,22,29,0.08); }}
        .history-card {{ border: 1px solid #dedfe5; border-radius: 14px; background: #ffffff; padding: 13px 14px; box-shadow: 0 6px 16px rgba(20,22,29,0.06); }}
        .history-card-head {{ display: flex; align-items: center; justify-content: space-between; gap: 10px; }}
        .history-ticker {{ color: #306dca; font-size: 14px; }}
        .history-change {{ padding: 4px 10px; border-radius: 999px; color: #ffffff; font-size: 12px; font-weight: 700; font-variant-numeric: tabular-nums; }}
        .history-change.up {{ background: #00a449; }}
        .history-change.down {{ background: #d91e2b; }}
        .history-date {{ margin-top: 7px; color: #676f85; font-size: 11px; font-weight: 600; }}
        .history-range {{ position: relative; height: 12px; margin: 16px 2px 12px; border-radius: 999px; background: linear-gradient(90deg, #fbb4b4, #fdf2df 50%, #beeac1); box-shadow: inset 0 1px 2px rgba(20,22,29,0.18); }}
        .history-marker {{ position: absolute; top: 50%; width: 10px; height: 10px; transform: translate(-50%, -50%); border-radius: 50%; border: 2px solid #ffffff; box-shadow: 0 1px 4px rgba(20,22,29,0.34); }}
        .history-marker.entry {{ background: #4c5263; }}
        .history-marker.last {{ background: #f3c736; }}
        .history-values {{ display: grid; grid-template-columns: repeat(4, 1fr); gap: 6px; }}
        .history-values span {{ display: block; padding: 7px 6px; border-radius: 10px; background: #f3f3f5; color: #22262f; font-size: 11px; font-weight: 700; text-align: center; font-variant-numeric: tabular-nums; }}
        .history-values em {{ display: block; margin-bottom: 2px; color: #676f85; font-size: 9px; font-style: normal; text-transform: uppercase; }}
        .history-footer {{ display: flex; justify-content: space-between; gap: 8px; margin-top: 10px; color: #4c5263; font-size: 11px; font-weight: 600; }}
        .history-empty {{ max-width: 720px; margin: 24px auto; padding: 18px; border: 1px solid #dedfe5; border-radius: 14px; background: #ffffff; color: #676f85; font-size: 13px; font-weight: 600; text-align: center; }}
        .chart-modal {{ position: fixed; inset: 0; display: none; align-items: center; justify-content: center; padding: 28px; background: rgba(20,22,29,0.62); z-index: 20; }}
        .chart-modal.open {{ display: flex; }}
        .chart-modal-card {{ width: min(1180px, 96vw); max-height: 92vh; overflow: auto; border-radius: 16px; background: #ffffff; box-shadow: 0 24px 70px rgba(0,0,0,0.35); border: 1px solid #c3c6d0; }}
        .chart-modal-header {{ display: flex; align-items: center; justify-content: space-between; gap: 12px; padding: 12px 16px; background: #353945; color: #ffffff; font-weight: 700; }}
        .chart-modal-close {{ border: none; border-radius: 999px; background: rgba(255,255,255,0.12); color: #ffffff; min-width: auto; width: 32px; height: 32px; padding: 0; cursor: pointer; font-size: 18px; font-weight: 700; }}
        .chart-modal-body {{ padding: 14px; text-align: center; }}
        .chart-modal-body img {{ max-width: 100%; height: auto; border: 1px solid #dedfe5; border-radius: 10px; background: #ffffff; }}
        @media (max-width: 980px) {{
            .header {{ grid-template-columns: 1fr; gap: 12px; padding: 12px 16px; }}
            .tabs, .live-clock {{ justify-self: start; }}
            .live-clock {{ text-align: left; }}
            .live-clock span {{ text-align: left; }}
            button {{ font-size: 14px; padding: 10px 14px; }}
            .screener-summary {{ display: block; }}
            .selected-ticker-list {{ max-width: none; margin-top: 12px; }}
            .screener-filters {{ grid-template-columns: repeat(2, minmax(120px, 1fr)); }}
        }}
    </style>
</head>
<body>
{DUO_THEME_BOOT_SCRIPT}
    <div class="header">
        <div class="brand">
            {header_logo_html}
            <span class="brand-text">
                <strong class="report-title">Inswing ScreenSim</strong>
                <span class="report-subtitle">Screening and simulation review</span>
            </span>
        </div>
        <div class="tabs">
            <button type="button" onclick="goToAppRoute('/?reset=screener')">Screener</button>
            <button class="active" type="button" data-main-tab="portfolio" onclick="showPortfolioSubTab(currentPortfolioSubTabId, document.querySelector('.portfolio-subtabs button.active') || document.querySelector('.portfolio-subtabs button'))">Portfolio</button>
            <button type="button" onclick="showMainReportTab('history-30d', this)">30D Follow-Through</button>
            <button type="button" onclick="goToAppRoute('/?panel=savedReports')">Saved Reports</button>
        </div>
        <span class="header-right">
            <span class="live-clock" id="liveClockDate">--<span id="liveClockTime">--</span></span>
{DUO_THEME_TOGGLE_HTML}
        </span>
    </div>
    <div class="portfolio-subtabs-wrap" id="portfolioSubtabs">
        <div class="portfolio-subtabs" aria-label="Portfolio report views">
            <button class="active" type="button" onclick="showPortfolioSubTab('screened', this)">Selected Stocks</button>
            <button type="button" onclick="showPortfolioSubTab('portfolio', this)">Account View</button>
            <button type="button" onclick="showPortfolioSubTab('all-stocks', this)">All Stocks</button>
            <button type="button" onclick="showPortfolioSubTab('individual', this)">Individual Stocks</button>
        </div>
    </div>
{live_refresh_html}
{selected_panel_html}
    <section id="portfolio" class="panel">
        <div class="image-wrap"><img class="fit-image" src="{portfolio_image}" alt="Portfolio performance"></div>
    </section>
    <section id="all-stocks" class="panel">
        <div class="image-wrap">
            <div class="all-stocks-stage">
                <button class="replay-button" id="allStocksReplayButton" type="button" onclick="toggleAllStocksReplay()">&#9658; Replay</button>
                <img class="fit-image" id="allStocksStaticImage" src="{all_stocks_image}" alt="All stocks performance">
                <div class="replay-wrap" id="allStocksReplayWrap"><svg class="replay-chart" id="allStocksReplayChart" role="img" aria-label="All stocks replay chart"></svg></div>
            </div>
            <span class="replay-status" id="allStocksReplayStatus">10-minute bars, 1 bar every 1/3 sec</span>
        </div>
    </section>
    <section id="individual" class="panel">
        <div class="stock-picker" id="stockPicker">
{individual_buttons_html}
        </div>
        <div class="single-stock-wrap">
            <img class="single-stock-image" id="selectedStockChart" src="{first_individual_image}" alt="Selected stock chart">
        </div>
    </section>
{history_panel_html}
    <div class="chart-modal" id="tickerChartModal" aria-hidden="true">
        <div class="chart-modal-card" role="dialog" aria-modal="true" aria-labelledby="tickerChartTitle">
            <div class="chart-modal-header">
                <span id="tickerChartTitle">Daily chart</span>
                <button class="chart-modal-close" type="button" id="tickerChartClose" aria-label="Close chart">&times;</button>
            </div>
            <div class="chart-modal-body">
                <img id="tickerChartImage" alt="6 month daily chart with PPO">
            </div>
        </div>
    </div>
    <script>
        const allStocksReplayData = {replay_payload};
        const individualCharts = {individual_charts_payload};
        const liveSnapshotPayload = {live_snapshot_payload};
        const reportNoteStorageKey = {report_note_storage_key};
        const reportNotePath = {report_note_rel_path};
        const portfolioSubTabIds = new Set(['screened', 'portfolio', 'all-stocks', 'individual']);
        let currentPortfolioSubTabId = 'screened';
        const allStocksReplayState = {{
            frameIndex: 0,
            playing: false,
            timer: null,
            initialized: false
        }};

        function goToAppRoute(path) {{
            const route = path || '/';
            if (window.location.protocol === 'file:') {{
                window.location.href = `http://127.0.0.1:8765${{route}}`;
                return;
            }}
            window.location.href = route;
        }}
        function setPortfolioSubtabsVisible(visible) {{
            const subtabs = document.getElementById('portfolioSubtabs');
            if (subtabs) {{
                subtabs.classList.toggle('hidden', !visible);
            }}
        }}
        function activatePanel(id) {{
            document.querySelectorAll('.panel').forEach(panel => panel.classList.remove('active'));
            const panel = document.getElementById(id);
            if (panel) {{
                panel.classList.add('active');
            }}
        }}
        function showPortfolioSubTab(id, button) {{
            if (!portfolioSubTabIds.has(id)) {{
                id = 'screened';
            }}
            currentPortfolioSubTabId = id;
            activatePanel(id);
            document.querySelectorAll('.tabs button').forEach(tab => tab.classList.remove('active'));
            document.querySelectorAll('.portfolio-subtabs button').forEach(tab => tab.classList.remove('active'));
            const portfolioTab = document.querySelector('.tabs button[data-main-tab="portfolio"]');
            if (portfolioTab) {{
                portfolioTab.classList.add('active');
            }}
            if (button) {{
                button.classList.add('active');
            }}
            setPortfolioSubtabsVisible(true);
            window.scrollTo(0, 0);
        }}
        function showMainReportTab(id, button) {{
            activatePanel(id);
            document.querySelectorAll('.tabs button').forEach(tab => tab.classList.remove('active'));
            document.querySelectorAll('.portfolio-subtabs button').forEach(tab => tab.classList.remove('active'));
            if (button) {{
                button.classList.add('active');
            }}
            setPortfolioSubtabsVisible(false);
            window.scrollTo(0, 0);
        }}
        function showStockChart(index, button) {{
            const chart = individualCharts[index];
            if (!chart) {{
                return;
            }}
            const image = document.getElementById('selectedStockChart');
            image.src = chart.src;
            image.alt = `${{chart.ticker}} chart`;
            document.querySelectorAll('.stock-picker button').forEach(tab => tab.classList.remove('active'));
            button.classList.add('active');
            window.scrollTo(0, 0);
        }}
        function updateLiveClock() {{
            const now = new Date();
            document.getElementById('liveClockDate').firstChild.nodeValue = now.toLocaleDateString(undefined, {{ weekday: 'short', month: 'short', day: '2-digit', year: 'numeric' }});
            document.getElementById('liveClockTime').textContent = now.toLocaleTimeString(undefined, {{ hour: '2-digit', minute: '2-digit', second: '2-digit' }});
        }}

        function screenSimChartTickers() {{
            return individualCharts.map(chart => chart.ticker).filter(Boolean);
        }}

        function screenSimChartPopoutUrl(ticker, anchorDate = '', forward = false, tickersOverride = null) {{
            const chartBaseUrl = window.location.protocol === 'file:' ? 'http://127.0.0.1:8765/chart-popout' : '/chart-popout';
            const params = new URLSearchParams();
            params.set('ticker', ticker);
            if (anchorDate) {{
                params.set('anchor', anchorDate);
            }}
            const tickers = Array.isArray(tickersOverride) ? tickersOverride : screenSimChartTickers();
            if (tickers.length) {{
                params.set('tickers', tickers.join(','));
            }}
            if (forward) {{
                params.set('forward', '1');
            }}
            return `${{chartBaseUrl}}?${{params.toString()}}`;
        }}

        function openTickerChart(ticker, anchorDate = '') {{
            window.open(screenSimChartPopoutUrl(ticker, anchorDate), '_blank', 'width=1800,height=1060,menubar=no,toolbar=no,location=no,status=no,resizable=yes,scrollbars=yes');
        }}

        function closeTickerChart() {{
            const modal = document.getElementById('tickerChartModal');
            const image = document.getElementById('tickerChartImage');
            modal.classList.remove('open');
            modal.setAttribute('aria-hidden', 'true');
            image.removeAttribute('src');
        }}

        function compareSelectedStockSortValues(aValue, bValue, direction) {{
            const aEmpty = aValue === null || aValue === undefined || String(aValue).trim() === '';
            const bEmpty = bValue === null || bValue === undefined || String(bValue).trim() === '';
            if (aEmpty || bEmpty) {{
                if (aEmpty && bEmpty) {{
                    return 0;
                }}
                return aEmpty ? 1 : -1;
            }}
            const aNumber = Number(aValue);
            const bNumber = Number(bValue);
            if (Number.isFinite(aNumber) && Number.isFinite(bNumber)) {{
                return (aNumber - bNumber) * direction;
            }}
            return String(aValue).localeCompare(String(bValue), undefined, {{ numeric: true, sensitivity: 'base' }}) * direction;
        }}

        function sortSelectedStocksTable(header) {{
            const table = header.closest('table');
            const tbody = table ? table.querySelector('tbody') : null;
            if (!tbody) {{
                return;
            }}
            const headers = [...table.querySelectorAll('th[data-sort-key]')];
            const columnIndex = headers.indexOf(header);
            if (columnIndex < 0) {{
                return;
            }}
            const nextDirection = header.classList.contains('sort-asc') ? 'desc' : 'asc';
            headers.forEach(th => {{
                th.classList.remove('sort-asc', 'sort-desc');
                th.setAttribute('aria-sort', 'none');
            }});
            header.classList.add(nextDirection === 'asc' ? 'sort-asc' : 'sort-desc');
            header.setAttribute('aria-sort', nextDirection === 'asc' ? 'ascending' : 'descending');
            const direction = nextDirection === 'asc' ? 1 : -1;
            const rows = [...tbody.querySelectorAll('tr')];
            rows.sort((a, b) => {{
                const aValue = a.children[columnIndex]?.getAttribute('data-sort-value') ?? a.children[columnIndex]?.textContent ?? '';
                const bValue = b.children[columnIndex]?.getAttribute('data-sort-value') ?? b.children[columnIndex]?.textContent ?? '';
                const result = compareSelectedStockSortValues(aValue, bValue, direction);
                if (result !== 0) {{
                    return result;
                }}
                return String(a.children[0]?.textContent || '').localeCompare(String(b.children[0]?.textContent || ''), undefined, {{ numeric: true, sensitivity: 'base' }});
            }});
            rows.forEach(row => tbody.appendChild(row));
        }}

        function initSelectedStocksNotes() {{
            const note = document.getElementById('selectedStocksNote');
            const status = document.getElementById('selectedStocksNoteStatus');
            if (!note || !status) {{
                return;
            }}
            const fallbackNote = window.localStorage ? (localStorage.getItem(reportNoteStorageKey) || '') : '';
            note.value = fallbackNote;
            const canUseServerNotes = Boolean(reportNotePath) && window.location.protocol !== 'file:';
            if (canUseServerNotes) {{
                fetch(`/report-note?path=${{encodeURIComponent(reportNotePath)}}`, {{ cache: 'no-store' }})
                    .then(resp => resp.ok ? resp.json() : Promise.reject(new Error('Unable to load note')))
                    .then(data => {{
                        const serverNote = String(data.note || '');
                        note.value = serverNote || fallbackNote;
                        status.textContent = 'Saved to report folder';
                        if (!serverNote && fallbackNote) {{
                            return fetch('/report-note', {{
                                method: 'POST',
                                headers: {{ 'Content-Type': 'application/json' }},
                                body: JSON.stringify({{ path: reportNotePath, note: fallbackNote }})
                            }});
                        }}
                    }})
                    .catch(() => {{
                        status.textContent = 'Autosaved in this browser';
                    }});
            }}
            let noteSaveTimer = null;
            note.addEventListener('input', () => {{
                status.textContent = 'Saving...';
                if (noteSaveTimer) {{
                    clearTimeout(noteSaveTimer);
                }}
                noteSaveTimer = setTimeout(() => {{
                    if (canUseServerNotes) {{
                        fetch('/report-note', {{
                            method: 'POST',
                            headers: {{ 'Content-Type': 'application/json' }},
                            body: JSON.stringify({{ path: reportNotePath, note: note.value }})
                        }})
                            .then(resp => resp.ok ? resp.json() : Promise.reject(new Error('Unable to save note')))
                            .then(() => {{
                                if (window.localStorage) {{
                                    localStorage.removeItem(reportNoteStorageKey);
                                }}
                                status.textContent = 'Saved to report folder';
                            }})
                            .catch(() => {{
                                if (window.localStorage) {{
                                    localStorage.setItem(reportNoteStorageKey, note.value);
                                }}
                                status.textContent = 'Saved in this browser only';
                            }});
                        return;
                    }}
                    if (window.localStorage) {{
                        localStorage.setItem(reportNoteStorageKey, note.value);
                    }}
                    status.textContent = 'Saved in this browser only';
                }}, 250);
            }});
        }}

        function startLiveRefreshCountdown() {{
            const countdown = document.getElementById('liveRefreshCountdown');
            const banner = document.getElementById('liveRefreshBanner');
            const snapshot = document.getElementById('liveRefreshSnapshot');
            if (!countdown || !banner || !snapshot) {{
                return;
            }}
            function secondsUntilNextBarCheck() {{
                const now = new Date();
                return Math.max(1, 63 - now.getSeconds());
            }}
            let remaining = secondsUntilNextBarCheck();
            countdown.textContent = String(remaining);
            let refreshing = false;
            function renderSnapshot(data) {{
                if (!data.active) {{
                    banner.classList.remove('active');
                    return false;
                }}
                banner.classList.add('active');
                const pnl = Number(data.pnl_pct || 0);
                const sign = pnl >= 0 ? '+' : '';
                banner.firstChild.nodeValue = `Live ${{data.session}} 1-min close: next update in `;
                snapshot.textContent = ` · ${{data.timestamp || '--:--'}} close · Portfolio ${{sign}}${{pnl.toFixed(2)}}%`;
                return true;
            }}
            function requestSnapshot() {{
                refreshing = true;
                const liveSnapshotUrl = window.location.protocol === 'file:' ? 'http://127.0.0.1:8765/live-snapshot' : '/live-snapshot';
                fetch(liveSnapshotUrl, {{
                    method: 'POST',
                    headers: {{ 'Content-Type': 'application/json' }},
                    body: JSON.stringify(liveSnapshotPayload),
                    cache: 'no-store'
                }})
                    .then(response => {{
                        if (!response.ok) {{
                            throw new Error(`Snapshot failed: ${{response.status}}`);
                        }}
                        return response.json();
                    }})
                    .then(data => {{
                        const isActive = renderSnapshot(data);
                        remaining = secondsUntilNextBarCheck();
                        countdown.textContent = String(remaining);
                        refreshing = false;
                    }})
                    .catch(() => {{
                        banner.classList.remove('active');
                        refreshing = false;
                    }});
            }}
            requestSnapshot();
            setInterval(() => {{
                if (refreshing) {{
                    return;
                }}
                remaining -= 1;
                if (remaining > 0) {{
                    countdown.textContent = String(remaining);
                    return;
                }}
                requestSnapshot();
            }}, 1000);
        }}

        function svgEl(name, attrs = {{}}) {{
            const el = document.createElementNS('http://www.w3.org/2000/svg', name);
            Object.entries(attrs).forEach(([key, value]) => el.setAttribute(key, value));
            return el;
        }}

        function darkenHexColor(hexColor, amount = 0.20) {{
            const raw = hexColor.replace('#', '');
            const red = Math.round(parseInt(raw.slice(0, 2), 16) * (1 - amount));
            const green = Math.round(parseInt(raw.slice(2, 4), 16) * (1 - amount));
            const blue = Math.round(parseInt(raw.slice(4, 6), 16) * (1 - amount));
            return `#${{red.toString(16).padStart(2, '0')}}${{green.toString(16).padStart(2, '0')}}${{blue.toString(16).padStart(2, '0')}}`;
        }}

        function allStocksReplayScales(width, height) {{
            const margin = {{ left: 90, right: 330, top: 72, bottom: 108 }};
            const plotWidth = Math.max(width - margin.left - margin.right, 1);
            const plotHeight = Math.max(height - margin.top - margin.bottom, 1);
            const xSpan = Math.max(allStocksReplayData.xMax - allStocksReplayData.xMin, 1);
            const ySpan = Math.max(allStocksReplayData.yMax - allStocksReplayData.yMin, 1);
            return {{
                margin,
                plotWidth,
                plotHeight,
                x: value => margin.left + ((value - allStocksReplayData.xMin) / xSpan) * plotWidth,
                y: value => margin.top + plotHeight - ((value - allStocksReplayData.yMin) / ySpan) * plotHeight
            }};
        }}

        function drawAllStocksReplayBase(svg, width, height, scales, currentMetrics) {{
            svg.innerHTML = '';
            svg.setAttribute('viewBox', `0 0 ${{width}} ${{height}}`);
            svg.appendChild(svgEl('rect', {{ x: 0, y: 0, width, height, fill: '#ffffff', rx: 8 }}));
            svg.appendChild(svgEl('rect', {{ x: 0, y: scales.margin.top, width: scales.margin.left, height: scales.plotHeight, fill: '#ffffff' }}));
            svg.appendChild(svgEl('rect', {{ x: scales.margin.left, y: height - scales.margin.bottom, width: scales.plotWidth, height: scales.margin.bottom, fill: '#ffffff' }}));

            allStocksReplayData.sessions.forEach((session, idx) => {{
                const startX = scales.x(session.start);
                const endX = scales.x(session.end);
                svg.appendChild(svgEl('rect', {{ x: startX, y: 28, width: Math.max(endX - startX, 1), height: 28, fill: '#353945' }}));
                const text = svgEl('text', {{ x: (startX + endX) / 2, y: 47, fill: '#ffffff', 'font-size': idx === 0 ? 11 : 14, 'font-weight': 800, 'text-anchor': 'middle' }});
                text.textContent = session.label;
                svg.appendChild(text);
                svg.appendChild(svgEl('text', {{ x: startX + 4, y: 74, fill: '#353945', 'font-size': 16, 'font-weight': 800 }})).textContent = '☼';
                svg.appendChild(svgEl('circle', {{ cx: endX - 10, cy: 70, r: 4.4, fill: '#ffffff', stroke: '#353945', 'stroke-width': 2 }}));
                if (idx > 0) {{
                    svg.appendChild(svgEl('line', {{ x1: startX, x2: startX, y1: 28, y2: height - scales.margin.bottom, stroke: '#a3a8b9', 'stroke-width': 2.4, opacity: 0.95 }}));
                }}
            }});

            const yStep = 2;
            const firstTick = Math.ceil(allStocksReplayData.yMin / yStep) * yStep;
            for (let yValue = firstTick; yValue <= allStocksReplayData.yMax; yValue += yStep) {{
                const y = scales.y(yValue);
                svg.appendChild(svgEl('line', {{ x1: scales.margin.left, x2: width - scales.margin.right, y1: y, y2: y, stroke: '#dedfe5', 'stroke-width': 1, 'stroke-dasharray': '4 4' }}));
                const label = svgEl('text', {{ x: scales.margin.left - 12, y: y + 4, fill: '#353945', 'font-size': 14, 'font-weight': 700, 'text-anchor': 'end' }});
                label.textContent = `${{yValue.toFixed(0)}}%`;
                svg.appendChild(label);
            }}

            const zeroY = scales.y(0);
            svg.appendChild(svgEl('line', {{ x1: scales.margin.left, x2: width - scales.margin.right, y1: zeroY, y2: zeroY, stroke: '#868ea5', 'stroke-width': 1.2, 'stroke-dasharray': '5 4' }}));
            svg.appendChild(svgEl('rect', {{ x: scales.margin.left, y: scales.margin.top, width: scales.plotWidth, height: scales.plotHeight, fill: 'none', stroke: '#dedfe5' }}));

            allStocksReplayData.sessions.forEach(session => {{
                const labelTimes = ['09:30', '10:00', '10:30', '11:00', '11:30', '12:00', '12:30', '13:00', '13:30', '14:00', '14:30', '15:00', '15:30', '16:00'];
                const points = allStocksReplayData.series.length ? allStocksReplayData.series[0].points : [];
                labelTimes.forEach(labelTime => {{
                    const point = points.find(item => item.time && item.time.endsWith(labelTime) && item.x >= session.start && item.x <= session.end);
                    if (!point) {{
                        return;
                    }}
                    const tickX = scales.x(point.x);
                    const tick = svgEl('text', {{ x: tickX, y: height - 28, fill: '#353945', 'font-size': 11, 'font-weight': 700, 'text-anchor': 'end', transform: `rotate(-45 ${{tickX}} ${{height - 28}})` }});
                    tick.textContent = labelTime;
                    svg.appendChild(tick);
                }});
            }});

            const axisLabelX = 30;
            const axisLabelY = scales.margin.top + scales.plotHeight / 2;
            svg.appendChild(svgEl('rect', {{ x: axisLabelX - 10, y: axisLabelY - 92, width: 23, height: 184, rx: 4, fill: '#ffffff', stroke: '#353945', 'stroke-width': 1 }}));
            const axisText = svgEl('text', {{ x: axisLabelX + 6, y: axisLabelY, fill: '#353945', 'font-size': 13, 'font-weight': 800, 'text-anchor': 'middle', transform: `rotate(-90 ${{axisLabelX + 6}} ${{axisLabelY}})` }});
            axisText.textContent = 'ALL STOCKS PLOTTING (%)';
            svg.appendChild(axisText);

            const tableX = width - 275;
            const tableY = 62;
            const tableW = 220;
            const rowGap = 25;
            const metrics = currentMetrics
                .filter(metric => !metric.benchmark)
                .sort((a, b) => b.value - a.value)
                .slice(0, 22);
            const tableH = Math.max(118, 58 + metrics.length * rowGap + 18);
            const tRange = allStocksReplayData.sessions.length ? `T0 - T${{allStocksReplayData.sessions.length - 1}}` : 'T0';
            const header = svgEl('text', {{ x: tableX + tableW / 2, y: 34, fill: '#22262f', 'font-size': 14, 'font-weight': 800, 'text-anchor': 'middle' }});
            header.textContent = `Stock Performance (${{tRange}})`;
            svg.appendChild(header);
            svg.appendChild(svgEl('rect', {{ x: tableX, y: tableY, width: tableW, height: tableH, rx: 4, fill: '#ffffff', stroke: '#dedfe5', 'stroke-width': 1.4 }}));
            const tableTitle = svgEl('text', {{ x: tableX + 46, y: tableY + 32, fill: '#22262f', 'font-size': 13, 'font-weight': 800, 'text-anchor': 'middle' }});
            tableTitle.textContent = 'Ticker';
            svg.appendChild(tableTitle);
            const valueTitle = svgEl('text', {{ x: tableX + tableW - 38, y: tableY + 32, fill: '#22262f', 'font-size': 13, 'font-weight': 800, 'text-anchor': 'middle' }});
            valueTitle.textContent = 'P&L (%)';
            svg.appendChild(valueTitle);

            metrics.forEach((metric, idx) => {{
                const rowY = tableY + 58 + idx * rowGap;
                const valueColor = metric.value >= 0 ? '#00a449' : '#d91e2b';
                svg.appendChild(svgEl('line', {{ x1: tableX + 10, x2: tableX + tableW - 10, y1: rowY + 9, y2: rowY + 9, stroke: '#dedfe5', 'stroke-width': 0.9 }}));
                const tickerText = svgEl('text', {{ x: tableX + 34, y: rowY, fill: '#22262f', 'font-size': 13, 'font-weight': 700, 'text-anchor': 'start' }});
                tickerText.textContent = metric.ticker;
                svg.appendChild(tickerText);
                const valueText = svgEl('text', {{ x: tableX + tableW - 30, y: rowY, fill: valueColor, 'font-size': 15, 'font-weight': 800, 'text-anchor': 'end' }});
                valueText.textContent = `${{metric.value >= 0 ? '+' : ''}}${{metric.value.toFixed(2)}}%`;
                svg.appendChild(valueText);
            }});

            const benchmarkMetrics = currentMetrics
                .filter(metric => metric.benchmark)
                .sort((a, b) => ['SPY', 'QQQ', 'IWM'].indexOf(a.ticker) - ['SPY', 'QQQ', 'IWM'].indexOf(b.ticker));
            if (benchmarkMetrics.length) {{
                const benchY = tableY + tableH + 50;
                const benchH = 160;
                svg.appendChild(svgEl('rect', {{ x: tableX, y: benchY, width: tableW, height: benchH, rx: 4, fill: '#ffffff', stroke: '#dedfe5', 'stroke-width': 1.4 }}));
                const benchTitle = svgEl('text', {{ x: tableX + tableW / 2, y: benchY + 24, fill: '#22262f', 'font-size': 14, 'font-weight': 800, 'text-anchor': 'middle' }});
                benchTitle.textContent = 'Benchmark Summary';
                svg.appendChild(benchTitle);
                const benchSubtitle = svgEl('text', {{ x: tableX + tableW / 2, y: benchY + 45, fill: '#676f85', 'font-size': 11.5, 'font-weight': 800, 'text-anchor': 'middle' }});
                benchSubtitle.textContent = `Performance ${{tRange}}`;
                svg.appendChild(benchSubtitle);
                benchmarkMetrics.forEach((metric, idx) => {{
                    const rowY = benchY + 74 + idx * 34;
                    const valueColor = metric.value >= 0 ? '#22262f' : metric.color;
                    const nameText = svgEl('text', {{ x: tableX + 34, y: rowY, fill: metric.color, 'font-size': 14, 'font-weight': 800, 'text-anchor': 'start' }});
                    nameText.textContent = metric.ticker;
                    svg.appendChild(nameText);
                    const valueText = svgEl('text', {{ x: tableX + tableW - 30, y: rowY, fill: valueColor, 'font-size': 14, 'font-weight': 800, 'text-anchor': 'end' }});
                    valueText.textContent = `${{metric.value >= 0 ? '+' : ''}}${{metric.value.toFixed(2)}}%`;
                    svg.appendChild(valueText);
                    const lineText = svgEl('text', {{ x: tableX + 34, y: rowY + 15, fill: metric.color, 'font-size': 10.5, 'font-weight': 400, 'text-anchor': 'start' }});
                    lineText.textContent = `${{metric.ticker}} Line`;
                    svg.appendChild(lineText);
                    svg.appendChild(svgEl('line', {{ x1: tableX + tableW - 66, x2: tableX + tableW - 30, y1: rowY + 14, y2: rowY + 14, stroke: metric.color, 'stroke-width': 1.1, 'stroke-dasharray': '7 5' }}));
                }});
            }}
        }}

        function renderAllStocksReplayFrame() {{
            const svg = document.getElementById('allStocksReplayChart');
            if (!svg || !allStocksReplayData.series.length || !allStocksReplayData.frames.length) {{
                return;
            }}
            const width = 2000;
            const height = 900;
            const scales = allStocksReplayScales(width, height);
            const frameX = allStocksReplayData.frames[Math.min(allStocksReplayState.frameIndex, allStocksReplayData.frames.length - 1)];
            const currentMetrics = allStocksReplayData.series
                .map(series => {{
                    const visiblePoints = series.points.filter(point => point.x <= frameX);
                    if (!visiblePoints.length) {{
                        return null;
                    }}
                    return {{ ticker: series.ticker, color: series.color, value: visiblePoints[visiblePoints.length - 1].y, benchmark: series.benchmark }};
                }})
                .filter(metric => metric !== null);
            drawAllStocksReplayBase(svg, width, height, scales, currentMetrics);

            const status = document.getElementById('allStocksReplayStatus');
            let latestTime = '';
            allStocksReplayData.series.forEach(series => {{
                const visiblePoints = series.points.filter(point => point.x <= frameX);
                if (!visiblePoints.length) {{
                    return;
                }}
                const pathData = visiblePoints.map((point, index) => `${{index === 0 ? 'M' : 'L'}} ${{scales.x(point.x).toFixed(2)}} ${{scales.y(point.y).toFixed(2)}}`).join(' ');
                svg.appendChild(svgEl('path', {{
                    d: pathData,
                    fill: 'none',
                    stroke: series.color,
                    'stroke-width': series.benchmark ? 2.4 : 1.8,
                    'stroke-dasharray': series.benchmark ? '7 5' : 'none',
                    'stroke-linecap': 'round',
                    'stroke-linejoin': 'round'
                }}));
                const lastPoint = visiblePoints[visiblePoints.length - 1];
                latestTime = lastPoint.time || latestTime;
                const dotX = scales.x(lastPoint.x);
                const dotY = scales.y(lastPoint.y);
                svg.appendChild(svgEl('circle', {{ cx: dotX, cy: dotY, r: series.benchmark ? 4.8 : 4.2, fill: series.color, stroke: '#ffffff', 'stroke-width': 1.5 }}));
                const pillWidth = Math.max(series.ticker.length * 7.4 + 15, 36);
                const pillX = Math.min(dotX + 8, width - scales.margin.right - pillWidth + 6);
                const pillY = Math.max(scales.margin.top + 2, Math.min(dotY - 10, height - scales.margin.bottom - 20));
                const pillColor = darkenHexColor(series.color, 0.20);
                svg.appendChild(svgEl('rect', {{ x: pillX, y: pillY, width: pillWidth, height: 20, rx: 10, fill: pillColor, stroke: '#ffffff', 'stroke-width': 1.1, opacity: 0.96 }}));
                const label = svgEl('text', {{ x: pillX + pillWidth / 2, y: pillY + 14, fill: '#ffffff', 'font-size': 11.5, 'font-weight': 800, 'text-anchor': 'middle' }});
                label.textContent = series.ticker;
                svg.appendChild(label);
            }});
            status.textContent = `${{allStocksReplayState.playing ? 'Playing' : 'Paused'}}: ${{latestTime || 'start'}} (${{allStocksReplayState.frameIndex + 1}}/${{allStocksReplayData.frames.length}})`;
        }}

        function setAllStocksReplayPlaying(playing) {{
            const button = document.getElementById('allStocksReplayButton');
            allStocksReplayState.playing = playing;
            button.innerHTML = playing ? '&#10073;&#10073; Pause' : '&#9658; Replay';
            button.classList.toggle('active', playing);
            if (allStocksReplayState.timer) {{
                clearInterval(allStocksReplayState.timer);
                allStocksReplayState.timer = null;
            }}
            if (playing) {{
                allStocksReplayState.timer = setInterval(() => {{
                    if (allStocksReplayState.frameIndex >= allStocksReplayData.frames.length - 1) {{
                        setAllStocksReplayPlaying(false);
                        document.getElementById('allStocksReplayWrap').classList.remove('active');
                        document.getElementById('allStocksStaticImage').classList.remove('hidden');
                        allStocksReplayState.initialized = false;
                        return;
                    }}
                    allStocksReplayState.frameIndex = Math.min(allStocksReplayState.frameIndex + 1, allStocksReplayData.frames.length - 1);
                    renderAllStocksReplayFrame();
                }}, 333);
            }}
            renderAllStocksReplayFrame();
        }}

        function toggleAllStocksReplay() {{
            if (!allStocksReplayData.series.length || !allStocksReplayData.frames.length) {{
                document.getElementById('allStocksReplayStatus').textContent = 'Replay data unavailable for this run.';
                return;
            }}
            document.getElementById('allStocksStaticImage').classList.add('hidden');
            document.getElementById('allStocksReplayWrap').classList.add('active');
            if (!allStocksReplayState.initialized || allStocksReplayState.frameIndex >= allStocksReplayData.frames.length - 1) {{
                allStocksReplayState.frameIndex = 0;
                allStocksReplayState.initialized = true;
            }}
            setAllStocksReplayPlaying(!allStocksReplayState.playing);
        }}

        window.screenSimChartPopoutUrl = screenSimChartPopoutUrl;
        document.querySelectorAll('.screener-table th[data-sort-key]').forEach(header => {{
            header.addEventListener('click', () => sortSelectedStocksTable(header));
        }});
        initSelectedStocksNotes();
        document.getElementById('tickerChartClose').addEventListener('click', closeTickerChart);
        document.getElementById('tickerChartModal').addEventListener('click', event => {{
            if (event.target.id === 'tickerChartModal') {{
                closeTickerChart();
            }}
        }});
        document.addEventListener('keydown', event => {{
            if (event.key === 'Escape') {{
                closeTickerChart();
            }}
        }});
        updateLiveClock();
        setInterval(updateLiveClock, 1000);
        startLiveRefreshCountdown();
    </script>
</body>
</html>
"""
        with open(viewer_path, "w", encoding="utf-8") as handle:
                handle.write(html_text)
        return viewer_path


def set_intraday_ticks(ax, df: pd.DataFrame):
    if df.empty:
        return

    boundary_label_gap = 1.0

    half_hour_tick_times = []
    cur = datetime.strptime("09:30", "%H:%M")
    end = datetime.strptime("16:00", "%H:%M")
    while cur <= end:
        half_hour_tick_times.append(cur.strftime("%H:%M"))
        cur += timedelta(minutes=30)

    tick_positions = []
    tick_labels = []
    grouped_days = list(df.groupby("session_date", sort=True))
    total_days = len(grouped_days)

    for day_idx, (_, day_df) in enumerate(grouped_days):
        day_tick_times = list(half_hour_tick_times)

        # Avoid label collisions at day boundaries (16:00 next to next-day 09:30).
        if day_idx < total_days - 1:
            day_tick_times = [t for t in day_tick_times if t != "16:00"]

        for tick_time in day_tick_times:
            m = day_df[day_df["session_time"] == tick_time]
            if not m.empty:
                tick_position = float(m.iloc[0]["x_idx"])
                if tick_time == "09:30" and day_idx > 0:
                    tick_position += boundary_label_gap
                tick_positions.append(tick_position)
                tick_labels.append(tick_time)

        if not tick_positions or tick_positions[-1] < float(day_df["x_idx"].min()):
            first_row = day_df.iloc[0]
            first_position = float(first_row["x_idx"])
            if day_idx > 0:
                first_position += boundary_label_gap
            tick_positions.append(first_position)
            tick_labels.append(str(first_row["session_time"]))

        last_row = day_df.iloc[-1]
        last_position = float(last_row["x_idx"])
        if tick_positions[-1] != last_position:
            label_position = last_position - boundary_label_gap if day_idx < total_days - 1 else last_position
            tick_positions.append(label_position)
            tick_labels.append(str(last_row["session_time"]))

    if tick_positions:
        ax.set_xticks(tick_positions)
        ax.set_xticklabels(tick_labels, rotation=45, ha="right", va="top")


def plot_candlesticks(ax, df: pd.DataFrame):
    if df.empty:
        return

    width = 0.65
    previous_closes = df["close"].astype(float).shift(1)
    previous_closes.iloc[0] = float(df["open"].iloc[0])
    price_range = float(df["high"].astype(float).max()) - float(df["low"].astype(float).min())
    min_body_height = max(price_range * 0.0015, 1e-6)

    for index, row in enumerate(df.itertuples(index=False)):
        x = float(row.x_idx)
        o = float(row.open)
        h = float(row.high)
        l = float(row.low)
        c = float(row.close)

        is_hollow = c >= o
        previous_close = float(previous_closes.iloc[index])
        color = WATCHLIST_CANDLE_UP_COLOR if c >= previous_close else WATCHLIST_CANDLE_DOWN_COLOR

        body_bottom = min(o, c)
        body_height = max(abs(c - o), min_body_height)
        if abs(c - o) < min_body_height:
            body_bottom -= min_body_height / 2
        ax.vlines(x, l, h, color=color, linewidth=0.9, alpha=0.95)
        rect = Rectangle(
            (x - width / 2, body_bottom),
            width,
            body_height,
            facecolor="none" if is_hollow else color,
            edgecolor=color,
            linewidth=0.8,
            alpha=0.95,
        )
        ax.add_patch(rect)


# ============================================================================
# MAIN
# ============================================================================


def build_benchmark_line_data(api_key: str, entry_date_str: str, end_date_str: str, entry_date_obj: date, trading_days: list[date], symbol_data: dict, positions: dict, entry_ts_target: datetime, exit_ts_target: datetime):
    benchmark_line_data = []
    for benchmark_ticker in BENCHMARK_TICKERS:
        if benchmark_ticker in symbol_data and benchmark_ticker in positions:
            benchmark_df = symbol_data[benchmark_ticker].copy()
            benchmark_entry_ts = positions[benchmark_ticker]["entry_ts"]
            benchmark_entry_price = positions[benchmark_ticker]["entry_price"]
        else:
            log_info(f"Downloading benchmark {benchmark_ticker} for plot reference...")
            benchmark_df = fetch_10min_data(benchmark_ticker, entry_date_str, end_date_str, api_key)
            benchmark_df = apply_entry_close_1min_window(benchmark_df, benchmark_ticker, entry_date_str, api_key)
            benchmark_df = apply_exact_1min_close(benchmark_df, benchmark_ticker, end_date_str, time(EXIT_HOUR, EXIT_MINUTE), api_key)
            if benchmark_df.empty:
                log_warn(f"Skipped benchmark: {benchmark_ticker} (no data)")
                continue
            benchmark_df = benchmark_df[benchmark_df["trade_date"].isin(set(trading_days))].copy()
            if benchmark_df.empty:
                log_warn(f"Skipped benchmark: {benchmark_ticker} (no valid session rows)")
                continue

            benchmark_entry_day_df = benchmark_df[benchmark_df["trade_date"] == entry_date_obj].copy().sort_values("timestamp")
            if benchmark_entry_day_df.empty:
                log_warn(f"Skipped benchmark: {benchmark_ticker} (no entry-day bars)")
                continue

            exact_benchmark_entry = benchmark_entry_day_df[benchmark_entry_day_df["timestamp"] == entry_ts_target]
            if not exact_benchmark_entry.empty:
                benchmark_entry_row = exact_benchmark_entry.iloc[-1]
            else:
                fallback_benchmark_entry = benchmark_entry_day_df[benchmark_entry_day_df["timestamp"] <= entry_ts_target]
                if fallback_benchmark_entry.empty:
                    log_warn(f"Skipped benchmark: {benchmark_ticker} (no bar at/before 15:50)")
                    continue
                benchmark_entry_row = fallback_benchmark_entry.iloc[-1]

            benchmark_entry_price = float(benchmark_entry_row["close"])
            benchmark_entry_ts = pd.to_datetime(benchmark_entry_row["timestamp"])
            if benchmark_entry_price <= 0:
                log_warn(f"Skipped benchmark: {benchmark_ticker} (invalid entry close)")
                continue

        benchmark_line_source_df = benchmark_df[(benchmark_df["timestamp"] >= benchmark_entry_ts) & (benchmark_df["timestamp"] <= exit_ts_target)].copy()
        if benchmark_line_source_df.empty:
            log_warn(f"Skipped benchmark: {benchmark_ticker} (no rows after entry)")
            continue
        benchmark_line_df = add_session_index(benchmark_line_source_df, trading_days, {entry_date_obj: time(ENTRY_HOUR, ENTRY_MINUTE)})
        benchmark_line_df["pnl_pct"] = ((benchmark_line_df["close"] - benchmark_entry_price) / benchmark_entry_price) * 100.0
        benchmark_line_data.append((benchmark_ticker, benchmark_line_df.copy()))
    return benchmark_line_data


def run_simulation(entry_date_str: str, tickers, open_dashboard: bool = True, screener_context: dict | None = None) -> str | None:
    api_key = read_polygon_key()

    if not tickers:
        raise ValueError("No tickers provided. Add tickers in config or input manually.")

    # Start processing timer after interactive inputs are complete.
    run_start_time = datetime.now()

    entry_date_obj = parse_entry_date(entry_date_str)
    log_info(f"Parsed entry date: {entry_date_obj:%A %d %B %Y}")

    if not is_trading_day(entry_date_obj):
        requested_entry_date_obj = entry_date_obj
        entry_date_obj = get_latest_closed_trading_day(entry_date_obj)
        log_warn(f"Entry date {requested_entry_date_obj:%Y-%m-%d} is not a trading day; using T0 {entry_date_obj:%Y-%m-%d}.")

    entry_date_str = entry_date_obj.strftime("%Y-%m-%d")
    end_date_obj = get_nth_next_trading_day(entry_date_obj, 3)
    end_date_str = end_date_obj.strftime("%Y-%m-%d")
    exit_ts_target = datetime.combine(end_date_obj, time(EXIT_HOUR, EXIT_MINUTE))
    date_range = format_file_date_range(entry_date_obj, end_date_obj)
    report_run_suffix = run_start_time.strftime("%H%M%S")
    artifact_label = f"{date_range} {report_run_suffix}"

    trading_days = build_trading_days(entry_date_obj, end_date_obj)
    if not trading_days:
        raise ValueError("No trading days in selected date range")

    tickers = sorted({str(ticker).strip().upper() for ticker in tickers if str(ticker).strip()})
    if not tickers:
        raise ValueError("No tickers provided. Add tickers in config or input manually.")

    output_folder = os.path.join(REPORTS_ROOT, f"{run_start_time:%a %d %b %Y} Runs")
    os.makedirs(output_folder, exist_ok=True)
    metadata_folder = os.path.join(output_folder, REPORT_METADATA_FOLDER_NAME)
    os.makedirs(metadata_folder, exist_ok=True)

    log_section("IN-SWING SIMULATION")
    log_info(f"Entry date: {entry_date_str} (T0)")
    log_info(f"Exit date:  {end_date_str} (T3)")
    log_info(f"Exit mode:  T3 {EXIT_HOUR:02d}:{EXIT_MINUTE:02d} 1-minute close")
    log_info(f"Bars:       {BAR_MINUTES}-minute")
    log_info(f"Sessions:   {', '.join(f'T{idx}={trading_day:%Y-%m-%d}' for idx, trading_day in enumerate(trading_days))}")
    log_info(f"Tickers:    {', '.join(tickers)}")
    log_info(f"Output:     {output_folder}")

    allocation_per_symbol = INITIAL_CAPITAL / len(tickers)

    symbol_data = {}
    positions = {}
    skipped_symbols = []

    entry_ts_target = datetime.strptime(f"{entry_date_str} {ENTRY_HOUR:02d}:{ENTRY_MINUTE:02d}", "%Y-%m-%d %H:%M")

    for ticker in tickers:
        log_info(f"Downloading {ticker}...")
        df = fetch_10min_data(ticker, entry_date_str, end_date_str, api_key)
        df = apply_entry_close_1min_window(df, ticker, entry_date_str, api_key)
        df = apply_exact_1min_close(df, ticker, end_date_str, time(EXIT_HOUR, EXIT_MINUTE), api_key)

        if df.empty:
            skipped_symbols.append((ticker, "No market data in date range"))
            log_warn(f"Skipped: {ticker} (no data)")
            continue

        df = df[df["trade_date"].isin(set(trading_days))].copy()
        if df.empty:
            skipped_symbols.append((ticker, "No trading-session rows after day filter"))
            log_warn(f"Skipped: {ticker} (no valid session rows)")
            continue

        csv_path = os.path.join(metadata_folder, f"3_{ticker} Data 10m {artifact_label}.csv")
        df.to_csv(csv_path, index=False)

        entry_day_df = df[df["trade_date"] == entry_date_obj].copy().sort_values("timestamp")
        if entry_day_df.empty:
            skipped_symbols.append((ticker, "No bars on entry date"))
            log_warn(f"Skipped: {ticker} (no entry-day bars)")
            continue

        exact_entry = entry_day_df[entry_day_df["timestamp"] == entry_ts_target]
        if not exact_entry.empty:
            entry_row = exact_entry.iloc[-1]
            entry_note = "exact 15:50 close"
        else:
            fallback_entry = entry_day_df[entry_day_df["timestamp"] <= entry_ts_target]
            if fallback_entry.empty:
                skipped_symbols.append((ticker, "No 15:50 or earlier bar on entry date"))
                log_warn(f"Skipped: {ticker} (no bar at/before 15:50)")
                continue
            entry_row = fallback_entry.iloc[-1]
            entry_note = "fallback latest <= 15:50"

        entry_price = float(entry_row["close"])
        entry_ts = pd.to_datetime(entry_row["timestamp"])

        if entry_price <= 0:
            skipped_symbols.append((ticker, "Invalid entry close price"))
            log_warn(f"Skipped: {ticker} (invalid entry close)")
            continue

        shares = allocation_per_symbol / entry_price

        symbol_data[ticker] = df
        positions[ticker] = {
            "entry_ts": entry_ts,
            "entry_price": entry_price,
            "shares": shares,
            "entry_value": shares * entry_price,
            "entry_note": entry_note,
        }

        log_success(
            f"Entry set: {ticker} at {entry_ts.strftime('%Y-%m-%d %H:%M')} "
            f"close={entry_price:.2f}, shares={shares:.2f} ({entry_note})"
        )

    if not positions:
        log_error("No positions could be created. Exiting.")
        return

    deployed_capital = sum(pos["entry_value"] for pos in positions.values())
    stop_loss_dollars = INITIAL_CAPITAL * PORTFOLIO_STOP_LOSS
    target_dollars = INITIAL_CAPITAL * PORTFOLIO_TARGET

    log_section("POSITION SUMMARY")
    log_info(f"Entered symbols: {', '.join(sorted(positions.keys()))}")
    log_info(f"Skipped symbols: {len(skipped_symbols)}")
    log_info(f"Configured capital: ${INITIAL_CAPITAL:,.2f}")
    log_info(f"Deployed capital:   ${deployed_capital:,.2f}")
    log_info(f"Stop (PnL $):       ${stop_loss_dollars:,.2f}")
    log_info(f"Target (PnL $):     ${target_dollars:,.2f}")

    timeline = set()
    for ticker, df in symbol_data.items():
        entry_ts = positions[ticker]["entry_ts"]
        timeline.update(df[(df["timestamp"] >= entry_ts) & (df["timestamp"] <= exit_ts_target)]["timestamp"].tolist())

    if not timeline:
        log_error("No timeline points available after entry. Exiting.")
        return

    timeline = sorted(timeline)
    price_curves = {}
    for ticker, df in symbol_data.items():
        series = df.set_index("timestamp")["close"].sort_index()
        price_curves[ticker] = series.reindex(timeline, method="ffill")

    portfolio_rows = []
    for ts in timeline:
        current_value = 0.0
        for ticker, pos in positions.items():
            if ts < pos["entry_ts"]:
                continue
            px = price_curves[ticker].loc[ts]
            if pd.notna(px):
                current_value += pos["shares"] * float(px)

        pnl_dollars = current_value - deployed_capital
        pnl_pct = (pnl_dollars / deployed_capital * 100.0) if deployed_capital else 0.0

        portfolio_rows.append(
            {
                "timestamp": ts,
                "date": ts.strftime("%Y-%m-%d"),
                "time": ts.strftime("%H:%M"),
                "portfolio_value": round(current_value, 2),
                "pnl_dollars": round(pnl_dollars, 2),
                "net_portfolio_pct_change": round(pnl_pct, 4),
            }
        )

    portfolio_df = pd.DataFrame(portfolio_rows)
    if portfolio_df.empty:
        log_error("No portfolio history generated. Exiting.")
        return

    symbol_exits = {}
    for ticker, pos in positions.items():
        df = symbol_data[ticker]

        end_day_rows = df[(df["trade_date"] == end_date_obj) & (df["timestamp"] <= exit_ts_target)]
        if not end_day_rows.empty:
            last_row = end_day_rows.sort_values("timestamp").iloc[-1]
            symbol_exits[ticker] = (float(last_row["close"]), pd.to_datetime(last_row["timestamp"]))
            continue

        fallback_rows = df[df["timestamp"] <= exit_ts_target]
        if not fallback_rows.empty:
            last_row = fallback_rows.sort_values("timestamp").iloc[-1]
            symbol_exits[ticker] = (float(last_row["close"]), pd.to_datetime(last_row["timestamp"]))
        else:
            symbol_exits[ticker] = (pos["entry_price"], pos["entry_ts"])

    exit_ts = max(ts for _, ts in symbol_exits.values())
    final_value = 0.0
    for ticker, pos in positions.items():
        exit_px, _ = symbol_exits[ticker]
        final_value += pos["shares"] * exit_px

    final_pnl = final_value - deployed_capital
    final_pct = (final_pnl / deployed_capital * 100.0) if deployed_capital else 0.0

    portfolio_df = pd.concat(
        [
            portfolio_df,
            pd.DataFrame(
                [
                    {
                        "timestamp": exit_ts,
                        "date": exit_ts.strftime("%Y-%m-%d"),
                        "time": exit_ts.strftime("%H:%M"),
                        "portfolio_value": round(final_value, 2),
                        "pnl_dollars": round(final_pnl, 2),
                        "net_portfolio_pct_change": round(final_pct, 4),
                    }
                ]
            ),
        ],
        ignore_index=True,
    ).drop_duplicates(subset=["timestamp"], keep="last").sort_values("timestamp").reset_index(drop=True)

    exit_reason = f"T3 {EXIT_HOUR:02d}:{EXIT_MINUTE:02d} 1-Minute Close"

    summary_rows = []
    for ticker, pos in positions.items():
        exit_px, symbol_exit_ts = symbol_exits[ticker]

        entry_value = pos["entry_value"]
        exit_value = pos["shares"] * exit_px
        net_pl = exit_value - entry_value
        net_pl_pct = (net_pl / entry_value * 100.0) if entry_value else 0.0

        summary_rows.append(
            {
                "Symbol": ticker,
                "Entry Date": pos["entry_ts"].strftime("%Y-%m-%d"),
                "Entry Time": pos["entry_ts"].strftime("%H:%M"),
                "Entry Price": round(pos["entry_price"], 4),
                "Entry Price Rule": pos["entry_note"],
                "Quantity": round(pos["shares"], 4),
                "Entry Value": round(entry_value, 2),
                "Exit Date": symbol_exit_ts.strftime("%Y-%m-%d"),
                "Exit Time": symbol_exit_ts.strftime("%H:%M"),
                "Exit Price": round(exit_px, 4),
                "Exit Value": round(exit_value, 2),
                "Net P/L": round(net_pl, 2),
                "Net P/L %": round(net_pl_pct, 4),
            }
        )

    summary_df = pd.DataFrame(summary_rows).sort_values(by="Net P/L %", ascending=False)
    skipped_df = pd.DataFrame(skipped_symbols, columns=["Symbol", "Reason"])

    excel_path = os.path.join(metadata_folder, f"4_Report {run_start_time:%A %d %b %Y %H%M%S}.xlsx")
    with pd.ExcelWriter(excel_path, engine="openpyxl") as writer:
        portfolio_df.to_excel(writer, sheet_name="Portfolio History 10min", index=False)
        summary_df.to_excel(writer, sheet_name="Symbol Summary", index=False)
        skipped_df.to_excel(writer, sheet_name="Skipped Symbols", index=False)

    benchmark_line_data = build_benchmark_line_data(api_key, entry_date_str, end_date_str, entry_date_obj, trading_days, symbol_data, positions, entry_ts_target, exit_ts_target)

    # Portfolio chart (session-only axis)
    portfolio_plot_df = add_session_index(
        portfolio_df[["timestamp", "net_portfolio_pct_change"]].copy(),
        trading_days,
        {entry_date_obj: time(ENTRY_HOUR, ENTRY_MINUTE)},
    )
    portfolio_chart_path = os.path.join(metadata_folder, f"2_Portfolio Chart 10m {artifact_label}.png")
    render_portfolio_chart(portfolio_plot_df, portfolio_chart_path, entry_date_str, end_date_str, final_pct, final_value, INITIAL_CAPITAL, benchmark_line_data, len(positions), allocation_per_symbol)

    # Per-symbol charts (candles + pnl)
    symbol_chart_paths = []
    stock_line_data = []
    ranked_symbols = summary_df["Symbol"].tolist()
    for ticker in ranked_symbols:
        pos = positions[ticker]
        chart_source_df = symbol_data[ticker][symbol_data[ticker]["timestamp"] <= exit_ts_target].copy()
        line_source_df = chart_source_df[chart_source_df["timestamp"] >= pos["entry_ts"]].copy()
        if chart_source_df.empty or line_source_df.empty:
            continue

        chart_df = add_session_index(chart_source_df, trading_days)
        chart_df["pnl_pct"] = ((chart_df["close"] - pos["entry_price"]) / pos["entry_price"]) * 100.0

        line_df = add_session_index(line_source_df, trading_days, {entry_date_obj: time(ENTRY_HOUR, ENTRY_MINUTE)})
        line_df["pnl_pct"] = ((line_df["close"] - pos["entry_price"]) / pos["entry_price"]) * 100.0

        exit_px, exit_symbol_ts = symbol_exits[ticker]

        stock_line_data.append((ticker, line_df.copy()))

        symbol_chart_path = os.path.join(metadata_folder, f"2_{ticker} Chart 10m {artifact_label}.png")
        render_stock_candle_report(ticker, chart_df, symbol_chart_path, pos["entry_price"], exit_px, pos["entry_ts"], exit_symbol_ts, benchmark_line_data)
        symbol_chart_paths.append(symbol_chart_path)

    all_stocks_chart_path = os.path.join(metadata_folder, f"2_All Symbols Chart 10m {artifact_label}.png")
    render_all_stock_lines_chart(stock_line_data, all_stocks_chart_path, entry_date_str, end_date_str, benchmark_line_data)
    live_state = {
        "entry_date": entry_date_str,
        "end_date": end_date_str,
        "deployed_capital": deployed_capital,
        "positions": {
            ticker: {
                "entry_price": float(position["entry_price"]),
                "shares": float(position["shares"]),
            }
            for ticker, position in positions.items()
        },
    }
    shortlisted_history_30d = build_shortlisted_history_30d_payload(api_key, ranked_symbols, entry_date_obj, positions)
    stock_viewer_path = write_stock_chart_viewer(output_folder, portfolio_chart_path, all_stocks_chart_path, symbol_chart_paths, entry_date_str, end_date_str, stock_line_data, benchmark_line_data, screener_context, live_state, shortlisted_history_30d, report_run_suffix)

    process_closed_at = datetime.now()
    elapsed = int((process_closed_at - run_start_time).total_seconds())
    summary_label_width = 15

    log_section("SIMULATION COMPLETE")
    log_success(f"{'Exit timestamp':<{summary_label_width}}: {exit_ts.strftime('%Y-%m-%d %H:%M')}")
    log_success(f"{'Exit reason':<{summary_label_width}}: {exit_reason}")
    log_success(f"{'Final value':<{summary_label_width}}: ${final_value:,.2f}")
    log_success(f"{'Net P/L':<{summary_label_width}}: ${final_pnl:,.2f}")
    log_success(f"{'Net P/L %':<{summary_label_width}}: {final_pct:+.2f}%")
    log_info(f"{'Excel report':<{summary_label_width}}: {os.path.relpath(excel_path, output_folder)}")
    log_info(f"{'Portfolio plot':<{summary_label_width}}: {os.path.relpath(portfolio_chart_path, output_folder)}")
    if stock_viewer_path:
        log_info(f"{'Dashboard HTML':<{summary_label_width}}: {os.path.basename(stock_viewer_path)}")
        if open_dashboard:
            open_file_in_default_app(stock_viewer_path)
            log_info(f"{'Opened':<{summary_label_width}}: Dashboard HTML in default browser")
    log_info(f"{'Processing Time':<{summary_label_width}}: {elapsed} seconds")
    log_info(f"{'Process closed':<{summary_label_width}}: {process_closed_at.strftime('%H:%M:%S')}")

    if "DUO_UI_STATE" in globals():
        DUO_UI_STATE["last_simulation_entry_date"] = entry_date_str
        DUO_UI_STATE["last_simulation_end_date"] = end_date_str
        DUO_UI_STATE["last_simulation_tickers"] = sorted(positions.keys())
        DUO_UI_STATE["last_simulation_live_state"] = live_state
        DUO_UI_STATE["last_shortlisted_history_30d"] = shortlisted_history_30d
    return stock_viewer_path


DUO_UI_STATE = {
    "screener_rows": [],
    "screener_config": None,
    "message": "",
    "dashboard_path": "",
    "last_screener_duration_seconds": None,
    "last_simulator_duration_seconds": None,
    "last_simulation_entry_date": "",
    "last_simulation_tickers": [],
    "last_simulation_end_date": "",
    "last_simulation_live_state": None,
    "last_shortlisted_history_30d": [],
    "active_saved_report_folder": "",
}
SIMULATION_REFRESH_LOCK = threading.Lock()
DAILY_CHART_JSON_CACHE: dict[tuple[str, str, bool], dict] = {}
DAILY_CHART_JSON_CACHE_LOCK = threading.Lock()
DAILY_CHART_JSON_CACHE_LIMIT = 256


def reset_duo_screener_state() -> None:
    DUO_UI_STATE["screener_rows"] = []
    DUO_UI_STATE["screener_config"] = None
    DUO_UI_STATE["message"] = ""
    DUO_UI_STATE["dashboard_path"] = ""
    DUO_UI_STATE["last_screener_duration_seconds"] = None
    DUO_UI_STATE["last_simulator_duration_seconds"] = None
    DUO_UI_STATE["last_simulation_entry_date"] = ""
    DUO_UI_STATE["last_simulation_tickers"] = []
    DUO_UI_STATE["last_simulation_end_date"] = ""
    DUO_UI_STATE["last_simulation_live_state"] = None
    DUO_UI_STATE["last_shortlisted_history_30d"] = []
    DUO_UI_STATE["active_saved_report_folder"] = ""


def build_live_snapshot(live_state: dict | None = None) -> dict:
    live_state = live_state or DUO_UI_STATE.get("last_simulation_live_state") or {}
    entry_date_str = str(live_state.get("entry_date") or DUO_UI_STATE.get("last_simulation_entry_date") or "")
    end_date_str = str(live_state.get("end_date") or DUO_UI_STATE.get("last_simulation_end_date") or "")
    positions = live_state.get("positions") or {}
    deployed_capital = float(live_state.get("deployed_capital") or 0.0)
    if not entry_date_str or not end_date_str or not positions or deployed_capital <= 0:
        return {"active": False, "reason": "No live simulation state is available."}

    now_et = datetime.now(ZoneInfo("America/New_York"))
    live_context = get_live_refresh_context(entry_date_str, end_date_str, now_et)
    if live_context is None:
        return {"active": False, "reason": "Live snapshot is only active on T1/T2/T3 during market hours."}

    api_key = read_polygon_key()
    today_str = now_et.date().isoformat()
    now_naive = now_et.replace(tzinfo=None)
    completed_minute = now_naive.replace(second=0, microsecond=0) - timedelta(minutes=1)

    current_value = 0.0
    prices = {}
    latest_timestamp = None
    missing = []
    for ticker, position in positions.items():
        shares = float(position["shares"])
        entry_price = float(position["entry_price"])
        df = fetch_minute_data(ticker, today_str, today_str, api_key, 1)
        usable = df[df["timestamp"] <= completed_minute].copy() if not df.empty else pd.DataFrame()
        if usable.empty and not df.empty:
            usable = df[df["timestamp"] <= now_naive].copy()

        if usable.empty:
            close = entry_price
            timestamp_text = ""
            missing.append(ticker)
        else:
            latest_row = usable.sort_values("timestamp").iloc[-1]
            close = float(latest_row["close"])
            timestamp = pd.to_datetime(latest_row["timestamp"]).to_pydatetime()
            timestamp_text = timestamp.strftime("%H:%M")
            if latest_timestamp is None or timestamp > latest_timestamp:
                latest_timestamp = timestamp

        current_value += shares * close
        prices[ticker] = {
            "close": round(close, 4),
            "timestamp": timestamp_text,
            "pnl_pct": round(((close - entry_price) / entry_price) * 100.0, 4) if entry_price else 0.0,
        }

    pnl_dollars = current_value - deployed_capital
    pnl_pct = (pnl_dollars / deployed_capital) * 100.0
    return {
        "active": True,
        "session": live_context["session"],
        "date": live_context["date"],
        "timestamp": latest_timestamp.strftime("%H:%M") if latest_timestamp else "",
        "portfolio_value": round(current_value, 2),
        "pnl_dollars": round(pnl_dollars, 2),
        "pnl_pct": round(pnl_pct, 4),
        "prices": prices,
        "missing": missing,
    }


def parse_dashboard_date_range_label(label: str) -> tuple[date, date] | None:
    label = dashboard_date_range_part(label)
    patterns = [
        (r"^(\d{1,2})-(\d{1,2}) ([A-Za-z]{3,9}) (\d{4})$", lambda m: (
            datetime.strptime(f"{m.group(1)} {m.group(3)} {m.group(4)}", "%d %b %Y").date(),
            datetime.strptime(f"{m.group(2)} {m.group(3)} {m.group(4)}", "%d %b %Y").date(),
        )),
        (r"^(\d{1,2}) ([A-Za-z]{3,9})-(\d{1,2}) ([A-Za-z]{3,9}) (\d{4})$", lambda m: (
            datetime.strptime(f"{m.group(1)} {m.group(2)} {m.group(5)}", "%d %b %Y").date(),
            datetime.strptime(f"{m.group(3)} {m.group(4)} {m.group(5)}", "%d %b %Y").date(),
        )),
        (r"^(\d{1,2}) ([A-Za-z]{3,9}) (\d{4})-(\d{1,2}) ([A-Za-z]{3,9}) (\d{4})$", lambda m: (
            datetime.strptime(f"{m.group(1)} {m.group(2)} {m.group(3)}", "%d %b %Y").date(),
            datetime.strptime(f"{m.group(4)} {m.group(5)} {m.group(6)}", "%d %b %Y").date(),
        )),
    ]
    for pattern, parser in patterns:
        match = re.match(pattern, label)
        if match:
            try:
                return parser(match)
            except ValueError:
                return None
    return None


def split_dashboard_label_suffix(label: str) -> tuple[str, str]:
    label = label.strip()
    match = re.match(r"^(.*\b\d{4})\s+(\d{4,6}(?:-\d+)?)$", label)
    if not match:
        return label, ""
    return match.group(1).strip(), match.group(2).strip()


def dashboard_date_range_part(label: str) -> str:
    return split_dashboard_label_suffix(label)[0]


def format_run_suffix_for_display(suffix: str) -> str:
    digits = re.match(r"^(\d{2})(\d{2})(?:\d{2})?(?:-\d+)?$", suffix or "")
    if not digits:
        return suffix
    hour = int(digits.group(1))
    minute = int(digits.group(2))
    am_pm = "AM" if hour < 12 else "PM"
    display_hour = hour % 12 or 12
    return f"{display_hour}:{minute:02d} {am_pm}"


def format_dashboard_ready_label(label: str) -> str:
    parsed_range = parse_dashboard_date_range_label(label)
    if not parsed_range:
        return f"{label} Dashboard Ready"
    start_value, end_value = parsed_range
    if start_value.year == end_value.year and start_value.month == end_value.month:
        return f"{start_value:%B} {start_value.day}-{end_value.day} {start_value:%Y} Dashboard Ready"
    if start_value.year == end_value.year:
        return f"{start_value:%B} {start_value.day}-{end_value:%B} {end_value.day} {start_value:%Y} Dashboard Ready"
    return f"{start_value:%B} {start_value.day} {start_value:%Y}-{end_value:%B} {end_value.day} {end_value:%Y} Dashboard Ready"


def format_saved_report_card_label(label: str) -> str:
    _date_label, run_suffix = split_dashboard_label_suffix(label)
    parsed_range = parse_dashboard_date_range_label(label)
    if not parsed_range:
        return f"{label} Report"
    start_value, end_value = parsed_range
    time_text = format_run_suffix_for_display(run_suffix)
    suffix_text = f" {time_text}" if time_text else ""
    if start_value.year == end_value.year and start_value.month == end_value.month:
        return f"{start_value:%b} {start_value.day}-{end_value.day} {start_value:%Y}{suffix_text} Report"
    if start_value.year == end_value.year:
        return f"{start_value:%b} {start_value.day}-{end_value:%b} {end_value.day} {start_value:%Y}{suffix_text} Report"
    return f"{start_value:%b} {start_value.day} {start_value:%Y}-{end_value:%b} {end_value.day} {end_value:%Y}{suffix_text} Report"


def get_report_note_rel_path(report_path: str) -> str:
    report_abs = os.path.abspath(report_path)
    reports_root_abs = os.path.abspath(REPORTS_ROOT)
    if not report_abs.startswith(reports_root_abs + os.sep):
        return ""
    rel_path = os.path.relpath(report_abs, reports_root_abs)
    rel_dir = os.path.dirname(rel_path)
    report_stem = os.path.splitext(os.path.basename(rel_path))[0]
    return os.path.join(rel_dir, REPORT_METADATA_FOLDER_NAME, f"{report_stem} Notes.txt").replace("\\", "/")


def resolve_report_note_path(rel_path: str) -> str:
    normalized_rel = unquote(str(rel_path or "")).replace("/", os.sep)
    if not normalized_rel or not normalized_rel.lower().endswith(".txt"):
        raise ValueError("Invalid report note path")
    if REPORT_METADATA_FOLDER_NAME not in normalized_rel.split(os.sep):
        raise ValueError("Report notes must be stored in the metadata folder")
    note_path = os.path.abspath(os.path.join(REPORTS_ROOT, normalized_rel))
    reports_root_abs = os.path.abspath(REPORTS_ROOT)
    if not note_path.startswith(reports_root_abs + os.sep):
        raise ValueError("Report note path is outside the reports folder")
    return note_path


def get_saved_dashboard_reports(limit: int | None = 10) -> list[dict]:
    reports = []
    if not os.path.isdir(REPORTS_ROOT):
        return reports

    now_et = datetime.now(ZoneInfo("America/New_York"))
    for root, _dirs, files in os.walk(REPORTS_ROOT):
        for filename in files:
            if not (filename.startswith("Dashboard ") and filename.endswith(".html")):
                continue
            path = os.path.join(root, filename)
            label = os.path.splitext(filename)[0].removeprefix("Dashboard ").strip()
            parsed_range = parse_dashboard_date_range_label(label)
            entry_date = parsed_range[0] if parsed_range else None
            end_date = parsed_range[1] if parsed_range else None
            live_session = ""
            status = "Historical"
            live_eligible = False
            if entry_date and end_date:
                live_status = get_report_live_status(entry_date, end_date, now_et)
                live_eligible = bool(live_status["live_eligible"])
                live_session = str(live_status["live_session"])
                status = str(live_status["status"])
            rel_path = os.path.relpath(path, REPORTS_ROOT)
            reports.append(
                {
                    "label": label,
                    "path": path,
                    "rel_path": rel_path,
                    "encoded_path": quote(rel_path.replace("\\", "/")),
                    "folder": os.path.basename(root),
                    "last_modified": os.path.getmtime(path),
                    "last_modified_text": datetime.fromtimestamp(os.path.getmtime(path)).strftime("%d %b %Y %I:%M %p"),
                    "entry_date": entry_date.isoformat() if entry_date else "",
                    "end_date": end_date.isoformat() if end_date else "",
                    "status": status,
                    "live_session": live_session,
                    "live_eligible": live_eligible,
                }
            )
    sorted_reports = sorted(reports, key=lambda item: item["last_modified"], reverse=True)
    return sorted_reports if limit is None else sorted_reports[:limit]


def resolve_saved_report_path(rel_path: str) -> str:
    cleaned = unquote(rel_path or "").replace("/", os.sep)
    requested_path = os.path.abspath(os.path.join(REPORTS_ROOT, cleaned))
    reports_root_abs = os.path.abspath(REPORTS_ROOT)
    if not requested_path.startswith(reports_root_abs + os.sep):
        raise ValueError("Invalid saved report path.")
    if not (os.path.isfile(requested_path) and os.path.basename(requested_path).startswith("Dashboard ") and requested_path.endswith(".html")):
        raise FileNotFoundError("Saved report was not found.")
    return requested_path


def build_saved_reports_sections_html(limit: int | None = None) -> str:
    reports = get_saved_dashboard_reports(limit)
    live_cards = []
    recent_cards = []
    for report in reports:
        report_title = format_saved_report_card_label(report["label"])
        live_badge = '<span class="badge live">Live</span>' if report["live_eligible"] else '<span class="badge muted">Saved</span>'
        open_report = f'/saved-report?path={report["encoded_path"]}'
        open_live = f'/saved-report?mode=live&path={report["encoded_path"]}'
        if report["live_eligible"]:
            actions = f'<a class="open live-action" href="{open_live}" target="_blank" rel="noopener noreferrer">Open Live</a>'
        else:
            actions = f'<a class="open" href="{open_report}" target="_blank" rel="noopener noreferrer">Open Report</a>'
        card = f"""
        <article class="report-card">
            <div class="report-top">
                <div>
                    <h2>{html.escape(report_title)}</h2>
                    <p>{html.escape(report["folder"])} · {html.escape(report["last_modified_text"])}</p>
                </div>
                {live_badge}
            </div>
            <div class="status">{html.escape(report["status"])}</div>
            <div class="dates">{html.escape(report["entry_date"] or "Unknown")} &rarr; {html.escape(report["end_date"] or "Unknown")}</div>
            <div class="actions">{actions}</div>
        </article>
"""
        if report["live_eligible"]:
            live_cards.append(card)
        else:
            recent_cards.append(card)

    live_html = "".join(live_cards) if live_cards else '<div class="empty">No saved reports are live-eligible right now. A report is live-eligible when today is T1/T2/T3 until 4:00 PM ET, or when a future T1/T2/T3 session still exists.</div>'
    recent_html = "".join(recent_cards) if recent_cards else '<div class="empty">No saved dashboard reports found yet.</div>'
    return f"""
        <section class="section saved-report-section">
            <h1>Live Eligible</h1>
            <div class="grid">{live_html}</div>
        </section>
        <section class="section saved-report-section">
            <h1>All Saved Reports</h1>
            <div class="grid">{recent_html}</div>
        </section>
"""


def render_saved_reports_page() -> str:
    saved_sections_html = build_saved_reports_sections_html(10)
    return f"""<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <title>Saved Reports - Inswing ScreenSim</title>
    <style>
{FINVIZ_THEME_CSS}
        body {{ margin: 0; background: #f3f3f5; color: #22262f; font-family: var(--fv-font-sans); }}
        .header {{ display: flex; align-items: center; justify-content: space-between; gap: 16px; padding: 10px 18px; background: #353945; color: #ffffff; }}
        .brand {{ font-size: 15px; font-weight: 700; }}
        .back {{ color: #22262f; background: #ffffff; border-radius: 999px; padding: 8px 14px; text-decoration: none; font-size: 12px; font-weight: 700; }}
        main {{ max-width: 1180px; margin: 22px auto 42px; padding: 0 18px; }}
        .section {{ margin-bottom: 22px; border: 1px solid #dedfe5; border-radius: 16px; overflow: hidden; background: #ffffff; box-shadow: 0 14px 34px rgba(20,22,29,0.08); }}
        .section h1 {{ margin: 0; padding: 13px 18px; background: linear-gradient(135deg, #353945, #4c5263); color: #ffffff; font-size: 14px; }}
        .grid {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(330px, 1fr)); gap: 12px; padding: 14px; }}
        .report-card {{ background: #ffffff; border: 1px solid #dedfe5; border-radius: 14px; padding: 14px; box-shadow: 0 6px 18px rgba(20,22,29,0.06); }}
        .report-top {{ display: flex; align-items: flex-start; justify-content: space-between; gap: 12px; }}
        .report-card h2 {{ margin: 0; color: #22262f; font-size: 15px; }}
        .report-card p {{ margin: 5px 0 0; color: #676f85; font-size: 11px; font-weight: 600; }}
        .badge {{ border-radius: 999px; padding: 4px 10px; font-size: 11px; font-weight: 700; white-space: nowrap; }}
        .badge.live {{ background: #f3f3f5; color: #353945; border: 1px solid #c3c6d0; }}
        .badge.muted {{ background: #f3f3f5; color: #676f85; border: 1px solid #dedfe5; }}
        .status {{ margin-top: 12px; color: #22262f; font-size: 13px; font-weight: 700; }}
        .dates {{ margin-top: 5px; color: #676f85; font-size: 11px; font-weight: 600; }}
        .actions {{ display: flex; flex-wrap: wrap; gap: 8px; margin-top: 13px; }}
        .open {{ display: inline-flex; align-items: center; justify-content: center; border-radius: 999px; background: #4c5263; color: #ffffff; padding: 8px 13px; text-decoration: none; font-size: 12px; font-weight: 700; }}
        .open.live-action {{ background: #353945; color: #ffffff; }}
        .empty {{ padding: 18px; color: #676f85; font-size: 13px; font-weight: 600; }}
    </style>
</head>
<body>
{DUO_THEME_BOOT_SCRIPT}
    <div class="header">
        <div class="brand">Inswing ScreenSim · Saved Reports</div>
        <span class="header-right">
{DUO_THEME_TOGGLE_HTML}
            <a class="back" href="/">Back to Screener</a>
        </span>
    </div>
    <main>
{saved_sections_html}
    </main>
</body>
</html>"""


def default_simulation_entry_date() -> str:
    run_date_et = datetime.now(ZoneInfo("America/New_York")).date()
    return CONFIG_ENTRY_DATE.strip() or get_nth_previous_trading_day(run_date_et, 4).strftime("%Y-%m-%d")


def default_screener_anchor_date() -> str:
    run_date_et = datetime.now(ZoneInfo("America/New_York")).date()
    return get_nth_previous_trading_day(run_date_et, 3).strftime("%Y-%m-%d")


def get_form_value(form: dict[str, list[str]], key: str, default: str = "") -> str:
    values = form.get(key)
    if not values:
        return default
    return values[0].strip()


def format_ui_date(value: str) -> str:
    try:
        return datetime.strptime(value, "%Y-%m-%d").strftime("%d/%m/%Y")
    except ValueError:
        return value


def format_ui_date_with_weekday(value: str) -> str:
    try:
        parsed = datetime.strptime(value, "%Y-%m-%d")
        return parsed.strftime("%d %b %Y %a")
    except ValueError:
        return value


def build_screener_config_from_form(form: dict[str, list[str]]):
    screener = load_daily_screener_module()
    anchor_date = get_form_value(form, "anchor_date", default_screener_anchor_date())
    if anchor_date:
        requested_anchor = datetime.strptime(anchor_date, "%Y-%m-%d").date()
        today_et = datetime.now(ZoneInfo("America/New_York")).date()
        if requested_anchor > today_et:
            raise ValueError("Anchor date cannot be in the future.")
    return screener.build_config_from_values(
        anchor_date=anchor_date,
        mcap_min=get_form_value(form, "mcap_min", str(screener.FILTERS["MCAP_MIN"])),
        mcap_max=get_form_value(form, "mcap_max", str(screener.FILTERS["MCAP_MAX"])),
        min_volume=get_form_value(form, "min_volume", str(screener.FILTERS["MIN_VOLUME"])),
        min_price=get_form_value(form, "min_price", str(screener.FILTERS["MIN_PRICE"])),
        min_atr10=get_form_value(form, "min_atr10", str(screener.FILTERS["MIN_ATR10"])),
        min_rsi14=get_form_value(form, "min_rsi14", str(screener.FILTERS["MIN_RSI14"])),
        min_momentum_score=None,
        require_ppo_gt_signal="require_ppo_gt_signal" in form or "require_macd_gt_signal" in form,
        require_ppo_cross="require_ppo_cross" in form or "require_macd_cross" in form,
        require_macd_gt_signal="require_macd_gt_signal" in form or "require_ppo_gt_signal" in form,
        require_macd_cross="require_macd_cross" in form or "require_ppo_cross" in form,
    )


def render_ui_page() -> str:
    screener = load_daily_screener_module()
    rows = DUO_UI_STATE["screener_rows"]
    config = DUO_UI_STATE["screener_config"]
    dashboard_path = DUO_UI_STATE["dashboard_path"]
    message = html.escape(DUO_UI_STATE["message"])
    default_anchor = getattr(config, "anchor_date", "") or default_screener_anchor_date()
    display_entry_date = format_ui_date_with_weekday(getattr(config, "anchor_date", default_simulation_entry_date()))
    today_et = datetime.now(ZoneInfo("America/New_York")).date().isoformat()
    has_rows = bool(rows)
    has_dashboard = bool(dashboard_path)
    has_screener_run = config is not None
    filter_panel_open = "" if has_rows else " open"
    refine_panel_open = " open" if len(rows) > 1 else ""
    screener_results_title = f"Screener Results ({len(rows):,})" if has_screener_run else "Screener Results"
    report_button_disabled = "" if has_dashboard else " disabled"
    report_button_class = "" if has_dashboard else " disabled-tab"
    cache_buster = int(datetime.now().timestamp() * 1000)
    report_tab_action = "goToGeneratedReport()" if has_dashboard else ""
    filter_values = {
        "mcap_min": screener.format_large_number(getattr(config, "mcap_min", screener.parse_large_number(screener.FILTERS["MCAP_MIN"]))),
        "mcap_max": screener.format_large_number(getattr(config, "mcap_max", screener.parse_large_number(screener.FILTERS["MCAP_MAX"]))),
        "min_volume": screener.format_large_number(getattr(config, "min_volume", screener.parse_large_number(screener.FILTERS["MIN_VOLUME"]))),
        "min_price": format_dashboard_cell(getattr(config, "min_price", screener.FILTERS["MIN_PRICE"])),
        "min_atr10": format_dashboard_cell(getattr(config, "min_atr10", screener.FILTERS["MIN_ATR10"])),
        "min_rsi14": format_dashboard_cell(getattr(config, "min_rsi14", screener.FILTERS["MIN_RSI14"])),
    }
    macd_checked = " checked" if getattr(config, "require_macd_gt_signal", getattr(config, "require_ppo_gt_signal", bool(screener.FILTERS.get("MACD>SIGNAL", screener.FILTERS.get("PPO>SIGNAL", False))))) else ""
    macd_cross_checked = " checked" if getattr(config, "require_macd_cross", getattr(config, "require_ppo_cross", bool(screener.FILTERS.get("MACD_CROSS", screener.FILTERS.get("PPO_CROSS", False))))) else ""
    screener_columns_payload = json.dumps([{"label": label, "key": key} for label, key in SCREENER_TABLE_COLUMNS], allow_nan=False)
    screener_comment_labels_payload = json.dumps(SCREENER_COMMENT_LABELS, allow_nan=False)
    screener_rows_payload = json.dumps(build_screener_rows_payload(rows), allow_nan=False)
    last_screener_duration = DUO_UI_STATE.get("last_screener_duration_seconds")
    estimated_screener_seconds = int(max(60, min(240, (float(last_screener_duration) * 1.15) if last_screener_duration else 120)))
    last_simulator_duration = DUO_UI_STATE.get("last_simulator_duration_seconds")
    estimated_simulator_seconds = int(max(30, min(180, (float(last_simulator_duration) * 1.15) if last_simulator_duration else 75)))
    run_simulator_disabled = "" if rows else " disabled"
    dashboard_html = ""
    dashboard_button_label = "Run Simulator"
    dashboard_button_type = "submit"
    dashboard_button_class = "watchlist-run-button"
    dashboard_button_ready = "0"
    if dashboard_path:
        dashboard_stem = os.path.splitext(os.path.basename(dashboard_path))[0]
        dashboard_range = dashboard_stem.removeprefix("Dashboard ").strip()
        dashboard_label = format_saved_report_card_label(dashboard_range)
        dashboard_html = f'<a class="dashboard-ready" href="/dashboard">{html.escape(dashboard_label)}</a>'
        dashboard_button_label = html.escape(dashboard_label)
        dashboard_button_type = "button"
        dashboard_button_class = "watchlist-run-button report-ready"
        dashboard_button_ready = "1"
    header_logo_html = ""
    if os.path.exists(HEADER_LOGO_SOURCE):
        copy_header_logo(HEADER_LOGO_SOURCE, SCRIPT_DIR)
        header_logo_html = '<img class="brand-logo" src="/app-static/nras-logo-transparent.png" alt="NRAS Alpha">'
    saved_reports_panel_html = build_saved_reports_sections_html(None)
    history_workspace_html = (
        build_shortlisted_history_30d_html(DUO_UI_STATE.get("last_shortlisted_history_30d") or [])
        .replace('id="history-30d"', 'id="history30dWorkspace"', 1)
        .replace('class="panel"', 'class="workspace-panel"', 1)
    )
    return f"""<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <title>Inswing ScreenSim</title>
    <style>
{FINVIZ_THEME_CSS}
        body {{ margin: 0; background: #f3f3f5; color: #22262f; font-family: var(--fv-font-sans); }}
        .header {{ display: grid; grid-template-columns: minmax(220px, 1fr) auto minmax(220px, 1fr); align-items: center; gap: 16px; padding: 3px 18px; background: #353945; color: white; position: sticky; top: 0; z-index: 2; border-bottom: 1px solid rgba(255,255,255,0.14); }}
        .brand {{ justify-self: start; display: flex; align-items: center; gap: 9px; min-width: 0; }}
        .brand::after {{ content: none; }}
        .brand-logo {{ display: block; width: 108px; height: 52px; object-fit: contain; border: 0; border-radius: 0; background: transparent; filter: brightness(0) invert(1); }}
        .brand-text {{ display: block; min-width: 0; }}
        .report-title {{ display: block; font-size: 14px; line-height: 1.1; font-weight: 600; letter-spacing: 0; white-space: nowrap; }}
        .report-subtitle {{ display: block; margin-top: 3px; color: rgba(255,255,255,0.72); font-size: 12px; line-height: 1.2; white-space: nowrap; }}
        .header-right {{ justify-self: end; display: inline-flex; align-items: center; gap: 14px; min-width: 0; }}
        .live-clock {{ justify-self: end; color: #ffffff; font-size: 12px; font-weight: 600; text-align: right; white-space: nowrap; }}
        .live-clock::before {{ content: none; }}
        .live-clock span {{ display: inline-block; width: 92px; margin-top: 3px; color: rgba(255,255,255,0.68); font-size: 13px; font-weight: 600; font-variant-numeric: tabular-nums; text-align: right; }}
        .tabs {{ display: inline-flex; gap: 4px; align-items: center; justify-self: center; border-radius: 999px; padding: 4px; background: rgba(255,255,255,0.13); border: 1px solid rgba(255,255,255,0.20); box-shadow: inset 0 1px 0 rgba(255,255,255,0.08); }}
        .tabs button {{ border: none; border-radius: 999px; background: transparent; color: rgba(255,255,255,0.76); padding: 10px 20px; font-size: 13.2px; font-weight: 700; white-space: nowrap; cursor: pointer; opacity: 1; transition: background 0.2s, color 0.2s, box-shadow 0.2s, transform 0.2s; }}
        .tabs button .tab-icon {{ display: inline-block; margin-right: 7px; color: currentColor; font-size: 15.8px; vertical-align: -1px; }}
        .tabs button:hover {{ background: rgba(255,255,255,0.06); color: #f2f4f3; transform: translateY(-1px); }}
        .tabs button.active {{ background: #ffffff; color: #22262f; box-shadow: 0 8px 18px rgba(0,0,0,0.22); font-weight: 800; }}
        .tabs button.active .tab-icon {{ color: currentColor; }}
        .tabs button:disabled, .tabs button.disabled-tab {{ color: rgba(255,255,255,0.34); cursor: not-allowed; box-shadow: none; }}
        body.dark-theme .header {{ grid-template-columns: minmax(220px, 1fr) auto minmax(220px, 1fr); gap: 16px; margin: 0; padding: 3px 18px; top: 0; border: 0; border-bottom: 1px solid #232927; border-radius: 0; align-items: center; }}
        body.dark-theme .brand {{ align-items: center; }}
        body.dark-theme .brand::after {{ content: ''; width: 1px; height: 42px; margin-left: 22px; background: linear-gradient(180deg, transparent, rgba(0,200,83,0.34), transparent); }}
        body.dark-theme .brand-logo {{ filter: brightness(0) saturate(100%) invert(77%) sepia(69%) saturate(814%) hue-rotate(359deg) brightness(101%) contrast(95%) drop-shadow(0 0 10px rgba(243,199,54,0.24)); }}
        body.dark-theme .report-title {{ font-weight: 700; color: #ffffff; line-height: 1.15; }}
        body.dark-theme .report-subtitle {{ margin-top: 5px; color: #ffffff; opacity: 0.82; line-height: 1.15; }}
        body.dark-theme .header-right {{ border-left: 1px solid rgba(0,200,83,0.22); padding-left: 24px; }}
        body.dark-theme .live-clock {{ color: #ffffff; font-weight: 800; display: inline-flex; align-items: center; gap: 12px; }}
        body.dark-theme .live-clock::before {{ content: '▣'; color: #ffffff; margin-right: 0; }}
        body.dark-theme .live-clock span {{ margin-left: 12px; color: #f8fafc; font-weight: 700; }}
        body.dark-theme .theme-switch {{ color: #ffffff; align-items: center; }}
        body.dark-theme .tabs {{ align-items: center; }}
        body.dark-theme .tabs button {{ color: rgba(255,255,255,0.82); display: inline-flex; align-items: center; }}
        body.dark-theme .tabs button .tab-icon {{ color: #ffffff; }}
        body.dark-theme .tabs button.active .tab-icon {{ color: #06130b; }}
        main {{ max-width: none; margin: 18px 28px 40px; padding: 0 16px; }}
        body.watchlist-mode {{ scroll-snap-type: y mandatory; }}
        body.watchlist-mode main {{ margin-top: 8px; margin-bottom: 0; box-sizing: border-box; }}
        .card {{ background: #ffffff; border: 1px solid #dedfe5; border-radius: 0; box-shadow: 0 14px 34px rgba(20,22,29,0.08); margin-bottom: 16px; overflow: hidden; }}
        .card h2 {{ margin: 0; padding: 10px 9px; background: linear-gradient(135deg, #353945, #4c5263); color: #ffffff; font-size: 12px; line-height: 1.2; font-weight: 600; }}
        .card-title-row {{ height: 34px; box-sizing: border-box; display: flex; align-items: center; justify-content: space-between; gap: 12px; margin: 0; padding: 0 9px; background: linear-gradient(135deg, #353945, #4c5263); color: #ffffff; }}
        .card-title-row h2 {{ margin: 0; padding: 0; background: none; }}
        .dashboard-ready {{ display: inline-flex; align-items: center; max-width: min(58vw, 640px); overflow: hidden; border: 1px solid #c3c6d0; border-radius: 999px; background: rgba(255,255,255,0.95); color: #22262f; padding: 5px 12px; font-size: 12px; font-weight: 700; text-decoration: none; white-space: nowrap; box-shadow: 0 5px 13px rgba(0,0,0,0.18); }}
        .dashboard-ready:hover {{ background: #f3f3f5; }}
        details.card summary {{ list-style: none; cursor: pointer; margin: 0; padding: 10px 9px; background: linear-gradient(135deg, #353945, #4c5263); color: #ffffff; font-size: 12px; line-height: 1.2; font-weight: 600; }}
        details.card summary::-webkit-details-marker {{ display: none; }}
        details.card:not([open]) > :not(summary) {{ display: none; }}
        details.card summary::after {{ content: 'Show filters'; float: right; font-size: 12px; opacity: 0.78; }}
        details.card[open] summary::after {{ content: 'Hide filters'; }}
        .form-grid {{ display: grid; grid-template-columns: 120px minmax(52px, 1fr) minmax(52px, 1fr) minmax(52px, 1fr) minmax(44px, 0.7fr) minmax(58px, 0.9fr) minmax(44px, 0.7fr) minmax(58px, 0.9fr) auto auto auto; column-gap: 6px; row-gap: 8px; padding: 10px 14px 12px; align-items: end; }}
        label {{ font-size: 12px; }}
        label span {{ display: block; color: #676f85; font-size: 9px; font-weight: 700; text-transform: uppercase; margin-bottom: 4px; white-space: nowrap; }}
        input[type="text"], input[type="date"] {{ width: 100%; height: 32px; box-sizing: border-box; border: 1px solid #c3c6d0; border-radius: 8px; padding: 4px 7px; font: inherit; font-size: 11px; font-weight: 600; color: #22262f; }}
        .checkbox-field {{ display: block; }}
        .checkbox-row {{ min-height: 32px; display: flex; align-items: center; gap: 6px; color: #22262f; font-size: 11px; font-weight: 500; line-height: 1.2; text-transform: none; white-space: nowrap; }}
        .checkbox-row input[type="checkbox"] {{ flex: none; margin: 0; }}
        .actions {{ display: flex; gap: 6px; align-items: end; padding: 0; white-space: nowrap; }}
        .primary {{ border: none; border-radius: 999px; background: #4c5263; color: #ffffff; height: 32px; padding: 0 12px; cursor: pointer; font-size: 11.5px; font-weight: 600; }}
        .actions .primary {{ width: auto; min-width: 105px; }}
        .actions .market-view-button,
        body.dark-theme .actions .market-view-button {{ background: linear-gradient(135deg, #f3c736, #d4af37); color: #111111; box-shadow: 0 6px 14px rgba(176,137,0,0.24); }}
        .actions .market-view-button:hover,
        body.dark-theme .actions .market-view-button:hover {{ background: linear-gradient(135deg, #ffd84d, #f3c736); color: #111111; }}
        .primary:disabled {{ opacity: 0.45; cursor: not-allowed; }}
        .screener-progress {{ grid-column: 1 / -1; display: none; padding: 6px 0 0; }}
        .sim-controls .screener-progress {{ padding-top: 2px; }}
        .screener-progress.running {{ display: block; }}
        .screener-progress-track {{ height: 10.5px; overflow: hidden; border: 1px solid #a3a8b9; border-radius: 2px; background: #dedfe5; box-shadow: inset 1px 1px 1px rgba(0,0,0,0.32), inset -1px -1px 1px rgba(255,255,255,0.78); }}
        .screener-progress-fill {{ width: 0%; height: 100%; border-radius: 1px; background: repeating-linear-gradient(90deg, #353945 0 8px, #dedfe5 8px 10px); transition: width 0.45s ease; }}
        .message {{ margin: 0 0 14px; padding: 12px 14px; border-radius: 12px; background: #fdf2df; color: #8b6a00; border: 1px solid #fcdc86; font-weight: 500; }}
        .message.success {{ background: #f3f3f5; color: #22262f; border-color: #c3c6d0; }}
        .result-toolbar {{ display: flex; justify-content: flex-end; gap: 10px; align-items: center; padding: 3px 18px; background: #f3f3f5; border-top: 1px solid #dedfe5; border-bottom: 1px solid #c3c6d0; box-shadow: inset 0 1px 0 rgba(255,255,255,0.75); }}
        .selection-count {{ color: #22262f; font-size: 12px; font-weight: 700; white-space: nowrap; }}
        .pagination {{ display: inline-flex; gap: 8px; align-items: center; color: #22262f; font-size: 11.7px; font-weight: 600; white-space: nowrap; }}
        .secondary {{ border: 1px solid #c3c6d0; border-radius: 999px; background: #ffffff; color: #22262f; padding: 4px 10px; cursor: pointer; font-size: 10.8px; font-weight: 700; }}
        .secondary:disabled {{ opacity: 0.45; cursor: not-allowed; }}
        .table-wrap {{ overflow: auto; max-height: 55vh; border-top: 1px solid #dedfe5; }}
        table {{ width: 100%; border-collapse: collapse; font-size: 12px; }}
        th {{ position: sticky; top: 0; background: #4c5263; color: #ffffff; padding: 8px 9px; text-align: center; vertical-align: middle; white-space: nowrap; cursor: pointer; user-select: none; }}
        th:first-child, td:first-child {{ text-align: center; }}
        /* Sort indicator: CSS triangle (no font glyph metrics to fight) that
           always reserves its slot, so toggling direction never shifts the label. */
        th.sortable .th-inner {{ display: inline-flex; align-items: center; justify-content: center; gap: 5px; line-height: 1; }}
        th.sortable .sort-arrow {{ width: 0; height: 0; flex: none; border-left: 3.5px solid transparent; border-right: 3.5px solid transparent; border-bottom: 4.5px solid currentColor; opacity: 0; transition: opacity 0.15s ease, transform 0.15s ease; }}
        th.sortable:hover .sort-arrow {{ opacity: 0.4; }}
        th.sortable.sort-asc .sort-arrow, th.sortable.sort-desc .sort-arrow {{ opacity: 1; }}
        th.sortable.sort-desc .sort-arrow {{ transform: rotate(180deg); }}
        th:first-child, td:first-child {{ width: 70px; text-align: center; }}
        th:nth-child(2), td:nth-child(2) {{ text-align: center; }}
        td {{ border-top: 1px solid #dedfe5; padding: 4.5px 9px; text-align: center; vertical-align: middle; white-space: nowrap; }}
        th.screener-col-daily-change, td.screener-col-daily-change {{ width: 1%; min-width: 58px; padding-left: 3px; padding-right: 3px; }}
        th.screener-col-drop-from-high, td.screener-col-drop-from-high {{ width: 1%; min-width: 65px; padding-left: 3px; padding-right: 3px; }}
        th.screener-col-daily-closing-position, td.screener-col-daily-closing-position {{ width: 1%; min-width: 96px; padding-left: 5px; padding-right: 5px; }}
        th.screener-col-macd-pct, td.screener-col-macd-pct {{ width: 1%; min-width: 60px; padding-left: 3px; padding-right: 3px; }}
        th.screener-col-hist-pct, td.screener-col-hist-pct {{ width: 1%; min-width: 60px; padding-left: 3px; padding-right: 3px; }}
        td input[type="checkbox"] {{ vertical-align: middle; }}
        td.daily-change-positive {{ color: green; font-weight: 600; }}
        td.daily-change-negative {{ color: red; font-weight: 600; }}
        td[class*="screener-change-"], td[class*="screener-drop-"], td[class*="screener-rvol-"], td[class*="screener-position-"], td[class*="screener-comment-"] {{ font-weight: 700; }}
        td.screener-change-pos-1 {{ background: #dcfce7; color: #166534; }}
        td.screener-change-pos-2 {{ background: #86efac; color: #14532d; }}
        td.screener-change-pos-3 {{ background: #22c55e; color: #052e16; }}
        td.screener-change-pos-4 {{ background: #16a34a; color: #ffffff; }}
        td.screener-change-pos-5 {{ background: #15803d; color: #ffffff; }}
        td.screener-change-neg-1 {{ background: #fee2e2; color: #991b1b; }}
        td.screener-change-neg-2 {{ background: #fecaca; color: #7f1d1d; }}
        td.screener-change-neg-3 {{ background: #fca5a5; color: #7f1d1d; }}
        td.screener-change-neg-4 {{ background: #ef4444; color: #ffffff; }}
        td.screener-change-neg-5 {{ background: #b91c1c; color: #ffffff; }}
        td.screener-drop-1 {{ background: #fee2e2; color: #991b1b; }}
        td.screener-drop-2 {{ background: #fecaca; color: #7f1d1d; }}
        td.screener-drop-3 {{ background: #fca5a5; color: #7f1d1d; }}
        td.screener-drop-4 {{ background: #ef4444; color: #ffffff; }}
        td.screener-drop-5 {{ background: #b91c1c; color: #ffffff; }}
        td.screener-rvol-1 {{ background: #dbeafe; color: #1e3a5f; }}
        td.screener-rvol-2 {{ background: #bfdbfe; color: #1e3a5f; }}
        td.screener-rvol-3 {{ background: #60a5fa; color: #0f172a; }}
        td.screener-rvol-4 {{ background: #2563eb; color: #ffffff; }}
        td.screener-rvol-5 {{ background: #1e40af; color: #ffffff; }}
        td.screener-position-pos-1 {{ background: #dcfce7; color: #166534; }}
        td.screener-position-pos-2 {{ background: #86efac; color: #14532d; }}
        td.screener-position-pos-3 {{ background: #22c55e; color: #052e16; }}
        td.screener-position-pos-4 {{ background: #16a34a; color: #ffffff; }}
        td.screener-position-pos-5 {{ background: #15803d; color: #ffffff; }}
        td.screener-position-neg-1 {{ background: #fee2e2; color: #991b1b; }}
        td.screener-position-neg-2 {{ background: #fecaca; color: #7f1d1d; }}
        td.screener-position-neg-3 {{ background: #fca5a5; color: #7f1d1d; }}
        td.screener-position-neg-4 {{ background: #ef4444; color: #ffffff; }}
        td.screener-position-neg-5 {{ background: #b91c1c; color: #ffffff; }}
        td.screener-bool-yes {{ color: #16a34a; font-weight: 800; }}
        td.screener-bool-no {{ color: #dc2626; font-weight: 800; }}
        td.screener-comment-below {{ background: #e5e7eb; color: #4b5563; }}
        td.screener-comment-5d {{ background: #d9f99d; color: #365314; }}
        td.screener-comment-10d {{ background: #bef264; color: #365314; }}
        td.screener-comment-1m {{ background: #86efac; color: #14532d; }}
        td.screener-comment-2m {{ background: #34d399; color: #064e3b; }}
        td.screener-comment-3m {{ background: #2dd4bf; color: #134e4a; }}
        td.screener-comment-6m {{ background: #059669; color: #ffffff; }}
        td.screener-comment-1y {{ background: #f3c736; color: #422006; }}
        td.screener-momentum-positive, td.screener-rsi-pos-1 {{ color: #16a34a; font-weight: 700; }}
        td.screener-momentum-negative, td.screener-rsi-neg-1 {{ color: #dc2626; font-weight: 700; }}
        td.screener-rsi-pos-2 {{ color: #15803d; font-weight: 800; }}
        td.screener-rsi-pos-3 {{ color: #166534; font-weight: 900; }}
        td.screener-rsi-neg-2 {{ color: #b91c1c; font-weight: 800; }}
        td.screener-rsi-neg-3 {{ color: #7f1d1d; font-weight: 900; }}
        td.screener-comment-ath {{ color: #19803d; font-weight: 600; }}
        .ticker-chart-link {{ border: none; background: transparent; color: #306dca; cursor: pointer; padding: 0; font: inherit; font-weight: 600; text-decoration: none; }}
        .ticker-chart-link:hover {{ color: #2f91ef; text-decoration: underline; }}
        .chart-modal {{ position: fixed; inset: 0; display: none; align-items: center; justify-content: center; padding: 28px; background: rgba(20,22,29,0.62); z-index: 20; }}
        .chart-modal.open {{ display: flex; }}
        .chart-modal-card {{ width: min(1180px, 96vw); max-height: 92vh; overflow: auto; border-radius: 16px; background: #ffffff; box-shadow: 0 24px 70px rgba(0,0,0,0.35); border: 1px solid #c3c6d0; }}
        .chart-modal-header {{ display: flex; align-items: center; justify-content: space-between; gap: 12px; padding: 12px 16px; background: #353945; color: #ffffff; font-weight: 700; }}
        .chart-modal-close {{ border: none; border-radius: 999px; background: rgba(255,255,255,0.12); color: #ffffff; width: 32px; height: 32px; cursor: pointer; font-size: 18px; font-weight: 700; }}
        .chart-modal-body {{ padding: 14px; text-align: center; }}
        .chart-modal-body img {{ max-width: 100%; height: auto; border: 1px solid #dedfe5; border-radius: 10px; background: #ffffff; }}
        .sim-controls {{ display: grid; grid-template-columns: 155px 180px 170px minmax(260px, 1fr) 162px; column-gap: 10px; row-gap: 5px; padding: 5px 14px 7px; align-items: end; background: #ffffff; border-bottom: 1px solid #dedfe5; }}
        .sim-controls label span {{ font-size: 10px; font-weight: 600; text-transform: none; margin-bottom: 2px; }}
        .entry-date-text {{ padding: 1px 0; font-size: 12px; font-weight: 600; color: #22262f; }}
        .sim-search {{ grid-column: 2; align-self: center; width: 100%; justify-self: stretch; }}
        .sim-search input {{ width: 100%; height: 36px; box-sizing: border-box; border: 1px solid #7c8397; border-radius: 999px; background: #676f85 url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='16' height='16' viewBox='0 0 24 24' fill='none' stroke='%23dedfe5' stroke-width='2.2' stroke-linecap='round'%3E%3Ccircle cx='11' cy='11' r='7'/%3E%3Cpath d='m20 20-4.3-4.3'/%3E%3C/svg%3E") no-repeat 12px 50%; color: #f3f3f5; padding: 0 12px 0 34px; font-size: 12px; font-weight: 500; text-align: left; outline: none; }}
        .sim-search input::placeholder {{ color: #f3f3f5; font-weight: 600; opacity: 1; }}
        .sim-search input:focus {{ border-color: #c3c6d0; box-shadow: 0 0 0 3px rgba(103,111,133,0.30); }}
        .sim-search input::-webkit-search-cancel-button {{ filter: invert(1) brightness(1.6); cursor: pointer; }}
        .refine-inline-control {{ grid-column: 3; align-self: center; }}
        .refine-inline-button {{ width: 100%; height: 36px; border: 1px solid #c3c6d0; border-radius: 999px; background: #ffffff; color: #22262f; font-size: 11px; font-weight: 700; cursor: pointer; display: inline-flex; align-items: center; justify-content: center; gap: 7px; }}
        .refine-inline-button:disabled {{ opacity: 0.45; cursor: not-allowed; }}
        .refine-inline-count {{ min-width: 18px; height: 18px; border-radius: 999px; background: #353945; color: #ffffff; font-size: 10px; font-weight: 700; display: inline-flex; align-items: center; justify-content: center; padding: 0 4px; }}
        .selected-stock-summary {{ grid-column: 4; align-self: center; height: 36px; box-sizing: border-box; display: flex; align-items: center; justify-content: center; border-radius: 999px; background: #f3f3f5; color: #4c5263; padding: 0 10px; font-size: 12px; font-weight: 600; text-align: center; transition: background 0.2s, color 0.2s; }}
        .selected-stock-summary.has-selection {{ background: #353945; color: #ffffff; }}
        .sim-controls .actions {{ grid-column: 5; align-self: center; }}
        .sim-controls .actions .primary {{ height: 36px; padding-top: 0; padding-bottom: 0; }}
        .watchlist-section {{ display: none; }}
        .watchlist-section.show {{ display: block; }}
        .watchlist-card {{ margin: 0; display: flex; flex-direction: column; overflow: hidden; background: #ffffff; height: calc(100vh - 102px); min-height: 0; }}
        .watchlist-card-title-row {{ height: 34px; min-height: 34px; max-height: 34px; box-sizing: border-box; display: flex; align-items: center; justify-content: space-between; gap: 10px; padding: 0 9px; background: linear-gradient(135deg, #353945, #4c5263); color: #ffffff; }}
        .watchlist-card-title-row .watchlist-card-title {{ margin: 0; padding: 0; background: transparent; color: #ffffff; font-size: 12px; line-height: 1.2; font-weight: 600; }}
        .watchlist-title-tools {{ display: inline-flex; align-items: center; gap: 12px; min-width: 0; }}
        .watchlist-header-controls {{ display: inline-flex; align-items: center; gap: 8px; min-width: 0; flex-wrap: wrap; justify-content: flex-end; }}
        .watchlist-card-title-row .dashboard-ready {{ max-width: min(32vw, 420px); }}
        .watchlist-head {{ display: none; }}
        .watchlist-title {{ color: #22262f; font-size: 12px; font-weight: 700; }}
        .watchlist-summary {{ color: #4c5263; font-size: 11px; font-weight: 600; }}
        .watchlist-layout {{ display: grid; grid-template-columns: 100px minmax(0, 1fr); gap: 0; flex: 1; min-height: 0; }}
        .watchlist-table-wrap {{ border-right: 1px solid #dedfe5; overflow: auto; min-height: 0; }}
        .watchlist-table {{ width: 100%; border-collapse: collapse; font-size: 11px; }}
        .watchlist-table th {{ position: sticky; top: 0; z-index: 1; height: 34px; box-sizing: border-box; background: #ffffff; color: #353945; padding: 0 7px; text-align: center; vertical-align: middle; white-space: nowrap; font-size: 10px; }}
        .watchlist-table th:first-child,
        .watchlist-table td:first-child {{ width: 40px; padding-left: 4px; padding-right: 4px; }}
        .watchlist-table th:nth-child(2),
        .watchlist-table td:nth-child(2) {{ text-align: left; padding-left: 0; }}
        .watchlist-table td {{ border-top: 1px solid #dedfe5; padding: 4px 7px; text-align: center; vertical-align: middle; white-space: nowrap; }}
        .watchlist-ticker-btn {{ border: none; background: transparent; color: #306dca; cursor: pointer; font: inherit; font-weight: 700; padding: 0; text-decoration: none; }}
        .watchlist-ticker-btn:hover {{ text-decoration: underline; color: #2f91ef; }}
        .watchlist-ticker-btn.active {{ color: #d91e2b; }}
        .watchlist-chart-area {{ display: flex; flex-direction: column; min-height: 0; }}
        .watchlist-chart-toolbar {{ display: flex; align-items: center; justify-content: space-between; gap: 8px; padding: 3px 8px; min-height: 32px; box-sizing: border-box; border-bottom: 1px solid #dedfe5; background: #f8fafc; }}
        .watchlist-legend-host {{ display: flex; align-items: center; gap: 6px; flex: 1; min-width: 0; overflow: hidden; }}
        .watchlist-forward-toggle {{ display: inline-flex; align-items: center; gap: 6px; color: #353945; font-size: 10.5px; font-weight: 800; white-space: nowrap; cursor: pointer; user-select: none; }}
        .watchlist-forward-toggle input {{ margin: 0; }}
        .watchlist-chart-body {{ flex: 1; min-height: 0; display: flex; align-items: flex-start; justify-content: center; background: #ffffff; overflow: auto; }}
        .watchlist-chart-area.dark-chart .watchlist-chart-body {{ background: #1b202b; color: #e5e7eb; border-color: #303746; }}
        .watchlist-chart-placeholder {{ color: #676f85; font-size: 12px; font-weight: 600; text-align: center; padding: 16px; }}
        .watchlist-chart-image {{ display: none; width: 100%; height: auto; max-width: none; object-fit: contain; object-position: top center; }}
        .watchlist-chart-canvas {{ display: none; flex: 1 1 auto; align-self: stretch; width: 100%; min-height: 300px; }}
        .watchlist-run-button {{ --run-progress: 0%; min-width: 190px; height: 28px; border: 0; border-radius: 999px; background: #d4af37; color: #111111; font-size: 12px; font-weight: 700; cursor: pointer; overflow: hidden; transition: background 0.2s, color 0.2s, box-shadow 0.2s, transform 0.2s; }}
        .watchlist-run-button:disabled {{ background: #d9dce6; color: #5b637a; opacity: 1; cursor: not-allowed; }}
        .watchlist-run-button.processing,
        .watchlist-run-button.processing:disabled {{ background: linear-gradient(90deg, #d4af37 0 var(--run-progress), #d9dce6 var(--run-progress) 100%); color: #22262f; cursor: wait; }}
        body.simulator-busy, body.simulator-busy * {{ cursor: wait !important; }}
        .busy-click-shield {{ position: fixed; inset: 0; z-index: 9998; cursor: wait; background: transparent; }}
        .watchlist-run-button.report-ready {{ min-width: 220px; border: 1px solid rgba(255,255,255,0.55); background: linear-gradient(135deg, #f7d86b, #d4af37); color: #111111; box-shadow: 0 6px 16px rgba(0,0,0,0.22), inset 0 1px 0 rgba(255,255,255,0.45); }}
        .watchlist-run-button.report-ready::after {{ content: '  Open'; opacity: 0.78; font-size: 10px; font-weight: 800; text-transform: uppercase; letter-spacing: 0.04em; }}
        .watchlist-run-button.report-ready:hover {{ background: linear-gradient(135deg, #ffe88a, #d4af37); transform: translateY(-1px); box-shadow: 0 8px 20px rgba(0,0,0,0.26), inset 0 1px 0 rgba(255,255,255,0.52); }}
        .watchlist-selection-status {{ color: #ffffff; font-size: 11px; font-weight: 700; }}
        .watchlist-header-controls.is-processing .watchlist-selection-status,
        .watchlist-header-controls.is-processing .watchlist-run-status {{ display: none; }}
        .watchlist-run-status {{ color: rgba(255,255,255,0.86); font-size: 11px; font-weight: 700; }}
        .watchlist-run-status.running {{ color: #b68900; }}
        body.watchlist-mode #screenerResultsCard,
        body.watchlist-mode #watchlistSectionCard {{ scroll-snap-align: start; scroll-margin-top: 76px; }}
        .refine-card {{ margin-top: 9px; position: relative; z-index: 12; overflow: visible; }}
        .refine-card summary {{ display: flex; align-items: center; gap: 8px; }}
        .refine-card summary::after {{ display: none; content: none; }}
        .refine-summary-count {{ min-width: 18px; height: 18px; border-radius: 999px; background: rgba(255,255,255,0.18); color: #ffffff; font-size: 10px; font-weight: 700; display: inline-flex; align-items: center; justify-content: center; padding: 0 5px; }}
        .refine-summary-toggle {{ margin-left: auto; font-size: 12px; opacity: 0.78; }}
        .refine-summary-toggle::before {{ content: 'Show results'; }}
        details.refine-card[open] .refine-summary-toggle::before {{ content: 'Hide results'; }}
        .refine-body {{ padding: 6px 8px 8px; background: #ffffff; border-top: 1px solid #dedfe5; overflow: visible; }}
        .refine-grid-scroll {{ overflow-x: auto; overflow-y: visible; padding-bottom: 0; }}
        .refine-grid {{ display: flex; flex-wrap: nowrap; align-items: flex-end; gap: 4px; min-width: 0; }}
        .refine-control {{ border: 0; border-radius: 0; padding: 0; background: transparent; min-width: 50px; flex: 1 1 54px; }}
        .refine-label {{ display: block; color: #676f85; font-size: 8.5px; font-weight: 700; text-transform: uppercase; margin-bottom: 3px; letter-spacing: 0.1px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }}
        .refine-num-row {{ display: grid; grid-template-columns: 1fr; gap: 4px; }}
        .refine-num-row input {{ width: 100%; height: 26px; box-sizing: border-box; border: 1px solid #c3c6d0; border-radius: 6px; padding: 2px 4px; font-size: 9.5px; font-weight: 600; color: #22262f; background: #ffffff; }}
        .refine-string-wrap {{ position: relative; }}
        .refine-string-btn {{ width: 100%; height: 26px; box-sizing: border-box; border: 1px solid #c3c6d0; border-radius: 6px; background: #ffffff; color: #22262f; padding: 2px 4px; font-size: 9.5px; font-weight: 600; text-align: left; cursor: pointer; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }}
        .refine-string-panel {{ position: fixed; z-index: 9999; min-width: 150px; width: 180px; max-width: 200px; border: 1px solid #c3c6d0; border-radius: 4px; background: #ffffff; box-shadow: 0 8px 18px rgba(20,22,29,0.20); padding: 0; display: none; }}
        .refine-string-panel[data-refine-key="PPO_GT_SIGNAL"] {{ min-width: 140px; width: 150px; max-width: 150px; }}
        .refine-string-panel.is-open {{ display: block; }}
        .refine-string-select-all-row {{ padding: 4px 6px; border-bottom: 1px solid #dedfe5; }}
        .refine-string-options {{ max-height: 156px; overflow-y: auto; overflow-x: hidden; padding: 4px 6px; }}
        .refine-string-opt {{ display: flex; align-items: flex-start; gap: 7px; padding: 3px 2px; color: #22262f; font-size: 11px; font-weight: 600; white-space: normal; line-height: 1.25; cursor: pointer; user-select: none; }}
        .refine-string-opt input {{ cursor: pointer; margin-top: 1px; }}
        .refine-string-clear {{ width: 100%; border: 0; border-top: 1px solid #dedfe5; background: #ffffff; color: #4c5263; cursor: pointer; font-size: 11px; font-weight: 700; padding: 6px 8px; text-align: left; }}
        .refine-actions-row {{ display: flex; justify-content: space-between; align-items: center; gap: 8px; margin-top: 8px; flex-wrap: wrap; }}
        .refine-active-row {{ display: flex; align-items: center; gap: 6px; flex-wrap: wrap; color: #4c5263; font-size: 11px; font-weight: 700; }}
        .refine-active-list {{ display: flex; align-items: center; gap: 6px; flex-wrap: wrap; }}
        .refine-chip {{ display: inline-flex; align-items: center; border: 1px solid #c3c6d0; border-radius: 999px; background: #f3f3f5; color: #22262f; font-size: 10px; font-weight: 700; padding: 3px 8px; }}
        .refine-link-clear {{ border: 0; background: transparent; color: #306dca; cursor: pointer; font-size: 11px; font-weight: 700; padding: 0; }}
        .refine-action-buttons {{ display: inline-flex; align-items: center; gap: 8px; }}
        .refine-action-buttons button {{ border-radius: 999px; padding: 6px 12px; font-size: 11px; font-weight: 700; cursor: pointer; }}
        .refine-action-buttons .refine-clear-btn {{ border: 1px solid #c3c6d0; background: #ffffff; color: #22262f; }}
        .refine-action-buttons .refine-apply-btn {{ border: none; background: #306dca; color: #ffffff; }}
        .refine-empty-note {{ color: #676f85; font-size: 12px; font-weight: 600; }}
        .workspace-panel {{ display: none; }}
        .workspace-panel.active {{ display: block; }}
        .saved-reports-panel {{ max-width: 1280px; margin: 0 auto; }}
        .saved-report-section {{ margin-bottom: 22px; border: 1px solid #dedfe5; border-radius: 16px; overflow: hidden; background: #ffffff; box-shadow: 0 14px 34px rgba(20,22,29,0.08); }}
        .saved-report-section h1 {{ margin: 0; padding: 13px 18px; background: linear-gradient(135deg, #353945, #4c5263); color: #ffffff; font-size: 14px; }}
        .grid {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(330px, 1fr)); gap: 12px; padding: 14px; }}
        .report-card {{ background: #ffffff; border: 1px solid #dedfe5; border-radius: 14px; padding: 14px; box-shadow: 0 6px 18px rgba(20,22,29,0.06); }}
        .report-top {{ display: flex; align-items: flex-start; justify-content: space-between; gap: 12px; }}
        .report-card h2 {{ margin: 0; color: #22262f; font-size: 15px; }}
        .report-card p {{ margin: 5px 0 0; color: #676f85; font-size: 11px; font-weight: 600; }}
        .badge {{ border-radius: 999px; padding: 4px 10px; font-size: 11px; font-weight: 700; white-space: nowrap; }}
        .badge.live {{ background: #f3f3f5; color: #353945; border: 1px solid #c3c6d0; }}
        .badge.muted {{ background: #f3f3f5; color: #676f85; border: 1px solid #dedfe5; }}
        .status {{ margin-top: 12px; color: #22262f; font-size: 13px; font-weight: 700; }}
        .dates {{ margin-top: 5px; color: #676f85; font-size: 11px; font-weight: 600; }}
        .report-card .actions {{ display: flex; flex-wrap: wrap; gap: 8px; margin-top: 13px; }}
        .open {{ display: inline-flex; align-items: center; justify-content: center; border-radius: 999px; background: #4c5263; color: #ffffff; padding: 8px 13px; text-decoration: none; font-size: 12px; font-weight: 700; }}
        .open.live-action {{ background: #353945; color: #ffffff; }}
        .empty {{ padding: 18px; color: #676f85; font-size: 13px; font-weight: 600; }}
        .history-panel {{ max-width: 1380px; margin: 0 auto 26px; }}
        .history-title {{ display: flex; align-items: end; justify-content: space-between; gap: 12px; padding: 14px 18px; border-radius: 14px 14px 0 0; background: linear-gradient(135deg, #353945, #4c5263); color: #ffffff; }}
        .history-title h2 {{ margin: 0; font-size: 15px; }}
        .history-title p {{ margin: 0; color: rgba(255,255,255,0.76); font-size: 12px; font-weight: 600; }}
        .history-grid {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(310px, 1fr)); gap: 12px; padding: 14px; background: #ffffff; border: 1px solid #dedfe5; border-top: 0; border-radius: 0 0 14px 14px; box-shadow: 0 14px 34px rgba(20,22,29,0.08); }}
        .history-card {{ border: 1px solid #dedfe5; border-radius: 14px; background: #ffffff; padding: 13px 14px; box-shadow: 0 6px 16px rgba(20,22,29,0.06); }}
        .history-card-head {{ display: flex; align-items: center; justify-content: space-between; gap: 10px; }}
        .history-ticker {{ color: #306dca; font-size: 14px; }}
        .history-change {{ padding: 4px 10px; border-radius: 999px; color: #ffffff; font-size: 12px; font-weight: 700; font-variant-numeric: tabular-nums; }}
        .history-change.up {{ background: #00a449; }}
        .history-change.down {{ background: #d91e2b; }}
        .history-date {{ margin-top: 7px; color: #676f85; font-size: 11px; font-weight: 600; }}
        .history-range {{ position: relative; height: 12px; margin: 16px 2px 12px; border-radius: 999px; background: linear-gradient(90deg, #fbb4b4, #fdf2df 50%, #beeac1); box-shadow: inset 0 1px 2px rgba(20,22,29,0.18); }}
        .history-marker {{ position: absolute; top: 50%; width: 10px; height: 10px; transform: translate(-50%, -50%); border-radius: 50%; border: 2px solid #ffffff; box-shadow: 0 1px 4px rgba(20,22,29,0.34); }}
        .history-marker.entry {{ background: #4c5263; }}
        .history-marker.last {{ background: #f3c736; }}
        .history-values {{ display: grid; grid-template-columns: repeat(4, 1fr); gap: 6px; }}
        .history-values span {{ display: block; padding: 7px 6px; border-radius: 10px; background: #f3f3f5; color: #22262f; font-size: 11px; font-weight: 700; text-align: center; font-variant-numeric: tabular-nums; }}
        .history-values em {{ display: block; margin-bottom: 2px; color: #676f85; font-size: 9px; font-style: normal; text-transform: uppercase; }}
        .history-footer {{ display: flex; justify-content: space-between; gap: 8px; margin-top: 10px; color: #4c5263; font-size: 11px; font-weight: 600; }}
        .history-empty {{ max-width: 720px; margin: 24px auto; padding: 18px; border: 1px solid #dedfe5; border-radius: 14px; background: #ffffff; color: #676f85; font-size: 13px; font-weight: 600; text-align: center; }}
        @media (max-width: 1100px) {{ .form-grid {{ grid-template-columns: repeat(4, minmax(130px, 1fr)); }} }}
        @media (max-width: 850px) {{ .header {{ grid-template-columns: 1fr; gap: 12px; padding: 12px 16px; }} .tabs, .live-clock {{ justify-self: start; }} .live-clock, .live-clock span {{ text-align: left; }} .form-grid, .sim-controls {{ grid-template-columns: 1fr; }} .refine-grid {{ flex-wrap: wrap; }} .refine-control {{ min-width: 120px; max-width: none; }} .watchlist-card {{ height: auto; }} .watchlist-card-title-row {{ align-items: flex-start; }} .watchlist-header-controls {{ width: 100%; justify-content: flex-start; }} .watchlist-layout {{ grid-template-columns: 1fr; height: auto; min-height: 0; }} .watchlist-table-wrap {{ border-right: 0; border-bottom: 1px solid #dedfe5; max-height: 260px; }} }}
    </style>
</head>
<body>
{DUO_THEME_BOOT_SCRIPT}
    <div class="header">
        <div class="brand">
            {header_logo_html}
            <span class="brand-text">
                <strong class="report-title">Inswing ScreenSim</strong>
                <span class="report-subtitle">Screening and simulation review</span>
            </span>
        </div>
        <div class="tabs">
            <button class="active" type="button" onclick="window.location.href='/?reset=screener'"><span class="tab-icon">⌁</span>Screener</button>
            <button class="{report_button_class}" type="button" onclick="{report_tab_action}"{report_button_disabled}><span class="tab-icon">◔</span>Portfolio</button>
            <button class="{report_button_class}" type="button" onclick="showMainPanel('history30dWorkspace', this)"{report_button_disabled}><span class="tab-icon">⬡</span>30D Follow-Through</button>
            <button type="button" onclick="showMainPanel('savedReportsPanel', this)"><span class="tab-icon">▱</span>Saved Reports</button>
        </div>
        <span class="header-right">
            <span class="live-clock" id="liveClockDate">--<span id="liveClockTime">--</span></span>
{DUO_THEME_TOGGLE_HTML}
        </span>
    </div>
    <main>
        <section id="screenerWorkspace" class="workspace-panel active">
        {f'<div class="message">{message}</div>' if message else ''}
        <details class="card" id="dailyScreenerDetails"{filter_panel_open}>
            <summary>Daily Screener</summary>
            <form method="post" action="/run-screener" id="screenerForm">
                <div class="form-grid">
                    <label><span>Anchor Date</span><input type="date" id="anchorDateInput" name="anchor_date" value="{html.escape(default_anchor)}" max="{html.escape(today_et)}"></label>
                    <label><span>MCAP Min</span><input type="text" name="mcap_min" value="{html.escape(filter_values['mcap_min'])}"></label>
                    <label><span>MCAP Max</span><input type="text" name="mcap_max" value="{html.escape(filter_values['mcap_max'])}"></label>
                    <label><span>Min Volume</span><input type="text" name="min_volume" value="{html.escape(filter_values['min_volume'])}"></label>
                    <label><span>Min Price</span><input type="text" name="min_price" value="{html.escape(filter_values['min_price'])}"></label>
                    <label><span>10D Velocity %</span><input type="text" name="min_atr10" value="{html.escape(filter_values['min_atr10'])}"></label>
                    <label><span>RSI14</span><input type="text" name="min_rsi14" value="{html.escape(filter_values['min_rsi14'])}"></label>
                    <label class="checkbox-field"><span>MACD Filter</span><span class="checkbox-row"><input type="checkbox" name="require_macd_gt_signal" value="1"{macd_checked}> MACD &gt; Signal</span></label>
                    <label class="checkbox-field"><span>MACD Cross</span><span class="checkbox-row"><input type="checkbox" name="require_macd_cross" value="1"{macd_cross_checked}> Yes</span></label>
                    <div class="actions"><button class="primary market-view-button" id="marketViewButton" type="button">Market View</button><button class="primary" id="runScreenerButton" type="submit">Run Screener</button></div>
                    <div class="screener-progress" id="screenerProgress" role="status" aria-live="polite" aria-label="Screener progress">
                        <div class="screener-progress-track" aria-hidden="true"><div class="screener-progress-fill" id="screenerProgressFill"></div></div>
                    </div>
                </div>
            </form>
        </details>
        <details class="card refine-card" id="refineResultsDetails"{refine_panel_open}>
            <summary>Refine Results <span class="refine-summary-count" id="refineSummaryCount">0</span><span class="refine-summary-toggle" aria-hidden="true"></span></summary>
            <div class="refine-body">
                <div class="refine-grid-scroll">
                    <div class="refine-grid" id="refineFiltersGrid"></div>
                </div>
                <div class="refine-actions-row">
                    <div class="refine-active-row">
                        <span>Active Filters:</span>
                        <div class="refine-active-list" id="refineActiveList"></div>
                        <button type="button" class="refine-link-clear" id="refineInlineClearButton">Clear all</button>
                    </div>
                    <div class="refine-action-buttons">
                        <button type="button" class="refine-clear-btn" id="refineClearButton">Clear all</button>
                        <button type="button" class="refine-apply-btn" id="refineApplyButton">Apply Filters</button>
                    </div>
                </div>
            </div>
        </details>
        <section class="card" id="screenerResultsCard">
            <div class="card-title-row">
                <h2 id="screenerResultsTitle">{screener_results_title}</h2>
            </div>
            <div>
                <div class="sim-controls">
                    <label><span>Entry date (T-0)</span><div class="entry-date-text" id="entryDateDisplay">{html.escape(display_entry_date)}</div></label>
                    <div class="sim-search"><input id="screenerSearch" type="search" placeholder="Search ticker" aria-label="Search screener rows"></div>
                    <div class="refine-inline-control">
                        <button type="button" class="refine-inline-button" id="refineInlineButton">Refine Results <span class="refine-inline-count" id="refineInlineCount">0</span></button>
                    </div>
                    <div class="selected-stock-summary" id="selectedStockSummary">Selected for Watchlist: 0</div>
                    <div class="actions"><button class="primary" id="addWatchlistButton" type="button">Add Watchlist</button></div>
                </div>
                <div class="result-toolbar">
                    <span class="pagination">
                        <button class="secondary" type="button" id="prevPage">Prev</button>
                        <span id="pageInfo">Page 0 of 0</span>
                        <button class="secondary" type="button" id="nextPage">Next</button>
                    </span>
                </div>
                <div class="table-wrap">
                    <table id="screenerTable">
                        <thead id="screenerTableHead"></thead>
                        <tbody id="screenerTableBody"></tbody>
                    </table>
                </div>
            </div>
        </section>
        <section class="card watchlist-section" id="watchlistSectionCard">
            <form method="post" action="/run-simulator" id="watchlistSimulatorForm">
                <div id="selectedTickerInputs"></div>
                <section class="watchlist-card" id="watchlistCard">
                    <div class="watchlist-card-title-row">
                        <div class="watchlist-title-tools">
                            <h2 class="watchlist-card-title" id="watchlistCardTitle">Watchlist (0 stocks)</h2>
                        </div>
                        <div class="watchlist-header-controls">
                            <span class="watchlist-selection-status" id="watchlistSelectionStatus">Select stocks (max 20)</span>
                            <span class="watchlist-run-status" id="watchlistRunStatus"></span>
                            <button class="{dashboard_button_class}" id="runSimulatorButton" type="{dashboard_button_type}" data-report-ready="{dashboard_button_ready}"{run_simulator_disabled}>{dashboard_button_label}</button>
                            <span id="watchlistDashboardReadySlot" hidden></span>
                        </div>
                    </div>
                    <div class="watchlist-layout">
                        <div class="watchlist-table-wrap">
                            <table class="watchlist-table" id="watchlistTable">
                                <thead>
                                    <tr><th><input type="checkbox" data-watchlist-select-all aria-label="Select all watchlist stocks"></th><th>Ticker</th></tr>
                                </thead>
                                <tbody id="watchlistTableBody"></tbody>
                            </table>
                        </div>
                        <div class="watchlist-chart-area">
                            <div class="watchlist-chart-toolbar">
                                <div class="watchlist-legend-host" id="watchlistLegendHost"></div>
                                <label class="watchlist-forward-toggle"><input id="watchlistForwardToggle" type="checkbox"> Forward View</label>
                            </div>
                            <div class="watchlist-chart-body">
                                <div class="watchlist-chart-placeholder" id="watchlistChartPlaceholder">Click a ticker in Watchlist to preview chart.</div>
                                <div class="watchlist-chart-canvas" id="watchlistChartCanvas"></div>
                            </div>
                        </div>
                    </div>
                </section>
            </form>
        </section>
        </section>
        <section id="savedReportsPanel" class="workspace-panel saved-reports-panel">
{saved_reports_panel_html}
        </section>
{history_workspace_html}
    </main>
    <div class="chart-modal" id="tickerChartModal" aria-hidden="true">
        <div class="chart-modal-card" role="dialog" aria-modal="true" aria-labelledby="tickerChartTitle">
            <div class="chart-modal-header">
                <span id="tickerChartTitle">Daily chart</span>
                <button class="chart-modal-close" type="button" id="tickerChartClose" aria-label="Close chart">&times;</button>
            </div>
            <div class="chart-modal-body">
                <img id="tickerChartImage" alt="6 month daily chart with PPO">
            </div>
        </div>
    </div>
    <script src="/app-static/lightweight-charts.standalone.production.js?v=5.0.9"></script>
    <script src="/chart-lib.js?v={cache_buster}"></script>
    <script>
        const screenerColumns = {screener_columns_payload};
        const screenerCommentKey = 'COMMENT';
        const screenerCommentLabels = {screener_comment_labels_payload};
        const screenerBooleanKeys = new Set(['MACD_GT_SIGNAL', 'MACD_CROSS', 'PPO_GT_SIGNAL', 'PPO_CROSS', 'TRIPLE_MA_BULLISH']);
        const screenerRows = {screener_rows_payload};
        const hasScreenerRun = {json.dumps(has_screener_run)};
        const estimatedScreenerSeconds = {estimated_screener_seconds};
        const estimatedSimulatorSeconds = {estimated_simulator_seconds};
        const selectedTickers = new Set();
        const watchlistTickers = new Set();
        const watchlistRunTickers = new Set();
        let activeWatchlistTicker = '';
        const watchlistStorageKey = 'duoWatchlistTickers';
        const watchlistActiveTickerStorageKey = 'duoWatchlistActiveTicker';
        // Watchlist chart dark mode follows the global app theme.
        let watchlistDarkChartEnabled = document.body.classList.contains('dark-theme');
        let watchlistForwardViewEnabled = false;
        let watchlistChartHandle = null;
        const watchlistLimit = {MAX_SIMULATOR_TICKERS};
        const generatedReportLabel = {json.dumps(dashboard_label if dashboard_path else "")};
        const pageSize = 50;
        const gridState = {{
            page: 1,
            sortKey: 'RVOL',
            sortDirection: 'desc'
        }};
        const refineColumns = screenerColumns.filter(column => !['TICKER', 'ANCHOR_DATE'].includes(column.key));
        const refineMeta = buildRefineMeta();
        let refineApplied = {{ numeric: {{}}, string: {{}} }};
        let refineAutoApplyTimer = null;

        function refineSlug(key) {{
            return String(key || '').toLowerCase().replace(/[^a-z0-9]+/g, '-');
        }}

        function parseRefineNumberByKey(rawValue, key) {{
            const text = String(rawValue ?? '').trim();
            if (!text) {{
                return null;
            }}
            const cleaned = text.replace(/[$,\\s]/g, '');
            const compactMatch = cleaned.match(/^(-?\\d+(?:\\.\\d+)?)([KMBTkmbt])$/);
            if (compactMatch) {{
                const base = Number.parseFloat(compactMatch[1]);
                if (!Number.isFinite(base)) {{
                    return null;
                }}
                const mult = {{ K: 1e3, M: 1e6, B: 1e9, T: 1e12 }}[compactMatch[2].toUpperCase()] || 1;
                return base * mult;
            }}
            if (cleaned.endsWith('%')) {{
                const pct = Number.parseFloat(cleaned.slice(0, -1));
                if (!Number.isFinite(pct)) {{
                    return null;
                }}
                if (key === '10DV' || key === 'MACD_PCT' || key === 'HIST_PCT') {{
                    return pct;
                }}
                return pct / 100;
            }}
            const parsed = Number.parseFloat(cleaned);
            if (!Number.isFinite(parsed)) {{
                return null;
            }}
            if ((key === 'DAILY_CHANGE_%' || key === 'DROP_FROM_HIGH_%') && Math.abs(parsed) >= 1) {{
                return parsed / 100;
            }}
            return parsed;
        }}

        function coerceRefineNumeric(row, key) {{
            const direct = row?.sort?.[key];
            if (typeof direct === 'number' && Number.isFinite(direct)) {{
                return direct;
            }}
            const parsedSort = parseRefineNumberByKey(direct, key);
            if (parsedSort !== null) {{
                return parsedSort;
            }}
            return parseRefineNumberByKey(row?.display?.[key], key);
        }}

        function buildRefineMeta() {{
            return refineColumns.map(column => {{
                const key = column.key;
                // Comment is a fixed breakout vocabulary, not a measurement. Its
                // labels ("1Y high") would otherwise parse as numbers and flip
                // the column to a numeric ">90" input, so pin it to a dropdown
                // carrying every known label instead of only observed values.
                if (key === screenerCommentKey) {{
                    return {{ key, label: column.label, isNumeric: false, options: [...screenerCommentLabels] }};
                }}
                if (screenerBooleanKeys.has(key)) {{
                    const options = [...new Set(
                        screenerRows
                            .map(row => String(row.display[key] ?? '').trim())
                            .filter(Boolean)
                    )].sort((a, b) => a.localeCompare(b, undefined, {{ sensitivity: 'base', numeric: true }}));
                    return {{ key, label: column.label, isNumeric: false, options }};
                }}
                const nonEmptyCount = screenerRows
                    .map(row => row?.sort?.[key])
                    .filter(value => value !== null && value !== undefined && value !== '').length;
                const values = screenerRows
                    .map(row => coerceRefineNumeric(row, key))
                    .filter(value => value !== null);
                const isNumeric = values.length > 0 && values.length >= nonEmptyCount;
                const options = isNumeric ? [] : [...new Set(
                    screenerRows
                        .map(row => String(row.display[key] ?? '').trim())
                        .filter(Boolean)
                )].sort((a, b) => a.localeCompare(b, undefined, {{ sensitivity: 'base', numeric: true }}));
                return {{ key, label: column.label, isNumeric, options }};
            }});
        }}

        function parseNumericExpression(rawExpression, columnKey) {{
            const raw = String(rawExpression ?? '').trim();
            if (!raw) {{
                return null;
            }}
            const match = raw.match(/^(>=|<=|>|<|=)?\\s*(-?\\d+(?:\\.\\d+)?)([KMBTkmbt%])?$/);
            if (!match) {{
                return null;
            }}
            const defaultOp = columnKey === 'DROP_FROM_HIGH_%' ? '<=' : '>=';
            const opToken = match[1] || defaultOp;
            const opMap = {{ '>': 'gt', '>=': 'gte', '<': 'lt', '<=': 'lte', '=': 'eq' }};
            const op = opMap[opToken];
            const value = parseRefineNumberByKey(`${{match[2]}}${{match[3] || ''}}`, columnKey);
            if (!op || !Number.isFinite(value)) {{
                return null;
            }}
            const isNegative = String(match[2]).startsWith('-');
            const isMagnitude = columnKey === 'DROP_FROM_HIGH_%' && !isNegative;
            return {{ op, value, isMagnitude }};
        }}

        function formatNumericExpression(op, value, columnKey = null, isMagnitude = false) {{
            if (!Number.isFinite(value)) {{
                return '';
            }}
            const symbol = {{ gt: '>', gte: '>=', lt: '<', lte: '<=', eq: '=' }}[op] || '>=';
            if (columnKey === 'DROP_FROM_HIGH_%') {{
                const percentText = (Math.abs(value) * 100).toFixed(2).replace(/\\.00$/, '').replace(/(\\.\\d*[1-9])0+$/, '$1');
                if (isMagnitude) {{
                    return op === 'lte' ? `${{percentText}}%` : `${{symbol}}${{percentText}}%`;
                }}
                const sign = value < 0 ? '-' : '';
                return `${{symbol}}${{sign}}${{percentText}}%`;
            }}
            if (columnKey === 'DAILY_CHANGE_%') {{
                const percentText = (value * 100).toFixed(2).replace(/\\.00$/, '').replace(/(\\.\\d*[1-9])0+$/, '$1');
                return `${{symbol}}${{percentText}}%`;
            }}
            if (columnKey === 'MACD_PCT' || columnKey === 'HIST_PCT') {{
                const percentText = value.toFixed(2).replace(/\\.00$/, '').replace(/(\\.\\d*[1-9])0+$/, '$1');
                return `${{symbol}}${{percentText}}%`;
            }}
            const numberText = Number.isInteger(value) ? String(value) : String(value);
            return `${{symbol}}${{numberText}}`;
        }}

        function formatRefinePercentValue(value) {{
            if (!Number.isFinite(value)) {{
                return '';
            }}
            const percentText = (value * 100).toFixed(2).replace(/\\.00$/, '').replace(/(\\.\\d*[1-9])0+$/, '$1');
            return `${{percentText}}%`;
        }}

        function captureRefineControls() {{
            const state = {{ numeric: {{}}, string: {{}} }};
            refineMeta.forEach(meta => {{
                if (meta.isNumeric) {{
                    const rawExpr = document.querySelector(`[data-refine-num-expr="${{meta.key}}"]`)?.value || '';
                    const parsed = parseNumericExpression(rawExpr, meta.key);
                    if (parsed) {{
                        state.numeric[meta.key] = parsed;
                    }}
                }} else {{
                    const selected = [...document.querySelectorAll(`input[data-refine-string="${{meta.key}}"]:checked`)]
                        .map(input => String(input.value));
                    if (selected.length) {{
                        state.string[meta.key] = selected;
                    }}
                }}
            }});
            return state;
        }}

        function applyRefineStateToControls(state) {{
            refineMeta.forEach(meta => {{
                if (meta.isNumeric) {{
                    const config = state.numeric[meta.key];
                    const exprInput = document.querySelector(`[data-refine-num-expr="${{meta.key}}"]`);
                    if (exprInput) {{
                        exprInput.value = config ? formatNumericExpression(config.op, config.value, meta.key, config.isMagnitude) : '';
                    }}
                }} else {{
                    const selected = new Set(state.string[meta.key] || []);
                    document.querySelectorAll(`input[data-refine-string="${{meta.key}}"]`).forEach(input => {{
                        input.checked = selected.has(input.value);
                    }});
                    updateStringButtonLabel(meta.key);
                }}
            }});
        }}

        function countActiveRefineFilters(state) {{
            return Object.keys(state.numeric).length + Object.keys(state.string).length;
        }}

        function getActiveRefineLabels(state) {{
            const labels = [];
            refineMeta.forEach(meta => {{
                if (meta.isNumeric) {{
                    const config = state.numeric[meta.key];
                    if (!config) {{
                        return;
                    }}
                    const opLabel = {{ gt: '>', gte: '>=', lt: '<', lte: '<=', eq: '=' }}[config.op] || '';
                    if (opLabel) {{
                        let displayValue;
                        if (meta.key === 'DROP_FROM_HIGH_%') {{
                            const percentText = (Math.abs(config.value) * 100).toFixed(2).replace(/\\.00$/, '').replace(/(\\.\\d*[1-9])0+$/, '$1');
                            if (config.isMagnitude) {{
                                const labelText = config.op === 'lte' ? `Drop from high: max ${{percentText}}%` : `${{meta.label}} ${{opLabel}} ${{percentText}}%`;
                                labels.push(labelText);
                                return;
                            }}
                            const sign = config.value < 0 ? '-' : '';
                            displayValue = `${{sign}}${{percentText}}%`;
                        }} else if (meta.key === 'DAILY_CHANGE_%') {{
                            displayValue = formatRefinePercentValue(config.value);
                        }} else if (meta.key === '10DV') {{
                            displayValue = `${{config.value}}%`;
                        }} else {{
                            displayValue = String(config.value);
                        }}
                        labels.push(`${{meta.label}} ${{opLabel}} ${{displayValue}}`);
                    }}
                    return;
                }}
                const selected = state.string[meta.key];
                if (!selected || !selected.length) {{
                    return;
                }}
                labels.push(selected.length === 1
                    ? `${{meta.label}}: ${{selected[0]}}`
                    : `${{meta.label}}: ${{selected.length}} selected`);
            }});
            return labels;
        }}

        function updateRefineBadges(state) {{
            const count = countActiveRefineFilters(state);
            const inlineCount = document.getElementById('refineInlineCount');
            const summaryCount = document.getElementById('refineSummaryCount');
            if (inlineCount) {{
                inlineCount.textContent = String(count);
            }}
            if (summaryCount) {{
                summaryCount.textContent = String(count);
            }}
            const activeList = document.getElementById('refineActiveList');
            if (activeList) {{
                const labels = getActiveRefineLabels(state);
                if (!labels.length) {{
                    activeList.innerHTML = '<span class="refine-empty-note">None</span>';
                }} else {{
                    activeList.innerHTML = labels.map(label => `<span class="refine-chip">${{escapeHtml(label)}}</span>`).join('');
                }}
            }}
        }}

        function syncSelectAllCheckbox(columnKey) {{
            const selectAll = document.querySelector(`input[data-refine-select-all="${{columnKey}}"]`);
            if (!selectAll) {{
                return;
            }}
            const allInputs = document.querySelectorAll(`input[data-refine-string="${{columnKey}}"]`);
            const checkedInputs = document.querySelectorAll(`input[data-refine-string="${{columnKey}}"]:checked`);
            if (allInputs.length === 0) {{
                selectAll.checked = false;
                selectAll.indeterminate = false;
            }} else if (checkedInputs.length === allInputs.length) {{
                selectAll.checked = true;
                selectAll.indeterminate = false;
            }} else if (checkedInputs.length > 0) {{
                selectAll.checked = false;
                selectAll.indeterminate = true;
            }} else {{
                selectAll.checked = false;
                selectAll.indeterminate = false;
            }}
        }}

        function updateStringButtonLabel(columnKey) {{
            const button = document.querySelector(`[data-refine-string-btn="${{columnKey}}"]`);
            if (!button) {{
                return;
            }}
            const count = document.querySelectorAll(`input[data-refine-string="${{columnKey}}"]:checked`).length;
            button.textContent = count ? `${{count}} selected` : 'Select';
            syncSelectAllCheckbox(columnKey);
        }}

        function closeAllRefinePanels() {{
            document.querySelectorAll('.refine-string-panel.is-open').forEach(panel => panel.classList.remove('is-open'));
        }}

        function positionRefineStringPanel(panel, triggerButton) {{
            if (!panel || !triggerButton) {{
                return;
            }}
            panel.style.top = '0px';
            panel.style.left = '0px';
            panel.style.visibility = 'hidden';
            panel.classList.add('is-open');
            const panelRect = panel.getBoundingClientRect();
            panel.classList.remove('is-open');
            panel.style.visibility = '';

            const triggerRect = triggerButton.getBoundingClientRect();
            const viewportWidth = window.innerWidth || document.documentElement.clientWidth;
            const viewportHeight = window.innerHeight || document.documentElement.clientHeight;
            const gap = 4;
            let left = triggerRect.left;
            let top = triggerRect.bottom + gap;

            if (left + panelRect.width > viewportWidth - 8) {{
                left = Math.max(8, viewportWidth - panelRect.width - 8);
            }}
            if (top + panelRect.height > viewportHeight - 8) {{
                top = Math.max(8, triggerRect.top - panelRect.height - gap);
            }}
            panel.style.left = `${{left}}px`;
            panel.style.top = `${{top}}px`;
        }}

        function toggleRefineStringPanel(columnKey, triggerButton = null) {{
            const panel = document.getElementById(`refine-string-panel-${{refineSlug(columnKey)}}`);
            if (!panel) {{
                return;
            }}
            const button = triggerButton || document.querySelector(`[data-refine-string-toggle="${{columnKey}}"]`);
            const shouldOpen = !panel.classList.contains('is-open');
            closeAllRefinePanels();
            if (shouldOpen) {{
                positionRefineStringPanel(panel, button);
                panel.classList.add('is-open');
            }}
        }}

        function rowMatchesRefineFilters(row) {{
            for (const [columnKey, config] of Object.entries(refineApplied.numeric)) {{
                const cellValue = coerceRefineNumeric(row, columnKey);
                if (cellValue === null) {{
                    return false;
                }}
                if (columnKey === 'DROP_FROM_HIGH_%' && config.isMagnitude) {{
                    const absVal = Math.abs(cellValue);
                    const targetVal = Math.abs(config.value);
                    if (config.op === 'gt' && !(absVal > targetVal)) return false;
                    if (config.op === 'gte' && !(absVal >= targetVal)) return false;
                    if (config.op === 'lt' && !(absVal < targetVal)) return false;
                    if (config.op === 'lte' && !(absVal <= targetVal + 1e-6)) return false;
                    if (config.op === 'eq' && !(Math.abs(absVal - targetVal) < 1e-6)) return false;
                    continue;
                }}
                if (config.op === 'gt' && !(cellValue > config.value)) return false;
                if (config.op === 'gte' && !(cellValue >= config.value)) return false;
                if (config.op === 'lt' && !(cellValue < config.value)) return false;
                if (config.op === 'lte' && !(cellValue <= config.value)) return false;
                if (config.op === 'eq' && !(cellValue === config.value)) return false;
            }}
            for (const [columnKey, selectedValues] of Object.entries(refineApplied.string)) {{
                const cellDisplay = String(row.display[columnKey] ?? '').trim();
                if (!selectedValues.includes(cellDisplay)) {{
                    return false;
                }}
            }}
            return true;
        }}

        function applyRefineFilters(closePanels = false) {{
            refineApplied = captureRefineControls();
            if (closePanels) {{
                closeAllRefinePanels();
            }}
            updateRefineBadges(refineApplied);
            gridState.page = 1;
            renderScreenerGrid();
        }}

        function scheduleRefineAutoApply() {{
            if (refineAutoApplyTimer) {{
                clearTimeout(refineAutoApplyTimer);
            }}
            refineAutoApplyTimer = setTimeout(() => {{
                applyRefineFilters();
                refineAutoApplyTimer = null;
            }}, 220);
        }}

        function clearRefineFilters() {{
            refineApplied = {{ numeric: {{}}, string: {{}} }};
            applyRefineStateToControls(refineApplied);
            closeAllRefinePanels();
            updateRefineBadges(refineApplied);
            gridState.page = 1;
            renderScreenerGrid();
        }}

        function renderRefineControls() {{
            const container = document.getElementById('refineFiltersGrid');
            const inlineButton = document.getElementById('refineInlineButton');
            if (!container) {{
                return;
            }}
            if (!screenerRows.length || !refineMeta.length) {{
                container.innerHTML = '<div class="refine-empty-note">Run screener to refine results.</div>';
                if (inlineButton) {{
                    inlineButton.disabled = true;
                }}
                updateRefineBadges(refineApplied);
                return;
            }}
            if (inlineButton) {{
                inlineButton.disabled = false;
            }}
            container.innerHTML = refineMeta.map(meta => {{
                if (meta.isNumeric) {{
                    const placeholder = meta.key === '10DV' ? 'e.g. >3%' : (meta.key === 'DROP_FROM_HIGH_%' ? 'e.g. 2% (max)' : (meta.key === 'DAILY_CHANGE_%' ? 'e.g. >2%' : (meta.key === 'MACD' || meta.key === 'MACD_SIGNAL' || meta.key === 'MACD_HISTOGRAM' ? 'e.g. >0' : 'e.g. >90')));
                    return `<div class="refine-control"><span class="refine-label">${{escapeHtml(meta.label)}}</span><div class="refine-num-row"><input data-refine-num-expr="${{meta.key}}" type="text" inputmode="decimal" placeholder="${{placeholder}}"></div></div>`;
                }}
                const selectAllHtml = meta.options && meta.options.length > 0
                    ? `<div class="refine-string-select-all-row"><label class="refine-string-opt"><input type="checkbox" data-refine-select-all="${{meta.key}}"> Select all</label></div>`
                    : '';
                const optionsHtml = meta.options.map(option => `<label class="refine-string-opt"><input type="checkbox" data-refine-string="${{meta.key}}" value="${{escapeHtml(option)}}"> ${{escapeHtml(option)}}</label>`).join('');
                const slug = refineSlug(meta.key);
                return `<div class="refine-control"><span class="refine-label">${{escapeHtml(meta.label)}}</span><div class="refine-string-wrap"><button type="button" class="refine-string-btn" data-refine-string-btn="${{meta.key}}" data-refine-string-toggle="${{meta.key}}">Select</button><div class="refine-string-panel" data-refine-key="${{meta.key}}" id="refine-string-panel-${{slug}}">${{selectAllHtml}}<div class="refine-string-options">${{optionsHtml || '<div class="refine-empty-note">No values</div>'}}</div><button type="button" class="refine-string-clear" data-refine-string-clear="${{meta.key}}">Clear</button></div></div></div>`;
            }}).join('');
            applyRefineStateToControls(refineApplied);
            updateRefineBadges(refineApplied);
        }}

        function goToGeneratedReport() {{
            window.location.href = '/dashboard';
        }}

        function showMainPanel(panelId, button) {{
            document.querySelectorAll('.workspace-panel').forEach(panel => panel.classList.remove('active'));
            document.querySelectorAll('.tabs button').forEach(tab => tab.classList.remove('active'));
            const panel = document.getElementById(panelId);
            if (panel) {{
                panel.classList.add('active');
            }}
            if (panelId === 'screenerWorkspace') {{
                const dailyScreener = document.getElementById('dailyScreenerDetails');
                if (dailyScreener) {{
                    dailyScreener.open = true;
                }}
                resetScreenerWorkspaceView();
            }}
            if (button) {{
                button.classList.add('active');
            }}
            window.scrollTo(0, 0);
        }}

        function resetProgressVisual(progressId, fillId) {{
            const progress = document.getElementById(progressId);
            const fill = document.getElementById(fillId);
            if (progress) {{
                progress.classList.remove('running');
            }}
            if (fill) {{
                fill.style.transition = 'none';
                fill.style.width = '0%';
                fill.offsetHeight;
                fill.style.transition = '';
            }}
        }}

        function resetScreenerWorkspaceView() {{
            sessionStorage.removeItem('duoScreenerProgressComplete');
            sessionStorage.removeItem('duoSimulatorProgressComplete');
            sessionStorage.removeItem(watchlistStorageKey);
            sessionStorage.removeItem(watchlistActiveTickerStorageKey);
            resetProgressVisual('screenerProgress', 'screenerProgressFill');
            resetProgressVisual('simulatorProgress', 'simulatorProgressFill');
            const dailyScreener = document.getElementById('dailyScreenerDetails');
            if (dailyScreener) {{
                dailyScreener.open = true;
            }}
            const refineResults = document.getElementById('refineResultsDetails');
            if (refineResults) {{
                refineResults.open = false;
            }}
            const dashboardReadySlot = document.getElementById('dashboardReadySlot');
            if (dashboardReadySlot) {{
                dashboardReadySlot.hidden = true;
            }}
            const watchlistDashboardReadySlot = document.getElementById('watchlistDashboardReadySlot');
            if (watchlistDashboardReadySlot) {{
                watchlistDashboardReadySlot.hidden = true;
            }}
            selectedTickers.clear();
            watchlistTickers.clear();
            watchlistRunTickers.clear();
            activeWatchlistTicker = '';
            const watchlistSection = document.getElementById('watchlistSectionCard');
            if (watchlistSection) {{
                watchlistSection.classList.remove('show');
            }}
            const screenerCard = document.getElementById('screenerResultsCard');
            if (screenerCard) {{
                screenerCard.classList.remove('watchlist-focus');
            }}
            document.body.classList.remove('watchlist-mode');
            updateSelectionControls();
            updateWatchlistControls();
        }}

        function syncWatchlistModeUi() {{
            const hasWatchlist = watchlistTickers.size > 0;
            document.body.classList.toggle('watchlist-mode', hasWatchlist);
        }}

        function persistWatchlistState() {{
            sessionStorage.setItem(watchlistStorageKey, JSON.stringify([...watchlistTickers]));
            if (activeWatchlistTicker && watchlistTickers.has(activeWatchlistTicker)) {{
                sessionStorage.setItem(watchlistActiveTickerStorageKey, activeWatchlistTicker);
            }} else {{
                sessionStorage.removeItem(watchlistActiveTickerStorageKey);
            }}
        }}

        function restoreWatchlistState() {{
            const raw = sessionStorage.getItem(watchlistStorageKey);
            if (!raw) {{
                return;
            }}
            let parsedTickers = [];
            try {{
                const parsed = JSON.parse(raw);
                if (Array.isArray(parsed)) {{
                    parsedTickers = parsed;
                }}
            }} catch (_error) {{
                sessionStorage.removeItem(watchlistStorageKey);
                sessionStorage.removeItem(watchlistActiveTickerStorageKey);
                return;
            }}
            watchlistTickers.clear();
            parsedTickers.forEach(ticker => {{
                if (rowByTicker(ticker)) {{
                    watchlistTickers.add(String(ticker));
                }}
            }});
            if (!watchlistTickers.size) {{
                sessionStorage.removeItem(watchlistStorageKey);
                sessionStorage.removeItem(watchlistActiveTickerStorageKey);
                return;
            }}
            const storedActiveTicker = sessionStorage.getItem(watchlistActiveTickerStorageKey) || '';
            activeWatchlistTicker = watchlistTickers.has(storedActiveTicker) ? storedActiveTicker : '';
            const forwardToggle = document.getElementById('watchlistForwardToggle');
            if (forwardToggle) {{
                forwardToggle.checked = watchlistForwardViewEnabled;
            }}
            renderWatchlistCard();
            if (activeWatchlistTicker) {{
                const activeRow = rowByTicker(activeWatchlistTicker);
                if (activeRow) {{
                    showWatchlistChart(activeWatchlistTicker, activeRow.anchorDate || '');
                    renderWatchlistCard();
                }}
            }}
            persistWatchlistState();
        }}

        function syncWatchlistDarkChartUi() {{
            const chartArea = document.querySelector('.watchlist-chart-area');
            if (chartArea) {{
                chartArea.classList.toggle('dark-chart', watchlistDarkChartEnabled);
            }}
        }}

        function escapeHtml(value) {{
            return String(value ?? '')
                .replace(/&/g, '&amp;')
                .replace(/</g, '&lt;')
                .replace(/>/g, '&gt;')
                .replace(/"/g, '&quot;')
                .replace(/'/g, '&#39;');
        }}

        function screenerConditionalCellClass(key, rawValue) {{
            if (key === 'DAILY_CLOSING_POSITION') {{
                const zone = String(rawValue || '').split('&').pop().trim();
                const zoneBuckets = {{
                    '>U7': ['pos', 5],
                    'U6-U7': ['pos', 5],
                    'U5-U6': ['pos', 5],
                    'U4-U5': ['pos', 4],
                    'U3-U4': ['pos', 4],
                    'U2-U3': ['pos', 3],
                    'U1-U2': ['pos', 2],
                    'Mid-U1': ['pos', 1],
                    'Mid-L1': ['neg', 1],
                    'L1-L2': ['neg', 2],
                    'L2-L3': ['neg', 3],
                    'L3-L4': ['neg', 4],
                    'L4-L5': ['neg', 5],
                    'L5-L6': ['neg', 5],
                    'L6-L7': ['neg', 5],
                    '<L7': ['neg', 5],
                }};
                const bucket = zoneBuckets[zone];
                return bucket ? `screener-position-${{bucket[0]}}-${{bucket[1]}}` : '';
            }}
            if (key === 'MACD_GT_SIGNAL' || key === 'MACD_CROSS' || key === 'PPO_GT_SIGNAL' || key === 'PPO_CROSS' || key === 'TRIPLE_MA_BULLISH') {{
                const textValue = String(rawValue ?? '').trim().toLowerCase();
                if (rawValue === true || textValue === 'yes') return 'screener-bool-yes';
                if (rawValue === false || textValue === 'no') return 'screener-bool-no';
                return '';
            }}
            if (key === 'COMMENT') {{
                const commentClasses = {{
                    'Below 5D high': 'screener-comment-below',
                    '5D high': 'screener-comment-5d',
                    '10D high': 'screener-comment-10d',
                    '1M high': 'screener-comment-1m',
                    '2M high': 'screener-comment-2m',
                    '3M high': 'screener-comment-3m',
                    '6M high': 'screener-comment-6m',
                    '1Y high': 'screener-comment-1y',
                }};
                return commentClasses[String(rawValue || '').trim()] || '';
            }}
            const numericValue = Number(rawValue);
            if (!Number.isFinite(numericValue)) {{
                return '';
            }}
            if (key === 'RVOL') {{
                if (numericValue >= 20) return 'screener-rvol-5';
                if (numericValue >= 10) return 'screener-rvol-4';
                if (numericValue >= 5) return 'screener-rvol-3';
                if (numericValue >= 2) return 'screener-rvol-2';
                if (numericValue >= 1) return 'screener-rvol-1';
                return '';
            }}
            if (key === 'DAILY_CHANGE_%') {{
                const percentValue = numericValue * 100;
                const absPercent = Math.abs(percentValue);
                if (absPercent < 0.01) return '';
                const direction = percentValue > 0 ? 'pos' : 'neg';
                let bucket = 1;
                if (absPercent >= 10) bucket = 5;
                else if (absPercent >= 5) bucket = 4;
                else if (absPercent >= 2) bucket = 3;
                else if (absPercent >= 1) bucket = 2;
                return `screener-change-${{direction}}-${{bucket}}`;
            }}
            if (key === 'DROP_FROM_HIGH_%') {{
                const percentValue = numericValue * 100;
                const absPercent = Math.abs(percentValue);
                if (absPercent < 0.50) return '';
                let bucket = 1;
                if (absPercent >= 10) bucket = 5;
                else if (absPercent >= 7) bucket = 4;
                else if (absPercent >= 4) bucket = 3;
                else if (absPercent >= 2) bucket = 2;
                return `screener-drop-${{bucket}}`;
            }}
            if (key === 'RSI14') {{
                if (numericValue < 30) return 'screener-rsi-neg-3';
                if (numericValue < 40) return 'screener-rsi-neg-2';
                if (numericValue < 45) return 'screener-rsi-neg-1';
                if (numericValue >= 70) return 'screener-rsi-pos-3';
                if (numericValue >= 55) return 'screener-rsi-pos-2';
                return 'screener-rsi-pos-1';
            }}
            if (key === 'MOMENTUM_SCORE') {{
                if (numericValue >= 80) return 'screener-score-high';
                if (numericValue >= 60) return 'screener-score-mid';
                return 'screener-score-low';
            }}
            if (key === 'MACD' || key === 'MACD_SIGNAL' || key === 'MACD_HISTOGRAM' || key === 'PPO' || key === 'PPO_SIGNAL' || key === 'PPO_HISTOGRAM' || key === 'MACD_PCT' || key === 'HIST_PCT') {{
                if (Math.abs(numericValue) < 1e-12) return '';
                return numericValue > 0 ? 'screener-momentum-positive' : 'screener-momentum-negative';
            }}
            return '';
        }}

        function updateLiveClock() {{
            const now = new Date();
            document.getElementById('liveClockDate').firstChild.nodeValue = now.toLocaleDateString(undefined, {{ weekday: 'short', month: 'short', day: '2-digit', year: 'numeric' }});
            document.getElementById('liveClockTime').textContent = now.toLocaleTimeString(undefined, {{ hour: '2-digit', minute: '2-digit', second: '2-digit' }});
        }}

        function formatEntryDateLabel(dateValue) {{
            if (!dateValue) {{
                return '--';
            }}
            const parts = dateValue.split('-').map(Number);
            if (parts.length !== 3 || parts.some(Number.isNaN)) {{
                return dateValue;
            }}
            const date = new Date(parts[0], parts[1] - 1, parts[2]);
            if (Number.isNaN(date.getTime())) {{
                return dateValue;
            }}
            const day = String(date.getDate()).padStart(2, '0');
            const month = date.toLocaleDateString('en-US', {{ month: 'short' }});
            const year = date.getFullYear();
            const weekday = date.toLocaleDateString('en-US', {{ weekday: 'short' }});
            return `${{day}} ${{month}} ${{year}} ${{weekday}}`;
        }}

        function syncEntryDateDisplay() {{
            const anchorInput = document.getElementById('anchorDateInput');
            const entryDisplay = document.getElementById('entryDateDisplay');
            if (!anchorInput || !entryDisplay) {{
                return;
            }}
            entryDisplay.textContent = formatEntryDateLabel(anchorInput.value);
        }}

        function syncRefineDefaultOpenState() {{
            const panel = document.getElementById('refineResultsDetails');
            if (panel) {{
                panel.open = screenerRows.length > 1;
            }}
        }}

        function startScreenerProgress() {{
            const progress = document.getElementById('screenerProgress');
            const fill = document.getElementById('screenerProgressFill');
            const button = document.getElementById('runScreenerButton');
            if (!progress || !fill || !button) {{
                return;
            }}
            const startedAt = Date.now();
            const estimatedMs = Math.max(60000, estimatedScreenerSeconds * 1000);
            button.disabled = true;
            progress.classList.add('running');
            sessionStorage.removeItem('duoScreenerProgressComplete');
            fill.style.transition = 'none';
            fill.style.width = '0%';
            fill.offsetHeight;
            fill.style.transition = '';

            function tick() {{
                const elapsedMs = Date.now() - startedAt;
                const linearProgress = elapsedMs / estimatedMs;
                const easedProgress = 1 - Math.exp(-3 * linearProgress);
                const percent = Math.min(100, Math.max(4, Math.round(easedProgress * 100)));
                fill.style.width = `${{percent}}%`;
            }}

            tick();
            return setInterval(tick, 500);
        }}

        function finishScreenerProgress() {{
            const fill = document.getElementById('screenerProgressFill');
            if (fill) {{
                fill.style.width = '100%';
            }}
        }}

        function restoreCompletedScreenerProgress() {{
            const navigationEntry = performance.getEntriesByType('navigation')[0];
            const isBrowserRefresh = navigationEntry && navigationEntry.type === 'reload';
            if (isBrowserRefresh) {{
                sessionStorage.removeItem('duoScreenerProgressComplete');
                sessionStorage.removeItem('duoSimulatorProgressComplete');
                return;
            }}
            if (sessionStorage.getItem('duoScreenerProgressComplete') !== '1') {{
                return;
            }}
            const progress = document.getElementById('screenerProgress');
            const fill = document.getElementById('screenerProgressFill');
            if (progress && fill) {{
                progress.classList.add('running');
                fill.style.width = '100%';
            }}
        }}

        function startSimulatorProgress() {{
            const button = document.getElementById('runSimulatorButton');
            const controls = document.querySelector('.watchlist-header-controls');
            if (!button) {{
                return;
            }}
            setSimulatorBusy(true);
            const startedAt = Date.now();
            const estimatedMs = Math.max(30000, estimatedSimulatorSeconds * 1000);
            button.disabled = true;
            button.type = 'button';
            button.dataset.reportReady = '0';
            button.classList.remove('report-ready');
            button.classList.add('processing');
            button.style.setProperty('--run-progress', '0%');
            button.textContent = 'Processing...';
            if (controls) {{
                controls.classList.add('is-processing');
            }}
            sessionStorage.removeItem('duoSimulatorProgressComplete');

            function tick() {{
                const elapsedMs = Date.now() - startedAt;
                const linearProgress = elapsedMs / estimatedMs;
                const easedProgress = 1 - Math.exp(-3 * linearProgress);
                const percent = Math.min(100, Math.max(4, Math.round(easedProgress * 100)));
                button.style.setProperty('--run-progress', `${{percent}}%`);
            }}

            tick();
            return setInterval(tick, 500);
        }}

        function finishSimulatorProgress() {{
            const button = document.getElementById('runSimulatorButton');
            if (button) {{
                button.style.setProperty('--run-progress', '100%');
            }}
        }}

        function setSimulatorBusy(isBusy) {{
            document.body.classList.toggle('simulator-busy', Boolean(isBusy));
            let shield = document.getElementById('simulatorBusyShield');
            if (isBusy) {{
                if (!shield) {{
                    shield = document.createElement('div');
                    shield.id = 'simulatorBusyShield';
                    shield.className = 'busy-click-shield';
                    shield.setAttribute('aria-hidden', 'true');
                    document.body.appendChild(shield);
                }}
                return;
            }}
            if (shield) {{
                shield.remove();
            }}
        }}

        function restoreCompletedSimulatorProgress() {{
            const navigationEntry = performance.getEntriesByType('navigation')[0];
            const isBrowserRefresh = navigationEntry && navigationEntry.type === 'reload';
            if (isBrowserRefresh || sessionStorage.getItem('duoSimulatorProgressComplete') !== '1') {{
                return;
            }}
            sessionStorage.removeItem('duoSimulatorProgressComplete');
        }}

        function screenSimChartTickers() {{
            return getFilteredRows().map(row => row.ticker).filter(Boolean);
        }}

        function screenSimChartPopoutUrl(ticker, anchorDate = '', forward = false, tickersOverride = null) {{
            const params = new URLSearchParams();
            params.set('ticker', ticker);
            if (anchorDate) {{
                params.set('anchor', anchorDate);
            }}
            const tickers = Array.isArray(tickersOverride) ? tickersOverride : screenSimChartTickers();
            if (tickers.length) {{
                params.set('tickers', tickers.join(','));
            }}
            if (forward) {{
                params.set('forward', '1');
            }}
            return `/chart-popout?${{params.toString()}}`;
        }}

        function openTickerChart(ticker, anchorDate = '') {{
            window.open(screenSimChartPopoutUrl(ticker, anchorDate), '_blank', 'width=1800,height=1060,menubar=no,toolbar=no,location=no,status=no,resizable=yes,scrollbars=yes');
        }}

        function closeTickerChart() {{
            const modal = document.getElementById('tickerChartModal');
            const image = document.getElementById('tickerChartImage');
            modal.classList.remove('open');
            modal.setAttribute('aria-hidden', 'true');
            image.removeAttribute('src');
        }}

        function getFilteredRows() {{
            let filtered = screenerRows;
            filtered = filtered.filter(rowMatchesRefineFilters);
            const searchTerm = String(document.getElementById('screenerSearch')?.value || '').trim().toUpperCase();
            if (searchTerm) {{
                filtered = filtered.filter(row => {{
                    const ticker = String(row.ticker || '').toUpperCase();
                    if (ticker.includes(searchTerm)) {{
                        return true;
                    }}
                    return screenerColumns.some(column => String(row.display[column.key] ?? '').toUpperCase().includes(searchTerm));
                }});
            }}
            const direction = gridState.sortDirection === 'asc' ? 1 : -1;
            return [...filtered].sort((a, b) => {{
                const av = a.sort[gridState.sortKey];
                const bv = b.sort[gridState.sortKey];
                if (typeof av === 'number' && typeof bv === 'number') {{
                    return (av - bv) * direction;
                }}
                return String(av ?? '').localeCompare(String(bv ?? ''), undefined, {{ numeric: true, sensitivity: 'base' }}) * direction;
            }});
        }}

        function updateSelectionControls() {{
            const selectedCount = selectedTickers.size;
            const selectedNames = [...selectedTickers].sort();
            const selectedSummary = document.getElementById('selectedStockSummary');
            if (selectedCount) {{
                const previewLimit = 25;
                const previewNames = selectedNames.slice(0, previewLimit);
                const remaining = Math.max(0, selectedNames.length - previewLimit);
                const previewText = remaining
                    ? `${{previewNames.join(', ')}} ... +${{remaining}} more`
                    : previewNames.join(', ');
                selectedSummary.textContent = `Selected for Watchlist (${{selectedCount}}): ${{previewText}}`;
            }} else {{
                selectedSummary.textContent = 'Selected for Watchlist: 0';
            }}
            selectedSummary.classList.toggle('has-selection', selectedCount > 0);
            const addButton = document.getElementById('addWatchlistButton');
            if (addButton) {{
                addButton.disabled = selectedCount === 0 || screenerRows.length === 0;
            }}
        }}

        function rowByTicker(ticker) {{
            const upperTicker = String(ticker || '').toUpperCase();
            return screenerRows.find(row => String(row.ticker || '').toUpperCase() === upperTicker) || null;
        }}

        function updateWatchlistControls() {{
            const runCount = watchlistRunTickers.size;
            const watchCount = watchlistTickers.size;
            const title = document.getElementById('watchlistCardTitle');
            if (title) {{
                title.textContent = `Watchlist (${{watchCount}} stock${{watchCount === 1 ? '' : 's'}})`;
            }}
            const selectionStatus = document.getElementById('watchlistSelectionStatus');
            if (selectionStatus) {{
                selectionStatus.textContent = runCount > 0
                    ? `Selected ${{runCount}}/${{watchlistLimit}}`
                    : `Select stocks (max ${{watchlistLimit}})`;
            }}
            const runButton = document.getElementById('runSimulatorButton');
            if (runButton) {{
                if (runButton.classList.contains('processing')) {{
                    document.querySelectorAll('input[data-watchlist-checkbox]').forEach(input => {{
                        input.disabled = true;
                    }});
                    return;
                }}
                const showReportButton = runCount === 0 && Boolean(generatedReportLabel);
                runButton.type = showReportButton ? 'button' : 'submit';
                runButton.dataset.reportReady = showReportButton ? '1' : '0';
                runButton.disabled = showReportButton ? false : (runCount === 0 || runCount > watchlistLimit);
                runButton.classList.toggle('report-ready', showReportButton);
                if (showReportButton) {{
                    runButton.textContent = generatedReportLabel;
                }} else if (!runButton.disabled) {{
                    runButton.textContent = 'Run Simulator';
                }}
            }}
            document.querySelectorAll('input[data-watchlist-checkbox]').forEach(input => {{
                input.disabled = !input.checked && runCount >= watchlistLimit;
            }});
            const selectAll = document.querySelector('input[data-watchlist-select-all]');
            if (selectAll) {{
                const watchlistValues = [...watchlistTickers];
                const selectedCount = watchlistValues.filter(ticker => watchlistRunTickers.has(ticker)).length;
                selectAll.checked = watchlistValues.length > 0 && selectedCount === watchlistValues.length;
                selectAll.indeterminate = selectedCount > 0 && selectedCount < watchlistValues.length;
                selectAll.disabled = watchlistValues.length === 0;
            }}
        }}

        function toggleWatchlistSelectAll(checked) {{
            if (checked) {{
                [...watchlistTickers].slice(0, watchlistLimit).forEach(ticker => watchlistRunTickers.add(ticker));
            }} else {{
                watchlistRunTickers.clear();
            }}
            renderWatchlistCard();
            updateWatchlistControls();
        }}

        async function showWatchlistChart(ticker, anchorDate = '') {{
            const canvas = document.getElementById('watchlistChartCanvas');
            const placeholder = document.getElementById('watchlistChartPlaceholder');
            if (!canvas || !placeholder || !ticker) {{
                return;
            }}
            canvas.style.display = 'block';
            placeholder.style.display = 'none';
            activeWatchlistTicker = ticker;
            persistWatchlistState();
            try {{
                watchlistChartHandle = await DuoCharts.mount(canvas, {{
                    ticker: ticker,
                    anchor: anchorDate || '',
                    compact: true,
                    legendHost: document.getElementById('watchlistLegendHost'),
                    dark: watchlistDarkChartEnabled,
                    forward: watchlistForwardViewEnabled,
                }});
            }} catch (err) {{
                watchlistChartHandle = null;
                const legendHost = document.getElementById('watchlistLegendHost');
                if (legendHost) legendHost.innerHTML = '';
                placeholder.textContent = 'Chart unavailable.';
                placeholder.style.display = 'flex';
                canvas.style.display = 'none';
            }}
        }}

        function renderWatchlistCard() {{
            const section = document.getElementById('watchlistSectionCard');
            const screenerCard = document.getElementById('screenerResultsCard');
            const body = document.getElementById('watchlistTableBody');
            if (!section || !body) {{
                return;
            }}
            const watchRows = [...watchlistTickers].map(rowByTicker).filter(Boolean);
            if (!watchRows.length) {{
                section.classList.remove('show');
                if (screenerCard) {{
                    screenerCard.classList.remove('watchlist-focus');
                }}
                syncWatchlistModeUi();
                body.innerHTML = '';
                updateWatchlistControls();
                sessionStorage.removeItem(watchlistStorageKey);
                sessionStorage.removeItem(watchlistActiveTickerStorageKey);
                return;
            }}
            body.innerHTML = watchRows.map(row => {{
                const safeTicker = escapeHtml(row.ticker);
                const safeAnchor = escapeHtml(row.anchorDate || '');
                const checked = watchlistRunTickers.has(row.ticker) ? ' checked' : '';
                const tickerClass = activeWatchlistTicker === row.ticker ? 'watchlist-ticker-btn active' : 'watchlist-ticker-btn';
                return `<tr><td><input data-watchlist-checkbox type="checkbox" value="${{safeTicker}}"${{checked}} aria-label="Run ${{safeTicker}}"></td><td><button type="button" class="${{tickerClass}}" data-watchlist-ticker="${{safeTicker}}" data-watchlist-anchor="${{safeAnchor}}">${{safeTicker}}</button></td></tr>`;
            }}).join('');
            section.classList.add('show');
            if (screenerCard) {{
                screenerCard.classList.add('watchlist-focus');
            }}
            syncWatchlistModeUi();
            syncWatchlistDarkChartUi();
            const watchlistDashboardReadySlot = document.getElementById('watchlistDashboardReadySlot');
            if (watchlistDashboardReadySlot) {{
                watchlistDashboardReadySlot.hidden = false;
            }}
            updateWatchlistControls();
            persistWatchlistState();
        }}

        function addCurrentSelectionToWatchlist() {{
            watchlistTickers.clear();
            [...selectedTickers].forEach(ticker => watchlistTickers.add(ticker));
            watchlistRunTickers.clear();
            selectedTickers.clear();
            activeWatchlistTicker = '';
            const canvas = document.getElementById('watchlistChartCanvas');
            const placeholder = document.getElementById('watchlistChartPlaceholder');
            if (canvas && placeholder) {{
                if (watchlistChartHandle) {{
                    watchlistChartHandle.destroy();
                    watchlistChartHandle = null;
                }}
                const legendHost = document.getElementById('watchlistLegendHost');
                if (legendHost) {{
                    legendHost.innerHTML = '';
                }}
                canvas.innerHTML = '';
                canvas.style.display = 'none';
                placeholder.textContent = 'Click a ticker in Watchlist to preview chart.';
                placeholder.style.display = 'block';
            }}
            persistWatchlistState();
            renderWatchlistCard();
            renderScreenerGrid();
            const section = document.getElementById('watchlistSectionCard');
            if (section) {{
                section.scrollIntoView({{ behavior: 'smooth', block: 'start' }});
            }}
        }}

        function updateScreenerResultsTitle(filteredCount, totalCount) {{
            const title = document.getElementById('screenerResultsTitle');
            if (!title) {{
                return;
            }}
            if (!hasScreenerRun) {{
                title.textContent = 'Screener Results';
                return;
            }}
            title.textContent = `Screener Results (${{filteredCount}}/${{totalCount}})`;
        }}

        function updateScreenerSelectAllState(filteredRows) {{
            const selectAll = document.querySelector('input[data-screener-select-all]');
            if (!selectAll) {{
                return;
            }}
            const tickers = filteredRows.map(row => row.ticker).filter(Boolean);
            const selectedInFiltered = tickers.filter(ticker => selectedTickers.has(ticker)).length;
            selectAll.checked = tickers.length > 0 && selectedInFiltered === tickers.length;
            selectAll.indeterminate = selectedInFiltered > 0 && selectedInFiltered < tickers.length;
        }}

        function toggleScreenerSelectAll(checked) {{
            const filteredRows = getFilteredRows();
            filteredRows.forEach(row => {{
                if (!row?.ticker) {{
                    return;
                }}
                if (checked) {{
                    selectedTickers.add(row.ticker);
                }} else {{
                    selectedTickers.delete(row.ticker);
                }}
            }});
            renderScreenerGrid();
        }}

        function renderScreenerGrid() {{
            const head = document.getElementById('screenerTableHead');
            const body = document.getElementById('screenerTableBody');
            if (!head || !body) {{
                return;
            }}
            head.innerHTML = '<tr><th><input type="checkbox" data-screener-select-all aria-label="Select all filtered rows"></th>' + screenerColumns.map(column => {{
                const isSorted = column.key === gridState.sortKey;
                const sortClass = isSorted ? (gridState.sortDirection === 'asc' ? ' sort-asc' : ' sort-desc') : '';
                const ariaSort = isSorted ? (gridState.sortDirection === 'asc' ? 'ascending' : 'descending') : 'none';
                const columnClass = 'screener-col-' + String(column.key).toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');
                return `<th data-sort-key="${{column.key}}" class="sortable ${{columnClass}}${{sortClass}}" aria-sort="${{ariaSort}}">`
                    + `<span class="th-inner"><span class="th-label">${{column.label}}</span>`
                    + `<span class="sort-arrow" aria-hidden="true"></span></span></th>`;
            }}).join('') + '</tr>';

            const filtered = getFilteredRows();
            updateScreenerResultsTitle(filtered.length, screenerRows.length);
            const pageCount = Math.max(1, Math.ceil(filtered.length / pageSize));
            gridState.page = Math.min(Math.max(gridState.page, 1), pageCount);
            const start = (gridState.page - 1) * pageSize;
            const pageRows = filtered.slice(start, start + pageSize);
            if (!pageRows.length) {{
                body.innerHTML = hasScreenerRun ? `<tr><td colspan="${{screenerColumns.length + 1}}">No rows match the current filter.</td></tr>` : '';
            }} else {{
                body.innerHTML = pageRows.map(row => {{
                    const checked = selectedTickers.has(row.ticker) ? ' checked' : '';
                    const safeTicker = escapeHtml(row.ticker);
                    const cells = screenerColumns.map(column => {{
                        const value = escapeHtml(row.display[column.key]);
                        const columnClass = 'screener-col-' + String(column.key).toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');
                        if (column.key === 'TICKER') {{
                            const safeAnchorDate = escapeHtml(row.anchorDate || '');
                            return `<td class="${{columnClass}}"><button class="ticker-chart-link" type="button" data-ticker-chart="${{safeTicker}}" data-anchor-date="${{safeAnchorDate}}">${{value}}</button></td>`;
                        }}
                        if (column.key === 'DAILY_CHANGE_%') {{
                            const dailyChangeClass = screenerConditionalCellClass(column.key, row.sort?.[column.key]);
                            return `<td class="${{columnClass}} ${{dailyChangeClass}}">${{value}}</td>`;
                        }}
                        if (column.key === 'RVOL') {{
                            const rvolClass = screenerConditionalCellClass(column.key, row.sort?.[column.key]);
                            return `<td class="${{columnClass}} ${{rvolClass}}">${{value}}</td>`;
                        }}
                        if (column.key === 'COMMENT') {{
                            const commentClass = screenerConditionalCellClass(column.key, row.sort?.[column.key]);
                            return `<td class="${{columnClass}} ${{commentClass}}">${{value}}</td>`;
                        }}
                        const conditionalClass = screenerConditionalCellClass(column.key, row.sort?.[column.key]);
                        return `<td class="${{columnClass}} ${{conditionalClass}}">${{value}}</td>`;
                    }}).join('');
                    return `<tr><td><input data-ticker-checkbox type="checkbox" value="${{safeTicker}}" aria-label="Select ${{safeTicker}}"${{checked}}></td>${{cells}}</tr>`;
                }}).join('');
            }}
            document.getElementById('pageInfo').textContent = `Page ${{filtered.length ? gridState.page : 0}} of ${{filtered.length ? pageCount : 0}} (${{filtered.length}} rows)`;
            document.getElementById('prevPage').disabled = gridState.page <= 1;
            document.getElementById('nextPage').disabled = gridState.page >= pageCount || filtered.length === 0;
            updateScreenerSelectAllState(filtered);
            updateSelectionControls();
        }}

        document.getElementById('prevPage').addEventListener('click', () => {{
            gridState.page -= 1;
            renderScreenerGrid();
        }});
        document.getElementById('nextPage').addEventListener('click', () => {{
            gridState.page += 1;
            renderScreenerGrid();
        }});
        document.getElementById('addWatchlistButton').addEventListener('click', () => {{
            if (selectedTickers.size === 0) {{
                return;
            }}
            addCurrentSelectionToWatchlist();
        }});
        document.getElementById('anchorDateInput').addEventListener('input', syncEntryDateDisplay);
        document.getElementById('anchorDateInput').addEventListener('change', syncEntryDateDisplay);
        document.getElementById('marketViewButton').addEventListener('click', () => {{
            const anchorDate = document.getElementById('anchorDateInput')?.value || '';
            window.open(screenSimChartPopoutUrl('SPY', anchorDate, false, ['SPY', 'QQQ', 'IWM']), '_blank', 'width=1800,height=980,menubar=no,toolbar=no,location=no,status=no,resizable=yes,scrollbars=yes');
        }});
        document.getElementById('screenerSearch').addEventListener('input', () => {{
            gridState.page = 1;
            renderScreenerGrid();
        }});
        document.getElementById('refineApplyButton').addEventListener('click', () => {{
            applyRefineFilters(true);
        }});
        document.getElementById('refineClearButton').addEventListener('click', clearRefineFilters);
        document.getElementById('refineInlineClearButton').addEventListener('click', clearRefineFilters);
        document.getElementById('refineInlineButton').addEventListener('click', () => {{
            const panel = document.getElementById('refineResultsDetails');
            if (!panel) {{
                return;
            }}
            panel.open = true;
            panel.scrollIntoView({{ behavior: 'smooth', block: 'start' }});
        }});
        document.addEventListener('duothemechange', event => {{
            watchlistDarkChartEnabled = Boolean(event.detail && event.detail.dark);
            syncWatchlistDarkChartUi();
            if (watchlistChartHandle) {{
                watchlistChartHandle.setTheme(watchlistDarkChartEnabled);
            }} else if (activeWatchlistTicker) {{
                const activeRow = rowByTicker(activeWatchlistTicker);
                showWatchlistChart(activeWatchlistTicker, activeRow ? activeRow.anchorDate || '' : '');
            }}
        }});
        document.getElementById('refineFiltersGrid').addEventListener('click', event => {{
            const toggle = event.target.closest('button[data-refine-string-toggle]');
            if (toggle) {{
                toggleRefineStringPanel(toggle.getAttribute('data-refine-string-toggle'), toggle);
                return;
            }}
            const clear = event.target.closest('button[data-refine-string-clear]');
            if (clear) {{
                const key = clear.getAttribute('data-refine-string-clear');
                document.querySelectorAll(`input[data-refine-string="${{key}}"]`).forEach(input => {{
                    input.checked = false;
                }});
                updateStringButtonLabel(key);
                scheduleRefineAutoApply();
            }}
        }});
        document.getElementById('refineFiltersGrid').addEventListener('change', event => {{
            const selectAll = event.target.closest('input[data-refine-select-all]');
            if (selectAll) {{
                const key = selectAll.getAttribute('data-refine-select-all');
                const isChecked = selectAll.checked;
                document.querySelectorAll(`input[data-refine-string="${{key}}"]`).forEach(input => {{
                    input.checked = isChecked;
                }});
                updateStringButtonLabel(key);
                scheduleRefineAutoApply();
                return;
            }}
            const checkbox = event.target.closest('input[data-refine-string]');
            if (checkbox) {{
                updateStringButtonLabel(checkbox.getAttribute('data-refine-string'));
                scheduleRefineAutoApply();
            }}
            if (event.target.closest('input[data-refine-num-expr]')) {{
                scheduleRefineAutoApply();
            }}
        }});
        document.getElementById('refineFiltersGrid').addEventListener('input', event => {{
            if (event.target.closest('input[data-refine-num-expr]')) {{
                scheduleRefineAutoApply();
            }}
        }});
        document.getElementById('refineFiltersGrid').addEventListener('keydown', event => {{
            const numExprInput = event.target.closest('input[data-refine-num-expr]');
            if (!numExprInput || event.key !== 'Enter') {{
                return;
            }}
            event.preventDefault();
            if (refineAutoApplyTimer) {{
                clearTimeout(refineAutoApplyTimer);
                refineAutoApplyTimer = null;
            }}
            applyRefineFilters();
        }});
        document.addEventListener('click', event => {{
            if (!event.target.closest('.refine-string-wrap') && !event.target.closest('.refine-string-panel')) {{
                closeAllRefinePanels();
            }}
        }});
        window.addEventListener('resize', closeAllRefinePanels);
        document.getElementById('screenerTableHead').addEventListener('click', event => {{
            const th = event.target.closest('th[data-sort-key]');
            if (!th) {{
                return;
            }}
            const sortKey = th.getAttribute('data-sort-key');
            if (gridState.sortKey === sortKey) {{
                gridState.sortDirection = gridState.sortDirection === 'asc' ? 'desc' : 'asc';
            }} else {{
                gridState.sortKey = sortKey;
                gridState.sortDirection = 'asc';
            }}
            renderScreenerGrid();
        }});
        document.getElementById('screenerTableHead').addEventListener('change', event => {{
            const selectAll = event.target.closest('input[data-screener-select-all]');
            if (!selectAll) {{
                return;
            }}
            toggleScreenerSelectAll(selectAll.checked);
        }});
        document.getElementById('screenerTableBody').addEventListener('change', event => {{
            const input = event.target.closest('input[data-ticker-checkbox]');
            if (!input) {{
                return;
            }}
            if (input.checked) {{
                selectedTickers.add(input.value);
            }} else {{
                selectedTickers.delete(input.value);
            }}
            updateSelectionControls();
        }});
        document.getElementById('screenerTableBody').addEventListener('click', event => {{
            const button = event.target.closest('button[data-ticker-chart]');
            if (!button) {{
                return;
            }}
            openTickerChart(button.getAttribute('data-ticker-chart'), button.getAttribute('data-anchor-date') || '');
        }});
        document.getElementById('watchlistTableBody').addEventListener('change', event => {{
            const input = event.target.closest('input[data-watchlist-checkbox]');
            if (!input) {{
                return;
            }}
            if (input.checked) {{
                if (watchlistRunTickers.size >= watchlistLimit) {{
                    input.checked = false;
                    return;
                }}
                watchlistRunTickers.add(input.value);
            }} else {{
                watchlistRunTickers.delete(input.value);
            }}
            updateWatchlistControls();
        }});
        document.querySelector('input[data-watchlist-select-all]').addEventListener('change', event => {{
            toggleWatchlistSelectAll(event.currentTarget.checked);
        }});
        document.getElementById('watchlistForwardToggle').addEventListener('change', event => {{
            watchlistForwardViewEnabled = Boolean(event.currentTarget.checked);
            persistWatchlistState();
            if (activeWatchlistTicker) {{
                const activeRow = rowByTicker(activeWatchlistTicker);
                showWatchlistChart(activeWatchlistTicker, activeRow ? activeRow.anchorDate || '' : '');
            }}
        }});
        document.getElementById('watchlistTableBody').addEventListener('click', event => {{
            const tickerBtn = event.target.closest('button[data-watchlist-ticker]');
            if (!tickerBtn) {{
                return;
            }}
            showWatchlistChart(tickerBtn.getAttribute('data-watchlist-ticker') || '', tickerBtn.getAttribute('data-watchlist-anchor') || '');
            renderWatchlistCard();
        }});
        window.screenSimChartPopoutUrl = screenSimChartPopoutUrl;
        document.getElementById('tickerChartClose').addEventListener('click', closeTickerChart);
        document.getElementById('tickerChartModal').addEventListener('click', event => {{
            if (event.target.id === 'tickerChartModal') {{
                closeTickerChart();
            }}
        }});
        document.addEventListener('keydown', event => {{
            if (event.key === 'Escape') {{
                closeTickerChart();
            }}
        }});
        document.getElementById('screenerForm').addEventListener('submit', event => {{
            event.preventDefault();
            const form = event.currentTarget;
            const intervalId = startScreenerProgress();
            fetch(form.action, {{
                method: form.method,
                body: new URLSearchParams(new FormData(form)),
                headers: {{ 'X-Duo-Async': '1' }},
                redirect: 'follow'
            }}).then(response => {{
                if (intervalId) {{
                    clearInterval(intervalId);
                }}
                finishScreenerProgress();
                sessionStorage.setItem('duoScreenerProgressComplete', '1');
                setTimeout(() => {{
                    window.location.href = '/';
                }}, 350);
            }}).catch(() => {{
                if (intervalId) {{
                    clearInterval(intervalId);
                }}
                form.submit();
            }});
        }});
        document.getElementById('runSimulatorButton').addEventListener('click', event => {{
            const button = event.currentTarget;
            if (button.dataset.reportReady === '1' && watchlistRunTickers.size === 0) {{
                event.preventDefault();
                goToGeneratedReport();
            }}
        }});
        document.getElementById('watchlistSimulatorForm').addEventListener('submit', event => {{
            if (watchlistRunTickers.size === 0 || watchlistRunTickers.size > watchlistLimit) {{
                event.preventDefault();
                return;
            }}
            event.preventDefault();
            const runButton = document.getElementById('runSimulatorButton');
            if (runButton) {{
                runButton.textContent = 'Processing...';
                runButton.disabled = true;
            }}
            const selectedForRun = [...watchlistRunTickers];
            const holder = document.getElementById('selectedTickerInputs');
            holder.innerHTML = '';
            selectedForRun.forEach(ticker => {{
                const input = document.createElement('input');
                input.type = 'hidden';
                input.name = 'ticker';
                input.value = ticker;
                holder.appendChild(input);
            }});
            watchlistRunTickers.clear();
            document.querySelectorAll('input[data-watchlist-checkbox]').forEach(input => {{
                input.checked = false;
            }});
            updateWatchlistControls();
            persistWatchlistState();
            const form = event.currentTarget;
            const intervalId = startSimulatorProgress();
            fetch(form.action, {{
                method: form.method,
                body: new URLSearchParams(new FormData(form)),
                headers: {{ 'X-Duo-Async': '1' }},
                redirect: 'follow'
            }}).then(response => {{
                if (intervalId) {{
                    clearInterval(intervalId);
                }}
                finishSimulatorProgress();
                sessionStorage.setItem('duoSimulatorProgressComplete', '1');
                setTimeout(() => {{
                    window.location.href = '/?watchlist=1';
                }}, 350);
            }}).catch(() => {{
                if (intervalId) {{
                    clearInterval(intervalId);
                }}
                form.submit();
            }});
        }});
        updateLiveClock();
        setInterval(updateLiveClock, 1000);
        const pageParams = new URLSearchParams(window.location.search);
        if (pageParams.get('reset') === 'screener') {{
            resetScreenerWorkspaceView();
        }} else {{
            restoreCompletedScreenerProgress();
            restoreCompletedSimulatorProgress();
        }}
        syncEntryDateDisplay();
        syncRefineDefaultOpenState();
        syncWatchlistDarkChartUi();
        renderRefineControls();
        renderScreenerGrid();
        restoreWatchlistState();
        updateWatchlistControls();
        if (pageParams.get('watchlist') === '1') {{
            requestAnimationFrame(() => {{
                const section = document.getElementById('watchlistSectionCard');
                if (section && section.classList.contains('show')) {{
                    section.scrollIntoView({{ behavior: 'auto', block: 'start' }});
                }}
            }});
        }}
        if (pageParams.get('panel') === 'savedReports') {{
            showMainPanel('savedReportsPanel', document.querySelector('.tabs button[onclick*="savedReportsPanel"]'));
        }}
    </script>
</body>
</html>"""


def apply_report_launch_style(html_text: str, live_mode: bool) -> str:
    return html_text


def apply_report_label_renames(html_text: str) -> str:
    return (
        html_text
        .replace(">Shortlisted History 30D</button>", ">30D Follow-Through</button>")
        .replace(">Shortlisted History 30D</h2>", ">30D Follow-Through</h2>")
        .replace("Shortlisted History 30D will appear after daily history is available.", "30D Follow-Through will appear after daily history is available.")
        .replace(">Shortlisted</button>", ">Selected Stocks</button>")
    )


def keep_only_portfolio_main_report_tab(html_text: str) -> str:
    html_text = re.sub(r'\s*<button\b[^>]*goToAppRoute\([^>]*>Screener</button>', "", html_text)
    html_text = re.sub(r'\s*<button\b[^>]*showMainReportTab\([\'"]history-30d[\'"][^>]*>30D Follow-Through</button>', "", html_text)
    html_text = re.sub(r'\s*<button\b[^>]*goToAppRoute\([^>]*>Saved Reports</button>', "", html_text)
    return html_text


def ensure_report_theme_support(html_text: str) -> str:
    """Inject dark-theme CSS and the theme boot script into report HTML that was
    generated before dark mode existed, so old saved reports follow the current
    theme too. No-ops for reports that already carry theme support."""
    if "body.dark-theme" not in html_text and "</head>" in html_text:
        html_text = html_text.replace("</head>", f"<style>{FINVIZ_THEME_CSS}</style>\n</head>", 1)
    if "duoSetDarkTheme" not in html_text:
        html_text = re.sub(r"(<body[^>]*>)", lambda m: m.group(1) + DUO_THEME_BOOT_SCRIPT, html_text, count=1)
    return html_text


def normalize_saved_report_tabs(html_text: str, live_mode: bool = False, saved_report_view: bool = False) -> str:
    html_text = apply_report_label_renames(html_text)
    html_text = ensure_report_theme_support(html_text)
    if saved_report_view:
        html_text = keep_only_portfolio_main_report_tab(html_text)
    return apply_report_launch_style(html_text, live_mode)


def normalize_dashboard_report_tabs(html_text: str) -> str:
    return ensure_report_theme_support(apply_report_label_renames(html_text))


class DuoScreenSimRequestHandler(BaseHTTPRequestHandler):
    # Raised when the browser hangs up mid-response (tab closed, reload, or an
    # image src swapped before the previous fetch finished). Not a server error.
    CLIENT_DISCONNECT_ERRORS = (ConnectionAbortedError, ConnectionResetError, BrokenPipeError)

    def handle_one_request(self) -> None:
        try:
            super().handle_one_request()
        except self.CLIENT_DISCONNECT_ERRORS:
            self.close_connection = True

    def send_html(self, content: str, status: int = 200) -> None:
        payload = content.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def send_no_content(self) -> None:
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def send_json(self, data: dict, status: int = 200) -> None:
        payload = json.dumps(data, allow_nan=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def send_bytes(self, payload: bytes, content_type: str, status: int = 200) -> None:
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def send_file(self, path: str) -> None:
        with open(path, "rb") as f:
            payload = f.read()
        extension = os.path.splitext(path)[1].lower()
        content_type = STATIC_CONTENT_TYPES.get(extension) or mimetypes.guess_type(path)[0] or "application/octet-stream"
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        if extension in STATIC_CONTENT_TYPES:
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Cache-Control", "public, max-age=31536000, immutable")
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def redirect_home(self) -> None:
        self.send_response(303)
        self.send_header("Location", "/")
        self.end_headers()

    def read_form(self) -> dict[str, list[str]]:
        length = int(self.headers.get("Content-Length") or "0")
        body = self.rfile.read(length).decode("utf-8") if length else ""
        return parse_qs(body, keep_blank_values=True)

    def read_json(self) -> dict:
        length = int(self.headers.get("Content-Length") or "0")
        if not length:
            return {}
        body = self.rfile.read(length).decode("utf-8")
        payload = json.loads(body) if body.strip() else {}
        return payload if isinstance(payload, dict) else {}

    def do_OPTIONS(self) -> None:
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type, X-Duo-Async")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        if parsed.path == "/":
            query = parse_qs(parsed.query, keep_blank_values=True)
            if (query.get("reset") or [""])[0] == "screener":
                reset_duo_screener_state()
            self.send_html(render_ui_page())
            return
        if parsed.path == "/saved-reports":
            self.send_html(render_saved_reports_page())
            return
        if parsed.path == "/saved-report":
            query = parse_qs(parsed.query, keep_blank_values=True)
            rel_path = (query.get("path") or [""])[0]
            live_mode = (query.get("mode") or [""])[0].lower() == "live"
            try:
                report_path = resolve_saved_report_path(rel_path)
                DUO_UI_STATE["active_saved_report_folder"] = os.path.dirname(report_path)
                with open(report_path, "r", encoding="utf-8") as f:
                    self.send_html(normalize_saved_report_tabs(f.read(), live_mode=live_mode, saved_report_view=True))
            except Exception as exc:
                self.send_html(f"<h1>Unable to open saved report</h1><p>{html.escape(str(exc))}</p>", status=404)
            return
        if parsed.path == "/live-snapshot":
            snapshot = build_live_snapshot()
            self.send_json(snapshot)
            return
        if parsed.path == "/report-note":
            query = parse_qs(parsed.query, keep_blank_values=True)
            rel_path = (query.get("path") or [""])[0]
            try:
                note_path = resolve_report_note_path(rel_path)
                note = ""
                if os.path.exists(note_path):
                    with open(note_path, "r", encoding="utf-8") as handle:
                        note = handle.read()
                self.send_json({"note": note})
            except Exception as exc:
                self.send_json({"error": str(exc)}, status=400)
            return
        if parsed.path == "/ticker-data":
            query = parse_qs(parsed.query, keep_blank_values=True)
            ticker = (query.get("ticker") or [""])[0].strip().upper()
            anchor = (query.get("anchor") or [""])[0].strip()
            compact = (query.get("compact") or [""])[0].strip().lower() == "watchlist"
            forward = (query.get("forward") or [""])[0].strip().lower() in {"1", "true", "yes"}
            try:
                self.send_json(get_cached_daily_chart_json_payload(ticker, anchor, compact=compact, forward=forward))
            except self.CLIENT_DISCONNECT_ERRORS:
                self.close_connection = True
            except Exception as exc:
                self.send_json({"error": str(exc)}, status=500)
            return
        if parsed.path == "/chart-lib.js":
            self.send_bytes(DUO_CHART_LIB_JS.encode("utf-8"), "text/javascript; charset=utf-8")
            return
        if parsed.path == "/ticker-chart":
            query = parse_qs(parsed.query, keep_blank_values=True)
            ticker = (query.get("ticker") or [""])[0].strip().upper()
            anchor = (query.get("anchor") or [""])[0].strip()
            compact = (query.get("compact") or [""])[0].strip().lower() == "watchlist"
            dark = (query.get("theme") or [""])[0].strip().lower() == "dark"
            forward = (query.get("forward") or [""])[0].strip().lower() in {"1", "true", "yes"}
            try:
                self.send_bytes(build_daily_ppo_chart_png(ticker, anchor, compact=compact, dark=dark, forward=forward), "image/png")
            except self.CLIENT_DISCONNECT_ERRORS:
                self.close_connection = True
            except Exception as exc:
                self.send_html(f"<h1>Unable to build chart</h1><p>{html.escape(str(exc))}</p>", status=500)
            return
        if parsed.path == "/chart-popout" or parsed.path.startswith("/chart-popout/"):
            query = parse_qs(parsed.query, keep_blank_values=True)
            ticker = (query.get("ticker") or [""])[0].strip().upper()
            if not ticker and parsed.path.startswith("/chart-popout/"):
                ticker = unquote(parsed.path.removeprefix("/chart-popout/")).strip().upper()
            tickers = parse_tickers((query.get("tickers") or [""])[0])
            anchor = (query.get("anchor") or [""])[0].strip()
            forward = (query.get("forward") or [""])[0].strip().lower() in {"1", "true", "yes"}
            try:
                self.send_html(render_chart_popout_page(ticker, tickers, anchor, forward))
            except Exception as exc:
                self.send_html(f"<h1>Unable to open chart</h1><p>{html.escape(str(exc))}</p>", status=400)
            return
        if parsed.path == "/dashboard":
            dashboard_path = DUO_UI_STATE["dashboard_path"]
            if dashboard_path and os.path.exists(dashboard_path):
                with open(dashboard_path, "r", encoding="utf-8") as f:
                    self.send_html(normalize_dashboard_report_tabs(f.read()))
                return
            self.send_html("<h1>No dashboard has been generated yet.</h1>", status=404)
            return
        if parsed.path.startswith("/app-static/"):
            requested_name = os.path.basename(unquote(parsed.path))
            requested_path = os.path.abspath(os.path.join(SCRIPT_DIR, "static", requested_name))
            static_root = os.path.abspath(os.path.join(SCRIPT_DIR, "static"))
            if requested_path.startswith(static_root + os.sep) and os.path.isfile(requested_path):
                self.send_file(requested_path)
                return
            self.send_html("<h1>Static file not found</h1>", status=404)
            return
        dashboard_path = DUO_UI_STATE["dashboard_path"]
        active_saved_report_folder = DUO_UI_STATE.get("active_saved_report_folder") or ""
        output_folder = active_saved_report_folder or (os.path.dirname(dashboard_path) if dashboard_path else "")
        if output_folder:
            requested_rel = unquote(parsed.path.lstrip("/")).replace("/", os.sep)
            requested_path = os.path.abspath(os.path.join(output_folder, requested_rel))
            output_folder_abs = os.path.abspath(output_folder)
            if requested_path.startswith(output_folder_abs + os.sep) and os.path.isfile(requested_path):
                self.send_file(requested_path)
                return
        self.send_html("<h1>Not found</h1>", status=404)

    def do_POST(self) -> None:
        try:
            if self.path == "/live-snapshot":
                self.send_json(build_live_snapshot(self.read_json()))
                return

            if self.path == "/report-note":
                payload = self.read_json()
                rel_path = str(payload.get("path") or "")
                note_text = str(payload.get("note") or "")
                if len(note_text) > 100_000:
                    self.send_json({"error": "Report note is too large."}, status=413)
                    return
                note_path = resolve_report_note_path(rel_path)
                os.makedirs(os.path.dirname(note_path), exist_ok=True)
                with open(note_path, "w", encoding="utf-8") as handle:
                    handle.write(note_text)
                self.send_json({"ok": True})
                return

            if self.path == "/refresh-simulation":
                self.send_json({"active": False, "reason": "Full report live refresh has been replaced by /live-snapshot."}, status=410)
                return

            if self.path == "/run-screener":
                form = self.read_form()
                config = build_screener_config_from_form(form)
                screener = load_daily_screener_module()
                started_at = perf_counter()
                rows = screener.run_screener(config)
                DUO_UI_STATE["last_screener_duration_seconds"] = max(1, round(perf_counter() - started_at))
                DUO_UI_STATE["screener_config"] = config
                DUO_UI_STATE["screener_rows"] = rows
                DUO_UI_STATE["dashboard_path"] = ""
                DUO_UI_STATE["last_shortlisted_history_30d"] = []
                DUO_UI_STATE["message"] = ""
                if self.headers.get("X-Duo-Async") == "1":
                    self.send_no_content()
                    return
                self.redirect_home()
                return
            if self.path == "/run-simulator":
                form = self.read_form()
                selected_tickers = sorted({value.strip().upper() for value in form.get("ticker", []) if value.strip()})
                if not selected_tickers:
                    DUO_UI_STATE["message"] = "Select at least one ticker before running the simulator."
                    self.redirect_home()
                    return
                if len(selected_tickers) > MAX_SIMULATOR_TICKERS:
                    DUO_UI_STATE["message"] = f"Select no more than {MAX_SIMULATOR_TICKERS} tickers before running the simulator."
                    self.redirect_home()
                    return
                config = DUO_UI_STATE["screener_config"]
                if config is None:
                    DUO_UI_STATE["message"] = "Run the screener before running the simulator."
                    self.redirect_home()
                    return
                screener_context = {
                    "config": config,
                    "rows": DUO_UI_STATE["screener_rows"],
                    "selected_tickers": selected_tickers,
                }
                entry_date_str = getattr(config, "anchor_date", default_simulation_entry_date())
                started_at = perf_counter()
                dashboard_path = run_simulation(entry_date_str, selected_tickers, open_dashboard=False, screener_context=screener_context)
                DUO_UI_STATE["last_simulator_duration_seconds"] = max(1, round(perf_counter() - started_at))
                DUO_UI_STATE["dashboard_path"] = dashboard_path or ""
                DUO_UI_STATE["last_simulation_entry_date"] = entry_date_str
                DUO_UI_STATE["last_simulation_tickers"] = selected_tickers
                DUO_UI_STATE["message"] = ""
                if self.headers.get("X-Duo-Async") == "1":
                    self.send_no_content()
                    return
                self.redirect_home()
                return
            self.send_html("<h1>Not found</h1>", status=404)
        except Exception as exc:
            DUO_UI_STATE["message"] = f"Error: {exc}"
            self.redirect_home()

    def log_message(self, format: str, *args) -> None:
        safe_args = list(args)
        if safe_args and isinstance(safe_args[0], str):
            request_line = safe_args[0]
            parts = request_line.split(" ", 2)
            if len(parts) == 3 and parts[0] in {"GET", "POST", "PUT", "DELETE", "PATCH", "OPTIONS", "HEAD"}:
                method, target, proto = parts
                compact_target = target
                try:
                    parsed = urlparse(target)
                    query = parse_qs(parsed.query, keep_blank_values=True)
                    if "tickers" in query:
                        ticker_count = len([t for t in (query.get("tickers", [""])[0] or "").split(",") if t.strip()])
                        compact_target = parsed.path
                        small_parts = []
                        if query.get("ticker"):
                            small_parts.append(f"ticker={query['ticker'][0]}")
                        if query.get("anchor"):
                            small_parts.append(f"anchor={query['anchor'][0]}")
                        small_parts.append(f"tickers={ticker_count}")
                        compact_target += "?" + "&".join(small_parts)
                    elif len(target) > 220:
                        compact_target = target[:220] + "..."
                except Exception:
                    if len(target) > 220:
                        compact_target = target[:220] + "..."
                safe_args[0] = f"{method} {compact_target} {proto}"
        message = format % tuple(safe_args)
        if len(message) > 320:
            message = message[:320] + "..."
        log_info(message)


def run_duo_ui(host: str = "127.0.0.1", port: int = 8765) -> None:
    server = ThreadingHTTPServer((host, port), DuoScreenSimRequestHandler)
    url = f"http://{host}:{server.server_port}/"
    launch_url = f"{url}?reset=screener"
    log_success(f"Duo ScreenSim UI running at {url}")
    threading.Timer(0.5, lambda: webbrowser.open(launch_url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        log_warn("Stopping Duo ScreenSim UI...")
    finally:
        server.server_close()


def parse_cli_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run In-Swing simulator or Duo ScreenSim UI")
    parser.add_argument("--ui", action="store_true", help="Open the integrated screener-to-simulator browser UI.")
    parser.add_argument("--entry-date", help="Simulation entry date. Defaults to the console prompt/default.")
    parser.add_argument("--tickers", help="Comma or whitespace separated tickers for non-interactive simulation.")
    parser.add_argument("--no-open", action="store_true", help="Generate dashboard without opening it in the default browser.")
    return parser.parse_args()


def prompt_for_simulation_inputs() -> tuple[str, list[str]]:
    default_entry_date = default_simulation_entry_date()
    print(f"Entry date (e.g. 2026-08-05 or Aug 5 2026) [Default: {default_entry_date}]: ", end="")
    entry_date_str = input().strip() or default_entry_date

    config_tickers_text = ", ".join(CONFIG_INSWING_TICKERS)
    print()
    print(f"Enter Tickers [Default: {config_tickers_text if config_tickers_text else '[empty]'}]: ", end="")
    typed_tickers = input().strip()
    if typed_tickers:
        return entry_date_str, parse_tickers(typed_tickers)
    return entry_date_str, [t.strip().upper() for t in CONFIG_INSWING_TICKERS if str(t).strip()]


def main():
    args = parse_cli_args()
    if args.ui:
        run_duo_ui()
        return
    if args.entry_date or args.tickers:
        entry_date_str = args.entry_date or default_simulation_entry_date()
        tickers = parse_tickers(args.tickers or "")
    else:
        entry_date_str, tickers = prompt_for_simulation_inputs()
    run_simulation(entry_date_str, tickers, open_dashboard=not args.no_open)


if __name__ == "__main__":
    main()
