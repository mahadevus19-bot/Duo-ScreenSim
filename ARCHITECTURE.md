# Duo-ScreenSim Architecture

Duo-ScreenSim is a Python-based equity screening, technical analysis, and portfolio simulation suite. It provides a standalone daily anchor screener, an integrated browser UI, and a 4-day (T0 to T3) in-swing portfolio backtest simulator. It is an analytical research and review tool and does not execute live broker orders.

---

## 1. System Components & Architecture

```
+---------------------------------------------------------------------------------------------------+
|                                   BROWSER FRONTEND (HTML / CSS / JS)                              |
|                                                                                                   |
|  - Daily Screener Form & Progress Bar      - Interactive Results Table (Filter/Sort/Multi-select) |
|  - TradingView Lightweight Charts v5       - Watchlist Card & Mini-Chart Viewer                   |
|  - Standalone Multi-Tab Report Dashboard   - SVG Time-Series Portfolio Replay                     |
|  - Saved Reports & Notes Manager           - Finviz-Style CSS Design System                       |
+-------------------------------------------------+-------------------------------------------------+
                                                  | HTTP / JSON / Form POST (Port 8765)
                                                  v
+---------------------------------------------------------------------------------------------------+
|                                PYTHON BACKEND (BT_InSwing_Simulator_1.0.py)                       |
|                                                                                                   |
|  - HTTP Server: ThreadingHTTPServer & BaseHTTPRequestHandler (DuoScreenSimRequestHandler)        |
|  - In-Memory State: DUO_UI_STATE & DAILY_CHART_JSON_CACHE                                         |
|  - Dynamic Module Loader: Imports daily_anchor_screener.py dynamically via importlib             |
|  - Simulation Engine: 10-minute intraday bar processing, T0 15:50 Entry -> T3 15:50 Exit          |
|  - Matplotlib / mplfinance Engine: Static PNG rendering with custom session-only axes             |
|  - Excel Reporter: openpyxl workbook generator                                                   |
+-------------------------------------------------+-------------------------------------------------+
                                                  | REST API over HTTPS
                                                  v
+---------------------------------------------------------------------------------------------------+
|                                 EXTERNAL MARKET DATA: Massive.com / Polygon.io                    |
|                                                                                                   |
|  - Grouped Daily Aggregates (US Equities)       - Intraday Aggregates (1-min & 10-min bars)       |
|  - Ticker Reference & Weighted Shares           - Daily Technical Indicators (PPO, EMA)           |
+---------------------------------------------------------------------------------------------------+
```

---

## 2. Core Files & Responsibilities

| File / Directory | Purpose |
|---|---|
| `BT_InSwing_Simulator_1.0.py` | **Main Application & Simulator Engine (~7,800 lines)**<br>- Runs the `ThreadingHTTPServer` on `127.0.0.1:8765`<br>- Renders the SPA UI (`render_ui_page`) and chart popups (`render_chart_popout_page`)<br>- Houses the TradingView Lightweight Charts JavaScript client (`DUO_CHART_LIB_JS`)<br>- Executes the 4-day portfolio simulation (`run_simulation`)<br>- Produces Matplotlib PNG charts and standalone dashboard HTML files (`write_stock_chart_viewer`)<br>- Manages saved report browsing (`get_saved_dashboard_reports`) |
| `daily_anchor_screener.py` | **Standalone Anchor Screener (~1,200 lines)**<br>- Contains `PolygonSession` for robust HTTP communication with rate limiting and retries<br>- Implements the 7-stage screening funnel and technical indicator math<br>- Outputs standalone Excel reports with `Master List` and `rvol` validation tabs<br>- Can be run directly from CLI or imported by `BT_InSwing_Simulator_1.0.py` |
| `static/` | **Frontend Assets**<br>- `lightweight-charts.standalone.production.js` (TradingView Lightweight Charts v5.0.9)<br>- Web fonts (`ibm-plex-sans-latin-*.woff2`)<br>- Branding logos (`nras-logo.png`, `nras-logo-transparent.png`) |
| `reports/` | **Generated Artifacts**<br>- Date-partitioned run directories (e.g. `reports/Mon 31 Aug 2026 Runs/`)<br>- Contains dashboard HTML files, Excel workbooks, raw 10m CSVs, PNG charts, and user notes |
| `.env` | **Configuration**<br>- Contains `POLYGON_API_KEY` |

---

## 3. Data & Execution Flows

### A. Screener Execution Flow
1. User enters filters in UI (or CLI) and submits `POST /run-screener`.
2. `daily_anchor_screener.py` fetches bulk daily bars for all US tickers for the anchor date.
3. Candidate filtering pipeline:
   - **Filter 1 (Price)**: `Close >= MIN_PRICE` (default: $2.00)
   - **Filter 2 (Volume)**: `Volume >= MIN_VOLUME` (default: 1M)
   - **Pre-Filter (Reference)**: Common stock check (`type == "CS"`) and Market Cap calculation (`shares * close` or reference market cap between `MCAP_MIN` and `MCAP_MAX`)
   - **Filter 4 (Velocity)**: 10-day ATR % of price (`(ATR10 / Close) * 100 >= MIN_ATR10`)
   - **Filter 5 (RSI)**: 14-day Wilder RSI (`RSI14 >= MIN_RSI14`)
   - **Filter 6 (PPO > Signal)**: 12/26/9 PPO line > Signal line (optional)
   - **Filter 7 (PPO Cross)**: PPO histogram crossed from negative to positive on anchor day (optional)
4. Calculated indicators (21-EMA, Keltner position zone, 4/9/18 SMAs, 20-day RVOL, Breakout lookback) are attached to passed rows.
5. Filtered candidates are stored in `DUO_UI_STATE["screener_rows"]` and displayed in the frontend data grid.

### B. Simulation Execution Flow
1. User selects 1 to 20 candidate tickers and triggers `POST /run-simulator`.
2. `run_simulation()`:
   - Resolves anchor date as T0 (adjusting for weekends and US market holidays).
   - Computes T3 (3rd subsequent trading day) at 15:50 ET exit target.
   - Downloads 10-minute intraday bars for selected tickers and benchmarks (`SPY`, `QQQ`, `IWM`).
   - Replaces entry bar with exact 15:50 1-minute close (or latest prior bar).
   - Allocates $250,000 capital equally across symbols (`allocation = 250000 / N`).
   - Builds continuous time-aligned portfolio value and net PnL curves.
   - Computes exit values at T3 15:50 close (or latest available bar).
3. Artifacts generated:
   - `4_Report <Timestamp>.xlsx`: Sheets for `Portfolio History 10min`, `Symbol Summary`, and `Skipped Symbols`.
   - `3_<Ticker> Data 10m <Artifact>.csv`: Raw intraday bars for each symbol.
   - `2_Portfolio Chart 10m <Artifact>.png`: Matplotlib portfolio curve with session-only axis.
   - `2_All Symbols Chart 10m <Artifact>.png`: Normalized comparative stock line chart.
   - `2_<Ticker> Chart 10m <Artifact>.png`: Per-symbol candlestick + PnL chart.
   - `Dashboard <Date Range> <Suffix>.html`: Standalone, interactive HTML report with embedded datasets.

### C. Live Market Hours Polling
During trading hours (9:30 AM – 4:00 PM ET on T1–T3), the active dashboard polls `GET /live-snapshot` every 60 seconds to refresh open position values using 1-minute recent bar closes.

---

## 4. Technical Indicator & Calculation Conventions

- **ATR (Average True Range)**: 10-period Wilder smoothed true range (`alpha = 1/10`).
- **RSI**: 14-period Wilder smoothed Relative Strength Index.
- **PPO (Percentage Price Oscillator)**: Standard 12-period fast EMA, 26-period slow EMA, 9-period signal EMA (`PPO = ((EMA12 - EMA26) / EMA26) * 100`). Warm-up lookback uses up to 1,200 calendar days to match charting platforms.
- **Keltner Bands (Upper 1–7, Lower 1–7)**: Centered on 21-period EMA, spaced by integer multiples of 10-period ATR (`EMA21 ± k * ATR10`).
- **Daily Closing Position**: Position categorized relative to EMA21 and Keltner bands (`>U7`, `U6-U7`, ..., `Mid-U1`, `Mid-L1`, ..., `<L7`).
- **RVOL (Relative Volume)**: Current anchor volume divided by the 20-day average volume of the preceding 20 trading sessions (excluding the anchor day).
- **Triple MA Bullish**: Evaluates whether `SMA4 > SMA9 > SMA18`.
- **Breakout Comment**: Longest lookback window (from `5D high` up to `1Y high`) whose prior highs are exceeded by the anchor close.

---

## 5. Backend-Frontend HTTP API Reference

The internal HTTP server runs on `http://127.0.0.1:8765` without external web framework dependencies.

| Route | Method | Payload / Params | Description |
|---|---|---|---|
| `/` | `GET` | `?reset=screener` | Renders the primary Single Page Application UI |
| `/run-screener` | `POST` | Form data (`X-Duo-Async: 1`) | Executes screener pipeline and updates in-memory rows |
| `/run-simulator` | `POST` | Form data (`ticker` array) | Runs the T0->T3 simulation and generates dashboard report |
| `/ticker-data` | `GET` | `ticker`, `anchor`, `compact`, `forward` | Returns JSON payload of daily candles, indicators, and channels |
| `/ticker-chart` | `GET` | `ticker`, `anchor`, `theme`, `compact` | Returns server-rendered Matplotlib/mplfinance PNG chart |
| `/chart-popout` | `GET` | `ticker`, `tickers`, `anchor`, `forward` | Renders interactive TradingView Lightweight Charts popout window |
| `/dashboard` | `GET` | — | Serves the active run's generated dashboard HTML |
| `/saved-reports` | `GET` | — | Renders the catalog of historical simulation runs |
| `/saved-report` | `GET` | `path`, `mode` | Opens a specific historical dashboard HTML report |
| `/report-note` | `GET` / `POST` | `path`, `note` | Loads or saves markdown/text notes for a specific report run |
| `/live-snapshot` | `GET` / `POST` | `positions` | Returns updated P/L snapshot during active market hours |
| `/app-static/*` | `GET` | — | Serves static assets from `static/` with caching headers |

---

## 6. Directory Structure & Naming Conventions

```
Duo- ScreenSim/
├── .env                              # POLYGON_API_KEY
├── ARCHITECTURE.md                   # This document
├── README.md                         # Project summary
├── BT_InSwing_Simulator_1.0.py       # Main application & simulator
├── daily_anchor_screener.py          # Standalone screener
├── static/                           # Client JS libraries, fonts, logos
│   ├── lightweight-charts.standalone.production.js
│   ├── ibm-plex-sans-latin-wght-normal.woff2
│   ├── ibm-plex-sans-latin-wght-italic.woff2
│   └── nras-logo-transparent.png
└── reports/                          # Generated simulation runs
    └── <Day DD Mon YYYY Runs>/       # Partitioned by run date
        ├── Dashboard <Range> <Suffix>.html
        └── meta data/
            ├── 4_Report <Date Timestamp>.xlsx
            ├── 2_Portfolio Chart 10m <Artifact>.png
            ├── 2_All Symbols Chart 10m <Artifact>.png
            ├── 2_<Ticker> Chart 10m <Artifact>.png
            ├── 3_<Ticker> Data 10m <Artifact>.csv
            └── Dashboard <Range> <Suffix> Notes.txt
```

---

## 7. Important Development Rules & Invariants

1. **No Order Execution**: This codebase does not place trades or interface with brokerage execution APIs.
2. **Deterministic File Naming**: Historical report discovery and notes persistence rely on exact filename patterns (`Dashboard <Range> <Suffix>.html` and `meta data/`). Do not alter artifact naming formats without updating regex loaders in `get_saved_dashboard_reports()` and `resolve_report_note_path()`.
3. **Data Field Consistency**: JavaScript table rendering, sorting, and client-side filtering depend on exact uppercase column names (`TICKER`, `PRICE`, `VOLUME`, `RVOL`, `MCAP`, `DAILY_CHANGE_%`, `DROP_FROM_HIGH_%`, `RSI14`, `DAILY_CLOSING_POSITION`, `PPO`, `PPO_SIGNAL`, `PPO_HISTOGRAM`, `PPO_GT_SIGNAL`, `PPO_CROSS`, `TRIPLE_MA_BULLISH`, `COMMENT`).
4. **Market Calendar Synchronization**: US market holidays are hardcoded in `MARKET_HOLIDAYS` in both `BT_InSwing_Simulator_1.0.py` and `daily_anchor_screener.py`. Any new holiday additions must be updated in both files.
5. **Chart Autoscale Isolation**: In TradingView Lightweight Charts popout views, Keltner Channel series use `autoscaleInfoProvider: () => null` so the price axis scales cleanly to candlestick price action without being distorted by outer ATR bands.
