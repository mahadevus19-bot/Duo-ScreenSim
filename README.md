# Duo-ScreenSim

## Overview

Duo-ScreenSim is a market screening, analysis, and simulation/review application.

It is designed to screen stocks using configurable market and technical criteria, analyze screening results, refine results interactively, and review historical screening/simulation runs.

The application is primarily a research and analysis tool and does not directly execute live trades.

## Main Application

### BT_InSwing_Simulator_1.0.py

Main application/backend containing the majority of the screening, simulation, calculation, reporting, and application logic.

### daily_anchor_screener.py

Handles daily screening and anchor-related processing.

## Running the Application

Launch the integrated browser UI at `http://127.0.0.1:8765/`:

```bash
python BT_InSwing_Simulator_1.0.py --ui
```

## Frontend

The `static/` directory contains frontend assets including:

- JavaScript
- Charts
- Fonts
- Logos
- UI assets

## Reports

The `reports/` directory contains generated historical screening and simulation results.

## Main UI Areas

- Daily Screener
- Market View
- Refine Results
- Watchlist
- Saved Reports
- Historical Results
- Simulation Review

## Development

The application consists primarily of Python backend logic with an HTML/JavaScript frontend.

When modifying the application, preserve existing screening calculations, data processing, report generation, and UI behavior unless a change is explicitly requested.