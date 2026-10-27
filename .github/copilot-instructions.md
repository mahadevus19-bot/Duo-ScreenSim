# Copilot Development Instructions

## Project Context

This is a Python-based market screening, analysis, and simulation/review application.

The application is primarily used to screen stocks, analyze market data and technical indicators, refine screening results, and review historical screening/simulation results.

It is NOT an automated live trading/order-execution system.

## Main Files

- `BT_InSwing_Simulator_1.0.py`
  - Main screening/simulation application.
  - Approximately 8,000 lines.
  - Contains significant portions of the backend processing, screening logic, calculations, simulation logic, reporting, and application functionality.

- `daily_anchor_screener.py`
  - Daily screening and anchor-related logic.
  - Approximately 1,000 lines.

- `static/`
  - Frontend assets including JavaScript libraries, charts, fonts, and logos.

- `reports/`
  - Generated screening/simulation reports and historical run output.

## Application Areas

The application currently includes functionality such as:

- Daily Screener
- Market View
- Result refinement/filtering
- Stock/ticker search
- Watchlist selection
- Saved Reports
- Historical screening/simulation review
- Technical indicator analysis
- HTML/JavaScript-based visualization

## General Development Rules

1. Before modifying code, understand the existing implementation and its dependencies.

2. Prefer the smallest safe change that solves the requested problem.

3. Do not perform large refactoring unless explicitly requested.

4. Do not rewrite working code simply to make it look cleaner.

5. Preserve existing behavior unless the requested change explicitly requires different behavior.

6. When modifying a function, inspect its callers and related functions before making changes.

7. Do not invent APIs, data fields, configuration values, or application behavior. Inspect the existing code first.

8. Do not remove existing functionality unless explicitly requested.

9. Avoid unnecessary changes to unrelated files.

10. Reuse existing patterns and components where practical.

## Screening and Simulation Logic

Treat screening criteria, indicator calculations, ranking logic, simulation calculations, and historical-result processing as important application logic.

Do not change existing calculation or screening behavior unless explicitly requested.

When a requested change affects screening or simulation results, identify the potential behavioral impact before implementing it.

## Frontend / UI

The frontend is an important part of the application.

When modifying HTML, JavaScript, CSS, tables, filters, charts, navigation, or other UI components:

- Preserve existing functionality.
- Maintain the existing visual design language.
- Reuse existing components and styles where practical.
- Avoid unnecessary changes to unrelated UI elements.
- Ensure changes work with the existing backend/data flow.

## Debugging

When debugging:

- Find the root cause rather than masking the error.
- Inspect surrounding code and data flow.
- Do not introduce broad exception handling just to suppress errors.
- Do not change unrelated behavior as a workaround.
- Explain the root cause and proposed fix.

## Code Changes

Before making a significant change:

1. Identify the relevant files.
2. Identify the relevant functions/classes.
3. Trace important callers and dependencies.
4. Briefly explain the proposed approach.
5. Make the smallest appropriate modification.

After making changes:

1. Check for syntax errors.
2. Check for obvious regressions.
3. Review the changed code for unintended behavior.
4. Clearly summarize what was changed.

## Communication

For complex changes, understand the existing implementation before modifying it.

Do not immediately rewrite large portions of the code.

If there is ambiguity that could materially affect application behavior, ask for clarification rather than guessing.