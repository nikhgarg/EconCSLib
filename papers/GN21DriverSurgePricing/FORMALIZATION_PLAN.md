# GN21 Formalization Plan

Last updated: 2026-05-16

## Current State

- `PaperInterface.lean` exposes a compact review surface for central
  single-state source claims and the current exact-bracket pointwise-transfer
  Theorem 3 route.
- `MainTheorems.lean` remains the large proof-facing ledger for the continuous
  and dynamic driver-surge development.
- The folder has active proof work; avoid broad rewrites while other agents are
  editing `MainTheorems.lean`.

## Review Plan

- Start human review with `PaperInterface.lean`; do not review the full
  `MainTheorems.lean` ledger directly.
- Treat the current interface as a curated starter surface, not as complete
  coverage of the paper.
- Add more paper-facing interface rows only when the corresponding source claim
  has a stable Lean statement.

## Next Work

- Refresh the dashboard cache.
- Extend the interface after the active proof campaign stabilizes the dynamic
  IC theorem statements.
