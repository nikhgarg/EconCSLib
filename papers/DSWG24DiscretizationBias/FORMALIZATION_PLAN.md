# DSWG24 Formalization Plan

Last updated: 2026-05-16

## Current State

- `PaperInterface.lean` is the paper-facing review surface for the current
  Theorem 1 and Theorem 2 claims.
- `MainTheorems.lean` contains the proof-facing development and should remain
  secondary for human paper-statement review.
- `review-dashboard.sh` launches the trace-backed review UI for this paper.

## Review Plan

- Review every theorem in `PaperInterface.lean` against the cached source paper.
- Record statement matches and mismatches through the dashboard; do not treat
  unreviewed rows as paper-faithful.
- If a statement mismatch is found, update `PaperInterface.lean` first, then
  decide whether the proof-facing theorem needs refactoring.

## Next Work

- Complete the initial dashboard review pass.
- Refresh `.review_traces/paper_interface_cache.json` before a human review
  session.
