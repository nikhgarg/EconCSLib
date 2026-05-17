# GHW01 Formalization Plan

Last updated: 2026-05-16

## Current State

- `PaperInterface.lean` is the human-facing surface for the digital-goods
  auction statements.
- `MainTheorems.lean` contains proof-facing auction details and reusable
  support.
- `PostPaperAudit.lean` records additional validation checks.

## Review Plan

- Launch `review-dashboard.sh` and review each paper-facing theorem against the
  cached source.
- Prioritize theorem-numbered claims and benchmark definitions before auxiliary
  inequalities.
- Record any source mismatch in dashboard notes with the exact paper section or
  theorem number.

## Next Work

- Refresh the dashboard cache before review.
- Fold any repeated reviewer concerns back into `PaperInterface.lean`.
