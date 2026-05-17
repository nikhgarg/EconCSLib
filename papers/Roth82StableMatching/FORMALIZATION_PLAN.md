# Roth82 Formalization Plan

Last updated: 2026-05-16

## Current State

- `PaperInterface.lean` is the human-facing surface for the Roth stable-matching
  theorem review.
- `PostPaperAudit.lean` records additional validation checks.
- Matching-library support lives in `EconCSLib/Markets/Matching`.

## Review Plan

- Review all paper-facing theorem rows through `review-dashboard.sh`.
- Check that complete-domain caveats are present where the Lean statement is
  narrower than the printed theorem.
- Record any paper-statement mismatch before editing shared matching support.

## Next Work

- Refresh the dashboard cache.
- Use review notes to decide whether any theorem should be restated at a more
  paper-natural level.
