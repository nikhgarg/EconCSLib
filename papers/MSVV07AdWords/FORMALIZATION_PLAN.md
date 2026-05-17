# MSVV07 Formalization Plan

Last updated: 2026-05-16

## Current State

- `PaperInterface.lean` is the human-facing surface for the AdWords theorem
  review.
- `MainTheorems.lean`, `AdWordsExtensions.lean`, and `AdWordsLowerBound.lean`
  hold proof-facing details.
- `review-dashboard.sh` launches the dashboard for paper-vs-Lean review.

## Review Plan

- Review the interface in theorem-number order.
- Pay special attention to whether finite error terms, small-bids limits, and
  lower-bound models match the paper statement.
- Use dashboard notes to flag any statement that is an auxiliary finite
  analogue rather than a direct paper theorem.

## Next Work

- Refresh the dashboard cache.
- After initial review, consider adding review slices if the interface becomes
  too large for one sitting.
