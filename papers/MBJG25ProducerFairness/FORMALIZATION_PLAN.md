# MBJG25 Formalization Plan

Last updated: 2026-05-16

## Current State

- `PaperInterface.lean` is the human-facing surface for the Bayesian rating
  fairness paper.
- `MainTheorems.lean` and sibling modules contain the proof-facing development.
- The interface is already structured by paper definitions and theorem groups.

## Review Plan

- Use `review-dashboard.sh` to review theorem rows in paper order.
- Check that theorem hypotheses expose only the model assumptions needed by the
  source claim.
- Record source wording mismatches in dashboard notes before changing proofs.

## Next Work

- Refresh the dashboard cache.
- Keep `PaperInterface.lean` as the source of truth for human statement review.
