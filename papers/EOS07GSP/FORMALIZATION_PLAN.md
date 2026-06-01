# EOS07 Formalization Plan

Last updated: 2026-05-16

## Current State

- `PaperInterface.lean` is the paper-facing surface for the GSP theorem-review
  campaign.
- `review_slices.json` splits the large interface into bounded review batches.
- The proof-facing details and pickup notes remain in `MainTheorems.lean`,
  `README.md`, and the handoff documents.

## Review Plan

- Use `./review-dashboard.sh --slice theorem8-01` through
  `./review-dashboard.sh --slice theorem8-04` rather than reviewing all rows at
  once.
- Check that each Lean statement reflects the paper claim before relying on
  proof status.
- Use dashboard notes for any theorem whose name or hypotheses expose support
  machinery rather than a paper-level claim.

## Next Work

- Complete the four-slice human review.
- After review, consider replacing support-heavy rows with a smaller curated
  interface if the dashboard notes show repeated non-paper-facing entries.
