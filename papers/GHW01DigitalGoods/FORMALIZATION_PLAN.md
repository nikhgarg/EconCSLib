# GHW01 Formalization Plan

Last updated: 2026-06-10

## Current State

- `PaperInterface.lean` is the human-facing surface for the digital-goods
  auction statements.
- `MainTheorems.lean` contains proof-facing auction details and reusable
  support.
- `PostPaperAudit.lean` records additional validation checks.
- Current status is formalized for the SODA paper. Theorem 9.3 is closed
  against the paper's focused set-of-bids deterministic auction convention.
  Theorem 8.2 uses the later journal version's refined monotone truthful
  randomized-offer wording with raw CDF marginal offer laws; Lean derives the
  adjacent probability monotonicity and surplus recursion directly from those
  CDF inequalities. Theorem 6.2 and Corollary 4.2 are closed.
- Source-version note: a 2026-06-01 web search did not find public TeX/source.
  The later journal version is used only where it refines Theorem 8.2's
  preliminary Section 8 wording. The folder identity remains the SODA paper.

## Review Plan

- Launch `review-dashboard.sh` and review each paper-facing theorem against the
  cached source.
- Prioritize theorem-numbered claims and benchmark definitions before auxiliary
  inequalities.
- Record any source mismatch in dashboard notes with the exact paper section or
  theorem number.

## Next Work

- Optional source-curation pass: add journal-only results only if maintainers
  want a separate full journal-paper inventory. This is not a theorem-closure
  task for the current SODA paper target.
- Optional reusable-library pass: factor the finite PMF layer-cake surplus
  lemmas behind Theorem 8.2 into a reusable stochastic-ordering API if another
  paper needs the same raw-CDF-to-surplus-recursion argument.
