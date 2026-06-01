# GHW01 Formalization Plan

Last updated: 2026-06-01

## Current State

- `PaperInterface.lean` is the human-facing surface for the digital-goods
  auction statements.
- `MainTheorems.lean` contains proof-facing auction details and reusable
  support.
- `PostPaperAudit.lean` records additional validation checks.
- Current status is formalized. Theorem 9.3 is closed against the paper's
  focused set-of-bids deterministic auction convention. Theorem 8.2 is closed
  against the later journal version's monotone truthful randomized-offer
  statement using raw CDF marginal offer laws; Lean derives the adjacent
  probability monotonicity and surplus recursion directly from those CDF
  inequalities. Lean also records a two-bidder `101 > 100` threshold
  counterexample to the broader weak technical-report wording. Theorem 6.2 and
  Corollary 4.2 are closed.
- Source-version note: a 2026-06-01 web search did not find public TeX/source.
  The later journal version is the controlling source where it refines the
  preliminary text. This folder keeps the InterTrust/SODA theorem-number labels
  as a crosswalk for the existing README, theorem list, DAG, and audit aliases.

## Review Plan

- Launch `review-dashboard.sh` and review each paper-facing theorem against the
  cached source.
- Prioritize theorem-numbered claims and benchmark definitions before auxiliary
  inequalities.
- Record any source mismatch in dashboard notes with the exact paper section or
  theorem number.

## Next Work

- Optional source-curation pass: retitle the paper folder and theorem inventory
  around the journal version if maintainers want journal numbering everywhere.
  This is not a theorem-closure task; the current InterTrust/SODA labels are an
  explicit crosswalk to the journal-controlled statements.
- Optional reusable-library pass: factor the finite PMF layer-cake surplus
  lemmas behind Theorem 8.2 into a reusable stochastic-ordering API if another
  paper needs the same raw-CDF-to-surplus-recursion argument.
