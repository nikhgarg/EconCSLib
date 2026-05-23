# Roth82 Formalization Plan

Last updated: 2026-05-23

## Current State

- `PaperInterface.lean` is the compact human-facing surface for Roth's paper
  definitions, Theorems 1--7, Lemmas 1--2, and Corollary 5.1. It is a 27-row
  dashboard surface: 17 paper definition/object rows and 10 named-result rows.
- `PostPaperAudit.lean` records source-numbered audit endpoints for the named
  source results; Theorem 1 has both the generic stable-outcome endpoint and the
  source-domain stable-complete endpoint.
- `MainTheorems.lean` contains the proof scripts and older compatibility
  wrappers. The source-domain endpoints are closed; the compatibility wrappers
  are not needed to mark any named source result complete.
- Theorem 3 and Theorem 7 are now exposed through strict-profile source
  endpoints, so the final paper-facing impossibility and arbitrary-`k`
  statements no longer rely on broad non-strict procedure predicates.
- Roth's quota/many-to-one general-matching discussion is recorded as a scope
  note: this folder follows the paper's stated route of using the strict
  one-to-one marriage problem as the formal representation, rather than adding
  a separate quota API.
- Matching-library support lives in `EconCSLib/Markets/Matching`.

## Completed Route

- The cached text inventory in `Roth82StableMatching.txt` has been reconciled
  with the README, paper interface, post-paper audit ledger, and final
  validation report.
- All named source results in the cached Roth 1982 text are marked
  `formalized` in `README.md`.
- The strict finite marriage-domain assumptions used by Lean match Roth's
  Section 2 source domain; they are not recorded as extra caveats.
- The review dashboard surface has been trimmed to 27 source-facing rows:
  17 paper definitions/formatted objects and 10 named-result endpoints. The
  ignored `.review_traces` dashboard log is human-review state; it is not
  clean-checkout validation evidence and may need human re-saving after
  interface wording changes.

## Validation Commands

- `lake build Roth82StableMatching.MainTheorems Roth82StableMatching.PaperInterface Roth82StableMatching.PostPaperAudit`
- `lake build Roth82StableMatching`
- `papers/Roth82StableMatching/review-dashboard.sh --check` only to inspect
  local human-review freshness; do not use it as tracked proof validation.

## Optional Future Work

- Extract generic direct-mechanism incentive predicates, finite
  serial-dictatorship APIs, and rank-based report-misrepresentation predicates
  from the Roth namespace into `EconCSLib` only if another paper needs them.
- Re-render the ignored local `DependencyDAG.pdf` after any future
  theorem-surface change to the tracked `DependencyDAG.tex`.
