# MSVV07 Post-Formalization Review Plan

Last updated: 2026-05-24

## Current State

- `PaperInterface.lean` is the compact human-facing surface for the AdWords
  theorem review.
- `MainTheorems.lean`, `SourceLemmas.lean`, `AdWordsExtensions.lean`,
  `AdWordsBatch.lean`, `AdWordsLowerBound.lean`, `ProofInterface.lean`, and
  `PostPaperAudit.lean` hold the proof-facing details and audit ledger.
- The paper-facing finite and limiting Theorem 8 endpoints, Theorem 9 endpoints,
  and Section 6/8 reductions are closed in Lean. Section 6 multiple slots now
  includes both the slot-expanded theorem and the source-shaped page-level
  top-`n_q` distinct-bidder competitive guarantee. Source-route LP and
  accounting declarations are retained as auxiliary proof-route audit lemmas,
  not as conditional replacements for the paper endpoints.
- `review-dashboard.sh` launches the dashboard for paper-vs-Lean review; the
  cache currently exposes 39 compact paper-facing rows in one slice.

## Review Plan

- Review the interface in theorem-number order.
- Pay special attention to whether finite error terms, small-bids limits, and
  lower-bound models match the paper statement.
- Use dashboard notes to distinguish direct paper endpoints from auxiliary
  proof-route lemmas when recording human review.

## External Validation Status

- No remaining MSVV Lean theorem caveat is recorded in this plan.
- Human dashboard review remains the external review step; a local
  `DependencyDAG.pdf` artifact is present for DAG inspection.
