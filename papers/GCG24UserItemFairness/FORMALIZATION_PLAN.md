# GCG24 Formalization Plan

Last updated: 2026-05-16

## Current State

- `PaperInterface.lean` lists the current user-item fairness paper-facing
  propositions and theorems.
- `MainTheorems.lean` and sibling modules contain the proof-facing development.
- This folder is active; coordinate proof edits with other agents.

## Review Plan

- Use `review-dashboard.sh` for paper-statement validation before treating a
  theorem as reviewed.
- Keep reviewer notes focused on whether the Lean hypotheses and conclusion
  match the paper wording.
- If a mismatch is found, update the interface contract before changing proof
  internals.

## Next Work

- Refresh the dashboard cache before the next human review session.
- Keep proof changes scoped to the active theorem under development.
