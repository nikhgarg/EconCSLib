# IM05 Formalization Plan

Last updated: 2026-05-16

## Current State

- `PaperInterface.lean` exposes a compact set of closed deterministic claims
  for review.
- `MainTheorems.lean`, `ProofStrategy.md`, and `NEXT_AGENT_HANDOFF.md` document
  the broader incomplete probabilistic campaign.
- The paper is not complete: Algorithm 4.1/4.2 and Section 6 probability
  construction work remains.

## Review Plan

- Review the compact deterministic interface first.
- Do not mark the probabilistic theorems as paper-reviewed until they have
  dedicated `PaperInterface.lean` rows.
- Use dashboard notes to distinguish closed deterministic claims from
  conditional probability endpoints.

## Next Work

- Refresh the dashboard cache.
- Add paper-facing rows for Algorithm 4.1/4.2 only after the source-completion
  certificate target stabilizes.
