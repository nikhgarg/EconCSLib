# Matching Track Handoff (2023 EC Test-of-Time)

This is the continuation plan and handoff note for the formalization of the 2023 SIGecom Test of Time paper: *The Economics of Matching: Stability and Incentives* (Roth 1982).

## Current Status
The foundational formalization layer is complete. The exact paper definitions are now securely in place, bypassing the issue of missing stable matching modules in Mathlib/CSLib.

**Completed Primitives (`EconCSLib.Matching.Basic`):**
- `Assignment M W`: Bipartite matching structure.
- `valM`, `valW`: Individual utilities representing preferences.
- `IsStable`: Formally combines Individual Rationality (IR) with the structural absence of Blocking Pairs.

**Completed Invariants (`EconCSLib.Matching.DeferredAcceptance`):**
- Defined the local step invariants of Gale-Shapley (`ManIRInvariant`, `WomanIRInvariant`, `MatchedProposedInvariant`, `WomanRejectionInvariant`, `ManProposalOrderInvariant`).
- Proved `stable_of_invariants_and_terminated`, a crucial bridging theorem showing that if those local invariants hold, and the algorithm terminates (no active proposers), the global matching perfectly satisfies `IsStable`.

**Completed Paper-Facing Ledger (`EconCSLib.Matching.MainTheorems`):**
- Formulated `paper_is_stable`, `paper_is_men_optimal`, and `paper_truthful_for_men` using explicitly typed mathematical formulas (adhering to the "No Hidden Definitions" mandate).
- Proved Theorem 1 (`paper_da_is_stable`), Theorem 2 (`paper_da_is_men_optimal`), and Theorem 3 (`paper_da_truthful_for_men`) **conditionally** against explicit algorithmic certificates (`DaProducesStableMatchingCertificate`, etc.).

## The Remaining Seam

The final remaining gap blocking this paper is the mechanical inductive proof that the `daStep` functional loop actually preserves the 5 local invariants.

The definitions for the algorithm are:
```lean
def initialDAState (M W : Type*) [Fintype W] : DAState M W
noncomputable def daStep (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W) : DAState M W
```

### Specific Blockers:
1. **Consistency Updates (`s.consistent`):** Updating the bipartite matching mappings inside `daStep` using `Function.update` creates massive goal explosions during rewrites. I created a standalone logic stub, but Lean 4's definitional equality struggles with nested `split_ifs` over `m' = m` checks when proving `s.m_match m' = some w' ↔ s.w_match w' = some m'`. 
2. **Invariant Preservation:** The lemmas `initialDAState_satisfies_invariants` and `daStep_preserves_invariants` are currently `sorry`'d. These require methodical tactic scripting across the state updates (`new_proposals`, `new_m_match`, `new_w_match`) to verify the structural inequalities.
3. **Termination:** `deferredAcceptanceState_terminated` is `sorry`'d. It requires a termination metric (e.g., the sum of the cardinalities of the `m_proposals` sets strictly decreases).

## Recommended Strategy for Next Agent

1. **Do not fight inline `daStep` updates:** Extract the bipartite assignment state update into a separate, pure helper function (e.g., `update_matching (s : DAState) (m : M) (w : W) : DAState`) and prove a standalone lemma `update_matching_consistent`. Only integrate it back into `daStep` once the standalone lemma compiles.
2. **Solve Termination First:** Since men propose to each woman at most once, use `Finset.card (s.m_proposals m)` as a strictly decreasing measure. Proving termination will close the `DaProducesStableMatchingCertificate`.
3. **Use the `lake build EconCSLib.Matching` command** scoped to the matching directory to keep your feedback loop fast.
