# KR21 Monoculture Handoff

Last updated: 2026-05-15

## Scope

This handoff is for continuing the formalization of Kleinberg-Raghavan,
*Algorithmic Monoculture and Social Welfare*, specifically the arbitrary-size
Mallows remaining-set part of Theorem 4.

The user wants this paper finished before moving to another paper. Do not move
to another paper unless Theorem 4 is genuinely closed or there is a clear
blocker that cannot be resolved with sustained work.

## Immediate Pickup For A Stronger Model

Start with this exact target in `papers/KR21Monoculture/Sequential.lean`:

```lean
ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes n qMore qLess
```

This is the remaining arbitrary-size, endpoint-present first-choice weighted
inequality.  It is not a routine wrapper problem.  The surrounding reductions
are already packaged: if this target is proved for every `n`, then
`ReflMallowsBestInSetPrefixCutDominance.of_extremeWeighted` should carry the
arbitrary prefix-cut dominance proof, and the existing prefix/expected-utility
bridges can finish the paper-facing Theorem 4 route.

Use the adjacent-gap form first:

```lean
firstChoiceBranchWeighted_eq_adjacent_gap_sum_boundary
```

The easy adjacent cases are already formalized:

- outside/outside adjacent first-choice gaps vanish;
- left-in-remaining-and-before-cut terms are nonnegative;
- right-in-remaining-and-after-cut terms are nonnegative;
- both-in-remaining adjacent terms are nonnegative.

The remaining hard work is aggregate cancellation of the two bad mixed-boundary
orientations:

- outside before a good remaining candidate, rewritten by
  `firstChoiceBranchWeighted_adjacentGapTerm_eq_tail_sub_partition`;
- bad remaining candidate before outside, rewritten by
  `firstChoiceBranchWeighted_adjacentGapTerm_eq_neg_tail`.

The most promising proof shape is a hole/block decomposition of the remaining
set in the adjacent-boundary sum.  Do not try to prove every adjacent term or
every first-choice pair term nonnegative.

## Current Git State

Most recent KR21 proof commits:

- `75d298b` `Package KR21 extreme weighted reduction`
- `a561e45` `Add KR21 adjacent-boundary bridge`
- `551dd50` `Close monoculture weighted first-choice base`

The repo is a shared dirty worktree.  At this handoff, no Lean proof edit is
intended outside the KR21 target unless the next agent deliberately changes it.
Treat unrelated dirty files as user/other-agent work.  If committing, stage only
the files intentionally edited for this proof.

Main KR21 pickup files:

- `papers/KR21Monoculture/Sequential.lean`
- `papers/KR21Monoculture/HANDOFF.md`
- `papers/KR21Monoculture/README.md`
- `skills/econcs-formalizer/references/proof-markets-social-choice.md`

Only update the skill reference if the proof attempt produces genuinely reusable
Mallows/ranking guidance.  Keep theorem-specific details out of the always-loaded
`SKILL.md`.

## Source Of Truth

Use these files first:

- Paper README/status: `papers/KR21Monoculture/README.md`
- Paper-facing wrappers: `papers/KR21Monoculture/MainTheorems.lean`
- Main proof infrastructure: `papers/KR21Monoculture/Sequential.lean`
- Proof-technique notes: `skills/econcs-formalizer/references/proof-markets-social-choice.md`

Do not rely on older author-wide status reports as source of truth. The KR21
README and the Lean declarations are the current status.

Cached paper sources are available and intentionally ignored by git:

- `papers/KR21Monoculture/sources/2101.05853.pdf`
- `papers/KR21Monoculture/sources/2101.05853.html`
- `papers/KR21Monoculture/sources/2101.05853.txt`

## Verification Baseline

The targeted build passed during the 2026-05-15 handoff check:

```bash
lake build KR21Monoculture.Sequential
```

The same check found no actual `sorry`, `admit`, or `axiom` in the KR21 Lean
files; text hits for "conditional" are documentation/docstring status notes.

`KR21Monoculture.MainTheorems` has also passed in this campaign, but it replays
older unrelated warnings/info from `KR21Monoculture/RUM.lean`. Those warnings
are not blockers for the Mallows/Theorem 4 route.

Before continuing after a fresh checkout/session, run:

```bash
git status --short
lake build KR21Monoculture.Sequential
```

## High-Level Estimate

For the current model, this is probably beyond a quick close.  For a stronger
model, the handoff is intentionally narrow: prove the endpoint-present weighted
target, then wire it through the existing reductions.  The theorem still looks
true; the risk is proof discovery and proof engineering, not an obvious false
statement.

## Current Theorem 4 Status

Closed / verified categories:

- All histories with at most two remaining candidates.
- Center-convex remaining intervals.
- Co-singleton histories, with `algorithm.q < 1`.
- All nonempty histories in the three-candidate Mallows universe.
- Four-candidate identity-center fiber MLR with `qLess < 1`.
- Four-candidate Mallows remaining-utility dominance with `algorithm.q < 1`.
- Three- and four-candidate all-human weak optimality wrappers.
- Stepwise dominance to all-human sequential optimality and strict nonterminal
  uniqueness wrappers.

Still open:

- Arbitrary-size, arbitrary nonconvex remaining-set lift for Theorem 4.

The current route has narrowed beyond the older first-choice-weighted route.
The verified absent-extreme recurrences reduce every same-size prefix-cut step
to the case where:

- the center-best candidate `0` is still in the remaining set;
- the center-worst candidate `reflLastCandidate` is still in the remaining set;
- the cut is nontrivial, `0 < cut` and `cut <= n + 2`.

The remaining Lean target is:

```lean
ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes n qMore qLess
```

Once this target is proved for every `n`, the verified induction step

```lean
ReflMallowsBestInSetPrefixCutDominance.succ_of_extremeWeighted
```

is packaged by

```lean
ReflMallowsBestInSetPrefixCutDominance.of_extremeWeighted
```

and will carry the arbitrary prefix-cut dominance proof. Then feed prefix-cut
dominance into the existing prefix-sum and expected-utility bridges.

## Important Declarations

Useful older declarations in `Sequential.lean`:

- `candidateRankPowerSum_sub_rankPower_nonneg`
- `candidateRankWeightedAverage_cross_eq_pair_sum`
- `firstChoiceBranchBracketSum_eq_offDiagonal`
- `firstChoiceBranchBracketSum_eq_complementPower`
- `firstChoiceBranchBracketSum_eq_diag_add_weighted`
- `firstChoiceBranchBracketSum_nonneg_of_diag_weighted`
- `firstChoiceBranchWeighted_eq_pair_sum`
- `firstChoiceBranchWeighted_eq_adjacent_gap_sum_boundary`
- `ReflMallowsBestInSetPrefixCutFirstChoiceWeighted`
- `ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum.of_dominance_weighted`
- `ReflMallowsBestInSetPrefixCutDominance.of_firstChoiceWeighted`
- `reflMallowsBestInSetPrefixSum_cross_of_firstChoiceWeighted`
- `expectedBestInSet_le_of_mallows_firstChoiceWeighted`

New declarations after the absent-extreme reduction:

- `bestInSet_rankingPeelWorstOrderEquiv_of_last_mem_tail_before`
- `bestInSet_rankingPeelWorstOrderEquiv_of_last_mem_tail_not_before`
- `bestInSet_rankingPeelWorstOrderEquiv_of_last_mem_init_empty`
- `candidateRankStrictSuffixReversePowerSum`
- `candidateRankReversePowerSum_eq_powerSum`
- `candidateRankStrictSuffixReversePowerSum_eq_rev_prefix`
- `candidateRankStrictSuffixReversePowerSum_cross_nonneg`
- `bestInSetPrefixCutTailWorstInsertPositionValue`
- `bestInSetPrefixCutTailWorstInsertPositionValue_insertPositionSum`
- `bestInSetPrefixCutIndicator_rankingPeelWorstOrderEquiv_of_last_mem`
- `reflMallowsBestInSetPrefixCutSum_eq_init_worstInsertPositionValue_of_last_mem`
- `bestInSetPrefixCutTailWorstInsertPositionValue_cross_nonneg`
- `reflMallowsPayoffSum_tailWorstInsertPositionValue_insertion_cross_nonneg`
- `reflMallowsBestInSetPrefixCutSum_cross_of_last_mem_from_init_fixed_worstInsertPositionValue`
- `bestInSetPrefixCutIndicator_rankingPeelWorstOrderEquiv_of_last_not_mem`
- `reflMallowsBestInSetPrefixCutSum_eq_init_of_last_not_mem`
- `reflMallowsBestInSetPrefixCutSum_cross_of_last_not_mem_from_init`
- `reflMallowsBestInSetPrefixCutSum_cross_of_extreme_not_mem_from_prev`
- `ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes`
- `ReflMallowsBestInSetPrefixCutDominance.succ_of_extremeWeighted`
- `ReflMallowsBestInSetPrefixCutDominance.of_extremeWeighted`

In `MainTheorems.lean`:

- `paper_theorem4_remaining_utility_dominance_of_firstChoiceWeighted`

## Counterexample Search And Theorem Risk

Finite searches were run before this handoff update.

Exact paper-level target searched: enumerate all rankings, all nonempty
remaining sets, and all prefix cuts through seven candidates. Tested
`0 < qMore < qLess <= 1` pairs:

```text
(0.05, 0.1), (0.1, 0.3), (0.3, 0.7), (0.5, 0.85),
(0.9, 1.0), (0.2, 1.0)
```

Also tested broader positive inverse-Mallows parameters:

```text
(1.0, 2.0), (2.0, 3.0), (0.5, 1.2), (0.1, 10.0)
```

No counterexample was found.

The stronger current first-choice weighted target was also brute-forced on all
nonempty remaining sets and cuts through seven candidates, including:

```text
(0.05, 0.1), (0.1, 0.3), (0.3, 0.7), (0.5, 0.85),
(0.9, 1.0), (1.0, 2.0), (0.1, 10.0)
```

No counterexample was found there either. This makes the theorem look true and
the current target viable. The main risk is not a false theorem but a proof
route that is too abstract and loses the best-in-set structure.

Additional local sanity checks during the 2026-05-15 review:

- Endpoint-present instances of the weighted target were again checked on small
  finite universes with representative positive `qMore < qLess`; no
  counterexample appeared.
- Outside first-choice branch values are not constant across all holes.  For
  example, with first-choice universe size `5`, remaining set `{0, 2, 4}`,
  cut `1`, and tail parameter `q = 0.5`, the branch values are
  `[4.921875, 3.0, 0.0, 3.375, 0.0]`; the outside branches at `1` and `3`
  differ.
- Individual first-choice pair terms can be negative even in endpoint-present
  cases.  For universe size `4`, remaining set `{0, 1, 3}`, cut `1`,
  `qMore = 0.3`, `qLess = 0.5`, the less-tail branch values
  `[2.625, 0.0, 1.5, 0.0]` make the pair term for `(1, 2)` negative.

These checks reinforce the current route: use aggregate cancellation, not
pointwise pair positivity or constant-outside shortcuts.

## Things Not To Try Again

Do not try to prove arbitrary nonconvex Theorem 4 from pairwise correctness
alone. Appendix F Lemma 8 is formalized and useful, but pairwise correctness is
not the arbitrary remaining-set lift.

Do not require every first-choice pair bracket to be nonnegative. Individual
pair brackets can be negative for arbitrary prefix first-hit events; the
aggregate bracket is the right object.

Do not require every first-choice weighted pair term to be nonnegative.  The
endpoint-present example in the previous section has a negative pair term.

Do not rely on simple antitonicity of the fixed-tail first-choice branch sums.
It is false for arbitrary nonconvex remaining sets. For example, small
computations show branch patterns like `[1.5, 0, 1]` under a three-candidate
nonconvex prefix instance, so `candidateRankWeightedAverage_anti` cannot be
used directly on the branch sums.

Do not assume all outside first-choice branches in a hole have the same value.
Adjacent outside/outside branches can be equal locally, but distinct holes can
have different deleted-tail prefix sums.

Do not try to prove `ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes`
from only endpoint bounds such as `B_0 = max`, `B_last = 0`, and
`0 <= B_i <= max`. That abstract statement is false; a synthetic sequence such
as `B = [1, 0, 1, 1, 1, 1, 1, 0]` can make the weighted gap negative for
parameters like `qMore = 0.5`, `qLess = 0.85`. The proof needs the actual
prefix-best-in-set branch structure.

Do not keep adding finite-candidate wrappers unless they close a real named
paper result. The user explicitly asked to pursue the arbitrary version using
the tooling already built.

## Current Best Proof Strategy

### Step 1: Use the packaged current reduction

The all-`n` induction wrapper is now present:

```lean
theorem ReflMallowsBestInSetPrefixCutDominance.of_extremeWeighted
    (n : Nat) {qMore qLess : Real}
    (hqMore_pos : 0 < qMore) (hq_lt : qMore < qLess)
    (hweighted :
      forall m,
        ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes
          m qMore qLess) :
    ReflMallowsBestInSetPrefixCutDominance n qMore qLess := ...
```

This is the bookkeeping wrapper using
`ReflMallowsBestInSetPrefixCutDominance.zero` and
`ReflMallowsBestInSetPrefixCutDominance.succ_of_extremeWeighted`. Later wrappers
should consume it rather than repeating the induction.

### Step 2: Attack the extreme weighted target by adjacent gaps

Prefer the adjacent-gap representation over the pair-sum representation for the
remaining hard theorem:

```lean
firstChoiceBranchWeighted_eq_adjacent_gap_sum_boundary
```

The adjacent representation is better because existing Lean already proves
outside/outside adjacent branch values are equal:

```lean
firstChoiceBranchPayoffSum_prefixCut_eq_of_adjacent_not_mem
```

So only boundaries of holes in the remaining set contribute. The proof should
group adjacent boundary terms around each outside block rather than trying to
prove every adjacent gap nonnegative.

The likely useful lemma shape is a restricted adjacent-boundary theorem with the
same hypotheses as `ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes`:
nonempty `remaining`, endpoint membership, and `0 < cut <= n + 2`.  It should
sum the boundary normal form and prove the total nonnegative by grouping
maximal outside blocks.  Once this lemma is available, the theorem itself should
be a short `change` plus `rw [firstChoiceBranchWeighted_eq_adjacent_gap_sum_boundary]`.

### Step 3: Prove local boundary-cancellation lemmas

Useful exact-value lemmas already exist:

- `firstChoiceBranchPayoffSum_prefixCut_eq_partition_of_mem_lt`
- `firstChoiceBranchPayoffSum_prefixCut_eq_zero_of_mem_ge`
- `firstChoiceBranchPayoffSum_prefixCut_eq_of_adjacent_not_mem`
- `firstChoiceBranchWeighted_adjacentGapTerm_eq_tail_sub_partition`
- `firstChoiceBranchWeighted_adjacentGapTerm_eq_neg_tail`

The hard negative terms occur at mixed boundaries:

- outside before good remaining, where the outside branch can exceed the
  good-in-remaining partition value;
- bad remaining before outside, where the bad-in-remaining branch is zero and
  the outside tail branch is positive.

The finite search suggests these negative mixed-boundary terms are canceled by
the opposite boundary of the same outside block or by the endpoint terms forced
by `0 in remaining` and `last in remaining`. Formalize this as local hole-block
cancellation if possible.

### Step 4: Use first-choice branch formulas only when needed

If adjacent boundary grouping stalls, fall back to expanding branch values with:

```lean
firstChoiceBranchPayoffSum_prefixCut
```

Then compare the two tail deletions around a hole using:

- `succAbove_val_lt_deleteFirstChoicePrefixCut_iff`
- `mem_firstChoiceTailRemainingOf`
- `firstChoiceTailRemainingOf_nonempty_of_nonempty_of_first_not_mem`
- `bestInSetPrefixCutIndicator_rankingFirstChoiceOrderEquiv`
- `reflMallowsBestInSetPrefixCutSum_firstChoice`

This route is more verbose, but it follows the structure of the first-choice
decomposition already used in Lean.

### Step 5: Close the paper-facing theorem

After proving the extreme weighted target for all `n`:

1. derive arbitrary prefix-cut dominance via
   `ReflMallowsBestInSetPrefixCutDominance.of_extremeWeighted`;
2. connect to prefix-sum dominance by rewriting
   `reflMallowsBestInSetPrefixSum` as the corresponding cut;
3. connect to expected remaining-set utility dominance through
   `expectedBestInSet_le_of_mallows_prefix`;
4. add or update the paper-facing Theorem 4 wrapper in
   `KR21Monoculture/MainTheorems.lean`;
5. update `papers/KR21Monoculture/README.md` and `DependencyDAG.tex`;
6. run `lake build KR21Monoculture.MainTheorems`;
7. commit only the KR21 proof/docs files.

## Alternative Routes If Weighted Target Stalls

These are formalized as conditional bridges but are probably broader than
needed:

- `ReflMallowsBestInSetWeightMLR`
- `ReflKendallPrefixLayerAverageAnti`
- `ReflMallowsAdjacentStochasticDominance`
- `ReflMallowsWeakBruhatCoupling`

The adjacent-stochastic/weak-Bruhat route is elegant but likely harder because
it asks for all adjacent-swap-improving payoffs, not just prefix first-hit
events. Prefer the weighted prefix route unless it becomes genuinely blocked.

## Commit Discipline

The user prefers fewer commits. Commit when:

- a named theorem/proposition is fully proved;
- a paper-facing wrapper is added;
- moving from one paper to another.

Do not commit every small helper lemma. When committing, stage only the files
you touched for the current proof. In particular, be careful not to accidentally
stage DAG/pdf/png/html artifacts unless you have intentionally updated and
verified them.

## Recommended First Commands For The Next Agent

```bash
git status --short
git log --oneline -5
lake build KR21Monoculture.Sequential
rg -n "ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes|succ_of_extremeWeighted|firstChoiceBranchWeighted_eq_adjacent_gap_sum_boundary" papers/KR21Monoculture/Sequential.lean
```

Then start in `Sequential.lean` near the weighted declarations and adjacent-gap
identity. Keep the theorem target narrow: prove
`ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes`, then let the
existing bridges carry the rest of Theorem 4.
