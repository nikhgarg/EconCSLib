# Markets and Social Choice

Use for `EconCSLib/Markets/*`, `EconCSLib/SocialChoice/*`, matching, fair
division, rankings, Mallows models, and social-choice/ranking papers.

## Matching and Fair Division

- For matching, keep preference, blocking-pair, stability, and algorithmic
  invariants separate. Paper-facing theorem wrappers should call generic
  deferred-acceptance correctness when possible.
- For fair division, reuse bundle/allocation primitives. Prove feasibility,
  marginal-value, and envy/fairness predicates separately before combining them
  in paper wrappers.
- For finite fair-division allocation theorems, first prove a theorem for an
  abstract marginal bound, then instantiate it with the paper's finite maximum
  one-good marginal value.

## Rankings and Mallows

- For rank-weight monotonicity, first prove the PMF/fiber decomposition, convert
  to a pure rank-only weight formula, then prove a generic cleared
  weighted-average lemma from pairwise cross-ratio or prefix dominance.
- If conditioning or deleting a rank creates piecewise weights, prove small
  closed-form below/above/self lemmas and a deletion-sum geometric identity
  before attempting the all-cases theorem.
- For Mallows/ranking proofs, match pairwise decompositions when the paper
  compares `(i,j)` and `(j,i)` top-two events. Prove the top-two expansion,
  define ordered-pair terms, then prove antisymmetric swap identities.
- Keep three Mallows layers separate: denominator-cleared paper sum, top-two
  pair/bracket regrouping, and rank-factorization formulas for first/top-two
  fibers.
- Check strictness and boundary cases before claiming a Mallows theorem is
  assumption-free. State needed interior-parameter and candidate-count
  assumptions at the wrapper.
- For weaker-competition Mallows totals, use the paper's conditional-gap route:
  rank-only conditional gap, adjacent-rank antitonicity, finite MLR
  weighted-average inequality, and the positive same-human square-weighted gap.
- For Mallows "first mover beats second mover" lemmas, first prove the generic
  collision-loss identity
  `firstMover - independentSecond = sum firstChoiceProb * firstChoiceGapMass`.
  Then use the rank-factorized first-choice and first-choice-gap weights to
  reduce the sum to a positive scalar times the same-human square-weighted
  conditional-gap sum. This is usually faster than expanding the full
  two-ranking expectation directly.
- For Mallows pairwise-correctness monotonicity, separate the paper's
  cancellation-reduced endpoint-position inequality from the later permutation
  bridge. With inverse parameter `q = phi^-1`, correct endpoint placements have
  lower Kendall exponents than incorrect placements, so prove a strict
  cross-product inequality for the reduced weights and then translate the final
  statement as "probability decreases in `q`" rather than "increases in
  `phi`". Keep this rank-only core as a helper, not as a replacement DAG node
  for the paper's full Lemma 8.
- For the full Mallows pairwise-correctness theorem, introduce actual
  `pairCorrectWeight`, `pairWrongWeight`, and `pairCorrectProb` first, with a
  theorem that correct+wrong weights equal the Mallows partition for a
  center-ordered pair. Then prove a `PairPositionReduction`-style bridge saying
  both actual weights are the same positive scale times the reduced
  endpoint-position weights. The final paper wrapper should consume this bridge
  internally; an explicit-input reduction theorem is only conditional progress.
- For sequential best-of-remaining Mallows claims, do not treat pairwise
  correct-ranking monotonicity as automatically proving expected top-of-set
  utility dominance. State the exact remaining-set dominance theorem needed:
  for every feasible hired set, the more accurate ranking law gives weakly or
  strictly higher `expectedBestInSet` on the remaining candidates. Pairwise
  Lemma-8-style declarations are useful inputs, but the source theorem remains
  conditional until the top-of-remaining-set lift is formalized (often via
  subset/restriction rank-factorization or another explicit stochastic
  dominance bridge).
- For KR21-style nonconvex remaining-set lifts, prefer the prefix first-hit
  layer-cake target over broad "all monotone payoff" Kendall-layer averages.
  Broad uniform Kendall-layer average antitonicity is only a sufficient
  condition and can be too strong for arbitrary weak-Bruhat monotone payoffs;
  the narrower active target is the prefix-event condition
  `ReflKendallPrefixLayerAverageAnti` or its consecutive-layer form
  `ReflKendallAdjacentPrefixLayerAverageAnti`.
- In KR21 prefix-event peel-best recurrences, do not require each fixed
  before-insert branch to satisfy Mallows dominance. That branchwise statement
  is false in small cases, e.g. a worse first choice can increase a
  `cut = 0` before-insert event. Sum over insertion positions first, using an
  aggregate payoff such as `bestInSetPrefixCutTailInsertPositionValue`, then
  split the proof into the geometric insertion-prefix comparison and the
  remaining fixed-tail-payoff dominance obligation.
- For KR21 arbitrary first-choice decompositions, do not assume the branch sums
  are antitone in the first-choice rank; arbitrary nonconvex prefix events can
  violate that monotonicity. Use the explicit branch-bracket layer instead:
  `firstChoiceBranchPayoffSum`, `firstChoiceBranchBracket`,
  `candidateRankBranchCross_nonneg_of_diag_pair`, and
  `reflMallowsPayoffSum_cross_of_firstChoice_pair_brackets`. For arbitrary
  prefix first-hit events, do not insist that every individual two-branch
  bracket is nonnegative; that pairwise sufficient condition can be too strong.
  Prefer the aggregate off-diagonal target
  `candidateRankBranchCross_nonneg_of_diag_pair_sum` and its wrappers
  `firstChoiceBranchPayoffSum_prefixCut`,
  `firstChoiceBranchPayoffSum_prefixCut_diag_nonneg_of_tail`,
  `firstChoiceBranchBracketSum`,
  `reflMallowsPayoffSum_cross_of_firstChoice_pair_bracket_sum`, and
  `reflMallowsBestInSetPrefixCutSum_cross_of_firstChoice_pair_bracket_sum`.
  The wrapper
  `reflMallowsBestInSetPrefixCutSum_cross_of_firstChoice_tail_pair_bracket_sum`
  packages the diagonal terms from smaller tail prefix-cut dominance, leaving
  the aggregate bracket sum as the main new arbitrary induction target. Use the
  recursive interface `ReflMallowsBestInSetPrefixCutDominance`,
  `ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum`,
  `ReflMallowsBestInSetPrefixCutDominance.succ`,
  `ReflMallowsBestInSetPrefixCutDominance.zero`, and
  `ReflMallowsBestInSetPrefixCutDominance.of_firstChoiceBracketSums`, then
  bridge to expected utility with
  `reflMallowsBestInSetPrefixSum_cross_of_firstChoiceBracketSums` and
  `expectedBestInSet_le_of_mallows_firstChoiceBracketSums`. This keeps the
  induction target arbitrary-size while allowing negative first-choice pair
  brackets to cancel in the total recurrence, instead of adding more finite
  candidate classifications.
- For KR21 aggregate first-choice brackets, prefer the diagonal-plus-weighted
  regrouping before trying more raw pair algebra. Use
  `firstChoiceBranchBracketSum_eq_complementPower` to collapse the unordered
  pair sum, then `firstChoiceBranchBracketSum_eq_diag_add_weighted` and
  `firstChoiceBranchBracketSum_nonneg_of_diag_weighted` to split the proof into
  smaller tail prefix-cut dominance plus the weighted first-choice target
  `ReflMallowsBestInSetPrefixCutFirstChoiceWeighted`. The bridge
  `ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum.of_dominance_weighted`
  and induction wrapper
  `ReflMallowsBestInSetPrefixCutDominance.of_firstChoiceWeighted` are the
  current narrowest arbitrary route; the full-remaining-set bracket case is
  already closed by `firstChoiceBranchBracketSum_univ_cut_nonneg`, and the
  corresponding full-remaining weighted target by
  `firstChoiceBranchWeighted_univ_cut_nonneg`. Boundary weighted targets are
  zero by `firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_lt`
  and `firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_ge`.
  For the remaining nonconvex weighted target, use
  `candidateRankWeightedAverage_cross_eq_pair_sum` /
  `firstChoiceBranchWeighted_eq_pair_sum` to expose aggregate cancellation over
  first-choice pairs.
- For KR21 arbitrary remaining-set Mallows dominance, keep the exact
  best-in-set fiber MLR target separate from broader weak-Bruhat or prefix
  dominance targets. Define an identity-center unnormalised fiber such as
  `reflMallowsBestInSetWeight`, prove its center-relabeling bridge to
  `MallowsSpec.bestInSetWeight`, and use the candidatewise weighted-average
  bridge before attempting the stronger all-payoff adjacent stochastic
  dominance theorem. The two-candidate base case and full-remaining-set case
  reduce to first-choice weights; arbitrary nonconvex sets need the dedicated
  fiber recurrence/MLR proof.
- For the two-candidate part of that KR21 fiber route, do not reprove Mallows
  pairwise monotonicity from scratch. First prove that `bestInSetWeight {c,d} c`
  and `bestInSetWeight {c,d} d` are exactly `pairCorrectWeight` and
  `pairWrongWeight` for the center-ordered pair, then call the existing
  `PairPositionReduction` / `pairWeight_cross_pos_of_pairPositionReduction`
  machinery. This gives a clean `card <= 2` fiber-MLR milestone while leaving
  only arbitrary-size nonconvex remaining sets open. In a three-candidate
  universe, combine this pair case with the full-set first-choice cross theorem
  to close the whole fiber-MLR target, since every nonempty remaining set has
  cardinality one, two, or all three candidates.
- For KR21 center-convex remaining sets, the stronger fiber-MLR theorem can be
  proved by deleting absent extremes, not by opening ranking sums. Prove exact
  common-scale deletion formulas for `reflMallowsBestInSetWeight` when `0` or
  the last center candidate is not remaining; lift a single tail/initial cross
  inequality through those common positive scales; then induct until the
  interval is the full set and use first-choice fiber MLR.
- For KR21 co-singleton remaining sets, do not develop a new best-in-set
  recurrence. Rewrite `bestInSetWeight (univ \ {removed})` to the existing
  `bestAfterRemovalWeight` fiber using `bestInSet_univ_sdiff_singleton`, then
  call the rank-factorized `candidateRankBestAfterRemovalWeight` MLR theorem.
  Preserve the theorem's geometric side condition (`qLess < 1`) in
  paper-facing wrappers unless a separate proof removes it.
- In a four-candidate KR21 wrapper, classify a nonempty remaining finset by
  cardinality: `card <= 2` uses pairwise dominance, `card = 4` is the full
  center-convex case, and `card = 3` is a co-singleton by taking the singleton
  complement `univ \ remaining`. This can close the full finite universe from
  existing local routes without proving arbitrary-size dominance.
- When using loose Kendall-layer index bounds, prove and reuse no-gap support
  lemmas before chaining adjacent layer inequalities: if a higher identity
  Kendall layer is nonempty, every lower layer is nonempty. This lets adjacent
  cleared-average inequalities telescope without division-by-zero side cases.
- For ranking fibers over `Fin`, normalize first-choice rank `r` with
  `Fin.cycleRange r`; normalize ordered top-two ranks `r < s` with
  `cycleRange r` followed by `cycleIcc 1 s`; normalize swapped top-two ranks
  with `cycleRange s` followed by `cycleIcc 1 (r+1)`.

## Social Choice Probability Bridges

- When only a ranking law changes, rewrite payoff differences as candidatewise
  probability deltas times conditional continuation values. This often turns a
  game/probability theorem into the scalar inequality written in the paper.
- For finite conditional utilities with exactly two possible continuation
  values, use a generic two-outcome expectation lemma
  (`E[f] = Pr[event] * x + (1 - Pr[event]) * y`) before specializing notation.
- For strict probability bounds such as `Pr[event] < 1`, prove positive mass
  outside the event and apply a finite PMF complement lemma.
