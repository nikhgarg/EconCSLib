# Decision Fairness Handoff

This is the continuation note for the imported decision/fairness/recommendation
track inside `EconCSLib`.

The immediate active project is **Paper 1: Algorithmic Monoculture and
Social Welfare**. The other two imported papers already have meaningful
scaffolds, and the paper-facing theorem surface for monoculture is now exposed
in `Monoculture/MainTheorems.lean`.

## Build First

Before refactoring, get the imported code building cleanly in this repository.

If there is build drift, repair:

- theorem names or namespaces
- small mathlib API drift
- import-path issues
- rewrite-direction changes

Do not do conceptual refactors before the build is stable.

## Current Best Theorem Seam

The main local interface is:

```lean
MallowsComparison.CenterMallowsCertificate
MallowsComparison.CenterMallowsFiniteSumCertificate
MallowsComparison.CenterMallowsProductCrossWeightCertificate
MallowsComparison.CenterMallowsReducedProductCrossWeightCertificate
AccuracyFamily.Theorem1GlobalAnalyticCertificate
AccuracyFamily.Theorem1IntervalAnalyticCertificate
AccuracyFamily.Theorem1SignChangeNudgeCertificate
AccuracyFamily.Theorem1AtomLocalNudgeCertificate
```

The closing theorem already exists:

```lean
MallowsComparison.centerProbabilityCertificate_of_centerMallowsCertificate
MallowsComparison.paperHypotheses_of_centerMallowsCertificate
MallowsComparison.theorem3_pointwise_of_centerMallowsFiniteSumCertificate
MallowsComparison.paperHypotheses_of_centerMallowsProductCrossWeightCertificate
MallowsComparison.theorem3_pointwise_of_centerMallowsReducedProductCrossWeightCertificate
AccuracyFamily.theorem1Target_of_globalAnalyticCertificate
AccuracyFamily.theorem1Target_of_intervalAnalyticCertificate
AccuracyFamily.theorem1Target_of_signChangeNudgeCertificate
AccuracyFamily.theorem1Target_of_atomLocalNudgeCertificate
AccuracyFamily.theorem1_f_sub_g_continuousOn_of_atom_continuity
AccuracyFamily.theorem1_f_lt_h_persists_right_of_atom_continuity
AccuracyFamily.theorem1_exists_right_initial_f_lt_g_of_atom_continuity
```

There are also constructors from finite sign inequalities:

```lean
MallowsComparison.centerMallowsCertificate_of_gapMass_nonneg
MallowsComparison.centerMallowsCertificate_of_gapMass_nonneg_and_collisionProb_le
MallowsComparison.centerMallowsCertificate_of_weightCertificate
MallowsComparison.candidateSumCertificate_of_centerMallowsFiniteSumCertificate
MallowsComparison.centerMallowsFiniteSumCertificate_of_candidateSumCertificate
MallowsComparison.centerMallowsCertificate_of_productCrossWeightCertificate
MallowsComparison.centerMallowsProductCrossWeightCertificate_of_reduced
```

The preferred packaging theorem is still the sum-level finite Mallows certificate,
because candidatewise non-center sign obligations are too strong for Mallows
first-choice fibers. The normalized candidate-sum obligations and
denominator-cleared finite sums are now connected in both directions by
`MallowsSpec.firstChoice_miss_gap_sum_pos_iff_weight_sum_pos` and
`MallowsComparison.firstChoice_collision_gap_sum_pos_iff_cross_weight_sum_pos`.

## What The Certificate Needs

Conceptually, the remaining obligations are:

1. candidate values are strictly ordered by the common center ranking
2. the algorithm denominator-cleared independent-reranking finite sum is positive
3. the human denominator-cleared independent-reranking finite sum is positive
4. the denominator-cleared weaker-competition finite sum is positive

The below-one center-probability obligations are closed by
`MallowsSpec.centerFirstProb_lt_one`, using positive mass on
`swapTopTwo M.center`. The sharp finite target is now
`CenterMallowsFiniteSumCertificate`; it avoids both over-strong candidatewise
probability monotonicity and over-strong non-center summand nonnegativity.

The remaining paper-specific seam is now to instantiate
`AccuracyFamily.Theorem1PaperAssumptions` for a concrete noisy permutation
family, or `AccuracyFamily.Theorem1GlobalAnalyticCertificate` for a fixed
baseline `θH`. From that bundle, Lean already derives the interval certificate,
the last-nonpositive crossing, the right nudge, and the payoff certificate. The
right-neighborhood `g < f` side is no longer a raw assumption: it is derived by
`DecisionCore.exists_last_nonpos_with_right_pos_on_Icc` from a compact-interval
sign change of `f - g`.

The equal-accuracy left endpoint uses only Definition 2 via
`AccuracyFamily.theorem1_exists_right_initial_f_lt_g_of_prefersIndependent_and_atom_continuity`.
Do not reintroduce `Model.PaperHypotheses (F.modelAt θH θH)` as the main
premise there; that predicate includes Definition 3, whose paper statement is
strictly for `θA > θH`.

For Mallows specifically, use `MallowsAccuracyFamilySpec` in
`Monoculture/MallowsFamily.lean`. It already lifts the fixed-parameter
rank-factorized Mallows theorem to the family-level Theorem 1 assumptions:
Definition 2 and Definition 3 are discharged for the parameterized family. It
also proves the strict `S = ∅` first-mover monotonicity clause by
`MallowsComparison.firstMoverUtility_strict_of_rankFactorization`. The remaining
concrete Mallows obligations are the Definition 1 fields still present in that
structure: atomwise continuity, asymptotic first dominance, and
singleton-removal weak monotonicity. The helper lemmas
`mallowsInverseAccuracyQ_lt_one` and `mallowsInverseAccuracyQ_strictAnti` cover
the paper convention `θ = φ - 1`, `q = 1 / (θ + 1)`.

## Recommended Next Proof Order

1. keep the paper-facing declaration layer in `Monoculture/MainTheorems.lean`
   and the active proof layer in `Monoculture/Theorem1.lean`;
2. for Mallows, instantiate the remaining analytic fields of
   `MallowsAccuracyFamilySpec`; for other families, instantiate
   `AccuracyFamily.Theorem1PaperAssumptions` or the fixed-`θH`
   `AccuracyFamily.Theorem1GlobalAnalyticCertificate`;
3. then the paper-facing Theorem 1 wrapper follows directly from
   `AccuracyFamily.theorem1Target_of_paperAssumptions` or
   `AccuracyFamily.theorem1Target_of_globalAnalyticCertificate`.

## What Not To Do Yet

- do not start the Gaussian or Laplacian monoculture branch
- do not formalize the outer value-vector distribution yet
- do not refactor the game definitions while finishing the Theorem 1 analytic
  crossing seam
- do not start external-solver LP work yet

## Other Imported Tracks

The imported code already contains worthwhile next steps beyond monoculture.

### User-item fairness

Next useful targets:

- original/reduced optimal-value equality for the LP reduction, or an explicit
  symmetric-feasible-region theorem
- sparse-support bounds for basic feasible solutions

Closed anchors now include exact item/user fairness preservation, conditional
equality of symmetric item-fairness value sets, conditional reduced-optimum
lifting, and conditional symmetric-original-optimum descent:

```lean
ReductionWitness.symmetricAttainableItemFairnessSet_eq_reduced
ReductionWitness.symmetricOptimalItemFairness_eq_reduced
ReductionWitness.isOptimalAtLevel_liftedPolicy_of_reduced
ReductionWitness.exists_reducedOptimalAtLevel_of_original_symmetric_optimal
```

### Accuracy-diversity

Next useful targets:

- discrete `TopKValueOracle` instantiations
- asymptotic homogeneity bounds from finite exchange inequalities

Closed anchors now include finite exchange accounting and Bernoulli/two-type
first-order inequalities:

```lean
ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
BernoulliSatisfactionModel.forwardMarginal_le_backwardMarginal_of_optimum
twoTypeAllocation_forward_one_le_backward_zero_of_optimum
twoTypeAllocation_forward_zero_le_backward_one_of_optimum
```

## Files To Keep Aligned

When the active theorem seam changes, keep these aligned:

- `README.md`
- `docs/DECISION_FAIRNESS_HANDOFF.md`
- `docs/ECONCSLEAN_CURRENT_STATUS.md`
- `docs/ARCHITECTURE.md`
- archived historical maps under `docs/archive/orientation/`
