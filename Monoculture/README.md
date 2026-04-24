# Algorithmic Monoculture and Social Welfare

## Source Version

- Paper: *Algorithmic Monoculture and Social Welfare*
- Authors: Jon Kleinberg and Manish Raghavan
- Version formalized: arXiv:2101.05853
- Source URL: https://arxiv.org/abs/2101.05853
- PDF URL: https://arxiv.org/pdf/2101.05853
- Accessed: 2026-04-23

Local cached source artifacts for active formalization:

- `Monoculture/sources/2101.05853.pdf`
- `Monoculture/sources/2101.05853.html`
- `Monoculture/sources/2101.05853.txt`

These source artifacts are intentionally ignored by git. Use the cached local
files first for theorem-number and definition comparisons; use the arXiv URLs
only to refresh or verify the source version.

## Central Theorem File

- `Monoculture/MainTheorems.lean`

That file contains the paper-facing theorem wrappers. Detailed definitions and
proof infrastructure live in the other files in this folder.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Definitions 2 and 3, independent reranking and weaker competition | `Model.PrefersIndependentReranking`, `Model.PrefersWeakerCompetition` | formalized | `Monoculture/PaperDefinitions.lean` | none |
| First-choice probability decomposition of independent reranking | `prefersIndependentReranking_iff_firstChoiceGapMassSum_pos` | formalized | `Monoculture/FirstChoiceDecomposition.lean` | none |
| First-choice probability decomposition of weaker competition | `prefersWeakerCompetition_iff_firstChoiceCollisionDiffSum_pos` | formalized | `Monoculture/FirstChoiceDecomposition.lean` | none |
| Appendix-E top-two expansion and ordered-pair bracket algebra for independent reranking | `MallowsSpec.firstChoiceGapWeight_eq_sum_firstSecondWeight`, `MallowsSpec.independent_weight_sum_eq_pair_sum`, `MallowsSpec.independentPairTerm_add_swap`, `MallowsSpec.independent_weight_sum_pos_of_rankFactorization` | formalized | `Monoculture/MallowsPairwise.lean` | finite Mallows fibers are constructed by `MallowsSpec.rankFactorization` |
| Theorem 3, rank-factorized center and prefix first-choice dominance | `MallowsComparison.paper_theorem3_centerFirstProb_lt_of_rankFactorization`, `MallowsComparison.paper_theorem3_firstWeightPrefix_cross_lt_of_rankFactorization`, `MallowsComparison.paper_theorem3_weaker_center_cross_weight_summand_pos_of_rankFactorization` | formalized | `Monoculture/MainTheorems.lean` | backward-compatible wrappers take rank-factorization inputs; use `MallowsSpec.rankFactorization` for the assumption-free finite Mallows instance |
| Theorem 3, pointwise Mallows route via cleared finite sums | `MallowsComparison.paper_theorem3_pointwise_finite_mallows_sum` | formalized | `Monoculture/MainTheorems.lean` | strict center ordering and the three cleared finite Mallows inequalities |
| Theorem 3, rank-factorized independent-reranking and weaker-competition route | `MallowsComparison.paper_theorem3_pointwise_rankFactorization`, `MallowsComparison.cross_weight_sum_pos_of_rankFactorization`, `candidateRankCrossConditionalGapSum_pos`, `candidateRankWeightedAverage_strictAnti` | formalized | `Monoculture/MainTheorems.lean`, `Monoculture/MallowsPairwise.lean` | strict center ordering, `0 < n`, `qA < qH`, and both `q < 1`; the finite Mallows `RankFactorization` is constructed by `MallowsSpec.rankFactorization` |
| Finite Mallows top-one/top-two fiber factorization | `MallowsSpec.rankFactorization`, `reflFirstWeight_eq_rank_mul_zero`, `reflFirstSecondWeight_eq_rank_mul_zero_one_of_lt`, `reflFirstSecondWeight_swap_eq_rank_mul_zero_one_of_lt` | formalized | `Monoculture/Kendall.lean`, `Monoculture/MallowsPairwise.lean` | none |
| Theorem 3, reduced product-sign route | `MallowsComparison.paper_theorem3_pointwise_reduced_product_certificate` | formalized | `Monoculture/MainTheorems.lean` | strict center ordering and non-center finite Mallows sign inequalities |
| Equivalence of normalized candidate sums and cleared finite sums | `MallowsComparison.paper_theorem3_finite_sum_certificate_from_candidate_sums` | formalized | `Monoculture/MainTheorems.lean` | strict center ordering and `CandidateSumCertificate` inputs |
| Theorem 1, shared-algorithm game semantics | `Model.secondMoverEU`, `Model.welfareOrdered`, `Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU` | formalized | `Monoculture/Game.lean`, `Monoculture/WelfareDecomposition.lean` | none |
| Theorem 1, Definition 2 initial crossing side | `paper_theorem1_initial_f_lt_g_from_definition2`, `AccuracyFamily.theorem1_f_lt_g_of_paperHypotheses_equalAccuracy` | formalized | `Monoculture/MainTheorems.lean`, `Monoculture/Theorem1.lean` | equal algorithm/human accuracy and `Model.PaperHypotheses (F.modelAt θH θH)` |
| Theorem 1, Definition 3 weaker-competition side | `paper_theorem1_g_lt_h_from_definition3`, `AccuracyFamily.theorem1_g_lt_h_of_paperHypotheses` | formalized | `Monoculture/MainTheorems.lean`, `Monoculture/Theorem1.lean` | `Model.PaperHypotheses (F.modelAt θA θH)` |
| Theorem 1, inequality (5) from finite-removal monotonicity | `paper_theorem1_inequality5_from_removal_monotonicity`, `paper_theorem1_inequality5_from_monotonicity`, `AccuracyFamily.Theorem1RemovalMonotonicityAt`, `AccuracyFamily.Theorem1MonotonicityAt` | formalized conditional bridge | `Monoculture/MainTheorems.lean`, `Monoculture/Theorem1.lean` | finite-removal monotonicity certificate not yet derived from a full formal Definition 1 structure |
| Theorem 1, finite continuity bridge for `f < h` persistence | `paper_theorem1_f_continuous_from_atom_continuity`, `paper_theorem1_f_lt_h_persists_right_from_atom_continuity`, `AccuracyFamily.theorem1_f_epsilonContinuousAt_of_atom_continuity`, `AccuracyFamily.theorem1_f_lt_h_persists_right_of_atom_continuity` | formalized conditional bridge | `DecisionCore/EpsilonContinuity.lean`, `Monoculture/MainTheorems.lean`, `Monoculture/Theorem1.lean` | requires atomwise epsilon-delta continuity of the finite ranking law `fun θ => ((F.dist θ) π).toReal` at the crossing point |
| Theorem 1, final interval-analytic/sign-change/atom-local/local-nudge/right-nudge/payoff bridge to monoculture paradox | `paper_theorem1_from_interval_analytic_certificate`, `paper_theorem1_from_sign_change_nudge_certificate`, `paper_theorem1_from_atom_local_nudge_certificate`, `paper_theorem1_from_local_nudge_certificate`, `paper_theorem1_from_right_nudge_certificate`, `paper_theorem1_from_crossing_certificate`, `AccuracyFamily.theorem1Target_of_intervalAnalyticCertificate`, `AccuracyFamily.theorem1Target_of_signChangeNudgeCertificate`, `AccuracyFamily.theorem1Target_of_atomLocalNudgeCertificate`, `AccuracyFamily.theorem1Target_of_localNudgeCertificate`, `AccuracyFamily.theorem1Target_of_rightNudgeCertificate`, `AccuracyFamily.theorem1Target_of_crossingCertificate`, `AccuracyFamily.theorem1Target_of_payoffCertificate` | formalized conditional bridge | `DecisionCore/IntervalCrossing.lean`, `Monoculture/MainTheorems.lean`, `Monoculture/Theorem1.lean` | requires `AccuracyFamily.Theorem1IntervalAnalyticCertificate F θH`, `AccuracyFamily.Theorem1SignChangeNudgeCertificate F θH`, `AccuracyFamily.Theorem1AtomLocalNudgeCertificate F θH`, `AccuracyFamily.Theorem1LocalNudgeCertificate F θH`, `AccuracyFamily.Theorem1RightNudgeCertificate F θH`, or `AccuracyFamily.Theorem1CrossingCertificate F θH`; the interval-analytic certificate fills weaker-competition and monotonicity fields from paper hypotheses |
| Theorem 1, full monoculture paradox existence over accuracy families | `AccuracyFamily.Theorem1Target` | conditional | `Monoculture/MainTheorems.lean`, `Monoculture/Family.lean`, `Monoculture/Theorem1.lean` | remaining analytic task: instantiate `AccuracyFamily.Theorem1IntervalAnalyticCertificate F θH` from Definition 1 differentiability/asymptotic optimality plus Definitions 2 and 3 |
