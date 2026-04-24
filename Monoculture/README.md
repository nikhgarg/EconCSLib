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
| Appendix-E top-two expansion and ordered-pair bracket algebra for independent reranking | `MallowsSpec.firstChoiceGapWeight_eq_sum_firstSecondWeight`, `MallowsSpec.independent_weight_sum_eq_pair_sum`, `MallowsSpec.independentPairTerm_add_swap`, `MallowsSpec.independent_weight_sum_pos_of_rankFactorization` | formalized | `Monoculture/MallowsPairwise.lean` | assumes `MallowsSpec.RankFactorization` for the finite Mallows fibers |
| Theorem 3, rank-factorized center and prefix first-choice dominance | `MallowsComparison.paper_theorem3_centerFirstProb_lt_of_rankFactorization`, `MallowsComparison.paper_theorem3_firstWeightPrefix_cross_lt_of_rankFactorization`, `MallowsComparison.paper_theorem3_weaker_center_cross_weight_summand_pos_of_rankFactorization` | formalized | `Monoculture/MainTheorems.lean` | assumes algorithm/human rank factorization and strict `qA < qH` |
| Theorem 3, pointwise Mallows route via cleared finite sums | `MallowsComparison.paper_theorem3_pointwise_finite_mallows_sum` | formalized | `Monoculture/MainTheorems.lean` | strict center ordering and the three cleared finite Mallows inequalities |
| Theorem 3, rank-factorized independent-reranking and weaker-competition route | `MallowsComparison.paper_theorem3_pointwise_rankFactorization`, `MallowsComparison.cross_weight_sum_pos_of_rankFactorization`, `candidateRankCrossConditionalGapSum_pos`, `candidateRankWeightedAverage_strictAnti` | formalized | `Monoculture/MainTheorems.lean`, `Monoculture/MallowsPairwise.lean` | strict center ordering, `0 < n`, `qA < qH`, and both `q < 1`; the finite Mallows `RankFactorization` is constructed by `MallowsSpec.rankFactorization` |
| Finite Mallows top-one/top-two fiber factorization | `MallowsSpec.rankFactorization`, `reflFirstWeight_eq_rank_mul_zero`, `reflFirstSecondWeight_eq_rank_mul_zero_one_of_lt`, `reflFirstSecondWeight_swap_eq_rank_mul_zero_one_of_lt` | formalized | `Monoculture/Kendall.lean`, `Monoculture/MallowsPairwise.lean` | none |
| Theorem 3, reduced product-sign route | `MallowsComparison.paper_theorem3_pointwise_reduced_product_certificate` | formalized | `Monoculture/MainTheorems.lean` | strict center ordering and non-center finite Mallows sign inequalities |
| Equivalence of normalized candidate sums and cleared finite sums | `MallowsComparison.paper_theorem3_finite_sum_certificate_from_candidate_sums` | formalized | `Monoculture/MainTheorems.lean` | strict center ordering and `CandidateSumCertificate` inputs |
| Theorem 1, full monoculture paradox existence over accuracy families | `AccuracyFamily.Theorem1Target` | paper-facing interface complete | `Monoculture/MainTheorems.lean` + `Monoculture/Family.lean` | external family-level assumptions required to produce a witness `θA` are not yet encoded |
