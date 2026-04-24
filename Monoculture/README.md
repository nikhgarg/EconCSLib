# Algorithmic Monoculture and Social Welfare

## Source Version

- Paper: *Algorithmic Monoculture and Social Welfare*
- Authors: Jon Kleinberg and Manish Raghavan
- Version formalized: arXiv:2101.05853
- Source URL: https://arxiv.org/abs/2101.05853
- PDF URL: https://arxiv.org/pdf/2101.05853
- Accessed: 2026-04-23

The PDF is not committed to git. Use the arXiv URL above as the source version
for theorem-number and definition comparisons.

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
| Appendix-E top-two expansion and ordered-pair bracket algebra for independent reranking | `MallowsSpec.firstChoiceGapWeight_eq_sum_firstSecondWeight`, `MallowsSpec.independent_weight_sum_eq_pair_sum`, `MallowsSpec.independentPairTerm_add_swap` | formalized | `Monoculture/MallowsPairwise.lean` | none |
| Theorem 3, pointwise Mallows route via cleared finite sums | `MallowsComparison.paper_theorem3_pointwise_finite_mallows_sum` | conditional | `Monoculture/MainTheorems.lean` | `MallowsComparison.CenterMallowsFiniteSumCertificate` |
| Theorem 3, reduced product-sign route | `MallowsComparison.paper_theorem3_pointwise_reduced_product_certificate` | conditional | `Monoculture/MainTheorems.lean` | `MallowsComparison.CenterMallowsReducedProductCrossWeightCertificate` |
| Equivalence of normalized candidate sums and cleared finite sums | `MallowsComparison.paper_theorem3_finite_sum_certificate_from_candidate_sums` | formalized | `Monoculture/MainTheorems.lean` | strict center ordering and `CandidateSumCertificate` inputs |
| Theorem 1, full monoculture paradox existence over accuracy families | `AccuracyFamily.Theorem1Target` | scaffold | `Monoculture/Family.lean` | connect paper hypotheses to paradox and instantiate the accuracy-family existence proof |
