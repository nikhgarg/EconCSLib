# User-Item Fairness Tradeoffs in Recommendations

## Source Version

- Paper: *User-item fairness tradeoffs in recommendations*
- Authors: Sophie Greenwood, Sudalakshmee Chiniah, and Nikhil Garg
- Version formalized: NeurIPS 2024 / arXiv:2412.04466
- Official URL: https://openreview.net/forum?id=ZOZjMs3JTs
- Official PDF: https://openreview.net/pdf?id=ZOZjMs3JTs
- arXiv URL: https://arxiv.org/abs/2412.04466
- Accessed: 2026-04-23

The PDF is not committed to git. Use the OpenReview PDF above as the primary
source version, with arXiv as a backup source.

## Central Theorem File

- `UserItemFairness/MainTheorems.lean`

That file contains the paper-facing theorem wrappers. Detailed LP, symmetry,
and preservation lemmas live in the other files in this folder.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Recommendation model utilities and fairness objectives | `RecommendationModel.userFairness`, `RecommendationModel.itemFairness` | formalized | `UserItemFairness/Basic.lean` | none |
| Problem 1 optimization predicate and unconstrained baseline | `RecommendationModel.SolvesProblemOne`, `RecommendationModel.paper_unconstrained_user_fairness_optimum_eq_one` | formalized | `UserItemFairness/Optimization.lean`, `UserItemFairness/MainTheorems.lean` | baseline theorem assumes nonnegative utilities and positive row normalizers |
| Symmetric user-type policy reduction | `ReductionWitness.paper_symmetric_item_fairness_value_set_reduction` | formalized | `UserItemFairness/MainTheorems.lean` | type representatives |
| Symmetric optimal item-fairness reduction | `ReductionWitness.paper_symmetric_optimal_item_fairness_reduction` | formalized | `UserItemFairness/MainTheorems.lean` | type representatives |
| User-utility symmetrization dominance | `RecommendationModel.SymmetricData.userFairness_le_userFairness_symmetrizedPolicy` | formalized | `UserItemFairness/Symmetrization.lean` | row-positive user normalizers |
| Appendix C Lemma 1 (`I^*_min > 0`) | `RecommendationModel.paper_lemma1_optimal_item_fairness_positive`, `TypePolicy.paper_reduced_optimal_item_fairness_positive` | formalized | `UserItemFairness/Optimization.lean`, `UserItemFairness/LPReduction.lean`, `UserItemFairness/MainTheorems.lean` | strictly positive utilities; reduced version also assumes strictly positive type weights |
| Appendix C Lemma 2 item-fairness LP value | `RecommendationModel.paper_lemma2_item_fairness_lp_value_eq` | formalized in epigraph (`ell ≤ I_j`) form | `UserItemFairness/Optimization.lean`, `UserItemFairness/MainTheorems.lean` | equality-form LP in the paper still needs the item-utility equalization argument |
| Proposition 2 symmetric optimum existence step | `RecommendationModel.SymmetricData.paper_proposition2_symmetric_optimum_exists` | formalized from supplied optimum | `UserItemFairness/Symmetrization.lean`, `UserItemFairness/MainTheorems.lean` | type representatives; row-positive user normalizers; supplied maximal-fairness optimum |
| Original/reduced optimal user-fairness value reduction | `ReductionWitness.paper_original_reduced_user_optimal_value_reduction_of_gamma_lt_one`, `ReductionWitness.paper_original_reduced_user_optimal_value_reduction_of_nonempty` | formalized for `γ < 1`; maximal-boundary version formalized with explicit feasibility-existence side conditions | `UserItemFairness/MainTheorems.lean` | at `γ = 1`, original/reduced feasible value sets nonempty, equivalently item-fairness optimum attainment |
| Baseline original/reduced optimal user-fairness value reduction at `γ = 0` | `ReductionWitness.paper_original_reduced_user_optimal_value_reduction_zero` | formalized | `UserItemFairness/MainTheorems.lean` | type representatives; row-positive user normalizers; nonnegative original utilities |
| Reduced optimum lifts to original optimum | `ReductionWitness.paper_reduced_optimum_lifts_to_original_auto_nonempty` | formalized | `UserItemFairness/MainTheorems.lean` | row-positive user normalizers; supplied reduced optimum |
| Symmetric original optimum descends to reduced optimum | `ReductionWitness.paper_symmetric_original_optimum_descends_to_reduced_auto_nonempty` | formalized | `UserItemFairness/MainTheorems.lean` | row-positive user normalizers; supplied type-symmetric original optimum |
| Sparse-support characterization | `ReducedSparseOptimalityTarget`, `TypePolicy.paper_active_pairs_bound_of_basic_feasible_support`, `TypePolicy.paper_sparse_shape_of_basic_feasible_maximal_optimum` | support-count bridge formalized | `UserItemFairness/LPReduction.lean`, `UserItemFairness/Symmetry.lean`, `UserItemFairness/MainTheorems.lean` | `BasicFeasibleSupportCertificate`, the finite support-count consequence of the LP basic-feasible-solution theorem |
| Price-of-fairness identity | `RecommendationModel.priceOfFairnessAt`, `RecommendationModel.paper_priceOfFairnessAt_eq_one_sub_optimalUserFairnessAtLevel`, `RecommendationModel.paper_priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one` | formalized | `UserItemFairness/Optimization.lean`, `UserItemFairness/MainTheorems.lean` | nonnegative utilities and positive row normalizers for the baseline normalization |
| Misestimation price definitions and exact-estimation benchmark | `EstimatedRecommendationModel.priceOfMisestimation`, `EstimatedRecommendationModel.paper_priceOfMisestimation_exact_estimation_eq_zero` | formalized benchmark | `UserItemFairness/Optimization.lean`, `UserItemFairness/MainTheorems.lean` | broader paper-specific comparative statics not yet proved |
