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
| Problem 1 optimization predicate | `RecommendationModel.SolvesProblemOne` | formalized | `UserItemFairness/Optimization.lean` | none |
| Symmetric user-type policy reduction | `ReductionWitness.paper_symmetric_item_fairness_value_set_reduction` | formalized | `UserItemFairness/MainTheorems.lean` | type representatives |
| Symmetric optimal item-fairness reduction | `ReductionWitness.paper_symmetric_optimal_item_fairness_reduction` | formalized | `UserItemFairness/MainTheorems.lean` | type representatives |
| Reduced optimum lifts to original optimum | `ReductionWitness.paper_reduced_optimum_lifts_to_original` | conditional | `UserItemFairness/MainTheorems.lean` | equality of original and reduced global optimal values |
| Symmetric original optimum descends to reduced optimum | `ReductionWitness.paper_symmetric_original_optimum_descends_to_reduced` | conditional | `UserItemFairness/MainTheorems.lean` | equality of original and reduced global optimal values |
| Sparse-support characterization | `ReducedSparseOptimalityTarget` | scaffold | `UserItemFairness/LPReduction.lean` | basic-feasible-solution / LP extreme-point proof |
| Misestimation price definitions | `EstimatedRecommendationModel.priceOfMisestimation` | scaffold | `UserItemFairness/Optimization.lean` | paper-specific comparative statics not yet proved |
