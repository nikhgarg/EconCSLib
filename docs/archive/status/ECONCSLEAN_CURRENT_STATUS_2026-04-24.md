# EconCSLib Current Status

This is a repository-status note, not a reusable Codex skill. Keep changing
module names, theorem anchors, build status, and next-step handoff details here
rather than in `skills/econcs-formalizer/SKILL.md`.

Current as of April 24, 2026.

## Build Status

The current integration check passes:

```bash
lake build EconCSLib
```

The current author-paper campaign report lives in:

- `docs/GARG_AUTHOR_FORMALIZATION_REPORT.md`

Toolchain/dependency status:

- Lean: `leanprover/lean4:v4.30.0-rc2`
- mathlib: `v4.30.0-rc2`
- CSLib: `v4.30.0-rc2`

The build still emits linter warnings in older imported modules. Treat build
failure as the blocker unless the user explicitly asks for warning cleanup.

GitHub automation status:

- `.github/workflows/lean_action_ci.yml` remains for Lean CI/doc generation.
- `.github/workflows/update.yml` remains for manual dependency-update PRs.
- The old release-tag/release-publishing workflow has been deleted.

## Active Tracks

### Paper Folder Audit Layout

Current paper folders now follow the repository audit contract:

- `Monoculture/README.md` and `Monoculture/MainTheorems.lean`
- `UserItemFairness/README.md` and `UserItemFairness/MainTheorems.lean`
- `AccuracyDiversity/README.md` and `AccuracyDiversity/MainTheorems.lean`
- `EconCSLib/FairDivision/README.md` and
  `EconCSLib/FairDivision/MainTheorems.lean`
- `EconCSLib/Auction/README.md` and `EconCSLib/Auction/MainTheorems.lean`
- `EconCSLib/Online/README.md` and `EconCSLib/Online/MainTheorems.lean`
- `ProducerFairness/README.md` and `ProducerFairness/MainTheorems.lean`

Each README records the source paper version and theorem-status table. Each
`MainTheorems.lean` file is a thin public interface over detailed proof files.

### CSLib Upstream Compatibility

Notes:

- `docs/CSLIB_COMPATIBILITY_NOTES.md`

Current finding:

- CSLib is now a pinned dependency at `v4.30.0-rc2`.
- The highest-value module used so far is
  `Cslib.Foundations.Data.RelatesInSteps`, which gives step-indexed relation
  paths and closed the fair-division simple-cycle extraction seam.
- `EconCSLib.Graph.Cycle` now imports this module and exposes the reusable
  finite simple-cycle extractor. The fair-division paper applies that generic
  theorem.
- CSLib automata/language/URM modules are better saved for later voting and
  complexity tracks.

### Statistical Learning Theory Library Lead

External source:

- `YuanheZ/lean-stat-learning-theory`
- Paper: *Statistical Learning Theory in Lean 4: Empirical Processes from
  Scratch* (`arXiv:2602.02285`)

Current finding:

- The upstream `SLT` library includes covering numbers, metric entropy,
  sub-Gaussian processes, Gaussian/Lipschitz concentration, Efron-Stein,
  Dudley's entropy integral, and least-squares regression bounds.
- Useful module names seen upstream include `SLT.CoveringNumber`,
  `SLT.MetricEntropy`, `SLT.SubGaussian`, `SLT.Dudley`, `SLT.EfronStein`,
  `SLT.GaussianLipConcen`, and `SLT.LeastSquares.*`.
- Upstream currently has only a `main` branch and targets
  `leanprover/lean4:v4.27.0-rc1`; this repo targets `v4.30.0-rc2`. Do not add
  it directly as a dependency without a compatibility check or port.

Recommended use:

- For probability/statistical-learning EC papers, first inspect SLT theorem
  names and module structure before rebuilding concentration, covering-number,
  entropy, empirical-process, or least-squares machinery.
- If a theorem is needed now, port the narrow lemma/interface into a generic
  EconCS probability/statistics module with attribution instead of depending on
  the whole upstream repo at the wrong toolchain.

### Optimization Library Lead

External source:

- `optsuite/optlib`

Current finding:

- Optlib includes convex-function, subgradient, Farkas, weak-duality, KKT, and
  first-order-method convergence developments.
- It targets `leanprover/lean4:v4.13.0`, while this repo targets
  `v4.30.0-rc2`; do not add it directly as a dependency without a port.
- The most relevant files for User-Item Fairness style LP work are
  `Optlib.Convex.Farkas`, `Optlib.Optimality.Weak_Duality`, and the finite
  dimensional convex-analysis files.

Recommended use:

- Before proving LP/convex optimization infrastructure locally, inspect Optlib
  theorem statements and port only the narrow compatible interface needed in
  generic EconCS modules.
- For finite recommendation LP reductions, the likely local reusable target is
  a small finite-polytope/symmetrization layer rather than importing Optlib's
  full constrained-optimization stack.

### Fair Division Test-of-Time Track

Module:

- `EconCSLib.Graph.Cycle`
- `EconCSLib.FairDivision.IndivisibleGoods`

Implemented theorem anchors:

- `EnvyEdge`
- `HasTransitiveEnvyCycle`
- `HasStepEnvyCycle`
- `hasTransitiveEnvyCycle_of_not_acyclic`
- `hasTransitiveEnvyCycleExtraction_of_finite`
- `hasStepEnvyCycleExtraction_of_finite`
- `exists_simple_cycle_list_of_stepCycle`
- `hasEnvyCycleListExtraction_of_finite`
- `EnvyCycleList`
- `EnvyCyclePermutation`
- `AcyclicEnvyGraph`
- `exists_noOneEnvies_of_acyclicEnvyGraph`
- `envyBoundedBy_rotate_of_self_improves`
- `isAllocationOf_rotate_of_bijective`
- `selfValueSum`
- `ImprovingBundleRotation`
- `PotentialMaximal`
- `exists_potentialMaximal`
- `hasImprovingRotationExtraction_of_envyCyclePermutationExtraction`
- `hasEnvyCyclePermutationExtraction_of_envyCycleListExtraction`
- `hasAcyclicReduction_of_improvingRotationExtraction`
- `hasAcyclicReduction_of_envyCyclePermutationExtraction`
- `hasAcyclicReduction_of_envyCycleListExtraction`
- `exists_envyBounded_allocation_of_unenviedReduction`
- `exists_envyBounded_allocation_of_acyclicReduction`
- `exists_envyBounded_allocation_of_improvingRotationExtraction`
- `exists_envyBounded_allocation_of_envyCyclePermutationExtraction`
- `exists_envyBounded_allocation_of_envyCycleListExtraction`
- `exists_envyBounded_allocation_of_finite`
- `lmms_theorem_2_1_finite`
- `maxMarginal`
- `marginalBound_maxMarginal`
- `maxMarginal_nonneg`
- `lmms_theorem_2_1_finite_maxMarginal`

Current seam:

- The finite LMMS existence theorem is closed, including the paper-facing
  version where `α` is instantiated as the finite maximum one-good marginal
  value. Next useful work is an executable algorithm version of the iterative
  construction, EF1-style corollaries, or additional fair-division primitives.

### Auction Test-of-Time Track

Module:

- `EconCSLib.Auction.DigitalGoods`
- `EconCSLib.Auction.Position`
- `EconCSLib.Auction.Combinatorial`

Implemented theorem anchors:

- `DigitalGoodsAuction.utility`
- `DigitalGoodsAuction.TruthfulDominantStrategy`
- `DigitalGoodsAuction.IndividuallyRational`
- `DigitalGoodsAuction.NoPositiveTransfers`
- `DigitalGoodsAuction.revenue`
- `postedPrice_utility_eq`
- `postedPrice_truthful`
- `postedPrice_individuallyRational`
- `postedPrice_noPositiveTransfers`
- `singlePriceRevenue`
- `saleCount`
- `singlePriceRevenue_eq_saleCount_mul`
- `postedPrice_const_revenue_eq_singlePriceRevenue`
- `IsFixedPriceBenchmark`
- `IsTwoWinnerFixedPriceBenchmark`
- `candidateFixedPriceRevenue`
- `finiteCandidateFixedPriceBenchmark`
- `finiteCandidateFixedPriceBenchmark_nonneg`
- `singlePriceRevenue_candidate_le_finiteCandidateFixedPriceBenchmark`
- `singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible`
- `finiteCandidateFixedPriceBenchmark_isFixedPriceBenchmark_of_feasible`
- `finiteCandidateFixedPriceBenchmark_isTwoWinnerFixedPriceBenchmark_of_feasible`
- `OwnBidIndependent`
- `eraseOwnBid`
- `ownErasedThreshold`
- `ownErasedThreshold_ownBidIndependent`
- `restrictBidsBySide`
- `crossSampleCandidateThreshold`
- `crossSampleCandidateThreshold_ownBidIndependent`
- `finiteCandidateOfferPrice`
- `singlePriceRevenue_finiteCandidateOfferPrice_eq_benchmark`
- `crossSampleCandidateOfferThreshold`
- `crossSampleCandidateOfferThreshold_ownBidIndependent`
- `thresholdPriceAuction`
- `thresholdPriceAuction_truthful`
- `ownErasedThresholdPriceAuction_truthful`
- `crossSampleCandidateThresholdPriceAuction_truthful`
- `crossSampleCandidateOfferThresholdPriceAuction_truthful`
- `crossSampleCandidateOfferThresholdPriceAuction_noPositiveTransfers`
- `averageCrossSampleCandidateOfferRevenue`
- `averageCrossSampleCandidateOfferRevenue_nonneg`
- `twoWinnerFixedPriceBenchmarkValue`
- `CrossSampleOfferApproximationCertificate`
- `crossSampleOffer_competitive_of_certificate`
- `thresholdPriceAuction_individuallyRational`
- `thresholdPriceAuction_noPositiveTransfers`
- `PositionEnvironment`
- `PositionOutcome.utility`
- `PositionOutcome.revenue`
- `PositionOutcome.welfare`
- `PositionOutcome.FeasibleAssignment`
- `PositionOutcome.IndividuallyRational`
- `PositionOutcome.individuallyRational_of_payment_le_value`
- `PositionMechanism.TruthfulDominantStrategy`
- `PositionMechanism.IsNashEquilibrium`
- `PositionOutcome.SlotEnvyFree`
- `PositionOutcome.NoProfitableAssignedSlotDeviation`
- `PositionOutcome.noProfitableAssignedSlotDeviation_of_slotEnvyFree`
- `gspCounterexample_lowerBid_profitable`
- `gspCounterexampleMechanism_not_truthful`
- `gsp3TwoSlotMechanism`
- `gsp3TwoSlot_not_truthful`
- `CombinatorialAuction`
- `CombinatorialAuction.utility`
- `CombinatorialAuction.TruthfulDominantStrategy`
- `IsFeasibleBundleAllocation`
- `SingleMindedBid.valuation`
- `singleMindedValuationProfile_normalized_of_nonempty`
- `IsNonemptySingleMindedProfile`
- `targetBundleThresholdAuction_truthfulOn_singleMindedProfiles`
- `singleMindedAllocation`
- `PairwiseDisjointDesired`
- `singleMindedAllocation_feasible`
- `targetBundleWinners`
- `targetBundleThresholdAuction_allocation_eq_singleMindedAllocation`
- `targetBundleThresholdAuction_feasible_of_pairwiseDisjoint`
- `rejectAllAuction_truthful`

Next seams:

- Digital goods: deterministic fixed-price benchmark, cross-sample
  truthfulness/NPT, and uniform partition-average revenue nonnegativity are
  closed. Remaining seam is the RSOP approximation certificate: lower-bound the
  average cross-sample revenue against `F^(2)` by proving
  `CrossSampleOfferApproximationCertificate` for a concrete ratio.
- Position/GSP: the concrete sorted three-bidder/two-slot GSP
  non-truthfulness theorem and the local-envy-free assigned-slot deviation
  certificate are closed. Remaining seam is a generic sorted-bid GSP mechanism
  for finite ordered slots plus symmetric Nash equilibrium and revenue/welfare
  comparison predicates.
- Combinatorial auctions: single-minded normalized-profile critical-price
  truthfulness and pairwise-disjoint accepted-set feasibility are closed.
  Remaining seam is the Lehmann-O'Callaghan-Shoham greedy allocation rule,
  including proof that the accepted desired bundles are pairwise disjoint and
  the critical prices are own-report independent.

### AdWords / Online Matching Test-of-Time Track

Module:

- `EconCSLib.Online.AdWords`
- `EconCSLib.Online.AdWordsExtensions`
- `EconCSLib.Online.AdWordsLowerBound`
- `EconCSLib.Online.MainTheorems`

Implemented theorem anchors:

- `AdWordsInstance`
- `AdWordsInstance.Assignment`
- `AdWordsInstance.spend`
- `AdWordsInstance.revenue`
- `AdWordsInstance.Feasible`
- `AdWordsInstance.FractionalAssignment`
- `AdWordsInstance.FractionalFeasible`
- `AdWordsInstance.fractionalRevenue`
- `AdWordsInstance.assignmentFraction`
- `AdWordsInstance.assignmentFraction_fractionalFeasible_of_feasible`
- `AdWordsInstance.fractionalRevenue_assignmentFraction_eq_revenue`
- `AdWordsInstance.fractionalRevenue_le_dualObjective_of_dualFeasible`
- `AdWordsInstance.residualBudget`
- `AdWordsInstance.CanAssign`
- `AdWordsInstance.PositiveBudgets`
- `AdWordsInstance.SmallBids`
- `AdWordsInstance.spentFraction_gt_one_sub_epsilon_of_not_canAssign`
- `AdWordsInstance.feasibleAssignments`
- `AdWordsInstance.IsOptimalAssignment`
- `AdWordsInstance.offlineOptimumAssignment`
- `AdWordsInstance.offlineOptimumValue`
- `AdWordsInstance.revenue_eq_sum_spend`
- `AdWordsInstance.revenue_le_totalBudget_of_feasible`
- `AdWordsInstance.exists_optimalAssignment`
- `AdWordsInstance.revenue_le_offlineOptimumValue`
- `AdWordsInstance.offlineOptimumValue_le_totalBudget`
- `AdWordsInstance.spentFraction`
- `AdWordsInstance.balanceDiscount`
- `AdWordsInstance.msvvDualAlpha`
- `AdWordsInstance.msvvNormalizedDualAlpha`
- `AdWordsInstance.slackScore`
- `AdWordsInstance.maxSlackBeta`
- `AdWordsInstance.msvvAlphaFromAssignment`
- `AdWordsInstance.msvvNormalizedAlphaFromAssignment`
- `AdWordsInstance.balanceScore_eq_slackScore_msvvDualAlpha`
- `AdWordsInstance.balanceScore_eq_slackScore_msvvAlphaFromAssignment`
- `AdWordsInstance.msvvRatio_mul_slackScore_msvvNormalizedAlphaFromAssignment_eq_balanceScore`
- `AdWordsInstance.dualFeasible_of_slackScore_le_beta`
- `AdWordsInstance.slackScore_le_maxSlackBeta`
- `AdWordsInstance.mul_maxSlackBeta_le_of_mul_slackScore_le`
- `AdWordsInstance.dualFeasible_maxSlackBeta`
- `AdWordsInstance.dualFeasible_msvvAssignment`
- `AdWordsInstance.dualFeasible_msvvNormalizedAssignment`
- `AdWordsInstance.msvvRatio`
- `AdWordsInstance.msvvRatio_pos`
- `AdWordsInstance.msvvRatio_lt_one`
- `AdWordsInstance.balanceScore`
- `AdWordsInstance.feasibleAdvertisers`
- `AdWordsInstance.IsBalanceChoice`
- `AdWordsInstance.exists_balanceChoice_of_exists_canAssign`
- `AdWordsInstance.HistoryState`
- `AdWordsInstance.stepHistoryState`
- `AdWordsInstance.runHistoryStateFrom`
- `AdWordsInstance.runHistoryState`
- `AdWordsInstance.runAssignment`
- `AdWordsInstance.historyFinset`
- `AdWordsInstance.mem_historyFinset`
- `AdWordsInstance.sum_univ_eq_list_sum_of_historyFinset_eq_univ`
- `AdWordsInstance.historyFinset_finRange`
- `AdWordsInstance.finRange_history_nodup`
- `AdWordsInstance.historyMaxSlackBetaSum`
- `AdWordsInstance.historyMaxBidErrorSum`
- `AdWordsInstance.historyBalanceChargeFrom`
- `AdWordsInstance.stepRevenueCharge`
- `AdWordsInstance.historyRevenueChargeFrom`
- `AdWordsInstance.historyMaxSlackBetaSum_balanceChoiceRun_le_balanceCharge_add_maxBidError`
- `AdWordsInstance.sum_maxSlackBeta_balanceRun_le_balanceCharge_add_maxBidError_of_cover`
- `AdWordsInstance.msvvRatio_mul_historyMaxSlackBetaSum_normalized_balanceChoiceRun_le_balanceCharge_add_maxBidError`
- `AdWordsInstance.msvvRatio_mul_sum_maxSlackBeta_normalized_balanceRun_le_balanceCharge_add_maxBidError_of_cover`
- `AdWordsInstance.balanceChoiceRule`
- `AdWordsInstance.balanceChoiceRule_feasible`
- `AdWordsInstance.balanceChoiceRule_eq_none_iff_forall_not_canAssign`
- `AdWordsInstance.stepHistoryState_invariant`
- `AdWordsInstance.spend_le_stepHistoryState_spend`
- `AdWordsInstance.spend_le_runHistoryStateFrom_spend`
- `AdWordsInstance.spentFraction_le_runHistoryStateFrom_spentFraction`
- `AdWordsInstance.msvvAlphaFromAssignment_le_runHistoryStateFrom`
- `AdWordsInstance.msvvNormalizedAlphaFromAssignment_le_runHistoryStateFrom`
- `AdWordsInstance.final_slackScore_le_initial_balanceScore`
- `AdWordsInstance.msvvRatio_mul_final_normalized_slackScore_le_initial_balanceScore`
- `AdWordsInstance.maxSlackBeta_le_of_slackScore_le`
- `AdWordsInstance.maxBidForQuery`
- `AdWordsInstance.bid_le_maxBidForQuery`
- `AdWordsInstance.maxSlackBeta_runHistoryStateFrom_le_balanceScore_of_all_canAssign`
- `AdWordsInstance.msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_balanceScore_of_all_canAssign`
- `AdWordsInstance.final_msvvAlphaFromAssignment_ge_exp_neg_epsilon_of_not_canAssign`
- `AdWordsInstance.final_msvvNormalizedAlphaFromAssignment_ge_one_sub_epsilon_of_not_canAssign`
- `AdWordsInstance.final_slackScore_le_bid_mul_one_sub_exp_neg_epsilon_of_not_canAssign`
- `AdWordsInstance.msvvRatio_mul_final_normalized_slackScore_le_bid_error_of_not_canAssign`
- `AdWordsInstance.final_slackScore_le_max_balanceScore_bidError_of_choice`
- `AdWordsInstance.final_slackScore_le_max_balanceScore_maxBidError_of_choice`
- `AdWordsInstance.maxSlackBeta_runHistoryStateFrom_le_max_balanceScore_maxBidError_of_choice`
- `AdWordsInstance.maxSlackBeta_runHistoryStateFrom_le_balanceScore_add_maxBidError_of_choice`
- `AdWordsInstance.msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_balanceScore_add_maxBidError_of_choice`
- `AdWordsInstance.runHistoryState_invariant`
- `AdWordsInstance.runHistoryState_seen`
- `AdWordsInstance.runAssignment_feasible`
- `AdWordsInstance.revenue_runAssignment_eq_historyRevenueChargeFrom`
- `AdWordsInstance.historyBalanceChargeFrom_initial_le_runAssignment_revenue`
- `AdWordsInstance.runAssignment_unseen_eq_none`
- `AdWordsInstance.runAssignment_assigned_mem_historyFinset`
- `AdWordsInstance.balanceRunAssignment_feasible`
- `AdWordsInstance.balanceRunAssignment_unseen_eq_none`
- `AdWordsInstance.balanceRunAssignment_assigned_mem_historyFinset`
- `AdWordsInstance.DualFeasible`
- `AdWordsInstance.dualObjective`
- `AdWordsInstance.assignedWeightedSpend`
- `AdWordsInstance.revenue_le_dualObjective_of_dualFeasible`
- `AdWordsInstance.offlineOptimumValue_le_dualObjective_of_dualFeasible`
- `AdWordsInstance.CompetitiveRatioCertificate`
- `AdWordsInstance.PrimalDualCompetitiveCertificate`
- `AdWordsInstance.MsvvObjectiveBoundCertificate`
- `AdWordsInstance.MsvvApproxObjectiveBoundCertificate`
- `AdWordsInstance.MsvvHistoryAccountingCertificate`
- `AdWordsInstance.MsvvHistoryApproxAccountingCertificate`
- `AdWordsInstance.msvvObjectiveBoundCertificate_of_historyAccounting`
- `AdWordsInstance.msvvApproxObjectiveBoundCertificate_of_historyApproxAccounting`
- `AdWordsInstance.msvvHistoryApproxAccountingCertificate_balanceChoiceRun`
- `AdWordsInstance.msvvApproxObjectiveBoundCertificate_balanceChoiceRun`
- `AdWordsInstance.competitiveRatioCertificate_of_primalDual`
- `AdWordsInstance.competitive_of_primalDual`
- `AdWordsInstance.primalDualCompetitiveCertificate_of_msvvObjectiveBound`
- `AdWordsInstance.balance_msvv_competitive_of_objectiveBound`
- `AdWordsInstance.balance_msvv_approx_competitive_of_approxObjectiveBound`
- `AdWordsInstance.balance_msvv_approx_competitive_with_history_error`
- `AdWordsInstance.balance_msvv_approx_competitive_with_error_bound`
- `AdWordsInstance.balance_msvv_approx_competitive_with_query_sum_error_bound`
- `AdWordsInstance.balance_msvv_approx_competitive_finRange_with_query_sum_error_bound`
- `AdWordsInstance.balance_msvv_approx_competitive_up_to_delta`
- `AdWordsInstance.balance_msvv_approx_competitive_finRange_up_to_delta`
- `AdWordsInstance.balance_msvv_approx_competitive_up_to_delta_of_smallBids_threshold`
- `AdWordsInstance.balance_msvv_approx_competitive_finRange_up_to_delta_of_smallBids_threshold`
- `AdWordsInstance.balance_msvv_competitive_of_arbitrarily_smallBids_threshold`
- `AdWordsInstance.balance_msvv_finRange_competitive_of_arbitrarily_smallBids_threshold`
- `AdWordsInstance.balance_msvv_finRange_family_eventually_up_to_delta`
- `AdWordsInstance.balance_msvv_finRange_family_eventually_up_to_delta_of_smallBids_threshold`
- `AdWordsInstance.balance_msvv_finRange_family_limit_competitive_of_error_eventually`
- `AdWordsInstance.balance_msvv_finRange_family_limit_competitive_of_smallBids_threshold`
- `AdWordsInstance.balance_msvv_finRange_family_limit_competitive_of_error_eventually_of_offlineOpt_convergence`
- `AdWordsInstance.balance_msvv_finRange_family_limit_competitive_of_smallBids_threshold_of_offlineOpt_convergence`
- `AdWordsInstance.MsvvSmallBidsLimitFamily`
- `AdWordsInstance.balance_msvv_competitive_of_smallBidsLimitFamily`
- `AdWordsInstance.withEffectiveBids`
- `AdWordsInstance.withEffectiveBids_nonnegativeBids`
- `AdWordsInstance.withEffectiveBids_smallBids`
- `AdWordsInstance.withClickThroughRates`
- `AdWordsInstance.withClickThroughRates_nonnegativeBids`
- `AdWordsInstance.withClickThroughRates_smallBids_of_ctr_le_one`
- `AdWordsInstance.withAdvertiserWeights`
- `AdWordsInstance.withAdvertiserWeights_nonnegativeBids`
- `AdWordsInstance.withAdvertiserWeights_smallBids_of_weight_le_one`
- `AdWordsInstance.withAvailability`
- `AdWordsInstance.withAvailability_nonnegativeBids`
- `AdWordsInstance.withAvailability_smallBids`
- `AdWordsInstance.withSlots`
- `AdWordsInstance.withSlots_nonnegativeBids`
- `AdWordsInstance.withSlots_smallBids`
- `Decision.exists_input_randomized_payoff_le_of_forall_deterministic_average_le`
- `Decision.not_forall_input_bound_lt_randomized_payoff_of_forall_deterministic_average_le`
- `RandomizedLowerBoundCertificate`
- `RandomizedLowerBoundCertificate.exists_input_randomized_normalizedRevenue_le`
- `RandomizedLowerBoundCertificate.no_strictly_better_randomized_algorithm`
- `BMatchingYaoLowerBoundCertificate`
- `bMatching_no_randomized_algorithm_beats_msvvRatio_of_certificate`
- `uniformPermutationDistribution`
- `uniformPermutationExpectation_eq_of_relabel`
- `theorem9BidderSpendUpperBound`
- `theorem9NormalizedRevenueUpperBound`
- `theorem9BidderSpendUpperBound_nonneg`
- `theorem9BidderSpendUpperBound_le_one`
- `theorem9BidderSpendUpperBound_mono_bidder`
- `theorem9EligibleBidders`
- `theorem9EligibleBidders_card`
- `theorem9ActualEligibleBidders`
- `theorem9ObservedPrefix`
- `theorem9ActualEligibleBidders_not_mem_of_not_eligible`
- `theorem9ActualEligibleBidders_sum_eq`
- `theorem9ActualEligibleBidders_mul_swap_eq`
- `theorem9ObservedPrefix_mul_swap_eq`
- `theorem9ExponentialGridUpperSum`
- `theorem9ExponentialGridUpperSum_le_msvvRatio`
- `theorem9NormalizedRevenueUpperBound_nonneg`
- `theorem9NormalizedRevenueUpperBound_le_one`
- `BMatchingPermutationLowerBoundCertificate`
- `BMatchingPermutationLowerBoundCertificate.toYaoCertificate`
- `BMatchingPermutationLowerBoundCertificate.no_randomized_algorithm_beats_msvvRatio`
- `BMatchingPermutationRevenueBoundCertificate`
- `BMatchingPermutationRevenueBoundCertificate.toPermutationLowerBoundCertificate`
- `BMatchingPermutationRevenueBoundCertificate.no_randomized_algorithm_beats_ratio`
- `BMatchingRoundAllocationRevenueCertificate`
- `BMatchingRoundAllocationRevenueCertificate.toRevenueBoundCertificate`
- `BMatchingRoundAllocationRevenueCertificate.no_randomized_algorithm_beats_ratio`
- `BMatchingPointwiseAllocationRevenueCertificate`
- `BMatchingPointwiseAllocationRevenueCertificate.toRoundAllocationRevenueCertificate`
- `BMatchingPointwiseAllocationRevenueCertificate.no_randomized_algorithm_beats_ratio`
- `BMatchingSymmetricPointwiseAllocationRevenueCertificate`
- `BMatchingSymmetricPointwiseAllocationRevenueCertificate.toPointwiseAllocationRevenueCertificate`
- `BMatchingSymmetricPointwiseAllocationRevenueCertificate.no_randomized_algorithm_beats_ratio`
- `BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate`
- `BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate.toSymmetricPointwiseAllocationRevenueCertificate`
- `BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate.no_randomized_algorithm_beats_ratio`
- `BMatchingObservedPrefixAllocationRevenueCertificate`
- `BMatchingObservedPrefixAllocationRevenueCertificate.toRelabelSymmetricPointwiseAllocationRevenueCertificate`
- `BMatchingObservedPrefixAllocationRevenueCertificate.no_randomized_algorithm_beats_ratio`
- `BMatchingFeasibleObservedPrefixAllocationRevenueCertificate`
- `BMatchingFeasibleObservedPrefixAllocationRevenueCertificate.toObservedPrefixAllocationRevenueCertificate`
- `BMatchingFeasibleObservedPrefixAllocationRevenueCertificate.no_randomized_algorithm_beats_ratio`
- `BMatchingTheorem9FamilyCertificate`
- `BMatchingTheorem9FamilyCertificate.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta`
- `BMatchingTheorem9PointwiseFamilyCertificate`
- `BMatchingTheorem9PointwiseFamilyCertificate.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta`
- `BMatchingTheorem9SymmetricPointwiseFamilyCertificate`
- `BMatchingTheorem9SymmetricPointwiseFamilyCertificate.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta`
- `BMatchingTheorem9RelabelSymmetricPointwiseFamilyCertificate`
- `BMatchingTheorem9RelabelSymmetricPointwiseFamilyCertificate.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta`
- `BMatchingTheorem9ObservedPrefixFamilyCertificate`
- `BMatchingTheorem9ObservedPrefixFamilyCertificate.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta`
- `BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate`
- `BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta`
- `BMatchingTheorem9FeasiblePrefixRuleFamily`
- `BMatchingTheorem9FeasiblePrefixRuleFamily.normalizedRevenue`
- `BMatchingTheorem9FeasiblePrefixRuleFamily.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta`
- `BMatchingIntegralPrefixChoice`
- `BMatchingIntegralPrefixChoice.Feasible`
- `BMatchingIntegralPrefixAlgorithm`
- `BMatchingIntegralPrefixAlgorithm.prefixAllocation`
- `BMatchingIntegralPrefixAlgorithm.prefixAllocation_zero_of_not_visible`
- `BMatchingIntegralPrefixAlgorithm.prefixAllocation_sum_le_one`
- `BMatchingTheorem9IntegralPrefixChoiceFamily`
- `BMatchingTheorem9IntegralPrefixChoiceFamily.normalizedRevenue`
- `BMatchingTheorem9IntegralPrefixChoiceFamily.toFeasiblePrefixRuleFamily`
- `BMatchingTheorem9IntegralPrefixChoiceFamily.eventually_no_randomized_algorithm_beats_msvvRatio_add_delta`
- `theorem9BidderHarmonicPrefixNat`
- `theorem9BidderSpendUpperBound_le_harmonicPrefixNat`
- `theorem9BidderHarmonicPrefixNat_le_log_tail`
- `theorem9BidderSpendUpperBound_le_log_tail`
- `theorem9HarmonicLayerCountBound_of_pos`
- `theorem9_harmonic_eventually_le_msvvRatio_add`
- `theorem9_eventually_no_randomized_algorithm_beats_msvvRatio_add_delta`
- `paper_adwords_empty_assignment_feasible`
- `paper_adwords_offline_optimum_exists`
- `paper_adwords_revenue_le_total_budget_of_feasible`
- `paper_adwords_lp_weak_duality`
- `paper_adwords_integral_assignment_fractional_feasible`
- `paper_adwords_fractional_lp_weak_duality`
- `paper_adwords_dual_feasible_of_slack_score_bound`
- `paper_adwords_dual_feasible_max_slack_beta`
- `paper_adwords_dual_feasible_msvv_assignment`
- `paper_adwords_dual_feasible_msvv_normalized_assignment`
- `paper_adwords_balance_choice_exists`
- `paper_adwords_run_assignment_feasible`
- `paper_adwords_balance_run_assignment_feasible`
- `paper_adwords_balance_assignment_assigned_only_from_history`
- `paper_adwords_spend_monotone_over_history`
- `paper_adwords_run_revenue_eq_history_revenue_charge`
- `paper_adwords_balance_charge_le_run_revenue`
- `paper_adwords_final_slack_score_le_initial_balance_score`
- `paper_adwords_max_slack_beta_le_balance_score_of_all_can_assign`
- `paper_adwords_msvv_ratio_mul_normalized_max_slack_beta_le_balance_score_of_all_can_assign`
- `paper_adwords_blocked_advertiser_final_alpha_ge_exp_neg_epsilon`
- `paper_adwords_blocked_advertiser_final_slack_score_le_error`
- `paper_adwords_msvv_ratio_mul_blocked_advertiser_normalized_final_slack_score_le_error`
- `paper_adwords_max_slack_beta_le_balance_score_or_max_bid_error`
- `paper_adwords_max_slack_beta_le_balance_score_add_max_bid_error`
- `paper_adwords_msvv_ratio_mul_normalized_max_slack_beta_le_balance_score_add_max_bid_error`
- `paper_adwords_balance_history_max_slack_beta_sum_le_charge_add_error`
- `paper_adwords_balance_query_dual_sum_le_charge_add_error_of_history_cover`
- `paper_adwords_msvv_ratio_mul_normalized_query_dual_sum_le_charge_add_error_of_history_cover`
- `paper_adwords_small_bids_blocked_advertiser_spent_fraction`
- `paper_adwords_effective_bids_small_bids`
- `paper_adwords_click_through_rates_small_bids`
- `paper_adwords_weighted_bids_small_bids`
- `paper_adwords_availability_small_bids`
- `paper_adwords_multiple_slots_small_bids`
- `paper_adwords_theorem9_no_randomized_algorithm_beats_msvv_ratio_of_certificate`
- `paper_adwords_theorem9_no_randomized_algorithm_beats_msvv_ratio_of_permutation_certificate`
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_revenue_bound_certificate`
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_round_allocation_certificate`
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_pointwise_allocation_certificate`
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_symmetric_pointwise_allocation_certificate`
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_relabel_symmetric_pointwise_allocation_certificate`
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_observed_prefix_allocation_certificate`
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_feasible_observed_prefix_allocation_certificate`
- `paper_adwords_theorem9_bidder_spend_upper_bound_le_log_tail`
- `paper_adwords_theorem9_harmonic_layer_count_bound`
- `paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta`
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta`
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_family_certificate`
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_pointwise_family_certificate`
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_symmetric_pointwise_family_certificate`
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_relabel_symmetric_pointwise_family_certificate`
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_observed_prefix_family_certificate`
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_observed_prefix_family_certificate`
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_prefix_rule_family`
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family`
- `paper_adwords_competitive_of_primal_dual_certificate`
- `paper_adwords_balance_msvv_competitive_of_primal_dual_certificate`
- `paper_adwords_balance_msvv_objective_bound_of_history_accounting`
- `paper_adwords_balance_msvv_competitive_of_objective_bound`
- `paper_adwords_balance_msvv_approx_objective_bound_of_history_accounting`
- `paper_adwords_balance_msvv_approx_competitive_of_approx_objective_bound`
- `paper_adwords_balance_msvv_history_approx_accounting_with_explicit_error`
- `paper_adwords_balance_msvv_approx_objective_bound_with_explicit_error`
- `paper_adwords_balance_msvv_approx_competitive_with_explicit_history_error`
- `paper_adwords_balance_msvv_approx_competitive_with_error_bound`
- `paper_adwords_balance_msvv_approx_competitive_with_query_sum_error_bound`
- `paper_adwords_balance_msvv_finRange_approx_competitive_with_query_sum_error_bound`
- `paper_adwords_balance_msvv_approx_competitive_up_to_delta`
- `paper_adwords_balance_msvv_finRange_approx_competitive_up_to_delta`
- `paper_adwords_balance_msvv_approx_competitive_up_to_delta_of_small_bids_threshold`
- `paper_adwords_balance_msvv_finRange_approx_competitive_up_to_delta_of_small_bids_threshold`
- `paper_adwords_balance_msvv_competitive_of_arbitrarily_small_bids_threshold`
- `paper_adwords_balance_msvv_finRange_competitive_of_arbitrarily_small_bids_threshold`
- `paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta`
- `paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta_of_small_bids_threshold`
- `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_error_eventually`
- `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_small_bids_threshold`
- `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_error_eventually_of_offline_opt_convergence`
- `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_small_bids_threshold_of_offline_opt_convergence`
- `paper_adwords_balance_msvv_competitive_of_small_bids_limit_family`

Current endpoint:

- The finite offline benchmark, fractional LP primal/dual weak-duality,
  residual-budget, small-bids boundary, online-history, Balance-choice,
  run-feasibility, run-monotonicity, query-dual charge, and query-dual
  summation, and revenue-trace layers are closed.
  The corrected dual-fitting layer now uses
  `msvvNormalizedAlphaFromAssignment`; the scaling identity is
  `msvvRatio_mul_slackScore_msvvNormalizedAlphaFromAssignment_eq_balanceScore`.
  The normalized non-exhausted case is
  `msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_balanceScore_of_all_canAssign`;
  the normalized exhausted case is
  `msvvRatio_mul_final_normalized_slackScore_le_bid_error_of_not_canAssign`;
  and the normalized summation-friendly mixed bound is
  `msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_balanceScore_add_maxBidError_of_choice`.
  The normalized history/list summation theorem is
  `msvvRatio_mul_historyMaxSlackBetaSum_normalized_balanceChoiceRun_le_balanceCharge_add_maxBidError`,
  and the finite normalized query-dual sum theorem is
  `msvvRatio_mul_sum_maxSlackBeta_normalized_balanceRun_le_balanceCharge_add_maxBidError_of_cover`.
  The recursive Balance charge is bounded by actual run revenue via
  `historyBalanceChargeFrom_initial_le_runAssignment_revenue`. The normalized
  advertiser-alpha increment accounting is also closed, yielding
  `msvvHistoryApproxAccountingCertificate_balanceChoiceRun`,
  `msvvApproxObjectiveBoundCertificate_balanceChoiceRun`, and
  `balance_msvv_approx_competitive_with_history_error`. The exact idealized
  seam `MsvvHistoryAccountingCertificate` still derives
  `MsvvObjectiveBoundCertificate`, while the finite small-bids theorem now has a
  concrete additive error:
  `historyMaxBidAlphaErrorSum ε history + historyMaxBidErrorSum ε history`.
  This combined error is bounded algebraically by
  `ε * (Real.exp 1 + 1) * historyMaxBidSum`, yielding
  `balance_msvv_approx_competitive_with_error_bound`, and reindexed to
  `ε * (Real.exp 1 + 1) * ∑ q, maxBidForQuery q` in
  `balance_msvv_approx_competitive_with_query_sum_error_bound`. The additive
  delta-form statement is
  `balance_msvv_approx_competitive_up_to_delta`, and the explicit threshold
  statement is
  `balance_msvv_approx_competitive_up_to_delta_of_smallBids_threshold`.
  The limit-style wrapper
  `balance_msvv_competitive_of_arbitrarily_smallBids_threshold` removes the
  additive term under an arbitrarily-small threshold assumption. For canonical
  finite query types, `historyFinset_finRange` and `finRange_history_nodup`
  discharge the nodup-cover obligations for `List.finRange n`; the public
  `paper_adwords_balance_msvv_finRange_*` wrappers state the error directly
  with the query sum `∑ q : Fin n, maxBidForQuery q`. The family-level wrappers
  `paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta` and
  `paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta_of_small_bids_threshold`
  now formalize the model-level limiting seam over dependent finite query
  types `Fin (n k)`: if the explicit error, or equivalently the threshold
  small-bids condition, is eventually below every positive target, then the
  guarantee is eventually additive-`δ`. The sequence-limit wrappers
  `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_error_eventually`
  and
  `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_small_bids_threshold`
  use `Sequence.SeqTendsTo` and `Sequence.le_of_seqTendsTo_eventually_le_add`
  to convert eventual additive guarantees plus convergence of the two real
  sides into the limiting inequality. The ordinary-offline-optimum wrappers use
  `Sequence.SeqTendsTo.const_mul_of_nonneg` so the conclusion is stated as
  `msvvRatio * optLimit ≤ revenueLimit`. The paper-level structure
  `MsvvSmallBidsLimitFamily` packages the finite instance family, vanishing
  small-bids threshold, and convergence fields; the public theorem
  `paper_adwords_balance_msvv_competitive_of_small_bids_limit_family` proves
  `msvvRatio * optLimit ≤ revenueLimit` for every such family. Section 6 is
  now represented by effective-bid transformations preserving the hypotheses
  needed to rerun the same theorem: arbitrary effective charges, click-through
  rates, Section 8 advertiser weights, delayed-entry/availability masks, and
  slot-query expansion. The slot expansion theorem is the independent
  slot-query reduction; a stricter "one advertiser per page" multiple-slot
  feasibility constraint is not yet encoded. Section 7 has a generic finite
  Yao lemma and a paper-facing Theorem
  9 wrapper through `BMatchingYaoLowerBoundCertificate` and the more specific
  `BMatchingPermutationLowerBoundCertificate`, which fixes the paper's uniform
  distribution over bidder permutations. The explicit finite harmonic
  expression from the paper is represented by
  `theorem9BidderSpendUpperBound` and
  `theorem9NormalizedRevenueUpperBound`, with
  `BMatchingPermutationRevenueBoundCertificate` splitting the remaining
  lower-bound instantiation into the deterministic average-revenue inequality
  and the comparison of that finite expression to a requested ratio. This is
  necessary because the finite harmonic cap approaches `msvvRatio` from above;
  the paper theorem uses the large-market/additive-`δ` limit rather than a
  false exact finite `≤ msvvRatio` claim.
  `BMatchingRoundAllocationRevenueCertificate` further isolates the paper's
  line `E[q_ij] <= 1 / (N - i + 1)` and proves mechanically that those
  round/bidder inequalities imply the harmonic revenue cap.
  `BMatchingPointwiseAllocationRevenueCertificate` starts from realized
  per-permutation allocation variables and proves the finite expectation
  algebra to reach the round-allocation certificate; its family analogue
  `BMatchingTheorem9PointwiseFamilyCertificate` is now the closest public seam
  to the paper's deterministic-algorithm calculation.
  `BMatchingSymmetricPointwiseAllocationRevenueCertificate` goes one step
  deeper: it proves the `1 / (N - i + 1)` expected-allocation bound from
  ineligible-zero allocation, per-round capacity, equal expected allocation
  across eligible positions, and the formal cardinality of
  `theorem9EligibleBidders`. Its family analogue
  `BMatchingTheorem9SymmetricPointwiseFamilyCertificate` remains available for
  direct expected-symmetry instantiations. The new relabel-symmetric
  certificates
  `BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate` and
  `BMatchingTheorem9RelabelSymmetricPointwiseFamilyCertificate` derive that
  expected symmetry from pointwise input relabeling via
  `uniformPermutationExpectation_eq_of_relabel`. The observed-prefix
  certificates
  `BMatchingObservedPrefixAllocationRevenueCertificate` and
  `BMatchingTheorem9ObservedPrefixFamilyCertificate` prove the paper's
  pointwise relabeling identity from the fact that swapping two positions in
  the current suffix leaves `theorem9ObservedPrefix` unchanged
  (`theorem9ObservedPrefix_mul_swap_eq`). The feasible observed-prefix
  certificates
  `BMatchingFeasibleObservedPrefixAllocationRevenueCertificate` and
  `BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate` derive the
  position-level ineligible-zero and round-capacity fields from actual-bidder
  feasibility over the visible set, using
  `theorem9ActualEligibleBidders_not_mem_of_not_eligible` and
  `theorem9ActualEligibleBidders_sum_eq`. The feasible prefix-rule family
  `BMatchingTheorem9FeasiblePrefixRuleFamily` removes the separate
  capped-revenue field by defining the payoff as the paper's capped normalized
  spend expression itself. The integral prefix-choice family
  `BMatchingTheorem9IntegralPrefixChoiceFamily` further specializes this to
  finite deterministic choice rules selecting at most one visible actual bidder
  in each round; this is now the closest concrete lower-bound endpoint. The
  harmonic side is now closed:
  `theorem9BidderSpendUpperBound_le_log_tail` proves the logarithmic
  tail-spend bound, `theorem9HarmonicLayerCountBound_of_pos` proves the finite
  layer-count estimate, `theorem9ExponentialGridUpperSum_le_msvvRatio` proves
  the finite geometric grid bound, and
  `theorem9_harmonic_eventually_le_msvvRatio_add` proves the eventual additive
  comparison to `msvvRatio`. The asymptotic wrapper
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta`
  now states the paper-level lower-bound seam with only the deterministic
  round-allocation inequalities as mathematical inputs: no randomized algorithm
  family beats `msvvRatio + δ` on all sufficiently large permutation instances.
  The public expected-allocation family interface for this lower-bound endpoint
  is `BMatchingTheorem9FamilyCertificate`; the pointwise-allocation family
  interfaces are `BMatchingTheorem9PointwiseFamilyCertificate` and
  `BMatchingTheorem9SymmetricPointwiseFamilyCertificate`, and the closest
  integral prefix-choice interface is
  `BMatchingTheorem9IntegralPrefixChoiceFamily`, with
  paper-facing wrappers
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_pointwise_family_certificate`,
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_symmetric_pointwise_family_certificate`,
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_relabel_symmetric_pointwise_family_certificate`,
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_observed_prefix_family_certificate`,
  and
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_observed_prefix_family_certificate`,
  plus the capped-payoff wrapper
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_prefix_rule_family`
  and the concrete choice-rule wrapper
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family`.

Current status for Theorem 9 in the AdWords pass (2026-04-24):
the concrete finite integral-prefix algorithm endpoint is fully formalized at the
paper-facing level via
`paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms`
and its realized-revenue variant
`paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms_of_realized_revenue`.
The verified command was `lake build EconCSLib.Online.MainTheorems`.
The finite offline benchmark, dual-fitting core, finite small-bids proof, and
Theorem 9 harmonic lower-bound chain are now fully closed. The concrete finite
integral-prefix algorithm endpoint is also formalized at paper-facing level for
both capped-normalized and realized-revenue variants. No additional paper-level
Theorem 9 seam is currently active. The multi-slot stand-in for multiple ads is
now documented with a separate per-page distinct-advertiser feasibility predicate
`withSlotsPerPageDistinct` and filtered choice wrapper `withSlotsDistinctChoice`.

### Monoculture Imported Track

Main module:

- `EconCSLib.Math.PositiveDenominator`
- `EconCSLib.Math.Sequence`
- `DecisionCore.EpsilonContinuity`
- `DecisionCore.IntervalCrossing`
- `Monoculture.MallowsCenterCertificate`
- `Monoculture.MallowsFiniteLemmas`

Implemented recent anchors:

- `swapTopTwo`
- `firstChoiceMissProb_eq_pmfProb_ne`
- `firstChoiceMissProb_pos_of_mass_ne_firstChoice`
- `MallowsSpec.law_apply_toReal_pos`
- `MallowsSpec.centerFirstMissProb_pos`
- `MallowsSpec.centerFirstProb_lt_one`
- `MallowsSpec.firstChoiceGapWeight`
- `MallowsSpec.firstChoiceGapMass_eq_firstChoiceGapWeight_div_partition`
- `MallowsSpec.firstChoiceMissProb_eq_partition_sub_firstWeight_div_partition`
- `MallowsSpec.firstChoice_miss_gap_sum_eq_weight_sum_div`
- `MallowsSpec.firstChoice_miss_gap_sum_pos_of_weight_sum_pos`
- `MallowsSpec.firstChoice_miss_gap_sum_pos_iff_weight_sum_pos`
- `MallowsComparison.CenterMallowsCertificate`
- `MallowsComparison.centerProbabilityCertificate_of_centerMallowsCertificate`
- `MallowsComparison.centerMallowsCertificate_of_gapMass_nonneg`
- `MallowsComparison.centerMallowsCertificate_of_gapMass_nonneg_and_collisionProb_le`
- `MallowsComparison.firstChoice_collision_gap_sum_eq_cross_weight_sum_div`
- `MallowsComparison.firstChoice_collision_gap_sum_pos_of_cross_weight_sum_pos`
- `MallowsComparison.firstChoice_collision_gap_sum_pos_iff_cross_weight_sum_pos`
- `MallowsComparison.CenterMallowsFiniteSumCertificate`
- `MallowsComparison.candidateSumCertificate_of_centerMallowsFiniteSumCertificate`
- `MallowsComparison.centerMallowsFiniteSumCertificate_of_candidateSumCertificate`
- `MallowsComparison.theorem3_pointwise_of_centerMallowsFiniteSumCertificate`
- `MallowsComparison.CenterMallowsWeightCertificate`
- `MallowsComparison.centerMallowsCertificate_of_weightCertificate`
- `MallowsComparison.CenterMallowsProductCrossWeightCertificate`
- `MallowsComparison.centerMallowsCertificate_of_productCrossWeightCertificate`
- `MallowsComparison.paperHypotheses_of_centerMallowsProductCrossWeightCertificate`
- `MallowsComparison.CenterMallowsReducedProductCrossWeightCertificate`
- `MallowsComparison.centerMallowsProductCrossWeightCertificate_of_reduced`
- `MallowsComparison.theorem3_pointwise_of_centerMallowsReducedProductCrossWeightCertificate`
- `MallowsComparison.centerPositiveCertificate_of_centerMallowsCertificate`
- `MallowsComparison.candidateSumCertificate_of_centerMallowsCertificate`
- `MallowsComparison.paperHypotheses_of_centerMallowsCertificate`
- `MallowsSpec.firstChoiceGapWeight_eq_sum_firstSecondWeight`
- `MallowsSpec.independent_weight_sum_eq_pair_sum`
- `MallowsSpec.independentPairTerm`
- `MallowsSpec.independentPairBracket`
- `MallowsSpec.firstSecondWeight_self`
- `MallowsSpec.independentPairTerm_add_swap`
- `candidateRankPowerSum_pos`
- `candidateRankPowerSum_strict_mono`
- `rankPower_mul_lt_mul_rankPower`
- `candidateRankPrefix_cross_pos`
- `weightedRankPower_pair_add_pos`
- `candidateRankWeightedPrefix_cross_pos`
- `candidateRankWeightedPrefixCrossDeltaSum_pos`
- `candidateRankCrossDelta_scaled_strictAnti`
- `candidateRankCrossDelta_last_neg`
- `candidateRankWeightedSuffixCrossDeltaSum_last_neg`
- `candidateRankAdjacentCoeff_eq_prefix_suffix`
- `candidateRankAdjacentCoeff_pos_of_suffix_nonpos`
- `candidateRankConditionalGapTerm`
- `candidateRankConditionalGap`
- `candidateRankConditionalGap_strictAnti`
- `candidateRankWeightedAverage_strictAnti`
- `candidateRankCollisionWeight_cross_pos`
- `candidateRankSquareWeightedConditionalGap_pos`
- `candidateRankCrossConditionalGapSum_pos`
- `inversionFinsetInvolving_firstChoice_card`
- `inversionFinsetNotInvolving_firstChoice_card_eq_cycleRange`
- `kendallTau_eq_firstChoice_add_cycleRange`
- `kendallTau_center_trans`
- `inversionFinsetInvolvingSecondNotFirst_card`
- `reflFirstWeight_eq_rank_mul_zero`
- `MallowsSpec.firstWeight_eq_reflFirstWeight`
- `MallowsSpec.firstWeight_eq_rank_mul_centerFirst`
- `MallowsSpec.partition_eq_rankPowerSum_mul_centerFirstWeight`
- `inversionFinsetInvolving_secondChoice_card_of_first_zero`
- `kendallTau_eq_secondChoice_sub_one_add_cycleIcc_one`
- `reflFirstSecondWeight_eq_rank_mul_zero_one_of_lt`
- `reflFirstSecondWeight_swap_eq_rank_mul_zero_one_of_lt`
- `MallowsSpec.firstSecondWeight_eq_reflFirstSecondWeight`
- `MallowsSpec.firstSecondWeight_eq_rank_mul_centerFirstSecond_of_lt`
- `MallowsSpec.firstSecondWeight_swap_eq_q_mul_rank_mul_centerFirstSecond_of_lt`
- `MallowsSpec.rankFactorization`
- `MallowsComparison.paper_appendixE_independent_weight_sum_pos`
- `MallowsComparison.paper_appendixE_cross_weight_sum_pos`
- `MallowsSpec.firstChoiceGapWeight_eq_rankConditionalGap`
- `MallowsSpec.firstWeightPrefix`
- `MallowsSpec.firstWeightPrefix_eq_rankPrefixPowerSum_mul`
- `MallowsComparison.centerFirstWeight_cross_lt_of_rankFactorization`
- `MallowsComparison.centerFirstProb_lt_of_rankFactorization`
- `MallowsComparison.firstWeightPrefix_cross_lt_of_rankFactorization`
- `MallowsComparison.crossAdjacentCoeff_eq_rankFactorization`
- `MallowsComparison.cross_weight_sum_pos_of_adjacent_coeff_pos`
- `MallowsComparison.cross_weight_sum_pos_of_rankFactorization_and_suffix_nonpos`
- `MallowsComparison.cross_weight_sum_pos_of_rankFactorization`
- `MallowsComparison.centerMallowsFiniteSumCertificate_of_rankFactorization`
- `MallowsComparison.theorem3_pointwise_of_rankFactorization`
- `MallowsComparison.weaker_center_cross_product_pos_of_rankFactorization`
- `MallowsComparison.weaker_center_cross_weight_summand_pos_of_rankFactorization`
- `MallowsAccuracyFamilySpec.theorem1PaperAssumptions`
- `MallowsAccuracyFamilySpec.theorem1Target`
- `MallowsAccuracyFamilySpec.paper_theorem1_mallows_family`
- `MallowsComparison.firstMoverUtility_strict_of_rankFactorization`
- `MallowsAccuracyFamilySpec.theorem1RemovalMonotonicityAt`
- `mallowsInverseAccuracyQ_strictAnti`
- `AccuracyFamily.theorem1_f_epsilonContinuousAt_of_atom_continuity`
- `AccuracyFamily.theorem1_g_epsilonContinuousAt_of_atom_continuity`
- `AccuracyFamily.theorem1_f_sub_g_continuousOn_of_atom_continuity`
- `AccuracyFamily.theorem1_f_lt_h_persists_right_of_atom_continuity`
- `AccuracyFamily.theorem1_exists_right_initial_f_lt_g_of_atom_continuity`
- `AccuracyFamily.Theorem1AtomLocalNudgeCertificate`
- `AccuracyFamily.theorem1Target_of_atomLocalNudgeCertificate`
- `AccuracyFamily.Theorem1SignChangeNudgeCertificate`
- `AccuracyFamily.theorem1Target_of_signChangeNudgeCertificate`
- `AccuracyFamily.Theorem1IntervalAnalyticCertificate`
- `AccuracyFamily.theorem1Target_of_intervalAnalyticCertificate`
- `AccuracyFamily.Theorem1PaperAssumptions`
- `AccuracyFamily.theorem1Target_of_paperAssumptions`
- `AccuracyFamily.Theorem1GlobalAnalyticCertificate`
- `AccuracyFamily.theorem1Target_of_globalAnalyticCertificate`
- `StrictlyWellOrderedNoise`
- `WeaklyWellOrderedNoise`
- `gaussianNoiseKernel_strictlyWellOrdered`
- `gaussianNoiseKernel_pos`
- `laplacianNoiseKernel_weaklyWellOrdered`
- `laplacianNoiseKernel_pos`
- `laplacianNoiseKernel_strictlyWellOrdered_of_overlap`
- `laplacianNoiseKernel_not_strictlyWellOrdered`
- `rumContractScore`
- `rumContractScore_preserves_weak_order`
- `rumContractScore_preserves_strict_order`
- `rum3_contract_top_first_of_original_top_first`
- `rum3_contract_bottom_first_imp_original_bottom_first`
- `rum3TopFirstByScores`
- `rum3MiddleBeatsTopByScores`
- `rum3BottomFirstByScores`
- `rum3_swap_middle_transition_geometry`
- `weaklyWellOrderedNoise_swap_middle_density_le`
- `strictlyWellOrderedNoise_swap_middle_density_lt`
- `weaklyWellOrderedNoise_swap12_density3_le`
- `strictlyWellOrderedNoise_swap12_density3_lt`
- `weaklyWellOrderedNoise_swap23_density3_le`
- `strictlyWellOrderedNoise_swap23_density3_lt`
- `rum3_swap12_mass_le_of_density_formula`
- `rum3_swap12_mass_lt_of_density_formula`
- `rum3_swap23_mass_le_of_density_formula`
- `rum3_swap23_mass_lt_of_density_formula`
- `rum3_delta_weighted_sum_neg`
- `rum3_theorem6_payoff_algebra`
- `paper_theorem6_threeCandidate_payoff_algebra`
- `AccuracyFamily.expectedSecondMoverIndependent_sub_eq_sum_firstChoiceProb_sub_mul_bestAfterRemoval`
- `pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if`
- `pmfProb_nonneg`
- `pmfProb_le_one`
- `pmfProb_compl`
- `pmfProb_pos_of_mass`
- `pmf_apply_toReal_pos_of_pmfProb_preimage`
- `pmfProb_lt_one_of_mass_not`
- `pmfProb_le_of_imp`
- `pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le`
- `pmfProb_eq_add_diff_of_imp`
- `pmfProb_lt_of_imp_of_mass`
- `pmfProb_le_of_equiv_event_mass_le`
- `pmfProb_lt_of_equiv_event_mass_le_of_exists_strict`
- `rum3Lambda1`
- `rum3Lambda2`
- `rum3Lambda3`
- `rum3Lambda1_wrong_eq_one_sub`
- `rum3Lambda3_wrong_eq_one_sub`
- `rum3Lambda1_half_of_wrong_lt_correct`
- `rum3Lambda3_half_of_wrong_lt_correct`
- `rum3Lambda1_wrong_lt_correct_of_equiv`
- `rum3Lambda3_wrong_lt_correct_of_equiv`
- `rum3Lambda1_lt_lambda2_of_equiv`
- `rum3Lambda1_wrong_lt_correct_of_sample_equiv`
- `rum3Lambda3_wrong_lt_correct_of_sample_equiv`
- `rum3Lambda1_lt_lambda2_of_sample_equiv`
- `rum3Lambda1_wrong_to_correct_map_of_score_swap23`
- `rum3Lambda3_wrong_to_correct_map_of_score_swap12`
- `RUM3Theorem6Certificate`
- `RUM3LambdaCertificate`
- `RUM3DeltaCertificate`
- `rum3Theorem6Certificate_of_lambda_delta`
- `rum3DeltaCertificate_of_paper_lemmas`
- `rum3_lemma2_bottom_of_coupling`
- `rum3_middle_delta_indicator_le_bottom_middle`
- `rum3_bottom_top_indicator_le_top_delta`
- `rum3_lemma3_middle_of_transition_mass`
- `rum3_bottomMiddle_transition_le_bottomTop_of_swap_equiv`
- `rum3_monotonicity_top_of_coupling`
- `rum3DeltaCertificate_of_finite_contraction_facts`
- `rum3DeltaCertificate_of_finite_contraction_swap_facts`
- `rum3DeltaCertificate_of_finite_score_contraction_swap_facts`
- `rum3LambdaCertificate_of_pairwise_facts`
- `rum3Lambda1_le_one`
- `rum3Lambda2_le_one`
- `rum3Lambda3_le_one`
- `rum3Lambda1_lt_one_of_mass_choose_third_after_first_removed`
- `rum3Lambda1_lt_one_of_full_support`
- `rum3_fullSupport_of_sample_preimages`
- `rum3LambdaCertificate_of_pairwise_facts_and_support`
- `rum3LambdaCertificate_of_pairwise_wrong_facts_and_support`
- `rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support`
- `rum3LambdaCertificate_of_pairwise_swap_facts_and_support`
- `rum3LambdaCertificate_of_all_pairwise_swap_facts_and_support`
- `rum3LambdaCertificate_of_all_pairwise_swap_facts_and_full_support`
- `rum3LambdaCertificate_of_sample_swap_facts_and_full_support`
- `expectedBestAfterRemoval_rum3_remove0`
- `expectedBestAfterRemoval_rum3_remove1`
- `expectedBestAfterRemoval_rum3_remove2`
- `rum3_prefersWeakerCompetition_of_payoff_algebra`
- `rum3_prefersWeakerCompetition`
- `rum3_prefersWeakerCompetition_of_certificate`
- `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_payoff_algebra`
- `paper_theorem6_threeCandidate_prefersWeakerCompetition`
- `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_certificate`
- `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_lambda_and_finite_contraction_facts`
- `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_pairwise_wrong_and_finite_swap_facts`
- `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_finite_pairwise_and_delta_swap_facts`
- `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_all_finite_swap_facts`
- `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_all_finite_swap_facts_and_full_support`
- `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_all_finite_swap_and_score_contraction_facts`
- `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_sample_swaps_and_score_contraction_facts`
- `paper_appendixC_contractedScore`
- `paper_appendixC_contraction_preserves_weak_order`
- `paper_appendixC_contraction_preserves_strict_order`
- `paper_appendixC_contraction_top_first_of_original_top_first`
- `paper_appendixC_contraction_bottom_first_imp_original_bottom_first`
- `paper_lemma3_swapi_middle_transition_geometry`
- `paper_lemma3_swapi_density_le_of_weaklyWellOrdered`
- `paper_lemma3_swapi_density_lt_of_strictlyWellOrdered`
- `paper_theorem6_lambda_swap12_density3_le_of_weaklyWellOrdered`
- `paper_theorem6_lambda_swap12_density3_lt_of_strictlyWellOrdered`
- `paper_theorem6_lambda_swap23_density3_le_of_weaklyWellOrdered`
- `paper_theorem6_lambda_swap23_density3_lt_of_strictlyWellOrdered`
- `paper_theorem6_lambda_swap12_mass_le_of_density_formula`
- `paper_theorem6_lambda_swap12_mass_lt_of_density_formula`
- `paper_theorem6_lambda_swap23_mass_le_of_density_formula`
- `paper_theorem6_lambda_swap23_mass_lt_of_density_formula`
- `paper_lemma3_bottomMiddle_transition_le_bottomTop_of_swap_equiv`
- `paper_theorem6_deltaCertificate_of_finite_contraction_swap_facts`
- `paper_theorem6_deltaCertificate_of_finite_score_contraction_swap_facts`
- `paper_theorem6_certificate_of_lambda_delta`
- `paper_theorem6_deltaCertificate_of_lemmas2_3`
- `paper_lemma2_bottom_of_coupling`
- `paper_lemma3_middle_of_transition_mass`
- `paper_monotonicity_top_of_coupling`
- `paper_theorem6_deltaCertificate_of_finite_contraction_facts`
- `paper_theorem6_lambdaCertificate_of_pairwise_facts`
- `paper_theorem6_lambda1_le_one`
- `paper_theorem6_lambda1_lt_one_of_mass_choose_third_after_first_removed`
- `paper_theorem6_lambda1_lt_one_of_full_support`
- `paper_theorem6_fullSupport_of_sample_preimages`
- `paper_theorem6_lambdaCertificate_of_pairwise_facts_and_support`
- `paper_theorem6_lambda1_wrong_eq_one_sub`
- `paper_theorem6_lambda3_wrong_eq_one_sub`
- `paper_theorem6_lambda1_half_of_wrong_lt_correct`
- `paper_theorem6_lambda3_half_of_wrong_lt_correct`
- `paper_theorem6_lambdaCertificate_of_pairwise_wrong_facts_and_support`
- `paper_theorem6_lambdaCertificate_of_pairwise_wrong_facts_and_full_support`
- `paper_theorem6_lambda1_wrong_lt_correct_of_pairwise_equiv`
- `paper_theorem6_lambda3_wrong_lt_correct_of_pairwise_equiv`
- `paper_theorem6_lambda1_lt_lambda2_of_pairwise_equiv`
- `paper_theorem6_lambdaCertificate_of_pairwise_swap_facts_and_support`
- `paper_theorem6_lambdaCertificate_of_all_pairwise_swap_facts_and_support`
- `paper_theorem6_lambdaCertificate_of_all_pairwise_swap_facts_and_full_support`
- `paper_theorem6_lambdaCertificate_of_sample_swap_facts_and_full_support`
- `paper_theorem6_lambda1_wrong_to_correct_map_of_score_swap23`
- `paper_theorem6_lambda3_wrong_to_correct_map_of_score_swap12`

Current seam:

- The paper-facing theorem layer in `Monoculture/MainTheorems.lean` now exposes
  Theorem 3 hypotheses directly as finite-sum, reduced product-sign,
  backward-compatible cross-weight, and rank-factorized theorem wrappers.
- The two denominator-cleared independent-reranking finite Mallows sums are
  proved from the constructed `MallowsSpec.rankFactorization`, `0 < n`,
  `q < 1`, and strict center ordering via
  `MallowsSpec.independent_weight_sum_pos_of_rankFactorization`.
- The total weaker-competition cleared finite Mallows sum is now proved from
  constructed algorithm/human `RankFactorization`, strict `qA < qH`,
  `qH < 1`, and strict center ordering via the paper's Appendix-E
  conditional-gap/MLR route:
  `MallowsComparison.cross_weight_sum_pos_of_rankFactorization`.
- `MallowsComparison.paper_theorem3_pointwise_rankFactorization` is the current
  strongest paper-facing Theorem 3 endpoint. It no longer assumes the finite
  Mallows fiber factorization; `MallowsSpec.rankFactorization` constructs that
  package from the actual finite Kendall permutation fibers.
- `MallowsAccuracyFamilySpec.theorem1PaperAssumptions` now lifts the fixed
  Mallows theorem to a parameterized family: Definition 2 for every positive
  parameter and Definition 3 for every `θA > θH > 0` are discharged by the
  rank-factorized Mallows route. The strict `S = ∅` first-mover part of
  Definition 1 monotonicity is also now proved by
  `MallowsComparison.firstMoverUtility_strict_of_rankFactorization` from the
  Mallows rank-power MLR inequality. The singleton-removal weak monotonicity
  part is also proved by
  `MallowsComparison.expectedBestAfterRemoval_le_of_rankFactorization`, using
  the rank-only theorem
  `candidateRankBestAfterRemovalWeight_pairwise_cross_nonneg`. The concrete
  finite Mallows PMF is now constructed by `MallowsSpec.ofQ`, and its positive
  parameter atomwise continuity is proved by
  `concreteMallowsSpec_atom_continuity`. The concrete Mallows asymptotic
  first-dominance field is now proved by
  `concreteMallowsSpec_asymptotic_first_dominance`, using the small-`q`
  rank-average crossing between `MallowsSpec.humanAgainstRankAverage` and
  `MallowsSpec.sharedRankPayoffAverage`. The assumption-free concrete family is
  packaged as `concreteMallowsAccuracyFamilySpec`, and the paper-facing endpoint
  is `paper_theorem1_concrete_mallows_family`.
- The top-one/top-two Mallows fiber package is proved from finite Kendall
  normalization:
  first-choice fibers use `cycleRange`; ordered top-two fibers use `cycleRange`
  followed by `cycleIcc 1 s`; swapped top-two fibers use the same construction
  and pick up the extra `q` factor.
- Theorem 1's game/payoff bridge is formalized through the sign-change nudge
  certificate. The finite analytic bridge
  `AccuracyFamily.theorem1_f_epsilonContinuousAt_of_atom_continuity`, which
  proves continuity of the paper's `f(θA)` from atomwise epsilon-delta
  continuity of the finite ranking law, and
  `AccuracyFamily.theorem1_f_lt_h_persists_right_of_atom_continuity`, which
  proves the paper's `f < h` persistence step, are closed.
- The right-neighborhood `g < f` side is now formalized from an interval
  sign-change certificate using `DecisionCore.exists_last_nonpos_with_right_pos_on_Icc`.
  Instead of assuming an arbitrary crossing has the right one-sided sign, Lean
  chooses the last nonpositive point of `f - g` on a compact interval.
- The strongest current Theorem 1 endpoint is
  `AccuracyFamily.theorem1Target_of_paperAssumptions`, which first builds
  `AccuracyFamily.Theorem1GlobalAnalyticCertificate`. It packages Definition 2
  at equal accuracy, Definition 3 only for `θA > θH`, atomwise continuity,
  asymptotic eventual `g < f`, and finite-removal monotonicity. From this
  bundle, Lean constructs the interval certificate, last-nonpositive crossing,
  right nudge, payoff certificate, and final paradox witness.
- The equal-accuracy crossing no longer requires `Model.PaperHypotheses
  (F.modelAt θH θH)`, which would include the Definition 3 comparison outside
  its paper domain. The exact bridge is now
  `AccuracyFamily.theorem1_exists_right_initial_f_lt_g_of_prefersIndependent_and_atom_continuity`.
- Theorem 1 is closed for the concrete Mallows family via
  `paper_theorem1_concrete_mallows_family`. The abstract Theorem 1 bridge
  remains available for other noisy permutation families that instantiate
  `AccuracyFamily.Theorem1PaperAssumptions F` or
  `AccuracyFamily.Theorem1GlobalAnalyticCertificate F θH`.
- Appendix C / Lemma 1 has a first RUM-side checkpoint in `Monoculture/RUM.lean`:
  Gaussian density kernels are strictly well-ordered
  (`paper_lemma1_gaussian_strictlyWellOrdered`), while Laplacian kernels satisfy
  only the weak pointwise inequality globally
  (`paper_lemma1_laplacian_weaklyWellOrdered`). Strictness is proved on the
  interval-overlap region as
  `paper_lemma1_laplacian_strictlyWellOrdered_of_overlap`. The strict
  Laplacian statement under paper Definition 4 is false as written; Lean records
  `paper_lemma1_laplacian_not_strictlyWellOrdered` using the concrete separated
  ordered pair `a=10, b=9, c=1, d=0`. Positivity of the Gaussian and Laplacian
  kernels is also exposed as `paper_lemma1_gaussianNoiseKernel_pos` and
  `paper_lemma1_laplacianNoiseKernel_pos` for density-product mass comparisons.
- Appendix C's deterministic contraction geometry is now formalized:
  `paper_appendixC_contraction_preserves_weak_order` and
  `paper_appendixC_contraction_preserves_strict_order` prove the two-candidate
  "contraction cannot create inversions" inequality for real score
  realizations, and `paper_appendixC_contraction_top_first_of_original_top_first`
  plus `paper_appendixC_contraction_bottom_first_imp_original_bottom_first`
  expose the three-candidate consequences. The score predicates
  `rum3TopFirstByScores`, `rum3MiddleBeatsTopByScores`, and
  `rum3BottomFirstByScores` now feed
  `paper_theorem6_deltaCertificate_of_finite_score_contraction_swap_facts`,
  which derives the ranking-level top-no-out, bottom-implication, and Lemma 3
  `swapi` event-map facts from score geometry. This is not yet the density
  pushforward or mass-dominance proof.
- Appendix C / Lemma 3 also has the pointwise `swapi` pieces formalized:
  `paper_lemma3_swapi_middle_transition_geometry` proves the deterministic
  score-region mapping for the middle-candidate case, and
  `paper_lemma3_swapi_density_le_of_weaklyWellOrdered` /
  `paper_lemma3_swapi_density_lt_of_strictlyWellOrdered` prove the pointwise
  density comparison from well-ordered noise. The finite change-of-variables
  skeleton is closed as
  `paper_lemma3_bottomMiddle_transition_le_bottomTop_of_swap_equiv`, and the
  delta side can now use
  `paper_theorem6_deltaCertificate_of_finite_contraction_swap_facts`. The
  remaining Lemma 3 gap is to instantiate the continuous `swapi` equivalence and
  mass-dominance premise from the density model.
- Appendix C / Theorem 6 now has its finite scalar payoff algebra closed as
  `paper_theorem6_threeCandidate_payoff_algebra`. This proves the paper's final
  `Σ Δp_i u_-i < 0` step from the value ordering, lambda inequalities, delta
  first-choice-probability inequalities, and total-mass identity. The theorem is
  also connected to Definition 3 at model level by
  `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_payoff_algebra`,
  using the generic payoff-delta identity
  `AccuracyFamily.expectedSecondMoverIndependent_sub_eq_sum_firstChoiceProb_sub_mul_bestAfterRemoval`.
  The stronger endpoint `paper_theorem6_threeCandidate_prefersWeakerCompetition`
  derives the three `u_-i` best-after-removal identities from finite two-outcome
  expectations (`expectedBestAfterRemoval_rum3_remove0/1/2`), so those are no
  longer assumptions. The current finite endpoint is packaged as
  `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_certificate`, whose
  `RUM3Theorem6Certificate` fields are exactly the upstream RUM facts from
  monotonicity, Lemma 2, Lemma 3, and the pairwise human lambda comparisons.
  Those are split into `RUM3DeltaCertificate` and `RUM3LambdaCertificate` with
  paper-facing constructors
  `paper_theorem6_deltaCertificate_of_lemmas2_3` and
  `paper_theorem6_lambdaCertificate_of_pairwise_facts`.
  The finite probability support step for the `λ₁ < 1` field is closed either by
  `paper_theorem6_lambda1_lt_one_of_mass_choose_third_after_first_removed`,
  which uses the generic finite probability lemma `pmfProb_lt_one_of_mass_not`,
  or by the stronger full-support wrapper
  `paper_theorem6_lambda1_lt_one_of_full_support`. Full support of the induced
  finite ranking law can itself be derived from realization preimages via
  `paper_theorem6_fullSupport_of_sample_preimages`, backed by the generic
  `pmf_apply_toReal_pos_of_pmfProb_preimage`. The preferred lambda
  constructors now avoid raw scalar half-bounds: wrong-vs-correct comparisons
  feed `paper_theorem6_lambdaCertificate_of_pairwise_wrong_facts_and_full_support`,
  and finite paired swap certificates feed
  `paper_theorem6_lambdaCertificate_of_all_pairwise_swap_facts_and_full_support`.
  The strict finite change-of-variables lemma
  `pmfProb_lt_of_equiv_event_mass_le_of_exists_strict` supports the pairwise
  wrappers `paper_theorem6_lambda1_wrong_lt_correct_of_pairwise_equiv`,
  `paper_theorem6_lambda3_wrong_lt_correct_of_pairwise_equiv`, and
  `paper_theorem6_lambda1_lt_lambda2_of_pairwise_equiv`. The same strict
  change-of-variables pattern is also exposed on a finite realization space by
  `paper_theorem6_lambdaCertificate_of_sample_swap_facts_and_full_support`, so
  lambda swaps no longer need to act directly on rankings. The complement
  identities are `paper_theorem6_lambda1_wrong_eq_one_sub` and
  `paper_theorem6_lambda3_wrong_eq_one_sub`. The wrong-vs-correct realization
  event maps for the `x₂`/`x₃` and `x₁`/`x₂` pairwise comparisons are also
  available from score swaps as
  `paper_theorem6_lambda1_wrong_to_correct_map_of_score_swap23` and
  `paper_theorem6_lambda3_wrong_to_correct_map_of_score_swap12`; their remaining
  analytic inputs are the mass comparisons and marginal identifications.
  The pointwise three-coordinate density comparisons for those pairwise swaps
  are formalized as
  `paper_theorem6_lambda_swap12_density3_le_of_weaklyWellOrdered` /
  `paper_theorem6_lambda_swap12_density3_lt_of_strictlyWellOrdered` and
  `paper_theorem6_lambda_swap23_density3_le_of_weaklyWellOrdered` /
  `paper_theorem6_lambda_swap23_density3_lt_of_strictlyWellOrdered`; the
  unaffected third coordinate is factored out explicitly. When a finite sample
  law provides atom masses by the corresponding three-coordinate density
  product, the wrappers
  `paper_theorem6_lambda_swap12_mass_le_of_density_formula`,
  `paper_theorem6_lambda_swap12_mass_lt_of_density_formula`,
  `paper_theorem6_lambda_swap23_mass_le_of_density_formula`, and
  `paper_theorem6_lambda_swap23_mass_lt_of_density_formula` turn those
  pointwise density comparisons into the finite mass-dominance hypotheses used
  by the sample-space lambda certificate.
  Appendix C / Lemma 2 has its finite coupling probability step closed as
  `paper_lemma2_bottom_of_coupling`, using the generic event-inclusion lemma
  `pmfProb_le_of_imp`. The remaining Lemma 2 work is the continuous RUM
  contraction coupling: construct the coupled law, identify its marginals with
  `F_{θA}` and `F_{θH}`, and prove the bottom-first event implication.
  Appendix C / Lemma 3 now has its three-candidate finite transition-mass step
  closed as `paper_lemma3_middle_of_transition_mass`. This packages the paper's
  finite delta algebra after the continuous `swapi` argument into two inputs:
  top-first realizations cannot leave the top under contraction, and the
  `x₃ → x₂` transition mass is at most the `x₃ → x₁` transition mass.
  The monotonicity step is similarly closed as
  `paper_monotonicity_top_of_coupling` from strict finite event inclusion, and
  these three finite delta ingredients are packaged by
  `paper_theorem6_deltaCertificate_of_finite_contraction_facts`.
  The current strongest direct endpoint is
  `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_sample_swaps_and_score_contraction_facts`,
  which proves the Definition 3 weaker-competition conclusion from a single
  finite realization law, full finite support of the induced human ranking law,
  realization-space swap certificates for all three lambda comparisons,
  score-to-ranking interface facts, marginal-identification equalities, and
  finite `swapi` mass dominance. The contraction and `swapi` event-map geometry
  are now proved inside Lean from real-score inequalities. The remaining work
  for full RUM Theorem 6 is to instantiate the finite support, realization
  swaps, score-interface, marginal, and mass-dominance fields from the
  continuous RUM density model.
- The adjacent-coefficient/suffix-sign bridge remains compiled as a diagnostic,
  but the global suffix sign condition is too strong in general and should not
  be used as the main theorem route. Individual cross pair brackets and
  non-center candidate products are also not sign-definite enough.

Recommended next proof order:

1. Keep `Monoculture/MainTheorems.lean` as the human-facing endpoint and
   `Monoculture/Theorem1.lean` as the active Theorem 1 proof file.
2. For Mallows, the actual `θ = φ - 1` concrete family is now instantiated by
   `concreteMallowsAccuracyFamilySpec`; do not redo the q-order, continuity,
   asymptotic, no-removal, or singleton-removal seams. For other noisy
   permutation families, instantiate
   `AccuracyFamily.Theorem1PaperAssumptions` or the fixed-`θH`
   `AccuracyFamily.Theorem1GlobalAnalyticCertificate` directly.
3. Separately instantiate atomwise continuity of concrete finite ranking
   families using `DecisionCore.EpsilonContinuity`; do not reprove finite
   expectation continuity inside the paper file.
4. Keep `Monoculture/MallowsPairwise.lean` as the rank-factorized Theorem 3
   proof and avoid the older suffix-sign route except as a diagnostic.
5. For RUM Appendix C, do not assume the paper's strict Laplacian Definition 4
   statement. Continue from the weak Laplacian inequality/counterexample and
   either prove the integrated strict comparison directly or isolate the exact
   strengthened condition needed for Theorem 6.
6. For RUM Theorem 6, do not redo the scalar two-case payoff algebra, the finite
   Lemma 2 event-inclusion step, or the finite Lemma 3 transition-mass algebra;
   continue from `paper_theorem6_threeCandidate_prefersWeakerCompetition` and
   attack the upstream continuous lambda/delta hypotheses as separate RUM
   lemmas.

### Other Imported Tracks

User-item fairness modules:

- `UserItemFairness.Basic`
- `UserItemFairness.Optimization`
- `UserItemFairness.Symmetry`
- `UserItemFairness.LPReduction`
- `UserItemFairness.ReductionPreservation`

Useful next targets:

- sparse-support bounds for basic feasible solutions
- finite-LP compactness/existence for nonzero `γ` feasible-value nonemptiness
  or attainment

Implemented recent anchors:

- `DecisionCore.pmf_apply_toReal_le_one`
- `DecisionCore.uniformPMF`
- `DecisionCore.uniformPMF_apply_toReal`
- `DecisionCore.uniformPMF_apply_toReal_pos`
- `DecisionCore.finiteMin_pos`
- `DecisionCore.Policy.sum_fiber_card_mul`
- `DecisionCore.Policy.finiteMin_comp_of_fiberRepresentatives`
- `DecisionCore.finiteMin_nonneg`
- `RecommendationModel.itemFairness_nonneg_of_nonnegative`
- `RecommendationModel.feasibleAtLevel_zero_of_nonnegative`
- `RecommendationModel.attainableUserFairnessAtLevel_zero_nonempty_of_nonnegative`
- `TypeWeightedRecommendationModel.NonnegativeUtilities`
- `TypeWeightedRecommendationModel.PositiveWeights`
- `TypeWeightedRecommendationModel.PositiveUtilities`
- `TypeWeightedRecommendationModel.itemFairness_nonneg_of_nonnegative`
- `TypeWeightedRecommendationModel.uniformTypePolicy`
- `TypeWeightedRecommendationModel.rawItemUtility_le_itemNormalizer_of_nonnegative`
- `TypeWeightedRecommendationModel.normalizedItemUtility_le_one_of_nonnegative`
- `TypeWeightedRecommendationModel.itemNormalizer_pos_of_positive`
- `TypeWeightedRecommendationModel.itemFairness_uniform_pos_of_positive`
- `TypeWeightedRecommendationModel.optimalItemFairness_pos_of_positive`
- `TypeWeightedRecommendationModel.item_coverage_of_itemFairness_pos`
- `TypeWeightedRecommendationModel.feasibleAtLevel_zero_of_nonnegative`
- `TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel_zero_nonempty_of_nonnegative`
- `ReductionWitness.reduced_nonnegativeWeights`
- `ReductionWitness.reduced_nonnegativeUtilities_of_nonnegative`
- `ReductionWitness.rawItemUtility_liftedPolicy_eq_rawItemUtility`
- `ReductionWitness.itemNormalizer_eq_itemNormalizer`
- `ReductionWitness.normalizedItemUtility_liftedPolicy_eq_normalizedItemUtility`
- `ReductionWitness.itemFairness_liftedPolicy_eq_itemFairness`
- `ReductionWitness.userFairness_liftedPolicy_eq_typeFairness`
- `RecommendationModel.symmetricAttainableItemFairnessSet`
- `RecommendationModel.symmetricOptimalItemFairness`
- `ReductionWitness.symmetricAttainableItemFairnessSet_eq_reduced`
- `ReductionWitness.symmetricOptimalItemFairness_eq_reduced`
- `RecommendationModel.SymmetricData.rawUserUtility_symmetrizedPolicy_eq_average`
- `RecommendationModel.SymmetricData.normalizedUserUtility_symmetrizedPolicy_eq_average`
- `RecommendationModel.SymmetricData.userFairness_le_userFairness_symmetrizedPolicy`
- `RecommendationModel.rawUserUtility_le_bestItemUtility`
- `RecommendationModel.normalizedUserUtility_le_one_of_rowHasPositiveItem`
- `RecommendationModel.attainableUserFairnessAtLevel_bddAbove_of_rowHasPositiveItem`
- `TypeWeightedRecommendationModel.rawTypeUtility_le_bestItemUtility`
- `TypeWeightedRecommendationModel.normalizedTypeUtility_le_one_of_rowHasPositiveItem`
- `TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel_bddAbove_of_rowHasPositiveItem`
- `ReductionWitness.optimalUserFairnessAtLevel_eq_reduced_of_nonempty`
- `ReductionWitness.optimalItemFairness_eq_reduced`
- `ReductionWitness.optimalUserFairnessAtLevel_eq_reduced_of_bddAbove_nonempty`
- `ReductionWitness.isOptimalAtLevel_liftedPolicy_of_reduced`
- `ReductionWitness.exists_typePolicy_preserving_fairness_of_isTypeSymmetric`
- `ReductionWitness.exists_reducedOptimalAtLevel_of_original_symmetric_optimal`
- `ReductionWitness.paper_original_reduced_user_optimal_value_reduction_zero`
- `TypePolicy.card_items_add_sharedItems_le_activePairsCard`
- `TypePolicy.BasicFeasibleSupportCertificate`
- `TypePolicy.activeTypeItemPairsCard_add_inactiveTypeItemPairsCard_eq`
- `TypePolicy.activePairsBound_of_basicFeasibleSupportCertificate`
- `TypePolicy.sharedItemsBound_of_activePairsBound_of_item_coverage`
- `TypePolicy.sparseShape_of_activePairsBound_of_item_coverage`
- `TypePolicy.paper_reduced_optimal_item_fairness_positive`
- `TypePolicy.paper_active_pairs_bound_of_basic_feasible_support`
- `TypePolicy.paper_sparse_shared_items_of_active_pairs_bound_of_maximal_optimum`
- `TypePolicy.paper_sparse_shape_of_active_pairs_bound_of_maximal_optimum`
- `TypePolicy.paper_sparse_shared_items_of_basic_feasible_maximal_optimum`
- `TypePolicy.paper_sparse_shape_of_basic_feasible_maximal_optimum`

Current seam:

- The lifted-policy preservation layer is closed for user fairness and item
  fairness. Symmetrization now preserves item fairness and weakly improves
  minimum normalized user fairness under row-positive user normalizers. The
  original/reduced optimal user-fairness value equality is proved from explicit
  nonempty feasible-value side conditions; boundedness is automatic because
  normalized user/type fairness is at most `1`. At baseline `γ = 0`,
  nonnegative utilities now discharge the original and reduced nonemptiness
  side conditions via a default policy. For the paper's sparse-support result,
  the finite counting half is closed: if every item has an active type and the
  active type-item support has size at most `n + K - 1`, then at most `K - 1`
  items are shared. The "every item active" condition is also discharged for a
  maximal-item-fairness optimum under strictly positive type weights/utilities,
  using the formalized reduced `IF* > 0` lemma and the uniform policy witness.
  The support-count arithmetic half of the LP/BFS argument is now closed via
  `TypePolicy.BasicFeasibleSupportCertificate`: if at least
  `nK + 1 - (n + K)` type-item nonnegativity constraints bind, then
  `TypePolicy.ActivePairsBound` follows, and a maximal-item-fairness optimum
  has the full `SparseShape`. The remaining seam is only the generic
  linear-programming theorem that a basic feasible solution of the reduced LP
  supplies `BasicFeasibleSupportCertificate`.

Recommended next proof order:

1. Add generic support-count lemmas, probably in `DecisionCore.Policy`: define
   inactive state-action pairs and prove
   `activePairsCard ρ + inactivePairsCard ρ = Fintype.card α * Fintype.card β`.
2. Formalize or import the generic finite-LP theorem that a basic feasible
   solution has enough active/binding constraints to produce
   `TypePolicy.BasicFeasibleSupportCertificate`.
3. Use that theorem to replace the remaining support certificate in
   `TypePolicy.paper_sparse_shape_of_basic_feasible_maximal_optimum`.

Accuracy-diversity modules:

- `AccuracyDiversity.Basic`
- `AccuracyDiversity.Representation`
- `AccuracyDiversity.TopKOracle`
- `AccuracyDiversity.Bernoulli`
- `AccuracyDiversity.Uniform`
- `AccuracyDiversity.Optimization`
- `AccuracyDiversity.Exchange`
- `AccuracyDiversity.BernoulliExchange`
- `AccuracyDiversity.Examples`

Useful next targets:

- order-statistic/asymptotic machinery for bounded, exponential, Pareto, and
  non-identical Bernoulli models
- discrete `TopKValueOracle` instantiations for non-Bernoulli item-value
  distributions

Implemented recent anchors:

- `EconCSLib.FiniteSum.sum_eq_sum_add_sub_add_sub_of_eq_off`
- `TopKValueOracle.HasNonnegativeMarginalsAt`
- `TopKValueOracle.toConsumptionModel_has_nonnegative_marginals`
- `TopKValueOracle.toConsumptionModel_has_diminishing_returns`
- `ConsumptionModel.total_moveOne_eq`
- `ConsumptionModel.objective_moveOne_eq`
- `ConsumptionModel.exchangeImprovementTarget`
- `ConsumptionModel.noProfitableExchangeAtOptimumTarget`
- `ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum`
- `ConsumptionModel.FeasibleAllocationCode`
- `ConsumptionModel.exists_isOptimalAtTotal`
- `ConsumptionModel.paper_finite_optimum_exists`
- `BernoulliSatisfactionModel.paper_bernoulli_finite_optimum_exists`
- `BernoulliSatisfactionModel.weightedForwardMarginal_toConsumptionModel`
- `BernoulliSatisfactionModel.weightedBackwardMarginal_toConsumptionModel`
- `BernoulliSatisfactionModel.forwardMarginal_le_backwardMarginal_of_optimum`
- `twoTypeAllocation_total`
- `twoTypeAllocation_objective`
- `twoTypeAllocation_forward_one_le_backward_zero_of_optimum`
- `twoTypeAllocation_forward_zero_le_backward_one_of_optimum`
- `BernoulliSatisfactionModel.pairwise_count_le_succ_of_symmetric_optimum`
- `count_abs_sub_uniform_average_le_one_of_pairwise_balanced`
- `uniformProfile_approx_of_pairwise_balanced_counts`
- `BernoulliSatisfactionModel.paper_iid_bernoulli_optimum_pairwise_balanced`
- `BernoulliSatisfactionModel.paper_iid_bernoulli_optimum_uniform_homogeneity`
- `paper_symmetric_two_type_bernoulli_optimum_balanced`
- `paper_symmetric_two_type_bernoulli_optimum_equal_homogeneity`
- `uniformTopOneValue_succ_sub`
- `uniformTopOneValue_sub_pred`
- `uniformTopOneConsumptionModel`
- `sqrtLikelihoodProfile`
- `sqrtLikelihoodProfile.approx_of_count_abs_error`
- `EconCSLib.FiniteRounding.NoRoundingCrossing`
- `EconCSLib.FiniteRounding.NoRoundingCrossing.count_lt_anchor_add_card`
- `EconCSLib.FiniteRounding.NoRoundingCrossing.anchor_lt_count_add_card`
- `EconCSLib.FiniteRounding.NoRoundingCrossingBetween`
- `EconCSLib.FiniteRounding.NoRoundingCrossingBetween.count_lt_upper_add_card`
- `EconCSLib.FiniteRounding.NoRoundingCrossingBetween.lower_lt_count_add_card`
- `UniformRounding.count_close_of_no_rounding_crossing`
- `UniformRounding.count_close_of_no_rounding_crossing_between`
- `UniformTopOne.StrictRoundingExchangeCertificate`
- `UniformTopOne.StrictRoundingExchangeCertificateBetween`
- `UniformTopOne.noRoundingCrossing_of_strictExchangeCertificate`
- `UniformTopOne.noRoundingCrossingBetween_of_strictExchangeCertificate`
- `UniformTopOne.strictRoundingExchangeCertificateBetween_of_shifted_target`
- `UniformTopOne.forwardMarginal_le_backwardMarginal_of_optimum`
- `paper_uniform_top_one_optimum_first_order_condition`
- `paper_uniform_sqrt_homogeneity_of_count_closeness`
- `paper_rounding_count_close_of_no_crossing`
- `paper_uniform_rounding_count_close_of_strict_exchange_certificate`
- `paper_uniform_top_one_sqrt_homogeneity_of_anchor_certificate`
- `paper_uniform_rounding_count_close_of_two_anchor_certificate`
- `paper_uniform_top_one_sqrt_homogeneity_of_two_anchor_certificate`
- `paper_uniform_rounding_count_close_of_shifted_square_anchors`
- `paper_uniform_top_one_sqrt_homogeneity_of_shifted_square_anchors`

Current seam:

- The finite fixed-total existence, exchange/local-optimality, and symmetric
  i.i.d. Bernoulli `0`-homogeneity layers are closed. The generic bridge now is:
  finite optimality gives pairwise count balance; pairwise count balance gives
  uniform-share approximation with error `1 / N`. For Proposition 2, the
  `U([0,1])`, `k = 1` order-statistic value and finite first-order marginal
  inequality are closed, as is the square-root-profile representation bridge.
  The combinatorial part of Appendix D.5 is now generic in `EconCSLib.Math`:
  no high/low crossing around floor anchors implies each integer count is
  within one type-cardinality of its anchor. For uniform top-one objectives, a
  strict boundary exchange certificate now proves no high/low crossing at any
  finite optimum. A more faithful two-anchor version is also closed: lower and
  upper anchors with nearby totals, coordinatewise `lower ≤ upper`, and a
  strict two-anchor exchange certificate give the same rounding closeness. The
  strict certificate itself is now discharged from a squared shifted-target
  representation `likelihood t = scale * shift t ^ 2` plus lower/upper
  bracketing of `shift`. The paper-facing finite assembly theorem now derives
  `((m : ℝ) + 1) / N`
  square-root-profile approximation from one-item lower/upper anchor closeness
  plus the shifted-square bracketing facts. Remaining Proposition 2 work is the
  real-relaxation optimizer and construction of finite lower/upper anchors that
  bracket the shifted square-root real targets and have one-item closeness to
  the paper's square-root profile, then the paper's full
  asymptotic/order-statistic layer for Theorems 1/2/3.

### Discretization Bias Author-Paper Track

Modules:

- `EconCSLib.Decision.Argmax`
- `DiscretizationBias.MainTheorems`

Implemented anchors:

- `EconCSLib.Decision.IsPointwiseMax`
- `EconCSLib.Decision.sum_score_le_of_isPointwiseMax`
- `EconCSLib.Decision.averageScore`
- `EconCSLib.Decision.averageScore_le_of_isPointwiseMax`
- `EconCSLib.Decision.exists_maximizingDecisionRule`
- `DiscretizationBias.paper_theorem2i_finite_objective_optimizer_exists`
- `DiscretizationBias.paper_theorem2ii_argmax_accuracy_maximizing`

Current seam:

- The finite deterministic optimizer-existence core of Theorem 2(i) and the
  Bayes-score core of Theorem 2(ii) are closed. Full paper formalization needs
  calibrated continuous predictors, randomized independent decision rules,
  reference-distribution/fidelity definitions, and Pareto-frontier reasoning.

### Producer Fairness Author-Paper Track

Modules:

- `EconCSLib.Statistics.BinaryRating`
- `ProducerFairness.MainTheorems`
- `ProducerFairness.PaperFacingTheorems`

Implemented anchors:

- `EconCSLib.Statistics.priorWeightedVariance`
- `EconCSLib.Statistics.priorWeightedPosteriorMean`
- `EconCSLib.Statistics.priorWeightedBias`
- `EconCSLib.Statistics.priorWeightedSquaredBias`
- `EconCSLib.Statistics.JensenConvex`
- `EconCSLib.Statistics.JensenConcave`
- `EconCSLib.Statistics.GlobalMinAt`
- `EconCSLib.Statistics.GlobalMaxAt`
- `EconCSLib.Statistics.priorWeightedSquaredBias_mono`
- `EconCSLib.Statistics.priorWeightedSquaredBias_jensenConvex_quality`
- `EconCSLib.Statistics.priorWeightedSquaredBias_globalMin_priorMean`
- `EconCSLib.Statistics.priorWeightedVariance_jensenConcave_quality`
- `EconCSLib.Statistics.priorWeightedVariance_globalMax_half`
- `EconCSLib.Statistics.priorWeightedVariance_quality_zero`
- `EconCSLib.Statistics.priorWeightedVariance_quality_one`
- `EconCSLib.Statistics.priorWeightedVariance_weak_decrease`
- `EconCSLib.Statistics.priorWeightedVariance_strict_decrease_of_interior_quality`
- `ProducerFairness.paper_theorem3_1_variance_weak_decrease`
- `ProducerFairness.paper_theorem3_1_variance_strict_decrease_interior`
- `ProducerFairness.paper_theorem3_1_squared_bias_nondecreasing`
- `ProducerFairness.paper_theorem3_2_squared_bias_convex_in_quality`
- `ProducerFairness.paper_theorem3_2_squared_bias_global_min_at_prior_mean`
- `ProducerFairness.paper_theorem3_2_variance_concave_in_quality`
- `ProducerFairness.paper_theorem3_2_variance_global_max_at_half`
- `ProducerFairness.paper_theorem3_1_variance_strict_decrease_counterexample_quality_zero`
- `ProducerFairness.paper_theorem3_1_variance_strict_decrease_counterexample_quality_one`

Current seam:

- The corrected strict-variance-decrease clause of Theorem 3.1 is formalized
  under `0 < q_v < 1`, `0 < t`, `0 < alpha + beta`, `0 ≤ etaLow`, and
  `etaLow < etaHigh`.
- The weak variance-decrease clause is formalized on the full closed quality
  interval `0 ≤ q_v ≤ 1` under nondecreasing prior strength.
- The Theorem 3.1 squared-bias monotonicity clause and Theorem 3.2
  squared-bias/variance shape clauses are formalized for the fixed binary
  rating model.
- The paper README logs the remaining statement bug: the published strict claim
  needs to exclude boundary qualities, or state weak decrease on `[0, 1]` and
  reserve strictness for the interior case.
- A declaration-ordered paper-facing ledger now exists at
  `ProducerFairness/PaperFacingTheorems.lean` for one-file human verification.
- Remaining Producer Fairness targets are outside the fixed-model theorem pair:
  responsive-market theory and any executable/statistical estimator extensions.

## Repo Conventions

- Keep durable proving guidance in `skills/econcs-formalizer/SKILL.md`.
- Keep current theorem status in this file and paper-specific docs.
- Build touched modules first, then paper roots, then `lake build EconCSLib`.
- Avoid broad refactors while theorem seams are active.
- Do not introduce `sorry` unless explicitly requested.
