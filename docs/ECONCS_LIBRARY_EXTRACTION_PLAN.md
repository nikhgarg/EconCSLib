# EconCS Library Extraction Plan

This plan records reusable infrastructure that should be moved out of paper
folders, plus cleanup instructions for paper-local wrappers that should call
shared lemmas. The scope is broader than probability: continuous analysis,
finite ranking models, stochastic processes, optimization, and asymptotics all
show up repeatedly in EconCS papers.

## Current Shared Lemmas To Reuse

- `EconCSLib.Foundations.Probability.MeasureInequalities`
  - a.e. congruence from null exceptional sets:
    `ae_of_forall_not_mem_null`, `ae_eq_of_forall_not_mem_null`,
    `ae_iff_of_forall_not_mem_null`, `ae_eq_of_subset_null`,
    `ae_iff_of_subset_null`;
  - indicator and cutoff conversion:
    `ae_eq_decide_of_ae_iff`, `ae_eq_if_of_ae_iff`,
    `ae_eq_setIndicator_of_ae_iff_mem`,
    `ae_iff_le_lt_of_level_null`, `ae_iff_lt_le_of_level_null`;
  - positive-mass contradiction for a.e. inequalities:
    `measure_eq_zero_of_ae_property_failure_mass`,
    `measure_eq_zero_of_ae_le_of_gt`,
    `measure_eq_zero_of_ae_lt_of_le`,
    `ae_imp_le_contradicts_positive_selected_lt_mass`, and
    `positive_selected_lt_mass_of_positive_lower_lt_mass`;
  - null symmetric-difference cleanup:
    `measure_set_congr_of_symmDiff_null`,
    `measure_symmDiff_union_left_eq_zero`,
    `measure_symmDiff_diff_left_eq_zero`,
    `measure_diff_left_congr_of_symmDiff_null`,
    `measure_symmDiff_Ioo_union_Ioo_touching_eq_zero`,
    `measure_symmDiff_Ioo_union_Ioi_touching_eq_zero`,
    `ae_eq_set_union_left`, `ae_eq_set_diff_left`,
    `ae_eq_Ioo_union_Ioo_touching`, and `ae_eq_Ioo_union_Ioi_touching`.
- `EconCSLib.Foundations.Optimization.ChoiceEquilibriumAE` and
  `BinaryChoiceAE`
  - `isChoiceEquilibriumAE_of_forall_not_mem_null`,
    `noProfitableBinaryChoiceDeviationAE_of_forall_not_mem_null`,
    `noProfitableBinaryChoiceDeviationAE_of_bool_best_response_forall_not_mem_null`,
    `choice_rule_iff_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie`,
    and `bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie`.
- `EconCSLib.Foundations.Probability.OrderStatistics`
  - bottom-indexed source mean bridges:
    `orderStatisticTopKSumFromMean`, `sampleOrderStatisticValue`,
    `expectedSampleOrderStatisticMean`, `expectedOrderStatisticMeanSeq`,
    `orderStatisticTopKSumFromSample_eq_sampleTopKSum`,
    `expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum`, and
    `expectedOrderStatisticMeanSeq_topKEndpointLoss_eq_expectedReflectedBottomKSum`.
- `EconCSLib.Foundations.Probability.FiniteExpectation`
  - finite event helpers:
    `pmfExp_le_const_mul_pmfProb_of_forall_le_indicator` and
    `pmfPairExp_indicator_and_eq_mul_pmfProb`.
- `EconCSLib.Foundations.Math.Asymptotics`
  - fixed finite asymptotic assembly:
    `finite_sum_asymptoticEquivalent_common_scale` and
    `asymptoticEquivalent_add_negligible_common_scale`;
  - finite-prefix cleanup for zero-convergent schedules:
    `tendsToZero_if_lt_const`.
- `EconCSLib.Foundations.Math.ConvexCombination`
  - two-point weighted-average algebra for pooled estimates:
    `twoPointWeightedAverage`,
    `twoPointWeightedAverage_denominator_pos_of_left_pos_right_nonneg`,
    `lt_twoPointWeightedAverage_of_lt_components`,
    `twoPointWeightedAverage_lt_of_components_lt`,
    `lt_twoPointWeightedAverage_of_weighted_gap_pos`,
    `twoPointWeightedAverage_lt_of_weighted_gap_neg`, and
    `continuous_twoPointWeightedAverage`.
- `EconCSLib.Foundations.Math.ThresholdCharacterization`
  - unbounded continuous monotone cutoff existence and threshold-region
    packages:
    `existsUnique_eq_of_continuous_strictAnti_tendsto_atBot_atTop` and
    `existsUnique_eq_and_upper_region_of_continuous_strictAnti_tendsto_atBot_atTop`.
- `EconCSLib.Foundations.Probability.Gaussian` and `GaussianMathlib`
  - hazard/truncated-normal seam:
    `GaussianHazardCertificate.hazard_gt_arg_of_pos`,
    `GaussianHazardCertificate.normalUpperTailMean_gt_threshold`, and
    `standardGaussian_normalUpperTailMean_gt_threshold`;
  - positive Gaussian interval mass between a threshold and its upper-tail
    conditional mean:
    `standardGaussian_toMeasure_Ico_threshold_normalUpperTailMean_pos`.
- `EconCSLib.Foundations.Probability.BivariateGaussian`
  - independent two-coordinate Gaussian product scaffolding and canonical
    variance scaling:
    `gaussianVarianceFromStd`, `canonicalHalfVarianceScale`,
    `gaussianReal_map_canonicalHalfVarianceScale`,
    `independentGaussianPairMeasureWithStd`,
    `independentGaussianPairMeasureHalf`,
    `pairStrictWinnerBelowEvent`, `pairStrictBothBelowEvent`, and
    `independentGaussianStrictConditionalWinnerRatioWithStd_eq_scaled`.
- `EconCSLib.Foundations.Probability.RandomUtility`
  - paper-neutral additive RUM primitives:
    `StrictlyWellOrderedNoise`, `WeaklyWellOrderedNoise`,
    `gaussianNoiseKernel`, `laplacianNoiseKernel`,
    `rumContractScore`, `rumContractScore_preserves_weak_order`,
    `rumContractScore_preserves_strict_order`,
    `rum3_contract_top_first_of_original_top_first`,
    `rum3_contract_bottom_first_imp_original_bottom_first`,
    `rum3_contract_bottom_first_imp_original_bottom_first_strict_of_t_lt_one`,
    `rum3_swap_middle_transition_geometry`,
    `rum3_swap_middle_source_score_lt`, and the `swap12`/`swap23`
    density-product comparison lemmas.
- `EconCSLib.Foundations.Probability.RandomUtilityDensity`
  - finite-atom and continuous `withDensity` wrappers for three-alternative
    additive RUM score-density laws:
    `rum3ScoreDensityENN`, score-density measurability/positivity/
    normalization helpers, finite `rum3_swap12`/`rum3_swap23` mass comparison
    formulas, and continuous `rum3_withDensity_swap12`/`swap23` weak/strict
    measure comparison formulas.
- `EconCSLib.Foundations.Probability.RenewalReward` and
  `ContinuousReward`
  - accepted-set reward/time add-remove algebra and renewal-rate marginal
    comparison lemmas:
    `acceptedSetReward_union`, `acceptedSetTime_union`,
    `acceptedSetReward_diff`, `acceptedSetTime_diff`,
    `acceptedSetReward_eq_zero_of_measure_zero`,
    `acceptedSetTime_eq_zero_of_measure_zero`,
    `continuousSetRenewalRewardRate_le_union_of_le_average`,
    `continuousSetRenewalRewardRate_le_diff_of_average_le`,
    `continuousSetRenewalRewardRate_lt_union_of_lt_average`,
    `continuousSetRenewalRewardRate_lt_diff_of_average_lt`,
    `continuousSetRenewalRewardRate_diff_eq_self_of_zero_component`,
    and `continuousSetRenewalRewardRate_union_eq_self_of_zero_component`.
- `EconCSLib.SocialChoice.Ranking.Probability`
  - ranking-law probability bridges:
    the discrete measurable-space instance for `Ranking n`,
    `firstChoiceProb`, `rankingPMFOfMeasure`,
    `rankingPMFOfMeasure_eventProb`,
    `bestRemainingAfterProb_rankingPMFOfMeasure`, and
    `firstChoiceProb_rankingPMFOfMeasure`.
- `EconCSLib.SocialChoice.Ranking.Payoff`
  - finite ranking-law payoff algebra:
    `firstChoiceMissProb`, `valueGap`, `expectedFirstMoverUtility`,
    `expectedSecondMoverShared`, `secondMoverUtility`,
    `expectedSecondMoverIndependent`, `expectedWelfareOrdered`,
    `rerankingGainOnPair`, `expectedRerankingGain`,
    `secondMoverFirstLawSwitchGain`, first-choice probability bounds/sum-to-one,
    miss-probability complement and positivity lemmas,
    `firstChoiceGapMass`, `firstChoiceCollisionDiff`,
    `sum_firstChoiceGapMass_eq_expectedGap`,
    `expectedFirstMoverUtility_eq_sum_firstChoiceProb`,
    `expectedSecondMoverShared_eq_sum_secondChoiceProb`,
    `innerRerankingGain_eq_missProb_mul_gap`,
    `expectedRerankingGain_eq_expect_missProb_mul_gap`,
    `expectedRerankingGain_eq_sum_firstChoiceMissProb_mul_firstChoiceGapMass`,
    `expectedFirstMover_sub_secondMoverIndependent_eq_sum_firstChoiceProb_mul_firstChoiceGapMass`,
    `expectedCollisionLossDiff_eq_sum_collisionDiff_mul_firstChoiceGapMass`,
    `secondMoverFirstLawSwitchGain_eq_expected_collision_loss_diff`, and
    `expectedSecondMoverIndependent_le_of_collisionProb_le_and_gap_nonneg`.
- `EconCSLib.Foundations.Math.FiniteSum`
  - ordered-pair regrouping and MLR-weighted averages:
    `pair_sum_eq_ordered_swap_sum_of_injective_key`,
    `pair_sum_eq_ordered_swap_sum`,
    `weighted_average_cross_nonneg_of_pairwise`, and
    `weighted_average_cross_pos_of_pairwise`.
- `EconCSLib.Applications.RecommenderSystems.Allocation`
  - finite count-allocation helpers, including
    `Allocation.exists_count_gt_of_card_mul_lt_total` and
    `Allocation.count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded`,
    `Allocation.count_abs_sub_uniform_average_le_C_of_pairwise_bounded`, and
    `Allocation.count_abs_sub_uniform_average_le_one_of_pairwise_balanced`,
    covering finite count pigeonhole facts, the generic bridge from pairwise
    bounded scaled counts to weighted target count closeness, and uniform
    average closeness from pairwise raw-count balance;
  - `Allocation.FeasibleCode` and `Allocation.exists_isOptimalAtTotal`, the
    generic finite-search witness for fixed-total count-allocation objectives;
  - one-unit exchange and finite FOC lemmas for weighted separable count
    objectives: `Allocation.weightedForwardMarginal`,
    `Allocation.weightedBackwardMarginal`, `Allocation.ExchangeCondition`,
    `Allocation.IsOptimalAtTotal`, `Allocation.total_moveOne_eq`,
    `Allocation.objective_moveOne_eq`,
    `Allocation.objective_le_objective_moveOne_of_exchangeCondition`,
    `Allocation.objective_moveOne_le_of_isOptimalAtTotal`,
    `Allocation.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum`,
    and the diminishing-returns marginal monotonicity lemmas;
  - scaled-count asymptotic bridges:
    `Allocation.pairwise_scaled_abs_le_of_total_lt`,
    `Allocation.pairwise_scaled_abs_le_of_large_gap_backward_lt_forward`,
    `Allocation.share_abs_sub_weighted_target_le_scaled_weight_of_pairwise_scaled_bounded`,
    `Allocation.share_abs_sub_weighted_target_le_total_weight_of_pairwise_scaled_bounded`,
    and
    `Allocation.share_abs_sub_weighted_target_le_error_total_weight_of_pairwise_scaled`.
- `EconCSLib.Applications.RecommenderSystems.AllocationSequence`
  - target-profile and optimum-sequence scaffolding:
    `Allocation.HasApproxShare`, `Allocation.Sequence`,
    `Allocation.Sequence.ConvergesToProfile`,
    `Allocation.Sequence.convergesToProfile_of_eventual_approx`,
    `Allocation.AsymptoticProfileTarget`, `Allocation.AsymptoticProfile`,
    `Allocation.OptimalSequence`, and
    `Allocation.OptimalSequence.convergesToProfile_of_asymptoticProfile`;
  - reusable profile-convergence endpoints from scaled-count control:
    `Allocation.asymptoticProfile_of_pairwise_scaled_sublinear` and
    `Allocation.asymptoticProfile_of_large_gap_backward_lt_forward`, plus the
    floor-aware/eventual variant
    `Allocation.asymptoticProfile_of_eventual_large_gap_backward_lt_forward`;
  - certificate packages for those same endpoints:
    `Allocation.PairwiseScaledSublinearProfileCertificate`,
    `Allocation.PairwiseScaledSublinearFOCCertificate`, and
    `Allocation.PairwiseScaledEventualSublinearFOCCertificate`, with
    `.toPairwiseScaledSublinearProfileCertificate`,
    `.toPairwiseScaledSublinearFOCCertificate`, and `.asymptoticProfile`
    methods.
- `EconCSLib.SocialChoice.Ranking.Basic`
  - finite ranking primitives for at least two candidates:
    `Candidate`, `Ranking`, `firstChoice`, `secondChoice`, `rankOf`,
    `swapTopTwo`, `bestRemainingAfter`, and top-two/rank simplification
    lemmas.
- `EconCSLib.SocialChoice.Ranking.Kendall`
  - inversion finsets, Kendall tau distance, first/second-choice deletion
    formulas, `cycleRange`/`cycleIcc` relabeling bridges, center-transposition
    invariance, and center-order predicates/value-gap consequences.
- `EconCSLib.SocialChoice.Ranking.Mallows`
  - reusable finite Mallows law/weight primitives: `mallowsWeight`,
    `mallowsPartition`, ranking-law `firstChoiceProb`, `MallowsSpec`,
    first/first-second/pair-correct/pair-wrong weights and probabilities, and
    finite partition/probability normalization identities.
- `EconCSLib.SocialChoice.Ranking.MallowsRankFactorization`
  - assumption-driven finite Mallows rank-factorization algebra:
    `MallowsSpec.RankFactorization`,
    `MallowsSpec.firstTail_eq_firstSecondTail_mul_removalPowerSum`,
    `MallowsSpec.firstWeightPrefix`, and
    `MallowsSpec.firstWeightPrefix_eq_rankPrefixPowerSum_mul`.  Concrete
    constructors from identity-center fiber decompositions remain paper-local
    until the source-specific fiber proofs are reusable.
- `EconCSLib.SocialChoice.Ranking.MallowsSequential`
  - Mallows best-in-feasible-set fiber weights and expected-payoff bridges:
    `MallowsSpec.bestInSetWeight`,
    `MallowsSpec.expectedBestInSet_pair_eq_pairCorrectProb`,
    `MallowsSpec.bestInSetWeight_pair_eq_pairCorrectWeight`,
    `MallowsSpec.bestInSetWeight_pair_eq_pairWrongWeight`,
    `MallowsSpec.bestInSetWeight_eq_sum_swapCandidatePositions`,
    `MallowsSpec.bestInSetWeight_cross_nonneg_of_swap_pairwise_cross`,
    `MallowsSpec.sum_bestInSetWeight_eq_partition`,
    `MallowsSpec.expectedBestInSet_eq_sum_bestInSetWeight_div_partition`, and
    `expectedBestInSet_le_of_bestInSetWeight_cross`.
- `EconCSLib.SocialChoice.Ranking.RankPower`
  - finite geometric rank-power algebra for Mallows rank-factorization and
    removal-renormalization proofs:
    `candidateRankPowerSum`, `candidateRankReversePowerSum`,
    `candidateRankPrefixPowerSum`, `candidateRankRemovalPowerSum`,
    `candidateRankBestAfterRemovalWeight`,
    `candidateRankRemovalPowerSum_pos`,
    `candidateRankRemovalPowerSum_eq_range`,
    `candidateRankRemovalPowerSum_mul_one_sub`,
    `candidateRankBestAfterRemovalWeight_of_lt`,
    `candidateRankBestAfterRemovalWeight_of_gt`,
    `candidateRankPowerSum_pos`,
    `candidateRankPowerSum_strict_mono`,
    `natPower_mul_lt_mul_natPower`,
    `candidateRankPowerSum_mul_one_sub`,
    `candidateRankPowerSum_inner_nonneg`, and
    `candidateRankPowerSum_inner_pos_zero_one`.
- `EconCSLib.SocialChoice.Ranking.Score`
  - pure three-score ranking API for KR-style RUM bridges:
    `rum3RankByScores`, `rum3RankByScoreFns`, six concrete three-candidate
    rankings, first/second-choice simplification, best-remaining-after-one
    simplification, no-tie predicates, and score-order consequences from
    first-choice or best-remaining outcomes.
- `EconCSLib.SocialChoice.Ranking.Sequential`
  - probability-free sequential-choice ranking helpers:
    `bestInSet`, `bestInSet_eq_of_forall_rank_le`, `bestInSet_mem`,
    `rankOf_bestInSet_le`, `bestInSet_univ`,
    `bestInSet_univ_sdiff_singleton`, `bestInSet_singleton`,
    `bestInSet_pair_eq_if_rank_lt`, `bestInSet_trans_center_symm`,
    `swapCandidatePositions`, rank simplification for candidate-position
    swaps, `swapCandidatePositionsEquiv`, `ranking_ext_of_rankOf`,
    `apply_eq_of_rankOf`, `eq_of_rankOf_eq`, and deterministic
    `bestInSet_value_le_swapCandidatePositions`,
    `bestInSet_value_le_adjacent_swapCandidatePositions`,
    `AdjacentSwapImproves`, `AdjacentCorrection`, `WeakBruhatLe`,
    `adjacentSwapImproves_bestInSet_value`, `SwapImprovesOn`,
    `swapImprovesOn_bestInSet_value`, `deleteFirstChoicePrefixCut`,
    `succAbove_val_lt_deleteFirstChoicePrefixCut_iff`,
    `bestInSetPrefixCutIndicator`,
    `bestInSetPrefixCutIndicator_nonneg`,
    `bestInSetPrefixCutIndicator_le_one`,
    `bestInSetPrefixCutIndicator_eq_of_adjacent_cut_not_mem`,
    `centerPrefixCutValue`, `weaklyOrderedBy_centerPrefixCutValue`,
    `bestInSetPrefixCutIndicator_eq_centerPrefixCutValue`, and
    `adjacentSwapImproves_bestInSetPrefixCutIndicator`.
- `EconCSLib.SocialChoice.Ranking.SequentialPayoff`
  - finite ranking-law expected best-feasible-candidate utilities:
    `expectedBestInSet`, `expectedBestAfterRemoval`,
    `expectedBestInSet_univ`, `expectedBestInSet_univ_sdiff_singleton`, and
    `expectedBestInSet_singleton`.

## Paper Cleanup Recipes

### GN21 Driver Surge Pricing

Current cleanup already done in `papers/GN21DriverSurgePricing/MainTheorems.lean`:
the interval/a.e. wrappers now delegate to `MeasureInequalities`, and the
single-state payment/time/reward-rate wrappers delegate to
`ContinuousReward`/`RenewalReward`.

How to call the shared lemmas:

- For local wrappers named like `singleStateTripPayment_union`,
  `singleStateTripTime_diff`, or zero-measure variants, unfold only the GN
  aliases and `simpa [singleStateTripPayment, singleStateTripTime,
  acceptedSetReward, acceptedSetTime]` using the corresponding
  `acceptedSet*` lemma.
- For Theorem 1 add/remove marginal steps, use
  `continuousSetRenewalRewardRate_le_union_of_le_average`,
  `continuousSetRenewalRewardRate_le_diff_of_average_le`,
  `continuousSetRenewalRewardRate_lt_union_of_lt_average`, or
  `continuousSetRenewalRewardRate_lt_diff_of_average_lt`, with
  `simpa [singleStateRenewalReward, singleStateAverageTripRate,
  continuousSetRenewalRewardRate, acceptedSetAverageRewardRate]`.
- For boundary or measure-zero components, first prove the component payment
  and time are zero, then call
  `continuousSetRenewalRewardRate_diff_eq_self_of_zero_component` or
  `continuousSetRenewalRewardRate_union_eq_self_of_zero_component`.

Future cleanup:

- Replace any remaining local "same except at a boundary point" set equality
  proofs with `measure_symmDiff_Ioo_union_Ioo_touching_eq_zero`,
  `measure_symmDiff_Ioo_union_Ioi_touching_eq_zero`, or their a.e. wrappers.
- Move positive-denominator reward-rate transfer and partial-defined-reward
  wrappers into a CTMC/renewal reward layer once a second paper needs the same
  denominator-valid interface.
- Keep paper theorem wrappers source-shaped: GN-specific policies, CTMC states,
  and theorem numbers stay in `papers/GN21DriverSurgePricing`.

### GLM20 Dropping Standardized Testing

Current reusable entry points:

- `ChoiceEquilibriumAE` and `BinaryChoiceAE` for off-null best-response and
  null-tie threshold identification.
- `GaussianHazardCertificate.normalUpperTailMean_gt_threshold` and
  `standardGaussian_normalUpperTailMean_gt_threshold` for upper-tail
  conditional means above positive thresholds.
- `StandardGaussianCDFAPI`, `StandardGaussianQuantileAPI`,
  `GaussianHazardInverseCertificate`, and finite-mixture tail/capacity
  certificates for admissions cutoffs.
- `existsUnique_eq_and_upper_region_of_continuous_strictAnti_tendsto_atBot_atTop`
  for the scalar school-capacity cutoff plus upper-region characterization.

Cleanup target:

- In GLM proof files, keep row/table identification data paper-local, but route
  all a.e. threshold-policy conclusions through `BinaryChoiceAE` constructors.
- Replace local Mills-ratio or truncated-normal "mean above cutoff" arguments
  with `GaussianHazardCertificate.normalUpperTailMean_gt_threshold`.
- When a theorem still assumes continuity of a capacity-clearing cutoff family,
  first try deriving it from the capacity equation, finite Gaussian mixture
  continuity, and strict antitonicity of the cutoff.
- For Lemma 3 or Proposition 2 selection thresholds, keep the GLM theorem name
  paper-facing but prove it by direct `exact
  existsUnique_eq_and_upper_region_of_continuous_strictAnti_tendsto_atBot_atTop
  hcont hanti hatBot hatTop hcapacity`.  Concrete Gaussian-mixture variants
  should call
  `existsUnique_mixtureTailMass_eq_and_region_of_capacity_mem_Ioo`, which now
  delegates to the same shared threshold theorem.

### LG21 Test-Optional Policies

Current reusable entry points:

- Same Gaussian CDF/quantile/hazard layer as GLM.
- `FiniteMixture` event-share and positive-share cancellation wrappers.
- `Admissions` wrappers around finite posterior expectations.
- `ConvexCombination.twoPointWeightedAverage` and its component/gap/
  continuity lemmas for optional no-report pooled estimates.
- `MeasureInequalities.ae_imp_le_contradicts_positive_selected_lt_mass` and
  `positive_selected_lt_mass_of_positive_lower_lt_mass` for a.e. equilibrium
  contradictions over positive-mass below-reference intervals.

Cleanup target:

- For no-report pooled estimates such as
  `lg21OptionalNoReportMixtureEstimate`, define paper notation locally but
  prove comparisons via `lt_twoPointWeightedAverage_of_lt_components`,
  `twoPointWeightedAverage_lt_of_components_lt`,
  `lt_twoPointWeightedAverage_of_weighted_gap_pos`, and
  `twoPointWeightedAverage_lt_of_weighted_gap_neg` after setting
  `w0 = 1 - accessFraction` and `w1 = accessFraction * normalCDF ...`.
- For continuity of those pooled estimates, use
  `continuous_twoPointWeightedAverage`; the only paper-specific side condition
  is the positive denominator from `1 - C + C * F(c)`.
- For a.e. source-equilibrium contradictions, first derive the a.e. implication
  (`selected info -> actorMean <= value`) from `BinaryChoiceAE` or the
  paper's equilibrium projection, then call
  `ae_imp_le_contradicts_positive_selected_lt_mass`.  If the source gives a
  cutoff interval rather than selected points directly, use
  `positive_selected_lt_mass_of_positive_lower_lt_mass` to transfer positive
  mass through the cutoff rule.
- Move any LG-local finite-mixture event-share algebra into wrappers around
  `EconCSLib.Foundations.Probability.FiniteMixture`.
- Use `GaussianHazardCertificate.normalUpperTailMean_gt_threshold` for
  admitted-mean lower comparisons and `mixtureUpperTailMean_mul_tailMass_eq_numerator`
  for finite group mixtures.
- When an instability proof needs positive Gaussian mass on
  `[threshold, upperTailMean)`, use
  `standardGaussian_toMeasure_Ico_threshold_normalUpperTailMean_pos` instead
  of separately proving the upper-tail mean is above the threshold and then
  calling `GaussianScaleLaw.toMeasure_Ico_pos`.
- Keep policy-specific "test optional", "test blind", and source notation in
  LG files; move only Gaussian/mixture math.

### PRPKG24 Accuracy Diversity

Current cleanup already done:

- `TopKOracle.lean` keeps paper names but delegates bottom-indexed mean bridges
  to `OrderStatistics`.
- `FiniteDiscreteOrderStats.lean` keeps paper names but delegates finite-PMF
  indicator estimates to `FiniteExpectation`.
- `Bounded.lean` keeps paper names but delegates fixed finite-sum asymptotic
  assembly to `EconCSLib.Math`.
- `Representation.lean` keeps the paper-facing
  `GammaHomogeneityProfile.count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded`
  name but delegates the generic scaled-count averaging proof to
  `EconCSLib.Allocation.count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded`.
- `Representation.lean` and `TailHomogeneity.lean` keep their paper-facing
  `exists_count_gt_of_card_mul_lt_total` names but delegate the finite
  count-pigeonhole proof to
  `EconCSLib.Allocation.exists_count_gt_of_card_mul_lt_total`.
- `Representation.lean` keeps paper-facing uniform-average lemmas but delegates
  raw pairwise count balance to
  `EconCSLib.Allocation.count_abs_sub_uniform_average_le_C_of_pairwise_bounded`
  and
  `EconCSLib.Allocation.count_abs_sub_uniform_average_le_one_of_pairwise_balanced`.
- `Optimization.lean` keeps `ConsumptionModel.exists_isOptimalAtTotal` as a
  paper-facing name but delegates fixed-total finite search to
  `EconCSLib.Allocation.exists_isOptimalAtTotal`.
- `Exchange.lean` keeps the paper-facing weighted marginal, one-step exchange,
  and FOC names but delegates the generic total-preservation, objective
  accounting, no-profitable-exchange, FOC, and diminishing-returns monotonicity
  proofs to `EconCSLib.Applications.RecommenderSystems.Allocation`.
- `SeparableAsymptotic.lean` keeps paper-facing asymptotic certificate names,
  but its finite-prefix error schedule wrapper delegates to
  `EconCSLib.Math.tendsToZero_if_lt_const`, and its sublinear FOC certificate
  delegates the "large scaled gap contradicts finite FOC" step to
  `EconCSLib.Allocation.pairwise_scaled_abs_le_of_large_gap_backward_lt_forward`.
  Its pairwise sublinear homogeneity certificate now delegates the generic
  target-profile conclusion to
  `EconCSLib.Allocation.asymptoticProfile_of_pairwise_scaled_sublinear`.
  Its floor-aware/eventual sublinear FOC endpoint delegates the finite-prefix
  and count-floor packaging to
  `EconCSLib.Allocation.asymptoticProfile_of_eventual_large_gap_backward_lt_forward`.
- `TailHomogeneity.lean` keeps Theorem 3's Bernoulli log-share wrapper but
  delegates the finite-prefix scaled-count bound to
  `EconCSLib.Allocation.pairwise_scaled_abs_le_of_total_lt`.

Next reusable extraction:

- Keep PRPKG's compatibility conversion definitions paper-facing, but route
  them through shared allocation certificates via `.toShared`:
  `PairwiseScaledSublinearHomogeneityCertificate`,
  `PairwiseScaledSublinearFOCCertificate`, and
  `PairwiseScaledEventualSublinearFOCCertificate` now adapt to the generic
  `Allocation.PairwiseScaled*Certificate` layer, and the top-k uniform
  eventual FOC wrapper delegates through the pairwise-scaled eventual
  certificate. New source-facing endpoints should follow that pattern instead
  of reconstructing finite-prefix absorption locally.
- Keep distribution-family tail asymptotics in probability/math modules:
  bounded-support reflected CDF, Pareto, exponential, and Bernoulli product
  kernels should produce common `TopKScaledMarginalLimitCertificate` inputs.
- Do not rebuild bottom-indexed `mu(rank, sampleSize)` bridges; use
  `expectedOrderStatisticMeanSeq` and its top-k/endpoint-loss theorems.

### KR21 Monoculture

Current cleanup already done:

- `MallowsSpec.pair_sum_eq_ordered_swap_sum` now delegates to
  `FiniteSum.pair_sum_eq_ordered_swap_sum_of_injective_key`.
- `candidateWeightedAverage_cross_nonneg_of_pairwise` and
  `candidateWeightedAverage_cross_pos_of_pairwise` now delegate to
  `FiniteSum.weighted_average_cross_nonneg_of_pairwise` and
  `FiniteSum.weighted_average_cross_pos_of_pairwise`.
- `EconCSLib/SocialChoice/Ranking/Basic.lean` now owns `Ranking`,
  `firstChoice`, `secondChoice`, `rankOf`, `swapTopTwo`,
  `bestRemainingAfter`, and the top-two simp/rank lemmas. The old
  `KR21Monoculture/Basic.lean` is a compatibility layer preserving paper names.
- `EconCSLib/SocialChoice/Ranking/Kendall.lean` now owns inversion finsets,
  Kendall tau, deletion/relabeling formulas, and center-order predicates. The
  old `KR21Monoculture/Kendall.lean` is a compatibility layer preserving paper
  names and the KR-specific `valueGap` wrappers.
- `EconCSLib/SocialChoice/Ranking/Mallows.lean` now owns the reusable finite
  Mallows law/weight layer. The KR file still keeps its local `MallowsSpec`
  structure stable for downstream field-rewrite scripts and owns the
  paper-specific `MallowsComparison` certificate layer.
- `KR21Monoculture/RUM.lean` keeps the Appendix C theorem names for
  arbitrary-`σ` Gaussian scaling, but the variance encoding, canonical
  variance-`1/2` scale, coordinatewise product-law scaling, strict winner/
  below-cutoff events, and strict conditional-ratio scaling now delegate to
  `EconCSLib.Foundations.Probability.BivariateGaussian`.
- `KR21Monoculture/RUM.lean` also keeps the paper-facing additive-noise and
  contraction-geometry names, but the well-ordering predicates, Gaussian/
  Laplacian kernels, scalar contraction order lemmas, three-alternative
  top/bottom preservation, swap-middle geometry, and pointwise density-product
  comparisons now delegate to `EconCSLib.Foundations.Probability.RandomUtility`.
- `KR21Monoculture/RUM.lean` keeps paper-facing score-density and swap-mass
  theorem names, but the three-coordinate score density, finite atom
  density-swap comparisons, and continuous `withDensity` swap comparisons now
  delegate to `EconCSLib.Foundations.Probability.RandomUtilityDensity`.
- `KR21Monoculture/RUM.lean` keeps its concrete three-score ranking names, but
  the score-order predicates, concrete rankings, `rum3RankByScores`,
  `rum3RankByScoreFns`, first/second-choice simp lemmas, best-remaining-after
  simp lemmas, and score-order implication lemmas now delegate to
  `EconCSLib.SocialChoice.Ranking.Score`.
- `KR21Monoculture/RUM.lean` keeps `rumRankingPMFOfMeasure` and the theorem-6
  lambda/first-choice measure-form wrappers, but the generic ranking
  pushforward PMF and event-probability bridge now delegate to
  `EconCSLib.SocialChoice.Ranking.Probability`.
- `KR21Monoculture/Sequential.lean` keeps proof-friendly raw definitions for
  `bestInSet` and `swapCandidatePositions` because later KR proofs unfold
  them, but its generic best-in-set, relabeling, candidate-position swap, rank
  extensionality, deterministic swap-improvement, adjacent-order monotonicity,
  bounded prefix-cut indicator/value API, expected best-in-set, and Mallows
  best-in-set fiber lemmas delegate to
  `EconCSLib.SocialChoice.Ranking.Sequential`,
  `EconCSLib.SocialChoice.Ranking.SequentialPayoff`, and
  `EconCSLib.SocialChoice.Ranking.MallowsSequential`.
- `KR21Monoculture/Mallows.lean` now has a stable `MallowsSpec.toShared`
  adapter into `EconCSLib.SocialChoice.Ranking.MallowsSpec`; the initial
  Mallows normalization, partition, and first/first-second/pair weight lemmas
  call the shared layer while preserving KR-local field names.
- `KR21Monoculture/MallowsPairwise.lean` keeps the paper-facing rank-power
  names, but the generic finite geometric rank sums, removal-renormalized
  rank sums, best-after-removal rank weights, and their positivity/closed-form
  lemmas delegate to `EconCSLib.SocialChoice.Ranking.RankPower`; it also keeps
  the paper-facing `RankFactorization` structure stable while its portable
  first-tail and prefix-weight algebra delegates through
  `RankFactorization.toShared` to
  `EconCSLib.SocialChoice.Ranking.MallowsRankFactorization`.
- `KR21Monoculture/Expectation.lean`, `RerankingGain.lean`,
  `FirstChoice.lean`, `WeakCompetition.lean`, and
  `FirstChoiceDecomposition.lean` keep paper-facing names for first/second
  mover utility, Equation (3), reranking gains, and weaker competition, but
  the generic probability, miss-probability, value-gap, candidate-fiber,
  collision-loss, pair-lifted, and first-mover-law switch identities delegate
  to `EconCSLib.SocialChoice.Ranking.Payoff`.

Next reusable extraction:

- Keep KR's recursive identity-center prefix-cut proof stack paper-local until
  a second paper needs the same recursive Mallows subset marginal machinery.
- Keep KR-specific "monoculture paradox", theorem numbers, and
  first-choice-weighted arbitrary-size proof targets in the paper folder until
  the ranking library has stable names.

### GHW01 Digital Goods

This is less continuous, but it shares finite ordered-sum infrastructure.

- Keep using `EconCSLib.Foundations.Math.FiniteSum` for telescoping revenue
  and monotone increment arguments.
- If future GHW cleanup finds sorted-bid pair or adjacent-rank regrouping
  proofs, prefer `pair_sum_eq_ordered_swap_sum` or
  `pair_sum_eq_ordered_swap_sum_of_injective_key` before adding auction-local
  ordered-pair algebra.

## General Library Modules To Build

### Probability And Stochastic Processes

- `Probability.Kernels`: standard finite and measurable Markov-kernel
  wrappers, joint/marginal laws, pushforward law congruence, conditioning on
  positive-probability events, and finite/standard-Borel law-of-total
  probability.
- `Probability.EmpiricalProcess`: empirical counts, empirical means, LLN/SLLN
  wrappers, multinomial counts, finite union bounds, and event-rate
  convergence for finite outcome spaces.
- `Probability.LargeDeviations.Analytic`: Cramer/Sanov/Chernoff wrappers that
  instantiate the existing `ExponentialRateCertificate` interface from
  concrete finite PMFs, moment generating functions, KL divergences, or
  pairwise error exponents.
- `Probability.StochasticProcesses`: reusable Markov-chain, CTMC, renewal,
  regenerative-cycle, hitting-time, and occupation-measure facts. GN-style
  reward-rate proofs and rating/recommender dynamics should share this layer.

### Ranking, Voting, And Social Choice

- `SocialChoice.Ranking.Basic`, `Kendall`, and `Mallows` as described for KR.
- `SocialChoice.Ranking.Partial`: top-k sets, ordered top-k partial rankings,
  projection from full rankings, positional scoring rules, K-approval, and
  score-vector algebra.
- `SocialChoice.ElectionLearning`: finite candidate outcomes, winner/top-set
  recovery events, positional-scoring empirical sums, pairwise score-margin
  deviations, and large-deviation learning-rate certificates.
- `SocialChoice.Ranking.Probability` and future RUM-ranking extensions:
  ranking-law pushforward PMFs are now in `Ranking.Probability`; still useful
  future work includes no-tie a.e. ranking maps, product-measure/Fubini bridges
  for pairwise score comparisons, and reusable Gaussian/Laplacian/noise-kernel
  instantiations.

### Continuous Analysis

- `Foundations.Analysis.IntegralAsymptotics`: split-integral certificates,
  change-of-variables wrappers, local dominated-convergence interfaces,
  tail-negligibility certificates, and finite-sum assembly over integral
  asymptotics.
- `Foundations.Analysis.ParameterizedIntegrals`: differentiation under the
  integral, continuity under an integral sign, monotone convergence wrappers,
  and quotient derivative positivity for conditional expectation ratios.
- `Foundations.Analysis.ImplicitThresholds`: existence/uniqueness/continuity of
  thresholds defined by monotone continuous capacity equations, including
  inverse-CDF and inverse-hazard wrappers.
- `Foundations.Analysis.ConvexOptimization`: finite-dimensional convexity,
  first-order conditions, KKT-like certificates for simplex/box constraints,
  envelope-style derivative signs, and uniqueness from strict convexity.
- `Foundations.Analysis.RealInequalities`: reusable scalar inequalities for
  `log`, `exp`, `rpow`, Mills ratios, gamma ratios, and polynomial/geometric
  tail bounds.

### Optimization And Design

- `Optimization.CountAllocation`: pairwise scaled-count bounds, weighted
  average/count-profile closeness, floor-aware FOC bridges, and exchange
  optimality for finite integer allocations.
- `Optimization.DesignSimplex`: finite mechanism/design randomization,
  simplex-valued designs, linear/convex objective certificates, and
  finite-search wrappers for candidate design sets.
- `Econometrics.RatingSystems`: finite rating labels, response-scale maps,
  score interpretations, informativeness objectives, finite mixture/latent
  quality models, and design optimization certificates.

## New Paper Families Motivating The Plan

### arXiv:1906.08160, Top-k Election Learning

The paper "Who is in Your Top Three? Optimizing Learning in Elections with Many
Candidates" studies K-approval and K-partial ranking mechanisms with positional
scoring rules, learning rates for recovering asymptotic outcomes, and
randomization between mechanisms.

Likely reusable requirements:

- finite ranking and top-k partial-ranking models;
- positional scoring-rule algebra and empirical score sums;
- finite outcome large-deviation rates for pairwise score margins;
- optimization over finite mechanisms and mixtures of mechanisms;
- links between score-vector separation and winner/top-set recovery events.

### arXiv:1810.13028, Rating-System Design

The paper "Designing Informative Rating Systems: Evidence from an Online Labor
Market" develops a model-based framework to choose rating labels and numeric
interpretations to improve convergence/informativeness.

Likely reusable requirements:

- finite rating-scale models and response-label maps;
- latent-quality finite mixtures or parametric response kernels;
- informativeness/convergence-rate objectives built from finite PMFs, KL-like
  distances, or exponential-rate certificates;
- finite and continuous design optimization over labels, scores, and
  randomized/parameterized designs;
- empirical-calibration wrappers separating data-specific estimation from the
  mathematical design theorem.

## Priority Order

1. Finish additive extraction cleanup already started:
   `FiniteSum`, `MeasureInequalities`, `OrderStatistics`, `FiniteExpectation`,
   `Asymptotics`, `Gaussian`, and `BinaryChoiceAE` should stay green under
   targeted builds.
2. Continue the ranking core from KR21:
   `Ranking.Basic`, `Ranking.Kendall`, and the base `Ranking.Mallows`
   law/weight layer are extracted; next thin KR's local Mallows wrappers with a
   local-to-shared adapter and then move rank-factorization/fiber weights.
3. Build the continuous-analysis layer for parameterized integrals and
   threshold equations, because it supports GLM, LG, GN, KR RUM, and future
   election/rating learning-rate papers.
4. Move PRPKG count-allocation and pairwise-scaled-count bridges into an
   application/optimization module.
5. Instantiate more analytic large-deviation certificates for finite scoring
   and rating-scale papers.

## Publication Gate Before New Deep Library Work

Before starting a new deep library-development campaign beyond the existing
paper-extraction plan, complete a full repository publication pass:

- finish the active extractions from GN21, GLM20, LG21, KR21, PRPKG24, and any
  remaining GHW01 cleanup already in scope;
- run the paper post-audit workflows and targeted paper builds for every paper
  whose proof surface or library dependencies changed;
- refresh each affected paper's status metadata and generated status outputs;
- update human-facing docs, including module descriptions, line/library-size
  counts, roadmap tables, and any "what the library contains" summaries;
- run final hygiene checks (`lake build` targets, `git diff --check`, and
  no-new-`sorry`/`admit` scans over touched files);
- make one coherent commit with explicit staged paths; and
- push the branch and open or update the pull request into the public
  EconCSLib repository.

This gate is intentionally before new broad modules such as Markov-chain,
large-deviation, or parameterized-integral infrastructure. Those modules should
start only after the existing paper extractions have a clean audit trail and a
public PR surface.
