# Driver Surge Pricing Verification Notes

This is a lightweight handoff document for source-to-Lean mapping.

- Namespace: `GN21DriverSurgePricing`
- Official URL: https://pubsonline.informs.org/doi/10.1287/mnsc.2021.4058
- Source PDF: `source.pdf`
- Source text cache: `source.txt`

## Verification checklist

- [x] Full named-result inventory copied to the README theorem table.
- [x] DAG graph includes all required paper-stage nodes and dependencies.
- [x] README status and remaining-assumption notes match proof artifacts.
- [x] Final status review completed before publishing.

## Notes

- Date reviewed: 2026-05-05
- Last theorem row verified: Theorem 1 measured marginal add/remove steps,
  Proposition 3.1 measured affine reward step, Lemma 2 CTMC closed form,
  Lemma 1/Lemma 3 measured algebra support, Appendix D derivative-kernel
  algebra, measured Lemma 9/10 accept-all-to-current tightening including
  positive-measure and primitive-equality variants, named-primitive Remark 4
  positivity wrappers, Lemma 9/10 endpoint bridges, Theorem 4 paper-ordered
  shape-derivation routes, raw statewise improvement adapters, shape-level
  with-density bridges for all four Theorem 4 shape cases, the accept-all-bound
  wrappers for all four shape cases, the packaged source-facing
  statewise-improvement certificate for Theorem 4/Theorem 3, Theorem 3 CTMC
  structured price form, Theorem 4 shape-replacement to shape-derivation and
  statewise-improvement bridges, direct Lemma 9 primitive-feasibility bridge,
  ratio-to-IC endpoints, and accept-all-primitive statewise-certificate
  endpoint, accept-all-primitive positive-primitives strict-local and
  statewise-certificate endpoints, raw statewise-improvement positive-primitives
  route, replacement-data Theorem 3 positive-primitives route, all-optimal
  replacement-data Theorem 4/Theorem 3 routes, canonical Lemma 5 replacement
  constructors for all five shape cases, state-specific Theorem 4
  allowed-replacement constructors, source-facing all-optimal replacement case
  data, packaged allowed-replacement Theorem 4/Theorem 3 boundary routes, and
  the accept-all-primitive packaged allowed-replacement Theorem 3 route, the
  endpoint-bridge-to-allowed-replacement certificate conversion,
  canonical non-accept-all finite-interval shape witnesses,
  weak-reward IC source wrapper
  `paper_theorem3_measured_structured_ic_prices_of_weak_reward_source_assumptions`,
  measured aggregate weak-reward bridge
  `theorem3AcceptAllWeakRewardCertificate_of_measured_aggregate_weak_reward`,
  aggregate add-left/add-right weak monotonicity lemmas
  `gn21AggregateDynamicReward_le_add_left_of_kernel_nonneg` and
  `gn21AggregateDynamicReward_le_add_right_of_kernel_nonneg`,
  pointwise-to-integrated kernel bridge
  `gn21PrimitiveKernel_nonneg_of_pointwise_derivative_kernel_nonneg`,
  measured primitive union and aggregate add bridges
  `gn21MeasuredAggregateRewardPrimitives_le_union_left_of_kernel_nonneg`
  and
  `gn21MeasuredAggregateRewardPrimitives_le_union_right_of_kernel_nonneg`,
  measured pointwise-kernel add bridges
  `gn21MeasuredAggregateRewardPrimitives_le_union_left_of_pointwise_kernel_nonneg`
  and
  `gn21MeasuredAggregateRewardPrimitives_le_union_right_of_pointwise_kernel_nonneg`,
  accept-all-complement aggregate add specializations
  `gn21MeasuredAggregateRewardPrimitives_le_acceptAll_left_of_complement_kernel_nonneg`
  and
  `gn21MeasuredAggregateRewardPrimitives_le_acceptAll_right_of_complement_kernel_nonneg`,
  accept-all-complement pointwise-kernel specializations
  `gn21MeasuredAggregateRewardPrimitives_le_acceptAll_left_of_complement_pointwise_kernel_nonneg`
  and
  `gn21MeasuredAggregateRewardPrimitives_le_acceptAll_right_of_complement_pointwise_kernel_nonneg`,
  Lemma 9/10 measured pointwise kernel wrappers
  `paper_lemma9_measured_derivative_sign_kernel_pos_of_current_bounds`
  and
  `paper_lemma10_measured_derivative_sign_kernel_pos_of_current_bounds`,
  and direct Lemma 9/10 accept-all aggregate bridges
  `gn21MeasuredAggregateRewardPrimitives_le_acceptAll_left_of_lemma10_current_bounds`
  and
  `gn21MeasuredAggregateRewardPrimitives_le_acceptAll_right_of_lemma9_current_bounds`,
  aggregate denominator positivity helpers,
  structured-price integrability helper
  `integrableOn_ctmcStructuredSurgePrice`,
  structured current-bounds weak aggregate package
  `Theorem4MeasuredAggregateStructuredCurrentBoundsWeakCertificate`,
  its adapter
  `theorem4MeasuredAggregateWeakAcceptAllRewardCertificate_of_structured_current_bounds`,
  primitive current-bounds packages
  `GN21NonsurgeLemma10AcceptAllAggregatePrimitiveData` and
  `GN21SurgeLemma9AcceptAllAggregatePrimitiveData`,
  primitive structured current-bounds certificate
  `Theorem4MeasuredAggregateStructuredCurrentBoundsPrimitiveCertificate`,
  feasible-measurable dynamic IC interface
  `dynamicMeasurableIncentiveCompatible`,
  feasible primitive current-bounds certificate
  `Theorem4MeasuredAggregateStructuredCurrentBoundsFeasiblePrimitiveCertificate`,
  feasible measurable strict-local interface
  `Theorem4MeasurableStrictLocalImprovementCertificate`,
  feasible measured aggregate strict-local certificate
  `Theorem4MeasuredAggregateFeasibleStrictLocalImprovementCertificate`,
  feasible measured aggregate strict-local adapter
  `theorem4MeasurableStrictLocalImprovementCertificate_of_measured_aggregate_feasible_strict_improvements`,
  feasible measured aggregate strict-local Theorem 4 endpoint
  `paper_theorem4_measurable_accept_all_unique_optimal_of_measured_aggregate_feasible_strict_local_improvements`,
  source-data current-bounds packages
  `GN21NonsurgeLemma10AcceptAllAggregateSourceData` and
  `GN21SurgeLemma9AcceptAllAggregateSourceData`,
  accounting-form current-bounds packages
  `GN21NonsurgeLemma10AcceptAllAggregateAccountingData` and
  `GN21SurgeLemma9AcceptAllAggregateAccountingData`,
  reward-rate current-bounds packages
  `GN21NonsurgeLemma10AcceptAllAggregateRewardRateData` and
  `GN21SurgeLemma9AcceptAllAggregateRewardRateData`,
  source-facing feasible current-bounds certificate
  `Theorem4MeasuredAggregateStructuredCurrentBoundsSourceFeasibleCertificate`,
  accounting-form feasible current-bounds certificate
  `Theorem4MeasuredAggregateStructuredCurrentBoundsAccountingFeasibleCertificate`,
  reward-rate feasible current-bounds certificate
  `Theorem4MeasuredAggregateStructuredCurrentBoundsRewardRateFeasibleCertificate`,
  reward-rate to scaled-earning bridge
  `gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate`,
  Theorem 3 feasible strict-local boundary
  `theorem3AcceptAllFeasibleStrictLocalCertificate`,
  feasible strict-local source wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_feasible_strict_local_source_assumptions`,
  measurable shape derivation certificates
  `Theorem4MeasurableShapeDerivationCertificate` and
  `Theorem4AllMeasurableOptimalShapeReplacementDerivationCertificate`,
  feasible statewise improvement adapters
  `Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate`,
  `theorem4MeasuredAggregateFeasibleStrictLocalImprovementCertificate_of_measurable_shape_statewise_improvements`,
  Theorem 3 measurable-shape source adapter
  `theorem3AcceptAllFeasibleStrictLocalCertificate_of_measurable_shape_statewise_improvements`,
  and measurable-shape source wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_statewise_improvements_source_assumptions`,
  all-measurable replacement source constructor
  `Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate.of_all_measurable_shape_replacements`,
  replacement source assumption wrapper
  `Theorem3AcceptAllMeasurableShapeReplacementStatewiseImprovementSourceAssumptions`,
  replacement source theorem
  `paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_replacement_statewise_improvements_source_assumptions`,
  feasible current-bounds endpoint wrappers
  `paper_theorem4_nonsurge_feasible_statewise_strict_aggregate_improvement_of_lemma10_reject_long_withDensity_of_shape_current_bounds_data`,
  `paper_theorem4_nonsurge_feasible_statewise_strict_aggregate_improvement_of_lemma10_accept_middle_withDensity_of_shape_current_bounds_data`,
  `paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_tail_withDensity_of_shape_current_bounds_data`,
  `paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity_of_shape_current_bounds_data`,
  and
  `paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity_of_shape_current_bounds_data`,
  endpoint current-bounds data packages
  `GN21NonsurgeRejectLongCurrentBoundsEndpointData`,
  `GN21NonsurgeAcceptMiddleCurrentBoundsEndpointData`,
  `GN21SurgeRejectShortCurrentBoundsEndpointData`,
  `GN21SurgeRejectMiddleLoCurrentBoundsEndpointData`,
  `GN21SurgeRejectMiddleHiCurrentBoundsEndpointData`,
  and
  `GN21SurgeRejectMiddleCurrentBoundsEndpointData`,
  endpoint current-bounds selection certificate
  `Theorem4MeasurableEndpointCurrentBoundsSelectionCertificate`,
  selection-to-Theorem-4 adapters
  `Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate.of_endpoint_current_bounds_selection`,
  `theorem4MeasuredAggregateFeasibleStrictLocalImprovementCertificate_of_endpoint_current_bounds_selection`,
  and
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_selection`,
  Theorem 3 endpoint current-bounds source wrapper
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsSelectionSourceAssumptions`
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_selection_source_assumptions`,
  source-facing measurable replacement data
  `Theorem4NonsurgeMeasurableReplacementData` and
  `Theorem4SurgeMeasurableReplacementData`,
  allowed-replacement-to-measurable constructor
  `Theorem4AllMeasurableOptimalShapeReplacementDerivationCertificate.of_allowed_replacement_data`,
  source-facing endpoint current-bounds selection certificate
  `Theorem4MeasurableEndpointCurrentBoundsAllowedReplacementSelectionCertificate`,
  source-facing selection-to-Theorem-4 adapter
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_allowed_replacement_selection`,
  and Theorem 3 source-facing endpoint current-bounds wrapper
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsAllowedReplacementSourceAssumptions`
  plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_allowed_replacement_source_assumptions`,
  supported endpoint records
  `GN21NonsurgeRejectLongSupportedEndpointData`,
  `GN21NonsurgeAcceptMiddleSupportedEndpointData`,
  `GN21SurgeRejectShortSupportedEndpointData`,
  `GN21SurgeRejectMiddleLoSupportedEndpointData`,
  `GN21SurgeRejectMiddleHiSupportedEndpointData`,
  and `GN21SurgeRejectMiddleSupportedEndpointData`,
  supported endpoint selection certificate
  `Theorem4MeasurableEndpointCurrentBoundsSupportedSelectionCertificate`,
  supported selection-to-Theorem-4 adapter
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_supported_selection`,
  and Theorem 3 supported endpoint wrapper
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsSupportedSourceAssumptions`
  plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_supported_source_assumptions`,
  regular endpoint records
  `GN21NonsurgeRejectLongRegularEndpointData`,
  `GN21NonsurgeAcceptMiddleRegularEndpointData`,
  `GN21SurgeRejectShortRegularEndpointData`,
  `GN21SurgeRejectMiddleLoRegularEndpointData`,
  `GN21SurgeRejectMiddleHiRegularEndpointData`,
  and `GN21SurgeRejectMiddleRegularEndpointData`,
  all-optimal allowed policy-form certificate
  `Theorem4AllMeasurableAllowedPolicyFormsCertificate`,
  regular allowed-policy-form endpoint certificate
  `Theorem4MeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsCertificate`,
  regular allowed-policy-form selection-to-Theorem-4 adapter
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_allowed_policy_forms`,
  and Theorem 3 regular allowed-policy-form endpoint wrapper
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsSourceAssumptions`
  plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_allowed_policy_forms_source_assumptions`,
  older regular-shape endpoint derivation certificate
  `Theorem4MeasurableEndpointCurrentBoundsRegularShapeDerivationCertificate`,
  regular-shape selection-to-Theorem-4 adapter
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_shape_derivation`,
  and Theorem 3 regular-shape endpoint wrapper
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularShapeSourceAssumptions`
  plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_shape_source_assumptions`,
  older regular endpoint selection certificate
  `Theorem4MeasurableEndpointCurrentBoundsRegularSelectionCertificate`,
  regular selection-to-Theorem-4 adapter
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_selection`,
  and Theorem 3 regular endpoint wrapper
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularSourceAssumptions`
  plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_source_assumptions`,
  accept-all density support package
  `GN21WithDensityAcceptAllSupport`,
  support-derived endpoint constructors
  `GN21NonsurgeRejectLongCurrentBoundsEndpointData.of_acceptAll_support`,
  `GN21NonsurgeAcceptMiddleCurrentBoundsEndpointData.of_acceptAll_support`,
  `GN21SurgeRejectShortCurrentBoundsEndpointData.of_acceptAll_support`,
  `GN21SurgeRejectMiddleLoCurrentBoundsEndpointData.of_acceptAll_support`,
  and
  `GN21SurgeRejectMiddleHiCurrentBoundsEndpointData.of_acceptAll_support`,
  continuous-density endpoint calculus helpers
  `continuous_gn21SwitchProb`,
  `continuous_ctmcStructuredSurgePrice`,
  `continuousAt_mul_density_of_continuous`,
  `stronglyMeasurableAtFilter_mul_density_of_continuous`,
  and
  `intervalIntegrable_mul_density_of_continuous`,
  bundled product-calculus packages
  `GN21EndpointProductContinuityData` and
  `GN21FiniteEndpointProductCalculusData`,
  short/tail integrability packages
  `GN21PositiveIntervalProductIntegrabilityData` and
  `GN21TailProductIntegrabilityData`,
  shared regular endpoint source package
  `GN21RegularEndpointSharedSourceData` and the five
  `...RegularEndpointData.of_shared_source` constructors, the five
  `...RegularEndpointData.of_shared_source_and_acceptAll_tightening`
  constructors, and the four
  `GN21RegularEndpointSharedSourceData.*_current_mass_pos` shape lemmas,
  shared fixed-state positivity helpers
  `GN21RegularEndpointSharedSourceData.nonsurge_scaled_time_pos`,
  `GN21RegularEndpointSharedSourceData.surge_scaled_time_pos`,
  `GN21RegularEndpointSharedSourceData.nonsurge_exit_weight_pos`,
  `GN21RegularEndpointSharedSourceData.surge_exit_weight_pos`, and
  `GN21RegularEndpointSharedSourceData.surge_fixed_switch_term_pos_for_nonsurge_bounds`,
  fixed-state Lemma 10 transfer lemmas
  `lemma10StructuredBounds_of_fixed_state_expansion` and
  `lemma10StructuredBounds_of_acceptAll_fixed_state_measured_expansion`,
  and fixed-state Lemma 9 comparison/transfer lemmas
  `lemma9StructuredLowerFromGap_le_of_fixed_state_expansion`,
  `lemma9StructuredUpperFromExitWeight_le_of_fixed_state_expansion`, and
  `lemma9StructuredBounds_of_fixed_state_expansion`,
  direct source current-bounds constructors
  `GN21NonsurgeLemma10AcceptAllAggregateData.of_source` and
  `GN21SurgeLemma9AcceptAllAggregateData.of_source`, source current-bound
  tightening constructors
  `GN21NonsurgeLemma10AcceptAllAggregateSourceData.of_acceptAll_tightening` and
  `GN21SurgeLemma9AcceptAllAggregateSourceData.of_acceptAll_tightening`,
  named Theorem 3 parameter-data extractor
  `Theorem3AcceptAllStructuredParameterData.of_evidence`,
  plus endpoint constructors ending in
  `of_acceptAll_support_and_calculus` and
  `of_acceptAll_support_and_continuity`,
  feasible accept-all-bound endpoint wrappers for all four Theorem 4 shape
  cases
  `paper_theorem4_nonsurge_feasible_statewise_strict_aggregate_improvement_of_lemma10_reject_long_withDensity_of_shape_acceptAll_bounds`,
  `paper_theorem4_nonsurge_feasible_statewise_strict_aggregate_improvement_of_lemma10_accept_middle_withDensity_of_shape_acceptAll_bounds`,
  `paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_tail_withDensity_of_shape_acceptAll_bounds`,
  `paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity_of_shape_acceptAll_bounds`,
  and
  `paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity_of_shape_acceptAll_bounds`,
  and the Theorem 3 weak-boundary adapter
  `theorem3AcceptAllWeakRewardCertificate_of_structured_current_bounds`,
  source-facing current-bounds wrapper
  `paper_theorem3_measured_structured_ic_prices_of_structured_current_bounds_source_assumptions`,
  primitive source-facing current-bounds wrapper
  `paper_theorem3_measured_structured_ic_prices_of_structured_current_bounds_primitive_source_assumptions`,
  feasible primitive measurable-IC source wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_feasible_primitive_source_assumptions`,
  source-data feasible measurable-IC source wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_source_feasible_source_assumptions`,
  accounting-form feasible measurable-IC source wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_accounting_source_assumptions`,
  reward-rate feasible measurable-IC source wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_reward_rate_source_assumptions`,
  bundled source-assumption wrapper
  `paper_theorem3_measured_structured_ic_prices_of_source_assumptions`,
  positive-replacement source wrapper
  `paper_theorem3_measured_structured_ic_prices_of_positive_replacement_source_assumptions`,
  endpoint-bridge source wrapper
  `paper_theorem3_measured_structured_ic_prices_of_endpoint_bridge_source_assumptions`,
  and
  auxiliary finite dynamic policy support.
- Outstanding assumptions / caveats: source theorems remain conditional on the
  global Theorem 1 threshold-existence compactness/continuity argument, the
  continuous renewal-reward cycle construction, CTMC stochastic-process bridge,
  and the remaining analytic selection/regularity hypotheses listed in
  `README.md`.
