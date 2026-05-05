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
  and the Theorem 3 weak-boundary adapter
  `theorem3AcceptAllWeakRewardCertificate_of_structured_current_bounds`,
  source-facing current-bounds wrapper
  `paper_theorem3_measured_structured_ic_prices_of_structured_current_bounds_source_assumptions`,
  primitive source-facing current-bounds wrapper
  `paper_theorem3_measured_structured_ic_prices_of_structured_current_bounds_primitive_source_assumptions`,
  feasible primitive measurable-IC source wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_feasible_primitive_source_assumptions`,
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
