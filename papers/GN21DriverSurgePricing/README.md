# Driver Surge Pricing

## Source Version

- Paper: *Driver Surge Pricing*
- Authors: Nikhil Garg and Hamid Nazerzadeh
- Version formalized: arXiv v4, dated March 9, 2021; Management Science publication DOI `10.1287/mnsc.2021.4058`
- Official URL: https://pubsonline.informs.org/doi/10.1287/mnsc.2021.4058
- Public PDF: https://arxiv.org/pdf/1905.07544

The PDF is cached locally as `source.pdf` and ignored by Git. The extracted text
cache is `source.txt`.

## Guideline Audit

- Folder follows the one-citation paper contract: local `.gitignore`, README,
  source PDF/text cache, `MainTheorems.lean`, aggregate import, and DAG source.
- `MainTheorems.lean` is source-facing for the continuous trip-length model:
  it uses sets of real trip lengths and abstract lifetime reward functionals.
- Single-state reward quantities are now stated directly as measure/set-integral
  formulas over continuous trip lengths; Proposition 3.1 has a compiled
  measured rejection-step proof rather than only a finite analogue, plus a
  standard-measure constructor that discharges routine nonnegativity and
  monotonicity assumptions and proves the zero-time feasible-set mass bridge
  from positivity of trip lengths, plus a bridge from positive real trip mass
  back to positive underlying measure mass for measured tightening.
- The reusable renewal-reward layer proves the marginal add/remove inequalities
  used in the continuous proof of Theorem 1, plus the same-time replacement
  improvement used in Step 1.
- Theorem 1 now has canonical strict, complete, and boundary threshold sets,
  with feasibility, measurability, partial-threshold, boundary-rate facts, and
  affine-pricing measurability specializations.
- The reusable CTMC layer proves the two-state switch/stay probability closed
  forms, forward equations, row-sum identity, basic probability bounds,
  strict positivity on positive times, the strict linearization bound
  `q(u) < lambda*u`, `q(u)/u` strict decrease on positive times, and the
  zero-time limit `q(u)/u -> lambda`.
- The reusable real-analysis layer now contains a derivative-proxy criterion
  for strict quasi-convexity on positive reals; GN21 instantiates it for the
  canonical CTMC response shapes in Lemmas 7-8. It also exposes between-endpoint
  consequences for strict quasi-convex/quasi-concave functions, the shape fact
  needed by later Lemma 5 interval arguments.
- Appendix D now exposes the derivative-sign kernel, the polynomial-to-response
  strict-sign transfer, interval-density endpoint primitive derivatives,
  measured upper- and lower-endpoint interval-policy primitive realizations,
  improper-tail FTC and tail primitive derivatives/realizations, bounded
  endpoint-move calculus, positive right-endpoint and left-expansion
  replacement realizations, concrete unbounded-tail left replacements, plus
  finite positive density-mass wrappers for
  interval nondegeneracy and canonical long-/short-trip-rejection primitive
  realizations, feasible shape-to-canonical-policy equalities, and arbitrary
  feasible reject-long/reject-short/accept-middle/reject-middle primitive
  realizations, canonical non-accept-all witnesses for finite interval policy
  shapes, including the two-piece reject-middle endpoint paths and both
  reject-middle cutoff derivative bridges, concrete with-density
  reject-middle cutoff and unbounded-tail replacement policies, and statewise
  wrappers that feed those replacements into the Lemma 9/10 strict-local
  bridges,
  including
  positive-density nondegeneracy constructors for non-surge reject-long
  and accept-middle current/replacement policies and both current/replacement
  surge tail and middle-rejection policies,
  measured monotone-tightening wrappers that derive current-policy Lemma 9/10
  bounds from accept-all bounds, including positive-measure variants that
  discharge `lambda*T-Q` nonnegativity and `lambda<Q`, plus primitive-equality
  variants matching the endpoint bridge signatures and named-primitive Remark
  4 positivity wrappers,
  aggregate quotient-calculus derivative bridge, aggregate quotient
  monotonicity for left/right accepted-trip additions from nonnegative
  integrated Lemma 6 kernels, measured `Q,T,W` union additivity and measured
  left/right aggregate weak-improvement bridges for adding accepted sets,
  including accept-all-complement specializations for rejected feasible sets,
  plus pointwise-to-integrated kernel bridges that turn nonnegative Lemma 6
  derivative kernels on an added set into the aggregate primitive side
  condition,
  endpoint-data-to-Lemma-6 derivative certificate bridge,
  structured-kernel-to-Lemma-6 derivative certificate bridge, structured-price
  derivative algebra, small-time switch derivative, the Lemma 7
  canonical derivative-numerator calculation,
  canonical CTMC quasi-convex/quasi-concave response shape, and
  `lambda*t - q(t)` / `lambda T - Q` monotonicity plus nonnegativity and
  strict measured positivity bridges used by Lemmas 6 and 9-10.
  Lemma 9/10 current-bound positivity now also has measured pointwise
  derivative-kernel wrappers and direct accept-all-complement aggregate
  improvement bridges for the surge and non-surge states.
- Theorem 3 now has the `C` numerator-bound factorization, a measured
  accept-all `C ∈ [0,1)` theorem with that bound discharged, the non-surge
  `C < R1/R2 < 1` to Lemma 10 bounds bridge, direct Lemma 9 primitive
  feasibility for the surge ratio, and explicit surge/non-surge `m_i,z_i`
  accounting packages for the structured-price construction, plus a
  CTMC IC endpoint that consumes the positive-form Theorem 4 accept-all
  derivation directly.  The integrated endpoint can now also consume the
  global statewise accept-all reward comparisons or the stricter local
  improvement certificates produced by endpoint derivative proofs, including
  measured-reward and measured aggregate versions specialized to the actual
  two-state CTMC reward functional and positive-primitives variants that avoid
  the stronger Lemma 9 final-sign assumptions.  Accept-all-primitive versions
  discharge scalar positivity and, with state-2 accept-all time integrability,
  the direct Lemma 9 feasibility side conditions from measure/CTMC assumptions
  for both the strict-local and packaged statewise-certificate routes.  The
  source-domain strict-local route is now exposed as
  `Theorem3AcceptAllFeasibleStrictLocalSourceAssumptions` plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_feasible_strict_local_source_assumptions`,
  whose final field is the feasible measurable local-improvement certificate
  for constructed prices; this is the closest current paper-facing endpoint to
  the Lemma 9/10 derivative proof.  A narrower measurable-shape source boundary
  is now exposed as
  `Theorem3AcceptAllMeasurableShapeStatewiseImprovementSourceAssumptions` plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_statewise_improvements_source_assumptions`;
  its final field supplies the measurable Lemma 5 shape derivation together
  with the four feasible endpoint-improvement cases, and Lean converts that
  into the feasible strict-local certificate internally.  The all-measurable
  replacement variant is now exposed as
  `Theorem3AcceptAllMeasurableShapeReplacementStatewiseImprovementSourceAssumptions`
  plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_replacement_statewise_improvements_source_assumptions`;
  it derives the shape derivation internally from Lemma 5-style replacement
  data using
  `Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate.of_all_measurable_shape_replacements`.
  The endpoint current-bounds selection boundary is now exposed as
  `Theorem4MeasurableEndpointCurrentBoundsSelectionCertificate`,
  `Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate.of_endpoint_current_bounds_selection`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_selection`,
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsSelectionSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_selection_source_assumptions`;
  it packages the all-measurable Lemma 5 replacement data together with the
  density endpoint choices and Lemma 9/10 current-bounds data for all four
  shape cases.  The source-facing variant is now exposed as
  `Theorem4NonsurgeMeasurableReplacementData`,
  `Theorem4SurgeMeasurableReplacementData`,
  `Theorem4AllMeasurableOptimalShapeReplacementDerivationCertificate.of_allowed_replacement_data`,
  `Theorem4MeasurableEndpointCurrentBoundsAllowedReplacementSelectionCertificate`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_allowed_replacement_selection`,
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsAllowedReplacementSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_allowed_replacement_source_assumptions`;
  it derives feasible measurability of the canonical Lemma 5 replacement
  policies from ordinary allowed replacement cases.  The density-support layer
  `GN21WithDensityAcceptAllSupport` and the five
  `GN21...CurrentBoundsEndpointData.of_acceptAll_support` constructors now
  derive current/replacement finite-mass and positive-density endpoint fields
  from finite positive accept-all density support.  The endpoint calculus
  helpers `continuous_gn21SwitchProb`,
  `continuous_ctmcStructuredSurgePrice`, and
  `intervalIntegrable_mul_density_of_continuous` derive the finite-interval
  continuity, strong-measurability, and integrability fields from continuous
  densities, with `GN21EndpointProductContinuityData` and
  `GN21FiniteEndpointProductCalculusData` bundling those fields for structured
  prices.  The endpoint constructors ending in
  `of_acceptAll_support_and_calculus` or
  `of_acceptAll_support_and_continuity` consume both the density support and
  product-calculus packages.  `GN21PositiveIntervalProductIntegrabilityData`
  derives short accepted-interval integrability from continuous product data,
  while `GN21TailProductIntegrabilityData` bundles improper tail integrability
  and reuses it for narrower tails.  `GN21RegularEndpointSharedSourceData` and
  the five `...RegularEndpointData.of_shared_source` constructors now factor
  shared density support, density continuity, arrival/switch positivity, and
  accept-all integrability out of the regular endpoint cases.  The current
  regular allowed-policy-form endpoint route is now exposed as
  the five `GN21...RegularEndpointData` packages,
  `Theorem4AllMeasurableAllowedPolicyFormsCertificate`,
  `Theorem4MeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsCertificate`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_allowed_policy_forms`,
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_allowed_policy_forms_source_assumptions`;
  it consumes the all-optimal measurable Lemma 5 allowed policy-form
  classification plus continuous-density endpoint data, source Lemma 9/10
  current-bounds data, support, and tail-integrability packages, then chooses a
  representative optimum and derives the feasible strict-local Theorem 4
  certificate internally.  The regular-shape route remains exposed as
  `Theorem4MeasurableEndpointCurrentBoundsRegularShapeDerivationCertificate`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_shape_derivation`,
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularShapeSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_shape_source_assumptions`;
  it is useful when the caller has already packaged the measurable Lemma 5
  shape derivation.  The older regular-selection route remains exposed as
  the five `GN21...RegularEndpointData` packages,
  `Theorem4MeasurableEndpointCurrentBoundsRegularSelectionCertificate`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_selection`,
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_source_assumptions`;
  it additionally asks for ordinary allowed Lemma 5 replacement data and expands
  the regular endpoint packages into the supported endpoint route internally.
  The supported endpoint route remains exposed as
  the five `GN21...SupportedEndpointData` packages,
  `Theorem4MeasurableEndpointCurrentBoundsSupportedSelectionCertificate`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_supported_selection`,
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsSupportedSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_supported_source_assumptions`;
  it expands ordinary allowed replacement cases plus density-support,
  calculus-backed endpoint data, and short/tail integrability packages into the
  allowed-replacement current-bounds route internally.  The lightest current
  IC-only source boundary is now exposed as
  `Theorem3AcceptAllWeakRewardSourceAssumptions` plus
  `paper_theorem3_measured_structured_ic_prices_of_weak_reward_source_assumptions`,
  whose final field is just weak statewise accept-all reward improvement for
  the constructed prices and does not require exact-set uniqueness of all
  optima. This can now be supplied from a weak measured aggregate `Q,T,W`
  certificate through
  `theorem3AcceptAllWeakRewardCertificate_of_measured_aggregate_weak_reward`,
  with accept-all-complement bridges reducing each statewise weak improvement
  to pointwise nonnegativity of the Lemma 6 kernel over the rejected feasible
  complement plus the usual denominator and integrability side conditions.
  The direct constructors
  `GN21NonsurgeLemma10AcceptAllAggregateData.of_source` and
  `GN21SurgeLemma9AcceptAllAggregateData.of_source` now compose source Lemma
  9/10 data with the primitive current-bounds route in one step.
  The current-bounds route is now packaged as
  `Theorem4MeasuredAggregateStructuredCurrentBoundsWeakCertificate`, which
  feeds the weak Theorem 3 boundary through
  `theorem3AcceptAllWeakRewardCertificate_of_structured_current_bounds`; the
  direct source wrapper is
  `paper_theorem3_measured_structured_ic_prices_of_structured_current_bounds_source_assumptions`.
  A lighter primitive current-bounds boundary,
  `Theorem4MeasuredAggregateStructuredCurrentBoundsPrimitiveCertificate`, now
  derives aggregate denominator and fixed-state positivity side conditions
  from feasible measurable policies, nonnegative arrivals, and positive switch
  rates, with source wrapper
  `paper_theorem3_measured_structured_ic_prices_of_structured_current_bounds_primitive_source_assumptions`.
  The source-domain variant now exposes
  `dynamicMeasurableIncentiveCompatible` and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_feasible_primitive_source_assumptions`,
  whose remaining current-bounds proof ranges only over feasible measurable
  dynamic policies.
  The lightest source-data version,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_source_feasible_source_assumptions`,
  derives nondegeneracy, current/rejected-set integrability, and Remark 4
  `Q > lambda` / `lambda*T-Q >= 0` side conditions from global accept-all
  integrability, positive rates, feasible measurability, and positive current
  mass.
  The accounting-form wrapper,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_accounting_source_assumptions`,
  further replaces fixed-state reward-rate identities with the structured
  price accounting equations discharged by Remark 2.  The reward-rate wrapper,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_reward_rate_source_assumptions`,
  goes in the other direction: fixed-state source obligations can be stated as
  measured reward-rate equalities, and Lean derives the scaled earning
  identities `W_i = R_i T_i` needed by the current-bounds route.
  The stronger positive-replacement source boundary is exposed as
  `Theorem3AcceptAllPositiveReplacementSourceAssumptions` plus
  `paper_theorem3_measured_structured_ic_prices_of_positive_replacement_source_assumptions`,
  whose final field is exactly the Lemma 9/10 positive-replacement proof for
  the constructed prices. The broader allowed-replacement route is also
  exposed as `Theorem3AcceptAllAllowedReplacementSourceAssumptions` plus
  `paper_theorem3_measured_structured_ic_prices_of_source_assumptions`, whose
  proof boundary is the continuous allowed-replacement Theorem 4 certificate
  for the constructed prices; endpoint-bridge data can now be converted
  directly into that boundary via
  `Theorem4AllowedReplacementEndpointBridgeCertificate` and
  `theorem3AcceptAllAllowedReplacementCertificate_of_endpoint_bridges`, with a
  direct source wrapper
  `paper_theorem3_measured_structured_ic_prices_of_endpoint_bridge_source_assumptions`.
- The finite MDP declarations are marked auxiliary support only. They are not
  used to claim the paper's continuous CTMC theorems.
- The DAG uses the shared TikZ preamble and separates solid verified support
  edges from dashed continuous-source proof debts.

## Paper-Facing Ledger

- Human-facing theorem file: `GN21DriverSurgePricing/MainTheorems.lean`
- Dependency DAG: `GN21DriverSurgePricing/DependencyDAG.tex`
- Rendered DAG: `GN21DriverSurgePricing/DependencyDAG.pdf`

Status cells use the controlled vocabulary from `../../docs/STATUS.md`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Section 2.2, driver optimality and IC definitions | `singleStateOptimal`, `singleStateIncentiveCompatible`, `dynamicOptimal`, `dynamicIncentiveCompatible`, `dynamicStateReward`, `dynamicStateReward_optimal_of_dynamicOptimal`, `dynamicOptimal_acceptAll_of_statewise_acceptAll_improvements`, `singleStateTripMass`, `singleStateTripTime`, `singleStateTripPayment`, `singleStateRenewalReward` | partially formalized | `MainTheorems.lean` | Continuous source predicates and the single-state renewal-reward formula are represented over real trip-length acceptance sets and set integrals; dynamic optima are now bridged to statewise local continuation optimality, and statewise accept-all reward improvements imply global accept-all optimality. The renewal theorem/LLN derivations are not yet encoded. |
| Lemma 1, dynamic earnings decomposition | `gn21SubcycleEarning`, `gn21StateRewardRate`, `gn21StateMeanEarning`, `gn21MeasuredStateRewardRate`, `gn21MeasuredDynamicReward`, `gn21MeasuredStateRewardRate_eq_scaled_primitives`, `gn21MeasuredTimeFraction_eq_scaled_primitives`, `paper_lemma1_measured_dynamic_reward_eq_aggregate_scaled_primitives`, `gn21MeasuredAggregateRewardPrimitives`, `GN21MeasuredPairNondegenerate`, `gn21MeasuredPairNondegenerate_of_positive_primitives`, `gn21MeasuredPairNondegenerate_of_positive_measure`, `gn21MeasuredPairNondegenerate_of_positive_measure_upperEndpoint_right`, `gn21MeasuredPairNondegenerate_of_positive_measure_upperEndpoint_left`, `singleStateTripMass_pos_of_measure_ne_zero_ne_top`, `singleStateTripMass_withDensity_pos_of_pos_on`, `singleStateTripMass_upperEndpoint_withDensity_pos_of_pos_on`, `singleStateTripMass_upperEndpointReplacement_withDensity_pos_of_pos_on`, `gn21MeasuredPairNondegenerate_of_upperEndpoint_withDensity_right`, `gn21MeasuredPairNondegenerate_of_upperEndpoint_withDensity_left`, `paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives`, `paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate`, `paper_lemma1_measured_dynamic_reward_le_of_aggregate_primitives_le`, `paper_lemma1_measured_dynamic_reward_lt_of_aggregate_primitives_lt`, `paper_lemma1_measured_dynamic_reward_le_of_aggregate_pair_le_of_nondegenerate`, `paper_lemma1_measured_dynamic_reward_lt_of_aggregate_pair_lt_of_nondegenerate`, `gn21MeasuredDynamicRewardFunctional`, `gn21MeasuredDynamicRewardFunctional_apply`, `gn21MeasuredCTMCStructuredDynamicReward`, `gn21AcceptAllScaledStateTime`, `gn21AcceptAllExitWeightIntegral`, `dynamicStateReward_gn21MeasuredDynamicRewardFunctional_zero`, `dynamicStateReward_gn21MeasuredDynamicRewardFunctional_one`, `paper_lemma1_state_reward_rate_algebra`, `paper_lemma1_measured_state_reward_rate_algebra`, `paper_lemma1_measured_dynamic_reward_decomposition` | partially formalized | `MainTheorems.lean` | The displayed reward-rate cancellation and measured `mu_i R_i + mu_j R_j` decomposition are proved once the paper's time-fraction and state-reward quantities are in place; the scalar measured formula now has a `DynamicReward` wrapper, accept-all primitive aliases, statewise unfolding lemmas for the actual two-state reward functional, a nondegenerate pair package with positivity constructors including finite positive-density upper-endpoint interval specializations, and compiled reductions from measured reward comparisons to the aggregate `Q,T,W` quotient used by Lemma 6. The stochastic renewal law-of-large-numbers bridge for two-state CTMC cycles remains open. |
| Theorem 1, single-state threshold best response | `strictThresholdRatePolicy`, `partialThresholdRatePolicy`, `thresholdRatePolicy`, `strictThresholdPolicy`, `completeThresholdPolicy`, `thresholdBoundaryPolicy`, `measurableSet_strictThresholdPolicy`, `measurableSet_completeThresholdPolicy`, `measurableSet_thresholdBoundaryPolicy`, `measurable_affinePricing_rate`, `measurableSet_strictThresholdPolicy_affinePricing`, `measurableSet_completeThresholdPolicy_affinePricing`, `measurableSet_thresholdBoundaryPolicy_affinePricing`, `onTripRateEquals_thresholdBoundaryPolicy`, `singleStateAverageTripRate`, `paper_theorem1_step1_same_time_more_payment_improves_reward`, `paper_theorem1_step1_equal_utilization_swap_improves_reward`, `paper_theorem1_add_positive_time_set_if_average_above_current`, `paper_theorem1_remove_positive_time_set_if_average_below_current`, `paper_theorem1_step2_add_boundary_set_if_threshold_ge_current`, `paper_theorem1_step2_remove_boundary_set_if_threshold_le_current`, `paper_theorem1_complete_threshold_optimal_of_step_certificates`, `SingleStateThresholdCertificate`, `paper_theorem1_threshold_certificate_of_step_certificates`, `paper_theorem1_single_state_threshold_best_response_of_certificate` | partially formalized | `MainTheorems.lean`, `EconCSLib/Foundations/Probability/RenewalReward.lean` | Lean proves canonical measurable threshold sets, affine-pricing threshold measurability, continuous measured Step 1 equal-utilization replacement algebra, Step 2 boundary add/remove cases, the general marginal add/remove renewal steps, an explicit Step 1/2/3 assembly theorem, and a constructor packaging those obligations into the standard threshold-certificate interface. Still needs the source selection/compactness argument that constructs the Step 1 replacement and Step 3 maximizer for every pricing function `w`. |
| Proposition 3.1, affine single-state IC | `affinePricing`, `singleStateTripPayment_affinePricing`, `affineSingleStateRenewalReward`, `SingleStateTripMeasureAssumptions`, `singleStateTripMeasureAssumptions_of_standard`, `singleStateTripMass_eq_zero_of_time_zero_subset_acceptAll`, `singleStateMeasurableIncentiveCompatible`, `affineSingleStateRenewalReward_acceptAll_diff_eq_complementReward`, `paper_proposition3_1_affine_rejected_set_average_rate_bound`, `paper_proposition3_1_affine_accept_all_ge_rejecting_any_measurable_set`, `paper_proposition3_1_affine_accept_all_ge_measurable_policy`, `paper_proposition3_1_affine_single_state_measurable_ic`, `paper_proposition3_1_affine_single_state_measurable_ic_of_standard_measure`, `SingleStateAffineICCertificate`, `paper_proposition3_1_affine_single_state_ic_of_certificate` | formalized with caveat | `MainTheorems.lean` | Lean proves the continuous measurable-policy endpoint: under `0 <= a <= m/lambda`, accept-all is optimal among all measurable feasible policies for the affine renewal reward. The standard-measure constructor now derives the basic nonnegativity, rejected-set time monotonicity, and zero-time feasible-set mass facts automatically from the accept-all first moment. Caveat: the older unrestricted `singleStateIncentiveCompatible` wrapper remains certificate-based because it quantifies over all sets, not just measurable feasible policies. |
| Lemma 2 and Remarks 1/3/4, two-state CTMC transition probability | `gn21SwitchProb`, `gn21TransitionProb`, `paper_lemma2_switch_probability_formula`, `paper_lemma2_switch_probability_forward_equation`, `paper_lemma2_switch_probability_pos`, `paper_lemma2_switch_probability_nonneg`, `paper_lemma2_switch_probability_le_one`, `paper_lemma2_transition_probability_zero_time`, `paper_lemma2_transition_probability_row_sum`, `paper_remark1_switch_probability_per_time_deriv_neg`, `paper_remark1_switch_probability_per_time_strictAntiOn`, `paper_remark3_switch_probability_deriv_at_zero`, `paper_remark3_switch_probability_per_time_tendsto_at_zero`, `paper_remark4_switch_probability_lt_rate_mul_time`, `paper_remark4_switch_probability_per_time_lt_rate`, `paper_remark4_switch_time_minus_switch_probability_pos`, `paper_remark4_switch_time_minus_switch_probability_nonneg`, `paper_remark4_switch_time_minus_switch_probability_deriv_nonneg`, `paper_remark4_switch_time_minus_switch_probability_deriv_pos`, `paper_remark4_switch_time_minus_switch_probability_strictMonoOn` | formalized with caveat | `MainTheorems.lean`, `EconCSLib/Foundations/Probability/CTMC.lean` | The switch/stay closed forms, transition-kernel initial condition, row sums, Kolmogorov forward equation, probability bounds, strict positivity for positive elapsed time, small-time derivative at zero, `q(u)/u -> lambda`, `q(u) < lambda*u`, strict decrease of `q(u)/u` on positive times, `lambda*t - q(t) > 0`, `lambda*t - q(t) >= 0`, and strict monotonicity of `lambda*t - q(t)` on positive times are proved under the usual positive/nonnegative-rate and time assumptions. Caveat: Lean does not yet construct the sample-path CTMC or reproduce the paper's Laplace-transform derivation. |
| Lemma 3, fraction of time in each state | `gn21StateCycleTime`, `gn21ExitWeightIntegral`, `gn21SubcycleLength`, `gn21CrossSubcycleProb`, `gn21TimeFractionFromCycles`, `gn21TimeFractionFormula`, `gn21MeasuredTimeFraction`, `paper_lemma3_time_fraction_formula_algebra`, `paper_lemma3_measured_time_fraction_formula_algebra`, `paper_lemma3_measured_time_fractions_sum_to_one` | partially formalized | `MainTheorems.lean` | The displayed time-fraction algebra is proved after substituting the paper's measured `T_i(σ_i)` and `Q_i(σ_i)` set-integral definitions into the subcycle expression, and the two measured state fractions are proved to sum to one when the denominator is nonzero; the renewal law-of-large-numbers bridge from CTMC cycles to actual long-run time fractions remains open. |
| Lemma 4, single-state optimal interval form | `agreesAwayFromThresholdBoundary`, `SingleStateUniqueThresholdCertificate`, `paper_lemma4_single_state_unique_threshold_of_certificate` | conditional | `MainTheorems.lean` | Source endpoint is exposed from an explicit continuous uniqueness certificate: optimal threshold policy, reward equal to threshold, and uniqueness away from boundary trips `w(tau)/tau = c`. The proof of that certificate from Theorem 1's compactness/continuity argument remains open. |
| Lemma 5, derivative-shape optimizer replacement | `Lemma5DerivativeShape`, `lemma5DerivativeShapeWitness`, `lemma5PolicyForm`, `rejectLongTripsPolicy`, `rejectShortTripsPolicy`, `acceptMiddleTripsPolicy`, `rejectMiddleTripsPolicy`, `measurableSet_rejectLongTripsPolicy`, `measurableSet_rejectShortTripsPolicy`, `measurableSet_acceptMiddleTripsPolicy`, `measurableSet_rejectMiddleTripsPolicy`, `lemma5PolicyForm_strictlyIncreasing_rejectShortTripsPolicy`, `lemma5PolicyForm_strictlyDecreasing_rejectLongTripsPolicy`, `lemma5DerivativeShapeWitness_strictlyQuasiConvex_of_lemma7_affine_ctmc_response`, `lemma5DerivativeShapeWitness_strictlyQuasiConcave_of_lemma8_affine_ctmc_response`, `paper_lemma5_strictQuasiConvex_response_lt_of_between`, `paper_lemma5_strictQuasiConcave_response_lt_between`, `Lemma5OptimizerReplacementCertificate`, `lemma5PositiveOptimizerReplacementCertificate_acceptAll`, `lemma5StrictlyIncreasingOptimizerReplacementCertificate_rejectShort`, `lemma5StrictlyDecreasingOptimizerReplacementCertificate_rejectLong`, `lemma5StrictlyQuasiConvexOptimizerReplacementCertificate_rejectMiddle`, `lemma5StrictlyQuasiConcaveOptimizerReplacementCertificate_acceptMiddle`, `paper_lemma5_optimizer_replacement_of_certificate`, `lemma5PolicyForm_of_optimizer_replacement_certificate_of_optimal`, `acceptsAllTrips_of_positive_optimizer_replacement_certificate_of_optimal` | conditional | `MainTheorems.lean`, `EconCSLib/Foundations/Math/QuasiConvex.lean` | The five derivative-shape cases and resulting policy forms are encoded, canonical measurable interval-policy representatives are provided, the canonical representatives are tied directly to Lemma 5 policy forms, Lemmas 7-8 now feed explicit derivative-shape witnesses, strict quasi-convex/quasi-concave between-endpoint facts used in the interval-shape proof are formalized, all five canonical shape cases now have direct optimizer-replacement constructors, and optimality-extraction lemmas convert strict replacement certificates back into policy forms. The endpoint is closed from a certificate that still packages the open-measurable-set approximation, continuity, and endpoint derivative argument. |
| Lemma 6, derivative formula for dynamic reward | `sameStrictSign`, `sameStrictSign_trans`, `sameStrictSign_pos_left`, `sameStrictSign_neg_left`, `exists_pos_between_of_lt_of_pos`, `exists_pos_right_improvement_of_hasDerivAt_pos`, `exists_pos_right_improvement_of_hasDerivAt_pos_lt`, `exists_pos_right_decrease_of_hasDerivAt_neg`, `exists_pos_right_decrease_of_hasDerivAt_neg_lt`, `exists_pos_left_improvement_of_hasDerivAt_neg`, `exists_pos_left_improvement_of_hasDerivAt_neg_lt`, `exists_pos_left_decrease_of_hasDerivAt_pos`, `exists_pos_left_decrease_of_hasDerivAt_pos_lt`, `integral_Ioi_hasDerivAt`, `gn21DerivativeSignKernel`, `gn21DerivativeSignKernelWithRates`, `gn21Lemma6Response`, `gn21AggregateDynamicReward`, `gn21AggregateDynamicReward_swap`, `gn21EndpointQiPath`, `gn21EndpointWiPath`, `gn21EndpointTiPath`, `gn21LowerEndpointQiPath`, `gn21LowerEndpointWiPath`, `gn21LowerEndpointTiPath`, `gn21TailQiPath`, `gn21TailWiPath`, `gn21TailTiPath`, `gn21RejectMiddleQiPath`, `gn21RejectMiddleWiPath`, `gn21RejectMiddleTiPath`, `gn21UpperEndpointPolicy`, `measurableSet_gn21UpperEndpointPolicy`, `gn21UpperEndpointReplacement`, `measurableSet_gn21UpperEndpointReplacement`, `gn21LowerEndpointPolicy`, `measurableSet_gn21LowerEndpointPolicy`, `gn21LowerEndpointReplacement`, `gn21LowerEndpointLeftReplacement`, `measurableSet_gn21LowerEndpointReplacement`, `measurableSet_gn21LowerEndpointLeftReplacement`, `gn21TailPolicy`, `measurableSet_gn21TailPolicy`, `gn21RejectMiddleLoReplacement`, `gn21RejectMiddleHiReplacement`, `measurableSet_gn21RejectMiddleLoReplacement`, `measurableSet_gn21RejectMiddleHiReplacement`, `gn21UpperEndpointPolicy_subset_acceptAllPolicy`, `gn21UpperEndpointReplacement_subset_acceptAllPolicy`, `gn21LowerEndpointPolicy_subset_acceptAllPolicy`, `gn21LowerEndpointReplacement_subset_acceptAllPolicy`, `gn21LowerEndpointLeftReplacement_subset_acceptAllPolicy`, `gn21TailPolicy_subset_acceptAllPolicy`, `gn21RejectMiddleLoReplacement_subset_acceptAllPolicy`, `gn21RejectMiddleHiReplacement_subset_acceptAllPolicy`, `gn21ExitWeightIntegral_upperEndpoint_withDensity_eq_endpointQiPath`, `gn21ScaledStateTime_upperEndpoint_withDensity_eq_endpointTiPath`, `gn21ScaledStateEarning_upperEndpoint_withDensity_eq_endpointWiPath`, `gn21ExitWeightIntegral_upperEndpointReplacement_withDensity_eq_endpointQiPath`, `gn21ScaledStateTime_upperEndpointReplacement_withDensity_eq_endpointTiPath`, `gn21ScaledStateEarning_upperEndpointReplacement_withDensity_eq_endpointWiPath`, `gn21ExitWeightIntegral_lowerEndpoint_withDensity_eq_lowerEndpointQiPath`, `gn21ScaledStateTime_lowerEndpoint_withDensity_eq_lowerEndpointTiPath`, `gn21ScaledStateEarning_lowerEndpoint_withDensity_eq_lowerEndpointWiPath`, `gn21ExitWeightIntegral_lowerEndpointReplacement_withDensity_eq_lowerEndpointQiPath`, `gn21ScaledStateTime_lowerEndpointReplacement_withDensity_eq_lowerEndpointTiPath`, `gn21ScaledStateEarning_lowerEndpointReplacement_withDensity_eq_lowerEndpointWiPath`, `gn21ExitWeightIntegral_lowerEndpointLeftReplacement_withDensity_eq_lowerEndpointQiPath`, `gn21ScaledStateTime_lowerEndpointLeftReplacement_withDensity_eq_lowerEndpointTiPath`, `gn21ScaledStateEarning_lowerEndpointLeftReplacement_withDensity_eq_lowerEndpointWiPath`, `gn21ExitWeightIntegral_tail_withDensity_eq_tailQiPath`, `gn21ScaledStateTime_tail_withDensity_eq_tailTiPath`, `gn21ScaledStateEarning_tail_withDensity_eq_tailWiPath`, `gn21ExitWeightIntegral_rejectLongTripsPolicy_withDensity_eq_endpointQiPath`, `gn21ScaledStateTime_rejectLongTripsPolicy_withDensity_eq_endpointTiPath`, `gn21ScaledStateEarning_rejectLongTripsPolicy_withDensity_eq_endpointWiPath`, `gn21ExitWeightIntegral_rejectShortTripsPolicy_withDensity_eq_tailQiPath`, `gn21ScaledStateTime_rejectShortTripsPolicy_withDensity_eq_tailTiPath`, `gn21ScaledStateEarning_rejectShortTripsPolicy_withDensity_eq_tailWiPath`, `gn21ExitWeightIntegral_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleQiPath`, `gn21ScaledStateTime_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleTiPath`, `gn21ScaledStateEarning_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleWiPath`, `gn21ExitWeightIntegral_rejectMiddleLoReplacement_withDensity_eq_rejectMiddleQiPath`, `gn21ScaledStateTime_rejectMiddleLoReplacement_withDensity_eq_rejectMiddleTiPath`, `gn21ScaledStateEarning_rejectMiddleLoReplacement_withDensity_eq_rejectMiddleWiPath`, `gn21ExitWeightIntegral_rejectMiddleHiReplacement_withDensity_eq_rejectMiddleQiPath`, `gn21ScaledStateTime_rejectMiddleHiReplacement_withDensity_eq_rejectMiddleTiPath`, `gn21ScaledStateEarning_rejectMiddleHiReplacement_withDensity_eq_rejectMiddleWiPath`, `gn21EndpointQiPath_hasDerivAt`, `gn21EndpointWiPath_hasDerivAt`, `gn21EndpointTiPath_hasDerivAt`, `gn21LowerEndpointQiPath_hasDerivAt`, `gn21LowerEndpointWiPath_hasDerivAt`, `gn21LowerEndpointTiPath_hasDerivAt`, `gn21TailQiPath_hasDerivAt`, `gn21TailWiPath_hasDerivAt`, `gn21TailTiPath_hasDerivAt`, `gn21RejectMiddleQiPath_lo_hasDerivAt`, `gn21RejectMiddleWiPath_lo_hasDerivAt`, `gn21RejectMiddleTiPath_lo_hasDerivAt`, `gn21RejectMiddleQiPath_hi_hasDerivAt`, `gn21RejectMiddleWiPath_hi_hasDerivAt`, `gn21RejectMiddleTiPath_hi_hasDerivAt`, `paper_lemma6_aggregate_reward_hasDerivAt`, `paper_lemma6_derivative_formula_of_aggregate_paths`, `paper_lemma6_derivative_formula_of_interval_density_paths`, `paper_lemma6_lower_derivative_formula_of_interval_density_paths`, `paper_lemma6_tail_derivative_formula_of_interval_density_paths`, `paper_lemma6_reject_middle_lo_derivative_formula_of_interval_density_paths`, `paper_lemma6_reject_middle_hi_derivative_formula_of_interval_density_paths`, `paper_lemma6_derivative_kernel_state_rate_algebra`, `paper_lemma6_derivative_kernel_eq_scaled_response`, `paper_lemma6_derivative_kernel_same_sign_response`, `Lemma6EndpointDerivativeData`, `lemma6EndpointDerivativeData_of_aggregate_paths`, `lemma6EndpointDerivativeData_of_interval_density_paths`, `lemma6DerivativeFormulaCertificate_of_endpoint_data`, `paper_lemma6_endpoint_hasDerivAt_of_data`, `paper_lemma6_derivative_value_pos_of_kernel_pos_of_endpoint_data`, `paper_lemma6_derivative_value_neg_of_kernel_neg_of_endpoint_data`, `paper_lemma6_exists_pos_right_improvement_of_kernel_pos_of_endpoint_data`, `paper_lemma6_exists_pos_right_decrease_of_kernel_neg_of_endpoint_data`, `paper_lemma6_exists_pos_right_improvement_of_interval_density_kernel_pos`, `paper_lemma6_exists_pos_right_decrease_of_interval_density_kernel_neg`, `paper_lemma6_exists_pos_right_improvement_of_lower_interval_density_kernel_neg`, `paper_lemma6_exists_pos_right_improvement_of_lower_interval_density_kernel_neg_lt`, `paper_lemma6_exists_pos_right_decrease_of_lower_interval_density_kernel_pos`, `paper_lemma6_exists_pos_right_decrease_of_lower_interval_density_kernel_pos_lt`, `paper_lemma6_exists_pos_left_improvement_of_lower_interval_density_kernel_pos_lt`, `paper_lemma6_exists_pos_left_improvement_of_tail_interval_density_kernel_pos_lt`, `paper_lemma6_exists_pos_right_improvement_of_reject_middle_lo_interval_density_kernel_pos_lt`, `paper_lemma6_exists_pos_left_improvement_of_reject_middle_hi_interval_density_kernel_pos_lt`, `paper_lemma6_derivative_value_pos_of_kernel_pos_of_certificate`, `paper_lemma6_derivative_value_neg_of_kernel_neg_of_certificate`, `paper_lemma6_derivative_value_same_sign_structured_kernel_of_certificate`, `paper_lemma6_derivative_value_pos_of_structured_kernel_pos_of_certificate`, `paper_lemma6_derivative_value_neg_of_structured_kernel_neg_of_certificate`, `paper_lemma6_derivative_value_same_sign_response_of_certificate`, `paper_lemma6_derivative_value_pos_of_response_pos_of_certificate`, `paper_lemma6_derivative_value_neg_of_response_neg_of_certificate`, `Lemma6DerivativeFormulaCertificate`, `paper_lemma6_derivative_formula_of_certificate` | partially formalized | `MainTheorems.lean` | The displayed derivative-sign kernel algebra, state-rate substitution, normalized paper `r(u,i,w,sigma)` response equivalence, aggregate reward state-swap symmetry, interval-density upper/lower, unbounded-tail, and two-piece middle-rejection endpoint primitive derivatives, measured upper/lower endpoint, tail, and reject-middle policy realizations of the `Q,T,W` primitives under `volume.withDensity`, positive right-endpoint and bounded lower-endpoint/tail/reject-middle replacement primitive realizations including concrete lower- and upper-cutoff reject-middle replacements, canonical long-, short-, and middle-trip-rejection primitive realizations up to null endpoint boundaries, aggregate quotient-calculus derivative, endpoint derivative-data package, positive-scale strict-sign transfer from the polynomial kernel to the normalized response, direct positive/negative derivative consequences from either kernel or response signs, local calculus bridges from derivative sign to strict right/left endpoint improvement/decrease with bounded variants, endpoint-data bridges from kernel sign to a strict nearby endpoint reward comparison, direct interval-density endpoint movement theorems for upper, lower, unbounded-tail, and reject-middle endpoints, and the structured-kernel-to-analytic-derivative certificate bridge used by Lemmas 9-10 are proved. The remaining analytic bridge is selecting endpoint moves from arbitrary optimal open measurable policies and feeding those realized primitives into the set-valued continuous reward functional. |
| Lemmas 7-8, affine pricing quasi-convex/concave response | `strictQuasiConvexOnPositive`, `strictQuasiConcaveOnPositive`, `paper_lemma7_8_affine_response_canonical_form`, `gn21Lemma7CanonicalResponse`, `gn21Lemma7CanonicalDerivativeNumerator`, `paper_lemma7_canonical_response_hasDerivAt`, `paper_lemma7_canonical_derivative_numerator_hasDerivAt`, `paper_lemma7_canonical_derivative_numerator_deriv_pos`, `paper_lemma7_canonical_ctmc_response_quasi_convex`, `paper_lemma8_canonical_ctmc_response_quasi_concave`, `paper_lemma7_affine_ctmc_response_eq_canonical`, `paper_lemma8_affine_ctmc_response_eq_canonical`, `paper_lemma7_affine_ctmc_response_quasi_convex`, `paper_lemma8_affine_ctmc_response_quasi_concave`, `Lemma7QuasiConvexCertificate`, `paper_lemma7_affine_ctmc_quasi_convex_certificate`, `paper_lemma7_affine_positive_additive_quasi_convex_of_certificate`, `Lemma8QuasiConcaveCertificate`, `paper_lemma8_affine_ctmc_quasi_concave_certificate`, `paper_lemma8_affine_negative_additive_quasi_concave_of_certificate` | partially formalized | `MainTheorems.lean`, `EconCSLib/Foundations/Math/QuasiConvex.lean` | The affine response algebra is reduced to the source canonical form, the source-series derivative-numerator calculation for Lemma 7 is proved directly from the CTMC closed form, the canonical CTMC response-shape cases are closed under the paper's sign assumptions, and the old certificate endpoints now have concrete CTMC certificate constructors. The remaining bridge is instantiating those sign assumptions from the full Lemma 6 endpoint-derivative setup and feeding the resulting derivative shapes into Lemma 5/Theorem 4. |
| Lemmas 9-10, IC derivative conditions | `gn21StructuredDerivativeSignKernel`, `gn21StructuredDerivativeSwitchBracket`, `gn21StructuredDerivativeStaticTerm`, `gn21StructuredDerivativeSignKernel_eq_bracket_static`, `structuredDerivativeKernel_pos_of_linearization_bound`, `structuredDerivativeKernel_pos_of_linearization_bound_and_tail`, `paper_remark2_structured_scaled_earning_algebra`, `paper_remark2_structured_derivative_kernel_algebra`, `paper_remark2_structured_derivative_kernel_pos_of_ctmc_switch`, `paper_remark2_structured_derivative_kernel_pos_of_ctmc_switch_and_tail`, `paper_remark4_scaled_time_minus_exit_weight_eq_integral`, `paper_remark4_scaled_time_minus_exit_weight_nonneg`, `paper_remark4_scaled_time_minus_exit_weight_integral_pos_of_positive_measure`, `paper_remark4_scaled_time_minus_exit_weight_pos_of_positive_measure`, `paper_remark4_scaled_time_minus_exit_weight_pos_of_positive_measure_eq`, `paper_remark4_scaled_time_minus_exit_weight_le_acceptAll`, `paper_remark4_scaled_time_minus_exit_weight_measured_le_acceptAll`, `paper_remark4_exit_weight_integral_component_pos_of_positive_measure`, `paper_remark4_exit_weight_gt_switch_of_positive_measure`, `paper_remark4_exit_weight_gt_switch_of_positive_measure_eq`, `paper_remark4_exit_weight_integral_component_le_acceptAll`, `paper_remark4_exit_weight_integral_le_acceptAll`, `lemma9StructuredLowerFromGap`, `lemma9StructuredUpperFromExitWeight`, `lemma9StructuredLowerFromGap_mono`, `lemma9StructuredUpperFromExitWeight_antitone`, `lemma9StructuredBounds_of_acceptAll_tightening`, `lemma9StructuredBounds_of_acceptAll_measured_tightening`, `lemma9StructuredBounds_of_acceptAll_measured_tightening_of_positive_measure`, `lemma9StructuredBounds_of_acceptAll_measured_tightening_of_positive_measure_eq`, `lemma9StructuredStaticTerm_pos_of_upper_bound`, `lemma9StructuredLinearEndpoint_pos_of_lower_bound`, `paper_lemma9_structured_derivative_kernel_pos_of_current_bounds`, `paper_lemma9_derivative_value_pos_of_current_bounds_certificate`, `paper_lemma9_exists_pos_right_improvement_of_current_bounds_endpoint_data`, `paper_lemma9_exists_pos_right_improvement_of_interval_density_current_bounds`, `paper_lemma9_exists_pos_left_improvement_of_lower_interval_density_current_bounds`, `paper_lemma9_exists_pos_left_improvement_of_tail_interval_density_current_bounds`, `lemma9StructuredLowerNumerator`, `lemma9StructuredLowerDenominator`, `lemma9StructuredUpperNumerator`, `lemma9StructuredUpperDenominator`, `lemma9StructuredBounds`, `lemma9StructuredUpper_pos`, `paper_lemma9_structured_bounds_feasible_positive_of_lower_lt_upper`, `paper_lemma9_structured_bounds_feasible_positive_of_final_signs`, `lemma10StructuredLowerFromGap`, `lemma10StructuredUpperFromExitWeight`, `lemma10StructuredLowerFromGap_mono`, `lemma10StructuredUpperFromExitWeight_antitone`, `lemma10StructuredBounds_of_acceptAll_tightening`, `lemma10StructuredBounds_of_acceptAll_measured_tightening`, `lemma10StructuredBounds_of_acceptAll_measured_tightening_of_positive_measure`, `lemma10StructuredBounds_of_acceptAll_measured_tightening_of_positive_measure_eq`, `lemma10StructuredStaticTerm_pos_of_upper_bound`, `lemma10StructuredLinearEndpoint_pos_of_lower_bound`, `paper_lemma10_structured_derivative_kernel_pos_of_current_bounds`, `paper_lemma10_derivative_value_pos_of_current_bounds_certificate`, `paper_lemma10_exists_pos_right_improvement_of_current_bounds_endpoint_data`, `paper_lemma10_exists_pos_right_improvement_of_interval_density_current_bounds`, `paper_lemma10_exists_pos_left_improvement_of_lower_interval_density_current_bounds`, `paper_lemma10_exists_pos_left_improvement_of_tail_interval_density_current_bounds`, `lemma10StructuredLowerNumerator`, `lemma10StructuredLowerDenominator`, `lemma10StructuredUpperDenominator`, `lemma10StructuredBounds`, `paper_lemma10_structured_bounds_feasible_of_positive_terms`, `paper_lemma10_structured_bounds_feasible_of_positive_pieces`, `lemma9SurgeDerivativeCertificate_of_current_bounds`, `lemma10NonsurgeDerivativeCertificate_of_current_bounds`, `lemma5DerivativeShapeWitness_positive_of_lemma9_current_bounds`, `lemma5DerivativeShapeWitness_positive_of_lemma10_current_bounds`, `paper_lemma9_surge_derivative_positive_of_certificate`, `paper_lemma10_nonsurge_derivative_positive_of_certificate` | partially formalized | `MainTheorems.lean` | Remark 2 structured derivative algebra, bracket/static decomposition, sign-splitting CTMC-linearization positivity bridges for the structured derivative kernel, Remark 3/4 CTMC support, strict measured positivity of `lambda T-Q` and `Q-lambda`, named-primitive positivity wrappers, accept-all maximization of nonnegative integral components, measured current-policy tightening for `lambda T-Q` and `Q`, Lemma 9/10 bound predicates, feasibility and positive-ratio feasibility bridges, monotone tightening from accept-all to current policies including measured-policy wrappers, positive-measure variants, and primitive-equality variants matching endpoint signatures, current-bounds-to-structured-kernel positivity, structured-kernel-to-Lemma-6 analytic derivative certificate consequences, direct endpoint-improvement bridges from current bounds plus Lemma 6 endpoint data, direct interval-density upper-endpoint plus finite lower-endpoint and unbounded-tail left-expansion bridges for the Lemma 9 and Lemma 10 structured cases, and positive Lemma 5 derivative-shape witnesses are formalized. The remaining analytic debt is connecting arbitrary open measurable policy moves to these interval/tail-density improvement primitives for the set-valued continuous reward functional. |
| Theorem 4, appendix structural theorem subsuming Theorem 2 | `theorem4NonsurgeShape`, `theorem4SurgeShape`, `theorem4NonsurgeShape_cases_of_not_acceptsAll`, `theorem4SurgeShape_cases_of_not_acceptsAll`, `theorem4NonsurgeAllowedLemma5Shape`, `theorem4SurgeAllowedLemma5Shape`, `theorem4NonsurgeAllowedLemma5Shape_strictlyDecreasing`, `theorem4SurgeAllowedLemma5Shape_strictlyQuasiConvex`, `theorem4NonsurgeShape_of_lemma5_positive`, `theorem4NonsurgeShape_of_lemma5_strictlyDecreasing`, `theorem4NonsurgeShape_of_lemma5_strictlyQuasiConcave`, `theorem4SurgeShape_of_lemma5_positive`, `theorem4SurgeShape_of_lemma5_strictlyIncreasing`, `theorem4SurgeShape_of_lemma5_strictlyQuasiConvex`, `theorem4NonsurgeShape_rejectLongTripsPolicy`, `theorem4SurgeShape_rejectMiddleTripsPolicy`, `theorem4NonsurgeShape_of_allowed_lemma5_form`, `theorem4SurgeShape_of_allowed_lemma5_form`, `theorem4NonsurgeAllowedReplacement_positive_acceptAll`, `theorem4NonsurgeAllowedReplacement_rejectLong`, `theorem4NonsurgeAllowedReplacement_acceptMiddle`, `theorem4SurgeAllowedReplacement_positive_acceptAll`, `theorem4SurgeAllowedReplacement_rejectShort`, `theorem4SurgeAllowedReplacement_rejectMiddle`, `Theorem4NonsurgeAllowedReplacementData`, `Theorem4SurgeAllowedReplacementData`, `Theorem4AllOptimalShapeReplacementDerivationCertificate.of_allowed_replacement_data`, `Theorem4ShapeDerivationCertificate`, `theorem4StructuralPolicyCertificate_of_shape_derivation`, `paper_theorem4_dynamic_structural_policy_of_shape_derivation`, `Theorem4AllOptimalShapeReplacementDerivationCertificate`, `theorem4ShapeReplacementDerivationCertificate_of_all_shape_replacements`, `theorem4ShapeDerivationCertificate_of_all_shape_replacements`, `paper_theorem4_dynamic_structural_policy_of_all_shape_replacements`, `Theorem4AllowedReplacementStatewiseImprovementCertificate`, `Theorem4ShapeDerivationStatewiseImprovementCertificate.of_allowed_replacement_data`, `paper_theorem4_accept_all_unique_optimal_of_allowed_replacement_data`, `Theorem4AcceptAllDerivationCertificate`, `theorem4ShapeDerivationCertificate_of_accept_all_derivation`, `paper_theorem4_accept_all_unique_optimal_of_positive_lemma5_forms`, `paper_theorem4_dynamic_structural_policy_of_accept_all_derivation`, `Theorem4PositiveReplacementDerivationCertificate`, `theorem4AcceptAllDerivationCertificate_of_positive_replacement`, `paper_theorem4_accept_all_unique_optimal_of_positive_replacement`, `Theorem4StatewiseAcceptAllRewardCertificate`, `theorem4PositiveReplacementDerivationCertificate_of_statewise_accept_all_reward`, `paper_theorem4_accept_all_unique_optimal_of_statewise_accept_all_reward`, `Theorem4GlobalStatewiseAcceptAllRewardCertificate`, `theorem4StatewiseAcceptAllRewardCertificate_of_global_statewise_accept_all_reward`, `paper_theorem4_accept_all_unique_optimal_of_global_statewise_accept_all_reward`, `Theorem4StrictLocalImprovementCertificate`, `acceptAllDynamic_unique_optimal_of_strict_local_improvements`, `paper_theorem4_accept_all_unique_optimal_of_strict_local_improvements`, `Theorem4MeasurableStrictLocalImprovementCertificate`, `acceptAllDynamic_measurable_unique_optimal_of_strict_local_improvements`, `theorem4GlobalStatewiseAcceptAllRewardCertificate_of_measured_reward_improvements`, `Theorem4MeasuredAggregateAcceptAllRewardCertificate`, `theorem4GlobalStatewiseAcceptAllRewardCertificate_of_measured_aggregate_improvements`, `Theorem4MeasuredAggregateStrictLocalImprovementCertificate`, `theorem4StrictLocalImprovementCertificate_of_measured_aggregate_strict_improvements`, `paper_theorem4_accept_all_unique_optimal_of_measured_aggregate_strict_local_improvements`, `Theorem4MeasuredAggregateFeasibleStrictLocalImprovementCertificate`, `theorem4MeasurableStrictLocalImprovementCertificate_of_measured_aggregate_feasible_strict_improvements`, `paper_theorem4_measurable_accept_all_unique_optimal_of_measured_aggregate_feasible_strict_local_improvements`, `replaceDynamicPolicyState`, `gn21MeasuredAggregateDynamicStateReward`, `gn21MeasuredAggregateDynamicStateReward_zero`, `gn21MeasuredAggregateDynamicStateReward_one`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_interval_density`, `paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_interval_density`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_lower_interval_density`, `paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_lower_interval_density`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_tail_interval_density`, `paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_reject_long_withDensity`, `paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_accept_middle_withDensity`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_tail_withDensity`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_interval_density`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_interval_density`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity`, `paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_tail_interval_density`, `GN21SurgeIntervalEndpointBridgeData`, `GN21NonsurgeIntervalEndpointBridgeData`, `GN21SurgeEndpointBridgeData`, `GN21NonsurgeEndpointBridgeData`, `Theorem4Lemma910IntervalBridgeCertificate`, `Theorem4Lemma910EndpointBridgeCertificate`, `Theorem4ShapeDerivationEndpointBridgeCertificate`, `Theorem4ShapeDerivationStatewiseImprovementCertificate`, `Theorem4ShapeDerivationStatewiseImprovementCertificate.of_all_shape_replacements`, `Theorem4ShapeEndpointSelectionCertificate`, `Theorem4ShapeEndpointSelectionCertificate.of_shape_derivation`, `Theorem4ShapeEndpointSelectionCertificate.of_shape_derivation_endpoint_bridges`, `Theorem4ShapeDerivationEndpointBridgeCertificate.of_statewise_improvements`, `Theorem4ShapeDerivationEndpointBridgeCertificate.of_statewise_improvement_certificate`, `Theorem4Lemma910EndpointBridgeCertificate.of_shape_endpoint_selection`, `theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate_of_lemma910_interval_bridges`, `theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_lemma910_interval_bridges`, `theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate_of_lemma910_endpoint_bridges`, `theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_lemma910_endpoint_bridges`, `theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate_of_shape_endpoint_selection`, `theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_shape_endpoint_selection`, `paper_theorem4_accept_all_unique_optimal_of_shape_endpoint_selection`, `paper_theorem4_accept_all_unique_optimal_of_shape_derivation_endpoint_bridges`, `paper_theorem4_accept_all_unique_optimal_of_shape_derivation_endpoint_bridge_certificate`, `paper_theorem4_accept_all_unique_optimal_of_shape_derivation_statewise_improvements`, `paper_theorem4_accept_all_unique_optimal_of_shape_derivation_statewise_improvement_certificate`, `paper_theorem4_accept_all_unique_optimal_of_all_shape_replacements_statewise_improvements`, `Theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate`, `theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_statewise_strict_improvements`, `Theorem4StructuralPolicyCertificate`, `paper_theorem4_dynamic_structural_policy_of_certificate` | conditional | `MainTheorems.lean` | The source endpoint is exposed from an explicit structural policy certificate, the pure logic routing from Lemma 5 policy forms to Theorem 4 surge/non-surge shape alternatives is closed, canonical interval policies have direct Theorem 4 shape facts, non-accept-all structural shapes now split into the four endpoint-selection cases used by the source proof, feasible reject-long/reject-short/accept-middle/reject-middle shapes canonicalize to measured endpoint primitives, state-specific allowed-replacement constructors package the canonical Lemma 5 replacement policies into the dependent Theorem 4 shape data, source-facing non-surge/surge replacement data types feed the all-optimal replacement certificate, and a packaged allowed-replacement statewise-improvement certificate combines replacement data, feasibility, and the four endpoint-improvement cases. There is a closer Lemma 5-style shape-derivation certificate that mechanically assembles Theorem 4, constructs the four-case endpoint-selection certificate from feasibility and the four endpoint bridges, and directly produces accept-all unique optimality from raw arguments, the packaged endpoint-bridge certificate, or the source-facing statewise-improvement certificate. All-optimal Lemma 5 replacement data now choose a structural optimum internally and feed the same Theorem 4 routes, so the source proof no longer needs a separate preselected optimum/replacement package. The positive-form special case gives accept-all unique optimality, statewise positive Lemma 5 replacement certificates feed that accept-all derivation through local continuation optimality, statewise accept-all reward comparisons instantiate the replacement interface, global statewise accept-all reward improvements derive accept-all optimality internally, and strict local improvements now also rule out every optimal non-accept-all policy. The feasible-measurable strict-local route restricts both optimality and local replacements to the source policy domain while still deriving accept-all measurable IC. The measured-reward and measured aggregate constructors let Lemma 6-style `Q,T,W` comparisons feed either the global comparison route or the stricter local-improvement route; the uniform statewise aggregate wrapper with state-specific unfolding lemmas removes duplicate state bookkeeping, Lemma 9/10 upper-endpoint, finite lower-endpoint, unbounded-tail, and two-sided middle-rejection endpoint movements now feed the surge and non-surge statewise strict aggregate improvement interfaces under primitive-identification assumptions, with concrete with-density replacement-policy specializations and finite positive-density current/replacement nondegeneracy constructors for all four Theorem 4 shape cases: non-surge reject-long and accept-middle, and surge reject-short and reject-middle. The generalized endpoint bridge plus shape-endpoint-selection certificates package those sides into the measured strict-local interface consumed by Theorem 3 and now directly produce the measured strict-local certificate and accept-all uniqueness endpoint for Theorem 4. The feasible accept-all-bound wrappers for all four shape cases now preserve the measurable feasible-policy domain, and the all-measurable replacement constructor feeds Lemma 5 replacement data into the same statewise-improvement certificate. The interval-density primitives and positive replacements are now realized by actual upper/lower endpoint, tail, and reject-middle policies under `volume.withDensity`; it remains to discharge arbitrary-optimal-policy endpoint selection for the continuous model. |
| Theorem 2, multiplicative pricing not IC and optimal policy shapes | `MultiplicativeNotICCertificate`, `paper_theorem2_multiplicative_not_ic_of_witness`, `MultiplicativePolicyShapeCertificate`, `paper_theorem2_multiplicative_policy_shape_of_certificate` | conditional | `MainTheorems.lean` | The endpoint wrappers are closed from explicit profitable-deviation and policy-shape certificates; constructing those certificates from the continuous model remains open. |
| Theorem 3, structured IC pricing | `structuredSurgePrice`, `ctmcStructuredSurgePrice`, `ctmcDynamicSwitchProb`, `ctmcStructuredDynamicSurgePrice`, `ctmcStructuredDynamicSurgePrice_price_form`, `paper_theorem3_structured_price_uses_lemma2_switch_probability`, `paper_theorem3_structured_price_closed_form`, `theorem3FeasibilityThresholdC`, `paper_theorem3_feasibility_numerator_pos_of_positive_pieces`, `paper_theorem3_feasibility_denominator_pos_of_positive_pieces`, `paper_theorem3_scaled_denominator_pos_of_positive_pieces`, `paper_theorem3_feasibility_numerator_le_scaled_den_of_nonneg_pieces`, `paper_theorem3_feasibility_thresholdC_mem_Ico`, `paper_theorem3_feasibility_thresholdC_mem_Ico_of_positive_pieces`, `paper_theorem3_feasibility_thresholdC_mem_Ico_acceptAll_of_measured_primitives_closed`, `theorem3NonsurgeZRatio`, `theorem3NonsurgeZRatio_accounting`, `lemma10StructuredBounds_of_theorem3_ratio`, `lemma10StructuredBounds_acceptAll_of_theorem3_ratio_measured`, `theorem3NonsurgeParameters_of_theorem3_ratio`, `theorem3SurgeMultiplierFromRatio`, `theorem3SurgeZFromRatio`, `theorem3SurgeRatio_accounting`, `theorem3SurgeRatio_denominator_pos`, `theorem3SurgeMultiplierFromRatio_gt_R1`, `theorem3SurgeZFromRatio_pos`, `paper_lemma9_structured_bounds_feasible_positive_of_positive_primitives`, `theorem3SurgeParameters_exist_of_lemma9_final_signs`, `theorem3SurgeParameters_exist_of_lemma9_positive_primitives`, `theorem3StructuredParameters_exist_of_ratio_and_lemma9_final_signs`, `theorem3StructuredParameters_exist_of_ratio_and_lemma9_positive_primitives`, `theorem3_acceptAll_measured_primitives_scalar_conditions`, `theorem3_acceptAll_measured_primitives_scalar_conditions_positive_primitives`, `StructuredPricingICCertificate`, `structuredPricingICCertificate_of_ctmc_structured_prices`, `paper_theorem3_structured_prices_ic_of_certificate`, `paper_theorem3_ctmc_structured_prices_ic_of_accept_all_unique_optimal`, `paper_theorem3_ctmc_structured_prices_ic_of_statewise_accept_all_optima`, `paper_theorem3_ctmc_structured_prices_ic_of_theorem4_accept_all_derivation`, `paper_theorem3_ctmc_structured_prices_ic_of_positive_replacement_derivation`, `paper_theorem3_ctmc_structured_prices_ic_of_strict_local_improvements`, `paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_positive_replacement`, `paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_strict_local_improvements`, `paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_statewise_accept_all_reward`, `paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_global_statewise_accept_all_reward`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_global_statewise_accept_all_reward`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_accept_all_reward`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_strict_local_improvements`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_strict_local_improvements_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_lemma910_interval_bridges`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_lemma910_endpoint_bridges`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_endpoint_selection`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_endpoint_bridge_certificate`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_statewise_improvement_certificate`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_statewise_improvement_certificate_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_replacement_statewise_improvements_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_all_shape_replacements_statewise_improvements_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_allowed_replacement_data_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_global_statewise_accept_all_reward`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_measured_aggregate_strict_local_improvements`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_measured_aggregate_strict_local_improvements_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_shape_derivation_statewise_improvement_certificate`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_shape_derivation_statewise_improvement_certificate_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_allowed_replacement_data_of_lemma9_positive_primitives` | conditional | `MainTheorems.lean` | The paper price form is tied directly to the Lemma 2 CTMC switch probability and expanded closed form; there is a concrete two-state CTMC dynamic price family; the source `C` threshold has compiled positivity-piece, measured accept-all `[0,1)`, and numerator-bound factorization bridges; the non-surge `C < R1/R2 < 1` to Lemma 10 bounds step is formalized; Lemma 9 surge-ratio feasibility now has a direct primitive-positivity bridge, so the strict-local and packaged statewise measured endpoints can avoid the stronger final-sign assumptions; both surge and non-surge `m_i,z_i` accounting packages are exposed and assembled into two-state parameter arrays with source sign constraints and target scaled-earning identities; and the accept-all IC endpoint can be invoked from unique optimality, statewise accept-all optimality, positive-form Theorem 4 accept-all derivation, statewise positive Lemma 5 replacement derivation, strict local improvement certificates, statewise accept-all reward comparison, global statewise accept-all reward improvements, measured aggregate accept-all improvements, the combined Lemma 9/10 interval bridge certificate, the generalized endpoint bridge certificate, the four-case Theorem 4 shape-endpoint-selection certificate, the paper-ordered shape-derivation endpoint-bridge/statewise-improvement certificates, Lemma 5 shape-replacement data, all-optimal Lemma 5 shape-replacement data, or packaged allowed-replacement source-boundary data. There is now a measured endpoint that constructs `m,z` first and concludes IC for `gn21MeasuredCTMCStructuredDynamicReward` once the measured global reward-improvement proof, the measured aggregate `Q,T,W` improvement proof, the measured aggregate strict-local improvement proof, the combined interval bridge certificate, generalized endpoint bridge certificate, four-shape endpoint-selection certificate, shape-derivation endpoint-bridge/statewise-improvement certificate, shape-replacement statewise-improvement package, all-optimal shape-replacement statewise-improvement package, or allowed-replacement source-boundary package is supplied for those constructed prices; accept-all-primitive endpoints specialize `T_i,Q_i` and share scalar-conditions helpers that derive the needed positivity and direct Lemma 9 feasibility facts from measure/CTMC assumptions for the global, strict-local, packaged statewise-certificate, and packaged allowed-replacement routes. Still needs the continuous proof selecting the realized endpoint policies from arbitrary optimal policies under the Lemma 9-10 derivative signs. |
| Auxiliary finite dynamic policy support | `paper_aux_finite_dynamic_pricing_ic_of_greedy`, `paper_aux_finite_dynamic_pricing_not_ic_of_profitable_deviation` | formalized | `MainTheorems.lean` | None; these are library-level finite MDP support lemmas, not source theorem substitutes. |

Additional bridge-adapter declarations now connect the concrete endpoint
calculus to the top-level routes without extra structure plumbing:
`Theorem4ShapeReplacementDerivationCertificate`,
`theorem4ShapeDerivationCertificate_of_shape_replacement`,
`paper_theorem4_dynamic_structural_policy_of_shape_replacement`,
`theorem4NonsurgeAllowedReplacement_positive_acceptAll`,
`theorem4NonsurgeAllowedReplacement_rejectLong`,
`theorem4NonsurgeAllowedReplacement_acceptMiddle`,
`theorem4SurgeAllowedReplacement_positive_acceptAll`,
`theorem4SurgeAllowedReplacement_rejectShort`,
`theorem4SurgeAllowedReplacement_rejectMiddle`,
`Theorem4NonsurgeAllowedReplacementData`,
`Theorem4SurgeAllowedReplacementData`,
`Theorem4AllOptimalShapeReplacementDerivationCertificate.of_allowed_replacement_data`,
`Theorem4AllOptimalShapeReplacementDerivationCertificate`,
`theorem4ShapeReplacementDerivationCertificate_of_all_shape_replacements`,
`theorem4ShapeDerivationCertificate_of_all_shape_replacements`,
`paper_theorem4_dynamic_structural_policy_of_all_shape_replacements`,
`Theorem4AllowedReplacementStatewiseImprovementCertificate`,
`Theorem4AllowedReplacementEndpointBridgeCertificate`,
`Theorem4AllowedReplacementStatewiseImprovementCertificate.of_endpoint_bridges`,
`Theorem4ShapeDerivationStatewiseImprovementCertificate.of_allowed_replacement_data`,
`paper_theorem4_accept_all_unique_optimal_of_allowed_replacement_data`,
`paper_theorem4_accept_all_unique_optimal_of_allowed_replacement_endpoint_bridges`,
`Theorem4ShapeDerivationStatewiseImprovementCertificate.of_shape_replacement`,
`Theorem4ShapeDerivationStatewiseImprovementCertificate.of_all_shape_replacements`,
`paper_theorem4_accept_all_unique_optimal_of_shape_replacement_statewise_improvements`,
`paper_theorem4_accept_all_unique_optimal_of_all_shape_replacements_statewise_improvements`,
`Theorem4MeasurableShapeDerivationCertificate`,
`Theorem4AllMeasurableOptimalShapeReplacementDerivationCertificate`,
`theorem4MeasurableShapeDerivationCertificate_of_all_measurable_shape_replacements`,
`paper_theorem4_measurable_dynamic_structural_policy_of_shape_derivation`,
`paper_theorem4_measurable_dynamic_structural_policy_of_all_shape_replacements`,
`gn21SurgeStatewiseStrictAggregateImprovement`,
`gn21NonsurgeStatewiseStrictAggregateImprovement`,
`gn21SurgeFeasibleStatewiseStrictAggregateImprovement`,
`gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement`,
`GN21SurgeEndpointBridgeData.of_statewise_strict_aggregate_improvement`,
`GN21NonsurgeEndpointBridgeData.of_statewise_strict_aggregate_improvement`,
`Theorem4MeasuredAggregateFeasibleStatewiseStrictLocalImprovementCertificate`,
`theorem4MeasuredAggregateFeasibleStatewiseStrictLocalImprovementCertificate_of_measurable_shape_statewise_improvements`,
`theorem4MeasuredAggregateFeasibleStrictLocalImprovementCertificate_of_measurable_shape_statewise_improvements`,
`Theorem4ShapeDerivationStatewiseImprovementCertificate`,
`Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate`,
`Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate.of_all_measurable_shape_replacements`,
`Theorem4ShapeDerivationStatewiseImprovementCertificate.of_statewise_improvements`,
`Theorem4ShapeDerivationEndpointBridgeCertificate.of_statewise_improvements`,
`Theorem4ShapeDerivationEndpointBridgeCertificate.of_statewise_improvement_certificate`,
`paper_theorem4_accept_all_unique_optimal_of_shape_derivation_statewise_improvements`,
`paper_theorem4_accept_all_unique_optimal_of_shape_derivation_statewise_improvement_certificate`,
and
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_statewise_improvement_certificate`,
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_shape_derivation_statewise_improvement_certificate`,
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_statewise_improvement_certificate_of_lemma9_positive_primitives`,
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_shape_derivation_statewise_improvement_certificate_of_lemma9_positive_primitives`,
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_allowed_replacement_data_of_lemma9_positive_primitives`,
`theorem3AcceptAllFeasibleStrictLocalCertificate_of_measurable_shape_statewise_improvements`,
`Theorem3AcceptAllMeasurableShapeStatewiseImprovementSourceAssumptions`,
`paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_statewise_improvements_source_assumptions`,
`Theorem3AcceptAllMeasurableShapeReplacementStatewiseImprovementSourceAssumptions`,
`paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_replacement_statewise_improvements_source_assumptions`,
`Theorem4MeasurableEndpointCurrentBoundsSelectionCertificate`,
`Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate.of_endpoint_current_bounds_selection`,
`theorem4MeasuredAggregateFeasibleStrictLocalImprovementCertificate_of_endpoint_current_bounds_selection`,
`paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_selection`,
`Theorem3AcceptAllMeasurableEndpointCurrentBoundsSelectionSourceAssumptions`,
`paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_selection_source_assumptions`,
`Theorem4NonsurgeMeasurableReplacementData`,
`Theorem4SurgeMeasurableReplacementData`,
`Theorem4AllMeasurableOptimalShapeReplacementDerivationCertificate.of_allowed_replacement_data`,
`Theorem4MeasurableEndpointCurrentBoundsAllowedReplacementSelectionCertificate`,
`Theorem4MeasurableEndpointCurrentBoundsSelectionCertificate.of_allowed_replacement_data`,
`GN21WithDensityAcceptAllSupport`,
`GN21NonsurgeRejectLongCurrentBoundsEndpointData.of_acceptAll_support`,
`GN21NonsurgeAcceptMiddleCurrentBoundsEndpointData.of_acceptAll_support`,
`GN21SurgeRejectShortCurrentBoundsEndpointData.of_acceptAll_support`,
`GN21SurgeRejectMiddleLoCurrentBoundsEndpointData.of_acceptAll_support`,
`GN21SurgeRejectMiddleHiCurrentBoundsEndpointData.of_acceptAll_support`,
`continuous_gn21SwitchProb`,
`continuous_ctmcStructuredSurgePrice`,
`continuousAt_mul_density_of_continuous`,
`stronglyMeasurableAtFilter_mul_density_of_continuous`,
`intervalIntegrable_mul_density_of_continuous`,
`GN21EndpointProductContinuityData`,
`GN21EndpointProductContinuityData.of_ctmcStructured`,
`GN21FiniteEndpointProductCalculusData`,
`GN21FiniteEndpointProductCalculusData.of_ctmcStructured`,
`paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_allowed_replacement_selection`,
`Theorem3AcceptAllMeasurableEndpointCurrentBoundsAllowedReplacementSourceAssumptions`,
`paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_allowed_replacement_source_assumptions`,
`theorem3AcceptAllStructuredParameterEvidence`,
`theorem3MeasuredStructuredICConclusion`,
`Theorem4StatewiseAcceptAllWeakRewardCertificate`,
`theorem4StatewiseAcceptAllWeakRewardCertificate_of_global_statewise_accept_all_reward`,
`paper_theorem4_accept_all_optimal_of_statewise_accept_all_weak_reward`,
`Theorem4MeasuredAggregateWeakAcceptAllRewardCertificate`,
`theorem4StatewiseAcceptAllWeakRewardCertificate_of_measured_aggregate_weak_improvements`,
`theorem4MeasuredAggregateWeakAcceptAllRewardCertificate_of_measured_aggregate_improvements`,
`paper_theorem3_ctmc_structured_prices_ic_of_accept_all_optimal`,
`paper_theorem3_ctmc_structured_prices_ic_of_statewise_accept_all_weak_reward`,
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_statewise_accept_all_weak_reward_of_lemma9_positive_primitives`,
`theorem3AcceptAllWeakRewardCertificate`,
`theorem3AcceptAllWeakRewardCertificate_of_global_statewise_accept_all_reward`,
`theorem3AcceptAllWeakRewardCertificate_of_measured_aggregate_weak_reward`,
`theorem3AcceptAllWeakRewardCertificate_of_measured_aggregate_reward`,
`paper_theorem3_measured_structured_ic_prices_of_weak_reward`,
`Theorem3AcceptAllWeakRewardSourceAssumptions`,
`paper_theorem3_measured_structured_ic_prices_of_weak_reward_source_assumptions`,
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_positive_replacement_of_lemma9_positive_primitives`,
`theorem3AcceptAllPositiveReplacementCertificate`,
`theorem3AcceptAllPositiveReplacementCertificate_of_statewise_accept_all_reward`,
`paper_theorem3_measured_structured_ic_prices_of_positive_replacement`,
`Theorem3AcceptAllPositiveReplacementSourceAssumptions`,
`paper_theorem3_measured_structured_ic_prices_of_positive_replacement_source_assumptions`,
`theorem3AcceptAllAllowedReplacementCertificate`,
`theorem3AcceptAllAllowedReplacementCertificate_of_endpoint_bridges`,
`Theorem3AcceptAllAllowedReplacementSourceAssumptions`,
`paper_theorem3_measured_structured_ic_prices_of_source_assumptions`,
`Theorem3AcceptAllAllowedReplacementEndpointBridgeSourceAssumptions`,
`paper_theorem3_measured_structured_ic_prices_of_endpoint_bridge_source_assumptions`,
with the unbundled raw-argument variant
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_statewise_improvements`
and its positive-primitives counterpart
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_statewise_improvements_of_lemma9_positive_primitives`;
the Lemma 5 replacement-data version is
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_replacement_statewise_improvements_of_lemma9_positive_primitives`;
the all-optimal replacement-data version is
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_all_shape_replacements_statewise_improvements_of_lemma9_positive_primitives`;
the packaged allowed-replacement source-boundary version is
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_allowed_replacement_data_of_lemma9_positive_primitives`.
The first concrete shape-level endpoint bridge is also exposed as
`paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_reject_long_withDensity_of_shape`,
with an accept-all-bound variant
`paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_reject_long_withDensity_of_shape_acceptAll_bounds`
that derives the current Lemma 10 bounds and Remark 4 positivity conditions,
with the corresponding accept-middle bridge
`paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_accept_middle_withDensity_of_shape`
and accept-all-bound variant
`paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_accept_middle_withDensity_of_shape_acceptAll_bounds`;
the surge reject-short bridge
`paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_tail_withDensity_of_shape`
and accept-all-bound variant
`paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_tail_withDensity_of_shape_acceptAll_bounds`
do the same for the tail case, and
`paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity_of_shape`
plus
`paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity_of_shape`
cover the two reject-middle endpoint moves, with accept-all-bound variants
`paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity_of_shape_acceptAll_bounds`
and
`paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity_of_shape_acceptAll_bounds`.
Their feasible-measurable counterparts are also compiled:
`paper_theorem4_nonsurge_feasible_statewise_strict_aggregate_improvement_of_lemma10_reject_long_withDensity_of_shape_acceptAll_bounds`,
`paper_theorem4_nonsurge_feasible_statewise_strict_aggregate_improvement_of_lemma10_accept_middle_withDensity_of_shape_acceptAll_bounds`,
`paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_tail_withDensity_of_shape_acceptAll_bounds`,
`paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity_of_shape_acceptAll_bounds`,
and
`paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity_of_shape_acceptAll_bounds`;
the current-bounds-data variants
`paper_theorem4_nonsurge_feasible_statewise_strict_aggregate_improvement_of_lemma10_reject_long_withDensity_of_shape_current_bounds_data`,
`paper_theorem4_nonsurge_feasible_statewise_strict_aggregate_improvement_of_lemma10_accept_middle_withDensity_of_shape_current_bounds_data`,
`paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_tail_withDensity_of_shape_current_bounds_data`,
`paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity_of_shape_current_bounds_data`,
and
`paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity_of_shape_current_bounds_data`
remove duplicated `Q,T,W`, denominator, and Remark 4 plumbing.  The endpoint
data packages
`GN21NonsurgeRejectLongCurrentBoundsEndpointData`,
`GN21NonsurgeAcceptMiddleCurrentBoundsEndpointData`,
`GN21SurgeRejectShortCurrentBoundsEndpointData`,
`GN21SurgeRejectMiddleLoCurrentBoundsEndpointData`,
`GN21SurgeRejectMiddleHiCurrentBoundsEndpointData`, and
`GN21SurgeRejectMiddleCurrentBoundsEndpointData` feed the compiled
`Theorem4MeasurableEndpointCurrentBoundsSelectionCertificate` route to Theorem
4 and Theorem 3.

## Remaining Work

The fastest source-faithful route is continuous, not finite.  The reusable
two-state CTMC transition-kernel closed form is now in place, including strict
switch positivity, `q(u)<lambda*u`, `q(u)/u` monotonicity, and the zero-time
limit needed by Appendix D, plus the `lambda*t - q(t)` strict positivity and
derivative monotonicity used in Remark 4. Theorem 1 has
the Step 1 equal-utilization swap, Step 2 boundary add/remove algebra, and a
closed Step 1/2/3 assembly theorem and canonical measurable threshold-set
infrastructure. Lemma 1/Lemma 3 deterministic algebra is
closed at the measured-formula level. Appendix D's derivative kernel, affine
canonical response, Lemma 6 strict-sign transfer, Lemma 7
derivative-numerator calculation, canonical CTMC quasi-convex/quasi-concave
response shapes, Remark 4 maximization, measured current-policy tightening
from accept-all bounds, strict measured-positivity support, structured-price
algebra, structured derivative-kernel positivity from CTMC
linearization, and Lemma 9/10 interval feasibility bridges are represented;
Theorem 1 now has a
constructor from Step 1/2/3 obligations to the threshold certificate interface,
Lemma 5 has canonical measurable interval-policy representatives, policy-form
wrappers, derivative-shape witnesses from Lemmas 7-8, canonical replacement
constructors for all five shape cases, optimality extraction from strict
replacement certificates, and the reusable quasi-convex/quasi-concave
between-endpoint facts. Theorem 4 now has the pure routing from Lemma 5 policy
forms into the source surge/non-surge shape alternatives plus a positive-form
accept-all uniqueness interface, a statewise positive-replacement route into
that interface, a statewise accept-all reward interface, and a global statewise
reward interface that derives accept-all optimality, plus a strict-local
interface that rules out non-accept-all optima, state-specific allowed
replacement constructors for the Theorem 4 shape data, source-facing
replacement-data cases for the all-optimal interface, and measured constructors for
the actual two-state reward formula; the measured aggregate strict-local route
now has a uniform statewise replacement wrapper, measured upper-endpoint
interval-policy, lower-endpoint interval-policy, and unbounded-tail primitive
realization for `Q,T,W`, two-piece middle-rejection realization, positive
endpoint replacement realization, Lemma 9/10 upper/lower/tail endpoint bridges
for both states, Lemma 9 reject-middle lower/upper cutoff bridges for the surge
  state, concrete with-density replacement-policy specializations for both
  surge reject-middle cutoff moves with finite positive-density nondegeneracy
  constructors for both current and replacement middle-rejection policies,
  concrete tail left-replacement realizations and current/replacement
  nondegeneracy constructors for the surge reject-short case, non-surge
  reject-long and accept-middle current/replacement nondegeneracy constructors,
  concrete with-density strict-local bridge wrappers for all four endpoint
  shape cases, and a generalized endpoint bridge certificate feeding the
  measured strict-local interface, with a direct Theorem 4 accept-all
  uniqueness endpoint from the four-case shape-selection certificate and a
  direct Theorem 4 endpoint from the Lemma 5-style shape derivation,
  feasibility, and the four endpoint bridges, plus a source-facing
  statewise-improvement certificate and an all-optimal replacement interface
  that package the remaining analytic selection obligations without requiring
  the caller to preselect a structural optimum, plus a single
  allowed-replacement source-boundary certificate bundling optimum existence,
  feasibility, replacement cases, and endpoint improvements.  The endpoint
  current-bounds selection certificate now packages the feasible endpoint data
  cases and compiles directly to Theorem 4 measurable accept-all uniqueness;
  its source-facing allowed-replacement variant also derives feasible
  measurability of the canonical Lemma 5 replacements internally.
  Theorem 3 now has a
concrete CTMC structured-price endpoint that consumes all of those interfaces,
including integrated ratio-to-parameters-to-IC theorems for the global
statewise reward comparisons, measured aggregate strict-local improvements,
the measured CTMC structured reward, and the measured accept-all primitives
with scalar positivity and direct Lemma 9 primitive-feasibility side
conditions derived for the global, strict-local, and packaged
statewise-certificate routes, plus a
direct weak-reward IC wrapper whose final obligation is only weak statewise
accept-all improvement for the constructed prices, a positive-replacement
source wrapper whose final obligation is the Lemma 9/10 positive Lemma 5
replacement proof for the constructed prices, current-bounds source wrappers
that accept either scaled accounting equations or measured reward-rate
equalities for the fixed state, plus
a direct ratio-to-IC route from the four-case Theorem 4 shape-endpoint-selection
certificate and the paper-ordered shape-derivation endpoint-bridge
certificate, plus a route that accepts the raw statewise improvement
existentials produced by the concrete endpoint lemmas and a packaged
statewise-improvement certificate for the same source boundary, and a route
that consumes all-optimal Lemma 5 replacement data directly or the packaged
allowed-replacement source-boundary certificate, and the current regular
allowed-policy-form route that consumes measurable Lemma 5 policy-form
classification plus regular endpoint packages directly.
Proposition 3.1 has a measurable continuous IC endpoint. Next: instantiate the
regular allowed-policy-form source-facing endpoint layer for arbitrary open measurable
optimal policies by proving the regularity theorem that derives the measurable
Lemma 5 allowed policy forms, chooses the relevant upper, lower, tail, or
middle-rejection endpoint move, and discharges the remaining density,
integrability, finite-mass, and current-bound fields of
`Theorem4MeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsCertificate`.
Concrete
with-density replacement policies, primitive equalities, finite positive-density
current/replacement nondegeneracy, accept-all density support constructors,
continuous-density endpoint calculus helpers, feasible-domain preservation, and
Lemma 9/10 current-bound data plumbing are now available through regular
endpoint records for all four Theorem 4 shape cases, with reject-middle split
into lower- and upper-cutoff endpoint variants; the older regular-selection
route remains compiled for the variant that proves ordinary allowed Lemma 5
  replacement data explicitly.  Shared source regularity is now factored into
  `GN21RegularEndpointSharedSourceData`, so the final selector can focus on
  cutoff-local density positivity, tail integrability, and source current
  bounds.  The source current-bound records can now be built with
  `GN21NonsurgeLemma10AcceptAllAggregateSourceData.of_acceptAll_tightening` and
  `GN21SurgeLemma9AcceptAllAggregateSourceData.of_acceptAll_tightening`, which
  apply the measured Remark 4 tightening lemmas from accept-all moving-state
  bounds to the current moving-state policy.  The shared-source package also
  has shape-specific current-mass positivity lemmas for reject-long,
  accept-middle, reject-short, and reject-middle policies.
Then finish Theorem 1's
global threshold-existence
compactness/continuity argument and the two-state renewal law-of-large-numbers
bridge.
