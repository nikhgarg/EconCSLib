# GN21 Next-Agent Handoff

## Scope

Stay on `papers/GN21DriverSurgePricing`.  The current target is to close the
Driver Surge Pricing Theorem 3 IC route, not to audit other papers.

## Build State

As of this handoff, both `lake build GN21DriverSurgePricing.MainTheorems` and
`lake build GN21DriverSurgePricing.PaperInterface` pass after the newest Lemma 1-3 IID-cycle
strong-law work, Lemma 9 envelope/slack source-boundary reduction, and the
current payment nonnegativity derivation.  The latest checked build also passes
after adding the generalized interval/ray Lemma 5 descent domain and the
global endpoint-path calculus used by Lemma 5 Step 2, plus the direct AE and
light existence normalized-mass ratio endpoints for Theorem 3.

Useful checks:

```bash
lake build GN21DriverSurgePricing
latexmk -pdf DependencyDAG.tex   # from papers/GN21DriverSurgePricing
git diff --check -- papers/GN21DriverSurgePricing skills/econcs-formalizer
```

## Current Public Theorem 3 Boundary

For the source-faithful paper path, prefer the normalized-mass bracket
middle-cutoff fixed-state-equality route:

```lean
PaperInterface.theorem3_structured_measurable_ic_ae_unique_of_bracket_eq_middle_cutoff_fixed_state_eq_normalized_mass_ratio_source
PaperInterface.theorem3_structured_measurable_ic_of_bracket_eq_middle_cutoff_fixed_state_eq_normalized_mass_ratio_source
```

It derives the scalar `R1` positivity/order facts from `R1 = rho * R2`,
`R2 > 0`, and `C < rho < 1`, and derives the positive accept-all measure
fields from `singleStateTripMass (mu i) acceptAllPolicy = 1`.  The per-price
selection now returns
`GN21Theorem3FixedResponseOneThresholdBracketEqMiddleCutoffFixedStateEqSourceExistenceData`,
so the local endpoint certificate is built internally from Lemma 6 bracket
source data, shared endpoint regularity, and the Lemma 9/10 fixed-state
pointwise/reward-rate equalities.  The remaining hard obligation is to prove
those bracket-source and fixed-state equality records from the paper's
algebra, not to assemble the endpoint record by hand.

If the source proof supplies the weaker one-sided rejected-complement
comparison instead of common fixed-state equality, use the finite-or-infinite
aggregate-cross route.  The aggregate-cross boundary now also has
normalized-mass public wrappers:

```lean
PaperInterface.theorem3_structured_measurable_ic_ae_unique_of_finite_or_infinite_branch_surge_cross_fixed_transfer_normalized_mass_ratio_source
PaperInterface.theorem3_structured_measurable_ic_of_finite_or_infinite_branch_surge_cross_fixed_transfer_normalized_mass_ratio_source
```

These consume the aggregate-cross source package directly and derive positive
accept-all measure from `singleStateTripMass (mu i) acceptAllPolicy = 1`; use
the pointwise-upper-transfer route only when Lean must first derive the
aggregate cross-ratio from the paper's rejected-tail comparison.

## Latest Lemma 5 Domain Update

The bounded finite interval domain is now explicitly just the inner-regularity
seed domain.  For source closeout, use the generalized interval/ray domain:

```lean
GN21GeneralizedIntervalComponent
GN21GeneralizedIntervalPolicy
GN21FiniteIntervalPolicy.toGeneralizedIntervalPolicy
exists_gn21GeneralizedIntervalPolicy_reward_close_below
lemma5OptimizerReplacementCertificate_of_generalizedIntervalPolicy_descent_and_maximizer
Lemma5GeneralizedIntervalPolicyDescentMaximizerData
exists_generalizedIntervalPolicy_eq_of_lemma5PolicyForm_of_subset_acceptAll
GN21GeneralizedIntervalPolicy.lemma5ShapeComplexity
lemma5OptimizerReplacementCertificate_of_generalizedIntervalPolicy_canonical_dominance_and_maximizer
Lemma5GeneralizedIntervalPolicyCanonicalDominanceMaximizerData
lemma5OptimizerReplacementCertificate_of_generalizedIntervalPolicy_policy_canonical_dominance_and_maximizer
lemma5OptimizerReplacementCertificate_of_policy_canonical_dominance_and_maximizer
Lemma5PolicyCanonicalDominanceMaximizerData
Lemma5PositiveResponseShapeData
Lemma5PositiveResponseShapeData.derivativeShapeWitness
Lemma5PositiveResponseShapeData.policyForm
Lemma5PositiveResponseShapeData.positive_zero_set_null
Lemma5PositiveResponseShapeData.policyAlmostEverywhereEq_positiveResponse_of_candidate_le
Lemma5PositiveResponseShapeData.policyFormAlmostEverywhere_of_candidate_le
Lemma5PositiveResponseShapeData.policyFormAlmostEverywhere_of_feasible_optimal
Lemma5PositiveResponseShapeData.marginalSetReward_lt_positiveResponsePolicy_of_not_policyFormAE
endpoint_path_le_of_hasDerivAt_nonneg_on_Icc
endpoint_path_lt_of_hasDerivAt_pos_on_Icc
endpoint_path_ge_of_hasDerivAt_nonpos_on_Icc
endpoint_path_gt_of_hasDerivAt_neg_on_Icc
lemma5_strictlyIncreasing_endpoint_sign_dichotomy
lemma5_strictlyDecreasing_gap_endpoint_sign_dichotomy
lemma5_strictQuasiConvex_middle_endpoint_signs_of_outer_nonpos
lemma5_strictQuasiConcave_gap_endpoint_sign_of_lower_nonneg
symmDiff_ioo_union_touching_subset_singleton
policyAlmostEverywhereEq_ioo_union_touching
lemma5_upper_endpoint_merge_reward_ge_of_endpoint_path
lemma5_upper_endpoint_merge_reward_gt_of_endpoint_path
lemma5_lower_endpoint_collapse_reward_ge_of_endpoint_path
lemma5_lower_endpoint_collapse_reward_gt_of_endpoint_path
lemma5_upper_endpoint_merge_reward_ge_of_endpoint_path_with_context
lemma5_upper_endpoint_merge_reward_gt_of_endpoint_path_with_context
lemma5_lower_endpoint_merge_reward_ge_of_endpoint_path_with_context
lemma5_lower_endpoint_merge_reward_gt_of_endpoint_path_with_context
lemma5_lower_endpoint_collapse_reward_ge_of_endpoint_path_with_context
lemma5_lower_endpoint_collapse_reward_gt_of_endpoint_path_with_context
lemma5_upper_endpoint_collapse_reward_ge_of_endpoint_path_with_context
lemma5_upper_endpoint_collapse_reward_gt_of_endpoint_path_with_context
GN21GeneralizedIntervalPolicy.singleBounded
GN21GeneralizedIntervalPolicy.twoBounded
GN21GeneralizedIntervalPolicy.empty
GN21GeneralizedIntervalPolicy.withComponent
GN21GeneralizedIntervalPolicy.withTwoComponents
GN21GeneralizedIntervalPolicy.withSingleBounded
GN21GeneralizedIntervalPolicy.withTwoBounded
GN21GeneralizedIntervalPolicy.policy_singleBounded
GN21GeneralizedIntervalPolicy.policy_twoBounded
GN21GeneralizedIntervalPolicy.policy_empty
GN21GeneralizedIntervalPolicy.policy_withComponent
GN21GeneralizedIntervalPolicy.policy_withTwoComponents
GN21GeneralizedIntervalPolicy.policy_withSingleBounded
GN21GeneralizedIntervalPolicy.policy_withTwoBounded
GN21GeneralizedIntervalPolicy.complexity_singleBounded
GN21GeneralizedIntervalPolicy.complexity_twoBounded
GN21GeneralizedIntervalPolicy.complexity_empty
GN21GeneralizedIntervalPolicy.complexity_withComponent
GN21GeneralizedIntervalPolicy.complexity_withTwoComponents
GN21GeneralizedIntervalPolicy.complexity_withSingleBounded
GN21GeneralizedIntervalPolicy.complexity_withTwoBounded
GN21GeneralizedIntervalListPolicy
GN21GeneralizedIntervalListPolicy.toGeneralizedIntervalPolicy
GN21GeneralizedIntervalListPolicy.toGeneralizedIntervalPolicy_policy
GN21GeneralizedIntervalListPolicy.toGeneralizedIntervalPolicy_complexity
GN21GeneralizedIntervalListPolicy.policy_nil
GN21GeneralizedIntervalListPolicy.policy_cons
GN21GeneralizedIntervalListPolicy.policy_pair_cons
GN21GeneralizedIntervalListPolicy.complexity_cons
GN21GeneralizedIntervalListPolicy.complexity_pair_cons
GN21GeneralizedIntervalListPolicy.policy_cons_eq_withComponent
GN21GeneralizedIntervalListPolicy.policy_pair_cons_eq_withTwoComponents
lemma5_list_bounded_bounded_upper_merge_step_of_endpoint_path
lemma5_list_bounded_bounded_upper_merge_strict_step_of_endpoint_path
lemma5_list_bounded_bounded_lower_merge_step_of_endpoint_path
lemma5_list_bounded_bounded_lower_merge_strict_step_of_endpoint_path
lemma5_list_bounded_lower_collapse_step_of_endpoint_path
lemma5_list_bounded_lower_collapse_strict_step_of_endpoint_path
lemma5_list_bounded_upper_collapse_step_of_endpoint_path
lemma5_list_bounded_upper_collapse_strict_step_of_endpoint_path
lemma5_list_bounded_rightRay_upper_merge_step_of_endpoint_path
lemma5_list_bounded_rightRay_upper_merge_strict_step_of_endpoint_path
lemma5_list_leftRay_bounded_lower_merge_step_of_endpoint_path
lemma5_list_leftRay_bounded_lower_merge_strict_step_of_endpoint_path
lemma5_list_leftRightRay_upper_merge_step_of_endpoint_path
lemma5_list_leftRightRay_upper_merge_strict_step_of_endpoint_path
lemma5_list_second_bounded_lower_collapse_step_of_endpoint_path
lemma5_list_second_bounded_lower_collapse_strict_step_of_endpoint_path
lemma5_list_second_bounded_upper_collapse_step_of_endpoint_path
lemma5_list_second_bounded_upper_collapse_strict_step_of_endpoint_path
lemma5_twoBounded_upper_merge_step_of_endpoint_path
lemma5_twoBounded_upper_merge_strict_step_of_endpoint_path
lemma5_withTwoBounded_upper_merge_step_of_endpoint_path
lemma5_withTwoBounded_upper_merge_strict_step_of_endpoint_path
lemma5_withTwoBounded_lower_merge_step_of_endpoint_path
lemma5_withTwoBounded_lower_merge_strict_step_of_endpoint_path
lemma5_singleBounded_lower_collapse_step_of_endpoint_path
lemma5_singleBounded_lower_collapse_strict_step_of_endpoint_path
lemma5_withSingleBounded_lower_collapse_step_of_endpoint_path
lemma5_withSingleBounded_lower_collapse_strict_step_of_endpoint_path
lemma5_withSingleBounded_upper_collapse_step_of_endpoint_path
lemma5_withSingleBounded_upper_collapse_strict_step_of_endpoint_path
lemma5_withBoundedRightRay_upper_merge_step_of_endpoint_path
lemma5_withBoundedRightRay_upper_merge_strict_step_of_endpoint_path
lemma5_withLeftRayBounded_lower_merge_step_of_endpoint_path
lemma5_withLeftRayBounded_lower_merge_strict_step_of_endpoint_path
lemma5_withLeftRightRay_upper_merge_step_of_endpoint_path
lemma5_withLeftRightRay_upper_merge_strict_step_of_endpoint_path
lemma5_withLeftRightRay_lower_merge_step_of_endpoint_path
lemma5_withLeftRightRay_lower_merge_strict_step_of_endpoint_path
measure_congr_policy_ae
singleStateTripMass_congr_policy_ae
singleStateTripTime_congr_policy_ae
singleStateTripPayment_congr_policy_ae
singleStateRenewalReward_congr_policy_ae
gn21ExitWeightIntegral_congr_policy_ae
gn21ScaledStateTime_congr_policy_ae
gn21ScaledStateEarning_congr_policy_ae
gn21MeasuredAggregateRewardPrimitives_congr_left_policy_ae
gn21MeasuredAggregateRewardPrimitives_congr_right_policy_ae
theorem4NonsurgeShapeRepresentative_of_allowed_lemma5_formAE
theorem4SurgeShapeRepresentative_of_allowed_lemma5_formAE
Lemma5FeasiblePolicyFormAlmostEverywhereData
Lemma5FeasiblePolicyFormAlmostEverywhereData.to_policyFormAlmostEverywhere
Lemma5FeasiblePolicyFormAlmostEverywhereData.acceptAllAlmostEverywhere_of_positive
paper_lemma5_fixed_response_policy_form_ae_of_response_shape
paper_lemma5_fixed_response_feasible_policy_form_ae_of_response_shape
paper_lemma5_marginal_optimizer_replacement_ae_of_response_shape
paper_lemma5_marginal_optimizer_replacement_of_response_shape
GN21MeasuredPairNondegenerate.congr_left_policy_ae
GN21MeasuredPairNondegenerate.congr_right_policy_ae
gn21MeasuredDynamicRewardFunctional_congr_left_policy_ae
gn21MeasuredDynamicRewardFunctional_congr_right_policy_ae
dynamicMeasurableOptimal_gn21MeasuredDynamicRewardFunctional_update_zero_of_policy_ae
dynamicMeasurableOptimal_gn21MeasuredDynamicRewardFunctional_update_one_of_policy_ae
gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement_congr_current_ae
gn21SurgeFeasibleStatewiseStrictAggregateImprovement_congr_current_ae
Theorem4NonsurgeAllowedReplacementData.of_optimizer_replacement_subset
Theorem4SurgeAllowedReplacementData.of_optimizer_replacement_subset
Theorem4NonsurgeAllowedReplacementData.of_policy_canonical_dominance
Theorem4SurgeAllowedReplacementData.of_policy_canonical_dominance
Theorem4NonsurgeAllowedReplacementData.of_positiveResponse_marginal
Theorem4SurgeAllowedReplacementData.of_positiveResponse_marginal
Theorem4AllMeasurablePolicyCanonicalDominanceData.to_allowed_policy_forms
Theorem4AllMeasurablePolicyCanonicalDominanceData.to_allowed_replacement_data
Theorem4MeasurableEndpointCurrentBoundsRegularPolicyCanonicalDominanceCertificate
Theorem4MeasurableEndpointCurrentBoundsRegularPolicyCanonicalDominanceCertificate.to_regular_selection
paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_policy_canonical_dominance
Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularPolicyCanonicalDominanceSourceAssumptions
Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularPolicyCanonicalDominanceSourceAssumptions.to_regular_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_policy_canonical_dominance_source_assumptions
paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_current_bounds_regular_policy_canonical_dominance_source_assumptions
```

This matters because the canonical Lemma 5 outputs include accept-all and
unbounded positive tails.  Bounded intervals alone cannot be the final descent
domain for the positive, short-rejection, or middle-rejection cases.

The fixed-response part of Lemma 5 is now compiled as a direct five-case
source table, not just downstream wrappers.  Use
`Lemma5PositiveResponseShapeData` to supply the positive, monotone, or
quasi-convex/quasi-concave response case; `.policyForm` identifies the
positive-response policy with the paper's canonical form, and
`paper_lemma5_marginal_optimizer_replacement_of_response_shape` proves weak
and strict variational replacement for `lemma5MarginalSetReward` under the
mass-strictness alternatives.

The strict-boundary issue is now handled directly.  `policyAlmostEverywhereEq`
and `lemma5PolicyFormAlmostEverywhere` record the source convention that
zero-response cutoffs can differ on null sets.  Under `[NoAtoms μ]`,
`Lemma5PositiveResponseShapeData.positive_zero_set_null` proves the feasible
zero-response set is null in all five response-shape cases, including the two
quasi cases by the strict quasi-convex/concave between-endpoint lemmas.
`paper_lemma5_fixed_response_policy_form_ae_of_response_shape` is the
paper-facing fixed-response Lemma 5 endpoint: feasible measurable optimality
for `lemma5MarginalSetReward μ response` implies the canonical Lemma 5 policy
form almost everywhere.  Start from this theorem rather than reproving the
boundary-null argument.  The fixed-response variational replacement is also
closed with the source a.e. strictness convention:
`paper_lemma5_marginal_optimizer_replacement_ae_of_response_shape` proves weak
dominance by the positive-response policy and strict improvement unless the
current feasible policy already has `lemma5PolicyFormAlmostEverywhere`.
The strengthened endpoint
`paper_lemma5_fixed_response_feasible_policy_form_ae_of_response_shape` keeps
the exact representative, feasibility, and measurability bundled.  When an
endpoint proof is easiest on that exact representative, prove the feasible
statewise strict aggregate improvement after updating the current state to
`D.policy`.  The
`dynamicMeasurableOptimal_gn21MeasuredDynamicRewardFunctional_update_*_of_policy_ae`
lemmas preserve optimality for that updated measured current policy.  Then use
`gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement_congr_current_ae` or
`gn21SurgeFeasibleStatewiseStrictAggregateImprovement_congr_current_ae` to
transfer the strict improvement back to the original optimal policy.
This pattern is also available as a compiled Theorem 4 bridge:
`Theorem4AllMeasurableFeasibleAEPolicyFormData` plus
`theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementCertificate_of_feasible_ae_forms_and_representative_improvements`
turn all-optimal feasible AE Lemma 5 representative data and the four exact
representative endpoint improvements into the positive rejected-mass strict
local improvement certificate.
The corresponding paper-facing endpoints are now compiled:
`paper_theorem4_measurable_accept_all_ae_unique_optimal_of_feasible_ae_forms_and_representative_improvements`
and
`paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_ae_representative_source_assumptions`.
Use this source boundary when Lemma 5 gives a feasible representative only
modulo null sets; it avoids forcing the endpoint proof to operate on the
original syntactic policy.
For the fixed-response Lemma 5 portion, target
`Theorem4AllMeasurableFixedResponseShapeData`: the compiled adapter
`Theorem4AllMeasurableFixedResponseShapeData.to_feasible_ae_policy_forms`
turns per-optimum response-shape data, response measurability/integrability,
and fixed-state marginal optimality into the feasible AE representative forms.
For scaled responses where only the positive-response set shape is stable, use
`Lemma5PositiveResponsePolicyFormData` and
`paper_lemma5_fixed_response_feasible_policy_form_ae_of_positive_response_policy_form`.
This endpoint asks for `lemma5PolicyForm shape
(lemma5PositiveResponsePolicy response)` plus nullity of
`{τ | 0 < τ ∧ response τ = 0}`, then gives the same feasible a.e.
representative conclusion.  It should speed up the measured quotient response,
which is a positive scaling of the Lemma 6 normalized response on positive
trip lengths.  Use `Lemma5PositiveResponsePolicyFormData.of_positive_scaling`
to transfer the policy-form/null-zero package through such a positive scaling.
The measured response scaling algebra is compiled:
`gn21LeftLinearResponse_eq_scaled_lemma6Response` handles the scalar
cross-multiplication identity,
`gn21LeftLinearResponse_lemma6_scale_pos` handles positivity of the multiplier,
and
`gn21MeasuredLeftMarginalResponse_eq_scaled_lemma6Response` /
`gn21MeasuredRightMarginalResponse_eq_scaled_lemma6Response` identify the
measured left/right Lemma 5 marginal responses as positive scalings of the
normalized Lemma 6 response under the current reward-rate identities
`W_i = R_i*T_i`, `W_j = R_j*T_j`, nonzero state times, and nonzero aggregate
denominator.
That first packaging step is now compiled for both states:
`gn21MeasuredLeftPositiveResponsePolicyFormData_of_scaled_lemma6Response` and
`gn21MeasuredRightPositiveResponsePolicyFormData_of_scaled_lemma6Response`
transfer normalized Lemma 6 positive-response policy-form data to the measured
marginal responses.  Their helper definitions
`gn21MeasuredLeftLemma6ResponseAtCurrent`,
`gn21MeasuredRightLemma6ResponseAtCurrent`,
`gn21MeasuredLeftLemma6ScaleAtCurrent`, and
`gn21MeasuredRightLemma6ScaleAtCurrent` keep the base response and positive
scale explicit.
For structured CTMC prices, the base normalized Lemma 6 response now has a
direct per-time algebra theorem:
`paper_lemma6_structured_response_per_time_form`.  Use
`strictAntiOn_gn21Lemma6Response_structured_ctmc_of_coeff_pos` and
`strictMonoOn_gn21Lemma6Response_structured_ctmc_of_coeff_neg` to get the
monotone response-shape witnesses from the sign of the coefficient on
`q(u)/u`.  If the source proof supplies a positive zero cutoff, the direct
policy-form packages
`gn21StructuredLemma6ResponsePolicyFormData_strictlyDecreasing` and
`gn21StructuredLemma6ResponsePolicyFormData_strictlyIncreasing` build the
`Lemma5PositiveResponsePolicyFormData` fields used by the measured scaling
adapters.  The measured structured one-threshold wrappers
`gn21MeasuredLeftLemma6PolicyFormData_strictlyDecreasing_of_structured` and
`gn21MeasuredRightLemma6PolicyFormData_strictlyIncreasing_of_structured` now
perform that substitution directly for the non-surge reject-long and surge
reject-short branches.  This is the fastest path for one-threshold
reject-long/reject-short branches of the fixed-response route.
If the source proof has endpoint signs rather than an explicit zero cutoff,
use the bracket route:
`continuousOn_gn21Lemma6Response_structured_ctmc`,
`exists_gn21Lemma6Response_structured_ctmc_zero_of_bracket`,
`exists_gn21Lemma6Response_structured_ctmc_zero_of_reverse_bracket`,
`gn21MeasuredLeftLemma6PolicyFormData_strictlyDecreasing_of_structured_bracket`,
and
`gn21MeasuredRightLemma6PolicyFormData_strictlyIncreasing_of_structured_bracket`.
The all-optima handoff boundary for this lighter route is
`Theorem4AllMeasurableFixedResponsePolicyFormData`; call
`.to_feasible_ae_policy_forms` to enter the existing feasible a.e. Theorem 4
representative pipeline.  If stronger analytic shape data are already
available, `Theorem4AllMeasurableFixedResponseShapeData.to_policy_form_data`
converts them to this lighter boundary.
The paper-facing consumers for this lighter route are
`paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_improvements`
and
`paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_source_assumptions`.
If the endpoint proof needs the positive rejected-mass hypothesis after
switching to the exact a.e. representative, use the hpos-aware fixed-response
route:
`theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementCertificate_of_feasible_ae_forms_and_representative_rejected_mass_improvements`,
`paper_theorem4_measurable_accept_all_ae_unique_optimal_of_feasible_ae_forms_and_representative_rejected_mass_improvements`,
`theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementCertificate_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements`,
`paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements`,
`GN21Theorem3FixedResponsePolicyFormRejectedMassSourceData`,
`theorem3AcceptAllFeasibleRejectedMassStrictLocalPositiveParameterCertificate_of_fixed_response_policy_form_rejected_mass`, and
`paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_rejected_mass_source_assumptions`.
The old source-data package coerces through
`GN21Theorem3FixedResponsePolicyFormRejectedMassSourceData.of_plain`; old
source assumptions coerce through
`Theorem3AcceptAllMeasurableFixedResponsePolicyFormSourceAssumptions.to_rejected_mass_source_assumptions`.
The common-fixed-state equality middle-reroute endpoint route now has a direct
fixed-response source adapter:
`Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteAELocalEndpointCertificate`,
`Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteLocalEndpointCertificate.to_eq_ae_local_endpoint`,
`GN21Theorem3FixedResponsePolicyFormRejectedMassSourceData.of_fixed_state_eq_middle_reroute`,
`GN21Theorem3FixedResponsePolicyFormEqMiddleRerouteSourceData`, and
`paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_eq_middle_reroute_source_assumptions`.
This is the preferred Theorem 3 boundary when the source proof has
fixed-response Lemma 5 policy-form data plus the shared fixed-state equality
AE endpoint certificate, but not exact all-measurable replacement data.  The
adapter derives untouched-state mass positivity from the a.e. representative and
derives the surge middle-gap only from positive rejected mass; do not rebuild a
separate exact-replacement route or reintroduce an all-branch `lo < hi` field for
that purpose.
For Theorem 3, package the constructed-price state data as
`GN21Theorem3FixedResponsePolicyFormSourceData`.
The state-level adapters
`gn21MeasuredLeftFixedResponsePolicyFormFeasibleOptimalData_of_dynamic_optimal`
and
`gn21MeasuredRightFixedResponsePolicyFormFeasibleOptimalData_of_dynamic_optimal`
now produce the fixed-response Lemma 5 data directly from dynamic optimality,
the measured quotient bridge, current `W=R*T` identities, measured-response
regularity, and the scaled Lemma 6 policy-form data.
The response-regularity plumbing is now internal.  Use
`GN21MeasuredLeftFixedResponsePolicyFormSourceData.of_regularity` and
`GN21MeasuredRightFixedResponsePolicyFormSourceData.of_regularity` when the
payments are arbitrary but measurable/integrable.  Use
`GN21MeasuredLeftFixedResponsePolicyFormSourceData.of_ctmc_structured_price`
and
`GN21MeasuredRightFixedResponsePolicyFormSourceData.of_ctmc_structured_price`
for the actual Theorem 3 structured CTMC prices; those constructors derive
structured-price measurability and integrability from switch-probability and
trip-time integrability.  The reusable state-indexed regularity lemmas are
`continuous_ctmcDynamicSwitchProb`, `measurable_ctmcDynamicSwitchProb`,
`continuous_ctmcStructuredDynamicSurgePrice`,
`measurable_ctmcStructuredDynamicSurgePrice`, and
`integrableOn_ctmcStructuredDynamicSurgePrice`.
For one-threshold structured branches, prefer the even thinner source
constructors
`GN21MeasuredLeftFixedResponsePolicyFormSourceData.of_ctmc_structured_price_decreasing`
and
`GN21MeasuredRightFixedResponsePolicyFormSourceData.of_ctmc_structured_price_increasing`.
They combine the measured structured Lemma 6 policy-form wrappers with the
structured-price regularity constructors, so callers supply only coefficient
sign, positive zero-cutoff, denominator/nondegeneracy, and integrability data.
Prefer
`GN21MeasuredLeftFixedResponsePolicyFormSourceData.of_ctmc_structured_price_decreasing_of_bracket`
and
`GN21MeasuredRightFixedResponsePolicyFormSourceData.of_ctmc_structured_price_increasing_of_bracket`
when the available source facts are sign brackets on a positive interval.
For all optima at once, use
`Theorem4AllMeasurableGN21FixedResponsePolicyFormSourceData` and its
`.to_fixed_response_policy_form_data` method to build
`Theorem4AllMeasurableFixedResponsePolicyFormData`.
If every measurable optimum has non-surge decreasing and surge increasing
one-threshold source data, use
`Theorem4AllMeasurableGN21FixedResponsePolicyFormSourceData.of_one_threshold_structured_forms`
to package the allowed shapes, or
`GN21Theorem3FixedResponsePolicyFormSourceData.of_one_threshold_structured_forms`
to go straight to the Theorem 3 fixed-response source boundary together with
accept-all optimality and the four endpoint-improvement fields.
For Theorem 3, `GN21Theorem3FixedResponsePolicyFormSourceData.of_gn21_source_data`
packages that all-optima GN21 data together with accept-all optimality and the
four endpoint-improvement cases.
The measured marginal-response measurability/integrability obligations now
have direct lemmas:
`measurable_gn21MeasuredLeftMarginalResponseAtCurrent`,
`measurable_gn21MeasuredRightMarginalResponseAtCurrent`,
`integrableOn_gn21MeasuredLeftMarginalResponseAtCurrent`, and
`integrableOn_gn21MeasuredRightMarginalResponseAtCurrent`.
When only dynamic local optimality is available, use
the measured GN21 quotient bridge first:
`gn21AggregateDynamicReward_candidate_left_linear_score_le_current_of_le`,
`gn21AggregateDynamicReward_candidate_right_linear_score_le_current_of_le`,
`gn21MeasuredLeftMarginalResponseAtCurrent`,
`gn21MeasuredRightMarginalResponseAtCurrent`,
`gn21MeasuredLeftLinearScore_eq_const_add_marginalSetReward`,
`gn21MeasuredRightLinearScore_eq_const_add_marginalSetReward`,
`lemma5MarginalSetReward_optimal_of_gn21MeasuredDynamicRewardFunctional_zero`,
and
`lemma5MarginalSetReward_optimal_of_gn21MeasuredDynamicRewardFunctional_one`.
These are the source-paper cross-multiplication step: dynamic optimality of
the measured two-state reward becomes a fixed-response Lemma 5 marginal
optimality inequality under Lemma 1 nondegeneracy, positive denominators,
positive arrival rate, and the usual feasible-policy integrability inputs.
Only use the older generic affine bridge for reward models that are actually
positive affine transforms of the marginal integral:
`Lemma5FixedResponseFeasibleOptimalData.of_dynamicStateReward_positive_affine`
or
`lemma5MarginalSetReward_optimal_of_dynamicStateReward_positive_affine`: after
proving the fixed-state continuation reward equals a positive affine transform
of the Lemma 5 marginal integral on feasible measurable policies, these derive
the marginal optimality field automatically.
The a.e. convention is now backed by actual primitive congruence lemmas:
single-state mass/time/payment/renewal reward, Lemma 3 `Q,T,W`, and
`gn21MeasuredAggregateRewardPrimitives` are unchanged under
`policyAlmostEverywhereEq`.  The bridge declarations
`theorem4NonsurgeShapeRepresentative_of_allowed_lemma5_formAE` and
`theorem4SurgeShapeRepresentative_of_allowed_lemma5_formAE` produce exact
Theorem 4 interval-shape representatives from a.e. Lemma 5 forms, so endpoint
work can switch to the exact representative and then use the primitive
congruence lemmas to transfer the measured reward facts back.

The global endpoint-path calculus is now proved.  The four
`endpoint_path_*_of_hasDerivAt_*_on_Icc` lemmas turn derivative sign on the
entire interval between two endpoint positions into weak or strict reward
ordering between the two endpoint policies.  This is the source Step 2 move
needed after choosing the next collision or boundary; future work should
instantiate these lemmas with the concrete endpoint path instead of returning
to infinitesimal-only wrappers.

The paper's Step 2 sign choices are also formalized for the monotone and quasi
cases.  The `lemma5_strictlyIncreasing_*` and `lemma5_strictlyDecreasing_*`
lemmas prove the upper-vs-lower endpoint dichotomies.  The quasi-convex lemma
shows that nonpositive outer endpoint responses force both middle endpoints to
move in reward-improving directions, and the quasi-concave lemma shows that
nonnegative lower endpoint responses force the gap-closing upper endpoint to
have positive response.

The collision merge step is also formalized:
`policyAlmostEverywhereEq_ioo_union_touching` proves that
`(a,b) ∪ (b,c)` and `(a,c)` differ only on the singleton `{b}` under `[NoAtoms
μ]`.  This is the exact measure-theoretic fact behind the source instruction
to combine intervals after an endpoint reaches the next lower endpoint.

Two concrete endpoint-path instantiations are compiled:
`lemma5_upper_endpoint_merge_reward_ge_of_endpoint_path` and its strict
variant turn a nonnegative/positive derivative path for an upper endpoint into
a reward comparison against the merged interval.  The lower-collapse pair does
the same for moving a lower endpoint until the interval becomes empty.  These
are the base finite-policy endpoint moves.  The contextual and ordered-list
threading now covers bounded-bounded upper/lower merges, bounded collapses,
bounded-to-right-ray, left-ray-to-bounded, and left/right-ray boundary merges,
including the second/third bounded merge and second bounded-to-right-ray cases
after one leading component has been peeled off.  The remaining work is to
select the correct move in an arbitrary ordered finite generalized policy and
connect that selection to the shape-case sign lemmas.
The source Subcases 1A/1B/1C are now available as pure sign selectors:
`lemma5_strictQuasiConvex_three_interval_endpoint_sign_trichotomy` and
`lemma5_strictQuasiConcave_two_interval_endpoint_sign_trichotomy`.
The quasi-convex boundary moves selected by those signs now include
`lemma5_list_leftRay_bounded_upper_merge_step_of_endpoint_path`,
`lemma5_list_bounded_rightRay_lower_merge_step_of_endpoint_path`, and
`lemma5_list_second_bounded_rightRay_lower_merge_step_of_endpoint_path`, with
strict variants.
Do not assume the endpoint-sign trichotomy alone closes the source induction:
the all-the-way endpoint merge lemmas still require the derivative sign to
persist over the movement interval.  The paper's missing formal step is a
stopping/sign-persistence argument: move until collision or first sign-change,
then re-enter the appropriate subcase, and prove this process eventually
lowers component count.
The stopping layer needed for this route is now compiled.  The first-hit and
last-zero lemmas
`continuousOn_endpoint_positive_or_first_zero`,
`continuousOn_endpoint_negative_or_first_zero`, and
`continuousOn_endpoint_negative_or_last_zero` record sign persistence before or
after the sign-change boundary.  The endpoint-path wrappers and the stopped
upper/lower merge plus lower/upper collapse policy lemmas now give strict
reward improvement whether the move reaches collision/deletion or stops at the
sign-change boundary.  The stopped moves are also now threaded through the
paper's source sign selectors:
`lemma5_strictlyIncreasing_interval_exists_strict_improvement_of_stopped_endpoint_paths_with_context`,
`lemma5_strictlyDecreasing_gap_exists_strict_improvement_of_stopped_endpoint_paths_with_context`,
`lemma5_strictQuasiConvex_three_interval_exists_strict_improvement_of_stopped_endpoint_paths_with_context`,
and
`lemma5_strictQuasiConcave_two_interval_exists_strict_improvement_of_stopped_endpoint_paths_with_context`
each produce an existential strict improvement from concrete stopped endpoint
paths.  There is now an even shorter strict-local route through the matching
`..._of_local_endpoint_paths_with_context` theorems, which require only
one-sided `HasDerivAt` endpoint data and produce a small feasible endpoint
move.  Prefer these local selectors for Theorem 4 optimal-policy exclusion
unless the full Lemma 5 dominance/iteration statement is required.  The
local selectors now have feasible-measurable counterparts whose conclusions
are already in the source policy domain:
`lemma5_strictlyIncreasing_interval_exists_strict_feasible_measurable_improvement_of_local_endpoint_paths_with_context`,
`lemma5_strictlyDecreasing_gap_exists_strict_feasible_measurable_improvement_of_local_endpoint_paths_with_context`,
`lemma5_strictQuasiConvex_three_interval_exists_strict_feasible_measurable_improvement_of_local_endpoint_paths_with_context`,
and
`lemma5_strictQuasiConcave_two_interval_exists_strict_feasible_measurable_improvement_of_local_endpoint_paths_with_context`.
Use `not_dynamicMeasurableOptimal_of_state_exists_strict_feasible_trip_policy_improvement`
to convert one of these endpoint-selector outputs into a contradiction to
dynamic measurable optimality.
The
replacement route now has a well-founded progress
interface:
`lemma5OptimizerReplacementCertificate_of_domain_wellFounded_descent_and_maximizer`
and
`Lemma5GeneralizedIntervalPolicyWellFoundedDescentMaximizerData`.  The
remaining hard step is no longer the local selector glue.  It is to instantiate
the endpoint derivative identities for arbitrary feasible optimal policies,
then either define the finite hybrid well-founded progress relation or use the
strict-local local selectors to rule out every noncanonical optimal
configuration directly.
There is also a shorter strict-local route for optimality:
`lemma5_strictlyIncreasing_interval_exists_strict_improvement_of_endpoint_moves`,
`lemma5_strictlyDecreasing_gap_exists_strict_improvement_of_endpoint_moves`,
`lemma5_strictQuasiConvex_three_interval_exists_strict_improvement_of_endpoint_moves`
and
`lemma5_strictQuasiConcave_two_interval_exists_strict_improvement_of_endpoint_moves`
combine the source sign dichotomies/trichotomies with stopped endpoint-move
improvement premises.  Use these to rule out noncanonical Case 1 optima
directly if the goal is Theorem 4-style optimal policy classification rather
than full Lemma 5 dominance for every seed.

One finite-domain threading instance is closed: the two-bounded-interval
generalized policy has explicit one/two component representatives, exact
policy-set lemmas, complexity lemmas, and weak/strict upper-endpoint merge
steps that return a one-bounded-interval seed with lower complexity.
The one-bounded-interval collapse case is also closed: moving the lower
endpoint to the upper endpoint returns the explicit empty generalized policy,
again with weak/strict reward variants and strictly lower complexity.

The next hard proof target is the paper-specific endpoint-step field on
`Lemma5GeneralizedIntervalPolicyDescentMaximizerData.step`: from a noncanonical
generalized finite interval/ray policy, construct a weakly improving endpoint
move to the next collision/canonical boundary that strictly lowers complexity,
and identify that move with the global endpoint-path lemmas.  If the endpoint
argument can instead produce a weakly improving canonical representative
directly, use
`Lemma5GeneralizedIntervalPolicyCanonicalDominanceMaximizerData`; its
shape-specific complexity discharges the termination/decrease proof
automatically.  If the endpoint argument naturally produces ordinary feasible
canonical `TripPolicy` replacements, use the policy-level constructor above; it
converts those replacements into equal generalized interval/ray codes before
applying the same finite-domain descent bridge.
If the final Theorem 4 target is the measurable all-optimal allowed-policy-form
certificate, prefer `Theorem4AllMeasurablePolicyCanonicalDominanceData`: it
uses the direct source-policy constructor, proves the canonical replacement is
feasible/measurable, and applies restricted measurable optimality to extract
the current policy form.
If the endpoint proof only ranges over interval/ray seeds that are already
source-feasible, use the feasible-seed version instead:
`Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData`,
`Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData.to_allowed_policy_forms`,
and `.to_allowed_replacement_data`.  It consumes
`Lemma5FeasiblePolicyCanonicalDominanceMaximizerData` and avoids proving
dominance for syntactically possible but infeasible generalized seeds.
If a source route already has a feasible Lemma 5 optimizer-replacement
certificate, use `Theorem4NonsurgeAllowedReplacementData.of_optimizer_replacement_subset`
or `Theorem4SurgeAllowedReplacementData.of_optimizer_replacement_subset` to get
the older concrete replacement data.  The positive-response marginal Lemma 5
certificate is already specialized by the two `.of_positiveResponse_marginal`
wrappers.
For the regular current-bounds endpoint route, use
`Theorem4MeasurableEndpointCurrentBoundsRegularPolicyCanonicalDominanceCertificate`;
it combines those policy-level Lemma 5 data with the four regular endpoint
families and feeds the existing allowed-policy-form route internally.  It now
also recovers the concrete allowed replacement cases through
`.to_regular_selection`, so older endpoint-selection and middle-reroute routes
can consume the same policy-level source data without a second Lemma 5 proof.
The feasible-seed counterpart is
`Theorem4MeasurableEndpointCurrentBoundsRegularFeasiblePolicyCanonicalDominanceCertificate`
with the paper-facing theorem
`paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_feasible_policy_canonical_dominance`.
For the structured-price top-level statement, the matching source-assumption
bundle is
`Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularPolicyCanonicalDominanceSourceAssumptions`;
use `.to_regular_source_assumptions` when a downstream route wants the older
regular selection boundary.
The feasible-seed top-level bundle is
`Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularFeasiblePolicyCanonicalDominanceSourceAssumptions`,
with IC and AE wrappers and `.to_regular_source_assumptions`.

## Lemmas 1-3 Status

Lemmas 1-3 are no longer represented only by opaque stochastic certificates.
The compiled declarations are:

```lean
SingleStateRenewalIIDCycleModel
paper_section2_single_state_renewal_reward_iid_stochastic_bridge
GN21TimeFractionIIDCycleModel
paper_lemma3_stochastic_time_fraction_formula_of_iid_cycles
GN21DynamicIIDCycleModel
paper_lemma1_stochastic_dynamic_reward_decomposition_of_iid_cycles
```

The reusable library wrappers are in
`EconCSLib/Foundations/Probability/RenewalReward.lean`:

```lean
ae_tendsto_empirical_mean_real_of_iid
ae_tendsto_sum_ratio_of_iid
```

The theorem signatures encode the paper's IID renewal-cycle variables,
source primitive positivity, feasible-policy assumptions,
integrability/identical-distribution/pairwise-independence hypotheses, and the
expected geometric-subcycle/Wald mean identities.  Lean now derives the
cycle-denominator, cross-subcycle-probability, state-cycle-time, and total
cycle-time nonzero side conditions internally instead of carrying them as
opaque model fields.  Mathlib's strong law then proves the almost-sure sample
average and quotient limits.  The DAG now has verified arrows
`Lemma2 -> Lemma3`, `Lemma3 -> Lemma1`, and `Lemma1/Lemma3 -> Lemma6`; do not
remove these, since Lemma 3 supplies the time fractions used by the aggregate
dynamic reward formula.

## Section 3.1 Status

Proposition 3.1 is closed for the actual single-state renewal-reward
functional on measurable feasible continuous policies.  The relevant endpoints
are:

```lean
paper_proposition3_1_affine_single_state_renewal_reward_measurable_ic
paper_proposition3_1_affine_single_state_renewal_reward_measurable_ic_of_standard_measure
paper_corollary_single_state_multiplicative_pricing_measurable_ic
paper_theorem1_multiplicative_threshold_best_response_measurable
```

Theorem 1's full general threshold-existence theorem is still partial, but
Step 2 is no longer an assumption.  Lean now proves the partial-threshold
strict/complete dominance theorem, including zero boundary-time cases, and the
renewal-reward certificate constructor only asks for Step 1 selection and
Step 3 threshold maximization:

```lean
paper_theorem1_step2_partial_threshold_dominated_by_strict_or_complete
paper_theorem1_complete_threshold_optimal_of_step1_step3_renewal_reward
paper_theorem1_threshold_certificate_of_step1_step3_renewal_reward
```

## Lemmas 7-8 Status

Lemma 6 is now closed for the local density upper-endpoint response formula
that Lemmas 7-8 depend on.  The direct source wrapper is:

```lean
paper_lemma6_upper_endpoint_interval_density_response_formula
```

It proves existence of the aggregate reward derivative and its same-strict-sign
relation with the paper's normalized response `r(u,i,w,sigma)` after
state-reward-rate substitution.  Lower, tail, and reject-middle endpoint
variants remain available for Theorem 4 shape arguments, but the named Lemma 6
derivative formula should no longer be treated as a gap.

Lemmas 7-8 are therefore closed as paper-facing affine response shape
theorems.  The source wrappers are:

```lean
paper_lemma7_affine_positive_additive_response_strict_quasi_convex
paper_lemma8_affine_negative_additive_response_strict_quasi_concave
```

These wrappers state the paper's affine-additive cases directly in terms of the
Lemma 6 response expression and the sign of
`Delta_ji = R_j - R_i`.  The older CTMC canonical/certificate declarations are
still present and feed the Lemma 5 derivative-shape interface, but the remaining
Lemma 5/Theorem 4 work is downstream optimizer/replacement selection, not a
Lemma 7-8 gap.

Lemmas 9-10 are now closed for their paper-facing derivative-sign and
ratio-feasibility statements.  The direct source-shaped wrappers are:

```lean
paper_lemma9_surge_derivative_positive_of_acceptAll_bounds
paper_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds
```

They start from the paper's accept-all structured ratio bounds, apply the
compiled tightening lemmas to current `Q,T` primitives, and then use the Lemma
6 derivative-value bridge to prove positive upper-endpoint derivatives.  Do not
track arbitrary open-policy endpoint selection as a Lemma 9/10 gap; that work
belongs to Lemma 5/Theorem 4.

## Important Conclusion

Do not try to finish Theorem 3 by proving a universal arbitrary-policy bound
`r1_current <= R1`.  That is not the invariant used by the source proof and can
be false for arbitrary current non-surge policies.

The paper's usable argument is the Theorem 3 surge-side slack paragraph:
state 2 can support any admissible payment ratio by choosing the surge
multiplier/intercept with enough slack.  The Lean route is:

```lean
r1_current <= Rmax
z_2 < current_Lemma9_upper * (m_2 - Rmax)
```

together with either current Lemma 9 lower-endpoint nonpositivity or, more
faithfully, exact lower interval slack.  The compiled constructors that package
these routes are:

```lean
GN21SurgeLemma9AcceptAllAggregateRewardRateData.exists_of_reward_envelope_current_lower_upper_slack
GN21SurgeLemma9AcceptAllAggregateRewardRateData.exists_of_reward_envelope_current_interval_slack
```

## Current Best Frontier

The newest source-facing endpoint is:

```lean
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_final_sign_data_assumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_current_interval_slack_final_sign_data_assumptions
```

It proves the positive-mass measurable Theorem 3 IC conclusion by choosing the
small-surge-slack prices directly from measured accept-all primitives, moving
surge to accept-all first, then using Lemma 10 only after surge is fixed at
accept-all.  Compared with the signed-envelope wrapper, callers no longer
provide data for every positive-parameter candidate; they provide the scalar
`Rmax,U` slack package and the current-policy Lemma 9 lower/uniform-upper
facts.  It still does not require either fixed-state cross-ratio comparison for
the surge move and does not ask for `R1_current <= R1`.  The interval variant
is now the preferred frontier when the current lower endpoint may be positive:
it asks for the selected-price inequality
`lower_current * (m_2-r1_current) < z_2` instead of trying to prove
`lower_current <= 0`.

The key new infrastructure is:

```lean
lemma9StructuredBounds_of_target_ratio_effective_ratio_le_current_lower_fixed_upper
GN21SurgeLemma9AcceptAllAggregateRewardRateData.of_target_ratio_reward_le_current_lower_fixed_upper
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentLowerRewardBoundFixedUpperNoRatioDataAssumptions
singleStateTripPayment_nonneg_of_pointwise_nonneg
gn21StateCycleTime_pos_of_mass_pos
gn21MeasuredStateRewardRate_nonneg_of_pointwise_payment_nonneg
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentLowerRewardBoundFixedUpperPaymentNonnegDataAssumptions
theorem3CurrentNonsurgePayment_nonneg_of_acceptAllLemma10
theorem3NonsurgeAfterSurgeAggregate_ge_of_acceptAllLemma10
theorem3SurgeAggregate_ge_of_currentLowerEnvelopeSlack
theorem3SurgeAggregate_ge_of_currentLowerSignedEnvelopeSlack
exists_effectiveRatio_lt_upperRatio_of_reward_le_envelope_interval_slack
theorem3SurgeAggregate_ge_of_currentIntervalEnvelopeSlack
theorem3SurgeAggregate_ge_of_currentSignedIntervalEnvelopeSlack
lemma9StructuredUpper_gt_uniform_of_switch_gap_pos
lemma9StructuredUpperUniformBound_pos
theorem3SurgeSlack_of_uniform_upper_lt_current
theorem3SurgeRatio_exists_small_slack_at_R2
theorem3SurgeRatio_exists_small_slack
theorem3SurgeParameters_exist_small_slack_of_current_lower_nonpos
theorem3StructuredParameters_exist_of_ratio_and_small_surge_slack
theorem3StructuredParameters_exist_of_ratio_and_small_surge_mass_affine_slack
paper_theorem3_measured_ctmc_structured_prices_exist_and_positive_mass_measurable_ic_of_ratio_and_sequential_accept_all_weak_reward_of_small_surge_slack
paper_theorem3_measured_ctmc_structured_prices_exist_and_positive_mass_measurable_ic_of_ratio_and_sequential_accept_all_weak_reward_of_small_surge_mass_affine_slack
theorem3MassAffineRmax_zero_ratio_pos_of_arrival_z_le_R2
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentLowerEnvelopeSlackDataAssumptions
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentLowerSignedEnvelopeSlackDataAssumptions
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentMassAffineIntervalSlackDataAssumptions
Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeSlackDataAssumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_data_assumptions
Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeSlackCurrentLowerDataAssumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_current_lower_data_assumptions
Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeSlackFinalSignDataAssumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_final_sign_data_assumptions
Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeCurrentIntervalSlackFinalSignDataAssumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_current_interval_slack_final_sign_data_assumptions
Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeMassAffineCurrentIntervalSlackFinalSignDataAssumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_interval_slack_final_sign_data_assumptions
```

## Remaining Mathematical Work

The newest source wrapper is:

```lean
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_final_sign_data_assumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_current_interval_slack_final_sign_data_assumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_interval_slack_final_sign_data_assumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_interval_slack_final_sign_arrival_bound_data_assumptions
```

The endpoint/allowed-policy pivot now has a compiled hnot-aware selection
interface:

```lean
Theorem4MeasurableEndpointCurrentBoundsSelectionUnlessCertificate
theorem4MeasuredAggregateFeasibleStrictLocalImprovementCertificate_of_endpoint_current_bounds_selection_unless
paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_selection_unless
Theorem3AcceptAllMeasurableEndpointCurrentBoundsSelectionUnlessSourceAssumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_selection_unless_source_assumptions
```

Use it when endpoint witnesses need the actual `¬ acceptsAllTrips (ρ i)`
hypothesis before proving cutoff nondegeneracy.  The supporting
shape-normalization lemmas are:

```lean
acceptsAllTrips_of_rejectsShortTrips_of_nonpos
cutoff_pos_of_rejectsShortTrips_of_not_acceptsAll
acceptsAllTrips_of_rejectsMiddleTrips_of_hi_nonpos
hi_pos_of_rejectsMiddleTrips_of_not_acceptsAll
rejectsShortTrips_of_rejectsMiddleTrips_of_lo_nonpos
```

There is also a direct hnot-aware statewise route for cases where a degenerate
syntactic shape should be rerouted before choosing endpoint data:

```lean
Theorem4MeasurableShapeReplacementStatewiseImprovementUnlessCertificate
paper_theorem4_measurable_accept_all_unique_optimal_of_shape_replacement_statewise_improvements_unless
Theorem3AcceptAllMeasurableShapeReplacementStatewiseImprovementUnlessSourceAssumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_shape_replacement_statewise_improvements_unless_positive_source_assumptions
Theorem4MeasurableEndpointCurrentBoundsSelectionUnlessMiddleRerouteCertificate
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_selection_unless_middle_reroute_positive_source_assumptions
```

The lower-sign wrapper asks for:

- a signed reward-envelope choice:
  `(z_0 <= 0 and Rmax = R2)` or
  `(0 <= z_0 and Rmax = R2 + z_0 * switch12)`, specialized to the
  accept-all non-surge ratio;
- the zero-ratio numerator condition
  `0 < R2*T2 - Rmax*(T2 - 1)`;
- for every feasible measurable positive-mass policy `rho`, the current
  Lemma 9 lower-endpoint sign condition:
  `lowerNumerator * upperDenominator <= 0`.

The preferred mass-affine interval wrapper asks for a sharper sign-selected
`Rmax`, accept-all mass-one/finite support for state 1, and accept-all
final-sign certificate.  The arrival-bound variant asks for the dimensionless
numerator inequality and derives `arrival_0*z_0 <= R2` and the old zero-ratio
numerator internally.  The newest lower-final-sign variant also derives the
selected-price current lower slack from the paper's current Lemma 9 final-sign
line, so callers should supply:

```lean
lemma9StructuredLowerNumerator ... *
  lemma9StructuredUpperDenominator ... <= 0
```

for each feasible positive-mass current policy, not the selected-price slack
below directly:

```lean
current_lower *
  (m_2 - gn21MeasuredStateRewardRate ... current_non_surge_policy) < z_2
```

for the selected small-surge prices.  Lean derives the selected lower slack
from the current final-sign inequality plus the mass-affine reward envelope,
and derives the current upper slack internally from the uniform `U` bound and
positive-mass Remark 4 facts.

Do not keep pushing this as an arbitrary-policy sequential obligation without
first adding a policy-shape restriction.  A CTMC-generated two-atom numerical
probe suggests that all-policy selected-price lower slack can fail even with
`C < rho < 1`: with `arrival0=arrival1=5`,
`switch12=switch21=1/2`, state-0 lengths `{1,6}` and state-1 lengths `{1,5}`
with equal masses, and `rho=(C+1)/2≈0.951787`, the accept-all Lemma 9 interval
is approximately `(5.568,12.699)`, but the current state-0 short-trip subset
has lower endpoint about `3.065` while the maximum effective current ratio
over target ratios in that accept-all interval is only about `2.255`.  This is
not a formal Lean counterexample, but it is strong guidance: either use the
endpoint/allowed-policy Theorem 4 route, or prove the lower slack only for the
policy shapes that can actually be optimal.

The paper's actual Lemma 9 final-line feasibility argument is now named
separately:

```lean
lemma9StructuredFeasibilityGap_eq_source_final_factor
lemma9StructuredFeasibilityGap_pos_of_positive_primitives
```

These prove the cross-multiplied lower/upper interval gap is positive from the
source primitive signs.  They do not prove, and should not be used as if they
proved, the stronger statement that the current lower endpoint is nonpositive.

The wrapper itself derives:

- positivity of `m_2 - Rmax`;
- accept-all and current Lemma 9 lower-endpoint nonpositivity;
- accept-all Lemma 9 upper positivity;
- a positive uniform lower bound `U` for current Lemma 9 upper endpoints;
- `U < current_Lemma9_upper` for every positive-mass current policy;
- surge-side slack
  `z_2 < current_Lemma9_upper * (m_2 - Rmax)`.

`0 <= r1_current`, the reward-rate identity, and `r1_current <= Rmax` are no
longer source fields.  Lean defines the current reward rate internally,
derives current non-surge pointwise payment nonnegativity from Lemma 10, and
derives the reward-rate envelope from the signed structured-price bound.  The
mass-affine branch improves that envelope from `m_0+z_0*switch12` to
`max m_0 (arrival_0*z_0)`.  The main compiled bridges are:

```lean
theorem3CurrentNonsurgePayment_nonneg_of_acceptAllLemma10
theorem3SurgeAggregate_ge_of_currentLowerSignedEnvelopeSlack
theorem3SurgeAggregate_ge_of_currentSignedIntervalEnvelopeSlack
theorem3SurgeAggregate_ge_of_currentMassAffineSignedIntervalEnvelopeSlack
theorem3MassAffineRmax_zero_ratio_pos_of_arrival_z_le_R2
```

The source-facing pointwise-nonnegativity field has already been removed by
the derived-payment wrapper.
Do not treat `r1_current <= R1` as a universal arbitrary-policy fact.  The
source proof's usable argument is the Theorem 3 surge-side slack paragraph:
choose the surge parameters so `z_2/(m_2-r1_current)` remains inside Lemma 9's
current interval for any current reward below a verified envelope.

Lean now has a compiled constructor for this route:

```lean
GN21SurgeLemma9AcceptAllAggregateRewardRateData.exists_of_reward_envelope_current_lower_upper_slack
GN21SurgeLemma9AcceptAllAggregateRewardRateData.exists_of_reward_envelope_current_interval_slack
```

The interval constructor combines `r1_current <= Rmax`,
`lower_current*(m_2-r1_current) < z_2`, and
`z_2 < current_upper*(m_2-Rmax)` to build the effective Lemma 9 ratio and the
full aggregate reward-rate data.

## Why This Route

Lemma 9's lower and upper fixed-state transfers pull in opposite cross-ratio
directions.  Requiring both directions effectively forces equality of the
current fixed non-surge exit-weight/time ratio with accept-all, which is too
strong for arbitrary feasible policies unless a pointwise equality has already
been proved.  The new route uses the source Lemma 9 final-sign logic directly
for the current fixed state to replace the lower cross comparison.

## Next Concrete Step

Start from `CLOSEOUT_PROOF_PLAN.txt`; it records why the all-policy sequential
Lemma 9 lower-slack route is suspect.  The next proof work should use the
endpoint/allowed-policy route, not another attempt to prove the selected lower
slack for arbitrary feasible positive-mass policies.

The fixed-transfer regular endpoint packages are now threaded through
`Theorem4MeasurableEndpointCurrentBoundsSelectionUnlessCertificate`; see
`Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularAllowedPolicyFormsCertificate.to_endpoint_current_bounds_selection_unless`
and the two `..._via_selection_unless` Theorem 3 wrappers.

The reject-long fixed-state lower comparison is no longer a source obligation.
Use:

```lean
gn21FixedState_lower_pointwise_of_rejectsLongTrips
GN21RegularEndpointSharedSourceData.nonsurge_lower_pointwise_of_rejectsLongTrips
GN21RegularEndpointSharedSourceData.nonsurge_fixed_cross_ge_acceptAll_of_rejectsLongTrips
GN21NonsurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassData.of_rejectsLongTrips_and_upper
GN21NonsurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassPolicyFormData.of_rejectLong_upper
```

These prove the lower complement/cross-ratio side from `q(t)/t`
monotonicity plus reject-long shape.  The remaining hard fixed-state fact for
that branch is the opposite upper pointwise comparison (and the reward-rate
identity/accounting), not equality on the rejected complement.

The middle-reroute source boundary already performs the `lo <= 0` split for
surge reject-middle shapes and routes that branch through the short-tail
endpoint at cutoff `hi`.  The lower fixed-transfer boundary is now compiled as
`Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularAllowedPolicyFormsMiddleRerouteCertificate`
and
`paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_middle_reroute_source_assumptions`.

That middle-reroute derivation from fixed-state-by-policy-form / derived-tail
data is now compiled.  The source-facing endpoints are:

```lean
paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_derived_tail_middle_reroute_source_assumptions
paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_middle_reroute_source_assumptions
```

The common fixed-state equality cutoff-bounds route can also bypass
policy-form-indexed fixed-state data entirely and feed the older
fixed-state-separated endpoint boundary:

```lean
GN21SurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassEqData.to_fixed_state
GN21NonsurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassEqData.to_fixed_state
Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailCutoffBoundsLocalEndpointCertificate.to_fixed_state_separated
Theorem3AcceptAllMeasurableEndpointTheorem3FixedTransferRegularAllowedReplacementFixedStateEqDerivedTailCutoffBoundsSourceAssumptions.to_fixed_state_separated_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_cutoff_bounds_source_assumptions_via_fixed_state_separated
```

Use this when the source proof has one complement pointwise equality and one
reward-rate identity per state; do not expand those equalities to
policy-form-indexed fixed-state records unless a later endpoint route actually
needs branch-indexed fields.

The next useful Lean target is to build the fields of the fixed-state-equality
middle-reroute source assumption from the paper's regularity hypotheses and
the Lemma 5 all-optimal shape classification, rather than reverting to global
`surge_rejectShort_pos` or all-branch `surge_rejectMiddle_bounds` fields.
For an AE-faithful route, use the compiled collapsed-gap bridge:

```lean
GN21WithDensityAcceptAllSupport.lo_lt_hi_of_rejectsMiddleTrips_of_rejected_mass_pos
GN21RegularEndpointSharedSourceData.surge_rejectMiddle_lo_lt_hi_of_rejected_mass_pos
GN21RegularEndpointSharedSourceData.surge_acceptAllAlmostEverywhere_of_rejectsMiddle_self
```

These let a future positive-rejected-mass endpoint certificate obtain
`lo < hi` only when strict improvement is actually needed; the `lo = hi`
branch should be treated as accept-all almost everywhere.
That future certificate layer is now started and compiled:

```lean
Theorem4MeasurableShapeReplacementStatewiseRejectedMassImprovementUnlessCertificate
theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementCertificate_of_shape_replacement_statewise_rejected_mass_improvements_unless
paper_theorem4_measurable_accept_all_ae_unique_optimal_of_endpoint_current_bounds_selection_unless_middle_reroute
```

The fixed-transfer local endpoint adapter into this AE layer is now compiled:

```lean
Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateByPolicyFormDerivedTailMiddleRerouteAELocalEndpointCertificate
Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateByPolicyFormDerivedTailMiddleRerouteAELocalEndpointCertificate.to_shape_replacement_rejected_mass_improvements_of_shape_replacements
Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteAELocalEndpointCertificate
Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteAELocalEndpointCertificate.to_by_policy_form_ae_local_endpoint
Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteLocalEndpointCertificate.to_ae_local_endpoint
```

The corresponding Theorem 3 AE source wrappers are also compiled:

```lean
paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_rejected_mass_strict_local_positive_parameters
GN21Theorem3MiddleRerouteAEPolicyFormSourceData
paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_derived_tail_middle_reroute_ae_source_assumptions
GN21Theorem3MiddleRerouteLightAEEqSourceData
paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_middle_reroute_light_ae_source_assumptions
paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_middle_reroute_light_ae_ratio_source_assumptions
paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_middle_reroute_light_ae_existence_ratio_source_assumptions
GN21Theorem3MiddleRerouteAEEqSourceData
paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_middle_reroute_ae_source_assumptions
paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_ae_endpoint_middle_reroute_ratio_source_assumptions
```

This is the paper-proof bridge for the collapsed-gap convention: positive
rejected mass supplies `lo < hi`; when there is no positive rejected mass, the
AE uniqueness theorem treats the branch as already accept-all almost
everywhere.  Prefer the light Eq source data for the final AE route; the older
`GN21Theorem3MiddleRerouteAEEqSourceData` is stronger because its local endpoint
record still includes the exact-route all-branch surge middle-gap field.  When
starting from the paper's `C < rho < 1` assumptions, prefer the ratio-source
wrappers so the source proof does not restate `R1 > 0` and `R1 < R2`; prefer
the existence light Eq ratio wrapper when accept-all optimality should be
derived internally from the rejected-mass strict-improvement certificate.  The
next integration target is to build the source-data records from the paper's
regularity hypotheses.  Use `R1_current`/`r1_current` for
Lemma 9's locally fixed non-surge reward rate and reserve `R1`/`targetR1` for
Theorem 3's target rate; the paper locally reuses `R1` in Lemma 9.

Keep the mass-affine sequential wrapper as a documented fallback/source
boundary:

```lean
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_lower_final_sign_arrival_bound_data_assumptions
```

Do not try to prove the mass-affine positive-`z0` branch from only loose scalar
feasibility facts; `arrival_0*z_0 <= R2` is the current explicit extra
condition, derived in the newest wrapper from the dimensionless numerator
bound.

## Documentation Map

- `README.md`: theorem inventory and status.
- `CLOSEOUT_PROOF_PLAN.txt`: shortest remaining source proof plan for Theorem 3.
- `CONTINUOUS_PROOF_PLAN.md`: strategic route and reusable infrastructure.
- `LEMMA9_10_REWARD_RATE_AUDIT.md`: why target reward rates cannot be confused
  with current fixed-state rates, and why the sequential route is only a
  fallback scalar audit after the endpoint/allowed-policy pivot.
- `DependencyDAG.tex`: graphical paper-stage status.
