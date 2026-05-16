# GN21 Continuous Proof Plan

This note records the fastest route to closing the remaining GN21 proof, beyond
the already-compiled wrappers.  The canonical broad measurable entry point is:

## Section 3.1 Update

Theorem 1 Step 1 and Step 2 are now compiled directly:

```lean
paper_theorem1_policy_le_complete_threshold_at_own_reward
paper_theorem1_step2_partial_threshold_dominated_by_strict_or_complete
paper_theorem1_complete_threshold_optimal_of_step1_step3_renewal_reward
paper_theorem1_threshold_certificate_of_step1_step3_renewal_reward
```

Do not ask future callers to provide Step 1 or Step 2 as certificate fields for
measurable feasible policies.  The direct Step 1 route sends any measurable
feasible policy to the complete threshold at its own renewal reward rate.  Step
3 now has compiled compact upper-semicontinuity and margin-resolution
reductions:

```lean
paper_theorem1_cutoff_maximizer_of_compact_upperSemicontinuity
paper_theorem1_complete_threshold_ge_strict_threshold_of_cutoff_ge_strict_reward
paper_theorem1_strict_threshold_reward_lt_higher_strict_threshold_of_positive_band
paper_theorem1_strict_threshold_reward_eq_complete_threshold_of_gap_measure_zero
paper_theorem1_step3_strict_complete_dominated_of_compact_upperSemicontinuity_band_or_gap_resolution
paper_theorem1_step3_strict_complete_dominated_of_compact_upperSemicontinuity_band_resolution
paper_theorem1_single_state_threshold_best_response_measurable_of_complete_maximizer
paper_theorem1_single_state_threshold_best_response_measurable_of_compact_continuity
paper_theorem1_single_state_threshold_best_response_measurable_of_compact_upperSemicontinuity_band_or_gap
paper_theorem1_high_reward_band_or_gap
paper_theorem1_left_tail_bound_of_nonnegative_rate
singleStateTripPayment_strictThresholdPolicy_tendsto_zero
singleStateTripTime_strictThresholdPolicy_tendsto_zero
singleStateTripPayment_completeThresholdPolicy_tendsto_zero
singleStateTripTime_completeThresholdPolicy_tendsto_zero
paper_theorem1_single_state_threshold_best_response_measurable_of_compact_upperSemicontinuity
paper_theorem1_single_state_threshold_best_response_measurable_of_compact_continuous_objective
continuousAt_setIntegral_strictThresholdPolicy_of_boundary_measure_zero
continuousAt_setIntegral_completeThresholdPolicy_of_boundary_measure_zero
continuousOn_theorem1_cutoff_objective_of_boundary_measure_zero
paper_theorem1_single_state_threshold_best_response_measurable_of_no_boundary_mass
tendsto_setIntegral_strictThresholdPolicy_left
tendsto_setIntegral_strictThresholdPolicy_right
tendsto_setIntegral_completeThresholdPolicy_left
tendsto_setIntegral_completeThresholdPolicy_right
upperSemicontinuousOn_theorem1_cutoff_objective
paper_theorem1_single_state_threshold_best_response_measurable
```

Theorem 1 is now closed for the source measurable single-state threshold best
response under the explicit source primitives in the Lean statement:
measurable nonnegative on-trip rates, finite accept-all mass, accept-all
payment/time integrability, positive arrival rate, and positive accept-all
payment.  Lean proves the high-reward band/gap dichotomy internally, derives
the negative-cutoff left tail from nonnegative on-trip rates, derives the
high-cutoff right tail from antitone threshold-set convergence plus accept-all
payment/time integrability, and closes the atom-at-threshold compactness seam
by one-sided dominated convergence.  From the left, strict and complete
threshold rewards converge to the complete-threshold reward; from the right,
they converge to the strict-threshold reward; therefore the strict/complete
max cutoff objective is upper-semicontinuous on every compact interval.
Proposition 3.1 and the single-state multiplicative-pricing corollary are
closed for the actual renewal reward on measurable feasible policies.
Lemma 4 is also closed in the source measurable domain:
`paper_lemma4_single_state_threshold_mass_zero_uniqueness_measurable` combines
Theorem 1 with the reward-cutoff move and converts the zero-time off-boundary
gaps to zero mass.

## Lemmas 6-10 Update

Lemma 6 is closed for the source upper-endpoint density formula that identifies
the dynamic reward derivative's sign with the paper's normalized response:

```lean
paper_lemma6_upper_endpoint_interval_density_response_formula
```

Lemmas 7-8 can therefore be treated as closed source-facing affine
response-shape statements:

```lean
paper_lemma7_affine_positive_additive_response_strict_quasi_convex
paper_lemma8_affine_negative_additive_response_strict_quasi_concave
```

The remaining work after these lemmas is not another affine-response calculus
bridge.  It is the downstream Lemma 5/Theorem 4 selection problem: use the
response shapes to choose valid endpoint replacements for arbitrary open
measurable optimal policies and connect those replacements back to the
set-valued reward functional.

The fixed-response part of Lemma 5 now has an a.e.-strict source endpoint:

```lean
paper_lemma5_marginal_optimizer_replacement_ae_of_response_shape
paper_lemma5_fixed_response_policy_form_ae_of_response_shape
paper_lemma5_fixed_response_feasible_policy_form_ae_of_response_shape
theorem4NonsurgeShapeRepresentative_of_allowed_lemma5_formAE
theorem4SurgeShapeRepresentative_of_allowed_lemma5_formAE
```

The first theorem proves weak dominance by the positive-response policy and
strict improvement unless the current feasible policy already has
`lemma5PolicyFormAlmostEverywhere`; the second turns feasible optimality into
the a.e. canonical form.  Do not reintroduce exact-boundary strictness as a
separate assumption for this fixed-response variational step.  When a later
endpoint proof needs exact interval syntax, use the two representative theorems
above, then transfer measured facts back with:

```lean
Lemma5FeasiblePolicyFormAlmostEverywhereData
Lemma5FeasiblePolicyFormAlmostEverywhereData.to_policyFormAlmostEverywhere
Lemma5FeasiblePolicyFormAlmostEverywhereData.acceptAllAlmostEverywhere_of_positive
GN21MeasuredPairNondegenerate.congr_left_policy_ae
GN21MeasuredPairNondegenerate.congr_right_policy_ae
gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement_congr_current_ae
gn21SurgeFeasibleStatewiseStrictAggregateImprovement_congr_current_ae
singleStateTripMass_congr_policy_ae
singleStateTripTime_congr_policy_ae
singleStateTripPayment_congr_policy_ae
singleStateRenewalReward_congr_policy_ae
gn21ExitWeightIntegral_congr_policy_ae
gn21ScaledStateTime_congr_policy_ae
gn21ScaledStateEarning_congr_policy_ae
gn21MeasuredAggregateRewardPrimitives_congr_left_policy_ae
gn21MeasuredAggregateRewardPrimitives_congr_right_policy_ae
```

The feasible a.e. representative is now the preferred handoff object for
Theorem 4 endpoint moves: prove the concrete endpoint improvement on
`D.policy`, then use the two `...congr_current_ae` lemmas to move the feasible
strict aggregate improvement back to the original optimal policy.

The global calculus part of Lemma 5 Step 2 is now compiled:

```lean
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
policyAlmostEverywhereEq_union_left
policyAlmostEverywhereEq_bounded_union_positiveRightRay_touching
policyAlmostEverywhereEq_positiveLeftRay_union_bounded_touching
policyAlmostEverywhereEq_positiveLeftRightRay_touching
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
```

These lemmas prove that derivative sign on the whole interval between two
endpoint positions gives the corresponding weak or strict reward ordering
after moving the endpoint all the way to the next collision or boundary, and
they prove the paper's monotone/quasi sign choices used to decide which
endpoint should move.  The touching-interval merge fact proves the paper's
zero-measure collision step: `(a,b) ∪ (b,c)` is a.e. equal to `(a,c)` under
nonatomic trip-length measures.  The remaining nonlinear work is therefore
not calculus, source sign algebra, or endpoint-collision measure theory.
Lean also has direct reward-comparison lemmas for the two basic finite moves:
upper-endpoint merge and lower-endpoint collapse, each in weak and strict
form.  The two-bounded-interval generalized-policy merge case is threaded all
the way to a lower-complexity one-bounded seed, and the one-bounded lower
collapse case is threaded to the explicit empty generalized seed.  The
threading now works inside an arbitrary fixed generalized-policy context, in
both endpoint directions, and includes the boundary/ray reductions needed to
reach right tails, left tails, and accept-all from finite seeds.  Lean also has
an ordered component-list policy domain and head/two-head decomposition lemmas
that identify the source proof's first components with the compiled context
seeds.  The first ordered bounded-bounded merge and bounded-interval collapse
steps now produce a shorter ordered list directly, in weak and strict forms;
the ordered bounded/right-ray, left-ray/bounded, and left/right-ray boundary
merges now reach shorter right-tail, left-tail, and accept-all lists.  The
second-component bounded lower-collapse also removes a middle component while
preserving the leading component and tail, and the symmetric upper-collapse is
also compiled.  Lean now also has the ordered second/third bounded-component
upper/lower merge primitives and the ordered second-component
bounded-to-right-ray merge, each in weak and strict forms.  The remaining
source sign-selection facts are no longer informal: the quasi-convex
three-interval case and quasi-concave two-interval case are compiled as
endpoint-sign trichotomies matching Subcases 1A/1B/1C.  The ordered
source-boundary moves used by the quasi-convex selector are also compiled:
positive-left-ray upper expansion into a bounded component, bounded/right-ray
lower merge, and the one-leading-component bounded/right-ray lower merge.  The
remaining nonlinear work is not another adjacent-merge normal form: endpoint
signs at the current seed do not by themselves justify moving all the way to
the next collision.  The source proof moves until either a collision occurs or
the relevant derivative sign changes, then switches subcases.  The stopping
layer is now compiled: `continuousOn_endpoint_positive_or_first_zero`,
`continuousOn_endpoint_negative_or_first_zero`, and
`continuousOn_endpoint_negative_or_last_zero` choose first/last sign-change
boundaries with prefix/suffix sign persistence, and the corresponding
endpoint-path wrappers turn those stopped sign intervals into strict reward
improvement.  At the policy level, the upper/lower merge and lower/upper
collapse stopped variants now either reach collision/deletion or stop at the
sign-change boundary, improving reward in both branches.  The replacement
certificate route now also accepts a well-founded progress relation via
`lemma5OptimizerReplacementCertificate_of_domain_wellFounded_descent_and_maximizer`
and
`Lemma5GeneralizedIntervalPolicyWellFoundedDescentMaximizerData`.  What
remains is the finite hybrid iteration: after a stopped sign-change move,
thread the updated endpoint back through the quasi-convex or quasi-concave
selector, define the well-founded progress relation, and prove repeated
sign-change stops cannot cycle without eventually lowering component count or
landing on a canonical Lemma 5 shape.

For the optimal-policy branch, Lean now also exposes a shorter strict-local
route for all nonpositive derivative-shape cases:
`lemma5_strictlyIncreasing_interval_exists_strict_improvement_of_endpoint_moves`,
`lemma5_strictlyDecreasing_gap_exists_strict_improvement_of_endpoint_moves`,
`lemma5_strictQuasiConvex_three_interval_exists_strict_improvement_of_endpoint_moves`
and
`lemma5_strictQuasiConcave_two_interval_exists_strict_improvement_of_endpoint_moves`.
These selectors combine the source sign dichotomies/trichotomies with stopped
endpoint-move improvement premises and can rule out the noncanonical Case 1
configurations without first constructing a complete finite path to the
canonical form.
The stopped endpoint moves have now been instantiated directly for those
selectors as
`lemma5_strictlyIncreasing_interval_exists_strict_improvement_of_stopped_endpoint_paths_with_context`,
`lemma5_strictlyDecreasing_gap_exists_strict_improvement_of_stopped_endpoint_paths_with_context`,
`lemma5_strictQuasiConvex_three_interval_exists_strict_improvement_of_stopped_endpoint_paths_with_context`,
and
`lemma5_strictQuasiConcave_two_interval_exists_strict_improvement_of_stopped_endpoint_paths_with_context`.
The same four cases also have local
`..._of_local_endpoint_paths_with_context` instantiations.  These require only
one-sided `HasDerivAt` endpoint data and are now the shortest route to Theorem
4 optimal-policy exclusion: supply the endpoint derivative identity for the
selected branch, get a nearby strict improvement, and contradict optimality.
This route is now source-domain compatible: each local selector has a
`...exists_strict_feasible_measurable_improvement...` variant returning
`∃ σ', σ' ⊆ acceptAllPolicy ∧ MeasurableSet σ' ∧ R current < R σ'`.
The four local endpoint primitives also have feasible-measurable versions, and
the bridge
`not_dynamicMeasurableOptimal_of_state_exists_strict_feasible_trip_policy_improvement`
turns those one-state replacements into the existing dynamic feasible-update
contradiction interface.

Lemmas 9-10 are also closed for their named derivative-sign and
ratio-feasibility statements.  The source-shaped wrappers are:

```lean
paper_lemma9_surge_derivative_positive_of_acceptAll_bounds
paper_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds
```

These start from the paper's accept-all ratio bounds, apply the formal
tightening bridge to the current `Q,T` primitives, and then use Lemma 6 to
prove positive upper-endpoint reward derivatives.  Arbitrary open-policy
endpoint selection remains a Lemma 5/Theorem 4 obligation, not a Lemma 9/10
gap.

```lean
paper_theorem3_measured_structured_measurable_ic_prices_of_source_assumptions
```

The newest reduced positive-mass frontier is:

```lean
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_current_lower_reward_bound_fixed_upper_no_ratio_data_assumptions
```

This sequential route is the preferred IC closure route.  It proves the surge-state
accept-all move first, using Lemma 9 with the current fixed non-surge reward
rate, and then proves the non-surge accept-all move only after surge is already
fixed at accept-all, where Lemma 10 can use the Theorem 3 target surge reward
rate.  The current-lower/fixed-upper frontier is the best handoff target for
closing the remaining Theorem 3 source boundary that consumes the Lemma 9
move.  The older fixed-transfer adapter
remains useful for branch bookkeeping,
but it should not be treated as the final source-faithful closure route unless
the source proof also establishes the target reward-rate/equality facts for
arbitrary non-accept-all fixed states.  The remaining field for that adapter is
`Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailCutoffBoundsLocalEndpointCertificate`
for the structured prices constructed by Theorem 3, paired with ordinary
all-measurable allowed Lemma 5 replacement data.  This endpoint packages shared
continuous-density regularity, non-surge cutoff nondegeneracy, one fixed-state
pointwise equality/reward-rate package for each state, and ordinary surge cutoff
bounds.  Lean converts those common fixed-state packages into the older
policy-form packages internally.
Lean chooses the upper reject-middle cutoff from `0 ≤ lo < hi`, derives
positive surge-tail product integrability from the shared
accept-all time/switch integrability fields, upgrades those positive tails to
the older uniform-tail package using continuous finite-interval product
calculus, then uses allowed Lemma 5 policy forms to
choose the accept-all or non-accept-all fixed-state branch, derives the
non-surge accept-middle local move from the positive lower cutoff, builds the
surge moving endpoint data from the uniform tail package, then derives current
mass, no-mass pointwise endpoint facts, mass-separated endpoint facts,
positive-cutoff endpoint data, and the regular Theorem 4 certificate
internally.  The older regular
allowed-policy-form route remains compiled and asks for fully built regular
endpoint records; the older regular-shape route remains compiled and asks for
the already-packaged shape derivation; the older regular-selection route remains
compiled and asks for ordinary allowed Lemma 5 replacement data in addition to
the same regular endpoint packages.  The previous broader endpoints remain
compiled:

```lean
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_allowed_policy_forms_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_shape_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_supported_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_allowed_replacement_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_selection_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_replacement_statewise_improvements_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_statewise_improvements_source_assumptions
```

## Current Best Path

1. The feasible endpoint improvement wrappers for the four shape cases are
   compiled, including the accept-all-bound versions:
   non-surge reject-long, non-surge accept-middle, surge reject-short, and
   both surge reject-middle endpoint moves.  The current-bounds-data variants
   are also compiled, so the final theorem no longer has to thread current
   `Q,T,W` paths, denominator positivity, or Remark 4 side conditions by hand.

2. Use the sequential Theorem 3 frontier instead of the stronger simultaneous
   statewise frontier.  The reward-rate audit in
   `LEMMA9_10_REWARD_RATE_AUDIT.md` records the current distinction between
   Theorem 3 target rates and Lemma 9/10 current fixed-state rates.  Lean now
   has a reward-rate-separated Lemma 10 endpoint-term route:
   `lemma10StructuredStaticTerm_eq_ratio_reward_split`,
   `lemma10StructuredLinearEndpoint_eq_ratio_reward_split`,
   `lemma10StructuredStaticTerm_pos_of_ratio_reward_slack`,
   `lemma10StructuredLinearEndpoint_pos_of_ratio_reward_slack`,
   `paper_lemma10_structured_derivative_kernel_pos_of_ratio_reward_slack`,
   `paper_lemma10_structured_derivative_kernel_pos_of_endpoint_terms`, and
   `gn21MeasuredAggregateRewardPrimitives_le_acceptAll_left_of_lemma10_endpoint_terms`.
   This route is threaded up to the weak Theorem 3 boundary through
   `GN21NonsurgeLemma10EndpointTermsAggregateData`,
   `Theorem4MeasuredAggregateStructuredEndpointTermsCurrentRateWeakCertificate`,
   and
   `theorem3AcceptAllWeakRewardCertificate_of_structured_endpoint_terms_current_rates`.
   The paper-facing source wrapper is
   `paper_theorem3_measured_structured_ic_prices_of_structured_endpoint_terms_current_rate_source_assumptions`.
   More importantly, Lean now has the sequential current-bounds route:
   `Theorem4MeasuredAggregateStructuredSequentialCurrentBoundsWeakCertificate`,
   `Theorem4MeasuredAggregateStructuredFeasibleSequentialCurrentBoundsWeakCertificate`,
   `paper_theorem3_measured_structured_ic_prices_of_structured_sequential_current_bounds_source_assumptions`,
   and
   `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_current_bounds_source_assumptions`.
   The lightest feasible-measurable wrapper is
   `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_current_bounds_source_data_assumptions`,
   exposed canonically as
   `paper_theorem3_measured_structured_measurable_ic_prices_of_source_assumptions`.
   The denominator-valid source theorem is now
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_source_assumptions`.
   Lean now derives the packed aggregate data, nondegeneracy fields, and the
   Lemma 10 accept-all fixed-surge branch from Theorem 3 parameter data.  The
   remaining field on the positive-mass route is just Lemma 9 reward-rate data
   for the surge move, quantified over feasible measurable policies whose
   accepted trip mass is positive in both states.  This field now has a
   compiled fixed-transfer adapter:
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_fixed_transfer_reward_rate_data_assumptions`.
   It asks for accept-all Lemma 9 bounds at the effective current ratio, the
   current fixed non-surge reward rate, and the two fixed-state cross-ratio
   comparisons; Lean transfers the fixed state and then tightens the moving
   surge state.  A target-rate specialization,
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_target_fixed_transfer_data_assumptions`,
   reuses the constructed Theorem 3 accept-all bounds when the current fixed
   non-surge reward rate is `R1` and `m_2-R1>0` is available.  The
   reward-bound specialization
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_target_reward_bound_fixed_transfer_data_assumptions`
   keeps the same target accept-all bounds but lets the current fixed
   non-surge reward rate be below `R1`; Lean converts the target ratio into
   the effective current ratio using the shared `z_2` accounting identity,
   a nonpositive accept-all lower endpoint, and the two fixed-state
   cross-ratio comparisons.  The pointwise
   variant
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_target_pointwise_fixed_transfer_data_assumptions`
   derives both fixed-state cross-ratio comparisons from one equality on the
   current non-surge rejected complement.  The positive-ratio pointwise wrapper
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_target_positive_ratio_pointwise_fixed_transfer_data_assumptions`
   additionally derives `m_2-R1>0` from the existing Theorem 3 multiplier
   lemma.  The positive-parameter sequential boundary
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_positive_parameter_positive_mass_feasible_sequential_weak_reward`
   preserves the constructed positive surge-ratio witness for source adapters
   that should not ask for it again.  The positive-parameter reward-bound
   wrapper
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_target_reward_bound_fixed_transfer_data_assumptions`
   is now the cleanest compiled boundary for the sequential route: the source
   supplies effective-ratio accounting, `r1_current <= R1`, nonnegativity of
   `r1_current`, reward-rate identity, and the fixed-state cross comparisons.
   The no-ratio variant
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_target_reward_bound_fixed_transfer_no_ratio_data_assumptions`
   constructs `z_2/(m_2-r1_current)` internally, leaving only
   `r1_current <= R1`, `0 <= r1_current`, reward-rate identity, and the
   fixed-state cross comparisons as policy-dependent data.  The final-sign
   variant
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_final_sign_reward_bound_fixed_transfer_no_ratio_data_assumptions`
   derives the accept-all lower-endpoint fact from the paper's Lemma 9
   denominator and left-nonpositive final-sign assumptions.  The newest
   reduced boundary is
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_current_lower_reward_bound_fixed_upper_no_ratio_data_assumptions`:
   it uses the current fixed non-surge Lemma 9 lower-endpoint nonpositivity
   directly, constructs the effective current ratio internally, and needs only
   the upper fixed-state cross-ratio comparison.
   The older broad
   feasible-measurable wrapper still exposes the explicit positive-current-mass
   obligation, and the accounting-form/raw source-data wrappers remain compiled
   as intermediate adapters.

3. Instantiate the positive-mass feasible sequential source route from source
   regularity: prove either the effective-ratio fixed-transfer data above for
   the surge move at each positive-mass feasible current policy, or prove the
   final-sign reward-bound/no-ratio specialization by showing the current
   non-surge reward rate is at most `R1`, nonnegative, and equal to the
   measured reward-rate expression, plus the fixed-state cross-ratio
   comparisons.  Prefer the current-lower/fixed-upper specialization if the
   source Lemma 9 final-sign proof can be repeated with the current fixed
   non-surge `T,Q`: it replaces the lower cross-ratio comparison by that direct
   current lower-endpoint sign proof, leaving only the upper fixed-state
   comparison.  The target-rate positive-ratio pointwise
   specialization remains available when the current non-surge reward rate is
   known to equal `R1`.  The Lemma 10 non-surge move with surge fixed to
   accept-all is now compiled from the constructed Theorem 3 parameter data,
   and positive mass supplies the denominator/nondegeneracy side conditions.
   The older regular
   allowed-policy-form and fixed-transfer routes can remain available for
   stronger uniqueness or statewise statements.

## Key Missing Mathematical Lemma

The hard theorem should have this shape:

```lean
theorem theorem4_measurable_shape_statewise_improvements_of_endpoint_regular
    (...) :
    Theorem4MeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsCertificate
      μ arrival m z switch12 switch21
```

Its hypotheses should be source-level regularity assumptions, not pre-unpacked
endpoint primitives:

- `μ 0` and `μ 1` are Lebesgue measures with nonnegative measurable densities,
  packaged as `GN21WithDensityAcceptAllSupport` when finite/positive support is
  needed.
- The densities are positive and continuous at the relevant finite endpoint.
- Current feasible optimal policies have the interval/tail shapes from Lemma 5.
- The current-policy `Q,T,W` primitives agree with the endpoint path formulas,
  or equivalently produce the compiled current-bounds endpoint data packages.
- The Lemma 9 structured bounds hold for the surge move with the current
  non-surge fixed-state reward rate.
- The Lemma 10 structured bounds hold for the non-surge move after the surge
  state is accept-all, so the fixed-state reward rate is the Theorem 3 target
  accept-all rate.
- The other state's current policy has positive finite mass and the required
  `Q,T,W` accounting identity.

Most of these already have local lemmas.  The missing work is packaging them so
the arbitrary optimum generated by measurable shape derivation can be converted
into the concrete endpoint policy data.

## Reusable Infrastructure To Build

- `dynamicFeasibleMeasurablePolicy_update` is now proved and should be reused
  everywhere a single-state replacement is selected.
- `Theorem4AllMeasurableOptimalShapeReplacementDerivationCertificate.of_allowed_replacement_data`
  now derives feasible measurable replacement data from source-facing allowed
  Lemma 5 cases, so the final source theorem should not provide dependent
  measurable replacement packages by hand.
- `GN21WithDensityAcceptAllSupport` now derives current and replacement
  finite-mass/positive-density support fields for feasible policies and all
  five endpoint movements.  Use
  `GN21NonsurgeRejectLongCurrentBoundsEndpointData.of_acceptAll_support`,
  `GN21NonsurgeAcceptMiddleCurrentBoundsEndpointData.of_acceptAll_support`,
  `GN21SurgeRejectShortCurrentBoundsEndpointData.of_acceptAll_support`,
  `GN21SurgeRejectMiddleLoCurrentBoundsEndpointData.of_acceptAll_support`, and
  `GN21SurgeRejectMiddleHiCurrentBoundsEndpointData.of_acceptAll_support`
  instead of filling those fields manually.
- `continuous_gn21SwitchProb`, `continuous_ctmcStructuredSurgePrice`,
  `continuousAt_mul_density_of_continuous`,
  `stronglyMeasurableAtFilter_mul_density_of_continuous`, and
  `intervalIntegrable_mul_density_of_continuous` derive endpoint continuity,
  strong measurability, and finite-interval integrability fields from a
  continuous real-valued density.
- `GN21EndpointProductContinuityData.of_ctmcStructured` and
  `GN21FiniteEndpointProductCalculusData.of_ctmcStructured` bundle the `q,w,t`
  endpoint calculus fields for structured prices.  Prefer the endpoint
  constructors ending in `of_acceptAll_support_and_calculus` or
  `of_acceptAll_support_and_continuity` when building the final endpoint data.
- `GN21PositiveIntervalProductIntegrabilityData.of_ctmcStructured` derives the
  short accepted-interval integrability fields for all positive finite
  endpoints from continuous density/product data.  `GN21TailProductIntegrabilityData`
  bundles one improper tail assumption and uses `q_mono`, `w_mono`, and
  `t_mono` to supply narrower current and replacement tails.
- The supported endpoint records
  `GN21NonsurgeRejectLongSupportedEndpointData`,
  `GN21NonsurgeAcceptMiddleSupportedEndpointData`,
  `GN21SurgeRejectShortSupportedEndpointData`,
  `GN21SurgeRejectMiddleLoSupportedEndpointData`,
  `GN21SurgeRejectMiddleHiSupportedEndpointData`, and
  `GN21SurgeRejectMiddleSupportedEndpointData` now bridge these support,
  calculus, and short/tail integrability packages into the current-bounds
  endpoint certificate expected by Theorem 4.
- `GN21NonsurgeLemma10AcceptAllAggregateData.of_source` and
  `GN21SurgeLemma9AcceptAllAggregateData.of_source` now turn source Lemma 9/10
  current-bounds data directly into the full current-bounds endpoint packages,
  so endpoint construction should not manually compose the primitive route.
- `GN21NonsurgeLemma10AcceptAllAggregateSourceData.of_acceptAll_tightening`
  and `GN21SurgeLemma9AcceptAllAggregateSourceData.of_acceptAll_tightening`
  build those source current-bound records from accept-all moving-state bounds,
  positive current mass, current integrability, and the fixed-state reward-rate
  identity.  Use these before falling back to hand-proving the source records.
- The regular endpoint records
  `GN21NonsurgeRejectLongRegularEndpointData`,
  `GN21NonsurgeAcceptMiddleRegularEndpointData`,
  `GN21SurgeRejectShortRegularEndpointData`,
  `GN21SurgeRejectMiddleLoRegularEndpointData`,
  `GN21SurgeRejectMiddleHiRegularEndpointData`, and
  `GN21SurgeRejectMiddleRegularEndpointData` now derive the supported endpoint
  records from continuous density, source current-bounds data, support, and
  tail-integrability packages.
- `GN21RegularEndpointSharedSourceData` and the five
  `...RegularEndpointData.of_shared_source` constructors factor out shared
  source regularity.  Use this package before case-splitting on endpoint
  shapes; the shape cases should only provide cutoff-local density positivity,
  small-move/tail data, mass positivity of the other state, and source
  Lemma 9/10 current-bound data.
- The shape-specific `GN21RegularEndpointSharedSourceData.*_current_mass_pos`
  lemmas derive the moving state's positive current mass from shared support
  and the realized Lemma 5 shape, which is exactly the mass input needed by
  the accept-all tightening constructors.
- `GN21RegularEndpointSharedSourceData.nonsurge_scaled_time_pos`,
  `surge_scaled_time_pos`, `nonsurge_exit_weight_pos`,
  `surge_exit_weight_pos`, and
  `surge_fixed_switch_term_pos_for_nonsurge_bounds` discharge routine
  fixed-state time/exit positivity for the shared-source endpoint builders.
- The five `...RegularEndpointData.of_shared_source_and_acceptAll_tightening`
  constructors are the preferred endpoint builders: they compose shared
  source regularity, shape-derived current mass, accept-all moving-state
  tightening, and fixed-state reward-rate data into the regular endpoint
  records consumed by Theorem 4.
- The non-surge endpoint cases now also have
  `GN21NonsurgeRejectLongRegularEndpointData.of_shared_source_and_theorem3_fixed_transfer`
  and
  `GN21NonsurgeAcceptMiddleRegularEndpointData.of_shared_source_and_theorem3_fixed_transfer`.
  These consume `Theorem3AcceptAllStructuredParameterData` directly and use
  the Lemma 10 fixed-state transfer, so the caller supplies a fixed-state
  cross-ratio condition instead of pre-built current-fixed Lemma 10 bounds.
- The surge endpoint cases likewise have
  `GN21SurgeRejectShortRegularEndpointData.of_shared_source_and_theorem3_fixed_transfer`,
  `GN21SurgeRejectMiddleLoRegularEndpointData.of_shared_source_and_theorem3_fixed_transfer`,
  and
  `GN21SurgeRejectMiddleHiRegularEndpointData.of_shared_source_and_theorem3_fixed_transfer`.
  These use the Lemma 9 fixed-state transfer and therefore expose both
  cross-ratio directions, plus the usual surge accept-all positive-measure
  input for `Q_2 > lambda_21`.
- The Theorem 3 fixed-transfer local data records now state the fixed-state
  structured-price accounting equation, not a pre-expanded scaled-earning
  reward-rate identity.  The adapter expands this with
  `paper_remark2_structured_scaled_earning_algebra` and shared accept-all
  integrability restricted to the current feasible policy.
- Fixed-state transfer is now named algebraically.  Lemma 10 has
  `lemma10StructuredBounds_of_fixed_state_expansion` and the measured wrapper
  `lemma10StructuredBounds_of_acceptAll_fixed_state_measured_expansion`,
  which reduce accept-all fixed-state transfer to the cross-ratio condition
  `T_acceptAll * Q_current <= T_current * Q_acceptAll`.  Lemma 9 has
  `lemma9StructuredBounds_of_fixed_state_expansion`; its lower and upper
  comparisons require opposite cross-ratio directions, exposing that this
  side cannot be discharged by one-sided monotonicity alone.
- `Theorem3AcceptAllStructuredParameterData.of_evidence` should be used as
  soon as a constructed-price endpoint receives
  `theorem3AcceptAllStructuredParameterEvidence`; it names the two ratios,
  accept-all Lemma 9/10 bounds, and accounting identities used by the endpoint
  builders.  When a surge endpoint needs the constructed positive-ratio witness,
  use `theorem3AcceptAllStructuredPositiveParameterEvidence` and
  `Theorem3AcceptAllStructuredPositiveParameterData.of_evidence`; the positive
  fixed-transfer wrapper preserves that witness through the Theorem 3
  strict-local route.
- `Theorem4AllMeasurableAllowedPolicyFormsCertificate` and
  `Theorem4MeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsCertificate`
  remain useful older targets because they avoid duplicating Lemma 5 replacement
  measurability work: the continuous proof only needs to classify every
  measurable optimum into the allowed policy forms, and the regular endpoint
  fields supply the realized endpoint moves.  If the source proof instead
  produces all-measurable Lemma 5 replacement data, it feeds this target through
  `Theorem4AllMeasurableAllowedPolicyFormsCertificate.of_shape_replacements`.
- `lemma5PositiveResponsePolicy` and the
  `lemma5PolicyForm_positiveResponse_*` theorems now prove the core
  sign-to-shape part of Lemma 5 directly: positive responses give accept-all,
  monotone responses with a positive zero crossing give tail/head policies, and
  quasi-convex/quasi-concave responses with boundary zeros give middle
  rejection/acceptance.  `Lemma5PositiveResponseShapeData` is the compiled
  five-case source table: it exposes both
  `.derivativeShapeWitness` and `.policyForm`, and
  `paper_lemma5_marginal_optimizer_replacement_of_response_shape` turns those
  cases into the fixed-response optimizer-replacement statement.
  `lemma5MarginalSetReward_le_positiveResponsePolicy`
  also proves the fixed-response variational comparison: for the linearized
  set-integral reward, the positive-response policy weakly dominates every
  measurable feasible policy; the strict theorem
  `lemma5MarginalSetReward_lt_positiveResponsePolicy_of_omits_positive_mass`
  covers policies that omit positive-measure positive-response trips, and
  `lemma5MarginalSetReward_lt_positiveResponsePolicy_of_accepts_negative_mass`
  covers policies that accept genuinely negative-response mass.
  `lemma5MarginalOptimizerReplacementCertificate_positiveResponse` and
  `paper_lemma5_marginal_optimizer_replacement_of_positiveResponse` package
  this into the same optimizer-replacement interface used by later Theorem 4
  code.  `acceptAllAlmostEverywhere_of_lemma5_positiveResponse_feasible_optimal`
  now derives the positive-case AE conclusion directly from restricted
  feasible optimality, and
  `paper_theorem4_measurable_accept_all_ae_unique_optimal_of_positive_response_marginal_optima`
  packages the same bridge at the two-state Theorem 4 level.  The remaining
  Lemma 5 work is no longer this interval geometry, fixed-response set
  comparison, restricted-optimality plumbing, or fixed-response certificate
  plumbing.  The first inner-regularity part of source Step 1 is also now
  compiled as `GN21FiniteOpenBallApproximation`,
  `GN21FiniteOpenIntervalApproximation`,
  `GN21FiniteIntervalPolicy`, `GN21FiniteIntervalPolicy.policy`,
  `GN21FiniteIntervalPolicy.measurableSet_policy`,
  `GN21FiniteIntervalPolicy.complexity`,
  `exists_gn21FiniteOpenBallApproximation_of_isOpen`,
  `GN21FiniteOpenBallApproximation.to_interval`,
  `exists_gn21FiniteOpenIntervalApproximation_of_isOpen`, and
  `GN21FiniteOpenIntervalApproximation.measure_symmDiff_lt`: every open trip
  policy under a finite regular measure has a finite open-interval subpolicy
  with arbitrarily small omitted mass, and its symmetric-difference error is
  the same omitted mass because it is an inner approximation.
  `GN21FiniteOpenIntervalApproximation.toFiniteIntervalPolicy` and
  `GN21FiniteOpenIntervalApproximation.toFiniteIntervalPolicy_subset` forget
  the measure bookkeeping while preserving the internal finite interval seed.
  The bounded seed domain now embeds into the generalized interval/ray domain
  through `GN21GeneralizedIntervalComponent`,
  `GN21GeneralizedIntervalPolicy`,
  `GN21FiniteIntervalPolicy.toGeneralizedIntervalPolicy`, and
  `GN21FiniteIntervalPolicy.toGeneralizedIntervalPolicy_policy`.  This matters
  because bounded intervals are enough for approximation, but not for the
  canonical Lemma 5 endpoints: accept-all, short-trip rejection, and
  middle-trip rejection use the full positive domain or unbounded positive
  rays.  The generalized domain has measurable policies, natural complexity,
  reward-close seed theorems
  `exists_gn21GeneralizedIntervalPolicy_reward_close` and
  `exists_gn21GeneralizedIntervalPolicy_reward_close_below`, and canonical
  representatives for all five Lemma 5 policy forms.  The converse bridge
  `exists_generalizedIntervalPolicy_eq_of_lemma5PolicyForm_of_subset_acceptAll`
  proves that every feasible policy already classified by Lemma 5 has an
  exactly equal representative in this generalized domain.
  The shape-specific complexity
  `GN21GeneralizedIntervalPolicy.lemma5ShapeComplexity` assigns complexity
  zero to already-canonical policies and a positive successor value to
  noncanonical policies.  Therefore
  `lemma5OptimizerReplacementCertificate_of_generalizedIntervalPolicy_canonical_dominance_and_maximizer`
  and `Lemma5GeneralizedIntervalPolicyCanonicalDominanceMaximizerData` let the
  endpoint proof supply a weakly improving canonical representative directly,
  without separately proving that raw interval-component count decreases.
  The policy-level wrapper
  `lemma5OptimizerReplacementCertificate_of_generalizedIntervalPolicy_policy_canonical_dominance_and_maximizer`
  is now the preferred target for endpoint calculus: it accepts ordinary
  feasible canonical `TripPolicy` replacements and uses the exact-representation
  bridge above to enter the generalized finite domain.
  The direct source-policy variant
  `lemma5OptimizerReplacementCertificate_of_policy_canonical_dominance_and_maximizer`
  returns the ordinary canonical replacement itself and records
  feasibility/measurability through
  `Lemma5PolicyCanonicalDominanceMaximizerData`.  At the two-state layer,
  `Theorem4AllMeasurablePolicyCanonicalDominanceData.to_allowed_policy_forms`
  turns those per-state certificates into the all-optimal measurable
  allowed-policy-form certificate, so future work should target policy-level
  dominance data rather than older opaque replacement packages.
  When a downstream route needs concrete canonical replacement cases instead
  of only policy-form classification, use
  `Theorem4NonsurgeAllowedReplacementData.of_optimizer_replacement_subset`,
  `Theorem4SurgeAllowedReplacementData.of_optimizer_replacement_subset`,
  `Theorem4NonsurgeAllowedReplacementData.of_policy_canonical_dominance`,
  `Theorem4SurgeAllowedReplacementData.of_policy_canonical_dominance`, and
  `Theorem4AllMeasurablePolicyCanonicalDominanceData.to_allowed_replacement_data`.
  These wrappers are noncomputable because they choose threshold parameters
  from Prop-valued Lemma 5 policy-form proofs.
  The positive-response marginal route is also packaged through
  `Theorem4NonsurgeAllowedReplacementData.of_positiveResponse_marginal` and
  `Theorem4SurgeAllowedReplacementData.of_positiveResponse_marginal`, so a
  source proof with response-shape and mass-strictness facts can enter the
  same concrete replacement interface directly.
  The fixed-response Lemma 5 endpoint is now also available in source-faithful
  almost-everywhere form.  `policyAlmostEverywhereEq` and
  `lemma5PolicyFormAlmostEverywhere` express equality modulo null symmetric
  difference, `Lemma5PositiveResponseShapeData.positive_zero_set_null` proves
  that zero-response boundary points have zero measure under `[NoAtoms μ]`,
  and `paper_lemma5_fixed_response_policy_form_ae_of_response_shape` proves
  that every measurable feasible maximizer of
  `lemma5MarginalSetReward μ response` has the appropriate five-case Lemma 5
  policy form almost everywhere.  This closes the strict-boundary ambiguity in
  the fixed-response part; the remaining source work is the nonlinear
  endpoint-selection/canonical-dominance bridge.
  The regular endpoint layer now has
  `Theorem4MeasurableEndpointCurrentBoundsRegularPolicyCanonicalDominanceCertificate`
  and
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_policy_canonical_dominance`,
  so the source closeout can combine policy-level Lemma 5 canonical dominance
  with regular endpoint data without first hand-building an allowed-policy-form
  certificate.  The same package also has `.to_regular_selection` for older
  endpoint-selection routes that require explicit allowed replacement data.
  The feasible-seed version is also compiled:
  `Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData`,
  `Theorem4MeasurableEndpointCurrentBoundsRegularFeasiblePolicyCanonicalDominanceCertificate`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_feasible_policy_canonical_dominance`,
  and the concrete replacement adapters
  `Theorem4NonsurgeAllowedReplacementData.of_feasible_policy_canonical_dominance`
  / `Theorem4SurgeAllowedReplacementData.of_feasible_policy_canonical_dominance`.
  Prefer this feasible version if the remaining endpoint argument only proves
  dominance for generalized interval/ray seeds contained in `acceptAllPolicy`.
  At the Theorem 3 boundary, use
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularPolicyCanonicalDominanceSourceAssumptions`
  and the paired `paper_theorem3_measured_structured_measurable_ic...` wrappers
  when the source proof supplies policy-level Lemma 5 dominance plus the regular
  endpoint families; use `.to_regular_source_assumptions` to feed the older
  regular selection boundary.  The analogous feasible-seed Theorem 3 boundary
  is
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularFeasiblePolicyCanonicalDominanceSourceAssumptions`,
  with IC and AE wrappers and `.to_regular_source_assumptions`.
  `GN21SymmDiffContinuousAt` and
  `exists_gn21FiniteOpenIntervalApproximation_reward_close`,
  `exists_gn21FiniteIntervalPolicy_reward_close`, and
  `exists_gn21FiniteIntervalPolicy_reward_close_below` now compose this
  approximation with the source continuity assumption to choose a concrete
  generalized interval/ray policy seed whose reward is arbitrarily close to the
  original open policy.  The finite-family descent and compactness handoff is
  also now
  compiled as `exists_canonical_ge_of_finite_descent`,
  `exists_canonical_gt_of_finite_descent`,
  `exists_canonical_arbitrarily_close_of_seed_finite_descent`,
  `target_le_canonical_maximizer_of_arbitrarily_close`,
  `exists_canonical_ge_of_arbitrarily_close_and_maximizer`,
  `lemma5OptimizerReplacementCertificate_of_finite_descent`,
  `lemma5OptimizerReplacementCertificate_of_seed_finite_descent`, and
  `lemma5OptimizerReplacementCertificate_of_domain_finite_descent_and_maximizer`,
  with the concrete finite-interval specialization
  `lemma5OptimizerReplacementCertificate_of_finiteIntervalPolicy_descent_and_maximizer`.
  The source-facing finite-interval data target is named
  `Lemma5FiniteIntervalPolicyDescentMaximizerData`, with
  `Lemma5FiniteIntervalPolicyDescentMaximizerData.to_optimizer_replacement`,
  `Lemma5FiniteIntervalPolicyDescentMaximizerData.policyForm_of_optimal`, and
  `Lemma5FiniteIntervalPolicyDescentMaximizerData.policyForm_of_candidate_le`
  converting that data into the exact optimizer-replacement and policy-form
  conclusions needed by Theorem 4.  For the actual source closeout, prefer the
  generalized target
  `lemma5OptimizerReplacementCertificate_of_generalizedIntervalPolicy_descent_and_maximizer`
  and `Lemma5GeneralizedIntervalPolicyDescentMaximizerData`, whose
  `to_optimizer_replacement`, `policyForm_of_optimal`, and
  `policyForm_of_candidate_le` methods have the same downstream interface but
  can terminate in the unbounded canonical policies.
  These theorems prove the source proof's termination and limit/maximizer
  bridge for any finite-policy domain with a natural-valued endpoint
  complexity.  The remaining Lemma 5 work is now the paper-specific endpoint
  step certificate for each derivative-shape case: given a noncanonical finite
  interval policy, construct the endpoint path to the next collision or
  canonical boundary, use the global endpoint-path calculus above to prove the
  weak or strict reward comparison, and show the moved policy lowers the
  chosen finite complexity.
- The Theorem 4 endpoint layer now has AE shape predicates
  `theorem4NonsurgeAEShape` and `theorem4SurgeAEShape`, plus
  `Theorem4AllMeasurableAllowedPolicyFormsCertificate.only_ae_shapes` and
  `paper_theorem4_measurable_accept_all_ae_unique_optimal_of_ae_shape_statewise_rejected_mass_improvements_unless`.
  Use this route when Lemma 5 gives exact endpoint forms for the nonpositive
  branches but only an AE accept-all conclusion for the positive branch.  On a
  positive rejected-mass branch, the AE accept-all alternative is impossible,
  so endpoint selection still reduces to the long/middle cases.
  `Theorem4MeasurableAEEndpointCurrentBoundsSelectionUnlessMiddleRerouteCertificate`
  and
  `paper_theorem4_measurable_accept_all_ae_unique_optimal_of_ae_endpoint_current_bounds_selection_unless_middle_reroute`
  thread the same AE shape classification through the preferred middle-reroute
  endpoint-current-bounds route.  The adapter
  `Theorem4MeasurableAEEndpointCurrentBoundsSelectionUnlessMiddleRerouteCertificate.of_exact_endpoint_current_bounds_selection`
  reuses existing exact endpoint data when exact replacement certificates are
  still available.
- The Theorem 3 side now consumes that AE endpoint route directly through
  `GN21Theorem3MiddleRerouteAEEndpointSourceData`,
  `theorem3AcceptAllFeasibleRejectedMassStrictLocalPositiveParameterCertificate_of_ae_endpoint_middle_reroute`,
  `Theorem3AcceptAllMeasurableAEEndpointMiddleRerouteSourceAssumptions`, and
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_ae_endpoint_middle_reroute_source_assumptions`.
  This is the current cleanest source boundary for finishing the measurable
  AE-unique version of Theorem 3: provide shared endpoint regularity plus the
  AE endpoint certificate for the constructed positive-parameter prices, and
  Lean supplies the positive-rejected-mass strict-local and IC routing.
- The nonlinear aggregate layer now has strict counterparts to the older weak
  add-set bridges:
  `gn21AggregateDynamicReward_lt_add_left_of_kernel_pos`,
  `gn21AggregateDynamicReward_lt_add_right_of_kernel_pos`,
  `gn21PrimitiveKernel_pos_of_pointwise_derivative_kernel_nonneg`,
  `gn21MeasuredAggregateRewardPrimitives_lt_union_left_of_kernel_pos`, and
  `gn21MeasuredAggregateRewardPrimitives_lt_union_right_of_kernel_pos`, plus
  the pointwise support variants
  `gn21MeasuredAggregateRewardPrimitives_lt_union_left_of_pointwise_kernel_nonneg`
  and
  `gn21MeasuredAggregateRewardPrimitives_lt_union_right_of_pointwise_kernel_nonneg`,
  plus the accept-all-complement specializations
  `gn21MeasuredAggregateRewardPrimitives_lt_acceptAll_left_of_complement_pointwise_kernel_nonneg`
  and
  `gn21MeasuredAggregateRewardPrimitives_lt_acceptAll_right_of_complement_pointwise_kernel_nonneg`,
  with current-bound Lemma 9/10 specializations
  `gn21MeasuredAggregateRewardPrimitives_lt_acceptAll_left_of_lemma10_current_bounds`
  and
  `gn21MeasuredAggregateRewardPrimitives_lt_acceptAll_right_of_lemma9_current_bounds`.
  The strict route is also packaged on the Lemma 9/10 aggregate data records as
  `GN21NonsurgeLemma10AcceptAllAggregateData.aggregate_lt_acceptAll`,
  `GN21SurgeLemma9AcceptAllAggregateData.aggregate_lt_acceptAll`, their
  primitive-data analogues, and the source-facing
  `GN21NonsurgeLemma10AcceptAllAggregateSourceData.aggregate_lt_acceptAll` /
  `GN21SurgeLemma9AcceptAllAggregateSourceData.aggregate_lt_acceptAll`
  methods.
  Positive rejected-complement mass can now discharge the support condition at
  the full-data level through `measure_support_inter_pos_of_pos_on`,
  `GN21NonsurgeLemma10AcceptAllAggregateData.aggregate_lt_acceptAll_of_rejected_measure_pos`,
  and
  `GN21SurgeLemma9AcceptAllAggregateData.aggregate_lt_acceptAll_of_rejected_measure_pos`.
  Primitive/source variants and the source-facing rejected-mass endpoint
  `paper_theorem4_measurable_accept_all_unique_optimal_of_structured_current_bounds_source_rejected_mass`
  are also compiled, so the final paper-facing task can use positive measure of
  the rejected trips rather than the lower-level support expression.
  These now feed the source-facing Theorem 4 strict-local route through
  `Theorem4MeasuredAggregateStructuredCurrentBoundsSourceFeasibleStrictCertificate`,
  `theorem4MeasuredAggregateFeasibleStrictLocalImprovementCertificate_of_structured_current_bounds_source_support`,
  and
  `paper_theorem4_measurable_accept_all_unique_optimal_of_structured_current_bounds_source_support`.
  That endpoint uses accept-all itself as the profitable replacement once the
  source current-bound data and either positive kernel support or positive
  rejected-complement mass are supplied.
  These are the useful bridge from "positive derivative kernel on positive
  mass" to an actual strict reward improvement for the quotient reward, and
  should be preferred over building more abstract wrappers when closing the
  remaining Lemma 5 endpoint step.
- For the fixed-transfer route, the lightest compiled fixed-state adapter is
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_cutoff_bounds_source_assumptions`:
  it derives the constructed parameter data, surge-ratio positivity,
  all-measurable Lemma 5 replacement certificates, allowed policy-form
  classification, density positivity, state-level current mass, fixed-state
  pointwise comparisons, fixed-state reward-rate accounting, and the older
  no-mass endpoint certificate internally.  The source proof now supplies
  ordinary allowed Lemma 5 replacement cases, nondegenerate non-surge cutoffs
  for the reject-long/accept-middle fixed-state forms, common fixed-state
  complement pointwise equality and reward-rate facts for each state, and
  ordinary surge cutoff bounds.  The branch-specific policy-form fixed-state
  packages, moving cutoff choice, and surge tail integrability are derived
  internally.  This is stronger than the paper currently gives for
  non-accept-all fixed-state branches, so it is no longer the primary closure
  target.
- If the fixed other state already accepts all trips, use the
  `...PositiveCutoffLocalData.of_other_acceptAll` constructors.  They derive
  the cross-ratio inequalities by equality, derive positive fixed-state mass
  from shared support and accept-all mass positivity, and use the Theorem 3
  accept-all accounting identities for the fixed-state accounting equation.
- If the fixed other state is non-accept-all, use
  `gn21FixedStateCross_le_union_of_increment_ratio_ge` or
  `gn21FixedStateCross_ge_union_of_increment_ratio_le` to reduce the needed
  cross-ratio direction to an increment ratio inequality on the trips added
  when passing from the current fixed-state policy to accept-all.
- The pointwise versions
  `gn21FixedStateCross_le_acceptAll_of_complement_pointwise_increment_ratio_ge`
  and
  `gn21FixedStateCross_ge_acceptAll_of_complement_pointwise_increment_ratio_le`
  now discharge those increment inequalities from pointwise rejected-complement
  comparisons.  The shared-source helpers
  `GN21RegularEndpointSharedSourceData.*_fixed_cross_*_of_complement_pointwise`
  add the accept-all/current integrability automatically, and the
  `...PositiveCutoffLocalData.of_fixed_complement_pointwise` constructors feed
  the resulting cross-ratio facts straight into the fixed-transfer local
  endpoint records.
- The fixed-state accounting equation in those local records can now be
  supplied as a measured reward-rate identity via
  `GN21RegularEndpointSharedSourceData.nonsurge_fixed_accounting_of_reward_rate`
  or
  `GN21RegularEndpointSharedSourceData.surge_fixed_accounting_of_reward_rate`;
  the helpers expand structured CTMC prices with Remark 2 and shared
  accept-all integrability restricted to the current feasible policy.  The
  `...PositiveCutoffLocalData.of_fixed_complement_pointwise_reward_rate`
  constructors combine the pointwise fixed-complement route with this
  reward-rate accounting route.
- The fixed-state-equality derived-tail cutoff-bounds source theorem asks for
  ordinary all-measurable allowed Lemma 5 replacement data and a
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailCutoffBoundsLocalEndpointCertificate`;
  the adapter chooses the upper reject-middle cutoff from `0 ≤ lo < hi`,
  derives positive tails from shared accept-all integrability,
  derives the uniform-tail package from positive tails plus continuous
  finite-interval product calculus, chooses fixed-state branches from allowed
  policy forms, builds surge moving endpoint data from the uniform tail package
  and cutoff choices,
  and then derives the fixed-state-separated certificate, the no-mass endpoint
  certificate, the mass-separated endpoint certificate, the older pointwise
  certificate, positive-cutoff endpoint data, fixed-state cross-ratios, and
  fixed-state accounting internally.  The
  shared-source helpers
  `GN21RegularEndpointSharedSourceData.surge_current_mass_pos_of_allowed_policy_form`
  and
  `GN21RegularEndpointSharedSourceData.nonsurge_current_mass_pos_of_allowed_policy_form`
  derive the two state-level mass fields from allowed policy forms, accept-all
  mass, and nondegenerate non-surge cutoffs.  The local constructors ending in
  `PointwiseRewardRateNoMassLocalData.of_fixed_complement_pointwise_eq` turn a
  fixed-state pointwise equality into the one-sided non-surge comparison or the
  two-sided surge comparisons.  The no-mass constructors ending in
  `of_other_acceptAll` discharge the fixed-state pointwise and reward-rate
  fields directly in accept-all fixed-state branches.  If the fixed-state
  target reward/equality facts are available, target the reusable common
  packages
  `GN21SurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassEqData` and
  `GN21NonsurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassEqData`
  once per optimal policy; Lean maps them to the branch-specific policy-form
  packages as needed.  If the source proof produces
  all-optimal allowed policy forms directly instead, use the sibling wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_policy_forms_fixed_state_by_policy_form_uniform_tail_source_assumptions`.
- The feasible endpoint wrappers now mirror the raw endpoint wrappers:
  `...nonsurge_feasible...reject_long...`,
  `...nonsurge_feasible...accept_middle...`,
  `...surge_feasible...tail...`,
  `...surge_feasible...reject_middle_lo...`, and
  `...surge_feasible...reject_middle_hi...`.
- The source certificate should now target
  `Theorem4MeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsCertificate`
  through a repaired current-bounds interface, rather than adding more
  fixed-state target-reward wrappers.

## What Would Fully Close The Paper

The paper is closed once Lean proves a source theorem of this form:

```lean
theorem paper_theorem3_measured_structured_measurable_ic_prices_of_continuous_source_assumptions
    (...) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21
```

where the final assumptions are standard continuous-measure regularity and the
paper's Lemma 9/10 inequalities, not any prepackaged local-improvement or
replacement certificate.
