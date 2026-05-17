import GN21DriverSurgePricing.MainTheorems

/-!
# Paper Interface: Driver Surge Pricing

This file is a compact human-facing review surface for the GN21 formalization.
The full proof ledger in `MainTheorems.lean` is large and active; this interface
starts with the central source-facing single-state results that are stable
enough for paper-vs-Lean review.
-/

open EconCSLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing
namespace PaperInterface

/-! ## Paper Definitions -/

/-- Paper single-state incentive compatibility predicate for measurable trip policies. -/
abbrev singleStateIC (R : SingleStateReward) : Prop :=
  singleStateMeasurableIncentiveCompatible R

/-- Paper threshold-policy shape predicate. -/
abbrev thresholdPolicy (w : PricingFunction) (c : ℝ) (sigma : TripPolicy) : Prop :=
  thresholdRatePolicy w c sigma

/-! ## Single-State Source Claims -/

/--
Proposition 3.1 source-facing measurable IC endpoint: in the continuous
single-state model with affine pricing `w(τ)=mτ+a`, the paper condition
`0 <= a <= m/λ` makes accepting all positive-length trips optimal among all
measurable feasible policies.
-/
theorem proposition3_1_affine_single_state_measurable_ic
    (mu : Measure TripLength) (arrivalRate m a : ℝ)
    (A : SingleStateTripMeasureAssumptions mu)
    (hlambda : 0 < arrivalRate)
    (ha_nonneg : 0 ≤ a)
    (ha_le_wait_value : a ≤ m / arrivalRate) :
    singleStateMeasurableIncentiveCompatible
      (affineSingleStateRenewalReward mu arrivalRate m a) := by
  exact
    GN21DriverSurgePricing.paper_proposition3_1_affine_single_state_measurable_ic
      mu arrivalRate m a A hlambda ha_nonneg ha_le_wait_value

/--
Proposition 3.1 renewal-reward endpoint from standard trip-distribution facts:
affine pricing is incentive compatible among measurable feasible policies for
the actual single-state renewal-reward functional whenever `0 <= a <= m/λ`.
-/
theorem proposition3_1_affine_single_state_renewal_reward_measurable_ic_of_standard_measure
    (mu : Measure TripLength) (arrivalRate m a : ℝ)
    (haccept_mass : singleStateTripMass mu acceptAllPolicy = 1)
    (hfinite_acceptAll : mu acceptAllPolicy ≠ ⊤)
    (htime_integrable_acceptAll :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy mu)
    (hlambda : 0 < arrivalRate)
    (ha_nonneg : 0 ≤ a)
    (ha_le_wait_value : a ≤ m / arrivalRate) :
    singleStateMeasurableIncentiveCompatible
      (singleStateRenewalReward mu arrivalRate (affinePricing m a)) := by
  exact
    GN21DriverSurgePricing.paper_proposition3_1_affine_single_state_renewal_reward_measurable_ic_of_standard_measure
      mu arrivalRate m a haccept_mass hfinite_acceptAll htime_integrable_acceptAll
      hlambda ha_nonneg ha_le_wait_value

/--
Theorem 1, source-facing measurable single-state threshold best response: an
optimal threshold policy exists without a zero-boundary-mass regularity
assumption.
-/
theorem theorem1_single_state_threshold_best_response_measurable
    (mu : Measure TripLength) (arrivalRate : ℝ) (w : PricingFunction)
    (hrate_measurable : Measurable (fun tau : TripLength => w tau / tau))
    (hrate_nonneg : ∀ tau : TripLength, 0 < tau → 0 ≤ w tau / tau)
    (hfinite_acceptAll : mu acceptAllPolicy ≠ ⊤)
    (hw_integrable_acceptAll : IntegrableOn w acceptAllPolicy mu)
    (htime_integrable_acceptAll :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy mu)
    (hlambda : 0 < arrivalRate)
    (hpayment_acceptAll_pos :
      0 < singleStateTripPayment mu w acceptAllPolicy) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ sigma : TripPolicy,
      thresholdRatePolicy w c sigma ∧
        singleStateMeasurableOptimal
          (singleStateRenewalReward mu arrivalRate w) sigma := by
  exact
    GN21DriverSurgePricing.paper_theorem1_single_state_threshold_best_response_measurable
      mu arrivalRate w hrate_measurable hrate_nonneg hfinite_acceptAll
      hw_integrable_acceptAll htime_integrable_acceptAll hlambda
      hpayment_acceptAll_pos

/-! ## Dynamic Multiplicative Pricing -/

/--
Theorem 2 policy-shape route from the Theorem 4 shape-derivation boundary:
when the non-surge Lemma 5 branch is positive/decreasing and the surge branch
is positive/increasing, the optimal policy has the paper's multiplicative
shape.  The non-surge statement allows the paper's `t = infinity` case as
accept-all.
-/
theorem theorem2_multiplicative_extended_policy_shape_of_shape_derivation
    (R : DynamicReward)
    (C : Theorem4ShapeDerivationCertificate R)
    (hnonsurge :
      C.nonsurge_shape = .positive ∨
        C.nonsurge_shape = .strictlyDecreasing)
    (hsurge :
      C.surge_shape = .positive ∨
        C.surge_shape = .strictlyIncreasing) :
    dynamicOptimal R C.policy ∧
      rejectsLongTripsFiniteOrInfiniteCutoff (C.policy 0) ∧
      (∃ t : ℝ, rejectsShortTrips t (C.policy 1)) := by
  exact
    GN21DriverSurgePricing.paper_theorem2_multiplicative_extended_policy_shape_of_shape_derivation
      R C hnonsurge hsurge

/--
Measurable-domain version of the Theorem 4-to-Theorem 2 multiplicative
policy-shape route.
-/
theorem theorem2_multiplicative_extended_measurable_policy_shape_of_shape_derivation
    (R : DynamicReward)
    (C : Theorem4MeasurableShapeDerivationCertificate R)
    (hnonsurge :
      C.nonsurge_shape = .positive ∨
        C.nonsurge_shape = .strictlyDecreasing)
    (hsurge :
      C.surge_shape = .positive ∨
        C.surge_shape = .strictlyIncreasing) :
    dynamicMeasurableOptimal R C.policy ∧
      rejectsLongTripsFiniteOrInfiniteCutoff (C.policy 0) ∧
      (∃ t : ℝ, rejectsShortTrips t (C.policy 1)) := by
  exact
    GN21DriverSurgePricing.paper_theorem2_multiplicative_extended_measurable_policy_shape_of_shape_derivation
      R C hnonsurge hsurge

/-! ## Structured Dynamic Pricing -/

/--
Lemma 9 source feasibility in measured form: regular GN21 source data and
positive surge accept-all mass imply that the Lemma 9 ratio interval is
nonempty for every feasible current non-surge policy.
-/
theorem lemma9_constraint_set_feasible_for_current_nonsurge
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (rho : Fin 2 → TripPolicy)
    (S : GN21RegularEndpointSharedSourceData mu arrival switch12 switch21)
    (hrho_feasible : dynamicFeasibleMeasurablePolicy rho)
    (hsurge_acceptAll_mass_pos : 0 < mu 1 acceptAllPolicy) :
    ∃ ratio : ℝ,
      0 < ratio ∧
        lemma9StructuredBounds ratio
          (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
          (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
          (gn21AcceptAllScaledStateTime (mu 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12)
          switch21 := by
  exact
    S.lemma9_structured_bounds_feasible_for_current_nonsurge
      hrho_feasible hsurge_acceptAll_mass_pos

/--
Lemma 10 source feasibility in measured form: regular GN21 source data and
positive non-surge accept-all mass imply that the Lemma 10 ratio interval is
nonempty for every feasible current surge policy.
-/
theorem lemma10_constraint_set_feasible_for_current_surge
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (rho : Fin 2 → TripPolicy)
    (S : GN21RegularEndpointSharedSourceData mu arrival switch12 switch21)
    (hrho_feasible : dynamicFeasibleMeasurablePolicy rho)
    (hnonsurge_acceptAll_mass_pos : 0 < mu 0 acceptAllPolicy) :
    ∃ ratio : ℝ,
      lemma10StructuredBounds ratio
        (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
        (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
        (gn21AcceptAllScaledStateTime (mu 0) (arrival 0))
        (gn21AcceptAllExitWeightIntegral (mu 0) (arrival 0) switch12 switch21)
        switch12 := by
  exact
    S.lemma10_structured_bounds_feasible_for_current_surge
      hrho_feasible hnonsurge_acceptAll_mass_pos

/--
Theorem 3 scalar bridge for the mass-affine source boundary: the
arrival/intercept condition `arrival_0*z_0 <= R2` follows from the
dimensionless numerator inequality on the constructed non-surge ratio.
-/
theorem theorem3_arrival_nonsurge_z_le_R2_of_ratio_numerator_bound
    (rho R2 T1 Q1 switch12 arrival0 : ℝ)
    (hR2_nonneg : 0 ≤ R2)
    (hden_pos : 0 < Q1 - switch12)
    (hbound : arrival0 * (rho * T1 - (T1 - 1)) ≤ Q1 - switch12) :
    arrival0 *
        (theorem3NonsurgeZRatio rho T1 Q1 switch12 * R2) ≤ R2 := by
  exact
    GN21DriverSurgePricing.theorem3_arrival_nonsurge_z_le_R2_of_ratio_numerator_bound
      rho R2 T1 Q1 switch12 arrival0 hR2_nonneg hden_pos hbound

/--
Theorem 3 positive-mass IC on the mass-affine small-surge route: the source
provides the current Lemma 9 final-sign inequality and the scalar
arrival/intercept numerator bound; Lean derives the selected-price lower slack
and the zero-ratio side condition internally.
-/
theorem theorem3_positive_mass_measurable_ic_of_mass_affine_current_final_sign
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeMassAffineCurrentLowerFinalSignArrivalBoundDataAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_lower_final_sign_arrival_bound_data_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Canonical source-facing Theorem 3 endpoint at the positive-replacement
boundary: constructed-price algebra and Lemma 9/10 primitive scalar conditions
are discharged in Lean; the source supplies the positive Lemma 5 replacement
proof for the constructed prices.
-/
theorem theorem3_structured_ic_of_positive_replacement
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllPositiveReplacementSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredICConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_ic_prices_of_positive_replacement_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Canonical source-facing Theorem 3 endpoint at the allowed-replacement
boundary: Lean constructs the price family and reduces IC to the continuous
Theorem 4 allowed-replacement certificate for those constructed prices.
-/
theorem theorem3_structured_ic_of_allowed_replacement
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllAllowedReplacementSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredICConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_ic_prices_of_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Canonical source-facing Theorem 3 endpoint at the endpoint-bridge boundary:
the remaining source obligation is to build the paper's continuous endpoint
bridge certificate for each constructed price vector.
-/
theorem theorem3_structured_ic_of_endpoint_bridge
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllAllowedReplacementEndpointBridgeSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredICConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_ic_prices_of_endpoint_bridge_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the exact endpoint current-bounds selection route: exact endpoint
selections imply structured measurable IC and the paper's a.e. uniqueness
convention.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_endpoint_current_bounds_selection
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointCurrentBoundsSelectionSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_current_bounds_selection_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the source-facing allowed-replacement endpoint-current-bounds
route.  Lean expands the allowed replacement and endpoint data into exact
Theorem 4 accept-all uniqueness, then returns a.e. uniqueness.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_endpoint_current_bounds_allowed_replacement
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointCurrentBoundsAllowedReplacementSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_current_bounds_allowed_replacement_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the supported endpoint-current-bounds route with density support
and product-calculus endpoint packages.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_endpoint_current_bounds_supported
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointCurrentBoundsSupportedSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_current_bounds_supported_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the regular endpoint-current-bounds route with continuous density
and source Lemma 9/10 current-bounds endpoint packages.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_endpoint_current_bounds_regular
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_current_bounds_regular_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the source-data feasible current-bounds route: for each
constructed price vector, the source supplies only the Lemma 9/10 current-bound
data and fixed-state reward-rate fields needed by the continuous endpoint
proof.  Lean derives structured measurable IC and a.e. uniqueness.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_current_bounds_source_feasible
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredCurrentBoundsSourceFeasibleSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_current_bounds_source_feasible_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the accounting-form feasible current-bounds route: the fixed-state
fields are supplied as the structured-price accounting equations from Remark 2.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_current_bounds_accounting
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredCurrentBoundsAccountingSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_current_bounds_accounting_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the reward-rate feasible current-bounds route: the fixed-state
fields are supplied as measured reward-rate equalities, matching the Lemma 9/10
source phrasing after fixing the current policy.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_current_bounds_reward_rate
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredCurrentBoundsRewardRateSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_current_bounds_reward_rate_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the direct measure-theoretic AE endpoint middle-reroute route:
the endpoint certificate supplies a.e. Lemma 5 shape classification and the
four local endpoint moves, while Lean derives structured measurable IC and
a.e. uniqueness for all measurable optima.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_ae_endpoint_middle_reroute
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableAEEndpointMiddleRerouteSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_ae_endpoint_middle_reroute_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the positive-parameter endpoint-current-bounds middle-reroute
route: exact endpoint selections with the branch-local non-accept-all
hypothesis give structured measurable IC and a.e. uniqueness.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_endpoint_current_bounds_middle_reroute
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointCurrentBoundsSelectionUnlessMiddleReroutePositiveSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_current_bounds_selection_unless_middle_reroute_positive_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the exact one-threshold endpoint route with finite exact cutoffs
required only in non-accept-all branches.  This matches the paper's extended
cutoff convention while still proving the measurable IC and a.e.-uniqueness
conclusion.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_exact_non_accept_all_endpoint_selection
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointCurrentBoundsExactOneThresholdNonAcceptAllSelectionUnlessSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_current_bounds_exact_one_threshold_non_accept_all_selection_unless_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the fixed-transfer exact one-threshold route with finite exact
cutoffs required only in non-accept-all branches.  This is the source-facing
fixed-transfer version of the extended-cutoff endpoint selector.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_exact_non_accept_all_fixed_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointTheorem3FixedTransferRegularExactOneThresholdNonAcceptAllSelectionUnlessSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_exact_one_threshold_non_accept_all_selection_unless_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the fixed-transfer middle-reroute route with source-facing
allowed replacement data: the exact endpoint selection derives accept-all
optimality internally and feeds the direct AE endpoint route, yielding the
paper's a.e. uniqueness convention.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_fixed_transfer_middle_reroute
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointTheorem3FixedTransferRegularAllowedReplacementMiddleRerouteSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_middle_reroute_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 source-facing measured structured-pricing endpoint on the current
paper proof route.  Lemma 6 is supplied at the sign-bracket level; the
remaining source fields are the Lemma 9/10 branch inequalities plus the
fixed-response reward-rate identifications, with the surge middle-cutoff
field required only on ordered gaps.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_bracket_ordered_cross_fields
    (mu : Fin 2 → Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableFixedResponseOneThresholdBracketOrderedSurgeCutoffCrossFieldMiddleCutoffRerouteExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_ordered_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Compatibility interface for the older all-middle cross-field source boundary;
internally it is consumed through the ordered route above.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_bracket_cross_fields
    (mu : Fin 2 → Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableFixedResponseOneThresholdBracketSurgeCutoffCrossFieldMiddleCutoffRerouteExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_bracket_surge_cutoff_cross_field_middle_cutoff_reroute_existence_source_assumptions_via_ordered
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the exact one-threshold fixed-transfer route: Lemma 6 is supplied
at the sign-bracket level, exact branch selectors choose reject-long and
reject-short optima, and the non-surge fixed-transfer condition is stated as a
pointwise equality on the rejected complement.  Lean integrates that equality
into the aggregate cross-ratio endpoint field.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_exact_bracket_pointwise_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableFixedResponseExactOneThresholdBracketBranchPointwiseTransferByPolicyFormMiddleCutoffRerouteExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_bracket_branch_pointwise_transfer_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the exact one-threshold fixed-transfer route with the non-surge
fixed-transfer side stated as the one-sided pointwise comparison on rejected
trips.  This is weaker than the equality interface above and is enough for the
aggregate cross-ratio endpoint field.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_exact_bracket_pointwise_upper_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableFixedResponseExactOneThresholdBracketBranchPointwiseUpperTransferByPolicyFormMiddleCutoffRerouteExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_bracket_branch_pointwise_upper_transfer_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the extended pointwise upper-transfer fixed-response route.  This
uses the paper's accept-all-or-finite-ray cutoff convention while retaining the
pointwise non-surge transfer comparison used to derive the endpoint cross-ratio.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_extended_branch_pointwise_upper_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableFixedResponseExtendedOneThresholdBranchPointwiseUpperTransferByPolicyFormMiddleCutoffRerouteExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_extended_one_threshold_branch_pointwise_upper_transfer_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the finite-or-infinite pointwise upper-transfer fixed-response
route.  This is the pointwise-transfer interface closest to the source's
non-surge `t = infinity` cutoff notation.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_finite_or_infinite_branch_pointwise_upper_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableFixedResponseFiniteOrInfiniteOneThresholdBranchPointwiseUpperTransferByPolicyFormMiddleCutoffRerouteExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_finite_or_infinite_one_threshold_branch_pointwise_upper_transfer_by_policy_form_middle_cutoff_reroute_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the exact one-threshold fixed-transfer route, with exact branch
selectors and replacement data derived internally.  This route does not require
nonatomic trip-length measures because it uses exact normalized branches rather
than the a.e. Lemma 5 representative boundary.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_exact_branch_fixed_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableFixedResponseExactOneThresholdBranchByPolicyFormMiddleCutoffRerouteExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_branch_by_policy_form_middle_cutoff_reroute_existence_source_assumptions_via_exact_fixed_transfer
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the extended exact-endpoint fixed-transfer route.  In each state
the source may supply either accept-all or the finite exact ray, while retaining
the exact endpoint certificate rather than weakening to the aggregate-cross
endpoint package.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_extended_branch_fixed_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointExtendedOneThresholdBranchFixedTransferExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_extended_one_threshold_branch_fixed_transfer_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the exact-endpoint finite-or-infinite fixed-transfer route.  This
is the exact-endpoint analogue of the paper's non-surge `t = infinity` cutoff
interface.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_finite_or_infinite_branch_fixed_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointFiniteOrInfiniteOneThresholdBranchFixedTransferExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_finite_or_infinite_one_threshold_branch_fixed_transfer_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the bracket-level exact one-threshold fixed-transfer route.
Lemma 6 is supplied as bracket data; exact branch selectors still let Lean
derive the all-optimal replacement field internally.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_exact_bracket_fixed_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableFixedResponseExactOneThresholdBracketBranchByPolicyFormMiddleCutoffRerouteExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_exact_one_threshold_bracket_branch_by_policy_form_middle_cutoff_reroute_existence_source_assumptions_via_exact_fixed_transfer
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the exact fixed-response branch route, lowered to the weaker
aggregate-cross fixed-transfer endpoint package consumed by Lemma 10.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_fixed_response_exact_branch_surge_cross_fixed_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableFixedResponseExactOneThresholdBranchByPolicyFormMiddleCutoffRerouteExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_exact_one_threshold_branch_surge_cross_by_policy_form_fixed_transfer_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21
      A.to_exact_branch_surge_cross_fixed_transfer_source_assumptions

/--
Theorem 3 on the bracket-level exact fixed-response route, lowered to the
aggregate-cross fixed-transfer endpoint package.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_fixed_response_exact_bracket_surge_cross_fixed_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableFixedResponseExactOneThresholdBracketBranchByPolicyFormMiddleCutoffRerouteExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_exact_one_threshold_branch_surge_cross_by_policy_form_fixed_transfer_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21
      A.to_exact_branch_surge_cross_fixed_transfer_source_assumptions

/--
Theorem 3 on the exact bracket pointwise-transfer route, lowered to the
aggregate-cross fixed-transfer endpoint package.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_exact_bracket_pointwise_transfer_surge_cross_fixed_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableFixedResponseExactOneThresholdBracketBranchPointwiseTransferByPolicyFormMiddleCutoffRerouteExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_exact_one_threshold_branch_surge_cross_by_policy_form_fixed_transfer_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21
      A.to_exact_branch_surge_cross_fixed_transfer_source_assumptions

/--
Theorem 3 on the exact bracket one-sided pointwise-transfer route, lowered to
the aggregate-cross fixed-transfer endpoint package.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_exact_bracket_pointwise_upper_transfer_surge_cross_fixed_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableFixedResponseExactOneThresholdBracketBranchPointwiseUpperTransferByPolicyFormMiddleCutoffRerouteExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_exact_one_threshold_branch_surge_cross_by_policy_form_fixed_transfer_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21
      A.to_exact_branch_surge_cross_fixed_transfer_source_assumptions

/--
Theorem 3 on the exact fixed-transfer route with the surge fixed-state side
weakened to the aggregate cross-ratio endpoint package consumed by Lemma 10.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_exact_branch_surge_cross_fixed_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointExactOneThresholdBranchSurgeCrossByPolicyFormFixedTransferExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_exact_one_threshold_branch_surge_cross_by_policy_form_fixed_transfer_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the extended one-threshold fixed-transfer route with the surge
fixed-state side weakened to the aggregate cross-ratio endpoint package.  In
each state the source may supply either accept-all or the finite exact ray,
matching the paper's extended-cutoff convention.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_extended_branch_surge_cross_fixed_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointExtendedOneThresholdBranchSurgeCrossByPolicyFormFixedTransferExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_extended_one_threshold_branch_surge_cross_by_policy_form_fixed_transfer_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

/--
Theorem 3 on the finite-or-infinite one-threshold fixed-transfer route with
aggregate cross-ratio endpoint data.  This is the closest interface to the
paper's non-surge `t = infinity` cutoff notation.
-/
theorem theorem3_structured_measurable_ic_ae_unique_of_finite_or_infinite_branch_surge_cross_fixed_transfer
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllMeasurableEndpointFiniteOrInfiniteOneThresholdBranchSurgeCrossByPolicyFormFixedTransferExistenceSourceAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_finite_or_infinite_one_threshold_branch_surge_cross_by_policy_form_fixed_transfer_existence_source_assumptions
      mu arrival rho R1 R2 switch12 switch21 A

end PaperInterface
end GN21DriverSurgePricing
