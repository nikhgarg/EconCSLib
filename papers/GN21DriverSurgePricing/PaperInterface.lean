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

end PaperInterface
end GN21DriverSurgePricing
