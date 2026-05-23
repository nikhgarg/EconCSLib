import GN21DriverSurgePricing.InterfaceAliases

/-!
# Paper Interface: Driver Surge Pricing

This is the compact human-review surface for the GN21 driver surge-pricing
formalization.  It mirrors the source-paper definitions and named results in
DAG order.  The larger compatibility alias layer lives in `InterfaceAliases.lean`;
the source-numbered importable audit ledger lives in `PostPaperAudit.lean`.
-/

namespace GN21DriverSurgePricing
namespace PaperInterface

/-! ## Section 2 model definitions -/

/-- Definition: single-state incentive compatibility. -/
abbrev review_definition_single_state_ic :=
  @definition_single_state_ic

/-- Definition: two-state dynamic incentive compatibility. -/
abbrev review_definition_dynamic_ic :=
  @definition_dynamic_ic

/-- Definition: threshold policies. -/
abbrev review_definition_threshold_policy :=
  @definition_threshold_policy

/-- Definition: dynamic reward with positive-mass denominators. -/
abbrev review_definition_dynamic_defined_reward :=
  @definition_dynamic_defined_reward

/-- Section 2.2: IID renewal-reward bridge for the single-state formula. -/
abbrev review_section2_single_state_renewal_reward_iid_bridge :=
  @section2_single_state_renewal_reward_iid_bridge

/-! ## Single-state results -/

/-- Proposition 3.1: affine single-state pricing is incentive compatible. -/
abbrev review_proposition3_1_affine_single_state_ic :=
  @proposition3_1_affine_single_state_ic

/-- Theorem 1: optimal single-state policies are threshold policies. -/
abbrev review_theorem1_single_state_threshold_best_response :=
  @theorem1_single_state_threshold_best_response

/-- Lemma 4: threshold optimizer uniqueness up to null sets. -/
abbrev review_lemma4_single_state_threshold_uniqueness :=
  @lemma4_single_state_threshold_uniqueness

/-! ## CTMC reward and probability lemmas -/

/-- Lemma 1: dynamic reward decomposition. -/
abbrev review_lemma1_measured_dynamic_reward_decomposition :=
  @lemma1_measured_dynamic_reward_decomposition

/-- Lemma 2: CTMC switch-probability formula. -/
abbrev review_lemma2_switch_probability_formula :=
  @lemma2_switch_probability_formula

/-- Lemma 3: state time-fraction formula. -/
abbrev review_lemma3_measured_time_fraction_formula :=
  @lemma3_measured_time_fraction_formula

/-- Remark 1: switch probability per unit time is strictly decreasing. -/
abbrev review_remark1_switch_probability_per_time_strictAntiOn :=
  @remark1_switch_probability_per_time_strictAntiOn

/-- Remark 3: small-time switch probability per unit time tends to the switch rate. -/
abbrev review_remark3_switch_probability_per_time_tendsto_at_zero :=
  @remark3_switch_probability_per_time_tendsto_at_zero

/-- Remark 4: `lambda * t - q(t)` is nonnegative. -/
abbrev review_remark4_switch_time_minus_switch_probability_nonneg :=
  @remark4_switch_time_minus_switch_probability_nonneg

/-! ## Lemma 5--10 response-shape chain -/

/-- Lemma 5: fixed-response feasible policy form almost everywhere. -/
abbrev review_lemma5_fixed_response_policy_form :=
  @lemma5_fixed_response_policy_form

/-- Lemma 6: upper-endpoint derivative formula. -/
abbrev review_lemma6_upper_endpoint_derivative_formula :=
  @lemma6_upper_endpoint_derivative_formula

/-- Lemma 7: positive-additive affine response is quasi-convex. -/
abbrev review_lemma7_affine_positive_additive_response_quasi_convex :=
  @lemma7_affine_positive_additive_response_quasi_convex

/-- Lemma 8: negative-additive affine response is quasi-concave. -/
abbrev review_lemma8_affine_negative_additive_response_quasi_concave :=
  @lemma8_affine_negative_additive_response_quasi_concave

/-- Lemma 9: surge-state derivative positivity under accept-all bounds. -/
abbrev review_lemma9_surge_derivative_positive_of_acceptAll_bounds :=
  @lemma9_surge_derivative_positive_of_acceptAll_bounds

/-- Lemma 10: non-surge-state derivative positivity under accept-all bounds. -/
abbrev review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds :=
  @lemma10_nonsurge_derivative_positive_of_acceptAll_bounds

/-! ## Main dynamic theorems -/

/-- Theorem 2: multiplicative-pricing optimal-policy shape handoff. -/
abbrev review_theorem2_multiplicative_policy_shape_ae :=
  @theorem2_multiplicative_policy_shape_ae_of_feasible_ae_policy_forms

/-- Theorem 2: explicit measured multiplicative non-IC instance. -/
abbrev review_theorem2_multiplicative_measured_not_ic_explicit_atomic :=
  @theorem2_multiplicative_measured_not_ic_explicit_atomic

/-- Theorem 2: explicit profitable multiplicative deviations in both states. -/
abbrev review_theorem2_multiplicative_profitable_deviations_both_states :=
  @theorem2_multiplicative_measured_profitable_deviations_both_states_explicit_atomic

/-- Theorem 2: positive finite cutoff deviations in both states. -/
abbrev review_theorem2_multiplicative_positive_finite_cutoff_deviations_both_states :=
  @theorem2_multiplicative_measured_profitable_positive_finite_cutoff_deviations_both_states_explicit_atomic

/-- Theorem 2: explicit both-state measured multiplicative non-IC instance. -/
abbrev review_theorem2_multiplicative_measured_not_ic_both_states :=
  @theorem2_multiplicative_measured_not_ic_both_states_explicit_atomic

/-- Theorem 4: structural representatives for optimal policies. -/
abbrev review_theorem4_structural_policy_representatives :=
  @theorem4_structural_policy_representatives_of_gn21_bracket_source_data

/-- Theorem 4: accept-all a.e. uniqueness route used by Theorem 3. -/
abbrev review_theorem4_acceptAll_ae_unique_of_current_bounds_source :=
  @theorem4_acceptAll_ae_unique_of_current_bounds_source

/-- Theorem 3: feasibility threshold lies in the admissible interval. -/
abbrev review_theorem3_feasibility_threshold :=
  @theorem3_feasibility_threshold

/-- Theorem 3: denominator-valid positive-mass source endpoint. -/
abbrev review_theorem3_positive_mass_source :=
  @theorem3_positive_mass_source

/-- Theorem 3: direct positive-response source proof line. -/
abbrev review_theorem3_positive_response :=
  @theorem3_positive_response

/-- Theorem 3: fixed-response source records imply the positive-response endpoint. -/
abbrev review_theorem3_positive_fixed_response_normalized :=
  @theorem3_positive_fixed_response_normalized

/-- Theorem 3: positive-mass IC in the defined-reward interface. -/
abbrev review_theorem3_defined_reward_ic_of_positive_mass :=
  @theorem3_defined_reward_ic_of_positive_mass

/-- Theorem 3: defined-reward source endpoint. -/
abbrev review_theorem3_defined_reward_source :=
  @theorem3_defined_reward_source

/-- Theorem 3: full feasible sequential current-bounds source-data route. -/
abbrev review_theorem3_feasible_sequential_current_bounds_source_data :=
  @theorem3_feasible_sequential_current_bounds_source_data

/--
Theorem 3: visible statement for the full feasible sequential current-bounds
source-data route.  This is the main no-caveat paper-facing Theorem 3 endpoint.
-/
theorem review_theorem3_feasible_sequential_current_bounds_source_data_statement
    (mu : Fin 2 → MeasureTheory.Measure TripLength) (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredFeasibleSequentialCurrentBoundsSourceDataAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 := by
  exact
    theorem3_feasible_sequential_current_bounds_source_data
      mu arrival rho R1 R2 switch12 switch21 A

/-- Theorem 3: full measurable lift with an explicit zero-mass dominance certificate. -/
abbrev review_theorem3_source_with_zero_mass_dominance :=
  @theorem3_source_with_zero_mass_dominance

/-- Theorem 3 audit: zero-mass totalization obstruction. -/
abbrev review_theorem3_zero_mass_totalization_obstruction :=
  @theorem3_zero_mass_totalization_obstruction

/-- Theorem 3 audit: state-rate zero-mass totalization obstruction. -/
abbrev review_theorem3_zero_mass_totalization_obstruction_state_rates :=
  @theorem3_zero_mass_totalization_obstruction_state_rates

/-- Theorem 3 audit: profitable zero-mass deviations preclude the dominance certificate. -/
abbrev review_theorem3_zero_mass_dominance_impossible_of_profitable_zero_mass :=
  @theorem3_zero_mass_dominance_impossible_of_profitable_zero_mass

end PaperInterface
end GN21DriverSurgePricing
