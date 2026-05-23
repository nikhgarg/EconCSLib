import GN21DriverSurgePricing.PaperInterface

/-!
# Post-paper audit: Driver Surge Pricing

This file is the importable audit ledger for Garg--Nazerzadeh, *Driver Surge
Pricing*.  `PaperInterface.lean` is the human-facing statement surface; this
ledger gives source-numbered entrypoints for the paper definitions and named
results, while keeping the current validation boundary explicit.

Cached source text inventory checked by this audit:

- Section 2.2 driver policies and incentive compatibility, lines 264--284.
- Theorem 1, source statement and proof, lines 498 and 2530.
- Proposition 3.1, proof section, line 2759.
- Theorem 2, line 560.
- Lemma 1, lines 324 and 3032.
- Lemma 2, lines 657 and 3000.
- Lemma 3, lines 671 and 3054.
- Lemma 4, line 2841.
- Lemma 5, line 3343.
- Lemma 6, lines 3724 and 4105.
- Remarks 1, 3, and 4, lines 3747, 3793, and 3799.
- Lemmas 7 and 8, lines 3773 and 3775.
- Lemmas 9 and 10, lines 3809 and 3834.
- Theorem 4, line 3859.
- Theorem 3, lines 704 and 3944.

Theorem 3 is closed on the denominator-valid positive-mass source domain and
also has a full feasible-measurable endpoint through the source-ordered
feasible sequential Lemma 9/10 current-bounds data.  The separate
zero-mass-dominance lift remains available as an optional route, but Lean also
records why that certificate is not automatic under the current real-valued
reward totalization.
-/

namespace GN21DriverSurgePricing
namespace PostPaperAudit

/-! ## Section 2 definitions and stochastic reward bridge -/

/-- Audit endpoint for Section 2.2 single-state incentive compatibility. -/
abbrev audit_section2_single_state_ic :=
  @PaperInterface.definition_single_state_ic

/-- Audit endpoint for Section 2.2 dynamic incentive compatibility. -/
abbrev audit_section2_dynamic_ic :=
  @PaperInterface.definition_dynamic_ic

/-- Audit endpoint for Section 2.2 threshold-policy notation. -/
abbrev audit_section2_threshold_policy :=
  @PaperInterface.definition_threshold_policy

/-- Audit endpoint for the IID renewal-reward bridge behind Section 2.2. -/
abbrev audit_section2_single_state_renewal_reward_iid_bridge :=
  @PaperInterface.section2_single_state_renewal_reward_iid_bridge

/-- Audit endpoint for the denominator-valid defined dynamic reward surface. -/
abbrev audit_section2_dynamic_defined_reward :=
  @PaperInterface.definition_dynamic_defined_reward

/-! ## Single-state source results -/

/-- Audit endpoint for Theorem 1: single-state threshold best response. -/
abbrev audit_theorem1_single_state_threshold_best_response :=
  @PaperInterface.theorem1_single_state_threshold_best_response

/-- Audit endpoint for Proposition 3.1: affine single-state measurable IC. -/
abbrev audit_proposition3_1_affine_single_state_ic :=
  @PaperInterface.proposition3_1_affine_single_state_ic

/-- Audit endpoint for Lemma 4: threshold optimizer uniqueness up to null sets. -/
abbrev audit_lemma4_single_state_threshold_uniqueness :=
  @PaperInterface.lemma4_single_state_threshold_uniqueness

/-! ## CTMC reward and time-fraction lemmas -/

/-- Audit endpoint for Lemma 1: measured dynamic reward decomposition. -/
abbrev audit_lemma1_measured_dynamic_reward_decomposition :=
  @PaperInterface.lemma1_measured_dynamic_reward_decomposition

/-- Audit endpoint for Lemma 2: CTMC switch-probability formula. -/
abbrev audit_lemma2_switch_probability_formula :=
  @PaperInterface.lemma2_switch_probability_formula

/-- Audit endpoint for Remark 1: switch probability per time is strictly antitone. -/
abbrev audit_remark1_switch_probability_per_time_strictAntiOn :=
  @PaperInterface.remark1_switch_probability_per_time_strictAntiOn

/-- Audit endpoint for Remark 3: switch probability per time tends to the switch rate. -/
abbrev audit_remark3_switch_probability_per_time_tendsto_at_zero :=
  @PaperInterface.remark3_switch_probability_per_time_tendsto_at_zero

/-- Audit endpoint for Remark 4: `lambda * t - q(t)` is nonnegative. -/
abbrev audit_remark4_switch_time_minus_switch_probability_nonneg :=
  @PaperInterface.remark4_switch_time_minus_switch_probability_nonneg

/-- Audit endpoint for Lemma 3: measured state time-fraction formula. -/
abbrev audit_lemma3_measured_time_fraction_formula :=
  @PaperInterface.lemma3_measured_time_fraction_formula

/-! ## Structural response lemmas -/

/-- Audit endpoint for Lemma 5: fixed-response feasible policy form a.e. -/
abbrev audit_lemma5_fixed_response_policy_form :=
  @PaperInterface.lemma5_fixed_response_policy_form

/-- Audit endpoint for Lemma 6: upper-endpoint derivative formula. -/
abbrev audit_lemma6_upper_endpoint_derivative_formula :=
  @PaperInterface.lemma6_upper_endpoint_derivative_formula

/-- Audit endpoint for Lemma 7: positive-additive response quasi-convexity. -/
abbrev audit_lemma7_affine_positive_additive_response_quasi_convex :=
  @PaperInterface.lemma7_affine_positive_additive_response_quasi_convex

/-- Audit endpoint for Lemma 8: negative-additive response quasi-concavity. -/
abbrev audit_lemma8_affine_negative_additive_response_quasi_concave :=
  @PaperInterface.lemma8_affine_negative_additive_response_quasi_concave

/-- Audit endpoint for Lemma 9: surge derivative positivity. -/
abbrev audit_lemma9_surge_derivative_positive_of_acceptAll_bounds :=
  @PaperInterface.lemma9_surge_derivative_positive_of_acceptAll_bounds

/-- Audit endpoint for Lemma 10: non-surge derivative positivity. -/
abbrev audit_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds :=
  @PaperInterface.lemma10_nonsurge_derivative_positive_of_acceptAll_bounds

/-! ## Main dynamic theorems -/

/-- Audit endpoint for Theorem 2: multiplicative policy shape handoff. -/
abbrev audit_theorem2_multiplicative_policy_shape_ae :=
  @PaperInterface.theorem2_multiplicative_policy_shape_ae_of_feasible_ae_policy_forms

/-- Audit endpoint for Theorem 2: explicit measured multiplicative non-IC instance. -/
abbrev audit_theorem2_multiplicative_measured_not_ic_explicit_atomic :=
  @PaperInterface.theorem2_multiplicative_measured_not_ic_explicit_atomic

/-- Audit endpoint for Theorem 4: measurable structural representatives. -/
abbrev audit_theorem4_structural_policy_representatives :=
  @PaperInterface.theorem4_structural_policy_representatives_of_gn21_bracket_source_data

/-- Audit endpoint for Theorem 4's accept-all uniqueness route used by Theorem 3. -/
abbrev audit_theorem4_acceptAll_ae_unique_of_current_bounds_source :=
  @PaperInterface.theorem4_acceptAll_ae_unique_of_current_bounds_source

/-- Audit endpoint for Theorem 3: feasibility threshold `C` lies in `[0,1)`. -/
abbrev audit_theorem3_feasibility_threshold :=
  @PaperInterface.theorem3_feasibility_threshold

/-- Audit endpoint for Theorem 3: positive-mass source-domain IC and a.e. uniqueness. -/
abbrev audit_theorem3_positive_mass_source :=
  @PaperInterface.theorem3_positive_mass_source

/-- Audit endpoint for Theorem 3: positive-mass IC as a defined-reward statement. -/
abbrev audit_theorem3_defined_reward_ic_of_positive_mass :=
  @PaperInterface.theorem3_defined_reward_ic_of_positive_mass

/-- Audit endpoint for Theorem 3: source assumptions over the defined-reward interface. -/
abbrev audit_theorem3_defined_reward_source :=
  @PaperInterface.theorem3_defined_reward_source

/-- Audit endpoint for Theorem 3: full feasible sequential current-bounds source-data route. -/
abbrev audit_theorem3_feasible_sequential_current_bounds_source_data :=
  @PaperInterface.theorem3_feasible_sequential_current_bounds_source_data

/-- Audit endpoint for Theorem 3: full measurable lift with zero-mass dominance. -/
abbrev audit_theorem3_source_with_zero_mass_dominance :=
  @PaperInterface.theorem3_source_with_zero_mass_dominance

/-- Audit endpoint for the zero-mass totalization obstruction in the current reward model. -/
abbrev audit_theorem3_zero_mass_totalization_obstruction :=
  @PaperInterface.theorem3_zero_mass_totalization_obstruction

/-- Audit endpoint for the state-rate form of the zero-mass totalization obstruction. -/
abbrev audit_theorem3_zero_mass_totalization_obstruction_state_rates :=
  @PaperInterface.theorem3_zero_mass_totalization_obstruction_state_rates

/-- Audit endpoint for the impossibility of zero-mass dominance after a profitable zero-mass deviation. -/
abbrev audit_theorem3_zero_mass_dominance_impossible_of_profitable_zero_mass :=
  @PaperInterface.theorem3_zero_mass_dominance_impossible_of_profitable_zero_mass

end PostPaperAudit
end GN21DriverSurgePricing
