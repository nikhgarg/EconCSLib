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

open MeasureTheory

/-! ## Section 2 model definitions -/

/--
Definition: single-state incentive compatibility.  Accepting all feasible trips
is optimal: every measurable feasible one-state trip policy earns no more than
accept-all.

Source status: direct paper definition
Source note: Paper source map uses `source.txt` lines 269--275.
-/
def review_definition_single_state_ic (R : SingleStateReward) : Prop :=
  ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ → R σ ≤ R acceptAllPolicy

/--
Definition: two-state dynamic incentive compatibility.  Accepting all feasible
trips in both CTMC states is optimal against dynamic policy deviations.

Source status: direct paper definition
Source note: Paper source map uses `source.txt` lines 269--275.
-/
def review_definition_dynamic_ic (R : DynamicReward) : Prop :=
  (∀ i : Fin 2, acceptAllDynamicPolicy i ⊆ acceptAllPolicy ∧
      MeasurableSet (acceptAllDynamicPolicy i)) ∧
    ∀ σ : Fin 2 → TripPolicy,
      (∀ i : Fin 2, σ i ⊆ acceptAllPolicy ∧ MeasurableSet (σ i)) →
        R σ ≤ R acceptAllDynamicPolicy

/--
Definition: threshold policies.  A trip policy accepts exactly the positive
trip lengths whose payment-per-time `w τ / τ` is at least the cutoff `c`.

Source status: direct paper definition
Source note: Paper source map uses `source.txt` lines 2149--2152.
-/
def review_definition_threshold_policy (w : PricingFunction) (c : ℝ) (sigma : TripPolicy) :
    Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → (τ ∈ sigma ↔ c ≤ w τ / τ)

/--
Definition: dynamic reward with positive-mass denominators.  The Appendix D
reward formulas are formalized as a reward value defined on feasible dynamic
policies where the accepted-trip mass denominators are positive.

Source status: source-domain formalization
Source note: Paper source map uses `source.txt` lines 308--319; this row makes the paper's implicit positive-denominator domain explicit.
-/
def review_definition_dynamic_defined_reward (mu : Fin 2 → MeasureTheory.Measure TripLength) :
    Type :=
  (σ : Fin 2 → TripPolicy) →
    ((∀ i : Fin 2, σ i ⊆ acceptAllPolicy ∧ MeasurableSet (σ i)) ∧
      ∀ i : Fin 2, 0 < singleStateTripMass (mu i) (σ i)) →
      ℝ

/--
Section 2.2: IID renewal-reward bridge for the single-state formula.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 279--292.
-/
abbrev review_section2_single_state_renewal_reward_iid_bridge := @section2_single_state_renewal_reward_iid_bridge

/-! ## Single-state results -/

/--
Proposition 3.1: affine single-state pricing is incentive compatible.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` line 499.
-/
abbrev review_proposition3_1_affine_single_state_ic := @proposition3_1_affine_single_state_ic

/--
Theorem 1: optimal single-state policies are threshold policies.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 455--459.
-/
abbrev review_theorem1_single_state_threshold_best_response := @theorem1_single_state_threshold_best_response

/--
Lemma 4: threshold optimizer uniqueness up to null sets.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 2375--2379.
-/
abbrev review_lemma4_single_state_threshold_uniqueness := @lemma4_single_state_threshold_uniqueness

/-! ## CTMC reward and probability lemmas -/

/--
Lemma 1: dynamic reward decomposition.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 2492--2502.
-/
abbrev review_lemma1_measured_dynamic_reward_decomposition := @lemma1_measured_dynamic_reward_decomposition

/--
Lemma 2: CTMC switch-probability formula.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 2470--2474.
-/
abbrev review_lemma2_switch_probability_formula := @lemma2_switch_probability_formula

/--
Lemma 3: state time-fraction formula.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 2503--2510.
-/
abbrev review_lemma3_measured_time_fraction_formula := @lemma3_measured_time_fraction_formula

/--
Remark 1: switch probability per unit time is strictly decreasing.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3050--3068.
-/
abbrev review_remark1_switch_probability_per_time_strictAntiOn := @remark1_switch_probability_per_time_strictAntiOn

/--
Remark 3: small-time switch probability per unit time tends to the switch rate.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` line 3089.
-/
abbrev review_remark3_switch_probability_per_time_tendsto_at_zero := @remark3_switch_probability_per_time_tendsto_at_zero

/--
Remark 4: `lambda * t - q(t)` is nonnegative.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3091--3092.
-/
abbrev review_remark4_switch_time_minus_switch_probability_nonneg := @remark4_switch_time_minus_switch_probability_nonneg

/-! ## Lemma 5--10 response-shape chain -/

/--
Lemma 5: fixed-response feasible policy form almost everywhere.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 2689--2720.
-/
abbrev review_lemma5_fixed_response_policy_form := @lemma5_fixed_response_policy_form

/--
Lemma 6: upper-endpoint derivative formula.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3042--3049.
-/
abbrev review_lemma6_upper_endpoint_derivative_formula := @lemma6_upper_endpoint_derivative_formula

/--
Lemma 7: positive-additive affine response is quasi-convex.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3072--3073.
-/
abbrev review_lemma7_affine_positive_additive_response_quasi_convex := @lemma7_affine_positive_additive_response_quasi_convex

/--
Lemma 8: negative-additive affine response is quasi-concave.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3075--3076.
-/
abbrev review_lemma8_affine_negative_additive_response_quasi_concave := @lemma8_affine_negative_additive_response_quasi_concave

/--
Lemma 9: surge-state derivative positivity under accept-all bounds.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3099--3108.
-/
abbrev review_lemma9_surge_derivative_positive_of_acceptAll_bounds := @lemma9_surge_derivative_positive_of_acceptAll_bounds

/--
Lemma 10: non-surge-state derivative positivity under accept-all bounds.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3114--3123.
-/
abbrev review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds := @lemma10_nonsurge_derivative_positive_of_acceptAll_bounds

/-! ## Main dynamic theorems -/

/--
Theorem 2: multiplicative-pricing optimal-policy shape handoff.

Lean states the policy-shape clause separately from the explicit non-IC
counterexample because the paper's theorem combines a structural statement with
an existential example.

Source status: source-facing theorem split
Source note: Paper source map uses `source.txt` lines 516--539; Lean separates the policy-shape clause from the explicit non-IC witness.
-/
theorem review_theorem2_multiplicative_policy_shape_ae
    (mu : Fin 2 → MeasureTheory.Measure TripLength) (R : DynamicReward)
    (forms : Theorem4AllMeasurableFeasibleAEPolicyFormData mu R)
    (hnonsurge :
      ∀ rho : Fin 2 → TripPolicy, (hrho : dynamicMeasurableOptimal R rho) →
        let D := forms.nonsurge rho hrho
        D.1.1 = .positive ∨ D.1.1 = .strictlyDecreasing)
    (hsurge :
      ∀ rho : Fin 2 → TripPolicy, (hrho : dynamicMeasurableOptimal R rho) →
        let D := forms.surge rho hrho
        D.1.1 = .positive ∨ D.1.1 = .strictlyIncreasing) :
    (∃ rho : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal R rho ∧
        rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 0) (rho 0) ∧
        rejectsShortTripsAlmostEverywhere (mu 1) (rho 1)) ∧
      ∀ rho : Fin 2 → TripPolicy, dynamicMeasurableOptimal R rho →
        rejectsLongTripsFiniteOrInfiniteCutoffAlmostEverywhere (mu 0) (rho 0) ∧
          rejectsShortTripsAlmostEverywhere (mu 1) (rho 1) :=
    theorem2_multiplicative_policy_shape_ae_of_feasible_ae_policy_forms
      mu R forms hnonsurge hsurge

/--
Theorem 2: explicit multiplicative-pricing instance with positive finite
cutoff deviations in both states, and hence measured dynamic non-IC.

Source status: source-facing theorem split
Source note: Paper source map uses `source.txt` lines 516--539; Lean supplies a concrete measured atomic witness for the paper's non-IC existence claim.
-/
theorem review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states :
    (((0 < (2 : ℝ) ∧
        rejectsLongTrips 2 (theorem2BothStatesAtomicNonsurgeDeviation 0)) ∧
      dynamicProfitableDeviation
        (gn21MeasuredDynamicRewardFunctional theorem2BothStatesAtomicMu
          theorem2BothStatesAtomicArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
          (fun i => multiplicativePricing (theorem2BothStatesAtomicM i)))
        theorem2BothStatesAtomicNonsurgeDeviation) ∧
      ((0 < (2 : ℝ) ∧
          rejectsShortTrips 2 (theorem2BothStatesAtomicSurgeDeviation 1)) ∧
        dynamicProfitableDeviation
          (gn21MeasuredDynamicRewardFunctional theorem2BothStatesAtomicMu
            theorem2BothStatesAtomicArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
            (fun i => multiplicativePricing (theorem2BothStatesAtomicM i)))
          theorem2BothStatesAtomicSurgeDeviation)) ∧
      ¬ dynamicIncentiveCompatible
        (gn21MeasuredDynamicRewardFunctional theorem2BothStatesAtomicMu
          theorem2BothStatesAtomicArrival ((1 : ℝ) / 4) ((1 : ℝ) / 4)
          (fun i => multiplicativePricing (theorem2BothStatesAtomicM i))) :=
    ⟨theorem2_multiplicative_measured_profitable_positive_finite_cutoff_deviations_both_states_explicit_atomic,
      theorem2_multiplicative_measured_not_ic_both_states_explicit_atomic⟩

/--
Theorem 4: structural representatives for optimal policies.

Source status: source-facing theorem summary
Source note: Paper source map uses `source.txt` lines 3128--3148.
-/
abbrev review_theorem4_structural_policy_representatives := @theorem4_structural_policy_representatives_of_gn21_bracket_source_data

/--
Theorem 3: visible statement for the full feasible sequential current-bounds
source-data route.  This is the main no-caveat paper-facing Theorem 3 endpoint.

Source status: source-facing theorem endpoint
Source note: Paper source map uses `source.txt` lines 3216--3232; Lean exposes the feasible sequential current-bounds source-data assumptions used by the paper proof path.
-/
theorem review_theorem3_feasible_sequential_current_bounds_source_data_statement
    (mu : Fin 2 → MeasureTheory.Measure TripLength) (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredFeasibleSequentialCurrentBoundsSourceDataAssumptions
        mu arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      mu arrival R1 R2 switch12 switch21 :=
    theorem3_feasible_sequential_current_bounds_source_data
      mu arrival rho R1 R2 switch12 switch21 A

end PaperInterface
end GN21DriverSurgePricing
