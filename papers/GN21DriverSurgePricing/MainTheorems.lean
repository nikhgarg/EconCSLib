import EconCSLib.Foundations.Math.QuasiConvex
import EconCSLib.Foundations.Probability.CTMC
import EconCSLib.Foundations.Probability.MDP
import EconCSLib.Foundations.Probability.MeasureInequalities
import EconCSLib.Foundations.Probability.RenewalReward
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set

open EconCSLib
open MeasureTheory
open scoped Topology ENNReal

/-!
# Paper-Facing Theorems: Driver Surge Pricing

This file is the human-facing Lean ledger for Garg--Nazerzadeh,
*Driver Surge Pricing*.  The source paper is continuous-time and uses trip
lengths in `ℝ₊`, open measurable acceptance sets, CTMC state switching, and
lifetime average reward.  The source-facing definitions below therefore keep
continuous trip-length sets and abstract reward functionals instead of replacing
the paper by a finite model.

The finite MDP declarations at the end are auxiliary library-level support for
dynamic incentive-compatibility arguments.  They are useful for discrete
approximations and later dynamic platform papers, but they are not claimed as
the continuous CTMC source theorems.

## Main declarations

- `singleStateOptimal`, `singleStateIncentiveCompatible`: paper Section 2.2
  best-response and IC predicates for continuous trip-acceptance sets.
- `singleStateTripMass`, `singleStateTripTime`, `singleStateRenewalReward`:
  source-level measure/integral reward quantities for continuous trip lengths.
- `paper_theorem1_add_positive_time_set_if_average_above_current`,
  `paper_theorem1_remove_positive_time_set_if_average_below_current`: measured
  marginal-rate algebra used in the source proof of Theorem 1.
- `strictThresholdRatePolicy`, `partialThresholdRatePolicy`,
  `thresholdRatePolicy`: paper Theorem 1 threshold structures.
- `strictThresholdPolicy`, `completeThresholdPolicy`,
  `thresholdBoundaryPolicy`: canonical continuous threshold sets, with
  measurability and boundary-rate facts.
- `measurable_affinePricing_rate` and paired threshold measurability
  specializations for affine pricing.
- `paper_theorem1_threshold_certificate_of_step_certificates`: constructor
  turning the Step 1/2/3 proof obligations into the standard threshold
  certificate interface.
- `dynamicOptimal`, `dynamicIncentiveCompatible`: dynamic-policy analogues for
  the two-state surge model.
- `gn21SwitchProb`: Section 4.1 two-state CTMC transition probability formula.
- `paper_lemma2_switch_probability_forward_equation`: the Lemma 2 closed form
  satisfies the two-state Kolmogorov forward equation.
- `paper_remark2_structured_derivative_kernel_algebra`,
  `paper_remark3_switch_probability_deriv_at_zero`,
  `paper_remark3_switch_probability_per_time_tendsto_at_zero`,
  `paper_remark1_switch_probability_per_time_deriv_neg`,
  `paper_remark1_switch_probability_per_time_strictAntiOn`,
  `paper_remark4_scaled_time_minus_exit_weight_eq_integral`: Appendix D CTMC
  and derivative-kernel algebra.
- `paper_lemma1_state_reward_rate_algebra`,
  `paper_lemma1_measured_dynamic_reward_decomposition`,
  `paper_lemma3_time_fraction_formula_algebra`,
  `paper_lemma3_measured_time_fractions_sum_to_one`: deterministic algebraic
  reductions inside the source renewal-reward proof.
- `gn21MeasuredDynamicRewardFunctional`,
  `gn21MeasuredCTMCStructuredDynamicReward`, `gn21AcceptAllScaledStateTime`,
  `gn21AcceptAllExitWeightIntegral`, and paired statewise unfolding lemmas:
  `DynamicReward` wrappers and accept-all primitive aliases for the actual
  measured two-state reward formula.
- `paper_lemma6_derivative_kernel_same_sign_response`: sign transfer from
  the Lemma 6 polynomial kernel to the normalized response after substituting
  state reward rates.
- `exists_pos_right_improvement_of_hasDerivAt_pos`,
  `exists_pos_right_decrease_of_hasDerivAt_neg`: local calculus bridges from
  endpoint derivative sign to strict nearby endpoint reward comparisons.
- `paper_lemma6_exists_pos_right_improvement_of_kernel_pos_of_endpoint_data`,
  `paper_lemma6_exists_pos_right_decrease_of_kernel_neg_of_endpoint_data`:
  endpoint-data bridges from Lemma 6 kernel sign to strict nearby reward
  comparisons.
- `gn21RejectMiddleQiPath`, `gn21RejectMiddleWiPath`,
  `gn21RejectMiddleTiPath`, and paired cutoff derivative/realization theorems:
  two-piece measured primitives for middle-rejection policies.
- `paper_lemma4_single_state_unique_threshold_of_certificate`,
  `paper_lemma5_optimizer_replacement_of_certificate`,
  `paper_lemma6_derivative_formula_of_certificate`, and
  `paper_theorem4_dynamic_structural_policy_of_certificate`: source-facing
  conditional endpoints for the appendix shape theorem chain.
- `paper_lemma7_canonical_derivative_numerator_deriv_pos`: closed calculus
  step for the affine positive-additive response used in Lemma 7.
- `paper_lemma7_affine_ctmc_response_quasi_convex`,
  `paper_lemma8_affine_ctmc_response_quasi_concave`: source affine-response
  shape theorems for Lemmas 7-8 after substituting the CTMC switch probability.
- `paper_lemma7_affine_ctmc_quasi_convex_certificate`,
  `paper_lemma8_affine_ctmc_quasi_concave_certificate`: concrete constructors
  for the older Lemma 7-8 certificate interfaces from CTMC sign assumptions.
- `paper_lemma5_strictQuasiConvex_response_lt_of_between`,
  `paper_lemma5_strictQuasiConcave_response_lt_between`: source-facing
  between-endpoint shape facts used in Lemma 5 interval arguments.
- `lemma5DerivativeShapeWitness_strictlyQuasiConvex_of_lemma7_affine_ctmc_response`,
  `lemma5DerivativeShapeWitness_strictlyQuasiConcave_of_lemma8_affine_ctmc_response`:
  bridge Lemmas 7-8 response shapes into Lemma 5's derivative-shape interface.
- `theorem4NonsurgeShape_of_lemma5_strictlyDecreasing`,
  `theorem4SurgeShape_of_lemma5_strictlyQuasiConvex`, and paired helpers:
  pure routing from Lemma 5 policy forms to Theorem 4's structural alternatives.
- `paper_theorem4_dynamic_structural_policy_of_shape_derivation`: Theorem 4
  assembly from a Lemma 5-style shape derivation certificate.
- `paper_proposition3_1_affine_accept_all_ge_complement_reward_of_rejected_set`:
  direct measure/integral affine-pricing reward step from Proposition 3.1.
- `paper_proposition3_1_affine_accept_all_ge_rejecting_measurable_set`:
  Proposition 3.1 measured-policy statement for measurable rejected subsets.
- `singleStateTripMeasureAssumptions_of_standard`: constructor deriving the
  routine Proposition 3.1 measure assumptions from standard distribution facts.
- `singleStateTripMass_eq_zero_of_time_zero_subset_acceptAll`: measure-theoretic
  bridge that zero total positive trip time implies zero mass for feasible sets.
- `paper_proposition3_1_affine_single_state_measurable_ic`: Proposition 3.1
  measurable-policy IC endpoint for the continuous single-state reward model.
- `paper_theorem1_single_state_threshold_best_response_of_certificate`,
  `paper_theorem2_multiplicative_not_ic_of_witness`, and
  `paper_theorem3_structured_prices_ic_of_certificate`: conditional
  source-facing wrappers that name the remaining continuous certificates.
- `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_global_statewise_accept_all_reward`:
  measured Theorem 3 endpoint that constructs the structured CTMC prices and
  concludes IC for the actual measured reward functional once the global
  reward-improvement proof is supplied.
- `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_strict_local_improvements`:
  measured Theorem 3 endpoint for the derivative-proof route where every
  optimal non-accept-all policy has a strict aggregate local improvement.
- `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_lemma910_interval_bridges`:
  measured Theorem 3 endpoint that consumes the combined Lemma 9/10 interval
  bridge certificate directly.
- `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_lemma910_endpoint_bridges`:
  measured Theorem 3 endpoint that consumes generalized endpoint bridge data,
  including upper, lower, tail, and reject-middle endpoint moves.
- `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_global_statewise_accept_all_reward`:
  measured Theorem 3 endpoint with `T_i,Q_i` specialized to accept-all measured
  primitives and scalar positivity obligations derived from CTMC/measure
  assumptions.
- `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_measured_aggregate_strict_local_improvements`:
  the corresponding accept-all-primitive endpoint for the strict local
  aggregate-improvement route.
- `GN21SurgeIntervalEndpointBridgeData`,
  `GN21NonsurgeIntervalEndpointBridgeData`, and
  `Theorem4Lemma910IntervalBridgeCertificate`: data packages for the remaining
  Lemma 9/10 interval endpoint identification step, with constructors into the
  measured aggregate strict-local interface.
- `paper_aux_finite_dynamic_pricing_ic_of_greedy`,
  `paper_aux_finite_dynamic_pricing_not_ic_of_profitable_deviation`: closed
  finite MDP support lemmas.
-/

namespace GN21DriverSurgePricing

noncomputable section

/-- Continuous trip length, represented directly as a real number. -/
abbrev TripLength := ℝ

/-- A driver acceptance policy in one world state: the set of accepted trip lengths. -/
abbrev TripPolicy := Set TripLength

/-- Driver pricing/payment as a function of trip length. -/
abbrev PricingFunction := TripLength → ℝ

/-- Lifetime earnings-rate functional for a one-state policy. -/
abbrev SingleStateReward := TripPolicy → ℝ

/-- Lifetime earnings-rate functional for a dynamic two-state policy. -/
abbrev DynamicReward := (Fin 2 → TripPolicy) → ℝ

/-- The source domain of positive trip lengths. -/
def positiveTripLengths : TripPolicy :=
  {τ | 0 < τ}

/-- A one-state policy accepts all feasible positive-length trip requests. -/
def acceptsAllTrips (σ : TripPolicy) : Prop :=
  positiveTripLengths ⊆ σ

/-- The accept-all one-state policy. -/
def acceptAllPolicy : TripPolicy :=
  positiveTripLengths

/-- A feasible policy that accepts all positive trips is exactly accept-all. -/
theorem eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
    {σ : TripPolicy}
    (hsubset : σ ⊆ acceptAllPolicy)
    (hall : acceptsAllTrips σ) :
    σ = acceptAllPolicy := by
  exact Set.Subset.antisymm hsubset
    (by simpa [acceptsAllTrips, acceptAllPolicy] using hall)

/-- The feasible positive-trip domain is measurable. -/
theorem measurableSet_acceptAllPolicy : MeasurableSet acceptAllPolicy := by
  simpa [acceptAllPolicy, positiveTripLengths, Set.Ioi] using
    (measurableSet_Ioi (a := (0 : ℝ)))

/-- Probability mass of a trip-length acceptance set under the trip distribution. -/
def singleStateTripMass (μ : Measure TripLength) (σ : TripPolicy) : ℝ :=
  (μ σ).toReal

/-- Expected trip time contributed by an accepted trip-length set. -/
def singleStateTripTime (μ : Measure TripLength) (σ : TripPolicy) : ℝ :=
  ∫ τ in σ, τ ∂μ

/-- Expected payment contributed by an accepted trip-length set. -/
def singleStateTripPayment
    (μ : Measure TripLength) (w : PricingFunction) (σ : TripPolicy) : ℝ :=
  ∫ τ in σ, w τ ∂μ

/--
Single-state renewal-reward formula from Section 2.2:
`λ ∫_σ w dF / (1 + λ ∫_σ τ dF)`.
-/
def singleStateRenewalReward
    (μ : Measure TripLength) (arrivalRate : ℝ)
    (w : PricingFunction) (σ : TripPolicy) : ℝ :=
  arrivalRate * singleStateTripPayment μ w σ /
    (1 + arrivalRate * singleStateTripTime μ σ)

/-- The accepted-trip average payment rate on a set of trip lengths. -/
def singleStateAverageTripRate
    (μ : Measure TripLength) (w : PricingFunction) (σ : TripPolicy) : ℝ :=
  averageRewardRate (singleStateTripPayment μ w σ) (singleStateTripTime μ σ)

/-- Single-state renewal reward is the generic renewal-reward summary applied to set integrals. -/
theorem singleStateRenewalReward_eq_renewalRewardRate
    (μ : Measure TripLength) (arrivalRate : ℝ)
    (w : PricingFunction) (σ : TripPolicy) :
    singleStateRenewalReward μ arrivalRate w σ =
      renewalRewardRate arrivalRate
        (singleStateTripPayment μ w σ) (singleStateTripTime μ σ) := by
  rfl

/--
If every trip in a positive-time set has payment at least `targetRate * τ`,
then the set's average trip rate is at least `targetRate`.
-/
theorem le_singleStateAverageTripRate_of_pointwise_le
    (μ : Measure TripLength) (w : PricingFunction) (σ : TripPolicy)
    (targetRate : ℝ)
    (hσ_measurable : MeasurableSet σ)
    (htime_integrable :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (hw_integrable : IntegrableOn w σ μ)
    (htime_pos : 0 < singleStateTripTime μ σ)
    (hpointwise : ∀ τ ∈ σ, targetRate * τ ≤ w τ) :
    targetRate ≤ singleStateAverageTripRate μ w σ := by
  unfold singleStateAverageTripRate averageRewardRate
  rw [le_div_iff₀ htime_pos]
  unfold singleStateTripPayment singleStateTripTime
  have hmono :
      ∫ τ in σ, targetRate * τ ∂μ ≤ ∫ τ in σ, w τ ∂μ := by
    exact setIntegral_mono_on (htime_integrable.const_mul targetRate)
      hw_integrable hσ_measurable hpointwise
  rw [integral_const_mul] at hmono
  exact hmono

/--
If every trip in a positive-time set has payment at most `targetRate * τ`,
then the set's average trip rate is at most `targetRate`.
-/
theorem singleStateAverageTripRate_le_of_pointwise_le
    (μ : Measure TripLength) (w : PricingFunction) (σ : TripPolicy)
    (targetRate : ℝ)
    (hσ_measurable : MeasurableSet σ)
    (htime_integrable :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (hw_integrable : IntegrableOn w σ μ)
    (htime_pos : 0 < singleStateTripTime μ σ)
    (hpointwise : ∀ τ ∈ σ, w τ ≤ targetRate * τ) :
    singleStateAverageTripRate μ w σ ≤ targetRate := by
  unfold singleStateAverageTripRate averageRewardRate
  rw [div_le_iff₀ htime_pos]
  unfold singleStateTripPayment singleStateTripTime
  have hmono :
      ∫ τ in σ, w τ ∂μ ≤ ∫ τ in σ, targetRate * τ ∂μ := by
    exact setIntegral_mono_on hw_integrable
      (htime_integrable.const_mul targetRate) hσ_measurable hpointwise
  rw [integral_const_mul] at hmono
  exact hmono

/-- Payment integral over a disjoint union of accepted trip-length sets. -/
theorem singleStateTripPayment_union
    (μ : Measure TripLength) (w : PricingFunction) (σ added : TripPolicy)
    (hdisjoint : Disjoint σ added)
    (hadded_measurable : MeasurableSet added)
    (hw_integrable_σ : IntegrableOn w σ μ)
    (hw_integrable_added : IntegrableOn w added μ) :
    singleStateTripPayment μ w (σ ∪ added) =
      singleStateTripPayment μ w σ + singleStateTripPayment μ w added := by
  unfold singleStateTripPayment
  exact setIntegral_union hdisjoint hadded_measurable
    hw_integrable_σ hw_integrable_added

/-- Trip-time integral over a disjoint union of accepted trip-length sets. -/
theorem singleStateTripTime_union
    (μ : Measure TripLength) (σ added : TripPolicy)
    (hdisjoint : Disjoint σ added)
    (hadded_measurable : MeasurableSet added)
    (htime_integrable_σ :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (htime_integrable_added :
      IntegrableOn (fun τ : TripLength => τ) added μ) :
    singleStateTripTime μ (σ ∪ added) =
      singleStateTripTime μ σ + singleStateTripTime μ added := by
  unfold singleStateTripTime
  exact setIntegral_union hdisjoint hadded_measurable
    htime_integrable_σ htime_integrable_added

/-- Payment integral after removing a measurable subset of accepted trip lengths. -/
theorem singleStateTripPayment_diff
    (μ : Measure TripLength) (w : PricingFunction) (σ removed : TripPolicy)
    (hremoved_subset : removed ⊆ σ)
    (hremoved_measurable : MeasurableSet removed)
    (hw_integrable_σ : IntegrableOn w σ μ) :
    singleStateTripPayment μ w (σ \ removed) =
      singleStateTripPayment μ w σ - singleStateTripPayment μ w removed := by
  unfold singleStateTripPayment
  exact setIntegral_diff hremoved_measurable hw_integrable_σ hremoved_subset

/-- Trip-time integral after removing a measurable subset of accepted trip lengths. -/
theorem singleStateTripTime_diff
    (μ : Measure TripLength) (σ removed : TripPolicy)
    (hremoved_subset : removed ⊆ σ)
    (hremoved_measurable : MeasurableSet removed)
    (htime_integrable_σ :
      IntegrableOn (fun τ : TripLength => τ) σ μ) :
    singleStateTripTime μ (σ \ removed) =
      singleStateTripTime μ σ - singleStateTripTime μ removed := by
  unfold singleStateTripTime
  exact setIntegral_diff hremoved_measurable htime_integrable_σ hremoved_subset

/-- A one-state policy is optimal for a reward functional. -/
def singleStateOptimal (R : SingleStateReward) (σ : TripPolicy) : Prop :=
  ∀ ρ : TripPolicy, R ρ ≤ R σ

/-- Source IC predicate: accepting every positive-length trip is optimal. -/
def singleStateIncentiveCompatible (R : SingleStateReward) : Prop :=
  singleStateOptimal R acceptAllPolicy

/-- Measurable feasible-policy version of one-state IC for continuous trip lengths. -/
def singleStateMeasurableIncentiveCompatible (R : SingleStateReward) : Prop :=
  ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ → R σ ≤ R acceptAllPolicy

/-- Accepted mass is nonnegative for any trip-length set. -/
theorem singleStateTripMass_nonneg
    (μ : Measure TripLength) (σ : TripPolicy) :
    0 ≤ singleStateTripMass μ σ := by
  unfold singleStateTripMass
  exact ENNReal.toReal_nonneg

/-- Accepted trip time is nonnegative for measurable feasible policies. -/
theorem singleStateTripTime_nonneg_of_subset_acceptAll
    (μ : Measure TripLength) (σ : TripPolicy)
    (hσ_measurable : MeasurableSet σ)
    (hσ_subset : σ ⊆ acceptAllPolicy) :
    0 ≤ singleStateTripTime μ σ := by
  unfold singleStateTripTime
  exact setIntegral_nonneg hσ_measurable (fun τ hτ =>
    le_of_lt (hσ_subset hτ))

/-- Accepted trip time is monotone among feasible policies. -/
theorem singleStateTripTime_le_acceptAll_of_subset
    (μ : Measure TripLength) (σ : TripPolicy)
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ)
    (hσ_subset : σ ⊆ acceptAllPolicy) :
    singleStateTripTime μ σ ≤ singleStateTripTime μ acceptAllPolicy := by
  unfold singleStateTripTime
  apply setIntegral_mono_set htime_integrable_acceptAll
  · exact (ae_restrict_iff' measurableSet_acceptAllPolicy).2
      (Filter.Eventually.of_forall (fun τ hτ =>
        le_of_lt (by
          simpa [acceptAllPolicy, positiveTripLengths] using hτ)))
  · exact Filter.Eventually.of_forall (fun _ hτ => hσ_subset hτ)

/-- Rejected mass is nonnegative for any feasible policy. -/
theorem singleStateTripMass_acceptAll_diff_nonneg
    (μ : Measure TripLength) (σ : TripPolicy) :
    0 ≤ singleStateTripMass μ (acceptAllPolicy \ σ) :=
  singleStateTripMass_nonneg μ (acceptAllPolicy \ σ)

/-- Rejected trip time is nonnegative for measurable feasible policies. -/
theorem singleStateTripTime_acceptAll_diff_nonneg
    (μ : Measure TripLength) (σ : TripPolicy)
    (hσ_measurable : MeasurableSet σ) :
    0 ≤ singleStateTripTime μ (acceptAllPolicy \ σ) :=
  singleStateTripTime_nonneg_of_subset_acceptAll μ (acceptAllPolicy \ σ)
    (measurableSet_acceptAllPolicy.diff hσ_measurable)
    (fun _ hτ => hτ.1)

/-- Rejected trip time is bounded by accept-all trip time. -/
theorem singleStateTripTime_acceptAll_diff_le_acceptAll
    (μ : Measure TripLength) (σ : TripPolicy)
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ) :
    singleStateTripTime μ (acceptAllPolicy \ σ) ≤
      singleStateTripTime μ acceptAllPolicy :=
  singleStateTripTime_le_acceptAll_of_subset μ (acceptAllPolicy \ σ)
    htime_integrable_acceptAll (fun _ hτ => hτ.1)

/--
A measurable feasible set with zero total positive trip time has zero mass.
This closes the usual no-mass-at-zero bridge because feasible trips are
restricted to `τ > 0`.
-/
theorem singleStateTripMass_eq_zero_of_time_zero_subset_acceptAll
    (μ : Measure TripLength) (σ : TripPolicy)
    (hσ_measurable : MeasurableSet σ)
    (hσ_subset : σ ⊆ acceptAllPolicy)
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ)
    (htime_zero : singleStateTripTime μ σ = 0) :
    singleStateTripMass μ σ = 0 := by
  have htime_integrable :
      IntegrableOn (fun τ : TripLength => τ) σ μ :=
    htime_integrable_acceptAll.mono_set hσ_subset
  have hnonneg_ae :
      0 ≤ᵐ[μ.restrict σ] (fun τ : TripLength => τ) :=
    (ae_restrict_iff' hσ_measurable).2
      (Filter.Eventually.of_forall (fun τ hτ =>
        le_of_lt (hσ_subset hτ)))
  have hsupport :
      Function.support (fun τ : TripLength => τ) ∩ σ = σ := by
    ext τ
    constructor
    · intro hτ
      exact hτ.2
    · intro hτ
      exact ⟨ne_of_gt (hσ_subset hτ), hτ⟩
  have hmeasure_zero : μ σ = 0 := by
    by_contra hmeasure_ne_zero
    have hmeasure_pos : 0 < μ σ := pos_iff_ne_zero.2 hmeasure_ne_zero
    have hintegral_pos :
        0 < ∫ τ in σ, τ ∂μ := by
      exact (setIntegral_pos_iff_support_of_nonneg_ae
        hnonneg_ae htime_integrable).2 (by
          simpa [hsupport] using hmeasure_pos)
    unfold singleStateTripTime at htime_zero
    rw [htime_zero] at hintegral_pos
    exact (lt_irrefl (0 : ℝ)) hintegral_pos
  unfold singleStateTripMass
  simp [hmeasure_zero]

/--
Theorem 1 threshold shape: accept exactly trips whose on-trip rate is above a
threshold `c`.
-/
def thresholdRatePolicy (w : PricingFunction) (c : ℝ) (σ : TripPolicy) : Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → (τ ∈ σ ↔ c ≤ w τ / τ)

/-- Theorem 1 strict-threshold policy `σ_c^> = {τ : c < w(τ)/τ}`. -/
def strictThresholdRatePolicy (w : PricingFunction) (c : ℝ) (σ : TripPolicy) : Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → (τ ∈ σ ↔ c < w τ / τ)

/--
Theorem 1 partial-threshold policy: it contains every trip with rate strictly
above `c`, excludes every trip with rate strictly below `c`, and may choose an
arbitrary subset of the boundary `w(τ)/τ = c`.
-/
def partialThresholdRatePolicy (w : PricingFunction) (c : ℝ) (σ : TripPolicy) : Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ →
    (c < w τ / τ → τ ∈ σ) ∧ (τ ∈ σ → c ≤ w τ / τ)

/-- Canonical strict-threshold set, accepting trips with rate strictly above `c`. -/
def strictThresholdPolicy (w : PricingFunction) (c : ℝ) : TripPolicy :=
  Set.Ioi (0 : ℝ) ∩ {τ : TripLength | c < w τ / τ}

/-- Canonical complete-threshold set, accepting trips with rate weakly above `c`. -/
def completeThresholdPolicy (w : PricingFunction) (c : ℝ) : TripPolicy :=
  Set.Ioi (0 : ℝ) ∩ {τ : TripLength | c ≤ w τ / τ}

/-- Canonical threshold boundary set, where the on-trip rate equals `c`. -/
def thresholdBoundaryPolicy (w : PricingFunction) (c : ℝ) : TripPolicy :=
  Set.Ioi (0 : ℝ) ∩ {τ : TripLength | w τ / τ = c}

/-- The canonical strict-threshold set has the strict threshold shape. -/
theorem strictThresholdRatePolicy_strictThresholdPolicy
    (w : PricingFunction) (c : ℝ) :
    strictThresholdRatePolicy w c (strictThresholdPolicy w c) := by
  intro τ hτ
  simp [strictThresholdPolicy, hτ]

/-- The canonical complete-threshold set has the complete threshold shape. -/
theorem thresholdRatePolicy_completeThresholdPolicy
    (w : PricingFunction) (c : ℝ) :
    thresholdRatePolicy w c (completeThresholdPolicy w c) := by
  intro τ hτ
  simp [completeThresholdPolicy, hτ]

/-- The canonical strict-threshold set is a partial threshold policy. -/
theorem partialThresholdRatePolicy_strictThresholdPolicy
    (w : PricingFunction) (c : ℝ) :
    partialThresholdRatePolicy w c (strictThresholdPolicy w c) := by
  intro τ hτ
  constructor
  · intro hlt
    simpa [strictThresholdPolicy, hτ] using hlt
  · intro hmem
    exact le_of_lt (by
      simpa [strictThresholdPolicy, hτ] using hmem)

/-- The canonical complete-threshold set is a partial threshold policy. -/
theorem partialThresholdRatePolicy_completeThresholdPolicy
    (w : PricingFunction) (c : ℝ) :
    partialThresholdRatePolicy w c (completeThresholdPolicy w c) := by
  intro τ hτ
  constructor
  · intro hlt
    simpa [completeThresholdPolicy, hτ] using le_of_lt hlt
  · intro hmem
    simpa [completeThresholdPolicy, hτ] using hmem

/-- Strict-threshold policies only accept positive trips. -/
theorem strictThresholdPolicy_subset_acceptAll
    (w : PricingFunction) (c : ℝ) :
    strictThresholdPolicy w c ⊆ acceptAllPolicy := by
  intro τ hτ
  exact hτ.1

/-- Complete-threshold policies only accept positive trips. -/
theorem completeThresholdPolicy_subset_acceptAll
    (w : PricingFunction) (c : ℝ) :
    completeThresholdPolicy w c ⊆ acceptAllPolicy := by
  intro τ hτ
  exact hτ.1

/-- Threshold-boundary policies only contain positive trips. -/
theorem thresholdBoundaryPolicy_subset_acceptAll
    (w : PricingFunction) (c : ℝ) :
    thresholdBoundaryPolicy w c ⊆ acceptAllPolicy := by
  intro τ hτ
  exact hτ.1

/-- Canonical strict-threshold sets are measurable when the rate function is measurable. -/
theorem measurableSet_strictThresholdPolicy
    (w : PricingFunction) (c : ℝ)
    (hrate_measurable : Measurable (fun τ : TripLength => w τ / τ)) :
    MeasurableSet (strictThresholdPolicy w c) := by
  unfold strictThresholdPolicy
  exact (measurableSet_Ioi (a := (0 : ℝ))).inter
    (hrate_measurable measurableSet_Ioi)

/-- Canonical complete-threshold sets are measurable when the rate function is measurable. -/
theorem measurableSet_completeThresholdPolicy
    (w : PricingFunction) (c : ℝ)
    (hrate_measurable : Measurable (fun τ : TripLength => w τ / τ)) :
    MeasurableSet (completeThresholdPolicy w c) := by
  unfold completeThresholdPolicy
  exact (measurableSet_Ioi (a := (0 : ℝ))).inter
    (hrate_measurable measurableSet_Ici)

/-- Canonical threshold-boundary sets are measurable when the rate function is measurable. -/
theorem measurableSet_thresholdBoundaryPolicy
    (w : PricingFunction) (c : ℝ)
    (hrate_measurable : Measurable (fun τ : TripLength => w τ / τ)) :
    MeasurableSet (thresholdBoundaryPolicy w c) := by
  unfold thresholdBoundaryPolicy
  exact (measurableSet_Ioi (a := (0 : ℝ))).inter
    (hrate_measurable (measurableSet_singleton c))

/-- A set of trip lengths all has on-trip earning rate exactly `c`. -/
def onTripRateEquals (w : PricingFunction) (c : ℝ) (σ : TripPolicy) : Prop :=
  ∀ τ ∈ σ, w τ = c * τ

/-- Every trip in the canonical threshold boundary has on-trip rate exactly `c`. -/
theorem onTripRateEquals_thresholdBoundaryPolicy
    (w : PricingFunction) (c : ℝ) :
    onTripRateEquals w c (thresholdBoundaryPolicy w c) := by
  intro τ hτ
  have hτ_pos : 0 < τ := hτ.1
  have hrate : w τ / τ = c := hτ.2
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
  have hmul : w τ / τ * τ = c * τ := by
    rw [hrate]
  field_simp [hτ_ne] at hmul
  simpa [mul_comm] using hmul

/--
Theorem 1 marginal step, add version: adding a disjoint measurable set of
positive total trip time whose average payment rate is at least the current
renewal-reward rate cannot reduce the single-state reward.
-/
theorem paper_theorem1_add_positive_time_set_if_average_above_current
    (μ : Measure TripLength) (arrivalRate : ℝ) (w : PricingFunction)
    (σ added : TripPolicy)
    (hdisjoint : Disjoint σ added)
    (hadded_measurable : MeasurableSet added)
    (hw_integrable_σ : IntegrableOn w σ μ)
    (hw_integrable_added : IntegrableOn w added μ)
    (htime_integrable_σ :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (htime_integrable_added :
      IntegrableOn (fun τ : TripLength => τ) added μ)
    (hlambda : 0 < arrivalRate)
    (htime_nonneg : 0 ≤ singleStateTripTime μ σ)
    (hadded_time_pos : 0 < singleStateTripTime μ added)
    (hcurrent_le_added_average :
      singleStateRenewalReward μ arrivalRate w σ ≤
        singleStateAverageTripRate μ w added) :
    singleStateRenewalReward μ arrivalRate w σ ≤
      singleStateRenewalReward μ arrivalRate w (σ ∪ added) := by
  change
    renewalRewardRate arrivalRate
        (singleStateTripPayment μ w σ) (singleStateTripTime μ σ) ≤
      renewalRewardRate arrivalRate
        (singleStateTripPayment μ w (σ ∪ added))
        (singleStateTripTime μ (σ ∪ added))
  rw [singleStateTripPayment_union μ w σ added hdisjoint hadded_measurable
      hw_integrable_σ hw_integrable_added,
    singleStateTripTime_union μ σ added hdisjoint hadded_measurable
      htime_integrable_σ htime_integrable_added]
  exact renewalRewardRate_le_add_component_of_le_average
    arrivalRate (singleStateTripPayment μ w σ) (singleStateTripTime μ σ)
    (singleStateTripPayment μ w added) (singleStateTripTime μ added)
    hlambda htime_nonneg hadded_time_pos
    (by
      simpa [singleStateRenewalReward, singleStateAverageTripRate,
        renewalRewardRate] using hcurrent_le_added_average)

/--
Theorem 1 marginal step, remove version: removing a measurable accepted subset
of positive total trip time whose average payment rate is at most the current
renewal-reward rate cannot reduce the single-state reward.
-/
theorem paper_theorem1_remove_positive_time_set_if_average_below_current
    (μ : Measure TripLength) (arrivalRate : ℝ) (w : PricingFunction)
    (σ removed : TripPolicy)
    (hremoved_subset : removed ⊆ σ)
    (hremoved_measurable : MeasurableSet removed)
    (hw_integrable_σ : IntegrableOn w σ μ)
    (htime_integrable_σ :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (hlambda : 0 < arrivalRate)
    (htime_remaining_nonneg : 0 ≤ singleStateTripTime μ σ - singleStateTripTime μ removed)
    (hremoved_time_pos : 0 < singleStateTripTime μ removed)
    (hremoved_average_le_current :
      singleStateAverageTripRate μ w removed ≤
        singleStateRenewalReward μ arrivalRate w σ) :
    singleStateRenewalReward μ arrivalRate w σ ≤
      singleStateRenewalReward μ arrivalRate w (σ \ removed) := by
  change
    renewalRewardRate arrivalRate
        (singleStateTripPayment μ w σ) (singleStateTripTime μ σ) ≤
      renewalRewardRate arrivalRate
        (singleStateTripPayment μ w (σ \ removed))
        (singleStateTripTime μ (σ \ removed))
  rw [singleStateTripPayment_diff μ w σ removed hremoved_subset hremoved_measurable
      hw_integrable_σ,
    singleStateTripTime_diff μ σ removed hremoved_subset hremoved_measurable
      htime_integrable_σ]
  exact renewalRewardRate_remove_component_ge_of_average_le
    arrivalRate (singleStateTripPayment μ w σ) (singleStateTripTime μ σ)
    (singleStateTripPayment μ w removed) (singleStateTripTime μ removed)
    hlambda htime_remaining_nonneg hremoved_time_pos
    (by
      simpa [singleStateRenewalReward, singleStateAverageTripRate,
        renewalRewardRate] using hremoved_average_le_current)

/--
Theorem 1 pointwise add step: adding a disjoint measurable positive-time set
whose every trip pays at least the current renewal-reward rate per unit time
cannot reduce reward.
-/
theorem paper_theorem1_add_positive_time_set_if_pointwise_rate_above_current
    (μ : Measure TripLength) (arrivalRate : ℝ) (w : PricingFunction)
    (σ added : TripPolicy)
    (hdisjoint : Disjoint σ added)
    (hadded_measurable : MeasurableSet added)
    (hw_integrable_σ : IntegrableOn w σ μ)
    (hw_integrable_added : IntegrableOn w added μ)
    (htime_integrable_σ :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (htime_integrable_added :
      IntegrableOn (fun τ : TripLength => τ) added μ)
    (hlambda : 0 < arrivalRate)
    (htime_nonneg : 0 ≤ singleStateTripTime μ σ)
    (hadded_time_pos : 0 < singleStateTripTime μ added)
    (hpointwise :
      ∀ τ ∈ added, singleStateRenewalReward μ arrivalRate w σ * τ ≤ w τ) :
    singleStateRenewalReward μ arrivalRate w σ ≤
      singleStateRenewalReward μ arrivalRate w (σ ∪ added) := by
  exact paper_theorem1_add_positive_time_set_if_average_above_current
    μ arrivalRate w σ added hdisjoint hadded_measurable hw_integrable_σ
    hw_integrable_added htime_integrable_σ htime_integrable_added
    hlambda htime_nonneg hadded_time_pos
    (le_singleStateAverageTripRate_of_pointwise_le
      μ w added (singleStateRenewalReward μ arrivalRate w σ)
      hadded_measurable htime_integrable_added hw_integrable_added
      hadded_time_pos hpointwise)

/--
Theorem 1 pointwise remove step: removing a measurable accepted positive-time
set whose every trip pays at most the current renewal-reward rate per unit time
cannot reduce reward.
-/
theorem paper_theorem1_remove_positive_time_set_if_pointwise_rate_below_current
    (μ : Measure TripLength) (arrivalRate : ℝ) (w : PricingFunction)
    (σ removed : TripPolicy)
    (hremoved_subset : removed ⊆ σ)
    (hremoved_measurable : MeasurableSet removed)
    (hw_integrable_σ : IntegrableOn w σ μ)
    (hw_integrable_removed : IntegrableOn w removed μ)
    (htime_integrable_σ :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (htime_integrable_removed :
      IntegrableOn (fun τ : TripLength => τ) removed μ)
    (hlambda : 0 < arrivalRate)
    (htime_remaining_nonneg : 0 ≤ singleStateTripTime μ σ - singleStateTripTime μ removed)
    (hremoved_time_pos : 0 < singleStateTripTime μ removed)
    (hpointwise :
      ∀ τ ∈ removed, w τ ≤ singleStateRenewalReward μ arrivalRate w σ * τ) :
    singleStateRenewalReward μ arrivalRate w σ ≤
      singleStateRenewalReward μ arrivalRate w (σ \ removed) := by
  exact paper_theorem1_remove_positive_time_set_if_average_below_current
    μ arrivalRate w σ removed hremoved_subset hremoved_measurable
    hw_integrable_σ htime_integrable_σ hlambda htime_remaining_nonneg
    hremoved_time_pos
    (singleStateAverageTripRate_le_of_pointwise_le
      μ w removed (singleStateRenewalReward μ arrivalRate w σ)
      hremoved_measurable htime_integrable_removed hw_integrable_removed
      hremoved_time_pos hpointwise)

/--
Theorem 1 Step 1 algebra: if a replacement policy keeps the same total
accepted trip time and strictly increases accepted payment, then the
single-state renewal reward strictly increases.
-/
theorem paper_theorem1_step1_same_time_more_payment_improves_reward
    (μ : Measure TripLength) (arrivalRate : ℝ) (w : PricingFunction)
    (σ replacement : TripPolicy)
    (hlambda : 0 < arrivalRate)
    (htime_nonneg : 0 ≤ singleStateTripTime μ σ)
    (htime_same :
      singleStateTripTime μ replacement = singleStateTripTime μ σ)
    (hpayment_gain :
      singleStateTripPayment μ w σ <
        singleStateTripPayment μ w replacement) :
    singleStateRenewalReward μ arrivalRate w σ <
      singleStateRenewalReward μ arrivalRate w replacement := by
  change
    renewalRewardRate arrivalRate
        (singleStateTripPayment μ w σ) (singleStateTripTime μ σ) <
      renewalRewardRate arrivalRate
        (singleStateTripPayment μ w replacement)
        (singleStateTripTime μ replacement)
  rw [htime_same]
  exact renewalRewardRate_lt_replace_reward_same_time_of_lt
    arrivalRate (singleStateTripPayment μ w σ) (singleStateTripTime μ σ)
    (singleStateTripPayment μ w replacement) hlambda htime_nonneg
    hpayment_gain

/--
Theorem 1 Step 1 source swap: replacing an accepted set by an equal-utilization
set with larger total payment strictly improves reward.  The set-integral
decomposition hypotheses are the measurable algebra for
`σ' = (σ \ removed) ∪ added`.
-/
theorem paper_theorem1_step1_equal_utilization_swap_improves_reward
    (μ : Measure TripLength) (arrivalRate : ℝ) (w : PricingFunction)
    (σ removed added : TripPolicy)
    (hlambda : 0 < arrivalRate)
    (htime_nonneg : 0 ≤ singleStateTripTime μ σ)
    (hreplacement_payment :
      singleStateTripPayment μ w ((σ \ removed) ∪ added) =
        singleStateTripPayment μ w σ -
          singleStateTripPayment μ w removed +
            singleStateTripPayment μ w added)
    (hreplacement_time :
      singleStateTripTime μ ((σ \ removed) ∪ added) =
        singleStateTripTime μ σ)
    (hadded_payment_gt_removed :
      singleStateTripPayment μ w removed <
        singleStateTripPayment μ w added) :
    singleStateRenewalReward μ arrivalRate w σ <
      singleStateRenewalReward μ arrivalRate w ((σ \ removed) ∪ added) := by
  apply paper_theorem1_step1_same_time_more_payment_improves_reward
    μ arrivalRate w σ ((σ \ removed) ∪ added)
    hlambda htime_nonneg hreplacement_time
  rw [hreplacement_payment]
  linarith

/--
Theorem 1 Step 2 add case: for a partial threshold policy, adding a positive
time boundary set with rate `c` cannot reduce reward when `c` is at least the
current reward rate.
-/
theorem paper_theorem1_step2_add_boundary_set_if_threshold_ge_current
    (μ : Measure TripLength) (arrivalRate : ℝ) (w : PricingFunction)
    (σ boundary : TripPolicy) (c : ℝ)
    (hdisjoint : Disjoint σ boundary)
    (hboundary_measurable : MeasurableSet boundary)
    (hw_integrable_σ : IntegrableOn w σ μ)
    (hw_integrable_boundary : IntegrableOn w boundary μ)
    (htime_integrable_σ :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (htime_integrable_boundary :
      IntegrableOn (fun τ : TripLength => τ) boundary μ)
    (hlambda : 0 < arrivalRate)
    (htime_nonneg : 0 ≤ singleStateTripTime μ σ)
    (hboundary_time_pos : 0 < singleStateTripTime μ boundary)
    (hboundary_positive : boundary ⊆ acceptAllPolicy)
    (hboundary_rate : onTripRateEquals w c boundary)
    (hcurrent_le_c : singleStateRenewalReward μ arrivalRate w σ ≤ c) :
    singleStateRenewalReward μ arrivalRate w σ ≤
      singleStateRenewalReward μ arrivalRate w (σ ∪ boundary) := by
  exact paper_theorem1_add_positive_time_set_if_pointwise_rate_above_current
    μ arrivalRate w σ boundary hdisjoint hboundary_measurable
    hw_integrable_σ hw_integrable_boundary htime_integrable_σ
    htime_integrable_boundary hlambda htime_nonneg hboundary_time_pos
    (fun τ hτ => by
      have hτ_nonneg : 0 ≤ τ := by
        exact le_of_lt (by
          simpa [acceptAllPolicy, positiveTripLengths] using
            hboundary_positive hτ)
      rw [hboundary_rate τ hτ]
      exact mul_le_mul_of_nonneg_right hcurrent_le_c hτ_nonneg)

/--
Theorem 1 Step 2 remove case: removing a positive-time boundary set with rate
`c` cannot reduce reward when `c` is no larger than the current reward rate.
-/
theorem paper_theorem1_step2_remove_boundary_set_if_threshold_le_current
    (μ : Measure TripLength) (arrivalRate : ℝ) (w : PricingFunction)
    (σ boundary : TripPolicy) (c : ℝ)
    (hboundary_subset : boundary ⊆ σ)
    (hboundary_measurable : MeasurableSet boundary)
    (hw_integrable_σ : IntegrableOn w σ μ)
    (hw_integrable_boundary : IntegrableOn w boundary μ)
    (htime_integrable_σ :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (htime_integrable_boundary :
      IntegrableOn (fun τ : TripLength => τ) boundary μ)
    (hlambda : 0 < arrivalRate)
    (htime_remaining_nonneg :
      0 ≤ singleStateTripTime μ σ - singleStateTripTime μ boundary)
    (hboundary_time_pos : 0 < singleStateTripTime μ boundary)
    (hboundary_positive : boundary ⊆ acceptAllPolicy)
    (hboundary_rate : onTripRateEquals w c boundary)
    (hc_le_current :
      c ≤ singleStateRenewalReward μ arrivalRate w σ) :
    singleStateRenewalReward μ arrivalRate w σ ≤
      singleStateRenewalReward μ arrivalRate w (σ \ boundary) := by
  exact paper_theorem1_remove_positive_time_set_if_pointwise_rate_below_current
    μ arrivalRate w σ boundary hboundary_subset hboundary_measurable
    hw_integrable_σ hw_integrable_boundary htime_integrable_σ
    htime_integrable_boundary hlambda htime_remaining_nonneg
    hboundary_time_pos
    (fun τ hτ => by
      have hτ_nonneg : 0 ≤ τ := by
        exact le_of_lt (by
          simpa [acceptAllPolicy, positiveTripLengths] using
            hboundary_positive hτ)
      rw [hboundary_rate τ hτ]
      exact mul_le_mul_of_nonneg_right hc_le_current hτ_nonneg)

/--
Theorem 1 proof assembly: if Step 1 sends every policy to a weakly better
partial threshold, Step 2 sends every partial threshold to a weakly better
strict or complete threshold, and Step 3 supplies a complete threshold that
dominates all strict and complete thresholds, then that complete threshold is
globally optimal.
-/
theorem paper_theorem1_complete_threshold_optimal_of_step_certificates
    (R : SingleStateReward) (w : PricingFunction)
    (strict complete : ℝ → TripPolicy) (cstar : ℝ)
    (hcomplete_shape :
      ∀ c : ℝ, thresholdRatePolicy w c (complete c))
    (hstep1 :
      ∀ σ : TripPolicy, ∃ c : ℝ, ∃ ρ : TripPolicy,
        partialThresholdRatePolicy w c ρ ∧ R σ ≤ R ρ)
    (hstep2 :
      ∀ c : ℝ, ∀ ρ : TripPolicy,
        partialThresholdRatePolicy w c ρ →
          R ρ ≤ max (R (strict c)) (R (complete c)))
    (hstep3 :
      ∀ c : ℝ, R (strict c) ≤ R (complete cstar) ∧
        R (complete c) ≤ R (complete cstar)) :
    ∃ σ : TripPolicy,
      thresholdRatePolicy w cstar σ ∧ singleStateOptimal R σ := by
  refine ⟨complete cstar, hcomplete_shape cstar, ?_⟩
  intro σ
  rcases hstep1 σ with ⟨c, ρ, hpartial, hσ_le_ρ⟩
  have hρ_le_max := hstep2 c ρ hpartial
  have hmax_le :
      max (R (strict c)) (R (complete c)) ≤ R (complete cstar) := by
    exact max_le (hstep3 c).1 (hstep3 c).2
  exact hσ_le_ρ.trans (hρ_le_max.trans hmax_le)

/-- Affine pricing `w(τ)=mτ+a`. -/
def affinePricing (m a : ℝ) : PricingFunction :=
  fun τ => m * τ + a

/-- The affine on-trip rate `w(τ)/τ` is measurable. -/
theorem measurable_affinePricing_rate (m a : ℝ) :
    Measurable (fun τ : TripLength => affinePricing m a τ / τ) := by
  unfold affinePricing
  fun_prop

/-- Strict affine threshold policies are measurable. -/
theorem measurableSet_strictThresholdPolicy_affinePricing
    (m a c : ℝ) :
    MeasurableSet (strictThresholdPolicy (affinePricing m a) c) :=
  measurableSet_strictThresholdPolicy (affinePricing m a) c
    (measurable_affinePricing_rate m a)

/-- Complete affine threshold policies are measurable. -/
theorem measurableSet_completeThresholdPolicy_affinePricing
    (m a c : ℝ) :
    MeasurableSet (completeThresholdPolicy (affinePricing m a) c) :=
  measurableSet_completeThresholdPolicy (affinePricing m a) c
    (measurable_affinePricing_rate m a)

/-- Affine threshold boundary policies are measurable. -/
theorem measurableSet_thresholdBoundaryPolicy_affinePricing
    (m a c : ℝ) :
    MeasurableSet (thresholdBoundaryPolicy (affinePricing m a) c) :=
  measurableSet_thresholdBoundaryPolicy (affinePricing m a) c
    (measurable_affinePricing_rate m a)

/-- Affine set-payment integral in terms of accepted mass and accepted trip time. -/
theorem singleStateTripPayment_affinePricing
    (μ : Measure TripLength) (σ : TripPolicy) (m a : ℝ)
    (htime_integrable : IntegrableOn (fun τ : TripLength => τ) σ μ)
    (hfinite : μ σ ≠ ⊤) :
    singleStateTripPayment μ (affinePricing m a) σ =
      m * singleStateTripTime μ σ + a * singleStateTripMass μ σ := by
  unfold singleStateTripPayment affinePricing singleStateTripTime singleStateTripMass
  rw [integral_add]
  · rw [integral_const_mul]
    rw [setIntegral_const]
    rw [measureReal_def]
    ring
  · exact htime_integrable.const_mul m
  · exact integrableOn_const hfinite

/--
Affine specialization of the single-state renewal-reward formula, expressed in
the paper's measured mass/time summaries.
-/
def affineSingleStateRenewalReward
    (μ : Measure TripLength) (arrivalRate m a : ℝ) (σ : TripPolicy) : ℝ :=
  arrivalRate *
    (m * singleStateTripTime μ σ + a * singleStateTripMass μ σ) /
      (1 + arrivalRate * singleStateTripTime μ σ)

/-- The affine measured reward formula is the source renewal-reward formula specialized to `mτ+a`. -/
theorem affineSingleStateRenewalReward_eq_singleStateRenewalReward
    (μ : Measure TripLength) (arrivalRate m a : ℝ) (σ : TripPolicy)
    (htime_integrable : IntegrableOn (fun τ : TripLength => τ) σ μ)
    (hfinite : μ σ ≠ ⊤) :
    affineSingleStateRenewalReward μ arrivalRate m a σ =
      singleStateRenewalReward μ arrivalRate (affinePricing m a) σ := by
  unfold affineSingleStateRenewalReward singleStateRenewalReward
  rw [singleStateTripPayment_affinePricing μ σ m a htime_integrable hfinite]

/-- Average on-trip affine earning rate over a rejected set. -/
def affineRejectedAverageRate
    (μ : Measure TripLength) (m a : ℝ) (rejected : TripPolicy) : ℝ :=
  (m * singleStateTripTime μ rejected +
      a * singleStateTripMass μ rejected) /
    singleStateTripTime μ rejected

/--
Affine reward of the policy that accepts every feasible trip except the
measured rejected set, after decomposing the accept-all integrals into accepted
minus rejected mass/time/payment terms.
-/
def affineSingleStateComplementRewardOfRejected
    (μ : Measure TripLength) (arrivalRate m a : ℝ) (rejected : TripPolicy) : ℝ :=
  arrivalRate *
      ((m * singleStateTripTime μ acceptAllPolicy +
          a * singleStateTripMass μ acceptAllPolicy) -
        (m * singleStateTripTime μ rejected +
          a * singleStateTripMass μ rejected)) /
    (1 + arrivalRate *
      (singleStateTripTime μ acceptAllPolicy - singleStateTripTime μ rejected))

/--
Measure-theoretic assumptions on the continuous trip-length distribution used
by the single-state renewal-reward model.
-/
structure SingleStateTripMeasureAssumptions (μ : Measure TripLength) where
  accept_all_mass : singleStateTripMass μ acceptAllPolicy = 1
  accept_all_time_nonneg : 0 ≤ singleStateTripTime μ acceptAllPolicy
  accept_all_finite : μ acceptAllPolicy ≠ ⊤
  accept_all_time_integrable :
    IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ
  rejected_mass_nonneg :
    ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
      0 ≤ singleStateTripMass μ (acceptAllPolicy \ σ)
  rejected_time_nonneg :
    ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
      0 ≤ singleStateTripTime μ (acceptAllPolicy \ σ)
  rejected_time_le_total :
    ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
      singleStateTripTime μ (acceptAllPolicy \ σ) ≤
        singleStateTripTime μ acceptAllPolicy
  zero_time_rejections_mass_zero :
    ∀ σ : TripPolicy, σ ⊆ acceptAllPolicy → MeasurableSet σ →
      singleStateTripTime μ (acceptAllPolicy \ σ) = 0 →
        singleStateTripMass μ (acceptAllPolicy \ σ) = 0

/--
Build the Proposition 3.1 trip-measure package from standard measure facts.
The basic nonnegativity and monotonicity obligations are discharged by set
integral lemmas, and the zero-time mass bridge follows from the fact that
feasible trip lengths are strictly positive.
-/
def singleStateTripMeasureAssumptions_of_standard
    (μ : Measure TripLength)
    (haccept_mass : singleStateTripMass μ acceptAllPolicy = 1)
    (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ) :
    SingleStateTripMeasureAssumptions μ where
  accept_all_mass := haccept_mass
  accept_all_time_nonneg :=
    singleStateTripTime_nonneg_of_subset_acceptAll μ acceptAllPolicy
      measurableSet_acceptAllPolicy (fun _ hτ => hτ)
  accept_all_finite := hfinite_acceptAll
  accept_all_time_integrable := htime_integrable_acceptAll
  rejected_mass_nonneg := by
    intro σ _hσ_subset _hσ_measurable
    exact singleStateTripMass_acceptAll_diff_nonneg μ σ
  rejected_time_nonneg := by
    intro σ _hσ_subset hσ_measurable
    exact singleStateTripTime_acceptAll_diff_nonneg μ σ hσ_measurable
  rejected_time_le_total := by
    intro σ _hσ_subset _hσ_measurable
    exact singleStateTripTime_acceptAll_diff_le_acceptAll μ σ
      htime_integrable_acceptAll
  zero_time_rejections_mass_zero := by
    intro σ _hσ_subset hσ_measurable htime_zero
    exact singleStateTripMass_eq_zero_of_time_zero_subset_acceptAll
      μ (acceptAllPolicy \ σ)
      (measurableSet_acceptAllPolicy.diff hσ_measurable)
      (fun _ hτ => hτ.1) htime_integrable_acceptAll htime_zero

/-- Mass of accepting all except a measurable rejected subset. -/
theorem singleStateTripMass_acceptAll_diff
    (μ : Measure TripLength) (rejected : TripPolicy)
    (hrejected_subset : rejected ⊆ acceptAllPolicy)
    (hrejected_measurable : MeasurableSet rejected)
    (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤) :
    singleStateTripMass μ (acceptAllPolicy \ rejected) =
      singleStateTripMass μ acceptAllPolicy - singleStateTripMass μ rejected := by
  unfold singleStateTripMass
  rw [← measureReal_def, measureReal_diff hrejected_subset hrejected_measurable
    hfinite_acceptAll, measureReal_def, measureReal_def]

/-- Trip-time integral of accepting all except a measurable rejected subset. -/
theorem singleStateTripTime_acceptAll_diff
    (μ : Measure TripLength) (rejected : TripPolicy)
    (hrejected_subset : rejected ⊆ acceptAllPolicy)
    (hrejected_measurable : MeasurableSet rejected)
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ) :
    singleStateTripTime μ (acceptAllPolicy \ rejected) =
      singleStateTripTime μ acceptAllPolicy - singleStateTripTime μ rejected := by
  unfold singleStateTripTime
  exact setIntegral_diff hrejected_measurable htime_integrable_acceptAll
    hrejected_subset

/--
Affine measured reward of accepting all except a rejected set equals the
paper's accepted-minus-rejected reward expression.
-/
theorem affineSingleStateRenewalReward_acceptAll_diff_eq_complementReward
    (μ : Measure TripLength) (arrivalRate m a : ℝ) (rejected : TripPolicy)
    (hrejected_subset : rejected ⊆ acceptAllPolicy)
    (hrejected_measurable : MeasurableSet rejected)
    (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ) :
    affineSingleStateRenewalReward μ arrivalRate m a (acceptAllPolicy \ rejected) =
      affineSingleStateComplementRewardOfRejected μ arrivalRate m a rejected := by
  unfold affineSingleStateRenewalReward affineSingleStateComplementRewardOfRejected
  rw [singleStateTripTime_acceptAll_diff μ rejected hrejected_subset
      hrejected_measurable htime_integrable_acceptAll,
    singleStateTripMass_acceptAll_diff μ rejected hrejected_subset
      hrejected_measurable hfinite_acceptAll]
  ring

/--
Paper C.3 algebraic bound: under `0 <= a <= m/λ`, the accept-all affine
renewal reward is no larger than the average on-trip affine earning rate of any
positive-time rejected set.
-/
theorem paper_proposition3_1_affine_rejected_set_average_rate_bound
    (μ : Measure TripLength) (arrivalRate m a : ℝ) (rejected : TripPolicy)
    (hlambda : 0 < arrivalRate)
    (ha_nonneg : 0 ≤ a)
    (ha_le_wait_value : a ≤ m / arrivalRate)
    (haccept_mass : singleStateTripMass μ acceptAllPolicy = 1)
    (htotal_nonneg : 0 ≤ singleStateTripTime μ acceptAllPolicy)
    (hrejected_mass_nonneg : 0 ≤ singleStateTripMass μ rejected)
    (hrejected_time_pos : 0 < singleStateTripTime μ rejected) :
    affineSingleStateRenewalReward μ arrivalRate m a acceptAllPolicy ≤
      affineRejectedAverageRate μ m a rejected := by
  unfold affineSingleStateRenewalReward affineRejectedAverageRate
  have hden_total : 0 < 1 + arrivalRate * singleStateTripTime μ acceptAllPolicy := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htotal_nonneg]
  have hlambda_mul_a_le_m : arrivalRate * a ≤ m := by
    have h := mul_le_mul_of_nonneg_left ha_le_wait_value (le_of_lt hlambda)
    field_simp [ne_of_gt hlambda] at h
    linarith
  have hreward_le_m :
      arrivalRate *
          (m * singleStateTripTime μ acceptAllPolicy + a * singleStateTripMass μ acceptAllPolicy) /
            (1 + arrivalRate * singleStateTripTime μ acceptAllPolicy) ≤ m := by
    rw [div_le_iff₀ hden_total]
    rw [haccept_mass]
    nlinarith
  have hm_le_rejected_average :
      m ≤ (m * singleStateTripTime μ rejected +
          a * singleStateTripMass μ rejected) /
          singleStateTripTime μ rejected := by
    rw [le_div_iff₀ hrejected_time_pos]
    nlinarith [mul_nonneg ha_nonneg hrejected_mass_nonneg]
  exact hreward_le_m.trans hm_le_rejected_average

/--
Proposition 3.1 direct measured reward step: rejecting any positive-time set
does not improve affine single-state renewal reward when `0 <= a <= m/λ`.

The theorem is stated in the paper's continuous mass/time variables.  The
remaining measure-theoretic bridge for a concrete trip distribution is to prove
that these variables are exactly the set integrals of the accepted/rejected
sets and that accept-all has unit mass.
-/
theorem paper_proposition3_1_affine_accept_all_ge_complement_reward_of_rejected_set
    (μ : Measure TripLength) (arrivalRate m a : ℝ) (rejected : TripPolicy)
    (hlambda : 0 < arrivalRate)
    (ha_nonneg : 0 ≤ a)
    (ha_le_wait_value : a ≤ m / arrivalRate)
    (haccept_mass : singleStateTripMass μ acceptAllPolicy = 1)
    (htotal_nonneg : 0 ≤ singleStateTripTime μ acceptAllPolicy)
    (hrejected_mass_nonneg : 0 ≤ singleStateTripMass μ rejected)
    (hrejected_time_pos : 0 < singleStateTripTime μ rejected)
    (hrejected_time_le_total :
      singleStateTripTime μ rejected ≤ singleStateTripTime μ acceptAllPolicy) :
    affineSingleStateComplementRewardOfRejected μ arrivalRate m a rejected ≤
      affineSingleStateRenewalReward μ arrivalRate m a acceptAllPolicy := by
  have havg :=
    paper_proposition3_1_affine_rejected_set_average_rate_bound
      μ arrivalRate m a rejected hlambda ha_nonneg ha_le_wait_value
      haccept_mass htotal_nonneg hrejected_mass_nonneg hrejected_time_pos
  unfold affineSingleStateComplementRewardOfRejected affineSingleStateRenewalReward
    affineRejectedAverageRate at *
  rw [haccept_mass] at havg ⊢
  have hden_total : 0 < 1 + arrivalRate * singleStateTripTime μ acceptAllPolicy := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htotal_nonneg]
  have hden_complement :
      0 < 1 + arrivalRate *
        (singleStateTripTime μ acceptAllPolicy - singleStateTripTime μ rejected) := by
    nlinarith [mul_nonneg (le_of_lt hlambda)
      (sub_nonneg.mpr hrejected_time_le_total)]
  have hcross :
      arrivalRate *
          (m * singleStateTripTime μ acceptAllPolicy + a) *
          singleStateTripTime μ rejected ≤
        (m * singleStateTripTime μ rejected +
            a * singleStateTripMass μ rejected) *
          (1 + arrivalRate * singleStateTripTime μ acceptAllPolicy) := by
    rw [div_le_div_iff₀ hden_total hrejected_time_pos] at havg
    nlinarith
  rw [div_le_div_iff₀ hden_complement hden_total]
  nlinarith

/--
Proposition 3.1 direct measurable-policy step: for any measurable positive-time
rejected subset of feasible trips, the affine renewal reward of the policy that
rejects exactly that set is no larger than accept-all reward.
-/
theorem paper_proposition3_1_affine_accept_all_ge_rejecting_measurable_set
    (μ : Measure TripLength) (arrivalRate m a : ℝ) (rejected : TripPolicy)
    (hlambda : 0 < arrivalRate)
    (ha_nonneg : 0 ≤ a)
    (ha_le_wait_value : a ≤ m / arrivalRate)
    (haccept_mass : singleStateTripMass μ acceptAllPolicy = 1)
    (htotal_nonneg : 0 ≤ singleStateTripTime μ acceptAllPolicy)
    (hrejected_subset : rejected ⊆ acceptAllPolicy)
    (hrejected_measurable : MeasurableSet rejected)
    (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ)
    (hrejected_mass_nonneg : 0 ≤ singleStateTripMass μ rejected)
    (hrejected_time_pos : 0 < singleStateTripTime μ rejected)
    (hrejected_time_le_total :
      singleStateTripTime μ rejected ≤ singleStateTripTime μ acceptAllPolicy) :
    affineSingleStateRenewalReward μ arrivalRate m a (acceptAllPolicy \ rejected) ≤
      affineSingleStateRenewalReward μ arrivalRate m a acceptAllPolicy := by
  rw [affineSingleStateRenewalReward_acceptAll_diff_eq_complementReward
    μ arrivalRate m a rejected hrejected_subset hrejected_measurable
    hfinite_acceptAll htime_integrable_acceptAll]
  exact
    paper_proposition3_1_affine_accept_all_ge_complement_reward_of_rejected_set
      μ arrivalRate m a rejected hlambda ha_nonneg ha_le_wait_value
      haccept_mass htotal_nonneg hrejected_mass_nonneg hrejected_time_pos
      hrejected_time_le_total

/-- Zero rejected-time case of the measurable rejection bridge. -/
theorem affineSingleStateRenewalReward_acceptAll_diff_eq_acceptAll_of_zero_rejected
    (μ : Measure TripLength) (arrivalRate m a : ℝ) (rejected : TripPolicy)
    (hrejected_subset : rejected ⊆ acceptAllPolicy)
    (hrejected_measurable : MeasurableSet rejected)
    (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ)
    (hrejected_time_zero : singleStateTripTime μ rejected = 0)
    (hrejected_mass_zero : singleStateTripMass μ rejected = 0) :
    affineSingleStateRenewalReward μ arrivalRate m a (acceptAllPolicy \ rejected) =
      affineSingleStateRenewalReward μ arrivalRate m a acceptAllPolicy := by
  rw [affineSingleStateRenewalReward_acceptAll_diff_eq_complementReward
    μ arrivalRate m a rejected hrejected_subset hrejected_measurable
    hfinite_acceptAll htime_integrable_acceptAll]
  unfold affineSingleStateComplementRewardOfRejected affineSingleStateRenewalReward
  rw [hrejected_time_zero, hrejected_mass_zero]
  ring

/--
Proposition 3.1 direct measurable-policy statement: under the paper condition
`0 <= a <= m/λ`, accept-all weakly dominates every policy obtained by rejecting
a measurable subset of feasible trips.  The `zero_time_rejections_mass_zero`
hypothesis is the source measure-theoretic no-atom-at-zero bridge for feasible
positive trip lengths.
-/
theorem paper_proposition3_1_affine_accept_all_ge_rejecting_any_measurable_set
    (μ : Measure TripLength) (arrivalRate m a : ℝ) (rejected : TripPolicy)
    (hlambda : 0 < arrivalRate)
    (ha_nonneg : 0 ≤ a)
    (ha_le_wait_value : a ≤ m / arrivalRate)
    (haccept_mass : singleStateTripMass μ acceptAllPolicy = 1)
    (htotal_nonneg : 0 ≤ singleStateTripTime μ acceptAllPolicy)
    (hrejected_subset : rejected ⊆ acceptAllPolicy)
    (hrejected_measurable : MeasurableSet rejected)
    (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ)
    (hrejected_mass_nonneg : 0 ≤ singleStateTripMass μ rejected)
    (hrejected_time_nonneg : 0 ≤ singleStateTripTime μ rejected)
    (hrejected_time_le_total :
      singleStateTripTime μ rejected ≤ singleStateTripTime μ acceptAllPolicy)
    (zero_time_rejections_mass_zero :
      singleStateTripTime μ rejected = 0 → singleStateTripMass μ rejected = 0) :
    affineSingleStateRenewalReward μ arrivalRate m a (acceptAllPolicy \ rejected) ≤
      affineSingleStateRenewalReward μ arrivalRate m a acceptAllPolicy := by
  rcases lt_or_eq_of_le hrejected_time_nonneg with hrejected_time_pos | hrejected_time_zero
  · exact paper_proposition3_1_affine_accept_all_ge_rejecting_measurable_set
      μ arrivalRate m a rejected hlambda ha_nonneg ha_le_wait_value
      haccept_mass htotal_nonneg hrejected_subset hrejected_measurable
      hfinite_acceptAll htime_integrable_acceptAll hrejected_mass_nonneg
      hrejected_time_pos hrejected_time_le_total
  · rw [affineSingleStateRenewalReward_acceptAll_diff_eq_acceptAll_of_zero_rejected
      μ arrivalRate m a rejected hrejected_subset hrejected_measurable
      hfinite_acceptAll htime_integrable_acceptAll hrejected_time_zero.symm
      (zero_time_rejections_mass_zero hrejected_time_zero.symm)]

/--
Proposition 3.1 source-facing measurable-policy form: any measurable feasible
policy has weakly lower affine single-state renewal reward than accepting every
positive-length trip, under `0 <= a <= m/λ`.
-/
theorem paper_proposition3_1_affine_accept_all_ge_measurable_policy
    (μ : Measure TripLength) (arrivalRate m a : ℝ) (σ : TripPolicy)
    (hlambda : 0 < arrivalRate)
    (ha_nonneg : 0 ≤ a)
    (ha_le_wait_value : a ≤ m / arrivalRate)
    (haccept_mass : singleStateTripMass μ acceptAllPolicy = 1)
    (htotal_nonneg : 0 ≤ singleStateTripTime μ acceptAllPolicy)
    (hpolicy_subset : σ ⊆ acceptAllPolicy)
    (hpolicy_measurable : MeasurableSet σ)
    (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ)
    (hrejected_mass_nonneg :
      0 ≤ singleStateTripMass μ (acceptAllPolicy \ σ))
    (hrejected_time_nonneg :
      0 ≤ singleStateTripTime μ (acceptAllPolicy \ σ))
    (hrejected_time_le_total :
      singleStateTripTime μ (acceptAllPolicy \ σ) ≤
        singleStateTripTime μ acceptAllPolicy)
    (zero_time_rejections_mass_zero :
      singleStateTripTime μ (acceptAllPolicy \ σ) = 0 →
        singleStateTripMass μ (acceptAllPolicy \ σ) = 0) :
    affineSingleStateRenewalReward μ arrivalRate m a σ ≤
      affineSingleStateRenewalReward μ arrivalRate m a acceptAllPolicy := by
  have hrejected_subset : acceptAllPolicy \ σ ⊆ acceptAllPolicy := by
    intro τ hτ
    exact hτ.1
  have hrejected_measurable : MeasurableSet (acceptAllPolicy \ σ) :=
    measurableSet_acceptAllPolicy.diff hpolicy_measurable
  have h :=
    paper_proposition3_1_affine_accept_all_ge_rejecting_any_measurable_set
      μ arrivalRate m a (acceptAllPolicy \ σ)
      hlambda ha_nonneg ha_le_wait_value haccept_mass htotal_nonneg
      hrejected_subset hrejected_measurable hfinite_acceptAll
      htime_integrable_acceptAll hrejected_mass_nonneg hrejected_time_nonneg
      hrejected_time_le_total zero_time_rejections_mass_zero
  have hset : acceptAllPolicy \ (acceptAllPolicy \ σ) = σ := by
    ext τ
    constructor
    · rintro ⟨haccept, hnot⟩
      by_contra hnotSigma
      exact hnot ⟨haccept, hnotSigma⟩
    · intro hsigma
      exact ⟨hpolicy_subset hsigma, by
        rintro ⟨-, hnotSigma⟩
        exact hnotSigma hsigma⟩
  simpa [hset] using h

/--
Proposition 3.1 source-facing measurable IC endpoint: in the continuous
single-state model with affine pricing `w(τ)=mτ+a`, the paper condition
`0 <= a <= m/λ` makes accepting all positive-length trips optimal among all
measurable feasible policies.
-/
theorem paper_proposition3_1_affine_single_state_measurable_ic
    (μ : Measure TripLength) (arrivalRate m a : ℝ)
    (A : SingleStateTripMeasureAssumptions μ)
    (hlambda : 0 < arrivalRate)
    (ha_nonneg : 0 ≤ a)
    (ha_le_wait_value : a ≤ m / arrivalRate) :
    singleStateMeasurableIncentiveCompatible
      (affineSingleStateRenewalReward μ arrivalRate m a) := by
  intro σ hpolicy_subset hpolicy_measurable
  exact
    paper_proposition3_1_affine_accept_all_ge_measurable_policy
      μ arrivalRate m a σ hlambda ha_nonneg ha_le_wait_value
      A.accept_all_mass A.accept_all_time_nonneg hpolicy_subset
      hpolicy_measurable A.accept_all_finite A.accept_all_time_integrable
      (A.rejected_mass_nonneg σ hpolicy_subset hpolicy_measurable)
      (A.rejected_time_nonneg σ hpolicy_subset hpolicy_measurable)
      (A.rejected_time_le_total σ hpolicy_subset hpolicy_measurable)
      (A.zero_time_rejections_mass_zero σ hpolicy_subset hpolicy_measurable)

/--
Proposition 3.1 measurable IC endpoint from standard trip-distribution facts.
Compared with `paper_proposition3_1_affine_single_state_measurable_ic`, this
version constructs the measure-assumption package automatically.
-/
theorem paper_proposition3_1_affine_single_state_measurable_ic_of_standard_measure
    (μ : Measure TripLength) (arrivalRate m a : ℝ)
    (haccept_mass : singleStateTripMass μ acceptAllPolicy = 1)
    (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ)
    (hlambda : 0 < arrivalRate)
    (ha_nonneg : 0 ≤ a)
    (ha_le_wait_value : a ≤ m / arrivalRate) :
    singleStateMeasurableIncentiveCompatible
      (affineSingleStateRenewalReward μ arrivalRate m a) := by
  exact paper_proposition3_1_affine_single_state_measurable_ic
    μ arrivalRate m a
    (singleStateTripMeasureAssumptions_of_standard μ haccept_mass
      hfinite_acceptAll htime_integrable_acceptAll)
    hlambda ha_nonneg ha_le_wait_value

/-- Policy that rejects sufficiently long trips, `σ = (0,t)`. -/
def rejectsLongTrips (t : ℝ) (σ : TripPolicy) : Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → (τ ∈ σ ↔ τ < t)

/-- Policy that rejects sufficiently short trips, `σ = (t,∞)`. -/
def rejectsShortTrips (t : ℝ) (σ : TripPolicy) : Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → (τ ∈ σ ↔ t < τ)

/-- Policy that accepts an interval of medium-length trips, `σ = (lo,hi)`. -/
def acceptsMiddleTrips (lo hi : ℝ) (σ : TripPolicy) : Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → (τ ∈ σ ↔ lo < τ ∧ τ < hi)

/-- Policy that rejects medium-length trips, `σ = (0,lo) ∪ (hi,∞)`. -/
def rejectsMiddleTrips (lo hi : ℝ) (σ : TripPolicy) : Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → (τ ∈ σ ↔ τ < lo ∨ hi < τ)

/--
Certificate for paper Theorem 1.  The continuous renewal-reward proof that such
a threshold policy exists remains the hard source-specific step; the wrapper
keeps the paper statement explicit.
-/
structure SingleStateThresholdCertificate (R : SingleStateReward)
    (w : PricingFunction) where
  policy : TripPolicy
  threshold : ℝ
  threshold_nonneg : 0 ≤ threshold
  threshold_shape : thresholdRatePolicy w threshold policy
  optimal : singleStateOptimal R policy

/--
Theorem 1 certificate constructor from the paper's Step 1/2/3 proof
obligations. This packages the earlier assembly theorem into the standard
single-state threshold-certificate interface used by later wrappers.
-/
def paper_theorem1_threshold_certificate_of_step_certificates
    (R : SingleStateReward) (w : PricingFunction)
    (strict complete : ℝ → TripPolicy) (cstar : ℝ)
    (hcstar_nonneg : 0 ≤ cstar)
    (hcomplete_shape :
      ∀ c : ℝ, thresholdRatePolicy w c (complete c))
    (hstep1 :
      ∀ σ : TripPolicy, ∃ c : ℝ, ∃ ρ : TripPolicy,
        partialThresholdRatePolicy w c ρ ∧ R σ ≤ R ρ)
    (hstep2 :
      ∀ c : ℝ, ∀ ρ : TripPolicy,
        partialThresholdRatePolicy w c ρ →
          R ρ ≤ max (R (strict c)) (R (complete c)))
    (hstep3 :
      ∀ c : ℝ, R (strict c) ≤ R (complete cstar) ∧
        R (complete c) ≤ R (complete cstar)) :
    SingleStateThresholdCertificate R w where
  policy := complete cstar
  threshold := cstar
  threshold_nonneg := hcstar_nonneg
  threshold_shape := hcomplete_shape cstar
  optimal := by
    intro σ
    rcases hstep1 σ with ⟨c, ρ, hpartial, hσ_le_ρ⟩
    have hρ_le_max := hstep2 c ρ hpartial
    have hmax_le :
        max (R (strict c)) (R (complete c)) ≤ R (complete cstar) := by
      exact max_le (hstep3 c).1 (hstep3 c).2
    exact hσ_le_ρ.trans (hρ_le_max.trans hmax_le)

/--
Theorem 1, conditional source-facing wrapper: given the continuous
renewal-reward threshold certificate, an optimal threshold policy exists.
-/
theorem paper_theorem1_single_state_threshold_best_response_of_certificate
    (R : SingleStateReward) (w : PricingFunction)
    (C : SingleStateThresholdCertificate R w) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ σ : TripPolicy,
      thresholdRatePolicy w c σ ∧ singleStateOptimal R σ := by
  exact ⟨C.threshold, C.threshold_nonneg, C.policy, C.threshold_shape, C.optimal⟩

/-- Two threshold policies agree away from the boundary set `w(τ)/τ = c`. -/
def agreesAwayFromThresholdBoundary
    (w : PricingFunction) (c : ℝ) (σ ρ : TripPolicy) : Prop :=
  ∀ ⦃τ : TripLength⦄, 0 < τ → w τ / τ ≠ c → (τ ∈ σ ↔ τ ∈ ρ)

/--
Lemma 4 certificate: a single-state optimal threshold policy can be chosen
with reward equal to the threshold and is unique away from boundary trips.
-/
structure SingleStateUniqueThresholdCertificate
    (R : SingleStateReward) (w : PricingFunction) where
  policy : TripPolicy
  threshold : ℝ
  threshold_nonneg : 0 ≤ threshold
  threshold_shape : thresholdRatePolicy w threshold policy
  reward_eq_threshold : R policy = threshold
  optimal : singleStateOptimal R policy
  unique_away_boundary :
    ∀ ρ : TripPolicy, singleStateOptimal R ρ →
      agreesAwayFromThresholdBoundary w threshold policy ρ

/-- Lemma 4 endpoint, conditional on the continuous uniqueness certificate. -/
theorem paper_lemma4_single_state_unique_threshold_of_certificate
    (R : SingleStateReward) (w : PricingFunction)
    (C : SingleStateUniqueThresholdCertificate R w) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ σ : TripPolicy,
      thresholdRatePolicy w c σ ∧ R σ = c ∧ singleStateOptimal R σ ∧
        ∀ ρ : TripPolicy, singleStateOptimal R ρ →
          agreesAwayFromThresholdBoundary w c σ ρ := by
  exact ⟨C.threshold, C.threshold_nonneg, C.policy, C.threshold_shape,
    C.reward_eq_threshold, C.optimal, C.unique_away_boundary⟩

/--
Paper Proposition 3.1 certificate: in the one-state model, affine pricing
`w(τ)=mτ+a` is IC under the paper's sufficient condition `0 ≤ a ≤ m/λ`.
-/
structure SingleStateAffineICCertificate
    (R : SingleStateReward) (w : PricingFunction) (m a arrivalRate : ℝ) where
  lambda_pos : 0 < arrivalRate
  multiplier_pos : 0 < m
  additive_nonneg : 0 ≤ a
  additive_le_wait_value : a ≤ m / arrivalRate
  affine_form : ∀ τ : TripLength, w τ = m * τ + a
  accept_all_optimal : singleStateIncentiveCompatible R

/-- Proposition 3.1, conditional source-facing affine-pricing IC wrapper. -/
theorem paper_proposition3_1_affine_single_state_ic_of_certificate
    (R : SingleStateReward) (w : PricingFunction) (m a arrivalRate : ℝ)
    (C : SingleStateAffineICCertificate R w m a arrivalRate) :
    singleStateIncentiveCompatible R := by
  exact C.accept_all_optimal

/-- Dynamic two-state accept-all policy. -/
def acceptAllDynamicPolicy : Fin 2 → TripPolicy :=
  fun _ => acceptAllPolicy

/-- A statewise feasible dynamic policy that accepts all positive trips is accept-all. -/
theorem eq_acceptAllDynamicPolicy_of_statewise_subset_acceptsAll
    {σ : Fin 2 → TripPolicy}
    (hsubset : ∀ i : Fin 2, σ i ⊆ acceptAllPolicy)
    (hall : ∀ i : Fin 2, acceptsAllTrips (σ i)) :
    σ = acceptAllDynamicPolicy := by
  funext i
  exact eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
    (hsubset i) (hall i)

/-- A dynamic policy is optimal for a two-state lifetime reward functional. -/
def dynamicOptimal (R : DynamicReward) (σ : Fin 2 → TripPolicy) : Prop :=
  ∀ ρ : Fin 2 → TripPolicy, R ρ ≤ R σ

/-- Dynamic source IC predicate: accepting all trips in both states is optimal. -/
def dynamicIncentiveCompatible (R : DynamicReward) : Prop :=
  dynamicOptimal R acceptAllDynamicPolicy

/--
Statewise continuation reward induced by a dynamic reward functional after
holding the other state's policy fixed.
-/
def dynamicStateReward
    (R : DynamicReward) (σ : Fin 2 → TripPolicy) (i : Fin 2) :
    SingleStateReward :=
  fun τ => R (Function.update σ i τ)

/--
A dynamically optimal policy is locally optimal in each state when the other
state's policy is fixed.
-/
theorem dynamicStateReward_optimal_of_dynamicOptimal
    (R : DynamicReward) {σ : Fin 2 → TripPolicy}
    (hσ : dynamicOptimal R σ) (i : Fin 2) :
    ∀ τ : TripPolicy,
      dynamicStateReward R σ i τ ≤ dynamicStateReward R σ i (σ i) := by
  intro τ
  unfold dynamicStateReward
  simpa [Function.update_eq_self] using hσ (Function.update σ i τ)

/--
If replacing either state's policy by accept-all weakly improves reward, then
accept-all is dynamically optimal.
-/
theorem dynamicOptimal_acceptAll_of_statewise_acceptAll_improvements
    (R : DynamicReward)
    (hnonsurge :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicStateReward R σ 0 (σ 0) ≤
          dynamicStateReward R σ 0 acceptAllPolicy)
    (hsurge :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicStateReward R σ 1 (σ 1) ≤
          dynamicStateReward R σ 1 acceptAllPolicy) :
    dynamicOptimal R acceptAllDynamicPolicy := by
  intro σ
  have h0 :
      R σ ≤ R (Function.update σ 0 acceptAllPolicy) := by
    simpa [dynamicStateReward, Function.update_eq_self] using hnonsurge σ
  have h1 :
      R (Function.update σ 0 acceptAllPolicy) ≤ R acceptAllDynamicPolicy := by
    have h := hsurge (Function.update σ 0 acceptAllPolicy)
    unfold dynamicStateReward at h
    have hcur :
        Function.update (Function.update σ 0 acceptAllPolicy) 1
            (σ 1) =
          Function.update σ 0 acceptAllPolicy := by
      have hval : (Function.update σ 0 acceptAllPolicy) 1 = σ 1 := by
        simp
      rw [← hval]
      exact Function.update_eq_self 1 (Function.update σ 0 acceptAllPolicy)
    have htarget :
        Function.update (Function.update σ 0 acceptAllPolicy) 1
            acceptAllPolicy =
          acceptAllDynamicPolicy := by
      funext i
      fin_cases i <;> simp [acceptAllDynamicPolicy]
    simpa [hcur, htarget] using h
  exact le_trans h0 h1

/--
Accept-all unique optimality from a strict global dominance certificate. This
is the direct order-theoretic endpoint used after the continuous derivative
arguments rule out every non-accept-all optimum.
-/
theorem acceptAllDynamic_unique_optimal_of_strict_dominates
    (R : DynamicReward)
    (hweak : ∀ σ : Fin 2 → TripPolicy, R σ ≤ R acceptAllDynamicPolicy)
    (hstrict :
      ∀ σ : Fin 2 → TripPolicy,
        σ ≠ acceptAllDynamicPolicy → R σ < R acceptAllDynamicPolicy) :
    dynamicOptimal R acceptAllDynamicPolicy ∧
      ∀ σ : Fin 2 → TripPolicy,
        dynamicOptimal R σ → σ = acceptAllDynamicPolicy := by
  constructor
  · exact hweak
  · intro σ hopt
    by_contra hne
    have hlt := hstrict σ hne
    have hge : R acceptAllDynamicPolicy ≤ R σ := hopt acceptAllDynamicPolicy
    linarith

/--
Accept-all unique optimality from the statewise conclusion that every optimal
policy is feasible and accepts all positive trip requests in both states.
-/
theorem acceptAllDynamic_unique_optimal_of_statewise_accept_all_optima
    (R : DynamicReward)
    (haccept_opt : dynamicOptimal R acceptAllDynamicPolicy)
    (hfeasible :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicOptimal R σ → ∀ i : Fin 2, σ i ⊆ acceptAllPolicy)
    (hall :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicOptimal R σ → ∀ i : Fin 2, acceptsAllTrips (σ i)) :
    dynamicOptimal R acceptAllDynamicPolicy ∧
      ∀ σ : Fin 2 → TripPolicy,
        dynamicOptimal R σ → σ = acceptAllDynamicPolicy := by
  constructor
  · exact haccept_opt
  · intro σ hσ
    exact eq_acceptAllDynamicPolicy_of_statewise_subset_acceptsAll
      (hfeasible σ hσ) (hall σ hσ)

/--
Strict local-improvement certificate: if an optimal policy fails accept-all in
some state, the one-state continuation problem has a strict profitable local
replacement.  Together with existence of an optimum and feasibility of all
optima, this is enough to recover accept-all unique optimality without a global
weak-dominance comparison against accept-all.
-/
structure Theorem4StrictLocalImprovementCertificate
    (R : DynamicReward) where
  exists_optimal : ∃ σ : Fin 2 → TripPolicy, dynamicOptimal R σ
  feasible_optimal :
    ∀ σ : Fin 2 → TripPolicy, dynamicOptimal R σ →
      ∀ i : Fin 2, σ i ⊆ acceptAllPolicy
  nonsurge_strict_improvement_unless :
    ∀ σ : Fin 2 → TripPolicy, (hσ : dynamicOptimal R σ) →
      ¬ acceptsAllTrips (σ 0) →
        ∃ τ : TripPolicy,
          dynamicStateReward R σ 0 (σ 0) < dynamicStateReward R σ 0 τ
  surge_strict_improvement_unless :
    ∀ σ : Fin 2 → TripPolicy, (hσ : dynamicOptimal R σ) →
      ¬ acceptsAllTrips (σ 1) →
        ∃ τ : TripPolicy,
          dynamicStateReward R σ 1 (σ 1) < dynamicStateReward R σ 1 τ

/--
Strict local improvements rule out every non-accept-all optimum.  An existing
optimum must therefore equal accept-all, which gives accept-all optimality and
uniqueness.
-/
theorem acceptAllDynamic_unique_optimal_of_strict_local_improvements
    (R : DynamicReward)
    (C : Theorem4StrictLocalImprovementCertificate R) :
    dynamicOptimal R acceptAllDynamicPolicy ∧
      ∀ σ : Fin 2 → TripPolicy,
        dynamicOptimal R σ → σ = acceptAllDynamicPolicy := by
  have hall :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicOptimal R σ → ∀ i : Fin 2, acceptsAllTrips (σ i) := by
    intro σ hσ i
    fin_cases i
    · by_contra hnot
      rcases C.nonsurge_strict_improvement_unless σ hσ hnot with
        ⟨τ, hlt⟩
      have hlocal := dynamicStateReward_optimal_of_dynamicOptimal R hσ 0 τ
      linarith
    · by_contra hnot
      rcases C.surge_strict_improvement_unless σ hσ hnot with
        ⟨τ, hlt⟩
      have hlocal := dynamicStateReward_optimal_of_dynamicOptimal R hσ 1 τ
      linarith
  have hunique :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicOptimal R σ → σ = acceptAllDynamicPolicy := by
    intro σ hσ
    exact eq_acceptAllDynamicPolicy_of_statewise_subset_acceptsAll
      (C.feasible_optimal σ hσ) (hall σ hσ)
  rcases C.exists_optimal with ⟨σstar, hσstar⟩
  have hstar_eq := hunique σstar hσstar
  have haccept : dynamicOptimal R acceptAllDynamicPolicy := by
    simpa [hstar_eq] using hσstar
  exact ⟨haccept, hunique⟩

/-- Concrete dynamic profitable-deviation witness against accept-all behavior. -/
def dynamicProfitableDeviation (R : DynamicReward) (ρ : Fin 2 → TripPolicy) : Prop :=
  R acceptAllDynamicPolicy < R ρ

/-- A profitable dynamic deviation refutes incentive compatibility. -/
theorem not_dynamicIncentiveCompatible_of_profitableDeviation
    (R : DynamicReward) (ρ : Fin 2 → TripPolicy)
    (hdev : dynamicProfitableDeviation R ρ) :
    ¬ dynamicIncentiveCompatible R := by
  intro hIC
  exact not_le_of_gt hdev (hIC ρ)

/--
Section 4.1 two-state CTMC transition probability from state `i` to the other
state after elapsed time `s`.
-/
def gn21SwitchProb (lambdaIJ lambdaJI s : ℝ) : ℝ :=
  twoStateCtmcSwitchProb lambdaIJ lambdaJI s

/-- Section 4.1 two-state CTMC transition kernel on non-surge/surge states. -/
def gn21TransitionProb (lambda01 lambda10 s : ℝ) (i j : Fin 2) : ℝ :=
  twoStateCtmcTransitionProb lambda01 lambda10 s i j

/-- Lemma 2 formula, as the reusable two-state CTMC switch probability. -/
theorem paper_lemma2_switch_probability_formula
    (lambdaIJ lambdaJI s : ℝ) :
    gn21SwitchProb lambdaIJ lambdaJI s =
      lambdaIJ / (lambdaIJ + lambdaJI) *
        (1 - Real.exp (-(lambdaIJ + lambdaJI) * s)) := by
  rfl

/-- Lemma 2 initial condition: the switch probability is zero at elapsed time zero. -/
@[simp] theorem paper_lemma2_switch_probability_zero
    (lambdaIJ lambdaJI : ℝ) :
    gn21SwitchProb lambdaIJ lambdaJI 0 = 0 := by
  simp [gn21SwitchProb]

/--
Lemma 2 ODE check: the closed-form switch probability satisfies the two-state
Kolmogorov forward equation.
-/
theorem paper_lemma2_switch_probability_forward_equation
    (lambdaIJ lambdaJI s : ℝ) (hsum : lambdaIJ + lambdaJI ≠ 0) :
    deriv (fun t => gn21SwitchProb lambdaIJ lambdaJI t) s =
      lambdaIJ * (1 - gn21SwitchProb lambdaIJ lambdaJI s) -
        lambdaJI * gn21SwitchProb lambdaIJ lambdaJI s := by
  exact twoStateCtmcSwitchProb_deriv_eq_forward lambdaIJ lambdaJI s hsum

/-- Lemma 2 probability-range lower bound for the closed-form switch probability. -/
theorem paper_lemma2_switch_probability_nonneg
    (lambdaIJ lambdaJI s : ℝ)
    (hlambdaIJ : 0 ≤ lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hs : 0 ≤ s) :
    0 ≤ gn21SwitchProb lambdaIJ lambdaJI s := by
  exact twoStateCtmcSwitchProb_nonneg lambdaIJ lambdaJI s hlambdaIJ hsum hs

/-- Lemma 2 strict positivity for positive elapsed time and positive outbound rate. -/
theorem paper_lemma2_switch_probability_pos
    (lambdaIJ lambdaJI s : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hs : 0 < s) :
    0 < gn21SwitchProb lambdaIJ lambdaJI s := by
  exact twoStateCtmcSwitchProb_pos lambdaIJ lambdaJI s hlambdaIJ hsum hs

/-- Lemma 2 probability-range upper bound for the closed-form switch probability. -/
theorem paper_lemma2_switch_probability_le_one
    (lambdaIJ lambdaJI s : ℝ)
    (hlambdaIJ : 0 ≤ lambdaIJ) (hlambdaJI : 0 ≤ lambdaJI)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hs : 0 ≤ s) :
    gn21SwitchProb lambdaIJ lambdaJI s ≤ 1 := by
  exact twoStateCtmcSwitchProb_le_one lambdaIJ lambdaJI s
    hlambdaIJ hlambdaJI hsum hs

/-- Lemma 2 transition-kernel initial condition. -/
theorem paper_lemma2_transition_probability_zero_time
    (lambda01 lambda10 : ℝ) (i j : Fin 2) :
    gn21TransitionProb lambda01 lambda10 0 i j =
      if i = j then 1 else 0 := by
  exact twoStateCtmcTransitionProb_zero_time lambda01 lambda10 i j

/-- Lemma 2 transition-kernel row-sum identity. -/
theorem paper_lemma2_transition_probability_row_sum
    (lambda01 lambda10 s : ℝ) (i : Fin 2) :
    gn21TransitionProb lambda01 lambda10 s i 0 +
        gn21TransitionProb lambda01 lambda10 s i 1 = 1 := by
  exact twoStateCtmcTransitionProb_row_sum lambda01 lambda10 s i

/-!
Lemma 3's stochastic renewal argument has a law-of-large-numbers layer and a
deterministic algebra layer.  The declarations below close the algebra layer:
once subcycle lengths and cross-state subcycle probabilities are reduced to
the paper's `T_i` and `Q_i` quantities, the displayed formula for `μ_i`
follows by cancellation.
-/

/-- Paper subcycle length `S_i = λ_i F_i/(λ_i F_i+λ_{i→j}) * T_i`. -/
def gn21SubcycleLength
    (arrivalRate acceptProb switchRate stateCycleTime : ℝ) : ℝ :=
  (arrivalRate * acceptProb) / (arrivalRate * acceptProb + switchRate) *
    stateCycleTime

/-- Lemma 1/3 one-state cycle time `T_i(σ_i)` from the source paper. -/
def gn21StateCycleTime
    (μ : Measure TripLength) (arrivalRate : ℝ) (σ : TripPolicy) : ℝ :=
  1 / (arrivalRate * singleStateTripMass μ σ) +
    singleStateTripTime μ σ / singleStateTripMass μ σ

/-- Lemma 3 integral exit weight `Q_i(σ_i)`. -/
def gn21ExitWeightIntegral
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy) : ℝ :=
  switchIJ + arrivalRate * ∫ τ in σ, gn21SwitchProb switchIJ switchJI τ ∂μ

/-- Exit weights are at least the raw switch rate under nonnegative arrivals and feasible trips. -/
theorem gn21ExitWeightIntegral_ge_switch_of_nonneg
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (harrival_nonneg : 0 ≤ arrivalRate)
    (hswitch_nonneg : 0 ≤ switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hσ_measurable : MeasurableSet σ)
    (hσ_positive : σ ⊆ acceptAllPolicy) :
    switchIJ ≤ gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ := by
  unfold gn21ExitWeightIntegral
  have hintegral_nonneg :
      0 ≤ ∫ τ in σ, gn21SwitchProb switchIJ switchJI τ ∂μ := by
    exact setIntegral_nonneg hσ_measurable (fun τ hτ =>
      paper_lemma2_switch_probability_nonneg switchIJ switchJI τ
        hswitch_nonneg hsum (le_of_lt (hσ_positive hτ)))
  have hcomponent_nonneg :
      0 ≤ arrivalRate * ∫ τ in σ, gn21SwitchProb switchIJ switchJI τ ∂μ :=
    mul_nonneg harrival_nonneg hintegral_nonneg
  linarith

/-- Exit weights are positive when the raw switch rate is positive. -/
theorem gn21ExitWeightIntegral_pos_of_switch_pos
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (harrival_nonneg : 0 ≤ arrivalRate)
    (hswitch_pos : 0 < switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hσ_measurable : MeasurableSet σ)
    (hσ_positive : σ ⊆ acceptAllPolicy) :
    0 < gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ := by
  exact lt_of_lt_of_le hswitch_pos
    (gn21ExitWeightIntegral_ge_switch_of_nonneg μ arrivalRate switchIJ switchJI σ
      harrival_nonneg (le_of_lt hswitch_pos) hsum hσ_measurable hσ_positive)

/--
Appendix D scaled state time `T_i = λ_i F_i(σ_i)T_i(σ_i) =
1 + λ_i ∫_σ τ dF_i(τ)`.
-/
def gn21ScaledStateTime
    (μ : Measure TripLength) (arrivalRate : ℝ) (σ : TripPolicy) : ℝ :=
  1 + arrivalRate * singleStateTripTime μ σ

/-- Scaled state time is at least one under nonnegative arrivals and feasible trips. -/
theorem gn21ScaledStateTime_ge_one_of_nonneg
    (μ : Measure TripLength) (arrivalRate : ℝ) (σ : TripPolicy)
    (harrival_nonneg : 0 ≤ arrivalRate)
    (hσ_measurable : MeasurableSet σ)
    (hσ_positive : σ ⊆ acceptAllPolicy) :
    1 ≤ gn21ScaledStateTime μ arrivalRate σ := by
  unfold gn21ScaledStateTime
  have htime_nonneg :
      0 ≤ singleStateTripTime μ σ :=
    singleStateTripTime_nonneg_of_subset_acceptAll μ σ hσ_measurable hσ_positive
  nlinarith [mul_nonneg harrival_nonneg htime_nonneg]

/-- Scaled state time is positive under nonnegative arrivals and feasible trips. -/
theorem gn21ScaledStateTime_pos_of_nonneg
    (μ : Measure TripLength) (arrivalRate : ℝ) (σ : TripPolicy)
    (harrival_nonneg : 0 ≤ arrivalRate)
    (hσ_measurable : MeasurableSet σ)
    (hσ_positive : σ ⊆ acceptAllPolicy) :
    0 < gn21ScaledStateTime μ arrivalRate σ := by
  exact lt_of_lt_of_le zero_lt_one
    (gn21ScaledStateTime_ge_one_of_nonneg μ arrivalRate σ
      harrival_nonneg hσ_measurable hσ_positive)

/-- Appendix D scaled state earning `W_i = λ_i ∫_σ w_i(τ)dF_i(τ)`. -/
def gn21ScaledStateEarning
    (μ : Measure TripLength) (arrivalRate : ℝ)
    (w : PricingFunction) (σ : TripPolicy) : ℝ :=
  arrivalRate * singleStateTripPayment μ w σ

/-- Structured IC price family from Theorem 3: `w_i(τ)=m_i τ + z_i q_{i→j}(τ)`. -/
def structuredSurgePrice (m z : ℝ) (q : TripLength → ℝ) : PricingFunction :=
  fun τ => m * τ + z * q τ

/-- Theorem 3 structured price using the Lemma 2 two-state CTMC switch probability. -/
def ctmcStructuredSurgePrice
    (m z lambdaIJ lambdaJI : ℝ) : PricingFunction :=
  structuredSurgePrice m z (gn21SwitchProb lambdaIJ lambdaJI)

/--
Theorem 3 state-indexed CTMC switch probabilities.  State `0` is the
non-surge state and state `1` is the surge state.
-/
def ctmcDynamicSwitchProb
    (switch12 switch21 : ℝ) (i : Fin 2) : TripLength → ℝ :=
  if i = 0 then
    gn21SwitchProb switch12 switch21
  else
    gn21SwitchProb switch21 switch12

@[simp] theorem ctmcDynamicSwitchProb_zero
    (switch12 switch21 : ℝ) :
    ctmcDynamicSwitchProb switch12 switch21 0 =
      gn21SwitchProb switch12 switch21 := by
  simp [ctmcDynamicSwitchProb]

@[simp] theorem ctmcDynamicSwitchProb_one
    (switch12 switch21 : ℝ) :
    ctmcDynamicSwitchProb switch12 switch21 1 =
      gn21SwitchProb switch21 switch12 := by
  simp [ctmcDynamicSwitchProb]

/-- Theorem 3 state-indexed structured CTMC price family. -/
def ctmcStructuredDynamicSurgePrice
    (m z : Fin 2 → ℝ) (switch12 switch21 : ℝ) :
    Fin 2 → PricingFunction :=
  fun i => structuredSurgePrice (m i) (z i)
    (ctmcDynamicSwitchProb switch12 switch21 i)

/-- The state-indexed CTMC price family has the paper's structured form. -/
theorem ctmcStructuredDynamicSurgePrice_price_form
    (m z : Fin 2 → ℝ) (switch12 switch21 : ℝ) (i : Fin 2)
    (τ : TripLength) :
    ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
      structuredSurgePrice (m i) (z i)
        (ctmcDynamicSwitchProb switch12 switch21 i) τ := by
  rfl

/--
The scaled Appendix D time agrees with the product
`λ_i F_i(σ_i)T_i(σ_i)` when the mass denominators are nonzero.
-/
def gn21ScaledStateCycleTime
    (μ : Measure TripLength) (arrivalRate : ℝ) (σ : TripPolicy) : ℝ :=
  arrivalRate * singleStateTripMass μ σ *
    gn21StateCycleTime μ arrivalRate σ

/-- Algebraic bridge between Lemma 1's cycle time and Appendix D's scaled `T_i`. -/
theorem gn21ScaledStateCycleTime_eq_scaledStateTime
    (μ : Measure TripLength) (arrivalRate : ℝ) (σ : TripPolicy)
    (hmass : singleStateTripMass μ σ ≠ 0)
    (harrival_mass : arrivalRate * singleStateTripMass μ σ ≠ 0) :
    gn21ScaledStateCycleTime μ arrivalRate σ =
      gn21ScaledStateTime μ arrivalRate σ := by
  unfold gn21ScaledStateCycleTime gn21StateCycleTime gn21ScaledStateTime
  have harrival : arrivalRate ≠ 0 := by
    intro harrival_zero
    exact harrival_mass (by rw [harrival_zero, zero_mul])
  field_simp [hmass, harrival]

/--
Remark 2 algebra for structured prices:
`W_i = m(T_i-1)+z(Q_i-λ_{i→j})`.
-/
theorem paper_remark2_structured_scaled_earning_algebra
    (μ : Measure TripLength) (arrivalRate m z switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (htime_integrable :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (hq_integrable :
      IntegrableOn (fun τ : TripLength =>
        gn21SwitchProb switchIJ switchJI τ) σ μ) :
    gn21ScaledStateEarning μ arrivalRate
        (ctmcStructuredSurgePrice m z switchIJ switchJI) σ =
      m * (gn21ScaledStateTime μ arrivalRate σ - 1) +
        z * (gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ - switchIJ) := by
  unfold gn21ScaledStateEarning singleStateTripPayment ctmcStructuredSurgePrice
    structuredSurgePrice gn21ScaledStateTime singleStateTripTime
    gn21ExitWeightIntegral
  rw [integral_add]
  · rw [integral_const_mul, integral_const_mul]
    ring
  · exact htime_integrable.const_mul m
  · exact hq_integrable.const_mul z

/-- Remark 3 derivative at zero of the CTMC switch probability. -/
theorem paper_remark3_switch_probability_deriv_at_zero
    (lambdaIJ lambdaJI : ℝ) (hsum : lambdaIJ + lambdaJI ≠ 0) :
    deriv (fun u => gn21SwitchProb lambdaIJ lambdaJI u) 0 = lambdaIJ := by
  rw [paper_lemma2_switch_probability_forward_equation lambdaIJ lambdaJI 0 hsum]
  simp

/-- Remark 3 limit form: `q_{i→j}(u)/u` tends to `lambdaIJ` at zero. -/
theorem paper_remark3_switch_probability_per_time_tendsto_at_zero
    (lambdaIJ lambdaJI : ℝ) (hsum : lambdaIJ + lambdaJI ≠ 0) :
    Filter.Tendsto (fun u => gn21SwitchProb lambdaIJ lambdaJI u / u)
      (𝓝[≠] 0) (𝓝 lambdaIJ) := by
  simpa [gn21SwitchProb, twoStateCtmcSwitchProbPerTime] using
    twoStateCtmcSwitchProbPerTime_tendsto_at_zero lambdaIJ lambdaJI hsum

/-- Remark 1 CTMC fact: `q_{i→j}(u)/u` is locally strictly decreasing for positive elapsed time. -/
theorem paper_remark1_switch_probability_per_time_deriv_neg
    (lambdaIJ lambdaJI u : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hu : 0 < u) :
    deriv (fun s => gn21SwitchProb lambdaIJ lambdaJI s / s) u < 0 := by
  simpa [gn21SwitchProb, twoStateCtmcSwitchProbPerTime] using
    twoStateCtmcSwitchProbPerTime_deriv_neg lambdaIJ lambdaJI u
      hlambdaIJ hsum hu

/-- Remark 1 CTMC fact: `q_{i→j}(u)/u` is strictly decreasing on positive elapsed times. -/
theorem paper_remark1_switch_probability_per_time_strictAntiOn
    (lambdaIJ lambdaJI : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI) :
    StrictAntiOn (fun u => gn21SwitchProb lambdaIJ lambdaJI u / u)
      (Set.Ioi 0) := by
  simpa [gn21SwitchProb, twoStateCtmcSwitchProbPerTime] using
    twoStateCtmcSwitchProbPerTime_strictAntiOn_Ioi lambdaIJ lambdaJI
      hlambdaIJ hsum

/--
Remark 4 pointwise inequality: `λ_{i→j} τ - q_{i→j}(τ) >= 0` for
nonnegative rates and nonnegative trip length.
-/
theorem paper_remark4_switch_time_minus_switch_probability_nonneg
    (lambdaIJ lambdaJI τ : ℝ)
    (hlambdaIJ : 0 ≤ lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (_hτ : 0 ≤ τ) :
    0 ≤ lambdaIJ * τ - gn21SwitchProb lambdaIJ lambdaJI τ := by
  unfold gn21SwitchProb twoStateCtmcSwitchProb
  have h_exp_bound :
      1 - Real.exp (-(lambdaIJ + lambdaJI) * τ) ≤
        (lambdaIJ + lambdaJI) * τ := by
    have h := Real.add_one_le_exp (-(lambdaIJ + lambdaJI) * τ)
    linarith
  have hmul := mul_le_mul_of_nonneg_left h_exp_bound
    (div_nonneg hlambdaIJ (le_of_lt hsum))
  have hprod :
      lambdaIJ / (lambdaIJ + lambdaJI) *
          ((lambdaIJ + lambdaJI) * τ) = lambdaIJ * τ := by
    field_simp [ne_of_gt hsum]
  linarith

/--
Remark 4 strict pointwise inequality: for positive elapsed time, the CTMC
switch probability is below its instantaneous-rate linearization.
-/
theorem paper_remark4_switch_probability_lt_rate_mul_time
    (lambdaIJ lambdaJI τ : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hτ : 0 < τ) :
    gn21SwitchProb lambdaIJ lambdaJI τ < lambdaIJ * τ := by
  exact twoStateCtmcSwitchProb_lt_rate_mul_time
    lambdaIJ lambdaJI τ hlambdaIJ hsum hτ

/-- Remark 4 per-time form: `q_{i→j}(τ)/τ < λ_{i→j}` for `τ > 0`. -/
theorem paper_remark4_switch_probability_per_time_lt_rate
    (lambdaIJ lambdaJI τ : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hτ : 0 < τ) :
    gn21SwitchProb lambdaIJ lambdaJI τ / τ < lambdaIJ := by
  simpa [gn21SwitchProb, twoStateCtmcSwitchProbPerTime] using
    twoStateCtmcSwitchProbPerTime_lt_rate lambdaIJ lambdaJI τ
      hlambdaIJ hsum hτ

/--
Remark 4 strict positivity of the linearization gap `λ_{i→j}τ-q_{i→j}(τ)`
for positive elapsed time.
-/
theorem paper_remark4_switch_time_minus_switch_probability_pos
    (lambdaIJ lambdaJI τ : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hτ : 0 < τ) :
    0 < lambdaIJ * τ - gn21SwitchProb lambdaIJ lambdaJI τ := by
  have hlt :=
    paper_remark4_switch_probability_lt_rate_mul_time
      lambdaIJ lambdaJI τ hlambdaIJ hsum hτ
  linarith

/--
Remark 4 derivative calculation: `λ_{i→j}τ - q_{i→j}(τ)` has nonnegative
derivative on nonnegative trip lengths.
-/
theorem paper_remark4_switch_time_minus_switch_probability_deriv_nonneg
    (lambdaIJ lambdaJI τ : ℝ)
    (hlambdaIJ : 0 ≤ lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hτ : 0 ≤ τ) :
    0 ≤ deriv (fun s => lambdaIJ * s - gn21SwitchProb lambdaIJ lambdaJI s) τ := by
  have hderiv :
      HasDerivAt
        (fun s => lambdaIJ * s - gn21SwitchProb lambdaIJ lambdaJI s)
        (lambdaIJ -
          lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * τ)) τ := by
    have hq :
        HasDerivAt (fun s => gn21SwitchProb lambdaIJ lambdaJI s)
          (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * τ)) τ := by
      convert twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI τ using 1
      field_simp [ne_of_gt hsum]
    simpa [mul_comm] using ((hasDerivAt_id τ).const_mul lambdaIJ).sub hq
  rw [hderiv.deriv]
  have harg : -(lambdaIJ + lambdaJI) * τ ≤ 0 := by nlinarith
  have hexp_le_one : Real.exp (-(lambdaIJ + lambdaJI) * τ) ≤ 1 := by
    have := (Real.exp_le_exp).2 harg
    simpa using this
  nlinarith [mul_le_mul_of_nonneg_left hexp_le_one hlambdaIJ]

/--
Remark 4 strict derivative calculation: with positive outbound rate and
positive elapsed time, `λ_{i→j}τ - q_{i→j}(τ)` is locally strictly increasing.
-/
theorem paper_remark4_switch_time_minus_switch_probability_deriv_pos
    (lambdaIJ lambdaJI τ : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hτ : 0 < τ) :
    0 < deriv (fun s => lambdaIJ * s - gn21SwitchProb lambdaIJ lambdaJI s) τ := by
  have hderiv :
      HasDerivAt
        (fun s => lambdaIJ * s - gn21SwitchProb lambdaIJ lambdaJI s)
        (lambdaIJ -
          lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * τ)) τ := by
    have hq :
        HasDerivAt (fun s => gn21SwitchProb lambdaIJ lambdaJI s)
          (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * τ)) τ := by
      convert twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI τ using 1
      field_simp [ne_of_gt hsum]
    simpa [mul_comm] using ((hasDerivAt_id τ).const_mul lambdaIJ).sub hq
  rw [hderiv.deriv]
  have harg : -(lambdaIJ + lambdaJI) * τ < 0 := by nlinarith
  have hexp_lt_one : Real.exp (-(lambdaIJ + lambdaJI) * τ) < 1 := by
    have := (Real.exp_lt_exp).2 harg
    simpa using this
  nlinarith [mul_lt_mul_of_pos_left hexp_lt_one hlambdaIJ]

/-- Remark 4 source monotonicity: `λ_{i→j}τ - q_{i→j}(τ)` is strictly increasing on `τ > 0`. -/
theorem paper_remark4_switch_time_minus_switch_probability_strictMonoOn
    (lambdaIJ lambdaJI : ℝ)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI) :
    StrictMonoOn
      (fun τ => lambdaIJ * τ - gn21SwitchProb lambdaIJ lambdaJI τ)
      (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro τ hτ
    have hq :
        HasDerivAt (fun s => gn21SwitchProb lambdaIJ lambdaJI s)
          (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * τ)) τ := by
      convert twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI τ using 1
      field_simp [ne_of_gt hsum]
    exact (((hasDerivAt_id τ).const_mul lambdaIJ).sub hq).continuousAt.continuousWithinAt
  · intro τ hτ
    have hτ_pos : 0 < τ := by
      simpa using hτ
    exact paper_remark4_switch_time_minus_switch_probability_deriv_pos
      lambdaIJ lambdaJI τ hlambdaIJ hsum hτ_pos

/--
Remark 4 algebra: `λ_{i→j}T_i - Q_i` is the integral of
`λ_{i→j}τ - q_{i→j}(τ)`, multiplied by the arrival rate.
-/
theorem paper_remark4_scaled_time_minus_exit_weight_eq_integral
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (htime_integrable :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (hq_integrable :
      IntegrableOn (fun τ : TripLength =>
        gn21SwitchProb switchIJ switchJI τ) σ μ) :
    switchIJ * gn21ScaledStateTime μ arrivalRate σ -
        gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ =
      arrivalRate *
        ∫ τ in σ, switchIJ * τ - gn21SwitchProb switchIJ switchJI τ ∂μ := by
  unfold gn21ScaledStateTime singleStateTripTime gn21ExitWeightIntegral
  rw [integral_sub]
  · rw [integral_const_mul]
    ring
  · exact htime_integrable.const_mul switchIJ
  · exact hq_integrable

/-- Remark 4 nonnegativity of `λ_{i→j}T_i - Q_i` in measured form. -/
theorem paper_remark4_scaled_time_minus_exit_weight_nonneg
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (harrival_nonneg : 0 ≤ arrivalRate)
    (hswitch_nonneg : 0 ≤ switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hσ_measurable : MeasurableSet σ)
    (hσ_positive : σ ⊆ acceptAllPolicy) :
    0 ≤ arrivalRate *
      ∫ τ in σ, switchIJ * τ - gn21SwitchProb switchIJ switchJI τ ∂μ := by
  apply mul_nonneg harrival_nonneg
  exact setIntegral_nonneg hσ_measurable (fun τ hτ =>
    paper_remark4_switch_time_minus_switch_probability_nonneg
      switchIJ switchJI τ hswitch_nonneg hsum (le_of_lt (hσ_positive hτ)))

/--
Remark 4 strict positivity of the `λτ-q(τ)` integral component when the
accepted feasible set has positive measure.
-/
theorem paper_remark4_scaled_time_minus_exit_weight_integral_pos_of_positive_measure
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (harrival_pos : 0 < arrivalRate)
    (hswitch_pos : 0 < switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hσ_measurable : MeasurableSet σ)
    (hσ_positive : σ ⊆ acceptAllPolicy)
    (hintegrable :
      IntegrableOn
        (fun τ : TripLength =>
          switchIJ * τ - gn21SwitchProb switchIJ switchJI τ)
        σ μ)
    (hmeasure_pos : 0 < μ σ) :
    0 < arrivalRate *
      ∫ τ in σ, switchIJ * τ - gn21SwitchProb switchIJ switchJI τ ∂μ := by
  have hnonneg_ae :
      0 ≤ᵐ[μ.restrict σ]
        (fun τ : TripLength =>
          switchIJ * τ - gn21SwitchProb switchIJ switchJI τ) :=
    (ae_restrict_iff' hσ_measurable).2
      (Filter.Eventually.of_forall (fun τ hτ =>
        le_of_lt
          (paper_remark4_switch_time_minus_switch_probability_pos
            switchIJ switchJI τ hswitch_pos hsum (hσ_positive hτ))))
  have hsupport :
      Function.support
          (fun τ : TripLength =>
            switchIJ * τ - gn21SwitchProb switchIJ switchJI τ) ∩ σ = σ := by
    ext τ
    constructor
    · intro hτ
      exact hτ.2
    · intro hτ
      exact
        ⟨ne_of_gt
          (paper_remark4_switch_time_minus_switch_probability_pos
            switchIJ switchJI τ hswitch_pos hsum (hσ_positive hτ)), hτ⟩
  have hintegral_pos :
      0 < ∫ τ in σ, switchIJ * τ - gn21SwitchProb switchIJ switchJI τ ∂μ := by
    exact (setIntegral_pos_iff_support_of_nonneg_ae
      hnonneg_ae hintegrable).2 (by
        simpa [hsupport] using hmeasure_pos)
  exact mul_pos harrival_pos hintegral_pos

/--
Remark 4 strict measured form:
`λ_{i→j}T_i(σ_i)-Q_i(σ_i) > 0` whenever the feasible accepted set has
positive measure.
-/
theorem paper_remark4_scaled_time_minus_exit_weight_pos_of_positive_measure
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (harrival_pos : 0 < arrivalRate)
    (hswitch_pos : 0 < switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hσ_measurable : MeasurableSet σ)
    (hσ_positive : σ ⊆ acceptAllPolicy)
    (htime_integrable :
      IntegrableOn (fun τ : TripLength => τ) σ μ)
    (hq_integrable :
      IntegrableOn (fun τ : TripLength =>
        gn21SwitchProb switchIJ switchJI τ) σ μ)
    (hmeasure_pos : 0 < μ σ) :
    0 < switchIJ * gn21ScaledStateTime μ arrivalRate σ -
        gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ := by
  rw [paper_remark4_scaled_time_minus_exit_weight_eq_integral
    μ arrivalRate switchIJ switchJI σ htime_integrable hq_integrable]
  exact
    paper_remark4_scaled_time_minus_exit_weight_integral_pos_of_positive_measure
      μ arrivalRate switchIJ switchJI σ harrival_pos hswitch_pos hsum
      hσ_measurable hσ_positive
      ((htime_integrable.const_mul switchIJ).sub hq_integrable)
      hmeasure_pos

/--
Remark 4 maximization step: the nonnegative integrand
`λ_{i→j}τ - q_{i→j}(τ)` has largest feasible set integral at accept-all.
-/
theorem paper_remark4_scaled_time_minus_exit_weight_le_acceptAll
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (harrival_nonneg : 0 ≤ arrivalRate)
    (hswitch_nonneg : 0 ≤ switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hintegrable_acceptAll :
      IntegrableOn
        (fun τ : TripLength =>
          switchIJ * τ - gn21SwitchProb switchIJ switchJI τ)
        acceptAllPolicy μ)
    (hσ_subset : σ ⊆ acceptAllPolicy) :
    arrivalRate *
        ∫ τ in σ, switchIJ * τ - gn21SwitchProb switchIJ switchJI τ ∂μ ≤
      arrivalRate *
        ∫ τ in acceptAllPolicy,
          switchIJ * τ - gn21SwitchProb switchIJ switchJI τ ∂μ := by
  apply mul_le_mul_of_nonneg_left ?_ harrival_nonneg
  apply setIntegral_mono_set hintegrable_acceptAll
  · exact (ae_restrict_iff' measurableSet_acceptAllPolicy).2
      (Filter.Eventually.of_forall (fun τ hτ => by
      exact paper_remark4_switch_time_minus_switch_probability_nonneg
        switchIJ switchJI τ hswitch_nonneg hsum
        (le_of_lt (by
          simpa [acceptAllPolicy, positiveTripLengths] using hτ))))
  · exact Filter.Eventually.of_forall (fun _ hτ => hσ_subset hτ)

/-- Remark 4 nonnegativity of the CTMC exit-weight integral component. -/
theorem paper_remark4_exit_weight_integral_component_nonneg
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (harrival_nonneg : 0 ≤ arrivalRate)
    (hswitch_nonneg : 0 ≤ switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hσ_measurable : MeasurableSet σ)
    (hσ_positive : σ ⊆ acceptAllPolicy) :
    0 ≤ arrivalRate *
      ∫ τ in σ, gn21SwitchProb switchIJ switchJI τ ∂μ := by
  apply mul_nonneg harrival_nonneg
  exact setIntegral_nonneg hσ_measurable (fun τ hτ =>
    paper_lemma2_switch_probability_nonneg
      switchIJ switchJI τ hswitch_nonneg hsum
      (le_of_lt (hσ_positive hτ)))

/--
Remark 4 strict positivity of the CTMC switch-probability integral component
when the accepted feasible set has positive measure.
-/
theorem paper_remark4_exit_weight_integral_component_pos_of_positive_measure
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (harrival_pos : 0 < arrivalRate)
    (hswitch_pos : 0 < switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hσ_measurable : MeasurableSet σ)
    (hσ_positive : σ ⊆ acceptAllPolicy)
    (hintegrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switchIJ switchJI τ)
        σ μ)
    (hmeasure_pos : 0 < μ σ) :
    0 < arrivalRate *
      ∫ τ in σ, gn21SwitchProb switchIJ switchJI τ ∂μ := by
  have hnonneg_ae :
      0 ≤ᵐ[μ.restrict σ]
        (fun τ : TripLength => gn21SwitchProb switchIJ switchJI τ) :=
    (ae_restrict_iff' hσ_measurable).2
      (Filter.Eventually.of_forall (fun τ hτ =>
        le_of_lt
          (paper_lemma2_switch_probability_pos
            switchIJ switchJI τ hswitch_pos hsum (hσ_positive hτ))))
  have hsupport :
      Function.support
          (fun τ : TripLength => gn21SwitchProb switchIJ switchJI τ) ∩ σ = σ := by
    ext τ
    constructor
    · intro hτ
      exact hτ.2
    · intro hτ
      exact
        ⟨ne_of_gt
          (paper_lemma2_switch_probability_pos
            switchIJ switchJI τ hswitch_pos hsum (hσ_positive hτ)), hτ⟩
  have hintegral_pos :
      0 < ∫ τ in σ, gn21SwitchProb switchIJ switchJI τ ∂μ := by
    exact (setIntegral_pos_iff_support_of_nonneg_ae
      hnonneg_ae hintegrable).2 (by
        simpa [hsupport] using hmeasure_pos)
  exact mul_pos harrival_pos hintegral_pos

/--
Remark 4 strict measured form for the exit weight:
`Q_i(σ_i) > λ_{i→j}` whenever the feasible accepted set has positive measure.
-/
theorem paper_remark4_exit_weight_gt_switch_of_positive_measure
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (harrival_pos : 0 < arrivalRate)
    (hswitch_pos : 0 < switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hσ_measurable : MeasurableSet σ)
    (hσ_positive : σ ⊆ acceptAllPolicy)
    (hintegrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switchIJ switchJI τ)
        σ μ)
    (hmeasure_pos : 0 < μ σ) :
    switchIJ < gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI σ := by
  unfold gn21ExitWeightIntegral
  have hpos :=
    paper_remark4_exit_weight_integral_component_pos_of_positive_measure
      μ arrivalRate switchIJ switchJI σ harrival_pos hswitch_pos hsum
      hσ_measurable hσ_positive hintegrable hmeasure_pos
  linarith

/--
Remark 4 maximization step for `Q_i`: the nonnegative switch-probability
integral is largest at accept-all.
-/
theorem paper_remark4_exit_weight_integral_component_le_acceptAll
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (σ : TripPolicy)
    (harrival_nonneg : 0 ≤ arrivalRate)
    (hswitch_nonneg : 0 ≤ switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hintegrable_acceptAll :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switchIJ switchJI τ)
        acceptAllPolicy μ)
    (hσ_subset : σ ⊆ acceptAllPolicy) :
    arrivalRate *
        ∫ τ in σ, gn21SwitchProb switchIJ switchJI τ ∂μ ≤
      arrivalRate *
        ∫ τ in acceptAllPolicy, gn21SwitchProb switchIJ switchJI τ ∂μ := by
  apply mul_le_mul_of_nonneg_left ?_ harrival_nonneg
  apply setIntegral_mono_set hintegrable_acceptAll
  · exact (ae_restrict_iff' measurableSet_acceptAllPolicy).2
      (Filter.Eventually.of_forall (fun τ hτ => by
      exact paper_lemma2_switch_probability_nonneg
        switchIJ switchJI τ hswitch_nonneg hsum
        (le_of_lt (by
          simpa [acceptAllPolicy, positiveTripLengths] using hτ))))
  · exact Filter.Eventually.of_forall (fun _ hτ => hσ_subset hτ)

/-!
Appendix D.3 works with a derivative-sign expression.  The declarations below
formalize the algebraic kernel used in Lemma 6 and the structured-price
simplification in Remark 2.  They do not assert differentiability of the
underlying set-valued reward functional; that analytic bridge remains tracked
separately in the README.
-/

/--
Lemma 6 scaled derivative-sign kernel:
`q(W_j T_i - T_j W_i) + w_i(u)(Q_i T_j + Q_j T_i)
 - u(Q_i W_j + Q_j W_i)`.
-/
def gn21DerivativeSignKernel
    (q u wi Qi Qj Ti Tj Wi Wj : ℝ) : ℝ :=
  q * (Wj * Ti - Tj * Wi) +
    wi * (Qi * Tj + Qj * Ti) -
      u * (Qi * Wj + Qj * Wi)

/-- Lemma 6 derivative kernel after substituting state reward rates `W_k=R_kT_k`. -/
def gn21DerivativeSignKernelWithRates
    (q u wi Qi Qj Ti Tj Ri Rj : ℝ) : ℝ :=
  q * ((Rj - Ri) * Tj * Ti) +
    wi * (Qi * Tj + Qj * Ti) -
      u * (Qi * Rj * Tj + Qj * Ri * Ti)

/--
Lemma 6 normalized response expression:
`q/u * (R_j-R_i) + w_i(u)/u * (Q_i/T_i + Q_j/T_j)
 - (Q_i/T_i R_j + Q_j/T_j R_i)`.
-/
def gn21Lemma6Response
    (q u wi Qi Qj Ti Tj Ri Rj : ℝ) : ℝ :=
  q / u * (Rj - Ri) +
    wi / u * (Qi / Ti + Qj / Tj) -
      (Qi / Ti * Rj + Qj / Tj * Ri)

/--
Lemma 6 aggregate dynamic reward after Lemma 1's time-fraction reduction:
`(Q_i W_j + Q_j W_i)/(Q_i T_j + Q_j T_i)`.
-/
def gn21AggregateDynamicReward
    (Qi Qj Ti Tj Wi Wj : ℝ) : ℝ :=
  (Qi * Wj + Qj * Wi) / (Qi * Tj + Qj * Ti)

/-- The aggregate two-state quotient is symmetric in the order of the states. -/
theorem gn21AggregateDynamicReward_swap
    (Qi Qj Ti Tj Wi Wj : ℝ) :
    gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj =
      gn21AggregateDynamicReward Qj Qi Tj Ti Wj Wi := by
  unfold gn21AggregateDynamicReward
  ring

/-- Endpoint path for `Q_i = lambda_{i→j} + lambda_i ∫ q_{i→j}(τ) f_i(τ)dτ`. -/
def gn21EndpointQiPath
    (arrivalRate switchRate lowerEndpoint : ℝ)
    (density switchProb : ℝ → ℝ) (x : ℝ) : ℝ :=
  switchRate +
    arrivalRate * ∫ τ in lowerEndpoint..x, switchProb τ * density τ

/-- Endpoint path for `W_i = lambda_i ∫ w_i(τ) f_i(τ)dτ`. -/
def gn21EndpointWiPath
    (arrivalRate lowerEndpoint : ℝ)
    (density payment : ℝ → ℝ) (x : ℝ) : ℝ :=
  arrivalRate * ∫ τ in lowerEndpoint..x, payment τ * density τ

/-- Endpoint path for `T_i = 1 + lambda_i ∫ τ f_i(τ)dτ`. -/
def gn21EndpointTiPath
    (arrivalRate lowerEndpoint : ℝ)
    (density : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + arrivalRate * ∫ τ in lowerEndpoint..x, τ * density τ

/-- Lower-endpoint path for `Q_i` with fixed upper endpoint. -/
def gn21LowerEndpointQiPath
    (arrivalRate switchRate upperEndpoint : ℝ)
    (density switchProb : ℝ → ℝ) (x : ℝ) : ℝ :=
  switchRate +
    arrivalRate * ∫ τ in x..upperEndpoint, switchProb τ * density τ

/-- Lower-endpoint path for `W_i` with fixed upper endpoint. -/
def gn21LowerEndpointWiPath
    (arrivalRate upperEndpoint : ℝ)
    (density payment : ℝ → ℝ) (x : ℝ) : ℝ :=
  arrivalRate * ∫ τ in x..upperEndpoint, payment τ * density τ

/-- Lower-endpoint path for `T_i` with fixed upper endpoint. -/
def gn21LowerEndpointTiPath
    (arrivalRate upperEndpoint : ℝ)
    (density : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + arrivalRate * ∫ τ in x..upperEndpoint, τ * density τ

/-- Tail path for `Q_i` on the unbounded policy interval `(x,∞)`. -/
def gn21TailQiPath
    (arrivalRate switchRate : ℝ)
    (density switchProb : ℝ → ℝ) (x : ℝ) : ℝ :=
  switchRate + arrivalRate * ∫ τ in Set.Ioi x, switchProb τ * density τ

/-- Tail path for `W_i` on the unbounded policy interval `(x,∞)`. -/
def gn21TailWiPath
    (arrivalRate : ℝ)
    (density payment : ℝ → ℝ) (x : ℝ) : ℝ :=
  arrivalRate * ∫ τ in Set.Ioi x, payment τ * density τ

/-- Tail path for `T_i` on the unbounded policy interval `(x,∞)`. -/
def gn21TailTiPath
    (arrivalRate : ℝ)
    (density : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + arrivalRate * ∫ τ in Set.Ioi x, τ * density τ

/-- Two-piece path for `Q_i` on the middle-rejection policy `(0,lo) ∪ (hi,∞)`. -/
def gn21RejectMiddleQiPath
    (arrivalRate switchRate : ℝ)
    (density switchProb : ℝ → ℝ) (lo hi : ℝ) : ℝ :=
  switchRate +
    arrivalRate *
      ((∫ τ in (0 : ℝ)..lo, switchProb τ * density τ) +
        ∫ τ in Set.Ioi hi, switchProb τ * density τ)

/-- Two-piece path for `W_i` on the middle-rejection policy `(0,lo) ∪ (hi,∞)`. -/
def gn21RejectMiddleWiPath
    (arrivalRate : ℝ)
    (density payment : ℝ → ℝ) (lo hi : ℝ) : ℝ :=
  arrivalRate *
    ((∫ τ in (0 : ℝ)..lo, payment τ * density τ) +
      ∫ τ in Set.Ioi hi, payment τ * density τ)

/-- Two-piece path for `T_i` on the middle-rejection policy `(0,lo) ∪ (hi,∞)`. -/
def gn21RejectMiddleTiPath
    (arrivalRate : ℝ)
    (density : ℝ → ℝ) (lo hi : ℝ) : ℝ :=
  1 + arrivalRate *
    ((∫ τ in (0 : ℝ)..lo, τ * density τ) +
      ∫ τ in Set.Ioi hi, τ * density τ)

/-- Upper-endpoint interval policy used by the interval-density endpoint paths. -/
def gn21UpperEndpointPolicy (lowerEndpoint x : ℝ) : TripPolicy :=
  Set.Ioc lowerEndpoint x

/-- Measurability of the upper-endpoint interval policy. -/
theorem measurableSet_gn21UpperEndpointPolicy (lowerEndpoint x : ℝ) :
    MeasurableSet (gn21UpperEndpointPolicy lowerEndpoint x) := by
  simpa [gn21UpperEndpointPolicy] using measurableSet_Ioc

/--
Measured-policy realization of the endpoint `Q_i` path when trip lengths are
Lebesgue distributed with density `density` and the accepted set is the upper
endpoint interval `(lowerEndpoint, x]`.
-/
theorem gn21ExitWeightIntegral_upperEndpoint_withDensity_eq_endpointQiPath
    (arrivalRate switchIJ switchJI lowerEndpoint x : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hle : lowerEndpoint ≤ x) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (gn21UpperEndpointPolicy lowerEndpoint x) =
      gn21EndpointQiPath arrivalRate switchIJ lowerEndpoint
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) x := by
  unfold gn21ExitWeightIntegral gn21EndpointQiPath gn21UpperEndpointPolicy
  rw [intervalIntegral.integral_of_le hle]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density)
    hdensity_meas
    (fun τ => gn21SwitchProb switchIJ switchJI τ)
    measurableSet_Ioc]
  apply congrArg (fun y => switchIJ + arrivalRate * y)
  apply setIntegral_congr_fun measurableSet_Ioc
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/--
Measured-policy realization of the endpoint `T_i` path under an interval policy
and a Lebesgue density.
-/
theorem gn21ScaledStateTime_upperEndpoint_withDensity_eq_endpointTiPath
    (arrivalRate lowerEndpoint x : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hle : lowerEndpoint ≤ x) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (gn21UpperEndpointPolicy lowerEndpoint x) =
      gn21EndpointTiPath arrivalRate lowerEndpoint
        (fun τ => (density τ : ℝ)) x := by
  unfold gn21ScaledStateTime singleStateTripTime gn21EndpointTiPath
    gn21UpperEndpointPolicy
  rw [intervalIntegral.integral_of_le hle]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas (fun τ => τ)
    measurableSet_Ioc]
  apply congrArg (fun y => 1 + arrivalRate * y)
  apply setIntegral_congr_fun measurableSet_Ioc
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/--
Measured-policy realization of the endpoint `W_i` path under an interval policy
and a Lebesgue density.
-/
theorem gn21ScaledStateEarning_upperEndpoint_withDensity_eq_endpointWiPath
    (arrivalRate lowerEndpoint x : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hle : lowerEndpoint ≤ x) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (gn21UpperEndpointPolicy lowerEndpoint x) =
      gn21EndpointWiPath arrivalRate lowerEndpoint
        (fun τ => (density τ : ℝ)) payment x := by
  unfold gn21ScaledStateEarning singleStateTripPayment gn21EndpointWiPath
    gn21UpperEndpointPolicy
  rw [intervalIntegral.integral_of_le hle]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas payment
    measurableSet_Ioc]
  apply congrArg (fun y => arrivalRate * y)
  apply setIntegral_congr_fun measurableSet_Ioc
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/-- Right-endpoint replacement path based at `(lowerEndpoint, u]`. -/
def gn21UpperEndpointReplacement
    (lowerEndpoint u : ℝ) (ε : ℝ) : TripPolicy :=
  gn21UpperEndpointPolicy lowerEndpoint (u + ε)

/-- Measurability of the right-endpoint replacement path. -/
theorem measurableSet_gn21UpperEndpointReplacement
    (lowerEndpoint u ε : ℝ) :
    MeasurableSet (gn21UpperEndpointReplacement lowerEndpoint u ε) := by
  simpa [gn21UpperEndpointReplacement] using
    measurableSet_gn21UpperEndpointPolicy lowerEndpoint (u + ε)

/--
An upper-endpoint interval is feasible whenever its lower endpoint is
nonnegative.
-/
theorem gn21UpperEndpointPolicy_subset_acceptAllPolicy
    (lowerEndpoint x : ℝ)
    (hlower_nonneg : 0 ≤ lowerEndpoint) :
    gn21UpperEndpointPolicy lowerEndpoint x ⊆ acceptAllPolicy := by
  intro τ hτ
  exact lt_of_le_of_lt hlower_nonneg hτ.1

/--
Right-endpoint replacements stay feasible whenever the base lower endpoint is
nonnegative.
-/
theorem gn21UpperEndpointReplacement_subset_acceptAllPolicy
    (lowerEndpoint u ε : ℝ)
    (hlower_nonneg : 0 ≤ lowerEndpoint) :
    gn21UpperEndpointReplacement lowerEndpoint u ε ⊆ acceptAllPolicy := by
  simpa [gn21UpperEndpointReplacement] using
    gn21UpperEndpointPolicy_subset_acceptAllPolicy lowerEndpoint (u + ε)
      hlower_nonneg

/-- Real trip mass is positive when the underlying measure mass is nonzero and finite. -/
theorem singleStateTripMass_pos_of_measure_ne_zero_ne_top
    (μ : Measure TripLength) (σ : TripPolicy)
    (h_ne_zero : μ σ ≠ 0)
    (h_ne_top : μ σ ≠ ∞) :
    0 < singleStateTripMass μ σ := by
  exact ENNReal.toReal_pos h_ne_zero h_ne_top

/-- A nontrivial upper-endpoint interval has positive Lebesgue mass. -/
theorem volume_gn21UpperEndpointPolicy_ne_zero
    (lowerEndpoint x : ℝ)
    (hlt : lowerEndpoint < x) :
    volume (gn21UpperEndpointPolicy lowerEndpoint x) ≠ 0 := by
  rw [gn21UpperEndpointPolicy, Real.volume_Ioc]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hlt))

/--
Positive density on a measurable set gives positive real trip mass under a
finite `withDensity` measure.
-/
theorem singleStateTripMass_withDensity_pos_of_pos_on
    (D : TripLength → ℝ≥0∞) {σ : TripPolicy}
    (hD : Measurable D)
    (hσ : MeasurableSet σ)
    (hvolume_ne_zero : volume σ ≠ 0)
    (hfinite : (volume.withDensity D) σ ≠ ∞)
    (hpos : ∀ τ, τ ∈ σ → D τ ≠ 0) :
    0 < singleStateTripMass (volume.withDensity D) σ := by
  exact
    singleStateTripMass_pos_of_measure_ne_zero_ne_top
      (volume.withDensity D) σ
      (withDensity_measure_ne_zero_of_pos_on volume D hD hσ
        hvolume_ne_zero hpos)
      hfinite

/--
Positive NNReal density on a nontrivial upper-endpoint interval gives positive
real trip mass under a finite `withDensity` measure.
-/
theorem singleStateTripMass_upperEndpoint_withDensity_pos_of_pos_on
    (density : TripLength → NNReal)
    (hdensity_meas : Measurable density)
    (lowerEndpoint x : ℝ)
    (hlt : lowerEndpoint < x)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21UpperEndpointPolicy lowerEndpoint x) ≠ ∞)
    (hpos :
      ∀ τ, τ ∈ gn21UpperEndpointPolicy lowerEndpoint x → density τ ≠ 0) :
    0 <
      singleStateTripMass
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21UpperEndpointPolicy lowerEndpoint x) := by
  refine
    singleStateTripMass_withDensity_pos_of_pos_on
      (fun τ => (density τ : ℝ≥0∞))
      (measurable_coe_nnreal_ennreal.comp hdensity_meas)
      (measurableSet_gn21UpperEndpointPolicy lowerEndpoint x)
      (volume_gn21UpperEndpointPolicy_ne_zero lowerEndpoint x hlt)
      hfinite ?_
  intro τ hτ
  simpa using hpos τ hτ

/--
Positive NNReal density on a nontrivial right-endpoint replacement interval
gives positive real trip mass under a finite `withDensity` measure.
-/
theorem singleStateTripMass_upperEndpointReplacement_withDensity_pos_of_pos_on
    (density : TripLength → NNReal)
    (hdensity_meas : Measurable density)
    (lowerEndpoint u ε : ℝ)
    (hle : lowerEndpoint < u)
    (hε_pos : 0 < ε)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21UpperEndpointReplacement lowerEndpoint u ε) ≠ ∞)
    (hpos :
      ∀ τ, τ ∈ gn21UpperEndpointReplacement lowerEndpoint u ε →
        density τ ≠ 0) :
    0 <
      singleStateTripMass
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21UpperEndpointReplacement lowerEndpoint u ε) := by
  simpa [gn21UpperEndpointReplacement] using
    singleStateTripMass_upperEndpoint_withDensity_pos_of_pos_on
      density hdensity_meas lowerEndpoint (u + ε) (by linarith)
      (by simpa [gn21UpperEndpointReplacement] using hfinite)
      (by
        intro τ hτ
        exact hpos τ (by simpa [gn21UpperEndpointReplacement] using hτ))

/-- `Q_i` primitive realization along the positive right-endpoint replacement path. -/
theorem gn21ExitWeightIntegral_upperEndpointReplacement_withDensity_eq_endpointQiPath
    (arrivalRate switchIJ switchJI lowerEndpoint u ε : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hle : lowerEndpoint ≤ u)
    (hε_pos : 0 < ε) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (gn21UpperEndpointReplacement lowerEndpoint u ε) =
      gn21EndpointQiPath arrivalRate switchIJ lowerEndpoint
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) (u + ε) := by
  simpa [gn21UpperEndpointReplacement] using
    gn21ExitWeightIntegral_upperEndpoint_withDensity_eq_endpointQiPath
      arrivalRate switchIJ switchJI lowerEndpoint (u + ε)
      density hdensity_meas (by linarith)

/-- `T_i` primitive realization along the positive right-endpoint replacement path. -/
theorem gn21ScaledStateTime_upperEndpointReplacement_withDensity_eq_endpointTiPath
    (arrivalRate lowerEndpoint u ε : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hle : lowerEndpoint ≤ u)
    (hε_pos : 0 < ε) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (gn21UpperEndpointReplacement lowerEndpoint u ε) =
      gn21EndpointTiPath arrivalRate lowerEndpoint
        (fun τ => (density τ : ℝ)) (u + ε) := by
  simpa [gn21UpperEndpointReplacement] using
    gn21ScaledStateTime_upperEndpoint_withDensity_eq_endpointTiPath
      arrivalRate lowerEndpoint (u + ε) density hdensity_meas (by linarith)

/-- `W_i` primitive realization along the positive right-endpoint replacement path. -/
theorem gn21ScaledStateEarning_upperEndpointReplacement_withDensity_eq_endpointWiPath
    (arrivalRate lowerEndpoint u ε : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hle : lowerEndpoint ≤ u)
    (hε_pos : 0 < ε) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (gn21UpperEndpointReplacement lowerEndpoint u ε) =
      gn21EndpointWiPath arrivalRate lowerEndpoint
        (fun τ => (density τ : ℝ)) payment (u + ε) := by
  simpa [gn21UpperEndpointReplacement] using
    gn21ScaledStateEarning_upperEndpoint_withDensity_eq_endpointWiPath
      arrivalRate lowerEndpoint (u + ε) density payment hdensity_meas
      (by linarith)

/-- Lower-endpoint interval policy used by finite moving-left/right endpoints. -/
def gn21LowerEndpointPolicy (x upperEndpoint : ℝ) : TripPolicy :=
  Set.Ioc x upperEndpoint

/-- Lower-endpoint interval policies are measurable. -/
theorem measurableSet_gn21LowerEndpointPolicy (x upperEndpoint : ℝ) :
    MeasurableSet (gn21LowerEndpointPolicy x upperEndpoint) := by
  simpa [gn21LowerEndpointPolicy] using measurableSet_Ioc

/--
A lower-endpoint interval is feasible whenever its moving lower endpoint is
nonnegative.
-/
theorem gn21LowerEndpointPolicy_subset_acceptAllPolicy
    (x upperEndpoint : ℝ)
    (hx_nonneg : 0 ≤ x) :
    gn21LowerEndpointPolicy x upperEndpoint ⊆ acceptAllPolicy := by
  intro τ hτ
  exact lt_of_le_of_lt hx_nonneg hτ.1

/--
Measured-policy realization of the lower-endpoint `Q_i` path on the finite
interval `(x, upperEndpoint]`.
-/
theorem gn21ExitWeightIntegral_lowerEndpoint_withDensity_eq_lowerEndpointQiPath
    (arrivalRate switchIJ switchJI upperEndpoint x : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hle : x ≤ upperEndpoint) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (gn21LowerEndpointPolicy x upperEndpoint) =
      gn21LowerEndpointQiPath arrivalRate switchIJ upperEndpoint
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) x := by
  unfold gn21ExitWeightIntegral gn21LowerEndpointQiPath gn21LowerEndpointPolicy
  rw [intervalIntegral.integral_of_le hle]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density)
    hdensity_meas
    (fun τ => gn21SwitchProb switchIJ switchJI τ)
    measurableSet_Ioc]
  apply congrArg (fun y => switchIJ + arrivalRate * y)
  apply setIntegral_congr_fun measurableSet_Ioc
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/--
Measured-policy realization of the lower-endpoint `T_i` path on the finite
interval `(x, upperEndpoint]`.
-/
theorem gn21ScaledStateTime_lowerEndpoint_withDensity_eq_lowerEndpointTiPath
    (arrivalRate upperEndpoint x : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hle : x ≤ upperEndpoint) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (gn21LowerEndpointPolicy x upperEndpoint) =
      gn21LowerEndpointTiPath arrivalRate upperEndpoint
        (fun τ => (density τ : ℝ)) x := by
  unfold gn21ScaledStateTime singleStateTripTime gn21LowerEndpointTiPath
    gn21LowerEndpointPolicy
  rw [intervalIntegral.integral_of_le hle]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas (fun τ => τ)
    measurableSet_Ioc]
  apply congrArg (fun y => 1 + arrivalRate * y)
  apply setIntegral_congr_fun measurableSet_Ioc
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/--
Measured-policy realization of the lower-endpoint `W_i` path on the finite
interval `(x, upperEndpoint]`.
-/
theorem gn21ScaledStateEarning_lowerEndpoint_withDensity_eq_lowerEndpointWiPath
    (arrivalRate upperEndpoint x : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hle : x ≤ upperEndpoint) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (gn21LowerEndpointPolicy x upperEndpoint) =
      gn21LowerEndpointWiPath arrivalRate upperEndpoint
        (fun τ => (density τ : ℝ)) payment x := by
  unfold gn21ScaledStateEarning singleStateTripPayment gn21LowerEndpointWiPath
    gn21LowerEndpointPolicy
  rw [intervalIntegral.integral_of_le hle]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas payment
    measurableSet_Ioc]
  apply congrArg (fun y => arrivalRate * y)
  apply setIntegral_congr_fun measurableSet_Ioc
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/-- Rightward movement of a lower endpoint inside a fixed finite interval. -/
def gn21LowerEndpointReplacement
    (upperEndpoint u : ℝ) (ε : ℝ) : TripPolicy :=
  gn21LowerEndpointPolicy (u + ε) upperEndpoint

/-- Lower-endpoint replacements are measurable. -/
theorem measurableSet_gn21LowerEndpointReplacement
    (upperEndpoint u ε : ℝ) :
    MeasurableSet (gn21LowerEndpointReplacement upperEndpoint u ε) := by
  simpa [gn21LowerEndpointReplacement] using
    measurableSet_gn21LowerEndpointPolicy (u + ε) upperEndpoint

/--
Lower-endpoint replacements remain feasible when the base endpoint is
nonnegative and the move is to the right.
-/
theorem gn21LowerEndpointReplacement_subset_acceptAllPolicy
    (upperEndpoint u ε : ℝ)
    (hu_nonneg : 0 ≤ u)
    (hε_nonneg : 0 ≤ ε) :
    gn21LowerEndpointReplacement upperEndpoint u ε ⊆ acceptAllPolicy := by
  refine gn21LowerEndpointPolicy_subset_acceptAllPolicy (u + ε) upperEndpoint ?_
  exact add_nonneg hu_nonneg hε_nonneg

/-- `Q_i` realization along a bounded lower-endpoint replacement path. -/
theorem gn21ExitWeightIntegral_lowerEndpointReplacement_withDensity_eq_lowerEndpointQiPath
    (arrivalRate switchIJ switchJI upperEndpoint u ε : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hle : u + ε ≤ upperEndpoint) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (gn21LowerEndpointReplacement upperEndpoint u ε) =
      gn21LowerEndpointQiPath arrivalRate switchIJ upperEndpoint
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) (u + ε) := by
  simpa [gn21LowerEndpointReplacement] using
    gn21ExitWeightIntegral_lowerEndpoint_withDensity_eq_lowerEndpointQiPath
      arrivalRate switchIJ switchJI upperEndpoint (u + ε)
      density hdensity_meas hle

/-- `T_i` realization along a bounded lower-endpoint replacement path. -/
theorem gn21ScaledStateTime_lowerEndpointReplacement_withDensity_eq_lowerEndpointTiPath
    (arrivalRate upperEndpoint u ε : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hle : u + ε ≤ upperEndpoint) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (gn21LowerEndpointReplacement upperEndpoint u ε) =
      gn21LowerEndpointTiPath arrivalRate upperEndpoint
        (fun τ => (density τ : ℝ)) (u + ε) := by
  simpa [gn21LowerEndpointReplacement] using
    gn21ScaledStateTime_lowerEndpoint_withDensity_eq_lowerEndpointTiPath
      arrivalRate upperEndpoint (u + ε) density hdensity_meas hle

/-- `W_i` realization along a bounded lower-endpoint replacement path. -/
theorem gn21ScaledStateEarning_lowerEndpointReplacement_withDensity_eq_lowerEndpointWiPath
    (arrivalRate upperEndpoint u ε : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hle : u + ε ≤ upperEndpoint) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (gn21LowerEndpointReplacement upperEndpoint u ε) =
      gn21LowerEndpointWiPath arrivalRate upperEndpoint
        (fun τ => (density τ : ℝ)) payment (u + ε) := by
  simpa [gn21LowerEndpointReplacement] using
    gn21ScaledStateEarning_lowerEndpoint_withDensity_eq_lowerEndpointWiPath
      arrivalRate upperEndpoint (u + ε) density payment hdensity_meas hle

/-- Leftward movement of a lower endpoint inside a fixed finite interval. -/
def gn21LowerEndpointLeftReplacement
    (upperEndpoint u : ℝ) (ε : ℝ) : TripPolicy :=
  gn21LowerEndpointPolicy (u - ε) upperEndpoint

/-- Leftward lower-endpoint replacements are measurable. -/
theorem measurableSet_gn21LowerEndpointLeftReplacement
    (upperEndpoint u ε : ℝ) :
    MeasurableSet (gn21LowerEndpointLeftReplacement upperEndpoint u ε) := by
  simpa [gn21LowerEndpointLeftReplacement] using
    measurableSet_gn21LowerEndpointPolicy (u - ε) upperEndpoint

/--
Leftward lower-endpoint replacements remain feasible when the moved endpoint
is still nonnegative.
-/
theorem gn21LowerEndpointLeftReplacement_subset_acceptAllPolicy
    (upperEndpoint u ε : ℝ)
    (hε_le_u : ε ≤ u) :
    gn21LowerEndpointLeftReplacement upperEndpoint u ε ⊆ acceptAllPolicy := by
  refine gn21LowerEndpointPolicy_subset_acceptAllPolicy (u - ε) upperEndpoint ?_
  exact sub_nonneg.mpr hε_le_u

/-- `Q_i` realization along a leftward lower-endpoint replacement path. -/
theorem gn21ExitWeightIntegral_lowerEndpointLeftReplacement_withDensity_eq_lowerEndpointQiPath
    (arrivalRate switchIJ switchJI upperEndpoint u ε : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hle : u - ε ≤ upperEndpoint) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (gn21LowerEndpointLeftReplacement upperEndpoint u ε) =
      gn21LowerEndpointQiPath arrivalRate switchIJ upperEndpoint
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) (u - ε) := by
  simpa [gn21LowerEndpointLeftReplacement] using
    gn21ExitWeightIntegral_lowerEndpoint_withDensity_eq_lowerEndpointQiPath
      arrivalRate switchIJ switchJI upperEndpoint (u - ε)
      density hdensity_meas hle

/-- `T_i` realization along a leftward lower-endpoint replacement path. -/
theorem gn21ScaledStateTime_lowerEndpointLeftReplacement_withDensity_eq_lowerEndpointTiPath
    (arrivalRate upperEndpoint u ε : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hle : u - ε ≤ upperEndpoint) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (gn21LowerEndpointLeftReplacement upperEndpoint u ε) =
      gn21LowerEndpointTiPath arrivalRate upperEndpoint
        (fun τ => (density τ : ℝ)) (u - ε) := by
  simpa [gn21LowerEndpointLeftReplacement] using
    gn21ScaledStateTime_lowerEndpoint_withDensity_eq_lowerEndpointTiPath
      arrivalRate upperEndpoint (u - ε) density hdensity_meas hle

/-- `W_i` realization along a leftward lower-endpoint replacement path. -/
theorem gn21ScaledStateEarning_lowerEndpointLeftReplacement_withDensity_eq_lowerEndpointWiPath
    (arrivalRate upperEndpoint u ε : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hle : u - ε ≤ upperEndpoint) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (gn21LowerEndpointLeftReplacement upperEndpoint u ε) =
      gn21LowerEndpointWiPath arrivalRate upperEndpoint
        (fun τ => (density τ : ℝ)) payment (u - ε) := by
  simpa [gn21LowerEndpointLeftReplacement] using
    gn21ScaledStateEarning_lowerEndpoint_withDensity_eq_lowerEndpointWiPath
      arrivalRate upperEndpoint (u - ε) density payment hdensity_meas hle

/-- Unbounded tail policy `(x,∞)`. -/
def gn21TailPolicy (x : ℝ) : TripPolicy :=
  Set.Ioi x

/-- Tail policies are measurable. -/
theorem measurableSet_gn21TailPolicy (x : ℝ) :
    MeasurableSet (gn21TailPolicy x) := by
  simpa [gn21TailPolicy] using measurableSet_Ioi

/-- Tail policies are feasible when the lower endpoint is nonnegative. -/
theorem gn21TailPolicy_subset_acceptAllPolicy
    (x : ℝ) (hx_nonneg : 0 ≤ x) :
    gn21TailPolicy x ⊆ acceptAllPolicy := by
  intro τ hτ
  exact lt_of_le_of_lt hx_nonneg hτ

/-- Lebesgue mass of an unbounded tail is nonzero. -/
theorem volume_gn21TailPolicy_ne_zero (x : ℝ) :
    volume (gn21TailPolicy x) ≠ 0 := by
  rw [gn21TailPolicy, Real.volume_Ioi]
  exact ENNReal.top_ne_zero

/-- Leftward movement of an unbounded tail cutoff. -/
def gn21TailLeftReplacement (u : ℝ) (ε : ℝ) : TripPolicy :=
  gn21TailPolicy (u - ε)

/-- Tail left-replacements are measurable. -/
theorem measurableSet_gn21TailLeftReplacement (u ε : ℝ) :
    MeasurableSet (gn21TailLeftReplacement u ε) := by
  simpa [gn21TailLeftReplacement] using
    measurableSet_gn21TailPolicy (u - ε)

/-- Tail left-replacements remain feasible while the moved cutoff is nonnegative. -/
theorem gn21TailLeftReplacement_subset_acceptAllPolicy
    (u ε : ℝ) (hε_le_u : ε ≤ u) :
    gn21TailLeftReplacement u ε ⊆ acceptAllPolicy := by
  simpa [gn21TailLeftReplacement] using
    gn21TailPolicy_subset_acceptAllPolicy (u - ε) (sub_nonneg.mpr hε_le_u)

/-- Tail left-replacements have nonzero Lebesgue volume. -/
theorem volume_gn21TailLeftReplacement_ne_zero (u ε : ℝ) :
    volume (gn21TailLeftReplacement u ε) ≠ 0 := by
  simpa [gn21TailLeftReplacement] using
    volume_gn21TailPolicy_ne_zero (u - ε)

/--
Positive NNReal density on a tail left-replacement gives positive real trip
mass under a finite `withDensity` measure.
-/
theorem singleStateTripMass_tailLeftReplacement_withDensity_pos_of_pos_on
    (density : TripLength → NNReal)
    (hdensity_meas : Measurable density)
    (u ε : ℝ)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21TailLeftReplacement u ε) ≠ ∞)
    (hpos :
      ∀ τ, τ ∈ gn21TailLeftReplacement u ε → density τ ≠ 0) :
    0 <
      singleStateTripMass
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21TailLeftReplacement u ε) := by
  refine
    singleStateTripMass_withDensity_pos_of_pos_on
      (fun τ => (density τ : ℝ≥0∞))
      (measurable_coe_nnreal_ennreal.comp hdensity_meas)
      (measurableSet_gn21TailLeftReplacement u ε)
      (volume_gn21TailLeftReplacement_ne_zero u ε)
      hfinite ?_
  intro τ hτ
  simpa using hpos τ hτ

/--
Measured-policy realization of the tail `Q_i` path under a Lebesgue density.
-/
theorem gn21ExitWeightIntegral_tail_withDensity_eq_tailQiPath
    (arrivalRate switchIJ switchJI x : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (gn21TailPolicy x) =
      gn21TailQiPath arrivalRate switchIJ
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) x := by
  unfold gn21ExitWeightIntegral gn21TailQiPath gn21TailPolicy
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density)
    hdensity_meas
    (fun τ => gn21SwitchProb switchIJ switchJI τ)
    measurableSet_Ioi]
  apply congrArg (fun y => switchIJ + arrivalRate * y)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/--
Measured-policy realization of the tail `T_i` path under a Lebesgue density.
-/
theorem gn21ScaledStateTime_tail_withDensity_eq_tailTiPath
    (arrivalRate x : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (gn21TailPolicy x) =
      gn21TailTiPath arrivalRate (fun τ => (density τ : ℝ)) x := by
  unfold gn21ScaledStateTime singleStateTripTime gn21TailTiPath
    gn21TailPolicy
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas (fun τ => τ)
    measurableSet_Ioi]
  apply congrArg (fun y => 1 + arrivalRate * y)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/--
Measured-policy realization of the tail `W_i` path under a Lebesgue density.
-/
theorem gn21ScaledStateEarning_tail_withDensity_eq_tailWiPath
    (arrivalRate x : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (gn21TailPolicy x) =
      gn21TailWiPath arrivalRate
        (fun τ => (density τ : ℝ)) payment x := by
  unfold gn21ScaledStateEarning singleStateTripPayment gn21TailWiPath
    gn21TailPolicy
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas payment
    measurableSet_Ioi]
  apply congrArg (fun y => arrivalRate * y)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/-- `Q_i` realization along a tail left-replacement path. -/
theorem gn21ExitWeightIntegral_tailLeftReplacement_withDensity_eq_tailQiPath
    (arrivalRate switchIJ switchJI u ε : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (gn21TailLeftReplacement u ε) =
      gn21TailQiPath arrivalRate switchIJ
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) (u - ε) := by
  simpa [gn21TailLeftReplacement] using
    gn21ExitWeightIntegral_tail_withDensity_eq_tailQiPath
      arrivalRate switchIJ switchJI (u - ε) density hdensity_meas

/-- `T_i` realization along a tail left-replacement path. -/
theorem gn21ScaledStateTime_tailLeftReplacement_withDensity_eq_tailTiPath
    (arrivalRate u ε : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (gn21TailLeftReplacement u ε) =
      gn21TailTiPath arrivalRate (fun τ => (density τ : ℝ)) (u - ε) := by
  simpa [gn21TailLeftReplacement] using
    gn21ScaledStateTime_tail_withDensity_eq_tailTiPath
      arrivalRate (u - ε) density hdensity_meas

/-- `W_i` realization along a tail left-replacement path. -/
theorem gn21ScaledStateEarning_tailLeftReplacement_withDensity_eq_tailWiPath
    (arrivalRate u ε : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (gn21TailLeftReplacement u ε) =
      gn21TailWiPath arrivalRate
        (fun τ => (density τ : ℝ)) payment (u - ε) := by
  simpa [gn21TailLeftReplacement] using
    gn21ScaledStateEarning_tail_withDensity_eq_tailWiPath
      arrivalRate (u - ε) density payment hdensity_meas

/--
Local FTC bridge for an improper tail integral.  Around `u`, the tail
`∫_(x,∞) f` is a fixed tail constant minus the finite interval integral
`∫_(u-1)^x f`, so its derivative is `-f u`.
-/
theorem integral_Ioi_hasDerivAt
    (f : ℝ → ℝ) (u : ℝ)
    (hint : IntegrableOn f (Set.Ioi (u - 1)) volume)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 u))
    (hcont : ContinuousAt f u) :
    HasDerivAt (fun x => ∫ τ in Set.Ioi x, f τ) (-(f u)) u := by
  let a : ℝ := u - 1
  have hau : a < u := by
    dsimp [a]
    linarith
  have hinterval : IntervalIntegrable f volume a u := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hau.le]
    exact hint.mono_set (fun _ hτ => hτ.1)
  have hfinite :
      HasDerivAt
        (fun x => (∫ τ in Set.Ioi a, f τ) - ∫ τ in a..x, f τ)
        (-(f u)) u := by
    have h :=
      (intervalIntegral.integral_hasDerivAt_right hinterval hmeas hcont).const_sub
        (∫ τ in Set.Ioi a, f τ)
    simpa using h
  have heq :
      (fun x => ∫ τ in Set.Ioi x, f τ) =ᶠ[𝓝 u]
        (fun x => (∫ τ in Set.Ioi a, f τ) - ∫ τ in a..x, f τ) := by
    filter_upwards [Ioi_mem_nhds hau] with x hx
    have hsub := intervalIntegral.integral_Ioi_sub_Ioi hint (le_of_lt hx)
    have hsub' :
        (∫ τ in Set.Ioi a, f τ) - (∫ τ in Set.Ioi x, f τ) =
          ∫ τ in a..x, f τ := by
      simpa [a] using hsub
    linarith
  exact hfinite.congr_of_eventuallyEq heq

/-- Fundamental-theorem bridge for the tail `Q_i` path. -/
theorem gn21TailQiPath_hasDerivAt
    (arrivalRate switchRate u : ℝ)
    (density switchProb : ℝ → ℝ)
    (hint :
      IntegrableOn (fun τ => switchProb τ * density τ) (Set.Ioi (u - 1))
        volume)
    (hmeas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => switchProb τ * density τ) u) :
    HasDerivAt
      (fun x => gn21TailQiPath arrivalRate switchRate density switchProb x)
      (-(arrivalRate * (switchProb u * density u))) u := by
  unfold gn21TailQiPath
  have h :=
    ((integral_Ioi_hasDerivAt
      (fun τ => switchProb τ * density τ) u hint hmeas hcont).const_mul
        arrivalRate).const_add switchRate
  convert h using 1
  ring

/-- Fundamental-theorem bridge for the tail `W_i` path. -/
theorem gn21TailWiPath_hasDerivAt
    (arrivalRate u : ℝ)
    (density payment : ℝ → ℝ)
    (hint :
      IntegrableOn (fun τ => payment τ * density τ) (Set.Ioi (u - 1))
        volume)
    (hmeas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => payment τ * density τ) u) :
    HasDerivAt
      (fun x => gn21TailWiPath arrivalRate density payment x)
      (-(arrivalRate * (payment u * density u))) u := by
  unfold gn21TailWiPath
  have h :=
    (integral_Ioi_hasDerivAt
      (fun τ => payment τ * density τ) u hint hmeas hcont).const_mul
        arrivalRate
  convert h using 1
  ring

/-- Fundamental-theorem bridge for the tail `T_i` path. -/
theorem gn21TailTiPath_hasDerivAt
    (arrivalRate u : ℝ)
    (density : ℝ → ℝ)
    (hint :
      IntegrableOn (fun τ => τ * density τ) (Set.Ioi (u - 1)) volume)
    (hmeas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => τ * density τ) u) :
    HasDerivAt
      (fun x => gn21TailTiPath arrivalRate density x)
      (-(arrivalRate * (u * density u))) u := by
  unfold gn21TailTiPath
  have h :=
    ((integral_Ioi_hasDerivAt
      (fun τ => τ * density τ) u hint hmeas hcont).const_mul
        arrivalRate).const_add 1
  convert h using 1
  ring

/-- Fundamental-theorem bridge for the endpoint `Q_i` path. -/
theorem gn21EndpointQiPath_hasDerivAt
    (arrivalRate switchRate lowerEndpoint u : ℝ)
    (density switchProb : ℝ → ℝ)
    (hint :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        lowerEndpoint u)
    (hmeas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => switchProb τ * density τ) u) :
    HasDerivAt
      (fun x => gn21EndpointQiPath arrivalRate switchRate lowerEndpoint
        density switchProb x)
      (arrivalRate * (switchProb u * density u)) u := by
  unfold gn21EndpointQiPath
  exact
    ((intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).const_mul
      arrivalRate).const_add switchRate

/-- Fundamental-theorem bridge for the endpoint `W_i` path. -/
theorem gn21EndpointWiPath_hasDerivAt
    (arrivalRate lowerEndpoint u : ℝ)
    (density payment : ℝ → ℝ)
    (hint :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        lowerEndpoint u)
    (hmeas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => payment τ * density τ) u) :
    HasDerivAt
      (fun x => gn21EndpointWiPath arrivalRate lowerEndpoint
        density payment x)
      (arrivalRate * (payment u * density u)) u := by
  unfold gn21EndpointWiPath
  exact
    (intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).const_mul
      arrivalRate

/-- Fundamental-theorem bridge for the endpoint `T_i` path. -/
theorem gn21EndpointTiPath_hasDerivAt
    (arrivalRate lowerEndpoint u : ℝ)
    (density : ℝ → ℝ)
    (hint :
      IntervalIntegrable (fun τ => τ * density τ) volume lowerEndpoint u)
    (hmeas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => τ * density τ) u) :
    HasDerivAt
      (fun x => gn21EndpointTiPath arrivalRate lowerEndpoint density x)
      (arrivalRate * (u * density u)) u := by
  unfold gn21EndpointTiPath
  exact
    ((intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).const_mul
      arrivalRate).const_add 1

/-- Fundamental-theorem bridge for the lower-endpoint `Q_i` path. -/
theorem gn21LowerEndpointQiPath_hasDerivAt
    (arrivalRate switchRate upperEndpoint u : ℝ)
    (density switchProb : ℝ → ℝ)
    (hint :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        u upperEndpoint)
    (hmeas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => switchProb τ * density τ) u) :
    HasDerivAt
      (fun x => gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
        density switchProb x)
      (-(arrivalRate * (switchProb u * density u))) u := by
  unfold gn21LowerEndpointQiPath
  convert
    ((intervalIntegral.integral_hasDerivAt_left hint hmeas hcont).const_mul
      arrivalRate).const_add switchRate using 1
  ring

/-- Fundamental-theorem bridge for the lower-endpoint `W_i` path. -/
theorem gn21LowerEndpointWiPath_hasDerivAt
    (arrivalRate upperEndpoint u : ℝ)
    (density payment : ℝ → ℝ)
    (hint :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        u upperEndpoint)
    (hmeas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => payment τ * density τ) u) :
    HasDerivAt
      (fun x => gn21LowerEndpointWiPath arrivalRate upperEndpoint
        density payment x)
      (-(arrivalRate * (payment u * density u))) u := by
  unfold gn21LowerEndpointWiPath
  convert
    (intervalIntegral.integral_hasDerivAt_left hint hmeas hcont).const_mul
      arrivalRate using 1
  ring

/-- Fundamental-theorem bridge for the lower-endpoint `T_i` path. -/
theorem gn21LowerEndpointTiPath_hasDerivAt
    (arrivalRate upperEndpoint u : ℝ)
    (density : ℝ → ℝ)
    (hint :
      IntervalIntegrable (fun τ => τ * density τ) volume u upperEndpoint)
    (hmeas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => τ * density τ) u) :
    HasDerivAt
      (fun x => gn21LowerEndpointTiPath arrivalRate upperEndpoint density x)
      (-(arrivalRate * (u * density u))) u := by
  unfold gn21LowerEndpointTiPath
  convert
    ((intervalIntegral.integral_hasDerivAt_left hint hmeas hcont).const_mul
      arrivalRate).const_add 1 using 1
  ring

/-- Fundamental-theorem bridge for the lower cutoff of a middle-rejection `Q_i` path. -/
theorem gn21RejectMiddleQiPath_lo_hasDerivAt
    (arrivalRate switchRate hi u : ℝ)
    (density switchProb : ℝ → ℝ)
    (hint :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume 0 u)
    (hmeas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => switchProb τ * density τ) u) :
    HasDerivAt
      (fun x => gn21RejectMiddleQiPath arrivalRate switchRate density
        switchProb x hi)
      (arrivalRate * (switchProb u * density u)) u := by
  unfold gn21RejectMiddleQiPath
  have hshort :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  exact
    (((hshort.add_const
      (∫ τ in Set.Ioi hi, switchProb τ * density τ)).const_mul
        arrivalRate).const_add switchRate)

/-- Fundamental-theorem bridge for the lower cutoff of a middle-rejection `W_i` path. -/
theorem gn21RejectMiddleWiPath_lo_hasDerivAt
    (arrivalRate hi u : ℝ)
    (density payment : ℝ → ℝ)
    (hint :
      IntervalIntegrable (fun τ => payment τ * density τ) volume 0 u)
    (hmeas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => payment τ * density τ) u) :
    HasDerivAt
      (fun x => gn21RejectMiddleWiPath arrivalRate density payment x hi)
      (arrivalRate * (payment u * density u)) u := by
  unfold gn21RejectMiddleWiPath
  have hshort :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  exact
    (hshort.add_const
      (∫ τ in Set.Ioi hi, payment τ * density τ)).const_mul arrivalRate

/-- Fundamental-theorem bridge for the lower cutoff of a middle-rejection `T_i` path. -/
theorem gn21RejectMiddleTiPath_lo_hasDerivAt
    (arrivalRate hi u : ℝ)
    (density : ℝ → ℝ)
    (hint :
      IntervalIntegrable (fun τ => τ * density τ) volume 0 u)
    (hmeas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => τ * density τ) u) :
    HasDerivAt
      (fun x => gn21RejectMiddleTiPath arrivalRate density x hi)
      (arrivalRate * (u * density u)) u := by
  unfold gn21RejectMiddleTiPath
  have hshort :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  exact
    (((hshort.add_const
      (∫ τ in Set.Ioi hi, τ * density τ)).const_mul
        arrivalRate).const_add 1)

/-- Fundamental-theorem bridge for the upper cutoff of a middle-rejection `Q_i` path. -/
theorem gn21RejectMiddleQiPath_hi_hasDerivAt
    (arrivalRate switchRate lo u : ℝ)
    (density switchProb : ℝ → ℝ)
    (hint :
      IntegrableOn (fun τ => switchProb τ * density τ) (Set.Ioi (u - 1))
        volume)
    (hmeas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => switchProb τ * density τ) u) :
    HasDerivAt
      (fun x => gn21RejectMiddleQiPath arrivalRate switchRate density
        switchProb lo x)
      (-(arrivalRate * (switchProb u * density u))) u := by
  unfold gn21RejectMiddleQiPath
  have htail :=
    integral_Ioi_hasDerivAt
      (fun τ => switchProb τ * density τ) u hint hmeas hcont
  convert
    (((htail.const_add
      (∫ τ in (0 : ℝ)..lo, switchProb τ * density τ)).const_mul
        arrivalRate).const_add switchRate) using 1
  ring

/-- Fundamental-theorem bridge for the upper cutoff of a middle-rejection `W_i` path. -/
theorem gn21RejectMiddleWiPath_hi_hasDerivAt
    (arrivalRate lo u : ℝ)
    (density payment : ℝ → ℝ)
    (hint :
      IntegrableOn (fun τ => payment τ * density τ) (Set.Ioi (u - 1))
        volume)
    (hmeas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => payment τ * density τ) u) :
    HasDerivAt
      (fun x => gn21RejectMiddleWiPath arrivalRate density payment lo x)
      (-(arrivalRate * (payment u * density u))) u := by
  unfold gn21RejectMiddleWiPath
  have htail :=
    integral_Ioi_hasDerivAt
      (fun τ => payment τ * density τ) u hint hmeas hcont
  convert
    (htail.const_add
      (∫ τ in (0 : ℝ)..lo, payment τ * density τ)).const_mul
        arrivalRate using 1
  ring

/-- Fundamental-theorem bridge for the upper cutoff of a middle-rejection `T_i` path. -/
theorem gn21RejectMiddleTiPath_hi_hasDerivAt
    (arrivalRate lo u : ℝ)
    (density : ℝ → ℝ)
    (hint :
      IntegrableOn (fun τ => τ * density τ) (Set.Ioi (u - 1)) volume)
    (hmeas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (hcont : ContinuousAt (fun τ => τ * density τ) u) :
    HasDerivAt
      (fun x => gn21RejectMiddleTiPath arrivalRate density lo x)
      (-(arrivalRate * (u * density u))) u := by
  unfold gn21RejectMiddleTiPath
  have htail :=
    integral_Ioi_hasDerivAt (fun τ => τ * density τ) u hint hmeas hcont
  convert
    (((htail.const_add
      (∫ τ in (0 : ℝ)..lo, τ * density τ)).const_mul
        arrivalRate).const_add 1) using 1
  ring

/-- Lemma 6 algebraic substitution of state reward rates into the derivative-sign kernel. -/
theorem paper_lemma6_derivative_kernel_state_rate_algebra
    (q u wi Qi Qj Ti Tj Ri Rj : ℝ) :
    gn21DerivativeSignKernel q u wi Qi Qj Ti Tj (Ri * Ti) (Rj * Tj) =
      gn21DerivativeSignKernelWithRates q u wi Qi Qj Ti Tj Ri Rj := by
  unfold gn21DerivativeSignKernel gn21DerivativeSignKernelWithRates
  ring

/--
Lemma 6 displayed-form algebra: the polynomial derivative-sign kernel with
state reward rates is `u T_i T_j` times the paper's normalized response `r`.
-/
theorem paper_lemma6_derivative_kernel_eq_scaled_response
    (q u wi Qi Qj Ti Tj Ri Rj : ℝ)
    (hu : u ≠ 0) (hTi : Ti ≠ 0) (hTj : Tj ≠ 0) :
    gn21DerivativeSignKernelWithRates q u wi Qi Qj Ti Tj Ri Rj =
      u * Ti * Tj *
        gn21Lemma6Response q u wi Qi Qj Ti Tj Ri Rj := by
  unfold gn21DerivativeSignKernelWithRates gn21Lemma6Response
  field_simp [hu, hTi, hTj]

/--
Lemma 6 quotient-calculus bridge.  If along an endpoint expansion
`Q_i' = scale*q`, `W_i' = scale*w_i(u)`, and `T_i' = scale*u`, then the
derivative of the aggregate dynamic reward is a positive scalar multiple of
the Lemma 6 derivative-sign kernel, up to the explicit factor
`scale*Q_j/(Q_i T_j+Q_j T_i)^2`.
-/
theorem paper_lemma6_aggregate_reward_hasDerivAt
    (QiPath WiPath TiPath : ℝ → ℝ)
    (q u wi Qi Qj Ti Tj Wi Wj scale : ℝ)
    (hQi_deriv : HasDerivAt QiPath (scale * q) u)
    (hWi_deriv : HasDerivAt WiPath (scale * wi) u)
    (hTi_deriv : HasDerivAt TiPath (scale * u) u)
    (hQi_val : QiPath u = Qi)
    (hWi_val : WiPath u = Wi)
    (hTi_val : TiPath u = Ti)
    (hden : Qi * Tj + Qj * Ti ≠ 0) :
    HasDerivAt
      (fun x =>
        gn21AggregateDynamicReward (QiPath x) Qj (TiPath x) Tj
          (WiPath x) Wj)
      (scale * Qj *
        gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj /
          (Qi * Tj + Qj * Ti) ^ 2) u := by
  have hnum :
      HasDerivAt
        (fun x => QiPath x * Wj + Qj * WiPath x)
        ((scale * q) * Wj + Qj * (scale * wi)) u := by
    exact (hQi_deriv.mul_const Wj).add (hWi_deriv.const_mul Qj)
  have hden_deriv :
      HasDerivAt
        (fun x => QiPath x * Tj + Qj * TiPath x)
        ((scale * q) * Tj + Qj * (scale * u)) u := by
    exact (hQi_deriv.mul_const Tj).add (hTi_deriv.const_mul Qj)
  have hden_path :
      QiPath u * Tj + Qj * TiPath u ≠ 0 := by
    simpa [hQi_val, hTi_val] using hden
  convert hnum.div hden_deriv hden_path using 1
  rw [hQi_val, hWi_val, hTi_val]
  unfold gn21DerivativeSignKernel
  field_simp [hden]
  ring

/--
Lemmas 7--8 affine-response algebra: after substituting `w_i(u)=m u+a`,
Lemma 6's normalized response has the canonical form used for the
quasi-convex/quasi-concave calculus argument.
-/
theorem paper_lemma7_8_affine_response_canonical_form
    (q u m a Qi Qj Ti Tj Ri Rj : ℝ)
    (hu : u ≠ 0) (hTi : Ti ≠ 0) (hTj : Tj ≠ 0) :
    gn21Lemma6Response q u (m * u + a) Qi Qj Ti Tj Ri Rj =
      ((Qi / Ti + Qj / Tj) * a - (Ri - Rj) * q) / u +
        (m * (Qi / Ti + Qj / Tj) -
          (Qi / Ti * Rj + Qj / Tj * Ri)) := by
  unfold gn21Lemma6Response
  field_simp [hu, hTi, hTj]
  ring

/--
Lemma 7 canonical response after the source reduction
`r(u) = (c1 - c2*q(u))/u + c3`.
-/
def gn21Lemma7CanonicalResponse
    (c1 c2 c3 lambdaIJ lambdaJI u : ℝ) : ℝ :=
  (c1 - c2 * gn21SwitchProb lambdaIJ lambdaJI u) / u + c3

/--
Lemma 8 canonical response, the sign-reversal of Lemma 7's source canonical
response up to an additive constant.
-/
def gn21Lemma8CanonicalResponse
    (c1 c2 c3 lambdaIJ lambdaJI u : ℝ) : ℝ :=
  -((c1 - c2 * gn21SwitchProb lambdaIJ lambdaJI u) / u) + c3

/--
Lemma 7 derivative numerator:
`c2 * (q(u) - u*q'(u)) - c1`, with `q'(u)` expanded from Lemma 2.
-/
def gn21Lemma7CanonicalDerivativeNumerator
    (c1 c2 lambdaIJ lambdaJI u : ℝ) : ℝ :=
  c2 * (gn21SwitchProb lambdaIJ lambdaJI u -
    u * (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * u))) - c1

/-- Lemma 7 closed derivative formula for the canonical response. -/
theorem paper_lemma7_canonical_response_hasDerivAt
    (c1 c2 c3 lambdaIJ lambdaJI u : ℝ)
    (hsum : lambdaIJ + lambdaJI ≠ 0)
    (hu : u ≠ 0) :
    HasDerivAt
      (fun x => gn21Lemma7CanonicalResponse c1 c2 c3 lambdaIJ lambdaJI x)
      (gn21Lemma7CanonicalDerivativeNumerator c1 c2 lambdaIJ lambdaJI u /
        u ^ 2) u := by
  have hq :
      HasDerivAt (fun x => gn21SwitchProb lambdaIJ lambdaJI x)
        (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * u)) u := by
    convert twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI u using 1
    field_simp [hsum]
  have hnum :
      HasDerivAt
        (fun x => c1 - c2 * gn21SwitchProb lambdaIJ lambdaJI x)
        (-(c2 * (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * u)))) u := by
    convert (hq.const_mul c2).const_sub c1 using 1
  have hdiv :=
    hnum.div (hasDerivAt_id u) hu
  have hresp := hdiv.add_const c3
  convert hresp using 1
  unfold gn21Lemma7CanonicalDerivativeNumerator
  simp [id]
  ring_nf

/--
Lemma 7 source-series calculus step: the derivative numerator
`c2*(q(u)-u*q'(u))-c1` has this positive-derivative closed form.
-/
theorem paper_lemma7_canonical_derivative_numerator_hasDerivAt
    (c1 c2 lambdaIJ lambdaJI u : ℝ)
    (hsum : lambdaIJ + lambdaJI ≠ 0) :
    HasDerivAt
      (fun x => gn21Lemma7CanonicalDerivativeNumerator c1 c2 lambdaIJ lambdaJI x)
      (c2 * lambdaIJ * (lambdaIJ + lambdaJI) * u *
        Real.exp (-(lambdaIJ + lambdaJI) * u)) u := by
  have hq :
      HasDerivAt (fun x => gn21SwitchProb lambdaIJ lambdaJI x)
        (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * u)) u := by
    convert twoStateCtmcSwitchProb_hasDerivAt lambdaIJ lambdaJI u using 1
    field_simp [hsum]
  have hlin :
      HasDerivAt (fun x : ℝ => -(lambdaIJ + lambdaJI) * x)
        (-(lambdaIJ + lambdaJI)) u := by
    simpa using ((hasDerivAt_id u).const_mul (-(lambdaIJ + lambdaJI)))
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (-(lambdaIJ + lambdaJI) * x))
        (Real.exp (-(lambdaIJ + lambdaJI) * u) *
          (-(lambdaIJ + lambdaJI))) u := by
    exact hlin.exp
  have hscaled_exp :
      HasDerivAt
        (fun x : ℝ =>
          lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * x))
        (lambdaIJ *
          (Real.exp (-(lambdaIJ + lambdaJI) * u) *
            (-(lambdaIJ + lambdaJI)))) u := by
    simpa [mul_assoc] using hexp.const_mul lambdaIJ
  have hproduct :
      HasDerivAt
        (fun x : ℝ =>
          x * (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * x)))
        (lambdaIJ * Real.exp (-(lambdaIJ + lambdaJI) * u) +
          u * (lambdaIJ *
            (Real.exp (-(lambdaIJ + lambdaJI) * u) *
              (-(lambdaIJ + lambdaJI))))) u := by
    simpa using (hasDerivAt_id u).mul hscaled_exp
  have hdiff :=
    hq.sub hproduct
  have hnum := (hdiff.const_mul c2).sub_const c1
  convert hnum using 1
  ring

/-- Lemma 7 derivative numerator is strictly increasing at positive trip lengths. -/
theorem paper_lemma7_canonical_derivative_numerator_deriv_pos
    (c1 c2 lambdaIJ lambdaJI u : ℝ)
    (hc2 : 0 < c2)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hu : 0 < u) :
    0 <
      deriv
        (fun x => gn21Lemma7CanonicalDerivativeNumerator
          c1 c2 lambdaIJ lambdaJI x) u := by
  rw [(paper_lemma7_canonical_derivative_numerator_hasDerivAt
    c1 c2 lambdaIJ lambdaJI u (ne_of_gt hsum)).deriv]
  positivity

/-- Remark 2 structured-price derivative-sign expression. -/
def gn21StructuredDerivativeSignKernel
    (q u m z switchIJ Qi Qj Ti Tj Rj : ℝ) : ℝ :=
  q * ((Rj - m) * Tj * Ti + m * Tj + z * Qj * Ti + z * Tj * switchIJ) +
    u * (Qi * Tj * (m - Rj) + Qj * (m - z * Qi + z * switchIJ))

/-- Coefficient of the CTMC switch probability in the structured derivative kernel. -/
def gn21StructuredDerivativeSwitchBracket
    (m z switchIJ Qi Qj Ti Tj Rj : ℝ) : ℝ :=
  (Rj - m) * Tj * Ti + m * Tj + z * Qj * Ti + z * Tj * switchIJ

/-- The non-switch-probability term in the structured derivative kernel. -/
def gn21StructuredDerivativeStaticTerm
    (m z switchIJ Qi Qj Tj Rj : ℝ) : ℝ :=
  Qi * Tj * (m - Rj) + Qj * (m - z * Qi + z * switchIJ)

/-- Structured derivative kernel split into its switch-probability and static terms. -/
theorem gn21StructuredDerivativeSignKernel_eq_bracket_static
    (q u m z switchIJ Qi Qj Ti Tj Rj : ℝ) :
    gn21StructuredDerivativeSignKernel q u m z switchIJ Qi Qj Ti Tj Rj =
      q * gn21StructuredDerivativeSwitchBracket m z switchIJ Qi Qj Ti Tj Rj +
        u * gn21StructuredDerivativeStaticTerm m z switchIJ Qi Qj Tj Rj := by
  rfl

/--
Algebraic positivity bridge for kernels of the form `q * bracket + u * tail`.
If `q` is below the linearization `lambda * u`, the bracket is nonpositive,
and the linearized endpoint `lambda * bracket + tail` is positive, then the
finite-`u` kernel is positive.
-/
theorem structuredDerivativeKernel_pos_of_linearization_bound
    (q u lambda bracket tail : ℝ)
    (hu : 0 < u)
    (hbound : q < lambda * u)
    (hbracket_nonpos : bracket ≤ 0)
    (hlinear_pos : 0 < lambda * bracket + tail) :
    0 < q * bracket + u * tail := by
  have hmul :
      lambda * u * bracket ≤ q * bracket := by
    exact mul_le_mul_of_nonpos_right (le_of_lt hbound) hbracket_nonpos
  have hscaled_pos : 0 < u * (lambda * bracket + tail) :=
    mul_pos hu hlinear_pos
  have hscaled_eq :
      u * (lambda * bracket + tail) = lambda * u * bracket + u * tail := by
    ring
  have hle :
      u * (lambda * bracket + tail) ≤ q * bracket + u * tail := by
    rw [hscaled_eq]
    have hle0 := add_le_add_right hmul (u * tail)
    simpa [add_comm, add_left_comm, add_assoc] using hle0
  exact lt_of_lt_of_le hscaled_pos hle

/--
Structured derivative positivity from a CTMC switch-probability linearization
bound.  This is the reusable inequality shape behind the final Lemma 9/10
endpoint derivative arguments.
-/
theorem paper_remark2_structured_derivative_kernel_pos_of_linearization_bound
    (q u m z switchIJ Qi Qj Ti Tj Rj : ℝ)
    (hu : 0 < u)
    (hbound : q < switchIJ * u)
    (hbracket_nonpos :
      gn21StructuredDerivativeSwitchBracket m z switchIJ Qi Qj Ti Tj Rj ≤ 0)
    (hlinear_pos :
      0 < switchIJ *
          gn21StructuredDerivativeSwitchBracket m z switchIJ Qi Qj Ti Tj Rj +
        gn21StructuredDerivativeStaticTerm m z switchIJ Qi Qj Tj Rj) :
    0 < gn21StructuredDerivativeSignKernel q u m z switchIJ Qi Qj Ti Tj Rj := by
  rw [gn21StructuredDerivativeSignKernel_eq_bracket_static]
  exact structuredDerivativeKernel_pos_of_linearization_bound
    q u switchIJ
    (gn21StructuredDerivativeSwitchBracket m z switchIJ Qi Qj Ti Tj Rj)
    (gn21StructuredDerivativeStaticTerm m z switchIJ Qi Qj Tj Rj)
    hu hbound hbracket_nonpos hlinear_pos

/--
CTMC-specialized structured derivative positivity: replace the abstract
linearization bound with Remark 4's strict `q(u) < lambda * u` fact.
-/
theorem paper_remark2_structured_derivative_kernel_pos_of_ctmc_switch
    (u m z switchIJ switchJI Qi Qj Ti Tj Rj : ℝ)
    (hswitchIJ : 0 < switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hu : 0 < u)
    (hbracket_nonpos :
      gn21StructuredDerivativeSwitchBracket m z switchIJ Qi Qj Ti Tj Rj ≤ 0)
    (hlinear_pos :
      0 < switchIJ *
          gn21StructuredDerivativeSwitchBracket m z switchIJ Qi Qj Ti Tj Rj +
        gn21StructuredDerivativeStaticTerm m z switchIJ Qi Qj Tj Rj) :
    0 < gn21StructuredDerivativeSignKernel
      (gn21SwitchProb switchIJ switchJI u) u m z switchIJ Qi Qj Ti Tj Rj := by
  exact paper_remark2_structured_derivative_kernel_pos_of_linearization_bound
    (gn21SwitchProb switchIJ switchJI u) u m z switchIJ Qi Qj Ti Tj Rj
    hu
    (paper_remark4_switch_probability_lt_rate_mul_time
      switchIJ switchJI u hswitchIJ hsum hu)
    hbracket_nonpos hlinear_pos

/--
Sign-splitting positivity bridge for kernels of the form `q * bracket + u *
tail`. If the bracket is nonpositive, the CTMC linearization bound controls
the negative part; if it is positive, nonnegativity of `q` and positivity of
the tail are enough.
-/
theorem structuredDerivativeKernel_pos_of_linearization_bound_and_tail
    (q u lambda bracket tail : ℝ)
    (hu : 0 < u)
    (hq_nonneg : 0 ≤ q)
    (hbound : q < lambda * u)
    (htail_pos : 0 < tail)
    (hlinear_pos : 0 < lambda * bracket + tail) :
    0 < q * bracket + u * tail := by
  by_cases hbracket_nonpos : bracket ≤ 0
  · exact structuredDerivativeKernel_pos_of_linearization_bound
      q u lambda bracket tail hu hbound hbracket_nonpos hlinear_pos
  · have hbracket_pos : 0 < bracket := lt_of_not_ge hbracket_nonpos
    have hqbracket_nonneg : 0 ≤ q * bracket :=
      mul_nonneg hq_nonneg (le_of_lt hbracket_pos)
    have hutail_pos : 0 < u * tail := mul_pos hu htail_pos
    exact add_pos_of_nonneg_of_pos hqbracket_nonneg hutail_pos

/--
Structured derivative positivity from a CTMC switch probability, without
requiring a prior sign choice for the switch-probability bracket.
-/
theorem paper_remark2_structured_derivative_kernel_pos_of_ctmc_switch_and_tail
    (u m z switchIJ switchJI Qi Qj Ti Tj Rj : ℝ)
    (hswitchIJ : 0 < switchIJ)
    (hsum : 0 < switchIJ + switchJI)
    (hu : 0 < u)
    (htail_pos :
      0 < gn21StructuredDerivativeStaticTerm m z switchIJ Qi Qj Tj Rj)
    (hlinear_pos :
      0 < switchIJ *
          gn21StructuredDerivativeSwitchBracket m z switchIJ Qi Qj Ti Tj Rj +
        gn21StructuredDerivativeStaticTerm m z switchIJ Qi Qj Tj Rj) :
    0 < gn21StructuredDerivativeSignKernel
      (gn21SwitchProb switchIJ switchJI u) u m z switchIJ Qi Qj Ti Tj Rj := by
  rw [gn21StructuredDerivativeSignKernel_eq_bracket_static]
  exact structuredDerivativeKernel_pos_of_linearization_bound_and_tail
    (gn21SwitchProb switchIJ switchJI u) u switchIJ
    (gn21StructuredDerivativeSwitchBracket m z switchIJ Qi Qj Ti Tj Rj)
    (gn21StructuredDerivativeStaticTerm m z switchIJ Qi Qj Tj Rj)
    hu
    (paper_lemma2_switch_probability_nonneg switchIJ switchJI u
      (le_of_lt hswitchIJ) hsum (le_of_lt hu))
    (paper_remark4_switch_probability_lt_rate_mul_time
      switchIJ switchJI u hswitchIJ hsum hu)
    htail_pos hlinear_pos

/--
Remark 2 algebra: substituting `w_i(u)=mu+zq_i(u)` and
`W_i=m(T_i-1)+z(Q_i-λ_{i→j})` into Lemma 6 gives the displayed structured
derivative-sign expression.
-/
theorem paper_remark2_structured_derivative_kernel_algebra
    (q u m z switchIJ Qi Qj Ti Tj Rj : ℝ) :
    gn21DerivativeSignKernel q u (m * u + z * q) Qi Qj Ti Tj
        (m * (Ti - 1) + z * (Qi - switchIJ)) (Rj * Tj) =
      gn21StructuredDerivativeSignKernel q u m z switchIJ Qi Qj Ti Tj Rj := by
  unfold gn21DerivativeSignKernel gn21StructuredDerivativeSignKernel
  ring

/-- Two real quantities have the same strict sign. -/
def sameStrictSign (x y : ℝ) : Prop :=
  (0 < x ↔ 0 < y) ∧ (x < 0 ↔ y < 0)

/-- Same strict sign is reflexive. -/
theorem sameStrictSign_refl (x : ℝ) : sameStrictSign x x := by
  constructor <;> rfl

/-- Same strict sign is symmetric. -/
theorem sameStrictSign_symm {x y : ℝ}
    (h : sameStrictSign x y) : sameStrictSign y x := by
  exact ⟨h.1.symm, h.2.symm⟩

/-- Positive strict-sign equivalence. -/
theorem sameStrictSign_pos_iff {x y : ℝ}
    (h : sameStrictSign x y) :
    (0 < x ↔ 0 < y) :=
  h.1

/-- Negative strict-sign equivalence. -/
theorem sameStrictSign_neg_iff {x y : ℝ}
    (h : sameStrictSign x y) :
    (x < 0 ↔ y < 0) :=
  h.2

/-- Transport positivity from the left side of a strict-sign equivalence. -/
theorem sameStrictSign_pos_right {x y : ℝ}
    (h : sameStrictSign x y) (hx : 0 < x) :
    0 < y :=
  h.1.mp hx

/-- Transport positivity from the right side of a strict-sign equivalence. -/
theorem sameStrictSign_pos_left {x y : ℝ}
    (h : sameStrictSign x y) (hy : 0 < y) :
    0 < x :=
  h.1.mpr hy

/-- Transport negativity from the left side of a strict-sign equivalence. -/
theorem sameStrictSign_neg_right {x y : ℝ}
    (h : sameStrictSign x y) (hx : x < 0) :
    y < 0 :=
  h.2.mp hx

/-- Transport negativity from the right side of a strict-sign equivalence. -/
theorem sameStrictSign_neg_left {x y : ℝ}
    (h : sameStrictSign x y) (hy : y < 0) :
    x < 0 :=
  h.2.mpr hy

/-- Same strict sign is transitive. -/
theorem sameStrictSign_trans {x y z : ℝ}
    (hxy : sameStrictSign x y) (hyz : sameStrictSign y z) :
    sameStrictSign x z := by
  exact ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

/-- Multiplication by a positive scalar preserves strict sign. -/
theorem sameStrictSign_of_pos_mul_left
    (c x : ℝ) (hc : 0 < c) :
    sameStrictSign (c * x) x := by
  constructor
  · constructor
    · intro hcx_pos
      by_contra hx_nonpos
      have hcx_nonpos : c * x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) (le_of_not_gt hx_nonpos)
      linarith
    · intro hx_pos
      exact mul_pos hc hx_pos
  · constructor
    · intro hcx_neg
      by_contra hx_nonneg
      have hcx_nonneg : 0 ≤ c * x :=
        mul_nonneg (le_of_lt hc) (le_of_not_gt hx_nonneg)
      linarith
    · intro hx_neg
      exact mul_neg_of_pos_of_neg hc hx_neg

/-- A nonempty open interval with positive upper endpoint contains a positive point. -/
theorem exists_pos_between_of_lt_of_pos
    (a b : ℝ) (hab : a < b) (hb : 0 < b) :
    ∃ x : ℝ, 0 < x ∧ a < x ∧ x < b := by
  let x := (max a 0 + b) / 2
  have hmax_lt : max a 0 < b := max_lt hab hb
  refine ⟨x, ?_, ?_, ?_⟩
  · have hnonneg : 0 ≤ max a 0 := le_max_right a 0
    have hsum_pos : 0 < max a 0 + b := add_pos_of_nonneg_of_pos hnonneg hb
    positivity
  · have ha_le_max : a ≤ max a 0 := le_max_left a 0
    have hmax_lt_x : max a 0 < x := by
      unfold x
      linarith
    exact lt_of_le_of_lt ha_le_max hmax_lt_x
  · unfold x
    linarith

/--
Lemma 6 sign-transfer bridge: after substituting state reward rates
`W_k=R_kT_k`, the derivative-sign kernel has the same strict sign as the
normalized response whenever the positive-time scaling factor `u*T_i*T_j` is
positive.
-/
theorem paper_lemma6_derivative_kernel_same_sign_response
    (q u wi Qi Qj Ti Tj Ri Rj : ℝ)
    (hu : 0 < u) (hTi_pos : 0 < Ti) (hTj_pos : 0 < Tj) :
    sameStrictSign
      (gn21DerivativeSignKernel q u wi Qi Qj Ti Tj (Ri * Ti) (Rj * Tj))
      (gn21Lemma6Response q u wi Qi Qj Ti Tj Ri Rj) := by
  rw [paper_lemma6_derivative_kernel_state_rate_algebra]
  rw [paper_lemma6_derivative_kernel_eq_scaled_response q u wi Qi Qj Ti Tj Ri Rj
    (ne_of_gt hu) (ne_of_gt hTi_pos) (ne_of_gt hTj_pos)]
  have hscale : 0 < u * Ti * Tj := by positivity
  simpa [mul_assoc] using
    sameStrictSign_of_pos_mul_left
      (u * Ti * Tj) (gn21Lemma6Response q u wi Qi Qj Ti Tj Ri Rj) hscale

/--
Lemma 6 source-facing endpoint: the analytic derivative has the same sign as
the algebraic derivative kernel.  The hard input is the endpoint-derivative
certificate for the set-valued reward functional.
-/
structure Lemma6DerivativeFormulaCertificate where
  derivativeValue : ℝ
  q : ℝ
  u : ℝ
  wi : ℝ
  Qi : ℝ
  Qj : ℝ
  Ti : ℝ
  Tj : ℝ
  Wi : ℝ
  Wj : ℝ
  same_sign :
    sameStrictSign derivativeValue
      (gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj)

/--
Lean-native endpoint derivative data behind Lemma 6.  The continuous
measure-theoretic work is now isolated to:

* a one-dimensional endpoint path `rewardAlongEndpoint`;
* a `HasDerivAt` proof at the endpoint `u`;
* a positive-scale equality between that derivative and Lemma 6's algebraic
  kernel.
-/
structure Lemma6EndpointDerivativeData where
  rewardAlongEndpoint : ℝ → ℝ
  derivativeValue : ℝ
  q : ℝ
  u : ℝ
  wi : ℝ
  Qi : ℝ
  Qj : ℝ
  Ti : ℝ
  Tj : ℝ
  Wi : ℝ
  Wj : ℝ
  scale : ℝ
  scale_pos : 0 < scale
  has_derivative : HasDerivAt rewardAlongEndpoint derivativeValue u
  derivative_eq_scaled_kernel :
    derivativeValue =
      scale * gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj

/--
Endpoint derivative data produce the Lemma 6 strict-sign certificate whenever
the derivative is a positive scalar multiple of the algebraic kernel.
-/
def lemma6DerivativeFormulaCertificate_of_endpoint_data
    (D : Lemma6EndpointDerivativeData) :
    Lemma6DerivativeFormulaCertificate where
  derivativeValue := D.derivativeValue
  q := D.q
  u := D.u
  wi := D.wi
  Qi := D.Qi
  Qj := D.Qj
  Ti := D.Ti
  Tj := D.Tj
  Wi := D.Wi
  Wj := D.Wj
  same_sign := by
    rw [D.derivative_eq_scaled_kernel]
    exact sameStrictSign_of_pos_mul_left D.scale
      (gn21DerivativeSignKernel D.q D.u D.wi D.Qi D.Qj D.Ti D.Tj D.Wi D.Wj)
      D.scale_pos

/-- Lemma 6 endpoint data include the promised analytic derivative statement. -/
theorem paper_lemma6_endpoint_hasDerivAt_of_data
    (D : Lemma6EndpointDerivativeData) :
    HasDerivAt D.rewardAlongEndpoint D.derivativeValue D.u :=
  D.has_derivative

/--
Local calculus bridge for endpoint-improvement arguments: a positive derivative
at an endpoint gives a positive right move with strictly larger reward.
-/
theorem exists_pos_right_improvement_of_hasDerivAt_pos
    {f : ℝ → ℝ} {x derivativeValue : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hpos : 0 < derivativeValue) :
    ∃ ε : ℝ, 0 < ε ∧ f x < f (x + ε) := by
  have hslope_pos :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        0 < ε⁻¹ * (f (x + ε) - f x) := by
    simpa using
      hderiv.tendsto_slope_zero_right.eventually (Ioi_mem_nhds hpos)
  have hε_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  rcases (hε_pos.and hslope_pos).exists with ⟨ε, hε, hslope⟩
  have hdiff_pos : 0 < f (x + ε) - f x := by
    rw [mul_comm] at hslope
    exact pos_of_mul_pos_left hslope (le_of_lt (inv_pos.mpr hε))
  exact ⟨ε, hε, by linarith⟩

/--
Bounded version of the one-sided improvement step.  This is useful for moving
a finite interval endpoint while preserving the interval order.
-/
theorem exists_pos_right_improvement_of_hasDerivAt_pos_lt
    {f : ℝ → ℝ} {x derivativeValue δ : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hpos : 0 < derivativeValue)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ f x < f (x + ε) := by
  have hslope_pos :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        0 < ε⁻¹ * (f (x + ε) - f x) := by
    simpa using
      hderiv.tendsto_slope_zero_right.eventually (Ioi_mem_nhds hpos)
  have hε_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  have hε_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < δ := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds hδ)
  rcases (hε_pos.and (hε_lt.and hslope_pos)).exists with
    ⟨ε, hε, hε_lt, hslope⟩
  have hdiff_pos : 0 < f (x + ε) - f x := by
    rw [mul_comm] at hslope
    exact pos_of_mul_pos_left hslope (le_of_lt (inv_pos.mpr hε))
  exact ⟨ε, hε, hε_lt, by linarith⟩

/--
Local calculus bridge for endpoint-improvement arguments: a negative derivative
at an endpoint gives a positive right move with strictly smaller reward.
-/
theorem exists_pos_right_decrease_of_hasDerivAt_neg
    {f : ℝ → ℝ} {x derivativeValue : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hneg : derivativeValue < 0) :
    ∃ ε : ℝ, 0 < ε ∧ f (x + ε) < f x := by
  have hpos : 0 < -derivativeValue := by linarith
  rcases exists_pos_right_improvement_of_hasDerivAt_pos
      (f := fun y => -f y) (x := x) (derivativeValue := -derivativeValue)
      hderiv.neg hpos with
    ⟨ε, hε_pos, hlt⟩
  exact ⟨ε, hε_pos, by linarith⟩

/--
Bounded version of the one-sided decrease step.
-/
theorem exists_pos_right_decrease_of_hasDerivAt_neg_lt
    {f : ℝ → ℝ} {x derivativeValue δ : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hneg : derivativeValue < 0)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ f (x + ε) < f x := by
  have hpos : 0 < -derivativeValue := by linarith
  rcases exists_pos_right_improvement_of_hasDerivAt_pos_lt
      (f := fun y => -f y) (x := x) (derivativeValue := -derivativeValue)
      hderiv.neg hpos hδ with
    ⟨ε, hε_pos, hε_lt, hlt⟩
  exact ⟨ε, hε_pos, hε_lt, by linarith⟩

/--
Left-move improvement step: with a negative derivative, moving a small positive
distance to the left strictly improves the function value.
-/
theorem exists_pos_left_improvement_of_hasDerivAt_neg
    {f : ℝ → ℝ} {x derivativeValue : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hneg : derivativeValue < 0) :
    ∃ ε : ℝ, 0 < ε ∧ f x < f (x - ε) := by
  have hslope_neg :
      ∀ᶠ t in 𝓝[<] (0 : ℝ),
        t⁻¹ * (f (x + t) - f x) < 0 := by
    simpa using
      hderiv.tendsto_slope_zero_left.eventually (Iio_mem_nhds hneg)
  have ht_neg : ∀ᶠ t in 𝓝[<] (0 : ℝ), t < 0 :=
    self_mem_nhdsWithin
  rcases (ht_neg.and hslope_neg).exists with ⟨t, ht, hslope⟩
  have hε_pos : 0 < -t := by linarith
  have hdiff_pos : 0 < f (x + t) - f x := by
    rw [mul_comm] at hslope
    exact pos_of_mul_neg_left hslope (inv_nonpos.mpr (le_of_lt ht))
  exact ⟨-t, hε_pos, by simpa [sub_eq_add_neg] using hdiff_pos⟩

/-- Bounded left-move improvement step. -/
theorem exists_pos_left_improvement_of_hasDerivAt_neg_lt
    {f : ℝ → ℝ} {x derivativeValue δ : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hneg : derivativeValue < 0)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ f x < f (x - ε) := by
  have hslope_neg :
      ∀ᶠ t in 𝓝[<] (0 : ℝ),
        t⁻¹ * (f (x + t) - f x) < 0 := by
    simpa using
      hderiv.tendsto_slope_zero_left.eventually (Iio_mem_nhds hneg)
  have ht_neg : ∀ᶠ t in 𝓝[<] (0 : ℝ), t < 0 :=
    self_mem_nhdsWithin
  have ht_gt : ∀ᶠ t in 𝓝[<] (0 : ℝ), -δ < t := by
    exact nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith))
  rcases (ht_neg.and (ht_gt.and hslope_neg)).exists with
    ⟨t, ht, ht_gt, hslope⟩
  have hε_pos : 0 < -t := by linarith
  have hε_lt : -t < δ := by linarith
  have hdiff_pos : 0 < f (x + t) - f x := by
    rw [mul_comm] at hslope
    exact pos_of_mul_neg_left hslope (inv_nonpos.mpr (le_of_lt ht))
  exact ⟨-t, hε_pos, hε_lt, by simpa [sub_eq_add_neg] using hdiff_pos⟩

/--
Left-move decrease step: with a positive derivative, moving a small positive
distance to the left strictly decreases the function value.
-/
theorem exists_pos_left_decrease_of_hasDerivAt_pos
    {f : ℝ → ℝ} {x derivativeValue : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hpos : 0 < derivativeValue) :
    ∃ ε : ℝ, 0 < ε ∧ f (x - ε) < f x := by
  have hneg : -derivativeValue < 0 := by linarith
  rcases exists_pos_left_improvement_of_hasDerivAt_neg
      (f := fun y => -f y) (x := x) (derivativeValue := -derivativeValue)
      hderiv.neg hneg with
    ⟨ε, hε_pos, hlt⟩
  exact ⟨ε, hε_pos, by linarith⟩

/-- Bounded left-move decrease step. -/
theorem exists_pos_left_decrease_of_hasDerivAt_pos_lt
    {f : ℝ → ℝ} {x derivativeValue δ : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hpos : 0 < derivativeValue)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ f (x - ε) < f x := by
  have hneg : -derivativeValue < 0 := by linarith
  rcases exists_pos_left_improvement_of_hasDerivAt_neg_lt
      (f := fun y => -f y) (x := x) (derivativeValue := -derivativeValue)
      hderiv.neg hneg hδ with
    ⟨ε, hε_pos, hε_lt, hlt⟩
  exact ⟨ε, hε_pos, hε_lt, by linarith⟩

/--
Concrete Lemma 6 endpoint-data constructor from the aggregate quotient
calculus.  The remaining measure-theoretic source obligations are exactly the
three endpoint path derivatives for `Q_i`, `W_i`, and `T_i`.
-/
def lemma6EndpointDerivativeData_of_aggregate_paths
    (QiPath WiPath TiPath : ℝ → ℝ)
    (q u wi Qi Qj Ti Tj Wi Wj endpointScale : ℝ)
    (hendpointScale_pos : 0 < endpointScale)
    (hQj_pos : 0 < Qj)
    (hQi_deriv : HasDerivAt QiPath (endpointScale * q) u)
    (hWi_deriv : HasDerivAt WiPath (endpointScale * wi) u)
    (hTi_deriv : HasDerivAt TiPath (endpointScale * u) u)
    (hQi_val : QiPath u = Qi)
    (hWi_val : WiPath u = Wi)
    (hTi_val : TiPath u = Ti)
    (hden : Qi * Tj + Qj * Ti ≠ 0) :
    Lemma6EndpointDerivativeData where
  rewardAlongEndpoint := fun x =>
    gn21AggregateDynamicReward (QiPath x) Qj (TiPath x) Tj (WiPath x) Wj
  derivativeValue :=
    endpointScale * Qj *
      gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj /
        (Qi * Tj + Qj * Ti) ^ 2
  q := q
  u := u
  wi := wi
  Qi := Qi
  Qj := Qj
  Ti := Ti
  Tj := Tj
  Wi := Wi
  Wj := Wj
  scale := endpointScale * Qj / (Qi * Tj + Qj * Ti) ^ 2
  scale_pos := by
    exact div_pos (mul_pos hendpointScale_pos hQj_pos)
      (sq_pos_of_ne_zero hden)
  has_derivative := by
    exact paper_lemma6_aggregate_reward_hasDerivAt
      QiPath WiPath TiPath q u wi Qi Qj Ti Tj Wi Wj endpointScale
      hQi_deriv hWi_deriv hTi_deriv hQi_val hWi_val hTi_val hden
  derivative_eq_scaled_kernel := by
    field_simp [hden]

/--
Aggregate-path form of Lemma 6: once the endpoint derivatives of `Q_i`,
`W_i`, and `T_i` are known, the derivative of the aggregate reward quotient
has the same strict sign as the Lemma 6 kernel.
-/
theorem paper_lemma6_derivative_formula_of_aggregate_paths
    (QiPath WiPath TiPath : ℝ → ℝ)
    (q u wi Qi Qj Ti Tj Wi Wj endpointScale : ℝ)
    (hendpointScale_pos : 0 < endpointScale)
    (hQj_pos : 0 < Qj)
    (hQi_deriv : HasDerivAt QiPath (endpointScale * q) u)
    (hWi_deriv : HasDerivAt WiPath (endpointScale * wi) u)
    (hTi_deriv : HasDerivAt TiPath (endpointScale * u) u)
    (hQi_val : QiPath u = Qi)
    (hWi_val : WiPath u = Wi)
    (hTi_val : TiPath u = Ti)
    (hden : Qi * Tj + Qj * Ti ≠ 0) :
    sameStrictSign
      (endpointScale * Qj *
        gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj /
          (Qi * Tj + Qj * Ti) ^ 2)
      (gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj) := by
  let D :=
    lemma6EndpointDerivativeData_of_aggregate_paths
      QiPath WiPath TiPath q u wi Qi Qj Ti Tj Wi Wj endpointScale
      hendpointScale_pos hQj_pos hQi_deriv hWi_deriv hTi_deriv
      hQi_val hWi_val hTi_val hden
  exact (lemma6DerivativeFormulaCertificate_of_endpoint_data D).same_sign

/--
Lower-endpoint aggregate derivative.  Moving a lower endpoint inward negates
the primitive endpoint derivatives, so the reward derivative is the negative
of the corresponding upper-endpoint derivative.
-/
theorem paper_lemma6_lower_aggregate_reward_hasDerivAt
    (QiPath WiPath TiPath : ℝ → ℝ)
    (q u wi Qi Qj Ti Tj Wi Wj endpointScale : ℝ)
    (hQi_deriv : HasDerivAt QiPath ((-endpointScale) * q) u)
    (hWi_deriv : HasDerivAt WiPath ((-endpointScale) * wi) u)
    (hTi_deriv : HasDerivAt TiPath ((-endpointScale) * u) u)
    (hQi_val : QiPath u = Qi)
    (hWi_val : WiPath u = Wi)
    (hTi_val : TiPath u = Ti)
    (hden : Qi * Tj + Qj * Ti ≠ 0) :
    HasDerivAt
      (fun x =>
        gn21AggregateDynamicReward (QiPath x) Qj (TiPath x) Tj
          (WiPath x) Wj)
      (-(endpointScale * Qj *
        gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj /
          (Qi * Tj + Qj * Ti) ^ 2)) u := by
  have h :=
    paper_lemma6_aggregate_reward_hasDerivAt
      QiPath WiPath TiPath q u wi Qi Qj Ti Tj Wi Wj (-endpointScale)
      hQi_deriv hWi_deriv hTi_deriv hQi_val hWi_val hTi_val hden
  convert h using 1
  ring

/--
Lower-endpoint aggregate sign bridge: the lower-endpoint derivative has the
same strict sign as the negative Lemma 6 kernel.
-/
theorem paper_lemma6_lower_derivative_formula_of_aggregate_paths
    (q u wi Qi Qj Ti Tj Wi Wj endpointScale : ℝ)
    (hendpointScale_pos : 0 < endpointScale)
    (hQj_pos : 0 < Qj)
    (hden : Qi * Tj + Qj * Ti ≠ 0) :
    sameStrictSign
      (-(endpointScale * Qj *
        gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj /
          (Qi * Tj + Qj * Ti) ^ 2))
      (-(gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj)) := by
  have hscale : 0 < endpointScale * Qj / (Qi * Tj + Qj * Ti) ^ 2 :=
    div_pos (mul_pos hendpointScale_pos hQj_pos)
      (sq_pos_of_ne_zero hden)
  convert
    sameStrictSign_of_pos_mul_left
      (endpointScale * Qj / (Qi * Tj + Qj * Ti) ^ 2)
      (-(gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj))
      hscale using 1
  field_simp [hden]

/--
Density/interval specialization of the Lemma 6 endpoint bridge.  This matches
the source assumptions where the distribution has density `f_i`, and an upper
endpoint `u` moves in an interval with fixed lower endpoint.
-/
def lemma6EndpointDerivativeData_of_interval_density_paths
    (arrivalRate switchRate lowerEndpoint u Qj Tj Wj : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
          switchProb u * Tj +
        Qj *
          gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        lowerEndpoint u)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        lowerEndpoint u)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume lowerEndpoint u)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u) :
    Lemma6EndpointDerivativeData :=
  lemma6EndpointDerivativeData_of_aggregate_paths
    (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb)
    (gn21EndpointWiPath arrivalRate lowerEndpoint density payment)
    (gn21EndpointTiPath arrivalRate lowerEndpoint density)
    (switchProb u) u (payment u)
    (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
      switchProb u)
    Qj
    (gn21EndpointTiPath arrivalRate lowerEndpoint density u)
    Tj
    (gn21EndpointWiPath arrivalRate lowerEndpoint density payment u)
    Wj
    (arrivalRate * density u)
    (mul_pos harrival_pos hdensity_pos)
    hQj_pos
    (by
      convert gn21EndpointQiPath_hasDerivAt
        arrivalRate switchRate lowerEndpoint u density switchProb
        hq_int hq_meas hq_cont using 1
      ring)
    (by
      convert gn21EndpointWiPath_hasDerivAt
        arrivalRate lowerEndpoint u density payment
        hw_int hw_meas hw_cont using 1
      ring)
    (by
      convert gn21EndpointTiPath_hasDerivAt
        arrivalRate lowerEndpoint u density
        ht_int ht_meas ht_cont using 1
      ring)
    rfl rfl rfl hden

/--
Interval-density form of Lemma 6: under the source density assumptions for a
moving upper endpoint, the aggregate reward derivative has the same strict sign
as the displayed Lemma 6 kernel.
-/
theorem paper_lemma6_derivative_formula_of_interval_density_paths
    (arrivalRate switchRate lowerEndpoint u Qj Tj Wj : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
          switchProb u * Tj +
        Qj *
          gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        lowerEndpoint u)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        lowerEndpoint u)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume lowerEndpoint u)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u) :
    sameStrictSign
      ((arrivalRate * density u) * Qj *
        gn21DerivativeSignKernel (switchProb u) u (payment u)
          (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
            switchProb u)
          Qj
          (gn21EndpointTiPath arrivalRate lowerEndpoint density u)
          Tj
          (gn21EndpointWiPath arrivalRate lowerEndpoint density payment u)
          Wj /
          (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
              switchProb u * Tj +
            Qj *
              gn21EndpointTiPath arrivalRate lowerEndpoint density u) ^ 2)
      (gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
          switchProb u)
        Qj
        (gn21EndpointTiPath arrivalRate lowerEndpoint density u)
        Tj
        (gn21EndpointWiPath arrivalRate lowerEndpoint density payment u)
        Wj) := by
  let D :=
    lemma6EndpointDerivativeData_of_interval_density_paths
      arrivalRate switchRate lowerEndpoint u Qj Tj Wj density switchProb
      payment harrival_pos hdensity_pos hQj_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont
  exact (lemma6DerivativeFormulaCertificate_of_endpoint_data D).same_sign

/--
Interval-density lower-endpoint form of Lemma 6.  Under the source density
assumptions for a moving lower endpoint, the aggregate reward derivative has
the same strict sign as the negative displayed Lemma 6 kernel.
-/
theorem paper_lemma6_lower_derivative_formula_of_interval_density_paths
    (arrivalRate switchRate upperEndpoint u Qj Tj Wj : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
          switchProb u * Tj +
        Qj *
          gn21LowerEndpointTiPath arrivalRate upperEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        u upperEndpoint)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        u upperEndpoint)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume u upperEndpoint)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u) :
    HasDerivAt
      (fun x =>
        gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb x)
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density x)
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment x)
          Wj)
      (-((arrivalRate * density u) * Qj *
        gn21DerivativeSignKernel (switchProb u) u (payment u)
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb u)
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
          Wj /
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
              switchProb u * Tj +
            Qj *
              gn21LowerEndpointTiPath arrivalRate upperEndpoint density u) ^ 2)) u ∧
    sameStrictSign
      (-((arrivalRate * density u) * Qj *
        gn21DerivativeSignKernel (switchProb u) u (payment u)
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb u)
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
          Wj /
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
              switchProb u * Tj +
            Qj *
              gn21LowerEndpointTiPath arrivalRate upperEndpoint density u) ^ 2))
      (-(gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
          switchProb u)
        Qj
        (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
        Tj
        (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
        Wj)) := by
  constructor
  · apply paper_lemma6_lower_aggregate_reward_hasDerivAt
    · convert gn21LowerEndpointQiPath_hasDerivAt
        arrivalRate switchRate upperEndpoint u density switchProb
        hq_int hq_meas hq_cont using 1
      ring
    · convert gn21LowerEndpointWiPath_hasDerivAt
        arrivalRate upperEndpoint u density payment
        hw_int hw_meas hw_cont using 1
      ring
    · convert gn21LowerEndpointTiPath_hasDerivAt
        arrivalRate upperEndpoint u density
        ht_int ht_meas ht_cont using 1
      ring
    · rfl
    · rfl
    · rfl
    · exact hden
  · exact paper_lemma6_lower_derivative_formula_of_aggregate_paths
      (switchProb u) u (payment u)
      (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
        switchProb u)
      Qj
      (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
      Tj
      (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
      Wj
      (arrivalRate * density u)
      (mul_pos harrival_pos hdensity_pos)
      hQj_pos hden

/--
Tail-density lower-endpoint form of Lemma 6.  This is the unbounded analogue
of the finite lower-endpoint interval formula: moving the lower endpoint of
`(u,∞)` inward negates the primitive endpoint derivatives, so the aggregate
derivative has the same strict sign as the negative Lemma 6 kernel.
-/
theorem paper_lemma6_tail_derivative_formula_of_interval_density_paths
    (arrivalRate switchRate u Qj Tj Wj : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21TailQiPath arrivalRate switchRate density switchProb u * Tj +
        Qj * gn21TailTiPath arrivalRate density u ≠ 0)
    (hq_int :
      IntegrableOn (fun τ => switchProb τ * density τ) (Set.Ioi (u - 1))
        volume)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntegrableOn (fun τ => payment τ * density τ) (Set.Ioi (u - 1))
        volume)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntegrableOn (fun τ => τ * density τ) (Set.Ioi (u - 1)) volume)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u) :
    HasDerivAt
      (fun x =>
        gn21AggregateDynamicReward
          (gn21TailQiPath arrivalRate switchRate density switchProb x)
          Qj
          (gn21TailTiPath arrivalRate density x)
          Tj
          (gn21TailWiPath arrivalRate density payment x)
          Wj)
      (-((arrivalRate * density u) * Qj *
        gn21DerivativeSignKernel (switchProb u) u (payment u)
          (gn21TailQiPath arrivalRate switchRate density switchProb u)
          Qj
          (gn21TailTiPath arrivalRate density u)
          Tj
          (gn21TailWiPath arrivalRate density payment u)
          Wj /
          (gn21TailQiPath arrivalRate switchRate density switchProb u * Tj +
            Qj * gn21TailTiPath arrivalRate density u) ^ 2)) u ∧
    sameStrictSign
      (-((arrivalRate * density u) * Qj *
        gn21DerivativeSignKernel (switchProb u) u (payment u)
          (gn21TailQiPath arrivalRate switchRate density switchProb u)
          Qj
          (gn21TailTiPath arrivalRate density u)
          Tj
          (gn21TailWiPath arrivalRate density payment u)
          Wj /
          (gn21TailQiPath arrivalRate switchRate density switchProb u * Tj +
            Qj * gn21TailTiPath arrivalRate density u) ^ 2))
      (-(gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21TailQiPath arrivalRate switchRate density switchProb u)
        Qj
        (gn21TailTiPath arrivalRate density u)
        Tj
        (gn21TailWiPath arrivalRate density payment u)
        Wj)) := by
  constructor
  · apply paper_lemma6_lower_aggregate_reward_hasDerivAt
    · convert gn21TailQiPath_hasDerivAt
        arrivalRate switchRate u density switchProb hq_int hq_meas hq_cont
        using 1
      ring
    · convert gn21TailWiPath_hasDerivAt
        arrivalRate u density payment hw_int hw_meas hw_cont using 1
      ring
    · convert gn21TailTiPath_hasDerivAt
        arrivalRate u density ht_int ht_meas ht_cont using 1
      ring
    · rfl
    · rfl
    · rfl
    · exact hden
  · exact paper_lemma6_lower_derivative_formula_of_aggregate_paths
      (switchProb u) u (payment u)
      (gn21TailQiPath arrivalRate switchRate density switchProb u)
      Qj
      (gn21TailTiPath arrivalRate density u)
      Tj
      (gn21TailWiPath arrivalRate density payment u)
      Wj
      (arrivalRate * density u)
      (mul_pos harrival_pos hdensity_pos)
      hQj_pos hden

/--
Middle-rejection lower-cutoff form of Lemma 6.  Moving `lo` right expands the
accepted short-trip interval, so the derivative has the upper-endpoint sign.
-/
theorem paper_lemma6_reject_middle_lo_derivative_formula_of_interval_density_paths
    (arrivalRate switchRate lo hi Qj Tj Wj : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density lo)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21RejectMiddleQiPath arrivalRate switchRate density switchProb lo hi *
          Tj +
        Qj * gn21RejectMiddleTiPath arrivalRate density lo hi ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume 0 lo)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 lo))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) lo)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume 0 lo)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 lo))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) lo)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume 0 lo)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 lo))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) lo) :
    HasDerivAt
      (fun x =>
        gn21AggregateDynamicReward
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
            x hi)
          Qj
          (gn21RejectMiddleTiPath arrivalRate density x hi)
          Tj
          (gn21RejectMiddleWiPath arrivalRate density payment x hi)
          Wj)
      ((arrivalRate * density lo) * Qj *
        gn21DerivativeSignKernel (switchProb lo) lo (payment lo)
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
            lo hi)
          Qj
          (gn21RejectMiddleTiPath arrivalRate density lo hi)
          Tj
          (gn21RejectMiddleWiPath arrivalRate density payment lo hi)
          Wj /
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
              lo hi * Tj +
            Qj * gn21RejectMiddleTiPath arrivalRate density lo hi) ^ 2) lo ∧
    sameStrictSign
      ((arrivalRate * density lo) * Qj *
        gn21DerivativeSignKernel (switchProb lo) lo (payment lo)
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
            lo hi)
          Qj
          (gn21RejectMiddleTiPath arrivalRate density lo hi)
          Tj
          (gn21RejectMiddleWiPath arrivalRate density payment lo hi)
          Wj /
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
              lo hi * Tj +
            Qj * gn21RejectMiddleTiPath arrivalRate density lo hi) ^ 2)
      (gn21DerivativeSignKernel (switchProb lo) lo (payment lo)
        (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
          lo hi)
        Qj
        (gn21RejectMiddleTiPath arrivalRate density lo hi)
        Tj
        (gn21RejectMiddleWiPath arrivalRate density payment lo hi)
        Wj) := by
  constructor
  · apply paper_lemma6_aggregate_reward_hasDerivAt
    · convert gn21RejectMiddleQiPath_lo_hasDerivAt
        arrivalRate switchRate hi lo density switchProb hq_int hq_meas
        hq_cont using 1
      ring
    · convert gn21RejectMiddleWiPath_lo_hasDerivAt
        arrivalRate hi lo density payment hw_int hw_meas hw_cont using 1
      ring
    · convert gn21RejectMiddleTiPath_lo_hasDerivAt
        arrivalRate hi lo density ht_int ht_meas ht_cont using 1
      ring
    · rfl
    · rfl
    · rfl
    · exact hden
  · exact paper_lemma6_derivative_formula_of_aggregate_paths
      (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb · hi)
      (gn21RejectMiddleWiPath arrivalRate density payment · hi)
      (gn21RejectMiddleTiPath arrivalRate density · hi)
      (switchProb lo) lo (payment lo)
      (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb lo hi)
      Qj
      (gn21RejectMiddleTiPath arrivalRate density lo hi)
      Tj
      (gn21RejectMiddleWiPath arrivalRate density payment lo hi)
      Wj
      (arrivalRate * density lo)
      (mul_pos harrival_pos hdensity_pos)
      hQj_pos
      (by
        convert gn21RejectMiddleQiPath_lo_hasDerivAt
          arrivalRate switchRate hi lo density switchProb hq_int hq_meas
          hq_cont using 1
        ring)
      (by
        convert gn21RejectMiddleWiPath_lo_hasDerivAt
          arrivalRate hi lo density payment hw_int hw_meas hw_cont using 1
        ring)
      (by
        convert gn21RejectMiddleTiPath_lo_hasDerivAt
          arrivalRate hi lo density ht_int ht_meas ht_cont using 1
        ring)
      rfl rfl rfl hden

/--
Middle-rejection upper-cutoff form of Lemma 6.  Moving `hi` right shrinks the
accepted tail, so the derivative has the lower-endpoint sign.
-/
theorem paper_lemma6_reject_middle_hi_derivative_formula_of_interval_density_paths
    (arrivalRate switchRate lo hi Qj Tj Wj : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density hi)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21RejectMiddleQiPath arrivalRate switchRate density switchProb lo hi *
          Tj +
        Qj * gn21RejectMiddleTiPath arrivalRate density lo hi ≠ 0)
    (hq_int :
      IntegrableOn (fun τ => switchProb τ * density τ)
        (Set.Ioi (hi - 1)) volume)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 hi))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) hi)
    (hw_int :
      IntegrableOn (fun τ => payment τ * density τ)
        (Set.Ioi (hi - 1)) volume)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 hi))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) hi)
    (ht_int :
      IntegrableOn (fun τ => τ * density τ) (Set.Ioi (hi - 1)) volume)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 hi))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) hi) :
    HasDerivAt
      (fun x =>
        gn21AggregateDynamicReward
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
            lo x)
          Qj
          (gn21RejectMiddleTiPath arrivalRate density lo x)
          Tj
          (gn21RejectMiddleWiPath arrivalRate density payment lo x)
          Wj)
      (-((arrivalRate * density hi) * Qj *
        gn21DerivativeSignKernel (switchProb hi) hi (payment hi)
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
            lo hi)
          Qj
          (gn21RejectMiddleTiPath arrivalRate density lo hi)
          Tj
          (gn21RejectMiddleWiPath arrivalRate density payment lo hi)
          Wj /
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
              lo hi * Tj +
            Qj * gn21RejectMiddleTiPath arrivalRate density lo hi) ^ 2)) hi ∧
    sameStrictSign
      (-((arrivalRate * density hi) * Qj *
        gn21DerivativeSignKernel (switchProb hi) hi (payment hi)
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
            lo hi)
          Qj
          (gn21RejectMiddleTiPath arrivalRate density lo hi)
          Tj
          (gn21RejectMiddleWiPath arrivalRate density payment lo hi)
          Wj /
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
              lo hi * Tj +
            Qj * gn21RejectMiddleTiPath arrivalRate density lo hi) ^ 2))
      (-(gn21DerivativeSignKernel (switchProb hi) hi (payment hi)
        (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
          lo hi)
        Qj
        (gn21RejectMiddleTiPath arrivalRate density lo hi)
        Tj
        (gn21RejectMiddleWiPath arrivalRate density payment lo hi)
        Wj)) := by
  constructor
  · apply paper_lemma6_lower_aggregate_reward_hasDerivAt
    · convert gn21RejectMiddleQiPath_hi_hasDerivAt
        arrivalRate switchRate lo hi density switchProb hq_int hq_meas
        hq_cont using 1
      ring
    · convert gn21RejectMiddleWiPath_hi_hasDerivAt
        arrivalRate lo hi density payment hw_int hw_meas hw_cont using 1
      ring
    · convert gn21RejectMiddleTiPath_hi_hasDerivAt
        arrivalRate lo hi density ht_int ht_meas ht_cont using 1
      ring
    · rfl
    · rfl
    · rfl
    · exact hden
  · exact paper_lemma6_lower_derivative_formula_of_aggregate_paths
      (switchProb hi) hi (payment hi)
      (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb lo hi)
      Qj
      (gn21RejectMiddleTiPath arrivalRate density lo hi)
      Tj
      (gn21RejectMiddleWiPath arrivalRate density payment lo hi)
      Wj
      (arrivalRate * density hi)
      (mul_pos harrival_pos hdensity_pos)
      hQj_pos hden

/--
Positive kernels imply positive endpoint derivatives directly from endpoint
data, without constructing the older certificate object by hand.
-/
theorem paper_lemma6_derivative_value_pos_of_kernel_pos_of_endpoint_data
    (D : Lemma6EndpointDerivativeData)
    (hkernel_pos :
      0 < gn21DerivativeSignKernel D.q D.u D.wi D.Qi D.Qj D.Ti D.Tj D.Wi D.Wj) :
    0 < D.derivativeValue := by
  exact sameStrictSign_pos_left
    (lemma6DerivativeFormulaCertificate_of_endpoint_data D).same_sign
    hkernel_pos

/--
Negative kernels imply negative endpoint derivatives directly from endpoint
data.
-/
theorem paper_lemma6_derivative_value_neg_of_kernel_neg_of_endpoint_data
    (D : Lemma6EndpointDerivativeData)
    (hkernel_neg :
      gn21DerivativeSignKernel D.q D.u D.wi D.Qi D.Qj D.Ti D.Tj D.Wi D.Wj < 0) :
    D.derivativeValue < 0 := by
  exact sameStrictSign_neg_left
    (lemma6DerivativeFormulaCertificate_of_endpoint_data D).same_sign
    hkernel_neg

/--
Endpoint-data version of the Lemma 6 improvement step: a positive kernel gives
a nearby right endpoint move with strictly larger aggregate reward.
-/
theorem paper_lemma6_exists_pos_right_improvement_of_kernel_pos_of_endpoint_data
    (D : Lemma6EndpointDerivativeData)
    (hkernel_pos :
      0 < gn21DerivativeSignKernel D.q D.u D.wi D.Qi D.Qj D.Ti D.Tj D.Wi D.Wj) :
    ∃ ε : ℝ, 0 < ε ∧
      D.rewardAlongEndpoint D.u < D.rewardAlongEndpoint (D.u + ε) :=
  exists_pos_right_improvement_of_hasDerivAt_pos D.has_derivative
    (paper_lemma6_derivative_value_pos_of_kernel_pos_of_endpoint_data
      D hkernel_pos)

/--
Endpoint-data version of the Lemma 6 decrease step: a negative kernel gives a
nearby right endpoint move with strictly smaller aggregate reward.
-/
theorem paper_lemma6_exists_pos_right_decrease_of_kernel_neg_of_endpoint_data
    (D : Lemma6EndpointDerivativeData)
    (hkernel_neg :
      gn21DerivativeSignKernel D.q D.u D.wi D.Qi D.Qj D.Ti D.Tj D.Wi D.Wj < 0) :
    ∃ ε : ℝ, 0 < ε ∧
      D.rewardAlongEndpoint (D.u + ε) < D.rewardAlongEndpoint D.u :=
  exists_pos_right_decrease_of_hasDerivAt_neg D.has_derivative
    (paper_lemma6_derivative_value_neg_of_kernel_neg_of_endpoint_data
      D hkernel_neg)

/--
Interval-density improvement step for a moving upper endpoint.  A positive
Lemma 6 kernel gives a nearby larger upper endpoint with strictly larger
aggregate dynamic reward.
-/
theorem paper_lemma6_exists_pos_right_improvement_of_interval_density_kernel_pos
    (arrivalRate switchRate lowerEndpoint u Qj Tj Wj : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
          switchProb u * Tj +
        Qj *
          gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        lowerEndpoint u)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        lowerEndpoint u)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume lowerEndpoint u)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hkernel_pos :
      0 < gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
          switchProb u)
        Qj
        (gn21EndpointTiPath arrivalRate lowerEndpoint density u)
        Tj
        (gn21EndpointWiPath arrivalRate lowerEndpoint density payment u)
        Wj) :
    ∃ ε : ℝ, 0 < ε ∧
      gn21AggregateDynamicReward
          (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
            switchProb u)
          Qj
          (gn21EndpointTiPath arrivalRate lowerEndpoint density u)
          Tj
          (gn21EndpointWiPath arrivalRate lowerEndpoint density payment u)
          Wj <
        gn21AggregateDynamicReward
          (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
            switchProb (u + ε))
          Qj
          (gn21EndpointTiPath arrivalRate lowerEndpoint density (u + ε))
          Tj
          (gn21EndpointWiPath arrivalRate lowerEndpoint density payment
            (u + ε))
          Wj := by
  let D :=
    lemma6EndpointDerivativeData_of_interval_density_paths
      arrivalRate switchRate lowerEndpoint u Qj Tj Wj density switchProb
      payment harrival_pos hdensity_pos hQj_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont
  have h :=
    paper_lemma6_exists_pos_right_improvement_of_kernel_pos_of_endpoint_data
      D (by simpa [D] using hkernel_pos)
  simpa [D] using h

/--
Interval-density decrease step for a moving upper endpoint.  A negative
Lemma 6 kernel gives a nearby larger upper endpoint with strictly smaller
aggregate dynamic reward.
-/
theorem paper_lemma6_exists_pos_right_decrease_of_interval_density_kernel_neg
    (arrivalRate switchRate lowerEndpoint u Qj Tj Wj : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
          switchProb u * Tj +
        Qj *
          gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        lowerEndpoint u)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        lowerEndpoint u)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume lowerEndpoint u)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hkernel_neg :
      gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
          switchProb u)
        Qj
        (gn21EndpointTiPath arrivalRate lowerEndpoint density u)
        Tj
        (gn21EndpointWiPath arrivalRate lowerEndpoint density payment u)
        Wj < 0) :
    ∃ ε : ℝ, 0 < ε ∧
      gn21AggregateDynamicReward
          (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
            switchProb (u + ε))
          Qj
          (gn21EndpointTiPath arrivalRate lowerEndpoint density (u + ε))
          Tj
          (gn21EndpointWiPath arrivalRate lowerEndpoint density payment
            (u + ε))
          Wj <
        gn21AggregateDynamicReward
          (gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density
            switchProb u)
          Qj
          (gn21EndpointTiPath arrivalRate lowerEndpoint density u)
          Tj
          (gn21EndpointWiPath arrivalRate lowerEndpoint density payment u)
          Wj := by
  let D :=
    lemma6EndpointDerivativeData_of_interval_density_paths
      arrivalRate switchRate lowerEndpoint u Qj Tj Wj density switchProb
      payment harrival_pos hdensity_pos hQj_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont
  have h :=
    paper_lemma6_exists_pos_right_decrease_of_kernel_neg_of_endpoint_data
      D (by simpa [D] using hkernel_neg)
  simpa [D] using h

/--
Interval-density improvement step for a moving lower endpoint.  A negative
Lemma 6 kernel makes the lower-endpoint derivative positive, so moving the
lower endpoint right strictly increases aggregate dynamic reward.
-/
theorem paper_lemma6_exists_pos_right_improvement_of_lower_interval_density_kernel_neg
    (arrivalRate switchRate upperEndpoint u Qj Tj Wj : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
          switchProb u * Tj +
        Qj *
          gn21LowerEndpointTiPath arrivalRate upperEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        u upperEndpoint)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        u upperEndpoint)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume u upperEndpoint)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hkernel_neg :
      gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
          switchProb u)
        Qj
        (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
        Tj
        (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
        Wj < 0) :
    ∃ ε : ℝ, 0 < ε ∧
      gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb u)
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
          Wj <
        gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb (u + ε))
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density (u + ε))
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment
            (u + ε))
          Wj := by
  rcases paper_lemma6_lower_derivative_formula_of_interval_density_paths
      arrivalRate switchRate upperEndpoint u Qj Tj Wj density switchProb
      payment harrival_pos hdensity_pos hQj_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont with
    ⟨hderiv, hsign⟩
  exact exists_pos_right_improvement_of_hasDerivAt_pos hderiv
    (sameStrictSign_pos_left hsign (by linarith))

/--
Bounded lower-endpoint improvement step.  The additional upper bound on `ε`
lets later measured-policy replacements stay inside a fixed finite interval.
-/
theorem paper_lemma6_exists_pos_right_improvement_of_lower_interval_density_kernel_neg_lt
    (arrivalRate switchRate upperEndpoint u Qj Tj Wj δ : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
          switchProb u * Tj +
        Qj *
          gn21LowerEndpointTiPath arrivalRate upperEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        u upperEndpoint)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        u upperEndpoint)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume u upperEndpoint)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hkernel_neg :
      gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
          switchProb u)
        Qj
        (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
        Tj
        (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
        Wj < 0)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb u)
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
          Wj <
        gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb (u + ε))
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density (u + ε))
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment
            (u + ε))
          Wj := by
  rcases paper_lemma6_lower_derivative_formula_of_interval_density_paths
      arrivalRate switchRate upperEndpoint u Qj Tj Wj density switchProb
      payment harrival_pos hdensity_pos hQj_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont with
    ⟨hderiv, hsign⟩
  exact exists_pos_right_improvement_of_hasDerivAt_pos_lt hderiv
    (sameStrictSign_pos_left hsign (by linarith)) hδ

/--
Interval-density decrease step for a moving lower endpoint.  A positive
Lemma 6 kernel makes the lower-endpoint derivative negative, so moving the
lower endpoint right strictly decreases aggregate dynamic reward.
-/
theorem paper_lemma6_exists_pos_right_decrease_of_lower_interval_density_kernel_pos
    (arrivalRate switchRate upperEndpoint u Qj Tj Wj : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
          switchProb u * Tj +
        Qj *
          gn21LowerEndpointTiPath arrivalRate upperEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        u upperEndpoint)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        u upperEndpoint)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume u upperEndpoint)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hkernel_pos :
      0 < gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
          switchProb u)
        Qj
        (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
        Tj
        (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
        Wj) :
    ∃ ε : ℝ, 0 < ε ∧
      gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb (u + ε))
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density (u + ε))
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment
            (u + ε))
          Wj <
        gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb u)
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
          Wj := by
  rcases paper_lemma6_lower_derivative_formula_of_interval_density_paths
      arrivalRate switchRate upperEndpoint u Qj Tj Wj density switchProb
      payment harrival_pos hdensity_pos hQj_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont with
    ⟨hderiv, hsign⟩
  exact exists_pos_right_decrease_of_hasDerivAt_neg hderiv
    (sameStrictSign_neg_left hsign (by linarith))

/--
Bounded lower-endpoint decrease step.  This is the finite-interval counterpart
of `paper_lemma6_exists_pos_right_decrease_of_lower_interval_density_kernel_pos`.
-/
theorem paper_lemma6_exists_pos_right_decrease_of_lower_interval_density_kernel_pos_lt
    (arrivalRate switchRate upperEndpoint u Qj Tj Wj δ : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
          switchProb u * Tj +
        Qj *
          gn21LowerEndpointTiPath arrivalRate upperEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        u upperEndpoint)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        u upperEndpoint)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume u upperEndpoint)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hkernel_pos :
      0 < gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
          switchProb u)
        Qj
        (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
        Tj
        (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
        Wj)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb (u + ε))
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density (u + ε))
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment
            (u + ε))
          Wj <
        gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb u)
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
          Wj := by
  rcases paper_lemma6_lower_derivative_formula_of_interval_density_paths
      arrivalRate switchRate upperEndpoint u Qj Tj Wj density switchProb
      payment harrival_pos hdensity_pos hQj_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont with
    ⟨hderiv, hsign⟩
  exact exists_pos_right_decrease_of_hasDerivAt_neg_lt hderiv
    (sameStrictSign_neg_left hsign (by linarith)) hδ

/--
Bounded lower-endpoint left-expansion improvement.  A positive Lemma 6 kernel
makes the derivative in the lower endpoint negative, so moving the lower
endpoint left strictly improves aggregate reward.
-/
theorem paper_lemma6_exists_pos_left_improvement_of_lower_interval_density_kernel_pos_lt
    (arrivalRate switchRate upperEndpoint u Qj Tj Wj δ : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
          switchProb u * Tj +
        Qj *
          gn21LowerEndpointTiPath arrivalRate upperEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume
        u upperEndpoint)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume
        u upperEndpoint)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume u upperEndpoint)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hkernel_pos :
      0 < gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint density
          switchProb u)
        Qj
        (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
        Tj
        (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
        Wj)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb u)
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment u)
          Wj <
        gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switchRate upperEndpoint
            density switchProb (u - ε))
          Qj
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density (u - ε))
          Tj
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density payment
            (u - ε))
          Wj := by
  rcases paper_lemma6_lower_derivative_formula_of_interval_density_paths
      arrivalRate switchRate upperEndpoint u Qj Tj Wj density switchProb
      payment harrival_pos hdensity_pos hQj_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont with
    ⟨hderiv, hsign⟩
  exact exists_pos_left_improvement_of_hasDerivAt_neg_lt hderiv
    (sameStrictSign_neg_left hsign (by linarith)) hδ

/--
Bounded tail left-expansion improvement.  This is the unbounded-tail analogue
of the finite lower-endpoint movement: a positive Lemma 6 kernel makes a small
decrease of the tail threshold strictly improve aggregate reward.
-/
theorem paper_lemma6_exists_pos_left_improvement_of_tail_interval_density_kernel_pos_lt
    (arrivalRate switchRate u Qj Tj Wj δ : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21TailQiPath arrivalRate switchRate density switchProb u * Tj +
        Qj * gn21TailTiPath arrivalRate density u ≠ 0)
    (hq_int :
      IntegrableOn (fun τ => switchProb τ * density τ) (Set.Ioi (u - 1))
        volume)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 u))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
    (hw_int :
      IntegrableOn (fun τ => payment τ * density τ) (Set.Ioi (u - 1))
        volume)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 u))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
    (ht_int :
      IntegrableOn (fun τ => τ * density τ) (Set.Ioi (u - 1)) volume)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hkernel_pos :
      0 < gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21TailQiPath arrivalRate switchRate density switchProb u)
        Qj
        (gn21TailTiPath arrivalRate density u)
        Tj
        (gn21TailWiPath arrivalRate density payment u)
        Wj)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      gn21AggregateDynamicReward
          (gn21TailQiPath arrivalRate switchRate density switchProb u)
          Qj
          (gn21TailTiPath arrivalRate density u)
          Tj
          (gn21TailWiPath arrivalRate density payment u)
          Wj <
        gn21AggregateDynamicReward
          (gn21TailQiPath arrivalRate switchRate density switchProb (u - ε))
          Qj
          (gn21TailTiPath arrivalRate density (u - ε))
          Tj
          (gn21TailWiPath arrivalRate density payment (u - ε))
          Wj := by
  rcases paper_lemma6_tail_derivative_formula_of_interval_density_paths
      arrivalRate switchRate u Qj Tj Wj density switchProb payment
      harrival_pos hdensity_pos hQj_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont with
    ⟨hderiv, hsign⟩
  exact exists_pos_left_improvement_of_hasDerivAt_neg_lt hderiv
    (sameStrictSign_neg_left hsign (by linarith)) hδ

/--
Bounded middle-rejection lower-cutoff improvement.  A positive Lemma 6 kernel
at `lo` makes a small rightward expansion of the short accepted interval
strictly improve aggregate reward.
-/
theorem paper_lemma6_exists_pos_right_improvement_of_reject_middle_lo_interval_density_kernel_pos_lt
    (arrivalRate switchRate lo hi Qj Tj Wj δ : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density lo)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21RejectMiddleQiPath arrivalRate switchRate density switchProb lo hi *
          Tj +
        Qj * gn21RejectMiddleTiPath arrivalRate density lo hi ≠ 0)
    (hq_int :
      IntervalIntegrable (fun τ => switchProb τ * density τ) volume 0 lo)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 lo))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) lo)
    (hw_int :
      IntervalIntegrable (fun τ => payment τ * density τ) volume 0 lo)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 lo))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) lo)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume 0 lo)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 lo))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) lo)
    (hkernel_pos :
      0 < gn21DerivativeSignKernel (switchProb lo) lo (payment lo)
        (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
          lo hi)
        Qj
        (gn21RejectMiddleTiPath arrivalRate density lo hi)
        Tj
        (gn21RejectMiddleWiPath arrivalRate density payment lo hi)
        Wj)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      gn21AggregateDynamicReward
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
            lo hi)
          Qj
          (gn21RejectMiddleTiPath arrivalRate density lo hi)
          Tj
          (gn21RejectMiddleWiPath arrivalRate density payment lo hi)
          Wj <
        gn21AggregateDynamicReward
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
            (lo + ε) hi)
          Qj
          (gn21RejectMiddleTiPath arrivalRate density (lo + ε) hi)
          Tj
          (gn21RejectMiddleWiPath arrivalRate density payment (lo + ε) hi)
          Wj := by
  rcases
      paper_lemma6_reject_middle_lo_derivative_formula_of_interval_density_paths
        arrivalRate switchRate lo hi Qj Tj Wj density switchProb payment
        harrival_pos hdensity_pos hQj_pos hden hq_int hq_meas hq_cont
        hw_int hw_meas hw_cont ht_int ht_meas ht_cont with
    ⟨hderiv, hsign⟩
  exact exists_pos_right_improvement_of_hasDerivAt_pos_lt hderiv
    (sameStrictSign_pos_left hsign hkernel_pos) hδ

/--
Bounded middle-rejection upper-cutoff improvement.  A positive Lemma 6 kernel
at `hi` makes a small leftward expansion of the accepted tail strictly improve
aggregate reward.
-/
theorem paper_lemma6_exists_pos_left_improvement_of_reject_middle_hi_interval_density_kernel_pos_lt
    (arrivalRate switchRate lo hi Qj Tj Wj δ : ℝ)
    (density switchProb payment : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density hi)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21RejectMiddleQiPath arrivalRate switchRate density switchProb lo hi *
          Tj +
        Qj * gn21RejectMiddleTiPath arrivalRate density lo hi ≠ 0)
    (hq_int :
      IntegrableOn (fun τ => switchProb τ * density τ)
        (Set.Ioi (hi - 1)) volume)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => switchProb τ * density τ) (𝓝 hi))
    (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) hi)
    (hw_int :
      IntegrableOn (fun τ => payment τ * density τ)
        (Set.Ioi (hi - 1)) volume)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => payment τ * density τ) (𝓝 hi))
    (hw_cont : ContinuousAt (fun τ => payment τ * density τ) hi)
    (ht_int :
      IntegrableOn (fun τ => τ * density τ) (Set.Ioi (hi - 1)) volume)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 hi))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) hi)
    (hkernel_pos :
      0 < gn21DerivativeSignKernel (switchProb hi) hi (payment hi)
        (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
          lo hi)
        Qj
        (gn21RejectMiddleTiPath arrivalRate density lo hi)
        Tj
        (gn21RejectMiddleWiPath arrivalRate density payment lo hi)
        Wj)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      gn21AggregateDynamicReward
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
            lo hi)
          Qj
          (gn21RejectMiddleTiPath arrivalRate density lo hi)
          Tj
          (gn21RejectMiddleWiPath arrivalRate density payment lo hi)
          Wj <
        gn21AggregateDynamicReward
          (gn21RejectMiddleQiPath arrivalRate switchRate density switchProb
            lo (hi - ε))
          Qj
          (gn21RejectMiddleTiPath arrivalRate density lo (hi - ε))
          Tj
          (gn21RejectMiddleWiPath arrivalRate density payment lo (hi - ε))
          Wj := by
  rcases
      paper_lemma6_reject_middle_hi_derivative_formula_of_interval_density_paths
        arrivalRate switchRate lo hi Qj Tj Wj density switchProb payment
        harrival_pos hdensity_pos hQj_pos hden hq_int hq_meas hq_cont
        hw_int hw_meas hw_cont ht_int ht_meas ht_cont with
    ⟨hderiv, hsign⟩
  exact exists_pos_left_improvement_of_hasDerivAt_neg_lt hderiv
    (sameStrictSign_neg_left hsign (by linarith)) hδ

/-- Lemma 6, conditional on the continuous endpoint-derivative certificate. -/
theorem paper_lemma6_derivative_formula_of_certificate
    (C : Lemma6DerivativeFormulaCertificate) :
    sameStrictSign C.derivativeValue
      (gn21DerivativeSignKernel C.q C.u C.wi C.Qi C.Qj C.Ti C.Tj C.Wi C.Wj) := by
  exact C.same_sign

/-- Positive algebraic derivative kernels imply positive analytic endpoint derivatives. -/
theorem paper_lemma6_derivative_value_pos_of_kernel_pos_of_certificate
    (C : Lemma6DerivativeFormulaCertificate)
    (hkernel_pos :
      0 < gn21DerivativeSignKernel C.q C.u C.wi C.Qi C.Qj C.Ti C.Tj C.Wi C.Wj) :
    0 < C.derivativeValue := by
  exact sameStrictSign_pos_left C.same_sign hkernel_pos

/-- Negative algebraic derivative kernels imply negative analytic endpoint derivatives. -/
theorem paper_lemma6_derivative_value_neg_of_kernel_neg_of_certificate
    (C : Lemma6DerivativeFormulaCertificate)
    (hkernel_neg :
      gn21DerivativeSignKernel C.q C.u C.wi C.Qi C.Qj C.Ti C.Tj C.Wi C.Wj < 0) :
    C.derivativeValue < 0 := by
  exact sameStrictSign_neg_left C.same_sign hkernel_neg

/--
Lemma 6 structured-kernel bridge: after substituting the structured price
fields, the analytic endpoint derivative has the same sign as the structured
kernel used by Remark 2 and Lemmas 9-10.
-/
theorem paper_lemma6_derivative_value_same_sign_structured_kernel_of_certificate
    (C : Lemma6DerivativeFormulaCertificate)
    (q u m z switchIJ Qi Qj Ti Tj Rj : ℝ)
    (hq : C.q = q)
    (hu_eq : C.u = u)
    (hwi : C.wi = m * u + z * q)
    (hQi : C.Qi = Qi)
    (hQj : C.Qj = Qj)
    (hTi : C.Ti = Ti)
    (hTj : C.Tj = Tj)
    (hWi : C.Wi = m * (Ti - 1) + z * (Qi - switchIJ))
    (hWj : C.Wj = Rj * Tj) :
    sameStrictSign C.derivativeValue
      (gn21StructuredDerivativeSignKernel q u m z switchIJ Qi Qj Ti Tj Rj) := by
  have hkernel :
      gn21DerivativeSignKernel C.q C.u C.wi C.Qi C.Qj C.Ti C.Tj C.Wi C.Wj =
        gn21StructuredDerivativeSignKernel q u m z switchIJ Qi Qj Ti Tj Rj := by
    rw [hq, hu_eq, hwi, hQi, hQj, hTi, hTj, hWi, hWj]
    exact paper_remark2_structured_derivative_kernel_algebra
      q u m z switchIJ Qi Qj Ti Tj Rj
  refine sameStrictSign_trans C.same_sign ?_
  rw [hkernel]
  exact sameStrictSign_refl _

/-- Positive structured kernels imply positive analytic endpoint derivatives. -/
theorem paper_lemma6_derivative_value_pos_of_structured_kernel_pos_of_certificate
    (C : Lemma6DerivativeFormulaCertificate)
    (q u m z switchIJ Qi Qj Ti Tj Rj : ℝ)
    (hq : C.q = q)
    (hu_eq : C.u = u)
    (hwi : C.wi = m * u + z * q)
    (hQi : C.Qi = Qi)
    (hQj : C.Qj = Qj)
    (hTi : C.Ti = Ti)
    (hTj : C.Tj = Tj)
    (hWi : C.Wi = m * (Ti - 1) + z * (Qi - switchIJ))
    (hWj : C.Wj = Rj * Tj)
    (hstructured_pos :
      0 < gn21StructuredDerivativeSignKernel q u m z switchIJ Qi Qj Ti Tj Rj) :
    0 < C.derivativeValue := by
  have hsign :=
    paper_lemma6_derivative_value_same_sign_structured_kernel_of_certificate
      C q u m z switchIJ Qi Qj Ti Tj Rj
      hq hu_eq hwi hQi hQj hTi hTj hWi hWj
  exact sameStrictSign_pos_left hsign hstructured_pos

/-- Negative structured kernels imply negative analytic endpoint derivatives. -/
theorem paper_lemma6_derivative_value_neg_of_structured_kernel_neg_of_certificate
    (C : Lemma6DerivativeFormulaCertificate)
    (q u m z switchIJ Qi Qj Ti Tj Rj : ℝ)
    (hq : C.q = q)
    (hu_eq : C.u = u)
    (hwi : C.wi = m * u + z * q)
    (hQi : C.Qi = Qi)
    (hQj : C.Qj = Qj)
    (hTi : C.Ti = Ti)
    (hTj : C.Tj = Tj)
    (hWi : C.Wi = m * (Ti - 1) + z * (Qi - switchIJ))
    (hWj : C.Wj = Rj * Tj)
    (hstructured_neg :
      gn21StructuredDerivativeSignKernel q u m z switchIJ Qi Qj Ti Tj Rj < 0) :
    C.derivativeValue < 0 := by
  have hsign :=
    paper_lemma6_derivative_value_same_sign_structured_kernel_of_certificate
      C q u m z switchIJ Qi Qj Ti Tj Rj
      hq hu_eq hwi hQi hQj hTi hTj hWi hWj
  exact sameStrictSign_neg_left hsign hstructured_neg

/--
Lemma 6 certificate bridge to the normalized response after substituting
state reward rates.  This narrows the remaining analytic input to the endpoint
derivative certificate itself; the polynomial-to-response sign transfer is
closed algebra.
-/
theorem paper_lemma6_derivative_value_same_sign_response_of_certificate
    (C : Lemma6DerivativeFormulaCertificate)
    (Ri Rj : ℝ)
    (hWi : C.Wi = Ri * C.Ti)
    (hWj : C.Wj = Rj * C.Tj)
    (hu : 0 < C.u)
    (hTi_pos : 0 < C.Ti)
    (hTj_pos : 0 < C.Tj) :
    sameStrictSign C.derivativeValue
      (gn21Lemma6Response C.q C.u C.wi C.Qi C.Qj C.Ti C.Tj Ri Rj) := by
  have hkernel :
      gn21DerivativeSignKernel C.q C.u C.wi C.Qi C.Qj C.Ti C.Tj C.Wi C.Wj =
        gn21DerivativeSignKernel C.q C.u C.wi C.Qi C.Qj C.Ti C.Tj
          (Ri * C.Ti) (Rj * C.Tj) := by
    simp [hWi, hWj]
  refine sameStrictSign_trans C.same_sign ?_
  rw [hkernel]
  exact paper_lemma6_derivative_kernel_same_sign_response
    C.q C.u C.wi C.Qi C.Qj C.Ti C.Tj Ri Rj hu hTi_pos hTj_pos

/--
Positive response values imply positive endpoint derivatives once the Lemma 6
analytic certificate and the state-rate substitution are in place.
-/
theorem paper_lemma6_derivative_value_pos_of_response_pos_of_certificate
    (C : Lemma6DerivativeFormulaCertificate)
    (Ri Rj : ℝ)
    (hWi : C.Wi = Ri * C.Ti)
    (hWj : C.Wj = Rj * C.Tj)
    (hu : 0 < C.u)
    (hTi_pos : 0 < C.Ti)
    (hTj_pos : 0 < C.Tj)
    (hresponse_pos :
      0 < gn21Lemma6Response C.q C.u C.wi C.Qi C.Qj C.Ti C.Tj Ri Rj) :
    0 < C.derivativeValue := by
  have hsign :=
    paper_lemma6_derivative_value_same_sign_response_of_certificate
      C Ri Rj hWi hWj hu hTi_pos hTj_pos
  exact sameStrictSign_pos_left hsign hresponse_pos

/--
Negative response values imply negative endpoint derivatives once the Lemma 6
analytic certificate and the state-rate substitution are in place.
-/
theorem paper_lemma6_derivative_value_neg_of_response_neg_of_certificate
    (C : Lemma6DerivativeFormulaCertificate)
    (Ri Rj : ℝ)
    (hWi : C.Wi = Ri * C.Ti)
    (hWj : C.Wj = Rj * C.Tj)
    (hu : 0 < C.u)
    (hTi_pos : 0 < C.Ti)
    (hTj_pos : 0 < C.Tj)
    (hresponse_neg :
      gn21Lemma6Response C.q C.u C.wi C.Qi C.Qj C.Ti C.Tj Ri Rj < 0) :
    C.derivativeValue < 0 := by
  have hsign :=
    paper_lemma6_derivative_value_same_sign_response_of_certificate
      C Ri Rj hWi hWj hu hTi_pos hTj_pos
  exact sameStrictSign_neg_left hsign hresponse_neg

/-- Strict quasi-convexity on positive trip lengths. -/
def strictQuasiConvexOnPositive (f : TripLength → ℝ) : Prop :=
  ∀ x y θ : ℝ, 0 < x → 0 < y → x ≠ y → 0 < θ → θ < 1 →
    f (θ * x + (1 - θ) * y) < max (f x) (f y)

/-- Strict quasi-concavity on positive trip lengths. -/
def strictQuasiConcaveOnPositive (f : TripLength → ℝ) : Prop :=
  ∀ x y θ : ℝ, 0 < x → 0 < y → x ≠ y → 0 < θ → θ < 1 →
    min (f x) (f y) < f (θ * x + (1 - θ) * y)

/--
The canonical positive-over-`u` response is strictly quasi-convex on positive
trip lengths.  This is the algebraic shape used by Lemma 7 after the source
calculus reduces the derivative response to a constant plus a positive
coefficient divided by `u`.
-/
theorem strictQuasiConvexOnPositive_const_add_pos_div
    (A B : ℝ) (hA : 0 < A) :
    strictQuasiConvexOnPositive (fun u : TripLength => A / u + B) := by
  intro x y θ hx hy hxy hθ_pos hθ_lt_one
  have hθ_nonneg : 0 ≤ θ := le_of_lt hθ_pos
  have hθ_le_one : θ ≤ 1 := le_of_lt hθ_lt_one
  have hone_minus_pos : 0 < 1 - θ := by linarith
  have hz_pos : 0 < θ * x + (1 - θ) * y := by
    exact add_pos (mul_pos hθ_pos hx) (mul_pos hone_minus_pos hy)
  by_cases hxy_lt : x < y
  · have hx_lt_z : x < θ * x + (1 - θ) * y := by
      nlinarith [mul_pos hone_minus_pos (sub_pos.mpr hxy_lt)]
    have hdiv : A / (θ * x + (1 - θ) * y) < A / x := by
      exact div_lt_div_of_pos_left hA hx hx_lt_z
    have hlt :
        (fun u : TripLength => A / u + B) (θ * x + (1 - θ) * y) <
          (fun u : TripLength => A / u + B) x := by
      simpa [add_comm] using add_lt_add_left hdiv B
    exact lt_of_lt_of_le hlt (le_max_left _ _)
  · have hy_lt_x : y < x := by
      exact lt_of_le_of_ne (le_of_not_gt hxy_lt) (Ne.symm hxy)
    have hy_lt_z : y < θ * x + (1 - θ) * y := by
      nlinarith [mul_pos hθ_pos (sub_pos.mpr hy_lt_x)]
    have hdiv : A / (θ * x + (1 - θ) * y) < A / y := by
      exact div_lt_div_of_pos_left hA hy hy_lt_z
    have hlt :
        (fun u : TripLength => A / u + B) (θ * x + (1 - θ) * y) <
          (fun u : TripLength => A / u + B) y := by
      simpa [add_comm] using add_lt_add_left hdiv B
    exact lt_of_lt_of_le hlt (le_max_right _ _)

/--
The canonical negative-over-`u` response is strictly quasi-concave on positive
trip lengths.  This is the sign-reversed shape used by Lemma 8.
-/
theorem strictQuasiConcaveOnPositive_const_add_neg_div
    (A B : ℝ) (hA : A < 0) :
    strictQuasiConcaveOnPositive (fun u : TripLength => A / u + B) := by
  intro x y θ hx hy hxy hθ_pos hθ_lt_one
  have hθ_nonneg : 0 ≤ θ := le_of_lt hθ_pos
  have hθ_le_one : θ ≤ 1 := le_of_lt hθ_lt_one
  have hone_minus_pos : 0 < 1 - θ := by linarith
  have hz_pos : 0 < θ * x + (1 - θ) * y := by
    exact add_pos (mul_pos hθ_pos hx) (mul_pos hone_minus_pos hy)
  have hnegA : 0 < -A := by linarith
  by_cases hxy_lt : x < y
  · have hx_lt_z : x < θ * x + (1 - θ) * y := by
      nlinarith [mul_pos hone_minus_pos (sub_pos.mpr hxy_lt)]
    have hdiv_pos : (-A) / (θ * x + (1 - θ) * y) < (-A) / x := by
      exact div_lt_div_of_pos_left hnegA hx hx_lt_z
    have hdiv : A / x < A / (θ * x + (1 - θ) * y) := by
      have hneg : -(A / (θ * x + (1 - θ) * y)) < -(A / x) := by
        simpa [neg_div] using hdiv_pos
      linarith
    have hlt :
        (fun u : TripLength => A / u + B) x <
          (fun u : TripLength => A / u + B) (θ * x + (1 - θ) * y) := by
      simpa [add_comm] using add_lt_add_left hdiv B
    exact lt_of_le_of_lt (min_le_left _ _) hlt
  · have hy_lt_x : y < x := by
      exact lt_of_le_of_ne (le_of_not_gt hxy_lt) (Ne.symm hxy)
    have hy_lt_z : y < θ * x + (1 - θ) * y := by
      nlinarith [mul_pos hθ_pos (sub_pos.mpr hy_lt_x)]
    have hdiv_pos : (-A) / (θ * x + (1 - θ) * y) < (-A) / y := by
      exact div_lt_div_of_pos_left hnegA hy hy_lt_z
    have hdiv : A / y < A / (θ * x + (1 - θ) * y) := by
      have hneg : -(A / (θ * x + (1 - θ) * y)) < -(A / y) := by
        simpa [neg_div] using hdiv_pos
      linarith
    have hlt :
        (fun u : TripLength => A / u + B) y <
          (fun u : TripLength => A / u + B) (θ * x + (1 - θ) * y) := by
      simpa [add_comm] using add_lt_add_left hdiv B
    exact lt_of_le_of_lt (min_le_right _ _) hlt

/-- Lemma 7 closed canonical response case. -/
theorem paper_lemma7_canonical_positive_over_u_quasi_convex
    (A B : ℝ) (hA : 0 < A) :
    strictQuasiConvexOnPositive (fun u : TripLength => A / u + B) := by
  exact strictQuasiConvexOnPositive_const_add_pos_div A B hA

/-- Lemma 8 closed canonical response case. -/
theorem paper_lemma8_canonical_negative_over_u_quasi_concave
    (A B : ℝ) (hA : A < 0) :
    strictQuasiConcaveOnPositive (fun u : TripLength => A / u + B) := by
  exact strictQuasiConcaveOnPositive_const_add_neg_div A B hA

/--
Lemma 7 closed canonical CTMC response-shape case:
`((c1 - c2*q(u))/u) + c3` is strictly quasi-convex on positive trip
lengths when `c1 > 0`, `c2 >= 0`, and CTMC rates are positive in the paper's
usual sense.
-/
theorem paper_lemma7_canonical_ctmc_response_quasi_convex
    (c1 c2 c3 lambdaIJ lambdaJI : ℝ)
    (hc1 : 0 < c1)
    (hc2 : 0 ≤ c2)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI) :
    strictQuasiConvexOnPositive
      (fun u : TripLength =>
        gn21Lemma7CanonicalResponse c1 c2 c3 lambdaIJ lambdaJI u) := by
  rcases lt_or_eq_of_le hc2 with hc2_pos | hc2_zero
  · have hlib :
        EconCSLib.StrictQuasiConvexOnPositive
          (fun u : ℝ =>
            gn21Lemma7CanonicalResponse c1 c2 c3 lambdaIJ lambdaJI u) := by
      apply EconCSLib.strictQuasiConvexOnPositive_of_deriv_proxy_strictMono
        (g := fun u : ℝ =>
          gn21Lemma7CanonicalDerivativeNumerator c1 c2 lambdaIJ lambdaJI u)
      · intro a b ha hab u hu
        have hu_pos : 0 < u := lt_of_lt_of_le ha hu.1
        exact
          (paper_lemma7_canonical_response_hasDerivAt c1 c2 c3
            lambdaIJ lambdaJI u (ne_of_gt hsum)
            (ne_of_gt hu_pos)).continuousAt.continuousWithinAt
      · intro u hu
        exact
          (paper_lemma7_canonical_response_hasDerivAt c1 c2 c3
            lambdaIJ lambdaJI u (ne_of_gt hsum)
            (ne_of_gt hu)).differentiableAt
      · apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
        · intro u hu
          exact
            (paper_lemma7_canonical_derivative_numerator_hasDerivAt
              c1 c2 lambdaIJ lambdaJI u
              (ne_of_gt hsum)).continuousAt.continuousWithinAt
        · intro u hu
          have hu_pos : 0 < u := by
            simpa using hu
          exact
            paper_lemma7_canonical_derivative_numerator_deriv_pos
              c1 c2 lambdaIJ lambdaJI u hc2_pos hlambdaIJ hsum hu_pos
      · intro u hu hderiv_nonneg
        have hu_sq_pos : 0 < u ^ 2 := sq_pos_of_ne_zero (ne_of_gt hu)
        have hderiv_eq :=
          (paper_lemma7_canonical_response_hasDerivAt c1 c2 c3
            lambdaIJ lambdaJI u (ne_of_gt hsum)
            (ne_of_gt hu)).deriv
        rw [hderiv_eq] at hderiv_nonneg
        have hmul := mul_nonneg hderiv_nonneg (le_of_lt hu_sq_pos)
        have hcancel :
            gn21Lemma7CanonicalDerivativeNumerator c1 c2 lambdaIJ lambdaJI u /
                u ^ 2 * u ^ 2 =
              gn21Lemma7CanonicalDerivativeNumerator c1 c2 lambdaIJ lambdaJI u := by
          field_simp [ne_of_gt hu_sq_pos]
        rwa [hcancel] at hmul
      · intro u hu hderiv_nonpos
        have hu_sq_pos : 0 < u ^ 2 := sq_pos_of_ne_zero (ne_of_gt hu)
        have hderiv_eq :=
          (paper_lemma7_canonical_response_hasDerivAt c1 c2 c3
            lambdaIJ lambdaJI u (ne_of_gt hsum)
            (ne_of_gt hu)).deriv
        rw [hderiv_eq] at hderiv_nonpos
        have hmul := mul_nonpos_of_nonpos_of_nonneg
          hderiv_nonpos (le_of_lt hu_sq_pos)
        have hcancel :
            gn21Lemma7CanonicalDerivativeNumerator c1 c2 lambdaIJ lambdaJI u /
                u ^ 2 * u ^ 2 =
              gn21Lemma7CanonicalDerivativeNumerator c1 c2 lambdaIJ lambdaJI u := by
          field_simp [ne_of_gt hu_sq_pos]
        rwa [hcancel] at hmul
    intro x y θ hx hy hxy hθ_pos hθ_lt_one
    exact hlib x y θ hx hy hxy hθ_pos hθ_lt_one
  · subst c2
    intro x y θ hx hy hxy hθ_pos hθ_lt_one
    have hbase :=
      paper_lemma7_canonical_positive_over_u_quasi_convex
        c1 c3 hc1 x y θ hx hy hxy hθ_pos hθ_lt_one
    simpa [gn21Lemma7CanonicalResponse] using hbase

/--
Lemma 8 closed canonical CTMC response-shape case, obtained as the sign
reversal of Lemma 7's canonical response.
-/
theorem paper_lemma8_canonical_ctmc_response_quasi_concave
    (c1 c2 c3 lambdaIJ lambdaJI : ℝ)
    (hc1 : 0 < c1)
    (hc2 : 0 ≤ c2)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI) :
    strictQuasiConcaveOnPositive
      (fun u : TripLength =>
        gn21Lemma8CanonicalResponse c1 c2 c3 lambdaIJ lambdaJI u) := by
  have hneg_qc :
      EconCSLib.StrictQuasiConvexOnPositive
        (fun u : ℝ =>
          -gn21Lemma8CanonicalResponse c1 c2 c3 lambdaIJ lambdaJI u) := by
    have hqc :=
      paper_lemma7_canonical_ctmc_response_quasi_convex
        c1 c2 (-c3) lambdaIJ lambdaJI hc1 hc2 hlambdaIJ hsum
    intro x y θ hx hy hxy hθ_pos hθ_lt_one
    have h := hqc x y θ hx hy hxy hθ_pos hθ_lt_one
    simpa [gn21Lemma7CanonicalResponse, gn21Lemma8CanonicalResponse,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hconcave :=
    EconCSLib.strictQuasiConcaveOnPositive_of_neg_strictQuasiConvex
      (f := fun u : ℝ =>
        gn21Lemma8CanonicalResponse c1 c2 c3 lambdaIJ lambdaJI u)
      hneg_qc
  intro x y θ hx hy hxy hθ_pos hθ_lt_one
  exact hconcave x y θ hx hy hxy hθ_pos hθ_lt_one

/--
Lemma 7 affine response identification: under positive trip length and
nonzero state times, the Lemma 6 affine response is the canonical CTMC
response with coefficients used in Lemma 7.
-/
theorem paper_lemma7_affine_ctmc_response_eq_canonical
    (lambdaIJ lambdaJI u m a Qi Qj Ti Tj Ri Rj : ℝ)
    (hu : u ≠ 0) (hTi : Ti ≠ 0) (hTj : Tj ≠ 0) :
    gn21Lemma6Response
        (gn21SwitchProb lambdaIJ lambdaJI u) u (m * u + a)
        Qi Qj Ti Tj Ri Rj =
      gn21Lemma7CanonicalResponse
        ((Qi / Ti + Qj / Tj) * a) (Ri - Rj)
        (m * (Qi / Ti + Qj / Tj) -
          (Qi / Ti * Rj + Qj / Tj * Ri))
        lambdaIJ lambdaJI u := by
  rw [paper_lemma7_8_affine_response_canonical_form
    (gn21SwitchProb lambdaIJ lambdaJI u) u m a Qi Qj Ti Tj Ri Rj
    hu hTi hTj]
  rfl

/--
Lemma 8 affine response identification: with negative additive term and
the opposite reward-gap sign, the same Lemma 6 affine response is the
sign-reversed canonical CTMC response used in Lemma 8.
-/
theorem paper_lemma8_affine_ctmc_response_eq_canonical
    (lambdaIJ lambdaJI u m a Qi Qj Ti Tj Ri Rj : ℝ)
    (hu : u ≠ 0) (hTi : Ti ≠ 0) (hTj : Tj ≠ 0) :
    gn21Lemma6Response
        (gn21SwitchProb lambdaIJ lambdaJI u) u (m * u + a)
        Qi Qj Ti Tj Ri Rj =
      gn21Lemma8CanonicalResponse
        ((Qi / Ti + Qj / Tj) * (-a)) (Rj - Ri)
        (m * (Qi / Ti + Qj / Tj) -
          (Qi / Ti * Rj + Qj / Tj * Ri))
        lambdaIJ lambdaJI u := by
  rw [paper_lemma7_8_affine_response_canonical_form
    (gn21SwitchProb lambdaIJ lambdaJI u) u m a Qi Qj Ti Tj Ri Rj
    hu hTi hTj]
  unfold gn21Lemma8CanonicalResponse
  ring

/--
Lemma 7 source affine-response shape: after substituting an affine price
`w_i(u)=m u+a` with `a>0`, the Lemma 6 normalized response is strictly
quasi-convex on positive trip lengths under the paper's reward-gap sign.
-/
theorem paper_lemma7_affine_ctmc_response_quasi_convex
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_pos : 0 < a)
    (hgap_nonneg : 0 ≤ Ri - Rj)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0) :
    strictQuasiConvexOnPositive
      (fun u : TripLength =>
        gn21Lemma6Response
          (gn21SwitchProb lambdaIJ lambdaJI u) u (m * u + a)
          Qi Qj Ti Tj Ri Rj) := by
  have hc1 : 0 < (Qi / Ti + Qj / Tj) * a :=
    mul_pos hstate_weight_pos ha_pos
  have hcanon :=
    paper_lemma7_canonical_ctmc_response_quasi_convex
      ((Qi / Ti + Qj / Tj) * a) (Ri - Rj)
      (m * (Qi / Ti + Qj / Tj) -
        (Qi / Ti * Rj + Qj / Tj * Ri))
      lambdaIJ lambdaJI hc1 hgap_nonneg hlambdaIJ hsum
  intro x y θ hx hy hxy hθ_pos hθ_lt_one
  have hone_minus_pos : 0 < 1 - θ := by linarith
  have hz_pos : 0 < θ * x + (1 - θ) * y := by
    exact add_pos (mul_pos hθ_pos hx) (mul_pos hone_minus_pos hy)
  change
    gn21Lemma6Response
        (gn21SwitchProb lambdaIJ lambdaJI (θ * x + (1 - θ) * y))
        (θ * x + (1 - θ) * y)
        (m * (θ * x + (1 - θ) * y) + a)
        Qi Qj Ti Tj Ri Rj <
      max
        (gn21Lemma6Response
          (gn21SwitchProb lambdaIJ lambdaJI x) x (m * x + a)
          Qi Qj Ti Tj Ri Rj)
        (gn21Lemma6Response
          (gn21SwitchProb lambdaIJ lambdaJI y) y (m * y + a)
          Qi Qj Ti Tj Ri Rj)
  rw [
    paper_lemma7_affine_ctmc_response_eq_canonical
      lambdaIJ lambdaJI (θ * x + (1 - θ) * y) m a Qi Qj Ti Tj Ri Rj
      (ne_of_gt hz_pos) hTi hTj,
    paper_lemma7_affine_ctmc_response_eq_canonical
      lambdaIJ lambdaJI x m a Qi Qj Ti Tj Ri Rj
      (ne_of_gt hx) hTi hTj,
    paper_lemma7_affine_ctmc_response_eq_canonical
      lambdaIJ lambdaJI y m a Qi Qj Ti Tj Ri Rj
      (ne_of_gt hy) hTi hTj]
  exact hcanon x y θ hx hy hxy hθ_pos hθ_lt_one

/--
Lemma 8 source affine-response shape: after substituting an affine price
`w_i(u)=m u+a` with `a<0`, the Lemma 6 normalized response is strictly
quasi-concave on positive trip lengths under the opposite reward-gap sign.
-/
theorem paper_lemma8_affine_ctmc_response_quasi_concave
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_neg : a < 0)
    (hgap_nonneg : 0 ≤ Rj - Ri)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0) :
    strictQuasiConcaveOnPositive
      (fun u : TripLength =>
        gn21Lemma6Response
          (gn21SwitchProb lambdaIJ lambdaJI u) u (m * u + a)
          Qi Qj Ti Tj Ri Rj) := by
  have hc1 : 0 < (Qi / Ti + Qj / Tj) * (-a) :=
    mul_pos hstate_weight_pos (neg_pos.mpr ha_neg)
  have hcanon :=
    paper_lemma8_canonical_ctmc_response_quasi_concave
      ((Qi / Ti + Qj / Tj) * (-a)) (Rj - Ri)
      (m * (Qi / Ti + Qj / Tj) -
        (Qi / Ti * Rj + Qj / Tj * Ri))
      lambdaIJ lambdaJI hc1 hgap_nonneg hlambdaIJ hsum
  intro x y θ hx hy hxy hθ_pos hθ_lt_one
  have hone_minus_pos : 0 < 1 - θ := by linarith
  have hz_pos : 0 < θ * x + (1 - θ) * y := by
    exact add_pos (mul_pos hθ_pos hx) (mul_pos hone_minus_pos hy)
  change
    min
        (gn21Lemma6Response
          (gn21SwitchProb lambdaIJ lambdaJI x) x (m * x + a)
          Qi Qj Ti Tj Ri Rj)
        (gn21Lemma6Response
          (gn21SwitchProb lambdaIJ lambdaJI y) y (m * y + a)
          Qi Qj Ti Tj Ri Rj) <
      gn21Lemma6Response
        (gn21SwitchProb lambdaIJ lambdaJI (θ * x + (1 - θ) * y))
        (θ * x + (1 - θ) * y)
        (m * (θ * x + (1 - θ) * y) + a)
        Qi Qj Ti Tj Ri Rj
  rw [
    paper_lemma8_affine_ctmc_response_eq_canonical
      lambdaIJ lambdaJI (θ * x + (1 - θ) * y) m a Qi Qj Ti Tj Ri Rj
      (ne_of_gt hz_pos) hTi hTj,
    paper_lemma8_affine_ctmc_response_eq_canonical
      lambdaIJ lambdaJI x m a Qi Qj Ti Tj Ri Rj
      (ne_of_gt hx) hTi hTj,
    paper_lemma8_affine_ctmc_response_eq_canonical
      lambdaIJ lambdaJI y m a Qi Qj Ti Tj Ri Rj
      (ne_of_gt hy) hTi hTj]
  exact hcanon x y θ hx hy hxy hθ_pos hθ_lt_one

/--
Lemma 7 certificate: affine pricing with positive additive term gives a
strictly quasi-convex derivative response in the relevant state.
-/
structure Lemma7QuasiConvexCertificate where
  response : TripLength → ℝ
  m : ℝ
  a : ℝ
  multiplier_pos : 0 < m
  additive_pos : 0 < a
  state_gap_nonpos : Prop
  state_gap_nonpos_holds : state_gap_nonpos
  response_quasi_convex : strictQuasiConvexOnPositive response

/-- Lemma 7 endpoint, conditional on the real-analysis quasi-convexity certificate. -/
theorem paper_lemma7_affine_positive_additive_quasi_convex_of_certificate
    (C : Lemma7QuasiConvexCertificate) :
    strictQuasiConvexOnPositive C.response := by
  exact C.response_quasi_convex

/--
Lemma 8 certificate: affine pricing with negative additive term gives a
strictly quasi-concave derivative response in the relevant state.
-/
structure Lemma8QuasiConcaveCertificate where
  response : TripLength → ℝ
  m : ℝ
  a : ℝ
  multiplier_pos : 0 < m
  additive_neg : a < 0
  state_gap_nonneg : Prop
  state_gap_nonneg_holds : state_gap_nonneg
  response_quasi_concave : strictQuasiConcaveOnPositive response

/-- Lemma 8 endpoint, conditional on the real-analysis quasi-concavity certificate. -/
theorem paper_lemma8_affine_negative_additive_quasi_concave_of_certificate
    (C : Lemma8QuasiConcaveCertificate) :
    strictQuasiConcaveOnPositive C.response := by
  exact C.response_quasi_concave

/--
Concrete Lemma 7 certificate constructor from the CTMC affine-response theorem.
This lets the older certificate endpoint consume the source-facing proof rather
than treating quasi-convexity as an opaque assumption.
-/
def paper_lemma7_affine_ctmc_quasi_convex_certificate
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hm_pos : 0 < m)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_pos : 0 < a)
    (hgap_nonneg : 0 ≤ Ri - Rj)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0) :
    Lemma7QuasiConvexCertificate where
  response := fun u : TripLength =>
    gn21Lemma6Response
      (gn21SwitchProb lambdaIJ lambdaJI u) u (m * u + a)
      Qi Qj Ti Tj Ri Rj
  m := m
  a := a
  multiplier_pos := hm_pos
  additive_pos := ha_pos
  state_gap_nonpos := Rj - Ri ≤ 0
  state_gap_nonpos_holds := by linarith
  response_quasi_convex :=
    paper_lemma7_affine_ctmc_response_quasi_convex
      m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI
      hstate_weight_pos ha_pos hgap_nonneg hlambdaIJ hsum hTi hTj

/--
Concrete Lemma 8 certificate constructor from the CTMC affine-response theorem.
-/
def paper_lemma8_affine_ctmc_quasi_concave_certificate
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hm_pos : 0 < m)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_neg : a < 0)
    (hgap_nonneg : 0 ≤ Rj - Ri)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0) :
    Lemma8QuasiConcaveCertificate where
  response := fun u : TripLength =>
    gn21Lemma6Response
      (gn21SwitchProb lambdaIJ lambdaJI u) u (m * u + a)
      Qi Qj Ti Tj Ri Rj
  m := m
  a := a
  multiplier_pos := hm_pos
  additive_neg := ha_neg
  state_gap_nonneg := 0 ≤ Rj - Ri
  state_gap_nonneg_holds := hgap_nonneg
  response_quasi_concave :=
    paper_lemma8_affine_ctmc_response_quasi_concave
      m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI
      hstate_weight_pos ha_neg hgap_nonneg hlambdaIJ hsum hTi hTj

/-- Lemma 5 derivative-shape cases and their policy forms. -/
inductive Lemma5DerivativeShape where
  | positive
  | strictlyIncreasing
  | strictlyDecreasing
  | strictlyQuasiConvex
  | strictlyQuasiConcave
  deriving DecidableEq

/-- The policy form produced by Lemma 5 for each derivative-shape case. -/
def lemma5PolicyForm (shape : Lemma5DerivativeShape) (σ : TripPolicy) : Prop :=
  match shape with
  | .positive => acceptsAllTrips σ
  | .strictlyIncreasing => ∃ t : ℝ, rejectsShortTrips t σ
  | .strictlyDecreasing => ∃ t : ℝ, rejectsLongTrips t σ
  | .strictlyQuasiConvex => ∃ lo hi : ℝ, rejectsMiddleTrips lo hi σ
  | .strictlyQuasiConcave => ∃ lo hi : ℝ, acceptsMiddleTrips lo hi σ

/--
Analytic witness behind each Lemma 5 derivative-shape case.  The policy-form
predicate above records the optimizer shape; this predicate records the
response-function shape that produces it in the source proof.
-/
def lemma5DerivativeShapeWitness
    (response : TripLength → ℝ) : Lemma5DerivativeShape → Prop
  | .positive => ∀ u : TripLength, 0 < u → 0 < response u
  | .strictlyIncreasing => StrictMonoOn response (Set.Ioi 0)
  | .strictlyDecreasing => StrictAntiOn response (Set.Ioi 0)
  | .strictlyQuasiConvex => strictQuasiConvexOnPositive response
  | .strictlyQuasiConcave => strictQuasiConcaveOnPositive response

/-- Lemma 7 supplies Lemma 5's strictly quasi-convex derivative-shape witness. -/
theorem lemma5DerivativeShapeWitness_strictlyQuasiConvex_of_lemma7_affine_ctmc_response
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_pos : 0 < a)
    (hgap_nonneg : 0 ≤ Ri - Rj)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0) :
    lemma5DerivativeShapeWitness
      (fun u : TripLength =>
        gn21Lemma6Response
          (gn21SwitchProb lambdaIJ lambdaJI u) u (m * u + a)
          Qi Qj Ti Tj Ri Rj)
      .strictlyQuasiConvex := by
  exact
    paper_lemma7_affine_ctmc_response_quasi_convex
      m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI
      hstate_weight_pos ha_pos hgap_nonneg hlambdaIJ hsum hTi hTj

/-- Lemma 8 supplies Lemma 5's strictly quasi-concave derivative-shape witness. -/
theorem lemma5DerivativeShapeWitness_strictlyQuasiConcave_of_lemma8_affine_ctmc_response
    (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ)
    (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj)
    (ha_neg : a < 0)
    (hgap_nonneg : 0 ≤ Rj - Ri)
    (hlambdaIJ : 0 < lambdaIJ)
    (hsum : 0 < lambdaIJ + lambdaJI)
    (hTi : Ti ≠ 0)
    (hTj : Tj ≠ 0) :
    lemma5DerivativeShapeWitness
      (fun u : TripLength =>
        gn21Lemma6Response
          (gn21SwitchProb lambdaIJ lambdaJI u) u (m * u + a)
          Qi Qj Ti Tj Ri Rj)
      .strictlyQuasiConcave := by
  exact
    paper_lemma8_affine_ctmc_response_quasi_concave
      m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI
      hstate_weight_pos ha_neg hgap_nonneg hlambdaIJ hsum hTi hTj

/-- Canonical policy accepting short trips and rejecting trips above threshold `t`. -/
def rejectLongTripsPolicy (t : ℝ) : TripPolicy :=
  Set.Ioi (0 : ℝ) ∩ Set.Iio t

/-- Canonical policy rejecting short trips and accepting trips above threshold `t`. -/
def rejectShortTripsPolicy (t : ℝ) : TripPolicy :=
  Set.Ioi (0 : ℝ) ∩ Set.Ioi t

/-- Canonical policy accepting only middle-length trips. -/
def acceptMiddleTripsPolicy (lo hi : ℝ) : TripPolicy :=
  Set.Ioi (0 : ℝ) ∩ Set.Ioi lo ∩ Set.Iio hi

/-- Canonical policy rejecting middle-length trips. -/
def rejectMiddleTripsPolicy (lo hi : ℝ) : TripPolicy :=
  Set.Ioi (0 : ℝ) ∩ (Set.Iio lo ∪ Set.Ioi hi)

/-- The canonical long-trip-rejection policy has the corresponding Lemma 5 form. -/
theorem rejectsLongTrips_rejectLongTripsPolicy (t : ℝ) :
    rejectsLongTrips t (rejectLongTripsPolicy t) := by
  intro τ hτ
  simp [rejectLongTripsPolicy, hτ]

/-- The canonical short-trip-rejection policy has the corresponding Lemma 5 form. -/
theorem rejectsShortTrips_rejectShortTripsPolicy (t : ℝ) :
    rejectsShortTrips t (rejectShortTripsPolicy t) := by
  intro τ hτ
  simp [rejectShortTripsPolicy, hτ]

/-- The canonical middle-acceptance policy has the corresponding Lemma 5 form. -/
theorem acceptsMiddleTrips_acceptMiddleTripsPolicy (lo hi : ℝ) :
    acceptsMiddleTrips lo hi (acceptMiddleTripsPolicy lo hi) := by
  intro τ hτ
  simp [acceptMiddleTripsPolicy, hτ]

/-- The canonical middle-rejection policy has the corresponding Lemma 5 form. -/
theorem rejectsMiddleTrips_rejectMiddleTripsPolicy (lo hi : ℝ) :
    rejectsMiddleTrips lo hi (rejectMiddleTripsPolicy lo hi) := by
  intro τ hτ
  simp [rejectMiddleTripsPolicy, hτ]

/--
A feasible policy with the long-trip-rejection shape is exactly the canonical
long-trip-rejection set.
-/
theorem eq_rejectLongTripsPolicy_of_rejectsLongTrips_of_subset_acceptAll
    {σ : TripPolicy} {t : ℝ}
    (hshape : rejectsLongTrips t σ)
    (hsub : σ ⊆ acceptAllPolicy) :
    σ = rejectLongTripsPolicy t := by
  ext τ
  constructor
  · intro hτ
    have hpos : 0 < τ := hsub hτ
    exact ⟨hpos, (hshape hpos).mp hτ⟩
  · intro hτ
    exact (hshape hτ.1).mpr hτ.2

/--
A feasible policy with the short-trip-rejection shape is exactly the canonical
tail set.
-/
theorem eq_rejectShortTripsPolicy_of_rejectsShortTrips_of_subset_acceptAll
    {σ : TripPolicy} {t : ℝ}
    (hshape : rejectsShortTrips t σ)
    (hsub : σ ⊆ acceptAllPolicy) :
    σ = rejectShortTripsPolicy t := by
  ext τ
  constructor
  · intro hτ
    have hpos : 0 < τ := hsub hτ
    exact ⟨hpos, (hshape hpos).mp hτ⟩
  · intro hτ
    exact (hshape hτ.1).mpr hτ.2

/--
A feasible policy with the middle-acceptance shape is exactly the canonical
bounded middle interval.
-/
theorem eq_acceptMiddleTripsPolicy_of_acceptsMiddleTrips_of_subset_acceptAll
    {σ : TripPolicy} {lo hi : ℝ}
    (hshape : acceptsMiddleTrips lo hi σ)
    (hsub : σ ⊆ acceptAllPolicy) :
    σ = acceptMiddleTripsPolicy lo hi := by
  ext τ
  constructor
  · intro hτ
    have hpos : 0 < τ := hsub hτ
    rcases (hshape hpos).mp hτ with ⟨hlo, hhi⟩
    exact ⟨⟨hpos, hlo⟩, hhi⟩
  · intro hτ
    exact (hshape hτ.1.1).mpr ⟨hτ.1.2, hτ.2⟩

/--
A feasible policy with the middle-rejection shape is exactly the canonical
short-or-tail set.
-/
theorem eq_rejectMiddleTripsPolicy_of_rejectsMiddleTrips_of_subset_acceptAll
    {σ : TripPolicy} {lo hi : ℝ}
    (hshape : rejectsMiddleTrips lo hi σ)
    (hsub : σ ⊆ acceptAllPolicy) :
    σ = rejectMiddleTripsPolicy lo hi := by
  ext τ
  constructor
  · intro hτ
    have hpos : 0 < τ := hsub hτ
    exact ⟨hpos, (hshape hpos).mp hτ⟩
  · intro hτ
    exact (hshape hτ.1).mpr hτ.2

/-- Canonical long-trip-rejection policies are measurable. -/
theorem measurableSet_rejectLongTripsPolicy (t : ℝ) :
    MeasurableSet (rejectLongTripsPolicy t) := by
  unfold rejectLongTripsPolicy
  exact (measurableSet_Ioi (a := (0 : ℝ))).inter (measurableSet_Iio (a := t))

/-- Canonical short-trip-rejection policies are measurable. -/
theorem measurableSet_rejectShortTripsPolicy (t : ℝ) :
    MeasurableSet (rejectShortTripsPolicy t) := by
  unfold rejectShortTripsPolicy
  exact (measurableSet_Ioi (a := (0 : ℝ))).inter (measurableSet_Ioi (a := t))

/-- Canonical middle-acceptance policies are measurable. -/
theorem measurableSet_acceptMiddleTripsPolicy (lo hi : ℝ) :
    MeasurableSet (acceptMiddleTripsPolicy lo hi) := by
  unfold acceptMiddleTripsPolicy
  exact
    ((measurableSet_Ioi (a := (0 : ℝ))).inter
      (measurableSet_Ioi (a := lo))).inter (measurableSet_Iio (a := hi))

/-- Canonical middle-rejection policies are measurable. -/
theorem measurableSet_rejectMiddleTripsPolicy (lo hi : ℝ) :
    MeasurableSet (rejectMiddleTripsPolicy lo hi) := by
  have htail :
      MeasurableSet (Set.Iio lo ∪ Set.Ioi hi) :=
    (measurableSet_Iio (a := lo)).union (measurableSet_Ioi (a := hi))
  unfold rejectMiddleTripsPolicy
  exact (measurableSet_Ioi (a := (0 : ℝ))).inter htail

/-- Canonical long-trip-rejection policies only accept positive trips. -/
theorem rejectLongTripsPolicy_subset_acceptAll (t : ℝ) :
    rejectLongTripsPolicy t ⊆ acceptAllPolicy := by
  intro τ hτ
  exact hτ.1

/--
Canonical long-trip-rejection policy realizes the endpoint `Q_i` path with
lower endpoint `0`; the open/closed endpoint difference is null for Lebesgue
`withDensity` primitives.
-/
theorem gn21ExitWeightIntegral_rejectLongTripsPolicy_withDensity_eq_endpointQiPath
    (arrivalRate switchIJ switchJI t : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (ht_nonneg : 0 ≤ t) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (rejectLongTripsPolicy t) =
      gn21EndpointQiPath arrivalRate switchIJ 0
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) t := by
  unfold gn21ExitWeightIntegral gn21EndpointQiPath rejectLongTripsPolicy
  rw [intervalIntegral.integral_of_le ht_nonneg]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density)
    hdensity_meas
    (fun τ => gn21SwitchProb switchIJ switchJI τ)
    ((measurableSet_Ioi (a := (0 : ℝ))).inter
      (measurableSet_Iio (a := t)))]
  apply congrArg (fun y => switchIJ + arrivalRate * y)
  rw [integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/--
Canonical long-trip-rejection policy realizes the endpoint `T_i` path with
lower endpoint `0`.
-/
theorem gn21ScaledStateTime_rejectLongTripsPolicy_withDensity_eq_endpointTiPath
    (arrivalRate t : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (ht_nonneg : 0 ≤ t) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (rejectLongTripsPolicy t) =
      gn21EndpointTiPath arrivalRate 0
        (fun τ => (density τ : ℝ)) t := by
  unfold gn21ScaledStateTime singleStateTripTime gn21EndpointTiPath
    rejectLongTripsPolicy
  rw [intervalIntegral.integral_of_le ht_nonneg]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas (fun τ => τ)
    ((measurableSet_Ioi (a := (0 : ℝ))).inter
      (measurableSet_Iio (a := t)))]
  apply congrArg (fun y => 1 + arrivalRate * y)
  rw [integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/--
Canonical long-trip-rejection policy realizes the endpoint `W_i` path with
lower endpoint `0`.
-/
theorem gn21ScaledStateEarning_rejectLongTripsPolicy_withDensity_eq_endpointWiPath
    (arrivalRate t : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (ht_nonneg : 0 ≤ t) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (rejectLongTripsPolicy t) =
      gn21EndpointWiPath arrivalRate 0
        (fun τ => (density τ : ℝ)) payment t := by
  unfold gn21ScaledStateEarning singleStateTripPayment gn21EndpointWiPath
    rejectLongTripsPolicy
  rw [intervalIntegral.integral_of_le ht_nonneg]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas payment
    ((measurableSet_Ioi (a := (0 : ℝ))).inter
      (measurableSet_Iio (a := t)))]
  apply congrArg (fun y => arrivalRate * y)
  rw [integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/--
Any feasible long-trip-rejection-shaped policy realizes the endpoint `Q_i`
path after canonicalizing the policy.
-/
theorem gn21ExitWeightIntegral_rejectsLongTrips_withDensity_eq_endpointQiPath
    (arrivalRate switchIJ switchJI t : ℝ)
    (σ : TripPolicy)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hshape : rejectsLongTrips t σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (ht_nonneg : 0 ≤ t) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI σ =
      gn21EndpointQiPath arrivalRate switchIJ 0
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) t := by
  rw [eq_rejectLongTripsPolicy_of_rejectsLongTrips_of_subset_acceptAll
    hshape hsub]
  exact
    gn21ExitWeightIntegral_rejectLongTripsPolicy_withDensity_eq_endpointQiPath
      arrivalRate switchIJ switchJI t density hdensity_meas ht_nonneg

/--
Any feasible long-trip-rejection-shaped policy realizes the endpoint `T_i`
path after canonicalizing the policy.
-/
theorem gn21ScaledStateTime_rejectsLongTrips_withDensity_eq_endpointTiPath
    (arrivalRate t : ℝ)
    (σ : TripPolicy)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hshape : rejectsLongTrips t σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (ht_nonneg : 0 ≤ t) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate σ =
      gn21EndpointTiPath arrivalRate 0
        (fun τ => (density τ : ℝ)) t := by
  rw [eq_rejectLongTripsPolicy_of_rejectsLongTrips_of_subset_acceptAll
    hshape hsub]
  exact
    gn21ScaledStateTime_rejectLongTripsPolicy_withDensity_eq_endpointTiPath
      arrivalRate t density hdensity_meas ht_nonneg

/--
Any feasible long-trip-rejection-shaped policy realizes the endpoint `W_i`
path after canonicalizing the policy.
-/
theorem gn21ScaledStateEarning_rejectsLongTrips_withDensity_eq_endpointWiPath
    (arrivalRate t : ℝ)
    (σ : TripPolicy)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hshape : rejectsLongTrips t σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (ht_nonneg : 0 ≤ t) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment σ =
      gn21EndpointWiPath arrivalRate 0
        (fun τ => (density τ : ℝ)) payment t := by
  rw [eq_rejectLongTripsPolicy_of_rejectsLongTrips_of_subset_acceptAll
    hshape hsub]
  exact
    gn21ScaledStateEarning_rejectLongTripsPolicy_withDensity_eq_endpointWiPath
      arrivalRate t density payment hdensity_meas ht_nonneg

/--
Canonical short-trip-rejection policy realizes the unbounded tail `Q_i` path
when the cutoff is nonnegative.
-/
theorem gn21ExitWeightIntegral_rejectShortTripsPolicy_withDensity_eq_tailQiPath
    (arrivalRate switchIJ switchJI t : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (ht_nonneg : 0 ≤ t) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (rejectShortTripsPolicy t) =
      gn21TailQiPath arrivalRate switchIJ
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) t := by
  have hpolicy : rejectShortTripsPolicy t = gn21TailPolicy t := by
    ext τ
    constructor
    · intro hτ
      exact hτ.2
    · intro hτ
      exact ⟨lt_of_le_of_lt ht_nonneg hτ, hτ⟩
  rw [hpolicy]
  exact gn21ExitWeightIntegral_tail_withDensity_eq_tailQiPath
    arrivalRate switchIJ switchJI t density hdensity_meas

/--
Canonical short-trip-rejection policy realizes the unbounded tail `T_i` path
when the cutoff is nonnegative.
-/
theorem gn21ScaledStateTime_rejectShortTripsPolicy_withDensity_eq_tailTiPath
    (arrivalRate t : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (ht_nonneg : 0 ≤ t) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (rejectShortTripsPolicy t) =
      gn21TailTiPath arrivalRate (fun τ => (density τ : ℝ)) t := by
  have hpolicy : rejectShortTripsPolicy t = gn21TailPolicy t := by
    ext τ
    constructor
    · intro hτ
      exact hτ.2
    · intro hτ
      exact ⟨lt_of_le_of_lt ht_nonneg hτ, hτ⟩
  rw [hpolicy]
  exact gn21ScaledStateTime_tail_withDensity_eq_tailTiPath
    arrivalRate t density hdensity_meas

/--
Canonical short-trip-rejection policy realizes the unbounded tail `W_i` path
when the cutoff is nonnegative.
-/
theorem gn21ScaledStateEarning_rejectShortTripsPolicy_withDensity_eq_tailWiPath
    (arrivalRate t : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (ht_nonneg : 0 ≤ t) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (rejectShortTripsPolicy t) =
      gn21TailWiPath arrivalRate (fun τ => (density τ : ℝ)) payment t := by
  have hpolicy : rejectShortTripsPolicy t = gn21TailPolicy t := by
    ext τ
    constructor
    · intro hτ
      exact hτ.2
    · intro hτ
      exact ⟨lt_of_le_of_lt ht_nonneg hτ, hτ⟩
  rw [hpolicy]
  exact gn21ScaledStateEarning_tail_withDensity_eq_tailWiPath
    arrivalRate t density payment hdensity_meas

/--
Any feasible short-trip-rejection-shaped policy realizes the tail `Q_i` path
after canonicalizing the policy.
-/
theorem gn21ExitWeightIntegral_rejectsShortTrips_withDensity_eq_tailQiPath
    (arrivalRate switchIJ switchJI t : ℝ)
    (σ : TripPolicy)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hshape : rejectsShortTrips t σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (ht_nonneg : 0 ≤ t) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI σ =
      gn21TailQiPath arrivalRate switchIJ
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) t := by
  rw [eq_rejectShortTripsPolicy_of_rejectsShortTrips_of_subset_acceptAll
    hshape hsub]
  exact
    gn21ExitWeightIntegral_rejectShortTripsPolicy_withDensity_eq_tailQiPath
      arrivalRate switchIJ switchJI t density hdensity_meas ht_nonneg

/--
Any feasible short-trip-rejection-shaped policy realizes the tail `T_i` path
after canonicalizing the policy.
-/
theorem gn21ScaledStateTime_rejectsShortTrips_withDensity_eq_tailTiPath
    (arrivalRate t : ℝ)
    (σ : TripPolicy)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hshape : rejectsShortTrips t σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (ht_nonneg : 0 ≤ t) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate σ =
      gn21TailTiPath arrivalRate (fun τ => (density τ : ℝ)) t := by
  rw [eq_rejectShortTripsPolicy_of_rejectsShortTrips_of_subset_acceptAll
    hshape hsub]
  exact
    gn21ScaledStateTime_rejectShortTripsPolicy_withDensity_eq_tailTiPath
      arrivalRate t density hdensity_meas ht_nonneg

/--
Any feasible short-trip-rejection-shaped policy realizes the tail `W_i` path
after canonicalizing the policy.
-/
theorem gn21ScaledStateEarning_rejectsShortTrips_withDensity_eq_tailWiPath
    (arrivalRate t : ℝ)
    (σ : TripPolicy)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hshape : rejectsShortTrips t σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (ht_nonneg : 0 ≤ t) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment σ =
      gn21TailWiPath arrivalRate
        (fun τ => (density τ : ℝ)) payment t := by
  rw [eq_rejectShortTripsPolicy_of_rejectsShortTrips_of_subset_acceptAll
    hshape hsub]
  exact
    gn21ScaledStateEarning_rejectShortTripsPolicy_withDensity_eq_tailWiPath
      arrivalRate t density payment hdensity_meas ht_nonneg

/--
Canonical middle-acceptance policy realizes the finite lower-endpoint `Q_i`
path when its lower endpoint is nonnegative.
-/
theorem gn21ExitWeightIntegral_acceptMiddleTripsPolicy_withDensity_eq_lowerEndpointQiPath
    (arrivalRate switchIJ switchJI lo hi : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (acceptMiddleTripsPolicy lo hi) =
      gn21LowerEndpointQiPath arrivalRate switchIJ hi
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) lo := by
  have hpolicy : acceptMiddleTripsPolicy lo hi = Set.Ioo lo hi := by
    ext τ
    constructor
    · intro hτ
      exact ⟨hτ.1.2, hτ.2⟩
    · intro hτ
      exact ⟨⟨lt_of_le_of_lt hlo_nonneg hτ.1, hτ.1⟩, hτ.2⟩
  unfold gn21ExitWeightIntegral gn21LowerEndpointQiPath
  rw [hpolicy]
  rw [intervalIntegral.integral_of_le hle]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density)
    hdensity_meas
    (fun τ => gn21SwitchProb switchIJ switchJI τ)
    measurableSet_Ioo]
  apply congrArg (fun y => switchIJ + arrivalRate * y)
  rw [integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/--
Canonical middle-acceptance policy realizes the finite lower-endpoint `T_i`
path when its lower endpoint is nonnegative.
-/
theorem gn21ScaledStateTime_acceptMiddleTripsPolicy_withDensity_eq_lowerEndpointTiPath
    (arrivalRate lo hi : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (acceptMiddleTripsPolicy lo hi) =
      gn21LowerEndpointTiPath arrivalRate hi
        (fun τ => (density τ : ℝ)) lo := by
  have hpolicy : acceptMiddleTripsPolicy lo hi = Set.Ioo lo hi := by
    ext τ
    constructor
    · intro hτ
      exact ⟨hτ.1.2, hτ.2⟩
    · intro hτ
      exact ⟨⟨lt_of_le_of_lt hlo_nonneg hτ.1, hτ.1⟩, hτ.2⟩
  unfold gn21ScaledStateTime singleStateTripTime gn21LowerEndpointTiPath
  rw [hpolicy]
  rw [intervalIntegral.integral_of_le hle]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas (fun τ => τ)
    measurableSet_Ioo]
  apply congrArg (fun y => 1 + arrivalRate * y)
  rw [integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/--
Canonical middle-acceptance policy realizes the finite lower-endpoint `W_i`
path when its lower endpoint is nonnegative.
-/
theorem gn21ScaledStateEarning_acceptMiddleTripsPolicy_withDensity_eq_lowerEndpointWiPath
    (arrivalRate lo hi : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (acceptMiddleTripsPolicy lo hi) =
      gn21LowerEndpointWiPath arrivalRate hi
        (fun τ => (density τ : ℝ)) payment lo := by
  have hpolicy : acceptMiddleTripsPolicy lo hi = Set.Ioo lo hi := by
    ext τ
    constructor
    · intro hτ
      exact ⟨hτ.1.2, hτ.2⟩
    · intro hτ
      exact ⟨⟨lt_of_le_of_lt hlo_nonneg hτ.1, hτ.1⟩, hτ.2⟩
  unfold gn21ScaledStateEarning singleStateTripPayment
    gn21LowerEndpointWiPath
  rw [hpolicy]
  rw [intervalIntegral.integral_of_le hle]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas payment measurableSet_Ioo]
  apply congrArg (fun y => arrivalRate * y)
  rw [integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro τ _hτ
  simp [Algebra.smul_def, mul_comm]

/--
Any feasible middle-acceptance-shaped policy realizes the finite
lower-endpoint `Q_i` path after canonicalizing the policy.
-/
theorem gn21ExitWeightIntegral_acceptsMiddleTrips_withDensity_eq_lowerEndpointQiPath
    (arrivalRate switchIJ switchJI lo hi : ℝ)
    (σ : TripPolicy)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hshape : acceptsMiddleTrips lo hi σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI σ =
      gn21LowerEndpointQiPath arrivalRate switchIJ hi
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) lo := by
  rw [eq_acceptMiddleTripsPolicy_of_acceptsMiddleTrips_of_subset_acceptAll
    hshape hsub]
  exact
    gn21ExitWeightIntegral_acceptMiddleTripsPolicy_withDensity_eq_lowerEndpointQiPath
      arrivalRate switchIJ switchJI lo hi density hdensity_meas
      hlo_nonneg hle

/--
Any feasible middle-acceptance-shaped policy realizes the finite
lower-endpoint `T_i` path after canonicalizing the policy.
-/
theorem gn21ScaledStateTime_acceptsMiddleTrips_withDensity_eq_lowerEndpointTiPath
    (arrivalRate lo hi : ℝ)
    (σ : TripPolicy)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hshape : acceptsMiddleTrips lo hi σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate σ =
      gn21LowerEndpointTiPath arrivalRate hi
        (fun τ => (density τ : ℝ)) lo := by
  rw [eq_acceptMiddleTripsPolicy_of_acceptsMiddleTrips_of_subset_acceptAll
    hshape hsub]
  exact
    gn21ScaledStateTime_acceptMiddleTripsPolicy_withDensity_eq_lowerEndpointTiPath
      arrivalRate lo hi density hdensity_meas hlo_nonneg hle

/--
Any feasible middle-acceptance-shaped policy realizes the finite
lower-endpoint `W_i` path after canonicalizing the policy.
-/
theorem gn21ScaledStateEarning_acceptsMiddleTrips_withDensity_eq_lowerEndpointWiPath
    (arrivalRate lo hi : ℝ)
    (σ : TripPolicy)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hshape : acceptsMiddleTrips lo hi σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment σ =
      gn21LowerEndpointWiPath arrivalRate hi
        (fun τ => (density τ : ℝ)) payment lo := by
  rw [eq_acceptMiddleTripsPolicy_of_acceptsMiddleTrips_of_subset_acceptAll
    hshape hsub]
  exact
    gn21ScaledStateEarning_acceptMiddleTripsPolicy_withDensity_eq_lowerEndpointWiPath
      arrivalRate lo hi density payment hdensity_meas hlo_nonneg hle

/--
Canonical middle-rejection policy realizes the two-piece `Q_i` path: a short
interval `(0,lo)` plus an unbounded tail `(hi,∞)`.
-/
theorem gn21ExitWeightIntegral_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleQiPath
    (arrivalRate switchIJ switchJI lo hi : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi)
    (hq_short_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switchIJ switchJI τ * (density τ : ℝ))
        (Set.Ioo (0 : ℝ) lo) volume)
    (hq_tail_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switchIJ switchJI τ * (density τ : ℝ))
        (Set.Ioi hi) volume) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (rejectMiddleTripsPolicy lo hi) =
      gn21RejectMiddleQiPath arrivalRate switchIJ
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) lo hi := by
  have hhi_nonneg : 0 ≤ hi := le_trans hlo_nonneg hle
  have hpolicy :
      rejectMiddleTripsPolicy lo hi =
        Set.Ioo (0 : ℝ) lo ∪ Set.Ioi hi := by
    ext τ
    constructor
    · intro hτ
      rcases hτ.2 with hshort | htail
      · exact Or.inl ⟨hτ.1, hshort⟩
      · exact Or.inr htail
    · intro hτ
      rcases hτ with hshort | htail
      · exact ⟨hshort.1, Or.inl hshort.2⟩
      · exact ⟨lt_of_le_of_lt hhi_nonneg htail, Or.inr htail⟩
  have hmeas_union :
      MeasurableSet (Set.Ioo (0 : ℝ) lo ∪ Set.Ioi hi) :=
    (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) lo)).union
      (measurableSet_Ioi (a := hi))
  have hdisjoint :
      Disjoint (Set.Ioo (0 : ℝ) lo) (Set.Ioi hi) := by
    exact Set.disjoint_left.2 (by
      intro τ hshort htail
      exact (lt_irrefl τ) ((lt_of_lt_of_le hshort.2 hle).trans htail))
  unfold gn21ExitWeightIntegral gn21RejectMiddleQiPath
  rw [hpolicy]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density)
    hdensity_meas
    (fun τ => gn21SwitchProb switchIJ switchJI τ)
    hmeas_union]
  apply congrArg (fun y => switchIJ + arrivalRate * y)
  have hcongr_union :
      (∫ τ in Set.Ioo (0 : ℝ) lo ∪ Set.Ioi hi,
          density τ • gn21SwitchProb switchIJ switchJI τ) =
        ∫ τ in Set.Ioo (0 : ℝ) lo ∪ Set.Ioi hi,
          gn21SwitchProb switchIJ switchJI τ * (density τ : ℝ) := by
    apply setIntegral_congr_fun hmeas_union
    intro τ _hτ
    simp [NNReal.smul_def, smul_eq_mul, mul_comm]
  rw [hcongr_union]
  rw [setIntegral_union hdisjoint (measurableSet_Ioi (a := hi))
    hq_short_int hq_tail_int]
  rw [intervalIntegral.integral_of_le hlo_nonneg]
  rw [integral_Ioc_eq_integral_Ioo]

/--
Canonical middle-rejection policy realizes the two-piece `T_i` path: a short
interval `(0,lo)` plus an unbounded tail `(hi,∞)`.
-/
theorem gn21ScaledStateTime_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleTiPath
    (arrivalRate lo hi : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi)
    (ht_short_int :
      IntegrableOn (fun τ => τ * (density τ : ℝ))
        (Set.Ioo (0 : ℝ) lo) volume)
    (ht_tail_int :
      IntegrableOn (fun τ => τ * (density τ : ℝ)) (Set.Ioi hi)
        volume) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (rejectMiddleTripsPolicy lo hi) =
      gn21RejectMiddleTiPath arrivalRate
        (fun τ => (density τ : ℝ)) lo hi := by
  have hhi_nonneg : 0 ≤ hi := le_trans hlo_nonneg hle
  have hpolicy :
      rejectMiddleTripsPolicy lo hi =
        Set.Ioo (0 : ℝ) lo ∪ Set.Ioi hi := by
    ext τ
    constructor
    · intro hτ
      rcases hτ.2 with hshort | htail
      · exact Or.inl ⟨hτ.1, hshort⟩
      · exact Or.inr htail
    · intro hτ
      rcases hτ with hshort | htail
      · exact ⟨hshort.1, Or.inl hshort.2⟩
      · exact ⟨lt_of_le_of_lt hhi_nonneg htail, Or.inr htail⟩
  have hmeas_union :
      MeasurableSet (Set.Ioo (0 : ℝ) lo ∪ Set.Ioi hi) :=
    (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) lo)).union
      (measurableSet_Ioi (a := hi))
  have hdisjoint :
      Disjoint (Set.Ioo (0 : ℝ) lo) (Set.Ioi hi) := by
    exact Set.disjoint_left.2 (by
      intro τ hshort htail
      exact (lt_irrefl τ) ((lt_of_lt_of_le hshort.2 hle).trans htail))
  unfold gn21ScaledStateTime singleStateTripTime gn21RejectMiddleTiPath
  rw [hpolicy]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas (fun τ => τ)
    hmeas_union]
  apply congrArg (fun y => 1 + arrivalRate * y)
  have hcongr_union :
      (∫ τ in Set.Ioo (0 : ℝ) lo ∪ Set.Ioi hi,
          density τ • τ) =
        ∫ τ in Set.Ioo (0 : ℝ) lo ∪ Set.Ioi hi,
          τ * (density τ : ℝ) := by
    apply setIntegral_congr_fun hmeas_union
    intro τ _hτ
    simp [NNReal.smul_def, smul_eq_mul, mul_comm]
  rw [hcongr_union]
  rw [setIntegral_union hdisjoint (measurableSet_Ioi (a := hi))
    ht_short_int ht_tail_int]
  rw [intervalIntegral.integral_of_le hlo_nonneg]
  rw [integral_Ioc_eq_integral_Ioo]

/--
Canonical middle-rejection policy realizes the two-piece `W_i` path: a short
interval `(0,lo)` plus an unbounded tail `(hi,∞)`.
-/
theorem gn21ScaledStateEarning_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleWiPath
    (arrivalRate lo hi : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi)
    (hw_short_int :
      IntegrableOn (fun τ => payment τ * (density τ : ℝ))
        (Set.Ioo (0 : ℝ) lo) volume)
    (hw_tail_int :
      IntegrableOn (fun τ => payment τ * (density τ : ℝ)) (Set.Ioi hi)
        volume) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (rejectMiddleTripsPolicy lo hi) =
      gn21RejectMiddleWiPath arrivalRate
        (fun τ => (density τ : ℝ)) payment lo hi := by
  have hhi_nonneg : 0 ≤ hi := le_trans hlo_nonneg hle
  have hpolicy :
      rejectMiddleTripsPolicy lo hi =
        Set.Ioo (0 : ℝ) lo ∪ Set.Ioi hi := by
    ext τ
    constructor
    · intro hτ
      rcases hτ.2 with hshort | htail
      · exact Or.inl ⟨hτ.1, hshort⟩
      · exact Or.inr htail
    · intro hτ
      rcases hτ with hshort | htail
      · exact ⟨hshort.1, Or.inl hshort.2⟩
      · exact ⟨lt_of_le_of_lt hhi_nonneg htail, Or.inr htail⟩
  have hmeas_union :
      MeasurableSet (Set.Ioo (0 : ℝ) lo ∪ Set.Ioi hi) :=
    (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) lo)).union
      (measurableSet_Ioi (a := hi))
  have hdisjoint :
      Disjoint (Set.Ioo (0 : ℝ) lo) (Set.Ioi hi) := by
    exact Set.disjoint_left.2 (by
      intro τ hshort htail
      exact (lt_irrefl τ) ((lt_of_lt_of_le hshort.2 hle).trans htail))
  unfold gn21ScaledStateEarning singleStateTripPayment gn21RejectMiddleWiPath
  rw [hpolicy]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas payment hmeas_union]
  apply congrArg (fun y => arrivalRate * y)
  have hcongr_union :
      (∫ τ in Set.Ioo (0 : ℝ) lo ∪ Set.Ioi hi,
          density τ • payment τ) =
        ∫ τ in Set.Ioo (0 : ℝ) lo ∪ Set.Ioi hi,
          payment τ * (density τ : ℝ) := by
    apply setIntegral_congr_fun hmeas_union
    intro τ _hτ
    simp [NNReal.smul_def, smul_eq_mul, mul_comm]
  rw [hcongr_union]
  rw [setIntegral_union hdisjoint (measurableSet_Ioi (a := hi))
    hw_short_int hw_tail_int]
  rw [intervalIntegral.integral_of_le hlo_nonneg]
  rw [integral_Ioc_eq_integral_Ioo]

/--
Any feasible middle-rejection-shaped policy realizes the two-piece `Q_i` path
after canonicalizing the policy.
-/
theorem gn21ExitWeightIntegral_rejectsMiddleTrips_withDensity_eq_rejectMiddleQiPath
    (arrivalRate switchIJ switchJI lo hi : ℝ)
    (σ : TripPolicy)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hshape : rejectsMiddleTrips lo hi σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi)
    (hq_short_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switchIJ switchJI τ * (density τ : ℝ))
        (Set.Ioo (0 : ℝ) lo) volume)
    (hq_tail_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switchIJ switchJI τ * (density τ : ℝ))
        (Set.Ioi hi) volume) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI σ =
      gn21RejectMiddleQiPath arrivalRate switchIJ
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) lo hi := by
  rw [eq_rejectMiddleTripsPolicy_of_rejectsMiddleTrips_of_subset_acceptAll
    hshape hsub]
  exact
    gn21ExitWeightIntegral_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleQiPath
      arrivalRate switchIJ switchJI lo hi density hdensity_meas
      hlo_nonneg hle hq_short_int hq_tail_int

/--
Any feasible middle-rejection-shaped policy realizes the two-piece `T_i` path
after canonicalizing the policy.
-/
theorem gn21ScaledStateTime_rejectsMiddleTrips_withDensity_eq_rejectMiddleTiPath
    (arrivalRate lo hi : ℝ)
    (σ : TripPolicy)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hshape : rejectsMiddleTrips lo hi σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi)
    (ht_short_int :
      IntegrableOn (fun τ => τ * (density τ : ℝ))
        (Set.Ioo (0 : ℝ) lo) volume)
    (ht_tail_int :
      IntegrableOn (fun τ => τ * (density τ : ℝ)) (Set.Ioi hi)
        volume) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate σ =
      gn21RejectMiddleTiPath arrivalRate
        (fun τ => (density τ : ℝ)) lo hi := by
  rw [eq_rejectMiddleTripsPolicy_of_rejectsMiddleTrips_of_subset_acceptAll
    hshape hsub]
  exact
    gn21ScaledStateTime_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleTiPath
      arrivalRate lo hi density hdensity_meas hlo_nonneg hle
      ht_short_int ht_tail_int

/--
Any feasible middle-rejection-shaped policy realizes the two-piece `W_i` path
after canonicalizing the policy.
-/
theorem gn21ScaledStateEarning_rejectsMiddleTrips_withDensity_eq_rejectMiddleWiPath
    (arrivalRate lo hi : ℝ)
    (σ : TripPolicy)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hshape : rejectsMiddleTrips lo hi σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi)
    (hw_short_int :
      IntegrableOn (fun τ => payment τ * (density τ : ℝ))
        (Set.Ioo (0 : ℝ) lo) volume)
    (hw_tail_int :
      IntegrableOn (fun τ => payment τ * (density τ : ℝ)) (Set.Ioi hi)
        volume) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment σ =
      gn21RejectMiddleWiPath arrivalRate
        (fun τ => (density τ : ℝ)) payment lo hi := by
  rw [eq_rejectMiddleTripsPolicy_of_rejectsMiddleTrips_of_subset_acceptAll
    hshape hsub]
  exact
    gn21ScaledStateEarning_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleWiPath
      arrivalRate lo hi density payment hdensity_meas hlo_nonneg hle
      hw_short_int hw_tail_int

/-- Canonical short-trip-rejection policies only accept positive trips. -/
theorem rejectShortTripsPolicy_subset_acceptAll (t : ℝ) :
    rejectShortTripsPolicy t ⊆ acceptAllPolicy := by
  intro τ hτ
  exact hτ.1

/-- Canonical middle-acceptance policies only accept positive trips. -/
theorem acceptMiddleTripsPolicy_subset_acceptAll (lo hi : ℝ) :
    acceptMiddleTripsPolicy lo hi ⊆ acceptAllPolicy := by
  intro τ hτ
  exact hτ.1.1

/-- Canonical middle-rejection policies only accept positive trips. -/
theorem rejectMiddleTripsPolicy_subset_acceptAll (lo hi : ℝ) :
    rejectMiddleTripsPolicy lo hi ⊆ acceptAllPolicy := by
  intro τ hτ
  exact hτ.1

/-- Canonical short-trip-rejection policies have nonzero Lebesgue volume. -/
theorem volume_rejectShortTripsPolicy_ne_zero (t : ℝ) :
    volume (rejectShortTripsPolicy t) ≠ 0 := by
  intro hzero
  have hsubset : Set.Ioi (max t 0) ⊆ rejectShortTripsPolicy t := by
    intro τ hτ
    have h0 : 0 < τ := lt_of_le_of_lt (le_max_right t 0) hτ
    have ht : t < τ := lt_of_le_of_lt (le_max_left t 0) hτ
    exact ⟨h0, ht⟩
  have hle : volume (Set.Ioi (max t 0)) ≤
      volume (rejectShortTripsPolicy t) :=
    measure_mono hsubset
  have hbad : ¬ ((⊤ : ℝ≥0∞) ≤ 0) := by simp
  exact hbad (by simpa [Real.volume_Ioi, hzero] using hle)

/--
Positive NNReal density on any feasible short-trip-rejection-shaped policy
gives positive real trip mass under a finite `withDensity` measure.
-/
theorem singleStateTripMass_rejectsShortTrips_withDensity_pos_of_pos_on
    (density : TripLength → NNReal)
    (hdensity_meas : Measurable density)
    (t : ℝ)
    (σ : TripPolicy)
    (hshape : rejectsShortTrips t σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞)) σ ≠ ∞)
    (hpos : ∀ τ, τ ∈ σ → density τ ≠ 0) :
    0 <
      singleStateTripMass
        (volume.withDensity fun τ => (density τ : ℝ≥0∞)) σ := by
  have hσ_eq : σ = rejectShortTripsPolicy t :=
    eq_rejectShortTripsPolicy_of_rejectsShortTrips_of_subset_acceptAll
      hshape hsub
  have hσ_meas : MeasurableSet σ := by
    rw [hσ_eq]
    exact measurableSet_rejectShortTripsPolicy t
  have hvolume_ne_zero : volume σ ≠ 0 := by
    rw [hσ_eq]
    exact volume_rejectShortTripsPolicy_ne_zero t
  refine
    singleStateTripMass_withDensity_pos_of_pos_on
      (fun τ => (density τ : ℝ≥0∞))
      (measurable_coe_nnreal_ennreal.comp hdensity_meas)
      hσ_meas hvolume_ne_zero hfinite ?_
  intro τ hτ
  simpa using hpos τ hτ

/-- Rightward movement of the lower cutoff in a middle-rejection policy. -/
def gn21RejectMiddleLoReplacement (lo hi : ℝ) (ε : ℝ) : TripPolicy :=
  rejectMiddleTripsPolicy (lo + ε) hi

/-- Leftward movement of the upper cutoff in a middle-rejection policy. -/
def gn21RejectMiddleHiReplacement (lo hi : ℝ) (ε : ℝ) : TripPolicy :=
  rejectMiddleTripsPolicy lo (hi - ε)

/-- Lower-cutoff middle-rejection replacements are measurable. -/
theorem measurableSet_gn21RejectMiddleLoReplacement (lo hi ε : ℝ) :
    MeasurableSet (gn21RejectMiddleLoReplacement lo hi ε) := by
  simpa [gn21RejectMiddleLoReplacement] using
    measurableSet_rejectMiddleTripsPolicy (lo + ε) hi

/-- Upper-cutoff middle-rejection replacements are measurable. -/
theorem measurableSet_gn21RejectMiddleHiReplacement (lo hi ε : ℝ) :
    MeasurableSet (gn21RejectMiddleHiReplacement lo hi ε) := by
  simpa [gn21RejectMiddleHiReplacement] using
    measurableSet_rejectMiddleTripsPolicy lo (hi - ε)

/-- Lower-cutoff replacements retain the middle-rejection shape. -/
theorem rejectsMiddleTrips_gn21RejectMiddleLoReplacement (lo hi ε : ℝ) :
    rejectsMiddleTrips (lo + ε) hi
      (gn21RejectMiddleLoReplacement lo hi ε) := by
  simpa [gn21RejectMiddleLoReplacement] using
    rejectsMiddleTrips_rejectMiddleTripsPolicy (lo + ε) hi

/-- Upper-cutoff replacements retain the middle-rejection shape. -/
theorem rejectsMiddleTrips_gn21RejectMiddleHiReplacement (lo hi ε : ℝ) :
    rejectsMiddleTrips lo (hi - ε)
      (gn21RejectMiddleHiReplacement lo hi ε) := by
  simpa [gn21RejectMiddleHiReplacement] using
    rejectsMiddleTrips_rejectMiddleTripsPolicy lo (hi - ε)

/-- Lower-cutoff middle-rejection replacements are feasible. -/
theorem gn21RejectMiddleLoReplacement_subset_acceptAllPolicy
    (lo hi ε : ℝ) :
    gn21RejectMiddleLoReplacement lo hi ε ⊆ acceptAllPolicy := by
  simpa [gn21RejectMiddleLoReplacement] using
    rejectMiddleTripsPolicy_subset_acceptAll (lo + ε) hi

/-- Upper-cutoff middle-rejection replacements are feasible. -/
theorem gn21RejectMiddleHiReplacement_subset_acceptAllPolicy
    (lo hi ε : ℝ) :
    gn21RejectMiddleHiReplacement lo hi ε ⊆ acceptAllPolicy := by
  simpa [gn21RejectMiddleHiReplacement] using
    rejectMiddleTripsPolicy_subset_acceptAll lo (hi - ε)

/-- Middle-rejection policies have nonzero Lebesgue volume because they include a tail. -/
theorem volume_rejectMiddleTripsPolicy_ne_zero (lo hi : ℝ) :
    volume (rejectMiddleTripsPolicy lo hi) ≠ 0 := by
  intro hzero
  have hsubset : Set.Ioi (max hi 0) ⊆ rejectMiddleTripsPolicy lo hi := by
    intro τ hτ
    have h0 : 0 < τ := lt_of_le_of_lt (le_max_right hi 0) hτ
    have hhi : hi < τ := lt_of_le_of_lt (le_max_left hi 0) hτ
    exact ⟨h0, Or.inr hhi⟩
  have hle : volume (Set.Ioi (max hi 0)) ≤
      volume (rejectMiddleTripsPolicy lo hi) :=
    measure_mono hsubset
  have hbad : ¬ ((⊤ : ℝ≥0∞) ≤ 0) := by simp
  exact hbad (by simpa [Real.volume_Ioi, hzero] using hle)

/-- Lower-cutoff middle-rejection replacements have nonzero Lebesgue volume. -/
theorem volume_gn21RejectMiddleLoReplacement_ne_zero (lo hi ε : ℝ) :
    volume (gn21RejectMiddleLoReplacement lo hi ε) ≠ 0 := by
  simpa [gn21RejectMiddleLoReplacement] using
    volume_rejectMiddleTripsPolicy_ne_zero (lo + ε) hi

/-- Upper-cutoff middle-rejection replacements have nonzero Lebesgue volume. -/
theorem volume_gn21RejectMiddleHiReplacement_ne_zero (lo hi ε : ℝ) :
    volume (gn21RejectMiddleHiReplacement lo hi ε) ≠ 0 := by
  simpa [gn21RejectMiddleHiReplacement] using
    volume_rejectMiddleTripsPolicy_ne_zero lo (hi - ε)

/--
Positive NNReal density on a concrete lower-cutoff middle-rejection
replacement gives positive real trip mass under a finite `withDensity` measure.
-/
theorem singleStateTripMass_rejectMiddleLoReplacement_withDensity_pos_of_pos_on
    (density : TripLength → NNReal)
    (hdensity_meas : Measurable density)
    (lo hi ε : ℝ)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21RejectMiddleLoReplacement lo hi ε) ≠ ∞)
    (hpos :
      ∀ τ, τ ∈ gn21RejectMiddleLoReplacement lo hi ε → density τ ≠ 0) :
    0 <
      singleStateTripMass
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21RejectMiddleLoReplacement lo hi ε) := by
  refine
    singleStateTripMass_withDensity_pos_of_pos_on
      (fun τ => (density τ : ℝ≥0∞))
      (measurable_coe_nnreal_ennreal.comp hdensity_meas)
      (measurableSet_gn21RejectMiddleLoReplacement lo hi ε)
      (volume_gn21RejectMiddleLoReplacement_ne_zero lo hi ε)
      hfinite ?_
  intro τ hτ
  simpa using hpos τ hτ

/--
Positive NNReal density on a concrete upper-cutoff middle-rejection
replacement gives positive real trip mass under a finite `withDensity` measure.
-/
theorem singleStateTripMass_rejectMiddleHiReplacement_withDensity_pos_of_pos_on
    (density : TripLength → NNReal)
    (hdensity_meas : Measurable density)
    (lo hi ε : ℝ)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21RejectMiddleHiReplacement lo hi ε) ≠ ∞)
    (hpos :
      ∀ τ, τ ∈ gn21RejectMiddleHiReplacement lo hi ε → density τ ≠ 0) :
    0 <
      singleStateTripMass
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21RejectMiddleHiReplacement lo hi ε) := by
  refine
    singleStateTripMass_withDensity_pos_of_pos_on
      (fun τ => (density τ : ℝ≥0∞))
      (measurable_coe_nnreal_ennreal.comp hdensity_meas)
      (measurableSet_gn21RejectMiddleHiReplacement lo hi ε)
      (volume_gn21RejectMiddleHiReplacement_ne_zero lo hi ε)
      hfinite ?_
  intro τ hτ
  simpa using hpos τ hτ

/--
Positive NNReal density on any feasible middle-rejection-shaped policy gives
positive real trip mass under a finite `withDensity` measure.
-/
theorem singleStateTripMass_rejectsMiddleTrips_withDensity_pos_of_pos_on
    (density : TripLength → NNReal)
    (hdensity_meas : Measurable density)
    (lo hi : ℝ)
    (σ : TripPolicy)
    (hshape : rejectsMiddleTrips lo hi σ)
    (hsub : σ ⊆ acceptAllPolicy)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞)) σ ≠ ∞)
    (hpos : ∀ τ, τ ∈ σ → density τ ≠ 0) :
    0 <
      singleStateTripMass
        (volume.withDensity fun τ => (density τ : ℝ≥0∞)) σ := by
  have hσ_eq : σ = rejectMiddleTripsPolicy lo hi :=
    eq_rejectMiddleTripsPolicy_of_rejectsMiddleTrips_of_subset_acceptAll
      hshape hsub
  have hσ_meas : MeasurableSet σ := by
    rw [hσ_eq]
    exact measurableSet_rejectMiddleTripsPolicy lo hi
  have hvolume_ne_zero : volume σ ≠ 0 := by
    rw [hσ_eq]
    exact volume_rejectMiddleTripsPolicy_ne_zero lo hi
  refine
    singleStateTripMass_withDensity_pos_of_pos_on
      (fun τ => (density τ : ℝ≥0∞))
      (measurable_coe_nnreal_ennreal.comp hdensity_meas)
      hσ_meas hvolume_ne_zero hfinite ?_
  intro τ hτ
  simpa using hpos τ hτ

/--
`Q_i` realization along a lower-cutoff movement of a middle-rejection policy.
-/
theorem gn21ExitWeightIntegral_rejectMiddleLoReplacement_withDensity_eq_rejectMiddleQiPath
    (arrivalRate switchIJ switchJI lo hi ε : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hloε_nonneg : 0 ≤ lo + ε)
    (hle : lo + ε ≤ hi)
    (hq_short_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switchIJ switchJI τ * (density τ : ℝ))
        (Set.Ioo (0 : ℝ) (lo + ε)) volume)
    (hq_tail_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switchIJ switchJI τ * (density τ : ℝ))
        (Set.Ioi hi) volume) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (gn21RejectMiddleLoReplacement lo hi ε) =
      gn21RejectMiddleQiPath arrivalRate switchIJ
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) (lo + ε) hi := by
  simpa [gn21RejectMiddleLoReplacement] using
    gn21ExitWeightIntegral_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleQiPath
      arrivalRate switchIJ switchJI (lo + ε) hi density hdensity_meas
      hloε_nonneg hle hq_short_int hq_tail_int

/--
`T_i` realization along a lower-cutoff movement of a middle-rejection policy.
-/
theorem gn21ScaledStateTime_rejectMiddleLoReplacement_withDensity_eq_rejectMiddleTiPath
    (arrivalRate lo hi ε : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hloε_nonneg : 0 ≤ lo + ε)
    (hle : lo + ε ≤ hi)
    (ht_short_int :
      IntegrableOn (fun τ => τ * (density τ : ℝ))
        (Set.Ioo (0 : ℝ) (lo + ε)) volume)
    (ht_tail_int :
      IntegrableOn (fun τ => τ * (density τ : ℝ)) (Set.Ioi hi)
        volume) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (gn21RejectMiddleLoReplacement lo hi ε) =
      gn21RejectMiddleTiPath arrivalRate
        (fun τ => (density τ : ℝ)) (lo + ε) hi := by
  simpa [gn21RejectMiddleLoReplacement] using
    gn21ScaledStateTime_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleTiPath
      arrivalRate (lo + ε) hi density hdensity_meas hloε_nonneg hle
      ht_short_int ht_tail_int

/--
`W_i` realization along a lower-cutoff movement of a middle-rejection policy.
-/
theorem gn21ScaledStateEarning_rejectMiddleLoReplacement_withDensity_eq_rejectMiddleWiPath
    (arrivalRate lo hi ε : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hloε_nonneg : 0 ≤ lo + ε)
    (hle : lo + ε ≤ hi)
    (hw_short_int :
      IntegrableOn (fun τ => payment τ * (density τ : ℝ))
        (Set.Ioo (0 : ℝ) (lo + ε)) volume)
    (hw_tail_int :
      IntegrableOn (fun τ => payment τ * (density τ : ℝ)) (Set.Ioi hi)
        volume) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (gn21RejectMiddleLoReplacement lo hi ε) =
      gn21RejectMiddleWiPath arrivalRate
        (fun τ => (density τ : ℝ)) payment (lo + ε) hi := by
  simpa [gn21RejectMiddleLoReplacement] using
    gn21ScaledStateEarning_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleWiPath
      arrivalRate (lo + ε) hi density payment hdensity_meas hloε_nonneg hle
      hw_short_int hw_tail_int

/--
`Q_i` realization along an upper-cutoff movement of a middle-rejection policy.
-/
theorem gn21ExitWeightIntegral_rejectMiddleHiReplacement_withDensity_eq_rejectMiddleQiPath
    (arrivalRate switchIJ switchJI lo hi ε : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi - ε)
    (hq_short_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switchIJ switchJI τ * (density τ : ℝ))
        (Set.Ioo (0 : ℝ) lo) volume)
    (hq_tail_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switchIJ switchJI τ * (density τ : ℝ))
        (Set.Ioi (hi - ε)) volume) :
    gn21ExitWeightIntegral
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (gn21RejectMiddleHiReplacement lo hi ε) =
      gn21RejectMiddleQiPath arrivalRate switchIJ
        (fun τ => (density τ : ℝ))
        (gn21SwitchProb switchIJ switchJI) lo (hi - ε) := by
  simpa [gn21RejectMiddleHiReplacement] using
    gn21ExitWeightIntegral_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleQiPath
      arrivalRate switchIJ switchJI lo (hi - ε) density hdensity_meas
      hlo_nonneg hle hq_short_int hq_tail_int

/--
`T_i` realization along an upper-cutoff movement of a middle-rejection policy.
-/
theorem gn21ScaledStateTime_rejectMiddleHiReplacement_withDensity_eq_rejectMiddleTiPath
    (arrivalRate lo hi ε : ℝ)
    (density : ℝ → NNReal)
    (hdensity_meas : Measurable density)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi - ε)
    (ht_short_int :
      IntegrableOn (fun τ => τ * (density τ : ℝ))
        (Set.Ioo (0 : ℝ) lo) volume)
    (ht_tail_int :
      IntegrableOn (fun τ => τ * (density τ : ℝ)) (Set.Ioi (hi - ε))
        volume) :
    gn21ScaledStateTime
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate
        (gn21RejectMiddleHiReplacement lo hi ε) =
      gn21RejectMiddleTiPath arrivalRate
        (fun τ => (density τ : ℝ)) lo (hi - ε) := by
  simpa [gn21RejectMiddleHiReplacement] using
    gn21ScaledStateTime_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleTiPath
      arrivalRate lo (hi - ε) density hdensity_meas hlo_nonneg hle
      ht_short_int ht_tail_int

/--
`W_i` realization along an upper-cutoff movement of a middle-rejection policy.
-/
theorem gn21ScaledStateEarning_rejectMiddleHiReplacement_withDensity_eq_rejectMiddleWiPath
    (arrivalRate lo hi ε : ℝ)
    (density : ℝ → NNReal)
    (payment : PricingFunction)
    (hdensity_meas : Measurable density)
    (hlo_nonneg : 0 ≤ lo)
    (hle : lo ≤ hi - ε)
    (hw_short_int :
      IntegrableOn (fun τ => payment τ * (density τ : ℝ))
        (Set.Ioo (0 : ℝ) lo) volume)
    (hw_tail_int :
      IntegrableOn (fun τ => payment τ * (density τ : ℝ))
        (Set.Ioi (hi - ε)) volume) :
    gn21ScaledStateEarning
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalRate payment
        (gn21RejectMiddleHiReplacement lo hi ε) =
      gn21RejectMiddleWiPath arrivalRate
        (fun τ => (density τ : ℝ)) payment lo (hi - ε) := by
  simpa [gn21RejectMiddleHiReplacement] using
    gn21ScaledStateEarning_rejectMiddleTripsPolicy_withDensity_eq_rejectMiddleWiPath
      arrivalRate lo (hi - ε) density payment hdensity_meas hlo_nonneg hle
      hw_short_int hw_tail_int

/-- Accept-all has Lemma 5's positive-derivative policy form. -/
theorem lemma5PolicyForm_positive_acceptAllPolicy :
    lemma5PolicyForm .positive acceptAllPolicy := by
  intro τ hτ
  exact hτ

/-- The canonical short-trip-rejection policy has Lemma 5's increasing form. -/
theorem lemma5PolicyForm_strictlyIncreasing_rejectShortTripsPolicy (t : ℝ) :
    lemma5PolicyForm .strictlyIncreasing (rejectShortTripsPolicy t) := by
  exact ⟨t, rejectsShortTrips_rejectShortTripsPolicy t⟩

/-- The canonical long-trip-rejection policy has Lemma 5's decreasing form. -/
theorem lemma5PolicyForm_strictlyDecreasing_rejectLongTripsPolicy (t : ℝ) :
    lemma5PolicyForm .strictlyDecreasing (rejectLongTripsPolicy t) := by
  exact ⟨t, rejectsLongTrips_rejectLongTripsPolicy t⟩

/-- The canonical middle-rejection policy has Lemma 5's quasi-convex form. -/
theorem lemma5PolicyForm_strictlyQuasiConvex_rejectMiddleTripsPolicy (lo hi : ℝ) :
    lemma5PolicyForm .strictlyQuasiConvex (rejectMiddleTripsPolicy lo hi) := by
  exact ⟨lo, hi, rejectsMiddleTrips_rejectMiddleTripsPolicy lo hi⟩

/-- The canonical middle-acceptance policy has Lemma 5's quasi-concave form. -/
theorem lemma5PolicyForm_strictlyQuasiConcave_acceptMiddleTripsPolicy (lo hi : ℝ) :
    lemma5PolicyForm .strictlyQuasiConcave (acceptMiddleTripsPolicy lo hi) := by
  exact ⟨lo, hi, acceptsMiddleTrips_acceptMiddleTripsPolicy lo hi⟩

/--
Lemma 5 quasi-convex interval fact: for a strictly quasi-convex endpoint
response, any positive interior point has response below the larger endpoint
response.
-/
theorem paper_lemma5_strictQuasiConvex_response_lt_of_between
    (response : TripLength → ℝ)
    (hqc : strictQuasiConvexOnPositive response)
    {x z y : TripLength} (hx : 0 < x) (hxz : x < z) (hzy : z < y) :
    response z < max (response x) (response y) := by
  exact
    EconCSLib.StrictQuasiConvexOnPositive.lt_of_between
      (f := response) hqc hx hxz hzy

/--
Lemma 5 quasi-concave interval fact: for a strictly quasi-concave endpoint
response, any positive interior point has response above the smaller endpoint
response.
-/
theorem paper_lemma5_strictQuasiConcave_response_lt_between
    (response : TripLength → ℝ)
    (hqc : strictQuasiConcaveOnPositive response)
    {x z y : TripLength} (hx : 0 < x) (hxz : x < z) (hzy : z < y) :
    min (response x) (response y) < response z := by
  exact
    EconCSLib.StrictQuasiConcaveOnPositive.lt_between
      (f := response) hqc hx hxz hzy

/--
Lemma 5 certificate: a derivative-shape hypothesis lets one replace an open
measurable policy by a policy of the corresponding interval form without
decreasing reward.
-/
structure Lemma5OptimizerReplacementCertificate
    (Rhat : SingleStateReward) (σ0 : TripPolicy)
    (shape : Lemma5DerivativeShape) where
  policy : TripPolicy
  policy_form : lemma5PolicyForm shape policy
  reward_ge : Rhat σ0 ≤ Rhat policy
  strict_unless_initial_form : ¬ lemma5PolicyForm shape σ0 → Rhat σ0 < Rhat policy

/--
Positive-case Lemma 5 replacement constructor using accept-all as the
replacement policy.
-/
def lemma5PositiveOptimizerReplacementCertificate_acceptAll
    (Rhat : SingleStateReward) (σ0 : TripPolicy)
    (hreward_ge : Rhat σ0 ≤ Rhat acceptAllPolicy)
    (hstrict_unless_accepts_all :
      ¬ acceptsAllTrips σ0 → Rhat σ0 < Rhat acceptAllPolicy) :
    Lemma5OptimizerReplacementCertificate Rhat σ0 .positive where
  policy := acceptAllPolicy
  policy_form := lemma5PolicyForm_positive_acceptAllPolicy
  reward_ge := hreward_ge
  strict_unless_initial_form := by
    intro hnot
    exact hstrict_unless_accepts_all hnot

/-- Lemma 5 endpoint, conditional on the endpoint-derivative shape certificate. -/
theorem paper_lemma5_optimizer_replacement_of_certificate
    (Rhat : SingleStateReward) (σ0 : TripPolicy)
    (shape : Lemma5DerivativeShape)
    (C : Lemma5OptimizerReplacementCertificate Rhat σ0 shape) :
    ∃ σstar : TripPolicy,
      lemma5PolicyForm shape σstar ∧ Rhat σ0 ≤ Rhat σstar ∧
        (¬ lemma5PolicyForm shape σ0 → Rhat σ0 < Rhat σstar) := by
  exact ⟨C.policy, C.policy_form, C.reward_ge, C.strict_unless_initial_form⟩

/--
If a policy is already optimal for the single-state continuation problem, a
Lemma 5 replacement certificate forces the original policy itself to have the
corresponding Lemma 5 form. Otherwise the strict replacement would contradict
optimality.
-/
theorem lemma5PolicyForm_of_optimizer_replacement_certificate_of_optimal
    (Rhat : SingleStateReward) (σ0 : TripPolicy)
    (shape : Lemma5DerivativeShape)
    (C : Lemma5OptimizerReplacementCertificate Rhat σ0 shape)
    (hoptimal : ∀ σ : TripPolicy, Rhat σ ≤ Rhat σ0) :
    lemma5PolicyForm shape σ0 := by
  by_contra hnot_form
  have hlt : Rhat σ0 < Rhat C.policy :=
    C.strict_unless_initial_form hnot_form
  have hle : Rhat C.policy ≤ Rhat σ0 := hoptimal C.policy
  linarith

/--
Positive-derivative Lemma 5 replacement plus local optimality gives
accept-all behavior directly.
-/
theorem acceptsAllTrips_of_positive_optimizer_replacement_certificate_of_optimal
    (Rhat : SingleStateReward) (σ0 : TripPolicy)
    (C : Lemma5OptimizerReplacementCertificate Rhat σ0 .positive)
    (hoptimal : ∀ σ : TripPolicy, Rhat σ ≤ Rhat σ0) :
    acceptsAllTrips σ0 := by
  exact lemma5PolicyForm_of_optimizer_replacement_certificate_of_optimal
    Rhat σ0 .positive C hoptimal

/-- Lemma 9 lower-bound numerator for the structured-price ratio. -/
def lemma9StructuredLowerNumerator
    (T1 Q1 Tbar2 Qbar2 switch21 : ℝ) : ℝ :=
  T1 * (switch21 * Tbar2 - Qbar2) - (Q1 + T1 * switch21)

/-- Lemma 9 lower-bound denominator for the structured-price ratio. -/
def lemma9StructuredLowerDenominator
    (T1 Q1 Tbar2 Qbar2 switch21 : ℝ) : ℝ :=
  Q1 * (switch21 * Tbar2 - Qbar2) +
    switch21 * (Q1 + T1 * switch21)

/-- Lemma 9 upper-bound numerator for the structured-price ratio. -/
def lemma9StructuredUpperNumerator
    (T1 Q1 Qbar2 : ℝ) : ℝ :=
  Qbar2 * T1 + Q1

/-- Lemma 9 upper-bound denominator for the structured-price ratio. -/
def lemma9StructuredUpperDenominator
    (Q1 Qbar2 switch21 : ℝ) : ℝ :=
  Q1 * (Qbar2 - switch21)

/-- Lemma 9 lower bound as a function of the gap `lambda*T_2-Q_2`. -/
def lemma9StructuredLowerFromGap
    (T1 Q1 gap switch21 : ℝ) : ℝ :=
  (T1 * gap - (Q1 + T1 * switch21)) /
    (Q1 * gap + switch21 * (Q1 + T1 * switch21))

/-- Lemma 9 upper bound as a function of the exit weight `Q_2`. -/
def lemma9StructuredUpperFromExitWeight
    (T1 Q1 Q2 switch21 : ℝ) : ℝ :=
  (Q2 * T1 + Q1) / (Q1 * (Q2 - switch21))

/-- Lemma 9 lower bound for the structured-price ratio. -/
def lemma9StructuredLower
    (T1 Q1 Tbar2 Qbar2 switch21 : ℝ) : ℝ :=
  lemma9StructuredLowerNumerator T1 Q1 Tbar2 Qbar2 switch21 /
    lemma9StructuredLowerDenominator T1 Q1 Tbar2 Qbar2 switch21

/-- Lemma 9 upper bound for the structured-price ratio. -/
def lemma9StructuredUpper
    (T1 Q1 _Tbar2 Qbar2 switch21 : ℝ) : ℝ :=
  lemma9StructuredUpperNumerator T1 Q1 Qbar2 /
    lemma9StructuredUpperDenominator Q1 Qbar2 switch21

/-- The named Lemma 9 lower bound is the lower-from-gap expression. -/
theorem lemma9StructuredLower_eq_lowerFromGap
    (T1 Q1 T2 Q2 switch21 : ℝ) :
    lemma9StructuredLower T1 Q1 T2 Q2 switch21 =
      lemma9StructuredLowerFromGap T1 Q1 (switch21 * T2 - Q2) switch21 := by
  rfl

/-- The named Lemma 9 upper bound is the upper-from-exit-weight expression. -/
theorem lemma9StructuredUpper_eq_upperFromExitWeight
    (T1 Q1 T2 Q2 switch21 : ℝ) :
    lemma9StructuredUpper T1 Q1 T2 Q2 switch21 =
      lemma9StructuredUpperFromExitWeight T1 Q1 Q2 switch21 := by
  rfl

/--
Lemma 9 monotonicity: the lower bound is increasing in the nonnegative gap
`lambda*T_2-Q_2`.
-/
theorem lemma9StructuredLowerFromGap_mono
    (T1 Q1 gap gapbar switch21 : ℝ)
    (hT1_nonneg : 0 ≤ T1)
    (hQ1_pos : 0 < Q1)
    (hswitch_pos : 0 < switch21)
    (hgap_nonneg : 0 ≤ gap)
    (hgap_le : gap ≤ gapbar) :
    lemma9StructuredLowerFromGap T1 Q1 gap switch21 ≤
      lemma9StructuredLowerFromGap T1 Q1 gapbar switch21 := by
  unfold lemma9StructuredLowerFromGap
  have hB_pos : 0 < Q1 + T1 * switch21 := by
    nlinarith [mul_nonneg hT1_nonneg (le_of_lt hswitch_pos)]
  have hgapbar_nonneg : 0 ≤ gapbar := le_trans hgap_nonneg hgap_le
  have hden_gap_pos :
      0 < Q1 * gap + switch21 * (Q1 + T1 * switch21) := by
    have hleft : 0 ≤ Q1 * gap := mul_nonneg (le_of_lt hQ1_pos) hgap_nonneg
    have hright : 0 < switch21 * (Q1 + T1 * switch21) :=
      mul_pos hswitch_pos hB_pos
    nlinarith
  have hden_gapbar_pos :
      0 < Q1 * gapbar + switch21 * (Q1 + T1 * switch21) := by
    have hleft : 0 ≤ Q1 * gapbar :=
      mul_nonneg (le_of_lt hQ1_pos) hgapbar_nonneg
    have hright : 0 < switch21 * (Q1 + T1 * switch21) :=
      mul_pos hswitch_pos hB_pos
    nlinarith
  rw [div_le_div_iff₀ hden_gap_pos hden_gapbar_pos]
  have hprod_nonneg :
      0 ≤ (gapbar - gap) * (Q1 + T1 * switch21) *
        (Q1 + T1 * switch21) := by
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hgap_le) (le_of_lt hB_pos))
      (le_of_lt hB_pos)
  nlinarith

/--
Lemma 9 monotonicity: the upper bound decreases as the exit weight `Q_2`
increases.
-/
theorem lemma9StructuredUpperFromExitWeight_antitone
    (T1 Q1 Q2 Qbar2 switch21 : ℝ)
    (hT1_nonneg : 0 ≤ T1)
    (hQ1_pos : 0 < Q1)
    (hswitch_nonneg : 0 ≤ switch21)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hQ2_le : Q2 ≤ Qbar2) :
    lemma9StructuredUpperFromExitWeight T1 Q1 Qbar2 switch21 ≤
      lemma9StructuredUpperFromExitWeight T1 Q1 Q2 switch21 := by
  unfold lemma9StructuredUpperFromExitWeight
  have hswitch_lt_Qbar2 : switch21 < Qbar2 :=
    lt_of_lt_of_le hswitch_lt_Q2 hQ2_le
  have hden_Qbar_pos : 0 < Q1 * (Qbar2 - switch21) :=
    mul_pos hQ1_pos (sub_pos.mpr hswitch_lt_Qbar2)
  have hden_Q_pos : 0 < Q1 * (Q2 - switch21) :=
    mul_pos hQ1_pos (sub_pos.mpr hswitch_lt_Q2)
  rw [div_le_div_iff₀ hden_Qbar_pos hden_Q_pos]
  have hfactor_nonneg : 0 ≤ T1 * switch21 + Q1 := by
    nlinarith [mul_nonneg hT1_nonneg hswitch_nonneg]
  have hprod_nonneg :
      0 ≤ Q1 * (Qbar2 - Q2) * (T1 * switch21 + Q1) := by
    exact mul_nonneg
      (mul_nonneg (le_of_lt hQ1_pos) (sub_nonneg.mpr hQ2_le))
      hfactor_nonneg
  nlinarith

/-- Lemma 9 structured-price bounds for the surge-state derivative condition. -/
def lemma9StructuredBounds
    (ratio T1 Q1 Tbar2 Qbar2 switch21 : ℝ) : Prop :=
  lemma9StructuredLower T1 Q1 Tbar2 Qbar2 switch21 < ratio ∧
    ratio < lemma9StructuredUpper T1 Q1 Tbar2 Qbar2 switch21

/--
Lemma 9 tightening bridge: if the accept-all lower/upper bounds hold, the
current-policy bounds hold whenever `lambda*T_2-Q_2` is no larger and `Q_2`
is no larger than their accept-all values.
-/
theorem lemma9StructuredBounds_of_acceptAll_tightening
    (ratio T1 Q1 T2 Q2 Tbar2 Qbar2 switch21 : ℝ)
    (hbounds_bar :
      lemma9StructuredBounds ratio T1 Q1 Tbar2 Qbar2 switch21)
    (hT1_nonneg : 0 ≤ T1)
    (hQ1_pos : 0 < Q1)
    (hswitch_pos : 0 < switch21)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (hgap_le :
      switch21 * T2 - Q2 ≤ switch21 * Tbar2 - Qbar2)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hQ2_le : Q2 ≤ Qbar2) :
    lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21 := by
  constructor
  · have hmono :=
      lemma9StructuredLowerFromGap_mono T1 Q1
        (switch21 * T2 - Q2) (switch21 * Tbar2 - Qbar2) switch21
        hT1_nonneg hQ1_pos hswitch_pos hgap_nonneg hgap_le
    have hmono' :
        lemma9StructuredLower T1 Q1 T2 Q2 switch21 ≤
          lemma9StructuredLower T1 Q1 Tbar2 Qbar2 switch21 := by
      simpa [lemma9StructuredLower_eq_lowerFromGap] using hmono
    exact lt_of_le_of_lt hmono' hbounds_bar.1
  · have hmono :=
      lemma9StructuredUpperFromExitWeight_antitone T1 Q1 Q2 Qbar2 switch21
        hT1_nonneg hQ1_pos (le_of_lt hswitch_pos) hswitch_lt_Q2 hQ2_le
    have hmono' :
        lemma9StructuredUpper T1 Q1 Tbar2 Qbar2 switch21 ≤
          lemma9StructuredUpper T1 Q1 T2 Q2 switch21 := by
      simpa [lemma9StructuredUpper_eq_upperFromExitWeight] using hmono
    exact lt_of_lt_of_le hbounds_bar.2 hmono'

/--
Lemma 9 upper-bound algebra: the current upper ratio bound implies positivity
of the structured derivative static term.
-/
theorem lemma9StructuredStaticTerm_pos_of_upper_bound
    (ratio T1 Q1 Q2 switch21 m R1 z : ℝ)
    (hupper :
      ratio < lemma9StructuredUpperFromExitWeight T1 Q1 Q2 switch21)
    (hz : z = ratio * (m - R1))
    (hmR_pos : 0 < m - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hQ1_nonneg : 0 ≤ Q1)
    (hden_pos : 0 < Q1 * (Q2 - switch21)) :
    0 < gn21StructuredDerivativeStaticTerm m z switch21 Q2 Q1 T1 R1 := by
  unfold lemma9StructuredUpperFromExitWeight at hupper
  rw [lt_div_iff₀ hden_pos] at hupper
  have hmargin_pos :
      0 < Q2 * T1 + Q1 - ratio * (Q1 * (Q2 - switch21)) := by
    linarith
  have htail_eq :
      gn21StructuredDerivativeStaticTerm m z switch21 Q2 Q1 T1 R1 =
        (m - R1) *
            (Q2 * T1 + Q1 - ratio * (Q1 * (Q2 - switch21))) +
          Q1 * R1 := by
    unfold gn21StructuredDerivativeStaticTerm
    rw [hz]
    ring
  rw [htail_eq]
  exact add_pos_of_pos_of_nonneg
    (mul_pos hmR_pos hmargin_pos)
    (mul_nonneg hQ1_nonneg hR1_nonneg)

/--
Lemma 9 lower-bound algebra: the current lower ratio bound implies positivity
of the zero-time linearized structured derivative endpoint.
-/
theorem lemma9StructuredLinearEndpoint_pos_of_lower_bound
    (ratio T1 Q1 T2 Q2 switch21 m R1 z : ℝ)
    (hlower :
      lemma9StructuredLowerFromGap T1 Q1 (switch21 * T2 - Q2) switch21 <
        ratio)
    (hz : z = ratio * (m - R1))
    (hmR_pos : 0 < m - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hB_nonneg : 0 ≤ Q1 + T1 * switch21)
    (hden_pos :
      0 < Q1 * (switch21 * T2 - Q2) +
        switch21 * (Q1 + T1 * switch21)) :
    0 < switch21 *
          gn21StructuredDerivativeSwitchBracket m z switch21 Q2 Q1 T2 T1 R1 +
        gn21StructuredDerivativeStaticTerm m z switch21 Q2 Q1 T1 R1 := by
  unfold lemma9StructuredLowerFromGap at hlower
  rw [div_lt_iff₀ hden_pos] at hlower
  have hmargin_pos :
      0 <
        ratio *
            (Q1 * (switch21 * T2 - Q2) +
              switch21 * (Q1 + T1 * switch21)) -
          (T1 * (switch21 * T2 - Q2) - (Q1 + T1 * switch21)) := by
    linarith
  have hlinear_eq :
      switch21 *
          gn21StructuredDerivativeSwitchBracket m z switch21 Q2 Q1 T2 T1 R1 +
        gn21StructuredDerivativeStaticTerm m z switch21 Q2 Q1 T1 R1 =
        (m - R1) *
            (ratio *
                (Q1 * (switch21 * T2 - Q2) +
                  switch21 * (Q1 + T1 * switch21)) -
              (T1 * (switch21 * T2 - Q2) - (Q1 + T1 * switch21))) +
          R1 * (Q1 + T1 * switch21) := by
    unfold gn21StructuredDerivativeSwitchBracket gn21StructuredDerivativeStaticTerm
    rw [hz]
    ring
  rw [hlinear_eq]
  exact add_pos_of_pos_of_nonneg
    (mul_pos hmR_pos hmargin_pos)
    (mul_nonneg hR1_nonneg hB_nonneg)

/--
Lemma 9 derivative-kernel positivity from the current structured ratio bounds.
This closes the algebraic part of the Lemma 9 endpoint, leaving only the
continuous Lemma 6 derivative-value certificate.
-/
theorem paper_lemma9_structured_derivative_kernel_pos_of_current_bounds
    (ratio u T1 Q1 T2 Q2 switch21 switch12 m R1 z : ℝ)
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z = ratio * (m - R1))
    (hmR_pos : 0 < m - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hQ1_pos : 0 < Q1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hu : 0 < u)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2) :
    0 < gn21StructuredDerivativeSignKernel
      (gn21SwitchProb switch21 switch12 u) u m z switch21 Q2 Q1 T2 T1 R1 := by
  have hden_upper_pos : 0 < Q1 * (Q2 - switch21) :=
    mul_pos hQ1_pos (sub_pos.mpr hswitch_lt_Q2)
  have hB_nonneg : 0 ≤ Q1 + T1 * switch21 := by
    nlinarith [mul_nonneg hT1_nonneg (le_of_lt hswitch21_pos)]
  have hden_lower_pos :
      0 < Q1 * (switch21 * T2 - Q2) +
        switch21 * (Q1 + T1 * switch21) := by
    have hleft : 0 ≤ Q1 * (switch21 * T2 - Q2) :=
      mul_nonneg (le_of_lt hQ1_pos) hgap_nonneg
    have hB_pos : 0 < Q1 + T1 * switch21 := by
      nlinarith [mul_nonneg hT1_nonneg (le_of_lt hswitch21_pos)]
    have hright : 0 < switch21 * (Q1 + T1 * switch21) :=
      mul_pos hswitch21_pos hB_pos
    nlinarith
  have htail_pos :
      0 < gn21StructuredDerivativeStaticTerm m z switch21 Q2 Q1 T1 R1 := by
    exact lemma9StructuredStaticTerm_pos_of_upper_bound
      ratio T1 Q1 Q2 switch21 m R1 z
      (by
        simpa [lemma9StructuredUpper_eq_upperFromExitWeight] using hbounds.2)
      hz hmR_pos hR1_nonneg (le_of_lt hQ1_pos) hden_upper_pos
  have hlinear_pos :
      0 < switch21 *
            gn21StructuredDerivativeSwitchBracket m z switch21 Q2 Q1 T2 T1 R1 +
          gn21StructuredDerivativeStaticTerm m z switch21 Q2 Q1 T1 R1 := by
    exact lemma9StructuredLinearEndpoint_pos_of_lower_bound
      ratio T1 Q1 T2 Q2 switch21 m R1 z
      (by
        simpa [lemma9StructuredLower_eq_lowerFromGap] using hbounds.1)
      hz hmR_pos hR1_nonneg hB_nonneg hden_lower_pos
  exact paper_remark2_structured_derivative_kernel_pos_of_ctmc_switch_and_tail
    u m z switch21 switch12 Q2 Q1 T2 T1 R1 hswitch21_pos hsum hu
    htail_pos hlinear_pos

/--
Lemma 9 analytic endpoint derivative, using the current structured ratio
bounds and the Lemma 6 endpoint-derivative certificate.
-/
theorem paper_lemma9_derivative_value_pos_of_current_bounds_certificate
    (C : Lemma6DerivativeFormulaCertificate)
    (ratio u T1 Q1 T2 Q2 switch21 switch12 m R1 z : ℝ)
    (hq : C.q = gn21SwitchProb switch21 switch12 u)
    (hu_eq : C.u = u)
    (hwi : C.wi = m * u + z * gn21SwitchProb switch21 switch12 u)
    (hQi : C.Qi = Q2)
    (hQj : C.Qj = Q1)
    (hTi : C.Ti = T2)
    (hTj : C.Tj = T1)
    (hWi : C.Wi = m * (T2 - 1) + z * (Q2 - switch21))
    (hWj : C.Wj = R1 * T1)
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z = ratio * (m - R1))
    (hmR_pos : 0 < m - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hQ1_pos : 0 < Q1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hu : 0 < u)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2) :
    0 < C.derivativeValue := by
  apply paper_lemma6_derivative_value_pos_of_structured_kernel_pos_of_certificate
    C (gn21SwitchProb switch21 switch12 u) u m z switch21 Q2 Q1 T2 T1 R1
    hq hu_eq hwi hQi hQj hTi hTj hWi hWj
  exact paper_lemma9_structured_derivative_kernel_pos_of_current_bounds
    ratio u T1 Q1 T2 Q2 switch21 switch12 m R1 z hbounds hz hmR_pos
    hR1_nonneg hT1_nonneg hQ1_pos hswitch21_pos hsum hu hswitch_lt_Q2
    hgap_nonneg

/--
Lemma 9 endpoint-improvement bridge: current structured ratio bounds and
endpoint derivative data produce a nearby right endpoint move with strictly
larger aggregate reward.
-/
theorem paper_lemma9_exists_pos_right_improvement_of_current_bounds_endpoint_data
    (D : Lemma6EndpointDerivativeData)
    (ratio u T1 Q1 T2 Q2 switch21 switch12 m R1 z : ℝ)
    (hq : D.q = gn21SwitchProb switch21 switch12 u)
    (hu_eq : D.u = u)
    (hwi : D.wi = m * u + z * gn21SwitchProb switch21 switch12 u)
    (hQi : D.Qi = Q2)
    (hQj : D.Qj = Q1)
    (hTi : D.Ti = T2)
    (hTj : D.Tj = T1)
    (hWi : D.Wi = m * (T2 - 1) + z * (Q2 - switch21))
    (hWj : D.Wj = R1 * T1)
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z = ratio * (m - R1))
    (hmR_pos : 0 < m - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hQ1_pos : 0 < Q1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hu : 0 < u)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2) :
    ∃ ε : ℝ, 0 < ε ∧
      D.rewardAlongEndpoint D.u < D.rewardAlongEndpoint (D.u + ε) := by
  have hpos : 0 < D.derivativeValue := by
    exact paper_lemma9_derivative_value_pos_of_current_bounds_certificate
      (lemma6DerivativeFormulaCertificate_of_endpoint_data D)
      ratio u T1 Q1 T2 Q2 switch21 switch12 m R1 z
      hq hu_eq hwi hQi hQj hTi hTj hWi hWj hbounds hz hmR_pos
      hR1_nonneg hT1_nonneg hQ1_pos hswitch21_pos hsum hu
      hswitch_lt_Q2 hgap_nonneg
  exact exists_pos_right_improvement_of_hasDerivAt_pos D.has_derivative hpos

/--
Interval-density Lemma 9 endpoint-improvement bridge.  This is the surge-state
version specialized to the paper's upper-endpoint primitive paths and CTMC
structured price `m u + z q(u)`.
-/
theorem paper_lemma9_exists_pos_right_improvement_of_interval_density_current_bounds
    (arrivalRate lowerEndpoint u T1 Q1 T2 Q2 switch21 switch12 m R1 z ratio : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQ1_pos : 0 < Q1)
    (hden :
      gn21EndpointQiPath arrivalRate switch21 lowerEndpoint density
          (gn21SwitchProb switch21 switch12) u * T1 +
        Q1 *
          gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) volume
        lowerEndpoint u)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (𝓝 u))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) u)
    (hw_int :
      IntervalIntegrable
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) volume lowerEndpoint u)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) (𝓝 u))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume lowerEndpoint u)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hQ2 :
      gn21EndpointQiPath arrivalRate switch21 lowerEndpoint density
        (gn21SwitchProb switch21 switch12) u = Q2)
    (hT2 :
      gn21EndpointTiPath arrivalRate lowerEndpoint density u = T2)
    (hW2 :
      gn21EndpointWiPath arrivalRate lowerEndpoint density
        (ctmcStructuredSurgePrice m z switch21 switch12) u =
          m * (T2 - 1) + z * (Q2 - switch21))
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z = ratio * (m - R1))
    (hmR_pos : 0 < m - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hu : 0 < u)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2) :
    ∃ ε : ℝ, 0 < ε ∧
      gn21AggregateDynamicReward
          (gn21EndpointQiPath arrivalRate switch21 lowerEndpoint density
            (gn21SwitchProb switch21 switch12) u)
          Q1
          (gn21EndpointTiPath arrivalRate lowerEndpoint density u)
          T1
          (gn21EndpointWiPath arrivalRate lowerEndpoint density
            (ctmcStructuredSurgePrice m z switch21 switch12) u)
          (R1 * T1) <
        gn21AggregateDynamicReward
          (gn21EndpointQiPath arrivalRate switch21 lowerEndpoint density
            (gn21SwitchProb switch21 switch12) (u + ε))
          Q1
          (gn21EndpointTiPath arrivalRate lowerEndpoint density (u + ε))
          T1
          (gn21EndpointWiPath arrivalRate lowerEndpoint density
            (ctmcStructuredSurgePrice m z switch21 switch12) (u + ε))
          (R1 * T1) := by
  let D :=
    lemma6EndpointDerivativeData_of_interval_density_paths
      arrivalRate switch21 lowerEndpoint u Q1 T1 (R1 * T1) density
      (gn21SwitchProb switch21 switch12)
      (ctmcStructuredSurgePrice m z switch21 switch12)
      harrival_pos hdensity_pos hQ1_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont
  have h :=
    paper_lemma9_exists_pos_right_improvement_of_current_bounds_endpoint_data
      D ratio u T1 Q1 T2 Q2 switch21 switch12 m R1 z
      (by rfl)
      (by rfl)
      (by rfl)
      (by simpa [D] using hQ2)
      (by rfl)
      (by simpa [D] using hT2)
      (by rfl)
      (by simpa [D] using hW2)
      (by rfl)
      hbounds hz hmR_pos hR1_nonneg hT1_nonneg hQ1_pos hswitch21_pos
      hsum hu hswitch_lt_Q2 hgap_nonneg
  simpa [D] using h

/--
Lower-endpoint Lemma 9 endpoint-improvement bridge.  This supports finite
tail-interval policy moves by expanding the lower endpoint left under the
same positive structured-kernel conditions as the upper-endpoint bridge.
-/
theorem paper_lemma9_exists_pos_left_improvement_of_lower_interval_density_current_bounds
    (arrivalRate upperEndpoint u T1 Q1 T2 Q2 switch21 switch12 m R1 z ratio δ : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQ1_pos : 0 < Q1)
    (hden :
      gn21LowerEndpointQiPath arrivalRate switch21 upperEndpoint density
          (gn21SwitchProb switch21 switch12) u * T1 +
        Q1 *
          gn21LowerEndpointTiPath arrivalRate upperEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) volume
        u upperEndpoint)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (𝓝 u))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) u)
    (hw_int :
      IntervalIntegrable
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) volume u upperEndpoint)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) (𝓝 u))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume u upperEndpoint)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hQ2 :
      gn21LowerEndpointQiPath arrivalRate switch21 upperEndpoint density
        (gn21SwitchProb switch21 switch12) u = Q2)
    (hT2 :
      gn21LowerEndpointTiPath arrivalRate upperEndpoint density u = T2)
    (hW2 :
      gn21LowerEndpointWiPath arrivalRate upperEndpoint density
        (ctmcStructuredSurgePrice m z switch21 switch12) u =
          m * (T2 - 1) + z * (Q2 - switch21))
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z = ratio * (m - R1))
    (hmR_pos : 0 < m - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hu : 0 < u)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switch21 upperEndpoint density
            (gn21SwitchProb switch21 switch12) u)
          Q1
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
          T1
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density
            (ctmcStructuredSurgePrice m z switch21 switch12) u)
          (R1 * T1) <
        gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switch21 upperEndpoint density
            (gn21SwitchProb switch21 switch12) (u - ε))
          Q1
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density (u - ε))
          T1
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density
            (ctmcStructuredSurgePrice m z switch21 switch12) (u - ε))
          (R1 * T1) := by
  have hstructured :
      0 < gn21StructuredDerivativeSignKernel
        (gn21SwitchProb switch21 switch12 u) u m z switch21 Q2 Q1 T2 T1 R1 :=
    paper_lemma9_structured_derivative_kernel_pos_of_current_bounds
      ratio u T1 Q1 T2 Q2 switch21 switch12 m R1 z hbounds hz hmR_pos
      hR1_nonneg hT1_nonneg hQ1_pos hswitch21_pos hsum hu
      hswitch_lt_Q2 hgap_nonneg
  have hkernel :
      0 < gn21DerivativeSignKernel (gn21SwitchProb switch21 switch12 u) u
        (ctmcStructuredSurgePrice m z switch21 switch12 u)
        (gn21LowerEndpointQiPath arrivalRate switch21 upperEndpoint density
          (gn21SwitchProb switch21 switch12) u)
        Q1
        (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
        T1
        (gn21LowerEndpointWiPath arrivalRate upperEndpoint density
          (ctmcStructuredSurgePrice m z switch21 switch12) u)
        (R1 * T1) := by
    rw [hQ2, hT2, hW2]
    simp only [ctmcStructuredSurgePrice, structuredSurgePrice]
    rw [paper_remark2_structured_derivative_kernel_algebra]
    exact hstructured
  exact
    paper_lemma6_exists_pos_left_improvement_of_lower_interval_density_kernel_pos_lt
      arrivalRate switch21 upperEndpoint u Q1 T1 (R1 * T1) δ density
      (gn21SwitchProb switch21 switch12)
      (ctmcStructuredSurgePrice m z switch21 switch12)
      harrival_pos hdensity_pos hQ1_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont hkernel hδ

/--
Tail Lemma 9 endpoint-improvement bridge.  This is the unbounded
`(u,∞)` counterpart of the finite lower-endpoint bridge.
-/
theorem paper_lemma9_exists_pos_left_improvement_of_tail_interval_density_current_bounds
    (arrivalRate u T1 Q1 T2 Q2 switch21 switch12 m R1 z ratio δ : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQ1_pos : 0 < Q1)
    (hden :
      gn21TailQiPath arrivalRate switch21 density
          (gn21SwitchProb switch21 switch12) u * T1 +
        Q1 * gn21TailTiPath arrivalRate density u ≠ 0)
    (hq_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ)
        (Set.Ioi (u - 1)) volume)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (𝓝 u))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) u)
    (hw_int :
      IntegrableOn
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) (Set.Ioi (u - 1)) volume)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) (𝓝 u))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) u)
    (ht_int :
      IntegrableOn (fun τ => τ * density τ) (Set.Ioi (u - 1)) volume)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hQ2 :
      gn21TailQiPath arrivalRate switch21 density
        (gn21SwitchProb switch21 switch12) u = Q2)
    (hT2 :
      gn21TailTiPath arrivalRate density u = T2)
    (hW2 :
      gn21TailWiPath arrivalRate density
        (ctmcStructuredSurgePrice m z switch21 switch12) u =
          m * (T2 - 1) + z * (Q2 - switch21))
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z = ratio * (m - R1))
    (hmR_pos : 0 < m - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hu : 0 < u)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      gn21AggregateDynamicReward
          (gn21TailQiPath arrivalRate switch21 density
            (gn21SwitchProb switch21 switch12) u)
          Q1
          (gn21TailTiPath arrivalRate density u)
          T1
          (gn21TailWiPath arrivalRate density
            (ctmcStructuredSurgePrice m z switch21 switch12) u)
          (R1 * T1) <
        gn21AggregateDynamicReward
          (gn21TailQiPath arrivalRate switch21 density
            (gn21SwitchProb switch21 switch12) (u - ε))
          Q1
          (gn21TailTiPath arrivalRate density (u - ε))
          T1
          (gn21TailWiPath arrivalRate density
            (ctmcStructuredSurgePrice m z switch21 switch12) (u - ε))
          (R1 * T1) := by
  have hstructured :
      0 < gn21StructuredDerivativeSignKernel
        (gn21SwitchProb switch21 switch12 u) u m z switch21 Q2 Q1 T2 T1 R1 :=
    paper_lemma9_structured_derivative_kernel_pos_of_current_bounds
      ratio u T1 Q1 T2 Q2 switch21 switch12 m R1 z hbounds hz hmR_pos
      hR1_nonneg hT1_nonneg hQ1_pos hswitch21_pos hsum hu
      hswitch_lt_Q2 hgap_nonneg
  have hkernel :
      0 < gn21DerivativeSignKernel (gn21SwitchProb switch21 switch12 u) u
        (ctmcStructuredSurgePrice m z switch21 switch12 u)
        (gn21TailQiPath arrivalRate switch21 density
          (gn21SwitchProb switch21 switch12) u)
        Q1
        (gn21TailTiPath arrivalRate density u)
        T1
        (gn21TailWiPath arrivalRate density
          (ctmcStructuredSurgePrice m z switch21 switch12) u)
        (R1 * T1) := by
    rw [hQ2, hT2, hW2]
    simp only [ctmcStructuredSurgePrice, structuredSurgePrice]
    rw [paper_remark2_structured_derivative_kernel_algebra]
    exact hstructured
  exact
    paper_lemma6_exists_pos_left_improvement_of_tail_interval_density_kernel_pos_lt
      arrivalRate switch21 u Q1 T1 (R1 * T1) δ density
      (gn21SwitchProb switch21 switch12)
      (ctmcStructuredSurgePrice m z switch21 switch12)
      harrival_pos hdensity_pos hQ1_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont hkernel hδ

/--
Reject-middle Lemma 9 lower-cutoff bridge.  Under the same current structured
bounds as the upper/lower/tail endpoint bridges, a small rightward move of
`lo` strictly improves the surge-state aggregate reward.
-/
theorem paper_lemma9_exists_pos_right_improvement_of_reject_middle_lo_interval_density_current_bounds
    (arrivalRate lo hi T1 Q1 T2 Q2 switch21 switch12 m R1 z ratio δ : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density lo)
    (hQ1_pos : 0 < Q1)
    (hden :
      gn21RejectMiddleQiPath arrivalRate switch21 density
          (gn21SwitchProb switch21 switch12) lo hi * T1 +
        Q1 * gn21RejectMiddleTiPath arrivalRate density lo hi ≠ 0)
    (hq_int :
      IntervalIntegrable
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) volume
        0 lo)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (𝓝 lo))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) lo)
    (hw_int :
      IntervalIntegrable
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) volume 0 lo)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) (𝓝 lo))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) lo)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume 0 lo)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 lo))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) lo)
    (hQ2 :
      gn21RejectMiddleQiPath arrivalRate switch21 density
        (gn21SwitchProb switch21 switch12) lo hi = Q2)
    (hT2 :
      gn21RejectMiddleTiPath arrivalRate density lo hi = T2)
    (hW2 :
      gn21RejectMiddleWiPath arrivalRate density
        (ctmcStructuredSurgePrice m z switch21 switch12) lo hi =
          m * (T2 - 1) + z * (Q2 - switch21))
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z = ratio * (m - R1))
    (hmR_pos : 0 < m - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hlo_pos : 0 < lo)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      gn21AggregateDynamicReward
          (gn21RejectMiddleQiPath arrivalRate switch21 density
            (gn21SwitchProb switch21 switch12) lo hi)
          Q1
          (gn21RejectMiddleTiPath arrivalRate density lo hi)
          T1
          (gn21RejectMiddleWiPath arrivalRate density
            (ctmcStructuredSurgePrice m z switch21 switch12) lo hi)
          (R1 * T1) <
        gn21AggregateDynamicReward
          (gn21RejectMiddleQiPath arrivalRate switch21 density
            (gn21SwitchProb switch21 switch12) (lo + ε) hi)
          Q1
          (gn21RejectMiddleTiPath arrivalRate density (lo + ε) hi)
          T1
          (gn21RejectMiddleWiPath arrivalRate density
            (ctmcStructuredSurgePrice m z switch21 switch12) (lo + ε) hi)
          (R1 * T1) := by
  have hstructured :
      0 < gn21StructuredDerivativeSignKernel
        (gn21SwitchProb switch21 switch12 lo) lo m z switch21 Q2 Q1 T2 T1 R1 :=
    paper_lemma9_structured_derivative_kernel_pos_of_current_bounds
      ratio lo T1 Q1 T2 Q2 switch21 switch12 m R1 z hbounds hz
      hmR_pos hR1_nonneg hT1_nonneg hQ1_pos hswitch21_pos hsum
      hlo_pos hswitch_lt_Q2 hgap_nonneg
  have hkernel :
      0 < gn21DerivativeSignKernel (gn21SwitchProb switch21 switch12 lo) lo
        (ctmcStructuredSurgePrice m z switch21 switch12 lo)
        (gn21RejectMiddleQiPath arrivalRate switch21 density
          (gn21SwitchProb switch21 switch12) lo hi)
        Q1
        (gn21RejectMiddleTiPath arrivalRate density lo hi)
        T1
        (gn21RejectMiddleWiPath arrivalRate density
          (ctmcStructuredSurgePrice m z switch21 switch12) lo hi)
        (R1 * T1) := by
    rw [hQ2, hT2, hW2]
    simp only [ctmcStructuredSurgePrice, structuredSurgePrice]
    rw [paper_remark2_structured_derivative_kernel_algebra]
    exact hstructured
  exact
    paper_lemma6_exists_pos_right_improvement_of_reject_middle_lo_interval_density_kernel_pos_lt
      arrivalRate switch21 lo hi Q1 T1 (R1 * T1) δ density
      (gn21SwitchProb switch21 switch12)
      (ctmcStructuredSurgePrice m z switch21 switch12)
      harrival_pos hdensity_pos hQ1_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont hkernel hδ

/--
Reject-middle Lemma 9 upper-cutoff bridge.  Under the same current structured
bounds as the upper/lower/tail endpoint bridges, a small leftward move of
`hi` strictly improves the surge-state aggregate reward.
-/
theorem paper_lemma9_exists_pos_left_improvement_of_reject_middle_hi_interval_density_current_bounds
    (arrivalRate lo hi T1 Q1 T2 Q2 switch21 switch12 m R1 z ratio δ : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density hi)
    (hQ1_pos : 0 < Q1)
    (hden :
      gn21RejectMiddleQiPath arrivalRate switch21 density
          (gn21SwitchProb switch21 switch12) lo hi * T1 +
        Q1 * gn21RejectMiddleTiPath arrivalRate density lo hi ≠ 0)
    (hq_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ)
        (Set.Ioi (hi - 1)) volume)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (𝓝 hi))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) hi)
    (hw_int :
      IntegrableOn
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) (Set.Ioi (hi - 1)) volume)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) (𝓝 hi))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ *
          density τ) hi)
    (ht_int :
      IntegrableOn (fun τ => τ * density τ) (Set.Ioi (hi - 1)) volume)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 hi))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) hi)
    (hQ2 :
      gn21RejectMiddleQiPath arrivalRate switch21 density
        (gn21SwitchProb switch21 switch12) lo hi = Q2)
    (hT2 :
      gn21RejectMiddleTiPath arrivalRate density lo hi = T2)
    (hW2 :
      gn21RejectMiddleWiPath arrivalRate density
        (ctmcStructuredSurgePrice m z switch21 switch12) lo hi =
          m * (T2 - 1) + z * (Q2 - switch21))
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z = ratio * (m - R1))
    (hmR_pos : 0 < m - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hhi_pos : 0 < hi)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      gn21AggregateDynamicReward
          (gn21RejectMiddleQiPath arrivalRate switch21 density
            (gn21SwitchProb switch21 switch12) lo hi)
          Q1
          (gn21RejectMiddleTiPath arrivalRate density lo hi)
          T1
          (gn21RejectMiddleWiPath arrivalRate density
            (ctmcStructuredSurgePrice m z switch21 switch12) lo hi)
          (R1 * T1) <
        gn21AggregateDynamicReward
          (gn21RejectMiddleQiPath arrivalRate switch21 density
            (gn21SwitchProb switch21 switch12) lo (hi - ε))
          Q1
          (gn21RejectMiddleTiPath arrivalRate density lo (hi - ε))
          T1
          (gn21RejectMiddleWiPath arrivalRate density
            (ctmcStructuredSurgePrice m z switch21 switch12) lo (hi - ε))
          (R1 * T1) := by
  have hstructured :
      0 < gn21StructuredDerivativeSignKernel
        (gn21SwitchProb switch21 switch12 hi) hi m z switch21 Q2 Q1 T2 T1 R1 :=
    paper_lemma9_structured_derivative_kernel_pos_of_current_bounds
      ratio hi T1 Q1 T2 Q2 switch21 switch12 m R1 z hbounds hz
      hmR_pos hR1_nonneg hT1_nonneg hQ1_pos hswitch21_pos hsum
      hhi_pos hswitch_lt_Q2 hgap_nonneg
  have hkernel :
      0 < gn21DerivativeSignKernel (gn21SwitchProb switch21 switch12 hi) hi
        (ctmcStructuredSurgePrice m z switch21 switch12 hi)
        (gn21RejectMiddleQiPath arrivalRate switch21 density
          (gn21SwitchProb switch21 switch12) lo hi)
        Q1
        (gn21RejectMiddleTiPath arrivalRate density lo hi)
        T1
        (gn21RejectMiddleWiPath arrivalRate density
          (ctmcStructuredSurgePrice m z switch21 switch12) lo hi)
        (R1 * T1) := by
    rw [hQ2, hT2, hW2]
    simp only [ctmcStructuredSurgePrice, structuredSurgePrice]
    rw [paper_remark2_structured_derivative_kernel_algebra]
    exact hstructured
  exact
    paper_lemma6_exists_pos_left_improvement_of_reject_middle_hi_interval_density_kernel_pos_lt
      arrivalRate switch21 lo hi Q1 T1 (R1 * T1) δ density
      (gn21SwitchProb switch21 switch12)
      (ctmcStructuredSurgePrice m z switch21 switch12)
      harrival_pos hdensity_pos hQ1_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont hkernel hδ

/-- Lemma 9 feasibility bridge: a nonempty open interval contains an admissible ratio. -/
theorem paper_lemma9_structured_bounds_feasible_of_lower_lt_upper
    (T1 Q1 Tbar2 Qbar2 switch21 : ℝ)
    (hinterval :
      lemma9StructuredLower T1 Q1 Tbar2 Qbar2 switch21 <
        lemma9StructuredUpper T1 Q1 Tbar2 Qbar2 switch21) :
    ∃ ratio : ℝ, lemma9StructuredBounds ratio T1 Q1 Tbar2 Qbar2 switch21 := by
  refine ⟨(lemma9StructuredLower T1 Q1 Tbar2 Qbar2 switch21 +
      lemma9StructuredUpper T1 Q1 Tbar2 Qbar2 switch21) / 2, ?_, ?_⟩ <;>
    linarith

/-- Lemma 9 upper ratio bound is positive under the source positivity assumptions. -/
theorem lemma9StructuredUpper_pos
    (T1 Q1 Tbar2 Qbar2 switch21 : ℝ)
    (hT1_nonneg : 0 ≤ T1)
    (hQ1_pos : 0 < Q1)
    (hswitch_pos : 0 < switch21)
    (hswitch_lt_Qbar2 : switch21 < Qbar2) :
    0 < lemma9StructuredUpper T1 Q1 Tbar2 Qbar2 switch21 := by
  unfold lemma9StructuredUpper lemma9StructuredUpperNumerator
    lemma9StructuredUpperDenominator
  have hQbar2_pos : 0 < Qbar2 := lt_trans hswitch_pos hswitch_lt_Qbar2
  have hnum_pos : 0 < Qbar2 * T1 + Q1 := by
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (le_of_lt hQbar2_pos) hT1_nonneg) hQ1_pos
  have hden_pos : 0 < Q1 * (Qbar2 - switch21) :=
    mul_pos hQ1_pos (sub_pos.mpr hswitch_lt_Qbar2)
  exact div_pos hnum_pos hden_pos

/-- Lemma 9 feasibility with a positive admissible structured-price ratio. -/
theorem paper_lemma9_structured_bounds_feasible_positive_of_lower_lt_upper
    (T1 Q1 Tbar2 Qbar2 switch21 : ℝ)
    (hinterval :
      lemma9StructuredLower T1 Q1 Tbar2 Qbar2 switch21 <
        lemma9StructuredUpper T1 Q1 Tbar2 Qbar2 switch21)
    (hupper_pos :
      0 < lemma9StructuredUpper T1 Q1 Tbar2 Qbar2 switch21) :
    ∃ ratio : ℝ,
      0 < ratio ∧
        lemma9StructuredBounds ratio T1 Q1 Tbar2 Qbar2 switch21 := by
  rcases exists_pos_between_of_lt_of_pos
      (lemma9StructuredLower T1 Q1 Tbar2 Qbar2 switch21)
      (lemma9StructuredUpper T1 Q1 Tbar2 Qbar2 switch21)
      hinterval hupper_pos with ⟨ratio, hratio_pos, hlower, hupper⟩
  exact ⟨ratio, hratio_pos, hlower, hupper⟩

/--
Lemma 9 feasibility bridge from the source proof's cross-multiplied
inequality, under positive denominators.
-/
theorem paper_lemma9_structured_bounds_feasible_of_cross_mul
    (T1 Q1 Tbar2 Qbar2 switch21 : ℝ)
    (hden_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 Tbar2 Qbar2 switch21)
    (hden_upper :
      0 < lemma9StructuredUpperDenominator Q1 Qbar2 switch21)
    (hcross :
      lemma9StructuredLowerNumerator T1 Q1 Tbar2 Qbar2 switch21 *
          lemma9StructuredUpperDenominator Q1 Qbar2 switch21 <
        lemma9StructuredUpperNumerator T1 Q1 Qbar2 *
          lemma9StructuredLowerDenominator T1 Q1 Tbar2 Qbar2 switch21) :
    ∃ ratio : ℝ, lemma9StructuredBounds ratio T1 Q1 Tbar2 Qbar2 switch21 := by
  apply paper_lemma9_structured_bounds_feasible_of_lower_lt_upper
  unfold lemma9StructuredLower lemma9StructuredUpper
  rw [div_lt_div_iff₀ hden_lower hden_upper]
  exact hcross

/--
Lemma 9 final-line feasibility bridge: the paper concludes the
cross-multiplied left side is non-positive while the right side is positive.
Those two sign facts imply a feasible ratio interval.
-/
theorem paper_lemma9_structured_bounds_feasible_of_final_signs
    (T1 Q1 Tbar2 Qbar2 switch21 : ℝ)
    (hden_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 Tbar2 Qbar2 switch21)
    (hden_upper :
      0 < lemma9StructuredUpperDenominator Q1 Qbar2 switch21)
    (hleft_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 Tbar2 Qbar2 switch21 *
          lemma9StructuredUpperDenominator Q1 Qbar2 switch21 ≤ 0)
    (hright_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Qbar2 *
        lemma9StructuredLowerDenominator T1 Q1 Tbar2 Qbar2 switch21) :
    ∃ ratio : ℝ, lemma9StructuredBounds ratio T1 Q1 Tbar2 Qbar2 switch21 := by
  apply paper_lemma9_structured_bounds_feasible_of_cross_mul
    T1 Q1 Tbar2 Qbar2 switch21 hden_lower hden_upper
  exact lt_of_le_of_lt hleft_nonpos hright_pos

/--
Lemma 9 final-sign feasibility with a positive admissible ratio, used by the
surge-side Theorem 3 construction to obtain `z_2 > 0`.
-/
theorem paper_lemma9_structured_bounds_feasible_positive_of_final_signs
    (T1 Q1 Tbar2 Qbar2 switch21 : ℝ)
    (hden_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 Tbar2 Qbar2 switch21)
    (hden_upper :
      0 < lemma9StructuredUpperDenominator Q1 Qbar2 switch21)
    (hleft_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 Tbar2 Qbar2 switch21 *
          lemma9StructuredUpperDenominator Q1 Qbar2 switch21 ≤ 0)
    (hright_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Qbar2 *
        lemma9StructuredLowerDenominator T1 Q1 Tbar2 Qbar2 switch21)
    (hupper_pos :
      0 < lemma9StructuredUpper T1 Q1 Tbar2 Qbar2 switch21) :
    ∃ ratio : ℝ,
      0 < ratio ∧
        lemma9StructuredBounds ratio T1 Q1 Tbar2 Qbar2 switch21 := by
  apply paper_lemma9_structured_bounds_feasible_positive_of_lower_lt_upper
    T1 Q1 Tbar2 Qbar2 switch21
  · unfold lemma9StructuredLower lemma9StructuredUpper
    rw [div_lt_div_iff₀ hden_lower hden_upper]
    exact lt_of_le_of_lt hleft_nonpos hright_pos
  · exact hupper_pos

/-- Lemma 9 certificate: the stated bounds imply positive upper-endpoint derivative in state 2. -/
structure Lemma9SurgeDerivativeCertificate where
  ratio : ℝ
  T1 : ℝ
  Q1 : ℝ
  Tbar2 : ℝ
  Qbar2 : ℝ
  switch21 : ℝ
  derivativeKernel : TripLength → ℝ
  bounds : lemma9StructuredBounds ratio T1 Q1 Tbar2 Qbar2 switch21
  derivativePositive : ∀ u : TripLength, 0 < u → 0 < derivativeKernel u

/--
Concrete Lemma 9 structured derivative certificate from the current-policy
ratio bounds and CTMC positivity assumptions.
-/
def lemma9SurgeDerivativeCertificate_of_current_bounds
    (ratio T1 Q1 T2 Q2 switch21 switch12 m R1 z : ℝ)
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z = ratio * (m - R1))
    (hmR_pos : 0 < m - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hQ1_pos : 0 < Q1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2) :
    Lemma9SurgeDerivativeCertificate where
  ratio := ratio
  T1 := T1
  Q1 := Q1
  Tbar2 := T2
  Qbar2 := Q2
  switch21 := switch21
  derivativeKernel := fun u : TripLength =>
    gn21StructuredDerivativeSignKernel
      (gn21SwitchProb switch21 switch12 u) u m z switch21 Q2 Q1 T2 T1 R1
  bounds := hbounds
  derivativePositive := by
    intro u hu
    exact paper_lemma9_structured_derivative_kernel_pos_of_current_bounds
      ratio u T1 Q1 T2 Q2 switch21 switch12 m R1 z hbounds hz hmR_pos
      hR1_nonneg hT1_nonneg hQ1_pos hswitch21_pos hsum hu hswitch_lt_Q2
      hgap_nonneg

/-- Lemma 9 supplies Lemma 5's positive derivative-shape witness. -/
theorem lemma5DerivativeShapeWitness_positive_of_lemma9_certificate
    (C : Lemma9SurgeDerivativeCertificate) :
    lemma5DerivativeShapeWitness C.derivativeKernel .positive := by
  exact C.derivativePositive

/--
Current-bounds form of Lemma 9's positive derivative-shape witness, avoiding an
intermediate certificate object when wiring the proof chain.
-/
theorem lemma5DerivativeShapeWitness_positive_of_lemma9_current_bounds
    (ratio T1 Q1 T2 Q2 switch21 switch12 m R1 z : ℝ)
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z = ratio * (m - R1))
    (hmR_pos : 0 < m - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hQ1_pos : 0 < Q1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2) :
    lemma5DerivativeShapeWitness
      (fun u : TripLength =>
        gn21StructuredDerivativeSignKernel
          (gn21SwitchProb switch21 switch12 u) u m z switch21 Q2 Q1 T2 T1 R1)
      .positive := by
  intro u hu
  exact paper_lemma9_structured_derivative_kernel_pos_of_current_bounds
    ratio u T1 Q1 T2 Q2 switch21 switch12 m R1 z hbounds hz hmR_pos
    hR1_nonneg hT1_nonneg hQ1_pos hswitch21_pos hsum hu hswitch_lt_Q2
    hgap_nonneg

/-- Lemma 9 endpoint, conditional on the structured derivative certificate. -/
theorem paper_lemma9_surge_derivative_positive_of_certificate
    (C : Lemma9SurgeDerivativeCertificate) :
    lemma9StructuredBounds C.ratio C.T1 C.Q1 C.Tbar2 C.Qbar2 C.switch21 ∧
      ∀ u : TripLength, 0 < u → 0 < C.derivativeKernel u := by
  exact ⟨C.bounds, C.derivativePositive⟩

/-- Lemma 10 positive numerator appearing in the lower bound. -/
def lemma10StructuredLowerNumerator
    (T2 Q2 switch12 : ℝ) : ℝ :=
  T2 * switch12 + Q2

/-- Lemma 10 denominator appearing in the lower bound. -/
def lemma10StructuredLowerDenominator
    (T2 Q2 Tbar1 Qbar1 switch12 : ℝ) : ℝ :=
  Q2 * (switch12 * Tbar1 - Qbar1) +
    switch12 * (T2 * switch12 + Q2)

/-- Lemma 10 upper-bound denominator. -/
def lemma10StructuredUpperDenominator
    (Qbar1 switch12 : ℝ) : ℝ :=
  Qbar1 - switch12

/-- Lemma 10 lower bound as a function of the gap `lambda*T_1-Q_1`. -/
def lemma10StructuredLowerFromGap
    (T2 Q2 gap switch12 : ℝ) : ℝ :=
  -((T2 * switch12 + Q2) /
    (Q2 * gap + switch12 * (T2 * switch12 + Q2)))

/-- Lemma 10 upper bound as a function of the exit weight `Q_1`. -/
def lemma10StructuredUpperFromExitWeight
    (Q1 switch12 : ℝ) : ℝ :=
  1 / (Q1 - switch12)

/-- Lemma 10 lower bound for the structured-price ratio. -/
def lemma10StructuredLower
    (T2 Q2 Tbar1 Qbar1 switch12 : ℝ) : ℝ :=
  -(lemma10StructuredLowerNumerator T2 Q2 switch12 /
      lemma10StructuredLowerDenominator T2 Q2 Tbar1 Qbar1 switch12)

/-- Lemma 10 upper bound for the structured-price ratio. -/
def lemma10StructuredUpper
    (_T2 _Q2 _Tbar1 Qbar1 switch12 : ℝ) : ℝ :=
  1 / lemma10StructuredUpperDenominator Qbar1 switch12

/-- The named Lemma 10 lower bound is the lower-from-gap expression. -/
theorem lemma10StructuredLower_eq_lowerFromGap
    (T2 Q2 T1 Q1 switch12 : ℝ) :
    lemma10StructuredLower T2 Q2 T1 Q1 switch12 =
      lemma10StructuredLowerFromGap T2 Q2 (switch12 * T1 - Q1) switch12 := by
  rfl

/-- The named Lemma 10 upper bound is the upper-from-exit-weight expression. -/
theorem lemma10StructuredUpper_eq_upperFromExitWeight
    (T2 Q2 T1 Q1 switch12 : ℝ) :
    lemma10StructuredUpper T2 Q2 T1 Q1 switch12 =
      lemma10StructuredUpperFromExitWeight Q1 switch12 := by
  rfl

/-- Lemma 10 structured-price bounds for the non-surge-state derivative condition. -/
def lemma10StructuredBounds
    (ratio T2 Q2 Tbar1 Qbar1 switch12 : ℝ) : Prop :=
  lemma10StructuredLower T2 Q2 Tbar1 Qbar1 switch12 < ratio ∧
    ratio < lemma10StructuredUpper T2 Q2 Tbar1 Qbar1 switch12

/--
Lemma 10 monotonicity: the lower bound is increasing in the nonnegative gap
`lambda*T_1-Q_1`.
-/
theorem lemma10StructuredLowerFromGap_mono
    (T2 Q2 gap gapbar switch12 : ℝ)
    (hA_pos : 0 < T2 * switch12 + Q2)
    (hQ2_nonneg : 0 ≤ Q2)
    (hswitch_pos : 0 < switch12)
    (hgap_nonneg : 0 ≤ gap)
    (hgap_le : gap ≤ gapbar) :
    lemma10StructuredLowerFromGap T2 Q2 gap switch12 ≤
      lemma10StructuredLowerFromGap T2 Q2 gapbar switch12 := by
  unfold lemma10StructuredLowerFromGap
  have hgapbar_nonneg : 0 ≤ gapbar := le_trans hgap_nonneg hgap_le
  have hden_gap_pos :
      0 < Q2 * gap + switch12 * (T2 * switch12 + Q2) := by
    have hleft : 0 ≤ Q2 * gap := mul_nonneg hQ2_nonneg hgap_nonneg
    have hright : 0 < switch12 * (T2 * switch12 + Q2) :=
      mul_pos hswitch_pos hA_pos
    nlinarith
  have hden_gapbar_pos :
      0 < Q2 * gapbar + switch12 * (T2 * switch12 + Q2) := by
    have hleft : 0 ≤ Q2 * gapbar := mul_nonneg hQ2_nonneg hgapbar_nonneg
    have hright : 0 < switch12 * (T2 * switch12 + Q2) :=
      mul_pos hswitch_pos hA_pos
    nlinarith
  rw [neg_le_neg_iff]
  rw [div_le_div_iff₀ hden_gapbar_pos hden_gap_pos]
  have hden_le :
      Q2 * gap + switch12 * (T2 * switch12 + Q2) ≤
        Q2 * gapbar + switch12 * (T2 * switch12 + Q2) := by
    nlinarith [mul_le_mul_of_nonneg_left hgap_le hQ2_nonneg]
  nlinarith [mul_le_mul_of_nonneg_left hden_le (le_of_lt hA_pos)]

/--
Lemma 10 monotonicity: the upper bound decreases as the exit weight `Q_1`
increases.
-/
theorem lemma10StructuredUpperFromExitWeight_antitone
    (Q1 Qbar1 switch12 : ℝ)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hQ1_le : Q1 ≤ Qbar1) :
    lemma10StructuredUpperFromExitWeight Qbar1 switch12 ≤
      lemma10StructuredUpperFromExitWeight Q1 switch12 := by
  unfold lemma10StructuredUpperFromExitWeight
  have hswitch_lt_Qbar1 : switch12 < Qbar1 :=
    lt_of_lt_of_le hswitch_lt_Q1 hQ1_le
  have hden_Qbar_pos : 0 < Qbar1 - switch12 :=
    sub_pos.mpr hswitch_lt_Qbar1
  have hden_Q_pos : 0 < Q1 - switch12 :=
    sub_pos.mpr hswitch_lt_Q1
  rw [div_le_div_iff₀ hden_Qbar_pos hden_Q_pos]
  nlinarith

/--
Lemma 10 tightening bridge: if the accept-all lower/upper bounds hold, the
current-policy bounds hold whenever `lambda*T_1-Q_1` is no larger and `Q_1`
is no larger than their accept-all values.
-/
theorem lemma10StructuredBounds_of_acceptAll_tightening
    (ratio T2 Q2 T1 Q1 Tbar1 Qbar1 switch12 : ℝ)
    (hbounds_bar :
      lemma10StructuredBounds ratio T2 Q2 Tbar1 Qbar1 switch12)
    (hA_pos : 0 < T2 * switch12 + Q2)
    (hQ2_nonneg : 0 ≤ Q2)
    (hswitch_pos : 0 < switch12)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hgap_le :
      switch12 * T1 - Q1 ≤ switch12 * Tbar1 - Qbar1)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hQ1_le : Q1 ≤ Qbar1) :
    lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12 := by
  constructor
  · have hmono :=
      lemma10StructuredLowerFromGap_mono T2 Q2
        (switch12 * T1 - Q1) (switch12 * Tbar1 - Qbar1) switch12
        hA_pos hQ2_nonneg hswitch_pos hgap_nonneg hgap_le
    have hmono' :
        lemma10StructuredLower T2 Q2 T1 Q1 switch12 ≤
          lemma10StructuredLower T2 Q2 Tbar1 Qbar1 switch12 := by
      simpa [lemma10StructuredLower_eq_lowerFromGap] using hmono
    exact lt_of_le_of_lt hmono' hbounds_bar.1
  · have hmono :=
      lemma10StructuredUpperFromExitWeight_antitone Q1 Qbar1 switch12
        hswitch_lt_Q1 hQ1_le
    have hmono' :
        lemma10StructuredUpper T2 Q2 Tbar1 Qbar1 switch12 ≤
          lemma10StructuredUpper T2 Q2 T1 Q1 switch12 := by
      simpa [lemma10StructuredUpper_eq_upperFromExitWeight] using hmono
    exact lt_of_lt_of_le hbounds_bar.2 hmono'

/--
Lemma 10 upper-bound algebra: the current upper ratio bound implies positivity
of the structured derivative static term when `m = R2`.
-/
theorem lemma10StructuredStaticTerm_pos_of_upper_bound
    (ratio Q1 Q2 switch12 R2 z : ℝ)
    (hupper : ratio < lemma10StructuredUpperFromExitWeight Q1 switch12)
    (hz : z = ratio * R2)
    (hR2_pos : 0 < R2)
    (hQ2_pos : 0 < Q2)
    (hden_pos : 0 < Q1 - switch12) :
    0 < gn21StructuredDerivativeStaticTerm R2 z switch12 Q1 Q2 1 R2 := by
  unfold lemma10StructuredUpperFromExitWeight at hupper
  rw [lt_div_iff₀ hden_pos] at hupper
  have hmargin_pos : 0 < 1 - ratio * (Q1 - switch12) := by
    linarith
  have htail_eq :
      gn21StructuredDerivativeStaticTerm R2 z switch12 Q1 Q2 1 R2 =
        Q2 * R2 * (1 - ratio * (Q1 - switch12)) := by
    unfold gn21StructuredDerivativeStaticTerm
    rw [hz]
    ring
  rw [htail_eq]
  positivity

/--
Lemma 10 lower-bound algebra: the current lower ratio bound implies positivity
of the zero-time linearized structured derivative endpoint when `m = R2`.
-/
theorem lemma10StructuredLinearEndpoint_pos_of_lower_bound
    (ratio T2 Q2 T1 Q1 switch12 R2 z : ℝ)
    (hlower :
      lemma10StructuredLowerFromGap T2 Q2 (switch12 * T1 - Q1) switch12 <
        ratio)
    (hz : z = ratio * R2)
    (hR2_pos : 0 < R2)
    (hden_pos :
      0 < Q2 * (switch12 * T1 - Q1) +
        switch12 * (T2 * switch12 + Q2)) :
    0 < switch12 *
          gn21StructuredDerivativeSwitchBracket R2 z switch12 Q1 Q2 T1 T2 R2 +
        gn21StructuredDerivativeStaticTerm R2 z switch12 Q1 Q2 T2 R2 := by
  unfold lemma10StructuredLowerFromGap at hlower
  have hneg_ratio_lt :
      -ratio <
        (T2 * switch12 + Q2) /
          (Q2 * (switch12 * T1 - Q1) +
            switch12 * (T2 * switch12 + Q2)) := by
    linarith
  rw [lt_div_iff₀ hden_pos] at hneg_ratio_lt
  have hmargin_pos :
      0 <
        T2 * switch12 + Q2 +
          ratio *
            (Q2 * (switch12 * T1 - Q1) +
              switch12 * (T2 * switch12 + Q2)) := by
    nlinarith
  have hlinear_eq :
      switch12 *
          gn21StructuredDerivativeSwitchBracket R2 z switch12 Q1 Q2 T1 T2 R2 +
        gn21StructuredDerivativeStaticTerm R2 z switch12 Q1 Q2 T2 R2 =
        R2 *
          (T2 * switch12 + Q2 +
            ratio *
              (Q2 * (switch12 * T1 - Q1) +
                switch12 * (T2 * switch12 + Q2))) := by
    unfold gn21StructuredDerivativeSwitchBracket gn21StructuredDerivativeStaticTerm
    rw [hz]
    ring
  rw [hlinear_eq]
  exact mul_pos hR2_pos hmargin_pos

/--
Lemma 10 derivative-kernel positivity from the current structured ratio bounds.
This closes the algebraic part of the Lemma 10 endpoint, leaving only the
continuous Lemma 6 derivative-value certificate.
-/
theorem paper_lemma10_structured_derivative_kernel_pos_of_current_bounds
    (ratio u T2 Q2 T1 Q1 switch12 switch21 R2 z : ℝ)
    (hbounds : lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12)
    (hz : z = ratio * R2)
    (hR2_pos : 0 < R2)
    (hQ2_pos : 0 < Q2)
    (hswitch12_pos : 0 < switch12)
    (hsum : 0 < switch12 + switch21)
    (hu : 0 < u)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hA_pos : 0 < T2 * switch12 + Q2) :
    0 < gn21StructuredDerivativeSignKernel
      (gn21SwitchProb switch12 switch21 u) u R2 z switch12 Q1 Q2 T1 T2 R2 := by
  have hden_upper_pos : 0 < Q1 - switch12 :=
    sub_pos.mpr hswitch_lt_Q1
  have hden_lower_pos :
      0 < Q2 * (switch12 * T1 - Q1) +
        switch12 * (T2 * switch12 + Q2) := by
    have hleft : 0 ≤ Q2 * (switch12 * T1 - Q1) :=
      mul_nonneg (le_of_lt hQ2_pos) hgap_nonneg
    have hright : 0 < switch12 * (T2 * switch12 + Q2) :=
      mul_pos hswitch12_pos hA_pos
    nlinarith
  have htail_pos :
      0 < gn21StructuredDerivativeStaticTerm R2 z switch12 Q1 Q2 T2 R2 := by
    have htail_one :
        0 < gn21StructuredDerivativeStaticTerm R2 z switch12 Q1 Q2 1 R2 :=
      lemma10StructuredStaticTerm_pos_of_upper_bound
        ratio Q1 Q2 switch12 R2 z
        (by
          simpa [lemma10StructuredUpper_eq_upperFromExitWeight] using hbounds.2)
        hz hR2_pos hQ2_pos hden_upper_pos
    unfold gn21StructuredDerivativeStaticTerm at htail_one ⊢
    simpa using htail_one
  have hlinear_pos :
      0 < switch12 *
            gn21StructuredDerivativeSwitchBracket R2 z switch12 Q1 Q2 T1 T2 R2 +
          gn21StructuredDerivativeStaticTerm R2 z switch12 Q1 Q2 T2 R2 := by
    exact lemma10StructuredLinearEndpoint_pos_of_lower_bound
      ratio T2 Q2 T1 Q1 switch12 R2 z
      (by
        simpa [lemma10StructuredLower_eq_lowerFromGap] using hbounds.1)
      hz hR2_pos hden_lower_pos
  exact paper_remark2_structured_derivative_kernel_pos_of_ctmc_switch_and_tail
    u R2 z switch12 switch21 Q1 Q2 T1 T2 R2 hswitch12_pos hsum hu
    htail_pos hlinear_pos

/--
Lemma 10 analytic endpoint derivative, using the current structured ratio
bounds and the Lemma 6 endpoint-derivative certificate.
-/
theorem paper_lemma10_derivative_value_pos_of_current_bounds_certificate
    (C : Lemma6DerivativeFormulaCertificate)
    (ratio u T2 Q2 T1 Q1 switch12 switch21 R2 z : ℝ)
    (hq : C.q = gn21SwitchProb switch12 switch21 u)
    (hu_eq : C.u = u)
    (hwi : C.wi = R2 * u + z * gn21SwitchProb switch12 switch21 u)
    (hQi : C.Qi = Q1)
    (hQj : C.Qj = Q2)
    (hTi : C.Ti = T1)
    (hTj : C.Tj = T2)
    (hWi : C.Wi = R2 * (T1 - 1) + z * (Q1 - switch12))
    (hWj : C.Wj = R2 * T2)
    (hbounds : lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12)
    (hz : z = ratio * R2)
    (hR2_pos : 0 < R2)
    (hQ2_pos : 0 < Q2)
    (hswitch12_pos : 0 < switch12)
    (hsum : 0 < switch12 + switch21)
    (hu : 0 < u)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hA_pos : 0 < T2 * switch12 + Q2) :
    0 < C.derivativeValue := by
  apply paper_lemma6_derivative_value_pos_of_structured_kernel_pos_of_certificate
    C (gn21SwitchProb switch12 switch21 u) u R2 z switch12 Q1 Q2 T1 T2 R2
    hq hu_eq hwi hQi hQj hTi hTj hWi hWj
  exact paper_lemma10_structured_derivative_kernel_pos_of_current_bounds
    ratio u T2 Q2 T1 Q1 switch12 switch21 R2 z hbounds hz hR2_pos
    hQ2_pos hswitch12_pos hsum hu hswitch_lt_Q1 hgap_nonneg hA_pos

/--
Lemma 10 endpoint-improvement bridge: current structured ratio bounds and
endpoint derivative data produce a nearby right endpoint move with strictly
larger aggregate reward.
-/
theorem paper_lemma10_exists_pos_right_improvement_of_current_bounds_endpoint_data
    (D : Lemma6EndpointDerivativeData)
    (ratio u T2 Q2 T1 Q1 switch12 switch21 R2 z : ℝ)
    (hq : D.q = gn21SwitchProb switch12 switch21 u)
    (hu_eq : D.u = u)
    (hwi : D.wi = R2 * u + z * gn21SwitchProb switch12 switch21 u)
    (hQi : D.Qi = Q1)
    (hQj : D.Qj = Q2)
    (hTi : D.Ti = T1)
    (hTj : D.Tj = T2)
    (hWi : D.Wi = R2 * (T1 - 1) + z * (Q1 - switch12))
    (hWj : D.Wj = R2 * T2)
    (hbounds : lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12)
    (hz : z = ratio * R2)
    (hR2_pos : 0 < R2)
    (hQ2_pos : 0 < Q2)
    (hswitch12_pos : 0 < switch12)
    (hsum : 0 < switch12 + switch21)
    (hu : 0 < u)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hA_pos : 0 < T2 * switch12 + Q2) :
    ∃ ε : ℝ, 0 < ε ∧
      D.rewardAlongEndpoint D.u < D.rewardAlongEndpoint (D.u + ε) := by
  have hpos : 0 < D.derivativeValue := by
    exact paper_lemma10_derivative_value_pos_of_current_bounds_certificate
      (lemma6DerivativeFormulaCertificate_of_endpoint_data D)
      ratio u T2 Q2 T1 Q1 switch12 switch21 R2 z
      hq hu_eq hwi hQi hQj hTi hTj hWi hWj hbounds hz hR2_pos
      hQ2_pos hswitch12_pos hsum hu hswitch_lt_Q1 hgap_nonneg hA_pos
  exact exists_pos_right_improvement_of_hasDerivAt_pos D.has_derivative hpos

/--
Interval-density Lemma 10 endpoint-improvement bridge.  This is the
non-surge-state version specialized to the paper's upper-endpoint primitive
paths and CTMC structured price `R_2 u + z q(u)`.
-/
theorem paper_lemma10_exists_pos_right_improvement_of_interval_density_current_bounds
    (arrivalRate lowerEndpoint u T2 Q2 T1 Q1 switch12 switch21 R2 z ratio : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQ2_pos : 0 < Q2)
    (hden :
      gn21EndpointQiPath arrivalRate switch12 lowerEndpoint density
          (gn21SwitchProb switch12 switch21) u * T2 +
        Q2 *
          gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) volume
        lowerEndpoint u)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) (𝓝 u))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) u)
    (hw_int :
      IntervalIntegrable
        (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ *
          density τ) volume lowerEndpoint u)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ *
          density τ) (𝓝 u))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ *
          density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume lowerEndpoint u)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hQ1 :
      gn21EndpointQiPath arrivalRate switch12 lowerEndpoint density
        (gn21SwitchProb switch12 switch21) u = Q1)
    (hT1 :
      gn21EndpointTiPath arrivalRate lowerEndpoint density u = T1)
    (hW1 :
      gn21EndpointWiPath arrivalRate lowerEndpoint density
        (ctmcStructuredSurgePrice R2 z switch12 switch21) u =
          R2 * (T1 - 1) + z * (Q1 - switch12))
    (hbounds : lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12)
    (hz : z = ratio * R2)
    (hR2_pos : 0 < R2)
    (hswitch12_pos : 0 < switch12)
    (hsum : 0 < switch12 + switch21)
    (hu : 0 < u)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hA_pos : 0 < T2 * switch12 + Q2) :
    ∃ ε : ℝ, 0 < ε ∧
      gn21AggregateDynamicReward
          (gn21EndpointQiPath arrivalRate switch12 lowerEndpoint density
            (gn21SwitchProb switch12 switch21) u)
          Q2
          (gn21EndpointTiPath arrivalRate lowerEndpoint density u)
          T2
          (gn21EndpointWiPath arrivalRate lowerEndpoint density
            (ctmcStructuredSurgePrice R2 z switch12 switch21) u)
          (R2 * T2) <
        gn21AggregateDynamicReward
          (gn21EndpointQiPath arrivalRate switch12 lowerEndpoint density
            (gn21SwitchProb switch12 switch21) (u + ε))
          Q2
          (gn21EndpointTiPath arrivalRate lowerEndpoint density (u + ε))
          T2
          (gn21EndpointWiPath arrivalRate lowerEndpoint density
            (ctmcStructuredSurgePrice R2 z switch12 switch21) (u + ε))
          (R2 * T2) := by
  let D :=
    lemma6EndpointDerivativeData_of_interval_density_paths
      arrivalRate switch12 lowerEndpoint u Q2 T2 (R2 * T2) density
      (gn21SwitchProb switch12 switch21)
      (ctmcStructuredSurgePrice R2 z switch12 switch21)
      harrival_pos hdensity_pos hQ2_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont
  have h :=
    paper_lemma10_exists_pos_right_improvement_of_current_bounds_endpoint_data
      D ratio u T2 Q2 T1 Q1 switch12 switch21 R2 z
      (by rfl)
      (by rfl)
      (by rfl)
      (by simpa [D] using hQ1)
      (by rfl)
      (by simpa [D] using hT1)
      (by rfl)
      (by simpa [D] using hW1)
      (by rfl)
      hbounds hz hR2_pos hQ2_pos hswitch12_pos hsum hu hswitch_lt_Q1
      hgap_nonneg hA_pos
  simpa [D] using h

/--
Lower-endpoint Lemma 10 endpoint-improvement bridge.  This is the finite
tail-interval counterpart of the upper-endpoint bridge: a positive structured
kernel makes a small leftward lower-endpoint expansion strictly improve
aggregate reward.
-/
theorem paper_lemma10_exists_pos_left_improvement_of_lower_interval_density_current_bounds
    (arrivalRate upperEndpoint u T2 Q2 T1 Q1 switch12 switch21 R2 z ratio δ : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQ2_pos : 0 < Q2)
    (hden :
      gn21LowerEndpointQiPath arrivalRate switch12 upperEndpoint density
          (gn21SwitchProb switch12 switch21) u * T2 +
        Q2 *
          gn21LowerEndpointTiPath arrivalRate upperEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) volume
        u upperEndpoint)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) (𝓝 u))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) u)
    (hw_int :
      IntervalIntegrable
        (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ *
          density τ) volume u upperEndpoint)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ *
          density τ) (𝓝 u))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ *
          density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume u upperEndpoint)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hQ1 :
      gn21LowerEndpointQiPath arrivalRate switch12 upperEndpoint density
        (gn21SwitchProb switch12 switch21) u = Q1)
    (hT1 :
      gn21LowerEndpointTiPath arrivalRate upperEndpoint density u = T1)
    (hW1 :
      gn21LowerEndpointWiPath arrivalRate upperEndpoint density
        (ctmcStructuredSurgePrice R2 z switch12 switch21) u =
          R2 * (T1 - 1) + z * (Q1 - switch12))
    (hbounds : lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12)
    (hz : z = ratio * R2)
    (hR2_pos : 0 < R2)
    (hswitch12_pos : 0 < switch12)
    (hsum : 0 < switch12 + switch21)
    (hu : 0 < u)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hA_pos : 0 < T2 * switch12 + Q2)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switch12 upperEndpoint density
            (gn21SwitchProb switch12 switch21) u)
          Q2
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
          T2
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density
            (ctmcStructuredSurgePrice R2 z switch12 switch21) u)
          (R2 * T2) <
        gn21AggregateDynamicReward
          (gn21LowerEndpointQiPath arrivalRate switch12 upperEndpoint density
            (gn21SwitchProb switch12 switch21) (u - ε))
          Q2
          (gn21LowerEndpointTiPath arrivalRate upperEndpoint density (u - ε))
          T2
          (gn21LowerEndpointWiPath arrivalRate upperEndpoint density
            (ctmcStructuredSurgePrice R2 z switch12 switch21) (u - ε))
          (R2 * T2) := by
  have hstructured :
      0 < gn21StructuredDerivativeSignKernel
        (gn21SwitchProb switch12 switch21 u) u R2 z switch12 Q1 Q2 T1 T2 R2 :=
    paper_lemma10_structured_derivative_kernel_pos_of_current_bounds
      ratio u T2 Q2 T1 Q1 switch12 switch21 R2 z hbounds hz hR2_pos
      hQ2_pos hswitch12_pos hsum hu hswitch_lt_Q1 hgap_nonneg hA_pos
  have hkernel :
      0 < gn21DerivativeSignKernel (gn21SwitchProb switch12 switch21 u) u
        (ctmcStructuredSurgePrice R2 z switch12 switch21 u)
        (gn21LowerEndpointQiPath arrivalRate switch12 upperEndpoint density
          (gn21SwitchProb switch12 switch21) u)
        Q2
        (gn21LowerEndpointTiPath arrivalRate upperEndpoint density u)
        T2
        (gn21LowerEndpointWiPath arrivalRate upperEndpoint density
          (ctmcStructuredSurgePrice R2 z switch12 switch21) u)
        (R2 * T2) := by
    rw [hQ1, hT1, hW1]
    simp only [ctmcStructuredSurgePrice, structuredSurgePrice]
    rw [paper_remark2_structured_derivative_kernel_algebra]
    exact hstructured
  exact
    paper_lemma6_exists_pos_left_improvement_of_lower_interval_density_kernel_pos_lt
      arrivalRate switch12 upperEndpoint u Q2 T2 (R2 * T2) δ density
      (gn21SwitchProb switch12 switch21)
      (ctmcStructuredSurgePrice R2 z switch12 switch21)
      harrival_pos hdensity_pos hQ2_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont hkernel hδ

/--
Tail Lemma 10 endpoint-improvement bridge.  This is the unbounded
`(u,∞)` counterpart of the finite lower-endpoint bridge.
-/
theorem paper_lemma10_exists_pos_left_improvement_of_tail_interval_density_current_bounds
    (arrivalRate u T2 Q2 T1 Q1 switch12 switch21 R2 z ratio δ : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrivalRate)
    (hdensity_pos : 0 < density u)
    (hQ2_pos : 0 < Q2)
    (hden :
      gn21TailQiPath arrivalRate switch12 density
          (gn21SwitchProb switch12 switch21) u * T2 +
        Q2 * gn21TailTiPath arrivalRate density u ≠ 0)
    (hq_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ)
        (Set.Ioi (u - 1)) volume)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) (𝓝 u))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) u)
    (hw_int :
      IntegrableOn
        (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ *
          density τ) (Set.Ioi (u - 1)) volume)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ *
          density τ) (𝓝 u))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ *
          density τ) u)
    (ht_int :
      IntegrableOn (fun τ => τ * density τ) (Set.Ioi (u - 1)) volume)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hQ1 :
      gn21TailQiPath arrivalRate switch12 density
        (gn21SwitchProb switch12 switch21) u = Q1)
    (hT1 :
      gn21TailTiPath arrivalRate density u = T1)
    (hW1 :
      gn21TailWiPath arrivalRate density
        (ctmcStructuredSurgePrice R2 z switch12 switch21) u =
          R2 * (T1 - 1) + z * (Q1 - switch12))
    (hbounds : lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12)
    (hz : z = ratio * R2)
    (hR2_pos : 0 < R2)
    (hswitch12_pos : 0 < switch12)
    (hsum : 0 < switch12 + switch21)
    (hu : 0 < u)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hA_pos : 0 < T2 * switch12 + Q2)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      gn21AggregateDynamicReward
          (gn21TailQiPath arrivalRate switch12 density
            (gn21SwitchProb switch12 switch21) u)
          Q2
          (gn21TailTiPath arrivalRate density u)
          T2
          (gn21TailWiPath arrivalRate density
            (ctmcStructuredSurgePrice R2 z switch12 switch21) u)
          (R2 * T2) <
        gn21AggregateDynamicReward
          (gn21TailQiPath arrivalRate switch12 density
            (gn21SwitchProb switch12 switch21) (u - ε))
          Q2
          (gn21TailTiPath arrivalRate density (u - ε))
          T2
          (gn21TailWiPath arrivalRate density
            (ctmcStructuredSurgePrice R2 z switch12 switch21) (u - ε))
          (R2 * T2) := by
  have hstructured :
      0 < gn21StructuredDerivativeSignKernel
        (gn21SwitchProb switch12 switch21 u) u R2 z switch12 Q1 Q2 T1 T2 R2 :=
    paper_lemma10_structured_derivative_kernel_pos_of_current_bounds
      ratio u T2 Q2 T1 Q1 switch12 switch21 R2 z hbounds hz hR2_pos
      hQ2_pos hswitch12_pos hsum hu hswitch_lt_Q1 hgap_nonneg hA_pos
  have hkernel :
      0 < gn21DerivativeSignKernel (gn21SwitchProb switch12 switch21 u) u
        (ctmcStructuredSurgePrice R2 z switch12 switch21 u)
        (gn21TailQiPath arrivalRate switch12 density
          (gn21SwitchProb switch12 switch21) u)
        Q2
        (gn21TailTiPath arrivalRate density u)
        T2
        (gn21TailWiPath arrivalRate density
          (ctmcStructuredSurgePrice R2 z switch12 switch21) u)
        (R2 * T2) := by
    rw [hQ1, hT1, hW1]
    simp only [ctmcStructuredSurgePrice, structuredSurgePrice]
    rw [paper_remark2_structured_derivative_kernel_algebra]
    exact hstructured
  exact
    paper_lemma6_exists_pos_left_improvement_of_tail_interval_density_kernel_pos_lt
      arrivalRate switch12 u Q2 T2 (R2 * T2) δ density
      (gn21SwitchProb switch12 switch21)
      (ctmcStructuredSurgePrice R2 z switch12 switch21)
      harrival_pos hdensity_pos hQ2_pos hden hq_int hq_meas hq_cont
      hw_int hw_meas hw_cont ht_int ht_meas ht_cont hkernel hδ

/--
Lemma 10 feasibility bridge: under the positivity conditions used in the
source proof, ratio `0` satisfies the displayed open interval.
-/
theorem paper_lemma10_structured_bounds_feasible_of_positive_terms
    (T2 Q2 Tbar1 Qbar1 switch12 : ℝ)
    (hnum : 0 < T2 * switch12 + Q2)
    (hden :
      0 < Q2 * (switch12 * Tbar1 - Qbar1) +
        switch12 * (T2 * switch12 + Q2))
    (hupper_den : 0 < Qbar1 - switch12) :
    ∃ ratio : ℝ, lemma10StructuredBounds ratio T2 Q2 Tbar1 Qbar1 switch12 := by
  refine ⟨0, ?_, ?_⟩
  · unfold lemma10StructuredLower
    have hdiv :
        0 < lemma10StructuredLowerNumerator T2 Q2 switch12 /
          lemma10StructuredLowerDenominator T2 Q2 Tbar1 Qbar1 switch12 := by
      exact div_pos hnum hden
    linarith
  · unfold lemma10StructuredUpper
    exact div_pos zero_lt_one hupper_den

/--
Lemma 10 feasibility bridge using the named positive pieces of the source
interval. The admissible ratio is `0`, since the lower bound is negative and
the upper bound is positive.
-/
theorem paper_lemma10_structured_bounds_feasible_of_positive_pieces
    (T2 Q2 Tbar1 Qbar1 switch12 : ℝ)
    (hnum : 0 < lemma10StructuredLowerNumerator T2 Q2 switch12)
    (hden :
      0 < lemma10StructuredLowerDenominator T2 Q2 Tbar1 Qbar1 switch12)
    (hupper_den :
      0 < lemma10StructuredUpperDenominator Qbar1 switch12) :
    ∃ ratio : ℝ, lemma10StructuredBounds ratio T2 Q2 Tbar1 Qbar1 switch12 := by
  simpa [lemma10StructuredLowerNumerator,
    lemma10StructuredLowerDenominator, lemma10StructuredUpperDenominator] using
    paper_lemma10_structured_bounds_feasible_of_positive_terms
      T2 Q2 Tbar1 Qbar1 switch12 hnum hden hupper_den

/-- Lemma 10 certificate: the stated bounds imply positive upper-endpoint derivative in state 1. -/
structure Lemma10NonsurgeDerivativeCertificate where
  ratio : ℝ
  T2 : ℝ
  Q2 : ℝ
  Tbar1 : ℝ
  Qbar1 : ℝ
  switch12 : ℝ
  derivativeKernel : TripLength → ℝ
  bounds : lemma10StructuredBounds ratio T2 Q2 Tbar1 Qbar1 switch12
  derivativePositive : ∀ u : TripLength, 0 < u → 0 < derivativeKernel u

/--
Concrete Lemma 10 structured derivative certificate from the current-policy
ratio bounds and CTMC positivity assumptions.
-/
def lemma10NonsurgeDerivativeCertificate_of_current_bounds
    (ratio T2 Q2 T1 Q1 switch12 switch21 R2 z : ℝ)
    (hbounds : lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12)
    (hz : z = ratio * R2)
    (hR2_pos : 0 < R2)
    (hQ2_pos : 0 < Q2)
    (hswitch12_pos : 0 < switch12)
    (hsum : 0 < switch12 + switch21)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hA_pos : 0 < T2 * switch12 + Q2) :
    Lemma10NonsurgeDerivativeCertificate where
  ratio := ratio
  T2 := T2
  Q2 := Q2
  Tbar1 := T1
  Qbar1 := Q1
  switch12 := switch12
  derivativeKernel := fun u : TripLength =>
    gn21StructuredDerivativeSignKernel
      (gn21SwitchProb switch12 switch21 u) u R2 z switch12 Q1 Q2 T1 T2 R2
  bounds := hbounds
  derivativePositive := by
    intro u hu
    exact paper_lemma10_structured_derivative_kernel_pos_of_current_bounds
      ratio u T2 Q2 T1 Q1 switch12 switch21 R2 z hbounds hz hR2_pos
      hQ2_pos hswitch12_pos hsum hu hswitch_lt_Q1 hgap_nonneg hA_pos

/-- Lemma 10 supplies Lemma 5's positive derivative-shape witness. -/
theorem lemma5DerivativeShapeWitness_positive_of_lemma10_certificate
    (C : Lemma10NonsurgeDerivativeCertificate) :
    lemma5DerivativeShapeWitness C.derivativeKernel .positive := by
  exact C.derivativePositive

/--
Current-bounds form of Lemma 10's positive derivative-shape witness, avoiding
an intermediate certificate object when wiring the proof chain.
-/
theorem lemma5DerivativeShapeWitness_positive_of_lemma10_current_bounds
    (ratio T2 Q2 T1 Q1 switch12 switch21 R2 z : ℝ)
    (hbounds : lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12)
    (hz : z = ratio * R2)
    (hR2_pos : 0 < R2)
    (hQ2_pos : 0 < Q2)
    (hswitch12_pos : 0 < switch12)
    (hsum : 0 < switch12 + switch21)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hA_pos : 0 < T2 * switch12 + Q2) :
    lemma5DerivativeShapeWitness
      (fun u : TripLength =>
        gn21StructuredDerivativeSignKernel
          (gn21SwitchProb switch12 switch21 u) u R2 z switch12 Q1 Q2 T1 T2 R2)
      .positive := by
  intro u hu
  exact paper_lemma10_structured_derivative_kernel_pos_of_current_bounds
    ratio u T2 Q2 T1 Q1 switch12 switch21 R2 z hbounds hz hR2_pos
    hQ2_pos hswitch12_pos hsum hu hswitch_lt_Q1 hgap_nonneg hA_pos

/-- Lemma 10 endpoint, conditional on the structured derivative certificate. -/
theorem paper_lemma10_nonsurge_derivative_positive_of_certificate
    (C : Lemma10NonsurgeDerivativeCertificate) :
    lemma10StructuredBounds C.ratio C.T2 C.Q2 C.Tbar1 C.Qbar1 C.switch12 ∧
      ∀ u : TripLength, 0 < u → 0 < C.derivativeKernel u := by
  exact ⟨C.bounds, C.derivativePositive⟩

/-- Theorem 4 non-surge policy shapes. -/
def theorem4NonsurgeShape (σ : TripPolicy) : Prop :=
  (∃ t : ℝ, rejectsLongTrips t σ) ∨
    (∃ lo hi : ℝ, acceptsMiddleTrips lo hi σ) ∨
      acceptsAllTrips σ

/-- Theorem 4 surge policy shapes. -/
def theorem4SurgeShape (σ : TripPolicy) : Prop :=
  (∃ t : ℝ, rejectsShortTrips t σ) ∨
    (∃ lo hi : ℝ, rejectsMiddleTrips lo hi σ) ∨
      acceptsAllTrips σ

/--
Non-surge shape elimination away from accept-all.  This is the pure logical
case split needed by the endpoint-selection layer of Theorem 4.
-/
theorem theorem4NonsurgeShape_cases_of_not_acceptsAll
    {σ : TripPolicy}
    (hshape : theorem4NonsurgeShape σ)
    (hnot : ¬ acceptsAllTrips σ) :
    (∃ t : ℝ, rejectsLongTrips t σ) ∨
      ∃ lo hi : ℝ, acceptsMiddleTrips lo hi σ := by
  rcases hshape with hlong | hmiddle_or_all
  · exact Or.inl hlong
  · rcases hmiddle_or_all with hmiddle | hall
    · exact Or.inr hmiddle
    · exact False.elim (hnot hall)

/--
Surge shape elimination away from accept-all.  This exposes the short-tail and
middle-rejection endpoint cases.
-/
theorem theorem4SurgeShape_cases_of_not_acceptsAll
    {σ : TripPolicy}
    (hshape : theorem4SurgeShape σ)
    (hnot : ¬ acceptsAllTrips σ) :
    (∃ t : ℝ, rejectsShortTrips t σ) ∨
      ∃ lo hi : ℝ, rejectsMiddleTrips lo hi σ := by
  rcases hshape with hshort | hmiddle_or_all
  · exact Or.inl hshort
  · rcases hmiddle_or_all with hmiddle | hall
    · exact Or.inr hmiddle
    · exact False.elim (hnot hall)

/-- Lemma 5 derivative-shape outcomes admissible for Theorem 4 non-surge states. -/
def theorem4NonsurgeAllowedLemma5Shape : Lemma5DerivativeShape → Prop
  | .positive => True
  | .strictlyIncreasing => False
  | .strictlyDecreasing => True
  | .strictlyQuasiConvex => False
  | .strictlyQuasiConcave => True

/-- Lemma 5 derivative-shape outcomes admissible for Theorem 4 surge states. -/
def theorem4SurgeAllowedLemma5Shape : Lemma5DerivativeShape → Prop
  | .positive => True
  | .strictlyIncreasing => True
  | .strictlyDecreasing => False
  | .strictlyQuasiConvex => True
  | .strictlyQuasiConcave => False

/-- The accept-all Lemma 5 case is allowed in non-surge states. -/
theorem theorem4NonsurgeAllowedLemma5Shape_positive :
    theorem4NonsurgeAllowedLemma5Shape .positive := by
  trivial

/-- The decreasing Lemma 5 case is allowed in non-surge states. -/
theorem theorem4NonsurgeAllowedLemma5Shape_strictlyDecreasing :
    theorem4NonsurgeAllowedLemma5Shape .strictlyDecreasing := by
  trivial

/-- The quasi-concave Lemma 5 case is allowed in non-surge states. -/
theorem theorem4NonsurgeAllowedLemma5Shape_strictlyQuasiConcave :
    theorem4NonsurgeAllowedLemma5Shape .strictlyQuasiConcave := by
  trivial

/-- The accept-all Lemma 5 case is allowed in surge states. -/
theorem theorem4SurgeAllowedLemma5Shape_positive :
    theorem4SurgeAllowedLemma5Shape .positive := by
  trivial

/-- The increasing Lemma 5 case is allowed in surge states. -/
theorem theorem4SurgeAllowedLemma5Shape_strictlyIncreasing :
    theorem4SurgeAllowedLemma5Shape .strictlyIncreasing := by
  trivial

/-- The quasi-convex Lemma 5 case is allowed in surge states. -/
theorem theorem4SurgeAllowedLemma5Shape_strictlyQuasiConvex :
    theorem4SurgeAllowedLemma5Shape .strictlyQuasiConvex := by
  trivial

/-- Lemma 5's accept-all form is admissible for Theorem 4 non-surge states. -/
theorem theorem4NonsurgeShape_of_lemma5_positive
    {σ : TripPolicy}
    (h : lemma5PolicyForm .positive σ) :
    theorem4NonsurgeShape σ := by
  exact Or.inr (Or.inr h)

/-- Lemma 5's decreasing-derivative form is a Theorem 4 non-surge shape. -/
theorem theorem4NonsurgeShape_of_lemma5_strictlyDecreasing
    {σ : TripPolicy}
    (h : lemma5PolicyForm .strictlyDecreasing σ) :
    theorem4NonsurgeShape σ := by
  exact Or.inl h

/-- Lemma 5's quasi-concave form is a Theorem 4 non-surge shape. -/
theorem theorem4NonsurgeShape_of_lemma5_strictlyQuasiConcave
    {σ : TripPolicy}
    (h : lemma5PolicyForm .strictlyQuasiConcave σ) :
    theorem4NonsurgeShape σ := by
  exact Or.inr (Or.inl h)

/-- Lemma 5's accept-all form is admissible for Theorem 4 surge states. -/
theorem theorem4SurgeShape_of_lemma5_positive
    {σ : TripPolicy}
    (h : lemma5PolicyForm .positive σ) :
    theorem4SurgeShape σ := by
  exact Or.inr (Or.inr h)

/-- Lemma 5's increasing-derivative form is a Theorem 4 surge shape. -/
theorem theorem4SurgeShape_of_lemma5_strictlyIncreasing
    {σ : TripPolicy}
    (h : lemma5PolicyForm .strictlyIncreasing σ) :
    theorem4SurgeShape σ := by
  exact Or.inl h

/-- Lemma 5's quasi-convex form is a Theorem 4 surge shape. -/
theorem theorem4SurgeShape_of_lemma5_strictlyQuasiConvex
    {σ : TripPolicy}
    (h : lemma5PolicyForm .strictlyQuasiConvex σ) :
    theorem4SurgeShape σ := by
  exact Or.inr (Or.inl h)

/-- The canonical long-trip-rejection policy has a Theorem 4 non-surge shape. -/
theorem theorem4NonsurgeShape_rejectLongTripsPolicy (t : ℝ) :
    theorem4NonsurgeShape (rejectLongTripsPolicy t) := by
  exact theorem4NonsurgeShape_of_lemma5_strictlyDecreasing
    (lemma5PolicyForm_strictlyDecreasing_rejectLongTripsPolicy t)

/-- The canonical middle-acceptance policy has a Theorem 4 non-surge shape. -/
theorem theorem4NonsurgeShape_acceptMiddleTripsPolicy (lo hi : ℝ) :
    theorem4NonsurgeShape (acceptMiddleTripsPolicy lo hi) := by
  exact theorem4NonsurgeShape_of_lemma5_strictlyQuasiConcave
    (lemma5PolicyForm_strictlyQuasiConcave_acceptMiddleTripsPolicy lo hi)

/-- The canonical accept-all policy has a Theorem 4 non-surge shape. -/
theorem theorem4NonsurgeShape_acceptAllPolicy :
    theorem4NonsurgeShape acceptAllPolicy := by
  exact theorem4NonsurgeShape_of_lemma5_positive
    lemma5PolicyForm_positive_acceptAllPolicy

/-- The canonical short-trip-rejection policy has a Theorem 4 surge shape. -/
theorem theorem4SurgeShape_rejectShortTripsPolicy (t : ℝ) :
    theorem4SurgeShape (rejectShortTripsPolicy t) := by
  exact theorem4SurgeShape_of_lemma5_strictlyIncreasing
    (lemma5PolicyForm_strictlyIncreasing_rejectShortTripsPolicy t)

/-- The canonical middle-rejection policy has a Theorem 4 surge shape. -/
theorem theorem4SurgeShape_rejectMiddleTripsPolicy (lo hi : ℝ) :
    theorem4SurgeShape (rejectMiddleTripsPolicy lo hi) := by
  exact theorem4SurgeShape_of_lemma5_strictlyQuasiConvex
    (lemma5PolicyForm_strictlyQuasiConvex_rejectMiddleTripsPolicy lo hi)

/-- The canonical accept-all policy has a Theorem 4 surge shape. -/
theorem theorem4SurgeShape_acceptAllPolicy :
    theorem4SurgeShape acceptAllPolicy := by
  exact theorem4SurgeShape_of_lemma5_positive
    lemma5PolicyForm_positive_acceptAllPolicy

/-- Route any admissible Lemma 5 outcome to the Theorem 4 non-surge shape predicate. -/
theorem theorem4NonsurgeShape_of_allowed_lemma5_form
    {shape : Lemma5DerivativeShape} {σ : TripPolicy}
    (hallowed : theorem4NonsurgeAllowedLemma5Shape shape)
    (hform : lemma5PolicyForm shape σ) :
    theorem4NonsurgeShape σ := by
  cases shape with
  | positive =>
      exact theorem4NonsurgeShape_of_lemma5_positive hform
  | strictlyIncreasing =>
      exact False.elim hallowed
  | strictlyDecreasing =>
      exact theorem4NonsurgeShape_of_lemma5_strictlyDecreasing hform
  | strictlyQuasiConvex =>
      exact False.elim hallowed
  | strictlyQuasiConcave =>
      exact theorem4NonsurgeShape_of_lemma5_strictlyQuasiConcave hform

/-- Route any admissible Lemma 5 outcome to the Theorem 4 surge shape predicate. -/
theorem theorem4SurgeShape_of_allowed_lemma5_form
    {shape : Lemma5DerivativeShape} {σ : TripPolicy}
    (hallowed : theorem4SurgeAllowedLemma5Shape shape)
    (hform : lemma5PolicyForm shape σ) :
    theorem4SurgeShape σ := by
  cases shape with
  | positive =>
      exact theorem4SurgeShape_of_lemma5_positive hform
  | strictlyIncreasing =>
      exact theorem4SurgeShape_of_lemma5_strictlyIncreasing hform
  | strictlyDecreasing =>
      exact False.elim hallowed
  | strictlyQuasiConvex =>
      exact theorem4SurgeShape_of_lemma5_strictlyQuasiConvex hform
  | strictlyQuasiConcave =>
      exact False.elim hallowed

/--
Theorem 4 certificate: an optimal dynamic policy with the paper's allowable
non-surge and surge interval forms, plus necessity of those forms for any
optimal policy.
-/
structure Theorem4StructuralPolicyCertificate (R : DynamicReward) where
  policy : Fin 2 → TripPolicy
  optimal : dynamicOptimal R policy
  nonsurge_shape : theorem4NonsurgeShape (policy 0)
  surge_shape : theorem4SurgeShape (policy 1)
  only_policy_forms :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      theorem4NonsurgeShape (ρ 0) ∧ theorem4SurgeShape (ρ 1)

/--
Theorem 4 shape-derivation certificate: a closer interface to the proof chain
from Lemma 5. It records Lemma 5 forms for the exhibited optimum and for every
other optimum, plus the allowed-shape side conditions supplied by Lemmas 7-10.
-/
structure Theorem4ShapeDerivationCertificate (R : DynamicReward) where
  policy : Fin 2 → TripPolicy
  optimal : dynamicOptimal R policy
  nonsurge_shape : Lemma5DerivativeShape
  surge_shape : Lemma5DerivativeShape
  nonsurge_allowed : theorem4NonsurgeAllowedLemma5Shape nonsurge_shape
  surge_allowed : theorem4SurgeAllowedLemma5Shape surge_shape
  nonsurge_form : lemma5PolicyForm nonsurge_shape (policy 0)
  surge_form : lemma5PolicyForm surge_shape (policy 1)
  only_policy_forms :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      (∃ shape : Lemma5DerivativeShape,
        theorem4NonsurgeAllowedLemma5Shape shape ∧
          lemma5PolicyForm shape (ρ 0)) ∧
      (∃ shape : Lemma5DerivativeShape,
        theorem4SurgeAllowedLemma5Shape shape ∧
          lemma5PolicyForm shape (ρ 1))

/--
Theorem 4 assembly from Lemma 5-style shape derivation. This removes one layer
of opaque structural certification: once Lemma 5 and Lemmas 7-10 deliver
allowed per-state forms, the paper's structural conclusion is pure logic.
-/
def theorem4StructuralPolicyCertificate_of_shape_derivation
    (R : DynamicReward)
    (C : Theorem4ShapeDerivationCertificate R) :
    Theorem4StructuralPolicyCertificate R where
  policy := C.policy
  optimal := C.optimal
  nonsurge_shape :=
    theorem4NonsurgeShape_of_allowed_lemma5_form
      C.nonsurge_allowed C.nonsurge_form
  surge_shape :=
    theorem4SurgeShape_of_allowed_lemma5_form
      C.surge_allowed C.surge_form
  only_policy_forms := by
    intro ρ hρ
    rcases C.only_policy_forms ρ hρ with
      ⟨⟨nshape, hnallowed, hnform⟩, ⟨sshape, hsallowed, hsform⟩⟩
    exact
      ⟨theorem4NonsurgeShape_of_allowed_lemma5_form hnallowed hnform,
        theorem4SurgeShape_of_allowed_lemma5_form hsallowed hsform⟩

/-- Theorem 4 endpoint from the Lemma 5-style shape derivation certificate. -/
theorem paper_theorem4_dynamic_structural_policy_of_shape_derivation
    (R : DynamicReward) (C : Theorem4ShapeDerivationCertificate R) :
    dynamicOptimal R C.policy ∧
      theorem4NonsurgeShape (C.policy 0) ∧
      theorem4SurgeShape (C.policy 1) ∧
      ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
        theorem4NonsurgeShape (ρ 0) ∧ theorem4SurgeShape (ρ 1) := by
  let D := theorem4StructuralPolicyCertificate_of_shape_derivation R C
  exact ⟨D.optimal, D.nonsurge_shape, D.surge_shape, D.only_policy_forms⟩

/-- Theorem 4 endpoint, conditional on the derivative-shape and replacement certificates. -/
theorem paper_theorem4_dynamic_structural_policy_of_certificate
    (R : DynamicReward) (C : Theorem4StructuralPolicyCertificate R) :
    dynamicOptimal R C.policy ∧
      theorem4NonsurgeShape (C.policy 0) ∧
      theorem4SurgeShape (C.policy 1) ∧
      ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
        theorem4NonsurgeShape (ρ 0) ∧ theorem4SurgeShape (ρ 1) := by
  exact ⟨C.optimal, C.nonsurge_shape, C.surge_shape, C.only_policy_forms⟩

/--
Theorem 4 accept-all derivation certificate: the Lemma 9/10 positive
derivative cases make every optimal policy positive-form in both states, and
the feasible domain excludes non-positive trips.
-/
structure Theorem4AcceptAllDerivationCertificate (R : DynamicReward) where
  accept_all_optimal : dynamicOptimal R acceptAllDynamicPolicy
  feasible_optimal :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      ∀ i : Fin 2, ρ i ⊆ acceptAllPolicy
  nonsurge_positive_form :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      lemma5PolicyForm .positive (ρ 0)
  surge_positive_form :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      lemma5PolicyForm .positive (ρ 1)

/--
The accept-all derivation is a special case of the Theorem 4 shape-derivation
interface with positive Lemma 5 forms in both states.
-/
def theorem4ShapeDerivationCertificate_of_accept_all_derivation
    (R : DynamicReward)
    (C : Theorem4AcceptAllDerivationCertificate R) :
    Theorem4ShapeDerivationCertificate R where
  policy := acceptAllDynamicPolicy
  optimal := C.accept_all_optimal
  nonsurge_shape := .positive
  surge_shape := .positive
  nonsurge_allowed := theorem4NonsurgeAllowedLemma5Shape_positive
  surge_allowed := theorem4SurgeAllowedLemma5Shape_positive
  nonsurge_form := lemma5PolicyForm_positive_acceptAllPolicy
  surge_form := lemma5PolicyForm_positive_acceptAllPolicy
  only_policy_forms := by
    intro ρ hρ
    exact
      ⟨⟨.positive, theorem4NonsurgeAllowedLemma5Shape_positive,
          C.nonsurge_positive_form ρ hρ⟩,
        ⟨.positive, theorem4SurgeAllowedLemma5Shape_positive,
          C.surge_positive_form ρ hρ⟩⟩

/--
When Lemma 9/10 force positive Lemma 5 forms for every optimal policy,
accept-all is uniquely optimal.
-/
theorem paper_theorem4_accept_all_unique_optimal_of_positive_lemma5_forms
    (R : DynamicReward)
    (C : Theorem4AcceptAllDerivationCertificate R) :
    dynamicOptimal R acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicOptimal R ρ → ρ = acceptAllDynamicPolicy := by
  exact acceptAllDynamic_unique_optimal_of_statewise_accept_all_optima R
    C.accept_all_optimal C.feasible_optimal
    (by
      intro ρ hρ i
      fin_cases i
      · exact C.nonsurge_positive_form ρ hρ
      · exact C.surge_positive_form ρ hρ)

/-- The accept-all derivation also gives the ordinary Theorem 4 structural endpoint. -/
theorem paper_theorem4_dynamic_structural_policy_of_accept_all_derivation
    (R : DynamicReward)
    (C : Theorem4AcceptAllDerivationCertificate R) :
    dynamicOptimal R acceptAllDynamicPolicy ∧
      theorem4NonsurgeShape acceptAllPolicy ∧
      theorem4SurgeShape acceptAllPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
        theorem4NonsurgeShape (ρ 0) ∧ theorem4SurgeShape (ρ 1) := by
  simpa [acceptAllDynamicPolicy] using
    paper_theorem4_dynamic_structural_policy_of_shape_derivation R
      (theorem4ShapeDerivationCertificate_of_accept_all_derivation R C)

/--
Theorem 4 positive-replacement derivation certificate: every dynamic optimum
has statewise positive Lemma 5 replacement certificates for the local
continuation problems obtained by holding the other state fixed.
-/
structure Theorem4PositiveReplacementDerivationCertificate
    (R : DynamicReward) where
  accept_all_optimal : dynamicOptimal R acceptAllDynamicPolicy
  feasible_optimal :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      ∀ i : Fin 2, ρ i ⊆ acceptAllPolicy
  nonsurge_replacement :
    ∀ ρ : Fin 2 → TripPolicy, (hρ : dynamicOptimal R ρ) →
      Lemma5OptimizerReplacementCertificate
        (dynamicStateReward R ρ 0) (ρ 0) .positive
  surge_replacement :
    ∀ ρ : Fin 2 → TripPolicy, (hρ : dynamicOptimal R ρ) →
      Lemma5OptimizerReplacementCertificate
        (dynamicStateReward R ρ 1) (ρ 1) .positive

/--
Theorem 4 statewise accept-all reward certificate: the endpoint-improvement
part of Lemma 5 can target this interface directly.  It says accept-all weakly
improves each local continuation problem and strictly improves it unless the
current state policy already accepts all positive trips.
-/
structure Theorem4StatewiseAcceptAllRewardCertificate
    (R : DynamicReward) where
  accept_all_optimal : dynamicOptimal R acceptAllDynamicPolicy
  feasible_optimal :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      ∀ i : Fin 2, ρ i ⊆ acceptAllPolicy
  nonsurge_accept_all_reward_ge :
    ∀ ρ : Fin 2 → TripPolicy, (hρ : dynamicOptimal R ρ) →
      dynamicStateReward R ρ 0 (ρ 0) ≤
        dynamicStateReward R ρ 0 acceptAllPolicy
  nonsurge_accept_all_reward_gt_unless :
    ∀ ρ : Fin 2 → TripPolicy, (hρ : dynamicOptimal R ρ) →
      ¬ acceptsAllTrips (ρ 0) →
        dynamicStateReward R ρ 0 (ρ 0) <
          dynamicStateReward R ρ 0 acceptAllPolicy
  surge_accept_all_reward_ge :
    ∀ ρ : Fin 2 → TripPolicy, (hρ : dynamicOptimal R ρ) →
      dynamicStateReward R ρ 1 (ρ 1) ≤
        dynamicStateReward R ρ 1 acceptAllPolicy
  surge_accept_all_reward_gt_unless :
    ∀ ρ : Fin 2 → TripPolicy, (hρ : dynamicOptimal R ρ) →
      ¬ acceptsAllTrips (ρ 1) →
        dynamicStateReward R ρ 1 (ρ 1) <
          dynamicStateReward R ρ 1 acceptAllPolicy

/--
Global statewise accept-all reward certificate: replacing either state's policy
by accept-all weakly improves every dynamic policy, and strictly improves
optimal policies unless the relevant state already accepts all positive trips.
This version derives accept-all optimality instead of assuming it.
-/
structure Theorem4GlobalStatewiseAcceptAllRewardCertificate
    (R : DynamicReward) where
  feasible_optimal :
    ∀ ρ : Fin 2 → TripPolicy, dynamicOptimal R ρ →
      ∀ i : Fin 2, ρ i ⊆ acceptAllPolicy
  nonsurge_accept_all_reward_ge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicStateReward R ρ 0 (ρ 0) ≤
        dynamicStateReward R ρ 0 acceptAllPolicy
  surge_accept_all_reward_ge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicStateReward R ρ 1 (ρ 1) ≤
        dynamicStateReward R ρ 1 acceptAllPolicy
  nonsurge_accept_all_reward_gt_unless :
    ∀ ρ : Fin 2 → TripPolicy, (hρ : dynamicOptimal R ρ) →
      ¬ acceptsAllTrips (ρ 0) →
        dynamicStateReward R ρ 0 (ρ 0) <
          dynamicStateReward R ρ 0 acceptAllPolicy
  surge_accept_all_reward_gt_unless :
    ∀ ρ : Fin 2 → TripPolicy, (hρ : dynamicOptimal R ρ) →
      ¬ acceptsAllTrips (ρ 1) →
        dynamicStateReward R ρ 1 (ρ 1) <
          dynamicStateReward R ρ 1 acceptAllPolicy

/-- Global statewise reward improvements instantiate the statewise reward interface. -/
def theorem4StatewiseAcceptAllRewardCertificate_of_global_statewise_accept_all_reward
    (R : DynamicReward)
    (C : Theorem4GlobalStatewiseAcceptAllRewardCertificate R) :
    Theorem4StatewiseAcceptAllRewardCertificate R where
  accept_all_optimal :=
    dynamicOptimal_acceptAll_of_statewise_acceptAll_improvements R
      C.nonsurge_accept_all_reward_ge C.surge_accept_all_reward_ge
  feasible_optimal := C.feasible_optimal
  nonsurge_accept_all_reward_ge := by
    intro ρ _
    exact C.nonsurge_accept_all_reward_ge ρ
  nonsurge_accept_all_reward_gt_unless :=
    C.nonsurge_accept_all_reward_gt_unless
  surge_accept_all_reward_ge := by
    intro ρ _
    exact C.surge_accept_all_reward_ge ρ
  surge_accept_all_reward_gt_unless :=
    C.surge_accept_all_reward_gt_unless

/--
Statewise accept-all reward comparisons instantiate the positive Lemma 5
replacement interface.
-/
def theorem4PositiveReplacementDerivationCertificate_of_statewise_accept_all_reward
    (R : DynamicReward)
    (C : Theorem4StatewiseAcceptAllRewardCertificate R) :
    Theorem4PositiveReplacementDerivationCertificate R where
  accept_all_optimal := C.accept_all_optimal
  feasible_optimal := C.feasible_optimal
  nonsurge_replacement := by
    intro ρ hρ
    exact lemma5PositiveOptimizerReplacementCertificate_acceptAll
      (dynamicStateReward R ρ 0) (ρ 0)
      (C.nonsurge_accept_all_reward_ge ρ hρ)
      (C.nonsurge_accept_all_reward_gt_unless ρ hρ)
  surge_replacement := by
    intro ρ hρ
    exact lemma5PositiveOptimizerReplacementCertificate_acceptAll
      (dynamicStateReward R ρ 1) (ρ 1)
      (C.surge_accept_all_reward_ge ρ hρ)
      (C.surge_accept_all_reward_gt_unless ρ hρ)

/--
Statewise positive Lemma 5 replacement certificates produce the accept-all
Theorem 4 derivation by local optimality of every dynamic optimum.
-/
def theorem4AcceptAllDerivationCertificate_of_positive_replacement
    (R : DynamicReward)
    (C : Theorem4PositiveReplacementDerivationCertificate R) :
    Theorem4AcceptAllDerivationCertificate R where
  accept_all_optimal := C.accept_all_optimal
  feasible_optimal := C.feasible_optimal
  nonsurge_positive_form := by
    intro ρ hρ
    exact acceptsAllTrips_of_positive_optimizer_replacement_certificate_of_optimal
      (dynamicStateReward R ρ 0) (ρ 0) (C.nonsurge_replacement ρ hρ)
      (dynamicStateReward_optimal_of_dynamicOptimal R hρ 0)
  surge_positive_form := by
    intro ρ hρ
    exact acceptsAllTrips_of_positive_optimizer_replacement_certificate_of_optimal
      (dynamicStateReward R ρ 1) (ρ 1) (C.surge_replacement ρ hρ)
      (dynamicStateReward_optimal_of_dynamicOptimal R hρ 1)

/--
Theorem 4 accept-all uniqueness from statewise positive Lemma 5 replacement
certificates.
-/
theorem paper_theorem4_accept_all_unique_optimal_of_positive_replacement
    (R : DynamicReward)
    (C : Theorem4PositiveReplacementDerivationCertificate R) :
    dynamicOptimal R acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicOptimal R ρ → ρ = acceptAllDynamicPolicy := by
  exact paper_theorem4_accept_all_unique_optimal_of_positive_lemma5_forms R
    (theorem4AcceptAllDerivationCertificate_of_positive_replacement R C)

/--
Theorem 4 accept-all uniqueness from statewise accept-all reward comparisons.
-/
theorem paper_theorem4_accept_all_unique_optimal_of_statewise_accept_all_reward
    (R : DynamicReward)
    (C : Theorem4StatewiseAcceptAllRewardCertificate R) :
    dynamicOptimal R acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicOptimal R ρ → ρ = acceptAllDynamicPolicy := by
  exact paper_theorem4_accept_all_unique_optimal_of_positive_replacement R
    (theorem4PositiveReplacementDerivationCertificate_of_statewise_accept_all_reward
      R C)

/--
Theorem 4 accept-all uniqueness from global statewise accept-all reward
improvements.
-/
theorem paper_theorem4_accept_all_unique_optimal_of_global_statewise_accept_all_reward
    (R : DynamicReward)
    (C : Theorem4GlobalStatewiseAcceptAllRewardCertificate R) :
    dynamicOptimal R acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicOptimal R ρ → ρ = acceptAllDynamicPolicy := by
  exact paper_theorem4_accept_all_unique_optimal_of_statewise_accept_all_reward R
    (theorem4StatewiseAcceptAllRewardCertificate_of_global_statewise_accept_all_reward
      R C)

/--
Theorem 4 accept-all uniqueness from strict local improvements that rule out
non-accept-all optima.
-/
theorem paper_theorem4_accept_all_unique_optimal_of_strict_local_improvements
    (R : DynamicReward)
    (C : Theorem4StrictLocalImprovementCertificate R) :
    dynamicOptimal R acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicOptimal R ρ → ρ = acceptAllDynamicPolicy :=
  acceptAllDynamic_unique_optimal_of_strict_local_improvements R C

/-- Paper cross-state subcycle probability `p_{ij} = Q_i/(λ_i F_i+λ_{i→j})`. -/
def gn21CrossSubcycleProb
    (arrivalRate acceptProb switchRate exitWeight : ℝ) : ℝ :=
  exitWeight / (arrivalRate * acceptProb + switchRate)

/-- Time fraction from renewal-cycle subcycle probabilities and subcycle lengths. -/
def gn21TimeFractionFromCycles
    (otherToThisProb thisSubcycleLength thisToOtherProb otherSubcycleLength : ℝ) : ℝ :=
  otherToThisProb * thisSubcycleLength /
    (otherToThisProb * thisSubcycleLength +
      thisToOtherProb * otherSubcycleLength)

/-- Lemma 3 displayed time-fraction formula for state `i`. -/
def gn21TimeFractionFormula
    (arrivalI acceptI timeI exitWeightJ
      arrivalJ acceptJ timeJ exitWeightI : ℝ) : ℝ :=
  arrivalI * acceptI * timeI * exitWeightJ /
    (arrivalJ * acceptJ * timeJ * exitWeightI +
      arrivalI * acceptI * timeI * exitWeightJ)

/-- Lemma 3 displayed time-fraction formula using the paper's measured `T_i` and `Q_i`. -/
def gn21MeasuredTimeFraction
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI σJ : TripPolicy) : ℝ :=
  gn21TimeFractionFormula
    arrivalI (singleStateTripMass μI σI)
    (gn21StateCycleTime μI arrivalI σI)
    (gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ)
    arrivalJ (singleStateTripMass μJ σJ)
    (gn21StateCycleTime μJ arrivalJ σJ)
    (gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI)

/-- The two displayed time-fraction formulas for states `i` and `j` add to one. -/
theorem gn21TimeFractionFormula_add_swap_eq_one
    (arrivalI acceptI timeI exitWeightJ
      arrivalJ acceptJ timeJ exitWeightI : ℝ)
    (hden :
      arrivalJ * acceptJ * timeJ * exitWeightI +
          arrivalI * acceptI * timeI * exitWeightJ ≠ 0) :
    gn21TimeFractionFormula arrivalI acceptI timeI exitWeightJ
        arrivalJ acceptJ timeJ exitWeightI +
      gn21TimeFractionFormula arrivalJ acceptJ timeJ exitWeightI
        arrivalI acceptI timeI exitWeightJ = 1 := by
  unfold gn21TimeFractionFormula
  have hden' :
      arrivalI * acceptI * timeI * exitWeightJ +
          arrivalJ * acceptJ * timeJ * exitWeightI ≠ 0 := by
    simpa [add_comm] using hden
  field_simp [hden, hden']
  ring

/-- Lemma 3 measured time fractions for the two states add to one. -/
theorem paper_lemma3_measured_time_fractions_sum_to_one
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI σJ : TripPolicy)
    (hden :
      arrivalJ * singleStateTripMass μJ σJ *
            gn21StateCycleTime μJ arrivalJ σJ *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI +
          arrivalI * singleStateTripMass μI σI *
            gn21StateCycleTime μI arrivalI σI *
            gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ ≠ 0) :
    gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI σI σJ +
      gn21MeasuredTimeFraction μJ μI arrivalJ arrivalI switchJI switchIJ σJ σI =
        1 := by
  unfold gn21MeasuredTimeFraction
  exact gn21TimeFractionFormula_add_swap_eq_one
    arrivalI (singleStateTripMass μI σI)
    (gn21StateCycleTime μI arrivalI σI)
    (gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ)
    arrivalJ (singleStateTripMass μJ σJ)
    (gn21StateCycleTime μJ arrivalJ σJ)
    (gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI)
    hden

/--
Lemma 3 algebra: substituting the paper's subcycle length and transition
probability formulas into the renewal-cycle expression gives the displayed
closed form for `μ_i`.
-/
theorem paper_lemma3_time_fraction_formula_algebra
    (arrivalI acceptI switchI timeI exitWeightI
      arrivalJ acceptJ switchJ timeJ exitWeightJ : ℝ)
    (hi : arrivalI * acceptI + switchI ≠ 0)
    (hj : arrivalJ * acceptJ + switchJ ≠ 0) :
    gn21TimeFractionFromCycles
        (gn21CrossSubcycleProb arrivalJ acceptJ switchJ exitWeightJ)
        (gn21SubcycleLength arrivalI acceptI switchI timeI)
        (gn21CrossSubcycleProb arrivalI acceptI switchI exitWeightI)
        (gn21SubcycleLength arrivalJ acceptJ switchJ timeJ)
      =
        gn21TimeFractionFormula arrivalI acceptI timeI exitWeightJ
          arrivalJ acceptJ timeJ exitWeightI := by
  unfold gn21TimeFractionFromCycles gn21CrossSubcycleProb gn21SubcycleLength
    gn21TimeFractionFormula
  field_simp [hi, hj]
  ring

/--
Lemma 3 measured algebra: once the continuous `T_i(σ_i)` and `Q_i(σ_i)` set
integrals have been defined, the subcycle expression reduces to the displayed
time-fraction formula.
-/
theorem paper_lemma3_measured_time_fraction_formula_algebra
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI σJ : TripPolicy)
    (hi : arrivalI * singleStateTripMass μI σI + switchIJ ≠ 0)
    (hj : arrivalJ * singleStateTripMass μJ σJ + switchJI ≠ 0) :
    gn21TimeFractionFromCycles
        (gn21CrossSubcycleProb arrivalJ (singleStateTripMass μJ σJ) switchJI
          (gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ))
        (gn21SubcycleLength arrivalI (singleStateTripMass μI σI) switchIJ
          (gn21StateCycleTime μI arrivalI σI))
        (gn21CrossSubcycleProb arrivalI (singleStateTripMass μI σI) switchIJ
          (gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI))
        (gn21SubcycleLength arrivalJ (singleStateTripMass μJ σJ) switchJI
          (gn21StateCycleTime μJ arrivalJ σJ))
      =
        gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI σI σJ := by
  unfold gn21MeasuredTimeFraction
  exact paper_lemma3_time_fraction_formula_algebra
    arrivalI (singleStateTripMass μI σI) switchIJ
    (gn21StateCycleTime μI arrivalI σI)
    (gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI)
    arrivalJ (singleStateTripMass μJ σJ) switchJI
    (gn21StateCycleTime μJ arrivalJ σJ)
    (gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ)
    hi hj

/-!
Lemma 1 decomposes dynamic earnings into state reward rates and time fractions.
The continuous renewal-reward and CTMC cycle construction is still the source
proof obligation; the definitions and theorem below close the displayed
reward-rate cancellation once subcycle earnings and lengths have been reduced
to their common cycle factor.
-/

/-- Paper subcycle earnings with the same cycle factor as subcycle length. -/
def gn21SubcycleEarning
    (arrivalRate acceptProb switchRate meanEarning : ℝ) : ℝ :=
  (arrivalRate * acceptProb) / (arrivalRate * acceptProb + switchRate) *
    meanEarning

/-- Paper one-state reward rate `W_i / T_i`. -/
def gn21StateRewardRate (meanEarning stateCycleTime : ℝ) : ℝ :=
  meanEarning / stateCycleTime

/-- Lemma 1 mean earning per accepted trip, `W_i(σ_i)`. -/
def gn21StateMeanEarning
    (μ : Measure TripLength) (w : PricingFunction) (σ : TripPolicy) : ℝ :=
  singleStateTripPayment μ w σ / singleStateTripMass μ σ

/-- Lemma 1 measured state reward rate `R_i(w_i,σ_i)=W_i(σ_i)/T_i(σ_i)`. -/
def gn21MeasuredStateRewardRate
    (μ : Measure TripLength) (arrivalRate : ℝ)
    (w : PricingFunction) (σ : TripPolicy) : ℝ :=
  gn21StateRewardRate
    (gn21StateMeanEarning μ w σ)
    (gn21StateCycleTime μ arrivalRate σ)

/-- Lemma 1 dynamic reward decomposition from time fractions and state reward rates. -/
def gn21DynamicRewardFormula
    (timeFractionI rewardRateI timeFractionJ rewardRateJ : ℝ) : ℝ :=
  timeFractionI * rewardRateI + timeFractionJ * rewardRateJ

/--
Lemma 1 measured dynamic reward formula with the paper's measured time
fractions and one-state reward rates.
-/
def gn21MeasuredDynamicReward
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy) : ℝ :=
  gn21DynamicRewardFormula
    (gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI σI σJ)
    (gn21MeasuredStateRewardRate μI arrivalI wI σI)
    (gn21MeasuredTimeFraction μJ μI arrivalJ arrivalI switchJI switchIJ σJ σI)
    (gn21MeasuredStateRewardRate μJ arrivalJ wJ σJ)

/-- Lemma 1 measured endpoint: dynamic reward decomposes into `μ_i R_i + μ_j R_j`. -/
theorem paper_lemma1_measured_dynamic_reward_decomposition
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ σI σJ =
      gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI σI σJ *
          gn21MeasuredStateRewardRate μI arrivalI wI σI +
        gn21MeasuredTimeFraction μJ μI arrivalJ arrivalI switchJI switchIJ σJ σI *
          gn21MeasuredStateRewardRate μJ arrivalJ wJ σJ := by
  rfl

/--
Measured one-state reward-rate algebra in Appendix-D scaled primitives:
`R_i = W_i/T_i`.
-/
theorem gn21MeasuredStateRewardRate_eq_scaled_primitives
    (μ : Measure TripLength) (arrivalRate : ℝ)
    (w : PricingFunction) (σ : TripPolicy)
    (hmass : singleStateTripMass μ σ ≠ 0)
    (harrivalMass : arrivalRate * singleStateTripMass μ σ ≠ 0) :
    gn21MeasuredStateRewardRate μ arrivalRate w σ =
      gn21ScaledStateEarning μ arrivalRate w σ /
        gn21ScaledStateTime μ arrivalRate σ := by
  unfold gn21MeasuredStateRewardRate gn21StateRewardRate gn21StateMeanEarning
    gn21StateCycleTime gn21ScaledStateEarning gn21ScaledStateTime
  have harrival : arrivalRate ≠ 0 := by
    intro hzero
    exact harrivalMass (by simp [hzero])
  field_simp [hmass, harrival, harrivalMass]

/--
Measured time-fraction algebra in Appendix-D scaled primitives:
`mu_i = T_i Q_j / (T_j Q_i + T_i Q_j)`.
-/
theorem gn21MeasuredTimeFraction_eq_scaled_primitives
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI σJ : TripPolicy)
    (hmassI : singleStateTripMass μI σI ≠ 0)
    (hmassJ : singleStateTripMass μJ σJ ≠ 0)
    (harrivalMassI : arrivalI * singleStateTripMass μI σI ≠ 0)
    (harrivalMassJ : arrivalJ * singleStateTripMass μJ σJ ≠ 0) :
    gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI σI σJ =
      gn21ScaledStateTime μI arrivalI σI *
          gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ /
        (gn21ScaledStateTime μJ arrivalJ σJ *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI +
          gn21ScaledStateTime μI arrivalI σI *
            gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ) := by
  unfold gn21MeasuredTimeFraction gn21TimeFractionFormula
  change
    gn21ScaledStateCycleTime μI arrivalI σI *
          gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ /
        (gn21ScaledStateCycleTime μJ arrivalJ σJ *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI +
          gn21ScaledStateCycleTime μI arrivalI σI *
            gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ) =
      gn21ScaledStateTime μI arrivalI σI *
          gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ /
        (gn21ScaledStateTime μJ arrivalJ σJ *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI +
          gn21ScaledStateTime μI arrivalI σI *
            gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ)
  rw [gn21ScaledStateCycleTime_eq_scaledStateTime μI arrivalI σI
      hmassI harrivalMassI,
    gn21ScaledStateCycleTime_eq_scaledStateTime μJ arrivalJ σJ
      hmassJ harrivalMassJ]

/--
Lemma 1/3 measured algebra in Appendix-D primitives: after scaling out the
arrival-rate and acceptance-mass factors, the measured two-state dynamic reward
is the aggregate quotient used in Lemma 6.
-/
theorem paper_lemma1_measured_dynamic_reward_eq_aggregate_scaled_primitives
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy)
    (hmassI : singleStateTripMass μI σI ≠ 0)
    (hmassJ : singleStateTripMass μJ σJ ≠ 0)
    (harrivalMassI : arrivalI * singleStateTripMass μI σI ≠ 0)
    (harrivalMassJ : arrivalJ * singleStateTripMass μJ σJ ≠ 0)
    (hscaledTimeI : gn21ScaledStateTime μI arrivalI σI ≠ 0)
    (hscaledTimeJ : gn21ScaledStateTime μJ arrivalJ σJ ≠ 0)
    (hden :
      gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI *
          gn21ScaledStateTime μJ arrivalJ σJ +
        gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ *
          gn21ScaledStateTime μI arrivalI σI ≠ 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ σI σJ =
      gn21AggregateDynamicReward
        (gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI)
        (gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ)
        (gn21ScaledStateTime μI arrivalI σI)
        (gn21ScaledStateTime μJ arrivalJ σJ)
        (gn21ScaledStateEarning μI arrivalI wI σI)
        (gn21ScaledStateEarning μJ arrivalJ wJ σJ) := by
  have hRi :=
    gn21MeasuredStateRewardRate_eq_scaled_primitives
      μI arrivalI wI σI hmassI harrivalMassI
  have hRj :=
    gn21MeasuredStateRewardRate_eq_scaled_primitives
      μJ arrivalJ wJ σJ hmassJ harrivalMassJ
  have hμi :=
    gn21MeasuredTimeFraction_eq_scaled_primitives
      μI μJ arrivalI arrivalJ switchIJ switchJI σI σJ
      hmassI hmassJ harrivalMassI harrivalMassJ
  have hμj :=
    gn21MeasuredTimeFraction_eq_scaled_primitives
      μJ μI arrivalJ arrivalI switchJI switchIJ σJ σI
      hmassJ hmassI harrivalMassJ harrivalMassI
  have hden_time :
      gn21ScaledStateTime μJ arrivalJ σJ *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI +
          gn21ScaledStateTime μI arrivalI σI *
            gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hden
  have hden_time_swap :
      gn21ScaledStateTime μI arrivalI σI *
            gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ +
          gn21ScaledStateTime μJ arrivalJ σJ *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI ≠ 0 := by
    simpa [add_comm] using hden_time
  unfold gn21MeasuredDynamicReward gn21DynamicRewardFormula
  rw [hμi, hμj, hRi, hRj]
  unfold gn21AggregateDynamicReward
  field_simp [hden, hden_time, hden_time_swap, hscaledTimeI, hscaledTimeJ]
  ring

/--
Measured two-state reward written directly in the Appendix-D `Q,T,W`
aggregate primitives.
-/
def gn21MeasuredAggregateRewardPrimitives
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy) : ℝ :=
  gn21AggregateDynamicReward
    (gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI)
    (gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ)
    (gn21ScaledStateTime μI arrivalI σI)
    (gn21ScaledStateTime μJ arrivalJ σJ)
    (gn21ScaledStateEarning μI arrivalI wI σI)
    (gn21ScaledStateEarning μJ arrivalJ wJ σJ)

/--
Nondegeneracy side conditions needed to identify measured dynamic reward with
the Appendix-D aggregate quotient for a fixed pair of state policies.
-/
structure GN21MeasuredPairNondegenerate
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI σJ : TripPolicy) : Prop where
  massI_ne : singleStateTripMass μI σI ≠ 0
  massJ_ne : singleStateTripMass μJ σJ ≠ 0
  arrivalMassI_ne : arrivalI * singleStateTripMass μI σI ≠ 0
  arrivalMassJ_ne : arrivalJ * singleStateTripMass μJ σJ ≠ 0
  scaledTimeI_ne : gn21ScaledStateTime μI arrivalI σI ≠ 0
  scaledTimeJ_ne : gn21ScaledStateTime μJ arrivalJ σJ ≠ 0
  denominator_ne :
    gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI *
        gn21ScaledStateTime μJ arrivalJ σJ +
      gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ *
        gn21ScaledStateTime μI arrivalI σI ≠ 0

/-- Positive primitive conditions imply the measured pair is nondegenerate. -/
theorem gn21MeasuredPairNondegenerate_of_positive_primitives
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI σJ : TripPolicy)
    (hmassI_pos : 0 < singleStateTripMass μI σI)
    (hmassJ_pos : 0 < singleStateTripMass μJ σJ)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hscaledTimeI_pos : 0 < gn21ScaledStateTime μI arrivalI σI)
    (hscaledTimeJ_pos : 0 < gn21ScaledStateTime μJ arrivalJ σJ)
    (hexitI_pos :
      0 < gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI)
    (hexitJ_pos :
      0 < gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ) :
    GN21MeasuredPairNondegenerate μI μJ arrivalI arrivalJ switchIJ switchJI
      σI σJ where
  massI_ne := ne_of_gt hmassI_pos
  massJ_ne := ne_of_gt hmassJ_pos
  arrivalMassI_ne := ne_of_gt (mul_pos harrivalI_pos hmassI_pos)
  arrivalMassJ_ne := ne_of_gt (mul_pos harrivalJ_pos hmassJ_pos)
  scaledTimeI_ne := ne_of_gt hscaledTimeI_pos
  scaledTimeJ_ne := ne_of_gt hscaledTimeJ_pos
  denominator_ne := by
    have hleft :
        0 <
          gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI *
            gn21ScaledStateTime μJ arrivalJ σJ :=
      mul_pos hexitI_pos hscaledTimeJ_pos
    have hright :
        0 <
          gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ *
            gn21ScaledStateTime μI arrivalI σI :=
      mul_pos hexitJ_pos hscaledTimeI_pos
    exact ne_of_gt (add_pos hleft hright)

/--
Measured pair nondegeneracy from the standard positive-measure and feasible
measurable-policy assumptions.
-/
theorem gn21MeasuredPairNondegenerate_of_positive_measure
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI σJ : TripPolicy)
    (hmassI_pos : 0 < singleStateTripMass μI σI)
    (hmassJ_pos : 0 < singleStateTripMass μJ σJ)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσI_measurable : MeasurableSet σI)
    (hσJ_measurable : MeasurableSet σJ)
    (hσI_positive : σI ⊆ acceptAllPolicy)
    (hσJ_positive : σJ ⊆ acceptAllPolicy) :
    GN21MeasuredPairNondegenerate μI μJ arrivalI arrivalJ switchIJ switchJI
      σI σJ := by
  have hsumIJ : 0 < switchIJ + switchJI := by linarith
  have hsumJI : 0 < switchJI + switchIJ := by linarith
  exact gn21MeasuredPairNondegenerate_of_positive_primitives
    μI μJ arrivalI arrivalJ switchIJ switchJI σI σJ
    hmassI_pos hmassJ_pos harrivalI_pos harrivalJ_pos
    (gn21ScaledStateTime_pos_of_nonneg μI arrivalI σI
      (le_of_lt harrivalI_pos) hσI_measurable hσI_positive)
    (gn21ScaledStateTime_pos_of_nonneg μJ arrivalJ σJ
      (le_of_lt harrivalJ_pos) hσJ_measurable hσJ_positive)
    (gn21ExitWeightIntegral_pos_of_switch_pos μI arrivalI switchIJ switchJI
      σI (le_of_lt harrivalI_pos) hswitchIJ_pos hsumIJ hσI_measurable
      hσI_positive)
    (gn21ExitWeightIntegral_pos_of_switch_pos μJ arrivalJ switchJI switchIJ
      σJ (le_of_lt harrivalJ_pos) hswitchJI_pos hsumJI hσJ_measurable
      hσJ_positive)

/--
Measured pair nondegeneracy when the right/state-`J` policy is an upper-endpoint
interval.  This discharges the interval measurability and positive-trip
feasibility side conditions, leaving only positive mass and rate assumptions.
-/
theorem gn21MeasuredPairNondegenerate_of_positive_measure_upperEndpoint_right
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI : TripPolicy)
    (lowerEndpoint x : ℝ)
    (hmassI_pos : 0 < singleStateTripMass μI σI)
    (hmassJ_pos :
      0 < singleStateTripMass μJ
        (gn21UpperEndpointPolicy lowerEndpoint x))
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσI_measurable : MeasurableSet σI)
    (hσI_positive : σI ⊆ acceptAllPolicy)
    (hlower_nonneg : 0 ≤ lowerEndpoint) :
    GN21MeasuredPairNondegenerate μI μJ arrivalI arrivalJ switchIJ switchJI
      σI (gn21UpperEndpointPolicy lowerEndpoint x) := by
  exact
    gn21MeasuredPairNondegenerate_of_positive_measure
      μI μJ arrivalI arrivalJ switchIJ switchJI
      σI (gn21UpperEndpointPolicy lowerEndpoint x)
      hmassI_pos hmassJ_pos harrivalI_pos harrivalJ_pos
      hswitchIJ_pos hswitchJI_pos hσI_measurable
      (measurableSet_gn21UpperEndpointPolicy lowerEndpoint x)
      hσI_positive
      (gn21UpperEndpointPolicy_subset_acceptAllPolicy lowerEndpoint x
        hlower_nonneg)

/--
Measured pair nondegeneracy when the left/state-`I` policy is an upper-endpoint
interval.
-/
theorem gn21MeasuredPairNondegenerate_of_positive_measure_upperEndpoint_left
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (lowerEndpoint x : ℝ)
    (σJ : TripPolicy)
    (hmassI_pos :
      0 < singleStateTripMass μI
        (gn21UpperEndpointPolicy lowerEndpoint x))
    (hmassJ_pos : 0 < singleStateTripMass μJ σJ)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσJ_measurable : MeasurableSet σJ)
    (hσJ_positive : σJ ⊆ acceptAllPolicy)
    (hlower_nonneg : 0 ≤ lowerEndpoint) :
    GN21MeasuredPairNondegenerate μI μJ arrivalI arrivalJ switchIJ switchJI
      (gn21UpperEndpointPolicy lowerEndpoint x) σJ := by
  exact
    gn21MeasuredPairNondegenerate_of_positive_measure
      μI μJ arrivalI arrivalJ switchIJ switchJI
      (gn21UpperEndpointPolicy lowerEndpoint x) σJ
      hmassI_pos hmassJ_pos harrivalI_pos harrivalJ_pos
      hswitchIJ_pos hswitchJI_pos
      (measurableSet_gn21UpperEndpointPolicy lowerEndpoint x)
      hσJ_measurable
      (gn21UpperEndpointPolicy_subset_acceptAllPolicy lowerEndpoint x
        hlower_nonneg)
      hσJ_positive

/--
Measured pair nondegeneracy when the right/state-`J` policy is an upper-endpoint
interval under an NNReal density with finite positive interval mass.
-/
theorem gn21MeasuredPairNondegenerate_of_upperEndpoint_withDensity_right
    (μI : Measure TripLength)
    (density : TripLength → NNReal)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI : TripPolicy)
    (lowerEndpoint x : ℝ)
    (hmassI_pos : 0 < singleStateTripMass μI σI)
    (hdensity_meas : Measurable density)
    (hlt : lowerEndpoint < x)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21UpperEndpointPolicy lowerEndpoint x) ≠ ∞)
    (hpos :
      ∀ τ, τ ∈ gn21UpperEndpointPolicy lowerEndpoint x → density τ ≠ 0)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσI_measurable : MeasurableSet σI)
    (hσI_positive : σI ⊆ acceptAllPolicy)
    (hlower_nonneg : 0 ≤ lowerEndpoint) :
    GN21MeasuredPairNondegenerate μI
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
      arrivalI arrivalJ switchIJ switchJI
      σI (gn21UpperEndpointPolicy lowerEndpoint x) := by
  exact
    gn21MeasuredPairNondegenerate_of_positive_measure_upperEndpoint_right
      μI (volume.withDensity fun τ => (density τ : ℝ≥0∞))
      arrivalI arrivalJ switchIJ switchJI σI lowerEndpoint x
      hmassI_pos
      (singleStateTripMass_upperEndpoint_withDensity_pos_of_pos_on
        density hdensity_meas lowerEndpoint x hlt hfinite hpos)
      harrivalI_pos harrivalJ_pos hswitchIJ_pos hswitchJI_pos
      hσI_measurable hσI_positive hlower_nonneg

/--
Measured pair nondegeneracy when the left/state-`I` policy is an upper-endpoint
interval under an NNReal density with finite positive interval mass.
-/
theorem gn21MeasuredPairNondegenerate_of_upperEndpoint_withDensity_left
    (μJ : Measure TripLength)
    (density : TripLength → NNReal)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (lowerEndpoint x : ℝ)
    (σJ : TripPolicy)
    (hdensity_meas : Measurable density)
    (hlt : lowerEndpoint < x)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21UpperEndpointPolicy lowerEndpoint x) ≠ ∞)
    (hpos :
      ∀ τ, τ ∈ gn21UpperEndpointPolicy lowerEndpoint x → density τ ≠ 0)
    (hmassJ_pos : 0 < singleStateTripMass μJ σJ)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσJ_measurable : MeasurableSet σJ)
    (hσJ_positive : σJ ⊆ acceptAllPolicy)
    (hlower_nonneg : 0 ≤ lowerEndpoint) :
    GN21MeasuredPairNondegenerate
      (volume.withDensity fun τ => (density τ : ℝ≥0∞)) μJ
      arrivalI arrivalJ switchIJ switchJI
      (gn21UpperEndpointPolicy lowerEndpoint x) σJ := by
  exact
    gn21MeasuredPairNondegenerate_of_positive_measure_upperEndpoint_left
      (volume.withDensity fun τ => (density τ : ℝ≥0∞)) μJ
      arrivalI arrivalJ switchIJ switchJI lowerEndpoint x σJ
      (singleStateTripMass_upperEndpoint_withDensity_pos_of_pos_on
        density hdensity_meas lowerEndpoint x hlt hfinite hpos)
      hmassJ_pos harrivalI_pos harrivalJ_pos hswitchIJ_pos hswitchJI_pos
      hσJ_measurable hσJ_positive hlower_nonneg

/--
Measured pair nondegeneracy when the right/state-`J` policy is a concrete
lower-cutoff middle-rejection replacement under a positive NNReal density.
-/
theorem gn21MeasuredPairNondegenerate_of_rejectMiddleLoReplacement_withDensity_right
    (μI : Measure TripLength)
    (density : TripLength → NNReal)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI : TripPolicy)
    (lo hi ε : ℝ)
    (hmassI_pos : 0 < singleStateTripMass μI σI)
    (hdensity_meas : Measurable density)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21RejectMiddleLoReplacement lo hi ε) ≠ ∞)
    (hpos :
      ∀ τ, τ ∈ gn21RejectMiddleLoReplacement lo hi ε → density τ ≠ 0)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσI_measurable : MeasurableSet σI)
    (hσI_positive : σI ⊆ acceptAllPolicy) :
    GN21MeasuredPairNondegenerate μI
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
      arrivalI arrivalJ switchIJ switchJI
      σI (gn21RejectMiddleLoReplacement lo hi ε) := by
  exact
    gn21MeasuredPairNondegenerate_of_positive_measure
      μI (volume.withDensity fun τ => (density τ : ℝ≥0∞))
      arrivalI arrivalJ switchIJ switchJI
      σI (gn21RejectMiddleLoReplacement lo hi ε)
      hmassI_pos
      (singleStateTripMass_rejectMiddleLoReplacement_withDensity_pos_of_pos_on
        density hdensity_meas lo hi ε hfinite hpos)
      harrivalI_pos harrivalJ_pos hswitchIJ_pos hswitchJI_pos
      hσI_measurable
      (measurableSet_gn21RejectMiddleLoReplacement lo hi ε)
      hσI_positive
      (gn21RejectMiddleLoReplacement_subset_acceptAllPolicy lo hi ε)

/--
Measured pair nondegeneracy when the right/state-`J` policy is a concrete
upper-cutoff middle-rejection replacement under a positive NNReal density.
-/
theorem gn21MeasuredPairNondegenerate_of_rejectMiddleHiReplacement_withDensity_right
    (μI : Measure TripLength)
    (density : TripLength → NNReal)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI : TripPolicy)
    (lo hi ε : ℝ)
    (hmassI_pos : 0 < singleStateTripMass μI σI)
    (hdensity_meas : Measurable density)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21RejectMiddleHiReplacement lo hi ε) ≠ ∞)
    (hpos :
      ∀ τ, τ ∈ gn21RejectMiddleHiReplacement lo hi ε → density τ ≠ 0)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσI_measurable : MeasurableSet σI)
    (hσI_positive : σI ⊆ acceptAllPolicy) :
    GN21MeasuredPairNondegenerate μI
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
      arrivalI arrivalJ switchIJ switchJI
      σI (gn21RejectMiddleHiReplacement lo hi ε) := by
  exact
    gn21MeasuredPairNondegenerate_of_positive_measure
      μI (volume.withDensity fun τ => (density τ : ℝ≥0∞))
      arrivalI arrivalJ switchIJ switchJI
      σI (gn21RejectMiddleHiReplacement lo hi ε)
      hmassI_pos
      (singleStateTripMass_rejectMiddleHiReplacement_withDensity_pos_of_pos_on
        density hdensity_meas lo hi ε hfinite hpos)
      harrivalI_pos harrivalJ_pos hswitchIJ_pos hswitchJI_pos
      hσI_measurable
      (measurableSet_gn21RejectMiddleHiReplacement lo hi ε)
      hσI_positive
      (gn21RejectMiddleHiReplacement_subset_acceptAllPolicy lo hi ε)

/--
Pointwise finite positive-density assumptions produce the nondegeneracy
function required by the lower-cutoff reject-middle strict-local bridge.
-/
theorem gn21MeasuredPairNondegenerate_rejectMiddleLoReplacement_withDensity_right_forall
    (μI : Measure TripLength)
    (density : TripLength → NNReal)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI : TripPolicy)
    (lo hi δ : ℝ)
    (hmassI_pos : 0 < singleStateTripMass μI σI)
    (hdensity_meas : Measurable density)
    (hfinite :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
          (gn21RejectMiddleLoReplacement lo hi ε) ≠ ∞)
    (hpos :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ∀ τ, τ ∈ gn21RejectMiddleLoReplacement lo hi ε → density τ ≠ 0)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσI_measurable : MeasurableSet σI)
    (hσI_positive : σI ⊆ acceptAllPolicy) :
    ∀ ε : ℝ, 0 < ε → ε < δ →
      GN21MeasuredPairNondegenerate μI
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalI arrivalJ switchIJ switchJI
        σI (gn21RejectMiddleLoReplacement lo hi ε) := by
  intro ε hε_pos hε_lt
  exact
    gn21MeasuredPairNondegenerate_of_rejectMiddleLoReplacement_withDensity_right
      μI density arrivalI arrivalJ switchIJ switchJI σI lo hi ε
      hmassI_pos hdensity_meas (hfinite ε hε_pos hε_lt)
      (hpos ε hε_pos hε_lt) harrivalI_pos harrivalJ_pos hswitchIJ_pos
      hswitchJI_pos hσI_measurable hσI_positive

/--
Pointwise finite positive-density assumptions produce the nondegeneracy
function required by the upper-cutoff reject-middle strict-local bridge.
-/
theorem gn21MeasuredPairNondegenerate_rejectMiddleHiReplacement_withDensity_right_forall
    (μI : Measure TripLength)
    (density : TripLength → NNReal)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI : TripPolicy)
    (lo hi δ : ℝ)
    (hmassI_pos : 0 < singleStateTripMass μI σI)
    (hdensity_meas : Measurable density)
    (hfinite :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
          (gn21RejectMiddleHiReplacement lo hi ε) ≠ ∞)
    (hpos :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ∀ τ, τ ∈ gn21RejectMiddleHiReplacement lo hi ε → density τ ≠ 0)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσI_measurable : MeasurableSet σI)
    (hσI_positive : σI ⊆ acceptAllPolicy) :
    ∀ ε : ℝ, 0 < ε → ε < δ →
      GN21MeasuredPairNondegenerate μI
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalI arrivalJ switchIJ switchJI
        σI (gn21RejectMiddleHiReplacement lo hi ε) := by
  intro ε hε_pos hε_lt
  exact
    gn21MeasuredPairNondegenerate_of_rejectMiddleHiReplacement_withDensity_right
      μI density arrivalI arrivalJ switchIJ switchJI σI lo hi ε
      hmassI_pos hdensity_meas (hfinite ε hε_pos hε_lt)
      (hpos ε hε_pos hε_lt) harrivalI_pos harrivalJ_pos hswitchIJ_pos
      hswitchJI_pos hσI_measurable hσI_positive

/--
Measured pair nondegeneracy when the right/state-`J` current policy has the
middle-rejection shape under a positive NNReal density.
-/
theorem gn21MeasuredPairNondegenerate_of_rejectsMiddleTrips_withDensity_right
    (μI : Measure TripLength)
    (density : TripLength → NNReal)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI σJ : TripPolicy)
    (lo hi : ℝ)
    (hshape : rejectsMiddleTrips lo hi σJ)
    (hsub : σJ ⊆ acceptAllPolicy)
    (hmassI_pos : 0 < singleStateTripMass μI σI)
    (hdensity_meas : Measurable density)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞)) σJ ≠ ∞)
    (hpos : ∀ τ, τ ∈ σJ → density τ ≠ 0)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσI_measurable : MeasurableSet σI)
    (hσI_positive : σI ⊆ acceptAllPolicy) :
    GN21MeasuredPairNondegenerate μI
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
      arrivalI arrivalJ switchIJ switchJI σI σJ := by
  have hσJ_measurable : MeasurableSet σJ := by
    rw [eq_rejectMiddleTripsPolicy_of_rejectsMiddleTrips_of_subset_acceptAll
      hshape hsub]
    exact measurableSet_rejectMiddleTripsPolicy lo hi
  exact
    gn21MeasuredPairNondegenerate_of_positive_measure
      μI (volume.withDensity fun τ => (density τ : ℝ≥0∞))
      arrivalI arrivalJ switchIJ switchJI σI σJ hmassI_pos
      (singleStateTripMass_rejectsMiddleTrips_withDensity_pos_of_pos_on
        density hdensity_meas lo hi σJ hshape hsub hfinite hpos)
      harrivalI_pos harrivalJ_pos hswitchIJ_pos hswitchJI_pos
      hσI_measurable hσJ_measurable hσI_positive hsub

/--
Measured pair nondegeneracy when the right/state-`J` policy is a concrete
tail left-replacement under a positive NNReal density.
-/
theorem gn21MeasuredPairNondegenerate_of_tailLeftReplacement_withDensity_right
    (μI : Measure TripLength)
    (density : TripLength → NNReal)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI : TripPolicy)
    (u ε : ℝ)
    (hmassI_pos : 0 < singleStateTripMass μI σI)
    (hdensity_meas : Measurable density)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        (gn21TailLeftReplacement u ε) ≠ ∞)
    (hpos :
      ∀ τ, τ ∈ gn21TailLeftReplacement u ε → density τ ≠ 0)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσI_measurable : MeasurableSet σI)
    (hσI_positive : σI ⊆ acceptAllPolicy)
    (hε_le_u : ε ≤ u) :
    GN21MeasuredPairNondegenerate μI
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
      arrivalI arrivalJ switchIJ switchJI
      σI (gn21TailLeftReplacement u ε) := by
  exact
    gn21MeasuredPairNondegenerate_of_positive_measure
      μI (volume.withDensity fun τ => (density τ : ℝ≥0∞))
      arrivalI arrivalJ switchIJ switchJI σI (gn21TailLeftReplacement u ε)
      hmassI_pos
      (singleStateTripMass_tailLeftReplacement_withDensity_pos_of_pos_on
        density hdensity_meas u ε hfinite hpos)
      harrivalI_pos harrivalJ_pos hswitchIJ_pos hswitchJI_pos
      hσI_measurable (measurableSet_gn21TailLeftReplacement u ε)
      hσI_positive
      (gn21TailLeftReplacement_subset_acceptAllPolicy u ε hε_le_u)

/--
Pointwise finite positive-density assumptions produce the nondegeneracy
function required by the tail strict-local bridge.
-/
theorem gn21MeasuredPairNondegenerate_tailLeftReplacement_withDensity_right_forall
    (μI : Measure TripLength)
    (density : TripLength → NNReal)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI : TripPolicy)
    (u δ : ℝ)
    (hmassI_pos : 0 < singleStateTripMass μI σI)
    (hdensity_meas : Measurable density)
    (hfinite :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
          (gn21TailLeftReplacement u ε) ≠ ∞)
    (hpos :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ∀ τ, τ ∈ gn21TailLeftReplacement u ε → density τ ≠ 0)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσI_measurable : MeasurableSet σI)
    (hσI_positive : σI ⊆ acceptAllPolicy)
    (hδ_le_u : δ ≤ u) :
    ∀ ε : ℝ, 0 < ε → ε < δ →
      GN21MeasuredPairNondegenerate μI
        (volume.withDensity fun τ => (density τ : ℝ≥0∞))
        arrivalI arrivalJ switchIJ switchJI
        σI (gn21TailLeftReplacement u ε) := by
  intro ε hε_pos hε_lt
  exact
    gn21MeasuredPairNondegenerate_of_tailLeftReplacement_withDensity_right
      μI density arrivalI arrivalJ switchIJ switchJI σI u ε
      hmassI_pos hdensity_meas (hfinite ε hε_pos hε_lt)
      (hpos ε hε_pos hε_lt) harrivalI_pos harrivalJ_pos hswitchIJ_pos
      hswitchJI_pos hσI_measurable hσI_positive (by linarith)

/--
Measured pair nondegeneracy when the right/state-`J` current policy has the
short-trip-rejection tail shape under a positive NNReal density.
-/
theorem gn21MeasuredPairNondegenerate_of_rejectsShortTrips_withDensity_right
    (μI : Measure TripLength)
    (density : TripLength → NNReal)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (σI σJ : TripPolicy)
    (t : ℝ)
    (hshape : rejectsShortTrips t σJ)
    (hsub : σJ ⊆ acceptAllPolicy)
    (hmassI_pos : 0 < singleStateTripMass μI σI)
    (hdensity_meas : Measurable density)
    (hfinite :
      (volume.withDensity fun τ => (density τ : ℝ≥0∞)) σJ ≠ ∞)
    (hpos : ∀ τ, τ ∈ σJ → density τ ≠ 0)
    (harrivalI_pos : 0 < arrivalI)
    (harrivalJ_pos : 0 < arrivalJ)
    (hswitchIJ_pos : 0 < switchIJ)
    (hswitchJI_pos : 0 < switchJI)
    (hσI_measurable : MeasurableSet σI)
    (hσI_positive : σI ⊆ acceptAllPolicy) :
    GN21MeasuredPairNondegenerate μI
      (volume.withDensity fun τ => (density τ : ℝ≥0∞))
      arrivalI arrivalJ switchIJ switchJI σI σJ := by
  have hσJ_measurable : MeasurableSet σJ := by
    rw [eq_rejectShortTripsPolicy_of_rejectsShortTrips_of_subset_acceptAll
      hshape hsub]
    exact measurableSet_rejectShortTripsPolicy t
  exact
    gn21MeasuredPairNondegenerate_of_positive_measure
      μI (volume.withDensity fun τ => (density τ : ℝ≥0∞))
      arrivalI arrivalJ switchIJ switchJI σI σJ hmassI_pos
      (singleStateTripMass_rejectsShortTrips_withDensity_pos_of_pos_on
        density hdensity_meas t σJ hshape hsub hfinite hpos)
      harrivalI_pos harrivalJ_pos hswitchIJ_pos hswitchJI_pos
      hσI_measurable hσJ_measurable hσI_positive hsub

/--
Named wrapper for Lemma 1/3's measured reward-to-aggregate reduction.
-/
theorem paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy)
    (hmassI : singleStateTripMass μI σI ≠ 0)
    (hmassJ : singleStateTripMass μJ σJ ≠ 0)
    (harrivalMassI : arrivalI * singleStateTripMass μI σI ≠ 0)
    (harrivalMassJ : arrivalJ * singleStateTripMass μJ σJ ≠ 0)
    (hscaledTimeI : gn21ScaledStateTime μI arrivalI σI ≠ 0)
    (hscaledTimeJ : gn21ScaledStateTime μJ arrivalJ σJ ≠ 0)
    (hden :
      gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI *
          gn21ScaledStateTime μJ arrivalJ σJ +
        gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ *
          gn21ScaledStateTime μI arrivalI σI ≠ 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ σI σJ =
      gn21MeasuredAggregateRewardPrimitives μI μJ arrivalI arrivalJ
        switchIJ switchJI wI wJ σI σJ := by
  unfold gn21MeasuredAggregateRewardPrimitives
  exact paper_lemma1_measured_dynamic_reward_eq_aggregate_scaled_primitives
    μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ σI σJ
    hmassI hmassJ harrivalMassI harrivalMassJ hscaledTimeI hscaledTimeJ hden

/--
Measured reward-to-aggregate reduction from the compact pair nondegeneracy
package.
-/
theorem paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy)
    (H :
      GN21MeasuredPairNondegenerate μI μJ arrivalI arrivalJ switchIJ switchJI
        σI σJ) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ σI σJ =
      gn21MeasuredAggregateRewardPrimitives μI μJ arrivalI arrivalJ
        switchIJ switchJI wI wJ σI σJ := by
  exact paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives
    μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ σI σJ
    H.massI_ne H.massJ_ne H.arrivalMassI_ne H.arrivalMassJ_ne
    H.scaledTimeI_ne H.scaledTimeJ_ne H.denominator_ne

/--
Weak comparison bridge for one-state replacements: a scalar aggregate
comparison in `Q,T,W` primitives implies the same measured dynamic reward
comparison.
-/
theorem paper_lemma1_measured_dynamic_reward_le_of_aggregate_primitives_le
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σI' σJ : TripPolicy)
    (hmassI : singleStateTripMass μI σI ≠ 0)
    (hmassI' : singleStateTripMass μI σI' ≠ 0)
    (hmassJ : singleStateTripMass μJ σJ ≠ 0)
    (harrivalMassI : arrivalI * singleStateTripMass μI σI ≠ 0)
    (harrivalMassI' : arrivalI * singleStateTripMass μI σI' ≠ 0)
    (harrivalMassJ : arrivalJ * singleStateTripMass μJ σJ ≠ 0)
    (hscaledTimeI : gn21ScaledStateTime μI arrivalI σI ≠ 0)
    (hscaledTimeI' : gn21ScaledStateTime μI arrivalI σI' ≠ 0)
    (hscaledTimeJ : gn21ScaledStateTime μJ arrivalJ σJ ≠ 0)
    (hden :
      gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI *
          gn21ScaledStateTime μJ arrivalJ σJ +
        gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ *
          gn21ScaledStateTime μI arrivalI σI ≠ 0)
    (hden' :
      gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI' *
          gn21ScaledStateTime μJ arrivalJ σJ +
        gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ *
          gn21ScaledStateTime μI arrivalI σI' ≠ 0)
    (hagg :
      gn21MeasuredAggregateRewardPrimitives μI μJ arrivalI arrivalJ
          switchIJ switchJI wI wJ σI σJ ≤
        gn21MeasuredAggregateRewardPrimitives μI μJ arrivalI arrivalJ
          switchIJ switchJI wI wJ σI' σJ) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ σI σJ ≤
      gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ σI' σJ := by
  rw [paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives
      μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ σI σJ
      hmassI hmassJ harrivalMassI harrivalMassJ hscaledTimeI hscaledTimeJ
      hden,
    paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives
      μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ σI' σJ
      hmassI' hmassJ harrivalMassI' harrivalMassJ hscaledTimeI'
      hscaledTimeJ hden']
  exact hagg

/--
Weak comparison bridge for arbitrary measured policy-pair replacements from
the compact nondegeneracy package.
-/
theorem paper_lemma1_measured_dynamic_reward_le_of_aggregate_pair_le_of_nondegenerate
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ σI' σJ' : TripPolicy)
    (H :
      GN21MeasuredPairNondegenerate μI μJ arrivalI arrivalJ switchIJ switchJI
        σI σJ)
    (H' :
      GN21MeasuredPairNondegenerate μI μJ arrivalI arrivalJ switchIJ switchJI
        σI' σJ')
    (hagg :
      gn21MeasuredAggregateRewardPrimitives μI μJ arrivalI arrivalJ
          switchIJ switchJI wI wJ σI σJ ≤
        gn21MeasuredAggregateRewardPrimitives μI μJ arrivalI arrivalJ
          switchIJ switchJI wI wJ σI' σJ') :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ σI σJ ≤
      gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ σI' σJ' := by
  rw [paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
      μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ σI σJ H,
    paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
      μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ σI' σJ' H']
  exact hagg

/--
Strict comparison bridge for one-state replacements: a strict aggregate
comparison in `Q,T,W` primitives implies the same measured dynamic reward
comparison.
-/
theorem paper_lemma1_measured_dynamic_reward_lt_of_aggregate_primitives_lt
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σI' σJ : TripPolicy)
    (hmassI : singleStateTripMass μI σI ≠ 0)
    (hmassI' : singleStateTripMass μI σI' ≠ 0)
    (hmassJ : singleStateTripMass μJ σJ ≠ 0)
    (harrivalMassI : arrivalI * singleStateTripMass μI σI ≠ 0)
    (harrivalMassI' : arrivalI * singleStateTripMass μI σI' ≠ 0)
    (harrivalMassJ : arrivalJ * singleStateTripMass μJ σJ ≠ 0)
    (hscaledTimeI : gn21ScaledStateTime μI arrivalI σI ≠ 0)
    (hscaledTimeI' : gn21ScaledStateTime μI arrivalI σI' ≠ 0)
    (hscaledTimeJ : gn21ScaledStateTime μJ arrivalJ σJ ≠ 0)
    (hden :
      gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI *
          gn21ScaledStateTime μJ arrivalJ σJ +
        gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ *
          gn21ScaledStateTime μI arrivalI σI ≠ 0)
    (hden' :
      gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI' *
          gn21ScaledStateTime μJ arrivalJ σJ +
        gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ *
          gn21ScaledStateTime μI arrivalI σI' ≠ 0)
    (hagg :
      gn21MeasuredAggregateRewardPrimitives μI μJ arrivalI arrivalJ
          switchIJ switchJI wI wJ σI σJ <
        gn21MeasuredAggregateRewardPrimitives μI μJ arrivalI arrivalJ
          switchIJ switchJI wI wJ σI' σJ) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ σI σJ <
      gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ σI' σJ := by
  rw [paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives
      μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ σI σJ
      hmassI hmassJ harrivalMassI harrivalMassJ hscaledTimeI hscaledTimeJ
      hden,
    paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives
      μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ σI' σJ
      hmassI' hmassJ harrivalMassI' harrivalMassJ hscaledTimeI'
      hscaledTimeJ hden']
  exact hagg

/--
Strict comparison bridge for arbitrary measured policy-pair replacements from
the compact nondegeneracy package.
-/
theorem paper_lemma1_measured_dynamic_reward_lt_of_aggregate_pair_lt_of_nondegenerate
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ σI' σJ' : TripPolicy)
    (H :
      GN21MeasuredPairNondegenerate μI μJ arrivalI arrivalJ switchIJ switchJI
        σI σJ)
    (H' :
      GN21MeasuredPairNondegenerate μI μJ arrivalI arrivalJ switchIJ switchJI
        σI' σJ')
    (hagg :
      gn21MeasuredAggregateRewardPrimitives μI μJ arrivalI arrivalJ
          switchIJ switchJI wI wJ σI σJ <
        gn21MeasuredAggregateRewardPrimitives μI μJ arrivalI arrivalJ
          switchIJ switchJI wI wJ σI' σJ') :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ σI σJ <
      gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ σI' σJ' := by
  rw [paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
      μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ σI σJ H,
    paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
      μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ σI' σJ' H']
  exact hagg

/--
Dynamic-reward wrapper for the measured two-state CTMC reward formula.  State
`0` is the non-surge state and state `1` is the surge state.
-/
def gn21MeasuredDynamicRewardFunctional
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) : DynamicReward :=
  fun σ =>
    gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
      switch12 switch21 (w 0) (w 1) (σ 0) (σ 1)

/-- The measured dynamic reward wrapper unfolds to the source two-state formula. -/
theorem gn21MeasuredDynamicRewardFunctional_apply
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (σ : Fin 2 → TripPolicy) :
    gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w σ =
      gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (w 0) (w 1) (σ 0) (σ 1) := by
  rfl

/-- Measured dynamic reward specialized to the CTMC structured price family. -/
def gn21MeasuredCTMCStructuredDynamicReward
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ) : DynamicReward :=
  gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
    (ctmcStructuredDynamicSurgePrice m z switch12 switch21)

/-- Accept-all scaled state time, used in the measured Theorem 3 endpoint. -/
def gn21AcceptAllScaledStateTime
    (μ : Measure TripLength) (arrivalRate : ℝ) : ℝ :=
  gn21ScaledStateTime μ arrivalRate acceptAllPolicy

/-- Accept-all exit weight, used in the measured Theorem 3 endpoint. -/
def gn21AcceptAllExitWeightIntegral
    (μ : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ) : ℝ :=
  gn21ExitWeightIntegral μ arrivalRate switchIJ switchJI acceptAllPolicy

/--
Statewise unfolding of the measured dynamic reward when the non-surge policy is
replaced and the surge policy is held fixed.
-/
theorem dynamicStateReward_gn21MeasuredDynamicRewardFunctional_zero
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (σ : Fin 2 → TripPolicy) (τ : TripPolicy) :
    dynamicStateReward
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        σ 0 τ =
      gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (w 0) (w 1) τ (σ 1) := by
  simp [dynamicStateReward, gn21MeasuredDynamicRewardFunctional]

/--
Statewise unfolding of the measured dynamic reward when the surge policy is
replaced and the non-surge policy is held fixed.
-/
theorem dynamicStateReward_gn21MeasuredDynamicRewardFunctional_one
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (σ : Fin 2 → TripPolicy) (τ : TripPolicy) :
    dynamicStateReward
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        σ 1 τ =
      gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (w 0) (w 1) (σ 0) τ := by
  simp [dynamicStateReward, gn21MeasuredDynamicRewardFunctional]

/--
Measured-reward constructor for the global Theorem 4 reward interface.  The
remaining analytic endpoint can now be stated directly as comparisons between
the measured two-state reward at `σ` and at the one-state accept-all
replacements.
-/
def theorem4GlobalStatewiseAcceptAllRewardCertificate_of_measured_reward_improvements
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (hfeasible :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ →
        ∀ i : Fin 2, ρ i ⊆ acceptAllPolicy)
    (hnonsurge_ge :
      ∀ ρ : Fin 2 → TripPolicy,
        gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) ≤
        gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) acceptAllPolicy (ρ 1))
    (hsurge_ge :
      ∀ ρ : Fin 2 → TripPolicy,
        gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) ≤
        gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (ρ 0) acceptAllPolicy)
    (hnonsurge_gt_unless :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ →
        ¬ acceptsAllTrips (ρ 0) →
        gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) <
        gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) acceptAllPolicy (ρ 1))
    (hsurge_gt_unless :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ →
        ¬ acceptsAllTrips (ρ 1) →
        gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) <
        gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (ρ 0) acceptAllPolicy) :
    Theorem4GlobalStatewiseAcceptAllRewardCertificate
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w) where
  feasible_optimal := hfeasible
  nonsurge_accept_all_reward_ge := by
    intro ρ
    simpa [dynamicStateReward_gn21MeasuredDynamicRewardFunctional_zero] using
      hnonsurge_ge ρ
  surge_accept_all_reward_ge := by
    intro ρ
    simpa [dynamicStateReward_gn21MeasuredDynamicRewardFunctional_one] using
      hsurge_ge ρ
  nonsurge_accept_all_reward_gt_unless := by
    intro ρ hρ hnot
    simpa [dynamicStateReward_gn21MeasuredDynamicRewardFunctional_zero] using
      hnonsurge_gt_unless ρ hρ hnot
  surge_accept_all_reward_gt_unless := by
    intro ρ hρ hnot
    simpa [dynamicStateReward_gn21MeasuredDynamicRewardFunctional_one] using
      hsurge_gt_unless ρ hρ hnot

/--
Theorem 4 aggregate-reward certificate for the measured two-state functional.
This is the closest interface to Lemma 6 endpoint movement: it asks for
accept-all improvements in the aggregate `Q,T,W` quotient, plus the
nondegeneracy needed to identify that quotient with the measured reward.
-/
structure Theorem4MeasuredAggregateAcceptAllRewardCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) where
  feasible_optimal :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ →
      ∀ i : Fin 2, ρ i ⊆ acceptAllPolicy
  current_nondegenerate :
    ∀ ρ : Fin 2 → TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1)
  nonsurge_accept_all_nondegenerate :
    ∀ ρ : Fin 2 → TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 acceptAllPolicy (ρ 1)
  surge_accept_all_nondegenerate :
    ∀ ρ : Fin 2 → TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) acceptAllPolicy
  nonsurge_aggregate_ge :
    ∀ ρ : Fin 2 → TripPolicy,
      gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) ≤
        gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) acceptAllPolicy (ρ 1)
  surge_aggregate_ge :
    ∀ ρ : Fin 2 → TripPolicy,
      gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) ≤
        gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) acceptAllPolicy
  nonsurge_aggregate_gt_unless :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ →
      ¬ acceptsAllTrips (ρ 0) →
        gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
            (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) <
          gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
            (arrival 1) switch12 switch21 (w 0) (w 1) acceptAllPolicy (ρ 1)
  surge_aggregate_gt_unless :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ →
      ¬ acceptsAllTrips (ρ 1) →
        gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
            (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) <
          gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
            (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) acceptAllPolicy

/--
Aggregate `Q,T,W` accept-all improvements instantiate the measured global
statewise reward interface used by Theorem 4.
-/
def theorem4GlobalStatewiseAcceptAllRewardCertificate_of_measured_aggregate_improvements
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (C : Theorem4MeasuredAggregateAcceptAllRewardCertificate
      μ arrival switch12 switch21 w) :
    Theorem4GlobalStatewiseAcceptAllRewardCertificate
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w) :=
  theorem4GlobalStatewiseAcceptAllRewardCertificate_of_measured_reward_improvements
    μ arrival switch12 switch21 w C.feasible_optimal
    (by
      intro ρ
      exact
        paper_lemma1_measured_dynamic_reward_le_of_aggregate_pair_le_of_nondegenerate
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (ρ 0) (ρ 1) acceptAllPolicy (ρ 1)
          (C.current_nondegenerate ρ)
          (C.nonsurge_accept_all_nondegenerate ρ)
          (C.nonsurge_aggregate_ge ρ))
    (by
      intro ρ
      exact
        paper_lemma1_measured_dynamic_reward_le_of_aggregate_pair_le_of_nondegenerate
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (ρ 0) (ρ 1) (ρ 0) acceptAllPolicy
          (C.current_nondegenerate ρ)
          (C.surge_accept_all_nondegenerate ρ)
          (C.surge_aggregate_ge ρ))
    (by
      intro ρ hρ hnot
      exact
        paper_lemma1_measured_dynamic_reward_lt_of_aggregate_pair_lt_of_nondegenerate
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (ρ 0) (ρ 1) acceptAllPolicy (ρ 1)
          (C.current_nondegenerate ρ)
          (C.nonsurge_accept_all_nondegenerate ρ)
          (C.nonsurge_aggregate_gt_unless ρ hρ hnot))
    (by
      intro ρ hρ hnot
      exact
        paper_lemma1_measured_dynamic_reward_lt_of_aggregate_pair_lt_of_nondegenerate
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (w 0) (w 1) (ρ 0) (ρ 1) (ρ 0) acceptAllPolicy
          (C.current_nondegenerate ρ)
          (C.surge_accept_all_nondegenerate ρ)
          (C.surge_aggregate_gt_unless ρ hρ hnot))

/--
Measured aggregate strict-local-improvement certificate.  This matches the
endpoint-derivative proof shape: every optimal policy that fails accept-all in
a state has a nearby replacement with strictly larger aggregate `Q,T,W`
reward.
-/
structure Theorem4MeasuredAggregateStrictLocalImprovementCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) where
  exists_optimal :
    ∃ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ
  feasible_optimal :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ →
      ∀ i : Fin 2, ρ i ⊆ acceptAllPolicy
  nonsurge_strict_aggregate_improvement_unless :
    ∀ ρ : Fin 2 → TripPolicy,
      (hρ :
        dynamicOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ) →
      ¬ acceptsAllTrips (ρ 0) →
        ∃ τ : TripPolicy,
          GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
            switch12 switch21 (ρ 0) (ρ 1) ∧
          GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
            switch12 switch21 τ (ρ 1) ∧
          gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
              (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) <
            gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
              (arrival 1) switch12 switch21 (w 0) (w 1) τ (ρ 1)
  surge_strict_aggregate_improvement_unless :
    ∀ ρ : Fin 2 → TripPolicy,
      (hρ :
        dynamicOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ) →
      ¬ acceptsAllTrips (ρ 1) →
        ∃ τ : TripPolicy,
          GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
            switch12 switch21 (ρ 0) (ρ 1) ∧
          GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
            switch12 switch21 (ρ 0) τ ∧
          gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
              (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) <
            gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
              (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) τ

/--
Measured aggregate strict-local improvements instantiate the generic strict
local-improvement interface.
-/
def theorem4StrictLocalImprovementCertificate_of_measured_aggregate_strict_improvements
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (C : Theorem4MeasuredAggregateStrictLocalImprovementCertificate
      μ arrival switch12 switch21 w) :
    Theorem4StrictLocalImprovementCertificate
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w) where
  exists_optimal := C.exists_optimal
  feasible_optimal := C.feasible_optimal
  nonsurge_strict_improvement_unless := by
    intro ρ hρ hnot
    rcases C.nonsurge_strict_aggregate_improvement_unless ρ hρ hnot with
      ⟨τ, Hcur, Hrep, hagg⟩
    refine ⟨τ, ?_⟩
    have hlt :=
      paper_lemma1_measured_dynamic_reward_lt_of_aggregate_pair_lt_of_nondegenerate
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (ρ 0) (ρ 1) τ (ρ 1) Hcur Hrep hagg
    simpa [dynamicStateReward_gn21MeasuredDynamicRewardFunctional_zero] using hlt
  surge_strict_improvement_unless := by
    intro ρ hρ hnot
    rcases C.surge_strict_aggregate_improvement_unless ρ hρ hnot with
      ⟨τ, Hcur, Hrep, hagg⟩
    refine ⟨τ, ?_⟩
    have hlt :=
      paper_lemma1_measured_dynamic_reward_lt_of_aggregate_pair_lt_of_nondegenerate
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (ρ 0) (ρ 1) (ρ 0) τ Hcur Hrep hagg
    simpa [dynamicStateReward_gn21MeasuredDynamicRewardFunctional_one] using hlt

/--
Measured aggregate strict-local improvements imply accept-all unique optimality
for the measured two-state reward functional.
-/
theorem paper_theorem4_accept_all_unique_optimal_of_measured_aggregate_strict_local_improvements
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (C : Theorem4MeasuredAggregateStrictLocalImprovementCertificate
      μ arrival switch12 switch21 w) :
    dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ →
          ρ = acceptAllDynamicPolicy :=
  paper_theorem4_accept_all_unique_optimal_of_strict_local_improvements
    (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
    (theorem4StrictLocalImprovementCertificate_of_measured_aggregate_strict_improvements
      μ arrival switch12 switch21 w C)

/-- Replace one component of a two-state dynamic trip policy. -/
def replaceDynamicPolicyState
    (ρ : Fin 2 → TripPolicy) (i : Fin 2) (τ : TripPolicy) : Fin 2 → TripPolicy :=
  fun j => if j = i then τ else ρ j

@[simp] theorem replaceDynamicPolicyState_same
    (ρ : Fin 2 → TripPolicy) (i : Fin 2) (τ : TripPolicy) :
    replaceDynamicPolicyState ρ i τ i = τ := by
  simp [replaceDynamicPolicyState]

@[simp] theorem replaceDynamicPolicyState_ne
    (ρ : Fin 2 → TripPolicy) (i j : Fin 2) (τ : TripPolicy)
    (hji : j ≠ i) :
    replaceDynamicPolicyState ρ i τ j = ρ j := by
  simp [replaceDynamicPolicyState, hji]

/--
Aggregate reward after replacing one component of a dynamic policy.  This is
the measured aggregate analogue of `dynamicStateReward`, useful for feeding
one-state endpoint moves into the two-state reward certificate.
-/
def gn21MeasuredAggregateDynamicStateReward
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (ρ : Fin 2 → TripPolicy) (i : Fin 2) (τ : TripPolicy) : ℝ :=
  gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
    (arrival 1) switch12 switch21 (w 0) (w 1)
    ((replaceDynamicPolicyState ρ i τ) 0)
    ((replaceDynamicPolicyState ρ i τ) 1)

/-- State-0 replacement unfolds to replacing the non-surge policy. -/
theorem gn21MeasuredAggregateDynamicStateReward_zero
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (ρ : Fin 2 → TripPolicy) (τ : TripPolicy) :
    gn21MeasuredAggregateDynamicStateReward
        μ arrival switch12 switch21 w ρ 0 τ =
      gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
        (arrival 1) switch12 switch21 (w 0) (w 1) τ (ρ 1) := by
  simp [gn21MeasuredAggregateDynamicStateReward, replaceDynamicPolicyState]

/-- State-1 replacement unfolds to replacing the surge policy. -/
theorem gn21MeasuredAggregateDynamicStateReward_one
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (ρ : Fin 2 → TripPolicy) (τ : TripPolicy) :
    gn21MeasuredAggregateDynamicStateReward
        μ arrival switch12 switch21 w ρ 1 τ =
      gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
        (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) τ := by
  simp [gn21MeasuredAggregateDynamicStateReward, replaceDynamicPolicyState]

/--
Surge-state bridge from the Lemma 9 interval-density endpoint movement to the
measured aggregate strict-local state-replacement interface.  The policy
equalities identify the current surge policy and the candidate endpoint
replacements with the interval primitive paths.
-/
theorem paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_interval_density
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy)
    (replacement : ℝ → TripPolicy)
    (lowerEndpoint u T1 Q1 T2 Q2 R1 ratio : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrival 1)
    (hdensity_pos : 0 < density u)
    (hQ1_pos : 0 < Q1)
    (hden :
      gn21EndpointQiPath (arrival 1) switch21 lowerEndpoint density
          (gn21SwitchProb switch21 switch12) u * T1 +
        Q1 *
          gn21EndpointTiPath (arrival 1) lowerEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) volume
        lowerEndpoint u)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (𝓝 u))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) u)
    (hw_int :
      IntervalIntegrable
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) volume lowerEndpoint u)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) (𝓝 u))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume lowerEndpoint u)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hQ2 :
      gn21EndpointQiPath (arrival 1) switch21 lowerEndpoint density
        (gn21SwitchProb switch21 switch12) u = Q2)
    (hT2 :
      gn21EndpointTiPath (arrival 1) lowerEndpoint density u = T2)
    (hW2 :
      gn21EndpointWiPath (arrival 1) lowerEndpoint density
        (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) u =
          m 1 * (T2 - 1) + z 1 * (Q2 - switch21))
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z 1 = ratio * (m 1 - R1))
    (hmR_pos : 0 < m 1 - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hu : 0 < u)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (Hcur :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (Hrep :
      ∀ ε : ℝ, 0 < ε →
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (ρ 0) (replacement ε))
    (hQ_other :
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) = Q1)
    (hT_other :
      gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) = T1)
    (hW_other :
      gn21ScaledStateEarning (μ 0) (arrival 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
          R1 * T1)
    (hQ_current :
      gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) =
        gn21EndpointQiPath (arrival 1) switch21 lowerEndpoint density
          (gn21SwitchProb switch21 switch12) u)
    (hT_current :
      gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) =
        gn21EndpointTiPath (arrival 1) lowerEndpoint density u)
    (hW_current :
      gn21ScaledStateEarning (μ 1) (arrival 1)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
        gn21EndpointWiPath (arrival 1) lowerEndpoint density
          (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) u)
    (hQ_replacement :
      ∀ ε : ℝ, 0 < ε →
        gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            (replacement ε) =
          gn21EndpointQiPath (arrival 1) switch21 lowerEndpoint density
            (gn21SwitchProb switch21 switch12) (u + ε))
    (hT_replacement :
      ∀ ε : ℝ, 0 < ε →
        gn21ScaledStateTime (μ 1) (arrival 1) (replacement ε) =
          gn21EndpointTiPath (arrival 1) lowerEndpoint density (u + ε))
    (hW_replacement :
      ∀ ε : ℝ, 0 < ε →
        gn21ScaledStateEarning (μ 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (replacement ε) =
          gn21EndpointWiPath (arrival 1) lowerEndpoint density
            (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12)
            (u + ε)) :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 1 τ) 0)
          ((replaceDynamicPolicyState ρ 1 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 (ρ 1) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 τ := by
  rcases
      paper_lemma9_exists_pos_right_improvement_of_interval_density_current_bounds
        (arrival 1) lowerEndpoint u T1 Q1 T2 Q2 switch21 switch12
        (m 1) R1 (z 1) ratio density harrival_pos hdensity_pos hQ1_pos
        hden hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas
        ht_cont hQ2 hT2 hW2 hbounds hz hmR_pos hR1_nonneg hT1_nonneg
        hswitch21_pos hsum hu hswitch_lt_Q2 hgap_nonneg with
    ⟨ε, hε_pos, hlt⟩
  refine ⟨replacement ε, Hcur, ?_, ?_⟩
  · simpa [replaceDynamicPolicyState] using Hrep ε hε_pos
  · simpa [gn21MeasuredAggregateDynamicStateReward_one,
      gn21MeasuredAggregateRewardPrimitives, hQ_other, hT_other, hW_other,
      hQ_current, hT_current, hW_current, hQ_replacement ε hε_pos,
      hT_replacement ε hε_pos, hW_replacement ε hε_pos,
      gn21AggregateDynamicReward_swap]
      using hlt

/--
Non-surge-state counterpart of the Lemma 9 bridge: Lemma 10's
interval-density endpoint movement feeds the measured aggregate strict-local
state-replacement interface for state `0`.
-/
theorem paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_interval_density
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy)
    (replacement : ℝ → TripPolicy)
    (lowerEndpoint u T2 Q2 T1 Q1 R2 ratio : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrival 0)
    (hdensity_pos : 0 < density u)
    (hQ2_pos : 0 < Q2)
    (hden :
      gn21EndpointQiPath (arrival 0) switch12 lowerEndpoint density
          (gn21SwitchProb switch12 switch21) u * T2 +
        Q2 *
          gn21EndpointTiPath (arrival 0) lowerEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) volume
        lowerEndpoint u)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) (𝓝 u))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) u)
    (hw_int :
      IntervalIntegrable
        (fun τ => ctmcStructuredSurgePrice R2 (z 0) switch12 switch21 τ *
          density τ) volume lowerEndpoint u)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice R2 (z 0) switch12 switch21 τ *
          density τ) (𝓝 u))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice R2 (z 0) switch12 switch21 τ *
          density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume lowerEndpoint u)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hQ1 :
      gn21EndpointQiPath (arrival 0) switch12 lowerEndpoint density
        (gn21SwitchProb switch12 switch21) u = Q1)
    (hT1 :
      gn21EndpointTiPath (arrival 0) lowerEndpoint density u = T1)
    (hW1 :
      gn21EndpointWiPath (arrival 0) lowerEndpoint density
        (ctmcStructuredSurgePrice R2 (z 0) switch12 switch21) u =
          R2 * (T1 - 1) + z 0 * (Q1 - switch12))
    (hbounds : lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12)
    (hz : z 0 = ratio * R2)
    (hR2_pos : 0 < R2)
    (hswitch12_pos : 0 < switch12)
    (hsum : 0 < switch12 + switch21)
    (hu : 0 < u)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hA_pos : 0 < T2 * switch12 + Q2)
    (Hcur :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (Hrep :
      ∀ ε : ℝ, 0 < ε →
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (replacement ε) (ρ 1))
    (hQ_other :
      gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) = Q2)
    (hT_other :
      gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) = T2)
    (hW_other :
      gn21ScaledStateEarning (μ 1) (arrival 1)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
          R2 * T2)
    (hQ_current :
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) =
        gn21EndpointQiPath (arrival 0) switch12 lowerEndpoint density
          (gn21SwitchProb switch12 switch21) u)
    (hT_current :
      gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) =
        gn21EndpointTiPath (arrival 0) lowerEndpoint density u)
    (hW_current :
      gn21ScaledStateEarning (μ 0) (arrival 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
        gn21EndpointWiPath (arrival 0) lowerEndpoint density
          (ctmcStructuredSurgePrice R2 (z 0) switch12 switch21) u)
    (hQ_replacement :
      ∀ ε : ℝ, 0 < ε →
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            (replacement ε) =
          gn21EndpointQiPath (arrival 0) switch12 lowerEndpoint density
            (gn21SwitchProb switch12 switch21) (u + ε))
    (hT_replacement :
      ∀ ε : ℝ, 0 < ε →
        gn21ScaledStateTime (μ 0) (arrival 0) (replacement ε) =
          gn21EndpointTiPath (arrival 0) lowerEndpoint density (u + ε))
    (hW_replacement :
      ∀ ε : ℝ, 0 < ε →
        gn21ScaledStateEarning (μ 0) (arrival 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (replacement ε) =
          gn21EndpointWiPath (arrival 0) lowerEndpoint density
            (ctmcStructuredSurgePrice R2 (z 0) switch12 switch21) (u + ε)) :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 0 τ) 0)
          ((replaceDynamicPolicyState ρ 0 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 0 (ρ 0) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 0 τ := by
  rcases
      paper_lemma10_exists_pos_right_improvement_of_interval_density_current_bounds
        (arrival 0) lowerEndpoint u T2 Q2 T1 Q1 switch12 switch21
        R2 (z 0) ratio density harrival_pos hdensity_pos hQ2_pos hden
        hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas
        ht_cont hQ1 hT1 hW1 hbounds hz hR2_pos hswitch12_pos hsum hu
        hswitch_lt_Q1 hgap_nonneg hA_pos with
    ⟨ε, hε_pos, hlt⟩
  refine ⟨replacement ε, Hcur, ?_, ?_⟩
  · simpa [replaceDynamicPolicyState] using Hrep ε hε_pos
  · simpa [gn21MeasuredAggregateDynamicStateReward_zero,
      gn21MeasuredAggregateRewardPrimitives, hQ_other, hT_other, hW_other,
      hQ_current, hT_current, hW_current, hQ_replacement ε hε_pos,
      hT_replacement ε hε_pos, hW_replacement ε hε_pos] using hlt

/--
Surge-state finite lower-endpoint counterpart of the Lemma 9 bridge.  A
leftward expansion of a lower endpoint feeds the same measured aggregate
strict-local state-replacement interface as the upper-endpoint movement.
-/
theorem paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_lower_interval_density
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy)
    (replacement : ℝ → TripPolicy)
    (upperEndpoint u T1 Q1 T2 Q2 R1 ratio δ : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrival 1)
    (hdensity_pos : 0 < density u)
    (hQ1_pos : 0 < Q1)
    (hden :
      gn21LowerEndpointQiPath (arrival 1) switch21 upperEndpoint density
          (gn21SwitchProb switch21 switch12) u * T1 +
        Q1 *
          gn21LowerEndpointTiPath (arrival 1) upperEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) volume
        u upperEndpoint)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (𝓝 u))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) u)
    (hw_int :
      IntervalIntegrable
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) volume u upperEndpoint)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) (𝓝 u))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume u upperEndpoint)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hQ2 :
      gn21LowerEndpointQiPath (arrival 1) switch21 upperEndpoint density
        (gn21SwitchProb switch21 switch12) u = Q2)
    (hT2 :
      gn21LowerEndpointTiPath (arrival 1) upperEndpoint density u = T2)
    (hW2 :
      gn21LowerEndpointWiPath (arrival 1) upperEndpoint density
        (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) u =
          m 1 * (T2 - 1) + z 1 * (Q2 - switch21))
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z 1 = ratio * (m 1 - R1))
    (hmR_pos : 0 < m 1 - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hu : 0 < u)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (hδ : 0 < δ)
    (Hcur :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (Hrep :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (ρ 0) (replacement ε))
    (hQ_other :
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) = Q1)
    (hT_other :
      gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) = T1)
    (hW_other :
      gn21ScaledStateEarning (μ 0) (arrival 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
          R1 * T1)
    (hQ_current :
      gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) =
        gn21LowerEndpointQiPath (arrival 1) switch21 upperEndpoint density
          (gn21SwitchProb switch21 switch12) u)
    (hT_current :
      gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) =
        gn21LowerEndpointTiPath (arrival 1) upperEndpoint density u)
    (hW_current :
      gn21ScaledStateEarning (μ 1) (arrival 1)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
        gn21LowerEndpointWiPath (arrival 1) upperEndpoint density
          (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) u)
    (hQ_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            (replacement ε) =
          gn21LowerEndpointQiPath (arrival 1) switch21 upperEndpoint density
            (gn21SwitchProb switch21 switch12) (u - ε))
    (hT_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ScaledStateTime (μ 1) (arrival 1) (replacement ε) =
          gn21LowerEndpointTiPath (arrival 1) upperEndpoint density (u - ε))
    (hW_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ScaledStateEarning (μ 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (replacement ε) =
          gn21LowerEndpointWiPath (arrival 1) upperEndpoint density
            (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12)
            (u - ε)) :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 1 τ) 0)
          ((replaceDynamicPolicyState ρ 1 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 (ρ 1) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 τ := by
  rcases
      paper_lemma9_exists_pos_left_improvement_of_lower_interval_density_current_bounds
        (arrival 1) upperEndpoint u T1 Q1 T2 Q2 switch21 switch12
        (m 1) R1 (z 1) ratio δ density harrival_pos hdensity_pos hQ1_pos
        hden hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas
        ht_cont hQ2 hT2 hW2 hbounds hz hmR_pos hR1_nonneg hT1_nonneg
        hswitch21_pos hsum hu hswitch_lt_Q2 hgap_nonneg hδ with
    ⟨ε, hε_pos, hε_lt, hlt⟩
  refine ⟨replacement ε, Hcur, ?_, ?_⟩
  · simpa [replaceDynamicPolicyState] using Hrep ε hε_pos hε_lt
  · simpa [gn21MeasuredAggregateDynamicStateReward_one,
      gn21MeasuredAggregateRewardPrimitives, hQ_other, hT_other, hW_other,
      hQ_current, hT_current, hW_current,
      hQ_replacement ε hε_pos hε_lt,
      hT_replacement ε hε_pos hε_lt,
      hW_replacement ε hε_pos hε_lt,
      gn21AggregateDynamicReward_swap]
      using hlt

/--
Non-surge finite lower-endpoint counterpart of the Lemma 10 bridge.
-/
theorem paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_lower_interval_density
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy)
    (replacement : ℝ → TripPolicy)
    (upperEndpoint u T2 Q2 T1 Q1 R2 ratio δ : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrival 0)
    (hdensity_pos : 0 < density u)
    (hQ2_pos : 0 < Q2)
    (hden :
      gn21LowerEndpointQiPath (arrival 0) switch12 upperEndpoint density
          (gn21SwitchProb switch12 switch21) u * T2 +
        Q2 *
          gn21LowerEndpointTiPath (arrival 0) upperEndpoint density u ≠ 0)
    (hq_int :
      IntervalIntegrable
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) volume
        u upperEndpoint)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) (𝓝 u))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) u)
    (hw_int :
      IntervalIntegrable
        (fun τ => ctmcStructuredSurgePrice R2 (z 0) switch12 switch21 τ *
          density τ) volume u upperEndpoint)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice R2 (z 0) switch12 switch21 τ *
          density τ) (𝓝 u))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice R2 (z 0) switch12 switch21 τ *
          density τ) u)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume u upperEndpoint)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hQ1 :
      gn21LowerEndpointQiPath (arrival 0) switch12 upperEndpoint density
        (gn21SwitchProb switch12 switch21) u = Q1)
    (hT1 :
      gn21LowerEndpointTiPath (arrival 0) upperEndpoint density u = T1)
    (hW1 :
      gn21LowerEndpointWiPath (arrival 0) upperEndpoint density
        (ctmcStructuredSurgePrice R2 (z 0) switch12 switch21) u =
          R2 * (T1 - 1) + z 0 * (Q1 - switch12))
    (hbounds : lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12)
    (hz : z 0 = ratio * R2)
    (hR2_pos : 0 < R2)
    (hswitch12_pos : 0 < switch12)
    (hsum : 0 < switch12 + switch21)
    (hu : 0 < u)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hA_pos : 0 < T2 * switch12 + Q2)
    (hδ : 0 < δ)
    (Hcur :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (Hrep :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (replacement ε) (ρ 1))
    (hQ_other :
      gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) = Q2)
    (hT_other :
      gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) = T2)
    (hW_other :
      gn21ScaledStateEarning (μ 1) (arrival 1)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
          R2 * T2)
    (hQ_current :
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) =
        gn21LowerEndpointQiPath (arrival 0) switch12 upperEndpoint density
          (gn21SwitchProb switch12 switch21) u)
    (hT_current :
      gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) =
        gn21LowerEndpointTiPath (arrival 0) upperEndpoint density u)
    (hW_current :
      gn21ScaledStateEarning (μ 0) (arrival 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
        gn21LowerEndpointWiPath (arrival 0) upperEndpoint density
          (ctmcStructuredSurgePrice R2 (z 0) switch12 switch21) u)
    (hQ_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            (replacement ε) =
          gn21LowerEndpointQiPath (arrival 0) switch12 upperEndpoint density
            (gn21SwitchProb switch12 switch21) (u - ε))
    (hT_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ScaledStateTime (μ 0) (arrival 0) (replacement ε) =
          gn21LowerEndpointTiPath (arrival 0) upperEndpoint density (u - ε))
    (hW_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ScaledStateEarning (μ 0) (arrival 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (replacement ε) =
          gn21LowerEndpointWiPath (arrival 0) upperEndpoint density
            (ctmcStructuredSurgePrice R2 (z 0) switch12 switch21) (u - ε)) :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 0 τ) 0)
          ((replaceDynamicPolicyState ρ 0 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 0 (ρ 0) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 0 τ := by
  rcases
      paper_lemma10_exists_pos_left_improvement_of_lower_interval_density_current_bounds
        (arrival 0) upperEndpoint u T2 Q2 T1 Q1 switch12 switch21
        R2 (z 0) ratio δ density harrival_pos hdensity_pos hQ2_pos hden
        hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas
        ht_cont hQ1 hT1 hW1 hbounds hz hR2_pos hswitch12_pos hsum hu
        hswitch_lt_Q1 hgap_nonneg hA_pos hδ with
    ⟨ε, hε_pos, hε_lt, hlt⟩
  refine ⟨replacement ε, Hcur, ?_, ?_⟩
  · simpa [replaceDynamicPolicyState] using Hrep ε hε_pos hε_lt
  · simpa [gn21MeasuredAggregateDynamicStateReward_zero,
      gn21MeasuredAggregateRewardPrimitives, hQ_other, hT_other, hW_other,
      hQ_current, hT_current, hW_current,
      hQ_replacement ε hε_pos hε_lt,
      hT_replacement ε hε_pos hε_lt,
      hW_replacement ε hε_pos hε_lt] using hlt

/--
Surge-state unbounded-tail counterpart of the Lemma 9 bridge.  A leftward
expansion of the lower endpoint of `(u,∞)` feeds the measured aggregate
strict-local state-replacement interface.
-/
theorem paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_tail_interval_density
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy)
    (replacement : ℝ → TripPolicy)
    (u T1 Q1 T2 Q2 R1 ratio δ : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrival 1)
    (hdensity_pos : 0 < density u)
    (hQ1_pos : 0 < Q1)
    (hden :
      gn21TailQiPath (arrival 1) switch21 density
          (gn21SwitchProb switch21 switch12) u * T1 +
        Q1 * gn21TailTiPath (arrival 1) density u ≠ 0)
    (hq_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ)
        (Set.Ioi (u - 1)) volume)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (𝓝 u))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) u)
    (hw_int :
      IntegrableOn
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) (Set.Ioi (u - 1)) volume)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) (𝓝 u))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) u)
    (ht_int :
      IntegrableOn (fun τ => τ * density τ) (Set.Ioi (u - 1)) volume)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hQ2 :
      gn21TailQiPath (arrival 1) switch21 density
        (gn21SwitchProb switch21 switch12) u = Q2)
    (hT2 :
      gn21TailTiPath (arrival 1) density u = T2)
    (hW2 :
      gn21TailWiPath (arrival 1) density
        (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) u =
          m 1 * (T2 - 1) + z 1 * (Q2 - switch21))
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z 1 = ratio * (m 1 - R1))
    (hmR_pos : 0 < m 1 - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hu : 0 < u)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (hδ : 0 < δ)
    (Hcur :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (Hrep :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (ρ 0) (replacement ε))
    (hQ_other :
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) = Q1)
    (hT_other :
      gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) = T1)
    (hW_other :
      gn21ScaledStateEarning (μ 0) (arrival 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
          R1 * T1)
    (hQ_current :
      gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) =
        gn21TailQiPath (arrival 1) switch21 density
          (gn21SwitchProb switch21 switch12) u)
    (hT_current :
      gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) =
        gn21TailTiPath (arrival 1) density u)
    (hW_current :
      gn21ScaledStateEarning (μ 1) (arrival 1)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
        gn21TailWiPath (arrival 1) density
          (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) u)
    (hQ_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            (replacement ε) =
          gn21TailQiPath (arrival 1) switch21 density
            (gn21SwitchProb switch21 switch12) (u - ε))
    (hT_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ScaledStateTime (μ 1) (arrival 1) (replacement ε) =
          gn21TailTiPath (arrival 1) density (u - ε))
    (hW_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ScaledStateEarning (μ 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (replacement ε) =
          gn21TailWiPath (arrival 1) density
            (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12)
            (u - ε)) :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 1 τ) 0)
          ((replaceDynamicPolicyState ρ 1 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 (ρ 1) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 τ := by
  rcases
      paper_lemma9_exists_pos_left_improvement_of_tail_interval_density_current_bounds
        (arrival 1) u T1 Q1 T2 Q2 switch21 switch12
        (m 1) R1 (z 1) ratio δ density harrival_pos hdensity_pos
        hQ1_pos hden hq_int hq_meas hq_cont hw_int hw_meas hw_cont
        ht_int ht_meas ht_cont hQ2 hT2 hW2 hbounds hz hmR_pos
        hR1_nonneg hT1_nonneg hswitch21_pos hsum hu hswitch_lt_Q2
        hgap_nonneg hδ with
    ⟨ε, hε_pos, hε_lt, hlt⟩
  refine ⟨replacement ε, Hcur, ?_, ?_⟩
  · simpa [replaceDynamicPolicyState] using Hrep ε hε_pos hε_lt
  · simpa [gn21MeasuredAggregateDynamicStateReward_one,
      gn21MeasuredAggregateRewardPrimitives, hQ_other, hT_other, hW_other,
      hQ_current, hT_current, hW_current,
      hQ_replacement ε hε_pos hε_lt,
      hT_replacement ε hε_pos hε_lt,
      hW_replacement ε hε_pos hε_lt,
      gn21AggregateDynamicReward_swap]
      using hlt

/--
Surge-state middle-rejection lower-cutoff counterpart of the Lemma 9 bridge.
A rightward expansion of the short accepted interval feeds the measured
aggregate strict-local state-replacement interface.
-/
theorem paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_interval_density
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy)
    (replacement : ℝ → TripPolicy)
    (lo hi T1 Q1 T2 Q2 R1 ratio δ : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrival 1)
    (hdensity_pos : 0 < density lo)
    (hQ1_pos : 0 < Q1)
    (hden :
      gn21RejectMiddleQiPath (arrival 1) switch21 density
          (gn21SwitchProb switch21 switch12) lo hi * T1 +
        Q1 * gn21RejectMiddleTiPath (arrival 1) density lo hi ≠ 0)
    (hq_int :
      IntervalIntegrable
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) volume
        0 lo)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (𝓝 lo))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) lo)
    (hw_int :
      IntervalIntegrable
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) volume 0 lo)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) (𝓝 lo))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) lo)
    (ht_int :
      IntervalIntegrable (fun τ => τ * density τ) volume 0 lo)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 lo))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) lo)
    (hQ2 :
      gn21RejectMiddleQiPath (arrival 1) switch21 density
        (gn21SwitchProb switch21 switch12) lo hi = Q2)
    (hT2 :
      gn21RejectMiddleTiPath (arrival 1) density lo hi = T2)
    (hW2 :
      gn21RejectMiddleWiPath (arrival 1) density
        (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) lo hi =
          m 1 * (T2 - 1) + z 1 * (Q2 - switch21))
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z 1 = ratio * (m 1 - R1))
    (hmR_pos : 0 < m 1 - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hlo_pos : 0 < lo)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (hδ : 0 < δ)
    (Hcur :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (Hrep :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (ρ 0) (replacement ε))
    (hQ_other :
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) = Q1)
    (hT_other :
      gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) = T1)
    (hW_other :
      gn21ScaledStateEarning (μ 0) (arrival 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
          R1 * T1)
    (hQ_current :
      gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) =
        gn21RejectMiddleQiPath (arrival 1) switch21 density
          (gn21SwitchProb switch21 switch12) lo hi)
    (hT_current :
      gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) =
        gn21RejectMiddleTiPath (arrival 1) density lo hi)
    (hW_current :
      gn21ScaledStateEarning (μ 1) (arrival 1)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
        gn21RejectMiddleWiPath (arrival 1) density
          (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) lo hi)
    (hQ_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            (replacement ε) =
          gn21RejectMiddleQiPath (arrival 1) switch21 density
            (gn21SwitchProb switch21 switch12) (lo + ε) hi)
    (hT_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ScaledStateTime (μ 1) (arrival 1) (replacement ε) =
          gn21RejectMiddleTiPath (arrival 1) density (lo + ε) hi)
    (hW_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ScaledStateEarning (μ 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (replacement ε) =
          gn21RejectMiddleWiPath (arrival 1) density
            (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12)
            (lo + ε) hi) :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 1 τ) 0)
          ((replaceDynamicPolicyState ρ 1 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 (ρ 1) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 τ := by
  rcases
      paper_lemma9_exists_pos_right_improvement_of_reject_middle_lo_interval_density_current_bounds
        (arrival 1) lo hi T1 Q1 T2 Q2 switch21 switch12
        (m 1) R1 (z 1) ratio δ density harrival_pos hdensity_pos
        hQ1_pos hden hq_int hq_meas hq_cont hw_int hw_meas hw_cont
        ht_int ht_meas ht_cont hQ2 hT2 hW2 hbounds hz hmR_pos
        hR1_nonneg hT1_nonneg hswitch21_pos hsum hlo_pos hswitch_lt_Q2
        hgap_nonneg hδ with
    ⟨ε, hε_pos, hε_lt, hlt⟩
  refine ⟨replacement ε, Hcur, ?_, ?_⟩
  · simpa [replaceDynamicPolicyState] using Hrep ε hε_pos hε_lt
  · simpa [gn21MeasuredAggregateDynamicStateReward_one,
      gn21MeasuredAggregateRewardPrimitives, hQ_other, hT_other, hW_other,
      hQ_current, hT_current, hW_current,
      hQ_replacement ε hε_pos hε_lt,
      hT_replacement ε hε_pos hε_lt,
      hW_replacement ε hε_pos hε_lt,
      gn21AggregateDynamicReward_swap]
      using hlt

/--
Surge-state middle-rejection upper-cutoff counterpart of the Lemma 9 bridge.
A leftward expansion of the accepted tail feeds the measured aggregate
strict-local state-replacement interface.
-/
theorem paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_interval_density
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy)
    (replacement : ℝ → TripPolicy)
    (lo hi T1 Q1 T2 Q2 R1 ratio δ : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrival 1)
    (hdensity_pos : 0 < density hi)
    (hQ1_pos : 0 < Q1)
    (hden :
      gn21RejectMiddleQiPath (arrival 1) switch21 density
          (gn21SwitchProb switch21 switch12) lo hi * T1 +
        Q1 * gn21RejectMiddleTiPath (arrival 1) density lo hi ≠ 0)
    (hq_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ)
        (Set.Ioi (hi - 1)) volume)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (𝓝 hi))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) hi)
    (hw_int :
      IntegrableOn
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) (Set.Ioi (hi - 1)) volume)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) (𝓝 hi))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          density τ) hi)
    (ht_int :
      IntegrableOn (fun τ => τ * density τ) (Set.Ioi (hi - 1)) volume)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 hi))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) hi)
    (hQ2 :
      gn21RejectMiddleQiPath (arrival 1) switch21 density
        (gn21SwitchProb switch21 switch12) lo hi = Q2)
    (hT2 :
      gn21RejectMiddleTiPath (arrival 1) density lo hi = T2)
    (hW2 :
      gn21RejectMiddleWiPath (arrival 1) density
        (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) lo hi =
          m 1 * (T2 - 1) + z 1 * (Q2 - switch21))
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z 1 = ratio * (m 1 - R1))
    (hmR_pos : 0 < m 1 - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hhi_pos : 0 < hi)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (hδ : 0 < δ)
    (Hcur :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (Hrep :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (ρ 0) (replacement ε))
    (hQ_other :
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) = Q1)
    (hT_other :
      gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) = T1)
    (hW_other :
      gn21ScaledStateEarning (μ 0) (arrival 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
          R1 * T1)
    (hQ_current :
      gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) =
        gn21RejectMiddleQiPath (arrival 1) switch21 density
          (gn21SwitchProb switch21 switch12) lo hi)
    (hT_current :
      gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) =
        gn21RejectMiddleTiPath (arrival 1) density lo hi)
    (hW_current :
      gn21ScaledStateEarning (μ 1) (arrival 1)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
        gn21RejectMiddleWiPath (arrival 1) density
          (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) lo hi)
    (hQ_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            (replacement ε) =
          gn21RejectMiddleQiPath (arrival 1) switch21 density
            (gn21SwitchProb switch21 switch12) lo (hi - ε))
    (hT_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ScaledStateTime (μ 1) (arrival 1) (replacement ε) =
          gn21RejectMiddleTiPath (arrival 1) density lo (hi - ε))
    (hW_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ScaledStateEarning (μ 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (replacement ε) =
          gn21RejectMiddleWiPath (arrival 1) density
            (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12)
            lo (hi - ε)) :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 1 τ) 0)
          ((replaceDynamicPolicyState ρ 1 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 (ρ 1) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 τ := by
  rcases
      paper_lemma9_exists_pos_left_improvement_of_reject_middle_hi_interval_density_current_bounds
        (arrival 1) lo hi T1 Q1 T2 Q2 switch21 switch12
        (m 1) R1 (z 1) ratio δ density harrival_pos hdensity_pos
        hQ1_pos hden hq_int hq_meas hq_cont hw_int hw_meas hw_cont
        ht_int ht_meas ht_cont hQ2 hT2 hW2 hbounds hz hmR_pos
        hR1_nonneg hT1_nonneg hswitch21_pos hsum hhi_pos hswitch_lt_Q2
        hgap_nonneg hδ with
    ⟨ε, hε_pos, hε_lt, hlt⟩
  refine ⟨replacement ε, Hcur, ?_, ?_⟩
  · simpa [replaceDynamicPolicyState] using Hrep ε hε_pos hε_lt
  · simpa [gn21MeasuredAggregateDynamicStateReward_one,
      gn21MeasuredAggregateRewardPrimitives, hQ_other, hT_other, hW_other,
      hQ_current, hT_current, hW_current,
      hQ_replacement ε hε_pos hε_lt,
      hT_replacement ε hε_pos hε_lt,
      hW_replacement ε hε_pos hε_lt,
      gn21AggregateDynamicReward_swap]
      using hlt

/--
Surge-state reject-middle lower-cutoff bridge specialized to the concrete
with-density replacement policy `rejectMiddleTripsPolicy (lo+ε) hi`.
-/
theorem paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy)
    (lo hi T1 Q1 T2 Q2 R1 ratio δ : ℝ)
    (densityNN : ℝ → NNReal)
    (hμ_surge :
      μ 1 = volume.withDensity fun τ => (densityNN τ : ℝ≥0∞))
    (hdensity_meas : Measurable densityNN)
    (harrival_pos : 0 < arrival 1)
    (hdensity_pos : 0 < (densityNN lo : ℝ))
    (hQ1_pos : 0 < Q1)
    (hden :
      gn21RejectMiddleQiPath (arrival 1) switch21
          (fun τ => (densityNN τ : ℝ)) (gn21SwitchProb switch21 switch12)
          lo hi * T1 +
        Q1 *
          gn21RejectMiddleTiPath (arrival 1)
            (fun τ => (densityNN τ : ℝ)) lo hi ≠ 0)
    (hq_int :
      IntervalIntegrable
        (fun τ => gn21SwitchProb switch21 switch12 τ *
          (densityNN τ : ℝ)) volume 0 lo)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch21 switch12 τ *
          (densityNN τ : ℝ)) (𝓝 lo))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch21 switch12 τ *
          (densityNN τ : ℝ)) lo)
    (hw_int :
      IntervalIntegrable
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          (densityNN τ : ℝ)) volume 0 lo)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          (densityNN τ : ℝ)) (𝓝 lo))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          (densityNN τ : ℝ)) lo)
    (ht_int :
      IntervalIntegrable (fun τ => τ * (densityNN τ : ℝ)) volume 0 lo)
    (ht_meas :
      StronglyMeasurableAtFilter
        (fun τ => τ * (densityNN τ : ℝ)) (𝓝 lo))
    (ht_cont : ContinuousAt (fun τ => τ * (densityNN τ : ℝ)) lo)
    (hQ2 :
      gn21RejectMiddleQiPath (arrival 1) switch21
        (fun τ => (densityNN τ : ℝ)) (gn21SwitchProb switch21 switch12)
        lo hi = Q2)
    (hT2 :
      gn21RejectMiddleTiPath (arrival 1) (fun τ => (densityNN τ : ℝ))
        lo hi = T2)
    (hW2 :
      gn21RejectMiddleWiPath (arrival 1) (fun τ => (densityNN τ : ℝ))
        (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) lo hi =
          m 1 * (T2 - 1) + z 1 * (Q2 - switch21))
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z 1 = ratio * (m 1 - R1))
    (hmR_pos : 0 < m 1 - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hlo_pos : 0 < lo)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (hδ : 0 < δ)
    (hloδ_le_hi : lo + δ ≤ hi)
    (Hcur :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (Hrep :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (ρ 0)
            (gn21RejectMiddleLoReplacement lo hi ε))
    (hQ_other :
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) = Q1)
    (hT_other :
      gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) = T1)
    (hW_other :
      gn21ScaledStateEarning (μ 0) (arrival 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
          R1 * T1)
    (hQ_current :
      gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) =
        gn21RejectMiddleQiPath (arrival 1) switch21
          (fun τ => (densityNN τ : ℝ)) (gn21SwitchProb switch21 switch12)
          lo hi)
    (hT_current :
      gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) =
        gn21RejectMiddleTiPath (arrival 1)
          (fun τ => (densityNN τ : ℝ)) lo hi)
    (hW_current :
      gn21ScaledStateEarning (μ 1) (arrival 1)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
        gn21RejectMiddleWiPath (arrival 1) (fun τ => (densityNN τ : ℝ))
          (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) lo hi)
    (hq_short_replacement_int :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        IntegrableOn
          (fun τ => gn21SwitchProb switch21 switch12 τ *
            (densityNN τ : ℝ))
          (Set.Ioo (0 : ℝ) (lo + ε)) volume)
    (hq_tail_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switch21 switch12 τ *
          (densityNN τ : ℝ)) (Set.Ioi hi) volume)
    (ht_short_replacement_int :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        IntegrableOn (fun τ => τ * (densityNN τ : ℝ))
          (Set.Ioo (0 : ℝ) (lo + ε)) volume)
    (ht_tail_int :
      IntegrableOn (fun τ => τ * (densityNN τ : ℝ)) (Set.Ioi hi)
        volume)
    (hw_short_replacement_int :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        IntegrableOn
          (fun τ =>
            ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
              (densityNN τ : ℝ))
          (Set.Ioo (0 : ℝ) (lo + ε)) volume)
    (hw_tail_int :
      IntegrableOn
        (fun τ =>
          ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
            (densityNN τ : ℝ)) (Set.Ioi hi) volume) :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 1 τ) 0)
          ((replaceDynamicPolicyState ρ 1 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 (ρ 1) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 τ := by
  refine
    paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_interval_density
      (μ := μ) (arrival := arrival) (m := m) (z := z)
      (switch12 := switch12) (switch21 := switch21) (ρ := ρ)
      (replacement := gn21RejectMiddleLoReplacement lo hi)
      (lo := lo) (hi := hi) (T1 := T1) (Q1 := Q1) (T2 := T2)
      (Q2 := Q2) (R1 := R1) (ratio := ratio) (δ := δ)
      (density := fun τ => (densityNN τ : ℝ))
      (harrival_pos := harrival_pos) (hdensity_pos := hdensity_pos)
      (hQ1_pos := hQ1_pos) (hden := hden) (hq_int := hq_int)
      (hq_meas := hq_meas) (hq_cont := hq_cont) (hw_int := hw_int)
      (hw_meas := hw_meas) (hw_cont := hw_cont) (ht_int := ht_int)
      (ht_meas := ht_meas) (ht_cont := ht_cont) (hQ2 := hQ2)
      (hT2 := hT2) (hW2 := hW2) (hbounds := hbounds) (hz := hz)
      (hmR_pos := hmR_pos) (hR1_nonneg := hR1_nonneg)
      (hT1_nonneg := hT1_nonneg) (hswitch21_pos := hswitch21_pos)
      (hsum := hsum) (hlo_pos := hlo_pos)
      (hswitch_lt_Q2 := hswitch_lt_Q2) (hgap_nonneg := hgap_nonneg)
      (hδ := hδ) (Hcur := Hcur) (Hrep := Hrep)
      (hQ_other := hQ_other) (hT_other := hT_other)
      (hW_other := hW_other) (hQ_current := hQ_current)
      (hT_current := hT_current) (hW_current := hW_current)
      (hQ_replacement := ?_) (hT_replacement := ?_)
      (hW_replacement := ?_)
  · intro ε hε_pos hε_lt
    rw [hμ_surge]
    exact
      gn21ExitWeightIntegral_rejectMiddleLoReplacement_withDensity_eq_rejectMiddleQiPath
        (arrival 1) switch21 switch12 lo hi ε densityNN hdensity_meas
        (by linarith) (by
          have hle_delta : lo + ε ≤ lo + δ := by linarith
          exact le_trans hle_delta hloδ_le_hi)
        (hq_short_replacement_int ε hε_pos hε_lt) hq_tail_int
  · intro ε hε_pos hε_lt
    rw [hμ_surge]
    exact
      gn21ScaledStateTime_rejectMiddleLoReplacement_withDensity_eq_rejectMiddleTiPath
        (arrival 1) lo hi ε densityNN hdensity_meas
        (by linarith) (by
          have hle_delta : lo + ε ≤ lo + δ := by linarith
          exact le_trans hle_delta hloδ_le_hi)
        (ht_short_replacement_int ε hε_pos hε_lt) ht_tail_int
  · intro ε hε_pos hε_lt
    rw [hμ_surge]
    simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
      ctmcStructuredSurgePrice] using
      gn21ScaledStateEarning_rejectMiddleLoReplacement_withDensity_eq_rejectMiddleWiPath
        (arrival 1) lo hi ε densityNN
        (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12)
        hdensity_meas (by linarith) (by
          have hle_delta : lo + ε ≤ lo + δ := by linarith
          exact le_trans hle_delta hloδ_le_hi)
        (hw_short_replacement_int ε hε_pos hε_lt) hw_tail_int

/--
Surge-state reject-middle upper-cutoff bridge specialized to the concrete
with-density replacement policy `rejectMiddleTripsPolicy lo (hi-ε)`.
-/
theorem paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy)
    (lo hi T1 Q1 T2 Q2 R1 ratio δ : ℝ)
    (densityNN : ℝ → NNReal)
    (hμ_surge :
      μ 1 = volume.withDensity fun τ => (densityNN τ : ℝ≥0∞))
    (hdensity_meas : Measurable densityNN)
    (harrival_pos : 0 < arrival 1)
    (hdensity_pos : 0 < (densityNN hi : ℝ))
    (hQ1_pos : 0 < Q1)
    (hden :
      gn21RejectMiddleQiPath (arrival 1) switch21
          (fun τ => (densityNN τ : ℝ)) (gn21SwitchProb switch21 switch12)
          lo hi * T1 +
        Q1 *
          gn21RejectMiddleTiPath (arrival 1)
            (fun τ => (densityNN τ : ℝ)) lo hi ≠ 0)
    (hq_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switch21 switch12 τ *
          (densityNN τ : ℝ)) (Set.Ioi (hi - 1)) volume)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch21 switch12 τ *
          (densityNN τ : ℝ)) (𝓝 hi))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch21 switch12 τ *
          (densityNN τ : ℝ)) hi)
    (hw_int :
      IntegrableOn
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          (densityNN τ : ℝ)) (Set.Ioi (hi - 1)) volume)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          (densityNN τ : ℝ)) (𝓝 hi))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
          (densityNN τ : ℝ)) hi)
    (ht_int :
      IntegrableOn (fun τ => τ * (densityNN τ : ℝ))
        (Set.Ioi (hi - 1)) volume)
    (ht_meas :
      StronglyMeasurableAtFilter
        (fun τ => τ * (densityNN τ : ℝ)) (𝓝 hi))
    (ht_cont : ContinuousAt (fun τ => τ * (densityNN τ : ℝ)) hi)
    (hQ2 :
      gn21RejectMiddleQiPath (arrival 1) switch21
        (fun τ => (densityNN τ : ℝ)) (gn21SwitchProb switch21 switch12)
        lo hi = Q2)
    (hT2 :
      gn21RejectMiddleTiPath (arrival 1) (fun τ => (densityNN τ : ℝ))
        lo hi = T2)
    (hW2 :
      gn21RejectMiddleWiPath (arrival 1) (fun τ => (densityNN τ : ℝ))
        (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) lo hi =
          m 1 * (T2 - 1) + z 1 * (Q2 - switch21))
    (hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21)
    (hz : z 1 = ratio * (m 1 - R1))
    (hmR_pos : 0 < m 1 - R1)
    (hR1_nonneg : 0 ≤ R1)
    (hT1_nonneg : 0 ≤ T1)
    (hswitch21_pos : 0 < switch21)
    (hsum : 0 < switch21 + switch12)
    (hhi_pos : 0 < hi)
    (hswitch_lt_Q2 : switch21 < Q2)
    (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
    (hδ : 0 < δ)
    (hlo_nonneg : 0 ≤ lo)
    (hlo_le_hiδ : lo ≤ hi - δ)
    (Hcur :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (Hrep :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (ρ 0)
            (gn21RejectMiddleHiReplacement lo hi ε))
    (hQ_other :
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) = Q1)
    (hT_other :
      gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) = T1)
    (hW_other :
      gn21ScaledStateEarning (μ 0) (arrival 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
          R1 * T1)
    (hQ_current :
      gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) =
        gn21RejectMiddleQiPath (arrival 1) switch21
          (fun τ => (densityNN τ : ℝ)) (gn21SwitchProb switch21 switch12)
          lo hi)
    (hT_current :
      gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) =
        gn21RejectMiddleTiPath (arrival 1)
          (fun τ => (densityNN τ : ℝ)) lo hi)
    (hW_current :
      gn21ScaledStateEarning (μ 1) (arrival 1)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
        gn21RejectMiddleWiPath (arrival 1) (fun τ => (densityNN τ : ℝ))
          (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) lo hi)
    (hq_short_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switch21 switch12 τ *
          (densityNN τ : ℝ)) (Set.Ioo (0 : ℝ) lo) volume)
    (hq_tail_replacement_int :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        IntegrableOn
          (fun τ => gn21SwitchProb switch21 switch12 τ *
            (densityNN τ : ℝ))
          (Set.Ioi (hi - ε)) volume)
    (ht_short_int :
      IntegrableOn (fun τ => τ * (densityNN τ : ℝ))
        (Set.Ioo (0 : ℝ) lo) volume)
    (ht_tail_replacement_int :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        IntegrableOn (fun τ => τ * (densityNN τ : ℝ))
          (Set.Ioi (hi - ε)) volume)
    (hw_short_int :
      IntegrableOn
        (fun τ =>
          ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
            (densityNN τ : ℝ)) (Set.Ioo (0 : ℝ) lo) volume)
    (hw_tail_replacement_int :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        IntegrableOn
          (fun τ =>
            ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
              (densityNN τ : ℝ))
          (Set.Ioi (hi - ε)) volume) :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 1 τ) 0)
          ((replaceDynamicPolicyState ρ 1 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 (ρ 1) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 τ := by
  refine
    paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_interval_density
      (μ := μ) (arrival := arrival) (m := m) (z := z)
      (switch12 := switch12) (switch21 := switch21) (ρ := ρ)
      (replacement := gn21RejectMiddleHiReplacement lo hi)
      (lo := lo) (hi := hi) (T1 := T1) (Q1 := Q1) (T2 := T2)
      (Q2 := Q2) (R1 := R1) (ratio := ratio) (δ := δ)
      (density := fun τ => (densityNN τ : ℝ))
      (harrival_pos := harrival_pos) (hdensity_pos := hdensity_pos)
      (hQ1_pos := hQ1_pos) (hden := hden) (hq_int := hq_int)
      (hq_meas := hq_meas) (hq_cont := hq_cont) (hw_int := hw_int)
      (hw_meas := hw_meas) (hw_cont := hw_cont) (ht_int := ht_int)
      (ht_meas := ht_meas) (ht_cont := ht_cont) (hQ2 := hQ2)
      (hT2 := hT2) (hW2 := hW2) (hbounds := hbounds) (hz := hz)
      (hmR_pos := hmR_pos) (hR1_nonneg := hR1_nonneg)
      (hT1_nonneg := hT1_nonneg) (hswitch21_pos := hswitch21_pos)
      (hsum := hsum) (hhi_pos := hhi_pos)
      (hswitch_lt_Q2 := hswitch_lt_Q2) (hgap_nonneg := hgap_nonneg)
      (hδ := hδ) (Hcur := Hcur) (Hrep := Hrep)
      (hQ_other := hQ_other) (hT_other := hT_other)
      (hW_other := hW_other) (hQ_current := hQ_current)
      (hT_current := hT_current) (hW_current := hW_current)
      (hQ_replacement := ?_) (hT_replacement := ?_)
      (hW_replacement := ?_)
  · intro ε hε_pos hε_lt
    rw [hμ_surge]
    exact
      gn21ExitWeightIntegral_rejectMiddleHiReplacement_withDensity_eq_rejectMiddleQiPath
        (arrival 1) switch21 switch12 lo hi ε densityNN hdensity_meas
        hlo_nonneg (by
          have hhi_delta_le : hi - δ ≤ hi - ε := by linarith
          exact le_trans hlo_le_hiδ hhi_delta_le)
        hq_short_int (hq_tail_replacement_int ε hε_pos hε_lt)
  · intro ε hε_pos hε_lt
    rw [hμ_surge]
    exact
      gn21ScaledStateTime_rejectMiddleHiReplacement_withDensity_eq_rejectMiddleTiPath
        (arrival 1) lo hi ε densityNN hdensity_meas hlo_nonneg
        (by
          have hhi_delta_le : hi - δ ≤ hi - ε := by linarith
          exact le_trans hlo_le_hiδ hhi_delta_le)
        ht_short_int (ht_tail_replacement_int ε hε_pos hε_lt)
  · intro ε hε_pos hε_lt
    rw [hμ_surge]
    simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
      ctmcStructuredSurgePrice] using
      gn21ScaledStateEarning_rejectMiddleHiReplacement_withDensity_eq_rejectMiddleWiPath
        (arrival 1) lo hi ε densityNN
        (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12)
        hdensity_meas hlo_nonneg (by
          have hhi_delta_le : hi - δ ≤ hi - ε := by linarith
          exact le_trans hlo_le_hiδ hhi_delta_le)
        hw_short_int (hw_tail_replacement_int ε hε_pos hε_lt)

/--
Non-surge unbounded-tail counterpart of the Lemma 10 bridge.
-/
theorem paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_tail_interval_density
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy)
    (replacement : ℝ → TripPolicy)
    (u T2 Q2 T1 Q1 R2 ratio δ : ℝ)
    (density : ℝ → ℝ)
    (harrival_pos : 0 < arrival 0)
    (hdensity_pos : 0 < density u)
    (hQ2_pos : 0 < Q2)
    (hden :
      gn21TailQiPath (arrival 0) switch12 density
          (gn21SwitchProb switch12 switch21) u * T2 +
        Q2 * gn21TailTiPath (arrival 0) density u ≠ 0)
    (hq_int :
      IntegrableOn
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ)
        (Set.Ioi (u - 1)) volume)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) (𝓝 u))
    (hq_cont :
      ContinuousAt
        (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) u)
    (hw_int :
      IntegrableOn
        (fun τ => ctmcStructuredSurgePrice R2 (z 0) switch12 switch21 τ *
          density τ) (Set.Ioi (u - 1)) volume)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun τ => ctmcStructuredSurgePrice R2 (z 0) switch12 switch21 τ *
          density τ) (𝓝 u))
    (hw_cont :
      ContinuousAt
        (fun τ => ctmcStructuredSurgePrice R2 (z 0) switch12 switch21 τ *
          density τ) u)
    (ht_int :
      IntegrableOn (fun τ => τ * density τ) (Set.Ioi (u - 1)) volume)
    (ht_meas :
      StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u))
    (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
    (hQ1 :
      gn21TailQiPath (arrival 0) switch12 density
        (gn21SwitchProb switch12 switch21) u = Q1)
    (hT1 :
      gn21TailTiPath (arrival 0) density u = T1)
    (hW1 :
      gn21TailWiPath (arrival 0) density
        (ctmcStructuredSurgePrice R2 (z 0) switch12 switch21) u =
          R2 * (T1 - 1) + z 0 * (Q1 - switch12))
    (hbounds : lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12)
    (hz : z 0 = ratio * R2)
    (hR2_pos : 0 < R2)
    (hswitch12_pos : 0 < switch12)
    (hsum : 0 < switch12 + switch21)
    (hu : 0 < u)
    (hswitch_lt_Q1 : switch12 < Q1)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hA_pos : 0 < T2 * switch12 + Q2)
    (hδ : 0 < δ)
    (Hcur :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (Hrep :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (replacement ε) (ρ 1))
    (hQ_other :
      gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) = Q2)
    (hT_other :
      gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) = T2)
    (hW_other :
      gn21ScaledStateEarning (μ 1) (arrival 1)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
          R2 * T2)
    (hQ_current :
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) =
        gn21TailQiPath (arrival 0) switch12 density
          (gn21SwitchProb switch12 switch21) u)
    (hT_current :
      gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) =
        gn21TailTiPath (arrival 0) density u)
    (hW_current :
      gn21ScaledStateEarning (μ 0) (arrival 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
        gn21TailWiPath (arrival 0) density
          (ctmcStructuredSurgePrice R2 (z 0) switch12 switch21) u)
    (hQ_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            (replacement ε) =
          gn21TailQiPath (arrival 0) switch12 density
            (gn21SwitchProb switch12 switch21) (u - ε))
    (hT_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ScaledStateTime (μ 0) (arrival 0) (replacement ε) =
          gn21TailTiPath (arrival 0) density (u - ε))
    (hW_replacement :
      ∀ ε : ℝ, 0 < ε → ε < δ →
        gn21ScaledStateEarning (μ 0) (arrival 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (replacement ε) =
          gn21TailWiPath (arrival 0) density
            (ctmcStructuredSurgePrice R2 (z 0) switch12 switch21) (u - ε)) :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 0 τ) 0)
          ((replaceDynamicPolicyState ρ 0 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 0 (ρ 0) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 0 τ := by
  rcases
      paper_lemma10_exists_pos_left_improvement_of_tail_interval_density_current_bounds
        (arrival 0) u T2 Q2 T1 Q1 switch12 switch21
        R2 (z 0) ratio δ density harrival_pos hdensity_pos hQ2_pos hden
        hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas
        ht_cont hQ1 hT1 hW1 hbounds hz hR2_pos hswitch12_pos hsum hu
        hswitch_lt_Q1 hgap_nonneg hA_pos hδ with
    ⟨ε, hε_pos, hε_lt, hlt⟩
  refine ⟨replacement ε, Hcur, ?_, ?_⟩
  · simpa [replaceDynamicPolicyState] using Hrep ε hε_pos hε_lt
  · simpa [gn21MeasuredAggregateDynamicStateReward_zero,
      gn21MeasuredAggregateRewardPrimitives, hQ_other, hT_other, hW_other,
      hQ_current, hT_current, hW_current,
      hQ_replacement ε hε_pos hε_lt,
      hT_replacement ε hε_pos hε_lt,
      hW_replacement ε hε_pos hε_lt] using hlt

/--
Primitive data package for applying the surge-state Lemma 9 interval bridge to
a fixed dynamic policy.  This isolates the remaining continuous endpoint
identification work from the already-compiled aggregate-reward routing.
-/
structure GN21SurgeIntervalEndpointBridgeData
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy) where
  replacement : ℝ → TripPolicy
  lowerEndpoint : ℝ
  u : ℝ
  T1 : ℝ
  Q1 : ℝ
  T2 : ℝ
  Q2 : ℝ
  R1 : ℝ
  ratio : ℝ
  density : ℝ → ℝ
  harrival_pos : 0 < arrival 1
  hdensity_pos : 0 < density u
  hQ1_pos : 0 < Q1
  hden :
    gn21EndpointQiPath (arrival 1) switch21 lowerEndpoint density
        (gn21SwitchProb switch21 switch12) u * T1 +
      Q1 *
        gn21EndpointTiPath (arrival 1) lowerEndpoint density u ≠ 0
  hq_int :
    IntervalIntegrable
      (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) volume
      lowerEndpoint u
  hq_meas :
    StronglyMeasurableAtFilter
      (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (𝓝 u)
  hq_cont :
    ContinuousAt
      (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) u
  hw_int :
    IntervalIntegrable
      (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
        density τ) volume lowerEndpoint u
  hw_meas :
    StronglyMeasurableAtFilter
      (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
        density τ) (𝓝 u)
  hw_cont :
    ContinuousAt
      (fun τ => ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12 τ *
        density τ) u
  ht_int :
    IntervalIntegrable (fun τ => τ * density τ) volume lowerEndpoint u
  ht_meas :
    StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u)
  ht_cont : ContinuousAt (fun τ => τ * density τ) u
  hQ2 :
    gn21EndpointQiPath (arrival 1) switch21 lowerEndpoint density
      (gn21SwitchProb switch21 switch12) u = Q2
  hT2 :
    gn21EndpointTiPath (arrival 1) lowerEndpoint density u = T2
  hW2 :
    gn21EndpointWiPath (arrival 1) lowerEndpoint density
      (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) u =
        m 1 * (T2 - 1) + z 1 * (Q2 - switch21)
  hbounds : lemma9StructuredBounds ratio T1 Q1 T2 Q2 switch21
  hz : z 1 = ratio * (m 1 - R1)
  hmR_pos : 0 < m 1 - R1
  hR1_nonneg : 0 ≤ R1
  hT1_nonneg : 0 ≤ T1
  hswitch21_pos : 0 < switch21
  hsum : 0 < switch21 + switch12
  hu : 0 < u
  hswitch_lt_Q2 : switch21 < Q2
  hgap_nonneg : 0 ≤ switch21 * T2 - Q2
  Hcur :
    GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
      switch12 switch21 (ρ 0) (ρ 1)
  Hrep :
    ∀ ε : ℝ, 0 < ε →
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (replacement ε)
  hQ_other :
    gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) = Q1
  hT_other :
    gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) = T1
  hW_other :
    gn21ScaledStateEarning (μ 0) (arrival 0)
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
        R1 * T1
  hQ_current :
    gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) =
      gn21EndpointQiPath (arrival 1) switch21 lowerEndpoint density
        (gn21SwitchProb switch21 switch12) u
  hT_current :
    gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) =
      gn21EndpointTiPath (arrival 1) lowerEndpoint density u
  hW_current :
    gn21ScaledStateEarning (μ 1) (arrival 1)
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
      gn21EndpointWiPath (arrival 1) lowerEndpoint density
        (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) u
  hQ_replacement :
    ∀ ε : ℝ, 0 < ε →
      gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
          (replacement ε) =
        gn21EndpointQiPath (arrival 1) switch21 lowerEndpoint density
          (gn21SwitchProb switch21 switch12) (u + ε)
  hT_replacement :
    ∀ ε : ℝ, 0 < ε →
      gn21ScaledStateTime (μ 1) (arrival 1) (replacement ε) =
        gn21EndpointTiPath (arrival 1) lowerEndpoint density (u + ε)
  hW_replacement :
    ∀ ε : ℝ, 0 < ε →
      gn21ScaledStateEarning (μ 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (replacement ε) =
        gn21EndpointWiPath (arrival 1) lowerEndpoint density
          (ctmcStructuredSurgePrice (m 1) (z 1) switch21 switch12) (u + ε)

/-- A surge bridge data package supplies the state-1 strict aggregate improvement. -/
theorem GN21SurgeIntervalEndpointBridgeData.statewise_strict_aggregate_improvement
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {ρ : Fin 2 → TripPolicy}
    (D : GN21SurgeIntervalEndpointBridgeData μ arrival m z switch12 switch21 ρ) :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 1 τ) 0)
          ((replaceDynamicPolicyState ρ 1 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 (ρ 1) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 τ := by
  exact
    paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_interval_density
      μ arrival m z switch12 switch21 ρ D.replacement D.lowerEndpoint D.u
      D.T1 D.Q1 D.T2 D.Q2 D.R1 D.ratio D.density D.harrival_pos
      D.hdensity_pos D.hQ1_pos D.hden D.hq_int D.hq_meas D.hq_cont
      D.hw_int D.hw_meas D.hw_cont D.ht_int D.ht_meas D.ht_cont D.hQ2
      D.hT2 D.hW2 D.hbounds D.hz D.hmR_pos D.hR1_nonneg D.hT1_nonneg
      D.hswitch21_pos D.hsum D.hu D.hswitch_lt_Q2 D.hgap_nonneg D.Hcur
      D.Hrep D.hQ_other D.hT_other D.hW_other D.hQ_current D.hT_current
      D.hW_current D.hQ_replacement D.hT_replacement D.hW_replacement

/--
Primitive data package for applying the non-surge-state Lemma 10 interval
bridge to a fixed dynamic policy.
-/
structure GN21NonsurgeIntervalEndpointBridgeData
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy) where
  replacement : ℝ → TripPolicy
  lowerEndpoint : ℝ
  u : ℝ
  T2 : ℝ
  Q2 : ℝ
  T1 : ℝ
  Q1 : ℝ
  R2 : ℝ
  ratio : ℝ
  density : ℝ → ℝ
  harrival_pos : 0 < arrival 0
  hdensity_pos : 0 < density u
  hQ2_pos : 0 < Q2
  hden :
    gn21EndpointQiPath (arrival 0) switch12 lowerEndpoint density
        (gn21SwitchProb switch12 switch21) u * T2 +
      Q2 *
        gn21EndpointTiPath (arrival 0) lowerEndpoint density u ≠ 0
  hq_int :
    IntervalIntegrable
      (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) volume
      lowerEndpoint u
  hq_meas :
    StronglyMeasurableAtFilter
      (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) (𝓝 u)
  hq_cont :
    ContinuousAt
      (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) u
  hw_int :
    IntervalIntegrable
      (fun τ => ctmcStructuredSurgePrice R2 (z 0) switch12 switch21 τ *
        density τ) volume lowerEndpoint u
  hw_meas :
    StronglyMeasurableAtFilter
      (fun τ => ctmcStructuredSurgePrice R2 (z 0) switch12 switch21 τ *
        density τ) (𝓝 u)
  hw_cont :
    ContinuousAt
      (fun τ => ctmcStructuredSurgePrice R2 (z 0) switch12 switch21 τ *
        density τ) u
  ht_int :
    IntervalIntegrable (fun τ => τ * density τ) volume lowerEndpoint u
  ht_meas :
    StronglyMeasurableAtFilter (fun τ => τ * density τ) (𝓝 u)
  ht_cont : ContinuousAt (fun τ => τ * density τ) u
  hQ1 :
    gn21EndpointQiPath (arrival 0) switch12 lowerEndpoint density
      (gn21SwitchProb switch12 switch21) u = Q1
  hT1 :
    gn21EndpointTiPath (arrival 0) lowerEndpoint density u = T1
  hW1 :
    gn21EndpointWiPath (arrival 0) lowerEndpoint density
      (ctmcStructuredSurgePrice R2 (z 0) switch12 switch21) u =
        R2 * (T1 - 1) + z 0 * (Q1 - switch12)
  hbounds : lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12
  hz : z 0 = ratio * R2
  hR2_pos : 0 < R2
  hswitch12_pos : 0 < switch12
  hsum : 0 < switch12 + switch21
  hu : 0 < u
  hswitch_lt_Q1 : switch12 < Q1
  hgap_nonneg : 0 ≤ switch12 * T1 - Q1
  hA_pos : 0 < T2 * switch12 + Q2
  Hcur :
    GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
      switch12 switch21 (ρ 0) (ρ 1)
  Hrep :
    ∀ ε : ℝ, 0 < ε →
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (replacement ε) (ρ 1)
  hQ_other :
    gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) = Q2
  hT_other :
    gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) = T2
  hW_other :
    gn21ScaledStateEarning (μ 1) (arrival 1)
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1) =
        R2 * T2
  hQ_current :
    gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) =
      gn21EndpointQiPath (arrival 0) switch12 lowerEndpoint density
        (gn21SwitchProb switch12 switch21) u
  hT_current :
    gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) =
      gn21EndpointTiPath (arrival 0) lowerEndpoint density u
  hW_current :
    gn21ScaledStateEarning (μ 0) (arrival 0)
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0) =
      gn21EndpointWiPath (arrival 0) lowerEndpoint density
        (ctmcStructuredSurgePrice R2 (z 0) switch12 switch21) u
  hQ_replacement :
    ∀ ε : ℝ, 0 < ε →
      gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
          (replacement ε) =
        gn21EndpointQiPath (arrival 0) switch12 lowerEndpoint density
          (gn21SwitchProb switch12 switch21) (u + ε)
  hT_replacement :
    ∀ ε : ℝ, 0 < ε →
      gn21ScaledStateTime (μ 0) (arrival 0) (replacement ε) =
        gn21EndpointTiPath (arrival 0) lowerEndpoint density (u + ε)
  hW_replacement :
    ∀ ε : ℝ, 0 < ε →
      gn21ScaledStateEarning (μ 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (replacement ε) =
        gn21EndpointWiPath (arrival 0) lowerEndpoint density
          (ctmcStructuredSurgePrice R2 (z 0) switch12 switch21) (u + ε)

/-- A non-surge bridge data package supplies the state-0 strict aggregate improvement. -/
theorem GN21NonsurgeIntervalEndpointBridgeData.statewise_strict_aggregate_improvement
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {ρ : Fin 2 → TripPolicy}
    (D : GN21NonsurgeIntervalEndpointBridgeData μ arrival m z switch12 switch21 ρ) :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 0 τ) 0)
          ((replaceDynamicPolicyState ρ 0 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 0 (ρ 0) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 0 τ := by
  exact
    paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_interval_density
      μ arrival m z switch12 switch21 ρ D.replacement D.lowerEndpoint D.u
      D.T2 D.Q2 D.T1 D.Q1 D.R2 D.ratio D.density D.harrival_pos
      D.hdensity_pos D.hQ2_pos D.hden D.hq_int D.hq_meas D.hq_cont
      D.hw_int D.hw_meas D.hw_cont D.ht_int D.ht_meas D.ht_cont D.hQ1
      D.hT1 D.hW1 D.hbounds D.hz D.hR2_pos D.hswitch12_pos D.hsum D.hu
      D.hswitch_lt_Q1 D.hgap_nonneg D.hA_pos D.Hcur D.Hrep D.hQ_other
      D.hT_other D.hW_other D.hQ_current D.hT_current D.hW_current
      D.hQ_replacement D.hT_replacement D.hW_replacement

/--
Combined Lemma 9/10 interval bridge certificate for the CTMC structured price
family.  The remaining analytic task is exactly to build the two bridge-data
objects for each optimal policy/state that is not accept-all.
-/
structure Theorem4Lemma910IntervalBridgeCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ) where
  exists_optimal :
    ∃ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ
  feasible_optimal :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ∀ i : Fin 2, ρ i ⊆ acceptAllPolicy
  nonsurge_bridge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ¬ acceptsAllTrips (ρ 0) →
        GN21NonsurgeIntervalEndpointBridgeData
          μ arrival m z switch12 switch21 ρ
  surge_bridge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ¬ acceptsAllTrips (ρ 1) →
        GN21SurgeIntervalEndpointBridgeData
          μ arrival m z switch12 switch21 ρ

/--
Uniform statewise strict-local aggregate certificate.  Endpoint arguments can
target this interface without duplicating the state-0/state-1 bookkeeping.
-/
structure Theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) where
  exists_optimal :
    ∃ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ
  feasible_optimal :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ →
      ∀ i : Fin 2, ρ i ⊆ acceptAllPolicy
  statewise_strict_aggregate_improvement_unless :
    ∀ ρ : Fin 2 → TripPolicy,
      (hρ :
        dynamicOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ) →
      ∀ i : Fin 2,
        ¬ acceptsAllTrips (ρ i) →
          ∃ τ : TripPolicy,
            GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
              switch12 switch21 (ρ 0) (ρ 1) ∧
            GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
              switch12 switch21 ((replaceDynamicPolicyState ρ i τ) 0)
              ((replaceDynamicPolicyState ρ i τ) 1) ∧
            gn21MeasuredAggregateDynamicStateReward
                μ arrival switch12 switch21 w ρ i (ρ i) <
              gn21MeasuredAggregateDynamicStateReward
                μ arrival switch12 switch21 w ρ i τ

/--
Uniform statewise strict aggregate improvements instantiate the two-field
measured aggregate strict-local certificate used by Theorem 4.
-/
def theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_statewise_strict_improvements
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (C : Theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate
      μ arrival switch12 switch21 w) :
    Theorem4MeasuredAggregateStrictLocalImprovementCertificate
      μ arrival switch12 switch21 w where
  exists_optimal := C.exists_optimal
  feasible_optimal := C.feasible_optimal
  nonsurge_strict_aggregate_improvement_unless := by
    intro ρ hρ hnot
    rcases C.statewise_strict_aggregate_improvement_unless ρ hρ 0 hnot with
      ⟨τ, Hcur, Hrep, hagg⟩
    refine ⟨τ, Hcur, ?_, ?_⟩
    · simpa [replaceDynamicPolicyState] using Hrep
    · simpa [gn21MeasuredAggregateDynamicStateReward,
        replaceDynamicPolicyState] using hagg
  surge_strict_aggregate_improvement_unless := by
    intro ρ hρ hnot
    rcases C.statewise_strict_aggregate_improvement_unless ρ hρ 1 hnot with
      ⟨τ, Hcur, Hrep, hagg⟩
    refine ⟨τ, Hcur, ?_, ?_⟩
    · simpa [replaceDynamicPolicyState] using Hrep
    · simpa [gn21MeasuredAggregateDynamicStateReward,
        replaceDynamicPolicyState] using hagg

/--
Lemma 9/10 interval bridge data instantiate the uniform statewise strict-local
aggregate certificate.
-/
def theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate_of_lemma910_interval_bridges
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (C : Theorem4Lemma910IntervalBridgeCertificate
      μ arrival m z switch12 switch21) :
    Theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate
      μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21) where
  exists_optimal := C.exists_optimal
  feasible_optimal := C.feasible_optimal
  statewise_strict_aggregate_improvement_unless := by
    intro ρ hρ i hnot
    fin_cases i
    · exact
        (C.nonsurge_bridge ρ hρ hnot).statewise_strict_aggregate_improvement
    · exact
        (C.surge_bridge ρ hρ hnot).statewise_strict_aggregate_improvement

/--
Lemma 9/10 interval bridge data instantiate the measured aggregate strict-local
certificate consumed by Theorem 4 and Theorem 3.
-/
def theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_lemma910_interval_bridges
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (C : Theorem4Lemma910IntervalBridgeCertificate
      μ arrival m z switch12 switch21) :
    Theorem4MeasuredAggregateStrictLocalImprovementCertificate
      μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21) :=
  theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_statewise_strict_improvements
    μ arrival switch12 switch21
    (ctmcStructuredDynamicSurgePrice m z switch12 switch21)
    (theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate_of_lemma910_interval_bridges
      μ arrival m z switch12 switch21 C)

/--
State-1 endpoint bridge in its most direct form.  Both upper-endpoint and
finite lower-endpoint Lemma 9 packages can instantiate this interface.
-/
structure GN21SurgeEndpointBridgeData
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy) where
  statewise_strict_aggregate_improvement :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 1 τ) 0)
          ((replaceDynamicPolicyState ρ 1 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 (ρ 1) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 1 τ

/--
State-0 endpoint bridge in its most direct form.  Both upper-endpoint and
finite lower-endpoint Lemma 10 packages can instantiate this interface.
-/
structure GN21NonsurgeEndpointBridgeData
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (ρ : Fin 2 → TripPolicy) where
  statewise_strict_aggregate_improvement :
    ∃ τ : TripPolicy,
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1) ∧
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21
          ((replaceDynamicPolicyState ρ 0 τ) 0)
          ((replaceDynamicPolicyState ρ 0 τ) 1) ∧
      gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 0 (ρ 0) <
        gn21MeasuredAggregateDynamicStateReward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21) ρ 0 τ

/-- Existing upper-endpoint surge bridge data lift to the generalized endpoint interface. -/
def GN21SurgeEndpointBridgeData.of_interval
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {ρ : Fin 2 → TripPolicy}
    (D : GN21SurgeIntervalEndpointBridgeData μ arrival m z switch12 switch21 ρ) :
    GN21SurgeEndpointBridgeData μ arrival m z switch12 switch21 ρ where
  statewise_strict_aggregate_improvement :=
    D.statewise_strict_aggregate_improvement

/-- Existing upper-endpoint non-surge bridge data lift to the generalized endpoint interface. -/
def GN21NonsurgeEndpointBridgeData.of_interval
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {ρ : Fin 2 → TripPolicy}
    (D : GN21NonsurgeIntervalEndpointBridgeData
      μ arrival m z switch12 switch21 ρ) :
    GN21NonsurgeEndpointBridgeData μ arrival m z switch12 switch21 ρ where
  statewise_strict_aggregate_improvement :=
    D.statewise_strict_aggregate_improvement

/--
Generalized Lemma 9/10 endpoint bridge certificate for the CTMC structured
price family.  This is the Theorem 4-facing route after the endpoint
primitive-identification proof has selected whichever endpoint move is
available in a state.
-/
structure Theorem4Lemma910EndpointBridgeCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ) where
  exists_optimal :
    ∃ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ
  feasible_optimal :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ∀ i : Fin 2, ρ i ⊆ acceptAllPolicy
  nonsurge_bridge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ¬ acceptsAllTrips (ρ 0) →
        GN21NonsurgeEndpointBridgeData
          μ arrival m z switch12 switch21 ρ
  surge_bridge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ¬ acceptsAllTrips (ρ 1) →
        GN21SurgeEndpointBridgeData
          μ arrival m z switch12 switch21 ρ

/--
Endpoint-selection certificate organized by the policy-shape cases of
Theorem 4.  Once the structural theorem classifies every optimal policy, the
remaining analytic work is to provide a Lemma 9/10 endpoint bridge for each
non-accept-all shape case.
-/
structure Theorem4ShapeEndpointSelectionCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ) where
  exists_optimal :
    ∃ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ
  feasible_optimal :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ∀ i : Fin 2, ρ i ⊆ acceptAllPolicy
  shape_optimal :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      theorem4NonsurgeShape (ρ 0) ∧ theorem4SurgeShape (ρ 1)
  nonsurge_reject_long_bridge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ∀ t : ℝ,
        rejectsLongTrips t (ρ 0) →
          GN21NonsurgeEndpointBridgeData
            μ arrival m z switch12 switch21 ρ
  nonsurge_accept_middle_bridge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ∀ lo hi : ℝ,
        acceptsMiddleTrips lo hi (ρ 0) →
          GN21NonsurgeEndpointBridgeData
            μ arrival m z switch12 switch21 ρ
  surge_reject_short_bridge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ∀ t : ℝ,
        rejectsShortTrips t (ρ 1) →
          GN21SurgeEndpointBridgeData
            μ arrival m z switch12 switch21 ρ
  surge_reject_middle_bridge :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρ →
      ∀ lo hi : ℝ,
        rejectsMiddleTrips lo hi (ρ 1) →
          GN21SurgeEndpointBridgeData
            μ arrival m z switch12 switch21 ρ

/--
Shape-case endpoint selection is exactly the data needed by the generalized
Lemma 9/10 endpoint bridge certificate.
-/
def Theorem4Lemma910EndpointBridgeCertificate.of_shape_endpoint_selection
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (C : Theorem4ShapeEndpointSelectionCertificate
      μ arrival m z switch12 switch21) :
    Theorem4Lemma910EndpointBridgeCertificate
      μ arrival m z switch12 switch21 where
  exists_optimal := C.exists_optimal
  feasible_optimal := C.feasible_optimal
  nonsurge_bridge := by
    intro ρ hρ hnot
    have hshape := (C.shape_optimal ρ hρ).1
    rcases theorem4NonsurgeShape_cases_of_not_acceptsAll hshape hnot with
      hlong | hmiddle
    · rcases hlong with ⟨t, ht⟩
      exact C.nonsurge_reject_long_bridge ρ hρ t ht
    · rcases hmiddle with ⟨lo, hi, hmid⟩
      exact C.nonsurge_accept_middle_bridge ρ hρ lo hi hmid
  surge_bridge := by
    intro ρ hρ hnot
    have hshape := (C.shape_optimal ρ hρ).2
    rcases theorem4SurgeShape_cases_of_not_acceptsAll hshape hnot with
      hshort | hmiddle
    · rcases hshort with ⟨t, ht⟩
      exact C.surge_reject_short_bridge ρ hρ t ht
    · rcases hmiddle with ⟨lo, hi, hmid⟩
      exact C.surge_reject_middle_bridge ρ hρ lo hi hmid

/-- Upper-endpoint interval certificates are a special case of endpoint bridge certificates. -/
def Theorem4Lemma910EndpointBridgeCertificate.of_interval_bridges
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (C : Theorem4Lemma910IntervalBridgeCertificate
      μ arrival m z switch12 switch21) :
    Theorem4Lemma910EndpointBridgeCertificate
      μ arrival m z switch12 switch21 where
  exists_optimal := C.exists_optimal
  feasible_optimal := C.feasible_optimal
  nonsurge_bridge := by
    intro ρ hρ hnot
    exact GN21NonsurgeEndpointBridgeData.of_interval
      (C.nonsurge_bridge ρ hρ hnot)
  surge_bridge := by
    intro ρ hρ hnot
    exact GN21SurgeEndpointBridgeData.of_interval
      (C.surge_bridge ρ hρ hnot)

/--
General endpoint bridge data instantiate the uniform statewise strict-local
aggregate certificate.
-/
def theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate_of_lemma910_endpoint_bridges
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (C : Theorem4Lemma910EndpointBridgeCertificate
      μ arrival m z switch12 switch21) :
    Theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate
      μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21) where
  exists_optimal := C.exists_optimal
  feasible_optimal := C.feasible_optimal
  statewise_strict_aggregate_improvement_unless := by
    intro ρ hρ i hnot
    fin_cases i
    · exact
        (C.nonsurge_bridge ρ hρ hnot).statewise_strict_aggregate_improvement
    · exact
        (C.surge_bridge ρ hρ hnot).statewise_strict_aggregate_improvement

/--
General endpoint bridge data instantiate the measured aggregate strict-local
certificate consumed by Theorem 4 and Theorem 3.
-/
def theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_lemma910_endpoint_bridges
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (C : Theorem4Lemma910EndpointBridgeCertificate
      μ arrival m z switch12 switch21) :
    Theorem4MeasuredAggregateStrictLocalImprovementCertificate
      μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21) :=
  theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_statewise_strict_improvements
    μ arrival switch12 switch21
    (ctmcStructuredDynamicSurgePrice m z switch12 switch21)
    (theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate_of_lemma910_endpoint_bridges
      μ arrival m z switch12 switch21 C)

/--
Lemma 1 algebra: if subcycle earning and length share the same nonzero cycle
factor, their ratio is the paper's one-state reward rate.
-/
theorem paper_lemma1_state_reward_rate_algebra
    (arrivalRate acceptProb switchRate meanEarning stateCycleTime : ℝ)
    (hfactor :
      (arrivalRate * acceptProb) / (arrivalRate * acceptProb + switchRate) ≠ 0) :
    gn21SubcycleEarning arrivalRate acceptProb switchRate meanEarning /
        gn21SubcycleLength arrivalRate acceptProb switchRate stateCycleTime =
      gn21StateRewardRate meanEarning stateCycleTime := by
  unfold gn21SubcycleEarning gn21SubcycleLength gn21StateRewardRate
  set c : ℝ := (arrivalRate * acceptProb) / (arrivalRate * acceptProb + switchRate)
  have hc : c ≠ 0 := by
    simpa [c] using hfactor
  change c * meanEarning / (c * stateCycleTime) = meanEarning / stateCycleTime
  field_simp [hc]

/--
Lemma 1 measured algebra: the subcycle earning/length ratio for state `i`
reduces to the measured source reward rate `R_i(w_i,σ_i)`.
-/
theorem paper_lemma1_measured_state_reward_rate_algebra
    (μ : Measure TripLength) (arrivalRate switchRate : ℝ)
    (w : PricingFunction) (σ : TripPolicy)
    (hfactor :
      (arrivalRate * singleStateTripMass μ σ) /
          (arrivalRate * singleStateTripMass μ σ + switchRate) ≠ 0) :
    gn21SubcycleEarning arrivalRate (singleStateTripMass μ σ) switchRate
        (gn21StateMeanEarning μ w σ) /
        gn21SubcycleLength arrivalRate (singleStateTripMass μ σ) switchRate
          (gn21StateCycleTime μ arrivalRate σ)
      =
      gn21MeasuredStateRewardRate μ arrivalRate w σ := by
  unfold gn21MeasuredStateRewardRate
  exact paper_lemma1_state_reward_rate_algebra
    arrivalRate (singleStateTripMass μ σ) switchRate
    (gn21StateMeanEarning μ w σ)
    (gn21StateCycleTime μ arrivalRate σ) hfactor

/-- Theorem 3 paper price form `w_i(τ)=m_iτ+z_i q_{i→j}(τ)`. -/
theorem paper_theorem3_structured_price_uses_lemma2_switch_probability
    (m z lambdaIJ lambdaJI τ : ℝ) :
    ctmcStructuredSurgePrice m z lambdaIJ lambdaJI τ =
      m * τ + z * gn21SwitchProb lambdaIJ lambdaJI τ := by
  rfl

/-- Theorem 3 structured price with Lemma 2's closed-form switch probability expanded. -/
theorem paper_theorem3_structured_price_closed_form
    (m z lambdaIJ lambdaJI τ : ℝ) :
    ctmcStructuredSurgePrice m z lambdaIJ lambdaJI τ =
      m * τ + z *
        (lambdaIJ / (lambdaIJ + lambdaJI) *
          (1 - Real.exp (-(lambdaIJ + lambdaJI) * τ))) := by
  rfl

/-- Theorem 3 feasibility-threshold numerator in the source constant `C`. -/
def theorem3FeasibilityNumerator
    (T1 T2 Q1 Q2 switch12 : ℝ) : ℝ :=
  Q2 * (switch12 * T1 - Q1) + Q1 * (T2 * switch12 + Q2)

/-- Theorem 3 feasibility-threshold denominator before the outer `T1` scaling. -/
def theorem3FeasibilityDenominator
    (T1 T2 Q1 Q2 switch12 : ℝ) : ℝ :=
  Q2 * (switch12 * T1 - Q1) + switch12 * (T2 * switch12 + Q2)

/--
Theorem 3 source threshold
`C = 1 - numerator / (T1 * denominator)`.
-/
def theorem3FeasibilityThresholdC
    (T1 T2 Q1 Q2 switch12 : ℝ) : ℝ :=
  1 -
    theorem3FeasibilityNumerator T1 T2 Q1 Q2 switch12 /
      (T1 * theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)

/-- Theorem 3 helper: the term `T2 * lambda + Q2` is nonnegative from nonnegative pieces. -/
theorem paper_theorem3_switch_term_nonneg
    (T2 Q2 switch12 : ℝ)
    (hT2_nonneg : 0 ≤ T2)
    (hQ2_nonneg : 0 ≤ Q2)
    (hswitch_nonneg : 0 ≤ switch12) :
    0 ≤ T2 * switch12 + Q2 := by
  nlinarith [mul_nonneg hT2_nonneg hswitch_nonneg]

/-- Theorem 3 feasibility numerator is positive from the source's positive pieces. -/
theorem paper_theorem3_feasibility_numerator_pos_of_positive_pieces
    (T1 T2 Q1 Q2 switch12 : ℝ)
    (hQ2_pos : 0 < Q2)
    (hgap_pos : 0 < switch12 * T1 - Q1)
    (hQ1_nonneg : 0 ≤ Q1)
    (hsecond_nonneg : 0 ≤ T2 * switch12 + Q2) :
    0 < theorem3FeasibilityNumerator T1 T2 Q1 Q2 switch12 := by
  unfold theorem3FeasibilityNumerator
  exact add_pos_of_pos_of_nonneg
    (mul_pos hQ2_pos hgap_pos)
    (mul_nonneg hQ1_nonneg hsecond_nonneg)

/-- Theorem 3 feasibility denominator is positive from the source's positive pieces. -/
theorem paper_theorem3_feasibility_denominator_pos_of_positive_pieces
    (T1 T2 Q1 Q2 switch12 : ℝ)
    (hQ2_pos : 0 < Q2)
    (hgap_pos : 0 < switch12 * T1 - Q1)
    (hswitch_pos : 0 < switch12)
    (hsecond_nonneg : 0 ≤ T2 * switch12 + Q2) :
    0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12 := by
  unfold theorem3FeasibilityDenominator
  exact add_pos_of_pos_of_nonneg
    (mul_pos hQ2_pos hgap_pos)
    (mul_nonneg (le_of_lt hswitch_pos) hsecond_nonneg)

/-- Theorem 3 scaled feasibility denominator is positive from positive cycle time. -/
theorem paper_theorem3_scaled_denominator_pos_of_positive_pieces
    (T1 T2 Q1 Q2 switch12 : ℝ)
    (hT1_pos : 0 < T1)
    (hQ2_pos : 0 < Q2)
    (hgap_pos : 0 < switch12 * T1 - Q1)
    (hswitch_pos : 0 < switch12)
    (hsecond_nonneg : 0 ≤ T2 * switch12 + Q2) :
    0 < T1 * theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12 := by
  exact mul_pos hT1_pos
    (paper_theorem3_feasibility_denominator_pos_of_positive_pieces
      T1 T2 Q1 Q2 switch12 hQ2_pos hgap_pos hswitch_pos hsecond_nonneg)

/--
Theorem 3 interval check for the feasibility threshold `C`: when the source
numerator is positive and smaller than the scaled denominator, `C ∈ [0,1)`.
-/
theorem paper_theorem3_feasibility_thresholdC_mem_Ico
    (T1 T2 Q1 Q2 switch12 : ℝ)
    (hnum_pos :
      0 < theorem3FeasibilityNumerator T1 T2 Q1 Q2 switch12)
    (hnum_le_scaled_den :
      theorem3FeasibilityNumerator T1 T2 Q1 Q2 switch12 ≤
        T1 * theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)
    (hscaled_den_pos :
      0 <
        T1 * theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12) :
    0 ≤ theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 ∧
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < 1 := by
  unfold theorem3FeasibilityThresholdC
  constructor
  · rw [sub_nonneg]
    rw [div_le_one hscaled_den_pos]
    exact hnum_le_scaled_den
  · rw [sub_lt_self_iff]
    exact div_pos hnum_pos hscaled_den_pos

/--
Theorem 3 interval check with numerator and denominator positivity derived
from primitive source inequalities.
-/
theorem paper_theorem3_feasibility_thresholdC_mem_Ico_of_positive_pieces
    (T1 T2 Q1 Q2 switch12 : ℝ)
    (hT1_pos : 0 < T1)
    (hQ2_pos : 0 < Q2)
    (hgap_pos : 0 < switch12 * T1 - Q1)
    (hQ1_nonneg : 0 ≤ Q1)
    (hswitch_pos : 0 < switch12)
    (hsecond_nonneg : 0 ≤ T2 * switch12 + Q2)
    (hnum_le_scaled_den :
      theorem3FeasibilityNumerator T1 T2 Q1 Q2 switch12 ≤
        T1 * theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12) :
    0 ≤ theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 ∧
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < 1 := by
  exact paper_theorem3_feasibility_thresholdC_mem_Ico
    T1 T2 Q1 Q2 switch12
    (paper_theorem3_feasibility_numerator_pos_of_positive_pieces
      T1 T2 Q1 Q2 switch12 hQ2_pos hgap_pos hQ1_nonneg hsecond_nonneg)
    hnum_le_scaled_den
    (paper_theorem3_scaled_denominator_pos_of_positive_pieces
      T1 T2 Q1 Q2 switch12 hT1_pos hQ2_pos hgap_pos hswitch_pos
      hsecond_nonneg)

/--
Theorem 3 scaled numerator bound: after the source substitution
`gap = lambda*T_1 - Q_1`, the difference between the scaled denominator and
the numerator factors into nonnegative pieces.
-/
theorem paper_theorem3_feasibility_numerator_le_scaled_den_of_nonneg_pieces
    (T1 T2 Q1 Q2 switch12 : ℝ)
    (hgap_nonneg : 0 ≤ switch12 * T1 - Q1)
    (hT1_nonneg : 0 ≤ T1)
    (hT2_nonneg : 0 ≤ T2)
    (hQ2_nonneg : 0 ≤ Q2)
    (hswitch_nonneg : 0 ≤ switch12) :
    theorem3FeasibilityNumerator T1 T2 Q1 Q2 switch12 ≤
      T1 * theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12 := by
  rw [← sub_nonneg]
  have hfactor :
      T1 * theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12 -
          theorem3FeasibilityNumerator T1 T2 Q1 Q2 switch12 =
        (switch12 * T1 - Q1) * (T1 * Q2 + T2 * switch12) := by
    unfold theorem3FeasibilityNumerator theorem3FeasibilityDenominator
    ring
  rw [hfactor]
  exact mul_nonneg hgap_nonneg
    (add_nonneg
      (mul_nonneg hT1_nonneg hQ2_nonneg)
      (mul_nonneg hT2_nonneg hswitch_nonneg))

/--
Theorem 3 non-surge structured-price ratio.  If `rho = R_1/R_2` and
`m_1 = R_2`, the state-1 accounting identity
`R_1*T_1 = R_2*(T_1-1)+z_1*(Q_1-lambda)` gives this value of `z_1/R_2`.
-/
def theorem3NonsurgeZRatio
    (rho T1 Q1 switch12 : ℝ) : ℝ :=
  (rho * T1 - (T1 - 1)) / (Q1 - switch12)

/--
Theorem 3 non-surge accounting identity: with `m_1=R_2` and
`z_1/R_2` chosen by `theorem3NonsurgeZRatio`, the scaled earning identity
matches target ratio `rho = R_1/R_2`.
-/
theorem theorem3NonsurgeZRatio_accounting
    (rho R2 T1 Q1 switch12 : ℝ)
    (hden : Q1 - switch12 ≠ 0) :
    R2 * (T1 - 1) +
        (R2 * theorem3NonsurgeZRatio rho T1 Q1 switch12) *
          (Q1 - switch12) =
      (rho * R2) * T1 := by
  unfold theorem3NonsurgeZRatio
  field_simp [hden]
  ring

/--
Theorem 3 to Lemma 10 bridge: the paper's condition `C < R_1/R_2 < 1`
places the non-surge ratio `z_1/R_2` inside Lemma 10's open interval.
-/
theorem lemma10StructuredBounds_of_theorem3_ratio
    (rho T1 T2 Q1 Q2 switch12 : ℝ)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hrho_lt_one : rho < 1)
    (hT1_pos : 0 < T1)
    (hQ1_sub_switch_pos : 0 < Q1 - switch12)
    (hden_pos :
      0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12) :
    lemma10StructuredBounds
      (theorem3NonsurgeZRatio rho T1 Q1 switch12) T2 Q2 T1 Q1 switch12 := by
  constructor
  · have hscaled_den_pos :
        0 < T1 * theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12 :=
      mul_pos hT1_pos hden_pos
    have hden_pos' :
        0 < Q2 * (switch12 * T1 - Q1) +
          switch12 * (T2 * switch12 + Q2) := by
      simpa [theorem3FeasibilityDenominator] using hden_pos
    have hCmul :=
      mul_lt_mul_of_pos_right hC_lt_rho hscaled_den_pos
    unfold theorem3FeasibilityThresholdC at hCmul
    field_simp [ne_of_gt hscaled_den_pos] at hCmul
    unfold theorem3FeasibilityNumerator theorem3FeasibilityDenominator at hCmul
    unfold lemma10StructuredLower theorem3NonsurgeZRatio
      lemma10StructuredLowerNumerator lemma10StructuredLowerDenominator
    rw [← neg_div]
    rw [div_lt_div_iff₀ hden_pos' hQ1_sub_switch_pos]
    nlinarith
  · unfold lemma10StructuredUpper theorem3NonsurgeZRatio
      lemma10StructuredUpperDenominator
    rw [div_lt_div_iff₀ hQ1_sub_switch_pos hQ1_sub_switch_pos]
    nlinarith [mul_pos hT1_pos (sub_pos.mpr hrho_lt_one)]

/--
Theorem 3 non-surge-side parameters from `C < rho < 1`: the ratio lies in
Lemma 10's interval and the resulting `z_1` satisfies the target scaled-earning
accounting identity.
-/
theorem theorem3NonsurgeParameters_of_theorem3_ratio
    (rho R2 T1 T2 Q1 Q2 switch12 : ℝ)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hrho_lt_one : rho < 1)
    (hT1_pos : 0 < T1)
    (hQ1_sub_switch_pos : 0 < Q1 - switch12)
    (hden_pos :
      0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12) :
    ∃ ratio z : ℝ,
      ratio = theorem3NonsurgeZRatio rho T1 Q1 switch12 ∧
        z = ratio * R2 ∧
        lemma10StructuredBounds ratio T2 Q2 T1 Q1 switch12 ∧
        R2 * (T1 - 1) + z * (Q1 - switch12) = (rho * R2) * T1 := by
  let ratio := theorem3NonsurgeZRatio rho T1 Q1 switch12
  let z := ratio * R2
  refine ⟨ratio, z, rfl, rfl, ?_, ?_⟩
  · exact lemma10StructuredBounds_of_theorem3_ratio
      rho T1 T2 Q1 Q2 switch12 hC_lt_rho hrho_lt_one hT1_pos
      hQ1_sub_switch_pos hden_pos
  · have hden_ne : Q1 - switch12 ≠ 0 := ne_of_gt hQ1_sub_switch_pos
    simpa [ratio, z, mul_comm, mul_left_comm, mul_assoc] using
      theorem3NonsurgeZRatio_accounting rho R2 T1 Q1 switch12 hden_ne

/--
Theorem 3 surge multiplier chosen from a feasible Lemma 9 ratio and a target
surge reward rate.
-/
def theorem3SurgeMultiplierFromRatio
    (R1 R2 T2 Q2 switch21 ratio : ℝ) : ℝ :=
  (R2 * T2 + ratio * R1 * (Q2 - switch21)) /
    ((T2 - 1) + ratio * (Q2 - switch21))

/-- The corresponding surge additive coefficient `z_2`. -/
def theorem3SurgeZFromRatio
    (R1 R2 T2 Q2 switch21 ratio : ℝ) : ℝ :=
  ratio *
    (theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 ratio - R1)

/--
Theorem 3 surge accounting identity: the multiplier and additive coefficient
chosen from a feasible Lemma 9 ratio reproduce the target surge scaled earning.
-/
theorem theorem3SurgeRatio_accounting
    (R1 R2 T2 Q2 switch21 ratio : ℝ)
    (hden :
      (T2 - 1) + ratio * (Q2 - switch21) ≠ 0) :
    theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 ratio * (T2 - 1) +
        theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 ratio *
          (Q2 - switch21) =
      R2 * T2 := by
  unfold theorem3SurgeZFromRatio
  unfold theorem3SurgeMultiplierFromRatio
  field_simp [hden]
  ring

/-- Positivity of the surge construction denominator from nonnegative cycle time and positive ratio. -/
theorem theorem3SurgeRatio_denominator_pos
    (T2 Q2 switch21 ratio : ℝ)
    (hT2_ge_one : 1 ≤ T2)
    (hratio_pos : 0 < ratio)
    (hswitch_lt_Q2 : switch21 < Q2) :
    0 < (T2 - 1) + ratio * (Q2 - switch21) := by
  have hleft : 0 ≤ T2 - 1 := sub_nonneg.mpr hT2_ge_one
  have hright : 0 < ratio * (Q2 - switch21) :=
    mul_pos hratio_pos (sub_pos.mpr hswitch_lt_Q2)
  exact add_pos_of_nonneg_of_pos hleft hright

/--
The surge multiplier chosen from a positive feasible ratio is strictly above
`R1`, assuming positive target rates and `R1 < R2`.
-/
theorem theorem3SurgeMultiplierFromRatio_gt_R1
    (R1 R2 T2 Q2 switch21 ratio : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hT2_nonneg : 0 ≤ T2)
    (hden_pos :
      0 < (T2 - 1) + ratio * (Q2 - switch21)) :
    R1 < theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 ratio := by
  unfold theorem3SurgeMultiplierFromRatio
  rw [lt_div_iff₀ hden_pos]
  have hgap_nonneg : 0 ≤ R2 - R1 := le_of_lt (sub_pos.mpr hR1_lt_R2)
  nlinarith [mul_nonneg hT2_nonneg hgap_nonneg]

/-- The surge additive coefficient is positive when the feasible ratio is positive. -/
theorem theorem3SurgeZFromRatio_pos
    (R1 R2 T2 Q2 switch21 ratio : ℝ)
    (hratio_pos : 0 < ratio)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hT2_nonneg : 0 ≤ T2)
    (hden_pos :
      0 < (T2 - 1) + ratio * (Q2 - switch21)) :
    0 < theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 ratio := by
  unfold theorem3SurgeZFromRatio
  exact mul_pos hratio_pos
    (sub_pos.mpr
      (theorem3SurgeMultiplierFromRatio_gt_R1
        R1 R2 T2 Q2 switch21 ratio hR1_pos hR1_lt_R2 hT2_nonneg
        hden_pos))

/--
Theorem 3 surge-side parameter existence from Lemma 9's final-sign feasibility
certificate. This packages the positive feasible ratio together with the
constructed `m_2,z_2` and their target scaled-earning identity.
-/
theorem theorem3SurgeParameters_exist_of_lemma9_final_signs
    (R1 R2 T1 Q1 Tbar2 Qbar2 switch21 : ℝ)
    (hden_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 Tbar2 Qbar2 switch21)
    (hden_upper :
      0 < lemma9StructuredUpperDenominator Q1 Qbar2 switch21)
    (hleft_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 Tbar2 Qbar2 switch21 *
          lemma9StructuredUpperDenominator Q1 Qbar2 switch21 ≤ 0)
    (hright_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Qbar2 *
        lemma9StructuredLowerDenominator T1 Q1 Tbar2 Qbar2 switch21)
    (hupper_pos :
      0 < lemma9StructuredUpper T1 Q1 Tbar2 Qbar2 switch21)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hTbar2_ge_one : 1 ≤ Tbar2)
    (hswitch_lt_Qbar2 : switch21 < Qbar2) :
    ∃ ratio m z : ℝ,
      0 < ratio ∧
        lemma9StructuredBounds ratio T1 Q1 Tbar2 Qbar2 switch21 ∧
        m = theorem3SurgeMultiplierFromRatio R1 R2 Tbar2 Qbar2 switch21 ratio ∧
        z = theorem3SurgeZFromRatio R1 R2 Tbar2 Qbar2 switch21 ratio ∧
        R1 < m ∧
        0 < z ∧
        m * (Tbar2 - 1) + z * (Qbar2 - switch21) = R2 * Tbar2 := by
  rcases paper_lemma9_structured_bounds_feasible_positive_of_final_signs
      T1 Q1 Tbar2 Qbar2 switch21 hden_lower hden_upper hleft_nonpos
      hright_pos hupper_pos with ⟨ratio, hratio_pos, hbounds⟩
  let m := theorem3SurgeMultiplierFromRatio R1 R2 Tbar2 Qbar2 switch21 ratio
  let z := theorem3SurgeZFromRatio R1 R2 Tbar2 Qbar2 switch21 ratio
  have hden_pos :
      0 < (Tbar2 - 1) + ratio * (Qbar2 - switch21) :=
    theorem3SurgeRatio_denominator_pos Tbar2 Qbar2 switch21 ratio
      hTbar2_ge_one hratio_pos hswitch_lt_Qbar2
  have hTbar2_nonneg : 0 ≤ Tbar2 := le_trans zero_le_one hTbar2_ge_one
  refine ⟨ratio, m, z, hratio_pos, hbounds, rfl, rfl, ?_, ?_, ?_⟩
  · exact theorem3SurgeMultiplierFromRatio_gt_R1
      R1 R2 Tbar2 Qbar2 switch21 ratio hR1_pos hR1_lt_R2 hTbar2_nonneg
      hden_pos
  · exact theorem3SurgeZFromRatio_pos
      R1 R2 Tbar2 Qbar2 switch21 ratio hratio_pos hR1_pos hR1_lt_R2
      hTbar2_nonneg hden_pos
  · exact theorem3SurgeRatio_accounting
      R1 R2 Tbar2 Qbar2 switch21 ratio (ne_of_gt hden_pos)

/--
Theorem 3 structured-parameter algebra assembly.  This combines the non-surge
`C < rho < 1` construction with the surge Lemma 9 positive-ratio construction
into two-state `m,z` arrays with the source sign constraints and target
scaled-earning identities.
-/
theorem theorem3StructuredParameters_exist_of_ratio_and_lemma9_final_signs
    (rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hrho_lt_one : rho < 1)
    (hT1_pos : 0 < T1)
    (hQ1_sub_switch12_pos : 0 < Q1 - switch12)
    (hden_theorem3_pos :
      0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)
    (hlemma9_den_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_den_upper :
      0 < lemma9StructuredUpperDenominator Q1 Q2 switch21)
    (hlemma9_left_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 T2 Q2 switch21 *
          lemma9StructuredUpperDenominator Q1 Q2 switch21 ≤ 0)
    (hlemma9_right_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Q2 *
        lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_upper_pos :
      0 < lemma9StructuredUpper T1 Q1 T2 Q2 switch21)
    (hT2_ge_one : 1 ≤ T2)
    (hswitch21_lt_Q2 : switch21 < Q2) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        ∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2 := by
  rcases theorem3NonsurgeParameters_of_theorem3_ratio
      rho R2 T1 T2 Q1 Q2 switch12 hC_lt_rho hrho_lt_one hT1_pos
      hQ1_sub_switch12_pos hden_theorem3_pos with
    ⟨nonsurgeRatio, zN, hnratio_eq, hzN_eq, hnBounds, hnAccount⟩
  rcases theorem3SurgeParameters_exist_of_lemma9_final_signs
      R1 R2 T1 Q1 T2 Q2 switch21 hlemma9_den_lower hlemma9_den_upper
      hlemma9_left_nonpos hlemma9_right_pos hlemma9_upper_pos hR1_pos
      hR1_lt_R2 hT2_ge_one hswitch21_lt_Q2 with
    ⟨surgeRatio, mS, zS, hsurgeRatio_pos, hsBounds, hmS_eq, hzS_eq,
      hmS_gt, hzS_pos, hsAccount⟩
  let m : Fin 2 → ℝ := fun i => if i = 0 then R2 else mS
  let z : Fin 2 → ℝ := fun i => if i = 0 then zN else zS
  have hm0_eq : m 0 = R2 := by simp [m]
  have hm1_eq : m 1 = mS := by simp [m]
  have hz0_eq : z 0 = zN := by simp [z]
  have hz1_eq : z 1 = zS := by simp [z]
  refine ⟨m, z, ?_, nonsurgeRatio, surgeRatio, hnBounds, hsBounds,
    hm0_eq, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [hm0_eq]
      exact le_of_lt hR2_pos
    · constructor
      · rw [hm1_eq]
        exact le_trans (le_of_lt hR1_pos) (le_of_lt hmS_gt)
      · rw [hz1_eq]
        exact le_of_lt hzS_pos
  · rw [hz0_eq]
    exact hzN_eq
  · rw [hm1_eq]
    exact hmS_eq
  · rw [hz1_eq]
    exact hzS_eq
  · rw [hm0_eq, hz0_eq, hR1_eq]
    exact hnAccount
  · rw [hm1_eq, hz1_eq]
    exact hsAccount

/--
Theorem 3 accept-all measured bridge: for the measured accept-all primitives,
the CTMC and positive-trip facts discharge the positivity side conditions
needed for the feasibility-threshold interval check.
-/
theorem paper_theorem3_feasibility_thresholdC_mem_Ico_acceptAll_of_measured_primitives
    (μ1 μ2 : Measure TripLength)
    (arrival1 arrival2 switch12 switch21 : ℝ)
    (harrival1_pos : 0 < arrival1)
    (harrival2_nonneg : 0 ≤ arrival2)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ1)
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy μ1)
    (hmeasure1_pos : 0 < μ1 acceptAllPolicy)
    (hnum_le_scaled_den :
      theorem3FeasibilityNumerator
          (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
          (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
          (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
          (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
          switch12 ≤
        gn21ScaledStateTime μ1 arrival1 acceptAllPolicy *
          theorem3FeasibilityDenominator
            (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
            (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
            (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
            (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
            switch12) :
    0 ≤ theorem3FeasibilityThresholdC
        (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
        (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
        (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
        (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
        switch12 ∧
      theorem3FeasibilityThresholdC
        (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
        (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
        (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
        (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
        switch12 < 1 := by
  have hsum12 : 0 < switch12 + switch21 := by
    linarith
  have hsum21 : 0 < switch21 + switch12 := by
    linarith
  have hT1_pos :
      0 < gn21ScaledStateTime μ1 arrival1 acceptAllPolicy :=
    gn21ScaledStateTime_pos_of_nonneg μ1 arrival1 acceptAllPolicy
      (le_of_lt harrival1_pos) measurableSet_acceptAllPolicy (fun _ hτ => hτ)
  have hT2_nonneg :
      0 ≤ gn21ScaledStateTime μ2 arrival2 acceptAllPolicy := by
    exact le_of_lt
      (gn21ScaledStateTime_pos_of_nonneg μ2 arrival2 acceptAllPolicy
        harrival2_nonneg measurableSet_acceptAllPolicy (fun _ hτ => hτ))
  have hQ2_pos :
      0 <
        gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy :=
    gn21ExitWeightIntegral_pos_of_switch_pos μ2 arrival2 switch21 switch12
      acceptAllPolicy harrival2_nonneg hswitch21_pos hsum21
      measurableSet_acceptAllPolicy (fun _ hτ => hτ)
  have hQ1_nonneg :
      0 ≤
        gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy := by
    exact le_of_lt
      (gn21ExitWeightIntegral_pos_of_switch_pos μ1 arrival1 switch12 switch21
        acceptAllPolicy (le_of_lt harrival1_pos) hswitch12_pos hsum12
        measurableSet_acceptAllPolicy (fun _ hτ => hτ))
  have hgap_pos :
      0 <
        switch12 * gn21ScaledStateTime μ1 arrival1 acceptAllPolicy -
          gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy :=
    paper_remark4_scaled_time_minus_exit_weight_pos_of_positive_measure
      μ1 arrival1 switch12 switch21 acceptAllPolicy harrival1_pos hswitch12_pos
      hsum12 measurableSet_acceptAllPolicy (fun _ hτ => hτ)
      htime1_integrable hq1_integrable hmeasure1_pos
  have hsecond_nonneg :
      0 ≤
        gn21ScaledStateTime μ2 arrival2 acceptAllPolicy * switch12 +
          gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy :=
    paper_theorem3_switch_term_nonneg
      (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
      (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
      switch12 hT2_nonneg (le_of_lt hQ2_pos) (le_of_lt hswitch12_pos)
  exact paper_theorem3_feasibility_thresholdC_mem_Ico_of_positive_pieces
    (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
    (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
    (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
    (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
    switch12 hT1_pos hQ2_pos hgap_pos hQ1_nonneg hswitch12_pos
    hsecond_nonneg hnum_le_scaled_den

/--
Theorem 3 accept-all measured bridge with the scaled numerator bound discharged
by the source factorization.
-/
theorem paper_theorem3_feasibility_thresholdC_mem_Ico_acceptAll_of_measured_primitives_closed
    (μ1 μ2 : Measure TripLength)
    (arrival1 arrival2 switch12 switch21 : ℝ)
    (harrival1_pos : 0 < arrival1)
    (harrival2_nonneg : 0 ≤ arrival2)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ1)
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy μ1)
    (hmeasure1_pos : 0 < μ1 acceptAllPolicy) :
    0 ≤ theorem3FeasibilityThresholdC
        (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
        (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
        (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
        (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
        switch12 ∧
      theorem3FeasibilityThresholdC
        (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
        (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
        (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
        (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
        switch12 < 1 := by
  have hsum12 : 0 < switch12 + switch21 := by
    linarith
  have hsum21 : 0 < switch21 + switch12 := by
    linarith
  have hT1_nonneg :
      0 ≤ gn21ScaledStateTime μ1 arrival1 acceptAllPolicy := by
    exact le_trans zero_le_one
      (gn21ScaledStateTime_ge_one_of_nonneg μ1 arrival1 acceptAllPolicy
        (le_of_lt harrival1_pos) measurableSet_acceptAllPolicy (fun _ hτ => hτ))
  have hT2_nonneg :
      0 ≤ gn21ScaledStateTime μ2 arrival2 acceptAllPolicy := by
    exact le_trans zero_le_one
      (gn21ScaledStateTime_ge_one_of_nonneg μ2 arrival2 acceptAllPolicy
        harrival2_nonneg measurableSet_acceptAllPolicy (fun _ hτ => hτ))
  have hQ2_nonneg :
      0 ≤
        gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy := by
    exact le_of_lt
      (gn21ExitWeightIntegral_pos_of_switch_pos μ2 arrival2 switch21 switch12
        acceptAllPolicy harrival2_nonneg hswitch21_pos hsum21
        measurableSet_acceptAllPolicy (fun _ hτ => hτ))
  have hgap_nonneg :
      0 ≤
        switch12 * gn21ScaledStateTime μ1 arrival1 acceptAllPolicy -
          gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy := by
    exact le_of_lt
      (paper_remark4_scaled_time_minus_exit_weight_pos_of_positive_measure
        μ1 arrival1 switch12 switch21 acceptAllPolicy harrival1_pos
        hswitch12_pos hsum12 measurableSet_acceptAllPolicy (fun _ hτ => hτ)
        htime1_integrable hq1_integrable hmeasure1_pos)
  have hnum_le_scaled_den :
      theorem3FeasibilityNumerator
          (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
          (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
          (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
          (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
          switch12 ≤
        gn21ScaledStateTime μ1 arrival1 acceptAllPolicy *
          theorem3FeasibilityDenominator
            (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
            (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
            (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
            (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
            switch12 :=
    paper_theorem3_feasibility_numerator_le_scaled_den_of_nonneg_pieces
      (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
      (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
      (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
      (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
      switch12 hgap_nonneg hT1_nonneg hT2_nonneg hQ2_nonneg
      (le_of_lt hswitch12_pos)
  exact paper_theorem3_feasibility_thresholdC_mem_Ico_acceptAll_of_measured_primitives
    μ1 μ2 arrival1 arrival2 switch12 switch21 harrival1_pos harrival2_nonneg
    hswitch12_pos hswitch21_pos htime1_integrable hq1_integrable
    hmeasure1_pos hnum_le_scaled_den

/--
Measured Theorem 3 to Lemma 10 bridge: for accept-all primitives, the paper's
ratio condition `C < rho < 1` supplies the non-surge structured ratio bounds.
-/
theorem lemma10StructuredBounds_acceptAll_of_theorem3_ratio_measured
    (rho : ℝ)
    (μ1 μ2 : Measure TripLength)
    (arrival1 arrival2 switch12 switch21 : ℝ)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
          (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
          (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
          (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival1)
    (harrival2_nonneg : 0 ≤ arrival2)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy μ1)
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy μ1)
    (hmeasure1_pos : 0 < μ1 acceptAllPolicy) :
    lemma10StructuredBounds
      (theorem3NonsurgeZRatio rho
        (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
        (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
        switch12)
      (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
      (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
      (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
      (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
      switch12 := by
  have hsum12 : 0 < switch12 + switch21 := by
    linarith
  have hsum21 : 0 < switch21 + switch12 := by
    linarith
  have hT1_pos :
      0 < gn21ScaledStateTime μ1 arrival1 acceptAllPolicy :=
    gn21ScaledStateTime_pos_of_nonneg μ1 arrival1 acceptAllPolicy
      (le_of_lt harrival1_pos) measurableSet_acceptAllPolicy (fun _ hτ => hτ)
  have hT2_nonneg :
      0 ≤ gn21ScaledStateTime μ2 arrival2 acceptAllPolicy := by
    exact le_of_lt
      (gn21ScaledStateTime_pos_of_nonneg μ2 arrival2 acceptAllPolicy
        harrival2_nonneg measurableSet_acceptAllPolicy (fun _ hτ => hτ))
  have hQ2_pos :
      0 <
        gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy :=
    gn21ExitWeightIntegral_pos_of_switch_pos μ2 arrival2 switch21 switch12
      acceptAllPolicy harrival2_nonneg hswitch21_pos hsum21
      measurableSet_acceptAllPolicy (fun _ hτ => hτ)
  have hQ1_sub_switch_pos :
      0 <
        gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy -
          switch12 :=
    sub_pos.mpr
      (paper_remark4_exit_weight_gt_switch_of_positive_measure
        μ1 arrival1 switch12 switch21 acceptAllPolicy harrival1_pos
        hswitch12_pos hsum12 measurableSet_acceptAllPolicy (fun _ hτ => hτ)
        hq1_integrable hmeasure1_pos)
  have hgap_pos :
      0 <
        switch12 * gn21ScaledStateTime μ1 arrival1 acceptAllPolicy -
          gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy :=
    paper_remark4_scaled_time_minus_exit_weight_pos_of_positive_measure
      μ1 arrival1 switch12 switch21 acceptAllPolicy harrival1_pos hswitch12_pos
      hsum12 measurableSet_acceptAllPolicy (fun _ hτ => hτ)
      htime1_integrable hq1_integrable hmeasure1_pos
  have hsecond_nonneg :
      0 ≤
        gn21ScaledStateTime μ2 arrival2 acceptAllPolicy * switch12 +
          gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy :=
    paper_theorem3_switch_term_nonneg
      (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
      (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
      switch12 hT2_nonneg (le_of_lt hQ2_pos) (le_of_lt hswitch12_pos)
  have hden_pos :
      0 <
        theorem3FeasibilityDenominator
          (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
          (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
          (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
          (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
          switch12 :=
    paper_theorem3_feasibility_denominator_pos_of_positive_pieces
      (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
      (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
      (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
      (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
      switch12 hQ2_pos hgap_pos hswitch12_pos hsecond_nonneg
  exact lemma10StructuredBounds_of_theorem3_ratio
    rho
    (gn21ScaledStateTime μ1 arrival1 acceptAllPolicy)
    (gn21ScaledStateTime μ2 arrival2 acceptAllPolicy)
    (gn21ExitWeightIntegral μ1 arrival1 switch12 switch21 acceptAllPolicy)
    (gn21ExitWeightIntegral μ2 arrival2 switch21 switch12 acceptAllPolicy)
    switch12 hC_lt_rho hrho_lt_one hT1_pos hQ1_sub_switch_pos hden_pos

/--
Certificate for Theorem 2's multiplicative-pricing non-IC conclusion.  The
source proves this by continuous interval-shape and derivative arguments; this
wrapper records the endpoint needed by downstream claims.
-/
structure MultiplicativeNotICCertificate (R : DynamicReward) where
  deviation : Fin 2 → TripPolicy
  deviation_profitable : dynamicProfitableDeviation R deviation

/-- Theorem 2 endpoint: a profitable deviation means multiplicative pricing is not IC. -/
theorem paper_theorem2_multiplicative_not_ic_of_witness
    (R : DynamicReward) (C : MultiplicativeNotICCertificate R) :
    ¬ dynamicIncentiveCompatible R := by
  exact not_dynamicIncentiveCompatible_of_profitableDeviation R C.deviation
    C.deviation_profitable

/--
Certificate for Theorem 2's policy-shape conclusion in the multiplicative
case: non-surge rejects long trips and surge rejects short trips.
-/
structure MultiplicativePolicyShapeCertificate (R : DynamicReward) where
  policy : Fin 2 → TripPolicy
  optimal : dynamicOptimal R policy
  nonsurge_rejects_long : ∃ t : ℝ, rejectsLongTrips t (policy 0)
  surge_rejects_short : ∃ t : ℝ, rejectsShortTrips t (policy 1)

/-- Theorem 2 policy-shape endpoint for the multiplicative case. -/
theorem paper_theorem2_multiplicative_policy_shape_of_certificate
    (R : DynamicReward) (C : MultiplicativePolicyShapeCertificate R) :
    dynamicOptimal R C.policy ∧
      (∃ t : ℝ, rejectsLongTrips t (C.policy 0)) ∧
      (∃ t : ℝ, rejectsShortTrips t (C.policy 1)) := by
  exact ⟨C.optimal, C.nonsurge_rejects_long, C.surge_rejects_short⟩

/--
Certificate for Theorem 3: structured prices exist and make accept-all uniquely
optimal.  The continuous construction of `m_i,z_i` and the CTMC integral
inequalities remain source-specific.
-/
structure StructuredPricingICCertificate (R : DynamicReward)
    (w : Fin 2 → PricingFunction) where
  m : Fin 2 → ℝ
  z : Fin 2 → ℝ
  q : Fin 2 → TripLength → ℝ
  nonsurge_multiplier_nonneg : 0 ≤ m 0
  surge_multiplier_nonneg : 0 ≤ m 1
  surge_z_nonneg : 0 ≤ z 1
  price_form : ∀ i τ, w i τ = structuredSurgePrice (m i) (z i) (q i) τ
  accept_all_unique_optimal :
    dynamicOptimal R acceptAllDynamicPolicy ∧
      ∀ σ : Fin 2 → TripPolicy,
        dynamicOptimal R σ → σ = acceptAllDynamicPolicy

/--
Concrete Theorem 3 certificate constructor for the CTMC structured price
family.  The remaining substantive input is the accept-all unique-optimality
claim delivered by Theorem 4 plus Lemmas 9-10.
-/
def structuredPricingICCertificate_of_ctmc_structured_prices
    (R : DynamicReward)
    (m z : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (hm0_nonneg : 0 ≤ m 0)
    (hm1_nonneg : 0 ≤ m 1)
    (hz1_nonneg : 0 ≤ z 1)
    (haccept_all_unique_optimal :
      dynamicOptimal R acceptAllDynamicPolicy ∧
        ∀ σ : Fin 2 → TripPolicy,
          dynamicOptimal R σ → σ = acceptAllDynamicPolicy) :
    StructuredPricingICCertificate R
      (ctmcStructuredDynamicSurgePrice m z switch12 switch21) where
  m := m
  z := z
  q := ctmcDynamicSwitchProb switch12 switch21
  nonsurge_multiplier_nonneg := hm0_nonneg
  surge_multiplier_nonneg := hm1_nonneg
  surge_z_nonneg := hz1_nonneg
  price_form := by
    intro i τ
    rfl
  accept_all_unique_optimal := haccept_all_unique_optimal

/-- Theorem 3 endpoint: structured prices make accept-all dynamically IC. -/
theorem paper_theorem3_structured_prices_ic_of_certificate
    (R : DynamicReward) (w : Fin 2 → PricingFunction)
    (C : StructuredPricingICCertificate R w) :
    dynamicIncentiveCompatible R ∧
      ∃ m z : Fin 2 → ℝ, ∃ q : Fin 2 → TripLength → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
          (∀ i τ, w i τ = structuredSurgePrice (m i) (z i) (q i) τ) := by
  exact ⟨C.accept_all_unique_optimal.1, C.m, C.z, C.q,
    ⟨C.nonsurge_multiplier_nonneg, C.surge_multiplier_nonneg, C.surge_z_nonneg⟩,
    C.price_form⟩

/--
Theorem 3 endpoint specialized to the concrete two-state CTMC structured price
family.
-/
theorem paper_theorem3_ctmc_structured_prices_ic_of_accept_all_unique_optimal
    (R : DynamicReward)
    (m z : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (hm0_nonneg : 0 ≤ m 0)
    (hm1_nonneg : 0 ≤ m 1)
    (hz1_nonneg : 0 ≤ z 1)
    (haccept_all_unique_optimal :
      dynamicOptimal R acceptAllDynamicPolicy ∧
        ∀ σ : Fin 2 → TripPolicy,
          dynamicOptimal R σ → σ = acceptAllDynamicPolicy) :
    dynamicIncentiveCompatible R ∧
      ∃ m' z' : Fin 2 → ℝ, ∃ q : Fin 2 → TripLength → ℝ,
        (0 ≤ m' 0 ∧ 0 ≤ m' 1 ∧ 0 ≤ z' 1) ∧
          (∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m' i) (z' i) (q i) τ) := by
  exact paper_theorem3_structured_prices_ic_of_certificate R
    (ctmcStructuredDynamicSurgePrice m z switch12 switch21)
    (structuredPricingICCertificate_of_ctmc_structured_prices
      R m z switch12 switch21 hm0_nonneg hm1_nonneg hz1_nonneg
      haccept_all_unique_optimal)

/--
Theorem 3 endpoint from the statewise accept-all conclusion produced by the
continuous structural proof: once every optimal policy is feasible and accepts
all positive trips in both states, the CTMC structured price family is IC.
-/
theorem paper_theorem3_ctmc_structured_prices_ic_of_statewise_accept_all_optima
    (R : DynamicReward)
    (m z : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (hm0_nonneg : 0 ≤ m 0)
    (hm1_nonneg : 0 ≤ m 1)
    (hz1_nonneg : 0 ≤ z 1)
    (haccept_opt : dynamicOptimal R acceptAllDynamicPolicy)
    (hfeasible :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicOptimal R σ → ∀ i : Fin 2, σ i ⊆ acceptAllPolicy)
    (hall :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicOptimal R σ → ∀ i : Fin 2, acceptsAllTrips (σ i)) :
    dynamicIncentiveCompatible R ∧
      ∃ m' z' : Fin 2 → ℝ, ∃ q : Fin 2 → TripLength → ℝ,
        (0 ≤ m' 0 ∧ 0 ≤ m' 1 ∧ 0 ≤ z' 1) ∧
          (∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m' i) (z' i) (q i) τ) := by
  exact paper_theorem3_ctmc_structured_prices_ic_of_accept_all_unique_optimal
    R m z switch12 switch21 hm0_nonneg hm1_nonneg hz1_nonneg
    (acceptAllDynamic_unique_optimal_of_statewise_accept_all_optima
      R haccept_opt hfeasible hall)

/--
Theorem 3 endpoint from the positive-form Theorem 4 derivation produced by
the Lemma 9/10 derivative signs: positive Lemma 5 forms in both states force
accept-all, and hence the CTMC structured price family is dynamically IC.
-/
theorem paper_theorem3_ctmc_structured_prices_ic_of_theorem4_accept_all_derivation
    (R : DynamicReward)
    (m z : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (hm0_nonneg : 0 ≤ m 0)
    (hm1_nonneg : 0 ≤ m 1)
    (hz1_nonneg : 0 ≤ z 1)
    (C : Theorem4AcceptAllDerivationCertificate R) :
    dynamicIncentiveCompatible R ∧
      ∃ m' z' : Fin 2 → ℝ, ∃ q : Fin 2 → TripLength → ℝ,
        (0 ≤ m' 0 ∧ 0 ≤ m' 1 ∧ 0 ≤ z' 1) ∧
          (∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m' i) (z' i) (q i) τ) := by
  exact paper_theorem3_ctmc_structured_prices_ic_of_accept_all_unique_optimal
    R m z switch12 switch21 hm0_nonneg hm1_nonneg hz1_nonneg
    (paper_theorem4_accept_all_unique_optimal_of_positive_lemma5_forms R C)

/--
Theorem 3 endpoint from statewise positive Lemma 5 replacement certificates.
This is the direct bridge expected after Lemmas 9-10 provide positive
derivative shapes for the non-surge and surge local continuation problems.
-/
theorem paper_theorem3_ctmc_structured_prices_ic_of_positive_replacement_derivation
    (R : DynamicReward)
    (m z : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (hm0_nonneg : 0 ≤ m 0)
    (hm1_nonneg : 0 ≤ m 1)
    (hz1_nonneg : 0 ≤ z 1)
    (C : Theorem4PositiveReplacementDerivationCertificate R) :
    dynamicIncentiveCompatible R ∧
      ∃ m' z' : Fin 2 → ℝ, ∃ q : Fin 2 → TripLength → ℝ,
        (0 ≤ m' 0 ∧ 0 ≤ m' 1 ∧ 0 ≤ z' 1) ∧
          (∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m' i) (z' i) (q i) τ) := by
  exact paper_theorem3_ctmc_structured_prices_ic_of_theorem4_accept_all_derivation
    R m z switch12 switch21 hm0_nonneg hm1_nonneg hz1_nonneg
    (theorem4AcceptAllDerivationCertificate_of_positive_replacement R C)

/--
Theorem 3 endpoint from strict local improvements that rule out non-accept-all
optima. This is the closest logical target for endpoint-derivative arguments
that produce a better nearby policy rather than a direct accept-all comparison.
-/
theorem paper_theorem3_ctmc_structured_prices_ic_of_strict_local_improvements
    (R : DynamicReward)
    (m z : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (hm0_nonneg : 0 ≤ m 0)
    (hm1_nonneg : 0 ≤ m 1)
    (hz1_nonneg : 0 ≤ z 1)
    (C : Theorem4StrictLocalImprovementCertificate R) :
    dynamicIncentiveCompatible R ∧
      ∃ m' z' : Fin 2 → ℝ, ∃ q : Fin 2 → TripLength → ℝ,
        (0 ≤ m' 0 ∧ 0 ≤ m' 1 ∧ 0 ≤ z' 1) ∧
          (∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m' i) (z' i) (q i) τ) := by
  exact paper_theorem3_ctmc_structured_prices_ic_of_accept_all_unique_optimal
    R m z switch12 switch21 hm0_nonneg hm1_nonneg hz1_nonneg
    (paper_theorem4_accept_all_unique_optimal_of_strict_local_improvements R C)

/--
Integrated Theorem 3 endpoint: the source ratio and Lemma 9 final-sign
conditions construct the CTMC structured-price parameters, and the positive
replacement derivation supplies dynamic IC for that constructed price family.
-/
theorem paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_positive_replacement
    (R : DynamicReward)
    (rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hrho_lt_one : rho < 1)
    (hT1_pos : 0 < T1)
    (hQ1_sub_switch12_pos : 0 < Q1 - switch12)
    (hden_theorem3_pos :
      0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)
    (hlemma9_den_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_den_upper :
      0 < lemma9StructuredUpperDenominator Q1 Q2 switch21)
    (hlemma9_left_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 T2 Q2 switch21 *
          lemma9StructuredUpperDenominator Q1 Q2 switch21 ≤ 0)
    (hlemma9_right_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Q2 *
        lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_upper_pos :
      0 < lemma9StructuredUpper T1 Q1 T2 Q2 switch21)
    (hT2_ge_one : 1 ≤ T2)
    (hswitch21_lt_Q2 : switch21 < Q2)
    (C : Theorem4PositiveReplacementDerivationCertificate R) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        dynamicIncentiveCompatible R ∧
        (∃ q : Fin 2 → TripLength → ℝ,
          ∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m i) (z i) (q i) τ) ∧
        ∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2 := by
  rcases theorem3StructuredParameters_exist_of_ratio_and_lemma9_final_signs
      rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 hR1_eq hR1_pos
      hR1_lt_R2 hR2_pos hC_lt_rho hrho_lt_one hT1_pos
      hQ1_sub_switch12_pos hden_theorem3_pos hlemma9_den_lower
      hlemma9_den_upper hlemma9_left_nonpos hlemma9_right_pos
      hlemma9_upper_pos hT2_ge_one hswitch21_lt_Q2 with
    ⟨m, z, hnonneg, nonsurgeRatio, surgeRatio, hnBounds, hsBounds,
      hm0_eq, hz0_eq, hm1_eq, hz1_eq, hnAccount, hsAccount⟩
  have hIC : dynamicIncentiveCompatible R :=
    (paper_theorem3_ctmc_structured_prices_ic_of_positive_replacement_derivation
      R m z switch12 switch21 hnonneg.1 hnonneg.2.1 hnonneg.2.2 C).1
  refine ⟨m, z, hnonneg, hIC, ?_, nonsurgeRatio, surgeRatio,
    hnBounds, hsBounds, hm0_eq, hz0_eq, hm1_eq, hz1_eq, hnAccount,
    hsAccount⟩
  exact ⟨ctmcDynamicSwitchProb switch12 switch21, by intro i τ; rfl⟩

/--
Integrated Theorem 3 endpoint from strict local improvements.  This is useful
when Lemma 6/9/10 produce a better nearby policy for every non-accept-all
optimum, rather than a direct accept-all weak-dominance certificate.
-/
theorem paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_strict_local_improvements
    (R : DynamicReward)
    (rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hrho_lt_one : rho < 1)
    (hT1_pos : 0 < T1)
    (hQ1_sub_switch12_pos : 0 < Q1 - switch12)
    (hden_theorem3_pos :
      0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)
    (hlemma9_den_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_den_upper :
      0 < lemma9StructuredUpperDenominator Q1 Q2 switch21)
    (hlemma9_left_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 T2 Q2 switch21 *
          lemma9StructuredUpperDenominator Q1 Q2 switch21 ≤ 0)
    (hlemma9_right_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Q2 *
        lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_upper_pos :
      0 < lemma9StructuredUpper T1 Q1 T2 Q2 switch21)
    (hT2_ge_one : 1 ≤ T2)
    (hswitch21_lt_Q2 : switch21 < Q2)
    (C : Theorem4StrictLocalImprovementCertificate R) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        dynamicIncentiveCompatible R ∧
        (∃ q : Fin 2 → TripLength → ℝ,
          ∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m i) (z i) (q i) τ) ∧
        ∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2 := by
  rcases theorem3StructuredParameters_exist_of_ratio_and_lemma9_final_signs
      rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 hR1_eq hR1_pos
      hR1_lt_R2 hR2_pos hC_lt_rho hrho_lt_one hT1_pos
      hQ1_sub_switch12_pos hden_theorem3_pos hlemma9_den_lower
      hlemma9_den_upper hlemma9_left_nonpos hlemma9_right_pos
      hlemma9_upper_pos hT2_ge_one hswitch21_lt_Q2 with
    ⟨m, z, hnonneg, nonsurgeRatio, surgeRatio, hnBounds, hsBounds,
      hm0_eq, hz0_eq, hm1_eq, hz1_eq, hnAccount, hsAccount⟩
  have hIC : dynamicIncentiveCompatible R :=
    (paper_theorem3_ctmc_structured_prices_ic_of_strict_local_improvements
      R m z switch12 switch21 hnonneg.1 hnonneg.2.1 hnonneg.2.2 C).1
  refine ⟨m, z, hnonneg, hIC, ?_, nonsurgeRatio, surgeRatio,
    hnBounds, hsBounds, hm0_eq, hz0_eq, hm1_eq, hz1_eq, hnAccount,
    hsAccount⟩
  exact ⟨ctmcDynamicSwitchProb switch12 switch21, by intro i τ; rfl⟩

/--
Integrated Theorem 3 endpoint using the statewise accept-all reward comparison
interface, the closest current Lean target for the remaining Lemma 5 endpoint
improvement argument.
-/
theorem paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_statewise_accept_all_reward
    (R : DynamicReward)
    (rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hrho_lt_one : rho < 1)
    (hT1_pos : 0 < T1)
    (hQ1_sub_switch12_pos : 0 < Q1 - switch12)
    (hden_theorem3_pos :
      0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)
    (hlemma9_den_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_den_upper :
      0 < lemma9StructuredUpperDenominator Q1 Q2 switch21)
    (hlemma9_left_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 T2 Q2 switch21 *
          lemma9StructuredUpperDenominator Q1 Q2 switch21 ≤ 0)
    (hlemma9_right_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Q2 *
        lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_upper_pos :
      0 < lemma9StructuredUpper T1 Q1 T2 Q2 switch21)
    (hT2_ge_one : 1 ≤ T2)
    (hswitch21_lt_Q2 : switch21 < Q2)
    (C : Theorem4StatewiseAcceptAllRewardCertificate R) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        dynamicIncentiveCompatible R ∧
        (∃ q : Fin 2 → TripLength → ℝ,
          ∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m i) (z i) (q i) τ) ∧
        ∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2 := by
  exact
    paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_positive_replacement
      R rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 hR1_eq hR1_pos
      hR1_lt_R2 hR2_pos hC_lt_rho hrho_lt_one hT1_pos
      hQ1_sub_switch12_pos hden_theorem3_pos hlemma9_den_lower
      hlemma9_den_upper hlemma9_left_nonpos hlemma9_right_pos
      hlemma9_upper_pos hT2_ge_one hswitch21_lt_Q2
      (theorem4PositiveReplacementDerivationCertificate_of_statewise_accept_all_reward
        R C)

/--
Integrated Theorem 3 endpoint from global statewise accept-all reward
improvements.  This derives accept-all optimality internally before invoking
the statewise reward-comparison endpoint.
-/
theorem paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_global_statewise_accept_all_reward
    (R : DynamicReward)
    (rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hrho_lt_one : rho < 1)
    (hT1_pos : 0 < T1)
    (hQ1_sub_switch12_pos : 0 < Q1 - switch12)
    (hden_theorem3_pos :
      0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)
    (hlemma9_den_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_den_upper :
      0 < lemma9StructuredUpperDenominator Q1 Q2 switch21)
    (hlemma9_left_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 T2 Q2 switch21 *
          lemma9StructuredUpperDenominator Q1 Q2 switch21 ≤ 0)
    (hlemma9_right_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Q2 *
        lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_upper_pos :
      0 < lemma9StructuredUpper T1 Q1 T2 Q2 switch21)
    (hT2_ge_one : 1 ≤ T2)
    (hswitch21_lt_Q2 : switch21 < Q2)
    (C : Theorem4GlobalStatewiseAcceptAllRewardCertificate R) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        dynamicIncentiveCompatible R ∧
        (∃ q : Fin 2 → TripLength → ℝ,
          ∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m i) (z i) (q i) τ) ∧
        ∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2 := by
  exact
    paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_statewise_accept_all_reward
      R rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 hR1_eq hR1_pos
      hR1_lt_R2 hR2_pos hC_lt_rho hrho_lt_one hT1_pos
      hQ1_sub_switch12_pos hden_theorem3_pos hlemma9_den_lower
      hlemma9_den_upper hlemma9_left_nonpos hlemma9_right_pos
      hlemma9_upper_pos hT2_ge_one hswitch21_lt_Q2
      (theorem4StatewiseAcceptAllRewardCertificate_of_global_statewise_accept_all_reward
        R C)

/--
Measured Theorem 3 endpoint: construct the CTMC structured-price parameters
from the paper's ratio/sign conditions, then use the remaining global
statewise accept-all reward proof for those constructed measured prices to
conclude dynamic IC for the actual measured reward functional.
-/
theorem paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_global_statewise_accept_all_reward
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hrho_lt_one : rho < 1)
    (hT1_pos : 0 < T1)
    (hQ1_sub_switch12_pos : 0 < Q1 - switch12)
    (hden_theorem3_pos :
      0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)
    (hlemma9_den_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_den_upper :
      0 < lemma9StructuredUpperDenominator Q1 Q2 switch21)
    (hlemma9_left_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 T2 Q2 switch21 *
          lemma9StructuredUpperDenominator Q1 Q2 switch21 ≤ 0)
    (hlemma9_right_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Q2 *
        lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_upper_pos :
      0 < lemma9StructuredUpper T1 Q1 T2 Q2 switch21)
    (hT2_ge_one : 1 ≤ T2)
    (hswitch21_lt_Q2 : switch21 < Q2)
    (hglobal :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        (∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2) →
        Theorem4GlobalStatewiseAcceptAllRewardCertificate
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z)) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        dynamicIncentiveCompatible
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ∧
        (∃ q : Fin 2 → TripLength → ℝ,
          ∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m i) (z i) (q i) τ) ∧
        ∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2 := by
  rcases theorem3StructuredParameters_exist_of_ratio_and_lemma9_final_signs
      rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 hR1_eq hR1_pos
      hR1_lt_R2 hR2_pos hC_lt_rho hrho_lt_one hT1_pos
      hQ1_sub_switch12_pos hden_theorem3_pos hlemma9_den_lower
      hlemma9_den_upper hlemma9_left_nonpos hlemma9_right_pos
      hlemma9_upper_pos hT2_ge_one hswitch21_lt_Q2 with
    ⟨m, z, hnonneg, nonsurgeRatio, surgeRatio, hnBounds, hsBounds,
      hm0_eq, hz0_eq, hm1_eq, hz1_eq, hnAccount, hsAccount⟩
  have hparams :
      ∃ nonsurgeRatio surgeRatio : ℝ,
        lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
          lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
          m 0 = R2 ∧
          z 0 = nonsurgeRatio * R2 ∧
          m 1 =
            theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
          z 1 =
            theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
          m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
          m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2 := by
    exact ⟨nonsurgeRatio, surgeRatio, hnBounds, hsBounds, hm0_eq, hz0_eq,
      hm1_eq, hz1_eq, hnAccount, hsAccount⟩
  let R : DynamicReward :=
    gn21MeasuredCTMCStructuredDynamicReward μ arrival switch12 switch21 m z
  have hglobalC : Theorem4GlobalStatewiseAcceptAllRewardCertificate R := by
    simpa [R] using hglobal m z hnonneg hparams
  have hunique :
      dynamicOptimal R acceptAllDynamicPolicy ∧
        ∀ σ : Fin 2 → TripPolicy,
          dynamicOptimal R σ → σ = acceptAllDynamicPolicy :=
    paper_theorem4_accept_all_unique_optimal_of_global_statewise_accept_all_reward
      R hglobalC
  have hIC : dynamicIncentiveCompatible R :=
    (paper_theorem3_ctmc_structured_prices_ic_of_accept_all_unique_optimal
      R m z switch12 switch21 hnonneg.1 hnonneg.2.1 hnonneg.2.2
      hunique).1
  refine ⟨m, z, hnonneg, ?_, ?_, nonsurgeRatio, surgeRatio,
    hnBounds, hsBounds, hm0_eq, hz0_eq, hm1_eq, hz1_eq, hnAccount,
    hsAccount⟩
  · simpa [R] using hIC
  · exact ⟨ctmcDynamicSwitchProb switch12 switch21, by intro i τ; rfl⟩

/--
Measured Theorem 3 endpoint from aggregate `Q,T,W` accept-all improvements.
This is the Theorem 3-facing version of the measured aggregate Theorem 4
interface: the caller supplies Lemma 6-style aggregate comparisons for the
constructed structured prices, and Lean converts them to the global reward
certificate internally.
-/
theorem paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_accept_all_reward
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hrho_lt_one : rho < 1)
    (hT1_pos : 0 < T1)
    (hQ1_sub_switch12_pos : 0 < Q1 - switch12)
    (hden_theorem3_pos :
      0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)
    (hlemma9_den_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_den_upper :
      0 < lemma9StructuredUpperDenominator Q1 Q2 switch21)
    (hlemma9_left_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 T2 Q2 switch21 *
          lemma9StructuredUpperDenominator Q1 Q2 switch21 ≤ 0)
    (hlemma9_right_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Q2 *
        lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_upper_pos :
      0 < lemma9StructuredUpper T1 Q1 T2 Q2 switch21)
    (hT2_ge_one : 1 ≤ T2)
    (hswitch21_lt_Q2 : switch21 < Q2)
    (hglobal :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        (∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2) →
        Theorem4MeasuredAggregateAcceptAllRewardCertificate
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        dynamicIncentiveCompatible
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ∧
        (∃ q : Fin 2 → TripLength → ℝ,
          ∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m i) (z i) (q i) τ) ∧
        ∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2 := by
  exact
    paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_global_statewise_accept_all_reward
      μ arrival rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 hR1_eq
      hR1_pos hR1_lt_R2 hR2_pos hC_lt_rho hrho_lt_one hT1_pos
      hQ1_sub_switch12_pos hden_theorem3_pos hlemma9_den_lower
      hlemma9_den_upper hlemma9_left_nonpos hlemma9_right_pos
      hlemma9_upper_pos hT2_ge_one hswitch21_lt_Q2
      (by
        intro m z hnonneg hparams
        simpa [gn21MeasuredCTMCStructuredDynamicReward] using
          theorem4GlobalStatewiseAcceptAllRewardCertificate_of_measured_aggregate_improvements
            μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21)
            (hglobal m z hnonneg hparams))

/--
Measured Theorem 3 endpoint from aggregate strict-local improvements.  This is
the endpoint shape closest to the Lemma 6/9/10 derivative argument: the caller
constructs the CTMC structured prices, then supplies a strict aggregate reward
improvement for every optimal policy that fails accept-all in some state.
-/
theorem paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_strict_local_improvements
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hrho_lt_one : rho < 1)
    (hT1_pos : 0 < T1)
    (hQ1_sub_switch12_pos : 0 < Q1 - switch12)
    (hden_theorem3_pos :
      0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)
    (hlemma9_den_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_den_upper :
      0 < lemma9StructuredUpperDenominator Q1 Q2 switch21)
    (hlemma9_left_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 T2 Q2 switch21 *
          lemma9StructuredUpperDenominator Q1 Q2 switch21 ≤ 0)
    (hlemma9_right_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Q2 *
        lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_upper_pos :
      0 < lemma9StructuredUpper T1 Q1 T2 Q2 switch21)
    (hT2_ge_one : 1 ≤ T2)
    (hswitch21_lt_Q2 : switch21 < Q2)
    (hstrict :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        (∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2) →
        Theorem4MeasuredAggregateStrictLocalImprovementCertificate
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        dynamicIncentiveCompatible
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ∧
        (∃ q : Fin 2 → TripLength → ℝ,
          ∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m i) (z i) (q i) τ) ∧
        ∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2 := by
  rcases theorem3StructuredParameters_exist_of_ratio_and_lemma9_final_signs
      rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 hR1_eq hR1_pos
      hR1_lt_R2 hR2_pos hC_lt_rho hrho_lt_one hT1_pos
      hQ1_sub_switch12_pos hden_theorem3_pos hlemma9_den_lower
      hlemma9_den_upper hlemma9_left_nonpos hlemma9_right_pos
      hlemma9_upper_pos hT2_ge_one hswitch21_lt_Q2 with
    ⟨m, z, hnonneg, nonsurgeRatio, surgeRatio, hnBounds, hsBounds,
      hm0_eq, hz0_eq, hm1_eq, hz1_eq, hnAccount, hsAccount⟩
  have hparams :
      ∃ nonsurgeRatio surgeRatio : ℝ,
        lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
          lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
          m 0 = R2 ∧
          z 0 = nonsurgeRatio * R2 ∧
          m 1 =
            theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
          z 1 =
            theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
          m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
          m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2 := by
    exact ⟨nonsurgeRatio, surgeRatio, hnBounds, hsBounds, hm0_eq, hz0_eq,
      hm1_eq, hz1_eq, hnAccount, hsAccount⟩
  let R : DynamicReward :=
    gn21MeasuredCTMCStructuredDynamicReward μ arrival switch12 switch21 m z
  have hstrictC :
      Theorem4MeasuredAggregateStrictLocalImprovementCertificate
        μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21) :=
    hstrict m z hnonneg hparams
  have hunique :
      dynamicOptimal R acceptAllDynamicPolicy ∧
        ∀ σ : Fin 2 → TripPolicy,
          dynamicOptimal R σ → σ = acceptAllDynamicPolicy := by
    simpa [R, gn21MeasuredCTMCStructuredDynamicReward] using
      paper_theorem4_accept_all_unique_optimal_of_measured_aggregate_strict_local_improvements
        μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21) hstrictC
  have hIC : dynamicIncentiveCompatible R :=
    (paper_theorem3_ctmc_structured_prices_ic_of_accept_all_unique_optimal
      R m z switch12 switch21 hnonneg.1 hnonneg.2.1 hnonneg.2.2
      hunique).1
  refine ⟨m, z, hnonneg, ?_, ?_, nonsurgeRatio, surgeRatio,
    hnBounds, hsBounds, hm0_eq, hz0_eq, hm1_eq, hz1_eq, hnAccount,
    hsAccount⟩
  · simpa [R] using hIC
  · exact ⟨ctmcDynamicSwitchProb switch12 switch21, by intro i τ; rfl⟩

/--
Measured Theorem 3 endpoint from Lemma 9/10 interval bridge data.  This is the
strict-local derivative route after the endpoint primitive-identification data
has been packaged state by state.
-/
theorem paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_lemma910_interval_bridges
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hrho_lt_one : rho < 1)
    (hT1_pos : 0 < T1)
    (hQ1_sub_switch12_pos : 0 < Q1 - switch12)
    (hden_theorem3_pos :
      0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)
    (hlemma9_den_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_den_upper :
      0 < lemma9StructuredUpperDenominator Q1 Q2 switch21)
    (hlemma9_left_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 T2 Q2 switch21 *
          lemma9StructuredUpperDenominator Q1 Q2 switch21 ≤ 0)
    (hlemma9_right_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Q2 *
        lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_upper_pos :
      0 < lemma9StructuredUpper T1 Q1 T2 Q2 switch21)
    (hT2_ge_one : 1 ≤ T2)
    (hswitch21_lt_Q2 : switch21 < Q2)
    (hbridges :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        (∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2) →
        Theorem4Lemma910IntervalBridgeCertificate
          μ arrival m z switch12 switch21) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        dynamicIncentiveCompatible
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ∧
        (∃ q : Fin 2 → TripLength → ℝ,
          ∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m i) (z i) (q i) τ) ∧
        ∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2 := by
  exact
    paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_strict_local_improvements
      μ arrival rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 hR1_eq
      hR1_pos hR1_lt_R2 hR2_pos hC_lt_rho hrho_lt_one hT1_pos
      hQ1_sub_switch12_pos hden_theorem3_pos hlemma9_den_lower
      hlemma9_den_upper hlemma9_left_nonpos hlemma9_right_pos
      hlemma9_upper_pos hT2_ge_one hswitch21_lt_Q2
      (by
        intro m z hnonneg hparams
        exact
          theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_lemma910_interval_bridges
            μ arrival m z switch12 switch21
            (hbridges m z hnonneg hparams))

/--
Measured Theorem 3 endpoint from generalized Lemma 9/10 endpoint bridge data.
This accepts either upper-endpoint or finite lower-endpoint primitive
identifications through the generalized bridge certificate.
-/
theorem paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_lemma910_endpoint_bridges
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC T1 T2 Q1 Q2 switch12 < rho)
    (hrho_lt_one : rho < 1)
    (hT1_pos : 0 < T1)
    (hQ1_sub_switch12_pos : 0 < Q1 - switch12)
    (hden_theorem3_pos :
      0 < theorem3FeasibilityDenominator T1 T2 Q1 Q2 switch12)
    (hlemma9_den_lower :
      0 < lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_den_upper :
      0 < lemma9StructuredUpperDenominator Q1 Q2 switch21)
    (hlemma9_left_nonpos :
      lemma9StructuredLowerNumerator T1 Q1 T2 Q2 switch21 *
          lemma9StructuredUpperDenominator Q1 Q2 switch21 ≤ 0)
    (hlemma9_right_pos :
      0 < lemma9StructuredUpperNumerator T1 Q1 Q2 *
        lemma9StructuredLowerDenominator T1 Q1 T2 Q2 switch21)
    (hlemma9_upper_pos :
      0 < lemma9StructuredUpper T1 Q1 T2 Q2 switch21)
    (hT2_ge_one : 1 ≤ T2)
    (hswitch21_lt_Q2 : switch21 < Q2)
    (hbridges :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        (∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2) →
        Theorem4Lemma910EndpointBridgeCertificate
          μ arrival m z switch12 switch21) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        dynamicIncentiveCompatible
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ∧
        (∃ q : Fin 2 → TripLength → ℝ,
          ∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m i) (z i) (q i) τ) ∧
        ∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio T2 Q2 T1 Q1 switch12 ∧
            lemma9StructuredBounds surgeRatio T1 Q1 T2 Q2 switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2 T2 Q2 switch21 surgeRatio ∧
            m 0 * (T1 - 1) + z 0 * (Q1 - switch12) = R1 * T1 ∧
            m 1 * (T2 - 1) + z 1 * (Q2 - switch21) = R2 * T2 := by
  exact
    paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_strict_local_improvements
      μ arrival rho R1 R2 T1 Q1 T2 Q2 switch12 switch21 hR1_eq
      hR1_pos hR1_lt_R2 hR2_pos hC_lt_rho hrho_lt_one hT1_pos
      hQ1_sub_switch12_pos hden_theorem3_pos hlemma9_den_lower
      hlemma9_den_upper hlemma9_left_nonpos hlemma9_right_pos
      hlemma9_upper_pos hT2_ge_one hswitch21_lt_Q2
      (by
        intro m z hnonneg hparams
        exact
          theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_lemma910_endpoint_bridges
            μ arrival m z switch12 switch21
            (hbridges m z hnonneg hparams))

/--
Accept-all measured primitives discharge the scalar positivity conditions used
by the integrated Theorem 3 endpoints.  This isolates the CTMC/measure facts so
global-comparison and strict-local Theorem 3 wrappers can share them.
-/
theorem theorem3_acceptAll_measured_primitives_scalar_conditions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmeasure1_pos : 0 < μ 0 acceptAllPolicy)
    (hmeasure2_pos : 0 < μ 1 acceptAllPolicy) :
    0 < gn21AcceptAllScaledStateTime (μ 0) (arrival 0) ∧
      0 <
        gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 -
          switch12 ∧
      0 <
        theorem3FeasibilityDenominator
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 ∧
      1 ≤ gn21AcceptAllScaledStateTime (μ 1) (arrival 1) ∧
      switch21 <
        gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 := by
  have hsum12 : 0 < switch12 + switch21 := by
    linarith
  have hsum21 : 0 < switch21 + switch12 := by
    linarith
  have hT1_pos :
      0 < gn21AcceptAllScaledStateTime (μ 0) (arrival 0) := by
    simpa [gn21AcceptAllScaledStateTime] using
      gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) acceptAllPolicy
        (le_of_lt harrival1_pos) measurableSet_acceptAllPolicy
        (fun _ hτ => hτ)
  have hT2_ge_one :
      1 ≤ gn21AcceptAllScaledStateTime (μ 1) (arrival 1) := by
    simpa [gn21AcceptAllScaledStateTime] using
      gn21ScaledStateTime_ge_one_of_nonneg (μ 1) (arrival 1) acceptAllPolicy
        (le_of_lt harrival2_pos) measurableSet_acceptAllPolicy
        (fun _ hτ => hτ)
  have hQ1_sub_switch12_pos :
      0 <
        gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 -
          switch12 := by
    simpa [gn21AcceptAllExitWeightIntegral] using
      (sub_pos.mpr
        (paper_remark4_exit_weight_gt_switch_of_positive_measure
          (μ 0) (arrival 0) switch12 switch21 acceptAllPolicy
          harrival1_pos hswitch12_pos hsum12 measurableSet_acceptAllPolicy
          (fun _ hτ => hτ) hq1_integrable hmeasure1_pos))
  have hQ2_pos :
      0 <
        gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 := by
    simpa [gn21AcceptAllExitWeightIntegral] using
      gn21ExitWeightIntegral_pos_of_switch_pos
        (μ 1) (arrival 1) switch21 switch12 acceptAllPolicy
        (le_of_lt harrival2_pos) hswitch21_pos hsum21
        measurableSet_acceptAllPolicy (fun _ hτ => hτ)
  have hgap_pos :
      0 <
        switch12 * gn21AcceptAllScaledStateTime (μ 0) (arrival 0) -
          gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 := by
    simpa [gn21AcceptAllScaledStateTime, gn21AcceptAllExitWeightIntegral] using
      paper_remark4_scaled_time_minus_exit_weight_pos_of_positive_measure
        (μ 0) (arrival 0) switch12 switch21 acceptAllPolicy
        harrival1_pos hswitch12_pos hsum12 measurableSet_acceptAllPolicy
        (fun _ hτ => hτ) htime1_integrable hq1_integrable hmeasure1_pos
  have hT2_nonneg :
      0 ≤ gn21AcceptAllScaledStateTime (μ 1) (arrival 1) :=
    le_trans zero_le_one hT2_ge_one
  have hsecond_nonneg :
      0 ≤
        gn21AcceptAllScaledStateTime (μ 1) (arrival 1) * switch12 +
          gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 :=
    paper_theorem3_switch_term_nonneg
      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
      switch12 hT2_nonneg (le_of_lt hQ2_pos) (le_of_lt hswitch12_pos)
  have hden_theorem3_pos :
      0 <
        theorem3FeasibilityDenominator
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 :=
    paper_theorem3_feasibility_denominator_pos_of_positive_pieces
      (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
      (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
      switch12 hQ2_pos hgap_pos hswitch12_pos hsecond_nonneg
  have hswitch21_lt_Q2 :
      switch21 <
        gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 := by
    simpa [gn21AcceptAllExitWeightIntegral] using
      paper_remark4_exit_weight_gt_switch_of_positive_measure
        (μ 1) (arrival 1) switch21 switch12 acceptAllPolicy
        harrival2_pos hswitch21_pos hsum21 measurableSet_acceptAllPolicy
        (fun _ hτ => hτ) hq2_integrable hmeasure2_pos
  exact ⟨hT1_pos, hQ1_sub_switch12_pos, hden_theorem3_pos,
    hT2_ge_one, hswitch21_lt_Q2⟩

/--
Measured Theorem 3 endpoint with `T_i,Q_i` specialized to the accept-all
measured primitives.  The CTMC/measure assumptions discharge the scalar
positivity obligations; what remains is the paper's Lemma 9 final-sign input
and the global reward-improvement proof for the constructed measured prices.
-/
theorem paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_global_statewise_accept_all_reward
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmeasure1_pos : 0 < μ 0 acceptAllPolicy)
    (hmeasure2_pos : 0 < μ 1 acceptAllPolicy)
    (hlemma9_den_lower :
      0 <
        lemma9StructuredLowerDenominator
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch21)
    (hlemma9_den_upper :
      0 <
        lemma9StructuredUpperDenominator
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch21)
    (hlemma9_left_nonpos :
      lemma9StructuredLowerNumerator
            (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
            (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
            switch21 *
          lemma9StructuredUpperDenominator
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
            switch21 ≤ 0)
    (hlemma9_right_pos :
      0 <
        lemma9StructuredUpperNumerator
            (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12) *
          lemma9StructuredLowerDenominator
            (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
            (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
            switch21)
    (hlemma9_upper_pos :
      0 <
        lemma9StructuredUpper
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch21)
    (hglobal :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        (∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio
            (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
            (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
            (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            switch12 ∧
            lemma9StructuredBounds surgeRatio
              (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
              (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
              (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
              (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
              switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
                switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
                switch21 surgeRatio ∧
            m 0 *
                (gn21AcceptAllScaledStateTime (μ 0) (arrival 0) - 1) +
              z 0 *
                (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 -
                  switch12) =
                R1 * gn21AcceptAllScaledStateTime (μ 0) (arrival 0) ∧
            m 1 *
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1) - 1) +
              z 1 *
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 -
                  switch21) =
                R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1)) →
        Theorem4GlobalStatewiseAcceptAllRewardCertificate
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z)) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        dynamicIncentiveCompatible
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ∧
        (∃ q : Fin 2 → TripLength → ℝ,
          ∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m i) (z i) (q i) τ) ∧
        ∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio
            (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
            (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
            (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            switch12 ∧
            lemma9StructuredBounds surgeRatio
              (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
              (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
              (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
              (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
              switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
                switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
                switch21 surgeRatio ∧
            m 0 *
                (gn21AcceptAllScaledStateTime (μ 0) (arrival 0) - 1) +
              z 0 *
                (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 -
                  switch12) =
                R1 * gn21AcceptAllScaledStateTime (μ 0) (arrival 0) ∧
            m 1 *
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1) - 1) +
              z 1 *
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 -
                  switch21) =
                R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1) := by
  have hsum12 : 0 < switch12 + switch21 := by
    linarith
  have hsum21 : 0 < switch21 + switch12 := by
    linarith
  have hT1_pos :
      0 < gn21AcceptAllScaledStateTime (μ 0) (arrival 0) := by
    simpa [gn21AcceptAllScaledStateTime] using
      gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) acceptAllPolicy
        (le_of_lt harrival1_pos) measurableSet_acceptAllPolicy
        (fun _ hτ => hτ)
  have hT2_ge_one :
      1 ≤ gn21AcceptAllScaledStateTime (μ 1) (arrival 1) := by
    simpa [gn21AcceptAllScaledStateTime] using
      gn21ScaledStateTime_ge_one_of_nonneg (μ 1) (arrival 1) acceptAllPolicy
        (le_of_lt harrival2_pos) measurableSet_acceptAllPolicy
        (fun _ hτ => hτ)
  have hQ1_sub_switch12_pos :
      0 <
        gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 -
          switch12 := by
    simpa [gn21AcceptAllExitWeightIntegral] using
      (sub_pos.mpr
        (paper_remark4_exit_weight_gt_switch_of_positive_measure
          (μ 0) (arrival 0) switch12 switch21 acceptAllPolicy
          harrival1_pos hswitch12_pos hsum12 measurableSet_acceptAllPolicy
          (fun _ hτ => hτ) hq1_integrable hmeasure1_pos))
  have hQ2_pos :
      0 <
        gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 := by
    simpa [gn21AcceptAllExitWeightIntegral] using
      gn21ExitWeightIntegral_pos_of_switch_pos
        (μ 1) (arrival 1) switch21 switch12 acceptAllPolicy
        (le_of_lt harrival2_pos) hswitch21_pos hsum21
        measurableSet_acceptAllPolicy (fun _ hτ => hτ)
  have hgap_pos :
      0 <
        switch12 * gn21AcceptAllScaledStateTime (μ 0) (arrival 0) -
          gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 := by
    simpa [gn21AcceptAllScaledStateTime, gn21AcceptAllExitWeightIntegral] using
      paper_remark4_scaled_time_minus_exit_weight_pos_of_positive_measure
        (μ 0) (arrival 0) switch12 switch21 acceptAllPolicy
        harrival1_pos hswitch12_pos hsum12 measurableSet_acceptAllPolicy
        (fun _ hτ => hτ) htime1_integrable hq1_integrable hmeasure1_pos
  have hT2_nonneg :
      0 ≤ gn21AcceptAllScaledStateTime (μ 1) (arrival 1) :=
    le_trans zero_le_one hT2_ge_one
  have hsecond_nonneg :
      0 ≤
        gn21AcceptAllScaledStateTime (μ 1) (arrival 1) * switch12 +
          gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 :=
    paper_theorem3_switch_term_nonneg
      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
      switch12 hT2_nonneg (le_of_lt hQ2_pos) (le_of_lt hswitch12_pos)
  have hden_theorem3_pos :
      0 <
        theorem3FeasibilityDenominator
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 :=
    paper_theorem3_feasibility_denominator_pos_of_positive_pieces
      (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
      (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
      switch12 hQ2_pos hgap_pos hswitch12_pos hsecond_nonneg
  have hswitch21_lt_Q2 :
      switch21 <
        gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 := by
    simpa [gn21AcceptAllExitWeightIntegral] using
      paper_remark4_exit_weight_gt_switch_of_positive_measure
        (μ 1) (arrival 1) switch21 switch12 acceptAllPolicy
        harrival2_pos hswitch21_pos hsum21 measurableSet_acceptAllPolicy
        (fun _ hτ => hτ) hq2_integrable hmeasure2_pos
  exact
    paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_global_statewise_accept_all_reward
      μ arrival rho R1 R2
      (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
      (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
      switch12 switch21 hR1_eq hR1_pos hR1_lt_R2 hR2_pos
      hC_lt_rho hrho_lt_one hT1_pos hQ1_sub_switch12_pos
      hden_theorem3_pos hlemma9_den_lower hlemma9_den_upper
      hlemma9_left_nonpos hlemma9_right_pos hlemma9_upper_pos hT2_ge_one
      hswitch21_lt_Q2 hglobal

/--
Measured Theorem 3 endpoint with `T_i,Q_i` specialized to the accept-all
measured primitives, using the strict-local aggregate-improvement route.  This
is the accept-all-primitive specialization of
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_strict_local_improvements`.
-/
theorem paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_measured_aggregate_strict_local_improvements
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmeasure1_pos : 0 < μ 0 acceptAllPolicy)
    (hmeasure2_pos : 0 < μ 1 acceptAllPolicy)
    (hlemma9_den_lower :
      0 <
        lemma9StructuredLowerDenominator
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch21)
    (hlemma9_den_upper :
      0 <
        lemma9StructuredUpperDenominator
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch21)
    (hlemma9_left_nonpos :
      lemma9StructuredLowerNumerator
            (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
            (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
            switch21 *
          lemma9StructuredUpperDenominator
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
            switch21 ≤ 0)
    (hlemma9_right_pos :
      0 <
        lemma9StructuredUpperNumerator
            (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12) *
          lemma9StructuredLowerDenominator
            (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
            (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
            switch21)
    (hlemma9_upper_pos :
      0 <
        lemma9StructuredUpper
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch21)
    (hstrict :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
        (∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio
            (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
            (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
            (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            switch12 ∧
            lemma9StructuredBounds surgeRatio
              (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
              (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
              (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
              (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
              switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
                switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
                switch21 surgeRatio ∧
            m 0 *
                (gn21AcceptAllScaledStateTime (μ 0) (arrival 0) - 1) +
              z 0 *
                (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 -
                  switch12) =
                R1 * gn21AcceptAllScaledStateTime (μ 0) (arrival 0) ∧
            m 1 *
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1) - 1) +
              z 1 *
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 -
                  switch21) =
                R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1)) →
        Theorem4MeasuredAggregateStrictLocalImprovementCertificate
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)) :
    ∃ m z : Fin 2 → ℝ,
      (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
        dynamicIncentiveCompatible
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ∧
        (∃ q : Fin 2 → TripLength → ℝ,
          ∀ i τ,
            ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
              structuredSurgePrice (m i) (z i) (q i) τ) ∧
        ∃ nonsurgeRatio surgeRatio : ℝ,
          lemma10StructuredBounds nonsurgeRatio
            (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
            (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
            (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
            (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
            switch12 ∧
            lemma9StructuredBounds surgeRatio
              (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
              (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
              (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
              (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
              switch21 ∧
            m 0 = R2 ∧
            z 0 = nonsurgeRatio * R2 ∧
            m 1 =
              theorem3SurgeMultiplierFromRatio R1 R2
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
                switch21 surgeRatio ∧
            z 1 =
              theorem3SurgeZFromRatio R1 R2
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
                switch21 surgeRatio ∧
            m 0 *
                (gn21AcceptAllScaledStateTime (μ 0) (arrival 0) - 1) +
              z 0 *
                (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 -
                  switch12) =
                R1 * gn21AcceptAllScaledStateTime (μ 0) (arrival 0) ∧
            m 1 *
                (gn21AcceptAllScaledStateTime (μ 1) (arrival 1) - 1) +
              z 1 *
                (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 -
                  switch21) =
                R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1) := by
  rcases theorem3_acceptAll_measured_primitives_scalar_conditions
      μ arrival switch12 switch21 harrival1_pos harrival2_pos
      hswitch12_pos hswitch21_pos htime1_integrable hq1_integrable
      hq2_integrable hmeasure1_pos hmeasure2_pos with
    ⟨hT1_pos, hQ1_sub_switch12_pos, hden_theorem3_pos, hT2_ge_one,
      hswitch21_lt_Q2⟩
  exact
    paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_strict_local_improvements
      μ arrival rho R1 R2
      (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
      (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
      (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
      (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
      switch12 switch21 hR1_eq hR1_pos hR1_lt_R2 hR2_pos
      hC_lt_rho hrho_lt_one hT1_pos hQ1_sub_switch12_pos
      hden_theorem3_pos hlemma9_den_lower hlemma9_den_upper
      hlemma9_left_nonpos hlemma9_right_pos hlemma9_upper_pos hT2_ge_one
      hswitch21_lt_Q2 hstrict

section FiniteSupport

variable {State Action : Type*}
variable [Fintype State] [DecidableEq State]
variable [Fintype Action] [DecidableEq Action]

/-- Finite approximation of a dynamic driver decision model. -/
abbrev FiniteDriverModel (State Action : Type*) := FiniteMDP State Action

/-- Finite-horizon driver IC in a discrete MDP approximation. -/
def finiteHorizonDriverIC
    (M : FiniteDriverModel State Action) (π : FiniteMDP.Policy State Action)
    (n : ℕ) : Prop :=
  FiniteMDP.IncentiveCompatibleAtHorizon M π n

/--
Auxiliary finite dynamic-pricing theorem: a deterministic policy that is
Bellman-greedy at every remaining horizon is finite-horizon IC.
-/
theorem paper_aux_finite_dynamic_pricing_ic_of_greedy
    [Nonempty Action]
    (M : FiniteDriverModel State Action) (choose : State → Action)
    (hgreedy : ∀ n, FiniteMDP.Greedy M choose (FiniteMDP.optimalValue M n))
    (n : ℕ) :
    finiteHorizonDriverIC M (FiniteMDP.deterministicPolicy choose) n := by
  exact FiniteMDP.incentiveCompatibleAtHorizon_of_greedy_optimalValue M choose
    hgreedy n

/--
Auxiliary finite dynamic-pricing theorem: an explicit better deviation refutes
finite-horizon IC.
-/
theorem paper_aux_finite_dynamic_pricing_not_ic_of_profitable_deviation
    (M : FiniteDriverModel State Action) (π ρ : FiniteMDP.Policy State Action)
    (n : ℕ) (x : State)
    (hdev : FiniteMDP.ProfitableDeviationAtHorizon M π ρ n x) :
    ¬ finiteHorizonDriverIC M π n := by
  exact FiniteMDP.not_incentiveCompatibleAtHorizon_of_profitableDeviation
    M π ρ n x hdev

end FiniteSupport

end

end GN21DriverSurgePricing
