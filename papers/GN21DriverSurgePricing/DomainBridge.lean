import EconCSLib.Foundations.Math.ConvexCombination
import GN21DriverSurgePricing.MainTheorems

/-!
# Domain Bridges for GN21 Measurable Theorem 3

The Appendix-D reward-rate formulas in the source paper divide by accepted
trip mass.  `MainTheorems.lean` therefore has a positive-mass measurable
source domain alongside the full feasible-measurable domain.  This file keeps
the order-theoretic bridge between those domains explicit: if every feasible
zero-mass policy is strictly dominated by a feasible positive-mass policy, then
positive-mass IC and positive-mass a.e. uniqueness lift to the full measurable
statement.
-/

open EconCSLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

/--
Positive-mass measurable optimality is locally optimal against one-state
replacements that stay in the positive-mass measurable source domain.
-/
theorem dynamicStateReward_optimal_of_dynamicPositiveMassMeasurableOptimal
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) {σ : Fin 2 → TripPolicy}
    (hσ : dynamicPositiveMassMeasurableOptimal μ R σ) (i : Fin 2)
    {τ : TripPolicy}
    (hτ :
      dynamicFeasibleMeasurablePositiveMassPolicy μ
        (Function.update σ i τ)) :
    dynamicStateReward R σ i τ ≤ dynamicStateReward R σ i (σ i) := by
  unfold dynamicStateReward
  simpa [Function.update_eq_self] using
    hσ.2 (Function.update σ i τ) hτ

/--
Positive-mass measurable optimality is locally optimal against replacing one
state by accept-all, provided accept-all has positive mass in each state.
-/
theorem dynamicStateReward_acceptAll_le_of_dynamicPositiveMassMeasurableOptimal
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) {σ : Fin 2 → TripPolicy}
    (hσ : dynamicPositiveMassMeasurableOptimal μ R σ)
    (hmass_acceptAll :
      ∀ i : Fin 2, 0 < singleStateTripMass (μ i) acceptAllPolicy)
    (i : Fin 2) :
    dynamicStateReward R σ i acceptAllPolicy ≤
      dynamicStateReward R σ i (σ i) :=
  dynamicStateReward_optimal_of_dynamicPositiveMassMeasurableOptimal μ R hσ i
    (dynamicFeasibleMeasurablePositiveMassPolicy_update_acceptAll
      hσ.1 hmass_acceptAll i)

/--
Positive-mass measurable optimality for the measured GN21 reward is preserved
when the surge-state policy is replaced by exact accept-all after it has been
shown accept-all almost everywhere.
-/
theorem dynamicPositiveMassMeasurableOptimal_gn21MeasuredDynamicRewardFunctional_update_one_acceptAll_of_ae
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    {ρ : Fin 2 → TripPolicy}
    (hρ :
      dynamicPositiveMassMeasurableOptimal μ
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ)
    (hmass_acceptAll :
      ∀ i : Fin 2, 0 < singleStateTripMass (μ i) acceptAllPolicy)
    (hae : acceptAllAlmostEverywhere (μ 1) (ρ 1)) :
    dynamicPositiveMassMeasurableOptimal μ
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
      (Function.update ρ 1 acceptAllPolicy) := by
  have hpolicy_ae :
      policyAlmostEverywhereEq (μ 1) (ρ 1) acceptAllPolicy :=
    policyAlmostEverywhereEq_acceptAll_of_acceptAllAlmostEverywhere
      (μ 1) (hρ.1.1 1).1 hae
  constructor
  · exact
      dynamicFeasibleMeasurablePositiveMassPolicy_update_acceptAll
        hρ.1 hmass_acceptAll 1
  · intro κ hκ
    have heq :=
      gn21MeasuredDynamicRewardFunctional_congr_right_policy_ae
        μ arrival switch12 switch21 w hpolicy_ae
    simpa [← heq] using hρ.2 κ hκ

/--
Local non-surge accept-all marginal comparison from a one-state dynamic reward
comparison.  This is the algebraic core of
`lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_zero`
with the global measurable-optimality premise replaced by the exact local
accept-all replacement inequality.
-/
theorem lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_zero_of_local_reward
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    {ρ : Fin 2 → TripPolicy}
    (hlocal :
      dynamicStateReward
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ 0 acceptAllPolicy ≤
        dynamicStateReward
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ 0 (ρ 0))
    (harrival_pos : 0 < arrival 0)
    (Hcurrent :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (HacceptAll :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 acceptAllPolicy (ρ 1))
    (hden_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
    (hden_acceptAll_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            acceptAllPolicy *
          gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
        gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
          gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy)
    (hq_integrable_acceptAll :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hw_integrable_acceptAll : IntegrableOn (w 0) acceptAllPolicy (μ 0))
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (hq_integrable_current :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        (ρ 0) (μ 0))
    (hw_integrable_current : IntegrableOn (w 0) (ρ 0) (μ 0))
    (htime_integrable_current :
      IntegrableOn (fun τ : TripLength => τ) (ρ 0) (μ 0)) :
    lemma5MarginalSetReward (μ 0)
        (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (ρ 0) (ρ 1)) acceptAllPolicy ≤
      lemma5MarginalSetReward (μ 0)
        (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (ρ 0) (ρ 1)) (ρ 0) := by
  have hdyn :
      gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) acceptAllPolicy (ρ 1) ≤
        gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) := by
    simpa [dynamicStateReward_gn21MeasuredDynamicRewardFunctional_zero]
      using hlocal
  have hagg :
      gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) acceptAllPolicy (ρ 1) ≤
        gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) := by
    rw [paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) acceptAllPolicy (ρ 1) HacceptAll,
      paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (ρ 0) (ρ 1) Hcurrent] at hdyn
    exact hdyn
  have hquot :
      gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            acceptAllPolicy)
          (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
          (gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy)
          (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
          (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) acceptAllPolicy)
          (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1)) ≤
        gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
          (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
          (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
          (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
          (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0))
          (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1)) := by
    simpa [gn21MeasuredAggregateRewardPrimitives] using hagg
  have hlinear_raw :=
    gn21AggregateDynamicReward_candidate_left_linear_score_le_current_of_le
      (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
      (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
      (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
      (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0))
      (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1))
      (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
        acceptAllPolicy)
      (gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy)
      (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) acceptAllPolicy)
      hden_pos hden_acceptAll_pos hquot
  have hlinear :
      gn21MeasuredLeftLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1)
          acceptAllPolicy ≤
        gn21MeasuredLeftLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1)
          (ρ 0) := by
    simpa [gn21MeasuredLeftLinearScoreAtCurrent, mul_comm, mul_left_comm,
      mul_assoc] using hlinear_raw
  have hscore_candidate :=
    gn21MeasuredLeftLinearScore_eq_const_add_marginalSetReward
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (ρ 0) (ρ 1) acceptAllPolicy
      hq_integrable_acceptAll hw_integrable_acceptAll
      htime_integrable_acceptAll
  have hscore_current :=
    gn21MeasuredLeftLinearScore_eq_const_add_marginalSetReward
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (ρ 0) (ρ 1) (ρ 0)
      hq_integrable_current hw_integrable_current htime_integrable_current
  rw [hscore_candidate, hscore_current] at hlinear
  nlinarith [harrival_pos, hlinear]

/--
Surge-state counterpart of
`lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_zero_of_local_reward`.
-/
theorem lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_one_of_local_reward
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    {ρ : Fin 2 → TripPolicy}
    (hlocal :
      dynamicStateReward
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ 1 acceptAllPolicy ≤
        dynamicStateReward
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ 1 (ρ 1))
    (harrival_pos : 0 < arrival 1)
    (Hcurrent :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) (ρ 1))
    (HacceptAll :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1) (arrival 0) (arrival 1)
        switch12 switch21 (ρ 0) acceptAllPolicy)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0) *
            gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) +
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1) *
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
    (hden_acceptAll_pos :
      0 <
        gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            (ρ 0) *
          gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy +
        gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            acceptAllPolicy *
          gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
    (hq_integrable_acceptAll :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hw_integrable_acceptAll : IntegrableOn (w 1) acceptAllPolicy (μ 1))
    (htime_integrable_acceptAll :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq_integrable_current :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        (ρ 1) (μ 1))
    (hw_integrable_current : IntegrableOn (w 1) (ρ 1) (μ 1))
    (htime_integrable_current :
      IntegrableOn (fun τ : TripLength => τ) (ρ 1) (μ 1)) :
    lemma5MarginalSetReward (μ 1)
        (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (ρ 0) (ρ 1)) acceptAllPolicy ≤
      lemma5MarginalSetReward (μ 1)
        (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
          (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
          (ρ 0) (ρ 1)) (ρ 1) := by
  have hdyn :
      gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (ρ 0) acceptAllPolicy ≤
        gn21MeasuredDynamicReward (μ 0) (μ 1) (arrival 0) (arrival 1)
          switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) := by
    simpa [dynamicStateReward_gn21MeasuredDynamicRewardFunctional_one]
      using hlocal
  have hagg :
      gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) acceptAllPolicy ≤
        gn21MeasuredAggregateRewardPrimitives (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1) := by
    rw [paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (ρ 0) acceptAllPolicy HacceptAll,
      paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (ρ 0) (ρ 1) Hcurrent] at hdyn
    exact hdyn
  have hquot :
      gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
          (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            acceptAllPolicy)
          (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
          (gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy)
          (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0))
          (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) acceptAllPolicy) ≤
        gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
          (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
          (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
          (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
          (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0))
          (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1)) := by
    simpa [gn21MeasuredAggregateRewardPrimitives] using hagg
  have hlinear_raw :=
    gn21AggregateDynamicReward_candidate_right_linear_score_le_current_of_le
      (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21 (ρ 0))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12 (ρ 1))
      (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
      (gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
      (gn21ScaledStateEarning (μ 0) (arrival 0) (w 0) (ρ 0))
      (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) (ρ 1))
      (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
        acceptAllPolicy)
      (gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy)
      (gn21ScaledStateEarning (μ 1) (arrival 1) (w 1) acceptAllPolicy)
      hden_pos hden_acceptAll_pos hquot
  have hlinear :
      gn21MeasuredRightLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1)
          acceptAllPolicy ≤
        gn21MeasuredRightLinearScoreAtCurrent (μ 0) (μ 1) (arrival 0)
          (arrival 1) switch12 switch21 (w 0) (w 1) (ρ 0) (ρ 1)
          (ρ 1) := by
    simpa [gn21MeasuredRightLinearScoreAtCurrent, mul_comm, mul_left_comm,
      mul_assoc] using hlinear_raw
  have hscore_candidate :=
    gn21MeasuredRightLinearScore_eq_const_add_marginalSetReward
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (ρ 0) (ρ 1) acceptAllPolicy
      hq_integrable_acceptAll hw_integrable_acceptAll
      htime_integrable_acceptAll
  have hscore_current :=
    gn21MeasuredRightLinearScore_eq_const_add_marginalSetReward
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (ρ 0) (ρ 1) (ρ 1)
      hq_integrable_current hw_integrable_current htime_integrable_current
  rw [hscore_candidate, hscore_current] at hlinear
  nlinarith [harrival_pos, hlinear]

/-- Zero real trip mass plus finite underlying measure forces measure zero. -/
theorem measure_zero_of_singleStateTripMass_eq_zero_of_ne_top
    {μ : Measure TripLength} {σ : TripPolicy}
    (hmass : singleStateTripMass μ σ = 0)
    (hfinite : μ σ ≠ ⊤) :
    μ σ = 0 := by
  have hzero_or_top : μ σ = 0 ∨ μ σ = ⊤ := by
    simpa [singleStateTripMass] using
      (ENNReal.toReal_eq_zero_iff (μ σ)).mp hmass
  rcases hzero_or_top with hzero | htop
  · exact hzero
  · exact False.elim (hfinite htop)

/-- Zero accepted mass on a finite-measure policy makes accepted trip time vanish. -/
theorem singleStateTripTime_eq_zero_of_mass_zero_of_ne_top
    {μ : Measure TripLength} {σ : TripPolicy}
    (hmass : singleStateTripMass μ σ = 0)
    (hfinite : μ σ ≠ ⊤) :
    singleStateTripTime μ σ = 0 :=
  singleStateTripTime_eq_zero_of_measure_zero μ σ
    (measure_zero_of_singleStateTripMass_eq_zero_of_ne_top hmass hfinite)

/-- Zero accepted mass on a finite-measure policy makes accepted payment vanish. -/
theorem singleStateTripPayment_eq_zero_of_mass_zero_of_ne_top
    {μ : Measure TripLength} {w : PricingFunction} {σ : TripPolicy}
    (hmass : singleStateTripMass μ σ = 0)
    (hfinite : μ σ ≠ ⊤) :
    singleStateTripPayment μ w σ = 0 :=
  singleStateTripPayment_eq_zero_of_measure_zero μ w σ
    (measure_zero_of_singleStateTripMass_eq_zero_of_ne_top hmass hfinite)

/-- The paper's real-valued state cycle time totalizes to zero at zero mass. -/
theorem gn21StateCycleTime_eq_zero_of_mass_time_zero
    (μ : Measure TripLength) (arrivalRate : ℝ) (σ : TripPolicy)
    (hmass : singleStateTripMass μ σ = 0)
    (htime : singleStateTripTime μ σ = 0) :
    gn21StateCycleTime μ arrivalRate σ = 0 := by
  simp [gn21StateCycleTime, hmass, htime]

/-- The paper's real-valued state reward rate totalizes to zero at zero mass/payment/time. -/
theorem gn21MeasuredStateRewardRate_eq_zero_of_mass_time_payment_zero
    (μ : Measure TripLength) (arrivalRate : ℝ)
    (w : PricingFunction) (σ : TripPolicy)
    (hmass : singleStateTripMass μ σ = 0)
    (htime : singleStateTripTime μ σ = 0)
    (hpayment : singleStateTripPayment μ w σ = 0) :
    gn21MeasuredStateRewardRate μ arrivalRate w σ = 0 := by
  simp [gn21MeasuredStateRewardRate, gn21StateRewardRate,
    gn21StateMeanEarning, gn21StateCycleTime, hmass, htime, hpayment]

/--
If both states have zero accepted mass, zero accepted time, and zero accepted
payment, the current real-valued measured dynamic reward totalizes to zero.
-/
theorem gn21MeasuredDynamicReward_eq_zero_of_both_zero_mass_time_payment
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy)
    (hmassI : singleStateTripMass μI σI = 0)
    (hmassJ : singleStateTripMass μJ σJ = 0)
    (htimeI : singleStateTripTime μI σI = 0)
    (htimeJ : singleStateTripTime μJ σJ = 0)
    (hpaymentI : singleStateTripPayment μI wI σI = 0)
    (hpaymentJ : singleStateTripPayment μJ wJ σJ = 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
      wI wJ σI σJ = 0 := by
  simp [gn21MeasuredDynamicReward, gn21DynamicRewardFormula,
    gn21MeasuredTimeFraction, gn21TimeFractionFormula,
    gn21MeasuredStateRewardRate, gn21StateRewardRate, gn21StateMeanEarning,
    gn21StateCycleTime, hmassI, hmassJ, htimeI, htimeJ, hpaymentI,
    hpaymentJ]

/--
With the current real-valued totalization, if the left state has zero accepted
mass/time/payment and the right-state time-fraction denominator is nonzero,
the measured dynamic reward collapses to the right state's reward rate.  This
is why full-domain Theorem 3 needs an explicit zero-mass dominance or a
different extended-real reward model.
-/
theorem gn21MeasuredDynamicReward_eq_right_rewardRate_of_left_zero_mass_time_payment
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy)
    (hmassI : singleStateTripMass μI σI = 0)
    (htimeI : singleStateTripTime μI σI = 0)
    (hpaymentI : singleStateTripPayment μI wI σI = 0)
    (hdenJ :
      arrivalJ * singleStateTripMass μJ σJ *
            gn21StateCycleTime μJ arrivalJ σJ *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI ≠ 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
      wI wJ σI σJ =
      gn21MeasuredStateRewardRate μJ arrivalJ wJ σJ := by
  have hleft_fraction :
      gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI
        σI σJ = 0 := by
    simp [gn21MeasuredTimeFraction, gn21TimeFractionFormula,
      gn21StateCycleTime, hmassI, htimeI]
  have hright_fraction :
      gn21MeasuredTimeFraction μJ μI arrivalJ arrivalI switchJI switchIJ
        σJ σI = 1 := by
    have hcycleI :
        gn21StateCycleTime μI arrivalI σI = 0 :=
      gn21StateCycleTime_eq_zero_of_mass_time_zero
        μI arrivalI σI hmassI htimeI
    unfold gn21MeasuredTimeFraction gn21TimeFractionFormula
    rw [hcycleI, hmassI]
    set A :=
      arrivalJ * singleStateTripMass μJ σJ *
        gn21StateCycleTime μJ arrivalJ σJ *
          gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI
    have hden_eq :
        arrivalI * 0 * 0 *
              gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ +
            A = A := by
      ring
    rw [hden_eq]
    exact div_self (by simpa [A] using hdenJ)
  have hleft_reward :
      gn21MeasuredStateRewardRate μI arrivalI wI σI = 0 :=
    gn21MeasuredStateRewardRate_eq_zero_of_mass_time_payment_zero
      μI arrivalI wI σI hmassI htimeI hpaymentI
  simp [gn21MeasuredDynamicReward, gn21DynamicRewardFormula,
    hleft_fraction, hright_fraction, hleft_reward]

/-- State-swapped one-zero-state simplification. -/
theorem gn21MeasuredDynamicReward_eq_left_rewardRate_of_right_zero_mass_time_payment
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy)
    (hmassJ : singleStateTripMass μJ σJ = 0)
    (htimeJ : singleStateTripTime μJ σJ = 0)
    (hpaymentJ : singleStateTripPayment μJ wJ σJ = 0)
    (hdenI :
      arrivalI * singleStateTripMass μI σI *
            gn21StateCycleTime μI arrivalI σI *
            gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ ≠ 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
      wI wJ σI σJ =
      gn21MeasuredStateRewardRate μI arrivalI wI σI := by
  have hswap :=
    gn21MeasuredDynamicReward_eq_right_rewardRate_of_left_zero_mass_time_payment
      μJ μI arrivalJ arrivalI switchJI switchIJ wJ wI σJ σI
      hmassJ htimeJ hpaymentJ hdenI
  simpa [gn21MeasuredDynamicReward, gn21DynamicRewardFormula, add_comm,
    mul_comm] using hswap

/--
Concrete zero-mass obstruction: if the left state accepts no trips and the
right state accepts all trips, the current real-valued measured reward
totalizes to the right state's reward rate whenever the right-state
time-fraction denominator is nonzero.
-/
theorem gn21MeasuredDynamicReward_eq_right_rewardRate_of_left_empty_acceptAll
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction)
    (hdenJ :
      arrivalJ * singleStateTripMass μJ acceptAllPolicy *
            gn21StateCycleTime μJ arrivalJ acceptAllPolicy *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI
              (∅ : TripPolicy) ≠ 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
      wI wJ (∅ : TripPolicy) acceptAllPolicy =
      gn21MeasuredStateRewardRate μJ arrivalJ wJ acceptAllPolicy :=
    gn21MeasuredDynamicReward_eq_right_rewardRate_of_left_zero_mass_time_payment
      μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ
      (∅ : TripPolicy) acceptAllPolicy
      (by simp [singleStateTripMass])
      (by simp [singleStateTripTime])
      (by simp [singleStateTripPayment])
      hdenJ

/--
If the right accept-all state reward rate is strictly larger than the full
accept-all dynamic reward, the left-empty/right-accept-all policy is a
profitable deviation under the current real-valued totalization.  This records
why a full-domain Theorem 3 cannot be obtained from the positive-mass source
proof without an explicit zero-mass dominance condition or a revised reward
interface.
-/
theorem gn21MeasuredDynamicReward_left_empty_acceptAll_gt_acceptAll_of_right_rewardRate_gt
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction)
    (hdenJ :
      arrivalJ * singleStateTripMass μJ acceptAllPolicy *
            gn21StateCycleTime μJ arrivalJ acceptAllPolicy *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI
              (∅ : TripPolicy) ≠ 0)
    (hgt :
      gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
          wI wJ acceptAllPolicy acceptAllPolicy <
        gn21MeasuredStateRewardRate μJ arrivalJ wJ acceptAllPolicy) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ acceptAllPolicy acceptAllPolicy <
      gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ (∅ : TripPolicy) acceptAllPolicy := by
  rw [gn21MeasuredDynamicReward_eq_right_rewardRate_of_left_empty_acceptAll
    μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ hdenJ]
  exact hgt

/--
If the two accept-all state reward rates are `R1 < R2` and the left state has
positive accept-all time share, then accept-all's dynamic reward is strictly
below the right accept-all state reward rate.  This is the weighted-average
algebra behind the zero-mass boundary obstruction.
-/
theorem gn21MeasuredDynamicReward_acceptAll_lt_right_rewardRate_of_state_rates
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction)
    (R1 R2 : ℝ)
    (hleft_rate :
      gn21MeasuredStateRewardRate μI arrivalI wI acceptAllPolicy = R1)
    (hright_rate :
      gn21MeasuredStateRewardRate μJ arrivalJ wJ acceptAllPolicy = R2)
    (hleft_fraction_pos :
      0 <
        gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI
          acceptAllPolicy acceptAllPolicy)
    (hfractions_sum :
      gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI
            acceptAllPolicy acceptAllPolicy +
          gn21MeasuredTimeFraction μJ μI arrivalJ arrivalI switchJI switchIJ
            acceptAllPolicy acceptAllPolicy =
        1)
    (hR1_lt_R2 : R1 < R2) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ acceptAllPolicy acceptAllPolicy <
      gn21MeasuredStateRewardRate μJ arrivalJ wJ acceptAllPolicy := by
  rw [paper_lemma1_measured_dynamic_reward_decomposition, hleft_rate,
    hright_rate]
  exact weightedAverage_lt_right_of_left_lt_right hleft_fraction_pos
    hfractions_sum hR1_lt_R2

/--
Sharper zero-mass obstruction for the Theorem 3 accept-all accounting shape:
when accept-all has state rates `R1 < R2` and a positive left-state time share,
the left-empty/right-accept-all zero-mass policy strictly improves on
accept-all under the current real-valued reward totalization.
-/
theorem gn21MeasuredDynamicReward_left_empty_acceptAll_gt_acceptAll_of_state_rates
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction)
    (R1 R2 : ℝ)
    (hdenJ :
      arrivalJ * singleStateTripMass μJ acceptAllPolicy *
            gn21StateCycleTime μJ arrivalJ acceptAllPolicy *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI
              (∅ : TripPolicy) ≠ 0)
    (hleft_rate :
      gn21MeasuredStateRewardRate μI arrivalI wI acceptAllPolicy = R1)
    (hright_rate :
      gn21MeasuredStateRewardRate μJ arrivalJ wJ acceptAllPolicy = R2)
    (hleft_fraction_pos :
      0 <
        gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI
          acceptAllPolicy acceptAllPolicy)
    (hfractions_sum :
      gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI
            acceptAllPolicy acceptAllPolicy +
          gn21MeasuredTimeFraction μJ μI arrivalJ arrivalI switchJI switchIJ
            acceptAllPolicy acceptAllPolicy =
        1)
    (hR1_lt_R2 : R1 < R2) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ acceptAllPolicy acceptAllPolicy <
      gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
        wI wJ (∅ : TripPolicy) acceptAllPolicy :=
  gn21MeasuredDynamicReward_left_empty_acceptAll_gt_acceptAll_of_right_rewardRate_gt
    μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ hdenJ
    (gn21MeasuredDynamicReward_acceptAll_lt_right_rewardRate_of_state_rates
      μI μJ arrivalI arrivalJ switchIJ switchJI wI wJ R1 R2 hleft_rate
      hright_rate hleft_fraction_pos hfractions_sum hR1_lt_R2)

/-- A feasible measurable dynamic policy has zero accepted mass in some state. -/
def dynamicHasZeroAcceptedMass
    (μ : Fin 2 → Measure TripLength) (σ : Fin 2 → TripPolicy) : Prop := ∃ i : Fin 2, singleStateTripMass (μ i) (σ i) = 0

/--
If no state has zero accepted mass, feasible measurability upgrades to the
positive-mass feasible source domain.
-/
theorem dynamicFeasibleMeasurablePositiveMassPolicy_of_no_zero_mass
    {μ : Fin 2 → Measure TripLength}
    {σ : Fin 2 → TripPolicy}
    (hσ : dynamicFeasibleMeasurablePolicy σ)
    (hno_zero : ¬ dynamicHasZeroAcceptedMass μ σ) :
    dynamicFeasibleMeasurablePositiveMassPolicy μ σ := by
  constructor
  · exact hσ
  · intro i
    have hne : singleStateTripMass (μ i) (σ i) ≠ 0 := by
      intro hzero
      exact hno_zero ⟨i, hzero⟩
    exact lt_of_le_of_ne (singleStateTripMass_nonneg (μ i) (σ i))
      (Ne.symm hne)

/-- A feasible measurable policy outside the positive-mass domain has zero mass in some state. -/
theorem dynamicHasZeroAcceptedMass_of_not_positiveMass
    {μ : Fin 2 → Measure TripLength}
    {σ : Fin 2 → TripPolicy}
    (hσ : dynamicFeasibleMeasurablePolicy σ)
    (hnot :
      ¬ dynamicFeasibleMeasurablePositiveMassPolicy μ σ) :
    dynamicHasZeroAcceptedMass μ σ := by
  by_contra hno_zero
  exact hnot
    (dynamicFeasibleMeasurablePositiveMassPolicy_of_no_zero_mass hσ
      hno_zero)

/-- A zero-mass state prevents membership in the positive-mass source domain. -/
theorem not_dynamicFeasibleMeasurablePositiveMassPolicy_of_zero_mass
    {μ : Fin 2 → Measure TripLength}
    {σ : Fin 2 → TripPolicy}
    (hzero : dynamicHasZeroAcceptedMass μ σ) :
    ¬ dynamicFeasibleMeasurablePositiveMassPolicy μ σ := by
  intro hpos
  rcases hzero with ⟨i, hmass_zero⟩
  have hmass_pos := hpos.2 i
  linarith

/--
Strict-dominance certificate for the boundary omitted by the paper's
positive-mass reward-rate algebra: every feasible measurable zero-mass policy
is strictly dominated by some feasible measurable positive-mass policy.
-/
structure DynamicZeroMassStrictDominanceCertificate
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward) where
  improve_zero_mass :
    ∀ σ : Fin 2 → TripPolicy,
      dynamicFeasibleMeasurablePolicy σ →
        dynamicHasZeroAcceptedMass μ σ →
          ∃ τ : Fin 2 → TripPolicy,
            dynamicFeasibleMeasurablePositiveMassPolicy μ τ ∧ R σ < R τ

/--
Build the explicit zero-mass certificate from the often-convenient complement
form: every feasible policy outside the positive-mass domain is dominated by a
positive-mass feasible policy.
-/
def DynamicZeroMassStrictDominanceCertificate.of_not_positive_mass
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hdom :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicFeasibleMeasurablePolicy σ →
          ¬ dynamicFeasibleMeasurablePositiveMassPolicy μ σ →
            ∃ τ : Fin 2 → TripPolicy,
              dynamicFeasibleMeasurablePositiveMassPolicy μ τ ∧ R σ < R τ) :
    DynamicZeroMassStrictDominanceCertificate μ R where
  improve_zero_mass := by
    intro σ hσ hzero
    exact hdom σ hσ
      (not_dynamicFeasibleMeasurablePositiveMassPolicy_of_zero_mass hzero)

/--
Build the zero-mass certificate from one fixed positive-mass witness that
strictly dominates every feasible zero-mass policy.
-/
def DynamicZeroMassStrictDominanceCertificate.of_fixed_witness
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (τ : Fin 2 → TripPolicy)
    (hτ : dynamicFeasibleMeasurablePositiveMassPolicy μ τ)
    (hdom :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicFeasibleMeasurablePolicy σ →
          dynamicHasZeroAcceptedMass μ σ →
            R σ < R τ) :
    DynamicZeroMassStrictDominanceCertificate μ R where
  improve_zero_mass := by
    intro σ hσ hzero
    exact ⟨τ, hτ, hdom σ hσ hzero⟩

/--
Accept-all specialization of the fixed-witness constructor.  This is the
paper-facing zero-mass route for GN21: after proving accept-all has positive
mass in both states, it remains only to prove every feasible zero-mass policy
has lower total reward than accept-all under the chosen reward interface.
-/
def DynamicZeroMassStrictDominanceCertificate.of_acceptAll_dominates_zero_mass
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hmass_acceptAll :
      ∀ i : Fin 2, 0 < singleStateTripMass (μ i) acceptAllPolicy)
    (hdom :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicFeasibleMeasurablePolicy σ →
          dynamicHasZeroAcceptedMass μ σ →
            R σ < R acceptAllDynamicPolicy) :
    DynamicZeroMassStrictDominanceCertificate μ R :=
  DynamicZeroMassStrictDominanceCertificate.of_fixed_witness
    acceptAllDynamicPolicy
    (dynamicFeasibleMeasurablePositiveMassPolicy_acceptAll hmass_acceptAll)
    hdom

/--
If a feasible zero-mass policy strictly beats accept-all while accept-all is
already optimal on the positive-mass source domain, then no zero-mass strict
dominance certificate can exist.  This records the logical obstruction behind
the GN21 totalized-reward boundary.
-/
theorem not_DynamicZeroMassStrictDominanceCertificate_of_zero_mass_policy_beats_acceptAll
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    {σ : Fin 2 → TripPolicy}
    (hposIC : dynamicPositiveMassMeasurableIncentiveCompatible μ R)
    (hσ : dynamicFeasibleMeasurablePolicy σ)
    (hσ_zero : dynamicHasZeroAcceptedMass μ σ)
    (hgt : R acceptAllDynamicPolicy < R σ) :
    ¬ DynamicZeroMassStrictDominanceCertificate μ R := by
  intro hzero
  rcases hzero.improve_zero_mass σ hσ hσ_zero with
    ⟨τ, hτ_pos, hσ_lt_τ⟩
  have hτ_le_accept : R τ ≤ R acceptAllDynamicPolicy := hposIC.2 τ hτ_pos
  linarith

/--
A dynamic reward whose value is defined only on the denominator-valid
positive-mass feasible source domain.
-/
structure DynamicDefinedReward
    (μ : Fin 2 → Measure TripLength) where
  value :
    (σ : Fin 2 → TripPolicy) →
      dynamicFeasibleMeasurablePositiveMassPolicy μ σ → ℝ

/-- The optional value of a defined reward at an arbitrary dynamic policy. -/
noncomputable def DynamicDefinedReward.value?
    {μ : Fin 2 → Measure TripLength}
    (R : DynamicDefinedReward μ)
    (σ : Fin 2 → TripPolicy) : Option ℝ := by
  classical
  exact
    if hσ : dynamicFeasibleMeasurablePositiveMassPolicy μ σ then
      some (R.value σ hσ)
    else
      none

/-- Order an optional reward value against a real benchmark. -/
def optionRewardLe (x : Option ℝ) (y : ℝ) : Prop := ∀ r : ℝ, x = some r → r ≤ y

/--
Defined-reward measurable optimality: the target is positive-mass feasible, and
every feasible measurable policy with a defined positive-mass reward is no
better than the target.  Feasible zero-mass policies have no reward value here
rather than a totalized real quotient value.
-/
def dynamicDefinedMeasurableOptimal
    {μ : Fin 2 → Measure TripLength}
    (R : DynamicDefinedReward μ)
    (σstar : Fin 2 → TripPolicy) : Prop :=
  ∃ hstar : dynamicFeasibleMeasurablePositiveMassPolicy μ σstar,
    ∀ σ : Fin 2 → TripPolicy,
      dynamicFeasibleMeasurablePolicy σ →
        optionRewardLe (R.value? σ) (R.value σstar hstar)

/--
Defined-reward measurable IC: accepting all trips is optimal for the partial
reward surface.
-/
def dynamicDefinedMeasurableIncentiveCompatible
    {μ : Fin 2 → Measure TripLength}
    (R : DynamicDefinedReward μ) : Prop := dynamicDefinedMeasurableOptimal R acceptAllDynamicPolicy

/-- View an ordinary total dynamic reward as a reward defined on positive-mass policies. -/
def DynamicDefinedReward.of_total
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) : DynamicDefinedReward μ where
  value := fun σ _hσ => R σ

/--
Positive-mass measurable optimality immediately gives defined-reward optimality
for any partial reward interface that agrees with the total reward on the
positive-mass source domain.
-/
theorem dynamicDefinedMeasurableOptimal_of_positiveMass_agree
    {μ : Fin 2 → Measure TripLength}
    {Rtot : DynamicReward}
    {Rdef : DynamicDefinedReward μ}
    {σstar : Fin 2 → TripPolicy}
    (hposOpt : dynamicPositiveMassMeasurableOptimal μ Rtot σstar)
    (hagree :
      ∀ σ hσ, Rdef.value σ hσ = Rtot σ) :
    dynamicDefinedMeasurableOptimal Rdef σstar := by
  classical
  refine ⟨hposOpt.1, ?_⟩
  intro σ _hσ r hr
  by_cases hσ_pos : dynamicFeasibleMeasurablePositiveMassPolicy μ σ
  · have hr' : some (Rdef.value σ hσ_pos) = some r := by
      simpa [DynamicDefinedReward.value?, hσ_pos] using hr
    have hreq : Rdef.value σ hσ_pos = r := Option.some.inj hr'
    rw [← hreq]
    rw [hagree σ hσ_pos, hagree σstar hposOpt.1]
    exact hposOpt.2 σ hσ_pos
  · simpa [DynamicDefinedReward.value?, hσ_pos] using hr

/--
Positive-mass measurable optimality immediately gives defined-reward optimality
for the corresponding total reward viewed through the partial interface.
-/
theorem dynamicDefinedMeasurableOptimal_of_positiveMass
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    {σstar : Fin 2 → TripPolicy}
    (hposOpt : dynamicPositiveMassMeasurableOptimal μ R σstar) :
    dynamicDefinedMeasurableOptimal
      (DynamicDefinedReward.of_total μ R) σstar :=
  dynamicDefinedMeasurableOptimal_of_positiveMass_agree hposOpt
    (by intro σ hσ; rfl)

/--
Positive-mass measurable IC immediately gives defined-reward IC for any partial
reward interface that agrees with the total reward on the positive-mass source
domain.
-/
theorem dynamicDefinedMeasurableIncentiveCompatible_of_positiveMass_agree
    {μ : Fin 2 → Measure TripLength}
    {Rtot : DynamicReward}
    {Rdef : DynamicDefinedReward μ}
    (hposIC : dynamicPositiveMassMeasurableIncentiveCompatible μ Rtot)
    (hagree :
      ∀ σ hσ, Rdef.value σ hσ = Rtot σ) :
    dynamicDefinedMeasurableIncentiveCompatible Rdef := dynamicDefinedMeasurableOptimal_of_positiveMass_agree hposIC hagree

/--
Positive-mass measurable IC immediately gives defined-reward IC for the
corresponding partial reward interface.  This is the source-faithful alternative
to assigning arbitrary totalized real values to zero-mass denominator failures.
-/
theorem dynamicDefinedMeasurableIncentiveCompatible_of_positiveMass
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hposIC : dynamicPositiveMassMeasurableIncentiveCompatible μ R) :
    dynamicDefinedMeasurableIncentiveCompatible
      (DynamicDefinedReward.of_total μ R) :=
  dynamicDefinedMeasurableIncentiveCompatible_of_positiveMass_agree hposIC
    (by intro σ hσ; rfl)

/--
A defined-reward optimum whose partial reward agrees with a total reward is also
a positive-mass optimum for that total reward.
-/
theorem dynamicPositiveMassMeasurableOptimal_of_dynamicDefinedMeasurableOptimal_agree
    {μ : Fin 2 → Measure TripLength}
    {Rtot : DynamicReward}
    {Rdef : DynamicDefinedReward μ}
    {σstar : Fin 2 → TripPolicy}
    (hdefOpt :
      dynamicDefinedMeasurableOptimal Rdef σstar)
    (hagree :
      ∀ σ hσ, Rdef.value σ hσ = Rtot σ) :
    dynamicPositiveMassMeasurableOptimal μ Rtot σstar := by
  classical
  rcases hdefOpt with ⟨hstar_pos, hle⟩
  refine ⟨hstar_pos, ?_⟩
  intro σ hσ_pos
  have hle_def :
      Rdef.value σ hσ_pos ≤ Rdef.value σstar hstar_pos :=
    hle σ hσ_pos.1 (Rdef.value σ hσ_pos) (by
      simp [DynamicDefinedReward.value?, hσ_pos])
  rwa [hagree σ hσ_pos, hagree σstar hstar_pos] at hle_def

/--
A defined-reward optimum for a total reward viewed partially is also a
positive-mass optimum for the original reward.
-/
theorem dynamicPositiveMassMeasurableOptimal_of_dynamicDefinedMeasurableOptimal
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    {σstar : Fin 2 → TripPolicy}
    (hdefOpt :
      dynamicDefinedMeasurableOptimal
        (DynamicDefinedReward.of_total μ R) σstar) :
    dynamicPositiveMassMeasurableOptimal μ R σstar :=
  dynamicPositiveMassMeasurableOptimal_of_dynamicDefinedMeasurableOptimal_agree
    hdefOpt (by intro σ hσ; rfl)

/--
Positive-mass a.e. uniqueness transfers to defined-reward optima for the same
total reward viewed through the partial reward interface.
-/
theorem dynamicAcceptAllAlmostEverywhere_of_dynamicDefinedMeasurableOptimal
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hAE :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ)
    {ρ : Fin 2 → TripPolicy}
    (hρ :
      dynamicDefinedMeasurableOptimal
        (DynamicDefinedReward.of_total μ R) ρ) :
    dynamicAcceptAllAlmostEverywhere μ ρ :=
  hAE ρ
    (dynamicPositiveMassMeasurableOptimal_of_dynamicDefinedMeasurableOptimal
      hρ)

/--
Positive-mass measurable IC lifts to full feasible-measurable IC once every
zero-mass feasible policy is strictly dominated by a positive-mass feasible
policy.
-/
theorem dynamicMeasurableIncentiveCompatible_of_positiveMass_and_zeroMassStrictDominance
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hposIC : dynamicPositiveMassMeasurableIncentiveCompatible μ R)
    (hzero : DynamicZeroMassStrictDominanceCertificate μ R) :
    dynamicMeasurableIncentiveCompatible R := by
  constructor
  · exact hposIC.1.1
  · intro σ hσ
    by_cases hσ_zero : dynamicHasZeroAcceptedMass μ σ
    · rcases hzero.improve_zero_mass σ hσ hσ_zero with
        ⟨τ, hτ_pos, hlt⟩
      have hτ_le_accept :
          R τ ≤ R acceptAllDynamicPolicy := hposIC.2 τ hτ_pos
      linarith
    · have hσ_pos :
          dynamicFeasibleMeasurablePositiveMassPolicy μ σ :=
        dynamicFeasibleMeasurablePositiveMassPolicy_of_no_zero_mass
          hσ hσ_zero
      exact hposIC.2 σ hσ_pos

/--
A full feasible-measurable optimum belongs to the positive-mass source domain
under the same zero-mass strict-dominance certificate.
-/
theorem dynamicPositiveMassMeasurableOptimal_of_dynamicMeasurableOptimal_of_zeroMassStrictDominance
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    {σ : Fin 2 → TripPolicy}
    (hzero : DynamicZeroMassStrictDominanceCertificate μ R)
    (hσ : dynamicMeasurableOptimal R σ) :
    dynamicPositiveMassMeasurableOptimal μ R σ := by
  by_cases hσ_zero : dynamicHasZeroAcceptedMass μ σ
  · rcases hzero.improve_zero_mass σ hσ.1 hσ_zero with
      ⟨τ, hτ_pos, hlt⟩
    have hτ_le_σ : R τ ≤ R σ := hσ.2 τ hτ_pos.1
    linarith
  · constructor
    · exact
        dynamicFeasibleMeasurablePositiveMassPolicy_of_no_zero_mass
          hσ.1 hσ_zero
    · intro τ hτ_pos
      exact hσ.2 τ hτ_pos.1

/--
Positive-mass measurable IC plus positive-mass a.e. uniqueness lifts to the
full feasible-measurable a.e.-unique conclusion under zero-mass strict
dominance.
-/
theorem dynamicMeasurableICAEUnique_of_positiveMass_ae_unique_and_zeroMassStrictDominance
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hposIC : dynamicPositiveMassMeasurableIncentiveCompatible μ R)
    (hposAE :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ)
    (hzero : DynamicZeroMassStrictDominanceCertificate μ R) :
    dynamicMeasurableIncentiveCompatible R ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  refine
    ⟨dynamicMeasurableIncentiveCompatible_of_positiveMass_and_zeroMassStrictDominance
      hposIC hzero, ?_⟩
  intro ρ hρ
  exact hposAE ρ
    (dynamicPositiveMassMeasurableOptimal_of_dynamicMeasurableOptimal_of_zeroMassStrictDominance
      hzero hρ)

/--
Positive-mass analogue of the measurable positive-response marginal
certificate.  This is the same Lemma-5 endpoint as the full certificate, but
the optimizers quantified over are restricted to the nondegenerate source
domain where the Appendix-D reward-rate formulas are defined.
-/
structure Theorem4PositiveMassMeasurablePositiveResponseAEMarginalCertificate
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) where
  accept_all_optimal : dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy
  nonsurge_marginal_optimal :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 0) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          (∀ τ : TripPolicy,
            τ ⊆ acceptAllPolicy →
            MeasurableSet τ →
              lemma5MarginalSetReward (μ 0) response τ ≤
                lemma5MarginalSetReward (μ 0) response (ρ 0))
  surge_marginal_optimal :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 1) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          (∀ τ : TripPolicy,
            τ ⊆ acceptAllPolicy →
            MeasurableSet τ →
              lemma5MarginalSetReward (μ 1) response τ ≤
                lemma5MarginalSetReward (μ 1) response (ρ 1))

/--
Positive-response marginal optimality gives a.e. accept-all uniqueness inside
the positive-mass measurable source domain.
-/
theorem paper_theorem4_positive_mass_measurable_accept_all_ae_unique_optimal_of_positive_response_marginal_optima
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (C :
      Theorem4PositiveMassMeasurablePositiveResponseAEMarginalCertificate
        μ R) :
    dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  refine ⟨C.accept_all_optimal, ?_⟩
  intro ρ hρ i
  fin_cases i
  · rcases C.nonsurge_marginal_optimal ρ hρ with
      ⟨response, hmeas, hint, hpositive, hoptimal⟩
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_feasible_optimal
        (μ 0) response (ρ 0) hmeas hint (hρ.1.1 0).2 (hρ.1.1 0).1
        hpositive hoptimal
  · rcases C.surge_marginal_optimal ρ hρ with
      ⟨response, hmeas, hint, hpositive, hoptimal⟩
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_feasible_optimal
        (μ 1) response (ρ 1) hmeas hint (hρ.1.1 1).2 (hρ.1.1 1).1
        hpositive hoptimal

/--
Positive-mass analogue of the accept-all-candidate positive-response
certificate.  This weaker Lemma-5 interface is enough for a.e. uniqueness and
only compares each positive-mass optimum with the accept-all candidate.
-/
structure Theorem4PositiveMassMeasurablePositiveResponseAEAcceptAllCandidateCertificate
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) where
  accept_all_optimal : dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy
  nonsurge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 0) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          lemma5MarginalSetReward (μ 0) response acceptAllPolicy ≤
            lemma5MarginalSetReward (μ 0) response (ρ 0)
  surge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 1) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          lemma5MarginalSetReward (μ 1) response acceptAllPolicy ≤
            lemma5MarginalSetReward (μ 1) response (ρ 1)

/--
Accept-all candidate comparisons give a.e. accept-all uniqueness inside the
positive-mass measurable source domain.
-/
theorem paper_theorem4_positive_mass_measurable_accept_all_ae_unique_optimal_of_positive_response_acceptAll_candidates
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (C :
      Theorem4PositiveMassMeasurablePositiveResponseAEAcceptAllCandidateCertificate
        μ R) :
    dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  refine ⟨C.accept_all_optimal, ?_⟩
  intro ρ hρ i
  fin_cases i
  · rcases C.nonsurge_acceptAll_candidate ρ hρ with
      ⟨response, hmeas, hint, hpositive, hcandidate⟩
    have hpositive_eq :
        lemma5PositiveResponsePolicy response = acceptAllPolicy :=
      eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
        (lemma5PositiveResponsePolicy_subset_acceptAll response)
        hpositive
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
        (μ 0) response (ρ 0) hmeas hint (hρ.1.1 0).2 (hρ.1.1 0).1
        hpositive (by simpa [hpositive_eq] using hcandidate)
  · rcases C.surge_acceptAll_candidate ρ hρ with
      ⟨response, hmeas, hint, hpositive, hcandidate⟩
    have hpositive_eq :
        lemma5PositiveResponsePolicy response = acceptAllPolicy :=
      eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
        (lemma5PositiveResponsePolicy_subset_acceptAll response)
        hpositive
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
        (μ 1) response (ρ 1) hmeas hint (hρ.1.1 1).2 (hρ.1.1 1).1
        hpositive (by simpa [hpositive_eq] using hcandidate)

/--
Candidate-only version of the positive-mass positive-response certificate.
This omits accept-all optimality because Theorem 3's positive-mass IC
construction can supply that separately; for a.e. uniqueness, the proof only
needs the statewise accept-all candidate comparisons.
-/
structure Theorem4PositiveMassMeasurablePositiveResponseAEAcceptAllCandidateUniquenessCertificate
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) where
  nonsurge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 0) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          lemma5MarginalSetReward (μ 0) response acceptAllPolicy ≤
            lemma5MarginalSetReward (μ 0) response (ρ 0)
  surge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 1) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          lemma5MarginalSetReward (μ 1) response acceptAllPolicy ≤
            lemma5MarginalSetReward (μ 1) response (ρ 1)

/--
Candidate comparisons alone give a.e. accept-all uniqueness for positive-mass
measurable optima.
-/
theorem positiveMassMeasurable_acceptAll_ae_unique_of_positive_response_acceptAll_candidates
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (C :
      Theorem4PositiveMassMeasurablePositiveResponseAEAcceptAllCandidateUniquenessCertificate
        μ R) :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicPositiveMassMeasurableOptimal μ R ρ →
        dynamicAcceptAllAlmostEverywhere μ ρ := by
  intro ρ hρ i
  fin_cases i
  · rcases C.nonsurge_acceptAll_candidate ρ hρ with
      ⟨response, hmeas, hint, hpositive, hcandidate⟩
    have hpositive_eq :
        lemma5PositiveResponsePolicy response = acceptAllPolicy :=
      eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
        (lemma5PositiveResponsePolicy_subset_acceptAll response)
        hpositive
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
        (μ 0) response (ρ 0) hmeas hint (hρ.1.1 0).2 (hρ.1.1 0).1
        hpositive (by simpa [hpositive_eq] using hcandidate)
  · rcases C.surge_acceptAll_candidate ρ hρ with
      ⟨response, hmeas, hint, hpositive, hcandidate⟩
    have hpositive_eq :
        lemma5PositiveResponsePolicy response = acceptAllPolicy :=
      eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
        (lemma5PositiveResponsePolicy_subset_acceptAll response)
        hpositive
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
        (μ 1) response (ρ 1) hmeas hint (hρ.1.1 1).2 (hρ.1.1 1).1
        hpositive (by simpa [hpositive_eq] using hcandidate)

/--
Sequential positive-response certificate for the paper's Theorem 3 route.  It
first proves the surge state is accept-all a.e. at the current fixed non-surge
policy; after that rewrite, the non-surge Lemma 10 comparison is only required
with the surge state fixed at exact accept-all.
-/
structure Theorem4PositiveMassMeasurableSequentialPositiveResponseAEAcceptAllCandidateCertificate
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) where
  surge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 1) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          lemma5MarginalSetReward (μ 1) response acceptAllPolicy ≤
            lemma5MarginalSetReward (μ 1) response (ρ 1)
  nonsurge_after_surge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicPositiveMassMeasurableOptimal μ R ρ →
        acceptAllAlmostEverywhere (μ 1) (ρ 1) →
          ∃ response : TripLength → ℝ,
            Measurable response ∧
              IntegrableOn response acceptAllPolicy (μ 0) ∧
              lemma5PolicyForm .positive
                (lemma5PositiveResponsePolicy response) ∧
              lemma5MarginalSetReward (μ 0) response acceptAllPolicy ≤
                lemma5MarginalSetReward (μ 0) response (ρ 0)

/--
Sequential statewise candidate comparisons give a.e. accept-all uniqueness in
the positive-mass measurable source domain.
-/
theorem positiveMassMeasurable_acceptAll_ae_unique_of_sequential_positive_response_acceptAll_candidates
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (C :
      Theorem4PositiveMassMeasurableSequentialPositiveResponseAEAcceptAllCandidateCertificate
        μ R) :
    ∀ ρ : Fin 2 → TripPolicy,
      dynamicPositiveMassMeasurableOptimal μ R ρ →
        dynamicAcceptAllAlmostEverywhere μ ρ := by
  intro ρ hρ
  rcases C.surge_acceptAll_candidate ρ hρ with
    ⟨response1, hmeas1, hint1, hpositive1, hcandidate1⟩
  have hpositive1_eq :
      lemma5PositiveResponsePolicy response1 = acceptAllPolicy :=
    eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
      (lemma5PositiveResponsePolicy_subset_acceptAll response1)
      hpositive1
  have hsurge :
      acceptAllAlmostEverywhere (μ 1) (ρ 1) :=
    acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
      (μ 1) response1 (ρ 1) hmeas1 hint1 (hρ.1.1 1).2 (hρ.1.1 1).1
      hpositive1 (by simpa [hpositive1_eq] using hcandidate1)
  rcases C.nonsurge_after_surge_acceptAll_candidate ρ hρ hsurge with
    ⟨response0, hmeas0, hint0, hpositive0, hcandidate0⟩
  have hpositive0_eq :
      lemma5PositiveResponsePolicy response0 = acceptAllPolicy :=
    eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
      (lemma5PositiveResponsePolicy_subset_acceptAll response0)
      hpositive0
  have hnonsurge :
      acceptAllAlmostEverywhere (μ 0) (ρ 0) :=
    acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
      (μ 0) response0 (ρ 0) hmeas0 hint0 (hρ.1.1 0).2 (hρ.1.1 0).1
      hpositive0 (by simpa [hpositive0_eq] using hcandidate0)
  intro i
  fin_cases i
  · exact hnonsurge
  · exact hsurge

/--
Positive-mass Theorem 3 marginal-response certificate.  This is the source
Theorem 4/Lemma 5 boundary restricted to the denominator-valid domain: after
Theorem 3 constructs `m,z`, every positive-mass measurable optimum has the
positive marginal-response data needed for a.e. accept-all uniqueness.
-/
def theorem3AcceptAllPositiveMassPositiveResponseAEMarginalCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∀ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z →
        Theorem4PositiveMassMeasurablePositiveResponseAEMarginalCertificate μ
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z)

/--
Positive-mass Theorem 3 candidate-only positive-response certificate.  This
is the weakest Lemma 5 a.e.-uniqueness boundary: after Theorem 3 constructs
`m,z`, every positive-mass measurable optimum has the positive-response
accept-all candidate comparisons in both states.
-/
def theorem3AcceptAllPositiveMassPositiveResponseAEAcceptAllCandidateCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∀ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z →
        Theorem4PositiveMassMeasurablePositiveResponseAEAcceptAllCandidateUniquenessCertificate μ
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z)

/--
Positive-mass Theorem 3 sequential candidate certificate.  This matches the
paper proof order: first prove the surge state is accept-all a.e.; then use
the non-surge Lemma 10 comparison with the surge state fixed at accept-all.
-/
def theorem3AcceptAllPositiveMassSequentialPositiveResponseAEAcceptAllCandidateCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∀ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z →
        Theorem4PositiveMassMeasurableSequentialPositiveResponseAEAcceptAllCandidateCertificate μ
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z)

/--
The canonical positive-mass sequential reward-rate source assumptions supply
the sequential positive-response uniqueness certificate for the prices
constructed by Theorem 3.
-/
noncomputable def theorem3AcceptAllPositiveMassSequentialPositiveResponseAEAcceptAllCandidateCertificate_of_source_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3AcceptAllPositiveMassSequentialPositiveResponseAEAcceptAllCandidateCertificate
      μ arrival R1 R2 switch12 switch21 := by
  intro m z hsigns hparams
  let P : Theorem3AcceptAllStructuredParameterData
      μ arrival R1 R2 switch12 switch21 m z :=
    Theorem3AcceptAllStructuredParameterData.of_evidence hparams
  let w : Fin 2 → PricingFunction :=
    ctmcStructuredDynamicSurgePrice m z switch12 switch21
  let R : DynamicReward :=
    gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w
  have hmass_acceptAll :
      ∀ i : Fin 2, 0 < singleStateTripMass (μ i) acceptAllPolicy := by
    intro i
    fin_cases i
    · exact A.hmass1_pos
    · exact A.hmass2_pos
  have current_nondegenerate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          GN21MeasuredPairNondegenerate (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21 (ρ 0) (ρ 1) := by
    intro ρ hρ
    exact
      gn21MeasuredPairNondegenerate_of_positive_measure
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ρ 0) (ρ 1) (hρ.1.2 0) (hρ.1.2 1) A.harrival1_pos
        A.harrival2_pos A.hswitch12_pos A.hswitch21_pos
        (hρ.1.1 0).2 (hρ.1.1 1).2 (hρ.1.1 0).1 (hρ.1.1 1).1
  have acceptAll_nondegenerate :
      GN21MeasuredPairNondegenerate (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21
        acceptAllPolicy acceptAllPolicy :=
    gn21MeasuredPairNondegenerate_of_positive_measure
      (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
      acceptAllPolicy acceptAllPolicy A.hmass1_pos A.hmass2_pos
      A.harrival1_pos A.harrival2_pos A.hswitch12_pos A.hswitch21_pos
      measurableSet_acceptAllPolicy measurableSet_acceptAllPolicy
      (fun _ hτ => hτ) (fun _ hτ => hτ)
  have nonsurge_current_acceptAll_nondegenerate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          GN21MeasuredPairNondegenerate (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (ρ 0) acceptAllPolicy := by
    intro ρ hρ
    exact
      gn21MeasuredPairNondegenerate_of_positive_measure
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ρ 0) acceptAllPolicy (hρ.1.2 0) A.hmass2_pos
        A.harrival1_pos A.harrival2_pos A.hswitch12_pos
        A.hswitch21_pos (hρ.1.1 0).2 measurableSet_acceptAllPolicy
        (hρ.1.1 0).1 (fun _ hτ => hτ)
  have surge_acceptAll_nondegenerate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          GN21MeasuredPairNondegenerate (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (ρ 0) acceptAllPolicy := by
    intro ρ hρ
    exact
      gn21MeasuredPairNondegenerate_of_positive_measure
        (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
        (ρ 0) acceptAllPolicy (hρ.1.2 0) A.hmass2_pos
        A.harrival1_pos A.harrival2_pos A.hswitch12_pos
        A.hswitch21_pos (hρ.1.1 0).2 measurableSet_acceptAllPolicy
        (hρ.1.1 0).1 (fun _ hτ => hτ)
  refine
    { surge_acceptAll_candidate := ?_
      nonsurge_after_surge_acceptAll_candidate := ?_ }
  · intro ρ hρctmc
    have hρ : dynamicPositiveMassMeasurableOptimal μ R ρ := by
      simpa [R, w, gn21MeasuredCTMCStructuredDynamicReward] using hρctmc
    rcases A.surge_reward_rate_data m z hsigns hparams ρ hρ.1 with
      ⟨R1_current, ratio, DSrr⟩
    have hmassI : singleStateTripMass (μ 0) (ρ 0) ≠ 0 :=
      ne_of_gt (hρ.1.2 0)
    have harrivalMassI :
        arrival 0 * singleStateTripMass (μ 0) (ρ 0) ≠ 0 :=
      mul_ne_zero (ne_of_gt A.harrival1_pos) hmassI
    have htimeI_pos :
        0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
      gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
        (le_of_lt A.harrival1_pos) (hρ.1.1 0).2 (hρ.1.1 0).1
    have DSsrc :
        GN21SurgeLemma9AcceptAllAggregateSourceData
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (m 1) R1_current (z 1) ratio
          (ctmcStructuredSurgePrice (m 0) (z 0) switch12 switch21)
          (ρ 0) (ρ 1) :=
      GN21SurgeLemma9AcceptAllAggregateSourceData.of_reward_rate
        hmassI harrivalMassI (ne_of_gt htimeI_pos) DSrr
    let DP :
        GN21SurgeLemma9AcceptAllAggregatePrimitiveData
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (m 1) R1_current (z 1) ratio
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ρ 0) (ρ 1) :=
      GN21SurgeLemma9AcceptAllAggregatePrimitiveData.of_source
        (hρ.1.1 0).1 (hρ.1.1 0).2 (hρ.1.1 1).1 (hρ.1.1 1).2
        A.harrival1_pos A.harrival2_pos A.hswitch12_pos A.hswitch21_pos
        A.htime2_integrable A.hq2_integrable
        (by
          simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
            using DSsrc)
    let DA := GN21SurgeLemma9AcceptAllAggregateData.of_primitive DP
    let response :=
      gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        (ρ 0) (ρ 1)
    refine ⟨response, ?_, ?_, ?_, ?_⟩
    · simpa [response] using
        measurable_gn21MeasuredRightMarginalResponseAtCurrent
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) (ρ 1)
          ((continuous_ctmcStructuredDynamicSurgePrice m z switch12 switch21
            1).measurable)
    · have hw_acceptAll :
          IntegrableOn
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            acceptAllPolicy (μ 1) := by
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
          ctmcStructuredSurgePrice] using
          integrableOn_ctmcStructuredSurgePrice (μ 1) (m 1) (z 1)
            switch21 switch12 acceptAllPolicy
            A.htime2_integrable A.hq2_integrable
      simpa [response] using
        integrableOn_gn21MeasuredRightMarginalResponseAtCurrent
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) (ρ 1) acceptAllPolicy A.hq2_integrable
          hw_acceptAll A.htime2_integrable
    · have hTj_pos :
          0 < gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
        gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1) (ρ 1)
          (le_of_lt A.harrival2_pos) (hρ.1.1 1).2 (hρ.1.1 1).1
      let Rj :=
        gn21MeasuredStateRewardRate (μ 1) (arrival 1)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1)
      have hWj :
          gn21ScaledStateEarning (μ 1) (arrival 1)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
              (ρ 1) =
            Rj * gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) :=
        gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate
          (μ 1) (arrival 1) Rj
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1) (ρ 1)
          (ne_of_gt DSsrc.current_mass_pos)
          (ne_of_gt (mul_pos A.harrival2_pos DSsrc.current_mass_pos))
          (ne_of_gt hTj_pos) rfl
      have hfixed_reward_rate :
          gn21ScaledStateEarning (μ 0) (arrival 0)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
              (ρ 0) =
            R1_current * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) := by
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
          using DSsrc.fixed_reward_rate
      have hbase :
          Lemma5PositiveResponsePolicyFormData
            (gn21MeasuredRightLemma6ResponseAtCurrent (μ 0) (μ 1)
              (arrival 0) (arrival 1) switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
              (ρ 0) (ρ 1) R1_current Rj) .positive :=
        Lemma5PositiveResponsePolicyFormData.positive
          (gn21MeasuredRightLemma6ResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 0) (ρ 1) R1_current Rj)
          (by
            have hpos :=
              gn21MeasuredRightLemma6ResponseAtCurrent_pos_of_lemma9_current_bounds
                (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
                (m 1) R1_current (z 1) ratio Rj
                (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
                (ρ 0) (ρ 1) DSsrc.bounds DSsrc.z_eq
                DSsrc.m_sub_R1_pos DSsrc.R1_nonneg DA.fixed_time_nonneg
                DA.fixed_exit_pos DA.switch_pos DA.switch_sum_pos
                DA.switch_lt_current_exit DA.current_gap_nonneg
                DP.time_integrable_current DP.q_integrable_current
                htimeI_pos hTj_pos hfixed_reward_rate hWj
            intro τ hτ
            simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb]
              using hpos τ hτ)
      have hscaled :
          Lemma5PositiveResponsePolicyFormData response .positive := by
        simpa [response] using
          gn21MeasuredRightPositiveResponsePolicyFormData_of_scaled_lemma6Response
            (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 0) (ρ 1) R1_current Rj hbase DA.fixed_exit_pos htimeI_pos
            hTj_pos DA.denominator_pos hfixed_reward_rate hWj
      exact hscaled.policy_form
    · have hw_acceptAll :
          IntegrableOn
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            acceptAllPolicy (μ 1) := by
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
          ctmcStructuredSurgePrice] using
          integrableOn_ctmcStructuredSurgePrice (μ 1) (m 1) (z 1)
            switch21 switch12 acceptAllPolicy
            A.htime2_integrable A.hq2_integrable
      have hw_current :
          IntegrableOn
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 1) (μ 1) := by
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
          ctmcStructuredSurgePrice] using
          integrableOn_ctmcStructuredSurgePrice (μ 1) (m 1) (z 1)
            switch21 switch12 (ρ 1) DP.time_integrable_current
            DP.q_integrable_current
      have hQ_acceptAll_pos :
          0 <
            gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
              acceptAllPolicy :=
        gn21ExitWeightIntegral_pos_of_switch_pos (μ 1) (arrival 1)
          switch21 switch12 acceptAllPolicy (le_of_lt A.harrival2_pos)
          A.hswitch21_pos (by linarith [A.hswitch12_pos, A.hswitch21_pos])
          measurableSet_acceptAllPolicy (fun _ hτ => hτ)
      have hT_acceptAll_pos :
          0 < gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy :=
        gn21ScaledStateTime_pos_of_nonneg (μ 1) (arrival 1)
          acceptAllPolicy (le_of_lt A.harrival2_pos)
          measurableSet_acceptAllPolicy (fun _ hτ => hτ)
      have hden_acceptAll_pos :
          0 <
            gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) *
              gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy +
            gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                acceptAllPolicy *
              gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
        gn21AggregateDenominator_pos_of_pos
          (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            (ρ 0))
          (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            acceptAllPolicy)
          (gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
          (gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy)
          DA.fixed_exit_pos hQ_acceptAll_pos htimeI_pos hT_acceptAll_pos
      have hlocal :=
        dynamicStateReward_acceptAll_le_of_dynamicPositiveMassMeasurableOptimal
          μ R hρ hmass_acceptAll 1
      simpa [response, R, w] using
        lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_one_of_local_reward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)
          hlocal A.harrival2_pos (current_nondegenerate ρ hρ)
          (surge_acceptAll_nondegenerate ρ hρ)
          DA.denominator_pos hden_acceptAll_pos A.hq2_integrable
          hw_acceptAll A.htime2_integrable DP.q_integrable_current
          hw_current DP.time_integrable_current
  · intro ρ hρctmc hsurgeAE
    have hρ : dynamicPositiveMassMeasurableOptimal μ R ρ := by
      simpa [R, w, gn21MeasuredCTMCStructuredDynamicReward] using hρctmc
    let ρA : Fin 2 → TripPolicy := Function.update ρ 1 acceptAllPolicy
    have hρ_w :
        dynamicPositiveMassMeasurableOptimal μ
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
          ρ := by
      simpa [R] using hρ
    have hρA :
        dynamicPositiveMassMeasurableOptimal μ R ρA := by
      have htmp :=
        dynamicPositiveMassMeasurableOptimal_gn21MeasuredDynamicRewardFunctional_update_one_acceptAll_of_ae
          μ arrival switch12 switch21 w hρ_w hmass_acceptAll hsurgeAE
      simpa [R, ρA] using htmp
    have hsum21 : 0 < switch21 + switch12 := by
      linarith [A.hswitch21_pos, A.hswitch12_pos]
    have hfixed_exit_pos :
        0 <
          gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            acceptAllPolicy :=
      gn21ExitWeightIntegral_pos_of_switch_pos
        (μ 1) (arrival 1) switch21 switch12 acceptAllPolicy
        (le_of_lt A.harrival2_pos) A.hswitch21_pos hsum21
        measurableSet_acceptAllPolicy (fun _ hτ => hτ)
    have hfixed_time_pos :
        0 < gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy :=
      gn21ScaledStateTime_pos_of_nonneg
        (μ 1) (arrival 1) acceptAllPolicy
        (le_of_lt A.harrival2_pos) measurableSet_acceptAllPolicy
        (fun _ hτ => hτ)
    have hfixed_A_pos :
        0 <
          gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy *
              switch12 +
            gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
              acceptAllPolicy :=
      add_pos (mul_pos hfixed_time_pos A.hswitch12_pos)
        hfixed_exit_pos
    have hfixed_reward_rate :
        gn21ScaledStateEarning (μ 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            acceptAllPolicy =
          R2 * gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy := by
      calc
        gn21ScaledStateEarning (μ 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            acceptAllPolicy
            =
          m 1 *
              (gn21AcceptAllScaledStateTime (μ 1) (arrival 1) - 1) +
            z 1 *
              (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1)
                  switch21 switch12 -
                switch21) := by
              simpa [ctmcStructuredDynamicSurgePrice,
                ctmcDynamicSwitchProb, ctmcStructuredSurgePrice,
                gn21AcceptAllScaledStateTime,
                gn21AcceptAllExitWeightIntegral] using
                paper_remark2_structured_scaled_earning_algebra
                  (μ 1) (arrival 1) (m 1) (z 1) switch21 switch12
                  acceptAllPolicy A.htime2_integrable A.hq2_integrable
        _ = R2 * gn21AcceptAllScaledStateTime (μ 1) (arrival 1) :=
          P.surge_accounting
    have Dsrc :
        ∃ ratio : ℝ,
          GN21NonsurgeLemma10AcceptAllAggregateSourceData
            (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
            R2 (z 0) ratio
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 0) acceptAllPolicy :=
      ⟨P.nonsurgeRatio,
        GN21NonsurgeLemma10AcceptAllAggregateSourceData.of_acceptAll_tightening
          (hρ.1.1 0).1 (hρ.1.1 0).2 A.harrival1_pos
          A.hswitch12_pos A.hswitch21_pos
          (A.htime1_integrable.mono_set (hρ.1.1 0).1)
          (A.hq1_integrable.mono_set (hρ.1.1 0).1)
          A.htime1_integrable A.hq1_integrable
          P.nonsurge_acceptAll_bounds hfixed_A_pos
          (le_of_lt hfixed_exit_pos) (hρ.1.2 0)
          P.hz0 A.hR2_pos hfixed_reward_rate⟩
    rcases Dsrc with ⟨ratio, DN⟩
    let DP :
        GN21NonsurgeLemma10AcceptAllAggregatePrimitiveData
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          R2 (z 0) ratio
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) acceptAllPolicy :=
      GN21NonsurgeLemma10AcceptAllAggregatePrimitiveData.of_source
        (hρ.1.1 0).1 (hρ.1.1 0).2 (fun _ hτ => hτ)
        measurableSet_acceptAllPolicy
        A.harrival1_pos A.harrival2_pos A.hswitch12_pos
        A.hswitch21_pos A.htime1_integrable A.hq1_integrable DN
    let DA := GN21NonsurgeLemma10AcceptAllAggregateData.of_primitive DP
    let response :=
      gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
        (arrival 0) (arrival 1) switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
        (ρ 0) acceptAllPolicy
    refine ⟨response, ?_, ?_, ?_, ?_⟩
    · simpa [response] using
        measurable_gn21MeasuredLeftMarginalResponseAtCurrent
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) acceptAllPolicy
          ((continuous_ctmcStructuredDynamicSurgePrice m z switch12 switch21
            0).measurable)
    · have hw_acceptAll :
          IntegrableOn
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            acceptAllPolicy (μ 0) := by
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
          ctmcStructuredSurgePrice] using
          integrableOn_ctmcStructuredSurgePrice (μ 0) (m 0) (z 0)
            switch12 switch21 acceptAllPolicy
            A.htime1_integrable A.hq1_integrable
      simpa [response] using
        integrableOn_gn21MeasuredLeftMarginalResponseAtCurrent
          (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
          (ρ 0) acceptAllPolicy acceptAllPolicy A.hq1_integrable
          hw_acceptAll A.htime1_integrable
    · have hTi_pos :
          0 < gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
        gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0) (ρ 0)
          (le_of_lt A.harrival1_pos) (hρ.1.1 0).2 (hρ.1.1 0).1
      let Ri :=
        gn21MeasuredStateRewardRate (μ 0) (arrival 0)
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0)
      have hWi :
          gn21ScaledStateEarning (μ 0) (arrival 0)
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
              (ρ 0) =
            Ri * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) :=
        gn21ScaledStateEarning_eq_reward_mul_scaled_time_of_measuredStateRewardRate
          (μ 0) (arrival 0) Ri
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0) (ρ 0)
          (ne_of_gt DN.current_mass_pos)
          (ne_of_gt (mul_pos A.harrival1_pos DN.current_mass_pos))
          (ne_of_gt hTi_pos) rfl
      have hbase :
          Lemma5PositiveResponsePolicyFormData
            (gn21MeasuredLeftLemma6ResponseAtCurrent (μ 0) (μ 1)
              (arrival 0) (arrival 1) switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
              (ρ 0) acceptAllPolicy Ri R2) .positive :=
        Lemma5PositiveResponsePolicyFormData.positive
          (gn21MeasuredLeftLemma6ResponseAtCurrent (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (ρ 0) acceptAllPolicy Ri R2)
          (by
            have hpos :=
              gn21MeasuredLeftLemma6ResponseAtCurrent_pos_of_lemma10_current_bounds
                (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
                R2 (z 0) ratio Ri
                (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
                (ρ 0) acceptAllPolicy DN.bounds DN.z_eq DN.R2_pos
                DA.fixed_exit_pos
                DA.switch_pos DA.switch_sum_pos DA.switch_lt_current_exit
                DA.current_gap_nonneg DA.lower_numerator_pos
                DP.time_integrable_current DP.q_integrable_current
                hTi_pos hfixed_time_pos
                (by
                  simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
                    P.hm0] using hWi)
                DN.fixed_reward_rate
            intro τ hτ
            simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
              P.hm0] using hpos τ hτ)
      have hscaled :
          Lemma5PositiveResponsePolicyFormData response .positive := by
        simpa [response] using
          gn21MeasuredLeftPositiveResponsePolicyFormData_of_scaled_lemma6Response
            (μ 0) (μ 1) (arrival 0) (arrival 1) switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 0) acceptAllPolicy Ri R2 hbase DA.fixed_exit_pos hTi_pos
            hfixed_time_pos DA.denominator_pos hWi DN.fixed_reward_rate
      exact hscaled.policy_form
    · have hw_acceptAll :
          IntegrableOn
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            acceptAllPolicy (μ 0) := by
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
          ctmcStructuredSurgePrice] using
          integrableOn_ctmcStructuredSurgePrice (μ 0) (m 0) (z 0)
            switch12 switch21 acceptAllPolicy
            A.htime1_integrable A.hq1_integrable
      have hw_current :
          IntegrableOn
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (ρ 0) (μ 0) := by
        simpa [ctmcStructuredDynamicSurgePrice, ctmcDynamicSwitchProb,
          ctmcStructuredSurgePrice] using
          integrableOn_ctmcStructuredSurgePrice (μ 0) (m 0) (z 0)
            switch12 switch21 (ρ 0) DP.time_integrable_current
            DP.q_integrable_current
      have hsum12 : 0 < switch12 + switch21 := by
        linarith [A.hswitch12_pos, A.hswitch21_pos]
      have hQ_acceptAll_pos :
          0 <
            gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
              acceptAllPolicy :=
        gn21ExitWeightIntegral_pos_of_switch_pos (μ 0) (arrival 0)
          switch12 switch21 acceptAllPolicy (le_of_lt A.harrival1_pos)
          A.hswitch12_pos hsum12 measurableSet_acceptAllPolicy
          (fun _ hτ => hτ)
      have hT_acceptAll_pos :
          0 < gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy :=
        gn21ScaledStateTime_pos_of_nonneg (μ 0) (arrival 0)
          acceptAllPolicy (le_of_lt A.harrival1_pos)
          measurableSet_acceptAllPolicy (fun _ hτ => hτ)
      have hden_acceptAll_pos :
          0 <
            gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                acceptAllPolicy *
              gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy +
            gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                acceptAllPolicy *
              gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy :=
        gn21AggregateDenominator_pos_of_pos
          (gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
            acceptAllPolicy)
          (gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
            acceptAllPolicy)
          (gn21ScaledStateTime (μ 0) (arrival 0) acceptAllPolicy)
          (gn21ScaledStateTime (μ 1) (arrival 1) acceptAllPolicy)
          hQ_acceptAll_pos hfixed_exit_pos hT_acceptAll_pos hfixed_time_pos
      have hlocal :=
        dynamicStateReward_acceptAll_le_of_dynamicPositiveMassMeasurableOptimal
          μ R hρA hmass_acceptAll 0
      have HcurrentA :
          GN21MeasuredPairNondegenerate (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            (ρA 0) (ρA 1) := by
        simpa [ρA] using nonsurge_current_acceptAll_nondegenerate ρ hρ
      have HacceptAllA :
          GN21MeasuredPairNondegenerate (μ 0) (μ 1)
            (arrival 0) (arrival 1) switch12 switch21
            acceptAllPolicy (ρA 1) := by
        simpa [ρA] using acceptAll_nondegenerate
      simpa [response, R, w, ρA] using
        lemma5MarginalSetReward_acceptAll_le_of_gn21MeasuredDynamicRewardFunctional_zero_of_local_reward
          μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)
          hlocal A.harrival1_pos HcurrentA HacceptAllA
          DA.denominator_pos hden_acceptAll_pos A.hq1_integrable
          hw_acceptAll A.htime1_integrable DP.q_integrable_current
          hw_current DP.time_integrable_current

/--
Readable positive-mass source-domain conclusion of Theorem 3 with the paper's
a.e. uniqueness convention restricted to positive-mass measurable optima.
-/
def theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∃ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
      dynamicPositiveMassMeasurableIncentiveCompatible μ
        (gn21MeasuredCTMCStructuredDynamicReward
          μ arrival switch12 switch21 m z) ∧
      (∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ) ∧
      (∃ q : Fin 2 → TripLength → ℝ,
        ∀ i τ,
          ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
            structuredSurgePrice (m i) (z i) (q i) τ) ∧
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z

/--
Theorem 3 conclusion over the partial defined-reward interface: accept-all is
IC among policies whose positive-mass reward is defined, and every
defined-reward optimum is accept-all a.e.
-/
def theorem3MeasuredStructuredDefinedMeasurableICAEUniqueConclusion
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∃ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
      dynamicDefinedMeasurableIncentiveCompatible
        (DynamicDefinedReward.of_total μ
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z)) ∧
      (∀ ρ : Fin 2 → TripPolicy,
        dynamicDefinedMeasurableOptimal
          (DynamicDefinedReward.of_total μ
            (gn21MeasuredCTMCStructuredDynamicReward
              μ arrival switch12 switch21 m z)) ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ) ∧
      (∃ q : Fin 2 → TripLength → ℝ,
        ∀ i τ,
          ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
            structuredSurgePrice (m i) (z i) (q i) τ) ∧
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z

/-- The positive-mass a.e.-unique conclusion contains the positive-mass IC conclusion. -/
theorem theorem3MeasuredStructuredPositiveMassMeasurableICConclusion_of_ae_unique
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hIC, _hAE, hprice_form, hparams⟩
  exact ⟨m, z, hsigns, hIC, hprice_form, hparams⟩

/--
The positive-mass Theorem 3 endpoint induces the defined-reward Theorem 3
endpoint by leaving zero-mass denominator failures outside the reward domain.
-/
theorem theorem3MeasuredStructuredDefinedMeasurableICAEUniqueConclusion_of_positiveMass
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredDefinedMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hIC, hAE, hprice_form, hparams⟩
  exact
    ⟨m, z, hsigns,
      dynamicDefinedMeasurableIncentiveCompatible_of_positiveMass hIC,
      (fun ρ hρ =>
        dynamicAcceptAllAlmostEverywhere_of_dynamicDefinedMeasurableOptimal
          hAE hρ),
      hprice_form, hparams⟩

/--
Add the positive-mass a.e.-unique Theorem 4 conclusion to any compiled
positive-mass Theorem 3 IC construction.  This avoids redoing the scalar
Theorem 3 price construction: the marginal-response certificate is checked
only for the already-constructed `m,z`.
-/
theorem theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_positive_response_marginal
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
        μ arrival R1 R2 switch12 switch21)
    (hpositive_marginal :
      theorem3AcceptAllPositiveMassPositiveResponseAEMarginalCertificate
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hIC, hprice_form, hparams⟩
  let R : DynamicReward :=
    gn21MeasuredCTMCStructuredDynamicReward
      μ arrival switch12 switch21 m z
  have htheorem4 :
      dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicPositiveMassMeasurableOptimal μ R ρ →
            dynamicAcceptAllAlmostEverywhere μ ρ :=
    paper_theorem4_positive_mass_measurable_accept_all_ae_unique_optimal_of_positive_response_marginal_optima
      μ R (hpositive_marginal m z hsigns hparams)
  exact ⟨m, z, hsigns, hIC, by simpa [R] using htheorem4.2,
    hprice_form, hparams⟩

/--
Add positive-mass a.e. uniqueness to a compiled positive-mass Theorem 3 IC
construction using only the statewise accept-all candidate comparisons.
-/
theorem theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_positive_response_acceptAll_candidates
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
        μ arrival R1 R2 switch12 switch21)
    (hpositive_candidates :
      theorem3AcceptAllPositiveMassPositiveResponseAEAcceptAllCandidateCertificate
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hIC, hprice_form, hparams⟩
  let R : DynamicReward :=
    gn21MeasuredCTMCStructuredDynamicReward
      μ arrival switch12 switch21 m z
  have hAE :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ :=
    positiveMassMeasurable_acceptAll_ae_unique_of_positive_response_acceptAll_candidates
      μ R (hpositive_candidates m z hsigns hparams)
  exact ⟨m, z, hsigns, hIC, by simpa [R] using hAE,
    hprice_form, hparams⟩

/--
Add positive-mass a.e. uniqueness to a compiled positive-mass Theorem 3 IC
construction using the paper-ordered sequential candidate comparisons.
-/
theorem theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_sequential_positive_response_acceptAll_candidates
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
        μ arrival R1 R2 switch12 switch21)
    (hpositive_candidates :
      theorem3AcceptAllPositiveMassSequentialPositiveResponseAEAcceptAllCandidateCertificate
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hIC, hprice_form, hparams⟩
  let R : DynamicReward :=
    gn21MeasuredCTMCStructuredDynamicReward
      μ arrival switch12 switch21 m z
  have hAE :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ :=
    positiveMassMeasurable_acceptAll_ae_unique_of_sequential_positive_response_acceptAll_candidates
      μ R (hpositive_candidates m z hsigns hparams)
  exact ⟨m, z, hsigns, hIC, by simpa [R] using hAE,
    hprice_form, hparams⟩

/--
Paper-facing positive-mass Theorem 3 endpoint from the canonical
denominator-valid sequential source assumptions plus the positive-response
Lemma 5 marginal proof.  The conclusion is exactly the source-domain version
of measurable IC with a.e. accept-all uniqueness: no zero-mass comparison
policy is quantified over.
-/
theorem paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions_and_positive_response_marginal
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21)
    (hpositive_marginal :
      theorem3AcceptAllPositiveMassPositiveResponseAEMarginalCertificate
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_positive_response_marginal
    (paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)
    hpositive_marginal

/--
Paper-facing positive-mass Theorem 3 endpoint from the canonical
denominator-valid sequential source assumptions plus the weaker
positive-response accept-all candidate comparisons.
-/
theorem paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions_and_positive_response_acceptAll_candidates
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21)
    (hpositive_candidates :
      theorem3AcceptAllPositiveMassPositiveResponseAEAcceptAllCandidateCertificate
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_positive_response_acceptAll_candidates
    (paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)
    hpositive_candidates

/--
Paper-facing positive-mass Theorem 3 endpoint from the canonical
denominator-valid sequential source assumptions.  This closes the paper-proof
path on the positive-mass source domain: the surge Lemma 9 response is proved
first, the surge state is rewritten to accept-all a.e., and then the non-surge
Lemma 10 response is applied with the surge state fixed at accept-all.
-/
theorem paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_sequential_positive_response_acceptAll_candidates
    (paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)
    (theorem3AcceptAllPositiveMassSequentialPositiveResponseAEAcceptAllCandidateCertificate_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)

/--
Paper-facing Theorem 3 endpoint over the partial defined-reward interface.  It
uses the same source assumptions as the positive-mass theorem and leaves
zero-mass denominator failures undefined instead of totalizing them as real
reward values.
-/
theorem paper_theorem3_measured_structured_defined_reward_ic_ae_unique_prices_of_source_assumptions
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredDefinedMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredDefinedMeasurableICAEUniqueConclusion_of_positiveMass
    (paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)

/--
Paper-facing domain bridge: a positive-mass a.e.-unique Theorem 3 result lifts
to the full feasible-measurable a.e.-unique result when the constructed prices
also strictly dominate every feasible zero-mass policy.
-/
theorem theorem3MeasuredStructuredMeasurableICAEUniqueConclusion_of_positiveMass_ae_unique_and_zeroMassStrictDominance
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
        μ arrival R1 R2 switch12 switch21)
    (hzero :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
            DynamicZeroMassStrictDominanceCertificate μ
              (gn21MeasuredCTMCStructuredDynamicReward
                μ arrival switch12 switch21 m z)) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hposIC, hposAE, hprice_form, hparams⟩
  rcases
      dynamicMeasurableICAEUnique_of_positiveMass_ae_unique_and_zeroMassStrictDominance
        hposIC hposAE (hzero m z hsigns hparams) with
    ⟨hIC, hAE⟩
  exact ⟨m, z, hsigns, hIC, hAE, hprice_form, hparams⟩

/--
Full feasible-measurable Theorem 3 from the denominator-valid sequential
source assumptions plus the exact zero-mass dominance bridge.  The positive
mass part is the paper-ordered Lemma 9 then Lemma 10 proof; the extra premise
is precisely what is needed to include feasible policies for which the
Appendix-D reward-rate denominators vanish.
-/
theorem paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_source_assumptions_and_zero_mass_dominance
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21)
    (hzero :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
            DynamicZeroMassStrictDominanceCertificate μ
              (gn21MeasuredCTMCStructuredDynamicReward
                μ arrival switch12 switch21 m z)) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredMeasurableICAEUniqueConclusion_of_positiveMass_ae_unique_and_zeroMassStrictDominance
    (paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)
    hzero

end GN21DriverSurgePricing
