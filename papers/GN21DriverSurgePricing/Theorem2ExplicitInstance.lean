import GN21DriverSurgePricing.MainTheorems

/-!
# GN21 Theorem 2 Explicit Atomic Instance

This file isolates a small atomic measured instance for Theorem 2.  The goal is
to close the paper-facing multiplicative-pricing non-IC endpoint by reducing the
Appendix-D aggregate primitives to rational bounds plus elementary CTMC switch
probability estimates.
-/

open EconCSLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

noncomputable section

/-- The explicit atomic trip-length distributions used for Theorem 2. -/
def theorem2AtomicMu : Fin 2 → Measure TripLength
  | 0 => Measure.dirac ((1 : ℝ) / 2)
  | 1 =>
      ((1 : ℝ≥0∞) / 2) • Measure.dirac (1 : ℝ) +
        ((1 : ℝ≥0∞) / 2) • Measure.dirac (6 : ℝ)

/-- The explicit arrival rates used for Theorem 2. -/
def theorem2AtomicArrival : Fin 2 → ℝ
  | 0 => 1
  | 1 => 50

/-- Multiplicative prices `w_i(τ)=m_i τ` in the explicit Theorem 2 instance. -/
def theorem2AtomicM : Fin 2 → ℝ
  | 0 => 4
  | 1 => 40

/-- The deviating policy: accept all in state 0, reject short trips in state 1. -/
def theorem2AtomicDeviation : Fin 2 → TripPolicy
  | 0 => acceptAllPolicy
  | 1 => rejectShortTripsPolicy 1

@[simp] theorem one_half_mem_acceptAllPolicy :
    ((1 : ℝ) / 2) ∈ acceptAllPolicy := by
  norm_num [acceptAllPolicy, positiveTripLengths]

@[simp] theorem one_mem_acceptAllPolicy :
    (1 : ℝ) ∈ acceptAllPolicy := by
  norm_num [acceptAllPolicy, positiveTripLengths]

@[simp] theorem six_mem_acceptAllPolicy :
    (6 : ℝ) ∈ acceptAllPolicy := by
  norm_num [acceptAllPolicy, positiveTripLengths]

@[simp] theorem one_not_mem_rejectShortTripsPolicy_one :
    (1 : ℝ) ∉ rejectShortTripsPolicy 1 := by
  simp [rejectShortTripsPolicy]

@[simp] theorem six_mem_rejectShortTripsPolicy_one :
    (6 : ℝ) ∈ rejectShortTripsPolicy 1 := by
  norm_num [rejectShortTripsPolicy]

theorem theorem2AtomicMu_zero_acceptAll_mass :
    singleStateTripMass (theorem2AtomicMu 0) acceptAllPolicy = 1 := by
  norm_num [singleStateTripMass, theorem2AtomicMu, acceptAllPolicy,
    positiveTripLengths]

theorem theorem2AtomicMu_zero_acceptAll_time :
    singleStateTripTime (theorem2AtomicMu 0) acceptAllPolicy = (1 : ℝ) / 2 := by
  classical
  rw [singleStateTripTime, theorem2AtomicMu, setIntegral_dirac]
  norm_num [acceptAllPolicy, positiveTripLengths]

theorem theorem2AtomicMu_zero_acceptAll_payment :
    singleStateTripPayment (theorem2AtomicMu 0)
        (multiplicativePricing (theorem2AtomicM 0)) acceptAllPolicy = 2 := by
  classical
  rw [singleStateTripPayment, theorem2AtomicMu, theorem2AtomicM,
    setIntegral_dirac]
  norm_num [acceptAllPolicy, positiveTripLengths, multiplicativePricing]

theorem theorem2AtomicMu_one_acceptAll_mass :
    singleStateTripMass (theorem2AtomicMu 1) acceptAllPolicy = 1 := by
  norm_num [singleStateTripMass, theorem2AtomicMu, acceptAllPolicy,
    positiveTripLengths, ENNReal.toReal_add]

theorem theorem2AtomicMu_one_rejectShort_mass :
    singleStateTripMass (theorem2AtomicMu 1) (rejectShortTripsPolicy 1) =
      (1 : ℝ) / 2 := by
  simp [singleStateTripMass, theorem2AtomicMu]

theorem theorem2AtomicMu_one_acceptAll_time :
    singleStateTripTime (theorem2AtomicMu 1) acceptAllPolicy = (7 : ℝ) / 2 := by
  classical
  simp only [singleStateTripTime, theorem2AtomicMu, Measure.restrict_add,
    Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_mem_acceptAllPolicy, six_mem_acceptAllPolicy, ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure]
    norm_num
  · exact (integrable_dirac (a := (1 : ℝ)) (f := fun τ : TripLength => τ)
      (by simp : ‖((fun τ : TripLength => τ) (1 : ℝ))‖ₑ < ∞)).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)
  · exact (integrable_dirac (a := (6 : ℝ)) (f := fun τ : TripLength => τ)
      (by simp : ‖((fun τ : TripLength => τ) (6 : ℝ))‖ₑ < ∞)).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

theorem theorem2AtomicMu_one_rejectShort_time :
    singleStateTripTime (theorem2AtomicMu 1) (rejectShortTripsPolicy 1) = 3 := by
  classical
  simp only [singleStateTripTime, theorem2AtomicMu, Measure.restrict_add,
    Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_not_mem_rejectShortTripsPolicy_one, six_mem_rejectShortTripsPolicy_one,
    ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure]
    norm_num
  · simp
  · exact (integrable_dirac (a := (6 : ℝ)) (f := fun τ : TripLength => τ)
      (by simp : ‖((fun τ : TripLength => τ) (6 : ℝ))‖ₑ < ∞)).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

theorem theorem2AtomicMu_one_acceptAll_payment :
    singleStateTripPayment (theorem2AtomicMu 1)
        (multiplicativePricing (theorem2AtomicM 1)) acceptAllPolicy = 140 := by
  classical
  simp only [singleStateTripPayment, theorem2AtomicMu, theorem2AtomicM,
    Measure.restrict_add, Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_mem_acceptAllPolicy, six_mem_acceptAllPolicy, ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure, multiplicativePricing]
    norm_num
  · exact
      (integrable_dirac (a := (1 : ℝ)) (f := multiplicativePricing 40)
        (by
          simpa [multiplicativePricing] using
            (enorm_lt_top : ‖(40 * (1 : ℝ))‖ₑ < ∞) :
          ‖multiplicativePricing 40 (1 : ℝ)‖ₑ < ∞)).smul_measure
        (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)
  · exact
      (integrable_dirac (a := (6 : ℝ)) (f := multiplicativePricing 40)
        (by
          simpa [multiplicativePricing] using
            (enorm_lt_top : ‖(40 * (6 : ℝ))‖ₑ < ∞) :
          ‖multiplicativePricing 40 (6 : ℝ)‖ₑ < ∞)).smul_measure
        (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

theorem theorem2AtomicMu_one_rejectShort_payment :
    singleStateTripPayment (theorem2AtomicMu 1)
        (multiplicativePricing (theorem2AtomicM 1)) (rejectShortTripsPolicy 1) =
      120 := by
  classical
  simp only [singleStateTripPayment, theorem2AtomicMu, theorem2AtomicM,
    Measure.restrict_add, Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_not_mem_rejectShortTripsPolicy_one, six_mem_rejectShortTripsPolicy_one,
    ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure, multiplicativePricing]
    norm_num
  · simp
  · exact
      (integrable_dirac (a := (6 : ℝ)) (f := multiplicativePricing 40)
        (by
          simpa [multiplicativePricing] using
            (enorm_lt_top : ‖(40 * (6 : ℝ))‖ₑ < ∞) :
          ‖multiplicativePricing 40 (6 : ℝ)‖ₑ < ∞)).smul_measure
        (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

theorem theorem2AtomicMu_zero_acceptAll_integral
    (f : TripLength → ℝ) :
    ∫ τ in acceptAllPolicy, f τ ∂theorem2AtomicMu 0 =
      f ((1 : ℝ) / 2) := by
  classical
  rw [theorem2AtomicMu, setIntegral_dirac]
  simp only [one_half_mem_acceptAllPolicy, ↓reduceIte]

theorem theorem2AtomicMu_one_acceptAll_integral
    (f : TripLength → ℝ) :
    ∫ τ in acceptAllPolicy, f τ ∂theorem2AtomicMu 1 =
      ((1 : ℝ) / 2) * f 1 + ((1 : ℝ) / 2) * f 6 := by
  classical
  simp only [theorem2AtomicMu, Measure.restrict_add, Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_mem_acceptAllPolicy, six_mem_acceptAllPolicy, ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure]
  · exact (integrable_dirac (a := (1 : ℝ)) (f := f)
      (by simpa using (enorm_lt_top : ‖f (1 : ℝ)‖ₑ < ∞))).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)
  · exact (integrable_dirac (a := (6 : ℝ)) (f := f)
      (by simpa using (enorm_lt_top : ‖f (6 : ℝ)‖ₑ < ∞))).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

theorem theorem2AtomicMu_one_rejectShort_integral
    (f : TripLength → ℝ) :
    ∫ τ in rejectShortTripsPolicy 1, f τ ∂theorem2AtomicMu 1 =
      ((1 : ℝ) / 2) * f 6 := by
  classical
  simp only [theorem2AtomicMu, Measure.restrict_add, Measure.restrict_smul]
  rw [restrict_dirac, restrict_dirac]
  simp only [one_not_mem_rejectShortTripsPolicy_one,
    six_mem_rejectShortTripsPolicy_one, ↓reduceIte]
  rw [integral_add_measure]
  · simp [integral_smul_measure]
  · simp
  · exact (integrable_dirac (a := (6 : ℝ)) (f := f)
      (by simpa using (enorm_lt_top : ‖f (6 : ℝ)‖ₑ < ∞))).smul_measure
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ∞)

/-- State-0 switch probability at the single state-0 atom. -/
def theorem2AtomicQ0 : ℝ :=
  gn21SwitchProb ((1 : ℝ) / 4) 4 ((1 : ℝ) / 2)

/-- State-1 switch probability at trip length `1`. -/
def theorem2AtomicQ1 : ℝ :=
  gn21SwitchProb 4 ((1 : ℝ) / 4) 1

/-- State-1 switch probability at trip length `6`. -/
def theorem2AtomicQ6 : ℝ :=
  gn21SwitchProb 4 ((1 : ℝ) / 4) 6

theorem theorem2AtomicQ0_le :
    theorem2AtomicQ0 ≤ (1 : ℝ) / 17 := by
  rw [theorem2AtomicQ0, paper_lemma2_switch_probability_formula]
  ring_nf
  have hexp_nonneg : 0 ≤ Real.exp (-(17 : ℝ) / 8) := Real.exp_nonneg _
  nlinarith

theorem theorem2AtomicQ1_gt :
    (16 : ℝ) / 21 < theorem2AtomicQ1 := by
  have hexp_lt : Real.exp (-(17 : ℝ) / 4) < (4 : ℝ) / 21 := by
    have hbase : (21 : ℝ) / 4 < Real.exp ((17 : ℝ) / 4) := by
      have hadd := Real.add_one_lt_exp
        (show ((17 : ℝ) / 4) ≠ 0 by norm_num)
      norm_num at hadd
      exact hadd
    have hinv :
        (Real.exp ((17 : ℝ) / 4))⁻¹ < ((21 : ℝ) / 4)⁻¹ :=
      inv_strictAnti₀ (by norm_num : 0 < (21 : ℝ) / 4) hbase
    have hexp_rewrite :
        Real.exp (-(17 : ℝ) / 4) = (Real.exp ((17 : ℝ) / 4))⁻¹ := by
      rw [show (-(17 : ℝ) / 4) = -((17 : ℝ) / 4) by ring, Real.exp_neg]
    rw [hexp_rewrite]
    norm_num at hinv ⊢
    exact hinv
  rw [theorem2AtomicQ1, paper_lemma2_switch_probability_formula]
  ring_nf
  nlinarith

theorem theorem2AtomicQ6_le :
    theorem2AtomicQ6 ≤ (16 : ℝ) / 17 := by
  rw [theorem2AtomicQ6, paper_lemma2_switch_probability_formula]
  ring_nf
  have hexp_nonneg : 0 ≤ Real.exp (-(51 : ℝ) / 2) := Real.exp_nonneg _
  nlinarith

theorem theorem2AtomicQ_bounds :
    theorem2AtomicQ0 ≤ (1 : ℝ) / 17 ∧
      (16 : ℝ) / 21 < theorem2AtomicQ1 ∧
      theorem2AtomicQ6 ≤ (16 : ℝ) / 17 :=
  ⟨theorem2AtomicQ0_le, theorem2AtomicQ1_gt, theorem2AtomicQ6_le⟩

theorem theorem2AtomicQ0_nonneg :
    0 ≤ theorem2AtomicQ0 := by
  exact paper_lemma2_switch_probability_nonneg ((1 : ℝ) / 4) 4 ((1 : ℝ) / 2)
    (by norm_num) (by norm_num) (by norm_num)

theorem theorem2AtomicQ1_nonneg :
    0 ≤ theorem2AtomicQ1 := by
  exact paper_lemma2_switch_probability_nonneg 4 ((1 : ℝ) / 4) 1
    (by norm_num) (by norm_num) (by norm_num)

theorem theorem2AtomicQ6_nonneg :
    0 ≤ theorem2AtomicQ6 := by
  exact paper_lemma2_switch_probability_nonneg 4 ((1 : ℝ) / 4) 6
    (by norm_num) (by norm_num) (by norm_num)

theorem theorem2AtomicExitWeight_zero_acceptAll :
    gn21ExitWeightIntegral (theorem2AtomicMu 0) 1 ((1 : ℝ) / 4) 4
        acceptAllPolicy =
      (1 : ℝ) / 4 + theorem2AtomicQ0 := by
  unfold gn21ExitWeightIntegral theorem2AtomicQ0
  rw [theorem2AtomicMu_zero_acceptAll_integral]
  ring

theorem theorem2AtomicExitWeight_one_acceptAll :
    gn21ExitWeightIntegral (theorem2AtomicMu 1) 50 4 ((1 : ℝ) / 4)
        acceptAllPolicy =
      4 + 25 * theorem2AtomicQ1 + 25 * theorem2AtomicQ6 := by
  unfold gn21ExitWeightIntegral theorem2AtomicQ1 theorem2AtomicQ6
  rw [theorem2AtomicMu_one_acceptAll_integral]
  ring

theorem theorem2AtomicExitWeight_one_rejectShort :
    gn21ExitWeightIntegral (theorem2AtomicMu 1) 50 4 ((1 : ℝ) / 4)
        (rejectShortTripsPolicy 1) =
      4 + 25 * theorem2AtomicQ6 := by
  unfold gn21ExitWeightIntegral theorem2AtomicQ6
  rw [theorem2AtomicMu_one_rejectShort_integral]
  ring

theorem theorem2AtomicScaledTime_zero_acceptAll :
    gn21ScaledStateTime (theorem2AtomicMu 0) 1 acceptAllPolicy =
      (3 : ℝ) / 2 := by
  unfold gn21ScaledStateTime
  rw [theorem2AtomicMu_zero_acceptAll_time]
  norm_num

theorem theorem2AtomicScaledTime_one_acceptAll :
    gn21ScaledStateTime (theorem2AtomicMu 1) 50 acceptAllPolicy = 176 := by
  unfold gn21ScaledStateTime
  rw [theorem2AtomicMu_one_acceptAll_time]
  norm_num

theorem theorem2AtomicScaledTime_one_rejectShort :
    gn21ScaledStateTime (theorem2AtomicMu 1) 50 (rejectShortTripsPolicy 1) =
      151 := by
  unfold gn21ScaledStateTime
  rw [theorem2AtomicMu_one_rejectShort_time]
  norm_num

theorem theorem2AtomicScaledEarning_zero_acceptAll :
    gn21ScaledStateEarning (theorem2AtomicMu 0) 1
        (multiplicativePricing (theorem2AtomicM 0)) acceptAllPolicy =
      2 := by
  unfold gn21ScaledStateEarning
  rw [theorem2AtomicMu_zero_acceptAll_payment]
  norm_num

theorem theorem2AtomicScaledEarning_one_acceptAll :
    gn21ScaledStateEarning (theorem2AtomicMu 1) 50
        (multiplicativePricing (theorem2AtomicM 1)) acceptAllPolicy =
      7000 := by
  unfold gn21ScaledStateEarning
  rw [theorem2AtomicMu_one_acceptAll_payment]
  norm_num

theorem theorem2AtomicScaledEarning_one_rejectShort :
    gn21ScaledStateEarning (theorem2AtomicMu 1) 50
        (multiplicativePricing (theorem2AtomicM 1)) (rejectShortTripsPolicy 1) =
      6000 := by
  unfold gn21ScaledStateEarning
  rw [theorem2AtomicMu_one_rejectShort_payment]
  norm_num

theorem theorem2AtomicAggregateReward_acceptAll :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2AtomicMu 0) (theorem2AtomicMu 1) 1 50 ((1 : ℝ) / 4) 4
        (multiplicativePricing (theorem2AtomicM 0))
        (multiplicativePricing (theorem2AtomicM 1))
        acceptAllPolicy acceptAllPolicy =
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + theorem2AtomicQ0)
        (4 + 25 * theorem2AtomicQ1 + 25 * theorem2AtomicQ6)
        ((3 : ℝ) / 2) 176 2 7000 := by
  unfold gn21MeasuredAggregateRewardPrimitives
  rw [theorem2AtomicExitWeight_zero_acceptAll,
    theorem2AtomicExitWeight_one_acceptAll,
    theorem2AtomicScaledTime_zero_acceptAll,
    theorem2AtomicScaledTime_one_acceptAll,
    theorem2AtomicScaledEarning_zero_acceptAll,
    theorem2AtomicScaledEarning_one_acceptAll]

theorem theorem2AtomicAggregateReward_deviation :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2AtomicMu 0) (theorem2AtomicMu 1) 1 50 ((1 : ℝ) / 4) 4
        (multiplicativePricing (theorem2AtomicM 0))
        (multiplicativePricing (theorem2AtomicM 1))
        acceptAllPolicy (rejectShortTripsPolicy 1) =
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + theorem2AtomicQ0)
        (4 + 25 * theorem2AtomicQ6)
        ((3 : ℝ) / 2) 151 2 6000 := by
  unfold gn21MeasuredAggregateRewardPrimitives
  rw [theorem2AtomicExitWeight_zero_acceptAll,
    theorem2AtomicExitWeight_one_rejectShort,
    theorem2AtomicScaledTime_zero_acceptAll,
    theorem2AtomicScaledTime_one_rejectShort,
    theorem2AtomicScaledEarning_zero_acceptAll,
    theorem2AtomicScaledEarning_one_rejectShort]

theorem theorem2AtomicAggregate_algebra
    {a b c : ℝ}
    (ha_nonneg : 0 ≤ a)
    (hb_lower : (16 : ℝ) / 21 < b)
    (hc_nonneg : 0 ≤ c)
    (ha_upper : a ≤ (1 : ℝ) / 17)
    (hc_upper : c ≤ (16 : ℝ) / 17) :
    gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + a)
        (4 + 25 * b + 25 * c)
        ((3 : ℝ) / 2) 176 2 7000 <
      gn21AggregateDynamicReward
        ((1 : ℝ) / 4 + a)
        (4 + 25 * c)
        ((3 : ℝ) / 2) 151 2 6000 := by
  have hQi_pos : 0 < (1 : ℝ) / 4 + a := by nlinarith
  have hQall_pos : 0 < 4 + 25 * b + 25 * c := by nlinarith
  have hQdev_pos : 0 < 4 + 25 * c := by nlinarith
  have hden_all_pos :
      0 < ((1 : ℝ) / 4 + a) * 176 +
          (4 + 25 * b + 25 * c) * ((3 : ℝ) / 2) := by
    nlinarith [mul_pos hQi_pos (by norm_num : 0 < (176 : ℝ)),
      mul_pos hQall_pos (by norm_num : 0 < (3 : ℝ) / 2)]
  have hden_dev_pos :
      0 < ((1 : ℝ) / 4 + a) * 151 +
          (4 + 25 * c) * ((3 : ℝ) / 2) := by
    nlinarith [mul_pos hQi_pos (by norm_num : 0 < (151 : ℝ)),
      mul_pos hQdev_pos (by norm_num : 0 < (3 : ℝ) / 2)]
  unfold gn21AggregateDynamicReward
  rw [div_lt_div_iff₀ hden_all_pos hden_dev_pos]
  ring_nf
  nlinarith

theorem theorem2AtomicAggregate_profitable :
    gn21MeasuredAggregateRewardPrimitives
        (theorem2AtomicMu 0) (theorem2AtomicMu 1) 1 50 ((1 : ℝ) / 4) 4
        (multiplicativePricing (theorem2AtomicM 0))
        (multiplicativePricing (theorem2AtomicM 1))
        acceptAllPolicy acceptAllPolicy <
      gn21MeasuredAggregateRewardPrimitives
        (theorem2AtomicMu 0) (theorem2AtomicMu 1) 1 50 ((1 : ℝ) / 4) 4
        (multiplicativePricing (theorem2AtomicM 0))
        (multiplicativePricing (theorem2AtomicM 1))
        acceptAllPolicy (rejectShortTripsPolicy 1) := by
  rw [theorem2AtomicAggregateReward_acceptAll,
    theorem2AtomicAggregateReward_deviation]
  exact theorem2AtomicAggregate_algebra theorem2AtomicQ0_nonneg
    theorem2AtomicQ1_gt theorem2AtomicQ6_nonneg theorem2AtomicQ0_le
    theorem2AtomicQ6_le

/--
Theorem 2 explicit measured endpoint: the atomic two-state instance with
multiplicative prices has a profitable dynamic deviation, so multiplicative
pricing is not dynamically incentive compatible.
-/
theorem paper_theorem2_multiplicative_measured_not_ic_explicit_atomic :
    ¬ dynamicIncentiveCompatible
      (gn21MeasuredDynamicRewardFunctional theorem2AtomicMu theorem2AtomicArrival
        ((1 : ℝ) / 4) 4
        (fun i => multiplicativePricing (theorem2AtomicM i))) := by
  exact
    paper_theorem2_multiplicative_measured_not_ic_of_aggregate_witness
      theorem2AtomicMu theorem2AtomicArrival ((1 : ℝ) / 4) 4
      theorem2AtomicM
      { deviation := theorem2AtomicDeviation
        acceptAll_nondegenerate := by
          apply gn21MeasuredPairNondegenerate_of_positive_measure
          · rw [theorem2AtomicMu_zero_acceptAll_mass]
            norm_num
          · rw [theorem2AtomicMu_one_acceptAll_mass]
            norm_num
          · norm_num [theorem2AtomicArrival]
          · norm_num [theorem2AtomicArrival]
          · norm_num
          · norm_num
          · exact measurableSet_acceptAllPolicy
          · exact measurableSet_acceptAllPolicy
          · intro τ hτ
            exact hτ
          · intro τ hτ
            exact hτ
        deviation_nondegenerate := by
          apply gn21MeasuredPairNondegenerate_of_positive_measure
          · simpa [theorem2AtomicDeviation, theorem2AtomicMu_zero_acceptAll_mass]
          · simpa [theorem2AtomicDeviation, theorem2AtomicMu_one_rejectShort_mass]
          · norm_num [theorem2AtomicArrival]
          · norm_num [theorem2AtomicArrival]
          · norm_num
          · norm_num
          · exact measurableSet_acceptAllPolicy
          · exact measurableSet_rejectShortTripsPolicy 1
          · intro τ hτ
            exact hτ
          · intro τ hτ
            rcases hτ with ⟨hpos, _⟩
            exact hpos
        aggregate_profitable := by
          simpa [theorem2AtomicArrival, theorem2AtomicDeviation,
            theorem2AtomicM] using theorem2AtomicAggregate_profitable }

end

end GN21DriverSurgePricing
