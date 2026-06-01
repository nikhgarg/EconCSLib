import PRPKG24AccuracyDiversity.Exchange
import PRPKG24AccuracyDiversity.TopKOracle
import EconCSLib.Foundations.Probability.RealDistribution
import EconCSLib.Foundations.Math.FiniteRounding
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Linarith

open scoped BigOperators
open MeasureTheory Set

namespace PRPKG24AccuracyDiversity

/-- The continuous uniform probability measure on `[0,1]`. -/
noncomputable def uniform01Measure : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc (0 : ℝ) 1)

instance uniform01Measure_isProbabilityMeasure :
    IsProbabilityMeasure uniform01Measure := by
  unfold uniform01Measure
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (μ := volume) (s := Set.Icc (0 : ℝ) 1)
    (by simp) (by simp)

theorem uniform01Measure_ae_bounds :
    ∀ᵐ y ∂uniform01Measure, 0 ≤ y ∧ y ≤ 1 := by
  simpa [uniform01Measure] using
    (ProbabilityTheory.ae_cond_mem
      (μ := volume) (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc)

theorem uniform01Measure_real_eq_volume_real_inter
    (t : Set ℝ) :
    uniform01Measure.real t =
      volume.real (t ∩ Set.Icc (0 : ℝ) 1) := by
  unfold uniform01Measure ProbabilityTheory.cond
  simp [Real.volume_Icc]

theorem uniform01_reflectedCDFMass_eq {x : ℝ}
    (hx_pos : 0 < x) (hx_lt_one : x < 1) :
    EconCSLib.Probability.reflectedCDFMass uniform01Measure 1 x = x := by
  let t : Set ℝ := {y : ℝ | (1 : ℝ) ≤ x + y}
  have ht_inter :
      t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (1 - x) 1 := by
    ext y
    constructor
    · intro hy
      have hyt : 1 ≤ x + y := by simpa [t] using hy.1
      exact ⟨by linarith [hyt], hy.2.2⟩
    · intro hy
      constructor
      · change 1 ≤ x + y
        linarith [hy.1]
      · exact ⟨by linarith [hy.1, hx_lt_one], hy.2⟩
  have hle : 1 - x ≤ (1 : ℝ) := by linarith
  calc
    EconCSLib.Probability.reflectedCDFMass uniform01Measure 1 x =
        uniform01Measure.real t := by rfl
    _ = volume.real (t ∩ Set.Icc (0 : ℝ) 1) :=
        uniform01Measure_real_eq_volume_real_inter t
    _ = volume.real (Set.Icc (1 - x) 1) := by rw [ht_inter]
    _ = x := by
      rw [Real.volume_real_Icc_of_le hle]
      ring

theorem uniform01_reflectedCDFMass_eventually_eq_power :
    ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      EconCSLib.Probability.reflectedCDFMass uniform01Measure 1 x =
        (1 / 1 : ℝ) * x ^ (1 : ℝ) := by
  filter_upwards
    [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with x hx_pos hx_lt_one
  rw [uniform01_reflectedCDFMass_eq hx_pos hx_lt_one]
  simp

noncomputable def uniformTopOneValue (q : ℕ) : ℝ :=
  1 - 1 / (q + 1 : ℝ)

@[simp] theorem uniformTopOneValue_zero :
    uniformTopOneValue 0 = 0 := by
  norm_num [uniformTopOneValue]

theorem uniformTopOneValue_succ_sub (q : ℕ) :
    uniformTopOneValue (q + 1) - uniformTopOneValue q =
      1 / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by
  unfold uniformTopOneValue
  have h_cast : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by push_cast; rfl
  rw [h_cast]
  have h1 : (q : ℝ) + 1 + 1 = (q : ℝ) + 2 := by ring
  rw [h1]
  have hd1 : (q : ℝ) + 1 ≠ 0 := by positivity
  have hd2 : (q : ℝ) + 2 ≠ 0 := by positivity
  have h_diff : 1 - 1 / ((q : ℝ) + 2) - (1 - 1 / ((q : ℝ) + 1)) = 1 / ((q : ℝ) + 1) - 1 / ((q : ℝ) + 2) := by ring
  rw [h_diff]
  have h_frac : 1 / ((q : ℝ) + 1) - 1 / ((q : ℝ) + 2) = (1 * ((q : ℝ) + 2) - ((q : ℝ) + 1) * 1) / (((q : ℝ) + 1) * ((q : ℝ) + 2)) := by
    exact div_sub_div 1 1 hd1 hd2
  rw [h_frac]
  have h_num : 1 * ((q : ℝ) + 2) - ((q : ℝ) + 1) * 1 = 1 := by ring
  rw [h_num]

theorem uniformTopOneValue_sub_pred {q : ℕ} (hq : 0 < q) :
    uniformTopOneValue q - uniformTopOneValue (q - 1) =
      1 / ((q : ℝ) * (q + 1 : ℝ)) := by
  unfold uniformTopOneValue
  have h_cast1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hq]
    push_cast
    rfl
  rw [h_cast1]
  have h1 : (q : ℝ) - 1 + 1 = (q : ℝ) := by ring
  rw [h1]
  have hd1 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hd2 : (q : ℝ) + 1 ≠ 0 := by positivity
  have h_diff : 1 - 1 / ((q : ℝ) + 1) - (1 - 1 / (q : ℝ)) = 1 / (q : ℝ) - 1 / ((q : ℝ) + 1) := by ring
  rw [h_diff]
  have h_frac : 1 / (q : ℝ) - 1 / ((q : ℝ) + 1) = (1 * ((q : ℝ) + 1) - (q : ℝ) * 1) / ((q : ℝ) * ((q : ℝ) + 1)) := by
    exact div_sub_div 1 1 hd1 hd2
  rw [h_frac]
  have h_num : 1 * ((q : ℝ) + 1) - (q : ℝ) * 1 = 1 := by ring
  rw [h_num]

noncomputable def uniformTopKFactor (k : ℕ) : ℝ :=
  (k : ℝ) * (k + 1 : ℝ) / 2

noncomputable def uniformTopKValue (k q : ℕ) : ℝ :=
  if q ≤ k then (q : ℝ) / 2
  else (k : ℝ) - uniformTopKFactor k / (q + 1 : ℝ)

noncomputable def uniformOrderStatisticMean (i q : ℕ) : ℝ :=
  1 - (i : ℝ) / (q + 1 : ℝ)

/--
Uniform `[0,1]` order-statistic mean in the paper's Definition 3 convention:
`i` is the `i`-th smallest draw among `q` samples.
-/
noncomputable def uniformAscendingOrderStatisticMean (i q : ℕ) : ℝ :=
  (i : ℝ) / (q + 1 : ℝ)

noncomputable def uniformTopKOrderStatisticSum (k q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (min k q), uniformOrderStatisticMean (i + 1) q

theorem uniformTopKFactor_pos {k : ℕ} (hk : 0 < k) :
    0 < uniformTopKFactor k := by
  unfold uniformTopKFactor
  positivity

theorem uniformTopKFactor_nonneg (k : ℕ) :
    0 ≤ uniformTopKFactor k := by
  unfold uniformTopKFactor
  positivity

@[simp] theorem uniformTopKValue_zero (k : ℕ) :
    uniformTopKValue k 0 = 0 := by
  simp [uniformTopKValue]

theorem sum_range_cast_succ (n : ℕ) :
    (∑ i ∈ Finset.range n, ((i + 1 : ℕ) : ℝ)) =
      (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num
      ring

theorem uniformTopKOrderStatisticSum_eq_value (k q : ℕ) :
    uniformTopKOrderStatisticSum k q = uniformTopKValue k q := by
  by_cases hqk : q ≤ k
  · have hmin : min k q = q := min_eq_right hqk
    unfold uniformTopKOrderStatisticSum uniformOrderStatisticMean uniformTopKValue
    simp [hqk]
    have hsum :
        (∑ i ∈ Finset.range q, ((i : ℝ) + 1)) =
          (q : ℝ) * ((q : ℝ) + 1) / 2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using sum_range_cast_succ q
    rw [← Finset.sum_div, hsum]
    have hden : (q : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]
    ring
  · have hkq : k < q := not_le.mp hqk
    have hmin : min k q = k := min_eq_left (le_of_lt hkq)
    unfold uniformTopKOrderStatisticSum uniformOrderStatisticMean uniformTopKValue
    simp [hqk, hmin]
    have hsum :
        (∑ i ∈ Finset.range k, ((i : ℝ) + 1)) =
          (k : ℝ) * ((k : ℝ) + 1) / 2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using sum_range_cast_succ k
    rw [← Finset.sum_div, hsum]
    unfold uniformTopKFactor
    have hden : (q : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]

/--
Proposition 5 specialized to the uniform `[0,1]` order-statistic means in the
paper's bottom-indexed convention.
-/
theorem uniform_orderStatisticTopKSumFromMean_eq_topKOrderStatisticSum
    (k q : ℕ) :
    orderStatisticTopKSumFromMean uniformAscendingOrderStatisticMean k q =
      uniformTopKOrderStatisticSum k q := by
  unfold orderStatisticTopKSumFromMean uniformAscendingOrderStatisticMean
    uniformTopKOrderStatisticSum uniformOrderStatisticMean
  apply Finset.sum_congr rfl
  intro i hi
  have hi_lt : i < min k q := Finset.mem_range.mp hi
  have hi_le_q : i ≤ q :=
    le_trans (Nat.le_of_lt hi_lt) (min_le_right k q)
  have hden : (q : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.cast_sub hi_le_q]
  field_simp [hden]
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

theorem uniform_orderStatisticTopKSumFromMean_eq_value (k q : ℕ) :
    orderStatisticTopKSumFromMean uniformAscendingOrderStatisticMean k q =
      uniformTopKValue k q := by
  rw [uniform_orderStatisticTopKSumFromMean_eq_topKOrderStatisticSum,
    uniformTopKOrderStatisticSum_eq_value]

theorem uniformTopKValue_succ_sub_of_le {k q : ℕ} (hkq : k ≤ q) :
    uniformTopKValue k (q + 1) - uniformTopKValue k q =
      uniformTopKFactor k / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by
  by_cases hqk : q = k
  · subst q
    unfold uniformTopKValue uniformTopKFactor
    have hnot : ¬ k + 1 ≤ k := by omega
    simp [hnot]
    field_simp
    ring
  · have hklt : k < q := lt_of_le_of_ne hkq (Ne.symm hqk)
    have hnot_q : ¬ q ≤ k := not_le_of_gt hklt
    have hnot_succ : ¬ q + 1 ≤ k := by omega
    unfold uniformTopKValue
    simp [hnot_q, hnot_succ]
    have hd1 : (q : ℝ) + 1 ≠ 0 := by positivity
    have hd2 : (q : ℝ) + 2 ≠ 0 := by positivity
    unfold uniformTopKFactor
    field_simp [hd1, hd2]
    ring

theorem uniformTopKValue_succ_sub_of_lt {k q : ℕ} (hq : q < k) :
    uniformTopKValue k (q + 1) - uniformTopKValue k q = 1 / 2 := by
  have hqle : q ≤ k := le_of_lt hq
  have hsuccle : q + 1 ≤ k := Nat.succ_le_of_lt hq
  unfold uniformTopKValue
  simp [hqle, hsuccle]
  ring

theorem uniformTopKValue_sub_pred_of_le {k q : ℕ}
    (hkq : k ≤ q) (hq : 0 < q) :
    uniformTopKValue k q - uniformTopKValue k (q - 1) =
      uniformTopKFactor k / ((q : ℝ) * (q + 1 : ℝ)) := by
  by_cases hqk : q = k
  · subst q
    have hk : 0 < k := hq
    unfold uniformTopKValue uniformTopKFactor
    have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hk)]
      norm_num
    simp [hsub]
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk
    have hk_succ_ne : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hk_ne, hk_succ_ne]
    ring_nf
  · have hpred : k ≤ q - 1 := by omega
    have hsucc := uniformTopKValue_succ_sub_of_le (k := k) (q := q - 1) hpred
    have hcancel : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
    have hden1 : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hq)]
      norm_num
    have hden2 : ((q - 1 : ℕ) : ℝ) + 2 = (q : ℝ) + 1 := by
      linarith
    simpa [hcancel, hden1, hden2] using hsucc

theorem uniformTopKValue_marginal_antitone_step (k q : ℕ) :
    uniformTopKValue k (q + 2) - uniformTopKValue k (q + 1) ≤
      uniformTopKValue k (q + 1) - uniformTopKValue k q := by
  by_cases hlt : q + 1 < k
  · have hq : q < k := by omega
    rw [uniformTopKValue_succ_sub_of_lt hlt,
      uniformTopKValue_succ_sub_of_lt hq]
  · have hge : k ≤ q + 1 := le_of_not_gt hlt
    by_cases heq : q + 1 = k
    · rw [uniformTopKValue_succ_sub_of_le hge,
        uniformTopKValue_succ_sub_of_lt (by omega : q < k)]
      norm_num only [Nat.cast_add, Nat.cast_one]
      subst k
      unfold uniformTopKFactor
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hdenpos :
          0 < (((q : ℝ) + 1 + 1) * ((q : ℝ) + 1 + 2)) := by
        positivity
      rw [div_le_iff₀ hdenpos]
      ring_nf
      norm_num only [Nat.cast_add, Nat.cast_one] at *
      nlinarith [show (0 : ℝ) ≤ q by positivity]
    · have hkq : k ≤ q := by omega
      rw [uniformTopKValue_succ_sub_of_le (k := k) (q := q + 1) hge,
        uniformTopKValue_succ_sub_of_le (k := k) (q := q) hkq]
      have hfactor_nonneg := uniformTopKFactor_nonneg k
      have hden :
          ((q + 1 : ℝ) * (q + 2 : ℝ)) ≤
            ((((q + 1 : ℕ) : ℝ) + 1) * (((q + 1 : ℕ) : ℝ) + 2)) := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        nlinarith [show (0 : ℝ) ≤ q + 2 by positivity]
      have hrec :
          1 / ((((q + 1 : ℕ) : ℝ) + 1) * (((q + 1 : ℕ) : ℝ) + 2)) ≤
            1 / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by
        gcongr
      calc
        uniformTopKFactor k /
            ((((q + 1 : ℕ) : ℝ) + 1) * (((q + 1 : ℕ) : ℝ) + 2))
            = uniformTopKFactor k *
                (1 / ((((q + 1 : ℕ) : ℝ) + 1) *
                  (((q + 1 : ℕ) : ℝ) + 2))) := by ring
        _ ≤ uniformTopKFactor k *
                (1 / ((q + 1 : ℝ) * (q + 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left hrec hfactor_nonneg
        _ = uniformTopKFactor k / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by ring

noncomputable def uniformTopOneConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) : ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := fun _ q => uniformTopOneValue q

noncomputable def uniformTopKConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ) : ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := fun _ q => uniformTopKValue k q

theorem uniformTopKConsumptionModel_has_diminishing_returns {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ) :
    (uniformTopKConsumptionModel likelihood k).HasDiminishingReturns := by
  intro t q
  exact uniformTopKValue_marginal_antitone_step k q

noncomputable def uniformSqrtTarget {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) : ℝ :=
  (N : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))

noncomputable def uniformSqrtShiftedTarget {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) : ℝ :=
  (N + T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))

noncomputable def uniformSqrtRealOptTarget {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) : ℝ :=
  uniformSqrtShiftedTarget likelihood N t - 1

noncomputable def uniformSqrtPrintedOptTarget {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) : ℝ :=
  uniformSqrtTarget likelihood N t - 1

noncomputable def uniformSqrtScale {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) : ℝ :=
  (∑ i, Real.sqrt (likelihood i)) ^ 2 / (N + T : ℝ) ^ 2

theorem likelihood_eq_scale_mul_shiftedTarget_sq {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (hlike_nonneg : ∀ i, 0 ≤ likelihood i)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    likelihood t =
      uniformSqrtScale likelihood N *
        (uniformSqrtShiftedTarget likelihood N t) ^ 2 := by
  unfold uniformSqrtScale uniformSqrtShiftedTarget
  have hT_pos : 0 < (T : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  have hden : (N + T : ℝ) ≠ 0 := by positivity
  have hden2 : (N + T : ℝ) ^ 2 ≠ 0 := by positivity
  have hnorm2 : (∑ i, Real.sqrt (likelihood i)) ^ 2 ≠ 0 := by
    have h : (∑ i, Real.sqrt (likelihood i)) ^ 2 = (∑ i, Real.sqrt (likelihood i)) * (∑ i, Real.sqrt (likelihood i)) := by ring
    rw [h]
    exact mul_ne_zero hnorm hnorm
  have hsq1 : (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) ^ 2 =
      (Real.sqrt (likelihood t)) ^ 2 / (∑ i, Real.sqrt (likelihood i)) ^ 2 := by ring
  have hsq2 : ((N + T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))) ^ 2 =
      (N + T : ℝ) ^ 2 * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) ^ 2 := by ring
  rw [hsq2, hsq1]
  have h_mul : ((∑ i, Real.sqrt (likelihood i)) ^ 2 / (N + T : ℝ) ^ 2) *
        ((N + T : ℝ) ^ 2 * ((Real.sqrt (likelihood t)) ^ 2 / (∑ i, Real.sqrt (likelihood i)) ^ 2)) =
      (Real.sqrt (likelihood t)) ^ 2 := by
    calc
      ((∑ i, Real.sqrt (likelihood i)) ^ 2 / (N + T : ℝ) ^ 2) *
          ((N + T : ℝ) ^ 2 * ((Real.sqrt (likelihood t)) ^ 2 / (∑ i, Real.sqrt (likelihood i)) ^ 2))
        = (((∑ i, Real.sqrt (likelihood i)) ^ 2) / (∑ i, Real.sqrt (likelihood i)) ^ 2) *
            (((N + T : ℝ) ^ 2) / (N + T : ℝ) ^ 2) * (Real.sqrt (likelihood t)) ^ 2 := by ring
      _ = 1 * 1 * (Real.sqrt (likelihood t)) ^ 2 := by
          rw [div_self hnorm2, div_self hden2]
      _ = (Real.sqrt (likelihood t)) ^ 2 := by ring
  rw [h_mul]
  exact (Real.sq_sqrt (hlike_nonneg t)).symm

theorem uniformSqrtShiftedTarget_nonneg {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) :
    0 ≤ uniformSqrtShiftedTarget likelihood N t := by
  unfold uniformSqrtShiftedTarget
  have hT_pos : 0 < (T : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (likelihood t) := Real.sqrt_nonneg _
  have hsum_nonneg : 0 ≤ ∑ i, Real.sqrt (likelihood i) := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  positivity

theorem sum_uniformSqrtShiftedTarget {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    ∑ t, uniformSqrtShiftedTarget likelihood N t = N + T := by
  unfold uniformSqrtShiftedTarget
  have hrewrite : ∀ t, (N + T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) =
      ((N + T : ℝ) / ∑ i, Real.sqrt (likelihood i)) * Real.sqrt (likelihood t) := by
    intro t
    ring
  have hsum_rewrite : (∑ t, (N + T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))) =
      ∑ t, ((N + T : ℝ) / ∑ i, Real.sqrt (likelihood i)) * Real.sqrt (likelihood t) :=
    Finset.sum_congr rfl (fun t _ => hrewrite t)
  rw [hsum_rewrite, ← Finset.mul_sum]
  have hden : (∑ i, Real.sqrt (likelihood i)) ≠ 0 := hnorm
  exact div_mul_cancel₀ (N + T : ℝ) hden

theorem sum_uniformSqrtRealOptTarget {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    ∑ t, uniformSqrtRealOptTarget likelihood N t = N := by
  unfold uniformSqrtRealOptTarget
  rw [Finset.sum_sub_distrib, sum_uniformSqrtShiftedTarget likelihood N hnorm]
  simp [Fintype.card_fin]

theorem uniformSqrtRealOptTarget_add_one {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) :
    uniformSqrtRealOptTarget likelihood N t + 1 =
      uniformSqrtShiftedTarget likelihood N t := by
  unfold uniformSqrtRealOptTarget
  ring

theorem sum_uniformSqrtPrintedOptTarget {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    ∑ t, uniformSqrtPrintedOptTarget likelihood N t = (N : ℝ) - T := by
  unfold uniformSqrtPrintedOptTarget uniformSqrtTarget
  rw [Finset.sum_sub_distrib]
  have hrewrite :
      (∑ t : ItemType T,
          (N : ℝ) * (Real.sqrt (likelihood t) /
            ∑ i : ItemType T, Real.sqrt (likelihood i))) =
        (N : ℝ) := by
    have hpoint : ∀ t,
        (N : ℝ) * (Real.sqrt (likelihood t) /
          ∑ i : ItemType T, Real.sqrt (likelihood i)) =
        ((N : ℝ) / ∑ i : ItemType T, Real.sqrt (likelihood i)) *
          Real.sqrt (likelihood t) := by
      intro t
      ring
    calc
      (∑ t : ItemType T,
          (N : ℝ) * (Real.sqrt (likelihood t) /
            ∑ i : ItemType T, Real.sqrt (likelihood i)))
          = ∑ t : ItemType T,
              ((N : ℝ) / ∑ i : ItemType T, Real.sqrt (likelihood i)) *
                Real.sqrt (likelihood t) := by
              exact Finset.sum_congr rfl (fun t _ => hpoint t)
      _ = ((N : ℝ) / ∑ i : ItemType T, Real.sqrt (likelihood i)) *
            ∑ t : ItemType T, Real.sqrt (likelihood t) := by
              rw [Finset.mul_sum]
      _ = (N : ℝ) := div_mul_cancel₀ (N : ℝ) hnorm
  rw [hrewrite]
  simp [Fintype.card_fin]

theorem sum_uniformSqrtShiftedTarget_nonneg {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) :
    0 ≤ ∑ t, uniformSqrtShiftedTarget likelihood N t :=
  Finset.sum_nonneg (fun t _ => uniformSqrtShiftedTarget_nonneg _ _ _)

theorem sqrtLikelihoodProfile_normalizer_ne_zero {T : ℕ}
    (likelihood : ItemType T → ℝ)
    (hsum : 0 < ∑ i, likelihood i) (hnonneg : ∀ i, 0 ≤ likelihood i) :
    ∑ i : ItemType T, Real.sqrt (likelihood i) ≠ 0 := by
  intro h
  have hwnonneg : ∀ i ∈ (Finset.univ : Finset (ItemType T)), 0 ≤ Real.sqrt (likelihood i) := fun i _ => Real.sqrt_nonneg _
  have h0 : ∀ i, Real.sqrt (likelihood i) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg hwnonneg).mp h i (Finset.mem_univ i)
  have hw0 : ∀ i, likelihood i = 0 := by
    intro i
    have hi := h0 i
    rwa [Real.sqrt_eq_zero (hnonneg i)] at hi
  have hsum0 : (∑ i, likelihood i) = 0 := Finset.sum_eq_zero (fun i _ => hw0 i)
  linarith

noncomputable def floorCountAnchor {T : ℕ}
    (target : ItemType T → ℝ) : CountAllocation T where
  count := fun t => ⌊target t⌋₊

noncomputable def uniformSqrtUpperAnchor {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) : CountAllocation T :=
  floorCountAnchor (uniformSqrtShiftedTarget likelihood N)

noncomputable def uniformSqrtLowerAnchor {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) : CountAllocation T where
  count := fun t => ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1

theorem total_uniformSqrtUpperAnchor_le {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    (EconCSLib.Allocation.total (uniformSqrtUpperAnchor likelihood N) : ℝ) ≤ N + T := by
  unfold uniformSqrtUpperAnchor floorCountAnchor EconCSLib.Allocation.total
  dsimp only
  have h_le : ∀ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) ≤ uniformSqrtShiftedTarget likelihood N t := by
    intro t
    exact Nat.floor_le (uniformSqrtShiftedTarget_nonneg likelihood N t)
  calc
    ((∑ t, ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℕ) : ℝ)
        = ∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) := by push_cast; rfl
    _ ≤ ∑ t, uniformSqrtShiftedTarget likelihood N t := Finset.sum_le_sum (fun t _ => h_le t)
    _ = N + T := sum_uniformSqrtShiftedTarget likelihood N hnorm

theorem total_uniformSqrtLowerAnchor_le_N {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0)
    (h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t) :
    (EconCSLib.Allocation.total (uniformSqrtLowerAnchor likelihood N) : ℝ) ≤ N := by
  unfold uniformSqrtLowerAnchor EconCSLib.Allocation.total
  dsimp only
  have h_ge1 : ∀ t, 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ := by
    intro t
    exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
  have h_le : ∀ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1 : ℕ) : ℝ) ≤ uniformSqrtShiftedTarget likelihood N t - 1 := by
    intro t
    rw [Nat.cast_sub (h_ge1 t), Nat.cast_one]
    exact sub_le_sub_right (Nat.floor_le (uniformSqrtShiftedTarget_nonneg likelihood N t)) 1
  calc
    ((∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1) : ℕ) : ℝ)
        = ∑ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1 : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ∑ t, (uniformSqrtShiftedTarget likelihood N t - 1) := Finset.sum_le_sum (fun t _ => h_le t)
    _ = (∑ t, uniformSqrtShiftedTarget likelihood N t) - T := by
          rw [Finset.sum_sub_distrib]
          simp
    _ = N := by
          rw [sum_uniformSqrtShiftedTarget likelihood N hnorm]
          ring

theorem total_uniformSqrtLowerAnchor_eq_N_of_integers {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0)
    (h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t)
    (hintegers : ∀ t, uniformSqrtShiftedTarget likelihood N t = ⌊uniformSqrtShiftedTarget likelihood N t⌋₊) :
    (EconCSLib.Allocation.total (uniformSqrtLowerAnchor likelihood N) : ℝ) = N := by
  unfold uniformSqrtLowerAnchor EconCSLib.Allocation.total
  dsimp only
  have h_ge1 : ∀ t, 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ := by
    intro t
    exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
  have h_eq : ∀ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1 : ℕ) : ℝ) = uniformSqrtShiftedTarget likelihood N t - 1 := by
    intro t
    rw [Nat.cast_sub (h_ge1 t), Nat.cast_one]
    rw [← hintegers t]
  calc
    ((∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1) : ℕ) : ℝ)
        = ∑ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1 : ℕ) : ℝ) := by push_cast; rfl
    _ = ∑ t, (uniformSqrtShiftedTarget likelihood N t - 1) := Finset.sum_congr rfl (fun t _ => h_eq t)
    _ = (∑ t, uniformSqrtShiftedTarget likelihood N t) - T := by
          rw [Finset.sum_sub_distrib]
          simp
    _ = N := by
          rw [sum_uniformSqrtShiftedTarget likelihood N hnorm]
          ring

theorem total_uniformSqrtLowerAnchor_gt_N_sub_T_refined {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0)
    (h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t)
    (hnot_integers : ∃ t, uniformSqrtShiftedTarget likelihood N t ≠ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊) :
    (N : ℝ) - T < (EconCSLib.Allocation.total (uniformSqrtLowerAnchor likelihood N) : ℝ) := by
  unfold uniformSqrtLowerAnchor EconCSLib.Allocation.total
  dsimp only
  have h_ge1 : ∀ t, 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ := by
    intro t
    exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
  have h_eq : ∀ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1 : ℕ) : ℝ) = (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) - 1 := by
    intro t
    rw [Nat.cast_sub (h_ge1 t), Nat.cast_one]
  have h_sum_rewrite : ((∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1) : ℕ) : ℝ) = ∑ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) - 1) := by
    calc
      ((∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1) : ℕ) : ℝ)
          = ∑ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1 : ℕ) : ℝ) := by push_cast; rfl
      _ = ∑ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) - 1) := Finset.sum_congr rfl (fun t _ => h_eq t)
  rw [h_sum_rewrite]
  rw [Finset.sum_sub_distrib]
  simp
  have h_lt : ∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) > (∑ t, uniformSqrtShiftedTarget likelihood N t) - T := by
    have h_diff : (∑ t, uniformSqrtShiftedTarget likelihood N t) - ∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) = ∑ t, (uniformSqrtShiftedTarget likelihood N t - ⌊uniformSqrtShiftedTarget likelihood N t⌋₊) := by
      rw [Finset.sum_sub_distrib]
    have h_sum_lt_T : ∑ t, (uniformSqrtShiftedTarget likelihood N t - ⌊uniformSqrtShiftedTarget likelihood N t⌋₊) < T := by
      have h_lt_one : ∀ t, uniformSqrtShiftedTarget likelihood N t - ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ < 1 := by
        intro t
        have ht := Nat.lt_floor_add_one (uniformSqrtShiftedTarget likelihood N t)
        linarith
      calc
        ∑ t, (uniformSqrtShiftedTarget likelihood N t - ⌊uniformSqrtShiftedTarget likelihood N t⌋₊)
            < ∑ t : ItemType T, (1 : ℝ) := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun t _ => h_lt_one t)
        _ = T := by simp
    linarith
  have hsum_target := sum_uniformSqrtShiftedTarget likelihood N hnorm
  linarith

theorem uniformSqrtUpperAnchor_shift_le {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) :
    uniformSqrtShiftedTarget likelihood N t ≤
      ((uniformSqrtUpperAnchor likelihood N).count t : ℝ) + 1 := by
  unfold uniformSqrtUpperAnchor floorCountAnchor
  dsimp only
  exact le_of_lt (Nat.lt_floor_add_one (uniformSqrtShiftedTarget likelihood N t))

theorem uniformSqrtLowerAnchor_le_shift {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t) :
    ((uniformSqrtLowerAnchor likelihood N).count t : ℝ) + 1 ≤
      uniformSqrtShiftedTarget likelihood N t := by
  unfold uniformSqrtLowerAnchor
  dsimp only
  have hge1 : 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ :=
    Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
  rw [Nat.cast_sub hge1]
  push_cast
  have hfloor := Nat.floor_le (uniformSqrtShiftedTarget_nonneg likelihood N t)
  linarith

theorem uniformSqrtUpperAnchor_abs_close {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    |((uniformSqrtUpperAnchor likelihood N).count t : ℝ) -
      uniformSqrtTarget likelihood N t| < (T : ℝ) + 1 := by
  unfold uniformSqrtUpperAnchor floorCountAnchor uniformSqrtShiftedTarget uniformSqrtTarget
  dsimp only
  have h_frac_nonneg : 0 ≤ Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i) := by
    have h1 : 0 ≤ Real.sqrt (likelihood t) := Real.sqrt_nonneg _
    have h2 : 0 ≤ ∑ i, Real.sqrt (likelihood i) := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
    positivity
  have h_den_pos : 0 < ∑ i, Real.sqrt (likelihood i) := by
    have h2 : 0 ≤ ∑ i, Real.sqrt (likelihood i) := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
    exact lt_of_le_of_ne h2 hnorm.symm
  have h_frac_le_one : Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i) ≤ 1 := by
    have hsum : Real.sqrt (likelihood t) ≤ ∑ i, Real.sqrt (likelihood i) :=
      Finset.single_le_sum (fun i _ => Real.sqrt_nonneg _) (Finset.mem_univ t)
    exact (div_le_one₀ h_den_pos).mpr hsum
  have h_shift : ((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) =
      (N : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) + (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) := by ring
  have h_floor_le := Nat.floor_le (uniformSqrtShiftedTarget_nonneg likelihood N t)
  have h_le_floor_add_one := Nat.lt_floor_add_one (uniformSqrtShiftedTarget likelihood N t)
  have h_T_frac_le_T : (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) ≤ T := by
    calc
      (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))
          ≤ (T : ℝ) * 1 := mul_le_mul_of_nonneg_left h_frac_le_one (by positivity)
      _ = T := mul_one _
  have h_pos_T : 0 ≤ (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) := mul_nonneg (by positivity) h_frac_nonneg
  have h_pos_T_num : 0 ≤ (T : ℝ) := by positivity
  rw [abs_lt]
  constructor
  · unfold uniformSqrtShiftedTarget at h_floor_le h_le_floor_add_one
    linarith
  · unfold uniformSqrtShiftedTarget at h_floor_le h_le_floor_add_one
    linarith

theorem uniformSqrtLowerAnchor_abs_close {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0)
    (h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t) :
    |((uniformSqrtLowerAnchor likelihood N).count t : ℝ) -
      uniformSqrtTarget likelihood N t| < (T : ℝ) + 1 := by
  unfold uniformSqrtLowerAnchor uniformSqrtShiftedTarget uniformSqrtTarget
  dsimp only
  have h_frac_nonneg : 0 ≤ Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i) := by
    have h1 : 0 ≤ Real.sqrt (likelihood t) := Real.sqrt_nonneg _
    have h2 : 0 ≤ ∑ i, Real.sqrt (likelihood i) := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
    positivity
  have h_den_pos : 0 < ∑ i, Real.sqrt (likelihood i) := by
    have h2 : 0 ≤ ∑ i, Real.sqrt (likelihood i) := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
    exact lt_of_le_of_ne h2 hnorm.symm
  have h_frac_le_one : Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i) ≤ 1 := by
    have hsum : Real.sqrt (likelihood t) ≤ ∑ i, Real.sqrt (likelihood i) :=
      Finset.single_le_sum (fun i _ => Real.sqrt_nonneg _) (Finset.mem_univ t)
    exact (div_le_one₀ h_den_pos).mpr hsum
  have h_shift : ((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) =
      (N : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) + (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) := by ring
  have h_floor_le := Nat.floor_le (uniformSqrtShiftedTarget_nonneg likelihood N t)
  have h_le_floor_add_one := Nat.lt_floor_add_one (uniformSqrtShiftedTarget likelihood N t)
  have h_T_frac_le_T : (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) ≤ T := by
    calc
      (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))
          ≤ (T : ℝ) * 1 := mul_le_mul_of_nonneg_left h_frac_le_one (by positivity)
      _ = T := mul_one _
  have h_pos_T : 0 ≤ (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) := mul_nonneg (by positivity) h_frac_nonneg
  have hT_ge_1 : 1 ≤ (T : ℝ) := by exact_mod_cast NeZero.one_le
  have h_sub : ((⌊((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))⌋₊ - 1 : ℕ) : ℝ) ≤
      (⌊((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))⌋₊ : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  have h_sub_lower : (⌊((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))⌋₊ : ℝ) - 1 ≤
      ((⌊((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))⌋₊ - 1 : ℕ) : ℝ) := by
    have hge1 : 1 ≤ ⌊((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))⌋₊ := Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
    rw [Nat.cast_sub hge1, Nat.cast_one]
  rw [abs_lt]
  constructor
  · unfold uniformSqrtShiftedTarget at h_floor_le h_le_floor_add_one
    linarith
  · unfold uniformSqrtShiftedTarget at h_floor_le h_le_floor_add_one
    linarith

noncomputable def sqrtLikelihoodProfile {T : ℕ}
    (likelihood : ItemType T → ℝ) : GammaHomogeneityProfile T where
  gamma := 1 / 2
  targetWeight := fun t => Real.sqrt (likelihood t)

noncomputable def uniformSqrtMinShare {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) : ℝ :=
  EconCSLib.finiteMin
    (fun t : ItemType T =>
      Real.sqrt (likelihood t) / ∑ i : ItemType T, Real.sqrt (likelihood i))

theorem uniformSqrtMinShare_le_share {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (t : ItemType T) :
    uniformSqrtMinShare likelihood ≤
      Real.sqrt (likelihood t) / ∑ i : ItemType T, Real.sqrt (likelihood i) := by
  unfold uniformSqrtMinShare
  exact EconCSLib.finiteMin_le
    (fun t : ItemType T =>
      Real.sqrt (likelihood t) / ∑ i : ItemType T, Real.sqrt (likelihood i)) t

theorem uniformSqrtTarget_le_shiftedTarget {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (hnorm : ∑ i : ItemType T, Real.sqrt (likelihood i) ≠ 0) :
    uniformSqrtTarget likelihood N t ≤ uniformSqrtShiftedTarget likelihood N t := by
  unfold uniformSqrtTarget uniformSqrtShiftedTarget
  have hden_nonneg : 0 ≤ ∑ i : ItemType T, Real.sqrt (likelihood i) :=
    Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hden_pos : 0 < ∑ i : ItemType T, Real.sqrt (likelihood i) :=
    lt_of_le_of_ne hden_nonneg hnorm.symm
  have hfrac_nonneg :
      0 ≤ Real.sqrt (likelihood t) / ∑ i : ItemType T, Real.sqrt (likelihood i) :=
    div_nonneg (Real.sqrt_nonneg _) (le_of_lt hden_pos)
  nlinarith [show (0 : ℝ) ≤ T by positivity]

theorem uniformTopK_eligible_of_paper_min_share_bound {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N k : ℕ)
    (hnorm : ∑ i : ItemType T, Real.sqrt (likelihood i) ≠ 0)
    (hbound :
      (k : ℝ) + 1 ≤ (N : ℝ) * uniformSqrtMinShare likelihood - T) :
    ∀ t, (k : ℝ) + 1 ≤ uniformSqrtShiftedTarget likelihood N t := by
  intro t
  have hmin_le := uniformSqrtMinShare_le_share likelihood t
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have htarget_bound :
      (k : ℝ) + 1 ≤ uniformSqrtTarget likelihood N t := by
    unfold uniformSqrtTarget
    nlinarith [mul_le_mul_of_nonneg_left hmin_le hN_nonneg,
      show (0 : ℝ) ≤ T by positivity]
  exact le_trans htarget_bound
    (uniformSqrtTarget_le_shiftedTarget likelihood N t hnorm)

namespace sqrtLikelihoodProfile

@[simp] theorem normalizer_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) :
    (sqrtLikelihoodProfile likelihood).normalizer =
      ∑ t : ItemType T, Real.sqrt (likelihood t) := by
  rfl

theorem targetShare_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0) :
    (sqrtLikelihoodProfile likelihood).targetShare t =
      Real.sqrt (likelihood t) /
        ∑ i : ItemType T, Real.sqrt (likelihood i) := by
  exact GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero
    (G := sqrtLikelihoodProfile likelihood) (t := t) (by simpa using hnorm)

theorem approx_of_count_abs_error {T : ℕ}
    (likelihood : ItemType T → ℝ) (a : CountAllocation T) {N : ℕ} {C : ℝ}
    (hN : EconCSLib.Allocation.total a = N) (hNpos : 0 < N)
    (hclose :
      ∀ t,
        |(a.count t : ℝ) -
          (N : ℝ) * (sqrtLikelihoodProfile likelihood).targetShare t| ≤ C) :
    (sqrtLikelihoodProfile likelihood).Approx a (C / (N : ℝ)) := by
  exact GammaHomogeneityProfile.approx_of_count_abs_error
    (sqrtLikelihoodProfile likelihood) a hN hNpos hclose

end sqrtLikelihoodProfile

namespace UniformTopOne

def StrictRoundingExchangeCertificateBetween {T : ℕ}
    (likelihood : ItemType T → ℝ)
    (lower upper : CountAllocation T) : Prop :=
  ∀ high low,
    0 < lower.count low →
      (likelihood high * (1 / ((upper.count high + 1 : ℝ) * (upper.count high + 2 : ℝ)))) <
        (likelihood low * (1 / ((lower.count low : ℝ) * (lower.count low + 1 : ℝ))))

theorem forwardMarginal_le_backwardMarginal_of_optimum {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hne : src ≠ dst)
    (hcan : EconCSLib.Allocation.CanMoveOne a src) :
    likelihood dst *
        (1 / ((a.count dst + 1 : ℝ) * (a.count dst + 2 : ℝ))) ≤
      likelihood src *
        (1 / ((a.count src : ℝ) * (a.count src + 1 : ℝ))) := by
  have h := ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum (uniformTopOneConsumptionModel likelihood) N hopt hne hcan
  unfold ConsumptionModel.weightedForwardMarginal ConsumptionModel.weightedBackwardMarginal at h
  unfold ConsumptionModel.marginalValue at h
  unfold EconCSLib.Allocation.marginal at h
  unfold uniformTopOneConsumptionModel at h
  dsimp only at h
  have hq : 0 < a.count src := hcan
  have hne0 : a.count src ≠ 0 := ne_of_gt hcan
  rw [dif_neg hne0] at h
  rw [uniformTopOneValue_succ_sub] at h
  rw [uniformTopOneValue_sub_pred hq] at h
  exact h

theorem noRoundingCrossingBetween_of_strictExchangeCertificate {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ)
    {a lower upper : CountAllocation T}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hlike_nonneg : ∀ t, 0 ≤ likelihood t)
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hcert : StrictRoundingExchangeCertificateBetween likelihood lower upper) :
    EconCSLib.FiniteRounding.NoRoundingCrossingBetween
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t) := by
  intro high low
  rintro ⟨h_high, h_low⟩
  have h_low_pos : 0 < lower.count low := by exact lt_of_le_of_lt (Nat.zero_le _) h_low
  have h_can : EconCSLib.Allocation.CanMoveOne a high := by
    exact lt_of_lt_of_le (Nat.succ_pos _) h_high
  have hne : high ≠ low := by
    rintro rfl
    have hc := calc
      upper.count high + 2 ≤ a.count high + 1 := Nat.add_le_add_right h_high 1
      _ ≤ lower.count high := h_low
      _ ≤ upper.count high := horder high
    linarith
  have h_foc := forwardMarginal_le_backwardMarginal_of_optimum likelihood N hopt hne h_can
  have h_cert_eval := hcert high low h_low_pos
  have hu_le : (upper.count high + 1 : ℝ) * (upper.count high + 2 : ℝ) ≤ (a.count high : ℝ) * (a.count high + 1 : ℝ) := by
    have h1 : (upper.count high + 1 : ℝ) ≤ (a.count high : ℝ) := by exact_mod_cast h_high
    have h2 : (upper.count high + 2 : ℝ) ≤ (a.count high + 1 : ℝ) := by exact_mod_cast (Nat.add_le_add_right h_high 1)
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hv_le : (a.count low + 1 : ℝ) * (a.count low + 2 : ℝ) ≤ (lower.count low : ℝ) * (lower.count low + 1 : ℝ) := by
    have h1 : (a.count low + 1 : ℝ) ≤ (lower.count low : ℝ) := by exact_mod_cast h_low
    have h2 : (a.count low + 2 : ℝ) ≤ (lower.count low + 1 : ℝ) := by exact_mod_cast (Nat.add_le_add_right h_low 1)
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have h_lx_le : likelihood high * (1 / ((a.count high : ℝ) * (a.count high + 1 : ℝ))) ≤ likelihood high * (1 / ((upper.count high + 1 : ℝ) * (upper.count high + 2 : ℝ))) := by
    gcongr
    exact hlike_nonneg high
  have h_ly_ge : likelihood low * (1 / ((lower.count low : ℝ) * (lower.count low + 1 : ℝ))) ≤ likelihood low * (1 / ((a.count low + 1 : ℝ) * (a.count low + 2 : ℝ))) := by
    gcongr
    exact hlike_nonneg low
  linarith

theorem strictRoundingExchangeCertificateBetween_of_shifted_target {T : ℕ}
    (likelihood : ItemType T → ℝ)
    (lower upper : CountAllocation T)
    (scale : ℝ) (shift : ItemType T → ℝ)
    (hscale_pos : 0 < scale)
    (hlike : ∀ t, likelihood t = scale * (shift t) ^ 2)
    (hshift_nonneg : ∀ t, 0 ≤ shift t)
    (hupper : ∀ t, shift t ≤ (upper.count t : ℝ) + 1)
    (hlower : ∀ t, 0 < lower.count t → (lower.count t : ℝ) + 1 ≤ shift t) :
    StrictRoundingExchangeCertificateBetween likelihood lower upper := by
  intro high low h_low_pos
  have hu : shift high ≤ (upper.count high : ℝ) + 1 := hupper high
  have hl : (lower.count low : ℝ) + 1 ≤ shift low := hlower low h_low_pos
  have h_sh_pos : 0 ≤ shift high := hshift_nonneg high
  have h_u_pos : 0 ≤ (upper.count high : ℝ) + 1 := by positivity
  have hs_h_sq_le : (shift high) ^ 2 ≤ ((upper.count high : ℝ) + 1) ^ 2 := by nlinarith
  have hs_h_lt : (shift high) ^ 2 / (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2)) < 1 := by
    rw [div_lt_iff₀ (by positivity)]
    calc
      (shift high) ^ 2 ≤ ((upper.count high : ℝ) + 1) ^ 2 := hs_h_sq_le
      _ = ((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 1) := by ring
      _ < ((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2) := by nlinarith
      _ = 1 * (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2)) := by ring
  have h_l_pos : 0 ≤ (lower.count low : ℝ) + 1 := by positivity
  have h_sl_pos : 0 ≤ shift low := hshift_nonneg low
  have hs_l_sq_ge : ((lower.count low : ℝ) + 1) ^ 2 ≤ (shift low) ^ 2 := by nlinarith
  have hs_l_gt : 1 < (shift low) ^ 2 / ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1)) := by
    rw [lt_div_iff₀ (by positivity)]
    calc
      1 * ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1)) = (lower.count low : ℝ) * ((lower.count low : ℝ) + 1) := by ring
      _ < ((lower.count low : ℝ) + 1) * ((lower.count low : ℝ) + 1) := by nlinarith
      _ = ((lower.count low : ℝ) + 1) ^ 2 := by ring
      _ ≤ (shift low) ^ 2 := hs_l_sq_ge
  rw [hlike high, hlike low]
  calc
    scale * (shift high) ^ 2 * (1 / (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2)))
        = scale * ((shift high) ^ 2 / (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2))) := by ring
    _ < scale * 1 := mul_lt_mul_of_pos_left hs_h_lt hscale_pos
    _ = scale * 1 := by rfl
    _ < scale * ((shift low) ^ 2 / ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1))) := by
      exact mul_lt_mul_of_pos_left hs_l_gt hscale_pos
    _ = scale * (shift low) ^ 2 * (1 / ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1))) := by ring

end UniformTopOne

namespace UniformTopK

theorem weightedForwardMarginal_eq_of_le {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ) (t : ItemType T) {q : ℕ}
    (hkq : k ≤ q) :
    (uniformTopKConsumptionModel likelihood k).weightedForwardMarginal t q =
      likelihood t *
        (uniformTopKFactor k / ((q + 1 : ℝ) * (q + 2 : ℝ))) := by
  unfold ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
    EconCSLib.Allocation.marginal uniformTopKConsumptionModel
  dsimp only
  rw [uniformTopKValue_succ_sub_of_le hkq]

theorem weightedBackwardMarginal_eq_of_le {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ) (t : ItemType T) {q : ℕ}
    (hkq : k ≤ q) (hq : 0 < q) :
    (uniformTopKConsumptionModel likelihood k).weightedBackwardMarginal t q =
      likelihood t *
        (uniformTopKFactor k / ((q : ℝ) * (q + 1 : ℝ))) := by
  unfold ConsumptionModel.weightedBackwardMarginal uniformTopKConsumptionModel
  dsimp only
  have hq_ne : ¬ q = 0 := ne_of_gt hq
  simp [hq_ne, uniformTopKValue_sub_pred_of_le hkq hq]

theorem strictRoundingExchangeCertificateBetween_of_shifted_target {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (lower upper : CountAllocation T)
    (scale : ℝ) (shift : ItemType T → ℝ)
    (hk_pos : 0 < k)
    (hscale_pos : 0 < scale)
    (hlike : ∀ t, likelihood t = scale * (shift t) ^ 2)
    (hshift_nonneg : ∀ t, 0 ≤ shift t)
    (hupper_tail : ∀ t, k ≤ upper.count t)
    (hlower_tail : ∀ t, k ≤ lower.count t)
    (hupper : ∀ t, shift t ≤ (upper.count t : ℝ) + 1)
    (hlower : ∀ t, 0 < lower.count t → (lower.count t : ℝ) + 1 ≤ shift t) :
    (uniformTopKConsumptionModel likelihood k).StrictRoundingExchangeCertificateBetween
      lower upper := by
  intro high low h_low_pos
  rw [weightedForwardMarginal_eq_of_le likelihood k high (hupper_tail high),
    weightedBackwardMarginal_eq_of_le likelihood k low (hlower_tail low) h_low_pos,
    hlike high, hlike low]
  have hcoef_pos : 0 < scale * uniformTopKFactor k :=
    mul_pos hscale_pos (uniformTopKFactor_pos hk_pos)
  have hu : shift high ≤ (upper.count high : ℝ) + 1 := hupper high
  have hl : (lower.count low : ℝ) + 1 ≤ shift low := hlower low h_low_pos
  have h_sh_pos : 0 ≤ shift high := hshift_nonneg high
  have hs_h_sq_le : (shift high) ^ 2 ≤ ((upper.count high : ℝ) + 1) ^ 2 := by
    nlinarith
  have hs_h_lt :
      (shift high) ^ 2 /
          (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2)) < 1 := by
    rw [div_lt_iff₀ (by positivity)]
    calc
      (shift high) ^ 2 ≤ ((upper.count high : ℝ) + 1) ^ 2 := hs_h_sq_le
      _ = ((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 1) := by ring
      _ < ((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2) := by nlinarith
      _ = 1 * (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2)) := by ring
  have h_sl_pos : 0 ≤ shift low := hshift_nonneg low
  have hs_l_sq_ge : ((lower.count low : ℝ) + 1) ^ 2 ≤ (shift low) ^ 2 := by
    nlinarith
  have hs_l_gt :
      1 < (shift low) ^ 2 /
          ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1)) := by
    rw [lt_div_iff₀ (by positivity)]
    calc
      1 * ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1)) =
          (lower.count low : ℝ) * ((lower.count low : ℝ) + 1) := by ring
      _ < ((lower.count low : ℝ) + 1) * ((lower.count low : ℝ) + 1) := by nlinarith
      _ = ((lower.count low : ℝ) + 1) ^ 2 := by ring
      _ ≤ (shift low) ^ 2 := hs_l_sq_ge
  calc
    scale * (shift high) ^ 2 *
        (uniformTopKFactor k /
          (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2)))
        = (scale * uniformTopKFactor k) *
            ((shift high) ^ 2 /
              (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2))) := by ring
    _ < (scale * uniformTopKFactor k) * 1 :=
          mul_lt_mul_of_pos_left hs_h_lt hcoef_pos
    _ < (scale * uniformTopKFactor k) *
            ((shift low) ^ 2 /
              ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1))) :=
          mul_lt_mul_of_pos_left hs_l_gt hcoef_pos
    _ = scale * (shift low) ^ 2 *
        (uniformTopKFactor k /
          ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1))) := by ring

end UniformTopK

namespace UniformRounding

theorem count_close_of_no_rounding_crossing_between {T : ℕ}
    (a lower upper : CountAllocation T) {N L U : ℕ}
    (ha : EconCSLib.Allocation.total a = N)
    (hlower : EconCSLib.Allocation.total lower = L)
    (hupper : EconCSLib.Allocation.total upper = U)
    (hNlt : N < L + Fintype.card (ItemType T) + 1)
    (hUlt : U < N + Fintype.card (ItemType T) + 1)
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hno :
      EconCSLib.FiniteRounding.NoRoundingCrossingBetween
        (fun t : ItemType T => a.count t)
        (fun t : ItemType T => lower.count t)
        (fun t : ItemType T => upper.count t)) :
    ∀ t : ItemType T,
      lower.count t < a.count t + Fintype.card (ItemType T) + 1 ∧
        a.count t < upper.count t + Fintype.card (ItemType T) + 1 := by
  intro t
  constructor
  · exact EconCSLib.FiniteRounding.NoRoundingCrossingBetween.lower_lt_count_add_card
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t)
      t ha hupper hUlt horder hno
  · exact EconCSLib.FiniteRounding.NoRoundingCrossingBetween.count_lt_upper_add_card
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t)
      t ha hlower hNlt horder hno
end UniformRounding

end PRPKG24AccuracyDiversity
