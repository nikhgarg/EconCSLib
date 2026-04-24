import AccuracyDiversity.Exchange
import EconCSLean.Math.FiniteRounding
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace AccuracyDiversity

noncomputable def uniformTopOneValue (q : ℕ) : ℝ :=
  1 - 1 / (q + 1 : ℝ)

@[simp] theorem uniformTopOneValue_zero :
    uniformTopOneValue 0 = 0 := by
  norm_num [uniformTopOneValue]

theorem uniformTopOneValue_succ_sub (q : ℕ) :
    uniformTopOneValue (q + 1) - uniformTopOneValue q =
      1 / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by
  sorry

theorem uniformTopOneValue_sub_pred {q : ℕ} (hq : 0 < q) :
    uniformTopOneValue q - uniformTopOneValue (q - 1) =
      1 / ((q : ℝ) * (q + 1 : ℝ)) := by
  sorry

noncomputable def uniformTopOneConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) : ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := fun _ q => uniformTopOneValue q

noncomputable def uniformSqrtTarget {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) : ℝ :=
  (N : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))

noncomputable def uniformSqrtShiftedTarget {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) : ℝ :=
  (N + T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))

noncomputable def uniformSqrtScale {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) : ℝ :=
  (∑ i, Real.sqrt (likelihood i)) ^ 2 / (N + T : ℝ) ^ 2

theorem likelihood_eq_scale_mul_shiftedTarget_sq {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (hlike_nonneg : ∀ i, 0 ≤ likelihood i)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    likelihood t =
      uniformSqrtScale likelihood N *
        (uniformSqrtShiftedTarget likelihood N t) ^ 2 := by
  sorry

theorem uniformSqrtShiftedTarget_nonneg {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) :
    0 ≤ uniformSqrtShiftedTarget likelihood N t := by
  sorry

theorem sum_uniformSqrtShiftedTarget {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    ∑ t, uniformSqrtShiftedTarget likelihood N t = N + T := by
  sorry

theorem sum_uniformSqrtShiftedTarget_nonneg {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) :
    0 ≤ ∑ t, uniformSqrtShiftedTarget likelihood N t :=
  sorry

theorem sqrtLikelihoodProfile_normalizer_ne_zero {T : ℕ}
    (likelihood : ItemType T → ℝ)
    (hsum : 0 < ∑ i, likelihood i) (hnonneg : ∀ i, 0 ≤ likelihood i) :
    ∑ i : ItemType T, Real.sqrt (likelihood i) ≠ 0 := by
  sorry

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
    (likelihood : ItemType T → ℝ) (N : ℕ) :
    (DecisionCore.Allocation.total (uniformSqrtUpperAnchor likelihood N) : ℝ) ≤ N + T := by
  sorry

theorem total_uniformSqrtLowerAnchor_le_N {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    (DecisionCore.Allocation.total (uniformSqrtLowerAnchor likelihood N) : ℝ) ≤ N := by
  sorry

theorem total_uniformSqrtLowerAnchor_eq_N_of_integers {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hintegers : ∀ t, uniformSqrtShiftedTarget likelihood N t = ⌊uniformSqrtShiftedTarget likelihood N t⌋₊) :
    (DecisionCore.Allocation.total (uniformSqrtLowerAnchor likelihood N) : ℝ) = N := by
  sorry

theorem total_uniformSqrtLowerAnchor_gt_N_sub_T_refined {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hnot_integers : ∃ t, uniformSqrtShiftedTarget likelihood N t ≠ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊) :
    (N : ℝ) - T < (DecisionCore.Allocation.total (uniformSqrtLowerAnchor likelihood N) : ℝ) := by
  sorry

theorem uniformSqrtUpperAnchor_shift_le {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) :
    uniformSqrtShiftedTarget likelihood N t ≤
      (uniformSqrtUpperAnchor likelihood N).count t + 1 := by
  sorry

theorem uniformSqrtLowerAnchor_le_shift {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (hlike_pos : ∀ i, 0 < likelihood i) :
    (uniformSqrtLowerAnchor likelihood N).count t + 1 ≤
      uniformSqrtShiftedTarget likelihood N t := by
  sorry

theorem uniformSqrtUpperAnchor_abs_close {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    |(uniformSqrtUpperAnchor likelihood N).count t -
      uniformSqrtTarget likelihood N t| < T + 1 := by
  sorry

theorem uniformSqrtLowerAnchor_abs_close {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0)
    (hlike_pos : ∀ i, 0 < likelihood i) :
    |(uniformSqrtLowerAnchor likelihood N).count t -
      uniformSqrtTarget likelihood N t| < T + 1 := by
  sorry

noncomputable def sqrtLikelihoodProfile {T : ℕ}
    (likelihood : ItemType T → ℝ) : GammaHomogeneityProfile T where
  gamma := 1 / 2
  targetWeight := fun t => Real.sqrt (likelihood t)

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
  sorry

theorem approx_of_count_abs_error {T : ℕ}
    (likelihood : ItemType T → ℝ) (a : CountAllocation T) {N : ℕ} {C : ℝ}
    (hN : DecisionCore.Allocation.total a = N) (hNpos : 0 < N)
    (hclose :
      ∀ t,
        |(a.count t : ℝ) -
          (N : ℝ) * (sqrtLikelihoodProfile likelihood).targetShare t| ≤ C) :
    (sqrtLikelihoodProfile likelihood).Approx a (C / (N : ℝ)) := by
  sorry

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
    (hcan : DecisionCore.Allocation.CanMoveOne a src) :
    likelihood dst *
        (1 / ((a.count dst + 1 : ℝ) * (a.count dst + 2 : ℝ))) ≤
      likelihood src *
        (1 / ((a.count src : ℝ) * (a.count src + 1 : ℝ))) := by
  sorry

theorem noRoundingCrossingBetween_of_strictExchangeCertificate {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ)
    {a lower upper : CountAllocation T}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hlike_nonneg : ∀ t, 0 ≤ likelihood t)
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hcert : StrictRoundingExchangeCertificateBetween likelihood lower upper) :
    EconCSLean.FiniteRounding.NoRoundingCrossingBetween
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t) := by
  sorry

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
  sorry

end UniformTopOne

namespace UniformRounding

theorem count_close_of_no_rounding_crossing_between {T : ℕ}
    (a lower upper : CountAllocation T) {N L U : ℕ}
    (ha : DecisionCore.Allocation.total a = N)
    (hlower : DecisionCore.Allocation.total lower = L)
    (hupper : DecisionCore.Allocation.total upper = U)
    (hNlt : N < L + Fintype.card (ItemType T))
    (hUlt : U < N + Fintype.card (ItemType T))
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hno :
      EconCSLean.FiniteRounding.NoRoundingCrossingBetween
        (fun t : ItemType T => a.count t)
        (fun t : ItemType T => lower.count t)
        (fun t : ItemType T => upper.count t)) :
    ∀ t : ItemType T,
      lower.count t < a.count t + Fintype.card (ItemType T) ∧
        a.count t < upper.count t + Fintype.card (ItemType T) := by
  intro t
  constructor
  · exact EconCSLean.FiniteRounding.NoRoundingCrossingBetween.lower_lt_count_add_card
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t)
      t ha hupper hUlt horder hno
  · exact EconCSLean.FiniteRounding.NoRoundingCrossingBetween.count_lt_upper_add_card
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t)
      t ha hlower hNlt horder hno

end UniformRounding

end AccuracyDiversity
