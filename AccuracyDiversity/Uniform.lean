import AccuracyDiversity.Exchange
import Mathlib.Data.Real.Sqrt

open scoped BigOperators

namespace AccuracyDiversity

/--
Expected maximum of `q` iid `U([0,1])` draws.

For `q = 0` this gives `0`, matching the empty recommendation value. For
positive `q`, the value is `q / (q + 1) = 1 - 1 / (q + 1)`.
-/
noncomputable def uniformTopOneValue (q : ℕ) : ℝ :=
  1 - 1 / (q + 1 : ℝ)

@[simp] theorem uniformTopOneValue_zero :
    uniformTopOneValue 0 = 0 := by
  norm_num [uniformTopOneValue]

/-- Closed form for the one-step marginal of the uniform top-one value. -/
theorem uniformTopOneValue_succ_sub (q : ℕ) :
    uniformTopOneValue (q + 1) - uniformTopOneValue q =
      1 / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by
  have hq1 : (q + 1 : ℝ) ≠ 0 := by positivity
  have hq2 : (q + 2 : ℝ) ≠ 0 := by positivity
  unfold uniformTopOneValue
  field_simp [hq1, hq2]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf

/--
Closed form for the value lost by removing the last recommendation from the
uniform top-one value.
-/
theorem uniformTopOneValue_sub_pred {q : ℕ} (hq : 0 < q) :
    uniformTopOneValue q - uniformTopOneValue (q - 1) =
      1 / ((q : ℝ) * (q + 1 : ℝ)) := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hq1 : (q + 1 : ℝ) ≠ 0 := by positivity
  have hpred : ((q - 1 : ℕ) + 1 : ℝ) = (q : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  have hpred_sub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    linarith
  unfold uniformTopOneValue
  field_simp [hq0, hq1, hpred, hpred_sub]
  rw [hpred_sub]
  ring_nf

/-- Consumption model for the paper's `U([0,1])`, `k = 1` objective. -/
noncomputable def uniformTopOneConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) : ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := fun _ q => uniformTopOneValue q

/--
The `1/2`-homogeneity profile induced by square roots of type likelihoods.

This is the target profile in Proposition 2 for uniform conditional item
values.
-/
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
  exact GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero
    (G := sqrtLikelihoodProfile likelihood) (t := t) (by simpa using hnorm)

/--
Count closeness to the square-root target implies approximate
`1/2`-homogeneity.

This is the representation-only bridge used after the real-relaxation and
integer-rounding part of Proposition 2.
-/
theorem approx_of_count_abs_error {T : ℕ}
    (likelihood : ItemType T → ℝ) (a : CountAllocation T) {N : ℕ} {C : ℝ}
    (hN : DecisionCore.Allocation.total a = N) (hNpos : 0 < N)
    (hclose :
      ∀ t,
        |(a.count t : ℝ) -
          (N : ℝ) * (sqrtLikelihoodProfile likelihood).targetShare t| ≤ C) :
    (sqrtLikelihoodProfile likelihood).Approx a (C / (N : ℝ)) := by
  exact GammaHomogeneityProfile.approx_of_count_abs_error
    (sqrtLikelihoodProfile likelihood) a hN hNpos hclose

end sqrtLikelihoodProfile

namespace UniformTopOne

@[simp] theorem toConsumptionModel_likelihood {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T) :
    (uniformTopOneConsumptionModel likelihood).likelihood t = likelihood t := rfl

@[simp] theorem toConsumptionModel_valueOfCount {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T) (q : ℕ) :
    (uniformTopOneConsumptionModel likelihood).valueOfCount t q =
      uniformTopOneValue q := rfl

@[simp] theorem marginalValue_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T) (q : ℕ) :
    (uniformTopOneConsumptionModel likelihood).marginalValue t q =
      1 / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by
  rw [ConsumptionModel.marginalValue, DecisionCore.Allocation.marginal]
  exact uniformTopOneValue_succ_sub q

@[simp] theorem weightedForwardMarginal_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T) (q : ℕ) :
    (uniformTopOneConsumptionModel likelihood).weightedForwardMarginal t q =
      likelihood t * (1 / ((q + 1 : ℝ) * (q + 2 : ℝ))) := by
  rw [ConsumptionModel.weightedForwardMarginal, marginalValue_eq]
  rfl

@[simp] theorem weightedBackwardMarginal_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T) {q : ℕ} (hq : 0 < q) :
    (uniformTopOneConsumptionModel likelihood).weightedBackwardMarginal t q =
      likelihood t * (1 / ((q : ℝ) * (q + 1 : ℝ))) := by
  rw [ConsumptionModel.weightedBackwardMarginal]
  simp [hq.ne', uniformTopOneValue_sub_pred hq]

/--
Finite first-order condition for the paper's `U([0,1])`, `k = 1` objective.

At an optimal fixed-total allocation, the weighted marginal gain from adding
one item to any destination is at most the weighted marginal loss from any
positive source.
-/
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
  have h :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := uniformTopOneConsumptionModel likelihood) N hopt hne hcan
  rw [weightedForwardMarginal_eq] at h
  rw [weightedBackwardMarginal_eq likelihood src hcan] at h
  exact h

end UniformTopOne

end AccuracyDiversity
