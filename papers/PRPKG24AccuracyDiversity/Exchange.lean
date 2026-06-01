import PRPKG24AccuracyDiversity.Optimization
import EconCSLib.Foundations.Math.FiniteSum
import EconCSLib.Foundations.Math.FiniteRounding

namespace PRPKG24AccuracyDiversity

namespace ConsumptionModel

/-- Move one recommendation from type `src` to type `dst`. -/
def moveOne {T : ℕ}
    (a : CountAllocation T) (src dst : ItemType T) : CountAllocation T :=
  EconCSLib.Allocation.moveOne a src dst

/-- Weighted forward marginal gain from adding one more item of type `t`. -/
noncomputable def weightedForwardMarginal {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) (q : ℕ) : ℝ :=
  M.likelihood t * M.marginalValue t q

/--
Weighted value lost by removing the `q`-th item of type `t`.
The value is set to `0` at `q = 0`; exchange lemmas should also assume `0 < q`.
-/
noncomputable def weightedBackwardMarginal {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) (q : ℕ) : ℝ :=
  if h : q = 0 then 0 else M.likelihood t * (M.valueOfCount t q - M.valueOfCount t (q - 1))

/-- The one-step exchange condition used in finite allocation optimality arguments. -/
def ExchangeCondition {T : ℕ}
    (M : ConsumptionModel T) (a : CountAllocation T) (src dst : ItemType T) : Prop :=
  weightedBackwardMarginal M src (a.count src) ≤ weightedForwardMarginal M dst (a.count dst)

/--
Target proposition for the finite exchange lemma:
if moving one count from `src` to `dst` loses no more than it gains, the objective weakly improves.
-/
def ExchangeImprovementTarget {T : ℕ} (M : ConsumptionModel T) : Prop :=
  ∀ a src dst,
    src ≠ dst →
    EconCSLib.Allocation.CanMoveOne a src →
    ExchangeCondition M a src dst →
    M.objective a ≤ M.objective (moveOne a src dst)

/--
Target proposition for local optimality:
if `a` is optimal at total size `N`, every valid one-step exchange has nonpositive gain.
-/
def NoProfitableExchangeAtOptimumTarget {T : ℕ} (M : ConsumptionModel T) (N : ℕ) : Prop :=
  ∀ a src dst,
    M.IsOptimalAtTotal N a →
    src ≠ dst →
    EconCSLib.Allocation.CanMoveOne a src →
    M.objective (moveOne a src dst) ≤ M.objective a

@[simp] theorem moveOne_eq_allocation_moveOne {T : ℕ}
    (a : CountAllocation T) (src dst : ItemType T) :
    moveOne a src dst = EconCSLib.Allocation.moveOne a src dst := rfl

@[simp] theorem weightedForwardMarginal_apply {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) (q : ℕ) :
    weightedForwardMarginal M t q = M.likelihood t * M.marginalValue t q := rfl

/-- Moving one item from a positive source to a distinct destination preserves total size. -/
theorem total_moveOne_eq {T : ℕ} (a : CountAllocation T)
    {src dst : ItemType T} (hne : src ≠ dst)
    (hcan : EconCSLib.Allocation.CanMoveOne a src) :
    EconCSLib.Allocation.total (moveOne a src dst) =
      EconCSLib.Allocation.total a := by
  classical
  unfold EconCSLib.Allocation.total
  have hsum :
      (∑ t : ItemType T, ((moveOne a src dst).count t : ℝ)) =
        (∑ t : ItemType T, (a.count t : ℝ)) +
          (((moveOne a src dst).count src : ℝ) - (a.count src : ℝ)) +
          (((moveOne a src dst).count dst : ℝ) - (a.count dst : ℝ)) := by
    exact EconCSLib.FiniteSum.sum_eq_sum_add_sub_add_sub_of_eq_off
      (f := fun t : ItemType T => ((moveOne a src dst).count t : ℝ))
      (g := fun t : ItemType T => (a.count t : ℝ))
      (a := src) (b := dst) hne
      (by
        intro x hxsrc hxdst
        unfold moveOne EconCSLib.Allocation.moveOne
        simp [hne, hxsrc, hxdst])
  have hreal : ((∑ t : ItemType T, (moveOne a src dst).count t : ℕ) : ℝ) =
      ((∑ t : ItemType T, a.count t : ℕ) : ℝ) := by
    norm_num only [Nat.cast_sum]
    rw [hsum]
    unfold moveOne EconCSLib.Allocation.moveOne
    have hle : 1 ≤ a.count src := Nat.succ_le_of_lt hcan
    have hsrc_sub : ((a.count src - 1 : ℕ) : ℝ) = (a.count src : ℝ) - 1 := by
      have hnat : a.count src - 1 + 1 = a.count src := Nat.sub_add_cancel hle
      have hcast := congrArg (fun q : ℕ => (q : ℝ)) hnat
      norm_num at hcast
      linarith
    simp [hne, hne.symm]
    rw [hsrc_sub]
    ring
  exact_mod_cast hreal

/--
Exact objective accounting for one valid exchange: the destination gains its
forward marginal and the source loses its backward marginal.
-/
theorem objective_moveOne_eq {T : ℕ} (M : ConsumptionModel T) (a : CountAllocation T)
    {src dst : ItemType T} (hne : src ≠ dst)
    (hcan : EconCSLib.Allocation.CanMoveOne a src) :
    M.objective (moveOne a src dst) =
      M.objective a - M.weightedBackwardMarginal src (a.count src) +
        M.weightedForwardMarginal dst (a.count dst) := by
  classical
  unfold objective EconCSLib.Allocation.objective
  have hsum :
      (∑ t : ItemType T,
          M.likelihood t * M.valueOfCount t ((moveOne a src dst).count t)) =
        (∑ t : ItemType T, M.likelihood t * M.valueOfCount t (a.count t)) +
          (M.likelihood src * M.valueOfCount src ((moveOne a src dst).count src) -
            M.likelihood src * M.valueOfCount src (a.count src)) +
          (M.likelihood dst * M.valueOfCount dst ((moveOne a src dst).count dst) -
            M.likelihood dst * M.valueOfCount dst (a.count dst)) := by
    exact EconCSLib.FiniteSum.sum_eq_sum_add_sub_add_sub_of_eq_off
      (f := fun t : ItemType T =>
        M.likelihood t * M.valueOfCount t ((moveOne a src dst).count t))
      (g := fun t : ItemType T => M.likelihood t * M.valueOfCount t (a.count t))
      (a := src) (b := dst) hne
      (by
        intro x hxsrc hxdst
        unfold moveOne EconCSLib.Allocation.moveOne
        simp [hne, hxsrc, hxdst])
  rw [hsum]
  unfold moveOne EconCSLib.Allocation.moveOne weightedBackwardMarginal
    weightedForwardMarginal marginalValue EconCSLib.Allocation.marginal
  have hsrc_ne_zero : ¬ a.count src = 0 := ne_of_gt hcan
  simp [hne, hne.symm, hsrc_ne_zero]
  ring

/-- The finite exchange-improvement target is closed by exact marginal accounting. -/
theorem exchangeImprovementTarget {T : ℕ} (M : ConsumptionModel T) :
    ExchangeImprovementTarget M := by
  intro a src dst hne hcan hcond
  rw [objective_moveOne_eq (M := M) (a := a) hne hcan]
  unfold ExchangeCondition at hcond
  linarith

/--
At any finite optimum, moving one item from a positive source to a distinct
destination cannot strictly improve the objective.
-/
theorem noProfitableExchangeAtOptimumTarget {T : ℕ} (M : ConsumptionModel T) (N : ℕ) :
    NoProfitableExchangeAtOptimumTarget M N := by
  intro a src dst hopt hne hcan
  exact hopt.2 (moveOne a src dst) (by
    change EconCSLib.Allocation.total (moveOne a src dst) = N
    rw [total_moveOne_eq (a := a) hne hcan]
    exact hopt.1)

/--
First-order finite optimality condition: at an optimum, the weighted marginal
gain from adding to `dst` cannot exceed the weighted marginal loss from `src`.
-/
theorem weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) {a : CountAllocation T}
    {src dst : ItemType T}
    (hopt : M.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : EconCSLib.Allocation.CanMoveOne a src) :
    weightedForwardMarginal M dst (a.count dst) ≤
      weightedBackwardMarginal M src (a.count src) := by
  have hno :=
    noProfitableExchangeAtOptimumTarget
      (M := M) N a src dst hopt hne hcan
  rw [objective_moveOne_eq (M := M) (a := a) hne hcan] at hno
  linarith

theorem marginalValue_antitone_of_diminishing {T : ℕ}
    (M : ConsumptionModel T) (hDR : M.HasDiminishingReturns)
    (t : ItemType T) {q r : ℕ} (hqr : q ≤ r) :
    M.marginalValue t r ≤ M.marginalValue t q := by
  exact Nat.le_induction (by rfl)
    (fun n _ ih => le_trans (hDR t n) ih) r hqr

theorem weightedForwardMarginal_antitone_of_diminishing {T : ℕ}
    (M : ConsumptionModel T) (hDR : M.HasDiminishingReturns)
    (hlike_nonneg : ∀ t, 0 ≤ M.likelihood t)
    (t : ItemType T) {q r : ℕ} (hqr : q ≤ r) :
    M.weightedForwardMarginal t r ≤ M.weightedForwardMarginal t q := by
  unfold weightedForwardMarginal
  exact mul_le_mul_of_nonneg_left
    (marginalValue_antitone_of_diminishing M hDR t hqr) (hlike_nonneg t)

theorem weightedBackwardMarginal_eq_weightedForwardMarginal_pred {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) {q : ℕ} (hq : 0 < q) :
    M.weightedBackwardMarginal t q = M.weightedForwardMarginal t (q - 1) := by
  unfold weightedBackwardMarginal weightedForwardMarginal marginalValue
    EconCSLib.Allocation.marginal
  have hq_ne : ¬ q = 0 := ne_of_gt hq
  have hq_cancel : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  simp [hq_ne, hq_cancel]

theorem weightedBackwardMarginal_le_weightedForwardMarginal_of_diminishing
    {T : ℕ} (M : ConsumptionModel T) (hDR : M.HasDiminishingReturns)
    (hlike_nonneg : ∀ t, 0 ≤ M.likelihood t)
    (t : ItemType T) {q r : ℕ} (hrq : r + 1 ≤ q) :
    M.weightedBackwardMarginal t q ≤ M.weightedForwardMarginal t r := by
  have hq_pos : 0 < q := lt_of_lt_of_le (Nat.succ_pos r) hrq
  rw [weightedBackwardMarginal_eq_weightedForwardMarginal_pred M t hq_pos]
  have hr_pred : r ≤ q - 1 := by omega
  exact weightedForwardMarginal_antitone_of_diminishing M hDR hlike_nonneg t hr_pred

def StrictRoundingExchangeCertificateBetween {T : ℕ}
    (M : ConsumptionModel T)
    (lower upper : CountAllocation T) : Prop :=
  ∀ high low,
    0 < lower.count low →
      M.weightedForwardMarginal high (upper.count high) <
        M.weightedBackwardMarginal low (lower.count low)

theorem noRoundingCrossingBetween_of_strictExchangeCertificate {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ)
    {a lower upper : CountAllocation T}
    (hopt : M.IsOptimalAtTotal N a)
    (hDR : M.HasDiminishingReturns)
    (hlike_nonneg : ∀ t, 0 ≤ M.likelihood t)
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hcert : M.StrictRoundingExchangeCertificateBetween lower upper) :
    EconCSLib.FiniteRounding.NoRoundingCrossingBetween
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t) := by
  intro high low
  rintro ⟨h_high, h_low⟩
  have h_low_pos : 0 < lower.count low := by
    exact lt_of_le_of_lt (Nat.zero_le _) h_low
  have h_can : EconCSLib.Allocation.CanMoveOne a high := by
    exact lt_of_lt_of_le (Nat.succ_pos _) h_high
  have hne : high ≠ low := by
    rintro rfl
    have hle : upper.count high + 1 ≤ upper.count high := by
      exact le_trans h_high
        (le_trans (Nat.le_of_succ_le h_low) (horder high))
    exact (Nat.not_succ_le_self (upper.count high)) hle
  have h_foc :=
    M.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      N hopt hne h_can
  have h_high_bound :
      M.weightedBackwardMarginal high (a.count high) ≤
        M.weightedForwardMarginal high (upper.count high) :=
    M.weightedBackwardMarginal_le_weightedForwardMarginal_of_diminishing
      hDR hlike_nonneg high h_high
  have h_low_bound :
      M.weightedBackwardMarginal low (lower.count low) ≤
        M.weightedForwardMarginal low (a.count low) :=
    M.weightedBackwardMarginal_le_weightedForwardMarginal_of_diminishing
      hDR hlike_nonneg low h_low
  have h_cert_eval := hcert high low h_low_pos
  linarith

end ConsumptionModel
end PRPKG24AccuracyDiversity
