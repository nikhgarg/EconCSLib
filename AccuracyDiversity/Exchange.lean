import AccuracyDiversity.Optimization

namespace AccuracyDiversity

namespace ConsumptionModel

/-- Move one recommendation from type `src` to type `dst`. -/
def moveOne {T : ℕ}
    (a : CountAllocation T) (src dst : ItemType T) : CountAllocation T :=
  DecisionCore.Allocation.moveOne a src dst

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
    DecisionCore.Allocation.CanMoveOne a src →
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
    DecisionCore.Allocation.CanMoveOne a src →
    M.objective (moveOne a src dst) ≤ M.objective a

@[simp] theorem moveOne_eq_allocation_moveOne {T : ℕ}
    (a : CountAllocation T) (src dst : ItemType T) :
    moveOne a src dst = DecisionCore.Allocation.moveOne a src dst := rfl

@[simp] theorem weightedForwardMarginal_apply {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) (q : ℕ) :
    weightedForwardMarginal M t q = M.likelihood t * M.marginalValue t q := rfl

end ConsumptionModel
end AccuracyDiversity
