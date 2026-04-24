import AccuracyDiversity.Bernoulli
import AccuracyDiversity.BernoulliExchange
import AccuracyDiversity.Optimization
import Mathlib.Algebra.BigOperators.Fin

namespace AccuracyDiversity

/-- Two-type allocation helper: type `0` gets `a`, type `1` gets `b`. -/
def twoTypeAllocation (a b : ℕ) : CountAllocation 2 where
  count := fun t => if t = 0 then a else b

@[simp] theorem twoTypeAllocation_zero (a b : ℕ) :
    (twoTypeAllocation a b).count (0 : ItemType 2) = a := by
  simp [twoTypeAllocation]

@[simp] theorem twoTypeAllocation_one (a b : ℕ) :
    (twoTypeAllocation a b).count (1 : ItemType 2) = b := by
  simp [twoTypeAllocation]

/-- Total size of the two-type allocation helper. -/
@[simp] theorem twoTypeAllocation_total (a b : ℕ) :
    DecisionCore.Allocation.total (twoTypeAllocation a b) = a + b := by
  simp [DecisionCore.Allocation.total, twoTypeAllocation, Fin.sum_univ_two]

/-- Objective expansion for two-type allocations. -/
theorem twoTypeAllocation_objective (M : ConsumptionModel 2) (a b : ℕ) :
    M.objective (twoTypeAllocation a b) =
      M.likelihood 0 * M.valueOfCount 0 a +
        M.likelihood 1 * M.valueOfCount 1 b := by
  simp [ConsumptionModel.objective, DecisionCore.Allocation.objective,
    twoTypeAllocation, Fin.sum_univ_two]

/--
Two-type Bernoulli first-order condition: if type `0` has positive count at an
optimum, the type-`1` forward marginal is bounded by type `0`'s last marginal.
-/
theorem twoTypeAllocation_forward_one_le_backward_zero_of_optimum
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (ha : 0 < a) :
    B.likelihood 1 * B.successProb 1 * (1 - B.successProb 1) ^ b ≤
      B.likelihood 0 * B.successProb 0 * (1 - B.successProb 0) ^ (a - 1) := by
  have h := B.forwardMarginal_le_backwardMarginal_of_optimum
    (N := N) (a := twoTypeAllocation a b)
    (src := (0 : ItemType 2)) (dst := (1 : ItemType 2)) hopt (by decide)
    (by simpa using ha)
  simpa using h

/--
The symmetric two-type first-order condition moving one count from type `1` to
type `0`.
-/
theorem twoTypeAllocation_forward_zero_le_backward_one_of_optimum
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (hb : 0 < b) :
    B.likelihood 0 * B.successProb 0 * (1 - B.successProb 0) ^ a ≤
      B.likelihood 1 * B.successProb 1 * (1 - B.successProb 1) ^ (b - 1) := by
  have h := B.forwardMarginal_le_backwardMarginal_of_optimum
    (N := N) (a := twoTypeAllocation a b)
    (src := (1 : ItemType 2)) (dst := (0 : ItemType 2)) hopt (by decide)
    (by simpa using hb)
  simpa using h

/-- A small milk/ice-cream style Bernoulli model: milk is more likely, ice cream is pickier. -/
noncomputable def milkIceCreamModel : BernoulliSatisfactionModel 2 where
  likelihood := fun t => if t = 0 then 0.7 else 0.3
  successProb := fun t => if t = 0 then 0.9 else 0.2

/-- A toy profile with equal representation across two types. -/
noncomputable def equalTwoTypeProfile : GammaHomogeneityProfile 2 where
  gamma := 0
  targetWeight := fun _ => 1

/-- A toy profile with weights matching the milk/ice-cream likelihoods. -/
noncomputable def likelihoodTwoTypeProfile : GammaHomogeneityProfile 2 where
  gamma := 1
  targetWeight := milkIceCreamModel.likelihood

#check milkIceCreamModel.toConsumptionModel
#check BernoulliSatisfactionModel.objective
#check ConsumptionModel.ApproxHomogeneityOfOptima
#check twoTypeAllocation

end AccuracyDiversity
