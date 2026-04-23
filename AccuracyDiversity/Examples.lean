import AccuracyDiversity.Bernoulli
import AccuracyDiversity.Optimization

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
