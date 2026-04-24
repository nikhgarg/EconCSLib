import AccuracyDiversity.Bernoulli
import AccuracyDiversity.Exchange

namespace AccuracyDiversity

namespace BernoulliSatisfactionModel

/-- Weighted forward marginal in the Bernoulli one-consumption model. -/
theorem weightedForwardMarginal_toConsumptionModel {T : ℕ}
    (B : BernoulliSatisfactionModel T) (t : ItemType T) (q : ℕ) :
    (B.toConsumptionModel).weightedForwardMarginal t q =
      B.likelihood t * B.successProb t * (1 - B.successProb t) ^ q := by
  unfold ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
    DecisionCore.Allocation.marginal toConsumptionModel
  rw [bernoulliAtLeastOneValue_succ_sub]
  ring

/-- Weighted backward marginal in the Bernoulli one-consumption model. -/
theorem weightedBackwardMarginal_toConsumptionModel {T : ℕ}
    (B : BernoulliSatisfactionModel T) (t : ItemType T) {q : ℕ}
    (hq : 0 < q) :
    (B.toConsumptionModel).weightedBackwardMarginal t q =
      B.likelihood t * B.successProb t * (1 - B.successProb t) ^ (q - 1) := by
  have hne : ¬ q = 0 := ne_of_gt hq
  unfold ConsumptionModel.weightedBackwardMarginal toConsumptionModel
  simp [hne]
  rw [bernoulliAtLeastOneValue_sub_pred (p := B.successProb t) hq]
  ring

/--
Paper-facing first-order condition for the finite Bernoulli specialization:
an optimal allocation has no exchange whose destination marginal exceeds the
source's last-item marginal.
-/
theorem forwardMarginal_le_backwardMarginal_of_optimum {T : ℕ}
    (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : DecisionCore.Allocation.CanMoveOne a src) :
    B.likelihood dst * B.successProb dst *
        (1 - B.successProb dst) ^ (a.count dst) ≤
      B.likelihood src * B.successProb src *
        (1 - B.successProb src) ^ (a.count src - 1) := by
  have h :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := B.toConsumptionModel) (N := N) (a := a)
      (src := src) (dst := dst) hopt hne hcan
  rw [weightedForwardMarginal_toConsumptionModel
    (B := B) (t := dst) (q := a.count dst)] at h
  rw [weightedBackwardMarginal_toConsumptionModel
    (B := B) (t := src) (q := a.count src) hcan] at h
  exact h

end BernoulliSatisfactionModel
end AccuracyDiversity
