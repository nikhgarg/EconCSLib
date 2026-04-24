import AccuracyDiversity.Examples

/-!
# Paper-Facing Theorems: Reconciling the Accuracy-Diversity Trade-off

This file is the public theorem interface for the accuracy-diversity
formalization. Detailed allocation, representation, Bernoulli, and exchange
lemmas live in the sibling files.
-/

namespace AccuracyDiversity

namespace ConsumptionModel

/--
Finite optimizer existence for a fixed slate size.

Because count allocations of total `N` form a finite search space, every
consumption-constrained model over a nonempty finite type space has an
objective-maximizing allocation.
-/
theorem paper_finite_optimum_exists
    {T : ℕ} [Nonempty (ItemType T)] (M : ConsumptionModel T) (N : ℕ) :
    ∃ a : CountAllocation T, M.IsOptimalAtTotal N a := by
  exact M.exists_isOptimalAtTotal N

/--
Finite exchange-improvement theorem.

If moving one recommendation from `src` to `dst` loses no more weighted marginal
value than it gains, then the consumption-constrained objective weakly improves.
-/
theorem paper_finite_exchange_improvement
    {T : ℕ} (M : ConsumptionModel T) :
    M.ExchangeImprovementTarget := by
  exact M.exchangeImprovementTarget

/--
Finite first-order condition for optimal count allocations.

At a finite optimum, the weighted forward marginal of any destination is at most
the weighted backward marginal of any positive source.
-/
theorem paper_finite_optimum_first_order_condition
    {T : ℕ} (M : ConsumptionModel T) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : M.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : DecisionCore.Allocation.CanMoveOne a src) :
    M.weightedForwardMarginal dst (a.count dst) ≤
      M.weightedBackwardMarginal src (a.count src) := by
  exact M.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
    N hopt hne hcan

end ConsumptionModel

namespace BernoulliSatisfactionModel

/--
Bernoulli fixed-total optimizer existence.

The finite optimizer-existence theorem applies directly to the Bernoulli
satisfaction specialization of the consumption model.
-/
theorem paper_bernoulli_finite_optimum_exists
    {T : ℕ} [Nonempty (ItemType T)]
    (B : BernoulliSatisfactionModel T) (N : ℕ) :
    ∃ a : CountAllocation T, B.toConsumptionModel.IsOptimalAtTotal N a := by
  exact B.toConsumptionModel.exists_isOptimalAtTotal N

/--
Bernoulli specialization of the finite first-order condition.

For one-consumption Bernoulli satisfaction, an optimal allocation cannot have a
destination's Bernoulli marginal exceed a positive source's last-item marginal.
-/
theorem paper_bernoulli_optimum_first_order_condition
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : DecisionCore.Allocation.CanMoveOne a src) :
    B.likelihood dst * B.successProb dst *
        (1 - B.successProb dst) ^ (a.count dst) ≤
      B.likelihood src * B.successProb src *
        (1 - B.successProb src) ^ (a.count src - 1) := by
  exact B.forwardMarginal_le_backwardMarginal_of_optimum N hopt hne hcan

end BernoulliSatisfactionModel

/--
Two-type Bernoulli first-order condition from type `0` to type `1`.
-/
theorem paper_two_type_forward_one_le_backward_zero
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (ha : 0 < a) :
    B.likelihood 1 * B.successProb 1 * (1 - B.successProb 1) ^ b ≤
      B.likelihood 0 * B.successProb 0 * (1 - B.successProb 0) ^ (a - 1) := by
  exact twoTypeAllocation_forward_one_le_backward_zero_of_optimum B N a b hopt ha

/--
Two-type Bernoulli first-order condition from type `1` to type `0`.
-/
theorem paper_two_type_forward_zero_le_backward_one
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (hb : 0 < b) :
    B.likelihood 0 * B.successProb 0 * (1 - B.successProb 0) ^ a ≤
      B.likelihood 1 * B.successProb 1 * (1 - B.successProb 1) ^ (b - 1) := by
  exact twoTypeAllocation_forward_zero_le_backward_one_of_optimum B N a b hopt hb

end AccuracyDiversity
