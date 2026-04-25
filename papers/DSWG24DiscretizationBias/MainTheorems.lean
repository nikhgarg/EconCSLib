import EconCSLib.Foundations.Optimization.Argmax

/-!
# Paper-Facing Theorems: Addressing Discretization-Induced Bias

This file is the public theorem interface for the current discretization-bias
formalization. It currently closes the finite deterministic Bayes-score core of
Theorem 2(ii): a pointwise argmax rule maximizes expected accuracy when accuracy
is evaluated by Bayes posterior scores.
-/

namespace DSWG24DiscretizationBias

open scoped BigOperators

/--
Finite deterministic form of Theorem 2(i)'s existence claim.

For a finite dataset and finite nonempty action/label set, every real-valued
objective over deterministic decision rules has an optimal deterministic rule.
The paper's fidelity/accuracy objective can instantiate `objective`.
-/
theorem paper_theorem2i_finite_objective_optimizer_exists
    {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
    (objective : (ι → α) → ℝ) :
    ∃ opt : ι → α, ∀ rule : ι → α, objective rule ≤ objective opt := by
  exact EconCSLib.Decision.exists_maximizingDecisionRule objective

/--
Finite deterministic form of Theorem 2(ii) from
*Addressing Discretization-Induced Bias in Demographic Prediction*.

For a finite dataset `ι`, label set `α`, and Bayes posterior score
`posterior i a`, any rule `argmaxRule` that pointwise maximizes this posterior
score also maximizes empirical Bayes-score accuracy among deterministic
decision rules.
-/
theorem paper_theorem2ii_argmax_accuracy_maximizing
    {ι α : Type*} [Fintype ι]
    (posterior : ι → α → ℝ) {decisionRule argmaxRule : ι → α}
    (hargmax : EconCSLib.Decision.IsPointwiseMax posterior argmaxRule) :
    EconCSLib.Decision.averageScore posterior decisionRule ≤
      EconCSLib.Decision.averageScore posterior argmaxRule := by
  exact EconCSLib.Decision.averageScore_le_of_isPointwiseMax posterior hargmax

end DSWG24DiscretizationBias
