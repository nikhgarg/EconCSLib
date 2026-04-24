import EconCSLean.Decision.Argmax

/-!
# Paper-Facing Theorems: Addressing Discretization-Induced Bias

This file is the public theorem interface for the current discretization-bias
formalization. It currently closes the finite deterministic Bayes-score core of
Theorem 2(ii): a pointwise argmax rule maximizes expected accuracy when accuracy
is evaluated by Bayes posterior scores.
-/

namespace DiscretizationBias

open scoped BigOperators

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
    (hargmax : EconCSLean.Decision.IsPointwiseMax posterior argmaxRule) :
    EconCSLean.Decision.averageScore posterior decisionRule ≤
      EconCSLean.Decision.averageScore posterior argmaxRule := by
  exact EconCSLean.Decision.averageScore_le_of_isPointwiseMax posterior hargmax

end DiscretizationBias
