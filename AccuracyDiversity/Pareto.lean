import AccuracyDiversity.Basic
import AccuracyDiversity.Representation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace AccuracyDiversity

/--
Expected maximum of `q` draws from a distribution with tail index α.
Instead of calculating the integral, we define the target marginal behavior.
-/
def HasTailIndex (f : ℕ → ℝ) (index : ℝ) : Prop :=
  ∃ C > 0, ∀ q, 0 < q → f (q + 1) - f q = C * (q : ℝ) ^ (index - 1)

/--
A model where every type has conditional item values with the same tail index.
-/
def HasTypeTailIndex (M : ConsumptionModel T) (index : ℝ) : Prop :=
  ∀ t, HasTailIndex (M.valueOfCount t) index

/--
The γ-homogeneity profile for a Pareto distribution with tail index α.
The target weights are proportional to `likelihood ^ α`.
-/
noncomputable def paretoProfile {T : ℕ} (likelihood : ItemType T → ℝ) (α : ℝ) :
    GammaHomogeneityProfile T where
  gamma := 1 - 1/α
  targetWeight := fun t => (likelihood t) ^ α

/--
Theorem 2 Bridge: If marginals decay as `q ^ (1/α - 1)`, then the optimal
allocation is approximately γ-homogeneous with γ = 1 - 1/α.
-/
theorem homogeneity_of_tail_index
    {T : ℕ} [NeZero T] (M : ConsumptionModel T) (α : ℝ) (hα : 1 < α)
    (htail : HasTypeTailIndex M (1/α))
    (hlike_pos : ∀ t, 0 < M.likelihood t) :
    ∀ N a, M.IsOptimalAtTotal N a →
      (paretoProfile M.likelihood α).Approx a (sorry / N) :=
  sorry

end AccuracyDiversity
