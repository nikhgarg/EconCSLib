import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import EconCSLib.Foundations.Math.FiniteDimensionalNormsDerivative

/-!
# Projected Subgradient Methods in Finite Coordinates

Reusable vocabulary for (stochastic) projected subgradient iterations on a
finite coordinate space `Coord → ℝ`.

These definitions are paper-independent: an iteration is described by a
projection map, a trajectory, a step-size schedule, and a decomposition of the
observed step direction into a true subgradient, a zero-mean noise term, and a
bias term.

- `FiniteSubgradientAt`: the defining subgradient inequality.
- `ProjectionOnto`: a map lands in the feasible set.
- `FiniteProjectedSSGMUpdateAt` and `FollowsFiniteProjectedSSGM`: one step and
  the whole trajectory of the projected update rule.
- `FollowsFiniteProjectedSampleSubgradientMethod`: the trajectory follows the
  update rule and each direction is a subgradient of the sampled cost.
- `SSGMStepSizeConditions`: the Robbins-Monro step-size hypotheses.
-/

open scoped BigOperators

namespace EconCSLib
namespace Optimization

/--
`g` is a subgradient of `cost` at `x`, written with the finite-coordinate
linear functional `h ↦ ∑ i, g i * h i`.
-/
def FiniteSubgradientAt {Coord : Type*} [Fintype Coord]
    (cost : (Coord → ℝ) → ℝ) (x g : Coord → ℝ) : Prop :=
  ∀ y,
    cost x +
      FiniteDimensionalNorms.coordinateLinearFunctional g
        (fun i => y i - x i) ≤ cost y

theorem finiteSubgradientAt_formula {Coord : Type*} [Fintype Coord]
    (cost : (Coord → ℝ) → ℝ) (x g : Coord → ℝ) :
    FiniteSubgradientAt cost x g ↔
      ∀ y,
        cost x +
          FiniteDimensionalNorms.coordinateLinearFunctional g
            (fun i => y i - x i) ≤ cost y := by
  rfl

/-- The finite-coordinate linear functional as an explicit sum. -/
theorem coordinateLinearFunctional_apply {Coord : Type*} [Fintype Coord]
    (g h : Coord → ℝ) :
    FiniteDimensionalNorms.coordinateLinearFunctional g h =
      ∑ i : Coord, g i * h i := by
  simp [FiniteDimensionalNorms.coordinateLinearFunctional]

/-- A map that always lands in the feasible set `X`. -/
def ProjectionOnto {Point : Type*} (X : Set Point) (project : Point → Point) :
    Prop :=
  ∀ y, project y ∈ X

/--
One projected stochastic subgradient step: move from `previous` along the
negative of `subgradient + noise + bias` scaled by `radius`, then project.
-/
def FiniteProjectedSSGMUpdateAt {Coord : Type*}
    (project : (Coord → ℝ) → Coord → ℝ)
    (previous : Coord → ℝ) (radius : ℝ)
    (subgradient noise bias next : Coord → ℝ) : Prop :=
  next =
    project
      (fun i => previous i -
        radius * (subgradient i + noise i + bias i))

/-- The trajectory follows the projected update rule at every step. -/
def FollowsFiniteProjectedSSGM {Coord : Type*}
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient noise bias : ℕ → Coord → ℝ) : Prop :=
  ∀ t : ℕ,
    FiniteProjectedSSGMUpdateAt project (trajectory t) (radius (t + 1))
      (subgradient t) (noise t) (bias t) (trajectory (t + 1))

/--
The trajectory follows the projected update rule and each step direction is a
genuine subgradient of that step's sampled cost.
-/
def FollowsFiniteProjectedSampleSubgradientMethod {Coord : Type*} [Fintype Coord]
    (sampleCost : ℕ → (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient noise bias : ℕ → Coord → ℝ) : Prop :=
  FollowsFiniteProjectedSSGM project trajectory radius subgradient noise bias ∧
    ∀ t : ℕ, FiniteSubgradientAt (sampleCost t) (trajectory t) (subgradient t)

/--
Robbins-Monro step-size hypotheses: positive steps, square-summable, with
divergent partial sums.  The shifted indices reflect that Lean's naturals start
at zero while the schedule starts at one.
-/
def SSGMStepSizeConditions (radius : ℕ → ℝ) : Prop :=
  (∀ t : ℕ, 0 < t → 0 < radius t) ∧
    Summable (fun t : ℕ => (radius (t + 1)) ^ 2) ∧
      Filter.Tendsto
        (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1))
        Filter.atTop Filter.atTop

end Optimization
end EconCSLib
