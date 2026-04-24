import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace EconCSLean
namespace Decision

/-!
# Finite Argmax Decision Lemmas

Reusable finite lemmas for paper arguments where a decision rule maximizes a
pointwise score, such as a Bayes posterior probability of correctness.
-/

/-- A decision rule is pointwise score-maximizing if it picks an action whose
score is at least the score of every alternative action for each instance. -/
def IsPointwiseMax {ι α : Type*} (score : ι → α → ℝ) (choose : ι → α) : Prop :=
  ∀ i a, score i a ≤ score i (choose i)

/-- Total finite score is maximized by any pointwise score-maximizing rule. -/
theorem sum_score_le_of_isPointwiseMax {ι α : Type*} [Fintype ι]
    (score : ι → α → ℝ) {choose opt : ι → α}
    (hopt : IsPointwiseMax score opt) :
    (∑ i : ι, score i (choose i)) ≤ ∑ i : ι, score i (opt i) := by
  exact Finset.sum_le_sum (by
    intro i _
    exact hopt i (choose i))

/-- Average finite score for a deterministic decision rule. -/
noncomputable def averageScore {ι α : Type*} [Fintype ι]
    (score : ι → α → ℝ) (choose : ι → α) : ℝ :=
  (∑ i : ι, score i (choose i)) / (Fintype.card ι : ℝ)

/-- Average finite score is maximized by any pointwise score-maximizing rule. -/
theorem averageScore_le_of_isPointwiseMax {ι α : Type*} [Fintype ι]
    (score : ι → α → ℝ) {choose opt : ι → α}
    (hopt : IsPointwiseMax score opt) :
    averageScore score choose ≤ averageScore score opt := by
  unfold averageScore
  exact div_le_div_of_nonneg_right
    (sum_score_le_of_isPointwiseMax score hopt)
    (Nat.cast_nonneg (Fintype.card ι))

end Decision
end EconCSLean
