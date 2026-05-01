import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace EconCSLib
namespace FiniteSum

/--
If two functions on a finite type differ only at two distinct points, the whole
sum changes by exactly the two pointwise deltas.
-/
theorem sum_eq_sum_add_sub_add_sub_of_eq_off
    {α : Type*} [Fintype α]
    {f g : α → ℝ} {a b : α} (hab : a ≠ b)
    (hoff : ∀ x, x ≠ a → x ≠ b → f x = g x) :
    (∑ x : α, f x) = (∑ x : α, g x) + (f a - g a) + (f b - g b) := by
  classical
  have hfg : ∑ x : α, f x = ∑ x : α, (g x + (f x - g x)) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    ring
  have hsumadd :
      ∑ x : α, (g x + (f x - g x)) =
        ∑ x : α, g x + ∑ x : α, (f x - g x) := by
    rw [Finset.sum_add_distrib]
  have hdiff_erase :
      ∑ x ∈ (Finset.univ : Finset α).erase a, (f x - g x) = f b - g b := by
    apply Finset.sum_eq_single_of_mem b
    · simp [hab.symm]
    · intro x hx hxb
      have hxa : x ≠ a := by
        simpa using hx
      rw [hoff x hxa hxb]
      ring
  have hdiff : ∑ x : α, (f x - g x) = (f a - g a) + (f b - g b) := by
    have herase_add := Finset.sum_erase_add (s := (Finset.univ : Finset α))
      (f := fun x => f x - g x) (a := a) (by simp)
    rw [hdiff_erase] at herase_add
    linarith
  rw [hfg, hsumadd, hdiff]
  ring

/--
A weighted sum of quantities bounded above by `B` is bounded above by `B`
whenever the weights are nonnegative, have total mass at most one, and `B` is
nonnegative.
-/
theorem finset_weighted_sum_le_bound_of_nonneg_sum_le_one
    {α : Type*} (s : Finset α) (weight value : α → ℝ) {B : ℝ}
    (hweight_nonneg : ∀ i, i ∈ s → 0 ≤ weight i)
    (hweight_sum : (∑ i ∈ s, weight i) ≤ 1)
    (hvalue : ∀ i, i ∈ s → value i ≤ B)
    (hB : 0 ≤ B) :
    (∑ i ∈ s, weight i * value i) ≤ B := by
  calc
    (∑ i ∈ s, weight i * value i)
        ≤ ∑ i ∈ s, weight i * B := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hvalue i ‹i ∈ s›)
              (hweight_nonneg i ‹i ∈ s›)
    _ = (∑ i ∈ s, weight i) * B := by
          rw [← Finset.sum_mul]
    _ ≤ 1 * B := by
          exact mul_le_mul_of_nonneg_right hweight_sum hB
    _ = B := by ring

/--
A weighted sum over a finite type is bounded by `B` under the same hypotheses
as the finset version, with the support set specialized to `univ`.
-/
theorem weighted_sum_le_bound_of_nonneg_sum_le_one
    {α : Type*} [Fintype α] (weight value : α → ℝ) {B : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_sum : (∑ i : α, weight i) ≤ 1)
    (hvalue : ∀ i, value i ≤ B)
    (hB : 0 ≤ B) :
    (∑ i : α, weight i * value i) ≤ B := by
  exact finset_weighted_sum_le_bound_of_nonneg_sum_le_one
    (Finset.univ : Finset α) weight value
    (by intro i _; exact hweight_nonneg i)
    (by simpa using hweight_sum)
    (by intro i _; exact hvalue i)
    hB

/-- Telescoping identity for adjacent real sequence increments. -/
theorem sum_range_probabilityIncrements
    (p : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (p (j + 1) - p j)) = p n - p 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/--
Paper-style weighted benchmark bound for monotone probability increments.
If expected revenue is bounded by a weighted sum whose weights are adjacent
increments of a monotone probability sequence and whose endpoint mass is at
most one, then the expected revenue is bounded by the common benchmark.
-/
theorem le_bound_of_le_range_probabilityIncrement_weighted_sum
    (n : ℕ) (p value : ℕ → ℝ) {R B : ℝ}
    (hR :
      R ≤ ∑ j ∈ Finset.range n, (p (j + 1) - p j) * value j)
    (hmono : ∀ j, j < n → p j ≤ p (j + 1))
    (hendpoint : p n - p 0 ≤ 1)
    (hvalue : ∀ j, j < n → value j ≤ B)
    (hB : 0 ≤ B) :
    R ≤ B := by
  have hweight_nonneg :
      ∀ j, j ∈ Finset.range n → 0 ≤ p (j + 1) - p j := by
    intro j hj
    exact sub_nonneg.mpr (hmono j (Finset.mem_range.mp hj))
  have hweight_sum :
      (∑ j ∈ Finset.range n, (p (j + 1) - p j)) ≤ 1 := by
    rw [sum_range_probabilityIncrements]
    exact hendpoint
  have hweighted :
      (∑ j ∈ Finset.range n, (p (j + 1) - p j) * value j) ≤ B := by
    exact finset_weighted_sum_le_bound_of_nonneg_sum_le_one
      (Finset.range n) (fun j => p (j + 1) - p j) value
      hweight_nonneg hweight_sum
      (by intro j hj; exact hvalue j (Finset.mem_range.mp hj)) hB
  exact le_trans hR hweighted

end FiniteSum
end EconCSLib
