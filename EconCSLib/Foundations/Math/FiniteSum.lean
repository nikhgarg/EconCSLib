import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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

end FiniteSum
end EconCSLib
