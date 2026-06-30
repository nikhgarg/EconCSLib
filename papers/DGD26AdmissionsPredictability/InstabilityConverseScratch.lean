import EconCSLib.Foundations.Math.FiniteChoice
import Mathlib.Tactic

namespace EconCSLib
namespace FiniteChoice

variable {α : Type*} [DecidableEq α]

/--
If there is no single-addition gain, then an element rejected from a feasible
set remains rejected after one fresh insertion.
-/
theorem rejected_persists_insert_of_no_single_add_gain
    {C : ChoiceRule α}
    (hno :
      ¬ ∃ X x xstar,
        x ∉ X ∧ xstar ∈ X ∧ xstar ∈ C (insert x X) ∧ xstar ∉ C X)
    {X : Finset α} {x xstar : α}
    (hx : x ∉ X) (hxstarX : xstar ∈ X) (hrej : xstar ∉ C X) :
    xstar ∉ C (insert x X) := by
  intro hacc
  exact hno ⟨X, x, xstar, hx, hxstarX, hacc, hrej⟩

/--
The same no-single-addition-gain hypothesis propagates rejection across any
finite sequence of insertions.
-/
theorem rejected_persists_union_of_no_single_add_gain
    {C : ChoiceRule α}
    (hno :
      ¬ ∃ X x xstar,
        x ∉ X ∧ xstar ∈ X ∧ xstar ∈ C (insert x X) ∧ xstar ∉ C X)
    {X S : Finset α} {xstar : α}
    (hxstarX : xstar ∈ X) (hrej : xstar ∉ C X) :
    xstar ∉ C (X ∪ S) := by
  induction S using Finset.induction_on with
  | empty =>
      simpa using hrej
  | @insert a S ha ih =>
      have hUnion : X ∪ insert a S = insert a (X ∪ S) := by
        ext y
        simp
      rw [hUnion]
      by_cases haBase : a ∈ X ∪ S
      · simpa [Finset.insert_eq_of_mem haBase] using ih
      · exact rejected_persists_insert_of_no_single_add_gain
          (C := C) hno haBase (Finset.mem_union_left S hxstarX) ih

/--
If no single fresh addition can make a previously rejected existing element
accepted, then the choice rule is substitutable.
-/
theorem substitutable_of_no_single_add_gain
    (C : ChoiceRule α)
    (hno :
      ¬ ∃ X x xstar,
        x ∉ X ∧ xstar ∈ X ∧ xstar ∈ C (insert x X) ∧ xstar ∉ C X) :
    Substitutable C := by
  intro X₁ X₂ hsubset x hx
  rcases Finset.mem_inter.mp hx with ⟨hxX₁, hxCX₂⟩
  by_contra hxnotCX₁
  have hpersist :
      x ∉ C (X₁ ∪ (X₂ \ X₁)) :=
    rejected_persists_union_of_no_single_add_gain
      (C := C) hno hxX₁ hxnotCX₁
  have hdecomp : X₁ ∪ (X₂ \ X₁) = X₂ := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_union.mp hy with hyX₁ | hysdiff
      · exact hsubset hyX₁
      · exact (Finset.mem_sdiff.mp hysdiff).1
    · intro hyX₂
      by_cases hyX₁ : y ∈ X₁
      · exact Finset.mem_union_left _ hyX₁
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hyX₂, hyX₁⟩)
  exact hpersist (by simpa [hdecomp] using hxCX₂)

/--
Non-substitutability has a one-step witness: adding one fresh alternative can
make an existing rejected alternative become accepted.
-/
theorem exists_single_add_gain_of_not_substitutable
    (C : ChoiceRule α) (hnot : ¬ Substitutable C) :
    ∃ X x xstar,
      x ∉ X ∧ xstar ∈ X ∧ xstar ∈ C (insert x X) ∧ xstar ∉ C X := by
  by_contra hno
  exact hnot (substitutable_of_no_single_add_gain C hno)

end FiniteChoice
end EconCSLib
