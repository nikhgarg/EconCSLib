import EconCSLib.Foundations.Math.FiniteChoice

namespace EconCSLib
namespace FiniteChoice

variable {α : Type*} [DecidableEq α]

/--
If `C` is substitutable, then removing the choices of `C` preserves inclusion
of feasible sets.
-/
theorem sdiff_choice_subset_sdiff_choice_of_subset_of_substitutable
    {C : ChoiceRule α} (hsub : Substitutable C)
    {X₁ X₂ : Finset α} (hsubset : X₁ ⊆ X₂) :
    X₁ \ C X₁ ⊆ X₂ \ C X₂ := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxX₁, hxnotC₁⟩
  refine Finset.mem_sdiff.mpr ⟨hsubset hxX₁, ?_⟩
  intro hxC₂
  exact hxnotC₁ (hsub hsubset (Finset.mem_inter.mpr ⟨hxX₁, hxC₂⟩))

/--
Sequential composition of feasible choice rules is feasible.
-/
theorem feasible_sequentialComposition_of_forall_mem
    {Cs : List (ChoiceRule α)}
    (hfeasible : ∀ C ∈ Cs, Feasible C) :
    Feasible (sequentialComposition Cs) := by
  induction Cs with
  | nil =>
      intro X x hx
      simp [sequentialComposition] at hx
  | cons C Cs ih =>
      intro X x hx
      simp [sequentialComposition] at hx
      rcases hx with hxC | hxTail
      · exact hfeasible C List.mem_cons_self X hxC
      · have htail : Feasible (sequentialComposition Cs) := by
          apply ih
          intro D hD
          exact hfeasible D (List.mem_cons_of_mem C hD)
        exact (Finset.mem_sdiff.mp (htail (X \ C X) hxTail)).1

/--
Sequential composition of feasible substitutable choice rules is substitutable.
-/
theorem substitutable_sequentialComposition_of_forall_mem
    {Cs : List (ChoiceRule α)}
    (hfeasible : ∀ C ∈ Cs, Feasible C)
    (hsub : ∀ C ∈ Cs, Substitutable C) :
    Substitutable (sequentialComposition Cs) := by
  induction Cs with
  | nil =>
      intro X₁ X₂ hsubset x hx
      simp [sequentialComposition] at hx
  | cons C Cs ih =>
      intro X₁ X₂ hsubset x hx
      rcases Finset.mem_inter.mp hx with ⟨hxX₁, hxChosen₂⟩
      simp [sequentialComposition] at hxChosen₂ ⊢
      rcases hxChosen₂ with hxC₂ | hxTail₂
      · exact Or.inl
          (hsub C List.mem_cons_self hsubset
            (Finset.mem_inter.mpr ⟨hxX₁, hxC₂⟩))
      · by_cases hxC₁ : x ∈ C X₁
        · exact Or.inl hxC₁
        · have htail : Substitutable (sequentialComposition Cs) := by
            apply ih
            · intro D hD
              exact hfeasible D (List.mem_cons_of_mem C hD)
            · intro D hD
              exact hsub D (List.mem_cons_of_mem C hD)
          have htailSubset :
              X₁ \ C X₁ ⊆ X₂ \ C X₂ :=
            sdiff_choice_subset_sdiff_choice_of_subset_of_substitutable
              (C := C) (hsub C List.mem_cons_self) hsubset
          have hxTail₁ : x ∈ sequentialComposition Cs (X₁ \ C X₁) :=
            htail htailSubset
              (Finset.mem_inter.mpr
                ⟨Finset.mem_sdiff.mpr ⟨hxX₁, hxC₁⟩, hxTail₂⟩)
          exact Or.inr hxTail₁

end FiniteChoice
end EconCSLib
