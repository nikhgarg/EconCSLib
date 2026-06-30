import EconCSLib.Foundations.Math.FiniteChoice

/-!
# Additive variability scratch work

Checked helper lemmas toward an additive variability bound for sequential
composition.  The main bound below is conditional on the key remaining-pool
premise: after adding one applicant to the first-stage input, the set passed to
the tail stage expands by at most one element.
-/

namespace EconCSLib
namespace FiniteChoice

variable {α : Type*} [DecidableEq α]

/--
If `S'` extends `S` by at most one element, then it is either unchanged or a
single insertion into `S`.
-/
theorem eq_or_exists_eq_insert_of_subset_of_sdiff_card_le_one
    {S S' : Finset α} (hsubset : S ⊆ S')
    (hcard : (S' \ S).card ≤ 1) :
    S' = S ∨ ∃ y, y ∉ S ∧ S' = insert y S := by
  by_cases hdiff_empty : S' \ S = ∅
  · left
    apply Finset.Subset.antisymm
    · intro z hzS'
      by_contra hzS
      have hzDiff : z ∈ S' \ S := Finset.mem_sdiff.mpr ⟨hzS', hzS⟩
      simp [hdiff_empty] at hzDiff
    · exact hsubset
  · right
    rcases Finset.nonempty_of_ne_empty hdiff_empty with ⟨y, hyDiff⟩
    rcases Finset.mem_sdiff.mp hyDiff with ⟨hyS', hyNotS⟩
    have hdiff_subset_singleton : S' \ S ⊆ ({y} : Finset α) := by
      intro z hzDiff
      by_contra hzSingleton
      have hz_ne_y : z ≠ y := by
        intro hzy
        exact hzSingleton (by simp [hzy])
      have hpair_subset : insert z ({y} : Finset α) ⊆ S' \ S := by
        intro w hw
        rw [Finset.mem_insert] at hw
        rcases hw with rfl | hw
        · exact hzDiff
        · have hwy : w = y := by simpa using hw
          simpa [hwy] using hyDiff
      have hpair_card : (insert z ({y} : Finset α)).card = 2 := by
        rw [Finset.card_insert_of_notMem]
        · simp
        · simpa using hz_ne_y
      have htwo_le : 2 ≤ (S' \ S).card := by
        rw [← hpair_card]
        exact Finset.card_le_card hpair_subset
      omega
    refine ⟨y, hyNotS, ?_⟩
    apply Finset.Subset.antisymm
    · intro z hzS'
      by_cases hzS : z ∈ S
      · exact Finset.mem_insert_of_mem hzS
      · have hzDiff : z ∈ S' \ S := Finset.mem_sdiff.mpr ⟨hzS', hzS⟩
        have hzY : z = y := by
          have hzMemSingleton := hdiff_subset_singleton hzDiff
          simpa using hzMemSingleton
        simp [hzY]
    · intro z hzInsert
      rw [Finset.mem_insert] at hzInsert
      rcases hzInsert with rfl | hzS
      · exact hyS'
      · exact hsubset hzS

/-- A one-insertion loss is contained in the borderline set at the smaller pool. -/
theorem choice_loss_subset_borderlineSet_of_eq_insert
    [Fintype α] {T : ChoiceRule α} {S S' : Finset α} {y : α}
    (hS' : S' = insert y S) :
    T S \ T S' ⊆ borderlineSet T S := by
  intro z hz
  rw [borderlineSet]
  exact Finset.mem_biUnion.mpr
    ⟨y, Finset.mem_univ y, by simpa [hS'] using hz⟩

/--
If `S'` extends `S` by at most one element, every tail-stage loss from `S` to
`S'` is already a one-step borderline loss at `S`.
-/
theorem choice_loss_subset_borderlineSet_of_subset_sdiff_card_le_one
    [Fintype α] {T : ChoiceRule α} {S S' : Finset α}
    (hsubset : S ⊆ S') (hcard : (S' \ S).card ≤ 1) :
    T S \ T S' ⊆ borderlineSet T S := by
  rcases eq_or_exists_eq_insert_of_subset_of_sdiff_card_le_one
      hsubset hcard with hEq | ⟨y, _hyNotS, hEq⟩
  · intro z hz
    simp [hEq] at hz
  · exact choice_loss_subset_borderlineSet_of_eq_insert (T := T) hEq

/--
The previous containment plus `VariabilityAtMost` gives the corresponding
cardinality bound.
-/
theorem choice_loss_card_le_variabilityAtMost_of_subset_sdiff_card_le_one
    [Fintype α] {m : ℕ} {T : ChoiceRule α} (hvar : VariabilityAtMost m T)
    {S S' : Finset α} (hsubset : S ⊆ S')
    (hcard : (S' \ S).card ≤ 1) :
    (T S \ T S').card ≤ m := by
  exact (Finset.card_le_card
      (choice_loss_subset_borderlineSet_of_subset_sdiff_card_le_one
        (T := T) hsubset hcard)).trans (hvar S)

/-- Substitutability of the first stage makes the tail input monotone. -/
theorem remainder_subset_insert_remainder_of_substitutable
    {C : ChoiceRule α} (hsub : Substitutable C) (X : Finset α) (x : α) :
    X \ C X ⊆ insert x X \ C (insert x X) :=
  sdiff_choice_subset_sdiff_choice_of_subset_of_substitutable
    (C := C) hsub (by intro z hz; exact Finset.mem_insert_of_mem hz)

/--
A loss of the two-stage rule is contained in the union of the first-stage loss
and the tail-stage loss on the corresponding remainders.
-/
theorem firstThen_loss_subset_first_loss_union_tail_loss
    (C T : ChoiceRule α) (X X' : Finset α) :
    (C X ∪ T (X \ C X)) \ (C X' ∪ T (X' \ C X')) ⊆
      (C X \ C X') ∪ (T (X \ C X) \ T (X' \ C X')) := by
  intro y hy
  rcases Finset.mem_sdiff.mp hy with ⟨hyComp, hyNotComp'⟩
  have hyNotC' : y ∉ C X' := by
    intro hyC'
    exact hyNotComp' (Finset.mem_union_left _ hyC')
  have hyNotT' : y ∉ T (X' \ C X') := by
    intro hyT'
    exact hyNotComp' (Finset.mem_union_right _ hyT')
  rcases Finset.mem_union.mp hyComp with hyC | hyT
  · exact Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨hyC, hyNotC'⟩)
  · exact Finset.mem_union_right _
      (Finset.mem_sdiff.mpr ⟨hyT, hyNotT'⟩)

/--
If every one-applicant first-stage expansion changes the remainder by at most
one element, then the composed borderline set is contained in the union of the
first-stage borderline set and the tail borderline set at the original
remainder.
-/
theorem borderlineSet_firstThen_subset_union_of_remainder_sdiff_card_le_one
    [Fintype α] {C T : ChoiceRule α} {X : Finset α}
    (hrem_subset :
      ∀ x, X \ C X ⊆ insert x X \ C (insert x X))
    (hrem_card :
      ∀ x, ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤ 1) :
    borderlineSet (fun Y => C Y ∪ T (Y \ C Y)) X ⊆
      borderlineSet C X ∪ borderlineSet T (X \ C X) := by
  intro y hy
  rw [borderlineSet] at hy ⊢
  rcases Finset.mem_biUnion.mp hy with ⟨x, _hxUniv, hyLoss⟩
  have hyLossUnion :
      y ∈ (C X \ C (insert x X)) ∪
        (T (X \ C X) \ T (insert x X \ C (insert x X))) :=
    firstThen_loss_subset_first_loss_union_tail_loss
      (C := C) (T := T) (X := X) (X' := insert x X) hyLoss
  rcases Finset.mem_union.mp hyLossUnion with hyFirst | hyTail
  · exact Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hyFirst⟩)
  · have hyTailBorder :
        y ∈ borderlineSet T (X \ C X) :=
      choice_loss_subset_borderlineSet_of_subset_sdiff_card_le_one
        (T := T) (hrem_subset x) (hrem_card x) hyTail
    exact Finset.mem_union_right _ hyTailBorder

/--
Conditional additive variability for an abstract first-then-tail composition.
-/
theorem variabilityAtMost_firstThen_of_remainder_sdiff_card_le_one
    [Fintype α] {mC mTail : ℕ} {C T : ChoiceRule α}
    (hvarC : VariabilityAtMost mC C)
    (hvarTail : VariabilityAtMost mTail T)
    (hrem_subset :
      ∀ X x, X \ C X ⊆ insert x X \ C (insert x X))
    (hrem_card :
      ∀ X x, ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤ 1) :
    VariabilityAtMost (mC + mTail) (fun X => C X ∪ T (X \ C X)) := by
  intro X
  have hborder_subset :
      borderlineSet (fun Y => C Y ∪ T (Y \ C Y)) X ⊆
        borderlineSet C X ∪ borderlineSet T (X \ C X) :=
    borderlineSet_firstThen_subset_union_of_remainder_sdiff_card_le_one
      (C := C) (T := T) (X := X) (hrem_subset X) (hrem_card X)
  have hcard_subset :=
    Finset.card_le_card hborder_subset
  have hcard_union :
      (borderlineSet C X ∪ borderlineSet T (X \ C X)).card ≤
        (borderlineSet C X).card + (borderlineSet T (X \ C X)).card :=
    Finset.card_union_le _ _
  have hC := hvarC X
  have hTail := hvarTail (X \ C X)
  omega

/--
Same conditional additive bound, with the remainder-cardinality premise only
required for fresh insertions.  Insertions by an element already in `X` are
definitionally unchanged.
-/
theorem variabilityAtMost_firstThen_of_substitutable_of_fresh_remainder_sdiff_card_le_one
    [Fintype α] {mC mTail : ℕ} {C T : ChoiceRule α}
    (hsub : Substitutable C)
    (hvarC : VariabilityAtMost mC C)
    (hvarTail : VariabilityAtMost mTail T)
    (hrem_card_fresh :
      ∀ X x, x ∉ X →
        ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤ 1) :
    VariabilityAtMost (mC + mTail) (fun X => C X ∪ T (X \ C X)) := by
  refine variabilityAtMost_firstThen_of_remainder_sdiff_card_le_one
    (C := C) (T := T) hvarC hvarTail ?_ ?_
  · intro X x
    exact remainder_subset_insert_remainder_of_substitutable hsub X x
  · intro X x
    by_cases hx : x ∈ X
    · have hinsert : insert x X = X := Finset.insert_eq_of_mem hx
      simp [hinsert]
    · exact hrem_card_fresh X x hx

/--
Conditional additive variability for the `C :: Cs` sequential-composition case.
-/
theorem variabilityAtMost_sequentialComposition_cons_of_substitutable_of_fresh_remainder_sdiff_card_le_one
    [Fintype α] {mC mTail : ℕ} {C : ChoiceRule α}
    {Cs : List (ChoiceRule α)}
    (hsub : Substitutable C)
    (hvarC : VariabilityAtMost mC C)
    (hvarTail : VariabilityAtMost mTail (sequentialComposition Cs))
    (hrem_card_fresh :
      ∀ X x, x ∉ X →
        ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤ 1) :
    VariabilityAtMost (mC + mTail) (sequentialComposition (C :: Cs)) := by
  simpa [sequentialComposition] using
    variabilityAtMost_firstThen_of_substitutable_of_fresh_remainder_sdiff_card_le_one
      (C := C) (T := sequentialComposition Cs)
      hsub hvarC hvarTail hrem_card_fresh

/--
The new remainder elements are contained in the inserted applicant together
with old first-stage choices that the first stage drops.
-/
theorem remainder_insert_sdiff_subset_insert_choiceLoss
    (C : ChoiceRule α) (X : Finset α) (x : α) :
    (insert x X \ C (insert x X)) \ (X \ C X) ⊆
      insert x (C X \ C (insert x X)) := by
  intro z hz
  rcases Finset.mem_sdiff.mp hz with ⟨hzRem', hzNotRem⟩
  rcases Finset.mem_sdiff.mp hzRem' with ⟨hzInsert, hzNotC'⟩
  rw [Finset.mem_insert] at hzInsert ⊢
  rcases hzInsert with rfl | hzX
  · exact Or.inl rfl
  · refine Or.inr (Finset.mem_sdiff.mpr ⟨?_, hzNotC'⟩)
    by_contra hzNotC
    exact hzNotRem (Finset.mem_sdiff.mpr ⟨hzX, hzNotC⟩)

/--
Consequently, the remainder expansion is bounded by one plus the first-stage
old-choice loss.
-/
theorem remainder_insert_sdiff_card_le_one_add_choiceLoss
    (C : ChoiceRule α) (X : Finset α) (x : α) :
    ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤
      1 + choiceLossTerm C X (insert x X) := by
  let L : Finset α := C X \ C (insert x X)
  have hsubset :
      (insert x X \ C (insert x X)) \ (X \ C X) ⊆ insert x L := by
    simpa [L] using remainder_insert_sdiff_subset_insert_choiceLoss C X x
  have hcard_subset :=
    Finset.card_le_card hsubset
  have hcard_insert : (insert x L).card ≤ L.card + 1 := by
    by_cases hxL : x ∈ L
    · rw [Finset.insert_eq_of_mem hxL]
      omega
    · rw [Finset.card_insert_of_notMem hxL]
  have hle :
      ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤ L.card + 1 :=
    hcard_subset.trans hcard_insert
  simpa [choiceLossTerm, L, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hle

/-- Under substitutability, one-step instability bounds old first-stage losses by one. -/
theorem choiceLossTerm_insert_le_one_of_substitutable_of_dUnstable_one
    {C : ChoiceRule α} (hsub : Substitutable C)
    (hunstable : DUnstable 1 C) {X : Finset α} {x : α} (hx : x ∉ X) :
    choiceLossTerm C X (insert x X) ≤ 1 := by
  have hsubset : X ⊆ insert x X := by
    intro z hz
    exact Finset.mem_insert_of_mem hz
  have hgain :
      choiceGainTerm C X (insert x X) = 0 :=
    (substitutable_iff_choiceGainTerm_eq_zero C).mp hsub hsubset
  have hdist := hunstable X x hx
  rw [choiceDistance, hgain] at hdist
  simpa using hdist

/--
The currently available first-stage hypotheses imply only a two-element bound
on the tail-input expansion: the fresh applicant plus at most one dropped old
first-stage choice.
-/
theorem remainder_insert_sdiff_card_le_two_of_substitutable_of_dUnstable_one
    {C : ChoiceRule α} (hsub : Substitutable C)
    (hunstable : DUnstable 1 C) {X : Finset α} {x : α} (hx : x ∉ X) :
    ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤ 2 := by
  have hcard :=
    remainder_insert_sdiff_card_le_one_add_choiceLoss C X x
  have hloss :
      choiceLossTerm C X (insert x X) ≤ 1 :=
    choiceLossTerm_insert_le_one_of_substitutable_of_dUnstable_one
      (C := C) hsub hunstable hx
  omega

/--
If the first stage chooses the fresh applicant, then the fresh applicant is not
passed to the tail, and the one-element remainder premise follows from
substitutability plus one-step instability.
-/
theorem remainder_insert_sdiff_card_le_one_of_substitutable_of_dUnstable_one_of_new_chosen
    {C : ChoiceRule α} (hsub : Substitutable C)
    (hunstable : DUnstable 1 C) {X : Finset α} {x : α}
    (hx : x ∉ X) (hxChosen : x ∈ C (insert x X)) :
    ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤ 1 := by
  have hsubset :
      (insert x X \ C (insert x X)) \ (X \ C X) ⊆
        C X \ C (insert x X) := by
    intro z hz
    rcases Finset.mem_sdiff.mp hz with ⟨hzRem', hzNotRem⟩
    rcases Finset.mem_sdiff.mp hzRem' with ⟨hzInsert, hzNotC'⟩
    rw [Finset.mem_insert] at hzInsert
    rcases hzInsert with rfl | hzX
    · exact False.elim (hzNotC' hxChosen)
    · refine Finset.mem_sdiff.mpr ⟨?_, hzNotC'⟩
      by_contra hzNotC
      exact hzNotRem (Finset.mem_sdiff.mpr ⟨hzX, hzNotC⟩)
  have hcard_loss :
      ((insert x X \ C (insert x X)) \ (X \ C X)).card ≤
        choiceLossTerm C X (insert x X) := by
    simpa [choiceLossTerm] using Finset.card_le_card hsubset
  have hloss :
      choiceLossTerm C X (insert x X) ≤ 1 :=
    choiceLossTerm_insert_le_one_of_substitutable_of_dUnstable_one
      (C := C) hsub hunstable hx
  exact hcard_loss.trans hloss

end FiniteChoice
end EconCSLib
