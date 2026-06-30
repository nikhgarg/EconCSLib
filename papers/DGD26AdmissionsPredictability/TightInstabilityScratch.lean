import EconCSLib.Foundations.Math.FiniteChoice
import Mathlib.Tactic

namespace EconCSLib
namespace FiniteChoice

variable {α : Type*} [DecidableEq α]

/--
If `B` is feasible for the one-element expansion `insert x X`, and `x` is not
in `B`, then every element of `B` already lies in `X`.  Thus the new-choice
side difference is exactly the gain set counted by `choiceGainTerm`.
-/
theorem sdiff_eq_inter_sdiff_of_subset_insert_of_not_mem
    {A B X : Finset α} {x : α}
    (hB : B ⊆ insert x X) (hxB : x ∉ B) :
    B \ A = (X ∩ B) \ A := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_sdiff.mp hy with ⟨hyB, hyA⟩
    have hyInsert : y ∈ insert x X := hB hyB
    rcases Finset.mem_insert.mp hyInsert with rfl | hyX
    · exact False.elim (hxB hyB)
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨hyX, hyB⟩, hyA⟩
  · intro hy
    rcases Finset.mem_sdiff.mp hy with ⟨hyInter, hyA⟩
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hyInter).2, hyA⟩

/--
If `A` is feasible for `X`, `B` is feasible for `insert x X`, and the fresh
element `x` is in `B`, then `B \ A` consists of `x` plus the old alternatives
in the gain set.
-/
theorem sdiff_eq_insert_inter_sdiff_of_subset_of_subset_insert_of_mem
    {A B X : Finset α} {x : α}
    (hA : A ⊆ X) (hB : B ⊆ insert x X) (hxX : x ∉ X)
    (hxB : x ∈ B) :
    B \ A = insert x ((X ∩ B) \ A) := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_sdiff.mp hy with ⟨hyB, hyA⟩
    have hyInsert : y ∈ insert x X := hB hyB
    rcases Finset.mem_insert.mp hyInsert with rfl | hyX
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hyX, hyB⟩, hyA⟩)
  · intro hy
    rcases Finset.mem_insert.mp hy with hyEq | hyGain
    · have hxA : x ∉ A := by
        intro hxA
        exact hxX (hA hxA)
      subst y
      exact Finset.mem_sdiff.mpr ⟨hxB, hxA⟩
    · rcases Finset.mem_sdiff.mp hyGain with ⟨hyInter, hyA⟩
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hyInter).2, hyA⟩

/--
Cardinality form of
`sdiff_eq_insert_inter_sdiff_of_subset_of_subset_insert_of_mem`.
-/
theorem card_sdiff_eq_card_inter_sdiff_add_one_of_subset_of_subset_insert_of_mem
    {A B X : Finset α} {x : α}
    (hA : A ⊆ X) (hB : B ⊆ insert x X) (hxX : x ∉ X)
    (hxB : x ∈ B) :
    (B \ A).card = ((X ∩ B) \ A).card + 1 := by
  have hxNotGain : x ∉ (X ∩ B) \ A := by
    intro hxGain
    exact hxX ((Finset.mem_inter.mp (Finset.mem_sdiff.mp hxGain).1).1)
  rw [sdiff_eq_insert_inter_sdiff_of_subset_of_subset_insert_of_mem
    hA hB hxX hxB]
  exact Finset.card_insert_of_notMem hxNotGain

/--
When `X` already has at least `q` alternatives, a feasible q-acceptant rule
chooses the same number from `X` and `insert x X`.
-/
theorem qAcceptant_card_choice_insert_eq_of_le_card
    {q : ℕ} {C : ChoiceRule α} (haccept : QAcceptant q C)
    {X : Finset α} {x : α} (hcard : q ≤ X.card) :
    (C X).card = (C (insert x X)).card := by
  have hX_subset : X ⊆ insert x X := by
    intro y hy
    exact Finset.mem_insert_of_mem hy
  have hcard_insert : q ≤ (insert x X).card :=
    hcard.trans (Finset.card_le_card hX_subset)
  rw [haccept X, haccept (insert x X)]
  rw [Nat.min_eq_left hcard, Nat.min_eq_left hcard_insert]

/--
Instability calculation, fresh entrant not chosen: the gain and loss terms have
the same cardinality, so the distance is twice the number of displaced old
choices.
-/
theorem choiceDistance_insert_eq_two_mul_loss_of_not_mem
    {q : ℕ} {C : ChoiceRule α} (hfeasible : Feasible C)
    (haccept : QAcceptant q C)
    {X : Finset α} {x : α} (hcard : q ≤ X.card)
    (hxNotChosen : x ∉ C (insert x X)) :
    choiceDistance C X (insert x X) =
      2 * (C X \ C (insert x X)).card := by
  let X' : Finset α := insert x X
  change choiceDistance C X X' = 2 * choiceLossTerm C X X'
  have hcard_eq : (C X).card = (C X').card := by
    simpa [X'] using
      qAcceptant_card_choice_insert_eq_of_le_card
        (C := C) (x := x) haccept hcard
  have hnew_eq_gain :
      (C X' \ C X).card = ((X ∩ C X') \ C X).card := by
    have hset :
        C X' \ C X = (X ∩ C X') \ C X :=
      sdiff_eq_inter_sdiff_of_subset_insert_of_not_mem
        (A := C X) (B := C X') (X := X) (x := x)
        (by simpa [X'] using hfeasible X')
        (by simpa [X'] using hxNotChosen)
    simp [hset]
  have hloss_eq_gain :
      choiceLossTerm C X X' = choiceGainTerm C X X' := by
    rw [choiceLossTerm, choiceGainTerm]
    rw [Finset.card_sdiff_comm hcard_eq]
    exact hnew_eq_gain
  rw [choiceDistance, hloss_eq_gain]
  omega

/--
Instability calculation, fresh entrant chosen: the gain term is one smaller
than the loss term, so this Nat-friendly statement is the
`2 * n - 1` case without using truncated subtraction.
-/
theorem choiceDistance_insert_add_one_eq_two_mul_loss_of_mem
    {q : ℕ} {C : ChoiceRule α} (hfeasible : Feasible C)
    (haccept : QAcceptant q C)
    {X : Finset α} {x : α} (hcard : q ≤ X.card)
    (hxX : x ∉ X) (hxChosen : x ∈ C (insert x X)) :
    choiceDistance C X (insert x X) + 1 =
      2 * (C X \ C (insert x X)).card := by
  let X' : Finset α := insert x X
  change choiceDistance C X X' + 1 = 2 * choiceLossTerm C X X'
  have hcard_eq : (C X).card = (C X').card := by
    simpa [X'] using
      qAcceptant_card_choice_insert_eq_of_le_card
        (C := C) (x := x) haccept hcard
  have hnew_eq_gain_add_one :
      (C X' \ C X).card = ((X ∩ C X') \ C X).card + 1 := by
    exact
      card_sdiff_eq_card_inter_sdiff_add_one_of_subset_of_subset_insert_of_mem
        (A := C X) (B := C X') (X := X) (x := x)
        (hfeasible X) (by simpa [X'] using hfeasible X') hxX
        (by simpa [X'] using hxChosen)
  have hloss_eq_gain_add_one :
      choiceLossTerm C X X' = choiceGainTerm C X X' + 1 := by
    rw [choiceLossTerm, choiceGainTerm]
    rw [Finset.card_sdiff_comm hcard_eq]
    exact hnew_eq_gain_add_one
  rw [choiceDistance, hloss_eq_gain_add_one]
  omega

/--
Combined indicator-style form of the scratch calculation.  The chosen-newcomer
case is `2 * n - 1`; the rejected-newcomer case is `2 * n`.
-/
theorem choiceDistance_insert_eq_if_mem
    {q : ℕ} {C : ChoiceRule α} (hfeasible : Feasible C)
    (haccept : QAcceptant q C)
    {X : Finset α} {x : α} (hcard : q ≤ X.card) (hxX : x ∉ X) :
    choiceDistance C X (insert x X) =
      if x ∈ C (insert x X) then
        2 * (C X \ C (insert x X)).card - 1
      else
        2 * (C X \ C (insert x X)).card := by
  by_cases hxChosen : x ∈ C (insert x X)
  · simp [hxChosen]
    have hcalc :=
      choiceDistance_insert_add_one_eq_two_mul_loss_of_mem
        (C := C) (q := q) hfeasible haccept hcard hxX hxChosen
    omega
  · simp [hxChosen]
    exact
      choiceDistance_insert_eq_two_mul_loss_of_not_mem
        (C := C) (q := q) hfeasible haccept hcard hxChosen

end FiniteChoice
end EconCSLib
