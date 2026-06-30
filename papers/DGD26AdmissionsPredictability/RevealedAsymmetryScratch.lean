import EconCSLib.Foundations.Math.FiniteChoice

/-!
# Scratch work for revealed asymmetry

This file is intentionally scoped to the remaining exchange step in the
q-representative converse.  The unconditional asymmetry theorem would follow
from the checked common-base condition isolated below.

It imports the reusable finite-choice library directly rather than
`QRepresentativeConverseScratch`: that scratch file currently redeclares a few
names that are already in the library, so it does not build as an import target.
-/

namespace EconCSLib
namespace FiniteChoice

variable {α : Type*} [DecidableEq α]

/--
`x` is revealed above `y` when some feasible pool chooses `x` while offering
and rejecting `y`.
-/
def RevealedAbove (C : ChoiceRule α) (x y : α) : Prop :=
  ∃ X, x ∈ C X ∧ y ∈ X ∧ y ∉ C X

theorem RevealedAbove.irrefl {C : ChoiceRule α} (x : α) :
    ¬ RevealedAbove C x x := by
  rintro ⟨_X, hxCX, _hxX, hxNotCX⟩
  exact hxNotCX hxCX

theorem RevealedAbove.ne {C : ChoiceRule α} {x y : α}
    (hxy : RevealedAbove C x y) :
    x ≠ y := by
  intro h
  subst y
  exact RevealedAbove.irrefl (C := C) x hxy

/--
Under consistency, a revealed comparison has a canonical witness of the form
`C X ∪ {y}`: all originally chosen alternatives plus the rejected alternative.
-/
theorem RevealedAbove.exists_canonical_choice_of_substitutable
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) {x y : α}
    (hxy : RevealedAbove C x y) :
    ∃ P : Finset α, x ∈ P ∧ y ∉ P ∧ P.card = q ∧
      C (insert y P) = P := by
  rcases hxy with ⟨X, hxCX, hyX, hyNotCX⟩
  refine ⟨C X, hxCX, hyNotCX, ?_, ?_⟩
  · have hnot_card_le : ¬ X.card ≤ q := by
      intro hcard
      have hCX : C X = X :=
        QAcceptant.eq_of_card_le hfeasible haccept hcard
      exact hyNotCX (by simpa [hCX] using hyX)
    have hq_lt : q < X.card := Nat.lt_of_not_ge hnot_card_le
    rw [haccept X, Nat.min_eq_left (le_of_lt hq_lt)]
  · have hconsistent : Consistent C :=
      consistent_of_qAcceptant_of_substitutable haccept hsub
    have hchosen_subset : C X ⊆ insert y (C X) := by
      intro z hz
      exact Finset.mem_insert_of_mem hz
    have hinsert_subset : insert y (C X) ⊆ X := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hzCX
      · exact hyX
      · exact hfeasible X hzCX
    exact (hconsistent hchosen_subset hinsert_subset).symm

/--
A canonical revealed witness turns into a one-step displacement after removing
any chosen element from the canonical chosen set.
-/
theorem mem_borderlineSet_of_canonical_choice_erase
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    {P : Finset α} {a y : α}
    (haP : a ∈ P) (hyP : y ∉ P) (hcard : P.card = q)
    (hchoice : C (insert y P) = P) :
    y ∈ borderlineSet C (insert y (P.erase a)) := by
  classical
  let S : Finset α := insert y (P.erase a)
  have hyErase : y ∉ P.erase a := by
    intro hy
    exact hyP (Finset.mem_of_mem_erase hy)
  have hcardS : S.card = q := by
    change (insert y (P.erase a)).card = q
    rw [Finset.card_insert_of_notMem hyErase]
    rw [Finset.card_erase_add_one haP]
    exact hcard
  have hCS : C S = S :=
    QAcceptant.eq_of_card_le hfeasible haccept (by omega)
  have hinsertS : insert a S = insert y P := by
    ext z
    by_cases hza : z = a
    · subst z
      simp [S, haP]
    · simp [S, Finset.mem_erase, hza]
  rw [borderlineSet]
  exact Finset.mem_biUnion.mpr
    ⟨a, Finset.mem_univ a, by
      exact Finset.mem_sdiff.mpr
        ⟨by simp [hCS, S],
          by
            rw [hinsertS, hchoice]
            exact hyP⟩⟩

/-- Variability at most one makes each borderline set a subsingleton. -/
theorem eq_of_mem_borderlineSet_of_variabilityAtMost_one
    [Fintype α] {C : ChoiceRule α}
    (hvar : VariabilityAtMost 1 C) {X : Finset α} {y z : α}
    (hy : y ∈ borderlineSet C X) (hz : z ∈ borderlineSet C X) :
    y = z := by
  by_contra hne
  have hpair_subset :
      insert y ({z} : Finset α) ⊆ borderlineSet C X := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact hy
    · have hwz : w = z := by simpa using hw
      simpa [hwz] using hz
  have hpair_card : (insert y ({z} : Finset α)).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · simpa using hne
  have htwo_le : 2 ≤ (borderlineSet C X).card := by
    rw [← hpair_card]
    exact Finset.card_le_card hpair_subset
  have hone := hvar X
  omega

/--
The exact finite exchange condition missing from the unconditional asymmetry
argument: the canonical witness for `x ≻ y` and the canonical witness for
`y ≻ x` can both be turned into the same q-sized base by one exchange.

For canonical witnesses `P` and `Q`, this says there are chosen applicants
`a ∈ P` and `b ∈ Q` such that replacing `a` by `y` in `P` gives the same base
as replacing `b` by `x` in `Q`.
-/
def HasCommonCanonicalExchangeBase
    (P Q : Finset α) (x y : α) : Prop :=
  ∃ a, a ∈ P ∧ ∃ b, b ∈ Q ∧
    insert y (P.erase a) = insert x (Q.erase b)

/--
Opposite canonical revealed witnesses are impossible once their one-step
displacements share a common exchanged base.

This is the checked common-base core: the `x ≻ y` canonical witness makes `y`
the displaced element from `insert y (P.erase a)`, while the `y ≻ x` canonical
witness makes `x` the displaced element from the same base.  Variability at
most one then identifies `x` and `y`, contradicting `x ∈ P` and `y ∉ P`.
-/
theorem false_of_opposite_canonical_choices_of_common_exchange
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hvar : VariabilityAtMost 1 C)
    {x y : α} {P Q : Finset α}
    (hxP : x ∈ P) (hyP : y ∉ P) (hcardP : P.card = q)
    (hchoiceP : C (insert y P) = P)
    (hyQ : y ∈ Q) (hxQ : x ∉ Q) (hcardQ : Q.card = q)
    (hchoiceQ : C (insert x Q) = Q)
    (hcommon : HasCommonCanonicalExchangeBase P Q x y) :
    False := by
  classical
  rcases hcommon with ⟨a, haP, b, hbQ, hbase⟩
  have hyBorder :
      y ∈ borderlineSet C (insert y (P.erase a)) :=
    mem_borderlineSet_of_canonical_choice_erase
      (C := C) hfeasible haccept haP hyP hcardP hchoiceP
  have hxBorderQ :
      x ∈ borderlineSet C (insert x (Q.erase b)) :=
    mem_borderlineSet_of_canonical_choice_erase
      (C := C) hfeasible haccept hbQ hxQ hcardQ hchoiceQ
  have hxBorder :
      x ∈ borderlineSet C (insert y (P.erase a)) := by
    simpa [hbase] using hxBorderQ
  have hy_eq_x : y = x :=
    eq_of_mem_borderlineSet_of_variabilityAtMost_one
      (C := C) hvar hyBorder hxBorder
  have hne : x ≠ y := by
    intro hxy
    subst y
    exact hyP hxP
  exact hne hy_eq_x.symm

/--
The exact asymmetry theorem reduces to the finite exchange condition above.

The still-missing finite step is proving `hexchange` for the two canonical
witnesses generated from opposite revealed comparisons.
-/
theorem revealedAbove_asymm_of_variabilityAtMost_one_of_common_exchange
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C) (hvar : VariabilityAtMost 1 C)
    (hexchange :
      ∀ {x y : α} {P Q : Finset α},
        x ∈ P → y ∉ P → P.card = q → C (insert y P) = P →
        y ∈ Q → x ∉ Q → Q.card = q → C (insert x Q) = Q →
        HasCommonCanonicalExchangeBase P Q x y)
    {x y : α} (hxy : RevealedAbove C x y) :
    ¬ RevealedAbove C y x := by
  intro hyx
  have hsub : Substitutable C :=
    substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
      (C := C) hfeasible haccept hunstable
  rcases RevealedAbove.exists_canonical_choice_of_substitutable
      (C := C) hfeasible haccept hsub hxy with
    ⟨P, hxP, hyP, hcardP, hchoiceP⟩
  rcases RevealedAbove.exists_canonical_choice_of_substitutable
      (C := C) hfeasible haccept hsub hyx with
    ⟨Q, hyQ, hxQ, hcardQ, hchoiceQ⟩
  exact false_of_opposite_canonical_choices_of_common_exchange
    (C := C) hfeasible haccept hvar
    hxP hyP hcardP hchoiceP
    hyQ hxQ hcardQ hchoiceQ
    (hexchange hxP hyP hcardP hchoiceP hyQ hxQ hcardQ hchoiceQ)

end FiniteChoice
end EconCSLib
