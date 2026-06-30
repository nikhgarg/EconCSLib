import EconCSLib.Foundations.Math.FiniteChoice
import Mathlib.Order.Extension.Linear
import Mathlib.Tactic

/-!
# Scratch work for the converse q-representativeness direction

This file is intentionally paper-local scratch.  It develops the revealed
preference relation used in the informal converse proof and isolates the
remaining exchange step needed to construct a representing strict total order.
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
  rintro ⟨X, hxCX, _hxX, hxNotCX⟩
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

theorem RevealedAbove.of_canonical_choice
    {C : ChoiceRule α} {P : Finset α} {x y : α}
    (hxP : x ∈ P) (hyP : y ∉ P) (hchoice : C (insert y P) = P) :
    RevealedAbove C x y := by
  refine ⟨insert y P, ?_, ?_, ?_⟩
  · simpa [hchoice] using hxP
  · exact Finset.mem_insert_self y P
  · simpa [hchoice] using hyP

/--
For a substitutable rule, choosing after adding one applicant only depends on
the old chosen set.  This is the consistency step used repeatedly in the paper's
converse proof.
-/
theorem choice_insert_eq_choice_insert_choice_of_substitutable
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) (X : Finset α) (a : α) :
    C (insert a X) = C (insert a (C X)) := by
  have hconsistent : Consistent C :=
    consistent_of_qAcceptant_of_substitutable haccept hsub
  have hX_subset : X ⊆ insert a X := by
    intro z hz
    exact Finset.mem_insert_of_mem hz
  have hchosen_subset : C (insert a X) ⊆ insert a (C X) := by
    intro z hz
    have hzOffered : z ∈ insert a X := hfeasible (insert a X) hz
    rw [Finset.mem_insert] at hzOffered
    rcases hzOffered with rfl | hzX
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (hsub hX_subset (Finset.mem_inter.mpr ⟨hzX, hz⟩))
  have hinsert_subset : insert a (C X) ⊆ insert a X := by
    intro z hz
    rw [Finset.mem_insert] at hz ⊢
    rcases hz with rfl | hzCX
    · exact Or.inl rfl
    · exact Or.inr (hfeasible X hzCX)
  exact hconsistent hchosen_subset hinsert_subset

/--
The borderline set only depends on the current chosen set for feasible,
q-acceptant, substitutable choice rules.
-/
theorem borderlineSet_eq_of_choice_eq_of_substitutable
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C) {X₁ X₂ : Finset α}
    (hchoice : C X₁ = C X₂) :
    borderlineSet C X₁ = borderlineSet C X₂ := by
  classical
  have hinsert : ∀ a, C (insert a X₁) = C (insert a X₂) := by
    intro a
    rw [choice_insert_eq_choice_insert_choice_of_substitutable
        (C := C) hfeasible haccept hsub X₁ a,
      choice_insert_eq_choice_insert_choice_of_substitutable
        (C := C) hfeasible haccept hsub X₂ a,
      hchoice]
  ext z
  constructor
  · intro hz
    rw [borderlineSet] at hz ⊢
    rcases Finset.mem_biUnion.mp hz with ⟨a, _ha, hzloss⟩
    exact Finset.mem_biUnion.mpr
      ⟨a, Finset.mem_univ a, by
        rcases Finset.mem_sdiff.mp hzloss with ⟨hzCX₁, hzNot⟩
        exact Finset.mem_sdiff.mpr
          ⟨by simpa [← hchoice] using hzCX₁,
            by
              intro hzCX₂a
              exact hzNot (by simpa [hinsert a] using hzCX₂a)⟩⟩
  · intro hz
    rw [borderlineSet] at hz ⊢
    rcases Finset.mem_biUnion.mp hz with ⟨a, _ha, hzloss⟩
    exact Finset.mem_biUnion.mpr
      ⟨a, Finset.mem_univ a, by
        rcases Finset.mem_sdiff.mp hzloss with ⟨hzCX₂, hzNot⟩
        exact Finset.mem_sdiff.mpr
          ⟨by simpa [hchoice] using hzCX₂,
            by
              intro hzCX₁a
              exact hzNot (by simpa [hinsert a] using hzCX₁a)⟩⟩

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
Equivalently, two distinct currently chosen elements cannot both be displaced
from the same base by two different fresh additions.
-/
theorem not_two_distinct_losses_same_base_of_variabilityAtMost_one
    [Fintype α] {C : ChoiceRule α}
    (hvar : VariabilityAtMost 1 C) {X : Finset α}
    {a b y z : α}
    (hy : y ∈ C X \ C (insert a X))
    (hz : z ∈ C X \ C (insert b X)) :
    y = z := by
  classical
  have hyB : y ∈ borderlineSet C X := by
    rw [borderlineSet]
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hy⟩
  have hzB : z ∈ borderlineSet C X := by
    rw [borderlineSet]
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, hz⟩
  exact eq_of_mem_borderlineSet_of_variabilityAtMost_one hvar hyB hzB

/--
If a revealed cycle can be converted into two one-step losses from the same
base pool, variability at most one immediately rules it out.  The missing hard
part of the full asymmetry proof is exactly constructing such a common base
from arbitrary opposite revealed witnesses.
-/
theorem false_of_revealedAbove_cycle_of_common_loss_base
    [Fintype α] {C : ChoiceRule α}
    (hvar : VariabilityAtMost 1 C) {x y : α}
    (hxy : RevealedAbove C x y) (_hyx : RevealedAbove C y x)
    {X : Finset α} {a b : α}
    (hyLoss : y ∈ C X \ C (insert a X))
    (hxLoss : x ∈ C X \ C (insert b X)) :
    False := by
  have hy_eq_x :
      y = x :=
    not_two_distinct_losses_same_base_of_variabilityAtMost_one
      hvar hyLoss hxLoss
  exact RevealedAbove.ne hxy hy_eq_x.symm

/--
Exact variability one is the upper bound plus a genuine one-step displacement.
This is the minimal extra nontriviality condition: without a displacement,
`VariabilityAtMost 1` can hold vacuously with exact variability zero.
-/
theorem hasDisplacement_of_variabilityExactly_one
    [Fintype α] {C : ChoiceRule α}
    (hexact : VariabilityExactly 1 C) :
    HasDisplacement C := by
  classical
  rcases hexact with ⟨_hatMost, X, hcard⟩
  have hpos : 0 < (borderlineSet C X).card := by
    omega
  rcases Finset.card_pos.mp hpos with ⟨y, hyB⟩
  rw [borderlineSet] at hyB
  rcases Finset.mem_biUnion.mp hyB with ⟨x, _hxUniv, hyloss⟩
  rcases Finset.mem_sdiff.mp hyloss with ⟨hyCX, hyNotCX'⟩
  have hxNotX : x ∉ X := by
    intro hxX
    exact hyNotCX'
      (by simpa [Finset.insert_eq_of_mem hxX] using hyCX)
  exact ⟨X, x, y, hxNotX, hyCX, hyNotCX'⟩

theorem variabilityExactly_one_iff_atMost_one_and_hasDisplacement
    [Fintype α] {C : ChoiceRule α} :
    VariabilityExactly 1 C ↔
      VariabilityAtMost 1 C ∧ HasDisplacement C := by
  constructor
  · intro hexact
    exact ⟨hexact.1, hasDisplacement_of_variabilityExactly_one hexact⟩
  · rintro ⟨hatMost, hdisp⟩
    exact variabilityExactly_one_of_atMost_one_of_hasDisplacement
      hatMost hdisp

/--
The paper's transitivity step is clean once asymmetry of the revealed relation
is available: add `c` to a canonical witness for `a ≻ b`; if `c` were chosen,
it would reveal `c ≻ b`, contradicting `b ≻ c`.
-/
theorem RevealedAbove.trans_of_asymm
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hsub : Substitutable C)
    (hasymm : ∀ {x y}, RevealedAbove C x y → ¬ RevealedAbove C y x)
    {a b c : α}
    (hab : RevealedAbove C a b) (hbc : RevealedAbove C b c) :
    RevealedAbove C a c := by
  rcases RevealedAbove.exists_canonical_choice_of_substitutable
      hfeasible haccept hsub hab with
    ⟨P, haP, hbP, _hcardP, hchoiceP⟩
  let X : Finset α := insert b P
  have haCX : a ∈ C X := by
    simpa [X, hchoiceP] using haP
  have hbX : b ∈ X := Finset.mem_insert_self b P
  have hbNotCX : b ∉ C X := by
    simpa [X, hchoiceP] using hbP
  let Xc : Finset α := insert c X
  have hX_subset_Xc : X ⊆ Xc := by
    intro z hz
    exact Finset.mem_insert_of_mem hz
  have hcNotCXc : c ∉ C Xc := by
    intro hcCXc
    have hbNotCXc : b ∉ C Xc := by
      intro hbCXc
      exact hbNotCX
        (hsub hX_subset_Xc (Finset.mem_inter.mpr ⟨hbX, hbCXc⟩))
    have hcb : RevealedAbove C c b :=
      ⟨Xc, hcCXc, Finset.mem_insert_of_mem hbX, hbNotCXc⟩
    exact hasymm hbc hcb
  have hCXc_subset_X : C Xc ⊆ X := by
    intro z hz
    have hzOffered : z ∈ Xc := hfeasible Xc hz
    rw [Finset.mem_insert] at hzOffered
    rcases hzOffered with rfl | hzX
    · exact False.elim (hcNotCXc hz)
    · exact hzX
  have hconsistent : Consistent C :=
    consistent_of_qAcceptant_of_substitutable haccept hsub
  have hsame : C Xc = C X :=
    hconsistent hCXc_subset_X hX_subset_Xc
  refine ⟨Xc, ?_, Finset.mem_insert_self c X, hcNotCXc⟩
  simpa [hsame] using haCX

namespace RevealedAbove

/-- A transitive revealed relation is asymmetric because it is irreflexive. -/
theorem asymm_of_trans {C : ChoiceRule α}
    (htrans :
      ∀ {x y z}, RevealedAbove C x y → RevealedAbove C y z →
        RevealedAbove C x z)
    {x y : α} (hxy : RevealedAbove C x y) :
    ¬ RevealedAbove C y x := by
  intro hyx
  exact RevealedAbove.irrefl (C := C) x (htrans hxy hyx)

end RevealedAbove

set_option linter.unusedSectionVars false in
/--
Any irreflexive transitive relation extends to a strict total order.  This is
the order-extension hook needed once revealed-preference transitivity is proved.
-/
theorem exists_strictTotalOrder_extension_of_trans
    {r : α → α → Prop}
    (hirr : ∀ x, ¬ r x x)
    (htrans : ∀ {x y z}, r x y → r y z → r x z) :
    ∃ s : α → α → Prop, StrictTotalOrder s ∧
      ∀ {x y}, r x y → s x y := by
  classical
  let leR : α → α → Prop := fun x y => x = y ∨ r x y
  haveI : IsPartialOrder α leR := by
    refine
      { refl := ?_
        trans := ?_
        antisymm := ?_ }
    · intro x
      exact Or.inl rfl
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      rcases hyz with rfl | hyz
      · exact Or.inr hxy
      · exact Or.inr (htrans hxy hyz)
    · intro x y hxy hyx
      rcases hxy with hxy_eq | hxy_rel
      · exact hxy_eq
      rcases hyx with hyx_eq | hyx_rel
      · exact hyx_eq.symm
      · exact False.elim (hirr x (htrans hxy_rel hyx_rel))
  rcases extend_partialOrder leR with ⟨le, hlinear, hle⟩
  let s : α → α → Prop := fun x y => le x y ∧ x ≠ y
  refine ⟨s, ?_, ?_⟩
  · constructor
    · intro x hx
      exact hx.2 rfl
    constructor
    · intro x y z hxy hyz
      refine ⟨hlinear.trans x y z hxy.1 hyz.1, ?_⟩
      intro hxz
      subst z
      have hyx : le y x := hyz.1
      have hxy_eq : x = y := hlinear.antisymm x y hxy.1 hyx
      exact hxy.2 hxy_eq
    · intro x y hne
      rcases hlinear.total x y with hxy | hyx
      · exact Or.inl ⟨hxy, hne⟩
      · exact Or.inr ⟨hyx, hne.symm⟩
  · intro x y hxy
    refine ⟨hle x y (Or.inr hxy), ?_⟩
    intro hxy_eq
    subst y
    exact hirr x hxy

/--
If revealed preference is transitive, extending it gives a q-representative
order immediately.
-/
theorem qRepresentative_of_revealedAbove_trans
    {q : ℕ} {C : ChoiceRule α}
    (haccept : QAcceptant q C)
    (htrans :
      ∀ {x y z}, RevealedAbove C x y → RevealedAbove C y z →
        RevealedAbove C x z) :
    QRepresentative q C := by
  rcases exists_strictTotalOrder_extension_of_trans
      (r := RevealedAbove C)
      (fun x => RevealedAbove.irrefl (C := C) x)
      (by intro x y z hxy hyz; exact htrans hxy hyz) with
    ⟨r, hstrict, hext⟩
  refine ⟨r, hstrict, haccept, ?_⟩
  intro X x y hxCX hyX hyNotCX
  exact hext ⟨X, hxCX, hyX, hyNotCX⟩

/--
Thus the full converse is reduced to the asymmetry/exchange argument.  The
paper's transitivity proof and mathlib's order-extension theorem handle the
rest.
-/
theorem qRepresentative_of_revealedAbove_asymm
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (haccept : QAcceptant q C)
    (hunstable : DUnstable 1 C)
    (hasymm : ∀ {x y}, RevealedAbove C x y → ¬ RevealedAbove C y x) :
    QRepresentative q C := by
  have hsub : Substitutable C :=
    substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
      (C := C) hfeasible haccept hunstable
  apply qRepresentative_of_revealedAbove_trans (C := C) haccept
  intro x y z hxy hyz
  exact RevealedAbove.trans_of_asymm
    (C := C) hfeasible haccept hsub hasymm hxy hyz

end FiniteChoice
end EconCSLib
