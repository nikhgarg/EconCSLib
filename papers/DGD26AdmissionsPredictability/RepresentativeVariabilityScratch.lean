import EconCSLib.Foundations.Math.FiniteChoice
import Mathlib.Tactic

namespace EconCSLib
namespace FiniteChoice

variable {α : Type*}

/-- The irreflexive projection from a library `StrictTotalOrder`. -/
theorem StrictTotalOrder.irrefl {r : α → α → Prop}
    (h : StrictTotalOrder r) (x : α) :
    ¬ r x x :=
  h.1 x

/-- The transitive projection from a library `StrictTotalOrder`. -/
theorem StrictTotalOrder.trans {r : α → α → Prop}
    (h : StrictTotalOrder r) {x y z : α} :
    r x y → r y z → r x z :=
  h.2.1

/-- The complete projection from a library `StrictTotalOrder`. -/
theorem StrictTotalOrder.total {r : α → α → Prop}
    (h : StrictTotalOrder r) {x y : α} :
    x ≠ y → r x y ∨ r y x :=
  h.2.2

/-- A strict total order is asymmetric. -/
theorem StrictTotalOrder.asymm {r : α → α → Prop}
    (h : StrictTotalOrder r) {x y : α} (hxy : r x y) :
    ¬ r y x := by
  intro hyx
  exact h.irrefl x (h.trans hxy hyx)

/-- Related alternatives in a strict total order are distinct. -/
theorem StrictTotalOrder.ne_of_rel {r : α → α → Prop}
    (h : StrictTotalOrder r) {x y : α} (hxy : r x y) :
    x ≠ y := by
  intro hxy_eq
  subst y
  exact h.irrefl x hxy

variable [DecidableEq α]

/-- A q-representative rule is q-acceptant by definition. -/
theorem QRepresentative.qAcceptant {q : ℕ} {C : ChoiceRule α}
    (hrep : QRepresentative q C) :
    QAcceptant q C := by
  rcases hrep with ⟨_, _, haccept, _⟩
  exact haccept

/--
If two finite sets have the same cardinality and `B` has an element missing
from `A`, then `A` has a compensating element missing from `B`.
-/
theorem exists_mem_sdiff_of_card_eq_of_mem_sdiff
    {A B : Finset α} (hcard : A.card = B.card) {x : α}
    (hx : x ∈ B \ A) :
    ∃ y, y ∈ A \ B := by
  rcases Finset.mem_sdiff.mp hx with ⟨hxB, hxnotA⟩
  by_contra hnone
  have hsubset : A ⊆ B := by
    intro y hyA
    by_contra hyB
    exact hnone ⟨y, Finset.mem_sdiff.mpr ⟨hyA, hyB⟩⟩
  have hAB : A = B :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  exact hxnotA (by simpa [hAB] using hxB)

/--
If at most one element of `A` is lost when moving to `B`, then every element
of `A` distinct from a witnessed lost element remains in `B`.
-/
theorem mem_of_mem_of_ne_lost_of_sdiff_card_le_one
    {A B : Finset α} {lost z : α}
    (hlost : lost ∈ A \ B) (hzA : z ∈ A) (hz_ne_lost : z ≠ lost)
    (hcard : (A \ B).card ≤ 1) :
    z ∈ B := by
  by_contra hzB
  have hpair_subset : insert z ({lost} : Finset α) ⊆ A \ B := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact Finset.mem_sdiff.mpr ⟨hzA, hzB⟩
    · have hw_lost : w = lost := by simpa using hw
      simpa [hw_lost] using hlost
  have hpair_card : (insert z ({lost} : Finset α)).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · simpa using hz_ne_lost
  have htwo_le : 2 ≤ (A \ B).card := by
    rw [← hpair_card]
    exact Finset.card_le_card hpair_subset
  omega

/--
Feasible q-representative choice rules are substitutable.  The proof uses the
single representing order to rule out an old rejected element becoming chosen:
equal q-acceptant cardinalities force some old chosen element to be displaced,
which would put the two elements above each other in the strict order.
-/
theorem substitutable_of_feasible_of_qRepresentative
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C) :
    Substitutable C := by
  rcases hrep with ⟨r, hstrict, haccept, hpriority⟩
  intro X₁ X₂ hsubset x hx
  rcases Finset.mem_inter.mp hx with ⟨hxX₁, hxCX₂⟩
  by_contra hxnotCX₁
  by_cases hX₁_le_q : X₁.card ≤ q
  · have hCX₁ : C X₁ = X₁ :=
      QAcceptant.eq_of_card_le hfeasible haccept hX₁_le_q
    exact hxnotCX₁ (by simpa [hCX₁] using hxX₁)
  · have hq_lt_X₁ : q < X₁.card := Nat.lt_of_not_ge hX₁_le_q
    have hq_le_X₁ : q ≤ X₁.card := le_of_lt hq_lt_X₁
    have hq_le_X₂ : q ≤ X₂.card :=
      hq_le_X₁.trans (Finset.card_le_card hsubset)
    have hcard_eq : (C X₁).card = (C X₂).card := by
      rw [haccept X₁, haccept X₂]
      rw [Nat.min_eq_left hq_le_X₁, Nat.min_eq_left hq_le_X₂]
    have hx_sdiff : x ∈ C X₂ \ C X₁ :=
      Finset.mem_sdiff.mpr ⟨hxCX₂, hxnotCX₁⟩
    rcases exists_mem_sdiff_of_card_eq_of_mem_sdiff hcard_eq hx_sdiff with
      ⟨y, hy_sdiff⟩
    rcases Finset.mem_sdiff.mp hy_sdiff with ⟨hyCX₁, hyNotCX₂⟩
    have hyX₁ : y ∈ X₁ := hfeasible X₁ hyCX₁
    have hyX₂ : y ∈ X₂ := hsubset hyX₁
    have hyx : r y x := hpriority hyCX₁ hxX₁ hxnotCX₁
    have hxy : r x y := hpriority hxCX₂ hyX₂ hyNotCX₂
    exact (hstrict.asymm hxy) hyx

/-- Feasible q-representative choice rules are 1-unstable for one fresh addition. -/
theorem dUnstable_one_of_feasible_of_qRepresentative
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C) :
    DUnstable 1 C := by
  exact dUnstable_one_of_feasible_of_qAcceptant_of_substitutable
    (C := C) hfeasible hrep.qAcceptant
    (substitutable_of_feasible_of_qRepresentative hfeasible hrep)

/-- In a feasible q-representative rule, one fresh applicant can displace at most one old choice. -/
theorem choiceLossTerm_insert_le_one_of_feasible_of_qRepresentative
    {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C)
    {X : Finset α} {x : α} (hx : x ∉ X) :
    choiceLossTerm C X (insert x X) ≤ 1 := by
  have hdist :=
    dUnstable_one_of_feasible_of_qRepresentative
      (C := C) hfeasible hrep X x hx
  rw [choiceDistance] at hdist
  omega

/--
Any two applicants in the borderline set of a feasible q-representative rule
must coincide.
-/
theorem eq_of_mem_borderlineSet_of_feasible_of_qRepresentative
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C)
    {X : Finset α} {y z : α}
    (hyB : y ∈ borderlineSet C X) (hzB : z ∈ borderlineSet C X) :
    y = z := by
  classical
  by_contra hy_ne_z
  rcases hrep with ⟨r, hstrict, haccept, hpriority⟩
  have hrep' : QRepresentative q C := ⟨r, hstrict, haccept, hpriority⟩
  rw [borderlineSet] at hyB hzB
  rcases Finset.mem_biUnion.mp hyB with ⟨a, _ha, hya⟩
  rcases Finset.mem_biUnion.mp hzB with ⟨b, _hb, hzb⟩
  rcases Finset.mem_sdiff.mp hya with ⟨hyCX, hyNotCa⟩
  rcases Finset.mem_sdiff.mp hzb with ⟨hzCX, hzNotCb⟩
  have hyX : y ∈ X := hfeasible X hyCX
  have hzX : z ∈ X := hfeasible X hzCX
  have ha_not_X : a ∉ X := by
    intro haX
    exact hyNotCa (by simpa [Finset.insert_eq_of_mem haX] using hyCX)
  have hb_not_X : b ∉ X := by
    intro hbX
    exact hzNotCb (by simpa [Finset.insert_eq_of_mem hbX] using hzCX)
  have hLossA : (C X \ C (insert a X)).card ≤ 1 := by
    simpa [choiceLossTerm] using
      choiceLossTerm_insert_le_one_of_feasible_of_qRepresentative
        (C := C) hfeasible hrep' (X := X) (x := a) ha_not_X
  have hLossB : (C X \ C (insert b X)).card ≤ 1 := by
    simpa [choiceLossTerm] using
      choiceLossTerm_insert_le_one_of_feasible_of_qRepresentative
        (C := C) hfeasible hrep' (X := X) (x := b) hb_not_X
  have hzCa : z ∈ C (insert a X) :=
    mem_of_mem_of_ne_lost_of_sdiff_card_le_one
      (A := C X) (B := C (insert a X)) (lost := y) (z := z)
      (Finset.mem_sdiff.mpr ⟨hyCX, hyNotCa⟩) hzCX
      (by intro hzy; exact hy_ne_z hzy.symm) hLossA
  have hyCb : y ∈ C (insert b X) :=
    mem_of_mem_of_ne_lost_of_sdiff_card_le_one
      (A := C X) (B := C (insert b X)) (lost := z) (z := y)
      (Finset.mem_sdiff.mpr ⟨hzCX, hzNotCb⟩) hyCX
      (by intro hyz; exact hy_ne_z hyz) hLossB
  have hr_zy : r z y :=
    hpriority hzCa (Finset.mem_insert_of_mem hyX) hyNotCa
  have hr_yz : r y z :=
    hpriority hyCb (Finset.mem_insert_of_mem hzX) hzNotCb
  exact (hstrict.asymm hr_yz) hr_zy

/-- Feasible q-representative choice rules have main-text variability at most one. -/
theorem variabilityAtMost_one_of_feasible_of_qRepresentative
    [Fintype α] {q : ℕ} {C : ChoiceRule α}
    (hfeasible : Feasible C) (hrep : QRepresentative q C) :
    VariabilityAtMost 1 C := by
  intro X
  classical
  let B : Finset α := borderlineSet C X
  by_cases hB_empty : B = ∅
  · simp [B, hB_empty]
  · rcases Finset.nonempty_of_ne_empty hB_empty with ⟨y, hyB⟩
    have hsubset : B ⊆ ({y} : Finset α) := by
      intro z hzB
      have hz_eq_y : z = y :=
        eq_of_mem_borderlineSet_of_feasible_of_qRepresentative
          (C := C) hfeasible hrep
          (by simpa [B] using hzB) (by simpa [B] using hyB)
      simp [hz_eq_y]
    have hcard := Finset.card_le_card hsubset
    simpa [B] using hcard

end FiniteChoice
end EconCSLib
