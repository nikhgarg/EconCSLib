import EconCSLib.Foundations.Math.FiniteChoice
import Mathlib.Tactic

/-!
# Tight instability construction scratch work

Concrete checked examples toward the construction claim that feasible
q-acceptant rules can be tightly d-unstable for every `1 ≤ d ≤ 2q`.

The first example is a `q = 1` priority rule with tight instability `1`.
The second example is a `q = 2` grouped/complementary rule with tight
instability `3`: adding applicant `2` to `{0, 1, 3}` flips the choice from
the old pair `{0, 1}` to `{2, 3}`.

Remaining all-d schema:
* Odd `d = 2m - 1`: start from a pool with `m` chosen old applicants and
  at least `m - 1` rejected old complements.  The fresh applicant triggers a
  group switch that drops all `m` old choices and chooses the fresh applicant
  plus `m - 1` old complements.  The one-step distance is
  `m` losses plus `m - 1` old gains.
* Even `d = 2m`: use the same switch, but make the fresh applicant rejected
  after insertion and choose `m` old complements instead.  The one-step
  distance is `m` losses plus `m` old gains.

To finish the paper-level claim, parameterize the rule over two disjoint old
blocks of size `m` (and a fresh trigger), prove the global one-step upper
bound by reducing to the switch/non-switch cases, and reuse the witnessed
distance to rule out smaller bounds.
-/

namespace EconCSLib
namespace FiniteChoice

/-! ## A tight 1-instability example -/

/-- A `q = 1` priority rule on `Fin 2`: applicant `0` beats applicant `1`. -/
def tightOneChoice : ChoiceRule (Fin 2) :=
  fun X =>
    if (0 : Fin 2) ∈ X then
      {(0 : Fin 2)}
    else
      X

/-- The singleton pool used to witness nonzero one-step instability. -/
def tightOneBase : Finset (Fin 2) :=
  {(1 : Fin 2)}

/-- The fresh high-priority applicant for the tight-1 witness. -/
def tightOneFresh : Fin 2 :=
  (0 : Fin 2)

theorem tightOne_feasible :
    Feasible tightOneChoice := by
  intro X
  fin_cases X <;> native_decide

theorem tightOne_qAcceptant :
    QAcceptant 1 tightOneChoice := by
  intro X
  fin_cases X <;> native_decide

theorem tightOne_dUnstable_one :
    DUnstable 1 tightOneChoice := by
  intro X x _hx
  fin_cases X <;> fin_cases x <;> native_decide

theorem tightOne_fresh_not_mem_base :
    tightOneFresh ∉ tightOneBase := by
  native_decide

theorem tightOne_choiceDistance_witness :
    choiceDistance tightOneChoice tightOneBase
      (insert tightOneFresh tightOneBase) = 1 := by
  native_decide

theorem tightOne_tightlyDUnstable_one :
    TightlyDUnstable 1 tightOneChoice := by
  constructor
  · exact tightOne_dUnstable_one
  · intro k hk hunstable
    have hle : 1 ≤ k := by
      have hdist := hunstable tightOneBase tightOneFresh
        tightOne_fresh_not_mem_base
      simpa [tightOne_choiceDistance_witness] using hdist
    omega

/-! ## A tight odd higher-instability example -/

/--
A grouped/complementary `q = 2` rule on `Fin 4`.

For pools of size at most two it accepts everyone.  For larger pools, the
presence of both applicants `2` and `3` triggers the complementary group
`{2, 3}`; otherwise the rule chooses `{0, 1}`.  On the pool `{0, 1, 3}`,
adding `2` switches the accepted pair from `{0, 1}` to `{2, 3}`.
-/
def tightThreeChoice : ChoiceRule (Fin 4) :=
  fun X =>
    if X.card ≤ 2 then
      X
    else if (2 : Fin 4) ∈ X ∧ (3 : Fin 4) ∈ X then
      {(2 : Fin 4), (3 : Fin 4)}
    else
      {(0 : Fin 4), (1 : Fin 4)}

/-- The pool whose one-step expansion attains distance `3`. -/
def tightThreeBase : Finset (Fin 4) :=
  {(0 : Fin 4), (1 : Fin 4), (3 : Fin 4)}

/-- The fresh applicant that triggers the complementary group. -/
def tightThreeFresh : Fin 4 :=
  (2 : Fin 4)

theorem tightThree_feasible :
    Feasible tightThreeChoice := by
  intro X
  fin_cases X <;> native_decide

theorem tightThree_qAcceptant :
    QAcceptant 2 tightThreeChoice := by
  intro X
  fin_cases X <;> native_decide

theorem tightThree_dUnstable_three :
    DUnstable 3 tightThreeChoice := by
  intro X x _hx
  fin_cases X <;> fin_cases x <;> native_decide

theorem tightThree_base_card_ge :
    2 ≤ tightThreeBase.card := by
  native_decide

theorem tightThree_fresh_not_mem_base :
    tightThreeFresh ∉ tightThreeBase := by
  native_decide

theorem tightThree_fresh_chosen_after_insert :
    tightThreeFresh ∈ tightThreeChoice
      (insert tightThreeFresh tightThreeBase) := by
  native_decide

theorem tightThree_loss_card_witness :
    (tightThreeChoice tightThreeBase \
      tightThreeChoice (insert tightThreeFresh tightThreeBase)).card = 2 := by
  native_decide

/--
The nontrivial one-step calculation, using the library's insert-distance
formula.  Since the fresh applicant is chosen and both old choices are lost,
the distance is `2 * 2 - 1 = 3`.
-/
theorem tightThree_choiceDistance_witness :
    choiceDistance tightThreeChoice tightThreeBase
      (insert tightThreeFresh tightThreeBase) = 3 := by
  rw [choiceDistance_insert_eq_if_mem
    (C := tightThreeChoice) (q := 2)
    tightThree_feasible tightThree_qAcceptant
    tightThree_base_card_ge tightThree_fresh_not_mem_base]
  simp [tightThree_fresh_chosen_after_insert,
    tightThree_loss_card_witness]

theorem tightThree_tightlyDUnstable_three :
    TightlyDUnstable 3 tightThreeChoice := by
  constructor
  · exact tightThree_dUnstable_three
  · intro k hk hunstable
    have hle : 3 ≤ k := by
      have hdist := hunstable tightThreeBase tightThreeFresh
        tightThree_fresh_not_mem_base
      simpa [tightThree_choiceDistance_witness] using hdist
    omega

end FiniteChoice
end EconCSLib
