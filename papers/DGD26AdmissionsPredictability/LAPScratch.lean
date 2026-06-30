import EconCSLib.Foundations.Math.FiniteChoice
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Linear-assignment scratch model

Paper-facing finite scratch work for a linear assignment problem.  Assignments
map each finite slot to either no applicant or one applicant.  Optimality is
kept primitive: no feasible one-slot replacement by a rejected applicant can
strictly raise the finite linear objective.
-/

namespace EconCSLib
namespace FiniteChoice
namespace LAPScratch

variable {α σ : Type*} [DecidableEq α] [DecidableEq σ] [Fintype σ]

/-- A finite-slot assignment.  Each slot contains at most one applicant. -/
structure Assignment (α σ : Type*) where
  matchSlot : σ → Option α

namespace Assignment

/-- Applicant `a` is assigned somewhere. -/
def Assigned (A : Assignment α σ) (a : α) : Prop :=
  ∃ s, A.matchSlot s = some a

/-- Every assigned applicant is drawn from the offered pool `X`. -/
def AssignedFrom (X : Finset α) (A : Assignment α σ) : Prop :=
  ∀ {s a}, A.matchSlot s = some a → a ∈ X

/-- No applicant occupies two distinct slots. -/
def NoDuplicateApplicants (A : Assignment α σ) : Prop :=
  ∀ {s t a}, A.matchSlot s = some a → A.matchSlot t = some a → s = t

/-- Feasibility for the scratch assignment model. -/
def Feasible (X : Finset α) (A : Assignment α σ) : Prop :=
  AssignedFrom X A ∧ NoDuplicateApplicants A

/-- Applicant `a` is in the offered pool but unassigned. -/
def Rejected (X : Finset α) (A : Assignment α σ) (a : α) : Prop :=
  a ∈ X ∧ ¬ Assigned A a

/-- The contribution of one slot to the linear assignment objective. -/
def slotValue (w : α → σ → ℤ) (A : Assignment α σ) (s : σ) : ℤ :=
  match A.matchSlot s with
  | none => 0
  | some a => w a s

/-- Linear objective: sum of assigned applicant-slot weights over all slots. -/
def objective (w : α → σ → ℤ) (A : Assignment α σ) : ℤ :=
  ∑ s : σ, slotValue w A s

/-- Replace the current occupant of slot `s` by applicant `a`. -/
def replaceSlot (A : Assignment α σ) (s : σ) (a : α) : Assignment α σ where
  matchSlot := Function.update A.matchSlot s (some a)

/--
Primitive local optimality: no feasible one-slot replacement of an assigned
slot occupant by a rejected applicant strictly improves the linear objective.
-/
def NoProfitableOneSlotSwap
    (X : Finset α) (w : α → σ → ℤ) (A : Assignment α σ) : Prop :=
  ∀ {s y x},
    A.matchSlot s = some y →
      Rejected X A x →
        Feasible X (replaceSlot A s x) →
          ¬ objective w A < objective w (replaceSlot A s x)

/-- Strict slot order induced by the slot's assignment weight. -/
def SlotBelow (w : α → σ → ℤ) (s : σ) (a b : α) : Prop :=
  w a s < w b s

/-- Weak slot order induced by the slot's assignment weight. -/
def SlotAtLeast (w : α → σ → ℤ) (s : σ) (a b : α) : Prop :=
  w b s ≤ w a s

set_option linter.unusedSectionVars false in
/--
Replacing the occupant of one slot by a strictly higher-weight applicant
strictly raises the finite linear objective.
-/
theorem objective_lt_replaceSlot_of_slot_weight_lt
    {w : α → σ → ℤ} {A : Assignment α σ} {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y) (hweight : w y s < w x s) :
    objective w A < objective w (replaceSlot A s x) := by
  let rest : ℤ := (Finset.univ.erase s).sum fun t => slotValue w A t
  have hrest :
      ((Finset.univ.erase s).sum fun t =>
        slotValue w (replaceSlot A s x) t) = rest := by
    dsimp [rest]
    apply Finset.sum_congr rfl
    intro t ht
    have hts : t ≠ s := (Finset.mem_erase.mp ht).1
    simp [slotValue, replaceSlot, Function.update_of_ne hts]
  have hA :
      objective w A = rest + w y s := by
    dsimp [objective, rest]
    rw [← Finset.sum_erase_add (Finset.univ : Finset σ)
      (fun t => slotValue w A t) (Finset.mem_univ s)]
    simp [slotValue, hslot]
  have hSwap :
      objective w (replaceSlot A s x) = rest + w x s := by
    dsimp [objective]
    rw [← Finset.sum_erase_add (Finset.univ : Finset σ)
      (fun t => slotValue w (replaceSlot A s x) t) (Finset.mem_univ s)]
    rw [hrest]
    simp [slotValue, replaceSlot]
  calc
    objective w A = rest + w y s := hA
    _ < rest + w x s := by
      simpa [add_comm] using add_lt_add_left hweight rest
    _ = objective w (replaceSlot A s x) := hSwap.symm

/--
LAP ordering lemma from primitive optimality: if `y` occupies slot `s`, `x` is
rejected from the same applicant pool, and the one-slot replacement is feasible,
then `y` is not below `x` in the slot-weight order.
-/
theorem not_slotBelow_of_noProfitableOneSlotSwap
    {X : Finset α} {w : α → σ → ℤ} {A : Assignment α σ}
    (hopt : NoProfitableOneSlotSwap X w A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hrej : Rejected X A x)
    (hfeas : Feasible X (replaceSlot A s x)) :
    ¬ SlotBelow w s y x := by
  intro hbelow
  exact hopt hslot hrej hfeas
    (objective_lt_replaceSlot_of_slot_weight_lt hslot hbelow)

/--
Equivalent weak-order form: under the same hypotheses, the assigned applicant
is at least as high as the rejected feasible replacement at slot `s`.
-/
theorem slotAtLeast_of_noProfitableOneSlotSwap
    {X : Finset α} {w : α → σ → ℤ} {A : Assignment α σ}
    (hopt : NoProfitableOneSlotSwap X w A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hrej : Rejected X A x)
    (hfeas : Feasible X (replaceSlot A s x)) :
    SlotAtLeast w s y x := by
  exact le_of_not_gt
    (not_slotBelow_of_noProfitableOneSlotSwap hopt hslot hrej hfeas)

end Assignment

end LAPScratch
end FiniteChoice
end EconCSLib
