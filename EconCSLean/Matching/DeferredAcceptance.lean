import EconCSLean.Matching.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace EconCSLean
namespace Matching

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

structure DAState (M W : Type*) where
  m_match : M → Option W
  w_match : W → Option M
  m_proposals : M → Finset W
  consistent : ∀ m w, m_match m = some w ↔ w_match w = some m

def initialDAState (M W : Type*) [Fintype W] : DAState M W where
  m_match _ := none
  w_match _ := none
  m_proposals _ := Finset.univ
  consistent m w := by simp

def IsActiveMan (val_m : M → W → ℝ) (s : DAState M W) (m : M) : Prop :=
  s.m_match m = none ∧ ∃ w ∈ s.m_proposals m, 0 ≤ val_m m w

def BestRemainingWoman (val_m : M → W → ℝ) (s : DAState M W) (m : M) (w : W) : Prop :=
  w ∈ s.m_proposals m ∧ 0 ≤ val_m m w ∧
  ∀ w' ∈ s.m_proposals m, 0 ≤ val_m m w' → val_m m w' ≤ val_m m w

lemma exists_best_woman (val_m : M → W → ℝ) (s : DAState M W) (m : M)
    (hact : IsActiveMan val_m s m) : ∃ w, BestRemainingWoman val_m s m w := by
  sorry

noncomputable def daStep (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) : DAState M W :=
  have _ : Decidable (∃ m, IsActiveMan val_m s m) := Classical.propDecidable _
  if h : ∃ m, IsActiveMan val_m s m then
    let m := Classical.choose h
    let hact := Classical.choose_spec h
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    let hw_best := Classical.choose_spec w_exists

    let new_proposals := fun m' => if m' = m then s.m_proposals m \ {w} else s.m_proposals m'
    let m_current := s.w_match w
    let accepts :=
      match m_current with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m

    have _ : Decidable accepts := Classical.propDecidable _
    if hacc : accepts then
      let new_w_match := Function.update s.w_match w (some m)
      let new_m_match := fun m'' =>
        if m'' = m then some w
        else if m_current = some m'' then none
        else s.m_match m''
      { m_match := new_m_match
        w_match := new_w_match
        m_proposals := new_proposals
        consistent := sorry }
    else
      { s with m_proposals := new_proposals }
  else
    s

-- DA algorithm fold
noncomputable def deferredAcceptanceState (val_m : M → W → ℝ) (val_w : W → M → ℝ) : DAState M W :=
  let max_steps := Fintype.card M * Fintype.card W
  (List.range max_steps).foldl (fun s _ => daStep val_m val_w s) (initialDAState M W)

noncomputable def deferredAcceptance (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W where
  m_match := (deferredAcceptanceState val_m val_w).m_match
  w_match := (deferredAcceptanceState val_m val_w).w_match
  consistent_m := (deferredAcceptanceState val_m val_w).consistent

/-! ### Local Invariants -/

def ManIRInvariant (val_m : M → W → ℝ) (s : DAState M W) : Prop :=
  ∀ m w, s.m_match m = some w → 0 ≤ val_m m w

def WomanIRInvariant (val_w : W → M → ℝ) (s : DAState M W) : Prop :=
  ∀ w m, s.w_match w = some m → 0 ≤ val_w w m

def MatchedProposedInvariant (s : DAState M W) : Prop :=
  ∀ m w, s.m_match m = some w → w ∉ s.m_proposals m

def WomanRejectionInvariant (val_w : W → M → ℝ) (s : DAState M W) : Prop :=
  ∀ w m', w ∉ s.m_proposals m' →
    val_w w m' < 0 ∨ (∃ m, s.w_match w = some m ∧ val_w w m' < val_w w m)

def ManProposalOrderInvariant (val_m : M → W → ℝ) (s : DAState M W) : Prop :=
  ∀ m w w', w ∉ s.m_proposals m → w' ∈ s.m_proposals m → 0 ≤ val_m m w' →
    val_m m w' ≤ val_m m w

def DAInvariants (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W) : Prop :=
  ManIRInvariant val_m s ∧
  WomanIRInvariant val_w s ∧
  MatchedProposedInvariant s ∧
  WomanRejectionInvariant val_w s ∧
  ManProposalOrderInvariant val_m s

lemma initialDAState_satisfies_invariants (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAInvariants val_m val_w (initialDAState M W) := by
  sorry

lemma daStep_preserves_invariants (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W) :
    DAInvariants val_m val_w s → DAInvariants val_m val_w (daStep val_m val_w s) := by
  sorry

lemma deferredAcceptanceState_satisfies_invariants (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAInvariants val_m val_w (deferredAcceptanceState val_m val_w) := by
  sorry

/-- 
If a state satisfies the invariants and no men are active (termination), 
then the matching is stable.
-/
lemma stable_of_invariants_and_terminated (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hinv : DAInvariants val_m val_w s)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m) :
    IsStable val_m val_w ⟨s.m_match, s.w_match, s.consistent⟩ := by
  sorry

lemma deferredAcceptanceState_terminated (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    ¬ ∃ m, IsActiveMan val_m (deferredAcceptanceState val_m val_w) m := by
  sorry

def DaProducesStableMatchingCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  DAInvariants val_m val_w (deferredAcceptanceState val_m val_w) ∧
  ¬ ∃ m, IsActiveMan val_m (deferredAcceptanceState val_m val_w) m

theorem da_produces_stable_matching_of_certificate (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaProducesStableMatchingCertificate val_m val_w) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) := by
  exact stable_of_invariants_and_terminated val_m val_w (deferredAcceptanceState val_m val_w) hcert.1 hcert.2

def DaIsMenOptimalCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ∀ mu', IsStable val_m val_w mu' →
    ∀ m, valM val_m m (mu'.m_match m) ≤ valM val_m m ((deferredAcceptance val_m val_w).m_match m)

end Matching
end EconCSLean
