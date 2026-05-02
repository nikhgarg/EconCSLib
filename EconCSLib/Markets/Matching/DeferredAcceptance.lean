import EconCSLib.Markets.Matching.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace EconCSLib
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
  rcases hact with ⟨_, w0, hw0_mem, hw0_nonneg⟩
  let eligible : Finset W := (s.m_proposals m).filter fun w => 0 ≤ val_m m w
  have helig_nonempty : eligible.Nonempty := by
    refine ⟨w0, ?_⟩
    simp [eligible, hw0_mem, hw0_nonneg]
  obtain ⟨w, hw_eligible, hw_max⟩ :=
    Finset.exists_max_image eligible (fun w => val_m m w) helig_nonempty
  refine ⟨w, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hw_eligible).1
  · exact (Finset.mem_filter.mp hw_eligible).2
  · intro w' hw'_mem hw'_nonneg
    exact hw_max w' (by simp [eligible, hw'_mem, hw'_nonneg])

lemma acceptMatch_consistent (s : DAState M W) {m : M} {w : W}
    (hm_unmatched : s.m_match m = none) :
    ∀ m0 w0,
      (if m0 = m then some w
        else if s.w_match w = some m0 then none
        else s.m_match m0) = some w0 ↔
      Function.update s.w_match w (some m) w0 = some m0 := by
  intro m0 w0
  by_cases hm : m0 = m
  · subst m0
    by_cases hw : w0 = w
    · subst w0
      simp
    · have hw' : w ≠ w0 := fun h => hw h.symm
      have hnot_old : s.w_match w0 ≠ some m := by
        intro hwm
        have hmmatch : s.m_match m = some w0 := (s.consistent m w0).2 hwm
        rw [hm_unmatched] at hmmatch
        cases hmmatch
      simp [hw, hw', hnot_old]
  · by_cases hw : w0 = w
    · subst w0
      have hm' : m ≠ m0 := fun h => hm h.symm
      by_cases hcur : s.w_match w = some m0
      · simp [hm, hm', hcur]
      · have hnot_old : s.m_match m0 ≠ some w := by
          intro hmmatch
          exact hcur ((s.consistent m0 w).1 hmmatch)
        simp [hm, hm', hcur, hnot_old]
    · by_cases hcur : s.w_match w = some m0
      · have hnot_old : s.w_match w0 ≠ some m0 := by
          intro hwm0
          have hm_w : s.m_match m0 = some w := (s.consistent m0 w).2 hcur
          have hm_w0 : s.m_match m0 = some w0 := (s.consistent m0 w0).2 hwm0
          have : w0 = w := Option.some.inj (hm_w0.symm.trans hm_w)
          exact hw this
        simp [hm, hw, hcur, hnot_old]
      · simpa [hm, hw, hcur] using (s.consistent m0 w0)

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
        consistent := by
          simpa [new_m_match, new_w_match, m_current] using
            acceptMatch_consistent s hact.1 }
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
  simp [DAInvariants, ManIRInvariant, WomanIRInvariant, MatchedProposedInvariant,
    WomanRejectionInvariant, ManProposalOrderInvariant, initialDAState]

def DAStepPreservesInvariantsCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ∀ s, DAInvariants val_m val_w s → DAInvariants val_m val_w (daStep val_m val_w s)

lemma daStep_preserves_invariants (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W) :
    DAStepPreservesInvariantsCertificate val_m val_w →
    DAInvariants val_m val_w s → DAInvariants val_m val_w (daStep val_m val_w s) := by
  intro hcert
  exact hcert s

def DAStateInvariantCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  DAInvariants val_m val_w (deferredAcceptanceState val_m val_w)

lemma deferredAcceptanceState_satisfies_invariants (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAStateInvariantCertificate val_m val_w →
    DAInvariants val_m val_w (deferredAcceptanceState val_m val_w) := by
  intro hcert
  exact hcert

def DAStableFromTerminatedInvariantsCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    Prop :=
  ∀ s, DAInvariants val_m val_w s →
    (¬ ∃ m, IsActiveMan val_m s m) →
    IsStable val_m val_w ⟨s.m_match, s.w_match, s.consistent⟩

/--
If a state satisfies the invariants and no men are active (termination), 
then the matching is stable.
-/
lemma stable_of_invariants_and_terminated (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hcert : DAStableFromTerminatedInvariantsCertificate val_m val_w)
    (hinv : DAInvariants val_m val_w s)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m) :
    IsStable val_m val_w ⟨s.m_match, s.w_match, s.consistent⟩ := by
  exact hcert s hinv hterm

def DATerminationCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ¬ ∃ m, IsActiveMan val_m (deferredAcceptanceState val_m val_w) m

lemma deferredAcceptanceState_terminated (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DATerminationCertificate val_m val_w →
    ¬ ∃ m, IsActiveMan val_m (deferredAcceptanceState val_m val_w) m := by
  intro hcert
  exact hcert

def DaProducesStableMatchingCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  DAStateInvariantCertificate val_m val_w ∧
  DATerminationCertificate val_m val_w ∧
  DAStableFromTerminatedInvariantsCertificate val_m val_w

theorem da_produces_stable_matching_of_certificate (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaProducesStableMatchingCertificate val_m val_w) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) := by
  exact stable_of_invariants_and_terminated val_m val_w (deferredAcceptanceState val_m val_w)
    hcert.2.2 hcert.1 hcert.2.1

def DaIsMenOptimalCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ∀ mu', IsStable val_m val_w mu' →
    ∀ m, valM val_m m (mu'.m_match m) ≤ valM val_m m ((deferredAcceptance val_m val_w).m_match m)

/-- A DA state with invariants and no active man is stable. -/
theorem daState_stable_of_invariants_and_termination (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hinv : DAInvariants val_m val_w s)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m)
    (hstable : DAStableFromTerminatedInvariantsCertificate val_m val_w) :
    IsStable val_m val_w ⟨s.m_match, s.w_match, s.consistent⟩ :=
  stable_of_invariants_and_terminated val_m val_w s hstable hinv hterm

/-- Stable matching from separated DA certificate components.

This gives a direct API that avoids unpacking `DaProducesStableMatchingCertificate`.
-/
theorem deferredAcceptance_stable_of_certificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstate : DAStateInvariantCertificate val_m val_w)
    (hterm : DATerminationCertificate val_m val_w)
    (hstable : DAStableFromTerminatedInvariantsCertificate val_m val_w) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) :=
  stable_of_invariants_and_terminated
    val_m val_w
    (deferredAcceptanceState val_m val_w)
    hstable hstate hterm

/-- Alias with the existing full DA certificate term. -/
theorem deferredAcceptance_stable_of_certificate'
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaProducesStableMatchingCertificate val_m val_w) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) :=
  da_produces_stable_matching_of_certificate val_m val_w hcert

end Matching
end EconCSLib
