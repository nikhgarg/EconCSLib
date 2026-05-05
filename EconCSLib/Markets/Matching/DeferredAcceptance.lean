import EconCSLib.Markets.Matching.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

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

/-- Remove the proposal opportunity `m -> w` from a DA state's proposal sets. -/
def removeProposal (s : DAState M W) (m : M) (w : W) : M → Finset W :=
  fun m' => if m' = m then s.m_proposals m \ {w} else s.m_proposals m'

@[simp] lemma removeProposal_self (s : DAState M W) (m : M) (w : W) :
    removeProposal s m w m = s.m_proposals m \ {w} := by
  simp [removeProposal]

@[simp] lemma removeProposal_of_ne (s : DAState M W) {m m' : M} (w : W)
    (h : m' ≠ m) :
    removeProposal s m w m' = s.m_proposals m' := by
  simp [removeProposal, h]

lemma mem_removeProposal_iff (s : DAState M W) (m m' : M) (w w' : W) :
    w' ∈ removeProposal s m w m' ↔ w' ∈ s.m_proposals m' ∧ (m' = m → w' ≠ w) := by
  by_cases hm : m' = m
  · subst m'
    simp
  · simp [removeProposal, hm]

lemma not_mem_of_not_mem_removeProposal (s : DAState M W) {m m' : M} {w w' : W}
    (hnot : w' ∉ removeProposal s m w m') :
    w' ∉ s.m_proposals m' ∨ (m' = m ∧ w' = w) := by
  by_cases hm : m' = m
  · subst m'
    simp [removeProposal] at hnot
    by_cases hmem : w' ∈ s.m_proposals m
    · exact Or.inr ⟨rfl, hnot hmem⟩
    · exact Or.inl hmem
  · left
    simpa [removeProposal, hm] using hnot

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
    let new_proposals := removeProposal s m w
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

/-- The proposer selected by `daStep` from an active state. -/
noncomputable def daStepChosenMan (val_m : M → W → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m) : M :=
  Classical.choose hactive

/-- The woman selected by `daStep` for the chosen active proposer. -/
noncomputable def daStepChosenWoman (val_m : M → W → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m) : W :=
  let m := daStepChosenMan val_m s hactive
  let hact : IsActiveMan val_m s m := Classical.choose_spec hactive
  Classical.choose (exists_best_woman val_m s m hact)

/-- The accept predicate used by `daStep` after the chosen proposal is selected. -/
def daStepChosenAccepts (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hactive : ∃ m, IsActiveMan val_m s m) : Prop :=
  let m := daStepChosenMan val_m s hactive
  let w := daStepChosenWoman val_m s hactive
  match s.w_match w with
  | none => 0 ≤ val_w w m
  | some m' => val_w w m' < val_w w m

/--
If two woman-side profiles make the same accept/reject decision for the chosen
proposal in a fixed active state, then the DA step is the same under both
profiles.
-/
theorem daStep_eq_of_chosen_accepts_iff
    (val_m : M → W → ℝ) (val_w₁ val_w₂ : W → M → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m)
    (hiff :
      daStepChosenAccepts val_m val_w₁ s hactive ↔
        daStepChosenAccepts val_m val_w₂ s hactive) :
    daStep val_m val_w₁ s = daStep val_m val_w₂ s := by
  classical
  let m := Classical.choose hactive
  let hact : IsActiveMan val_m s m := Classical.choose_spec hactive
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts₁ : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w₁ w m
    | some m' => val_w₁ w m' < val_w₁ w m
  let accepts₂ : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w₂ w m
    | some m' => val_w₂ w m' < val_w₂ w m
  have hiff' : accepts₁ ↔ accepts₂ := by
    simpa [daStepChosenAccepts, daStepChosenMan, daStepChosenWoman, m, hact,
      w_exists, w, accepts₁, accepts₂] using hiff
  by_cases hacc₁ : accepts₁
  · have hacc₂ : accepts₂ := hiff'.1 hacc₁
    simp [daStep, hactive, m, w, accepts₁, accepts₂,
      hacc₁, hacc₂]
  · have hacc₂ : ¬ accepts₂ := fun h => hacc₁ (hiff'.2 h)
    simp [daStep, hactive, m, w, accepts₁, accepts₂,
      hacc₁, hacc₂]

set_option linter.unusedSimpArgs false

/-- If `daStep` accepts the chosen proposal, the chosen woman holds the proposer. -/
theorem daStep_w_match_chosen_of_accepts
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m)
    (hacc : daStepChosenAccepts val_m val_w s hactive) :
    (daStep val_m val_w s).w_match (daStepChosenWoman val_m s hactive) =
      some (daStepChosenMan val_m s hactive) := by
  classical
  let m := Classical.choose hactive
  let hact : IsActiveMan val_m s m := Classical.choose_spec hactive
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  have hacc' : accepts := by
    simpa [daStepChosenAccepts, daStepChosenMan, daStepChosenWoman, m, hact,
      w_exists, w, accepts] using hacc
  simpa [daStepChosenMan, daStepChosenWoman, m, hact, w_exists, w] using
    (by
      simp [daStep, hactive, m, hact, w_exists, w, accepts, hacc'])

set_option linter.unusedSimpArgs true

-- DA algorithm fold
noncomputable def deferredAcceptanceState (val_m : M → W → ℝ) (val_w : W → M → ℝ) : DAState M W :=
  let max_steps := Fintype.card M * Fintype.card W
  (List.range max_steps).foldl (fun s _ => daStep val_m val_w s) (initialDAState M W)

/--
The DA state after exactly `steps` iterations of the folded implementation.
This exposes the run prefix used by trace arguments while staying definitionally
aligned with `deferredAcceptanceState` at the fixed finite horizon.
-/
noncomputable def daStateAfterSteps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (steps : ℕ) : DAState M W :=
  (List.range steps).foldl (fun s _ => daStep val_m val_w s) (initialDAState M W)

@[simp] theorem daStateAfterSteps_zero
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    daStateAfterSteps val_m val_w 0 = initialDAState M W := by
  simp [daStateAfterSteps]

@[simp] theorem daStateAfterSteps_succ
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (steps : ℕ) :
    daStateAfterSteps val_m val_w (steps + 1) =
      daStep val_m val_w (daStateAfterSteps val_m val_w steps) := by
  unfold daStateAfterSteps
  rw [List.range_succ, List.foldl_append]
  simp

theorem deferredAcceptanceState_eq_daStateAfterSteps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    deferredAcceptanceState val_m val_w =
      daStateAfterSteps val_m val_w (Fintype.card M * Fintype.card W) := by
  rfl

noncomputable def deferredAcceptance (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W where
  m_match := (deferredAcceptanceState val_m val_w).m_match
  w_match := (deferredAcceptanceState val_m val_w).w_match
  consistent_m := (deferredAcceptanceState val_m val_w).consistent

/-! ### Local Invariants -/

/-- Number of proposal opportunities that have not yet been used. -/
def remainingProposalCount (s : DAState M W) : ℕ :=
  ∑ m : M, (s.m_proposals m).card

/-- Initially, every man can still propose to every woman. -/
lemma remainingProposalCount_initial :
    remainingProposalCount (initialDAState M W) = Fintype.card M * Fintype.card W := by
  simp [remainingProposalCount, initialDAState, Finset.sum_const]

/-- Any active state has at least one remaining proposal opportunity. -/
lemma remainingProposalCount_pos_of_active
    (val_m : M → W → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m) :
    0 < remainingProposalCount s := by
  rcases hactive with ⟨m, _hm_unmatched, w, hw_mem, _hw_nonneg⟩
  have hcard_pos : 0 < (s.m_proposals m).card :=
    Finset.card_pos.mpr ⟨w, hw_mem⟩
  have hle : (s.m_proposals m).card ≤ remainingProposalCount s := by
    unfold remainingProposalCount
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset M))
      (f := fun m => (s.m_proposals m).card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  exact lt_of_lt_of_le hcard_pos hle

/-- Removing an available proposal lowers the remaining proposal count by one. -/
lemma remainingProposalCount_removeProposal_add_one
    (s : DAState M W) {m : M} {w : W}
    (hw : w ∈ s.m_proposals m) :
    (∑ m' : M, ((removeProposal s m w) m').card) + 1 =
      remainingProposalCount s := by
  classical
  let oldCount : M → ℕ := fun m' => (s.m_proposals m').card
  let newCount : M → ℕ := fun m' => ((removeProposal s m w) m').card
  have hnew_at_m : newCount m + 1 = oldCount m := by
    simpa [newCount, oldCount, removeProposal, Finset.sdiff_singleton_eq_erase] using
      (Finset.card_erase_add_one (s := s.m_proposals m) (a := w) hw)
  have hnew_off :
      (∑ x ∈ (Finset.univ : Finset M).erase m, newCount x) =
        ∑ x ∈ (Finset.univ : Finset M).erase m, oldCount x := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hx_ne : x ≠ m := (Finset.mem_erase.mp hx).1
    simp [newCount, oldCount, removeProposal, hx_ne]
  have hnew_sum := Finset.sum_erase_add
    (s := (Finset.univ : Finset M)) (f := newCount) (a := m) (Finset.mem_univ m)
  have hold_sum := Finset.sum_erase_add
    (s := (Finset.univ : Finset M)) (f := oldCount) (a := m) (Finset.mem_univ m)
  have hnew_total : (∑ m' : M, newCount m') + 1 = ∑ m' : M, oldCount m' := by
    rw [← hnew_sum, ← hold_sum, hnew_off]
    linarith
  simpa [remainingProposalCount, oldCount, newCount] using hnew_total

/-- If no man is active, a DA step leaves the state unchanged. -/
lemma daStep_eq_self_of_not_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hnot : ¬ ∃ m, IsActiveMan val_m s m) :
    daStep val_m val_w s = s := by
  simp [daStep, hnot]

theorem daStateAfterSteps_eq_self_add_of_not_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (steps extra : ℕ)
    (hnot : ¬ ∃ m, IsActiveMan val_m (daStateAfterSteps val_m val_w steps) m) :
    daStateAfterSteps val_m val_w (steps + extra) =
      daStateAfterSteps val_m val_w steps := by
  induction extra with
  | zero =>
      simp
  | succ extra ih =>
      rw [Nat.add_succ, daStateAfterSteps_succ, ih,
        daStep_eq_self_of_not_active val_m val_w
          (daStateAfterSteps val_m val_w steps) hnot]

theorem deferredAcceptanceState_eq_daStateAfterSteps_of_not_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (steps : ℕ)
    (hle : steps ≤ Fintype.card M * Fintype.card W)
    (hnot : ¬ ∃ m, IsActiveMan val_m (daStateAfterSteps val_m val_w steps) m) :
    deferredAcceptanceState val_m val_w =
      daStateAfterSteps val_m val_w steps := by
  have hadd :
      steps + (Fintype.card M * Fintype.card W - steps) =
        Fintype.card M * Fintype.card W := Nat.add_sub_of_le hle
  rw [deferredAcceptanceState_eq_daStateAfterSteps, ← hadd]
  exact daStateAfterSteps_eq_self_add_of_not_active val_m val_w steps
    (Fintype.card M * Fintype.card W - steps) hnot

/-- A finite Boolean trace has a final true time immediately before false. -/
lemma exists_last_true_before_false_nat
    {P : ℕ → Prop} {N : ℕ} (h0 : P 0) (hN : ¬ P N) :
    ∃ t, t < N ∧ P t ∧ ¬ P (t + 1) := by
  classical
  let Q : ℕ → Prop := fun n => ¬ P n
  have hQ : ∃ n, Q n := ⟨N, hN⟩
  let n := Nat.find hQ
  have hnQ : Q n := Nat.find_spec hQ
  have hnpos : 0 < n := by
    by_contra hnot
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnot
    have hnQ0 : ¬ P 0 := by
      simpa [Q, hn0] using hnQ
    exact hnQ0 h0
  refine ⟨n - 1, ?_, ?_, ?_⟩
  · have hnleN : n ≤ N := Nat.find_min' hQ hN
    exact lt_of_lt_of_le (Nat.sub_one_lt hnpos.ne') hnleN
  · by_contra hnotP
    have hnle : n ≤ n - 1 := Nat.find_min' hQ hnotP
    exact (not_lt_of_ge hnle) (Nat.sub_one_lt hnpos.ne')
  · have hs : n - 1 + 1 = n :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)
    simpa [Q, hs] using hnQ

/-- A DA step can only remove proposal opportunities; it never adds one. -/
theorem m_proposals_daStep_subset
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (m0 : M) :
    (daStep val_m val_w s).m_proposals m0 ⊆ s.m_proposals m0 := by
  classical
  intro w0 hw0
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · unfold daStep at hw0
    rw [dif_pos hactive] at hw0
    let m := Classical.choose hactive
    have hact : IsActiveMan val_m s m := by
      simpa [m] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    by_cases hacc : accepts
    · have hmemRemove : w0 ∈ removeProposal s m w m0 := by
        simpa [m, hact, w_exists, w, accepts, hacc] using hw0
      exact ((mem_removeProposal_iff s m m0 w w0).1 hmemRemove).1
    · have hmemRemove : w0 ∈ removeProposal s m w m0 := by
        simpa [m, hact, w_exists, w, accepts, hacc] using hw0
      exact ((mem_removeProposal_iff s m m0 w w0).1 hmemRemove).1
  · simpa [daStep, hactive] using hw0

/-- Proposal opportunities are monotone decreasing along DA run prefixes. -/
theorem m_proposals_daStateAfterSteps_subset_add
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps extra : ℕ) (m : M) :
    (daStateAfterSteps val_m val_w (steps + extra)).m_proposals m ⊆
      (daStateAfterSteps val_m val_w steps).m_proposals m := by
  induction extra with
  | zero =>
      intro w hw
      simpa using hw
  | succ extra ih =>
      intro w hw
      have hstep :
          w ∈ (daStateAfterSteps val_m val_w (steps + extra)).m_proposals m := by
        exact m_proposals_daStep_subset val_m val_w
          (daStateAfterSteps val_m val_w (steps + extra)) m
          (by
            simpa only [Nat.add_succ, daStateAfterSteps_succ] using hw)
      exact ih hstep

/-- Later DA run prefixes have proposal sets contained in earlier prefixes. -/
theorem m_proposals_daStateAfterSteps_subset_of_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps later : ℕ} (hle : steps ≤ later) (m : M) :
    (daStateAfterSteps val_m val_w later).m_proposals m ⊆
      (daStateAfterSteps val_m val_w steps).m_proposals m := by
  have hadd : steps + (later - steps) = later := Nat.add_sub_of_le hle
  simpa [hadd] using
    m_proposals_daStateAfterSteps_subset_add val_m val_w steps (later - steps) m

/-- If a proposal opportunity is gone at a prefix, it remains gone at later prefixes. -/
theorem not_mem_daStateAfterSteps_of_not_mem_of_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps later : ℕ} (hle : steps ≤ later) {m : M} {w : W}
    (hnot : w ∉ (daStateAfterSteps val_m val_w steps).m_proposals m) :
    w ∉ (daStateAfterSteps val_m val_w later).m_proposals m := by
  intro hmem
  exact hnot
    (m_proposals_daStateAfterSteps_subset_of_le val_m val_w hle m hmem)

/-- The final DA state has no more proposal opportunities than any earlier prefix. -/
theorem m_proposals_deferredAcceptanceState_subset_after_steps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ) (hle : steps ≤ Fintype.card M * Fintype.card W) (m : M) :
    (deferredAcceptanceState val_m val_w).m_proposals m ⊆
      (daStateAfterSteps val_m val_w steps).m_proposals m := by
  have hsubset :=
    m_proposals_daStateAfterSteps_subset_of_le val_m val_w hle m
  simpa [deferredAcceptanceState_eq_daStateAfterSteps] using hsubset

/-- If a proposal opportunity is gone at a prefix, it is gone in the final DA state. -/
theorem not_mem_deferredAcceptanceState_of_not_mem_after_steps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ) (hle : steps ≤ Fintype.card M * Fintype.card W)
    {m : M} {w : W}
    (hnot : w ∉ (daStateAfterSteps val_m val_w steps).m_proposals m) :
    w ∉ (deferredAcceptanceState val_m val_w).m_proposals m := by
  intro hmem
  exact hnot
    (m_proposals_deferredAcceptanceState_subset_after_steps val_m val_w
      steps hle m hmem)

/--
If a specific proposal opportunity disappears in one DA step, then that man was
the active proposer and that woman was his best remaining acceptable option.
-/
theorem proposal_removed_at_daStep
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    {m : M} {w : W}
    (hmem : w ∈ s.m_proposals m)
    (hnot : w ∉ (daStep val_m val_w s).m_proposals m) :
    IsActiveMan val_m s m ∧ BestRemainingWoman val_m s m w := by
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · unfold daStep at hnot
    rw [dif_pos hactive] at hnot
    let m0 := Classical.choose hactive
    have hact : IsActiveMan val_m s m0 := by
      simpa [m0] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m0 hact
    let w0 := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s m0 w0 := by
      simpa [w0, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w0 with
      | none => 0 ≤ val_w w0 m0
      | some m' => val_w w0 m' < val_w w0 m0
    by_cases hacc : accepts
    · have hnotRemove : w ∉ removeProposal s m0 w0 m := by
        simpa [m0, hact, w_exists, w0, accepts, hacc] using hnot
      rcases not_mem_of_not_mem_removeProposal s hnotRemove with hnotOld | ⟨hm, hw⟩
      · exact False.elim (hnotOld hmem)
      · subst m
        subst w
        exact ⟨hact, hwbest⟩
    · have hnotRemove : w ∉ removeProposal s m0 w0 m := by
        simpa [m0, hact, w_exists, w0, accepts, hacc] using hnot
      rcases not_mem_of_not_mem_removeProposal s hnotRemove with hnotOld | ⟨hm, hw⟩
      · exact False.elim (hnotOld hmem)
      · subst m
        subst w
        exact ⟨hact, hwbest⟩
  · have hsame : daStep val_m val_w s = s :=
      daStep_eq_self_of_not_active val_m val_w s hactive
    exact False.elim (hnot (by simpa [hsame] using hmem))

/-- Run-prefix version of `proposal_removed_at_daStep`. -/
theorem proposal_removed_at_daStateAfterSteps_succ
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ) {m : M} {w : W}
    (hmem : w ∈ (daStateAfterSteps val_m val_w steps).m_proposals m)
    (hnot :
      w ∉ (daStateAfterSteps val_m val_w (steps + 1)).m_proposals m) :
    IsActiveMan val_m (daStateAfterSteps val_m val_w steps) m ∧
      BestRemainingWoman val_m (daStateAfterSteps val_m val_w steps) m w := by
  exact proposal_removed_at_daStep val_m val_w
    (daStateAfterSteps val_m val_w steps) hmem
    (by simpa [daStateAfterSteps_succ] using hnot)

/--
Once `m` has already used the proposal opportunity to `w` and is not currently
matched to `w`, one DA step cannot rematch `m` to `w`.
-/
theorem m_match_ne_of_not_mem_proposal_daStep
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    {m : M} {w : W}
    (hnot : w ∉ s.m_proposals m)
    (hne : s.m_match m ≠ some w) :
    (daStep val_m val_w s).m_match m ≠ some w := by
  classical
  intro hafter
  by_cases hactive : ∃ a, IsActiveMan val_m s a
  · unfold daStep at hafter
    rw [dif_pos hactive] at hafter
    let a := Classical.choose hactive
    have hact : IsActiveMan val_m s a := by
      simpa [a] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s a hact
    let w0 := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s a w0 := by
      simpa [w0, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w0 with
      | none => 0 ≤ val_w w0 a
      | some m' => val_w w0 m' < val_w w0 a
    by_cases hacc : accepts
    · by_cases hm : m = a
      · have hw_eq : w0 = w := by
          exact Option.some.inj
            (by simpa [a, w0, accepts, hacc, hm] using hafter)
        have hmem : w ∈ s.m_proposals m := by
          rw [hm]
          simpa [hw_eq] using hwbest.1
        exact hnot hmem
      · by_cases hcur : s.w_match w0 = some m
        · have hpref : val_w w0 m < val_w w0 a := by
            simpa [accepts, hcur] using hacc
          have hnone : (none : Option W) = some w := by
            simpa [a, w0, hcur, hpref, hm] using hafter
          cases hnone
        · have hold : s.m_match m = some w := by
            simpa [a, w0, accepts, hacc, hm, hcur] using hafter
          exact hne hold
    · have hold : s.m_match m = some w := by
        simpa [a, w0, accepts, hacc] using hafter
      exact hne hold
  · have hsame : daStep val_m val_w s = s :=
      daStep_eq_self_of_not_active val_m val_w s hactive
    exact hne (by simpa [hsame] using hafter)

/--
If a proposal opportunity is gone at a prefix and the man is not then holding
that woman, no later prefix can match them.
-/
theorem m_match_ne_daStateAfterSteps_of_not_mem_of_ne_of_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps later : ℕ} (hle : steps ≤ later) {m : M} {w : W}
    (hnot : w ∉ (daStateAfterSteps val_m val_w steps).m_proposals m)
    (hne : (daStateAfterSteps val_m val_w steps).m_match m ≠ some w) :
    (daStateAfterSteps val_m val_w later).m_match m ≠ some w := by
  have hadd : steps + (later - steps) = later := Nat.add_sub_of_le hle
  suffices
      (daStateAfterSteps val_m val_w (steps + (later - steps))).m_match m ≠
        some w by
    simpa [hadd] using this
  induction later - steps with
  | zero =>
      simpa using hne
  | succ extra ih =>
      have hnotCur :
          w ∉ (daStateAfterSteps val_m val_w (steps + extra)).m_proposals m := by
        exact not_mem_daStateAfterSteps_of_not_mem_of_le val_m val_w
          (Nat.le_add_right steps extra) hnot
      have hnext :=
        m_match_ne_of_not_mem_proposal_daStep val_m val_w
          (daStateAfterSteps val_m val_w (steps + extra)) hnotCur ih
      have hs :
          daStateAfterSteps val_m val_w (steps + (extra + 1)) =
            daStep val_m val_w
              (daStateAfterSteps val_m val_w (steps + extra)) := by
        rw [← Nat.add_assoc, daStateAfterSteps_succ]
      simpa [hs] using hnext

/--
Final-state version: a spent proposal cannot become a later match unless the
man was already holding that woman at the prefix.
-/
theorem m_match_ne_deferredAcceptanceState_of_not_mem_after_steps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps : ℕ} (hle : steps ≤ Fintype.card M * Fintype.card W)
    {m : M} {w : W}
    (hnot : w ∉ (daStateAfterSteps val_m val_w steps).m_proposals m)
    (hne : (daStateAfterSteps val_m val_w steps).m_match m ≠ some w) :
    (deferredAcceptanceState val_m val_w).m_match m ≠ some w := by
  simpa [deferredAcceptanceState_eq_daStateAfterSteps] using
    m_match_ne_daStateAfterSteps_of_not_mem_of_ne_of_le
      val_m val_w hle hnot hne

/--
If a proposal opportunity is already gone by a DA prefix, then an earlier
concrete step removed it.
-/
theorem exists_proposal_removal_step_before_of_not_mem_daStateAfterSteps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps : ℕ} {m : M} {w : W}
    (hnot : w ∉ (daStateAfterSteps val_m val_w steps).m_proposals m) :
    ∃ t, t < steps ∧
      w ∈ (daStateAfterSteps val_m val_w t).m_proposals m ∧
      w ∉ (daStateAfterSteps val_m val_w (t + 1)).m_proposals m := by
  let P : ℕ → Prop := fun t =>
    w ∈ (daStateAfterSteps val_m val_w t).m_proposals m
  have h0 : P 0 := by
    simp [P, initialDAState]
  have hN : ¬ P steps := by
    simpa [P] using hnot
  simpa [P] using exists_last_true_before_false_nat (P := P) h0 hN

set_option linter.unusedSimpArgs false

/-- A woman's held-match value weakly increases after one DA step. -/
theorem woman_match_value_daStep_mono
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (w0 : W) :
    valW val_w w0 (s.w_match w0) ≤
      valW val_w w0 ((daStep val_m val_w s).w_match w0) := by
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · let m := Classical.choose hactive
    have hact : IsActiveMan val_m s m := by
      simpa [m] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    by_cases hacc : accepts
    · by_cases hw0 : w0 = w
      · subst w0
        have hafter : (daStep val_m val_w s).w_match w = some m := by
          simp [daStep, hactive, m, hact, w_exists, w, accepts, hacc]
        cases hcur : s.w_match w with
        | none =>
            have hnonneg : 0 ≤ val_w w m := by
              simpa [accepts, hcur] using hacc
            simpa [valW, hcur, hafter] using hnonneg
        | some mcur =>
            have hpref : val_w w mcur < val_w w m := by
              simpa [accepts, hcur] using hacc
            have hle : val_w w mcur ≤ val_w w m := le_of_lt hpref
            simpa [valW, hcur, hafter] using hle
      · have hafter : (daStep val_m val_w s).w_match w0 = s.w_match w0 := by
          simp [daStep, hactive, m, hact, w_exists, w, accepts, hacc,
            Function.update, hw0]
        simp [hafter]
    · have hafter : (daStep val_m val_w s).w_match w0 = s.w_match w0 := by
        simp [daStep, hactive, m, hact, w_exists, w, accepts, hacc]
      simp [hafter]
  · simp [daStep, hactive]

/-- A woman's held-match value is monotone along DA run prefixes. -/
theorem woman_match_value_daStateAfterSteps_mono_add
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps extra : ℕ) (w : W) :
    valW val_w w ((daStateAfterSteps val_m val_w steps).w_match w) ≤
      valW val_w w
        ((daStateAfterSteps val_m val_w (steps + extra)).w_match w) := by
  induction extra with
  | zero =>
      simp
  | succ extra ih =>
      have hstep :=
        woman_match_value_daStep_mono val_m val_w
          (daStateAfterSteps val_m val_w (steps + extra)) w
      have hstep' :
          valW val_w w
              ((daStateAfterSteps val_m val_w (steps + extra)).w_match w) ≤
            valW val_w w
              ((daStateAfterSteps val_m val_w (steps + (extra + 1))).w_match w) := by
        rw [← Nat.add_assoc, daStateAfterSteps_succ]
        exact hstep
      exact le_trans ih hstep'

/-- Later DA run prefixes give every woman a weakly better held match. -/
theorem woman_match_value_daStateAfterSteps_mono_of_le
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps later : ℕ} (hle : steps ≤ later) (w : W) :
    valW val_w w ((daStateAfterSteps val_m val_w steps).w_match w) ≤
      valW val_w w ((daStateAfterSteps val_m val_w later).w_match w) := by
  have hadd : steps + (later - steps) = later := Nat.add_sub_of_le hle
  simpa [hadd] using
    woman_match_value_daStateAfterSteps_mono_add val_m val_w steps (later - steps) w

/-- The final DA state gives every woman a weakly better held match than any prefix. -/
theorem woman_match_value_deferredAcceptanceState_mono_after_steps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ) (hle : steps ≤ Fintype.card M * Fintype.card W) (w : W) :
    valW val_w w ((daStateAfterSteps val_m val_w steps).w_match w) ≤
      valW val_w w ((deferredAcceptanceState val_m val_w).w_match w) := by
  have hmono :=
    woman_match_value_daStateAfterSteps_mono_of_le val_m val_w hle w
  simpa [deferredAcceptanceState_eq_daStateAfterSteps] using hmono

/--
If a proposal opportunity disappears in a DA step, then after that step the
woman holds someone she weakly prefers to the proposer.
-/
theorem woman_value_ge_of_proposal_removed_at_daStep
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    {m : M} {w : W}
    (hmem : w ∈ s.m_proposals m)
    (hnot : w ∉ (daStep val_m val_w s).m_proposals m) :
    val_w w m ≤ valW val_w w ((daStep val_m val_w s).w_match w) := by
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · let m0 := Classical.choose hactive
    have hact : IsActiveMan val_m s m0 := by
      simpa [m0] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m0 hact
    let w0 := Classical.choose w_exists
    let accepts : Prop :=
      match s.w_match w0 with
      | none => 0 ≤ val_w w0 m0
      | some m' => val_w w0 m' < val_w w0 m0
    by_cases hacc : accepts
    · have hnotRemove : w ∉ removeProposal s m0 w0 m := by
        simpa [daStep, hactive, m0, hact, w_exists, w0, accepts, hacc] using hnot
      rcases not_mem_of_not_mem_removeProposal s hnotRemove with hnotOld | ⟨hm, hw⟩
      · exact False.elim (hnotOld hmem)
      · subst m
        subst w
        have hafter : (daStep val_m val_w s).w_match w0 = some m0 := by
          simp [daStep, hactive, m0, hact, w_exists, w0, accepts, hacc]
        simp [valW, hafter]
    · have hnotRemove : w ∉ removeProposal s m0 w0 m := by
        simpa [daStep, hactive, m0, hact, w_exists, w0, accepts, hacc] using hnot
      rcases not_mem_of_not_mem_removeProposal s hnotRemove with hnotOld | ⟨hm, hw⟩
      · exact False.elim (hnotOld hmem)
      · subst m
        subst w
        have hafter : (daStep val_m val_w s).w_match w0 = s.w_match w0 := by
          simp [daStep, hactive, m0, hact, w_exists, w0, accepts, hacc]
        cases hcur : s.w_match w0 with
        | none =>
            have hle : val_w w0 m0 ≤ 0 := by
              have hnotNonneg : ¬ 0 ≤ val_w w0 m0 := by
                simpa [accepts, hcur] using hacc
              exact le_of_not_ge hnotNonneg
            simpa [valW, hcur, hafter] using hle
        | some mcur =>
            have hle : val_w w0 m0 ≤ val_w w0 mcur := by
              have hnotlt : ¬ val_w w0 mcur < val_w w0 m0 := by
                simpa [accepts, hcur] using hacc
              exact le_of_not_gt hnotlt
            simpa [valW, hcur, hafter] using hle
  · have hsame : daStep val_m val_w s = s :=
      daStep_eq_self_of_not_active val_m val_w s hactive
    exact False.elim (hnot (by simpa [hsame] using hmem))

set_option linter.unusedSimpArgs true

/--
Run-prefix/final-state version: after a removed proposal, the final woman-side
match is weakly preferred by that woman to the proposer.
-/
theorem woman_final_value_ge_of_proposal_removed_at_daStateAfterSteps
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps : ℕ} {m : M} {w : W}
    (hsteps : steps < Fintype.card M * Fintype.card W)
    (hmem : w ∈ (daStateAfterSteps val_m val_w steps).m_proposals m)
    (hnot :
      w ∉ (daStateAfterSteps val_m val_w (steps + 1)).m_proposals m) :
    val_w w m ≤ valW val_w w ((deferredAcceptanceState val_m val_w).w_match w) := by
  have hstep :
      val_w w m ≤
        valW val_w w
          ((daStateAfterSteps val_m val_w (steps + 1)).w_match w) :=
    by
      have hraw :=
        woman_value_ge_of_proposal_removed_at_daStep val_m val_w
          (daStateAfterSteps val_m val_w steps) hmem
          (by simpa [daStateAfterSteps_succ] using hnot)
      simpa [daStateAfterSteps_succ] using hraw
  have hle : steps + 1 ≤ Fintype.card M * Fintype.card W :=
    Nat.succ_le_of_lt hsteps
  have hmono :=
    woman_match_value_deferredAcceptanceState_mono_after_steps
      val_m val_w (steps + 1) hle w
  exact le_trans hstep hmono

/--
If one DA step takes woman `w0` from weakly below a threshold man `r` to strictly
above him, the active proposer at that step proposed to `w0` and is strictly
preferred by `w0` to `r`.
-/
theorem woman_threshold_crossed_at_daStep
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (w0 : W) (r : M)
    (hbefore : valW val_w w0 (s.w_match w0) ≤ val_w w0 r)
    (hafter : val_w w0 r <
      valW val_w w0 ((daStep val_m val_w s).w_match w0)) :
    ∃ a,
      IsActiveMan val_m s a ∧
        BestRemainingWoman val_m s a w0 ∧
        (daStep val_m val_w s).w_match w0 = some a ∧
        val_w w0 r < val_w w0 a := by
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · let a := Classical.choose hactive
    have hact : IsActiveMan val_m s a := by
      simpa [a] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s a hact
    let w := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s a w := by
      simpa [w, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w a
      | some m' => val_w w m' < val_w w a
    by_cases hacc : accepts
    · by_cases hw0 : w0 = w
      · subst w0
        have hafterMatch : (daStep val_m val_w s).w_match w = some a := by
          simp [daStep, hactive, a, w, accepts, hacc]
        refine ⟨a, hact, hwbest, hafterMatch, ?_⟩
        simpa [valW, hafterMatch] using hafter
      · have hsame :
          (daStep val_m val_w s).w_match w0 = s.w_match w0 := by
          simp [daStep, hactive, a, w, accepts, hacc,
            Function.update, hw0]
        have hlt : val_w w0 r < valW val_w w0 (s.w_match w0) := by
          simpa [hsame] using hafter
        exact False.elim ((not_lt_of_ge hbefore) hlt)
    · have hsame :
          (daStep val_m val_w s).w_match w0 = s.w_match w0 := by
        simp [daStep, hactive, a, w, accepts, hacc]
      have hlt : val_w w0 r < valW val_w w0 (s.w_match w0) := by
        simpa [hsame] using hafter
      exact False.elim ((not_lt_of_ge hbefore) hlt)
  · have hsame : daStep val_m val_w s = s :=
      daStep_eq_self_of_not_active val_m val_w s hactive
    have hlt : val_w w0 r < valW val_w w0 (s.w_match w0) := by
      simpa [hsame] using hafter
    exact False.elim ((not_lt_of_ge hbefore) hlt)

/-- Run-prefix version of `woman_threshold_crossed_at_daStep`. -/
theorem woman_threshold_crossed_at_daStateAfterSteps_succ
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ) (w : W) (r : M)
    (hbefore :
      valW val_w w ((daStateAfterSteps val_m val_w steps).w_match w) ≤
        val_w w r)
    (hafter :
      val_w w r <
        valW val_w w
          ((daStateAfterSteps val_m val_w (steps + 1)).w_match w)) :
    ∃ a,
      IsActiveMan val_m (daStateAfterSteps val_m val_w steps) a ∧
        BestRemainingWoman val_m
          (daStateAfterSteps val_m val_w steps) a w ∧
        (daStateAfterSteps val_m val_w (steps + 1)).w_match w = some a ∧
        val_w w r < val_w w a := by
  rcases woman_threshold_crossed_at_daStep val_m val_w
      (daStateAfterSteps val_m val_w steps) w r hbefore
      (by simpa [daStateAfterSteps_succ] using hafter) with
    ⟨a, hact, hbest, hmatch, hpref⟩
  exact ⟨a, hact, hbest, by simpa [daStateAfterSteps_succ] using hmatch, hpref⟩

/--
If a woman's prefix trace eventually crosses a strict threshold, then there is
a first crossing step.
-/
theorem exists_woman_threshold_crossing_step_before
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {steps : ℕ} {w : W} {r : M}
    (hstart :
      ¬ val_w w r <
        valW val_w w ((daStateAfterSteps val_m val_w 0).w_match w))
    (hend :
      val_w w r <
        valW val_w w ((daStateAfterSteps val_m val_w steps).w_match w)) :
    ∃ t, t < steps ∧
      ¬ val_w w r <
        valW val_w w ((daStateAfterSteps val_m val_w t).w_match w) ∧
      val_w w r <
        valW val_w w ((daStateAfterSteps val_m val_w (t + 1)).w_match w) := by
  let P : ℕ → Prop := fun t =>
    ¬ val_w w r <
      valW val_w w ((daStateAfterSteps val_m val_w t).w_match w)
  have hN : ¬ P steps := by
    intro hnot
    exact hnot hend
  simpa [P] using exists_last_true_before_false_nat (P := P) hstart hN

/-- An active DA step consumes exactly one remaining proposal opportunity. -/
lemma remainingProposalCount_daStep_add_one_of_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hactive : ∃ m, IsActiveMan val_m s m) :
    remainingProposalCount (daStep val_m val_w s) + 1 =
      remainingProposalCount s := by
  classical
  unfold daStep
  rw [dif_pos hactive]
  let m := Classical.choose hactive
  have hact : IsActiveMan val_m s m := by
    simpa [m] using Classical.choose_spec hactive
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  have hwbest : BestRemainingWoman val_m s m w := by
    simpa [w, w_exists] using Classical.choose_spec w_exists
  have hremove := remainingProposalCount_removeProposal_add_one
    (s := s) (m := m) (w := w) hwbest.1
  let accepts : Prop :=
    match s.w_match w with
    | none => 0 ≤ val_w w m
    | some m' => val_w w m' < val_w w m
  by_cases hacc : accepts
  · simpa [m, hact, w_exists, w, accepts, hacc, remainingProposalCount] using hremove
  · simpa [m, hact, w_exists, w, accepts, hacc, remainingProposalCount] using hremove

/-- Once no man is active, any further list of DA steps leaves the state unchanged. -/
lemma foldl_daStep_eq_self_of_not_active
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : List ℕ) (s : DAState M W)
    (hnot : ¬ ∃ m, IsActiveMan val_m s m) :
    steps.foldl (fun s _ => daStep val_m val_w s) s = s := by
  induction steps generalizing s with
  | nil =>
      rfl
  | cons _ steps ih =>
      rw [List.foldl_cons, daStep_eq_self_of_not_active val_m val_w s hnot]
      exact ih s hnot

/--
If the number of remaining proposal opportunities is bounded by the number of
steps left, then after those steps no man is active.
-/
lemma no_active_after_steps_of_count_le_length
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : List ℕ) (s : DAState M W)
    (hcount : remainingProposalCount s ≤ steps.length) :
    ¬ ∃ m, IsActiveMan val_m
      (steps.foldl (fun s _ => daStep val_m val_w s) s) m := by
  induction steps generalizing s with
  | nil =>
      intro hactive
      have hpos := remainingProposalCount_pos_of_active val_m s hactive
      simp at hcount
      linarith
  | cons _ steps ih =>
      by_cases hactive : ∃ m, IsActiveMan val_m s m
      · have hstep_count :=
          remainingProposalCount_daStep_add_one_of_active val_m val_w s hactive
        have hcount_step : remainingProposalCount (daStep val_m val_w s) ≤ steps.length := by
          have hsucc :
              remainingProposalCount (daStep val_m val_w s) + 1 ≤ steps.length + 1 := by
            simpa [hstep_count] using hcount
          exact Nat.succ_le_succ_iff.mp hsucc
        simpa [List.foldl_cons] using ih (daStep val_m val_w s) hcount_step
      · rw [List.foldl_cons,
          daStep_eq_self_of_not_active val_m val_w s hactive]
        simpa [foldl_daStep_eq_self_of_not_active val_m val_w steps s hactive] using hactive

def ManIRInvariant (val_m : M → W → ℝ) (s : DAState M W) : Prop :=
  ∀ m w, s.m_match m = some w → 0 ≤ val_m m w

def WomanIRInvariant (val_w : W → M → ℝ) (s : DAState M W) : Prop :=
  ∀ w m, s.w_match w = some m → 0 ≤ val_w w m

def MatchedProposedInvariant (s : DAState M W) : Prop :=
  ∀ m w, s.m_match m = some w → w ∉ s.m_proposals m

def WomanRejectionInvariant (val_w : W → M → ℝ) (s : DAState M W) : Prop :=
  ∀ w m', w ∉ s.m_proposals m' →
    s.m_match m' ≠ some w →
    val_w w m' < 0 ∨ (∃ m, s.w_match w = some m ∧ val_w w m' ≤ val_w w m)

def ManProposalOrderInvariant (val_m : M → W → ℝ) (s : DAState M W) : Prop :=
  ∀ m w w', w ∉ s.m_proposals m → w' ∈ s.m_proposals m → 0 ≤ val_m m w' →
    val_m m w' ≤ val_m m w

def DAInvariants (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W) : Prop :=
  ManIRInvariant val_m s ∧
  WomanIRInvariant val_w s ∧
  MatchedProposedInvariant s ∧
  WomanRejectionInvariant val_w s ∧
  ManProposalOrderInvariant val_m s

/--
If an invariant DA state leaves a woman unmatched, then she has not rejected any
acceptable proposal: every man still has the opportunity to propose to her.
-/
lemma unmatched_woman_mem_proposals_of_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hwAcceptable : ∀ w m, 0 < val_w w m)
    (hinv : DAInvariants val_m val_w s)
    {w : W} (hwNone : s.w_match w = none) :
    ∀ m, w ∈ s.m_proposals m := by
  intro m
  by_contra hnot
  rcases hinv with ⟨_hmanIR, _hwomanIR, _hmatchedProposed, hwomanReject,
    _hproposalOrder⟩
  have hnotMatched : s.m_match m ≠ some w := by
    intro hmatch
    have hwMatch : s.w_match w = some m := (s.consistent m w).1 hmatch
    rw [hwNone] at hwMatch
    cases hwMatch
  rcases hwomanReject w m hnot hnotMatched with hneg | ⟨mcur, hwcur, _hle⟩
  · have hpos := hwAcceptable w m
    linarith
  · rw [hwNone] at hwcur
    cases hwcur

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

lemma manProposalOrder_removeProposal
    (val_m : M → W → ℝ) (s : DAState M W) {m : M} {w : W}
    (hwbest : BestRemainingWoman val_m s m w)
    (horder : ManProposalOrderInvariant val_m s) :
    ∀ m0 w0 w1, w0 ∉ removeProposal s m w m0 →
      w1 ∈ removeProposal s m w m0 → 0 ≤ val_m m0 w1 →
      val_m m0 w1 ≤ val_m m0 w0 := by
  intro m0 w0 w1 hnotNew hmemNew hnonneg
  have hmemOld : w1 ∈ s.m_proposals m0 :=
    ((mem_removeProposal_iff s m m0 w w1).1 hmemNew).1
  rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
  · exact horder m0 w0 w1 hnotOld hmemOld hnonneg
  · subst m0
    subst w0
    exact hwbest.2.2 w1 hmemOld hnonneg

lemma rejectStep_preserves_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) {m : M} {w : W}
    (hact : IsActiveMan val_m s m)
    (hwbest : BestRemainingWoman val_m s m w)
    (hreject :
      ¬ match s.w_match w with
        | none => 0 ≤ val_w w m
        | some m' => val_w w m' < val_w w m)
    (hinv : DAInvariants val_m val_w s) :
    DAInvariants val_m val_w { s with m_proposals := removeProposal s m w } := by
  rcases hinv with ⟨hmanIR, hwomanIR, hmatchedProposed, hwomanReject, hproposalOrder⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m0 w0 hmatch
    exact hmanIR m0 w0 hmatch
  · intro w0 m0 hmatch
    exact hwomanIR w0 m0 hmatch
  · intro m0 w0 hmatch
    by_cases hm0 : m0 = m
    · subst m0
      rw [hact.1] at hmatch
      cases hmatch
    · simpa [removeProposal, hm0] using hmatchedProposed m0 w0 hmatch
  · intro w0 m0 hnotNew hnotMatched
    rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
    · exact hwomanReject w0 m0 hnotOld hnotMatched
    · subst m0
      subst w0
      cases hcur : s.w_match w with
      | none =>
          left
          have hnotNonneg : ¬ 0 ≤ val_w w m := by
            simpa [hcur] using hreject
          exact lt_of_not_ge hnotNonneg
      | some mcur =>
          right
          refine ⟨mcur, rfl, ?_⟩
          have hnotPref : ¬ val_w w mcur < val_w w m := by
            simpa [hcur] using hreject
          exact le_of_not_gt hnotPref
  · exact manProposalOrder_removeProposal val_m s hwbest hproposalOrder

lemma acceptStep_preserves_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) {m : M} {w : W}
    (hact : IsActiveMan val_m s m)
    (hwbest : BestRemainingWoman val_m s m w)
    (haccept :
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m)
    (hinv : DAInvariants val_m val_w s) :
    DAInvariants val_m val_w
      { m_match := fun m'' =>
          if m'' = m then some w
          else if s.w_match w = some m'' then none
          else s.m_match m''
        w_match := Function.update s.w_match w (some m)
        m_proposals := removeProposal s m w
        consistent := by
          simpa using acceptMatch_consistent s hact.1 } := by
  rcases hinv with ⟨hmanIR, hwomanIR, hmatchedProposed, hwomanReject, hproposalOrder⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m0 w0 hmatch
    by_cases hm0 : m0 = m
    · subst m0
      simp at hmatch
      subst w0
      exact hwbest.2.1
    · by_cases hcur : s.w_match w = some m0
      · simp [hm0, hcur] at hmatch
      · have hold : s.m_match m0 = some w0 := by
          simpa [hm0, hcur] using hmatch
        exact hmanIR m0 w0 hold
  · intro w0 m0 hmatch
    by_cases hw0 : w0 = w
    · subst w0
      simp at hmatch
      subst m0
      cases hcur : s.w_match w with
      | none =>
          simpa [hcur] using haccept
      | some mcur =>
          have hcurIR : 0 ≤ val_w w mcur := hwomanIR w mcur hcur
          have hpref : val_w w mcur < val_w w m := by
            simpa [hcur] using haccept
          linarith
    · have hold : s.w_match w0 = some m0 := by
        simpa [Function.update, hw0] using hmatch
      exact hwomanIR w0 m0 hold
  · intro m0 w0 hmatch
    by_cases hm0 : m0 = m
    · subst m0
      simp at hmatch
      subst w0
      simp [removeProposal]
    · by_cases hcur : s.w_match w = some m0
      · simp [hm0, hcur] at hmatch
      · have hold : s.m_match m0 = some w0 := by
          simpa [hm0, hcur] using hmatch
        simpa [removeProposal, hm0] using hmatchedProposed m0 w0 hold
  · intro w0 m0 hnotNew hnotMatchedNew
    rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
    · by_cases holdMatch : s.m_match m0 = some w0
      · have hm0_ne_m : m0 ≠ m := by
          intro hm0
          subst m0
          rw [hact.1] at holdMatch
          cases holdMatch
        by_cases hcur : s.w_match w = some m0
        · have holdW : s.m_match m0 = some w := (s.consistent m0 w).2 hcur
          have hw0_eq : w0 = w := by
            exact Option.some.inj (holdMatch.symm.trans holdW)
          subst w0
          right
          refine ⟨m, by simp, ?_⟩
          have hpref : val_w w m0 < val_w w m := by
            simpa [hcur] using haccept
          exact le_of_lt hpref
        · exfalso
          exact hnotMatchedNew (by simpa [hm0_ne_m, hcur] using holdMatch)
      · rcases hwomanReject w0 m0 hnotOld holdMatch with hneg | ⟨mold, hwold, hleOld⟩
        · exact Or.inl hneg
        · by_cases hw0 : w0 = w
          · subst w0
            right
            refine ⟨m, by simp, ?_⟩
            have hpref : val_w w mold < val_w w m := by
              simpa [hwold] using haccept
            exact le_trans hleOld (le_of_lt hpref)
          · right
            refine ⟨mold, ?_, hleOld⟩
            simpa [Function.update, hw0] using hwold
    · subst m0
      subst w0
      exfalso
      exact hnotMatchedNew (by simp)
  · exact manProposalOrder_removeProposal val_m s hwbest hproposalOrder

theorem daStep_preserves_invariants_certificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAStepPreservesInvariantsCertificate val_m val_w := by
  intro s hinv
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · unfold daStep
    rw [dif_pos hactive]
    let m := Classical.choose hactive
    have hact : IsActiveMan val_m s m := by
      simpa [m] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s m w := by
      simpa [w, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    by_cases hacc : accepts
    · simpa [m, hact, w_exists, w, accepts, hacc] using
        acceptStep_preserves_invariants val_m val_w s hact hwbest hacc hinv
    · simpa [m, hact, w_exists, w, accepts, hacc] using
        rejectStep_preserves_invariants val_m val_w s hact hwbest hacc hinv
  · simpa [daStep, hactive] using hinv

/-- A list of DA steps preserves the invariants when each individual step does. -/
lemma foldl_daStep_preserves_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : List ℕ) (s : DAState M W)
    (hstep : DAStepPreservesInvariantsCertificate val_m val_w)
    (hinv : DAInvariants val_m val_w s) :
    DAInvariants val_m val_w
      (steps.foldl (fun s _ => daStep val_m val_w s) s) := by
  induction steps generalizing s with
  | nil =>
      simpa using hinv
  | cons _ steps ih =>
      simp [List.foldl_cons]
      exact ih (daStep val_m val_w s) (hstep s hinv)

def DAStateInvariantCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  DAInvariants val_m val_w (deferredAcceptanceState val_m val_w)

lemma deferredAcceptanceState_satisfies_invariants (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAStateInvariantCertificate val_m val_w →
    DAInvariants val_m val_w (deferredAcceptanceState val_m val_w) := by
  intro hcert
  exact hcert

/-- The deferred-acceptance final state satisfies the invariants if each step preserves them. -/
theorem deferredAcceptanceState_satisfies_invariants_of_step_certificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstep : DAStepPreservesInvariantsCertificate val_m val_w) :
    DAStateInvariantCertificate val_m val_w := by
  unfold DAStateInvariantCertificate deferredAcceptanceState
  exact foldl_daStep_preserves_invariants val_m val_w
    (List.range (Fintype.card M * Fintype.card W))
    (initialDAState M W) hstep
    (initialDAState_satisfies_invariants val_m val_w)

/-- Every finite DA run prefix satisfies the invariants when each step preserves them. -/
theorem daStateAfterSteps_satisfies_invariants_of_step_certificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ)
    (hstep : DAStepPreservesInvariantsCertificate val_m val_w) :
    DAInvariants val_m val_w (daStateAfterSteps val_m val_w steps) := by
  unfold daStateAfterSteps
  exact foldl_daStep_preserves_invariants val_m val_w
    (List.range steps)
    (initialDAState M W) hstep
    (initialDAState_satisfies_invariants val_m val_w)

theorem daStateAfterSteps_satisfies_invariants
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : ℕ) :
    DAInvariants val_m val_w (daStateAfterSteps val_m val_w steps) :=
  daStateAfterSteps_satisfies_invariants_of_step_certificate val_m val_w steps
    (daStep_preserves_invariants_certificate val_m val_w)

/--
If a state satisfies the invariants and no men are active (termination), 
then the matching is stable.
-/
lemma stable_of_invariants_and_terminated (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    (hinv : DAInvariants val_m val_w s)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m) :
    IsStable val_m val_w ⟨s.m_match, s.w_match, s.consistent⟩ := by
  rcases hinv with ⟨hmanIR, hwomanIR, hmatchedProposed, hwomanReject, hproposalOrder⟩
  refine ⟨?_, ?_, ?_⟩
  · intro m
    cases hmatch : s.m_match m with
    | none =>
        simp [valM, hmatch]
    | some w =>
        simpa [valM, hmatch] using hmanIR m w hmatch
  · intro w
    cases hmatch : s.w_match w with
    | none =>
        simp [valW, hmatch]
    | some m =>
        simpa [valW, hmatch] using hwomanIR w m hmatch
  · intro m w hm hw
    by_cases hremaining : w ∈ s.m_proposals m
    · cases hmatch : s.m_match m with
      | none =>
          have hpositive : 0 < val_m m w := by
            simpa [valM, hmatch] using hm
          exact hterm ⟨m, hmatch, ⟨w, hremaining, le_of_lt hpositive⟩⟩
      | some wcur =>
          have hnotCurrentRemaining : wcur ∉ s.m_proposals m :=
            hmatchedProposed m wcur hmatch
          have hstrict : val_m m wcur < val_m m w := by
            simpa [valM, hmatch] using hm
          have hnonneg : 0 ≤ val_m m w :=
            le_trans (hmanIR m wcur hmatch) (le_of_lt hstrict)
          have hle : val_m m w ≤ val_m m wcur :=
            hproposalOrder m wcur w hnotCurrentRemaining hremaining hnonneg
          linarith
    · have hnotMatched : s.m_match m ≠ some w := by
        intro hmatch
        have hself : val_m m w < val_m m w := by
          simpa [valM, hmatch] using hm
        exact (lt_irrefl (val_m m w)) hself
      have hrej := hwomanReject w m hremaining hnotMatched
      rcases hrej with hnegative | ⟨mcur, hwcur, hrejectsForCurrent⟩
      · have hcurrentNonneg : 0 ≤ valW val_w w (s.w_match w) := by
          cases hmatch : s.w_match w with
          | none =>
              simp [valW]
          | some mcur =>
              simpa [valW, hmatch] using hwomanIR w mcur hmatch
        have hpositive : 0 < val_w w m := lt_of_le_of_lt hcurrentNonneg hw
        linarith
      · have hcurrentStrict : val_w w mcur < val_w w m := by
          simpa [valW, hwcur] using hw
        linarith

def DATerminationCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ¬ ∃ m, IsActiveMan val_m (deferredAcceptanceState val_m val_w) m

/-- The finite folded DA implementation terminates within `|M| * |W|` steps. -/
theorem deferredAcceptanceState_terminated (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DATerminationCertificate val_m val_w := by
  unfold DATerminationCertificate deferredAcceptanceState
  exact no_active_after_steps_of_count_le_length val_m val_w
    (List.range (Fintype.card M * Fintype.card W))
    (initialDAState M W)
    (by simp [remainingProposalCount_initial])

def DaProducesStableMatchingCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  DAStepPreservesInvariantsCertificate val_m val_w

theorem da_produces_stable_matching_of_certificate (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaProducesStableMatchingCertificate val_m val_w) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) := by
  have hstate : DAStateInvariantCertificate val_m val_w :=
    deferredAcceptanceState_satisfies_invariants_of_step_certificate val_m val_w hcert
  exact stable_of_invariants_and_terminated val_m val_w (deferredAcceptanceState val_m val_w)
    hstate (deferredAcceptanceState_terminated val_m val_w)

theorem deferredAcceptanceState_satisfies_invariants_closed
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DAStateInvariantCertificate val_m val_w :=
  deferredAcceptanceState_satisfies_invariants_of_step_certificate val_m val_w
    (daStep_preserves_invariants_certificate val_m val_w)

theorem da_produces_stable_matching (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) :=
  da_produces_stable_matching_of_certificate val_m val_w
    (daStep_preserves_invariants_certificate val_m val_w)

/-- Men have strict preferences over women. -/
def MenStrictPreferenceProfile (val_m : M → W → ℝ) : Prop :=
  ∀ m w w', val_m m w = val_m m w' → w = w'

/-- Women have strict preferences over men. -/
def WomenStrictPreferenceProfile (val_w : W → M → ℝ) : Prop :=
  ∀ w m m', val_w w m = val_w w m' → m = m'

/--
All potential pairs are acceptable to both sides. This is the marriage-problem
specialization in Roth's proof, where every agent must be matched.
-/
def AllPairsAcceptable (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  (∀ m w, 0 < val_m m w) ∧ (∀ w m, 0 < val_w w m)

/--
On equal-size all-acceptable marriage markets, the DA outcome matches every man
and every woman. This is the completeness bridge between the no-outside-option
marriage model and the generic optional-partner DA encoding.
-/
theorem deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    (∀ m, ∃ w, (deferredAcceptance val_m val_w).m_match m = some w) ∧
      (∀ w, ∃ m, (deferredAcceptance val_m val_w).w_match w = some m) := by
  classical
  let s := deferredAcceptanceState val_m val_w
  have hinv : DAInvariants val_m val_w s := by
    simpa [s, DAStateInvariantCertificate] using
      deferredAcceptanceState_satisfies_invariants_closed val_m val_w
  have hterm : ¬ ∃ m, IsActiveMan val_m s m := by
    have htermCert := deferredAcceptanceState_terminated val_m val_w
    simpa [s, DATerminationCertificate] using htermCert
  let mu : Assignment M W := ⟨s.m_match, s.w_match, s.consistent⟩
  have hmComplete : ∀ m, ∃ w, s.m_match m = some w := by
    intro m
    cases hm : s.m_match m with
    | some w =>
        exact ⟨w, rfl⟩
    | none =>
        have hnoRemaining : ∀ w, w ∉ s.m_proposals m := by
          intro w hw
          exact hterm ⟨m, hm, ⟨w, hw, le_of_lt (hacceptable.1 m w)⟩⟩
        have hwComplete : ∀ w, ∃ m, s.w_match w = some m := by
          intro w
          have hnotMatched : s.m_match m ≠ some w := by
            rw [hm]
            simp
          rcases hinv.2.2.2.1 w m (hnoRemaining w) hnotMatched with
            hneg | ⟨mcur, hwcur, _hle⟩
          · have hpos := hacceptable.2 w m
            linarith
          · exact ⟨mcur, hwcur⟩
        have hmCompleteFromWomen :
            ∀ m, ∃ w, s.m_match m = some w := by
          simpa [mu] using
            Assignment.m_complete_of_w_complete_of_card_eq
              (mu := mu) hcard hwComplete
        rcases hmCompleteFromWomen m with ⟨w, hw⟩
        rw [hm] at hw
        cases hw
  have hwComplete : ∀ w, ∃ m, s.w_match w = some m := by
    simpa [mu] using
      Assignment.w_complete_of_m_complete_of_card_eq
        (mu := mu) hcard hmComplete
  constructor
  · intro m
    simpa [deferredAcceptance, s] using hmComplete m
  · intro w
    simpa [deferredAcceptance, s] using hwComplete w

/--
Roth's "possible woman" invariant for the proposing side: if a man has already
lost access to a woman and is not currently holding her, then no stable matching
can pair them.
-/
def DARejectedPairImpossibleInvariant
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W) : Prop :=
  ∀ mu, IsStable val_m val_w mu →
    ∀ m w, w ∉ s.m_proposals m → s.m_match m ≠ some w →
      mu.m_match m ≠ some w

/-- Initially no pair has been rejected, so the rejected-pair invariant is vacuous. -/
lemma initialDAState_satisfies_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    DARejectedPairImpossibleInvariant val_m val_w (initialDAState M W) := by
  intro mu hstable m w hnot _
  simp [initialDAState] at hnot

lemma better_than_best_not_remaining
    (val_m : M → W → ℝ) (s : DAState M W) {m : M} {w : W}
    (hacceptable : ∀ m w, 0 < val_m m w)
    (hwbest : BestRemainingWoman val_m s m w) :
    ∀ w', val_m m w < val_m m w' → w' ∉ s.m_proposals m := by
  intro w' hbetter hmem
  have hle := hwbest.2.2 w' hmem (le_of_lt (hacceptable m w'))
  linarith

/--
If woman `w` rejects `r` in favor of `a`, and `a` has just proposed to `w`,
then no stable matching can pair `r` with `w`. This is the local blocking-pair
step in Roth's proof of men-optimality.
-/
lemma stable_matching_excludes_rejected_pair
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (mu : Assignment M W)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s)
    (hstable : IsStable val_m val_w mu)
    {a r : M} {w : W}
    (hne : a ≠ r)
    (hbetterRemoved : ∀ w', val_m a w < val_m a w' → w' ∉ s.m_proposals a)
    (hnotCurrentBetter : ∀ w', val_m a w < val_m a w' → s.m_match a ≠ some w')
    (hwomanPref : val_w w r < val_w w a) :
    mu.m_match r ≠ some w := by
  intro hrw
  have hw_mu : mu.w_match w = some r := (mu.consistent_m r w).1 hrw
  have hmanPref : valM val_m a (mu.m_match a) < val_m a w := by
    cases ha_mu : mu.m_match a with
    | none =>
        simpa [valM, ha_mu] using hacceptable.1 a w
    | some wmu =>
        have hne_wmu : wmu ≠ w := by
          intro heq
          have hw_a : mu.w_match w = some a := by
            simpa [heq] using (mu.consistent_m a wmu).1 ha_mu
          have : some a = some r := by
            rw [← hw_a, hw_mu]
          exact hne (Option.some.inj this)
        by_cases hle : val_m a wmu ≤ val_m a w
        · have hneq : val_m a wmu ≠ val_m a w := by
            intro heq
            exact hne_wmu (hstrictM a wmu w heq)
          exact lt_of_le_of_ne hle hneq
        · have hbetter : val_m a w < val_m a wmu := lt_of_not_ge hle
          exact False.elim
            (hrejected mu hstable a wmu
              (hbetterRemoved wmu hbetter)
              (hnotCurrentBetter wmu hbetter)
              ha_mu)
  have hwomanPref' : valW val_w w (mu.w_match w) < val_w w a := by
    simpa [valW, hw_mu] using hwomanPref
  exact hstable.2.2 a w hmanPref hwomanPref'

lemma rejectStep_preserves_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) {m : M} {w : W}
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hact : IsActiveMan val_m s m)
    (hwbest : BestRemainingWoman val_m s m w)
    (hreject :
      ¬ match s.w_match w with
        | none => 0 ≤ val_w w m
        | some m' => val_w w m' < val_w w m)
    (hinv : DAInvariants val_m val_w s)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    DARejectedPairImpossibleInvariant val_m val_w
      { s with m_proposals := removeProposal s m w } := by
  rcases hinv with ⟨_hmanIR, _hwomanIR, hmatchedProposed, _hwomanReject,
    hproposalOrder⟩
  intro mu hstable m0 w0 hnotNew hnotMatchNew
  rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
  · exact hrejected mu hstable m0 w0 hnotOld hnotMatchNew
  · subst m0
    subst w0
    cases hcur : s.w_match w with
    | none =>
        intro hmu
        have hw_mu : mu.w_match w = some m := (mu.consistent_m m w).1 hmu
        have hwIR := hstable.2.1 w
        have hnotNonneg : ¬ 0 ≤ val_w w m := by
          simpa [hcur] using hreject
        have hnonneg : 0 ≤ val_w w m := by
          simpa [valW, hw_mu] using hwIR
        exact hnotNonneg hnonneg
    | some a =>
        have ha_match : s.m_match a = some w := (s.consistent a w).2 hcur
        have hne : a ≠ m := by
          intro h
          subst a
          rw [hact.1] at ha_match
          cases ha_match
        have hle : val_w w m ≤ val_w w a := by
          have hnotlt : ¬ val_w w a < val_w w m := by
            simpa [hcur] using hreject
          exact le_of_not_gt hnotlt
        have hwomanPref : val_w w m < val_w w a := by
          have hneq : val_w w m ≠ val_w w a := by
            intro heq
            exact hne ((hstrictW w m a heq).symm)
          exact lt_of_le_of_ne hle hneq
        refine stable_matching_excludes_rejected_pair val_m val_w s mu
          hstrictM hacceptable hrejected hstable hne ?_ ?_ hwomanPref
        · intro w' hbetter hmem
          have hnotCurrent : w ∉ s.m_proposals a :=
            hmatchedProposed a w ha_match
          have hle' := hproposalOrder a w w' hnotCurrent hmem
            (le_of_lt (hacceptable.1 a w'))
          linarith
        · intro w' hbetter hmatch
          rw [ha_match] at hmatch
          injection hmatch with hw'
          subst w'
          linarith

lemma acceptStep_preserves_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) {m : M} {w : W}
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hact : IsActiveMan val_m s m)
    (hwbest : BestRemainingWoman val_m s m w)
    (haccept :
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    DARejectedPairImpossibleInvariant val_m val_w
      { m_match := fun m'' =>
          if m'' = m then some w
          else if s.w_match w = some m'' then none
          else s.m_match m''
        w_match := Function.update s.w_match w (some m)
        m_proposals := removeProposal s m w
        consistent := by
          simpa using acceptMatch_consistent s hact.1 } := by
  intro mu hstable m0 w0 hnotNew hnotMatchNew
  rcases not_mem_of_not_mem_removeProposal s hnotNew with hnotOld | ⟨hm0, hw0⟩
  · by_cases holdMatch : s.m_match m0 = some w0
    · have hm0_ne_m : m0 ≠ m := by
        intro hm0
        subst m0
        rw [hact.1] at holdMatch
        cases holdMatch
      by_cases hcur0 : s.w_match w = some m0
      · have holdW : s.m_match m0 = some w := (s.consistent m0 w).2 hcur0
        have hw0_eq : w0 = w := Option.some.inj (holdMatch.symm.trans holdW)
        subst w0
        have hne : m ≠ m0 := fun h => hm0_ne_m h.symm
        have hwomanPref : val_w w m0 < val_w w m := by
          simpa [hcur0] using haccept
        exact stable_matching_excludes_rejected_pair val_m val_w s mu
          hstrictM hacceptable hrejected hstable hne
          (better_than_best_not_remaining val_m s hacceptable.1 hwbest)
          (by
            intro w' _ hmatch
            rw [hact.1] at hmatch
            cases hmatch)
          hwomanPref
      · exact False.elim (hnotMatchNew (by simpa [hm0_ne_m, hcur0] using holdMatch))
    · exact hrejected mu hstable m0 w0 hnotOld holdMatch
  · subst m0
    subst w0
    exact False.elim (hnotMatchNew (by simp))

theorem daStep_preserves_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    ∀ s, DAInvariants val_m val_w s →
      DARejectedPairImpossibleInvariant val_m val_w s →
        DARejectedPairImpossibleInvariant val_m val_w
          (daStep val_m val_w s) := by
  intro s hinv hrejected
  classical
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · unfold daStep
    rw [dif_pos hactive]
    let m := Classical.choose hactive
    have hact : IsActiveMan val_m s m := by
      simpa [m] using Classical.choose_spec hactive
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    have hwbest : BestRemainingWoman val_m s m w := by
      simpa [w, w_exists] using Classical.choose_spec w_exists
    let accepts : Prop :=
      match s.w_match w with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    by_cases hacc : accepts
    · simpa [m, hact, w_exists, w, accepts, hacc] using
        acceptStep_preserves_rejected_pair_impossible
          val_m val_w s hstrictM hacceptable hact hwbest hacc hrejected
    · simpa [m, hact, w_exists, w, accepts, hacc] using
        rejectStep_preserves_rejected_pair_impossible
          val_m val_w s hstrictM hstrictW hacceptable hact hwbest hacc hinv
          hrejected
  · simpa [daStep, hactive] using hrejected

lemma foldl_daStep_preserves_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (steps : List ℕ) (s : DAState M W)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hinv : DAInvariants val_m val_w s)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w s) :
    DARejectedPairImpossibleInvariant val_m val_w
      (steps.foldl (fun s _ => daStep val_m val_w s) s) := by
  induction steps generalizing s with
  | nil =>
      simpa using hrejected
  | cons _ steps ih =>
      rw [List.foldl_cons]
      exact ih (daStep val_m val_w s)
        (daStep_preserves_invariants_certificate val_m val_w s hinv)
        (daStep_preserves_rejected_pair_impossible val_m val_w
          hstrictM hstrictW hacceptable s hinv hrejected)

theorem deferredAcceptanceState_satisfies_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    DARejectedPairImpossibleInvariant val_m val_w
      (deferredAcceptanceState val_m val_w) := by
  unfold deferredAcceptanceState
  exact foldl_daStep_preserves_rejected_pair_impossible val_m val_w
    (List.range (Fintype.card M * Fintype.card W))
    (initialDAState M W)
    hstrictM hstrictW hacceptable
    (initialDAState_satisfies_invariants val_m val_w)
    (initialDAState_satisfies_rejected_pair_impossible val_m val_w)

def DaIsMenOptimalCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ∀ mu', IsStable val_m val_w mu' →
    ∀ m, valM val_m m (mu'.m_match m) ≤ valM val_m m ((deferredAcceptance val_m val_w).m_match m)

theorem da_is_men_optimal_of_rejected_pair_impossible
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstate : DAStateInvariantCertificate val_m val_w)
    (hterm : DATerminationCertificate val_m val_w)
    (hrejected : DARejectedPairImpossibleInvariant val_m val_w
      (deferredAcceptanceState val_m val_w)) :
    DaIsMenOptimalCertificate val_m val_w := by
  unfold DaIsMenOptimalCertificate
  intro mu hstable m
  change valM val_m m (mu.m_match m) ≤
    valM val_m m ((deferredAcceptanceState val_m val_w).m_match m)
  unfold DAStateInvariantCertificate at hstate
  unfold DATerminationCertificate at hterm
  rcases hstate with ⟨hmanIR, _hwomanIR, hmatchedProposed, _hwomanReject,
    hproposalOrder⟩
  by_contra hnot
  have hgt :
      valM val_m m ((deferredAcceptanceState val_m val_w).m_match m) <
        valM val_m m (mu.m_match m) := lt_of_not_ge hnot
  cases hmu : mu.m_match m with
  | none =>
      have hfinalIR :
          0 ≤ valM val_m m ((deferredAcceptanceState val_m val_w).m_match m) := by
        cases hfinal : (deferredAcceptanceState val_m val_w).m_match m with
        | none =>
            simp [valM]
        | some w =>
            simpa [valM, hfinal] using hmanIR m w hfinal
      simp [valM, hmu] at hgt
      simp [valM] at hfinalIR
      linarith
  | some w =>
      have hnotFinal :
          (deferredAcceptanceState val_m val_w).m_match m ≠ some w := by
        intro hfinal
        simp [valM, hmu, hfinal] at hgt
      have hnotRemaining :
          w ∉ (deferredAcceptanceState val_m val_w).m_proposals m := by
        intro hremaining
        cases hfinal : (deferredAcceptanceState val_m val_w).m_match m with
        | none =>
            have hpositive : 0 < val_m m w := by
              simpa [valM, hmu, hfinal] using hgt
            exact hterm ⟨m, hfinal, ⟨w, hremaining, le_of_lt hpositive⟩⟩
        | some wcur =>
            have hnotCurrentRemaining :
                wcur ∉ (deferredAcceptanceState val_m val_w).m_proposals m :=
              hmatchedProposed m wcur hfinal
            have hbetter : val_m m wcur < val_m m w := by
              simpa [valM, hmu, hfinal] using hgt
            have hnonneg : 0 ≤ val_m m w := by
              have hcurIR : 0 ≤ val_m m wcur := hmanIR m wcur hfinal
              linarith
            have hle := hproposalOrder m wcur w hnotCurrentRemaining
              hremaining hnonneg
            linarith
      exact hrejected mu hstable m w hnotRemaining hnotFinal hmu

theorem da_is_men_optimal_of_strict_preferences
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    DaIsMenOptimalCertificate val_m val_w :=
  da_is_men_optimal_of_rejected_pair_impossible val_m val_w
    (deferredAcceptanceState_satisfies_invariants_closed val_m val_w)
    (deferredAcceptanceState_terminated val_m val_w)
    (deferredAcceptanceState_satisfies_rejected_pair_impossible val_m val_w
      hstrictM hstrictW hacceptable)

/-- A DA state with invariants and no active man is stable. -/
theorem daState_stable_of_invariants_and_termination (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (hinv : DAInvariants val_m val_w s)
    (hterm : ¬ ∃ m, IsActiveMan val_m s m) :
    IsStable val_m val_w ⟨s.m_match, s.w_match, s.consistent⟩ :=
  stable_of_invariants_and_terminated val_m val_w s hinv hterm

/-- Stable matching from separated DA certificate components.

This gives a direct API that avoids unpacking `DaProducesStableMatchingCertificate`.
-/
theorem deferredAcceptance_stable_of_certificate
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstate : DAStateInvariantCertificate val_m val_w)
    (hterm : DATerminationCertificate val_m val_w) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) :=
  stable_of_invariants_and_terminated
    val_m val_w
    (deferredAcceptanceState val_m val_w)
    hstate hterm

/-- Alias with the existing full DA certificate term. -/
theorem deferredAcceptance_stable_of_certificate'
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaProducesStableMatchingCertificate val_m val_w) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) :=
  da_produces_stable_matching_of_certificate val_m val_w hcert

end Matching
end EconCSLib
