import EconCSLib.SocialChoice.Voting.STV.Quota
import Mathlib.Tactic.Linarith

/-!
# Solid-Coalition STV Process Primitives

Paper-neutral process invariants for STV proofs under solid coalitions.

The central abstraction is a separate same-party quota process. It tracks how
many same-party candidates have reached quota and how much same-party vote mass
remains. When the remaining same-party vote mass is below one quota, the process
provides the quota-witness used by two-party STV seat-share arguments.
-/

namespace EconCSLib
namespace SocialChoice
namespace Voting

/-- State of a same-party quota process. -/
structure PartyQuotaState where
  remainingCandidates : ℕ
  quotaWinners : ℕ
  voteMass : ℝ

/-- Initial state for a same-party quota process. -/
def PartyQuotaStartState (remainingCandidates : ℕ) (initialVotes : ℝ) :
    PartyQuotaState where
  remainingCandidates := remainingCandidates
  quotaWinners := 0
  voteMass := initialVotes

/--
Invariant for a same-party quota process: the initial vote mass decomposes into
`quotaWinners` full quotas plus current residual same-party vote mass.
-/
def PartyQuotaInvariant (initialVotes quota : ℝ) (state : PartyQuotaState) : Prop :=
  initialVotes = (state.quotaWinners : ℝ) * quota + state.voteMass ∧
    0 ≤ state.voteMass

/-- The start state satisfies the quota decomposition invariant. -/
theorem PartyQuotaInvariant.start {initialVotes quota : ℝ} {remainingCandidates : ℕ}
    (hvotes_nonneg : 0 ≤ initialVotes) :
    PartyQuotaInvariant initialVotes quota
      (PartyQuotaStartState remainingCandidates initialVotes) := by
  constructor
  · simp [PartyQuotaStartState]
  · simpa [PartyQuotaStartState] using hvotes_nonneg

/-- An elect step consumes one quota and records one additional quota winner. -/
def PartyQuotaElectStep (quota : ℝ) (before after : PartyQuotaState) : Prop :=
  quota ≤ before.voteMass ∧
    after.remainingCandidates + 1 = before.remainingCandidates ∧
    after.quotaWinners = before.quotaWinners + 1 ∧
    after.voteMass = before.voteMass - quota

/-- An elimination step removes a candidate without consuming same-party vote mass. -/
def PartyQuotaEliminateStep (_quota : ℝ) (before after : PartyQuotaState) : Prop :=
  after.remainingCandidates + 1 = before.remainingCandidates ∧
    after.quotaWinners = before.quotaWinners ∧
    after.voteMass = before.voteMass

/-- A process is terminal for the lower-bound proof once residual vote mass is below quota. -/
def PartyQuotaTerminalBelowQuota (quota : ℝ) (state : PartyQuotaState) : Prop :=
  state.voteMass < quota

/-- A same-party quota process step either elects a quota winner or eliminates a candidate. -/
def PartyQuotaStep (quota : ℝ) (before after : PartyQuotaState) : Prop :=
  PartyQuotaElectStep quota before after ∨ PartyQuotaEliminateStep quota before after

/--
A complete same-party quota process certificate: a start state with the quota
decomposition invariant, a reachable terminal state, and terminal residual vote
mass below quota.
-/
structure PartyQuotaProcess (initialVotes quota : ℝ) where
  startState : PartyQuotaState
  terminalState : PartyQuotaState
  startInvariant : PartyQuotaInvariant initialVotes quota startState
  path : Relation.ReflTransGen (PartyQuotaStep quota) startState terminalState
  terminalBelowQuota : PartyQuotaTerminalBelowQuota quota terminalState

/-- If a party has a remaining candidate with at least one quota of vote mass, an elect step exists. -/
theorem exists_partyQuotaElectStep {quota : ℝ} {before : PartyQuotaState}
    (hquota_le : quota ≤ before.voteMass)
    (hremaining : 0 < before.remainingCandidates) :
    ∃ after, PartyQuotaElectStep quota before after := by
  refine ⟨{
    remainingCandidates := before.remainingCandidates - 1
    quotaWinners := before.quotaWinners + 1
    voteMass := before.voteMass - quota
  }, hquota_le, ?_, rfl, rfl⟩
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt hremaining)

/-- If a party has a remaining candidate, an elimination step exists. -/
theorem exists_partyQuotaEliminateStep {quota : ℝ} {before : PartyQuotaState}
    (hremaining : 0 < before.remainingCandidates) :
    ∃ after, PartyQuotaEliminateStep quota before after := by
  refine ⟨{
    remainingCandidates := before.remainingCandidates - 1
    quotaWinners := before.quotaWinners
    voteMass := before.voteMass
  }, ?_, rfl, rfl⟩
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt hremaining)

/-- If a party's vote mass is not at least quota, it is terminal for this proof. -/
theorem PartyQuotaTerminalBelowQuota.of_not_quota_le {quota : ℝ}
    {state : PartyQuotaState} (hquota_not_le : ¬ quota ≤ state.voteMass) :
    PartyQuotaTerminalBelowQuota quota state :=
  not_le.mp hquota_not_le

/--
Starting from all same-party votes in one process state, repeated elect steps
can realize any number of quota winners whose full quotas fit inside the
initial vote mass and candidate supply.
-/
theorem exists_partyQuotaElectPath {initialVotes quota : ℝ}
    (hquota_pos : 0 < quota) :
    ∀ {quotaSeats remainingCandidates : ℕ},
      quotaSeats ≤ remainingCandidates →
      (quotaSeats : ℝ) * quota ≤ initialVotes →
      ∃ state,
        Relation.ReflTransGen (PartyQuotaStep quota)
          (PartyQuotaStartState remainingCandidates initialVotes) state ∧
        state.remainingCandidates = remainingCandidates - quotaSeats ∧
        state.quotaWinners = quotaSeats ∧
        state.voteMass = initialVotes - (quotaSeats : ℝ) * quota := by
  intro quotaSeats
  induction quotaSeats with
  | zero =>
      intro remainingCandidates _hcandidates _hvotes
      refine ⟨PartyQuotaStartState remainingCandidates initialVotes,
        Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
      · simp [PartyQuotaStartState]
      · simp [PartyQuotaStartState]
      · simp [PartyQuotaStartState]
  | succ quotaSeats ih =>
      intro remainingCandidates hcandidates hvotes
      have hprev_candidates : quotaSeats ≤ remainingCandidates := by
        omega
      have hprev_votes : (quotaSeats : ℝ) * quota ≤ initialVotes := by
        have hcast_le : (quotaSeats : ℝ) ≤ ((quotaSeats + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ quotaSeats
        nlinarith
      rcases ih hprev_candidates hprev_votes with
        ⟨state, hpath, hremaining, hwinners, hmass⟩
      have hstate_remaining_pos : 0 < state.remainingCandidates := by
        rw [hremaining]
        have hlt : quotaSeats < remainingCandidates := by
          exact Nat.lt_of_succ_le hcandidates
        exact Nat.sub_pos_of_lt hlt
      have hquota_le : quota ≤ state.voteMass := by
        rw [hmass]
        have hvotes_succ : (((quotaSeats + 1 : ℕ) : ℝ) * quota) ≤
            initialVotes := hvotes
        norm_num [Nat.cast_add, Nat.cast_one] at hvotes_succ
        nlinarith
      rcases exists_partyQuotaElectStep hquota_le hstate_remaining_pos with
        ⟨after, hstep⟩
      have hsingle :
          Relation.ReflTransGen (PartyQuotaStep quota) state after :=
        Relation.ReflTransGen.single (Or.inl hstep)
      refine ⟨after, Relation.ReflTransGen.trans hpath hsingle, ?_, ?_, ?_⟩
      · rcases hstep with ⟨_hquota, hafter_remaining, _hwinners, _hmass⟩
        have hafter_succ :
            after.remainingCandidates + 1 = remainingCandidates - quotaSeats := by
          simpa [hremaining] using hafter_remaining
        omega
      · rcases hstep with ⟨_hquota, _hremaining, hafter_winners, _hmass⟩
        rw [hafter_winners, hwinners]
      · rcases hstep with ⟨_hquota, _hremaining, _hwinners, hafter_mass⟩
        rw [hafter_mass, hmass]
        have hsucc_cast : (((quotaSeats + 1 : ℕ) : ℝ) = (quotaSeats : ℝ) + 1) := by
          norm_num [Nat.cast_add, Nat.cast_one, add_comm]
        rw [hsucc_cast]
        ring

/--
With enough same-party candidates, the elect-step recurrence reaches the
canonical floor-quota terminal state.
-/
theorem exists_partyQuotaProcess_floor {initialVotes quota : ℝ}
    {remainingCandidates : ℕ}
    (hquota_pos : 0 < quota) (hvotes_nonneg : 0 ≤ initialVotes)
    (hcandidates : ⌊initialVotes / quota⌋₊ ≤ remainingCandidates) :
    ∃ process : PartyQuotaProcess initialVotes quota,
      process.terminalState.quotaWinners = ⌊initialVotes / quota⌋₊ ∧
      process.terminalState.voteMass =
        initialVotes - (⌊initialVotes / quota⌋₊ : ℝ) * quota := by
  let quotaSeats : ℕ := ⌊initialVotes / quota⌋₊
  have hres :
      QuotaResidualBound quotaSeats initialVotes quota := by
    simpa [quotaSeats] using
      quotaResidualBound_floor_votes_div_quota hquota_pos hvotes_nonneg
  rcases hres with ⟨_hquota_pos, residual, hres_nonneg, hres_lt, hinit⟩
  have hvotes_floor : (quotaSeats : ℝ) * quota ≤ initialVotes := by
    nlinarith
  rcases exists_partyQuotaElectPath (initialVotes := initialVotes)
      (quota := quota) hquota_pos hcandidates hvotes_floor with
    ⟨terminalState, hpath, _hremaining, hwinners, hmass⟩
  have hterminal : PartyQuotaTerminalBelowQuota quota terminalState := by
    change terminalState.voteMass < quota
    rw [hmass]
    have hresidual_eq :
        initialVotes - (⌊initialVotes / quota⌋₊ : ℝ) * quota = residual := by
      simpa [quotaSeats] using
        (by nlinarith : initialVotes - (quotaSeats : ℝ) * quota = residual)
    rw [hresidual_eq]
    exact hres_lt
  refine ⟨{
    startState := PartyQuotaStartState remainingCandidates initialVotes
    terminalState := terminalState
    startInvariant := PartyQuotaInvariant.start hvotes_nonneg
    path := hpath
    terminalBelowQuota := hterminal
  }, ?_, ?_⟩
  · simpa [quotaSeats] using hwinners
  · simpa [quotaSeats] using hmass

/-- Elect steps preserve the quota decomposition invariant. -/
theorem PartyQuotaInvariant.of_electStep {initialVotes quota : ℝ}
    {before after : PartyQuotaState}
    (hinv : PartyQuotaInvariant initialVotes quota before)
    (hstep : PartyQuotaElectStep quota before after) :
    PartyQuotaInvariant initialVotes quota after := by
  rcases hinv with ⟨hinit, hmass_nonneg⟩
  rcases hstep with ⟨hquota_le, _hcand, hwinners, hmass⟩
  constructor
  · rw [hinit, hwinners, hmass]
    norm_num
    ring
  · rw [hmass]
    linarith

/-- Elimination steps preserve the quota decomposition invariant. -/
theorem PartyQuotaInvariant.of_eliminateStep {initialVotes quota : ℝ}
    {before after : PartyQuotaState}
    (hinv : PartyQuotaInvariant initialVotes quota before)
    (hstep : PartyQuotaEliminateStep quota before after) :
    PartyQuotaInvariant initialVotes quota after := by
  rcases hinv with ⟨hinit, hmass_nonneg⟩
  rcases hstep with ⟨_hcand, hwinners, hmass⟩
  constructor
  · rw [hinit, hwinners, hmass]
  · rw [hmass]
    exact hmass_nonneg

/-- Any same-party quota process step preserves the quota decomposition invariant. -/
theorem PartyQuotaInvariant.of_step {initialVotes quota : ℝ}
    {before after : PartyQuotaState}
    (hinv : PartyQuotaInvariant initialVotes quota before)
    (hstep : PartyQuotaStep quota before after) :
    PartyQuotaInvariant initialVotes quota after := by
  rcases hstep with hstep | hstep
  · exact PartyQuotaInvariant.of_electStep hinv hstep
  · exact PartyQuotaInvariant.of_eliminateStep hinv hstep

/--
Reachability along a same-party quota process preserves the quota decomposition
invariant.
-/
theorem PartyQuotaInvariant.of_reflTransGen {initialVotes quota : ℝ}
    {before after : PartyQuotaState}
    (hinv : PartyQuotaInvariant initialVotes quota before)
    (hpath : Relation.ReflTransGen (PartyQuotaStep quota) before after) :
    PartyQuotaInvariant initialVotes quota after := by
  induction hpath using Relation.ReflTransGen.trans_induction_on with
  | refl => exact hinv
  | single hstep => exact PartyQuotaInvariant.of_step hinv hstep
  | trans _ _ hleft hright => exact hright (hleft hinv)

namespace PartyQuotaProcess

/-- The terminal state of a certified same-party process satisfies the invariant. -/
theorem terminalInvariant {initialVotes quota : ℝ}
    (process : PartyQuotaProcess initialVotes quota) :
    PartyQuotaInvariant initialVotes quota process.terminalState :=
  PartyQuotaInvariant.of_reflTransGen process.startInvariant process.path

end PartyQuotaProcess

/--
A terminal same-party quota process provides a residual certificate for its
number of quota winners.
-/
theorem quotaResidualBound_of_partyQuotaInvariant_of_terminalBelowQuota
    {initialVotes quota : ℝ} {state : PartyQuotaState}
    (hquota_pos : 0 < quota)
    (hinv : PartyQuotaInvariant initialVotes quota state)
    (hterminal : PartyQuotaTerminalBelowQuota quota state) :
    QuotaResidualBound state.quotaWinners initialVotes quota := by
  exact ⟨hquota_pos, state.voteMass, hinv.2, hterminal, hinv.1⟩

/--
If final same-party STV seats include all quota winners from a terminal
same-party process, then the final seat count has the quota lower-bound witness.
-/
theorem quotaLowerBoundWitness_of_partyQuotaProcess {finalSeats : ℕ}
    {initialVotes quota : ℝ} {state : PartyQuotaState}
    (hquota_pos : 0 < quota)
    (hfinal : state.quotaWinners ≤ finalSeats)
    (hinv : PartyQuotaInvariant initialVotes quota state)
    (hterminal : PartyQuotaTerminalBelowQuota quota state) :
    QuotaLowerBoundWitness finalSeats initialVotes quota :=
  ⟨state.quotaWinners, hfinal,
    quotaResidualBound_of_partyQuotaInvariant_of_terminalBelowQuota
      hquota_pos hinv hterminal⟩

/--
If final same-party STV seats include all quota winners from a certified
same-party process, then the final seat count has the quota lower-bound witness.
-/
theorem quotaLowerBoundWitness_of_partyQuotaProcessCertificate {finalSeats : ℕ}
    {initialVotes quota : ℝ}
    (process : PartyQuotaProcess initialVotes quota)
    (hquota_pos : 0 < quota)
    (hfinal : process.terminalState.quotaWinners ≤ finalSeats) :
    QuotaLowerBoundWitness finalSeats initialVotes quota :=
  quotaLowerBoundWitness_of_partyQuotaProcess hquota_pos hfinal
    process.terminalInvariant process.terminalBelowQuota

end Voting
end SocialChoice
end EconCSLib
