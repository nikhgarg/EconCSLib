import EconCSLib.SocialChoice.Voting.Ballot

/-!
# STV Trace Primitives

Paper-neutral vocabulary for deterministic single-transferable-vote and
ranked-choice traces.

This module intentionally does not encode a single quota or tie-breaking
convention. Downstream developments should instantiate these structures with
their concrete rules and prove replay/validity theorems there or in later
generic modules.

## Main declarations

- `STVQuota`
- `strictSupportGroupRemovalCondition`
- `strictSupportGroupRemovalSafety`
- `strictSupportGroupRemovalSafety_of_condition`
- `strictSupportGroupRemovalSafety_trace_elimination_focus_mem_group`
- `StepKind`
- `STVStep`
- `STVTrace`
- `STVStep.activeMonotone`
- `STVStep.eliminatesMinimalTally`
- `STVStep.removesFocusedCandidate`
- `STVStep.focus_eq_of_tally_lt_all_other_active`
- `ActiveUntilExitRank`
-/

namespace EconCSLib
namespace SocialChoice
namespace Voting

/-- Droop-style integer quota used by many STV presentations. -/
def STVQuota (seats voters : ℕ) : ℕ :=
  voters / (seats + 1) + 1

/--
Strict-support group-removal condition: every candidate inside a removable
group remains below quota after the budget, and every outside candidate still
strictly dominates the possible last inside candidate after the rest of the
group transfers away.
-/
def strictSupportGroupRemovalCondition {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (candidates group : Finset Candidate) (budget quota : ℕ) : Prop :=
  (∀ inside, inside ∈ group →
    budget + Ballot.strictSupportCount voters ballots group
        (candidates \ group) inside < quota) ∧
    ∀ inside, inside ∈ group → ∀ outside, outside ∈ candidates \ group →
      budget + Ballot.strictSupportCount voters ballots group
          (candidates \ group) inside <
        Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside ∧
      Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside < quota

/--
Separated safety consequences of strict-support group removal: inside
candidates remain below quota, outside candidates dominate each possible last
inside candidate, and outside candidates remain below quota.
-/
def strictSupportGroupRemovalSafety {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (candidates group : Finset Candidate) (budget quota : ℕ) : Prop :=
  (∀ inside, inside ∈ group →
    budget + Ballot.strictSupportCount voters ballots group
        (candidates \ group) inside < quota) ∧
    (∀ inside, inside ∈ group → ∀ outside, outside ∈ candidates \ group →
      budget + Ballot.strictSupportCount voters ballots group
          (candidates \ group) inside <
        Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside) ∧
    ∀ inside, inside ∈ group → ∀ outside, outside ∈ candidates \ group →
      Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside < quota

/--
The compact strict-support group-removal condition entails its separated
safety consequences.
-/
theorem strictSupportGroupRemovalSafety_of_condition
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hcondition :
      strictSupportGroupRemovalCondition
        voters ballots candidates group budget quota) :
    strictSupportGroupRemovalSafety voters ballots candidates group budget quota := by
  rcases hcondition with ⟨hbelow_quota, houtside_condition⟩
  exact ⟨hbelow_quota,
    (by
      intro inside hinside outside houtside
      exact (houtside_condition inside hinside outside houtside).1),
    (by
      intro inside hinside outside houtside
      exact (houtside_condition inside hinside outside houtside).2)⟩

/-- A deterministic trace step either elects, eliminates, transfers, or stops. -/
inductive StepKind where
  | elect
  | eliminate
  | transfer
  | finish
  deriving DecidableEq, Repr

/--
One deterministic STV/RCV trace step.

The `tally` field is intentionally an input datum here. Different papers may
derive tallies from first-active ballots, fractional transfers, or audited data
sources before instantiating this generic trace layer.
-/
structure STVStep (Candidate : Type*) where
  beforeActive : Finset Candidate
  afterActive : Finset Candidate
  kind : StepKind
  focus : Option Candidate
  tally : Candidate → ℕ

namespace STVStep

/-- The active set only shrinks along an ordinary deterministic STV step. -/
def activeMonotone {Candidate : Type*} (step : STVStep Candidate) : Prop :=
  step.afterActive ⊆ step.beforeActive

/--
The step removes exactly its focused candidate from the active set.

This is separated from `kind`: different papers may use the same active-set
transition for eliminations, elections, or quota-transfer bookkeeping.
-/
def removesFocusedCandidate {Candidate : Type*} [DecidableEq Candidate]
    (step : STVStep Candidate) : Prop :=
  ∃ candidate, step.focus = some candidate ∧
    step.afterActive = step.beforeActive.erase candidate

/--
An elimination step chooses an active candidate whose tally is no larger than
every active candidate's tally.

This predicate deliberately leaves tie-breaking abstract. Paper-local replay
theorems can strengthen it with a concrete tie-breaker when needed.
-/
def eliminatesMinimalTally {Candidate : Type*} (step : STVStep Candidate) :
    Prop :=
  step.kind = StepKind.eliminate ∧
    ∃ loser, step.focus = some loser ∧ loser ∈ step.beforeActive ∧
      ∀ candidate, candidate ∈ step.beforeActive →
        step.tally loser ≤ step.tally candidate

/--
If an active candidate has strictly larger tally than another active
candidate, a minimum-tally elimination step cannot eliminate the larger-tally
candidate.
-/
theorem focus_ne_of_exists_active_tally_lt {Candidate : Type*}
    {step : STVStep Candidate} (hminimal : step.eliminatesMinimalTally)
    {lower candidate : Candidate}
    (hlower_active : lower ∈ step.beforeActive)
    (hcandidate_active : candidate ∈ step.beforeActive)
    (hlt : step.tally lower < step.tally candidate) :
    step.focus ≠ some candidate := by
  rcases hminimal with ⟨_hkind, loser, hfocus, _hloser_active, hloser_le⟩
  intro hfocus_candidate
  have hloser_eq_candidate : loser = candidate := by
    exact Option.some.inj (hfocus.symm.trans hfocus_candidate)
  subst loser
  have hle : step.tally candidate ≤ step.tally lower :=
    hloser_le lower hlower_active
  exact not_lt_of_ge hle hlt

/--
If one active candidate has strictly smaller tally than every other active
candidate, a minimum-tally elimination step must focus on that candidate.
-/
theorem focus_eq_of_tally_lt_all_other_active {Candidate : Type*}
    {step : STVStep Candidate} (hminimal : step.eliminatesMinimalTally)
    {candidate : Candidate}
    (hcandidate_active : candidate ∈ step.beforeActive)
    (hlt :
      ∀ other, other ∈ step.beforeActive → other ≠ candidate →
        step.tally candidate < step.tally other) :
    step.focus = some candidate := by
  rcases hminimal with ⟨_hkind, loser, hfocus, hloser_active, hloser_le⟩
  by_cases hloser_eq : loser = candidate
  · simpa [hloser_eq] using hfocus
  · have hlt_loser : step.tally candidate < step.tally loser :=
      hlt loser hloser_active hloser_eq
    have hle : step.tally loser ≤ step.tally candidate :=
      hloser_le candidate hcandidate_active
    exact (not_lt_of_ge hle hlt_loser).elim

/--
If a step removes its focused candidate, the focused candidate is absent from
the step's post-active set.
-/
theorem focus_not_mem_afterActive_of_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {step : STVStep Candidate} (hremove : step.removesFocusedCandidate)
    {candidate : Candidate} (hfocus : step.focus = some candidate) :
    candidate ∉ step.afterActive := by
  rcases hremove with ⟨removed, hremoved_focus, hafter⟩
  have hremoved_eq : removed = candidate :=
    Option.some.inj (hremoved_focus.symm.trans hfocus)
  subst removed
  simp [hafter]

/--
Removing a focused active candidate from a group strictly decreases the number
of active candidates in that group.
-/
theorem card_afterActive_inter_lt_beforeActive_inter_of_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {step : STVStep Candidate} {group : Finset Candidate}
    (hremove : step.removesFocusedCandidate)
    {candidate : Candidate} (hfocus : step.focus = some candidate)
    (hgroup : candidate ∈ group) (hactive : candidate ∈ step.beforeActive) :
    (step.afterActive ∩ group).card <
      (step.beforeActive ∩ group).card := by
  rcases hremove with ⟨removed, hremoved_focus, hafter⟩
  have hremoved_eq : removed = candidate :=
    Option.some.inj (hremoved_focus.symm.trans hfocus)
  subst removed
  have hmem : candidate ∈ step.beforeActive ∩ group := by
    simp [hactive, hgroup]
  have hinter :
      step.afterActive ∩ group =
        (step.beforeActive ∩ group).erase candidate := by
    ext other
    simp [hafter, and_comm]
  rw [hinter]
  exact Finset.card_erase_lt_of_mem hmem

/--
Removing a focused active candidate from a group decreases the number of active
group candidates by exactly one.
-/
theorem card_afterActive_inter_add_one_eq_beforeActive_inter_of_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {step : STVStep Candidate} {group : Finset Candidate}
    (hremove : step.removesFocusedCandidate)
    {candidate : Candidate} (hfocus : step.focus = some candidate)
    (hgroup : candidate ∈ group) (hactive : candidate ∈ step.beforeActive) :
    (step.afterActive ∩ group).card + 1 =
      (step.beforeActive ∩ group).card := by
  rcases hremove with ⟨removed, hremoved_focus, hafter⟩
  have hremoved_eq : removed = candidate :=
    Option.some.inj (hremoved_focus.symm.trans hfocus)
  subst removed
  have hmem : candidate ∈ step.beforeActive ∩ group := by
    simp [hactive, hgroup]
  have hinter :
      step.afterActive ∩ group =
        (step.beforeActive ∩ group).erase candidate := by
    ext other
    simp [hafter, and_comm]
  rw [hinter]
  exact Finset.card_erase_add_one hmem

end STVStep

/--
Strict-support group-removal safety, read as a current-round tally fact: an
inside candidate's budget-augmented strict support is still below quota.
-/
theorem strictSupportGroupRemovalSafety_inside_tally_lt_quota
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {inside : Candidate} (hinside : inside ∈ group)
    {step : STVStep Candidate}
    (htally_inside :
      step.tally inside =
        budget +
          Ballot.strictSupportCount voters ballots group (candidates \ group)
            inside) :
    step.tally inside < quota := by
  simpa [htally_inside] using hsafety.1 inside hinside

/--
Strict-support group-removal safety, read as a current-round tally fact: an
outside candidate's strict support after transfers from `group \ {inside}` is
still below quota.
-/
theorem strictSupportGroupRemovalSafety_outside_tally_lt_quota
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {inside outside : Candidate} (hinside : inside ∈ group)
    (houtside : outside ∈ candidates \ group)
    {step : STVStep Candidate}
    (htally_outside :
      step.tally outside =
        Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside) :
    step.tally outside < quota := by
  simpa [htally_outside] using hsafety.2.2 inside hinside outside houtside

/--
Strict-support group-removal safety prevents an outside candidate from being
the focus of a minimum-tally elimination step when some inside candidate is
still active with the group-removal tally interpretation.
-/
theorem strictSupportGroupRemovalSafety_outside_not_minimal_elimination_focus
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {inside outside : Candidate} (hinside : inside ∈ group)
    (houtside : outside ∈ candidates \ group)
    {step : STVStep Candidate}
    (hminimal : step.eliminatesMinimalTally)
    (hinside_active : inside ∈ step.beforeActive)
    (houtside_active : outside ∈ step.beforeActive)
    (htally_inside :
      step.tally inside =
        budget +
          Ballot.strictSupportCount voters ballots group (candidates \ group)
            inside)
    (htally_outside :
      step.tally outside =
        Ballot.strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside) :
    step.focus ≠ some outside := by
  have hlt :
      step.tally inside < step.tally outside := by
    simpa [htally_inside, htally_outside] using
      hsafety.2.1 inside hinside outside houtside
  exact STVStep.focus_ne_of_exists_active_tally_lt
    hminimal hinside_active houtside_active hlt

/--
Strict-support group-removal safety forces a minimum-tally elimination step to
focus on a group candidate, provided some group candidate is still active and
the step tallies agree with the group-removal strict-support quantities.
-/
theorem strictSupportGroupRemovalSafety_minimal_elimination_focus_mem_group
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {inside : Candidate} (hinside : inside ∈ group)
    {step : STVStep Candidate}
    (hminimal : step.eliminatesMinimalTally)
    (hinside_active : inside ∈ step.beforeActive)
    (hactive_subset_candidates : step.beforeActive ⊆ candidates)
    (htally_inside :
      step.tally inside =
        budget +
          Ballot.strictSupportCount voters ballots group (candidates \ group)
            inside)
    (htally_outside :
      ∀ outside, outside ∈ candidates \ group →
        step.tally outside =
          Ballot.strictSupportCount voters ballots
            (insert outside (group.erase inside)) (∅ : Finset Candidate)
            outside) :
    ∃ loser, step.focus = some loser ∧ loser ∈ group ∧
      loser ∈ step.beforeActive := by
  rcases hminimal with ⟨hkind, loser, hfocus, hloser_active, hloser_le⟩
  refine ⟨loser, hfocus, ?_, hloser_active⟩
  by_contra hloser_not_group
  have hminimal' : step.eliminatesMinimalTally :=
    ⟨hkind, loser, hfocus, hloser_active, hloser_le⟩
  have hloser_candidates : loser ∈ candidates :=
    hactive_subset_candidates hloser_active
  have hloser_outside : loser ∈ candidates \ group :=
    Finset.mem_sdiff.mpr ⟨hloser_candidates, hloser_not_group⟩
  have hfocus_ne :
      step.focus ≠ some loser :=
    strictSupportGroupRemovalSafety_outside_not_minimal_elimination_focus
      hsafety hinside hloser_outside hminimal' hinside_active
      hloser_active htally_inside (htally_outside loser hloser_outside)
  exact hfocus_ne hfocus

/-- A deterministic STV/RCV trace is a list of election steps. -/
structure STVTrace (Candidate : Type*) where
  steps : List (STVStep Candidate)

namespace STVTrace

/-- Every step in a trace has monotone active sets. -/
def activeMonotone {Candidate : Type*} (trace : STVTrace Candidate) : Prop :=
  ∀ step ∈ trace.steps, step.activeMonotone

@[simp] theorem activeMonotone_nil {Candidate : Type*} :
    activeMonotone ({ steps := [] } : STVTrace Candidate) := by
  intro step hstep
  simp at hstep

/--
Every elimination step in the trace removes a focused candidate from the named
group.
-/
def eliminationRemovesFromGroup {Candidate : Type*} [DecidableEq Candidate]
    (trace : STVTrace Candidate) (group : Finset Candidate) : Prop :=
  ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
    ∃ loser, step.focus = some loser ∧ loser ∈ group ∧
      loser ∈ step.beforeActive ∧
      step.afterActive = step.beforeActive.erase loser

/--
Every elimination step in the trace strictly decreases the number of active
candidates in the named group.
-/
def eliminationActiveGroupCardDecreases {Candidate : Type*}
    [DecidableEq Candidate]
    (trace : STVTrace Candidate) (group : Finset Candidate) : Prop :=
  ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
    (step.afterActive ∩ group).card <
      (step.beforeActive ∩ group).card

/--
Every elimination step in the trace removes exactly one active candidate from
the named group.
-/
def eliminationActiveGroupCardAddOneEq {Candidate : Type*}
    [DecidableEq Candidate]
    (trace : STVTrace Candidate) (group : Finset Candidate) : Prop :=
  ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
    (step.afterActive ∩ group).card + 1 =
      (step.beforeActive ∩ group).card

/--
The list of steps replays active sets from `startActive` to `terminalActive`.
This is the recursion kernel behind `STVTrace.replaysFrom`.
-/
def replayStepsFrom {Candidate : Type*} (steps : List (STVStep Candidate))
    (startActive terminalActive : Finset Candidate) : Prop :=
  match steps with
  | [] => terminalActive = startActive
  | step :: rest =>
      step.beforeActive = startActive ∧
        replayStepsFrom rest step.afterActive terminalActive

/--
The trace replays active sets from `startActive` to `terminalActive`: the first
step starts at `startActive`, each following step starts at the previous step's
post-active set, and the final post-active set is `terminalActive`.
-/
def replaysFrom {Candidate : Type*} (trace : STVTrace Candidate)
    (startActive terminalActive : Finset Candidate) : Prop :=
  replayStepsFrom trace.steps startActive terminalActive

/--
A replayed trace supplies a replay for every strict prefix ending at the
`beforeActive` set of the next step.
-/
theorem replayStepsFrom_take_get_beforeActive {Candidate : Type*}
    {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    (hreplay : replayStepsFrom steps startActive terminalActive)
    (i : Fin steps.length) :
    replayStepsFrom (steps.take i.1) startActive (steps.get i).beforeActive := by
  induction steps generalizing startActive with
  | nil =>
      exact Fin.elim0 i
  | cons step rest ih =>
      simp only [replayStepsFrom] at hreplay
      rcases hreplay with ⟨hbefore, hrest⟩
      cases i with
      | mk n hn =>
          cases n with
          | zero =>
              simp [replayStepsFrom, hbefore]
          | succ n =>
              have hn_rest : n < rest.length := by
                simpa using Nat.succ_lt_succ_iff.mp hn
              simp [replayStepsFrom, hbefore]
              exact ih hrest ⟨n, hn_rest⟩

/--
Trace-level wrapper for `replayStepsFrom_take_get_beforeActive`.
-/
theorem replaysFrom_take_get_beforeActive {Candidate : Type*}
    {trace : STVTrace Candidate}
    {startActive terminalActive : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (i : Fin trace.steps.length) :
    replayStepsFrom (trace.steps.take i.1) startActive
      (trace.steps.get i).beforeActive :=
  replayStepsFrom_take_get_beforeActive hreplay i

/-- Removing a focused candidate is an active-set monotone transition. -/
theorem activeMonotone_of_removesFocusedCandidate {Candidate : Type*}
    [DecidableEq Candidate] {step : STVStep Candidate}
    (hremove : step.removesFocusedCandidate) :
    step.activeMonotone := by
  rcases hremove with ⟨focused, _hfocus, hafter⟩
  intro candidate hcandidate
  rw [hafter] at hcandidate
  exact (Finset.mem_erase.mp hcandidate).2

/--
Along a replay whose steps are active-set monotone, the terminal active set is
contained in the initial active set.
-/
theorem terminalActive_subset_startActive_of_replayStepsFrom_activeMonotone
    {Candidate : Type*} {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    (hreplay : replayStepsFrom steps startActive terminalActive)
    (hmono : ∀ step, step ∈ steps → step.activeMonotone) :
    terminalActive ⊆ startActive := by
  induction steps generalizing startActive with
  | nil =>
      simp [replayStepsFrom] at hreplay
      intro candidate hcandidate
      simpa [hreplay] using hcandidate
  | cons step rest ih =>
      simp only [replayStepsFrom] at hreplay
      rcases hreplay with ⟨hbefore, hrest⟩
      have htail :
          terminalActive ⊆ step.afterActive :=
        ih hrest (fun step' hstep' => hmono step' (by simp [hstep']))
      intro candidate hcandidate
      have hbefore_mem : candidate ∈ step.beforeActive :=
        hmono step (by simp) (htail hcandidate)
      simpa [hbefore] using hbefore_mem

/--
Along a replay whose steps are active-set monotone, the terminal active set is
contained in every indexed step's pre-active set.
-/
theorem terminalActive_subset_beforeActive_of_replayStepsFrom_activeMonotone
    {Candidate : Type*} {steps : List (STVStep Candidate)}
    {startActive terminalActive : Finset Candidate}
    (hreplay : replayStepsFrom steps startActive terminalActive)
    (hmono : ∀ step, step ∈ steps → step.activeMonotone)
    (i : Fin steps.length) :
    terminalActive ⊆ (steps.get i).beforeActive := by
  induction steps generalizing startActive with
  | nil =>
      exact Fin.elim0 i
  | cons step rest ih =>
      simp only [replayStepsFrom] at hreplay
      rcases hreplay with ⟨hbefore, hrest⟩
      cases i with
      | mk n hn =>
          cases n with
          | zero =>
              have htail :
                  terminalActive ⊆ step.afterActive :=
                terminalActive_subset_startActive_of_replayStepsFrom_activeMonotone
                  hrest
                  (fun step' hstep' => hmono step' (by simp [hstep']))
              intro candidate hcandidate
              have hbefore_mem : candidate ∈ step.beforeActive :=
                hmono step (by simp) (htail hcandidate)
              simpa using hbefore_mem
          | succ n =>
              have hn_rest : n < rest.length := by
                simpa using Nat.succ_lt_succ_iff.mp hn
              simpa using
                ih hrest
                  (fun step' hstep' => hmono step' (by simp [hstep']))
                  ⟨n, hn_rest⟩

/--
At every indexed step of a replay whose steps are active-set monotone, the
step's pre-active set is contained in the initial active set.
-/
theorem beforeActive_subset_startActive_of_replaysFrom_activeMonotone
    {Candidate : Type*} {trace : STVTrace Candidate}
    {startActive terminalActive : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hmono : ∀ step, step ∈ trace.steps → step.activeMonotone)
    (i : Fin trace.steps.length) :
    (trace.steps.get i).beforeActive ⊆ startActive := by
  exact terminalActive_subset_startActive_of_replayStepsFrom_activeMonotone
    (replaysFrom_take_get_beforeActive hreplay i)
    (fun step hstep => hmono step (List.mem_of_mem_take hstep))

/--
At every indexed step of a replay whose steps remove their focused candidates,
the step's pre-active set is contained in the initial active set.
-/
theorem beforeActive_subset_startActive_of_replaysFrom_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    {startActive terminalActive : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hremove : ∀ step, step ∈ trace.steps → step.removesFocusedCandidate)
    (i : Fin trace.steps.length) :
    (trace.steps.get i).beforeActive ⊆ startActive := by
  exact beforeActive_subset_startActive_of_replaysFrom_activeMonotone
    hreplay
    (fun step hstep =>
      activeMonotone_of_removesFocusedCandidate (hremove step hstep))
    i

/--
At every indexed step of a replay whose steps remove focused candidates, the
terminal active set is contained in the step's pre-active set.
-/
theorem terminalActive_subset_beforeActive_of_replaysFrom_removesFocusedCandidate
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate}
    {startActive terminalActive : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hremove : ∀ step, step ∈ trace.steps → step.removesFocusedCandidate)
    (i : Fin trace.steps.length) :
    terminalActive ⊆ (trace.steps.get i).beforeActive := by
  exact terminalActive_subset_beforeActive_of_replayStepsFrom_activeMonotone
    hreplay
    (fun step hstep =>
      activeMonotone_of_removesFocusedCandidate (hremove step hstep))
    i

/--
A trace whose elimination steps remove focused group candidates has strictly
decreasing active-group cardinality at those elimination steps.
-/
theorem eliminationActiveGroupCardDecreases_of_eliminationRemovesFromGroup
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate} {group : Finset Candidate}
    (htrace : trace.eliminationRemovesFromGroup group) :
    trace.eliminationActiveGroupCardDecreases group := by
  intro step hstep hkind
  rcases htrace step hstep hkind with
    ⟨loser, hfocus, hloser_group, hloser_active, hafter⟩
  exact STVStep.card_afterActive_inter_lt_beforeActive_inter_of_removesFocusedCandidate
    ⟨loser, hfocus, hafter⟩ hfocus hloser_group hloser_active

/--
A trace whose elimination steps remove focused group candidates removes exactly
one active group candidate at those elimination steps.
-/
theorem eliminationActiveGroupCardAddOneEq_of_eliminationRemovesFromGroup
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate} {group : Finset Candidate}
    (htrace : trace.eliminationRemovesFromGroup group) :
    trace.eliminationActiveGroupCardAddOneEq group := by
  intro step hstep hkind
  rcases htrace step hstep hkind with
    ⟨loser, hfocus, hloser_group, hloser_active, hafter⟩
  exact STVStep.card_afterActive_inter_add_one_eq_beforeActive_inter_of_removesFocusedCandidate
    ⟨loser, hfocus, hafter⟩ hfocus hloser_group hloser_active

/--
If a replayed trace consists of eliminations and each elimination removes from
the named group, then the number of terminal active group candidates plus the
number of replayed steps is the number of initially active group candidates.
-/
theorem terminal_activeGroup_card_add_length_eq_start_card_of_replaysFrom
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate} {startActive terminalActive group : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (htrace : trace.eliminationRemovesFromGroup group) :
    (terminalActive ∩ group).card + trace.steps.length =
      (startActive ∩ group).card := by
  cases trace with
  | mk steps =>
      induction steps generalizing startActive with
      | nil =>
          simp [replaysFrom, replayStepsFrom] at hreplay ⊢
          rw [hreplay]
      | cons step rest ih =>
          simp only [replaysFrom, replayStepsFrom] at hreplay
          rcases hreplay with ⟨hbefore, hrest_replay⟩
          have hkind : step.kind = StepKind.eliminate :=
            hall_eliminate step (by simp)
          rcases htrace step (by simp) hkind with
            ⟨loser, hfocus, hloser_group, hloser_active, hafter⟩
          have hstep_card :
              (step.afterActive ∩ group).card + 1 =
                (step.beforeActive ∩ group).card :=
            STVStep.card_afterActive_inter_add_one_eq_beforeActive_inter_of_removesFocusedCandidate
              ⟨loser, hfocus, hafter⟩ hfocus hloser_group hloser_active
          have hrest_eliminate :
              ∀ step', step' ∈ rest → step'.kind = StepKind.eliminate := by
            intro step' hstep'
            exact hall_eliminate step' (by simp [hstep'])
          have hrest_trace :
              ({ steps := rest } : STVTrace Candidate).eliminationRemovesFromGroup
                group := by
            intro step' hstep' hkind'
            exact htrace step' (by simp [hstep']) hkind'
          have hrest_card :
              (terminalActive ∩ group).card + rest.length =
                (step.afterActive ∩ group).card :=
            ih hrest_replay hrest_eliminate hrest_trace
          calc
            (terminalActive ∩ group).card + (step :: rest).length
                = ((terminalActive ∩ group).card + rest.length) + 1 := by
                    simp [Nat.add_assoc]
            _ = (step.afterActive ∩ group).card + 1 := by
                    rw [hrest_card]
            _ = (step.beforeActive ∩ group).card := hstep_card
            _ = (startActive ∩ group).card := by rw [hbefore]

/--
If a replayed all-elimination trace removes from the named group for exactly
the number of initially active group candidates, no group candidate remains
active at the terminal state.
-/
theorem terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : STVTrace Candidate} {startActive terminalActive group : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (htrace : trace.eliminationRemovesFromGroup group)
    (hlength : trace.steps.length = (startActive ∩ group).card) :
    terminalActive ∩ group = ∅ := by
  have hsum :
      (terminalActive ∩ group).card + trace.steps.length =
        (startActive ∩ group).card :=
    terminal_activeGroup_card_add_length_eq_start_card_of_replaysFrom
      hreplay hall_eliminate htrace
  have hle :
      (terminalActive ∩ group).card + trace.steps.length ≤
        0 + trace.steps.length := by
    rw [hsum, hlength]
    simp
  have hcard_le_zero : (terminalActive ∩ group).card ≤ 0 :=
    Nat.le_of_add_le_add_right hle
  have hcard_zero : (terminalActive ∩ group).card = 0 :=
    Nat.eq_zero_of_le_zero hcard_le_zero
  exact Finset.card_eq_zero.mp hcard_zero

end STVTrace

/--
Strict-support group-removal trace bridge: along any trace whose elimination
steps choose and remove minimum-tally active candidates, the safety inequalities
force every certified elimination step to remove a focused group candidate.
-/
theorem strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {trace : STVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              Ballot.strictSupportCount voters ballots group
                (candidates \ group) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            Ballot.strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside) :
    trace.eliminationRemovesFromGroup group := by
  intro step hstep hkind
  rcases hgroup_active step hstep hkind with
    ⟨inside, hinside, hinside_active⟩
  rcases strictSupportGroupRemovalSafety_minimal_elimination_focus_mem_group
      hsafety hinside (hminimal step hstep hkind) hinside_active
      (hactive_subset_candidates step hstep hkind)
      (htally_inside step hstep hkind inside hinside hinside_active)
      (fun outside houtside =>
        htally_outside step hstep hkind inside hinside hinside_active
          outside houtside) with
    ⟨loser, hfocus, hloser_group, hloser_active⟩
  rcases hremove step hstep hkind with
    ⟨removed, hremoved_focus, hafter⟩
  have hremoved_eq_loser : removed = loser :=
    Option.some.inj (hremoved_focus.symm.trans hfocus)
  subst removed
  exact ⟨loser, hfocus, hloser_group, hloser_active, hafter⟩

/--
Strict-support group-removal trace bridge: along any trace whose elimination
steps choose and remove minimum-tally active candidates, the safety inequalities
force every certified elimination step to remove a focused group candidate.
-/
theorem strictSupportGroupRemovalSafety_trace_elimination_focus_mem_group
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {trace : STVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              Ballot.strictSupportCount voters ballots group
                (candidates \ group) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            Ballot.strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside) :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∃ loser, step.focus = some loser ∧ loser ∈ group ∧
        loser ∈ step.beforeActive ∧
        step.afterActive = step.beforeActive.erase loser := by
  exact strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup
    hsafety hminimal hremove hgroup_active hactive_subset_candidates
    htally_inside htally_outside

/--
Strict-support group-removal trace bridge, cardinality form: every certified
minimum-tally elimination step strictly decreases the number of active
candidates in the removable group.
-/
theorem strictSupportGroupRemovalSafety_trace_elimination_activeGroup_card_decreases
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {trace : STVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              Ballot.strictSupportCount voters ballots group
                (candidates \ group) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            Ballot.strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside) :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      (step.afterActive ∩ group).card <
        (step.beforeActive ∩ group).card := by
  exact STVTrace.eliminationActiveGroupCardDecreases_of_eliminationRemovesFromGroup
    (strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup
      hsafety (trace := trace) hminimal hremove hgroup_active
      hactive_subset_candidates htally_inside htally_outside
    )

/--
Strict-support group-removal trace bridge, exact cardinality form: every
certified minimum-tally elimination step removes exactly one active candidate
from the removable group.
-/
theorem strictSupportGroupRemovalSafety_trace_elimination_activeGroup_card_add_one_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates group budget quota)
    {trace : STVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              Ballot.strictSupportCount voters ballots group
                (candidates \ group) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            Ballot.strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside) :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      (step.afterActive ∩ group).card + 1 =
        (step.beforeActive ∩ group).card := by
  exact STVTrace.eliminationActiveGroupCardAddOneEq_of_eliminationRemovesFromGroup
    (strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup
      hsafety (trace := trace) hminimal hremove hgroup_active
      hactive_subset_candidates htally_inside htally_outside
    )

/--
Source-shaped strict-support trace certificate.

This is the paper-neutral package behind the Algorithm 6 / Algorithm 2 replay
arguments: a compact strict-support group-removal condition plus a concrete
candidate-level trace whose elimination steps choose minimum-tally focused
candidates and whose tallies agree with the strict-support quantities.
-/
structure StrictSupportGroupRemovalTraceCertificate
    (Voter Candidate : Type*) [DecidableEq Candidate] where
  voters : Finset Voter
  ballots : Voter → Ballot Candidate
  candidates : Finset Candidate
  group : Finset Candidate
  budget : ℕ
  quota : ℕ
  trace : STVTrace Candidate
  condition :
    strictSupportGroupRemovalCondition
      voters ballots candidates group budget quota
  minimal_eliminations :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      step.eliminatesMinimalTally
  focused_eliminations_remove_focus :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      step.removesFocusedCandidate
  group_active_at_elimination :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive
  active_subset_candidates :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      step.beforeActive ⊆ candidates
  tally_inside :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        step.tally inside =
          budget +
            Ballot.strictSupportCount voters ballots group
              (candidates \ group) inside
  tally_outside :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
      ∀ outside, outside ∈ candidates \ group →
        step.tally outside =
          Ballot.strictSupportCount voters ballots
            (insert outside (group.erase inside)) (∅ : Finset Candidate)
            outside

namespace StrictSupportGroupRemovalTraceCertificate

/-- The compact condition supplies the separated safety inequalities. -/
theorem safety {Voter Candidate : Type*} [DecidableEq Candidate]
    (cert : StrictSupportGroupRemovalTraceCertificate Voter Candidate) :
    strictSupportGroupRemovalSafety
      cert.voters cert.ballots cert.candidates cert.group
      cert.budget cert.quota := by
  exact strictSupportGroupRemovalSafety_of_condition cert.condition

/-- The certified trace removes focused candidates from the removable group. -/
theorem eliminationRemovesFromGroup {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (cert : StrictSupportGroupRemovalTraceCertificate Voter Candidate) :
    cert.trace.eliminationRemovesFromGroup cert.group := by
  exact strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup
    (safety cert)
    cert.minimal_eliminations
    cert.focused_eliminations_remove_focus
    cert.group_active_at_elimination
    cert.active_subset_candidates
    cert.tally_inside
    cert.tally_outside

/-- Every certified elimination step strictly decreases active group size. -/
theorem eliminationActiveGroupCardDecreases {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (cert : StrictSupportGroupRemovalTraceCertificate Voter Candidate) :
    cert.trace.eliminationActiveGroupCardDecreases cert.group := by
  exact STVTrace.eliminationActiveGroupCardDecreases_of_eliminationRemovesFromGroup
    (eliminationRemovesFromGroup cert)

/-- Every certified elimination step removes exactly one active group member. -/
theorem eliminationActiveGroupCardAddOneEq {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (cert : StrictSupportGroupRemovalTraceCertificate Voter Candidate) :
    cert.trace.eliminationActiveGroupCardAddOneEq cert.group := by
  exact STVTrace.eliminationActiveGroupCardAddOneEq_of_eliminationRemovesFromGroup
    (eliminationRemovesFromGroup cert)

/--
Replay accounting for a certified all-elimination prefix: terminal active group
count plus prefix length equals initial active group count.
-/
theorem terminal_activeGroup_card_add_length_eq {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (cert : StrictSupportGroupRemovalTraceCertificate Voter Candidate)
    {startActive terminalActive : Finset Candidate}
    (hreplay : cert.trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ cert.trace.steps → step.kind = StepKind.eliminate) :
    (terminalActive ∩ cert.group).card + cert.trace.steps.length =
      (startActive ∩ cert.group).card := by
  exact STVTrace.terminal_activeGroup_card_add_length_eq_start_card_of_replaysFrom
    hreplay hall_eliminate (eliminationRemovesFromGroup cert)

/--
If the certified all-elimination replay prefix is long enough to remove every
initial active group member, no group member remains terminally active.
-/
theorem terminal_activeGroup_empty {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (cert : StrictSupportGroupRemovalTraceCertificate Voter Candidate)
    {startActive terminalActive : Finset Candidate}
    (hreplay : cert.trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ cert.trace.steps → step.kind = StepKind.eliminate)
    (hlength :
      cert.trace.steps.length = (startActive ∩ cert.group).card) :
    terminalActive ∩ cert.group = ∅ := by
  exact STVTrace.terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
    hreplay hall_eliminate (eliminationRemovesFromGroup cert) hlength

end StrictSupportGroupRemovalTraceCertificate

/--
Round-rank active-set invariant: candidates whose exit rank is strictly after
the current round rank are active in that round.

This is intentionally independent of a particular quota or transfer convention;
downstream replay proofs can instantiate `roundRank` from their deterministic
trace.
-/
def ActiveUntilExitRank {Candidate Round : Type*}
    (active : Round → Finset Candidate)
    (roundRank : Round → ℕ)
    (exitRank : Candidate → ℕ) : Prop :=
  ∀ {candidate round}, roundRank round < exitRank candidate →
    candidate ∈ active round

namespace ActiveUntilExitRank

/--
If a round is before one candidate's exit rank, then any candidate with weakly
later exit rank is active in that round.
-/
theorem active_of_rank_lt_of_le {Candidate Round : Type*}
    {active : Round → Finset Candidate}
    {roundRank : Round → ℕ} {exitRank : Candidate → ℕ}
    (hactive : ActiveUntilExitRank active roundRank exitRank)
    {candidate other : Candidate} {round : Round}
    (hround_lt : roundRank round < exitRank candidate)
    (hle : exitRank candidate ≤ exitRank other) :
    other ∈ active round :=
  hactive (lt_of_lt_of_le hround_lt hle)

end ActiveUntilExitRank

end Voting
end SocialChoice
end EconCSLib
