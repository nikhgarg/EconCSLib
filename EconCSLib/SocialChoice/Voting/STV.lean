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
- `StepKind`
- `STVStep`
- `STVTrace`
- `STVStep.activeMonotone`
- `ActiveUntilExitRank`
-/

namespace EconCSLib
namespace SocialChoice
namespace Voting

/-- Droop-style integer quota used by many STV presentations. -/
def STVQuota (seats voters : ℕ) : ℕ :=
  voters / (seats + 1) + 1

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

end STVStep

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

end STVTrace

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
