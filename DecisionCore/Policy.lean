import DecisionCore.FiniteExpectation

open scoped BigOperators

namespace DecisionCore

/-- A randomized policy from states/agents `α` to actions `β`. -/
abbrev Policy (α β : Type*) := α → PMF β

/-- Finite maximum of a real-valued function on a nonempty finite type. -/
noncomputable def finiteMax {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : ℝ :=
  (Finset.univ : Finset α).sup' Finset.univ_nonempty f

/-- Finite minimum of a real-valued function on a nonempty finite type. -/
noncomputable def finiteMin {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : ℝ :=
  (Finset.univ : Finset α).inf' Finset.univ_nonempty f

namespace Policy

/-- Deterministic policy induced by a pure action selector. -/
noncomputable def pure (f : α → β) : Policy α β :=
  fun a => PMF.pure (f a)

/-- Expected score received by a single agent/state under policy `ρ`. -/
noncomputable def agentScore {α β : Type*}
    [Fintype β] [DecidableEq β]
    (ρ : Policy α β) (score : α → β → ℝ) (a : α) : ℝ :=
  pmfExp (ρ a) (score a)

/-- Expected score after sampling an agent/state from `μ` and acting via `ρ`. -/
noncomputable def aggregateScore {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ρ : Policy α β) (score : α → β → ℝ) : ℝ :=
  pmfExp μ (fun a => agentScore ρ score a)

/-- Agent score normalized by an externally supplied benchmark. -/
noncomputable def normalizedAgentScore {α β : Type*}
    [Fintype β] [DecidableEq β]
    (benchmark : α → ℝ) (ρ : Policy α β) (score : α → β → ℝ) (a : α) : ℝ :=
  agentScore ρ score a / benchmark a

/-- The finite support of the action distribution for agent/state `a`. -/
noncomputable def actionSupport {α β : Type*}
    [Fintype β] [DecidableEq β]
    (ρ : Policy α β) (a : α) : Finset β :=
  Finset.univ.filter fun b => ρ a b ≠ 0

@[simp] theorem mem_actionSupport {α β : Type*}
    [Fintype β] [DecidableEq β]
    (ρ : Policy α β) (a : α) (b : β) :
    b ∈ actionSupport ρ a ↔ ρ a b ≠ 0 := by
  simp [actionSupport]

/-- All state-action pairs used with positive probability by a policy. -/
noncomputable def activePairs {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : Policy α β) : Finset (α × β) :=
  Finset.univ.filter fun p => ρ p.1 p.2 ≠ 0

@[simp] theorem mem_activePairs {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : Policy α β) (p : α × β) :
    p ∈ activePairs ρ ↔ ρ p.1 p.2 ≠ 0 := by
  simp [activePairs]

/-- Cardinality of the positive-support state-action pairs used by `ρ`. -/
noncomputable def activePairsCard {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : Policy α β) : ℕ :=
  (activePairs ρ).card

/-- Actions used by more than one distinct state/agent. -/
noncomputable def multiAssignedActions {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : Policy α β) : Finset β :=
  Finset.univ.filter fun b => ∃ a a', a ≠ a' ∧ ρ a b ≠ 0 ∧ ρ a' b ≠ 0

@[simp] theorem mem_multiAssignedActions {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : Policy α β) (b : β) :
    b ∈ multiAssignedActions ρ ↔ ∃ a a', a ≠ a' ∧ ρ a b ≠ 0 ∧ ρ a' b ≠ 0 := by
  simp [multiAssignedActions]

end Policy
end DecisionCore

namespace DecisionCore
namespace Policy

@[simp] theorem agentScore_pure {α β : Type*}
    [Fintype β] [DecidableEq β]
    (choose : α → β) (score : α → β → ℝ) (a : α) :
    agentScore (pure choose) score a = score a (choose a) := by
  simp [agentScore, pure]

/-- Aggregate score under a deterministic policy is the expectation of the selected scores. -/
theorem aggregateScore_pure {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (choose : α → β) (score : α → β → ℝ) :
    aggregateScore μ (pure choose) score = pmfExp μ (fun a => score a (choose a)) := by
  simp [aggregateScore]

/-- Agent scores are extensional in the action distribution for that agent. -/
theorem agentScore_congr_policy {α β : Type*}
    [Fintype β] [DecidableEq β]
    {ρ ρ' : Policy α β} {score : α → β → ℝ} {a : α}
    (h : ρ a = ρ' a) :
    agentScore ρ score a = agentScore ρ' score a := by
  simp [agentScore, h]

/-- Agent scores are extensional in the score row for that agent. -/
theorem agentScore_congr_score {α β : Type*}
    [Fintype β] [DecidableEq β]
    (ρ : Policy α β) {score score' : α → β → ℝ} {a : α}
    (h : score a = score' a) :
    agentScore ρ score a = agentScore ρ score' a := by
  simp [agentScore, h]

end Policy
end DecisionCore
