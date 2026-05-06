import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

namespace EconCSLib
namespace Optimization

/-!
# Optimization Certificates

Reusable certificate wrappers for finite, LP, allocation, and policy
optimization arguments.

## Main declarations

- `IsMaximizerOn`, `IsMinimizerOn`: optimality on an explicit feasible set.
- `UpperBoundCertificate`: a candidate value plus a universal upper bound.
- `LowerBoundCertificate`: a candidate value plus a universal lower bound.
- `StrictUpperBoundCertificate`, `StrictLowerBoundCertificate`: uniqueness
  variants based on strict bounds away from the candidate.
-/

/-- Objective values achieved by feasible points. -/
def feasibleValueSet {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) : Set ℝ :=
  {v | ∃ x, feasible x ∧ v = objective x}

/-- `x` maximizes `objective` over the feasible region. -/
def IsMaximizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → objective y ≤ objective x

/-- `x` minimizes `objective` over the feasible region. -/
def IsMinimizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → objective x ≤ objective y

/-- Strict sufficient condition for a unique maximizer. -/
def IsStrictMaximizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → y ≠ x → objective y < objective x

/-- Strict sufficient condition for a unique minimizer. -/
def IsStrictMinimizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → y ≠ x → objective x < objective y

namespace IsMaximizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

/-- A maximizer is feasible. -/
theorem isFeasible (h : IsMaximizerOn feasible objective x) : feasible x :=
  h.1

/-- A maximizer upper-bounds every feasible objective value. -/
theorem le (h : IsMaximizerOn feasible objective x)
    (hy : feasible y) : objective y ≤ objective x :=
  h.2 y hy

/-- No feasible point strictly improves on a maximizer. -/
theorem not_lt (h : IsMaximizerOn feasible objective x)
    (hy : feasible y) : ¬ objective x < objective y :=
  not_lt_of_ge (h.le hy)

/-- The objective value of a maximizer is in the feasible value set. -/
theorem value_mem_feasibleValueSet
    (h : IsMaximizerOn feasible objective x) :
    objective x ∈ feasibleValueSet feasible objective :=
  ⟨x, h.isFeasible, rfl⟩

/-- Any two maximizers have the same objective value. -/
theorem objective_eq_of_isMaximizerOn
    (hx : IsMaximizerOn feasible objective x)
    (hy : IsMaximizerOn feasible objective y) :
    objective x = objective y :=
  le_antisymm (hy.le hx.isFeasible) (hx.le hy.isFeasible)

end IsMaximizerOn

namespace IsMinimizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

/-- A minimizer is feasible. -/
theorem isFeasible (h : IsMinimizerOn feasible objective x) : feasible x :=
  h.1

/-- A minimizer lower-bounds every feasible objective value. -/
theorem le (h : IsMinimizerOn feasible objective x)
    (hy : feasible y) : objective x ≤ objective y :=
  h.2 y hy

/-- No feasible point strictly improves on a minimizer. -/
theorem not_lt (h : IsMinimizerOn feasible objective x)
    (hy : feasible y) : ¬ objective y < objective x :=
  not_lt_of_ge (h.le hy)

/-- The objective value of a minimizer is in the feasible value set. -/
theorem value_mem_feasibleValueSet
    (h : IsMinimizerOn feasible objective x) :
    objective x ∈ feasibleValueSet feasible objective :=
  ⟨x, h.isFeasible, rfl⟩

/-- Any two minimizers have the same objective value. -/
theorem objective_eq_of_isMinimizerOn
    (hx : IsMinimizerOn feasible objective x)
    (hy : IsMinimizerOn feasible objective y) :
    objective x = objective y :=
  le_antisymm (hx.le hy.isFeasible) (hy.le hx.isFeasible)

end IsMinimizerOn

namespace IsStrictMaximizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

/-- A strict maximizer is feasible. -/
theorem isFeasible (h : IsStrictMaximizerOn feasible objective x) :
    feasible x :=
  h.1

/-- Every other feasible point has strictly smaller value than a strict maximizer. -/
theorem lt_of_ne (h : IsStrictMaximizerOn feasible objective x)
    (hy : feasible y) (hne : y ≠ x) : objective y < objective x :=
  h.2 y hy hne

/-- Strict maximization implies weak maximization. -/
theorem isMaximizerOn
    (h : IsStrictMaximizerOn feasible objective x) :
    IsMaximizerOn feasible objective x := by
  constructor
  · exact h.isFeasible
  · intro y hy
    by_cases hxy : y = x
    · subst y
      exact le_rfl
    · exact le_of_lt (h.lt_of_ne hy hxy)

/-- A strict maximizer is the only weak maximizer. -/
theorem eq_of_isMaximizerOn
    (h : IsStrictMaximizerOn feasible objective x)
    (hy : IsMaximizerOn feasible objective y) : y = x := by
  by_contra hne
  exact hy.not_lt h.isFeasible (h.lt_of_ne hy.isFeasible hne)

end IsStrictMaximizerOn

namespace IsStrictMinimizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

/-- A strict minimizer is feasible. -/
theorem isFeasible (h : IsStrictMinimizerOn feasible objective x) :
    feasible x :=
  h.1

/-- Every other feasible point has strictly larger value than a strict minimizer. -/
theorem lt_of_ne (h : IsStrictMinimizerOn feasible objective x)
    (hy : feasible y) (hne : y ≠ x) : objective x < objective y :=
  h.2 y hy hne

/-- Strict minimization implies weak minimization. -/
theorem isMinimizerOn
    (h : IsStrictMinimizerOn feasible objective x) :
    IsMinimizerOn feasible objective x := by
  constructor
  · exact h.isFeasible
  · intro y hy
    by_cases hxy : y = x
    · subst y
      exact le_rfl
    · exact le_of_lt (h.lt_of_ne hy hxy)

/-- A strict minimizer is the only weak minimizer. -/
theorem eq_of_isMinimizerOn
    (h : IsStrictMinimizerOn feasible objective x)
    (hy : IsMinimizerOn feasible objective y) : y = x := by
  by_contra hne
  exact hy.not_lt h.isFeasible (h.lt_of_ne hy.isFeasible hne)

end IsStrictMinimizerOn

/--
A maximization certificate: the candidate is feasible, has value `value`, and
`value` upper-bounds every feasible objective value.
-/
structure UpperBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  upper_bound : ∀ y, feasible y → objective y ≤ value

/--
A minimization certificate: the candidate is feasible, has value `value`, and
`value` lower-bounds every feasible objective value.
-/
structure LowerBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  lower_bound : ∀ y, feasible y → value ≤ objective y

/-- A strict maximization certificate proving uniqueness by strict upper bounds. -/
structure StrictUpperBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  strict_upper_bound : ∀ y, feasible y → y ≠ candidate → objective y < value

/-- A strict minimization certificate proving uniqueness by strict lower bounds. -/
structure StrictLowerBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  strict_lower_bound : ∀ y, feasible y → y ≠ candidate → value < objective y

namespace UpperBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

/-- The certified value is achieved by a feasible point. -/
theorem value_mem_feasibleValueSet
    (cert : UpperBoundCertificate feasible objective value) :
    value ∈ feasibleValueSet feasible objective := by
  exact ⟨cert.candidate, cert.candidate_feasible, cert.candidate_value.symm⟩

/-- Every feasible value is at most the certified value. -/
theorem le_value_of_mem_feasibleValueSet
    (cert : UpperBoundCertificate feasible objective value)
    {v : ℝ} (hv : v ∈ feasibleValueSet feasible objective) : v ≤ value := by
  rcases hv with ⟨x, hx, hvx⟩
  rw [hvx]
  exact cert.upper_bound x hx

/-- The feasible value set is bounded above by the certified value. -/
theorem bddAbove_feasibleValueSet
    (cert : UpperBoundCertificate feasible objective value) :
    BddAbove (feasibleValueSet feasible objective) :=
  ⟨value, fun _v hv => cert.le_value_of_mem_feasibleValueSet hv⟩

/-- A maximization certificate proves candidate optimality. -/
theorem isMaximizerOn
    (cert : UpperBoundCertificate feasible objective value) :
    IsMaximizerOn feasible objective cert.candidate := by
  constructor
  · exact cert.candidate_feasible
  · intro y hy
    simpa [cert.candidate_value] using cert.upper_bound y hy

/-- Any maximizer has the certified objective value. -/
theorem objective_eq_value_of_isMaximizerOn
    (cert : UpperBoundCertificate feasible objective value)
    {y : α} (hy : IsMaximizerOn feasible objective y) :
    objective y = value := by
  have hle : objective y ≤ value := cert.upper_bound y hy.isFeasible
  have hge : value ≤ objective y := by
    rw [← cert.candidate_value]
    exact hy.le cert.candidate_feasible
  exact le_antisymm hle hge

end UpperBoundCertificate

namespace LowerBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

/-- The certified value is achieved by a feasible point. -/
theorem value_mem_feasibleValueSet
    (cert : LowerBoundCertificate feasible objective value) :
    value ∈ feasibleValueSet feasible objective := by
  exact ⟨cert.candidate, cert.candidate_feasible, cert.candidate_value.symm⟩

/-- Every feasible value is at least the certified value. -/
theorem value_le_of_mem_feasibleValueSet
    (cert : LowerBoundCertificate feasible objective value)
    {v : ℝ} (hv : v ∈ feasibleValueSet feasible objective) : value ≤ v := by
  rcases hv with ⟨x, hx, hvx⟩
  rw [hvx]
  exact cert.lower_bound x hx

/-- The feasible value set is bounded below by the certified value. -/
theorem bddBelow_feasibleValueSet
    (cert : LowerBoundCertificate feasible objective value) :
    BddBelow (feasibleValueSet feasible objective) :=
  ⟨value, fun _v hv => cert.value_le_of_mem_feasibleValueSet hv⟩

/-- A minimization certificate proves candidate optimality. -/
theorem isMinimizerOn
    (cert : LowerBoundCertificate feasible objective value) :
    IsMinimizerOn feasible objective cert.candidate := by
  constructor
  · exact cert.candidate_feasible
  · intro y hy
    simpa [cert.candidate_value] using cert.lower_bound y hy

/-- Any minimizer has the certified objective value. -/
theorem objective_eq_value_of_isMinimizerOn
    (cert : LowerBoundCertificate feasible objective value)
    {y : α} (hy : IsMinimizerOn feasible objective y) :
    objective y = value := by
  have hge : value ≤ objective y := cert.lower_bound y hy.isFeasible
  have hle : objective y ≤ value := by
    rw [← cert.candidate_value]
    exact hy.le cert.candidate_feasible
  exact le_antisymm hle hge

end LowerBoundCertificate

namespace StrictUpperBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

/-- Forget strictness to obtain an ordinary maximization certificate. -/
def toUpperBoundCertificate
    (cert : StrictUpperBoundCertificate feasible objective value) :
    UpperBoundCertificate feasible objective value where
  candidate := cert.candidate
  candidate_feasible := cert.candidate_feasible
  candidate_value := cert.candidate_value
  upper_bound := by
    intro y hy
    by_cases h : y = cert.candidate
    · subst y
      exact le_of_eq cert.candidate_value
    · exact le_of_lt (cert.strict_upper_bound y hy h)

/-- A strict maximization certificate proves strict candidate optimality. -/
theorem isStrictMaximizerOn
    (cert : StrictUpperBoundCertificate feasible objective value) :
    IsStrictMaximizerOn feasible objective cert.candidate := by
  constructor
  · exact cert.candidate_feasible
  · intro y hy hne
    simpa [cert.candidate_value] using cert.strict_upper_bound y hy hne

/-- A strict maximization certificate also proves weak candidate optimality. -/
theorem isMaximizerOn
    (cert : StrictUpperBoundCertificate feasible objective value) :
    IsMaximizerOn feasible objective cert.candidate :=
  cert.toUpperBoundCertificate.isMaximizerOn

/-- A strict maximization certificate identifies every weak maximizer. -/
theorem eq_of_isMaximizerOn
    (cert : StrictUpperBoundCertificate feasible objective value)
    {y : α} (hy : IsMaximizerOn feasible objective y) : y = cert.candidate :=
  cert.isStrictMaximizerOn.eq_of_isMaximizerOn hy

end StrictUpperBoundCertificate

namespace StrictLowerBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

/-- Forget strictness to obtain an ordinary minimization certificate. -/
def toLowerBoundCertificate
    (cert : StrictLowerBoundCertificate feasible objective value) :
    LowerBoundCertificate feasible objective value where
  candidate := cert.candidate
  candidate_feasible := cert.candidate_feasible
  candidate_value := cert.candidate_value
  lower_bound := by
    intro y hy
    by_cases h : y = cert.candidate
    · subst y
      exact le_of_eq cert.candidate_value.symm
    · exact le_of_lt (cert.strict_lower_bound y hy h)

/-- A strict minimization certificate proves strict candidate optimality. -/
theorem isStrictMinimizerOn
    (cert : StrictLowerBoundCertificate feasible objective value) :
    IsStrictMinimizerOn feasible objective cert.candidate := by
  constructor
  · exact cert.candidate_feasible
  · intro y hy hne
    simpa [cert.candidate_value] using cert.strict_lower_bound y hy hne

/-- A strict minimization certificate also proves weak candidate optimality. -/
theorem isMinimizerOn
    (cert : StrictLowerBoundCertificate feasible objective value) :
    IsMinimizerOn feasible objective cert.candidate :=
  cert.toLowerBoundCertificate.isMinimizerOn

/-- A strict minimization certificate identifies every weak minimizer. -/
theorem eq_of_isMinimizerOn
    (cert : StrictLowerBoundCertificate feasible objective value)
    {y : α} (hy : IsMinimizerOn feasible objective y) : y = cert.candidate :=
  cert.isStrictMinimizerOn.eq_of_isMinimizerOn hy

end StrictLowerBoundCertificate

end Optimization
end EconCSLib
