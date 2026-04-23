import DecisionCore.Policy

namespace DecisionCore
namespace Policy

/-- Lift a class-level policy along a quotient/classification map `τ : α → κ`. -/
def liftAlong {α κ β : Type*} (τ : α → κ) (ρ : Policy κ β) : Policy α β :=
  fun a => ρ (τ a)

/-- A policy on `α` is classwise if it is constant on fibers of `τ`. -/
def IsClasswise {α κ β : Type*} (τ : α → κ) (ρ : Policy α β) : Prop :=
  ∀ a a', τ a = τ a' → ρ a = ρ a'

/-- The set of policies that are constant on fibers of `τ`. -/
def ClasswisePolicies {α κ β : Type*} (τ : α → κ) : Set (Policy α β) :=
  {ρ | IsClasswise τ ρ}

@[simp] theorem liftAlong_apply {α κ β : Type*}
    (τ : α → κ) (ρ : Policy κ β) (a : α) :
    liftAlong τ ρ a = ρ (τ a) := rfl

@[simp] theorem mem_classwisePolicies {α κ β : Type*}
    (τ : α → κ) (ρ : Policy α β) :
    ρ ∈ ClasswisePolicies τ ↔ IsClasswise τ ρ := Iff.rfl

theorem liftAlong_isClasswise {α κ β : Type*}
    (τ : α → κ) (ρ : Policy κ β) :
    IsClasswise τ (liftAlong τ ρ) := by
  intro a a' h
  simp [liftAlong, h]

/--
Chosen representatives for the fibers of `τ`. This is the exact data needed to
turn a classwise policy on `α` into a policy on the class space `κ`.
-/
structure FiberRepresentatives {α κ : Type*} (τ : α → κ) where
  repr : κ → α
  repr_spec : ∀ k, τ (repr k) = k

/-- Descend a policy on `α` to the class space `κ` by evaluating it on representatives. -/
def descendAlong {α κ β : Type*} {τ : α → κ}
    (reps : FiberRepresentatives τ) (ρ : Policy α β) : Policy κ β :=
  fun k => ρ (reps.repr k)

@[simp] theorem descendAlong_apply {α κ β : Type*} {τ : α → κ}
    (reps : FiberRepresentatives τ) (ρ : Policy α β) (k : κ) :
    descendAlong reps ρ k = ρ (reps.repr k) := rfl

@[simp] theorem descendAlong_liftAlong {α κ β : Type*}
    (τ : α → κ) (reps : FiberRepresentatives τ) (ρ : Policy κ β) :
    descendAlong reps (liftAlong τ ρ) = ρ := by
  funext k
  simp [descendAlong, liftAlong, reps.repr_spec]

theorem liftAlong_descendAlong_eq_of_isClasswise {α κ β : Type*}
    (τ : α → κ) (reps : FiberRepresentatives τ) (ρ : Policy α β)
    (hρ : IsClasswise τ ρ) :
    liftAlong τ (descendAlong reps ρ) = ρ := by
  funext a
  exact hρ (reps.repr (τ a)) a (reps.repr_spec (τ a))

/--
A policy on `α` is classwise exactly when it comes from lifting some policy on `κ`.
The only extra input needed is one representative in each fiber of `τ`.
-/
theorem isClasswise_iff_exists_liftAlong {α κ β : Type*}
    (τ : α → κ) (reps : FiberRepresentatives τ) (ρ : Policy α β) :
    IsClasswise τ ρ ↔ ∃ ρκ : Policy κ β, liftAlong τ ρκ = ρ := by
  constructor
  · intro hρ
    refine ⟨descendAlong reps ρ, ?_⟩
    exact liftAlong_descendAlong_eq_of_isClasswise τ reps ρ hρ
  · rintro ⟨ρκ, hEq⟩
    rw [← hEq]
    exact liftAlong_isClasswise τ ρκ

end Policy
end DecisionCore
