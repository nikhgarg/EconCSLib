import AccuracyDiversity.Representation

namespace AccuracyDiversity

namespace ConsumptionModel

/-- Objective values attainable by allocations of exactly `N` items. -/
def attainableValuesAtTotal {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) : Set ℝ :=
  {r | ∃ a : CountAllocation T, FeasibleAtTotal N a ∧ r = M.objective a}

/-- Supremal objective value among allocations of size `N`. -/
noncomputable def optimalValueAtTotal {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) : ℝ :=
  sSup (attainableValuesAtTotal M N)

/-- The set of optimal allocations of size `N`. -/
def optimalAllocationsAtTotal {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) : Set (CountAllocation T) :=
  {a | M.IsOptimalAtTotal N a}

/--
A theorem target: every optimal allocation at size `N` approximately matches a
specified γ-homogeneity profile.
-/
noncomputable def ApproxHomogeneityOfOptima {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) (G : GammaHomogeneityProfile T) (ε : ℝ) : Prop :=
  ∀ a : CountAllocation T, M.IsOptimalAtTotal N a → G.Approx a ε

/--
A theorem target for asymptotic statements: there exists an error schedule tending to zero
such that all optimal allocations approximately match the profile.

This is intentionally only a scaffold; a serious proof should replace `TendsToZero` with
mathlib's filter-based limit statement once the order-statistic branch is started.
-/
def AsymptoticHomogeneityTarget {T : ℕ}
    (Mseq : ℕ → ConsumptionModel T) (G : GammaHomogeneityProfile T)
    (TendsToZero : (ℕ → ℝ) → Prop) : Prop :=
  ∃ ε : ℕ → ℝ,
    TendsToZero ε ∧ ∀ N a, (Mseq N).IsOptimalAtTotal N a → G.Approx a (ε N)

end ConsumptionModel
end AccuracyDiversity
