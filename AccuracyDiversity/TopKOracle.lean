import AccuracyDiversity.Basic

namespace AccuracyDiversity

/--
Oracle for the expected value of the best `ℓ` consumed items among `q` recommendations
of a single type.

This file intentionally keeps order statistics abstract. It is the right interface for
Theorem 1 of the paper: later files can instantiate this oracle for finite-discrete,
bounded, exponential-tail, or heavy-tail conditional item-value distributions.
-/
structure TopKValueOracle (T : ℕ) where
  expectedTopSum : ℕ → ItemType T → ℕ → ℝ

namespace TopKValueOracle

/-- Build a consumption model for a fixed consumption constraint `ℓ`. -/
def toConsumptionModel {T : ℕ}
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (ℓ : ℕ) : ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := fun t q => O.expectedTopSum ℓ t q

/-- Marginal top-`ℓ` value from adding one more recommendation of type `t`. -/
noncomputable def marginalTopK {T : ℕ}
    (O : TopKValueOracle T) (ℓ : ℕ) (t : ItemType T) (q : ℕ) : ℝ :=
  O.expectedTopSum ℓ t (q + 1) - O.expectedTopSum ℓ t q

/-- Diminishing returns for a fixed consumption level `ℓ`. -/
def HasDiminishingReturnsAt {T : ℕ}
    (O : TopKValueOracle T) (ℓ : ℕ) : Prop :=
  ∀ t q, marginalTopK O ℓ t (q + 1) ≤ marginalTopK O ℓ t q

@[simp] theorem toConsumptionModel_objective {T : ℕ}
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (ℓ : ℕ)
    (a : CountAllocation T) :
    (O.toConsumptionModel likelihood ℓ).objective a =
      DecisionCore.Allocation.objective a likelihood (fun t q => O.expectedTopSum ℓ t q) := rfl

@[simp] theorem marginalTopK_apply {T : ℕ}
    (O : TopKValueOracle T) (ℓ : ℕ) (t : ItemType T) (q : ℕ) :
    marginalTopK O ℓ t q = O.expectedTopSum ℓ t (q + 1) - O.expectedTopSum ℓ t q := rfl

end TopKValueOracle
end AccuracyDiversity
