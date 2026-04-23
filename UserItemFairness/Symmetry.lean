import UserItemFairness.Optimization
import DecisionCore.Classwise

open DecisionCore

namespace UserItemFairness

abbrev UserType (K : ℕ) := Fin K
abbrev TypePolicy (K n : ℕ) := DecisionCore.Policy (UserType K) (Item n)

namespace RecommendationModel

/--
A recommendation model together with a user-type map for which equal types have
identical utility rows. This is the data needed to formalize the paper's `S_symm`.
-/
structure SymmetricData (m n K : ℕ) where
  model : RecommendationModel m n
  types : UserTypeAssignment m K
  agreeWithinTypes : UtilitiesAgreeWithinTypes model types

end RecommendationModel

namespace UserTypeAssignment

/-- Lift a type-level policy to a user-level policy by composition with the type map. -/
def liftTypePolicy {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : TypePolicy K n) : Policy m n :=
  DecisionCore.Policy.liftAlong τ.toType ρ

/-- A user-level policy is type-symmetric if equal types receive equal PMFs. -/
def IsTypeSymmetric {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : Policy m n) : Prop :=
  DecisionCore.Policy.IsClasswise τ.toType ρ

/-- The set `S_symm` of type-symmetric user-level policies. -/
def SymmetricPolicies {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) : Set (Policy m n) :=
  DecisionCore.Policy.ClasswisePolicies τ.toType

@[simp] theorem liftTypePolicy_apply {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : TypePolicy K n) (u : User m) :
    liftTypePolicy τ ρ u = ρ (τ.toType u) := rfl

@[simp] theorem liftTypePolicy_sameType {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : TypePolicy K n)
    {u u' : User m} (h : τ.toType u = τ.toType u') :
    liftTypePolicy τ ρ u = liftTypePolicy τ ρ u' := by
  simp [liftTypePolicy, h]

/-- Every lifted type-level policy is type-symmetric. -/
theorem liftTypePolicy_isTypeSymmetric {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : TypePolicy K n) :
    IsTypeSymmetric τ (liftTypePolicy τ ρ) := by
  simpa [IsTypeSymmetric, liftTypePolicy] using
    (DecisionCore.Policy.liftAlong_isClasswise (τ := τ.toType) (ρ := ρ))

/-- Chosen representative user for each declared user type. -/
abbrev TypeRepresentatives {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) :=
  DecisionCore.Policy.FiberRepresentatives τ.toType

/--
Descend a user-level policy to the type level by evaluating it on one chosen
representative user from each type.
-/
def descendTypePolicy {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n) : TypePolicy K n :=
  DecisionCore.Policy.descendAlong reps ρ

@[simp] theorem descendTypePolicy_apply {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n) (k : UserType K) :
    descendTypePolicy τ reps ρ k = ρ (reps.repr k) := rfl

@[simp] theorem descendTypePolicy_liftTypePolicy {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : TypePolicy K n) :
    descendTypePolicy τ reps (liftTypePolicy τ ρ) = ρ := by
  simpa [descendTypePolicy, liftTypePolicy] using
    (DecisionCore.Policy.descendAlong_liftAlong (τ := τ.toType) reps ρ)

/--
If a user-level policy is type-symmetric, then after choosing one representative
per type it is exactly the lift of a type-level policy.
-/
theorem liftTypePolicy_descendTypePolicy_eq_of_isTypeSymmetric {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n)
    (hρ : IsTypeSymmetric τ ρ) :
    liftTypePolicy τ (descendTypePolicy τ reps ρ) = ρ := by
  simpa [IsTypeSymmetric, descendTypePolicy, liftTypePolicy] using
    (DecisionCore.Policy.liftAlong_descendAlong_eq_of_isClasswise
      (τ := τ.toType) reps ρ hρ)

/--
A user-level policy is type-symmetric exactly when it comes from lifting some
policy on user types. Representatives make the reverse direction explicit.
-/
theorem isTypeSymmetric_iff_exists_liftTypePolicy {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n) :
    IsTypeSymmetric τ ρ ↔ ∃ ρK : TypePolicy K n, liftTypePolicy τ ρK = ρ := by
  simpa [IsTypeSymmetric, liftTypePolicy] using
    (DecisionCore.Policy.isClasswise_iff_exists_liftAlong (τ := τ.toType) reps ρ)

end UserTypeAssignment

namespace TypePolicy

/-- Positive-support type-item pairs `(k, j)`. -/
noncomputable def activeTypeItemPairs {K n : ℕ}
    (ρ : TypePolicy K n) : Finset (UserType K × Item n) :=
  DecisionCore.Policy.activePairs ρ

/-- Number of positive-support type-item pairs. -/
noncomputable def activeTypeItemPairsCard {K n : ℕ} (ρ : TypePolicy K n) : ℕ :=
  DecisionCore.Policy.activePairsCard ρ

/-- Items recommended to more than one user type. -/
noncomputable def sharedItems {K n : ℕ} (ρ : TypePolicy K n) : Finset (Item n) :=
  DecisionCore.Policy.multiAssignedActions ρ

/-- Target shape of the first sparsity conclusion in Proposition 2. -/
def ActivePairsBound {K n : ℕ} (ρ : TypePolicy K n) : Prop :=
  activeTypeItemPairsCard ρ ≤ n + K - 1

/-- Target shape of the second sparsity conclusion in Proposition 2. -/
def SharedItemsBound {K n : ℕ} (ρ : TypePolicy K n) : Prop :=
  (sharedItems ρ).card ≤ K - 1

/-- The combined sparse-support shape extracted from Proposition 2. -/
def SparseShape {K n : ℕ} (ρ : TypePolicy K n) : Prop :=
  ActivePairsBound ρ ∧ SharedItemsBound ρ

end TypePolicy
end UserItemFairness
