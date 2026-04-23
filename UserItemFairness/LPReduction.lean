import UserItemFairness.Symmetry

open scoped BigOperators
open DecisionCore

namespace UserItemFairness

namespace RecommendationModel

/-- The feasible set for Problem 1 at fairness level `γ`. -/
def feasiblePoliciesAtLevelSet {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : Set (Policy m n) :=
  {ρ | feasibleAtLevel W γ ρ}

/-- The optimal-solution set for Problem 1 at fairness level `γ`. -/
def optimalPoliciesAtLevelSet {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : Set (Policy m n) :=
  {ρ | IsOptimalAtLevel W γ ρ}

/-- The feasible region restricted to type-symmetric policies. -/
def symmetricFeasiblePolicies {m n K : ℕ} [NeZero n]
    (S : SymmetricData m n K) (γ : ℝ) : Set (Policy m n) :=
  {ρ | UserTypeAssignment.IsTypeSymmetric S.types ρ ∧ feasibleAtLevel S.model γ ρ}

/-- The optimal region restricted to type-symmetric policies. -/
def symmetricOptimalPolicies {m n K : ℕ} [NeZero m] [NeZero n]
    (S : SymmetricData m n K) (γ : ℝ) : Set (Policy m n) :=
  {ρ | UserTypeAssignment.IsTypeSymmetric S.types ρ ∧ IsOptimalAtLevel S.model γ ρ}

end RecommendationModel

namespace RecommendationModel.UserTypeAssignment

/-- The cardinality of a user type, viewed as the size of its fiber. -/
def typeCard {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (k : UserType K) : ℕ :=
  (Finset.univ.filter fun u => τ.toType u = k).card

/-- The same multiplicity, but as a real weight for the reduced LP. -/
noncomputable def typeWeight {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (k : UserType K) : ℝ :=
  (typeCard τ k : ℝ)

@[simp] theorem typeWeight_nonneg {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (k : UserType K) :
    0 ≤ typeWeight τ k := by
  exact Nat.cast_nonneg _

end RecommendationModel.UserTypeAssignment

/--
A type-weighted reduction of the recommendation problem. This is the natural LP-side
object once users with identical utility rows have been merged into types.
-/
structure TypeWeightedRecommendationModel (K n : ℕ) where
  utility : UserType K → Item n → ℝ
  weight : UserType K → ℝ

namespace TypeWeightedRecommendationModel

/-- Nonnegativity of the type weights. -/
def NonnegativeWeights {K n : ℕ} (T : TypeWeightedRecommendationModel K n) : Prop :=
  ∀ k, 0 ≤ T.weight k

/-- Raw expected utility received by a type `k`. -/
noncomputable def rawTypeUtility {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) (k : UserType K) : ℝ :=
  DecisionCore.Policy.agentScore ρ T.utility k

/-- Best item utility available to type `k`. -/
noncomputable def bestItemUtility {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (k : UserType K) : ℝ :=
  DecisionCore.finiteMax (T.utility k)

/-- Normalized utility received by type `k`. -/
noncomputable def normalizedTypeUtility {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) (k : UserType K) : ℝ :=
  rawTypeUtility T ρ k / bestItemUtility T k

/-- Minimum normalized utility over user types. -/
noncomputable def typeFairness {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) : ℝ :=
  DecisionCore.finiteMin (normalizedTypeUtility T ρ)

/-- Weighted raw utility accumulated by an item. -/
noncomputable def rawItemUtility {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) (j : Item n) : ℝ :=
  ∑ k, T.weight k * T.utility k j * (ρ k j).toReal

/-- Weighted item normalizer. -/
noncomputable def itemNormalizer {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (j : Item n) : ℝ :=
  ∑ k, T.weight k * T.utility k j

/-- Normalized item utility in the reduced type-level problem. -/
noncomputable def normalizedItemUtility {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) (j : Item n) : ℝ :=
  let denom := itemNormalizer T j
  if h : denom = 0 then 0 else rawItemUtility T ρ j / denom

/-- Minimum normalized item utility in the reduced problem. -/
noncomputable def itemFairness {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) : ℝ :=
  DecisionCore.finiteMin (normalizedItemUtility T ρ)

/-- Attainable reduced-problem item fairness levels. -/
def attainableItemFairnessSet {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) : Set ℝ :=
  {r | ∃ ρ : TypePolicy K n, r = itemFairness T ρ}

/-- The reduced analogue of `I^*_min`. -/
noncomputable def optimalItemFairness {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) : ℝ :=
  sSup (attainableItemFairnessSet T)

/-- Feasibility for the reduced problem at fairness level `γ`. -/
def feasibleAtLevel {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (γ : ℝ) (ρ : TypePolicy K n) : Prop :=
  γ * optimalItemFairness T ≤ itemFairness T ρ

/-- Attainable reduced-problem type-fairness levels at item-fairness level `γ`. -/
def attainableTypeFairnessAtLevel {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (γ : ℝ) : Set ℝ :=
  {r | ∃ ρ : TypePolicy K n, feasibleAtLevel T γ ρ ∧ r = typeFairness T ρ}

/-- The reduced analogue of `U^*_min(γ, w)`. -/
noncomputable def optimalTypeFairnessAtLevel {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (γ : ℝ) : ℝ :=
  sSup (attainableTypeFairnessAtLevel T γ)

/-- A type-level policy solves the reduced problem at item-fairness level `γ`. -/
def IsOptimalAtLevel {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (γ : ℝ) (ρ : TypePolicy K n) : Prop :=
  feasibleAtLevel T γ ρ ∧ typeFairness T ρ = optimalTypeFairnessAtLevel T γ

end TypeWeightedRecommendationModel

/--
A witness connecting the original user-level model with a chosen type-level reduction.
The equality clauses are intentionally exact, so Codex can later prove preservation of
utilities, fairness functionals, and feasible regions by rewriting.
-/
structure ReductionWitness (m n K : ℕ) where
  data : RecommendationModel.SymmetricData m n K
  reduced : TypeWeightedRecommendationModel K n
  utility_agrees : ∀ u j,
    data.model.utility u j = reduced.utility (data.types.toType u) j
  weight_eq_typeWeight : ∀ k,
    reduced.weight k = RecommendationModel.UserTypeAssignment.typeWeight data.types k

namespace ReductionWitness

/-- Lift a reduced-policy candidate back to a user-level policy. -/
def liftedPolicy {m n K : ℕ}
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) : Policy m n :=
  UserTypeAssignment.liftTypePolicy R.data.types ρ

@[simp] theorem liftedPolicy_apply {m n K : ℕ}
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) (u : User m) :
    liftedPolicy R ρ u = ρ (R.data.types.toType u) := rfl

/-- Every lifted reduced-policy candidate is type-symmetric on users. -/
theorem liftedPolicy_isTypeSymmetric {m n K : ℕ}
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) :
    UserTypeAssignment.IsTypeSymmetric R.data.types (liftedPolicy R ρ) :=
  UserTypeAssignment.liftTypePolicy_isTypeSymmetric _ _



/--
If each user type has a chosen representative, then every type-symmetric user-level
policy comes from a genuine reduced type-level policy.
-/
theorem exists_typePolicy_of_isTypeSymmetric {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ) :
    ∃ ρK : TypePolicy K n, liftedPolicy R ρK = ρ := by
  simpa [liftedPolicy] using
    (UserTypeAssignment.isTypeSymmetric_iff_exists_liftTypePolicy R.data.types reps ρ).mp hρ

end ReductionWitness

/--
A clean target proposition for Proposition 1: every symmetric optimal user-level policy
should come from a type-level policy in the reduced problem.
-/
def LPReductionTarget {m n K : ℕ} [NeZero m] [NeZero n]
    (R : ReductionWitness m n K) (γ : ℝ) : Prop :=
  ∀ ρ,
    ρ ∈ RecommendationModel.symmetricOptimalPolicies R.data γ →
      ∃ ρK : TypePolicy K n, ReductionWitness.liftedPolicy R ρK = ρ

/--
A clean target proposition for Proposition 2: optimal reduced policies have sparse
support in the precise sense already encoded in `TypePolicy.SparseShape`.
-/
def ReducedSparseOptimalityTarget {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (γ : ℝ) : Prop :=
  ∀ ρ : TypePolicy K n,
    TypeWeightedRecommendationModel.IsOptimalAtLevel T γ ρ → TypePolicy.SparseShape ρ

/--
With chosen representatives for user types, the abstract LP-reduction target follows
immediately from the classwise lifting theorem.
-/
theorem lpReductionTarget_of_representatives {m n K : ℕ} [NeZero m] [NeZero n]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) :
    LPReductionTarget R γ := by
  intro ρ hρ
  exact ReductionWitness.exists_typePolicy_of_isTypeSymmetric R reps hρ.1

end UserItemFairness
