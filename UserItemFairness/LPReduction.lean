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

/-- Item-fairness values attainable by type-symmetric user-level policies. -/
def symmetricAttainableItemFairnessSet {m n K : ℕ} [NeZero n]
    (S : SymmetricData m n K) : Set ℝ :=
  {r | ∃ ρ : Policy m n,
    UserTypeAssignment.IsTypeSymmetric S.types ρ ∧ r = itemFairness S.model ρ}

/-- Supremal item fairness over type-symmetric user-level policies. -/
noncomputable def symmetricOptimalItemFairness {m n K : ℕ} [NeZero n]
    (S : SymmetricData m n K) : ℝ :=
  sSup (symmetricAttainableItemFairnessSet S)

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

/-- Entrywise nonnegativity of the reduced utility matrix. -/
def NonnegativeUtilities {K n : ℕ} (T : TypeWeightedRecommendationModel K n) : Prop :=
  ∀ k j, 0 ≤ T.utility k j

/-- Every user type has at least one strictly positive item. -/
def RowHasPositiveItem {K n : ℕ} (T : TypeWeightedRecommendationModel K n) : Prop :=
  ∀ k, ∃ j, 0 < T.utility k j

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

/-- Positive reduced item fairness implies every item is used by some type. -/
theorem item_coverage_of_itemFairness_pos {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hpos : 0 < itemFairness T ρ) :
    ∀ j : Item n, ∃ k : UserType K, ρ k j ≠ 0 := by
  classical
  intro j
  by_contra hnone
  have hall_zero : ∀ k : UserType K, ρ k j = 0 := by
    intro k
    exact Classical.byContradiction (by
      intro hk
      exact hnone ⟨k, hk⟩)
  have hraw_zero : rawItemUtility T ρ j = 0 := by
    unfold rawItemUtility
    simp [hall_zero]
  have hnorm_zero : normalizedItemUtility T ρ j = 0 := by
    unfold normalizedItemUtility
    rw [hraw_zero]
    by_cases hden : itemNormalizer T j = 0
    · simp [hden]
    · simp [hden]
  have hle := DecisionCore.finiteMin_le (normalizedItemUtility T ρ) j
  have hnorm_pos : 0 < normalizedItemUtility T ρ j := lt_of_lt_of_le hpos hle
  rw [hnorm_zero] at hnorm_pos
  exact (lt_irrefl (0 : ℝ)) hnorm_pos

/-- Nonnegative weights/utilities make every reduced raw item utility nonnegative. -/
theorem rawItemUtility_nonneg_of_nonnegative
    {K n : ℕ} (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (ρ : TypePolicy K n) (j : Item n) :
    0 ≤ rawItemUtility T ρ j := by
  unfold rawItemUtility
  exact Finset.sum_nonneg (by
    intro k _hk
    exact mul_nonneg (mul_nonneg (hWeight k) (hUtil k j))
      ENNReal.toReal_nonneg)

/-- Nonnegative weights/utilities make every reduced item normalizer nonnegative. -/
theorem itemNormalizer_nonneg_of_nonnegative
    {K n : ℕ} (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (j : Item n) :
    0 ≤ itemNormalizer T j := by
  unfold itemNormalizer
  exact Finset.sum_nonneg (by
    intro k _hk
    exact mul_nonneg (hWeight k) (hUtil k j))

/-- Nonnegative weights/utilities make reduced normalized item utility nonnegative. -/
theorem normalizedItemUtility_nonneg_of_nonnegative
    {K n : ℕ} (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (ρ : TypePolicy K n) (j : Item n) :
    0 ≤ normalizedItemUtility T ρ j := by
  unfold normalizedItemUtility
  by_cases hden : itemNormalizer T j = 0
  · simp [hden]
  · simpa [hden] using div_nonneg
      (rawItemUtility_nonneg_of_nonnegative T hWeight hUtil ρ j)
      (itemNormalizer_nonneg_of_nonnegative T hWeight hUtil j)

/-- Nonnegative weights/utilities make reduced minimum item fairness nonnegative. -/
theorem itemFairness_nonneg_of_nonnegative {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (ρ : TypePolicy K n) :
    0 ≤ itemFairness T ρ := by
  exact DecisionCore.finiteMin_nonneg (normalizedItemUtility T ρ)
    (normalizedItemUtility_nonneg_of_nonnegative T hWeight hUtil ρ)

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

/-- Row positivity makes the type-normalization denominator strictly positive. -/
theorem bestItemUtility_pos_of_rowHasPositiveItem {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (hRow : T.RowHasPositiveItem)
    (k : UserType K) :
    0 < bestItemUtility T k := by
  obtain ⟨j, hj⟩ := hRow k
  exact lt_of_lt_of_le hj (DecisionCore.le_finiteMax (T.utility k) j)

/-- A type's raw expected utility is at most that type's best item utility. -/
theorem rawTypeUtility_le_bestItemUtility {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (k : UserType K) :
    rawTypeUtility T ρ k ≤ bestItemUtility T k := by
  unfold rawTypeUtility bestItemUtility DecisionCore.Policy.agentScore
  exact DecisionCore.pmfExp_le_of_forall_le (ρ k) (T.utility k)
    (DecisionCore.finiteMax (T.utility k))
    (fun j => DecisionCore.le_finiteMax (T.utility k) j)

/-- Positive row normalizers make every normalized type utility at most one. -/
theorem normalizedTypeUtility_le_one_of_rowHasPositiveItem
    {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (hRow : T.RowHasPositiveItem)
    (ρ : TypePolicy K n) (k : UserType K) :
    normalizedTypeUtility T ρ k ≤ 1 := by
  have hraw := rawTypeUtility_le_bestItemUtility T ρ k
  have hbest_pos := bestItemUtility_pos_of_rowHasPositiveItem T hRow k
  unfold normalizedTypeUtility
  rw [div_le_iff₀ hbest_pos]
  simpa using hraw

/-- Minimum type fairness is bounded above by one. -/
theorem typeFairness_le_one_of_rowHasPositiveItem
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (hRow : T.RowHasPositiveItem)
    (ρ : TypePolicy K n) :
    typeFairness T ρ ≤ 1 := by
  classical
  let k0 : UserType K := Classical.choice inferInstance
  exact (DecisionCore.finiteMin_le (normalizedTypeUtility T ρ) k0).trans
    (normalizedTypeUtility_le_one_of_rowHasPositiveItem T hRow ρ k0)

/-- Feasible type-fairness values are bounded above by one under positive row normalizers. -/
theorem attainableTypeFairnessAtLevel_bddAbove_of_rowHasPositiveItem
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (hRow : T.RowHasPositiveItem)
    (γ : ℝ) :
    BddAbove (attainableTypeFairnessAtLevel T γ) := by
  refine ⟨1, ?_⟩
  intro r hr
  obtain ⟨ρ, _hfeas, hr⟩ := hr
  rw [hr]
  exact typeFairness_le_one_of_rowHasPositiveItem T hRow ρ

/-- A canonical reduced policy used only to witness nonempty finite feasible sets. -/
noncomputable def defaultTypePolicy {K n : ℕ} [NeZero n] : TypePolicy K n :=
  DecisionCore.Policy.pure
    (fun _ : UserType K => Classical.choice (inferInstance : Nonempty (Item n)))

/--
At baseline `γ = 0`, every reduced policy is feasible under nonnegative
weights and utilities.
-/
theorem feasibleAtLevel_zero_of_nonnegative
    {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (ρ : TypePolicy K n) :
    feasibleAtLevel T 0 ρ := by
  unfold feasibleAtLevel
  simpa using itemFairness_nonneg_of_nonnegative T hWeight hUtil ρ

/-- The baseline reduced feasible value set is nonempty under nonnegativity. -/
theorem attainableTypeFairnessAtLevel_zero_nonempty_of_nonnegative
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities) :
    (attainableTypeFairnessAtLevel T 0).Nonempty := by
  refine ⟨typeFairness T (defaultTypePolicy (K := K) (n := n)), ?_⟩
  exact ⟨defaultTypePolicy (K := K) (n := n),
    feasibleAtLevel_zero_of_nonnegative T hWeight hUtil _, rfl⟩

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
