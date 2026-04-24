import UserItemFairness.Symmetrization

/-!
# Paper-Facing Theorems: User-Item Fairness Tradeoffs in Recommendations

This file is the public theorem interface for the user-item fairness
formalization. Detailed LP, symmetry, and utility-preservation lemmas live in
the sibling files.
-/

namespace UserItemFairness
namespace ReductionWitness

/--
Symmetric item-fairness reduction theorem.

The item-fairness values attainable by type-symmetric user-level policies are
exactly the values attainable by the reduced type-level problem.
-/
theorem paper_symmetric_item_fairness_value_set_reduction
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    RecommendationModel.symmetricAttainableItemFairnessSet R.data =
      TypeWeightedRecommendationModel.attainableItemFairnessSet R.reduced := by
  exact R.symmetricAttainableItemFairnessSet_eq_reduced reps

/--
Symmetric optimal item-fairness reduction theorem.

The optimum item-fairness value over type-symmetric user-level policies equals
the optimum item-fairness value in the reduced type-level problem.
-/
theorem paper_symmetric_optimal_item_fairness_reduction
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    RecommendationModel.symmetricOptimalItemFairness R.data =
      TypeWeightedRecommendationModel.optimalItemFairness R.reduced := by
  exact R.symmetricOptimalItemFairness_eq_reduced reps

/--
Proposition 1 symmetric LP-reduction target.

Every type-symmetric original optimal policy is represented by a reduced
type-level policy. This is the unconditional part of the paper's symmetry
reduction that follows from chosen representatives for each user type.
-/
theorem paper_symmetric_lp_reduction_target
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) :
    LPReductionTarget R γ := by
  exact lpReductionTarget_of_representatives R reps γ

/--
Pointwise form of the symmetric LP-reduction target.

If a user-level optimum is already type-symmetric, then it is exactly the lift
of some type-level policy.
-/
theorem paper_symmetric_original_optimum_has_type_representative
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n, R.liftedPolicy ρK = ρ := by
  exact lpReductionTarget_of_representatives R reps γ ρ ⟨hρ, hopt⟩

/--
Original/reduced optimal user-fairness value reduction.

This replaces the earlier opaque optimal-value equality assumption with the
standard side conditions needed to reason about `sSup` on real-valued feasible
sets: both feasible value sets are nonempty and bounded above.
-/
theorem paper_original_reduced_user_optimal_value_reduction
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hOrigBdd :
      BddAbove (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ))
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hRedBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ)) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ := by
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_bddAbove_nonempty
    reps hRow γ hOrigNonempty hOrigBdd hRedNonempty hRedBdd

/--
Original/reduced optimal user-fairness value reduction with automatic
boundedness.

The remaining side condition is now only nonemptiness of the original and
reduced feasible value sets; row positivity gives the common `≤ 1` upper bound.
-/
theorem paper_original_reduced_user_optimal_value_reduction_of_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ := by
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
    reps hRow γ hOrigNonempty hRedNonempty

/--
Baseline original/reduced optimal user-fairness value reduction.

For `γ = 0`, nonnegative utilities automatically make both original and
reduced feasible value sets nonempty; row positivity supplies boundedness.
-/
theorem paper_original_reduced_user_optimal_value_reduction_zero
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (hNonneg : R.data.model.Nonnegative) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model 0 =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced 0 := by
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model 0).Nonempty :=
    RecommendationModel.attainableUserFairnessAtLevel_zero_nonempty_of_nonnegative
      R.data.model hNonneg
  have hRedWeight : R.reduced.NonnegativeWeights :=
    R.reduced_nonnegativeWeights
  have hRedUtil : R.reduced.NonnegativeUtilities :=
    R.reduced_nonnegativeUtilities_of_nonnegative reps hNonneg
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced 0).Nonempty :=
    TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel_zero_nonempty_of_nonnegative
      R.reduced hRedWeight hRedUtil
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
    reps hRow 0 hOrigNonempty hRedNonempty

/--
Reduced-to-original optimum theorem under the explicit supremum conditions used
by the value-reduction theorem.
-/
theorem paper_reduced_optimum_lifts_to_original
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) (ρ : TypePolicy K n)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hOrigBdd :
      BddAbove (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ))
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hRedBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ))
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_bddAbove_nonempty
      reps hRow γ hOrigNonempty hOrigBdd hRedNonempty hRedBdd
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced reps γ ρ
    (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Reduced-to-original optimum theorem with automatic boundedness.

Only nonemptiness of the original and reduced feasible value sets remains
explicit; row positivity supplies the `≤ 1` bounds needed by `sSup`.
-/
theorem paper_reduced_optimum_lifts_to_original_of_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) (ρ : TypePolicy K n)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow γ hOrigNonempty hRedNonempty
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced reps γ ρ
    (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Symmetric original-to-reduced optimum theorem under the explicit supremum
conditions used by the value-reduction theorem.
-/
theorem paper_symmetric_original_optimum_descends_to_reduced
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hOrigBdd :
      BddAbove (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ))
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hRedBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ))
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_bddAbove_nonempty
      reps hRow γ hOrigNonempty hOrigBdd hRedNonempty hRedBdd
  exact R.exists_reducedOptimalAtLevel_of_original_symmetric_optimal
    reps γ hρ (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Symmetric original-to-reduced optimum theorem with automatic boundedness.

Only nonemptiness of the original and reduced feasible value sets remains
explicit; row positivity supplies the `≤ 1` bounds needed by `sSup`.
-/
theorem paper_symmetric_original_optimum_descends_to_reduced_of_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow γ hOrigNonempty hRedNonempty
  exact R.exists_reducedOptimalAtLevel_of_original_symmetric_optimal
    reps γ hρ (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

end ReductionWitness

namespace TypePolicy

/--
Proposition 1 sparse shared-item consequence.

If a reduced type-level policy has at most `n + K - 1` active type-item pairs
and every item is recommended by at least one type, then at most `K - 1` items
are shared by multiple user types. This is the finite counting half of the
paper's sparse-support statement, separated from the LP basic-feasible-solution
theorem that supplies the active-pair bound.
-/
theorem paper_sparse_shared_items_of_active_pairs_bound
    {K n : ℕ} [NeZero K]
    (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    SharedItemsBound ρ := by
  exact sharedItemsBound_of_activePairsBound_of_item_coverage ρ hactive hcover

/--
Proposition 1 sparse-shape consequence from active-pair sparsity and item
coverage.
-/
theorem paper_sparse_shape_of_active_pairs_bound
    {K n : ℕ} [NeZero K]
    (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    SparseShape ρ := by
  exact sparseShape_of_activePairsBound_of_item_coverage ρ hactive hcover

/--
Proposition 1 sparse shared-item consequence with item coverage discharged from
positive reduced item fairness.

If the reduced type policy has positive minimum normalized item utility, then
every item is recommended by at least one type. Therefore the paper's
basic-feasible-solution active-pair bound implies that at most `K - 1` items
are shared by multiple user types.
-/
theorem paper_sparse_shared_items_of_active_pairs_bound_of_positive_item_fairness
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hitem_pos : 0 < TypeWeightedRecommendationModel.itemFairness T ρ) :
    SharedItemsBound ρ := by
  exact sharedItemsBound_of_activePairsBound_of_item_coverage ρ hactive
    (TypeWeightedRecommendationModel.item_coverage_of_itemFairness_pos T ρ hitem_pos)

/--
Proposition 1 sparse-shape consequence with item coverage discharged from
positive reduced item fairness.
-/
theorem paper_sparse_shape_of_active_pairs_bound_of_positive_item_fairness
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hitem_pos : 0 < TypeWeightedRecommendationModel.itemFairness T ρ) :
    SparseShape ρ := by
  exact sparseShape_of_activePairsBound_of_item_coverage ρ hactive
    (TypeWeightedRecommendationModel.item_coverage_of_itemFairness_pos T ρ hitem_pos)

/--
Lemma `IF* > 0` from the paper, in the reduced type-level model.

Strictly positive type weights and utility entries imply that the maximal
reduced item-fairness value is strictly positive; the proof is witnessed by the
uniform policy.
-/
theorem paper_reduced_optimal_item_fairness_positive
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities) :
    0 < TypeWeightedRecommendationModel.optimalItemFairness T := by
  exact TypeWeightedRecommendationModel.optimalItemFairness_pos_of_positive
    T hWeight hUtil

/--
Proposition 1 sparse shared-item consequence for a maximal-item-fairness
reduced optimum.

The only remaining hypothesis is the paper's basic-feasible-solution
active-pair bound. Positivity of the item-fairness optimum is discharged from
strictly positive weights/utilities.
-/
theorem paper_sparse_shared_items_of_active_pairs_bound_of_maximal_optimum
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (hactive : ActivePairsBound ρ)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel T 1 ρ) :
    SharedItemsBound ρ := by
  have hopt_pos :
      0 < TypeWeightedRecommendationModel.optimalItemFairness T :=
    TypeWeightedRecommendationModel.optimalItemFairness_pos_of_positive
      T hWeight hUtil
  have hitem_pos : 0 < TypeWeightedRecommendationModel.itemFairness T ρ := by
    have hfeas := hopt.1
    unfold TypeWeightedRecommendationModel.feasibleAtLevel at hfeas
    exact lt_of_lt_of_le hopt_pos (by simpa using hfeas)
  exact sharedItemsBound_of_activePairsBound_of_item_coverage ρ hactive
    (TypeWeightedRecommendationModel.item_coverage_of_itemFairness_pos T ρ hitem_pos)

/--
Proposition 1 sparse-shape consequence for a maximal-item-fairness reduced
optimum, with positivity discharged from strictly positive data.
-/
theorem paper_sparse_shape_of_active_pairs_bound_of_maximal_optimum
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (hactive : ActivePairsBound ρ)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel T 1 ρ) :
    SparseShape ρ := by
  exact ⟨hactive,
    paper_sparse_shared_items_of_active_pairs_bound_of_maximal_optimum
      T ρ hWeight hUtil hactive hopt⟩

end TypePolicy

end UserItemFairness
