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

end ReductionWitness
end UserItemFairness
