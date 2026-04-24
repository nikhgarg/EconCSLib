import UserItemFairness.ReductionPreservation

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
Conditional reduced-to-original optimum theorem.

If the global original and reduced optimal values agree, then every reduced
optimal policy lifts to an original user-level optimum.
-/
theorem paper_reduced_optimum_lifts_to_original
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) (ρ : TypePolicy K n)
    (hItemOpt :
      RecommendationModel.optimalItemFairness R.data.model =
        TypeWeightedRecommendationModel.optimalItemFairness R.reduced)
    (hUserOpt :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced reps γ ρ
    hItemOpt hUserOpt hopt

/--
Conditional original-to-reduced optimum theorem.

If a user-level optimum is type-symmetric and the global original and reduced
optimal values agree, then it descends to a reduced type-level optimum.
-/
theorem paper_symmetric_original_optimum_descends_to_reduced
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hItemOpt :
      RecommendationModel.optimalItemFairness R.data.model =
        TypeWeightedRecommendationModel.optimalItemFairness R.reduced)
    (hUserOpt :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  exact R.exists_reducedOptimalAtLevel_of_original_symmetric_optimal
    reps γ hρ hItemOpt hUserOpt hopt

end ReductionWitness
end UserItemFairness
