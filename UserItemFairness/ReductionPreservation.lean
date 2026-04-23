import UserItemFairness.LPReduction

open scoped BigOperators
open DecisionCore

namespace UserItemFairness

namespace RecommendationModel.SymmetricData

/-- Under a type-symmetric policy, same-type users have the same raw utility. -/
theorem rawUserUtility_eq_of_sameType {m n K : ℕ}
    (S : RecommendationModel.SymmetricData m n K)
    {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric S.types ρ)
    {u u' : User m} (hType : S.types.toType u = S.types.toType u') :
    RecommendationModel.rawUserUtility S.model ρ u =
      RecommendationModel.rawUserUtility S.model ρ u' := by
  unfold RecommendationModel.rawUserUtility DecisionCore.Policy.agentScore DecisionCore.pmfExp
  refine Finset.sum_congr rfl ?_
  intro j _
  have hrow : S.model.utility u j = S.model.utility u' j := by
    exact congrFun (S.agreeWithinTypes u u' hType) j
  have hpol : ρ u = ρ u' := hρ u u' hType
  rw [hrow, hpol]

/-- Same-type users have the same best-item normalizer. -/
theorem bestItemUtility_eq_of_sameType {m n K : ℕ} [NeZero n]
    (S : RecommendationModel.SymmetricData m n K)
    {u u' : User m} (hType : S.types.toType u = S.types.toType u') :
    RecommendationModel.bestItemUtility S.model u =
      RecommendationModel.bestItemUtility S.model u' := by
  have hrow : S.model.utility u = S.model.utility u' := S.agreeWithinTypes u u' hType
  unfold RecommendationModel.bestItemUtility
  rw [hrow]

/-- Under a type-symmetric policy, same-type users have the same normalized utility. -/
theorem normalizedUserUtility_eq_of_sameType {m n K : ℕ} [NeZero n]
    (S : RecommendationModel.SymmetricData m n K)
    {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric S.types ρ)
    {u u' : User m} (hType : S.types.toType u = S.types.toType u') :
    RecommendationModel.normalizedUserUtility S.model ρ u =
      RecommendationModel.normalizedUserUtility S.model ρ u' := by
  unfold RecommendationModel.normalizedUserUtility
  rw [rawUserUtility_eq_of_sameType (S := S) (ρ := ρ) hρ hType]
  rw [bestItemUtility_eq_of_sameType (S := S) hType]

end RecommendationModel.SymmetricData

namespace ReductionWitness

/--
A lifted reduced policy gives each original user exactly the raw utility of that
user's type in the reduced model.
-/
theorem rawUserUtility_liftedPolicy_eq_rawTypeUtility {m n K : ℕ}
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) (u : User m) :
    RecommendationModel.rawUserUtility R.data.model (R.liftedPolicy ρ) u =
      TypeWeightedRecommendationModel.rawTypeUtility R.reduced ρ (R.data.types.toType u) := by
  unfold RecommendationModel.rawUserUtility TypeWeightedRecommendationModel.rawTypeUtility
    DecisionCore.Policy.agentScore DecisionCore.pmfExp ReductionWitness.liftedPolicy
    UserTypeAssignment.liftTypePolicy DecisionCore.Policy.liftAlong
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [R.utility_agrees u j]

/-- Best-item normalizers are preserved by the reduction for each original user. -/
theorem bestItemUtility_eq_bestTypeUtility {m n K : ℕ} [NeZero n]
    (R : ReductionWitness m n K) (u : User m) :
    RecommendationModel.bestItemUtility R.data.model u =
      TypeWeightedRecommendationModel.bestItemUtility R.reduced (R.data.types.toType u) := by
  have hrow : R.data.model.utility u = R.reduced.utility (R.data.types.toType u) := by
    funext j
    exact R.utility_agrees u j
  unfold RecommendationModel.bestItemUtility TypeWeightedRecommendationModel.bestItemUtility
  rw [hrow]

/-- Normalized user utility is preserved pointwise under lifting from the reduced model. -/
theorem normalizedUserUtility_liftedPolicy_eq_normalizedTypeUtility {m n K : ℕ} [NeZero n]
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) (u : User m) :
    RecommendationModel.normalizedUserUtility R.data.model (R.liftedPolicy ρ) u =
      TypeWeightedRecommendationModel.normalizedTypeUtility R.reduced ρ (R.data.types.toType u) := by
  unfold RecommendationModel.normalizedUserUtility
    TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [rawUserUtility_liftedPolicy_eq_rawTypeUtility (R := R) (ρ := ρ) (u := u)]
  rw [bestItemUtility_eq_bestTypeUtility (R := R) (u := u)]

end ReductionWitness

end UserItemFairness
