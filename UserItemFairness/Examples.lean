import UserItemFairness.Symmetry

namespace UserItemFairness

/-- A `2 × 2` utility matrix with opposite user preferences. -/
def twoByTwoUtility : User 2 → Item 2 → ℝ :=
  fun u j => if u = j then 10 else 1

/-- A tiny instance useful for notation and smoke tests. -/
noncomputable def twoByTwoModel : RecommendationModel 2 2 where
  utility := twoByTwoUtility

/-- A deterministic policy that recommends item `u` to user `u`. -/
noncomputable def diagonalPolicy : Policy 2 2 :=
  DecisionCore.Policy.pure (fun u => u)

/-- A deterministic policy that flips the two users' preferred items. -/
noncomputable def swappedPolicy : Policy 2 2 :=
  DecisionCore.Policy.pure (fun u => if u = 0 then (1 : Item 2) else 0)

/-- The obvious two-type partition for the `2 × 2` toy instance. -/
def twoTypeAssignment : RecommendationModel.UserTypeAssignment 2 2 where
  toType := fun u => u

/-- A toy estimated model that swaps the two rows of the utility matrix. -/
noncomputable def twoByTwoEstimated : EstimatedRecommendationModel 2 2 where
  trueModel := twoByTwoModel
  estimatedUtility u j := twoByTwoUtility (if u = 0 then (1 : User 2) else 0) j

end UserItemFairness
