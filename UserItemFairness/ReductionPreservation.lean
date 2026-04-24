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

/-- Row positivity in the original symmetric model transfers to the reduced model. -/
theorem reduced_rowHasPositiveItem_of_rowHasPositiveItem
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem) :
    R.reduced.RowHasPositiveItem := by
  intro k
  obtain ⟨j, hj⟩ := hRow (reps.repr k)
  refine ⟨j, ?_⟩
  rw [R.utility_agrees (reps.repr k) j] at hj
  simpa [reps.repr_spec k] using hj

/-- Type weights in the reduced model are nonnegative cardinalities. -/
theorem reduced_nonnegativeWeights {m n K : ℕ}
    (R : ReductionWitness m n K) :
    R.reduced.NonnegativeWeights := by
  intro k
  rw [R.weight_eq_typeWeight k]
  exact RecommendationModel.UserTypeAssignment.typeWeight_nonneg R.data.types k

/-- Original entrywise utility nonnegativity transfers to the reduced model. -/
theorem reduced_nonnegativeUtilities_of_nonnegative
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hNonneg : R.data.model.Nonnegative) :
    R.reduced.NonnegativeUtilities := by
  intro k j
  have h := hNonneg (reps.repr k) j
  rw [R.utility_agrees (reps.repr k) j] at h
  simpa [reps.repr_spec k] using h

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

/-- Lifted reduced policies preserve item raw utility exactly. -/
theorem rawItemUtility_liftedPolicy_eq_rawItemUtility {m n K : ℕ}
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) (j : Item n) :
    RecommendationModel.rawItemUtility R.data.model (R.liftedPolicy ρ) j =
      TypeWeightedRecommendationModel.rawItemUtility R.reduced ρ j := by
  classical
  unfold RecommendationModel.rawItemUtility TypeWeightedRecommendationModel.rawItemUtility
    ReductionWitness.liftedPolicy UserTypeAssignment.liftTypePolicy DecisionCore.Policy.liftAlong
  calc
    ∑ u : User m, R.data.model.utility u j * (ρ (R.data.types.toType u) j).toReal
        = ∑ u : User m,
            R.reduced.utility (R.data.types.toType u) j *
              (ρ (R.data.types.toType u) j).toReal := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [R.utility_agrees u j]
    _ = ∑ k : UserType K,
          RecommendationModel.UserTypeAssignment.typeWeight R.data.types k *
            (R.reduced.utility k j * (ρ k j).toReal) := by
          exact (DecisionCore.Policy.sum_fiber_card_mul
            (τ := R.data.types.toType)
            (f := fun k : UserType K => R.reduced.utility k j * (ρ k j).toReal)).symm
    _ = ∑ k : UserType K,
          R.reduced.weight k * R.reduced.utility k j * (ρ k j).toReal := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [R.weight_eq_typeWeight k]
          ring

/-- Lifted reduced policies preserve item normalizers exactly. -/
theorem itemNormalizer_eq_itemNormalizer {m n K : ℕ}
    (R : ReductionWitness m n K) (j : Item n) :
    RecommendationModel.itemNormalizer R.data.model j =
      TypeWeightedRecommendationModel.itemNormalizer R.reduced j := by
  classical
  unfold RecommendationModel.itemNormalizer TypeWeightedRecommendationModel.itemNormalizer
  calc
    ∑ u : User m, R.data.model.utility u j
        = ∑ u : User m, R.reduced.utility (R.data.types.toType u) j := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [R.utility_agrees u j]
    _ = ∑ k : UserType K,
          RecommendationModel.UserTypeAssignment.typeWeight R.data.types k *
            R.reduced.utility k j := by
          exact (DecisionCore.Policy.sum_fiber_card_mul
            (τ := R.data.types.toType)
            (f := fun k : UserType K => R.reduced.utility k j)).symm
    _ = ∑ k : UserType K, R.reduced.weight k * R.reduced.utility k j := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [R.weight_eq_typeWeight k]

/-- Lifted reduced policies preserve normalized item utility pointwise. -/
theorem normalizedItemUtility_liftedPolicy_eq_normalizedItemUtility {m n K : ℕ}
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) (j : Item n) :
    RecommendationModel.normalizedItemUtility R.data.model (R.liftedPolicy ρ) j =
      TypeWeightedRecommendationModel.normalizedItemUtility R.reduced ρ j := by
  unfold RecommendationModel.normalizedItemUtility
    TypeWeightedRecommendationModel.normalizedItemUtility
  rw [rawItemUtility_liftedPolicy_eq_rawItemUtility (R := R) (ρ := ρ) (j := j)]
  rw [itemNormalizer_eq_itemNormalizer (R := R) (j := j)]

/-- Lifted reduced policies preserve minimum item fairness. -/
theorem itemFairness_liftedPolicy_eq_itemFairness {m n K : ℕ} [NeZero n]
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) :
    RecommendationModel.itemFairness R.data.model (R.liftedPolicy ρ) =
      TypeWeightedRecommendationModel.itemFairness R.reduced ρ := by
  unfold RecommendationModel.itemFairness TypeWeightedRecommendationModel.itemFairness
    DecisionCore.finiteMin
  exact Finset.inf'_congr Finset.univ_nonempty rfl
    (by
      intro j _
      exact normalizedItemUtility_liftedPolicy_eq_normalizedItemUtility
        (R := R) (ρ := ρ) (j := j))

/--
With representatives for every user type, lifted reduced policies preserve
minimum user fairness.
-/
theorem userFairness_liftedPolicy_eq_typeFairness {m n K : ℕ}
    [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (ρ : TypePolicy K n) :
    RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ) =
      TypeWeightedRecommendationModel.typeFairness R.reduced ρ := by
  let f : UserType K → ℝ :=
    fun k => TypeWeightedRecommendationModel.normalizedTypeUtility R.reduced ρ k
  calc
    RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ)
        = DecisionCore.finiteMin
            (fun u : User m => f (R.data.types.toType u)) := by
          unfold RecommendationModel.userFairness DecisionCore.finiteMin f
          exact Finset.inf'_congr Finset.univ_nonempty rfl
            (by
              intro u _
              exact normalizedUserUtility_liftedPolicy_eq_normalizedTypeUtility
                (R := R) (ρ := ρ) (u := u))
    _ = DecisionCore.finiteMin f := by
          exact DecisionCore.Policy.finiteMin_comp_of_fiberRepresentatives
            R.data.types.toType reps f
    _ = TypeWeightedRecommendationModel.typeFairness R.reduced ρ := by
          rfl

/--
If the reduced and original optimal values agree, reduced optimality lifts to
original optimality.  This isolates the remaining LP-value equality seam.
-/
theorem isOptimalAtLevel_liftedPolicy_of_reduced
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
  constructor
  · unfold RecommendationModel.feasibleAtLevel
    rw [hItemOpt]
    rw [itemFairness_liftedPolicy_eq_itemFairness (R := R) (ρ := ρ)]
    exact hopt.1
  · rw [userFairness_liftedPolicy_eq_typeFairness (R := R) (reps := reps) (ρ := ρ)]
    rw [hUserOpt]
    exact hopt.2

/--
Every type-symmetric user-level policy has a reduced representative preserving
both fairness functionals exactly.
-/
theorem exists_typePolicy_preserving_fairness_of_isTypeSymmetric
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        RecommendationModel.itemFairness R.data.model ρ =
          TypeWeightedRecommendationModel.itemFairness R.reduced ρK ∧
        RecommendationModel.userFairness R.data.model ρ =
          TypeWeightedRecommendationModel.typeFairness R.reduced ρK := by
  obtain ⟨ρK, hlift⟩ :=
    ReductionWitness.exists_typePolicy_of_isTypeSymmetric R reps hρ
  refine ⟨ρK, hlift, ?_, ?_⟩
  · rw [← hlift]
    exact itemFairness_liftedPolicy_eq_itemFairness (R := R) (ρ := ρK)
  · rw [← hlift]
    exact userFairness_liftedPolicy_eq_typeFairness
      (R := R) (reps := reps) (ρ := ρK)

/--
The item-fairness values attainable by symmetric user-level policies are exactly
the values attainable by reduced type-level policies.
-/
theorem symmetricAttainableItemFairnessSet_eq_reduced
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    RecommendationModel.symmetricAttainableItemFairnessSet R.data =
      TypeWeightedRecommendationModel.attainableItemFairnessSet R.reduced := by
  ext r
  constructor
  · intro hr
    obtain ⟨ρ, hsym, hr⟩ := hr
    obtain ⟨ρK, _hlift, hitem, _huser⟩ :=
      exists_typePolicy_preserving_fairness_of_isTypeSymmetric
        (R := R) (reps := reps) hsym
    refine ⟨ρK, ?_⟩
    rw [hr]
    exact hitem
  · intro hr
    obtain ⟨ρK, hr⟩ := hr
    refine ⟨R.liftedPolicy ρK, R.liftedPolicy_isTypeSymmetric ρK, ?_⟩
    rw [hr]
    exact (itemFairness_liftedPolicy_eq_itemFairness
      (R := R) (ρ := ρK)).symm

/-- Symmetric user-level optimal item fairness equals reduced optimal item fairness. -/
theorem symmetricOptimalItemFairness_eq_reduced
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    RecommendationModel.symmetricOptimalItemFairness R.data =
      TypeWeightedRecommendationModel.optimalItemFairness R.reduced := by
  unfold RecommendationModel.symmetricOptimalItemFairness
    TypeWeightedRecommendationModel.optimalItemFairness
  rw [symmetricAttainableItemFairnessSet_eq_reduced (R := R) (reps := reps)]

/--
Conversely, if a user-level optimum is type-symmetric and the original/reduced
optimal values agree, then it descends to a reduced optimum.
-/
theorem exists_reducedOptimalAtLevel_of_original_symmetric_optimal
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
  obtain ⟨ρK, hlift, hitem, huser⟩ :=
    exists_typePolicy_preserving_fairness_of_isTypeSymmetric
      (R := R) (reps := reps) hρ
  refine ⟨ρK, hlift, ?_⟩
  constructor
  · unfold TypeWeightedRecommendationModel.feasibleAtLevel
    have hfeas := hopt.1
    unfold RecommendationModel.feasibleAtLevel at hfeas
    rw [hItemOpt] at hfeas
    rw [hitem] at hfeas
    exact hfeas
  · have hufair := hopt.2
    rw [hUserOpt] at hufair
    rw [huser] at hufair
    exact hufair

end ReductionWitness

end UserItemFairness
