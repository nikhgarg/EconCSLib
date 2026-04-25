import UserItemFairness.OpposingTypes

open DecisionCore

namespace UserItemFairness
namespace OpposingTypes

/-!
Appendix E helper definitions for Theorem 4.

The paper's misestimation construction has three estimated user types: the two
opposing known types and a cold-start type whose estimated values are the
average of those two rows.  The true cold-start row is one of the two opposing
rows.  This file isolates the model definitions and the utility bounds used in
the final price-of-misestimation argument.
-/

/-- The first item, corresponding to paper index `1`. -/
def theorem4FirstItem {n : ℕ} [NeZero n] : Item n :=
  ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩

/-- The second item, corresponding to paper index `2`. -/
def theorem4SecondItem {n : ℕ} (hn : 1 < n) : Item n :=
  ⟨1, hn⟩

/-- The last item, corresponding to paper index `n`. -/
def theorem4LastItem {n : ℕ} [NeZero n] : Item n :=
  reverseItem theorem4FirstItem

@[simp] theorem theorem4FirstItem_val {n : ℕ} [NeZero n] :
    (theorem4FirstItem : Item n).val = 0 := rfl

@[simp] theorem theorem4SecondItem_val {n : ℕ} (hn : 1 < n) :
    (theorem4SecondItem hn : Item n).val = 1 := rfl

@[simp] theorem reverseItem_theorem4LastItem {n : ℕ} [NeZero n] :
    reverseItem (theorem4LastItem : Item n) = theorem4FirstItem := by
  simp [theorem4LastItem, reverseItem_reverseItem]

theorem eq_theorem4FirstItem_of_val_eq_zero {n : ℕ} [NeZero n]
    {j : Item n} (hj : j.val = 0) :
    j = theorem4FirstItem := by
  ext
  simpa using hj

theorem theorem4FirstItem_ne_of_val_pos {n : ℕ} [NeZero n]
    {j : Item n} (hj : 0 < j.val) :
    j ≠ theorem4FirstItem := by
  intro h
  rw [h] at hj
  simp at hj

/--
In the strictly decreasing value vector, every non-first item has value at most
the second item.
-/
theorem theorem4_value_le_second_of_ne_first
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    (hn : 1 < n) (hdec : StrictlyDecreasingByIndex v)
    {j : Item n} (hj : j ≠ theorem4FirstItem) :
    v j ≤ v (theorem4SecondItem hn) := by
  have hjpos : 0 < j.val := by
    have hval_ne : j.val ≠ 0 := by
      intro hzero
      exact hj (eq_theorem4FirstItem_of_val_eq_zero hzero)
    exact Nat.pos_of_ne_zero hval_ne
  have hle : (theorem4SecondItem hn : Item n).val ≤ j.val := by
    simpa using hjpos
  exact value_antitone_of_val_le hdec hle

/-- The first item attains the finite maximum of a strictly decreasing vector. -/
theorem theorem4_finiteMax_eq_first
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    DecisionCore.finiteMax v = v theorem4FirstItem := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := DecisionCore.exists_finiteMax_eq v
    rw [hj]
    have hle : (theorem4FirstItem : Item n).val ≤ j.val := by
      simp
    exact value_antitone_of_val_le hdec hle
  · exact DecisionCore.le_finiteMax v theorem4FirstItem

/--
The estimated three-type reduced model from Appendix E. Types `0` and `1` are
the known opposing rows, while type `2` is the cold-start row estimated as the
average of the two.
-/
noncomputable def theorem4EstimatedReducedModel {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel 3 n where
  utility k j :=
    if k = (0 : UserType 3) then v j
    else if k = (1 : UserType 3) then v (reverseItem j)
    else (v j + v (reverseItem j)) / 2
  weight k :=
    if k = (0 : UserType 3) then beta
    else if k = (1 : UserType 3) then beta
    else 1 - 2 * beta

/--
The true three-type model when the cold-start type's actual preferences are the
first opposing row.
-/
noncomputable def theorem4TrueReducedModelTypeZero {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel 3 n where
  utility k j :=
    if k = (0 : UserType 3) then v j
    else if k = (1 : UserType 3) then v (reverseItem j)
    else v j
  weight k :=
    if k = (0 : UserType 3) then beta
    else if k = (1 : UserType 3) then beta
    else 1 - 2 * beta

/--
The true three-type model when the cold-start type's actual preferences are the
second opposing row.
-/
noncomputable def theorem4TrueReducedModelTypeOne {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel 3 n where
  utility k j :=
    if k = (0 : UserType 3) then v j
    else if k = (1 : UserType 3) then v (reverseItem j)
    else v (reverseItem j)
  weight k :=
    if k = (0 : UserType 3) then beta
    else if k = (1 : UserType 3) then beta
    else 1 - 2 * beta

@[simp] theorem theorem4EstimatedReducedModel_utility_zero {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    (theorem4EstimatedReducedModel beta v).utility 0 j = v j := by
  simp [theorem4EstimatedReducedModel]

@[simp] theorem theorem4EstimatedReducedModel_utility_one {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    (theorem4EstimatedReducedModel beta v).utility 1 j =
      v (reverseItem j) := by
  simp [theorem4EstimatedReducedModel]

@[simp] theorem theorem4EstimatedReducedModel_utility_two {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    (theorem4EstimatedReducedModel beta v).utility 2 j =
      (v j + v (reverseItem j)) / 2 := by
  have h20 : (2 : UserType 3) ≠ 0 := by decide
  have h21 : (2 : UserType 3) ≠ 1 := by decide
  simp [theorem4EstimatedReducedModel, h20, h21]

@[simp] theorem theorem4TrueReducedModelTypeZero_utility_two {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    (theorem4TrueReducedModelTypeZero beta v).utility 2 j = v j := by
  have h20 : (2 : UserType 3) ≠ 0 := by decide
  have h21 : (2 : UserType 3) ≠ 1 := by decide
  simp [theorem4TrueReducedModelTypeZero, h20, h21]

@[simp] theorem theorem4TrueReducedModelTypeOne_utility_two {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    (theorem4TrueReducedModelTypeOne beta v).utility 2 j =
      v (reverseItem j) := by
  have h20 : (2 : UserType 3) ≠ 0 := by decide
  simp [theorem4TrueReducedModelTypeOne, h20]

theorem theorem4TrueReducedModelTypeZero_bestItemUtility_two
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeZero beta v) 2 =
      v theorem4FirstItem := by
  change DecisionCore.finiteMax (fun j : Item n => v j) =
    v theorem4FirstItem
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4TrueReducedModelTypeOne_bestItemUtility_two
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeOne beta v) 2 =
      v theorem4FirstItem := by
  change DecisionCore.finiteMax (fun j : Item n => v (reverseItem j)) =
    v theorem4FirstItem
  rw [finiteMax_reverseItem]
  exact theorem4_finiteMax_eq_first hdec

/--
Appendix E, Theorem 4 utility bound for a cold-start user of the first true
type: if the estimated optimum gives the cold-start row no probability on item
`1`, and `v₂` is below `eps/n` times `v₁`, then this user's normalized utility
is below `eps/n`.
-/
theorem paper_theorem4_coldStart_typeZero_normalizedUtility_lt
    {n : ℕ} [NeZero n] {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (hdec : StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v theorem4FirstItem)
    (hsmall : v (theorem4SecondItem hn) <
      eps / (n : ℝ) * v theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_first : ρ 2 theorem4FirstItem = 0) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4TrueReducedModelTypeZero beta v) ρ 2 <
      eps / (n : ℝ) := by
  have hraw :
      TypeWeightedRecommendationModel.rawTypeUtility
          (theorem4TrueReducedModelTypeZero beta v) ρ 2 <
        eps / (n : ℝ) * v theorem4FirstItem := by
    unfold TypeWeightedRecommendationModel.rawTypeUtility
      DecisionCore.Policy.agentScore
    change DecisionCore.pmfExp (ρ 2) (fun j : Item n => v j) <
      eps / (n : ℝ) * v theorem4FirstItem
    refine DecisionCore.pmfExp_lt_of_support_forall_lt
      (ρ 2) v (eps / (n : ℝ) * v theorem4FirstItem) ?_
    intro j hmass
    have hj_ne : j ≠ theorem4FirstItem := by
      intro hj
      subst j
      have hmass_zero : ((ρ 2 theorem4FirstItem).toReal) = 0 := by
        simpa [hno_first]
      linarith
    exact lt_of_le_of_lt
      (theorem4_value_le_second_of_ne_first hn hdec hj_ne) hsmall
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [theorem4TrueReducedModelTypeZero_bestItemUtility_two hdec]
  rw [div_lt_iff₀ hfirst_pos]
  exact hraw

/--
Appendix E, Theorem 4 utility bound for a cold-start user of the second true
type: if the estimated optimum gives the cold-start row no probability on item
`n`, and `v₂` is below `eps/n` times `v₁`, then this user's normalized utility
is below `eps/n`.
-/
theorem paper_theorem4_coldStart_typeOne_normalizedUtility_lt
    {n : ℕ} [NeZero n] {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (hdec : StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v theorem4FirstItem)
    (hsmall : v (theorem4SecondItem hn) <
      eps / (n : ℝ) * v theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_last : ρ 2 theorem4LastItem = 0) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4TrueReducedModelTypeOne beta v) ρ 2 <
      eps / (n : ℝ) := by
  have hraw :
      TypeWeightedRecommendationModel.rawTypeUtility
          (theorem4TrueReducedModelTypeOne beta v) ρ 2 <
        eps / (n : ℝ) * v theorem4FirstItem := by
    unfold TypeWeightedRecommendationModel.rawTypeUtility
      DecisionCore.Policy.agentScore
    change DecisionCore.pmfExp (ρ 2)
        (fun j : Item n => v (reverseItem j)) <
      eps / (n : ℝ) * v theorem4FirstItem
    refine DecisionCore.pmfExp_lt_of_support_forall_lt
      (ρ 2) (fun j : Item n => v (reverseItem j))
      (eps / (n : ℝ) * v theorem4FirstItem) ?_
    intro j hmass
    have hj_ne_last : j ≠ theorem4LastItem := by
      intro hj
      subst j
      have hmass_zero : ((ρ 2 theorem4LastItem).toReal) = 0 := by
        simpa [hno_last]
      linarith
    have hrev_ne_first : reverseItem j ≠ theorem4FirstItem := by
      intro hrev
      have hj_last : j = theorem4LastItem := by
        have h := congrArg reverseItem hrev
        simpa [theorem4LastItem, reverseItem_reverseItem] using h
      exact hj_ne_last hj_last
    exact lt_of_le_of_lt
      (theorem4_value_le_second_of_ne_first hn hdec hrev_ne_first)
      hsmall
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [theorem4TrueReducedModelTypeOne_bestItemUtility_two hdec]
  rw [div_lt_iff₀ hfirst_pos]
  exact hraw

theorem paper_theorem4_coldStart_typeZero_typeFairness_lt
    {n : ℕ} [NeZero n] {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (hdec : StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v theorem4FirstItem)
    (hsmall : v (theorem4SecondItem hn) <
      eps / (n : ℝ) * v theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_first : ρ 2 theorem4FirstItem = 0) :
    TypeWeightedRecommendationModel.typeFairness
        (theorem4TrueReducedModelTypeZero beta v) ρ <
      eps / (n : ℝ) := by
  exact lt_of_le_of_lt
    (DecisionCore.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4TrueReducedModelTypeZero beta v) ρ) 2)
    (paper_theorem4_coldStart_typeZero_normalizedUtility_lt
      hn hdec hfirst_pos hsmall ρ hno_first)

theorem paper_theorem4_coldStart_typeOne_typeFairness_lt
    {n : ℕ} [NeZero n] {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (hdec : StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v theorem4FirstItem)
    (hsmall : v (theorem4SecondItem hn) <
      eps / (n : ℝ) * v theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_last : ρ 2 theorem4LastItem = 0) :
    TypeWeightedRecommendationModel.typeFairness
        (theorem4TrueReducedModelTypeOne beta v) ρ <
      eps / (n : ℝ) := by
  exact lt_of_le_of_lt
    (DecisionCore.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4TrueReducedModelTypeOne beta v) ρ) 2)
    (paper_theorem4_coldStart_typeOne_normalizedUtility_lt
      hn hdec hfirst_pos hsmall ρ hno_last)

end OpposingTypes

namespace EstimatedRecommendationModel

/--
Theorem 4 fairness-constrained misestimation bridge, first true cold-start type.

The remaining estimated-LP obligation is exactly the paper's Appendix E
no-extreme-item certificate for the estimated optimum: the cold-start type's
row assigns zero mass to item `1`.
-/
theorem theorem4_misestimation_with_fairness_large_typeZero_from_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v OpposingTypes.theorem4FirstItem)
    (hsmall : v (OpposingTypes.theorem4SecondItem hn) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_first : ρ 2 OpposingTypes.theorem4FirstItem = 0) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have htype :
      TypeWeightedRecommendationModel.typeFairness
          (OpposingTypes.theorem4TrueReducedModelTypeZero beta v) ρ <
        eps / (n : ℝ) :=
    OpposingTypes.paper_theorem4_coldStart_typeZero_typeFairness_lt
      hn hdec hfirst_pos hsmall ρ hno_first
  have htypeR :
      TypeWeightedRecommendationModel.typeFairness R.reduced ρ <
        eps / (n : ℝ) := by
    rw [hred]
    exact htype
  have huserR :
      RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ) <
        eps / (n : ℝ) := by
    rw [R.userFairness_liftedPolicy_eq_typeFairness reps ρ]
    exact htypeR
  have huserE :
      RecommendationModel.userFairness E.trueModel (R.liftedPolicy ρ) <
        eps / (n : ℝ) := by
    rw [htrue]
    exact huserR
  exact E.priceOfMisestimation_gt_one_sub_of_userFairness_lt_div_card
    eps (R.liftedPolicy ρ) heps hbase huserE

/--
Theorem 4 fairness-constrained misestimation bridge, second true cold-start
type.

The remaining estimated-LP obligation is the mirror no-extreme-item
certificate: the cold-start type's row assigns zero mass to item `n`.
-/
theorem theorem4_misestimation_with_fairness_large_typeOne_from_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v OpposingTypes.theorem4FirstItem)
    (hsmall : v (OpposingTypes.theorem4SecondItem hn) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_last : ρ 2 OpposingTypes.theorem4LastItem = 0) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have htype :
      TypeWeightedRecommendationModel.typeFairness
          (OpposingTypes.theorem4TrueReducedModelTypeOne beta v) ρ <
        eps / (n : ℝ) :=
    OpposingTypes.paper_theorem4_coldStart_typeOne_typeFairness_lt
      hn hdec hfirst_pos hsmall ρ hno_last
  have htypeR :
      TypeWeightedRecommendationModel.typeFairness R.reduced ρ <
        eps / (n : ℝ) := by
    rw [hred]
    exact htype
  have huserR :
      RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ) <
        eps / (n : ℝ) := by
    rw [R.userFairness_liftedPolicy_eq_typeFairness reps ρ]
    exact htypeR
  have huserE :
      RecommendationModel.userFairness E.trueModel (R.liftedPolicy ρ) <
        eps / (n : ℝ) := by
    rw [htrue]
    exact huserR
  exact E.priceOfMisestimation_gt_one_sub_of_userFairness_lt_div_card
    eps (R.liftedPolicy ρ) heps hbase huserE

end EstimatedRecommendationModel
end UserItemFairness
