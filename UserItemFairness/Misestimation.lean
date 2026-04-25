import UserItemFairness.OpposingTypes

open scoped BigOperators
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

theorem theorem4TrueReducedModelTypeZero_bestItemUtility_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeZero beta v) 0 =
      v theorem4FirstItem := by
  change DecisionCore.finiteMax (fun j : Item n => v j) =
    v theorem4FirstItem
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4TrueReducedModelTypeZero_bestItemUtility_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeZero beta v) 1 =
      v theorem4FirstItem := by
  change DecisionCore.finiteMax (fun j : Item n => v (reverseItem j)) =
    v theorem4FirstItem
  rw [finiteMax_reverseItem]
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4TrueReducedModelTypeZero_bestItemUtility_two
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeZero beta v) 2 =
      v theorem4FirstItem := by
  change DecisionCore.finiteMax (fun j : Item n => v j) =
    v theorem4FirstItem
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4TrueReducedModelTypeOne_bestItemUtility_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeOne beta v) 0 =
      v theorem4FirstItem := by
  change DecisionCore.finiteMax (fun j : Item n => v j) =
    v theorem4FirstItem
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4TrueReducedModelTypeOne_bestItemUtility_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeOne beta v) 1 =
      v theorem4FirstItem := by
  change DecisionCore.finiteMax (fun j : Item n => v (reverseItem j)) =
    v theorem4FirstItem
  rw [finiteMax_reverseItem]
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

/-- The estimated cold-start row's paper value `(v_j + v_{n-j+1}) / 2`. -/
noncomputable def theorem4AverageUtility {n : ℕ} (v : Item n → ℝ)
    (j : Item n) : ℝ :=
  (v j + v (reverseItem j)) / 2

@[simp] theorem theorem4AverageUtility_reverse {n : ℕ} [NeZero n]
    (v : Item n → ℝ) (j : Item n) :
    theorem4AverageUtility v (reverseItem j) =
      theorem4AverageUtility v j := by
  unfold theorem4AverageUtility
  rw [reverseItem_reverseItem]
  ring

/-- A pair attaining the cold-start estimated row maximum. -/
noncomputable def theorem4BestAverageItem {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : Item n :=
  Classical.choose
    (DecisionCore.exists_finiteMax_eq (theorem4AverageUtility v))

theorem theorem4BestAverageItem_spec {n : ℕ} [NeZero n]
    (v : Item n → ℝ) :
    DecisionCore.finiteMax (theorem4AverageUtility v) =
      theorem4AverageUtility v (theorem4BestAverageItem v) := by
  exact Classical.choose_spec
    (DecisionCore.exists_finiteMax_eq (theorem4AverageUtility v))

/--
For a cold-start user whose true row is the first opposing type, orient an
estimated-best mirror pair toward the larger true utility.
-/
noncomputable def theorem4BestAverageItemTypeZero {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : Item n :=
  let j := theorem4BestAverageItem v
  if v j < v (reverseItem j) then reverseItem j else j

/-- The mirror-oriented estimated-best item for the second true cold-start row. -/
noncomputable def theorem4BestAverageItemTypeOne {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : Item n :=
  reverseItem (theorem4BestAverageItemTypeZero v)

theorem theorem4AverageUtility_bestAverageItemTypeZero
    {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    theorem4AverageUtility v (theorem4BestAverageItemTypeZero v) =
      DecisionCore.finiteMax (theorem4AverageUtility v) := by
  unfold theorem4BestAverageItemTypeZero
  by_cases h :
      v (theorem4BestAverageItem v) <
        v (reverseItem (theorem4BestAverageItem v))
  · simp [h, theorem4BestAverageItem_spec]
  · simp [h, theorem4BestAverageItem_spec]

theorem theorem4AverageUtility_le_value_bestAverageItemTypeZero
    {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    theorem4AverageUtility v (theorem4BestAverageItemTypeZero v) ≤
      v (theorem4BestAverageItemTypeZero v) := by
  unfold theorem4BestAverageItemTypeZero
  by_cases h :
      v (theorem4BestAverageItem v) <
        v (reverseItem (theorem4BestAverageItem v))
  · simp [h, theorem4AverageUtility, reverseItem_reverseItem]
    linarith
  · have hle :
        v (reverseItem (theorem4BestAverageItem v)) ≤
          v (theorem4BestAverageItem v) := le_of_not_gt h
    simp [h, theorem4AverageUtility]
    linarith

theorem theorem4AverageUtility_bestAverageItemTypeOne
    {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    theorem4AverageUtility v (theorem4BestAverageItemTypeOne v) =
      DecisionCore.finiteMax (theorem4AverageUtility v) := by
  simp [theorem4BestAverageItemTypeOne,
    theorem4AverageUtility_bestAverageItemTypeZero]

theorem theorem4AverageUtility_le_reverse_value_bestAverageItemTypeOne
    {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    theorem4AverageUtility v (theorem4BestAverageItemTypeOne v) ≤
      v (reverseItem (theorem4BestAverageItemTypeOne v)) := by
  simpa [theorem4BestAverageItemTypeOne, reverseItem_reverseItem] using
    theorem4AverageUtility_le_value_bestAverageItemTypeZero v

theorem theorem4AverageUtility_finiteMax_pos
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) :
    0 < DecisionCore.finiteMax (theorem4AverageUtility v) := by
  have hfirst :
      0 < theorem4AverageUtility v theorem4FirstItem := by
    unfold theorem4AverageUtility
    nlinarith [hpos theorem4FirstItem,
      hpos (reverseItem theorem4FirstItem)]
  exact lt_of_lt_of_le hfirst
    (DecisionCore.le_finiteMax (theorem4AverageUtility v) theorem4FirstItem)

theorem theorem4AverageUtility_endpoint_half_lt_finiteMax
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    (hfirst_pos : 0 < v theorem4FirstItem)
    (hlast_pos : 0 < v theorem4LastItem) :
    v theorem4FirstItem / 2 <
      DecisionCore.finiteMax (theorem4AverageUtility v) := by
  have havg :
      v theorem4FirstItem / 2 <
        theorem4AverageUtility v theorem4FirstItem := by
    have hrev_pos : 0 < v (reverseItem theorem4FirstItem) := by
      simpa [theorem4LastItem] using hlast_pos
    unfold theorem4AverageUtility
    nlinarith
  exact lt_of_lt_of_le havg
    (DecisionCore.le_finiteMax (theorem4AverageUtility v) theorem4FirstItem)

theorem theorem4EstimatedReducedModel_bestItemUtility_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4EstimatedReducedModel beta v) 0 =
      v theorem4FirstItem := by
  change DecisionCore.finiteMax (fun j : Item n => v j) =
    v theorem4FirstItem
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4EstimatedReducedModel_bestItemUtility_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4EstimatedReducedModel beta v) 1 =
      v theorem4FirstItem := by
  change DecisionCore.finiteMax (fun j : Item n => v (reverseItem j)) =
    v theorem4FirstItem
  rw [finiteMax_reverseItem]
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4EstimatedReducedModel_bestItemUtility_two
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ} :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4EstimatedReducedModel beta v) 2 =
      DecisionCore.finiteMax (theorem4AverageUtility v) := by
  change DecisionCore.finiteMax
      (fun j : Item n => (v j + v (reverseItem j)) / 2) =
    DecisionCore.finiteMax (theorem4AverageUtility v)
  rfl

noncomputable def theorem4NoFairnessChoiceTypeZero {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : UserType 3 → Item n :=
  fun k =>
    if k = (0 : UserType 3) then theorem4FirstItem
    else if k = (1 : UserType 3) then theorem4LastItem
    else theorem4BestAverageItemTypeZero v

noncomputable def theorem4NoFairnessChoiceTypeOne {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : UserType 3 → Item n :=
  fun k =>
    if k = (0 : UserType 3) then theorem4FirstItem
    else if k = (1 : UserType 3) then theorem4LastItem
    else theorem4BestAverageItemTypeOne v

/--
The no-item-fairness policy from Theorem 4, oriented for a cold-start user whose
true row is the first opposing type.
-/
noncomputable def theorem4NoFairnessPolicyTypeZero {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : TypePolicy 3 n :=
  DecisionCore.Policy.pure (theorem4NoFairnessChoiceTypeZero v)

/--
The no-item-fairness policy from Theorem 4, oriented for a cold-start user whose
true row is the second opposing type.
-/
noncomputable def theorem4NoFairnessPolicyTypeOne {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : TypePolicy 3 n :=
  DecisionCore.Policy.pure (theorem4NoFairnessChoiceTypeOne v)

theorem theorem4EstimatedReducedModel_nonnegativeWeights
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta) :
    (theorem4EstimatedReducedModel beta v).NonnegativeWeights := by
  intro k
  fin_cases k <;> simp [theorem4EstimatedReducedModel, hbeta, hcold]

theorem theorem4EstimatedReducedModel_nonnegativeUtilities
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) :
    (theorem4EstimatedReducedModel beta v).NonnegativeUtilities := by
  intro k j
  fin_cases k
  · simp [theorem4EstimatedReducedModel, (hpos j).le]
  · simp [theorem4EstimatedReducedModel, (hpos (reverseItem j)).le]
  · simp [theorem4EstimatedReducedModel]
    nlinarith [hpos j, hpos (reverseItem j)]

theorem theorem4EstimatedReducedModel_rowHasPositiveItem
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) :
    (theorem4EstimatedReducedModel beta v).RowHasPositiveItem := by
  intro k
  refine ⟨theorem4FirstItem, ?_⟩
  fin_cases k
  · simp [theorem4EstimatedReducedModel, hpos theorem4FirstItem]
  · simp [theorem4EstimatedReducedModel, hpos (reverseItem theorem4FirstItem)]
  · simp [theorem4EstimatedReducedModel]
    nlinarith [hpos theorem4FirstItem,
      hpos (reverseItem theorem4FirstItem)]

/-! ### Appendix E, Lemma 12: mirror symmetrization -/

/-- Appendix E's averaged first known-type row. -/
noncomputable def theorem4SymmetricX {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) : ℝ :=
  ((ρ 0 j).toReal + (ρ 1 (reverseItem j)).toReal) / 2

/-- Appendix E's averaged second known-type row. -/
noncomputable def theorem4SymmetricY {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) : ℝ :=
  ((ρ 1 j).toReal + (ρ 0 (reverseItem j)).toReal) / 2

/-- Appendix E's averaged cold-start row. -/
noncomputable def theorem4SymmetricZ {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) : ℝ :=
  ((ρ 2 j).toReal + (ρ 2 (reverseItem j)).toReal) / 2

theorem theorem4SymmetricX_nonneg {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) :
    0 ≤ theorem4SymmetricX ρ j := by
  unfold theorem4SymmetricX
  have h0 : 0 ≤ (ρ 0 j).toReal := ENNReal.toReal_nonneg
  have h1 : 0 ≤ (ρ 1 (reverseItem j)).toReal := ENNReal.toReal_nonneg
  nlinarith

theorem theorem4SymmetricY_nonneg {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) :
    0 ≤ theorem4SymmetricY ρ j := by
  unfold theorem4SymmetricY
  have h0 : 0 ≤ (ρ 1 j).toReal := ENNReal.toReal_nonneg
  have h1 : 0 ≤ (ρ 0 (reverseItem j)).toReal := ENNReal.toReal_nonneg
  nlinarith

theorem theorem4SymmetricZ_nonneg {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) :
    0 ≤ theorem4SymmetricZ ρ j := by
  unfold theorem4SymmetricZ
  have h0 : 0 ≤ (ρ 2 j).toReal := ENNReal.toReal_nonneg
  have h1 : 0 ≤ (ρ 2 (reverseItem j)).toReal := ENNReal.toReal_nonneg
  nlinarith

theorem theorem4SymmetricX_sum_eq_one {n : ℕ}
    (ρ : TypePolicy 3 n) :
    (∑ j : Item n, theorem4SymmetricX ρ j) = 1 := by
  unfold theorem4SymmetricX
  calc
    (∑ j : Item n,
        ((ρ 0 j).toReal + (ρ 1 (reverseItem j)).toReal) / 2)
        =
        ((∑ j : Item n, (ρ 0 j).toReal) +
          (∑ j : Item n, (ρ 1 (reverseItem j)).toReal)) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ((∑ j : Item n, (ρ 0 j).toReal) +
          (∑ j : Item n, (ρ 1 j).toReal)) / 2 := by
          have hrev :
              (∑ j : Item n, (ρ 1 (reverseItem j)).toReal) =
                ∑ j : Item n, (ρ 1 j).toReal :=
            sum_reverseItem (fun j : Item n => (ρ 1 j).toReal)
          rw [hrev]
    _ = 1 := by
          rw [DecisionCore.pmfToRealSum (ρ 0),
            DecisionCore.pmfToRealSum (ρ 1)]
          norm_num

theorem theorem4SymmetricY_sum_eq_one {n : ℕ}
    (ρ : TypePolicy 3 n) :
    (∑ j : Item n, theorem4SymmetricY ρ j) = 1 := by
  unfold theorem4SymmetricY
  calc
    (∑ j : Item n,
        ((ρ 1 j).toReal + (ρ 0 (reverseItem j)).toReal) / 2)
        =
        ((∑ j : Item n, (ρ 1 j).toReal) +
          (∑ j : Item n, (ρ 0 (reverseItem j)).toReal)) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ((∑ j : Item n, (ρ 1 j).toReal) +
          (∑ j : Item n, (ρ 0 j).toReal)) / 2 := by
          have hrev :
              (∑ j : Item n, (ρ 0 (reverseItem j)).toReal) =
                ∑ j : Item n, (ρ 0 j).toReal :=
            sum_reverseItem (fun j : Item n => (ρ 0 j).toReal)
          rw [hrev]
    _ = 1 := by
          rw [DecisionCore.pmfToRealSum (ρ 0),
            DecisionCore.pmfToRealSum (ρ 1)]
          norm_num

theorem theorem4SymmetricZ_sum_eq_one {n : ℕ}
    (ρ : TypePolicy 3 n) :
    (∑ j : Item n, theorem4SymmetricZ ρ j) = 1 := by
  unfold theorem4SymmetricZ
  calc
    (∑ j : Item n,
        ((ρ 2 j).toReal + (ρ 2 (reverseItem j)).toReal) / 2)
        =
        ((∑ j : Item n, (ρ 2 j).toReal) +
          (∑ j : Item n, (ρ 2 (reverseItem j)).toReal)) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ((∑ j : Item n, (ρ 2 j).toReal) +
          (∑ j : Item n, (ρ 2 j).toReal)) / 2 := by
          have hrev :
              (∑ j : Item n, (ρ 2 (reverseItem j)).toReal) =
                ∑ j : Item n, (ρ 2 j).toReal :=
            sum_reverseItem (fun j : Item n => (ρ 2 j).toReal)
          rw [hrev]
    _ = 1 := by
          rw [DecisionCore.pmfToRealSum (ρ 2)]
          norm_num

/-- Appendix E Lemma 12's mirror-averaged policy. -/
noncomputable def theorem4SymmetrizedPolicy {n : ℕ}
    (ρ : TypePolicy 3 n) : TypePolicy 3 n :=
  fun k =>
    if k = (0 : UserType 3) then
      pmfOfRealVector (theorem4SymmetricX ρ)
        (theorem4SymmetricX_nonneg ρ)
        (theorem4SymmetricX_sum_eq_one ρ)
    else if k = (1 : UserType 3) then
      pmfOfRealVector (theorem4SymmetricY ρ)
        (theorem4SymmetricY_nonneg ρ)
        (theorem4SymmetricY_sum_eq_one ρ)
    else
      pmfOfRealVector (theorem4SymmetricZ ρ)
        (theorem4SymmetricZ_nonneg ρ)
        (theorem4SymmetricZ_sum_eq_one ρ)

@[simp] theorem theorem4SymmetrizedPolicy_zero_toReal {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) :
    ((theorem4SymmetrizedPolicy ρ 0) j).toReal =
      theorem4SymmetricX ρ j := by
  simp [theorem4SymmetrizedPolicy]

@[simp] theorem theorem4SymmetrizedPolicy_one_toReal {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) :
    ((theorem4SymmetrizedPolicy ρ 1) j).toReal =
      theorem4SymmetricY ρ j := by
  simp [theorem4SymmetrizedPolicy]

@[simp] theorem theorem4SymmetrizedPolicy_two_toReal {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) :
    ((theorem4SymmetrizedPolicy ρ 2) j).toReal =
      theorem4SymmetricZ ρ j := by
  have h20 : (2 : UserType 3) ≠ 0 := by decide
  have h21 : (2 : UserType 3) ≠ 1 := by decide
  simp [theorem4SymmetrizedPolicy, h20, h21]

/-- The mirror-symmetric subspace `S'` in Appendix E. -/
def Theorem4MirrorSymmetricPolicy {n : ℕ} (ρ : TypePolicy 3 n) : Prop :=
  (∀ j : Item n, ρ 1 (reverseItem j) = ρ 0 j) ∧
    (∀ j : Item n, ρ 2 (reverseItem j) = ρ 2 j)

theorem theorem4SymmetrizedPolicy_mirrorSymmetric {n : ℕ} [NeZero n]
    (ρ : TypePolicy 3 n) :
    Theorem4MirrorSymmetricPolicy (theorem4SymmetrizedPolicy ρ) := by
  constructor
  · intro j
    apply (ENNReal.toReal_eq_toReal_iff'
      ((theorem4SymmetrizedPolicy ρ 1).apply_ne_top (reverseItem j))
      ((theorem4SymmetrizedPolicy ρ 0).apply_ne_top j)).mp
    simp [theorem4SymmetricX, theorem4SymmetricY,
      reverseItem_reverseItem, add_comm]
  · intro j
    apply (ENNReal.toReal_eq_toReal_iff'
      ((theorem4SymmetrizedPolicy ρ 2).apply_ne_top (reverseItem j))
      ((theorem4SymmetrizedPolicy ρ 2).apply_ne_top j)).mp
    simp [theorem4SymmetricZ, reverseItem_reverseItem, add_comm]

theorem theorem4AverageUtility_pos {n : ℕ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j) (j : Item n) :
    0 < theorem4AverageUtility v j := by
  unfold theorem4AverageUtility
  nlinarith [hpos j, hpos (reverseItem j)]

theorem theorem4EstimatedReducedModel_itemNormalizer_eq_average
    {n : ℕ} (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    TypeWeightedRecommendationModel.itemNormalizer
        (theorem4EstimatedReducedModel beta v) j =
      theorem4AverageUtility v j := by
  unfold TypeWeightedRecommendationModel.itemNormalizer
    theorem4EstimatedReducedModel theorem4AverageUtility
  have huniv : (Finset.univ : Finset (UserType 3)) = {0, 1, 2} := by
    decide
  rw [huniv]
  simp
  ring

theorem theorem4EstimatedReducedModel_rawItemUtility_symmetrized_eq_average
    {n : ℕ} [NeZero n] (beta : ℝ) (v : Item n → ℝ)
    (ρ : TypePolicy 3 n) (j : Item n) :
    TypeWeightedRecommendationModel.rawItemUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) j =
      (TypeWeightedRecommendationModel.rawItemUtility
          (theorem4EstimatedReducedModel beta v) ρ j +
        TypeWeightedRecommendationModel.rawItemUtility
          (theorem4EstimatedReducedModel beta v) ρ (reverseItem j)) / 2 := by
  unfold TypeWeightedRecommendationModel.rawItemUtility
    theorem4EstimatedReducedModel
  have huniv : (Finset.univ : Finset (UserType 3)) = {0, 1, 2} := by
    decide
  rw [huniv]
  simp [theorem4SymmetrizedPolicy, theorem4SymmetricX, theorem4SymmetricY,
    theorem4SymmetricZ, reverseItem_reverseItem]
  ring

theorem theorem4EstimatedReducedModel_normalizedItemUtility_symmetrized_eq_average
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (ρ : TypePolicy 3 n) (j : Item n) :
    TypeWeightedRecommendationModel.normalizedItemUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) j =
      (TypeWeightedRecommendationModel.normalizedItemUtility
          (theorem4EstimatedReducedModel beta v) ρ j +
        TypeWeightedRecommendationModel.normalizedItemUtility
          (theorem4EstimatedReducedModel beta v) ρ (reverseItem j)) / 2 := by
  unfold TypeWeightedRecommendationModel.normalizedItemUtility
  rw [theorem4EstimatedReducedModel_itemNormalizer_eq_average,
    theorem4EstimatedReducedModel_itemNormalizer_eq_average,
    theorem4EstimatedReducedModel_rawItemUtility_symmetrized_eq_average]
  have hden_pos : 0 < theorem4AverageUtility v j :=
    theorem4AverageUtility_pos hpos j
  have hden_ne : theorem4AverageUtility v j ≠ 0 := ne_of_gt hden_pos
  have hrev :
      theorem4AverageUtility v (reverseItem j) =
        theorem4AverageUtility v j := by
    simp [theorem4AverageUtility_reverse]
  simp [hden_ne, hrev]
  field_simp [hden_ne]

theorem theorem4EstimatedReducedModel_itemFairness_le_symmetrized
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.itemFairness
        (theorem4EstimatedReducedModel beta v) ρ ≤
      TypeWeightedRecommendationModel.itemFairness
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) := by
  unfold TypeWeightedRecommendationModel.itemFairness
  apply DecisionCore.le_finiteMin
  intro j
  rw [theorem4EstimatedReducedModel_normalizedItemUtility_symmetrized_eq_average
    hpos ρ j]
  have hj :
      DecisionCore.finiteMin
          (TypeWeightedRecommendationModel.normalizedItemUtility
            (theorem4EstimatedReducedModel beta v) ρ) ≤
        TypeWeightedRecommendationModel.normalizedItemUtility
          (theorem4EstimatedReducedModel beta v) ρ j :=
    DecisionCore.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedItemUtility
        (theorem4EstimatedReducedModel beta v) ρ) j
  have hrev :
      DecisionCore.finiteMin
          (TypeWeightedRecommendationModel.normalizedItemUtility
            (theorem4EstimatedReducedModel beta v) ρ) ≤
        TypeWeightedRecommendationModel.normalizedItemUtility
          (theorem4EstimatedReducedModel beta v) ρ (reverseItem j) :=
    DecisionCore.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedItemUtility
        (theorem4EstimatedReducedModel beta v) ρ) (reverseItem j)
  nlinarith

theorem theorem4EstimatedReducedModel_feasibleAtLevel_symmetrized
    {n : ℕ} [NeZero n] {beta gamma : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hfeas :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (theorem4EstimatedReducedModel beta v) gamma ρ) :
    TypeWeightedRecommendationModel.feasibleAtLevel
        (theorem4EstimatedReducedModel beta v) gamma
        (theorem4SymmetrizedPolicy ρ) := by
  exact hfeas.trans
    (theorem4EstimatedReducedModel_itemFairness_le_symmetrized hpos ρ)

theorem theorem4EstimatedReducedModel_rawTypeUtility_symmetrized_zero
    {n : ℕ} [NeZero n] (beta : ℝ) (v : Item n → ℝ)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.rawTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) 0 =
      (TypeWeightedRecommendationModel.rawTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 0 +
        TypeWeightedRecommendationModel.rawTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 1) / 2 := by
  unfold TypeWeightedRecommendationModel.rawTypeUtility
    DecisionCore.Policy.agentScore DecisionCore.pmfExp
  simp [theorem4EstimatedReducedModel, theorem4SymmetrizedPolicy,
    theorem4SymmetricX]
  have hrev :
      (∑ j : Item n, (ρ 1 (reverseItem j)).toReal * v j) =
        ∑ j : Item n, (ρ 1 j).toReal * v (reverseItem j) := by
    calc
      (∑ j : Item n, (ρ 1 (reverseItem j)).toReal * v j)
          =
          ∑ j : Item n,
            (ρ 1 (reverseItem j)).toReal *
              v (reverseItem (reverseItem j)) := by
            simp [reverseItem_reverseItem]
      _ = ∑ j : Item n, (ρ 1 j).toReal * v (reverseItem j) := by
            simpa using
              (sum_reverseItem
                (fun j : Item n => (ρ 1 j).toReal * v (reverseItem j)))
  calc
    (∑ x : Item n,
        (((ρ 0) x).toReal + ((ρ 1) (reverseItem x)).toReal) / 2 *
          v x)
        =
        ∑ x : Item n,
          (((ρ 0) x).toReal * v x +
            ((ρ 1) (reverseItem x)).toReal * v x) / 2 := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          ring
    _ 
        =
        (∑ x : Item n,
          (((ρ 0) x).toReal * v x +
            ((ρ 1) (reverseItem x)).toReal * v x)) / 2 := by
          rw [Finset.sum_div]
    _ =
        ((∑ x : Item n, ((ρ 0) x).toReal * v x) +
          (∑ x : Item n, ((ρ 1) (reverseItem x)).toReal * v x)) / 2 := by
          rw [Finset.sum_add_distrib]
    _ =
        ((∑ x : Item n, ((ρ 0) x).toReal * v x) +
          (∑ x : Item n, ((ρ 1) x).toReal * v (reverseItem x))) / 2 := by
          rw [hrev]

theorem theorem4EstimatedReducedModel_rawTypeUtility_symmetrized_one
    {n : ℕ} [NeZero n] (beta : ℝ) (v : Item n → ℝ)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.rawTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) 1 =
      (TypeWeightedRecommendationModel.rawTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 0 +
        TypeWeightedRecommendationModel.rawTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 1) / 2 := by
  unfold TypeWeightedRecommendationModel.rawTypeUtility
    DecisionCore.Policy.agentScore DecisionCore.pmfExp
  simp [theorem4EstimatedReducedModel, theorem4SymmetrizedPolicy,
    theorem4SymmetricY]
  have hrev :
      (∑ j : Item n,
          (ρ 0 (reverseItem j)).toReal * v (reverseItem j)) =
        ∑ j : Item n, (ρ 0 j).toReal * v j := by
    simpa using
      (sum_reverseItem (fun j : Item n => (ρ 0 j).toReal * v j))
  calc
    (∑ x : Item n,
        (((ρ 1) x).toReal + ((ρ 0) (reverseItem x)).toReal) / 2 *
          v (reverseItem x))
        =
        ∑ x : Item n,
          (((ρ 1) x).toReal * v (reverseItem x) +
            ((ρ 0) (reverseItem x)).toReal * v (reverseItem x)) / 2 := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          ring
    _ =
        (∑ x : Item n,
          (((ρ 1) x).toReal * v (reverseItem x) +
            ((ρ 0) (reverseItem x)).toReal * v (reverseItem x))) / 2 := by
          rw [Finset.sum_div]
    _ =
        ((∑ x : Item n, ((ρ 1) x).toReal * v (reverseItem x)) +
          (∑ x : Item n,
            ((ρ 0) (reverseItem x)).toReal * v (reverseItem x))) / 2 := by
          rw [Finset.sum_add_distrib]
    _ =
        ((∑ x : Item n, ((ρ 0) x).toReal * v x) +
          (∑ x : Item n, ((ρ 1) x).toReal * v (reverseItem x))) / 2 := by
          rw [hrev]
          ring

theorem theorem4EstimatedReducedModel_rawTypeUtility_symmetrized_two
    {n : ℕ} [NeZero n] (beta : ℝ) (v : Item n → ℝ)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.rawTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) 2 =
      TypeWeightedRecommendationModel.rawTypeUtility
        (theorem4EstimatedReducedModel beta v) ρ 2 := by
  unfold TypeWeightedRecommendationModel.rawTypeUtility
    DecisionCore.Policy.agentScore DecisionCore.pmfExp
  simp [theorem4EstimatedReducedModel, theorem4SymmetrizedPolicy,
    theorem4SymmetricZ]
  have hrev :
      (∑ j : Item n,
          (ρ 2 (reverseItem j)).toReal *
            ((v j + v (reverseItem j)) / 2)) =
        ∑ j : Item n,
          (ρ 2 j).toReal * ((v j + v (reverseItem j)) / 2) := by
    calc
      (∑ j : Item n,
          (ρ 2 (reverseItem j)).toReal *
            ((v j + v (reverseItem j)) / 2))
          =
          ∑ j : Item n,
            (ρ 2 (reverseItem j)).toReal *
              theorem4AverageUtility v (reverseItem j) := by
            simp [theorem4AverageUtility, reverseItem_reverseItem,
              add_comm]
      _ = ∑ j : Item n,
            (ρ 2 j).toReal * theorem4AverageUtility v j := by
            simpa using
              (sum_reverseItem
                (fun j : Item n =>
                  (ρ 2 j).toReal * theorem4AverageUtility v j))
      _ = ∑ j : Item n,
            (ρ 2 j).toReal * ((v j + v (reverseItem j)) / 2) := by
            simp [theorem4AverageUtility]
  calc
    (∑ x : Item n,
        (((ρ 2) x).toReal + ((ρ 2) (reverseItem x)).toReal) / 2 *
          ((v x + v (reverseItem x)) / 2))
        =
        ∑ x : Item n,
          (((ρ 2) x).toReal * ((v x + v (reverseItem x)) / 2) +
            ((ρ 2) (reverseItem x)).toReal *
              ((v x + v (reverseItem x)) / 2)) / 2 := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          ring
    _ =
        (∑ x : Item n,
          (((ρ 2) x).toReal * ((v x + v (reverseItem x)) / 2) +
            ((ρ 2) (reverseItem x)).toReal *
              ((v x + v (reverseItem x)) / 2))) / 2 := by
          rw [Finset.sum_div]
    _ =
        ((∑ x : Item n,
            ((ρ 2) x).toReal * ((v x + v (reverseItem x)) / 2)) +
          (∑ x : Item n,
            ((ρ 2) (reverseItem x)).toReal *
              ((v x + v (reverseItem x)) / 2))) / 2 := by
          rw [Finset.sum_add_distrib]
    _ =
        ∑ x : Item n,
          ((ρ 2) x).toReal * ((v x + v (reverseItem x)) / 2) := by
          rw [hrev]
          ring

theorem theorem4EstimatedReducedModel_bestItemUtility_one_eq_zero
    {n : ℕ} [NeZero n] (beta : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4EstimatedReducedModel beta v) 1 =
      TypeWeightedRecommendationModel.bestItemUtility
        (theorem4EstimatedReducedModel beta v) 0 := by
  unfold TypeWeightedRecommendationModel.bestItemUtility
  change DecisionCore.finiteMax (fun j : Item n => v (reverseItem j)) =
    DecisionCore.finiteMax v
  exact finiteMax_reverseItem v

theorem theorem4EstimatedReducedModel_normalizedTypeUtility_symmetrized_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) 0 =
      (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 0 +
        TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 1) / 2 := by
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [theorem4EstimatedReducedModel_rawTypeUtility_symmetrized_zero]
  rw [theorem4EstimatedReducedModel_bestItemUtility_one_eq_zero]
  have hbest_pos :
      0 < TypeWeightedRecommendationModel.bestItemUtility
          (theorem4EstimatedReducedModel beta v) 0 :=
    TypeWeightedRecommendationModel.bestItemUtility_pos_of_rowHasPositiveItem
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_rowHasPositiveItem hpos) 0
  field_simp [ne_of_gt hbest_pos]

theorem theorem4EstimatedReducedModel_normalizedTypeUtility_symmetrized_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) 1 =
      (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 0 +
        TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 1) / 2 := by
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [theorem4EstimatedReducedModel_rawTypeUtility_symmetrized_one]
  rw [theorem4EstimatedReducedModel_bestItemUtility_one_eq_zero]
  have hbest_pos :
      0 < TypeWeightedRecommendationModel.bestItemUtility
          (theorem4EstimatedReducedModel beta v) 0 :=
    TypeWeightedRecommendationModel.bestItemUtility_pos_of_rowHasPositiveItem
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_rowHasPositiveItem hpos) 0
  field_simp [ne_of_gt hbest_pos]

theorem theorem4EstimatedReducedModel_normalizedTypeUtility_symmetrized_two
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) 2 =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v) ρ 2 := by
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [theorem4EstimatedReducedModel_rawTypeUtility_symmetrized_two]

theorem theorem4EstimatedReducedModel_typeFairness_le_symmetrized
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.typeFairness
        (theorem4EstimatedReducedModel beta v) ρ ≤
      TypeWeightedRecommendationModel.typeFairness
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) := by
  unfold TypeWeightedRecommendationModel.typeFairness
  apply DecisionCore.le_finiteMin
  intro k
  fin_cases k
  · change DecisionCore.finiteMin
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) (0 : UserType 3)
    rw [theorem4EstimatedReducedModel_normalizedTypeUtility_symmetrized_zero
      hpos ρ]
    have h0 :=
      DecisionCore.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) (0 : UserType 3)
    have h1 :=
      DecisionCore.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) (1 : UserType 3)
    nlinarith
  · change DecisionCore.finiteMin
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) (1 : UserType 3)
    rw [theorem4EstimatedReducedModel_normalizedTypeUtility_symmetrized_one
      hpos ρ]
    have h0 :=
      DecisionCore.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) (0 : UserType 3)
    have h1 :=
      DecisionCore.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) (1 : UserType 3)
    nlinarith
  · change DecisionCore.finiteMin
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) (2 : UserType 3)
    rw [theorem4EstimatedReducedModel_normalizedTypeUtility_symmetrized_two]
    exact DecisionCore.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v) ρ) (2 : UserType 3)

/--
Appendix E, Lemma 12: any policy solving the estimated maximal-item-fairness
problem can be mirror-symmetrized into the subspace `S'` without losing
estimated optimality.
-/
theorem theorem4_symmetrizedPolicy_isOptimalAtLevel
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hopt :
      TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 1 ρ) :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 1
        (theorem4SymmetrizedPolicy ρ) ∧
      Theorem4MirrorSymmetricPolicy (theorem4SymmetrizedPolicy ρ) := by
  let T := theorem4EstimatedReducedModel beta v
  have hfeas :
      TypeWeightedRecommendationModel.feasibleAtLevel T 1
        (theorem4SymmetrizedPolicy ρ) :=
    theorem4EstimatedReducedModel_feasibleAtLevel_symmetrized hpos hopt.1
  have htype_lower :
      TypeWeightedRecommendationModel.typeFairness T ρ ≤
        TypeWeightedRecommendationModel.typeFairness T
          (theorem4SymmetrizedPolicy ρ) :=
    theorem4EstimatedReducedModel_typeFairness_le_symmetrized hpos ρ
  have htype_upper :
      TypeWeightedRecommendationModel.typeFairness T
          (theorem4SymmetrizedPolicy ρ) ≤
        TypeWeightedRecommendationModel.typeFairness T ρ :=
    TypeWeightedRecommendationModel.typeFairness_le_of_isOptimalAtLevel
      T (theorem4EstimatedReducedModel_rowHasPositiveItem hpos)
      hopt hfeas
  have htype_eq :
      TypeWeightedRecommendationModel.typeFairness T
          (theorem4SymmetrizedPolicy ρ) =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel T 1 := by
    apply le_antisymm
    · exact htype_upper.trans_eq hopt.2
    · rw [← hopt.2]
      exact htype_lower
  exact ⟨⟨hfeas, htype_eq⟩,
    theorem4SymmetrizedPolicy_mirrorSymmetric ρ⟩

theorem theorem4NoFairnessPolicyTypeZero_estimated_typeFairness_eq_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.typeFairness
        (theorem4EstimatedReducedModel beta v)
        (theorem4NoFairnessPolicyTypeZero v) = 1 := by
  unfold TypeWeightedRecommendationModel.typeFairness
  apply DecisionCore.finiteMin_eq_of_forall
  intro k
  fin_cases k
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeZero, theorem4NoFairnessChoiceTypeZero,
      theorem4EstimatedReducedModel_bestItemUtility_zero hdec]
    exact ne_of_gt (hpos theorem4FirstItem)
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeZero, theorem4NoFairnessChoiceTypeZero,
      theorem4EstimatedReducedModel_bestItemUtility_one hdec, theorem4LastItem]
    rw [reverseItem_reverseItem]
    exact div_self (ne_of_gt (hpos theorem4FirstItem))
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeZero, theorem4NoFairnessChoiceTypeZero,
      theorem4EstimatedReducedModel_bestItemUtility_two]
    change theorem4AverageUtility v (theorem4BestAverageItemTypeZero v) /
        DecisionCore.finiteMax (theorem4AverageUtility v) = 1
    rw [theorem4AverageUtility_bestAverageItemTypeZero]
    exact div_self
      (ne_of_gt (theorem4AverageUtility_finiteMax_pos hpos))

theorem theorem4NoFairnessPolicyTypeOne_estimated_typeFairness_eq_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.typeFairness
        (theorem4EstimatedReducedModel beta v)
        (theorem4NoFairnessPolicyTypeOne v) = 1 := by
  unfold TypeWeightedRecommendationModel.typeFairness
  apply DecisionCore.finiteMin_eq_of_forall
  intro k
  fin_cases k
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeOne, theorem4NoFairnessChoiceTypeOne,
      theorem4EstimatedReducedModel_bestItemUtility_zero hdec]
    exact ne_of_gt (hpos theorem4FirstItem)
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeOne, theorem4NoFairnessChoiceTypeOne,
      theorem4EstimatedReducedModel_bestItemUtility_one hdec, theorem4LastItem]
    rw [reverseItem_reverseItem]
    exact div_self (ne_of_gt (hpos theorem4FirstItem))
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeOne, theorem4NoFairnessChoiceTypeOne,
      theorem4EstimatedReducedModel_bestItemUtility_two]
    change theorem4AverageUtility v (theorem4BestAverageItemTypeOne v) /
        DecisionCore.finiteMax (theorem4AverageUtility v) = 1
    rw [theorem4AverageUtility_bestAverageItemTypeOne]
    exact div_self
      (ne_of_gt (theorem4AverageUtility_finiteMax_pos hpos))

theorem theorem4NoFairnessPolicyTypeZero_estimated_optimalAtLevel_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 0
        (theorem4NoFairnessPolicyTypeZero v) := by
  refine ⟨?_, ?_⟩
  · exact TypeWeightedRecommendationModel.feasibleAtLevel_zero_of_nonnegative
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
      (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
      (theorem4NoFairnessPolicyTypeZero v)
  · rw [theorem4NoFairnessPolicyTypeZero_estimated_typeFairness_eq_one
      hpos hdec]
    rw [TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel_zero_eq_one
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
      (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
      (theorem4EstimatedReducedModel_rowHasPositiveItem hpos)]

theorem theorem4NoFairnessPolicyTypeOne_estimated_optimalAtLevel_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 0
        (theorem4NoFairnessPolicyTypeOne v) := by
  refine ⟨?_, ?_⟩
  · exact TypeWeightedRecommendationModel.feasibleAtLevel_zero_of_nonnegative
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
      (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
      (theorem4NoFairnessPolicyTypeOne v)
  · rw [theorem4NoFairnessPolicyTypeOne_estimated_typeFairness_eq_one
      hpos hdec]
    rw [TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel_zero_eq_one
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
      (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
      (theorem4EstimatedReducedModel_rowHasPositiveItem hpos)]

theorem theorem4NoFairnessPolicyTypeZero_true_typeFairness_ge_half
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    (1 / 2 : ℝ) ≤
      TypeWeightedRecommendationModel.typeFairness
        (theorem4TrueReducedModelTypeZero beta v)
        (theorem4NoFairnessPolicyTypeZero v) := by
  unfold TypeWeightedRecommendationModel.typeFairness
  apply DecisionCore.le_finiteMin
  intro k
  fin_cases k
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeZero, theorem4NoFairnessChoiceTypeZero,
      theorem4TrueReducedModelTypeZero]
    unfold TypeWeightedRecommendationModel.bestItemUtility
    simp
    rw [theorem4_finiteMax_eq_first hdec]
    rw [div_self (ne_of_gt (hpos theorem4FirstItem))]
    norm_num
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeZero, theorem4NoFairnessChoiceTypeZero,
      theorem4TrueReducedModelTypeZero, theorem4LastItem]
    rw [reverseItem_reverseItem]
    unfold TypeWeightedRecommendationModel.bestItemUtility
    simp
    rw [finiteMax_reverseItem, theorem4_finiteMax_eq_first hdec]
    rw [div_self (ne_of_gt (hpos theorem4FirstItem))]
    norm_num
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeZero, theorem4NoFairnessChoiceTypeZero,
      theorem4TrueReducedModelTypeZero]
    have hhalf :
        v theorem4FirstItem / 2 <
          DecisionCore.finiteMax (theorem4AverageUtility v) :=
      theorem4AverageUtility_endpoint_half_lt_finiteMax
        (hpos theorem4FirstItem) (hpos theorem4LastItem)
    have hle_avg :
        DecisionCore.finiteMax (theorem4AverageUtility v) ≤
          v (theorem4BestAverageItemTypeZero v) := by
      rw [← theorem4AverageUtility_bestAverageItemTypeZero v]
      exact theorem4AverageUtility_le_value_bestAverageItemTypeZero v
    have hhalf_value :
        v theorem4FirstItem / 2 <
          v (theorem4BestAverageItemTypeZero v) :=
      lt_of_lt_of_le hhalf hle_avg
    unfold TypeWeightedRecommendationModel.bestItemUtility
    simp
    rw [theorem4_finiteMax_eq_first hdec]
    rw [le_div_iff₀ (hpos theorem4FirstItem)]
    nlinarith

theorem theorem4NoFairnessPolicyTypeOne_true_typeFairness_ge_half
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    (1 / 2 : ℝ) ≤
      TypeWeightedRecommendationModel.typeFairness
        (theorem4TrueReducedModelTypeOne beta v)
        (theorem4NoFairnessPolicyTypeOne v) := by
  unfold TypeWeightedRecommendationModel.typeFairness
  apply DecisionCore.le_finiteMin
  intro k
  fin_cases k
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeOne, theorem4NoFairnessChoiceTypeOne,
      theorem4TrueReducedModelTypeOne]
    unfold TypeWeightedRecommendationModel.bestItemUtility
    simp
    rw [theorem4_finiteMax_eq_first hdec]
    rw [div_self (ne_of_gt (hpos theorem4FirstItem))]
    norm_num
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeOne, theorem4NoFairnessChoiceTypeOne,
      theorem4TrueReducedModelTypeOne, theorem4LastItem]
    rw [reverseItem_reverseItem]
    unfold TypeWeightedRecommendationModel.bestItemUtility
    simp
    rw [finiteMax_reverseItem, theorem4_finiteMax_eq_first hdec]
    rw [div_self (ne_of_gt (hpos theorem4FirstItem))]
    norm_num
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeOne, theorem4NoFairnessChoiceTypeOne,
      theorem4TrueReducedModelTypeOne]
    have hhalf :
        v theorem4FirstItem / 2 <
          DecisionCore.finiteMax (theorem4AverageUtility v) :=
      theorem4AverageUtility_endpoint_half_lt_finiteMax
        (hpos theorem4FirstItem) (hpos theorem4LastItem)
    have hle_avg :
        DecisionCore.finiteMax (theorem4AverageUtility v) ≤
          v (reverseItem (theorem4BestAverageItemTypeOne v)) := by
      rw [← theorem4AverageUtility_bestAverageItemTypeOne v]
      exact theorem4AverageUtility_le_reverse_value_bestAverageItemTypeOne v
    have hhalf_value :
        v theorem4FirstItem / 2 <
          v (reverseItem (theorem4BestAverageItemTypeOne v)) :=
      lt_of_lt_of_le hhalf hle_avg
    unfold TypeWeightedRecommendationModel.bestItemUtility
    simp
    rw [finiteMax_reverseItem, theorem4_finiteMax_eq_first hdec]
    rw [le_div_iff₀ (hpos theorem4FirstItem)]
    nlinarith

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
