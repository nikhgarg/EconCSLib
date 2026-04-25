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

theorem theorem4FirstItem_val_lt_of_ne {n : ℕ} [NeZero n]
    {j : Item n} (hj : j ≠ theorem4FirstItem) :
    (theorem4FirstItem : Item n).val < j.val := by
  have hval_ne : j.val ≠ 0 := by
    intro hzero
    exact hj (eq_theorem4FirstItem_of_val_eq_zero hzero)
  simpa using Nat.pos_of_ne_zero hval_ne

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

/-! ### Appendix E, Problem 11: estimated LP in `S'` coordinates -/

/--
Problem 11's item value in the paper's `x,z,λ` notation after restricting to
the mirror-symmetric subspace `S'`.
-/
noncomputable def theorem4Problem11ItemValue {n : ℕ}
    (beta : ℝ) (v x z : Item n → ℝ) (j : Item n) : ℝ :=
  2 * beta *
      (pairShare (1 / 2) v j * x j +
        (1 - pairShare (1 / 2) v j) * x (reverseItem j)) +
    (1 - 2 * beta) * z j

/-- Problem 11's item value for a type policy in `S'`. -/
noncomputable def theorem4Problem11PolicyItemValue {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n)
    (j : Item n) : ℝ :=
  theorem4Problem11ItemValue beta v
    (fun l : Item n => (ρ 0 l).toReal)
    (fun l : Item n => (ρ 2 l).toReal) j

/--
Problem 11 translation: on the mirror-symmetric subspace `S'`, the estimated
normalized item utility is exactly the paper's linear expression in `x` and
`z`.
-/
theorem theorem4EstimatedReducedModel_normalizedItemUtility_eq_problem11
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hsym : Theorem4MirrorSymmetricPolicy ρ)
    (j : Item n) :
    TypeWeightedRecommendationModel.normalizedItemUtility
        (theorem4EstimatedReducedModel beta v) ρ j =
      theorem4Problem11PolicyItemValue beta v ρ j := by
  have hy :
      (ρ 1 j).toReal = (ρ 0 (reverseItem j)).toReal := by
    have h := hsym.1 (reverseItem j)
    simpa [reverseItem_reverseItem] using congrArg ENNReal.toReal h
  unfold TypeWeightedRecommendationModel.normalizedItemUtility
  rw [theorem4EstimatedReducedModel_itemNormalizer_eq_average]
  have hden_avg : theorem4AverageUtility v j ≠ 0 :=
    ne_of_gt (theorem4AverageUtility_pos hpos j)
  simp [hden_avg]
  unfold TypeWeightedRecommendationModel.rawItemUtility
    theorem4EstimatedReducedModel theorem4Problem11PolicyItemValue
    theorem4Problem11ItemValue theorem4AverageUtility pairShare
  have huniv : (Finset.univ : Finset (UserType 3)) = {0, 1, 2} := by
    decide
  rw [huniv]
  simp [hy]
  have hsum_pos : 0 < v j + v (reverseItem j) := by
    nlinarith [hpos j, hpos (reverseItem j)]
  have hsum_ne : v j + v (reverseItem j) ≠ 0 := ne_of_gt hsum_pos
  have hpair_denom_ne :
      (2 : ℝ)⁻¹ * v j + (1 - (2 : ℝ)⁻¹) *
          v (reverseItem j) ≠ 0 := by
    nlinarith
  have hcomp :
      1 - typeOneShare (2 : ℝ)⁻¹ (v j) (v (reverseItem j)) =
        (1 - (2 : ℝ)⁻¹) * v (reverseItem j) /
          ((2 : ℝ)⁻¹ * v j + (1 - (2 : ℝ)⁻¹) *
            v (reverseItem j)) :=
    one_sub_typeOneShare_eq hpair_denom_ne
  rw [hcomp]
  unfold typeOneShare
  norm_num
  field_simp [hsum_ne]
  ring

/-- Problem 11 epigraph feasibility in the paper's `x,z,λ` notation. -/
def theorem4Problem11LPFeasible {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) (ell : ℝ) : Prop :=
  ∀ j : Item n, ell ≤ theorem4Problem11PolicyItemValue beta v ρ j

/--
For a mirror-symmetric policy, Problem 11 epigraph feasibility is equivalent to
being below the reduced estimated item-fairness value.
-/
theorem theorem4Problem11LPFeasible_iff_le_itemFairness
    {n : ℕ} [NeZero n] {beta ell : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hsym : Theorem4MirrorSymmetricPolicy ρ) :
    theorem4Problem11LPFeasible beta v ρ ell ↔
      ell ≤
        TypeWeightedRecommendationModel.itemFairness
          (theorem4EstimatedReducedModel beta v) ρ := by
  constructor
  · intro h
    unfold TypeWeightedRecommendationModel.itemFairness
    apply DecisionCore.le_finiteMin
    intro j
    rw [theorem4EstimatedReducedModel_normalizedItemUtility_eq_problem11
      hpos hsym j]
    exact h j
  · intro h j
    rw [← theorem4EstimatedReducedModel_normalizedItemUtility_eq_problem11
      hpos hsym j]
    exact h.trans
      (DecisionCore.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedItemUtility
          (theorem4EstimatedReducedModel beta v) ρ) j)

/-- A policy/value pair is optimal for the Problem 11 epigraph LP. -/
def Theorem4Problem11PolicyOptimal {n : ℕ} [NeZero n]
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) (ell : ℝ) : Prop :=
  Theorem4MirrorSymmetricPolicy ρ ∧
    theorem4Problem11LPFeasible beta v ρ ell ∧
      ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
        Theorem4MirrorSymmetricPolicy ρ' →
          theorem4Problem11LPFeasible beta v ρ' ell' → ell' ≤ ell

/--
An estimated `γ = 1` optimum in the mirror-symmetric subspace solves the
Problem 11 epigraph LP with objective value equal to its item-fairness value.
-/
theorem theorem4Problem11PolicyOptimal_of_isOptimalAtLevel
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hsym : Theorem4MirrorSymmetricPolicy ρ)
    (hopt :
      TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 1 ρ) :
    Theorem4Problem11PolicyOptimal beta v ρ
      (TypeWeightedRecommendationModel.itemFairness
        (theorem4EstimatedReducedModel beta v) ρ) := by
  let T := theorem4EstimatedReducedModel beta v
  refine ⟨hsym, ?_, ?_⟩
  · exact (theorem4Problem11LPFeasible_iff_le_itemFairness
      hpos hsym).mpr le_rfl
  · intro ρ' ell' hsym' hfeas'
    have hell_le_item :
        ell' ≤ TypeWeightedRecommendationModel.itemFairness T ρ' :=
      (theorem4Problem11LPFeasible_iff_le_itemFairness
        hpos hsym').mp hfeas'
    have hbdd :
        BddAbove (TypeWeightedRecommendationModel.attainableItemFairnessSet T) :=
      TypeWeightedRecommendationModel.attainableItemFairnessSet_bddAbove_of_nonnegative
        T
        (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
        (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
    have hmem :
        TypeWeightedRecommendationModel.itemFairness T ρ' ∈
          TypeWeightedRecommendationModel.attainableItemFairnessSet T := by
      exact ⟨ρ', rfl⟩
    have hitem_le_opt :
        TypeWeightedRecommendationModel.itemFairness T ρ' ≤
          TypeWeightedRecommendationModel.optimalItemFairness T :=
      le_csSup hbdd hmem
    have hopt_le_item :
        TypeWeightedRecommendationModel.optimalItemFairness T ≤
          TypeWeightedRecommendationModel.itemFairness T ρ := by
      simpa [TypeWeightedRecommendationModel.feasibleAtLevel] using hopt.1
    exact hell_le_item.trans (hitem_le_opt.trans hopt_le_item)

/-- An optimal Problem 11 epigraph value is the minimum item value of its policy. -/
theorem theorem4Problem11PolicyOptimal_value_eq_finiteMin
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    ell =
      DecisionCore.finiteMin
        (fun j : Item n => theorem4Problem11PolicyItemValue beta v ρ j) := by
  let value : Item n → ℝ :=
    fun j : Item n => theorem4Problem11PolicyItemValue beta v ρ j
  have hell_le_min : ell ≤ DecisionCore.finiteMin value := by
    apply DecisionCore.le_finiteMin
    intro j
    exact hopt.2.1 j
  have hmin_feas :
      theorem4Problem11LPFeasible beta v ρ
        (DecisionCore.finiteMin value) := by
    intro j
    exact DecisionCore.finiteMin_le value j
  have hmin_le_ell :
      DecisionCore.finiteMin value ≤ ell :=
    hopt.2.2 ρ (DecisionCore.finiteMin value) hopt.1 hmin_feas
  exact le_antisymm hell_le_min hmin_le_ell

/--
Problem 11 equality-form optimal package. This is the formal target for the
remaining Appendix E Lemmas 13-15 selected-BFS argument.
-/
structure Theorem4Problem11EqualizedBasicOptimal {n : ℕ} [NeZero n]
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) (ell : ℝ) :
    Prop where
  mirror : Theorem4MirrorSymmetricPolicy ρ
  item_eq :
    ∀ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j = ell
  optimal : Theorem4Problem11PolicyOptimal beta v ρ ell
  basic_feasible : TypePolicy.BasicFeasibleSupportCertificate ρ

theorem theorem4UniformTypePolicy_mirrorSymmetric {n : ℕ} [NeZero n] :
    Theorem4MirrorSymmetricPolicy
      (TypeWeightedRecommendationModel.uniformTypePolicy (K := 3) (n := n)) := by
  constructor
  · intro j
    simp [TypeWeightedRecommendationModel.uniformTypePolicy]
  · intro j
    simp [TypeWeightedRecommendationModel.uniformTypePolicy]

theorem theorem4Problem11UniformPolicyItemValue_eq_inv_card
    {n : ℕ} [NeZero n] (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    theorem4Problem11PolicyItemValue beta v
        (TypeWeightedRecommendationModel.uniformTypePolicy (K := 3) (n := n)) j =
      (n : ℝ)⁻¹ := by
  unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue
  simp [TypeWeightedRecommendationModel.uniformTypePolicy_apply_toReal]
  ring

theorem theorem4Problem11PolicyOptimal_value_pos
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    0 < ell := by
  let ρu : TypePolicy 3 n :=
    TypeWeightedRecommendationModel.uniformTypePolicy (K := 3) (n := n)
  have hinv_pos : 0 < (n : ℝ)⁻¹ := by
    have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact inv_pos.mpr (by exact_mod_cast hnpos_nat)
  have hsym : Theorem4MirrorSymmetricPolicy ρu :=
    theorem4UniformTypePolicy_mirrorSymmetric
  have hfeas : theorem4Problem11LPFeasible beta v ρu ((n : ℝ)⁻¹) := by
    intro j
    rw [theorem4Problem11UniformPolicyItemValue_eq_inv_card]
  have hle : (n : ℝ)⁻¹ ≤ ell :=
    hopt.2.2 ρu ((n : ℝ)⁻¹) hsym hfeas
  exact lt_of_lt_of_le hinv_pos hle

theorem theorem4Problem11_item_coverage_of_equalized_policyOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    ∀ j : Item n,
      ρ 0 j ≠ 0 ∨ ρ 0 (reverseItem j) ≠ 0 ∨ ρ 2 j ≠ 0 := by
  intro j
  by_contra hnone
  push Not at hnone
  have hitem := h.item_eq j
  have hzero :
      theorem4Problem11PolicyItemValue beta v ρ j = 0 := by
    unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue
    simp [hnone.1, hnone.2.1, hnone.2.2]
  have hell_pos : 0 < ell :=
    theorem4Problem11PolicyOptimal_value_pos h.optimal
  rw [hzero] at hitem
  linarith

theorem theorem4Problem11_type_item_coverage_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    ∀ j : Item n, ∃ k : UserType 3, ρ k j ≠ 0 := by
  intro j
  rcases theorem4Problem11_item_coverage_of_equalized_policyOptimal h j with
    h0 | h0rev | h2
  · exact ⟨0, h0⟩
  · refine ⟨1, ?_⟩
    have hmirror :
        ρ 1 j = ρ 0 (reverseItem j) := by
      simpa [reverseItem_reverseItem] using h.mirror.1 (reverseItem j)
    rwa [hmirror]
  · exact ⟨2, h2⟩

theorem theorem4Problem11_sharedItemsBound_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    TypePolicy.SharedItemsBound ρ := by
  have hactive : TypePolicy.ActivePairsBound ρ :=
    TypePolicy.activePairsBound_of_basicFeasibleSupportCertificate
      ρ h.basic_feasible
  exact TypePolicy.sharedItemsBound_of_activePairsBound_of_item_coverage
    ρ hactive
    (theorem4Problem11_type_item_coverage_of_equalizedBasicOptimal h)

def Theorem4Problem11PolicyNoStrictPointwiseImprovement {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) : Prop :=
  ¬ ∃ ρ' : TypePolicy 3 n,
    Theorem4MirrorSymmetricPolicy ρ' ∧
      ∀ j : Item n,
        theorem4Problem11PolicyItemValue beta v ρ j <
          theorem4Problem11PolicyItemValue beta v ρ' j

theorem theorem4Problem11_noStrictPointwiseImprovement_of_policyOptimal_equalized
    {n : ℕ} [NeZero n]
    {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n} {ell : ℝ}
    (hitem_eq :
      ∀ l : Item n, theorem4Problem11PolicyItemValue beta v ρ l = ell)
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ := by
  intro himprove
  rcases himprove with ⟨ρ', hsym', hstrict⟩
  let gap : Item n → ℝ :=
    fun j => theorem4Problem11PolicyItemValue beta v ρ' j - ell
  let delta : ℝ := DecisionCore.finiteMin gap
  have hgap_pos : ∀ j : Item n, 0 < gap j := by
    intro j
    dsimp [gap]
    have hbase : theorem4Problem11PolicyItemValue beta v ρ j = ell :=
      hitem_eq j
    have hlt := hstrict j
    rw [hbase] at hlt
    linarith
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact DecisionCore.finiteMin_pos gap hgap_pos
  have hfeas' :
      theorem4Problem11LPFeasible beta v ρ' (ell + delta) := by
    intro j
    have hle := DecisionCore.finiteMin_le gap j
    dsimp [delta, gap] at hle
    linarith
  have hle : ell + delta ≤ ell :=
    hopt.2.2 ρ' (ell + delta) hsym' hfeas'
  linarith

theorem theorem4Problem11_noStrictPointwiseImprovement_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n]
    {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ := by
  exact theorem4Problem11_noStrictPointwiseImprovement_of_policyOptimal_equalized
    h.item_eq h.optimal

/-! ### Appendix E, Lemma 17: no right-half `x` support -/

/--
Lemma 17 perturbation of the Problem 11 known-type row: remove the donor mass
at `j`, move all but `eps` of it to the mirror item, and spread `eps` over the
unaffected coordinates through `r`.
-/
noncomputable def theorem4Problem11RightHalfShiftX {n : ℕ}
    (x r : Item n → ℝ) (j : Item n) (eps : ℝ) : Item n → ℝ :=
  lemma4GapExchangeX x j (reverseItem j) (x j) eps r

theorem theorem4Problem11RightHalfShiftX_donor_eq_zero
    {n : ℕ} {x r : Item n → ℝ} {j : Item n} {eps : ℝ}
    (hne : j ≠ reverseItem j) (hrj : r j = 0) :
    theorem4Problem11RightHalfShiftX x r j eps j = 0 := by
  unfold theorem4Problem11RightHalfShiftX lemma4GapExchangeX
  simp [hne, hrj]

theorem theorem4Problem11RightHalfShiftX_receiver_eq
    {n : ℕ} {x r : Item n → ℝ} {j : Item n} {eps : ℝ}
    (hne : j ≠ reverseItem j) (hrrev : r (reverseItem j) = 0) :
    theorem4Problem11RightHalfShiftX x r j eps (reverseItem j) =
      x (reverseItem j) + (x j - eps) := by
  unfold theorem4Problem11RightHalfShiftX lemma4GapExchangeX
  simp [hne.symm, hrrev]

theorem theorem4Problem11RightHalfShiftX_other_eq
    {n : ℕ} {x r : Item n → ℝ} {j l : Item n} {eps : ℝ}
    (hlj : l ≠ j) (hlrev : l ≠ reverseItem j) :
    theorem4Problem11RightHalfShiftX x r j eps l =
      x l + eps * r l := by
  unfold theorem4Problem11RightHalfShiftX lemma4GapExchangeX
  simp [hlj, hlrev]

theorem theorem4Problem11RightHalfShiftX_sum_eq
    {n : ℕ} {x r : Item n → ℝ} {j : Item n} {eps : ℝ}
    (hrsum : (∑ l : Item n, r l) = 1) :
    (∑ l : Item n, theorem4Problem11RightHalfShiftX x r j eps l) =
      ∑ l : Item n, x l := by
  exact lemma4GapExchangeX_sum_eq x j (reverseItem j) (x j) eps r hrsum

theorem theorem4Problem11RightHalfShiftX_nonneg
    {n : ℕ} {x r : Item n → ℝ} {j : Item n} {eps : ℝ}
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hne : j ≠ reverseItem j)
    (hr_nonneg : ∀ l : Item n, 0 ≤ r l)
    (hrj : r j = 0) (hrrev : r (reverseItem j) = 0)
    (heps_pos : 0 < eps) (heps_lt : eps < x j) :
    ∀ l : Item n, 0 ≤ theorem4Problem11RightHalfShiftX x r j eps l := by
  intro l
  by_cases hlj : l = j
  · subst l
    rw [theorem4Problem11RightHalfShiftX_donor_eq_zero hne hrj]
  · by_cases hlrev : l = reverseItem j
    · subst l
      rw [theorem4Problem11RightHalfShiftX_receiver_eq hne hrrev]
      nlinarith [hx_nonneg (reverseItem j), heps_lt]
    · rw [theorem4Problem11RightHalfShiftX_other_eq hlj hlrev]
      exact add_nonneg (hx_nonneg l)
        (mul_nonneg heps_pos.le (hr_nonneg l))

/--
Appendix E, Lemma 17 real-vector perturbation. If a Problem 11 solution gives
positive known-type mass to an item strictly after its mirror, then shifting
that mass left and spreading a tiny amount over the remaining coordinates
strictly improves every Problem 11 item value.
-/
theorem theorem4Problem11_rightHalfShift_exists_strictlyImproves
    {n : ℕ} {beta : ℝ} {v x z : Item n → ℝ} {j : Item n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hj_right : (reverseItem j).val < j.val)
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hsumx : (∑ l : Item n, x l) = 1)
    (hxj_pos : 0 < x j) :
    ∃ x' : Item n → ℝ,
      (∀ l : Item n, 0 ≤ x' l) ∧
      (∑ l : Item n, x' l) = 1 ∧
      ∀ l : Item n,
        theorem4Problem11ItemValue beta v x z l <
          theorem4Problem11ItemValue beta v x' z l := by
  classical
  let a : Item n := reverseItem j
  have hne : j ≠ a := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [a] at hval
    omega
  have hane : a ≠ j := hne.symm
  have ha_lt_rev : a.val < (reverseItem a).val := by
    simpa [a, reverseItem_reverseItem] using hj_right
  let qa : ℝ := pairShare (1 / 2) v a
  have hqa_half : (1 / 2 : ℝ) < qa := by
    dsimp [qa]
    exact half_lt_pairShare_half_of_val_lt_reverse a hpos hdec ha_lt_rev
  have hqa_lt_one : qa < 1 := by
    dsimp [qa]
    exact pairShare_lt_one a (by norm_num) (by norm_num) hpos
  let cap : ℝ := (2 * qa - 1) * x j
  have hcap_pos : 0 < cap := by
    dsimp [cap]
    nlinarith
  let eps : ℝ := min (x j) cap / 2
  have hmin_pos : 0 < min (x j) cap := lt_min hxj_pos hcap_pos
  have heps_pos : 0 < eps := by
    dsimp [eps]
    nlinarith
  have heps_lt_min : eps < min (x j) cap := by
    dsimp [eps]
    nlinarith
  have heps_lt_xj : eps < x j :=
    lt_of_lt_of_le heps_lt_min (min_le_left _ _)
  have heps_lt_cap : eps < cap :=
    lt_of_lt_of_le heps_lt_min (min_le_right _ _)
  obtain ⟨r, hr_nonneg, hr_pos, hrj, hra, hrsum⟩ :=
    lemma4_redistribution_exists_of_two_lt hn hne
  let x' : Item n → ℝ := theorem4Problem11RightHalfShiftX x r j eps
  have hx'_nonneg : ∀ l : Item n, 0 ≤ x' l := by
    intro l
    exact theorem4Problem11RightHalfShiftX_nonneg
      hx_nonneg hne hr_nonneg hrj hra heps_pos heps_lt_xj l
  have hx'_sum : (∑ l : Item n, x' l) = 1 := by
    dsimp [x']
    rw [theorem4Problem11RightHalfShiftX_sum_eq hrsum, hsumx]
  refine ⟨x', hx'_nonneg, hx'_sum, ?_⟩
  intro l
  have hq_pos : 0 < pairShare (1 / 2) v l :=
    pairShare_pos l (by norm_num) (by norm_num) hpos
  have hq_lt_one : pairShare (1 / 2) v l < 1 :=
    pairShare_lt_one l (by norm_num) (by norm_num) hpos
  unfold theorem4Problem11ItemValue
  by_cases hlj : l = j
  · subst l
    have hxj' : x' j = 0 := by
      dsimp [x']
      exact theorem4Problem11RightHalfShiftX_donor_eq_zero hne hrj
    have hxa' : x' a = x a + (x j - eps) := by
      dsimp [x']
      exact theorem4Problem11RightHalfShiftX_receiver_eq hne hra
    have hshare :
        pairShare (1 / 2) v j = 1 - qa := by
      dsimp [qa, a]
      rw [pairShare_half_eq_one_sub_reverse j hpos]
    dsimp [a] at *
    rw [hxj', hxa', hshare]
    have heps_small : qa * eps < cap := by
      have hqa_pos : 0 < qa := lt_trans (by norm_num) hqa_half
      have hqa_le_one : qa ≤ 1 := hqa_lt_one.le
      have hmul_le : qa * eps ≤ eps := by nlinarith
      exact lt_of_le_of_lt hmul_le heps_lt_cap
    dsimp [cap] at heps_small
    nlinarith
  · by_cases hla : l = a
    · subst l
      have hxj' : x' j = 0 := by
        dsimp [x']
        exact theorem4Problem11RightHalfShiftX_donor_eq_zero hne hrj
      have hxa' : x' a = x a + (x j - eps) := by
        dsimp [x']
        exact theorem4Problem11RightHalfShiftX_receiver_eq hne hra
      have hrev_a : reverseItem a = j := by
        dsimp [a]
        rw [reverseItem_reverseItem]
      rw [hxa', hrev_a, hxj']
      have heps_small : qa * eps < cap := by
        have hqa_pos : 0 < qa := lt_trans (by norm_num) hqa_half
        have hqa_le_one : qa ≤ 1 := hqa_lt_one.le
        have hmul_le : qa * eps ≤ eps := by nlinarith
        exact lt_of_le_of_lt hmul_le heps_lt_cap
      dsimp [qa, cap] at *
      nlinarith
    · have hlrev_ne_j : reverseItem l ≠ j := by
        intro h
        apply hla
        calc
          l = reverseItem j := by
            rw [← h, reverseItem_reverseItem]
          _ = a := rfl
      have hlrev_ne_a : reverseItem l ≠ a := by
        intro h
        apply hlj
        calc
          l = reverseItem a := by
            rw [← h, reverseItem_reverseItem]
          _ = j := by
            dsimp [a]
            rw [reverseItem_reverseItem]
      have hxl' : x' l = x l + eps * r l := by
        dsimp [x']
        exact theorem4Problem11RightHalfShiftX_other_eq hlj hla
      have hxrev' :
          x' (reverseItem l) =
            x (reverseItem l) + eps * r (reverseItem l) := by
        dsimp [x']
        exact theorem4Problem11RightHalfShiftX_other_eq hlrev_ne_j hlrev_ne_a
      rw [hxl', hxrev']
      have hrl_pos : 0 < r l := hr_pos hlj hla
      have hrrev_pos : 0 < r (reverseItem l) :=
        hr_pos hlrev_ne_j hlrev_ne_a
      have hleft_pos :
          0 < pairShare (1 / 2) v l * (eps * r l) :=
        mul_pos hq_pos (mul_pos heps_pos hrl_pos)
      have hright_pos :
          0 < (1 - pairShare (1 / 2) v l) *
            (eps * r (reverseItem l)) :=
        mul_pos (sub_pos.mpr hq_lt_one) (mul_pos heps_pos hrrev_pos)
      nlinarith

theorem theorem4Problem11_typeZero_zero_after_mirror_of_noStrictPointwiseImprovement
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsym : Theorem4MirrorSymmetricPolicy ρ)
    (hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ) :
    ∀ j : Item n, (reverseItem j).val < j.val → ρ 0 j = 0 := by
  intro j hj_right
  by_contra hρj_ne
  let x : Item n → ℝ := fun l => (ρ 0 l).toReal
  let z : Item n → ℝ := fun l => (ρ 2 l).toReal
  have hx_nonneg : ∀ l : Item n, 0 ≤ x l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hsumx : (∑ l : Item n, x l) = 1 := by
    dsimp [x]
    exact DecisionCore.pmfToRealSum (ρ 0)
  have hxj_pos : 0 < x j := by
    have htoReal_ne : (ρ 0 j).toReal ≠ 0 := by
      intro hzero
      rcases (ENNReal.toReal_eq_zero_iff (ρ 0 j)).mp hzero with hzero_enn | htop
      · exact hρj_ne hzero_enn
      · exact (ρ 0).apply_ne_top j htop
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm htoReal_ne)
  obtain ⟨x', hx'_nonneg, hx'_sum, hstrict⟩ :=
    theorem4Problem11_rightHalfShift_exists_strictlyImproves
      hn hbeta_pos hpos hdec hj_right hx_nonneg hsumx hxj_pos
      (z := z)
  let y' : Item n → ℝ := fun l => x' (reverseItem l)
  have hy'_nonneg : ∀ l : Item n, 0 ≤ y' l := by
    intro l
    exact hx'_nonneg (reverseItem l)
  have hy'_sum : (∑ l : Item n, y' l) = 1 := by
    dsimp [y']
    rw [sum_reverseItem x', hx'_sum]
  let ρ' : TypePolicy 3 n := fun k =>
    if k = 0 then
      pmfOfRealVector x' hx'_nonneg hx'_sum
    else if k = 1 then
      pmfOfRealVector y' hy'_nonneg hy'_sum
    else
      ρ 2
  have hsym' : Theorem4MirrorSymmetricPolicy ρ' := by
    constructor
    · intro l
      apply (ENNReal.toReal_eq_toReal_iff'
        ((ρ' 1).apply_ne_top (reverseItem l))
        ((ρ' 0).apply_ne_top l)).mp
      simp [ρ', y', reverseItem_reverseItem]
    · intro l
      have h := hsym.2 l
      simpa [ρ'] using h
  apply hno
  refine ⟨ρ', hsym', ?_⟩
  intro l
  unfold theorem4Problem11PolicyItemValue
  simpa [theorem4Problem11ItemValue, x, z, ρ'] using hstrict l

/-- Problem 11 no-gap condition for the known-type row `x`. -/
def Theorem4Problem11TypeZeroZeroClosed {n : ℕ}
    (ρ : TypePolicy 3 n) : Prop :=
  ∀ {j i : Item n}, j.val < i.val → ρ 0 j = 0 → ρ 0 i = 0

/--
Problem 11 no-gap condition for the cold-start row on the half-problem:
once `z_i` is positive, all later half-side `z_j` are positive.
-/
def Theorem4Problem11ColdStartPositiveClosed {n : ℕ}
    (ρ : TypePolicy 3 n) : Prop :=
  ∀ {i j : Item n}, i.val < j.val → ρ 2 i ≠ 0 → ρ 2 j ≠ 0

/--
Exact Appendix E Lemma 13 perturbation certificate for an `x` support gap:
an earlier zero and a later positive known-type coordinate yield a
mirror-symmetric policy that strictly improves every Problem 11 item value.
-/
def Theorem4Problem11TypeZeroGapStrictImprovement {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) : Prop :=
  ∀ {i j : Item n}, i.val < j.val → ρ 0 i = 0 → ρ 0 j ≠ 0 →
    ∃ ρ' : TypePolicy 3 n,
      Theorem4MirrorSymmetricPolicy ρ' ∧
        ∀ l : Item n,
          theorem4Problem11PolicyItemValue beta v ρ l <
            theorem4Problem11PolicyItemValue beta v ρ' l

/--
Exact Appendix E Lemma 13 perturbation certificate for a `z` support gap:
an earlier positive and a later zero cold-start coordinate yield a
mirror-symmetric policy that strictly improves every Problem 11 item value.
-/
def Theorem4Problem11ColdStartGapStrictImprovement {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) : Prop :=
  ∀ {i j : Item n}, i.val < j.val → ρ 2 i ≠ 0 → ρ 2 j = 0 →
    ∃ ρ' : TypePolicy 3 n,
      Theorem4MirrorSymmetricPolicy ρ' ∧
        ∀ l : Item n,
          theorem4Problem11PolicyItemValue beta v ρ l <
            theorem4Problem11PolicyItemValue beta v ρ' l

theorem theorem4Problem11_typeZeroZeroClosed_of_gapStrictImprovement
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n}
    (hgap : Theorem4Problem11TypeZeroGapStrictImprovement beta v ρ)
    (hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ) :
    Theorem4Problem11TypeZeroZeroClosed ρ := by
  intro i j hij hi_zero
  by_contra hj_ne
  exact hno (hgap hij hi_zero hj_ne)

theorem theorem4Problem11_coldStartPositiveClosed_of_gapStrictImprovement
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n}
    (hgap : Theorem4Problem11ColdStartGapStrictImprovement beta v ρ)
    (hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ) :
    Theorem4Problem11ColdStartPositiveClosed ρ := by
  intro i j hij hi_pos hj_zero
  exact hno (hgap hij hi_pos hj_zero)

/-- Items used with positive probability by Problem 11's known-type row. -/
noncomputable def theorem4Problem11TypeZeroActiveItems {n : ℕ}
    (ρ : TypePolicy 3 n) : Finset (Item n) :=
  Finset.univ.filter fun j => ρ 0 j ≠ 0

theorem theorem4Problem11TypeZeroActiveItems_nonempty {n : ℕ} [NeZero n]
    (ρ : TypePolicy 3 n) :
    (theorem4Problem11TypeZeroActiveItems ρ).Nonempty := by
  rcases TypePolicy.exists_active_item_for_type ρ 0 with ⟨j, hj⟩
  exact ⟨j, by simp [theorem4Problem11TypeZeroActiveItems, hj]⟩

/-- Problem 11 pivot candidate: the last item with positive known-type mass. -/
noncomputable def theorem4Problem11LastActiveTypeZero {n : ℕ} [NeZero n]
    (ρ : TypePolicy 3 n) : Item n :=
  (theorem4Problem11TypeZeroActiveItems ρ).max'
    (theorem4Problem11TypeZeroActiveItems_nonempty ρ)

theorem theorem4Problem11LastActiveTypeZero_active {n : ℕ} [NeZero n]
    (ρ : TypePolicy 3 n) :
    ρ 0 (theorem4Problem11LastActiveTypeZero ρ) ≠ 0 := by
  have hmem :=
    Finset.max'_mem (theorem4Problem11TypeZeroActiveItems ρ)
      (theorem4Problem11TypeZeroActiveItems_nonempty ρ)
  simpa [theorem4Problem11LastActiveTypeZero,
    theorem4Problem11TypeZeroActiveItems] using hmem

theorem theorem4Problem11_typeZero_zero_after_lastActive {n : ℕ}
    [NeZero n] (ρ : TypePolicy 3 n) {j : Item n}
    (hj : (theorem4Problem11LastActiveTypeZero ρ).val < j.val) :
    ρ 0 j = 0 := by
  by_contra hne
  have hmem : j ∈ theorem4Problem11TypeZeroActiveItems ρ := by
    simp [theorem4Problem11TypeZeroActiveItems, hne]
  have hle :
      j ≤ theorem4Problem11LastActiveTypeZero ρ := by
    simpa [theorem4Problem11LastActiveTypeZero] using
      (theorem4Problem11TypeZeroActiveItems ρ).le_max' j hmem
  have hle_val : j.val ≤ (theorem4Problem11LastActiveTypeZero ρ).val := hle
  omega

theorem theorem4Problem11_typeZero_active_before_lastActive_of_zeroClosed
    {n : ℕ} [NeZero n] (ρ : TypePolicy 3 n)
    (hx : Theorem4Problem11TypeZeroZeroClosed ρ) {j : Item n}
    (hj : j.val < (theorem4Problem11LastActiveTypeZero ρ).val) :
    ρ 0 j ≠ 0 := by
  by_contra hz
  exact theorem4Problem11LastActiveTypeZero_active ρ (hx hj hz)

theorem theorem4Problem11_sharedItems_of_active_types
    {n : ℕ} (ρ : TypePolicy 3 n) {j : Item n}
    {k k' : UserType 3}
    (hne : k ≠ k') (hk : ρ k j ≠ 0) (hk' : ρ k' j ≠ 0) :
    j ∈ TypePolicy.sharedItems ρ := by
  simp [TypePolicy.sharedItems]
  exact ⟨k, k', hne, hk, hk'⟩

/-! ### Appendix E, Lemma 15: ruling out pivot `t = 1` -/

/-- Lemma 15's closed-form `λ` when the Problem 11 pivot is item `1`. -/
noncomputable def theorem4Problem11PivotOneLambda {n : ℕ} [NeZero n]
    (beta : ℝ) (v : Item n → ℝ) : ℝ :=
  (2 * beta * pairShare (1 / 2) v theorem4FirstItem +
      (1 / 2) * (1 - 2 * beta)) /
    (1 + (1 / 2) * ((n : ℝ) - 2))

/-- Lemma 15's closed-form pivot coordinate `z₁` when the pivot is item `1`. -/
noncomputable def theorem4Problem11PivotOneZ {n : ℕ} [NeZero n]
    (beta : ℝ) (v : Item n → ℝ) : ℝ :=
  (1 / 2) *
    (1 - ((n : ℝ) - 2) *
      theorem4Problem11PivotOneLambda beta v / (1 - 2 * beta))

theorem theorem4Problem11PivotOneLambda_gt_inv_card
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    (n : ℝ)⁻¹ < theorem4Problem11PivotOneLambda beta v := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hinv_pos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
  have hbeta_pos : 0 < beta := lt_trans hinv_pos hbeta
  have hfirst_before :
      (theorem4FirstItem : Item n).val <
        (reverseItem (theorem4FirstItem : Item n)).val := by
    simp [theorem4FirstItem, reverseItem]
    omega
  have hq :
      (1 / 2 : ℝ) <
        pairShare (1 / 2) v (theorem4FirstItem : Item n) :=
    half_lt_pairShare_half_of_val_lt_reverse
      (theorem4FirstItem : Item n) hpos hdec hfirst_before
  have hnum :
      (1 / 2 : ℝ) <
        2 * beta * pairShare (1 / 2) v (theorem4FirstItem : Item n) +
          (1 / 2) * (1 - 2 * beta) := by
    nlinarith
  have hden_eq :
      1 + (1 / 2 : ℝ) * ((n : ℝ) - 2) = (n : ℝ) / 2 := by
    ring
  have hden_pos : 0 < (n : ℝ) / 2 := by positivity
  have hscale :
      (n : ℝ)⁻¹ * ((n : ℝ) / 2) = (1 / 2 : ℝ) := by
    field_simp [ne_of_gt hnpos]
  unfold theorem4Problem11PivotOneLambda
  rw [hden_eq]
  rw [lt_div_iff₀ hden_pos]
  rw [hscale]
  exact hnum

theorem theorem4Problem11PivotOneZ_neg
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    theorem4Problem11PivotOneZ beta v < 0 := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn_one : 1 < n := by omega
  have hlambda :
      (n : ℝ)⁻¹ < theorem4Problem11PivotOneLambda beta v :=
    theorem4Problem11PivotOneLambda_gt_inv_card
      hn_one hbeta hpos hdec
  have hnminus_pos : 0 < (n : ℝ) - 2 := by
    have hn_real : (2 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hthreshold :
      1 - 2 * beta < ((n : ℝ) - 2) * (n : ℝ)⁻¹ := by
    have hcalc :
        ((n : ℝ) - 2) * (n : ℝ)⁻¹ =
          1 - 2 * (n : ℝ)⁻¹ := by
      field_simp [ne_of_gt hnpos]
    rw [hcalc]
    nlinarith
  have hprod :
      1 - 2 * beta <
        ((n : ℝ) - 2) * theorem4Problem11PivotOneLambda beta v := by
    exact lt_trans hthreshold
      (mul_lt_mul_of_pos_left hlambda hnminus_pos)
  have hcold_pos : 0 < 1 - 2 * beta := by
    nlinarith
  have hdiv :
      1 <
        ((n : ℝ) - 2) * theorem4Problem11PivotOneLambda beta v /
          (1 - 2 * beta) := by
    rw [lt_div_iff₀ hcold_pos]
    simpa using hprod
  unfold theorem4Problem11PivotOneZ
  nlinarith

/--
If Lemma 15's pivot-one closed form is imposed on an actual PMF coordinate,
the pivot-one case is impossible under the Theorem 4 `β > 1/n` assumptions.
-/
theorem theorem4Problem11PivotOne_closedZ_impossible
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (ρ : TypePolicy 3 n)
    (hz :
      (ρ 2 theorem4FirstItem).toReal =
        theorem4Problem11PivotOneZ beta v) :
    False := by
  have hneg :
      theorem4Problem11PivotOneZ beta v < 0 :=
    theorem4Problem11PivotOneZ_neg hn hbeta hbeta_half hpos hdec
  have hnonneg : 0 ≤ (ρ 2 theorem4FirstItem).toReal :=
    ENNReal.toReal_nonneg
  rw [hz] at hnonneg
  linarith

/-! ### Appendix E, Lemma 13 pivot-support interface -/

/--
Appendix E, Lemma 13 pivot-support shape for Problem 11: the known-type row
has no mass strictly after the pivot, while the cold-start row has no mass
strictly before the pivot or its mirror.
-/
def Theorem4Problem11PivotSupport {n : ℕ}
    (ρ : TypePolicy 3 n) (t : Item n) : Prop :=
  (∀ j : Item n, t.val < j.val → ρ 0 j = 0) ∧
    (∀ j : Item n, j.val < t.val →
      ρ 2 j = 0 ∧ ρ 2 (reverseItem j) = 0)

theorem theorem4Problem11PivotSupport_of_lastActive_noGap_of_sharedBound
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n}
    (hmirror : Theorem4MirrorSymmetricPolicy ρ)
    (hx : Theorem4Problem11TypeZeroZeroClosed ρ)
    (hz : Theorem4Problem11ColdStartPositiveClosed ρ)
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hleft :
      (theorem4Problem11LastActiveTypeZero ρ).val ≤
        (reverseItem (theorem4Problem11LastActiveTypeZero ρ)).val) :
    Theorem4Problem11PivotSupport ρ
      (theorem4Problem11LastActiveTypeZero ρ) := by
  classical
  let t : Item n := theorem4Problem11LastActiveTypeZero ρ
  constructor
  · intro j hj
    exact theorem4Problem11_typeZero_zero_after_lastActive ρ hj
  · intro j hjt
    have hxt : ρ 0 t ≠ 0 := by
      dsimp [t]
      exact theorem4Problem11LastActiveTypeZero_active ρ
    have hxj : ρ 0 j ≠ 0 := by
      exact theorem4Problem11_typeZero_active_before_lastActive_of_zeroClosed
        ρ hx (by simpa [t] using hjt)
    have hrev_t_lt_rev_j :
        (reverseItem t).val < (reverseItem j).val :=
      reverseItem_val_lt_of_val_lt hjt
    have ht_lt_rev_j : t.val < (reverseItem j).val :=
      lt_of_le_of_lt (by simpa [t] using hleft) hrev_t_lt_rev_j
    have hj_lt_rev_j : j.val < (reverseItem j).val := by
      exact lt_trans hjt ht_lt_rev_j
    have hj_ne_rev : j ≠ reverseItem j := by
      intro h
      have hval := congrArg Fin.val h
      omega
    have hj_ne_t : j ≠ t := by
      intro h
      subst h
      omega
    have hrevj_ne_t : reverseItem j ≠ t := by
      intro h
      have hval := congrArg Fin.val h
      omega
    have hcontradict_shared (hzj_ne : ρ 2 j ≠ 0) : False := by
      have hzt : ρ 2 t ≠ 0 := hz hjt hzj_ne
      have hzrevj : ρ 2 (reverseItem j) ≠ 0 := by
        rw [hmirror.2 j]
        exact hzj_ne
      have hyrevj : ρ 1 (reverseItem j) ≠ 0 := by
        rw [hmirror.1 j]
        exact hxj
      have hj_shared : j ∈ TypePolicy.sharedItems ρ :=
        theorem4Problem11_sharedItems_of_active_types ρ
          (by decide : (0 : UserType 3) ≠ 2) hxj hzj_ne
      have hrevj_shared : reverseItem j ∈ TypePolicy.sharedItems ρ :=
        theorem4Problem11_sharedItems_of_active_types ρ
          (by decide : (1 : UserType 3) ≠ 2) hyrevj hzrevj
      have ht_shared : t ∈ TypePolicy.sharedItems ρ :=
        theorem4Problem11_sharedItems_of_active_types ρ
          (by decide : (0 : UserType 3) ≠ 2) hxt hzt
      have hsubset :
          ({j, reverseItem j, t} : Finset (Item n)) ⊆
            TypePolicy.sharedItems ρ := by
        intro u hu
        simp at hu
        rcases hu with rfl | rfl | rfl
        · exact hj_shared
        · exact hrevj_shared
        · exact ht_shared
      have hcard_three :
          ({j, reverseItem j, t} : Finset (Item n)).card = 3 := by
        simp [hj_ne_rev, hj_ne_t, hrevj_ne_t]
      have hthree : 3 ≤ (TypePolicy.sharedItems ρ).card := by
        calc
          3 = ({j, reverseItem j, t} : Finset (Item n)).card :=
            hcard_three.symm
          _ ≤ (TypePolicy.sharedItems ρ).card :=
            Finset.card_le_card hsubset
      have htwo : (TypePolicy.sharedItems ρ).card ≤ 2 := by
        simpa [TypePolicy.SharedItemsBound] using hshared
      omega
    have hzj_zero : ρ 2 j = 0 := by
      by_contra hzj_ne
      exact hcontradict_shared hzj_ne
    constructor
    · exact hzj_zero
    · rw [hmirror.2 j]
      exact hzj_zero

theorem theorem4Problem11PivotSupport_of_equalizedBasicOptimal_noGap
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hx : Theorem4Problem11TypeZeroZeroClosed ρ)
    (hz : Theorem4Problem11ColdStartPositiveClosed ρ) :
    Theorem4Problem11PivotSupport ρ
      (theorem4Problem11LastActiveTypeZero ρ) := by
  have hshared : TypePolicy.SharedItemsBound ρ :=
    theorem4Problem11_sharedItemsBound_of_equalizedBasicOptimal h
  have hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ :=
    theorem4Problem11_noStrictPointwiseImprovement_of_equalizedBasicOptimal h
  have hright_zero :
      ∀ j : Item n, (reverseItem j).val < j.val → ρ 0 j = 0 :=
    theorem4Problem11_typeZero_zero_after_mirror_of_noStrictPointwiseImprovement
      hn hbeta_pos hpos hdec h.mirror hno
  have hleft :
      (theorem4Problem11LastActiveTypeZero ρ).val ≤
        (reverseItem (theorem4Problem11LastActiveTypeZero ρ)).val := by
    by_contra hnot
    have hrev_lt :
        (reverseItem (theorem4Problem11LastActiveTypeZero ρ)).val <
          (theorem4Problem11LastActiveTypeZero ρ).val := by
      omega
    have hz0 :=
      hright_zero (theorem4Problem11LastActiveTypeZero ρ) hrev_lt
    exact theorem4Problem11LastActiveTypeZero_active ρ hz0
  exact theorem4Problem11PivotSupport_of_lastActive_noGap_of_sharedBound
    h.mirror hx hz hshared hleft

theorem theorem4Problem11PivotSupport_of_equalizedBasicOptimal_gapStrictImprovements
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hxgap : Theorem4Problem11TypeZeroGapStrictImprovement beta v ρ)
    (hzgap : Theorem4Problem11ColdStartGapStrictImprovement beta v ρ) :
    Theorem4Problem11PivotSupport ρ
      (theorem4Problem11LastActiveTypeZero ρ) := by
  have hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ :=
    theorem4Problem11_noStrictPointwiseImprovement_of_equalizedBasicOptimal h
  have hx : Theorem4Problem11TypeZeroZeroClosed ρ :=
    theorem4Problem11_typeZeroZeroClosed_of_gapStrictImprovement hxgap hno
  have hz : Theorem4Problem11ColdStartPositiveClosed ρ :=
    theorem4Problem11_coldStartPositiveClosed_of_gapStrictImprovement hzgap hno
  exact theorem4Problem11PivotSupport_of_equalizedBasicOptimal_noGap
    hn hbeta_pos hpos hdec h hx hz

theorem theorem4Problem11PivotSupport_typeZero_zero_of_pivot_first
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem)
    (hj : j ≠ theorem4FirstItem) :
    ρ 0 j = 0 := by
  have hlt : t.val < j.val := by
    simpa [ht] using theorem4FirstItem_val_lt_of_ne hj
  exact hpivot.1 j hlt

theorem theorem4Problem11PivotSupport_typeZero_first_toReal_eq_one
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    (ρ 0 theorem4FirstItem).toReal = 1 := by
  have hsum_single :
      (∑ j : Item n, (ρ 0 j).toReal) =
        (ρ 0 theorem4FirstItem).toReal := by
    apply Finset.sum_eq_single theorem4FirstItem
    · intro j _hj hj_ne
      have hz :
          ρ 0 j = 0 :=
        theorem4Problem11PivotSupport_typeZero_zero_of_pivot_first
          hpivot ht hj_ne
      simp [hz]
    · intro hnot
      simp at hnot
  have hsum : (∑ j : Item n, (ρ 0 j).toReal) = 1 :=
    DecisionCore.pmfToRealSum (ρ 0)
  rw [hsum] at hsum_single
  exact hsum_single.symm

theorem theorem4Problem11PivotSupport_typeZero_reverse_first_toReal_eq_zero
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t : Item n}
    (hn : 1 < n)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    (ρ 0 (reverseItem theorem4FirstItem)).toReal = 0 := by
  have hne :
      reverseItem (theorem4FirstItem : Item n) ≠ theorem4FirstItem := by
    intro h
    have hval := congrArg Fin.val h
    simp [theorem4FirstItem, reverseItem] at hval
    omega
  have hz :
      ρ 0 (reverseItem theorem4FirstItem) = 0 :=
    theorem4Problem11PivotSupport_typeZero_zero_of_pivot_first
      hpivot ht hne
  simp [hz]

theorem theorem4Problem11PivotSupport_sum_typeZero_q_of_pivot_first
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    (∑ j : Item n,
        pairShare (1 / 2) v j * (ρ 0 j).toReal) =
      pairShare (1 / 2) v theorem4FirstItem := by
  have hxfirst :=
    theorem4Problem11PivotSupport_typeZero_first_toReal_eq_one
      hpivot ht
  have hsum_single :
      (∑ j : Item n,
          pairShare (1 / 2) v j * (ρ 0 j).toReal) =
        pairShare (1 / 2) v theorem4FirstItem *
          (ρ 0 theorem4FirstItem).toReal := by
    apply Finset.sum_eq_single theorem4FirstItem
    · intro j _hj hj_ne
      have hz :
          ρ 0 j = 0 :=
        theorem4Problem11PivotSupport_typeZero_zero_of_pivot_first
          hpivot ht hj_ne
      simp [hz]
    · intro hnot
      simp at hnot
  rw [hsum_single, hxfirst]
  ring

theorem theorem4Problem11PivotSupport_sum_typeZero_reverse_q_of_pivot_first
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    (∑ j : Item n,
        (1 - pairShare (1 / 2) v j) *
          (ρ 0 (reverseItem j)).toReal) =
      pairShare (1 / 2) v theorem4FirstItem := by
  have hreindex :
      (∑ j : Item n,
          (1 - pairShare (1 / 2) v j) *
            (ρ 0 (reverseItem j)).toReal) =
        ∑ j : Item n,
          (1 - pairShare (1 / 2) v (reverseItem j)) *
            (ρ 0 j).toReal := by
    simpa [reverseItem_reverseItem] using
      (sum_reverseItem
        (fun j : Item n =>
          (1 - pairShare (1 / 2) v (reverseItem j)) *
            (ρ 0 j).toReal))
  have hxfirst :=
    theorem4Problem11PivotSupport_typeZero_first_toReal_eq_one
      hpivot ht
  have hsum_single :
      (∑ j : Item n,
          (1 - pairShare (1 / 2) v (reverseItem j)) *
            (ρ 0 j).toReal) =
        (1 - pairShare (1 / 2) v (reverseItem theorem4FirstItem)) *
          (ρ 0 theorem4FirstItem).toReal := by
    apply Finset.sum_eq_single theorem4FirstItem
    · intro j _hj hj_ne
      have hz :
          ρ 0 j = 0 :=
        theorem4Problem11PivotSupport_typeZero_zero_of_pivot_first
          hpivot ht hj_ne
      simp [hz]
    · intro hnot
      simp at hnot
  have hq :
      1 - pairShare (1 / 2) v (reverseItem theorem4FirstItem) =
        pairShare (1 / 2) v theorem4FirstItem :=
    (pairShare_half_eq_one_sub_reverse theorem4FirstItem hpos).symm
  rw [hreindex, hsum_single, hxfirst, hq]
  ring

theorem theorem4Problem11PivotSupport_sum_itemValue_of_pivot_first
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    (∑ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j) =
      4 * beta * pairShare (1 / 2) v theorem4FirstItem +
        (1 - 2 * beta) := by
  have hsum_q :=
    theorem4Problem11PivotSupport_sum_typeZero_q_of_pivot_first
      (v := v) hpivot ht
  have hsum_rev :=
    theorem4Problem11PivotSupport_sum_typeZero_reverse_q_of_pivot_first
      hpos hpivot ht
  have hsum_z : (∑ j : Item n, (ρ 2 j).toReal) = 1 :=
    DecisionCore.pmfToRealSum (ρ 2)
  unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue
  have hleft :
      (∑ j : Item n,
        2 * beta *
            (pairShare (1 / 2) v j * (ρ 0 j).toReal +
              (1 - pairShare (1 / 2) v j) *
                (ρ 0 (reverseItem j)).toReal)) =
        2 * beta *
          ((∑ j : Item n,
              pairShare (1 / 2) v j * (ρ 0 j).toReal) +
            (∑ j : Item n,
              (1 - pairShare (1 / 2) v j) *
                (ρ 0 (reverseItem j)).toReal)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hright :
      (∑ j : Item n, (1 - 2 * beta) * (ρ 2 j).toReal) =
        (1 - 2 * beta) * (∑ j : Item n, (ρ 2 j).toReal) := by
    rw [← Finset.mul_sum]
  rw [Finset.sum_add_distrib, hleft, hright, hsum_q, hsum_rev, hsum_z]
  ring

theorem theorem4Problem11PivotOneLambda_eq_of_equalized_pivotSupport
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    ell = theorem4Problem11PivotOneLambda beta v := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos_nat)
  have hsum_values :=
    theorem4Problem11PivotSupport_sum_itemValue_of_pivot_first
      (beta := beta) hpos hpivot ht
  have hsum_eq :
      (∑ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j) =
        (n : ℝ) * ell := by
    calc
      (∑ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j)
          = ∑ _j : Item n, ell := by
            apply Finset.sum_congr rfl
            intro j _hj
            exact h.item_eq j
      _ = (n : ℝ) * ell := by
            simp [Item]
  have hell_mul :
      (n : ℝ) * ell =
        4 * beta * pairShare (1 / 2) v theorem4FirstItem +
          (1 - 2 * beta) := by
    rw [← hsum_eq]
    exact hsum_values
  have hden_eq :
      1 + (1 / 2 : ℝ) * ((n : ℝ) - 2) = (n : ℝ) / 2 := by
    ring
  unfold theorem4Problem11PivotOneLambda
  rw [hden_eq]
  rw [eq_div_iff (by positivity : (n : ℝ) / 2 ≠ 0)]
  nlinarith

theorem theorem4Problem11PivotOne_closedZ_of_equalized_pivotSupport
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    (ρ 2 theorem4FirstItem).toReal =
      theorem4Problem11PivotOneZ beta v := by
  let q := pairShare (1 / 2) v theorem4FirstItem
  have hxfirst :
      (ρ 0 theorem4FirstItem).toReal = 1 :=
    theorem4Problem11PivotSupport_typeZero_first_toReal_eq_one
      hpivot ht
  have hxrev :
      (ρ 0 (reverseItem theorem4FirstItem)).toReal = 0 :=
    theorem4Problem11PivotSupport_typeZero_reverse_first_toReal_eq_zero
      hn hpivot ht
  have hellambda :
      ell = theorem4Problem11PivotOneLambda beta v :=
    theorem4Problem11PivotOneLambda_eq_of_equalized_pivotSupport
      hpos h hpivot ht
  have hfirst_value :
      2 * beta * q + (1 - 2 * beta) *
          (ρ 2 theorem4FirstItem).toReal = ell := by
    have hitem := h.item_eq theorem4FirstItem
    unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue at hitem
    change
      2 * beta *
          (q * (ρ 0 theorem4FirstItem).toReal +
            (1 - q) * (ρ 0 (reverseItem theorem4FirstItem)).toReal) +
        (1 - 2 * beta) * (ρ 2 theorem4FirstItem).toReal = ell at hitem
    rw [hxfirst, hxrev] at hitem
    nlinarith
  have hdelta_ne : 1 - 2 * beta ≠ 0 := by
    nlinarith
  have hz :
      (ρ 2 theorem4FirstItem).toReal =
        (ell - 2 * beta * q) / (1 - 2 * beta) := by
    rw [eq_div_iff hdelta_ne]
    nlinarith
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos_nat)
  have hden_eq :
      1 + (1 / 2 : ℝ) * ((n : ℝ) - 2) = (n : ℝ) / 2 := by
    ring
  have hlambda_mul :
      (n : ℝ) * theorem4Problem11PivotOneLambda beta v =
        4 * beta * q + (1 - 2 * beta) := by
    unfold theorem4Problem11PivotOneLambda
    change
      (n : ℝ) *
          ((2 * beta * q + (1 / 2) * (1 - 2 * beta)) /
            (1 + (1 / 2) * ((n : ℝ) - 2))) =
        4 * beta * q + (1 - 2 * beta)
    rw [hden_eq]
    field_simp [hn_ne]
    ring
  rw [hz, hellambda]
  unfold theorem4Problem11PivotOneZ
  field_simp [hdelta_ne]
  nlinarith

/--
Once Lemma 13's pivot is strictly after item `1`, the cold-start row gives zero
probability to both extreme items.
-/
theorem theorem4Problem11PivotSupport_no_extremes_of_first_lt
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hfirst_lt : (theorem4FirstItem : Item n).val < t.val) :
    ρ 2 theorem4FirstItem = 0 ∧ ρ 2 theorem4LastItem = 0 := by
  have hzero := hpivot.2 theorem4FirstItem hfirst_lt
  constructor
  · exact hzero.1
  · simpa [theorem4LastItem] using hzero.2

/--
Appendix E Lemmas 13 and 15 combine to give the no-extreme cold-start
certificate: Lemma 13 supplies the pivot-support shape, and Lemma 15's
closed-form pivot-one coordinate rules out `t = 1`.
-/
theorem theorem4Problem11_no_extremes_of_pivotSupport_of_closedZ
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hclosed_first :
      t = theorem4FirstItem →
        (ρ 2 theorem4FirstItem).toReal =
          theorem4Problem11PivotOneZ beta v) :
    ρ 2 theorem4FirstItem = 0 ∧ ρ 2 theorem4LastItem = 0 := by
  by_cases ht : t = theorem4FirstItem
  · exact False.elim
      (theorem4Problem11PivotOne_closedZ_impossible
        hn hbeta hbeta_half hpos hdec ρ (hclosed_first ht))
  · have hfirst_lt : (theorem4FirstItem : Item n).val < t.val :=
      theorem4FirstItem_val_lt_of_ne ht
    exact theorem4Problem11PivotSupport_no_extremes_of_first_lt
      hpivot hfirst_lt

theorem theorem4Problem11_no_extremes_of_equalized_pivotSupport
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t) :
    ρ 2 theorem4FirstItem = 0 ∧ ρ 2 theorem4LastItem = 0 := by
  exact theorem4Problem11_no_extremes_of_pivotSupport_of_closedZ
    hn hbeta hbeta_half hpos hdec hpivot
    (fun ht =>
      theorem4Problem11PivotOne_closedZ_of_equalized_pivotSupport
        (by omega : 1 < n) hbeta_half hpos h hpivot ht)

theorem theorem4Problem11_no_extremes_of_equalized_noGap
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hx : Theorem4Problem11TypeZeroZeroClosed ρ)
    (hz : Theorem4Problem11ColdStartPositiveClosed ρ) :
    ρ 2 theorem4FirstItem = 0 ∧ ρ 2 theorem4LastItem = 0 := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hbeta_pos : 0 < beta := lt_trans (inv_pos.mpr hnpos) hbeta
  have hpivot :
      Theorem4Problem11PivotSupport ρ
        (theorem4Problem11LastActiveTypeZero ρ) :=
    theorem4Problem11PivotSupport_of_equalizedBasicOptimal_noGap
      hn hbeta_pos hpos hdec h hx hz
  exact theorem4Problem11_no_extremes_of_equalized_pivotSupport
    hn hbeta hbeta_half hpos hdec h hpivot

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

/--
Theorem 4 fairness-constrained misestimation bridge, first true cold-start
type, using the Problem 11 pivot-support/closed-form certificate rather than a
bare no-first-item assumption.
-/
theorem theorem4_misestimation_with_fairness_large_typeZero_from_problem11_certificate
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (t : Item n)
    (hpivot : OpposingTypes.Theorem4Problem11PivotSupport ρ t)
    (hclosed_first :
      t = OpposingTypes.theorem4FirstItem →
        (ρ 2 OpposingTypes.theorem4FirstItem).toReal =
          OpposingTypes.theorem4Problem11PivotOneZ beta v) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_pivotSupport_of_closedZ
      hn hbeta hbeta_half hpos hdec hpivot hclosed_first
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.1

/--
Theorem 4 fairness-constrained misestimation bridge, second true cold-start
type, using the Problem 11 pivot-support/closed-form certificate.
-/
theorem theorem4_misestimation_with_fairness_large_typeOne_from_problem11_certificate
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (t : Item n)
    (hpivot : OpposingTypes.Theorem4Problem11PivotSupport ρ t)
    (hclosed_first :
      t = OpposingTypes.theorem4FirstItem →
        (ρ 2 OpposingTypes.theorem4FirstItem).toReal =
          OpposingTypes.theorem4Problem11PivotOneZ beta v) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_pivotSupport_of_closedZ
      hn hbeta hbeta_half hpos hdec hpivot hclosed_first
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.2

/--
Theorem 4 fairness-constrained misestimation bridge, first true cold-start
type, from the equality-form Problem 11 optimum plus Lemma 13 pivot support.

The Lemma 15 pivot-one closed-coordinate calculation is discharged internally.
-/
theorem theorem4_misestimation_with_fairness_large_typeZero_from_equalized_problem11
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (ell : ℝ) (t : Item n)
    (heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : OpposingTypes.Theorem4Problem11PivotSupport ρ t) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_equalized_pivotSupport
      hn hbeta hbeta_half hpos hdec heq hpivot
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.1

/--
Theorem 4 fairness-constrained misestimation bridge, second true cold-start
type, from the equality-form Problem 11 optimum plus Lemma 13 pivot support.

The Lemma 15 pivot-one closed-coordinate calculation is discharged internally.
-/
theorem theorem4_misestimation_with_fairness_large_typeOne_from_equalized_problem11
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (ell : ℝ) (t : Item n)
    (heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : OpposingTypes.Theorem4Problem11PivotSupport ρ t) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_equalized_pivotSupport
      hn hbeta hbeta_half hpos hdec heq hpivot
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.2

/--
Theorem 4 fairness-constrained misestimation bridge, first true cold-start
type, from the equality-form Problem 11 optimum plus the two no-gap
conclusions that complete Appendix E Lemma 13.
-/
theorem theorem4_misestimation_with_fairness_large_typeZero_from_equalized_problem11_noGap
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (ell : ℝ)
    (heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hx : OpposingTypes.Theorem4Problem11TypeZeroZeroClosed ρ)
    (hz : OpposingTypes.Theorem4Problem11ColdStartPositiveClosed ρ) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_equalized_noGap
      hn hbeta hbeta_half hpos hdec heq hx hz
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.1

/--
Theorem 4 fairness-constrained misestimation bridge, second true cold-start
type, from the equality-form Problem 11 optimum plus the two no-gap
conclusions that complete Appendix E Lemma 13.
-/
theorem theorem4_misestimation_with_fairness_large_typeOne_from_equalized_problem11_noGap
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (ell : ℝ)
    (heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hx : OpposingTypes.Theorem4Problem11TypeZeroZeroClosed ρ)
    (hz : OpposingTypes.Theorem4Problem11ColdStartPositiveClosed ρ) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_equalized_noGap
      hn hbeta hbeta_half hpos hdec heq hx hz
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.2

end EstimatedRecommendationModel
end UserItemFairness
