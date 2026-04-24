import UserItemFairness.Symmetrization

namespace UserItemFairness

/-!
Scalar algebra for the two-opposing-type models used in Theorems 3 and 4.

The paper writes this quantity as
`q_j(α) = α v_j / (α v_j + (1 - α) v_{n-j+1})`.
-/
namespace OpposingTypes

/-- The normalized contribution share of the first type for one item pair. -/
noncomputable def typeOneShare (alpha left right : ℝ) : ℝ :=
  alpha * left / (alpha * left + (1 - alpha) * right)

/-- The denominator in `q_j(α)` is positive for interior `α` and positive utilities. -/
theorem typeOneShare_denom_pos
    {alpha left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right) :
    0 < alpha * left + (1 - alpha) * right := by
  exact add_pos (mul_pos halpha0 hleft)
    (mul_pos (sub_pos.mpr halpha1) hright)

/-- `q_j(α)` is positive for interior `α` and positive utilities. -/
theorem typeOneShare_pos
    {alpha left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right) :
    0 < typeOneShare alpha left right := by
  unfold typeOneShare
  exact div_pos (mul_pos halpha0 hleft)
    (typeOneShare_denom_pos halpha0 halpha1 hleft hright)

/-- `q_j(α)` is less than one for interior `α` and positive utilities. -/
theorem typeOneShare_lt_one
    {alpha left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right) :
    typeOneShare alpha left right < 1 := by
  unfold typeOneShare
  have hden := typeOneShare_denom_pos halpha0 halpha1 hleft hright
  rw [div_lt_one hden]
  nlinarith [mul_pos (sub_pos.mpr halpha1) hright]

/-- The complementary share `1 - q_j(α)` is positive. -/
theorem one_sub_typeOneShare_pos
    {alpha left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right) :
    0 < 1 - typeOneShare alpha left right := by
  have hlt := typeOneShare_lt_one halpha0 halpha1 hleft hright
  linarith

/--
Appendix D, Lemma 9, scalar alpha-monotonicity component:
`q_j(α)` strictly increases as `α` increases.
-/
theorem typeOneShare_strictMono_alpha
    {alpha alpha' left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (hlt : alpha < alpha')
    (hleft : 0 < left) (hright : 0 < right) :
    typeOneShare alpha left right <
      typeOneShare alpha' left right := by
  unfold typeOneShare
  have hden :=
    typeOneShare_denom_pos halpha0 halpha1 hleft hright
  have hden' :=
    typeOneShare_denom_pos halpha0' halpha1' hleft hright
  rw [div_lt_div_iff₀ hden hden']
  ring_nf
  have hprod : 0 < left * right := mul_pos hleft hright
  nlinarith [hprod, hlt]

/--
For fixed `α`, the share decreases when the opposing-value ratio
`right / left` increases, stated in denominator-cleared form.
-/
theorem typeOneShare_lt_of_cross_mul_lt
    {alpha left right left' right' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right)
    (hleft' : 0 < left') (hright' : 0 < right')
    (hcross : right * left' < right' * left) :
    typeOneShare alpha left' right' <
      typeOneShare alpha left right := by
  unfold typeOneShare
  have hden :=
    typeOneShare_denom_pos halpha0 halpha1 hleft hright
  have hden' :=
    typeOneShare_denom_pos halpha0 halpha1 hleft' hright'
  rw [div_lt_div_iff₀ hden' hden]
  ring_nf
  have hscale : 0 < alpha * (1 - alpha) :=
    mul_pos halpha0 (sub_pos.mpr halpha1)
  nlinarith [hscale, hcross]

/--
Appendix E, Lemma 16, scalar midpoint component: at `α = 1/2`, the share is
above `1/2` when the left utility exceeds the right utility.
-/
theorem half_lt_typeOneShare_half_of_right_lt_left
    {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) (hlt : right < left) :
    (1 / 2 : ℝ) < typeOneShare (1 / 2) left right := by
  unfold typeOneShare
  have hden : 0 < (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * right := by
    norm_num
    nlinarith [hleft, hright]
  rw [lt_div_iff₀ hden]
  nlinarith

/--
Appendix E, Lemma 16, scalar midpoint component: at `α = 1/2`, the share is
below `1/2` when the left utility is below the right utility.
-/
theorem typeOneShare_half_lt_half_of_left_lt_right
    {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) (hlt : left < right) :
    typeOneShare (1 / 2) left right < (1 / 2 : ℝ) := by
  unfold typeOneShare
  have hden : 0 < (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * right := by
    norm_num
    nlinarith [hleft, hright]
  rw [div_lt_iff₀ hden]
  nlinarith

/--
Appendix E, Lemma 16, scalar midpoint component: at `α = 1/2`, equal opposing
utilities give share exactly `1/2`.
-/
theorem typeOneShare_half_eq_half_of_eq
    {left right : ℝ}
    (hleft : 0 < left) (heq : left = right) :
    typeOneShare (1 / 2) left right = (1 / 2 : ℝ) := by
  subst right
  unfold typeOneShare
  have hden : (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * left ≠ 0 := by
    norm_num
    exact ne_of_gt hleft
  field_simp [hden]
  ring

/-- The opposite item index `n - j + 1` in zero-based `Fin n` notation. -/
def reverseItem {n : ℕ} (j : Item n) : Item n :=
  ⟨n - 1 - j.val, by omega⟩

/-- The indexed `q_j(α)` used in the opposing-preference proofs. -/
noncomputable def pairShare {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) : ℝ :=
  typeOneShare alpha (v j) (v (reverseItem j))

/-- Values are strictly decreasing in the item index, matching `v₁ > ... > vₙ`. -/
def StrictlyDecreasingByIndex {n : ℕ} (v : Item n → ℝ) : Prop :=
  ∀ ⦃i j : Item n⦄, i.val < j.val → v j < v i

/--
Appendix D, Lemma 9, indexed alpha-monotonicity component:
for each item `j`, `q_j(α)` strictly increases with `α`.
-/
theorem pairShare_strictMono_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (hlt : alpha < alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j < pairShare alpha' v j := by
  exact typeOneShare_strictMono_alpha
    halpha0 halpha1 halpha0' halpha1' hlt (hpos j) (hpos (reverseItem j))

/-- The indexed share `q_j(α)` is positive. -/
theorem pairShare_pos
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < pairShare alpha v j := by
  exact typeOneShare_pos halpha0 halpha1 (hpos j) (hpos (reverseItem j))

/-- The indexed share `q_j(α)` is less than one. -/
theorem pairShare_lt_one
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j < 1 := by
  exact typeOneShare_lt_one halpha0 halpha1 (hpos j) (hpos (reverseItem j))

/-- The indexed complementary share `1 - q_j(α)` is positive. -/
theorem one_sub_pairShare_pos
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < 1 - pairShare alpha v j := by
  exact one_sub_typeOneShare_pos halpha0 halpha1 (hpos j) (hpos (reverseItem j))

/-- Reversing item indices flips strict order. -/
theorem reverseItem_val_lt_of_val_lt {n : ℕ} {i j : Item n}
    (hij : i.val < j.val) :
    (reverseItem j).val < (reverseItem i).val := by
  simp [reverseItem]
  omega

/--
Appendix D, Lemma 9, indexed item-monotonicity component:
for a strictly decreasing value vector, `q_j(α)` strictly decreases as the item
index `j` increases.
-/
theorem pairShare_strictAnti_index
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hij : i.val < j.val) :
    pairShare alpha v j < pairShare alpha v i := by
  have hleft : 0 < v i := hpos i
  have hright : 0 < v (reverseItem i) := hpos (reverseItem i)
  have hleft' : 0 < v j := hpos j
  have hright' : 0 < v (reverseItem j) := hpos (reverseItem j)
  have hleft_lt : v j < v i := hdec hij
  have hrev_val : (reverseItem j).val < (reverseItem i).val :=
    reverseItem_val_lt_of_val_lt hij
  have hrev_lt : v (reverseItem i) < v (reverseItem j) :=
    hdec hrev_val
  have hcross :
      v (reverseItem i) * v j < v (reverseItem j) * v i := by
    have h1 :
        v (reverseItem i) * v j <
          v (reverseItem j) * v j := by
      exact mul_lt_mul_of_pos_right hrev_lt hleft'
    have h2 :
        v (reverseItem j) * v j <
          v (reverseItem j) * v i := by
      exact mul_lt_mul_of_pos_left hleft_lt hright'
    exact lt_trans h1 h2
  exact typeOneShare_lt_of_cross_mul_lt
    halpha0 halpha1 hleft hright hleft' hright' hcross

/--
Appendix E, Lemma 16, indexed midpoint component: if item `j` has higher value
than its opposite item, then `q_j(1/2) > 1/2`.
-/
theorem half_lt_pairShare_half_of_reverse_lt
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hlt : v (reverseItem j) < v j) :
    (1 / 2 : ℝ) < pairShare (1 / 2) v j := by
  exact half_lt_typeOneShare_half_of_right_lt_left
    (hpos j) (hpos (reverseItem j)) hlt

/--
Appendix E, Lemma 16, indexed midpoint component: if item `j` has lower value
than its opposite item, then `q_j(1/2) < 1/2`.
-/
theorem pairShare_half_lt_half_of_lt_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hlt : v j < v (reverseItem j)) :
    pairShare (1 / 2) v j < (1 / 2 : ℝ) := by
  exact typeOneShare_half_lt_half_of_left_lt_right
    (hpos j) (hpos (reverseItem j)) hlt

/--
Appendix E, Lemma 16, indexed midpoint component: equal opposite item values
give `q_j(1/2) = 1/2`.
-/
theorem pairShare_half_eq_half_of_eq_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (heq : v j = v (reverseItem j)) :
    pairShare (1 / 2) v j = (1 / 2 : ℝ) := by
  exact typeOneShare_half_eq_half_of_eq (hpos j) heq

/-- If `j` is before its reverse partner, strict index-decrease gives `v_rev < v_j`. -/
theorem reverse_value_lt_of_val_lt_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hdec : StrictlyDecreasingByIndex v)
    (hval : j.val < (reverseItem j).val) :
    v (reverseItem j) < v j := by
  exact hdec hval

/-- If `j` is after its reverse partner, strict index-decrease gives `v_j < v_rev`. -/
theorem value_lt_reverse_value_of_reverse_val_lt
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hdec : StrictlyDecreasingByIndex v)
    (hval : (reverseItem j).val < j.val) :
    v j < v (reverseItem j) := by
  exact hdec hval

/--
Appendix E, Lemma 16, indexed order form: an item before its reverse partner
has `q_j(1/2) > 1/2`.
-/
theorem half_lt_pairShare_half_of_val_lt_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hval : j.val < (reverseItem j).val) :
    (1 / 2 : ℝ) < pairShare (1 / 2) v j := by
  exact half_lt_pairShare_half_of_reverse_lt j hpos
    (reverse_value_lt_of_val_lt_reverse j hdec hval)

/--
Appendix E, Lemma 16, indexed order form: an item after its reverse partner
has `q_j(1/2) < 1/2`.
-/
theorem pairShare_half_lt_half_of_reverse_val_lt
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hval : (reverseItem j).val < j.val) :
    pairShare (1 / 2) v j < (1 / 2 : ℝ) := by
  exact pairShare_half_lt_half_of_lt_reverse j hpos
    (value_lt_reverse_value_of_reverse_val_lt j hdec hval)

/--
Appendix E, Lemma 16, indexed order form: an item equal to its reverse partner
has `q_j(1/2) = 1/2`.
-/
theorem pairShare_half_eq_half_of_val_eq_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hval : j.val = (reverseItem j).val) :
    pairShare (1 / 2) v j = (1 / 2 : ℝ) := by
  have heq_item : j = reverseItem j := by
    exact Fin.ext hval
  exact pairShare_half_eq_half_of_eq_reverse j hpos (congrArg v heq_item)

/-- Zero-based arithmetic form of being before the reverse item. -/
theorem val_lt_reverseItem_iff {n : ℕ} (j : Item n) :
    j.val < (reverseItem j).val ↔ 2 * j.val + 1 < n := by
  simp [reverseItem]
  omega

/-- Zero-based arithmetic form of being after the reverse item. -/
theorem reverseItem_val_lt_iff {n : ℕ} (j : Item n) :
    (reverseItem j).val < j.val ↔ n < 2 * j.val + 1 := by
  simp [reverseItem]
  omega

/-- Zero-based arithmetic form of being the middle item. -/
theorem val_eq_reverseItem_iff {n : ℕ} (j : Item n) :
    j.val = (reverseItem j).val ↔ 2 * j.val + 1 = n := by
  simp [reverseItem]
  omega

/--
The reduced two-type model for the opposing-preference setting in Theorem 3.
Type `0` has values `v_j`; type `1` has reversed values `v_{n-j+1}`.
-/
noncomputable def twoTypeReducedModel {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel 2 n where
  utility := fun k j => if k = 0 then v j else v (reverseItem j)
  weight := fun k => if k = 0 then alpha else 1 - alpha

@[simp] theorem twoTypeReducedModel_utility_zero {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) :
    (twoTypeReducedModel alpha v).utility 0 j = v j := by
  simp [twoTypeReducedModel]

@[simp] theorem twoTypeReducedModel_utility_one {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) :
    (twoTypeReducedModel alpha v).utility 1 j = v (reverseItem j) := by
  simp [twoTypeReducedModel]

@[simp] theorem twoTypeReducedModel_weight_zero {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) :
    (twoTypeReducedModel alpha v).weight 0 = alpha := by
  simp [twoTypeReducedModel]

@[simp] theorem twoTypeReducedModel_weight_one {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) :
    (twoTypeReducedModel alpha v).weight 1 = 1 - alpha := by
  simp [twoTypeReducedModel]

/-- Interior type shares give strictly positive type weights. -/
theorem twoTypeReducedModel_positiveWeights {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    (twoTypeReducedModel alpha v).PositiveWeights := by
  intro k
  fin_cases k <;> simp [halpha0, sub_pos.mpr halpha1]

/-- Positive base values give strictly positive reduced utilities. -/
theorem twoTypeReducedModel_positiveUtilities {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ)
    (hpos : ∀ j : Item n, 0 < v j) :
    (twoTypeReducedModel alpha v).PositiveUtilities := by
  intro k j
  fin_cases k <;> simp [hpos]

/-- Item normalizers in the two-type model are the denominators of `q_j(α)`. -/
theorem twoTypeReducedModel_itemNormalizer_eq {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) :
    TypeWeightedRecommendationModel.itemNormalizer
      (twoTypeReducedModel alpha v) j =
      alpha * v j + (1 - alpha) * v (reverseItem j) := by
  unfold TypeWeightedRecommendationModel.itemNormalizer
  have huniv : (Finset.univ : Finset (UserType 2)) = {0, 1} := by
    decide
  rw [huniv]
  simp

/-- Raw item utility in the two-type model expanded by type policies. -/
theorem twoTypeReducedModel_rawItemUtility_eq {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (j : Item n) :
    TypeWeightedRecommendationModel.rawItemUtility
      (twoTypeReducedModel alpha v) ρ j =
      alpha * v j * (ρ 0 j).toReal +
        (1 - alpha) * v (reverseItem j) * (ρ 1 j).toReal := by
  unfold TypeWeightedRecommendationModel.rawItemUtility
  have huniv : (Finset.univ : Finset (UserType 2)) = {0, 1} := by
    decide
  rw [huniv]
  simp

/--
Problem 6 item-utility expansion: normalized item utility is the convex
combination `q_j(α) x_j + (1-q_j(α)) y_j`.
-/
theorem twoTypeReducedModel_normalizedItemUtility_eq_pairShare
    {n : ℕ} (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (j : Item n)
    (hden : 0 < alpha * v j + (1 - alpha) * v (reverseItem j)) :
    TypeWeightedRecommendationModel.normalizedItemUtility
      (twoTypeReducedModel alpha v) ρ j =
      pairShare alpha v j * (ρ 0 j).toReal +
        (1 - pairShare alpha v j) * (ρ 1 j).toReal := by
  unfold TypeWeightedRecommendationModel.normalizedItemUtility
  rw [twoTypeReducedModel_itemNormalizer_eq]
  simp [hden.ne']
  rw [twoTypeReducedModel_rawItemUtility_eq]
  unfold pairShare typeOneShare
  field_simp [hden.ne']
  ring

end OpposingTypes
end UserItemFairness
