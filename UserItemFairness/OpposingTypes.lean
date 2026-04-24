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
Lemma 6 scalar algebra: the inverse share gap for mirror items expands to the
paper's denominator-cleared expression.
-/
theorem typeOneShare_inv_sub_inv_one_sub_reverse_eq
    {alpha left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right) :
    (typeOneShare alpha left right)⁻¹ -
        (1 - typeOneShare alpha right left)⁻¹ =
      right / left * (1 - 2 * alpha) / (alpha * (1 - alpha)) := by
  have hden₁ :=
    typeOneShare_denom_pos halpha0 halpha1 hleft hright
  have hden₂ :=
    typeOneShare_denom_pos halpha0 halpha1 hright hleft
  have hq₁ :
      typeOneShare alpha left right ≠ 0 :=
    ne_of_gt (typeOneShare_pos halpha0 halpha1 hleft hright)
  have hq₂ :
      1 - typeOneShare alpha right left ≠ 0 :=
    ne_of_gt (one_sub_typeOneShare_pos halpha0 halpha1 hright hleft)
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha0
  have hone_sub_ne : 1 - alpha ≠ 0 := ne_of_gt (sub_pos.mpr halpha1)
  have hleft_ne : left ≠ 0 := ne_of_gt hleft
  have halpha_left_ne : alpha * left ≠ 0 :=
    mul_ne_zero halpha_ne hleft_ne
  have honesub_left_ne : (1 - alpha) * left ≠ 0 :=
    mul_ne_zero hone_sub_ne hleft_ne
  have hinv_left :
      (typeOneShare alpha left right)⁻¹ =
        (alpha * left + (1 - alpha) * right) / (alpha * left) := by
    unfold typeOneShare
    field_simp [hden₁.ne', halpha_left_ne]
  have hinv_right :
      (1 - typeOneShare alpha right left)⁻¹ =
        (alpha * right + (1 - alpha) * left) / ((1 - alpha) * left) := by
    unfold typeOneShare
    field_simp [hden₂.ne', honesub_left_ne]
    ring
  rw [hinv_left, hinv_right]
  field_simp [halpha_ne, hone_sub_ne, hleft_ne]
  ring_nf

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

/--
At `α = 1/2`, mirror shares are complementary:
`q(left,right) + q(right,left) = 1`.
-/
theorem typeOneShare_half_add_reverse_eq_one
    {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) :
    typeOneShare (1 / 2) left right +
        typeOneShare (1 / 2) right left = 1 := by
  unfold typeOneShare
  have hden₁ :
      (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * right ≠ 0 := by
    have hpos : 0 <
        (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * right := by
      nlinarith
    exact ne_of_gt hpos
  have hden₂ :
      (1 / 2 : ℝ) * right + (1 - (1 / 2 : ℝ)) * left ≠ 0 := by
    have hpos : 0 <
        (1 / 2 : ℝ) * right + (1 - (1 / 2 : ℝ)) * left := by
      nlinarith
    exact ne_of_gt hpos
  field_simp [hden₁, hden₂]
  ring

/-- The opposite item index `n - j + 1` in zero-based `Fin n` notation. -/
def reverseItem {n : ℕ} (j : Item n) : Item n :=
  ⟨n - 1 - j.val, by omega⟩

/-- Reversing the opposite item index returns the original item. -/
theorem reverseItem_reverseItem {n : ℕ} (j : Item n) :
    reverseItem (reverseItem j) = j := by
  ext
  simp [reverseItem]
  omega

/-- The indexed `q_j(α)` used in the opposing-preference proofs. -/
noncomputable def pairShare {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) : ℝ :=
  typeOneShare alpha (v j) (v (reverseItem j))

/--
Appendix D, Lemma 6, indexed mirror-pair algebra:
`1/q_j - 1/(1-q_{n-j+1})` has the paper's closed form.
-/
theorem pairShare_inv_sub_inv_one_sub_reverse_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (pairShare alpha v j)⁻¹ -
        (1 - pairShare alpha v (reverseItem j))⁻¹ =
      v (reverseItem j) / v j * (1 - 2 * alpha) /
        (alpha * (1 - alpha)) := by
  unfold pairShare
  rw [reverseItem_reverseItem]
  exact typeOneShare_inv_sub_inv_one_sub_reverse_eq
    halpha0 halpha1 (hpos j) (hpos (reverseItem j))

/--
Appendix D, Lemma 6, indexed mirror-pair inequality for `α ≤ 1/2`.
-/
theorem pairShare_inv_sub_inv_one_sub_reverse_nonneg_of_alpha_le_half
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 ≤ (pairShare alpha v j)⁻¹ -
        (1 - pairShare alpha v (reverseItem j))⁻¹ := by
  rw [pairShare_inv_sub_inv_one_sub_reverse_eq
    j halpha0 halpha1 hpos]
  have hratio : 0 ≤ v (reverseItem j) / v j :=
    div_nonneg (hpos (reverseItem j)).le (hpos j).le
  have hnum : 0 ≤ 1 - 2 * alpha := by
    nlinarith
  have hden : 0 ≤ alpha * (1 - alpha) :=
    (mul_pos halpha0 (sub_pos.mpr halpha1)).le
  exact div_nonneg (mul_nonneg hratio hnum) hden

/--
Appendix D, Lemma 10 setup: at `α = 1/2`, opposite items have complementary
shares.
-/
theorem pairShare_half_add_reverse_eq_one
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare (1 / 2) v j +
        pairShare (1 / 2) v (reverseItem j) = 1 := by
  unfold pairShare
  rw [reverseItem_reverseItem]
  exact typeOneShare_half_add_reverse_eq_one
    (hpos j) (hpos (reverseItem j))

/--
Appendix D, Lemma 10 setup: `q_j(1/2) = 1 - q_{n-j+1}(1/2)`.
-/
theorem pairShare_half_eq_one_sub_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare (1 / 2) v j =
      1 - pairShare (1 / 2) v (reverseItem j) := by
  have hsum := pairShare_half_add_reverse_eq_one j hpos
  linarith

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

/--
Problem 6 LP feasibility in the paper's `x_j`, `y_j`, `q_j(α)`, `λ` notation.
For a type policy `ρ`, `x_j` is `ρ 0 j` and `y_j` is `ρ 1 j`.
-/
def problem6LPFeasible {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (ell : ℝ) : Prop :=
  ∀ j : Item n,
    ell ≤ pairShare alpha v j * (ρ 0 j).toReal +
      (1 - pairShare alpha v j) * (ρ 1 j).toReal

/-- Problem 6 variable nonnegativity for `x_j = ρ_{0j}`. -/
theorem problem6_typeZero_prob_nonneg {n : ℕ}
    (ρ : TypePolicy 2 n) (j : Item n) :
    0 ≤ (ρ 0 j).toReal := by
  exact ENNReal.toReal_nonneg

/-- Problem 6 variable nonnegativity for `y_j = ρ_{1j}`. -/
theorem problem6_typeOne_prob_nonneg {n : ℕ}
    (ρ : TypePolicy 2 n) (j : Item n) :
    0 ≤ (ρ 1 j).toReal := by
  exact ENNReal.toReal_nonneg

/-- Problem 6 row constraint `∑_j x_j = 1`. -/
theorem problem6_typeZero_sum_eq_one {n : ℕ}
    (ρ : TypePolicy 2 n) :
    (∑ j : Item n, (ρ 0 j).toReal) = 1 := by
  exact DecisionCore.pmfToRealSum (ρ 0)

/-- Problem 6 row constraint `∑_j y_j = 1`. -/
theorem problem6_typeOne_sum_eq_one {n : ℕ}
    (ρ : TypePolicy 2 n) :
    (∑ j : Item n, (ρ 1 j).toReal) = 1 := by
  exact DecisionCore.pmfToRealSum (ρ 1)

/-- Lemma 5's left-side sum `L_t = ∑_{j<t} 1 / q_j`. -/
noncomputable def problem6LeftSum {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  ∑ j : Item n, if j.val < t.val then (pairShare alpha v j)⁻¹ else 0

/-- Lemma 5's right-side sum `R_t = ∑_{j>t} 1 / (1 - q_j)`. -/
noncomputable def problem6RightSum {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  ∑ j : Item n, if t.val < j.val then (1 - pairShare alpha v j)⁻¹ else 0

/-- Lemma 5's denominator `1 + q_t L_t + (1 - q_t) R_t`. -/
noncomputable def problem6ClosedDenominator {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  1 + pairShare alpha v t * problem6LeftSum alpha v t +
    (1 - pairShare alpha v t) * problem6RightSum alpha v t

/-- Lemma 5's closed-form value `I^*_min = 1 / (1 + q_t L_t + (1-q_t)R_t)`. -/
noncomputable def problem6ClosedValue {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  1 / problem6ClosedDenominator alpha v t

/--
The sparse, equalized solution shape produced by Lemma 4 and used in Lemma 5.
The real variables `x` and `y` correspond to the two type policies.
-/
structure Problem6SparseEqualized {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n)
    (x y : Item n → ℝ) (ell : ℝ) : Prop where
  item_eq :
    ∀ j : Item n,
      pairShare alpha v j * x j + (1 - pairShare alpha v j) * y j = ell
  sum_x : (∑ j : Item n, x j) = 1
  sum_y : (∑ j : Item n, y j) = 1
  x_after_pivot_zero : ∀ {j : Item n}, t.val < j.val → x j = 0
  y_before_pivot_zero : ∀ {j : Item n}, j.val < t.val → y j = 0

theorem problem6LeftSum_nonneg {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 ≤ problem6LeftSum alpha v t := by
  unfold problem6LeftSum
  refine Finset.sum_nonneg ?_
  intro j _hj
  by_cases hlt : j.val < t.val
  · simp [hlt, inv_nonneg.mpr (pairShare_pos j halpha0 halpha1 hpos).le]
  · simp [hlt]

theorem problem6RightSum_nonneg {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 ≤ problem6RightSum alpha v t := by
  unfold problem6RightSum
  refine Finset.sum_nonneg ?_
  intro j _hj
  by_cases hlt : t.val < j.val
  · simp [hlt, inv_nonneg.mpr (one_sub_pairShare_pos j halpha0 halpha1 hpos).le]
  · simp [hlt]

/-- The Lemma 5 denominator is strictly positive. -/
theorem problem6ClosedDenominator_pos {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < problem6ClosedDenominator alpha v t := by
  have hL := problem6LeftSum_nonneg t halpha0 halpha1 hpos
  have hR := problem6RightSum_nonneg t halpha0 halpha1 hpos
  have hq := (pairShare_pos t halpha0 halpha1 hpos).le
  have hqc := (one_sub_pairShare_pos t halpha0 halpha1 hpos).le
  unfold problem6ClosedDenominator
  nlinarith

/-- Lemma 5's closed-form value is positive. -/
theorem problem6ClosedValue_pos {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < problem6ClosedValue alpha v t := by
  unfold problem6ClosedValue
  exact one_div_pos.mpr
    (problem6ClosedDenominator_pos t halpha0 halpha1 hpos)

private theorem problem6_sum_eq_left_part_add_pivot_of_after_zero {n : ℕ}
    (x : Item n → ℝ) (t : Item n)
    (hzero : ∀ {j : Item n}, t.val < j.val → x j = 0) :
    (∑ j : Item n, x j) =
      (∑ j : Item n, if j.val < t.val then x j else 0) + x t := by
  classical
  calc
    (∑ j : Item n, x j)
        = ∑ j : Item n,
            ((if j.val < t.val then x j else 0) +
              (if j = t then x t else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          by_cases hlt : j.val < t.val
          · have hne : j ≠ t := by
              intro h
              subst h
              omega
            simp [hlt, hne]
          · by_cases heq : j = t
            · subst heq
              simp
            · have hgt : t.val < j.val := by
                have hne_val : j.val ≠ t.val := by
                  intro hval
                  exact heq (Fin.ext hval)
                omega
              simp [hlt, heq, hzero hgt]
    _ = (∑ j : Item n, if j.val < t.val then x j else 0) +
          (∑ j : Item n, if j = t then x t else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ j : Item n, if j.val < t.val then x j else 0) + x t := by
          simp

private theorem problem6_sum_eq_pivot_add_right_part_of_before_zero {n : ℕ}
    (y : Item n → ℝ) (t : Item n)
    (hzero : ∀ {j : Item n}, j.val < t.val → y j = 0) :
    (∑ j : Item n, y j) =
      y t + (∑ j : Item n, if t.val < j.val then y j else 0) := by
  classical
  calc
    (∑ j : Item n, y j)
        = ∑ j : Item n,
            ((if j = t then y t else 0) +
              (if t.val < j.val then y j else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          by_cases heq : j = t
          · subst heq
            simp
          · by_cases hgt : t.val < j.val
            · simp [heq, hgt]
            · have hlt : j.val < t.val := by
                have hne_val : j.val ≠ t.val := by
                  intro hval
                  exact heq (Fin.ext hval)
                omega
              simp [heq, hgt, hzero hlt]
    _ = (∑ j : Item n, if j = t then y t else 0) +
          (∑ j : Item n, if t.val < j.val then y j else 0) := by
          rw [Finset.sum_add_distrib]
    _ = y t + (∑ j : Item n, if t.val < j.val then y j else 0) := by
          simp

/-- Lemma 5: before the pivot, `x_j = λ / q_j`. -/
theorem problem6SparseEqualized_x_before_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hj : j.val < t.val) :
    x j = ell / pairShare alpha v j := by
  have hqne : pairShare alpha v j ≠ 0 :=
    ne_of_gt (pairShare_pos j halpha0 halpha1 hpos)
  have hmul : pairShare alpha v j * x j = ell := by
    have heq := h.item_eq j
    rw [h.y_before_pivot_zero hj] at heq
    simpa using heq
  calc
    x j = (pairShare alpha v j * x j) / pairShare alpha v j := by
      field_simp [hqne]
    _ = ell / pairShare alpha v j := by
      rw [hmul]

/-- Lemma 5: after the pivot, `y_j = λ / (1 - q_j)`. -/
theorem problem6SparseEqualized_y_after_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hj : t.val < j.val) :
    y j = ell / (1 - pairShare alpha v j) := by
  have hqne : 1 - pairShare alpha v j ≠ 0 :=
    ne_of_gt (one_sub_pairShare_pos j halpha0 halpha1 hpos)
  have hmul : (1 - pairShare alpha v j) * y j = ell := by
    have heq := h.item_eq j
    rw [h.x_after_pivot_zero hj] at heq
    simpa using heq
  calc
    y j = ((1 - pairShare alpha v j) * y j) /
        (1 - pairShare alpha v j) := by
      field_simp [hqne]
    _ = ell / (1 - pairShare alpha v j) := by
      rw [hmul]

private theorem problem6SparseEqualized_left_part_sum_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    (∑ j : Item n, if j.val < t.val then x j else 0) =
      ell * problem6LeftSum alpha v t := by
  unfold problem6LeftSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hj : j.val < t.val
  · simp [hj, problem6SparseEqualized_x_before_eq
      halpha0 halpha1 hpos h hj, div_eq_mul_inv]
  · simp [hj]

private theorem problem6SparseEqualized_right_part_sum_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    (∑ j : Item n, if t.val < j.val then y j else 0) =
      ell * problem6RightSum alpha v t := by
  unfold problem6RightSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hj : t.val < j.val
  · simp [hj, problem6SparseEqualized_y_after_eq
      halpha0 halpha1 hpos h hj, div_eq_mul_inv]
  · simp [hj]

/-- Lemma 5 pivot equation: `x_t = 1 - λ L_t`. -/
theorem problem6SparseEqualized_x_pivot_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    x t = 1 - ell * problem6LeftSum alpha v t := by
  have hsplit :=
    problem6_sum_eq_left_part_add_pivot_of_after_zero x t
      h.x_after_pivot_zero
  have hleft :=
    problem6SparseEqualized_left_part_sum_eq halpha0 halpha1 hpos h
  nlinarith [h.sum_x, hsplit, hleft]

/-- Lemma 5 pivot equation: `y_t = 1 - λ R_t`. -/
theorem problem6SparseEqualized_y_pivot_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    y t = 1 - ell * problem6RightSum alpha v t := by
  have hsplit :=
    problem6_sum_eq_pivot_add_right_part_of_before_zero y t
      h.y_before_pivot_zero
  have hright :=
    problem6SparseEqualized_right_part_sum_eq halpha0 halpha1 hpos h
  nlinarith [h.sum_y, hsplit, hright]

/-- Lemma 5 closed value: `λ = 1 / (1 + q_t L_t + (1-q_t)R_t)`. -/
theorem problem6SparseEqualized_value_eq_closed
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    ell = problem6ClosedValue alpha v t := by
  have hx :=
    problem6SparseEqualized_x_pivot_eq halpha0 halpha1 hpos h
  have hy :=
    problem6SparseEqualized_y_pivot_eq halpha0 halpha1 hpos h
  have ht := h.item_eq t
  rw [hx, hy] at ht
  have hmul : ell * problem6ClosedDenominator alpha v t = 1 := by
    unfold problem6ClosedDenominator
    nlinarith
  have hDpos :=
    problem6ClosedDenominator_pos t halpha0 halpha1 hpos
  unfold problem6ClosedValue
  rw [eq_div_iff (ne_of_gt hDpos)]
  exact hmul

/-- Lemma 5 closed form: before the pivot, `x_j = I^*_min / q_j`. -/
theorem problem6SparseEqualized_x_before_eq_closed
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hj : j.val < t.val) :
    x j = problem6ClosedValue alpha v t / pairShare alpha v j := by
  rw [problem6SparseEqualized_x_before_eq halpha0 halpha1 hpos h hj,
    problem6SparseEqualized_value_eq_closed halpha0 halpha1 hpos h]

/-- Lemma 5 closed form: after the pivot, `y_j = I^*_min / (1 - q_j)`. -/
theorem problem6SparseEqualized_y_after_eq_closed
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hj : t.val < j.val) :
    y j = problem6ClosedValue alpha v t / (1 - pairShare alpha v j) := by
  rw [problem6SparseEqualized_y_after_eq halpha0 halpha1 hpos h hj,
    problem6SparseEqualized_value_eq_closed halpha0 halpha1 hpos h]

/-- Lemma 5 closed form for the pivot `x_t`. -/
theorem problem6SparseEqualized_x_pivot_eq_closed
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    x t = 1 - problem6ClosedValue alpha v t *
      problem6LeftSum alpha v t := by
  rw [problem6SparseEqualized_x_pivot_eq halpha0 halpha1 hpos h,
    problem6SparseEqualized_value_eq_closed halpha0 halpha1 hpos h]

/-- Lemma 5 closed form for the pivot `y_t`. -/
theorem problem6SparseEqualized_y_pivot_eq_closed
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    y t = 1 - problem6ClosedValue alpha v t *
      problem6RightSum alpha v t := by
  rw [problem6SparseEqualized_y_pivot_eq halpha0 halpha1 hpos h,
    problem6SparseEqualized_value_eq_closed halpha0 halpha1 hpos h]

/--
A certificate that a proposed Problem 6 policy and value solve the finite LP:
the policy attains `ell`, and no feasible policy can exceed `ell`.
-/
structure Problem6OptimalityCertificate {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ell : ℝ) where
  policy : TypePolicy 2 n
  feasible : problem6LPFeasible alpha v policy ell
  upper_bound :
    ∀ (ρ : TypePolicy 2 n) (ell' : ℝ),
      problem6LPFeasible alpha v ρ ell' → ell' ≤ ell

/-- Feasible objective values for Problem 6's LP. -/
def problem6LPValueSet {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) : Set ℝ :=
  {ell | ∃ ρ : TypePolicy 2 n, problem6LPFeasible alpha v ρ ell}

/-- The optimal value of Problem 6's LP. -/
noncomputable def problem6LPOptimalValue {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) : ℝ :=
  sSup (problem6LPValueSet alpha v)

/-- Problem 6 LP feasibility is equivalent to the reduced item-fairness epigraph. -/
theorem problem6LPFeasible_iff_le_itemFairness
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (ell : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6LPFeasible alpha v ρ ell ↔
      ell ≤ TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) ρ := by
  constructor
  · intro h
    unfold TypeWeightedRecommendationModel.itemFairness DecisionCore.finiteMin
    apply Finset.le_inf'
    intro j _hj
    have hden :=
      typeOneShare_denom_pos halpha0 halpha1 (hpos j) (hpos (reverseItem j))
    rw [twoTypeReducedModel_normalizedItemUtility_eq_pairShare
      alpha v ρ j hden]
    exact h j
  · intro h j
    have hden :=
      typeOneShare_denom_pos halpha0 halpha1 (hpos j) (hpos (reverseItem j))
    have hle :
        TypeWeightedRecommendationModel.itemFairness
            (twoTypeReducedModel alpha v) ρ ≤
          TypeWeightedRecommendationModel.normalizedItemUtility
            (twoTypeReducedModel alpha v) ρ j := by
      exact DecisionCore.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedItemUtility
          (twoTypeReducedModel alpha v) ρ) j
    rw [twoTypeReducedModel_normalizedItemUtility_eq_pairShare
      alpha v ρ j hden] at hle
    exact h.trans hle

/-- Problem 6's LP value set is nonempty. -/
theorem problem6LPValueSet_nonempty
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (problem6LPValueSet alpha v).Nonempty := by
  let ρ : TypePolicy 2 n := TypeWeightedRecommendationModel.uniformTypePolicy
  refine ⟨TypeWeightedRecommendationModel.itemFairness
    (twoTypeReducedModel alpha v) ρ, ?_⟩
  exact ⟨ρ, (problem6LPFeasible_iff_le_itemFairness
    alpha v ρ
    (TypeWeightedRecommendationModel.itemFairness
      (twoTypeReducedModel alpha v) ρ)
    halpha0 halpha1 hpos).mpr le_rfl⟩

/-- Problem 6 LP objective values are bounded above by one. -/
theorem problem6LPValueSet_bddAbove
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    BddAbove (problem6LPValueSet alpha v) := by
  refine ⟨1, ?_⟩
  intro ell hell
  obtain ⟨ρ, hρ⟩ := hell
  have hle_item :
      ell ≤ TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) ρ :=
    (problem6LPFeasible_iff_le_itemFairness
      alpha v ρ ell halpha0 halpha1 hpos).mp hρ
  let j0 : Item n := Classical.choice inferInstance
  have hitem_le :
      TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ ≤
        TypeWeightedRecommendationModel.normalizedItemUtility
          (twoTypeReducedModel alpha v) ρ j0 := by
    exact DecisionCore.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedItemUtility
        (twoTypeReducedModel alpha v) ρ) j0
  have hWeightNonneg :
      (twoTypeReducedModel alpha v).NonnegativeWeights :=
    TypeWeightedRecommendationModel.nonnegativeWeights_of_positiveWeights
      (twoTypeReducedModel alpha v)
      (twoTypeReducedModel_positiveWeights alpha v halpha0 halpha1)
  have hUtilNonneg :
      (twoTypeReducedModel alpha v).NonnegativeUtilities :=
    TypeWeightedRecommendationModel.nonnegativeUtilities_of_positiveUtilities
      (twoTypeReducedModel alpha v)
      (twoTypeReducedModel_positiveUtilities alpha v hpos)
  exact hle_item.trans (hitem_le.trans
    (TypeWeightedRecommendationModel.normalizedItemUtility_le_one_of_nonnegative
      (twoTypeReducedModel alpha v) hWeightNonneg hUtilNonneg ρ j0))

/--
Problem 6 LP equivalence: maximizing the paper's LP objective `λ` has the same
value as the reduced type-level item-fairness optimum.
-/
theorem problem6LPOptimalValue_eq_optimalItemFairness
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6LPOptimalValue alpha v =
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) := by
  have hLPNonempty :=
    problem6LPValueSet_nonempty alpha v halpha0 halpha1 hpos
  have hLPBdd :=
    problem6LPValueSet_bddAbove alpha v halpha0 halpha1 hpos
  have hWeightNonneg :
      (twoTypeReducedModel alpha v).NonnegativeWeights :=
    TypeWeightedRecommendationModel.nonnegativeWeights_of_positiveWeights
      (twoTypeReducedModel alpha v)
      (twoTypeReducedModel_positiveWeights alpha v halpha0 halpha1)
  have hUtilNonneg :
      (twoTypeReducedModel alpha v).NonnegativeUtilities :=
    TypeWeightedRecommendationModel.nonnegativeUtilities_of_positiveUtilities
      (twoTypeReducedModel alpha v)
      (twoTypeReducedModel_positiveUtilities alpha v hpos)
  have hItemBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableItemFairnessSet
        (twoTypeReducedModel alpha v)) :=
    TypeWeightedRecommendationModel.attainableItemFairnessSet_bddAbove_of_nonnegative
      (twoTypeReducedModel alpha v) hWeightNonneg hUtilNonneg
  have hItemNonempty :
      (TypeWeightedRecommendationModel.attainableItemFairnessSet
        (twoTypeReducedModel alpha v)).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.itemFairness
      (twoTypeReducedModel alpha v)
      (TypeWeightedRecommendationModel.uniformTypePolicy (K := 2) (n := n)), ?_⟩
    exact ⟨TypeWeightedRecommendationModel.uniformTypePolicy (K := 2) (n := n), rfl⟩
  apply le_antisymm
  · unfold problem6LPOptimalValue
    refine csSup_le hLPNonempty ?_
    intro ell hell
    obtain ⟨ρ, hρ⟩ := hell
    have hle_item :
        ell ≤ TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ :=
      (problem6LPFeasible_iff_le_itemFairness
        alpha v ρ ell halpha0 halpha1 hpos).mp hρ
    have hitem_mem :
        TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ ∈
            TypeWeightedRecommendationModel.attainableItemFairnessSet
              (twoTypeReducedModel alpha v) := by
      exact ⟨ρ, rfl⟩
    exact hle_item.trans (le_csSup hItemBdd hitem_mem)
  · unfold TypeWeightedRecommendationModel.optimalItemFairness
    refine csSup_le hItemNonempty ?_
    intro r hr
    obtain ⟨ρ, hr⟩ := hr
    rw [hr]
    have hlp_mem :
        TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ ∈ problem6LPValueSet alpha v := by
      exact ⟨ρ, (problem6LPFeasible_iff_le_itemFairness
        alpha v ρ
        (TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ)
        halpha0 halpha1 hpos).mpr le_rfl⟩
    exact le_csSup hLPBdd hlp_mem

/--
If the paper's proposed closed-form policy/value pair satisfies the finite
upper-bound certificate, then it is exactly the Problem 6 LP optimum.
-/
theorem problem6LPOptimalValue_eq_of_certificate
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ell : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (cert : Problem6OptimalityCertificate alpha v ell) :
    problem6LPOptimalValue alpha v = ell := by
  have hLPNonempty :=
    problem6LPValueSet_nonempty alpha v halpha0 halpha1 hpos
  have hLPBdd :=
    problem6LPValueSet_bddAbove alpha v halpha0 halpha1 hpos
  apply le_antisymm
  · unfold problem6LPOptimalValue
    refine csSup_le hLPNonempty ?_
    intro ell' hell'
    obtain ⟨ρ, hρ⟩ := hell'
    exact cert.upper_bound ρ ell' hρ
  · unfold problem6LPOptimalValue
    exact le_csSup hLPBdd ⟨cert.policy, cert.feasible⟩

end OpposingTypes
end UserItemFairness
