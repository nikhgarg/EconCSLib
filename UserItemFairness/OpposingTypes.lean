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

/-- Reversal as a finite equivalence on item indices. -/
def reverseItemEquiv (n : ℕ) : Item n ≃ Item n where
  toFun := reverseItem
  invFun := reverseItem
  left_inv := reverseItem_reverseItem
  right_inv := reverseItem_reverseItem

/-- Reindex a finite sum by item reversal. -/
theorem sum_reverseItem {n : ℕ} (f : Item n → ℝ) :
    (∑ j : Item n, f (reverseItem j)) = ∑ j : Item n, f j := by
  simpa [reverseItemEquiv] using
    (Equiv.sum_comp (reverseItemEquiv n) f)

/-- Reindexing by item reversal preserves finite maxima. -/
theorem finiteMax_reverseItem {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    DecisionCore.finiteMax (fun j : Item n => v (reverseItem j)) =
      DecisionCore.finiteMax v := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ :=
      DecisionCore.exists_finiteMax_eq
        (fun j : Item n => v (reverseItem j))
    rw [hj]
    exact DecisionCore.le_finiteMax v (reverseItem j)
  · obtain ⟨j, hj⟩ := DecisionCore.exists_finiteMax_eq v
    rw [hj]
    have hle :=
      DecisionCore.le_finiteMax
        (fun j : Item n => v (reverseItem j)) (reverseItem j)
    simpa [reverseItem_reverseItem] using hle

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

/-- Zero-based arithmetic form of being at or before the reverse item. -/
theorem val_le_reverseItem_iff {n : ℕ} (j : Item n) :
    j.val ≤ (reverseItem j).val ↔ 2 * j.val + 1 ≤ n := by
  simp [reverseItem]
  omega

/--
If the pivot is at or before its mirror, then every item before the pivot has
its mirror after the pivot.
-/
theorem reverseItem_after_pivot_of_before_pivot_of_pivot_le_reverse
    {n : ℕ} {t j : Item n}
    (hcenter : t.val ≤ (reverseItem t).val)
    (hj : j.val < t.val) :
    t.val < (reverseItem j).val := by
  exact lt_of_le_of_lt hcenter (reverseItem_val_lt_of_val_lt hj)

/-- For an exact center pivot, mirroring identifies post-pivot and pre-pivot items. -/
theorem pivot_lt_reverseItem_iff_val_lt_pivot_of_pivot_eq_reverse
    {n : ℕ} {t j : Item n}
    (hcenter : t.val = (reverseItem t).val) :
    t.val < (reverseItem j).val ↔ j.val < t.val := by
  simp [reverseItem] at hcenter ⊢
  omega

/--
For an even midpoint pivot immediately before its mirror, post-pivot mirrors
are exactly the pivot and pre-pivot items.
-/
theorem pivot_lt_reverseItem_iff_val_le_pivot_of_pivot_succ_reverse
    {n : ℕ} {t j : Item n}
    (hsucc : t.val + 1 = (reverseItem t).val) :
    t.val < (reverseItem j).val ↔ j.val ≤ t.val := by
  simp [reverseItem] at hsucc ⊢
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

/-- The two opposing types have the same best-item utility. -/
theorem twoTypeReducedModel_bestItemUtility_one_eq_zero {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 0 := by
  unfold TypeWeightedRecommendationModel.bestItemUtility
  change DecisionCore.finiteMax (fun j : Item n => v (reverseItem j)) =
    DecisionCore.finiteMax v
  exact finiteMax_reverseItem v

/-- Positive base values give a positive common best-item denominator. -/
theorem twoTypeReducedModel_bestItemUtility_zero_pos {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < TypeWeightedRecommendationModel.bestItemUtility
      (twoTypeReducedModel alpha v) 0 := by
  let j0 : Item n := Classical.choice inferInstance
  unfold TypeWeightedRecommendationModel.bestItemUtility
  change 0 < DecisionCore.finiteMax v
  exact lt_of_lt_of_le (hpos j0) (DecisionCore.le_finiteMax v j0)

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

/-- Lemma 5's closed-form `x_j` coordinates for a fixed pivot `t`. -/
noncomputable def problem6ClosedX {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t j : Item n) : ℝ :=
  if j.val < t.val then
    problem6ClosedValue alpha v t / pairShare alpha v j
  else if j = t then
    1 - problem6ClosedValue alpha v t * problem6LeftSum alpha v t
  else
    0

/-- Lemma 5's closed-form `y_j` coordinates for a fixed pivot `t`. -/
noncomputable def problem6ClosedY {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t j : Item n) : ℝ :=
  if j.val < t.val then
    0
  else if j = t then
    1 - problem6ClosedValue alpha v t * problem6RightSum alpha v t
  else
    problem6ClosedValue alpha v t / (1 - pairShare alpha v j)

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

/--
Appendix D, Lemma 10 exact-center case: at `α = 1/2`, an exact center pivot
has identical left and right inverse-share sums after mirror reindexing.
-/
theorem problem6LeftSum_half_eq_rightSum_half_of_pivot_eq_reverse {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    problem6LeftSum (1 / 2) v t = problem6RightSum (1 / 2) v t := by
  unfold problem6LeftSum problem6RightSum
  rw [← sum_reverseItem
    (fun j : Item n =>
      if t.val < j.val then (1 - pairShare (1 / 2) v j)⁻¹ else 0)]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  have hiff :=
    pivot_lt_reverseItem_iff_val_lt_pivot_of_pivot_eq_reverse
      (t := t) (j := j) hcenter
  by_cases hj : j.val < t.val
  · have hmirror : t.val < (reverseItem j).val := hiff.mpr hj
    have hshare := pairShare_half_eq_one_sub_reverse j hpos
    simpa [hj, hmirror, one_div] using hshare
  · have hmirror : ¬ t.val < (reverseItem j).val := by
      intro hlt
      exact hj (hiff.mp hlt)
    simp [hj, hmirror]

/--
Appendix D, Lemma 10 exact-center denominator simplification:
at `α = 1/2` and an exact center pivot, Lemma 5's denominator is `1 + L_t`.
-/
theorem problem6ClosedDenominator_half_center_eq_one_add_leftSum {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    problem6ClosedDenominator (1 / 2) v t =
      1 + problem6LeftSum (1 / 2) v t := by
  have hsum :=
    problem6LeftSum_half_eq_rightSum_half_of_pivot_eq_reverse
      (v := v) (t := t) hpos hcenter
  have hshare := pairShare_half_eq_half_of_val_eq_reverse t hpos hcenter
  unfold problem6ClosedDenominator
  rw [hshare, ← hsum]
  ring

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

theorem problem6ClosedX_before {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) {t j : Item n}
    (hj : j.val < t.val) :
    problem6ClosedX alpha v t j =
      problem6ClosedValue alpha v t / pairShare alpha v j := by
  simp [problem6ClosedX, hj]

theorem problem6ClosedX_at {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedX alpha v t t =
      1 - problem6ClosedValue alpha v t * problem6LeftSum alpha v t := by
  simp [problem6ClosedX]

theorem problem6ClosedX_after {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) {t j : Item n}
    (hj : t.val < j.val) :
    problem6ClosedX alpha v t j = 0 := by
  have hnlt : ¬ j.val < t.val := by omega
  have hne : j ≠ t := by
    intro h
    subst h
    omega
  simp [problem6ClosedX, hnlt, hne]

theorem problem6ClosedY_before {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) {t j : Item n}
    (hj : j.val < t.val) :
    problem6ClosedY alpha v t j = 0 := by
  simp [problem6ClosedY, hj]

theorem problem6ClosedY_at {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedY alpha v t t =
      1 - problem6ClosedValue alpha v t * problem6RightSum alpha v t := by
  simp [problem6ClosedY]

theorem problem6ClosedY_after {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) {t j : Item n}
    (hj : t.val < j.val) :
    problem6ClosedY alpha v t j =
      problem6ClosedValue alpha v t / (1 - pairShare alpha v j) := by
  have hnlt : ¬ j.val < t.val := by omega
  have hne : j ≠ t := by
    intro h
    subst h
    omega
  simp [problem6ClosedY, hnlt, hne]

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

private theorem problem6_sum_eq_left_part_add_pivot_add_right_part {n : ℕ}
    (x : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, x j) =
      (∑ j : Item n, if j.val < t.val then x j else 0) + x t +
        (∑ j : Item n, if t.val < j.val then x j else 0) := by
  classical
  calc
    (∑ j : Item n, x j)
        = ∑ j : Item n,
            ((if j.val < t.val then x j else 0) +
              (if j = t then x t else 0) +
              (if t.val < j.val then x j else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          by_cases hlt : j.val < t.val
          · have hne : j ≠ t := by
              intro h
              subst h
              omega
            have hnlt : ¬ t.val < j.val := by omega
            simp [hlt, hne, hnlt]
          · by_cases heq : j = t
            · subst heq
              simp
            · have hgt : t.val < j.val := by
                have hne_val : j.val ≠ t.val := by
                  intro hval
                  exact heq (Fin.ext hval)
                omega
              simp [hlt, heq, hgt]
    _ =
        ((∑ j : Item n, if j.val < t.val then x j else 0) +
          (∑ j : Item n, if j = t then x t else 0)) +
          (∑ j : Item n, if t.val < j.val then x j else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ j : Item n, if j.val < t.val then x j else 0) + x t +
        (∑ j : Item n, if t.val < j.val then x j else 0) := by
          simp [add_assoc]

/--
Appendix D, Lemma 10 even-center case: when the midpoint candidate is
immediately before its mirror, the right inverse-share sum is the left sum plus
the pivot's inverse share.
-/
theorem problem6RightSum_half_eq_leftSum_half_add_inv_pairShare_of_pivot_succ_reverse
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    problem6RightSum (1 / 2) v t =
      problem6LeftSum (1 / 2) v t + (pairShare (1 / 2) v t)⁻¹ := by
  unfold problem6LeftSum problem6RightSum
  rw [← sum_reverseItem
    (fun j : Item n =>
      if t.val < j.val then (1 - pairShare (1 / 2) v j)⁻¹ else 0)]
  have hreindex :
      (∑ j : Item n,
        if t.val < (reverseItem j).val then
          (1 - pairShare (1 / 2) v (reverseItem j))⁻¹
        else 0) =
        ∑ j : Item n,
          if j.val ≤ t.val then (pairShare (1 / 2) v j)⁻¹ else 0 := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    have hiff :=
      pivot_lt_reverseItem_iff_val_le_pivot_of_pivot_succ_reverse
        (t := t) (j := j) hsucc
    by_cases hj : j.val ≤ t.val
    · have hmirror : t.val < (reverseItem j).val := hiff.mpr hj
      have hshare := pairShare_half_eq_one_sub_reverse j hpos
      simpa [hj, hmirror, one_div] using hshare.symm
    · have hmirror : ¬ t.val < (reverseItem j).val := by
        intro hlt
        exact hj (hiff.mp hlt)
      simp [hj, hmirror]
  rw [hreindex]
  let x : Item n → ℝ :=
    fun j => if j.val ≤ t.val then (pairShare (1 / 2) v j)⁻¹ else 0
  have hzero : ∀ {j : Item n}, t.val < j.val → x j = 0 := by
    intro j hj
    have hnle_fin : ¬ j ≤ t := not_le.mpr hj
    simp [x, hnle_fin]
  have hsplit :=
    problem6_sum_eq_left_part_add_pivot_of_after_zero x t hzero
  have hleft :
      (∑ j : Item n, if j.val < t.val then x j else 0) =
        ∑ j : Item n,
          if j.val < t.val then (pairShare (1 / 2) v j)⁻¹ else 0 := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hlt : j.val < t.val
    · have hle_fin : j ≤ t := le_of_lt hlt
      simp [x, hlt, hle_fin]
    · simp [x, hlt]
  calc
    (∑ j : Item n, if j.val ≤ t.val then
        (pairShare (1 / 2) v j)⁻¹ else 0)
        = (∑ j : Item n, if j.val < t.val then x j else 0) + x t := by
          simpa [x] using hsplit
    _ = (∑ j : Item n,
          if j.val < t.val then (pairShare (1 / 2) v j)⁻¹ else 0) +
          (pairShare (1 / 2) v t)⁻¹ := by
          rw [hleft]
          simp [x]

/--
Appendix D, Lemma 10 even-center case: for the midpoint pivot immediately
before its mirror, Lemma 5's denominator equals the right inverse-share sum.
-/
theorem problem6ClosedDenominator_half_succ_center_eq_rightSum {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    problem6ClosedDenominator (1 / 2) v t =
      problem6RightSum (1 / 2) v t := by
  have hright :=
    problem6RightSum_half_eq_leftSum_half_add_inv_pairShare_of_pivot_succ_reverse
      (v := v) (t := t) hpos hsucc
  set q := pairShare (1 / 2) v t
  set L := problem6LeftSum (1 / 2) v t
  have hqpos : 0 < q := by
    simpa [q] using
      pairShare_pos t (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos
  have hqne : q ≠ 0 := ne_of_gt hqpos
  unfold problem6ClosedDenominator
  rw [hright]
  change 1 + q * L + (1 - q) * (L + q⁻¹) = L + q⁻¹
  field_simp [hqne]
  ring

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

/--
Appendix D, Lemma 10 comparison core.  A sparse equalized solution whose pivot
is to the right of another sparse equalized candidate cannot have a strictly
larger value, provided the later solution's `x` masses and the candidate's
pivot `y` mass are nonnegative.
-/
theorem problem6SparseEqualized_value_le_of_candidate_before
    {n : ℕ} {v : Item n → ℝ} {c t : Item n}
    {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (hct : c.val < t.val)
    (h : Problem6SparseEqualized (1 / 2) v t x y ell)
    (hcand : Problem6SparseEqualized (1 / 2) v c x' y' ell')
    (hx_nonneg : ∀ j : Item n, 0 ≤ x j)
    (hy'_pivot_nonneg : 0 ≤ y' c) :
    ell ≤ ell' := by
  by_contra hnot
  have hell_lt : ell' < ell := lt_of_not_ge hnot
  let q : ℝ := pairShare (1 / 2) v c
  have hqpos : 0 < q := by
    simpa [q] using
      pairShare_pos c (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos
  have hqnonneg : 0 ≤ q := hqpos.le
  have hqcomp_nonneg : 0 ≤ 1 - q := by
    have hqcomp_pos :
        0 < 1 - pairShare (1 / 2) v c :=
      one_sub_pairShare_pos c (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos
    simpa [q] using hqcomp_pos.le
  have hitem_later : q * x c = ell := by
    have heq := h.item_eq c
    rw [h.y_before_pivot_zero hct] at heq
    simpa [q] using heq
  have hitem_candidate : q * x' c + (1 - q) * y' c = ell' := by
    have heq := hcand.item_eq c
    simpa [q] using heq
  have hstrict :
      q * x c > q * x' c + (1 - q) * y' c := by
    nlinarith
  let leftx : ℝ :=
    ∑ j : Item n, if j.val < c.val then x j else 0
  let leftx' : ℝ :=
    ∑ j : Item n, if j.val < c.val then x' j else 0
  have hleft_le : leftx' ≤ leftx := by
    unfold leftx leftx'
    refine Finset.sum_le_sum ?_
    intro j _hj
    by_cases hjc : j.val < c.val
    · have hjt : j.val < t.val := lt_trans hjc hct
      have hqj_nonneg :
          0 ≤ pairShare (1 / 2) v j :=
        (pairShare_pos j (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos).le
      simp [hjc]
      rw [problem6SparseEqualized_x_before_eq
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos hcand hjc,
        problem6SparseEqualized_x_before_eq
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos h hjt]
      exact div_le_div_of_nonneg_right hell_lt.le hqj_nonneg
    · simp [hjc]
  have hsplit_candidate :=
    problem6_sum_eq_left_part_add_pivot_of_after_zero
      x' c hcand.x_after_pivot_zero
  have hx'_pivot : x' c = 1 - leftx' := by
    have hsum :
        (∑ j : Item n, x' j) = leftx' + x' c := by
      simpa [leftx'] using hsplit_candidate
    nlinarith [hcand.sum_x, hsum]
  let rightx : ℝ :=
    ∑ j : Item n, if c.val < j.val then x j else 0
  have hright_nonneg : 0 ≤ rightx := by
    unfold rightx
    refine Finset.sum_nonneg ?_
    intro j _hj
    by_cases hj : c.val < j.val
    · simp [hj, hx_nonneg j]
    · simp [hj]
  have hsplit_later :=
    problem6_sum_eq_left_part_add_pivot_add_right_part x c
  have hxc_le : x c ≤ 1 - leftx := by
    have hsum :
        (∑ j : Item n, x j) = leftx + x c + rightx := by
      simpa [leftx, rightx] using hsplit_later
    nlinarith [h.sum_x, hsum, hright_nonneg]
  have hx'_ge : 1 - leftx ≤ x' c := by
    nlinarith [hx'_pivot, hleft_le]
  have hcandidate_ge :
      q * (1 - leftx) ≤ q * x' c + (1 - q) * y' c := by
    have hq_part : q * (1 - leftx) ≤ q * x' c :=
      mul_le_mul_of_nonneg_left hx'_ge hqnonneg
    have hy_part : 0 ≤ (1 - q) * y' c :=
      mul_nonneg hqcomp_nonneg hy'_pivot_nonneg
    nlinarith
  have hlater_le : q * x c ≤ q * (1 - leftx) :=
    mul_le_mul_of_nonneg_left hxc_le hqnonneg
  nlinarith

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

private theorem problem6ClosedX_left_part_sum_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    (∑ j : Item n,
        if j.val < t.val then problem6ClosedX alpha v t j else 0) =
      problem6ClosedValue alpha v t * problem6LeftSum alpha v t := by
  unfold problem6LeftSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hj : j.val < t.val
  · simp [hj, problem6ClosedX_before alpha v hj, div_eq_mul_inv]
  · simp [hj]

private theorem problem6ClosedY_right_part_sum_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    (∑ j : Item n,
        if t.val < j.val then problem6ClosedY alpha v t j else 0) =
      problem6ClosedValue alpha v t * problem6RightSum alpha v t := by
  unfold problem6RightSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hj : t.val < j.val
  · simp [hj, problem6ClosedY_after alpha v hj, div_eq_mul_inv]
  · simp [hj]

/-- The closed-form `x_j` coordinates sum to one. -/
theorem problem6ClosedX_sum_eq_one {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, problem6ClosedX alpha v t j) = 1 := by
  have hsplit :=
    problem6_sum_eq_left_part_add_pivot_of_after_zero
      (problem6ClosedX alpha v t) t
      (fun {j} hj => problem6ClosedX_after alpha v hj)
  have hleft : (∑ j : Item n,
        if j.val < t.val then problem6ClosedX alpha v t j else 0) =
      problem6ClosedValue alpha v t * problem6LeftSum alpha v t :=
    problem6ClosedX_left_part_sum_eq
  rw [hsplit, hleft, problem6ClosedX_at]
  ring

/-- The closed-form `y_j` coordinates sum to one. -/
theorem problem6ClosedY_sum_eq_one {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, problem6ClosedY alpha v t j) = 1 := by
  have hsplit :=
    problem6_sum_eq_pivot_add_right_part_of_before_zero
      (problem6ClosedY alpha v t) t
      (fun {j} hj => problem6ClosedY_before alpha v hj)
  have hright : (∑ j : Item n,
        if t.val < j.val then problem6ClosedY alpha v t j else 0) =
      problem6ClosedValue alpha v t * problem6RightSum alpha v t :=
    problem6ClosedY_right_part_sum_eq
  rw [hsplit, hright, problem6ClosedY_at]
  ring

/-- The closed-form coordinates equalize every Problem 6 item constraint. -/
theorem problem6Closed_item_eq {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} (t j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j * problem6ClosedX alpha v t j +
        (1 - pairShare alpha v j) * problem6ClosedY alpha v t j =
      problem6ClosedValue alpha v t := by
  by_cases hlt : j.val < t.val
  · rw [problem6ClosedX_before alpha v hlt,
      problem6ClosedY_before alpha v hlt]
    have hqne : pairShare alpha v j ≠ 0 :=
      ne_of_gt (pairShare_pos j halpha0 halpha1 hpos)
    field_simp [hqne]
    ring
  · by_cases heq : j = t
    · subst j
      rw [problem6ClosedX_at, problem6ClosedY_at]
      have hmul :
          problem6ClosedValue alpha v t *
              problem6ClosedDenominator alpha v t = 1 := by
        unfold problem6ClosedValue
        field_simp [ne_of_gt
          (problem6ClosedDenominator_pos t halpha0 halpha1 hpos)]
      unfold problem6ClosedDenominator at hmul
      nlinarith
    · have hgt : t.val < j.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact heq (Fin.ext hval)
        omega
      rw [problem6ClosedX_after alpha v hgt,
        problem6ClosedY_after alpha v hgt]
      have hqne : 1 - pairShare alpha v j ≠ 0 :=
        ne_of_gt (one_sub_pairShare_pos j halpha0 halpha1 hpos)
      field_simp [hqne]
      ring

/--
The Lemma 5 closed-form coordinates satisfy the sparse, equalized real LP
shape for every pivot. Nonnegativity of the pivot coordinates is the remaining
condition needed to turn this real certificate into a probability policy.
-/
theorem problem6Closed_sparseEqualized {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    Problem6SparseEqualized alpha v t
      (problem6ClosedX alpha v t) (problem6ClosedY alpha v t)
      (problem6ClosedValue alpha v t) where
  item_eq := fun j => problem6Closed_item_eq t j halpha0 halpha1 hpos
  sum_x := problem6ClosedX_sum_eq_one alpha v t
  sum_y := problem6ClosedY_sum_eq_one alpha v t
  x_after_pivot_zero := fun {j} hj => problem6ClosedX_after alpha v hj
  y_before_pivot_zero := fun {j} hj => problem6ClosedY_before alpha v hj

/--
The only coordinate-level nonnegativity conditions not automatic from the
closed form: the two pivot masses.
-/
structure Problem6ClosedNonnegativePivots {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : Prop where
  x_pivot_nonneg : 0 ≤ problem6ClosedX alpha v t t
  y_pivot_nonneg : 0 ≤ problem6ClosedY alpha v t t

/--
A denominator-bound certificate implying the two closed-form pivot masses are
nonnegative.
-/
structure Problem6ClosedPivotDenominatorBounds {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : Prop where
  left_le_denominator :
    problem6LeftSum alpha v t ≤ problem6ClosedDenominator alpha v t
  right_le_denominator :
    problem6RightSum alpha v t ≤ problem6ClosedDenominator alpha v t

/--
Appendix D, Lemma 10 exact-center feasibility certificate: the closed-form
Lemma 5 midpoint construction has nonnegative pivot masses.
-/
theorem problem6ClosedPivotDenominatorBounds_half_center {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    Problem6ClosedPivotDenominatorBounds (1 / 2) v t := by
  have hsum :=
    problem6LeftSum_half_eq_rightSum_half_of_pivot_eq_reverse
      (v := v) (t := t) hpos hcenter
  have hden :=
    problem6ClosedDenominator_half_center_eq_one_add_leftSum
      (v := v) (t := t) hpos hcenter
  have hleft_nonneg :
      0 ≤ problem6LeftSum (1 / 2) v t :=
    problem6LeftSum_nonneg t (by norm_num) (by norm_num) hpos
  constructor
  · rw [hden]
    linarith
  · rw [← hsum, hden]
    linarith

/--
Appendix D, Lemma 10 even-center feasibility certificate: the midpoint
candidate immediately before its mirror has nonnegative closed-form pivot masses.
-/
theorem problem6ClosedPivotDenominatorBounds_half_succ_center {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    Problem6ClosedPivotDenominatorBounds (1 / 2) v t := by
  have hright :=
    problem6RightSum_half_eq_leftSum_half_add_inv_pairShare_of_pivot_succ_reverse
      (v := v) (t := t) hpos hsucc
  have hden :=
    problem6ClosedDenominator_half_succ_center_eq_rightSum
      (v := v) (t := t) hpos hsucc
  have hq_nonneg :
      0 ≤ (pairShare (1 / 2) v t)⁻¹ :=
    inv_nonneg.mpr
      (pairShare_pos t (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos).le
  constructor
  · rw [hden, hright]
    exact le_add_of_nonneg_right hq_nonneg
  · rw [hden]

/-- Denominator bounds imply nonnegative pivot coordinates. -/
theorem problem6ClosedNonnegativePivots_of_denominatorBounds {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    Problem6ClosedNonnegativePivots alpha v t := by
  have hDpos := problem6ClosedDenominator_pos t halpha0 halpha1 hpos
  constructor
  · rw [problem6ClosedX_at]
    rw [sub_nonneg]
    unfold problem6ClosedValue
    have hdiv :
        problem6LeftSum alpha v t /
            problem6ClosedDenominator alpha v t ≤ 1 := by
      rw [div_le_iff₀ hDpos]
      simpa using hbounds.left_le_denominator
    have heq :
        1 / problem6ClosedDenominator alpha v t *
            problem6LeftSum alpha v t =
          problem6LeftSum alpha v t /
            problem6ClosedDenominator alpha v t := by
      ring
    rw [heq]
    exact hdiv
  · rw [problem6ClosedY_at]
    rw [sub_nonneg]
    unfold problem6ClosedValue
    have hdiv :
        problem6RightSum alpha v t /
            problem6ClosedDenominator alpha v t ≤ 1 := by
      rw [div_le_iff₀ hDpos]
      simpa using hbounds.right_le_denominator
    have heq :
        1 / problem6ClosedDenominator alpha v t *
            problem6RightSum alpha v t =
          problem6RightSum alpha v t /
            problem6ClosedDenominator alpha v t := by
      ring
    rw [heq]
    exact hdiv

/-- Under pivot nonnegativity, all closed-form `x_j` coordinates are nonnegative. -/
theorem problem6ClosedX_nonneg {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (j : Item n) :
    0 ≤ problem6ClosedX alpha v t j := by
  by_cases hlt : j.val < t.val
  · rw [problem6ClosedX_before alpha v hlt]
    exact div_nonneg
      (problem6ClosedValue_pos t halpha0 halpha1 hpos).le
      (pairShare_pos j halpha0 halpha1 hpos).le
  · by_cases heq : j = t
    · subst j
      exact hpivot.x_pivot_nonneg
    · have hgt : t.val < j.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact heq (Fin.ext hval)
        omega
      rw [problem6ClosedX_after alpha v hgt]

/-- Under pivot nonnegativity, all closed-form `y_j` coordinates are nonnegative. -/
theorem problem6ClosedY_nonneg {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (j : Item n) :
    0 ≤ problem6ClosedY alpha v t j := by
  by_cases hlt : j.val < t.val
  · rw [problem6ClosedY_before alpha v hlt]
  · by_cases heq : j = t
    · subst j
      exact hpivot.y_pivot_nonneg
    · have hgt : t.val < j.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact heq (Fin.ext hval)
        omega
      rw [problem6ClosedY_after alpha v hgt]
      exact div_nonneg
        (problem6ClosedValue_pos t halpha0 halpha1 hpos).le
        (one_sub_pairShare_pos j halpha0 halpha1 hpos).le

/--
Appendix D, Lemma 10 comparison specialized to Lemma 5's closed form:
a closed-form pivot to the right of a nonnegative closed-form candidate cannot
have a larger `I^*_min` value.
-/
theorem problem6ClosedValue_le_of_closed_candidate_before {n : ℕ}
    {v : Item n → ℝ} {c t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hct : c.val < t.val)
    (hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t)
    (hcandidate : Problem6ClosedNonnegativePivots (1 / 2) v c) :
    problem6ClosedValue (1 / 2) v t ≤
      problem6ClosedValue (1 / 2) v c := by
  exact problem6SparseEqualized_value_le_of_candidate_before
    hpos hct
    (problem6Closed_sparseEqualized t
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos)
    (problem6Closed_sparseEqualized c
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos)
    (fun j =>
      problem6ClosedX_nonneg
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivot j)
    (problem6ClosedY_nonneg
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hcandidate c)

/--
Appendix D, Lemma 10 exact-center candidate comparison: any nonnegative
closed-form pivot strictly after an exact center candidate has value no larger
than that candidate.
-/
theorem problem6ClosedValue_le_of_center_candidate_before {n : ℕ}
    {v : Item n → ℝ} {c t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : c.val = (reverseItem c).val)
    (hct : c.val < t.val)
    (hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t) :
    problem6ClosedValue (1 / 2) v t ≤
      problem6ClosedValue (1 / 2) v c := by
  exact problem6ClosedValue_le_of_closed_candidate_before
    hpos hct hpivot
    (problem6ClosedNonnegativePivots_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos
      (problem6ClosedPivotDenominatorBounds_half_center
        (v := v) (t := c) hpos hcenter))

/--
Appendix D, Lemma 10 even-center candidate comparison: any nonnegative
closed-form pivot strictly after the candidate immediately before its mirror has
value no larger than that candidate.
-/
theorem problem6ClosedValue_le_of_succ_center_candidate_before {n : ℕ}
    {v : Item n → ℝ} {c t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hct : c.val < t.val)
    (hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t) :
    problem6ClosedValue (1 / 2) v t ≤
      problem6ClosedValue (1 / 2) v c := by
  exact problem6ClosedValue_le_of_closed_candidate_before
    hpos hct hpivot
    (problem6ClosedNonnegativePivots_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos
      (problem6ClosedPivotDenominatorBounds_half_succ_center
        (v := v) (t := c) hpos hsucc))

/-- Build a finite PMF from a nonnegative real vector with total mass one. -/
noncomputable def pmfOfRealVector {n : ℕ}
    (x : Item n → ℝ)
    (hnonneg : ∀ j : Item n, 0 ≤ x j)
    (hsum : (∑ j : Item n, x j) = 1) : PMF (Item n) :=
  PMF.ofFintype (fun j : Item n => ENNReal.ofReal (x j)) (by
    calc
      (∑ j : Item n, ENNReal.ofReal (x j))
          = ENNReal.ofReal (∑ j : Item n, x j) := by
            rw [← ENNReal.ofReal_sum_of_nonneg
              (s := Finset.univ) (f := x)]
            simp [hnonneg]
      _ = 1 := by
            simp [hsum])

@[simp] theorem pmfOfRealVector_apply_toReal {n : ℕ}
    (x : Item n → ℝ)
    (hnonneg : ∀ j : Item n, 0 ≤ x j)
    (hsum : (∑ j : Item n, x j) = 1)
    (j : Item n) :
    ((pmfOfRealVector x hnonneg hsum) j).toReal = x j := by
  unfold pmfOfRealVector
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (hnonneg j)

/-- The Problem 6 closed-form real solution as a two-type policy. -/
noncomputable def problem6ClosedPolicy {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypePolicy 2 n :=
  fun k =>
    if k = 0 then
      pmfOfRealVector (problem6ClosedX alpha v t)
        (problem6ClosedX_nonneg halpha0 halpha1 hpos hpivot)
        (problem6ClosedX_sum_eq_one alpha v t)
    else
      pmfOfRealVector (problem6ClosedY alpha v t)
        (problem6ClosedY_nonneg halpha0 halpha1 hpos hpivot)
        (problem6ClosedY_sum_eq_one alpha v t)

@[simp] theorem problem6ClosedPolicy_zero_toReal {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (j : Item n) :
    ((problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot 0) j).toReal =
      problem6ClosedX alpha v t j := by
  simp [problem6ClosedPolicy]

@[simp] theorem problem6ClosedPolicy_one_toReal {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (j : Item n) :
    ((problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot 1) j).toReal =
      problem6ClosedY alpha v t j := by
  simp [problem6ClosedPolicy]

/-- The closed-form policy satisfies Problem 6's LP epigraph constraints. -/
theorem problem6ClosedPolicy_feasible {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    problem6LPFeasible alpha v
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
      (problem6ClosedValue alpha v t) := by
  intro j
  rw [problem6ClosedPolicy_zero_toReal halpha0 halpha1 hpos hpivot,
    problem6ClosedPolicy_one_toReal halpha0 halpha1 hpos hpivot]
  exact le_of_eq (problem6Closed_item_eq t j halpha0 halpha1 hpos).symm

/--
Denominator bounds are enough to build a feasible closed-form Problem 6 policy.
-/
theorem problem6ClosedPolicy_feasible_of_denominatorBounds {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    problem6LPFeasible alpha v
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos
        (problem6ClosedNonnegativePivots_of_denominatorBounds
          halpha0 halpha1 hpos hbounds))
      (problem6ClosedValue alpha v t) := by
  exact problem6ClosedPolicy_feasible halpha0 halpha1 hpos
    (problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos hbounds)

/-- Raw type-0 utility of the closed-form Problem 6 policy. -/
noncomputable def problem6ClosedTypeZeroRawUtility {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  ∑ j : Item n, v j * problem6ClosedX alpha v t j

/-- Raw type-1 utility of the closed-form Problem 6 policy. -/
noncomputable def problem6ClosedTypeOneRawUtility {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  ∑ j : Item n, v (reverseItem j) * problem6ClosedY alpha v t j

/--
Mirror-reindexing form of the closed type-1 raw utility, matching the summation
used in Lemma 6.
-/
theorem problem6ClosedTypeOneRawUtility_eq_mirror_sum {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedTypeOneRawUtility alpha v t =
      ∑ j : Item n, v j * problem6ClosedY alpha v t (reverseItem j) := by
  unfold problem6ClosedTypeOneRawUtility
  simpa [reverseItem_reverseItem] using
    (sum_reverseItem
      (fun j : Item n => v j * problem6ClosedY alpha v t (reverseItem j)))

/-- Mirrored closed-form `y` coordinates still have total mass one. -/
theorem problem6ClosedY_reverse_sum_eq_one {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, problem6ClosedY alpha v t (reverseItem j)) = 1 := by
  rw [sum_reverseItem]
  exact problem6ClosedY_sum_eq_one alpha v t

/--
Appendix D, Lemma 6 summation identity: the raw utility gap is the weighted
sum of mirror-coordinate gaps.
-/
theorem problem6ClosedRawUtility_sub_eq_mirror_gap_sum {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedTypeZeroRawUtility alpha v t -
        problem6ClosedTypeOneRawUtility alpha v t =
      ∑ j : Item n,
        v j * (problem6ClosedX alpha v t j -
          problem6ClosedY alpha v t (reverseItem j)) := by
  unfold problem6ClosedTypeZeroRawUtility
  rw [problem6ClosedTypeOneRawUtility_eq_mirror_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  ring

/--
Appendix D, Lemma 6 coordinate dominance: for `α ≤ 1/2`, a pre-pivot
closed-form `x_j` coordinate dominates the mirrored `y_{n-j+1}` coordinate
whenever the mirror item lies after the pivot.
-/
theorem problem6ClosedX_sub_closedY_reverse_nonneg_of_alpha_le_half
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hj : j.val < t.val)
    (hrev : t.val < (reverseItem j).val) :
    0 ≤ problem6ClosedX alpha v t j -
      problem6ClosedY alpha v t (reverseItem j) := by
  rw [problem6ClosedX_before alpha v hj,
    problem6ClosedY_after alpha v hrev]
  have hcv : 0 ≤ problem6ClosedValue alpha v t :=
    (problem6ClosedValue_pos t halpha0 halpha1 hpos).le
  have hgap :
      0 ≤ (pairShare alpha v j)⁻¹ -
        (1 - pairShare alpha v (reverseItem j))⁻¹ :=
    pairShare_inv_sub_inv_one_sub_reverse_nonneg_of_alpha_le_half
      j halpha0 halpha1 halpha_half hpos
  have heq :
      problem6ClosedValue alpha v t / pairShare alpha v j -
          problem6ClosedValue alpha v t /
            (1 - pairShare alpha v (reverseItem j)) =
        problem6ClosedValue alpha v t *
          ((pairShare alpha v j)⁻¹ -
            (1 - pairShare alpha v (reverseItem j))⁻¹) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [heq]
  exact mul_nonneg hcv hgap

/--
Appendix D, Lemma 6 finite-sum comparison: if all mirror gaps up to the pivot
are nonnegative, and all mirrored `y` masses are nonnegative, then the closed
type-0 raw utility dominates the closed type-1 raw utility.
-/
theorem problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_left_gaps
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (hdec : StrictlyDecreasingByIndex v)
    (hleft :
      ∀ j : Item n, j.val ≤ t.val →
        0 ≤ problem6ClosedX alpha v t j -
          problem6ClosedY alpha v t (reverseItem j))
    (hy_nonneg :
      ∀ j : Item n, 0 ≤ problem6ClosedY alpha v t (reverseItem j)) :
    problem6ClosedTypeOneRawUtility alpha v t ≤
      problem6ClosedTypeZeroRawUtility alpha v t := by
  let gap : Item n → ℝ :=
    fun j => problem6ClosedX alpha v t j -
      problem6ClosedY alpha v t (reverseItem j)
  have hgap_sum : (∑ j : Item n, gap j) = 0 := by
    unfold gap
    rw [Finset.sum_sub_distrib]
    rw [problem6ClosedX_sum_eq_one, problem6ClosedY_reverse_sum_eq_one]
    ring
  have hterm :
      (∑ j : Item n, v t * gap j) ≤
        ∑ j : Item n, v j * gap j := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    by_cases hjle : j.val ≤ t.val
    · have hv : v t ≤ v j := by
        by_cases heq : j = t
        · subst j
          rfl
        · have hlt : j.val < t.val := by
            have hne_val : j.val ≠ t.val := by
              intro hval
              exact heq (Fin.ext hval)
            omega
          exact (hdec hlt).le
      exact mul_le_mul_of_nonneg_right hv (hleft j hjle)
    · have hgt : t.val < j.val := by omega
      have hv : v j ≤ v t := (hdec hgt).le
      have hgap_nonpos : gap j ≤ 0 := by
        unfold gap
        rw [problem6ClosedX_after alpha v hgt]
        linarith [hy_nonneg j]
      exact mul_le_mul_of_nonpos_right hv hgap_nonpos
  have hweighted_nonneg :
      0 ≤ ∑ j : Item n, v j * gap j := by
    have hconst :
        (∑ j : Item n, v t * gap j) = 0 := by
      rw [← Finset.mul_sum, hgap_sum, mul_zero]
    linarith
  have hraw :=
    problem6ClosedRawUtility_sub_eq_mirror_gap_sum alpha v t
  unfold gap at hweighted_nonneg
  linarith

/--
Appendix D, Lemma 6 comparison specialized to `α ≤ 1/2`: the scalar
mirror-gap algebra supplies all pre-pivot gaps; the pivot gap is left explicit.
-/
theorem problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_alpha_le_half
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hmirror :
      ∀ j : Item n, j.val < t.val → t.val < (reverseItem j).val)
    (hpivot_gap :
      0 ≤ problem6ClosedX alpha v t t -
        problem6ClosedY alpha v t (reverseItem t)) :
    problem6ClosedTypeOneRawUtility alpha v t ≤
      problem6ClosedTypeZeroRawUtility alpha v t := by
  refine problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_left_gaps
    hdec ?_ ?_
  · intro j hjle
    by_cases hj : j = t
    · subst j
      exact hpivot_gap
    · have hjlt : j.val < t.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact hj (Fin.ext hval)
        omega
      exact problem6ClosedX_sub_closedY_reverse_nonneg_of_alpha_le_half
        halpha0 halpha1 halpha_half hpos hjlt (hmirror j hjlt)
  · intro j
    exact problem6ClosedY_nonneg halpha0 halpha1 hpos hpivot (reverseItem j)

/-- Closed-form policy type-0 raw utility equals the closed `x` raw utility. -/
theorem problem6ClosedPolicy_rawTypeUtility_zero_eq {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypeWeightedRecommendationModel.rawTypeUtility
      (twoTypeReducedModel alpha v)
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 =
      problem6ClosedTypeZeroRawUtility alpha v t := by
  unfold TypeWeightedRecommendationModel.rawTypeUtility
    DecisionCore.Policy.agentScore DecisionCore.pmfExp
    problem6ClosedTypeZeroRawUtility
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [problem6ClosedPolicy_zero_toReal halpha0 halpha1 hpos hpivot]
  simp
  ring

/-- Closed-form policy type-1 raw utility equals the closed `y` raw utility. -/
theorem problem6ClosedPolicy_rawTypeUtility_one_eq {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypeWeightedRecommendationModel.rawTypeUtility
      (twoTypeReducedModel alpha v)
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 =
      problem6ClosedTypeOneRawUtility alpha v t := by
  unfold TypeWeightedRecommendationModel.rawTypeUtility
    DecisionCore.Policy.agentScore DecisionCore.pmfExp
    problem6ClosedTypeOneRawUtility
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [problem6ClosedPolicy_one_toReal halpha0 halpha1 hpos hpivot]
  simp
  ring

/--
Lemma 6 normalization bridge: once the raw closed-form utility of type `0`
dominates type `1` and their best-item normalizers coincide, the normalized
type utility comparison follows.
-/
theorem problem6ClosedPolicy_normalizedType_one_le_zero_of_raw
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hbest :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 1 =
        TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 0)
    (hbest_pos :
      0 < TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 0)
    (hraw :
      problem6ClosedTypeOneRawUtility alpha v t ≤
        problem6ClosedTypeZeroRawUtility alpha v t) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [problem6ClosedPolicy_rawTypeUtility_one_eq halpha0 halpha1 hpos hpivot,
    problem6ClosedPolicy_rawTypeUtility_zero_eq halpha0 halpha1 hpos hpivot,
    hbest]
  exact div_le_div_of_nonneg_right hraw hbest_pos.le

/--
Lemma 6 normalized-utility comparison under the remaining paper-specific
pivot-gap and center-position obligations.
-/
theorem problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hpivot_gap :
      0 ≤ problem6ClosedX alpha v t t -
        problem6ClosedY alpha v t (reverseItem t))
    (hbest :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 1 =
        TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 0)
    (hbest_pos :
      0 < TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 0) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  have hraw :
      problem6ClosedTypeOneRawUtility alpha v t ≤
        problem6ClosedTypeZeroRawUtility alpha v t :=
    problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_alpha_le_half
      halpha0 halpha1 halpha_half hpos hdec hpivot
      (fun j hj =>
        reverseItem_after_pivot_of_before_pivot_of_pivot_le_reverse
          hcenter hj)
      hpivot_gap
  exact problem6ClosedPolicy_normalizedType_one_le_zero_of_raw
    halpha0 halpha1 hpos hpivot hbest hbest_pos hraw

/--
Lemma 6 normalized-utility comparison under `α ≤ 1/2`, with the common
best-item denominator discharged by the opposing-preference model.
-/
theorem problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half_auto_best
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hpivot_gap :
      0 ≤ problem6ClosedX alpha v t t -
        problem6ClosedY alpha v t (reverseItem t)) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  exact problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half
    halpha0 halpha1 halpha_half hpos hdec hpivot hcenter hpivot_gap
    (twoTypeReducedModel_bestItemUtility_one_eq_zero alpha v)
    (twoTypeReducedModel_bestItemUtility_zero_pos alpha v hpos)

/-- In a two-type model, if type `1` is no better than type `0`, it is the minimum. -/
theorem twoType_typeFairness_eq_one_of_one_le_zero {n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel 2 n) (ρ : TypePolicy 2 n)
    (hle :
      TypeWeightedRecommendationModel.normalizedTypeUtility T ρ 1 ≤
        TypeWeightedRecommendationModel.normalizedTypeUtility T ρ 0) :
    TypeWeightedRecommendationModel.typeFairness T ρ =
      TypeWeightedRecommendationModel.normalizedTypeUtility T ρ 1 := by
  unfold TypeWeightedRecommendationModel.typeFairness DecisionCore.finiteMin
  apply le_antisymm
  · exact Finset.inf'_le
      (s := (Finset.univ : Finset (UserType 2)))
      (f := TypeWeightedRecommendationModel.normalizedTypeUtility T ρ)
      (by simp : (1 : UserType 2) ∈ Finset.univ)
  · apply Finset.le_inf'
    intro k _hk
    fin_cases k
    · exact hle
    · rfl

/--
Lemma 6 consequence: under the remaining pivot-gap and center-position
obligations, the closed policy's type fairness is exactly type `1`'s
normalized utility.
-/
theorem problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hpivot_gap :
      0 ≤ problem6ClosedX alpha v t t -
        problem6ClosedY alpha v t (reverseItem t)) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  exact twoType_typeFairness_eq_one_of_one_le_zero
    (twoTypeReducedModel alpha v)
    (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
    (problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half_auto_best
      halpha0 halpha1 halpha_half hpos hdec hpivot hcenter hpivot_gap)

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

/--
Closed-form certificate target for Problem 6: denominator bounds make the
closed coordinates a feasible policy, and the remaining field is the LP
upper-bound proof for the paper's proposed value.
-/
structure Problem6ClosedOptimalityCertificate {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : Prop where
  denominator_bounds : Problem6ClosedPivotDenominatorBounds alpha v t
  upper_bound :
    ∀ (ρ : TypePolicy 2 n) (ell' : ℝ),
      problem6LPFeasible alpha v ρ ell' →
        ell' ≤ problem6ClosedValue alpha v t

/--
A closed-form certificate supplies the generic `Problem6OptimalityCertificate`
for the value `problem6ClosedValue`.
-/
noncomputable def problem6OptimalityCertificate_of_closed {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (cert : Problem6ClosedOptimalityCertificate alpha v t) :
    Problem6OptimalityCertificate alpha v (problem6ClosedValue alpha v t) where
  policy :=
    problem6ClosedPolicy alpha v t halpha0 halpha1 hpos
      (problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds)
  feasible :=
    problem6ClosedPolicy_feasible_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  upper_bound := cert.upper_bound

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

/--
Closed-form Problem 6 optimal-value theorem: after the paper-specific
denominator and upper-bound certificate is supplied, the LP optimum is the
Lemma 5 closed value.
-/
theorem problem6LPOptimalValue_eq_closedValue_of_closed_certificate
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (cert : Problem6ClosedOptimalityCertificate alpha v t) :
    problem6LPOptimalValue alpha v = problem6ClosedValue alpha v t := by
  exact problem6LPOptimalValue_eq_of_certificate
    alpha v (problem6ClosedValue alpha v t) halpha0 halpha1 hpos
    (problem6OptimalityCertificate_of_closed halpha0 halpha1 hpos cert)

end OpposingTypes
end UserItemFairness
