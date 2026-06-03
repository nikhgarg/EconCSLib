import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.Field

namespace EconCSLib

/-!
# Two-Point Convex Combination Algebra

Reusable real-line algebra for paper arguments that compare one component to a
two-group weighted mixture.

## Main declarations

- `right_lt_weightedAverage_of_right_lt_left`
- `weighted_share_lt_weight_of_value_lt_total`
- `twoPointWeightedAverage`
- `lt_twoPointWeightedAverage_of_lt_components`
- `lt_twoPointWeightedAverage_of_weighted_gap_pos`
- `continuous_twoPointWeightedAverage`
-/

/--
The weighted average of two real components with arbitrary real weights.  Most
paper uses provide nonnegative weights and a positive denominator separately.
-/
noncomputable def twoPointWeightedAverage
    (weightLeft weightRight left right : ℝ) : ℝ :=
  (weightLeft * left + weightRight * right) / (weightLeft + weightRight)

/--
If the right endpoint is strictly below the left endpoint and the right weight
is less than one, then the two-point weighted average lies strictly above the
right endpoint.
-/
theorem right_lt_weightedAverage_of_right_lt_left
    {weightRight left right : ℝ}
    (hweight_lt_one : weightRight < 1)
    (hright_lt_left : right < left) :
    right < (1 - weightRight) * left + weightRight * right := by
  have hleft_weight_pos : 0 < 1 - weightRight := by
    linarith
  have hgap_pos : 0 < left - right := sub_pos.mpr hright_lt_left
  have hprod_pos : 0 < (1 - weightRight) * (left - right) :=
    mul_pos hleft_weight_pos hgap_pos
  nlinarith

/--
If a component value is strictly below the total and the component weight and
total are positive, then its normalized share is strictly below its weight.
-/
theorem weighted_share_lt_weight_of_value_lt_total
    {weight value total : ℝ}
    (hweight_pos : 0 < weight)
    (htotal_pos : 0 < total)
    (hvalue_lt_total : value < total) :
    weight * value / total < weight := by
  rw [div_lt_iff₀ htotal_pos]
  nlinarith [mul_pos hweight_pos (sub_pos.mpr hvalue_lt_total)]

/-- A positive left weight and nonnegative right weight give a positive sum. -/
theorem twoPointWeightedAverage_denominator_pos_of_left_pos_right_nonneg
    {weightLeft weightRight : ℝ}
    (hleft_pos : 0 < weightLeft) (hright_nonneg : 0 ≤ weightRight) :
    0 < weightLeft + weightRight := by
  linarith

/--
If both components are strictly above a target, with positive total weight and
nonnegative component weights, then their two-point weighted average is above
the target.
-/
theorem lt_twoPointWeightedAverage_of_lt_components
    {weightLeft weightRight left right target : ℝ}
    (hdenom_pos : 0 < weightLeft + weightRight)
    (hleft_weight_pos : 0 < weightLeft)
    (hright_weight_nonneg : 0 ≤ weightRight)
    (hleft : target < left)
    (hright : target < right) :
    target <
      twoPointWeightedAverage weightLeft weightRight left right := by
  have hnum :
      (weightLeft + weightRight) * target <
        weightLeft * left + weightRight * right := by
    have h0 : weightLeft * target < weightLeft * left :=
      mul_lt_mul_of_pos_left hleft hleft_weight_pos
    have h1 : weightRight * target ≤ weightRight * right :=
      mul_le_mul_of_nonneg_left hright.le hright_weight_nonneg
    nlinarith
  calc
    target = ((weightLeft + weightRight) * target) /
        (weightLeft + weightRight) := by
      rw [mul_div_cancel_left₀ target (ne_of_gt hdenom_pos)]
    _ < (weightLeft * left + weightRight * right) /
        (weightLeft + weightRight) :=
      div_lt_div_of_pos_right hnum hdenom_pos
    _ = twoPointWeightedAverage weightLeft weightRight left right := by
      rfl

/--
If both components are strictly below a target, with positive total weight and
nonnegative component weights, then their two-point weighted average is below
the target.
-/
theorem twoPointWeightedAverage_lt_of_components_lt
    {weightLeft weightRight left right target : ℝ}
    (hdenom_pos : 0 < weightLeft + weightRight)
    (hleft_weight_pos : 0 < weightLeft)
    (hright_weight_nonneg : 0 ≤ weightRight)
    (hleft : left < target)
    (hright : right < target) :
    twoPointWeightedAverage weightLeft weightRight left right <
      target := by
  have hnum :
      weightLeft * left + weightRight * right <
        (weightLeft + weightRight) * target := by
    have h0 : weightLeft * left < weightLeft * target :=
      mul_lt_mul_of_pos_left hleft hleft_weight_pos
    have h1 : weightRight * right ≤ weightRight * target :=
      mul_le_mul_of_nonneg_left hright.le hright_weight_nonneg
    nlinarith
  calc
    twoPointWeightedAverage weightLeft weightRight left right =
        (weightLeft * left + weightRight * right) /
          (weightLeft + weightRight) := by
      rfl
    _ < ((weightLeft + weightRight) * target) /
        (weightLeft + weightRight) :=
      div_lt_div_of_pos_right hnum hdenom_pos
    _ = target := by
      rw [mul_div_cancel_left₀ target (ne_of_gt hdenom_pos)]

/--
Weighted-gap form: if the weighted sum of component gaps above the target is
positive, then the weighted average is above the target.
-/
theorem lt_twoPointWeightedAverage_of_weighted_gap_pos
    {weightLeft weightRight left right target : ℝ}
    (hdenom_pos : 0 < weightLeft + weightRight)
    (hgap :
      0 <
        weightLeft * (left - target) +
          weightRight * (right - target)) :
    target <
      twoPointWeightedAverage weightLeft weightRight left right := by
  have hnum :
      (weightLeft + weightRight) * target <
        weightLeft * left + weightRight * right := by
    nlinarith
  calc
    target = ((weightLeft + weightRight) * target) /
        (weightLeft + weightRight) := by
      rw [mul_div_cancel_left₀ target (ne_of_gt hdenom_pos)]
    _ < (weightLeft * left + weightRight * right) /
        (weightLeft + weightRight) :=
      div_lt_div_of_pos_right hnum hdenom_pos
    _ = twoPointWeightedAverage weightLeft weightRight left right := by
      rfl

/--
Weighted-gap form: if the weighted sum of component gaps above the target is
negative, then the weighted average is below the target.
-/
theorem twoPointWeightedAverage_lt_of_weighted_gap_neg
    {weightLeft weightRight left right target : ℝ}
    (hdenom_pos : 0 < weightLeft + weightRight)
    (hgap :
      weightLeft * (left - target) +
          weightRight * (right - target) <
        0) :
    twoPointWeightedAverage weightLeft weightRight left right <
      target := by
  have hnum :
      weightLeft * left + weightRight * right <
        (weightLeft + weightRight) * target := by
    nlinarith
  calc
    twoPointWeightedAverage weightLeft weightRight left right =
        (weightLeft * left + weightRight * right) /
          (weightLeft + weightRight) := by
      rfl
    _ < ((weightLeft + weightRight) * target) /
        (weightLeft + weightRight) :=
      div_lt_div_of_pos_right hnum hdenom_pos
    _ = target := by
      rw [mul_div_cancel_left₀ target (ne_of_gt hdenom_pos)]

/-- Continuity of a two-point weighted average with nonzero denominator. -/
theorem continuous_twoPointWeightedAverage
    {α : Type*} [TopologicalSpace α]
    {weightLeft weightRight left right : α → ℝ}
    (hweightLeft : Continuous weightLeft)
    (hweightRight : Continuous weightRight)
    (hleft : Continuous left)
    (hright : Continuous right)
    (hdenom : ∀ x, weightLeft x + weightRight x ≠ 0) :
    Continuous (fun x : α =>
      twoPointWeightedAverage
        (weightLeft x) (weightRight x) (left x) (right x)) := by
  unfold twoPointWeightedAverage
  exact ((hweightLeft.mul hleft).add (hweightRight.mul hright)).div
    (hweightLeft.add hweightRight) hdenom

/--
For a positive constant `a`, the ratio `x / (a + x)` is strictly increasing on
nonnegative `x`.
-/
theorem div_const_add_lt_div_const_add
    {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hxy : x < y) :
    x / (a + x) < y / (a + y) := by
  have hdenx : 0 < a + x := by
    linarith
  have hdeny : 0 < a + y := by
    linarith
  rw [div_lt_div_iff₀ hdenx hdeny]
  nlinarith [mul_pos ha (sub_pos.mpr hxy)]

end EconCSLib
