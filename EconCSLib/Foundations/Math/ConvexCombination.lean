import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace EconCSLib

/-!
# Two-Point Convex Combination Algebra

Reusable real-line algebra for paper arguments that compare one component to a
two-group weighted mixture.

## Main declarations

- `right_lt_weightedAverage_of_right_lt_left`
- `weighted_share_lt_weight_of_value_lt_total`
-/

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

end EconCSLib
