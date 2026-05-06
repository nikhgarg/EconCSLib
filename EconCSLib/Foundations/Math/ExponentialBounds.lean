import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Elementary Exponential Bounds

Reusable real exponential inequalities for finite probability estimates.

## Main declarations

- `exp_neg_two_div_le_one_sub_inv_of_two_le`: for `x >= 2`,
  `exp(-(2/x)) <= 1 - 1/x`.
- `exp_neg_two_mul_nat_div_le_one_sub_inv_pow_of_two_le`: the corresponding
  finite-power lower bound.
-/

namespace EconCSLib
namespace Math

/--
For any real denominator at least two, the elementary logarithmic estimate
`log(1 - 1/x) >= -2/x` gives `exp(-2/x) <= 1 - 1/x`.
-/
theorem exp_neg_two_div_le_one_sub_inv_of_two_le
    {x : ℝ} (hx : 2 ≤ x) :
    Real.exp (-(2 / x)) ≤ 1 - 1 / x := by
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxm1_pos : 0 < x - 1 := by linarith
  have hy_pos : 0 < 1 - 1 / x := by
    rw [sub_pos]
    rw [div_lt_one hx_pos]
    linarith
  have hrepr :
      1 - 1 / x = (1 + 1 / (x - 1))⁻¹ := by
    field_simp [ne_of_gt hx_pos, ne_of_gt hxm1_pos]
    ring
  have hlog_upper :
      Real.log (1 + 1 / (x - 1)) ≤ 2 / x := by
    have harg_pos : 0 < 1 + 1 / (x - 1) := by positivity
    have hlog_le :
        Real.log (1 + 1 / (x - 1)) ≤
          (1 + 1 / (x - 1)) - 1 :=
      Real.log_le_sub_one_of_pos harg_pos
    have hfrac : 1 / (x - 1) ≤ 2 / x := by
      rw [div_le_div_iff₀ hxm1_pos hx_pos]
      nlinarith
    linarith
  have hlog_lower :
      -(2 / x) ≤ Real.log (1 - 1 / x) := by
    rw [hrepr, Real.log_inv]
    exact neg_le_neg hlog_upper
  exact (Real.le_log_iff_exp_le hy_pos).mp hlog_lower

/--
Finite-power form of `exp_neg_two_div_le_one_sub_inv_of_two_le`: if `x >= 2`,
then `exp(-(2N/x)) <= (1 - 1/x)^N`.
-/
theorem exp_neg_two_mul_nat_div_le_one_sub_inv_pow_of_two_le
    (N : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    Real.exp (-(2 * (N : ℝ) / x)) ≤ (1 - 1 / x) ^ N := by
  have hbase := exp_neg_two_div_le_one_sub_inv_of_two_le (x := x) hx
  have hpow :
      (Real.exp (-(2 / x))) ^ N ≤ (1 - 1 / x) ^ N :=
    pow_le_pow_left₀ (Real.exp_pos _).le hbase N
  have hleft :
      Real.exp (-(2 * (N : ℝ) / x)) =
        (Real.exp (-(2 / x))) ^ N := by
    calc
      Real.exp (-(2 * (N : ℝ) / x)) =
          Real.exp ((N : ℝ) * (-(2 / x))) := by
            congr 1
            ring
      _ = (Real.exp (-(2 / x))) ^ N :=
          Real.exp_nat_mul (-(2 / x)) N
  simpa [hleft] using hpow

end Math
end EconCSLib
