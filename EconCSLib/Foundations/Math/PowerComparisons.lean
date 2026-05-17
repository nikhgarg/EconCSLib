import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace EconCSLib
namespace Math

/-!
# Power Comparison Lemmas

Reusable algebraic comparisons for objectives whose marginal terms are
negative powers.

## Main declarations

- `rpow_neg_marginal_lt_of_scaled_lt`: a scaled-count inequality implies the
  corresponding strict comparison between negative-power weighted marginals.
-/

/--
If `y / p_dst^(1/eta) < x / p_src^(1/eta)`, then the weighted negative-power
marginal at `x` is smaller than the destination marginal at `y`.

This is the algebraic core behind power-law first-order conditions.
-/
theorem rpow_neg_marginal_lt_of_scaled_lt
    {p_src p_dst c eta x y : ℝ}
    (hp_src : 0 < p_src) (hp_dst : 0 < p_dst) (hc : 0 < c)
    (heta : 0 < eta) (hx : 0 < x) (hy : 0 < y)
    (hscaled : y / p_dst ^ (1 / eta) < x / p_src ^ (1 / eta)) :
    p_src * (c * x ^ (-eta)) < p_dst * (c * y ^ (-eta)) := by
  let wsrc : ℝ := p_src ^ (1 / eta)
  let wdst : ℝ := p_dst ^ (1 / eta)
  have hwsrc_pos : 0 < wsrc := by
    dsimp [wsrc]
    exact Real.rpow_pos_of_pos hp_src (1 / eta)
  have hwdst_pos : 0 < wdst := by
    dsimp [wdst]
    exact Real.rpow_pos_of_pos hp_dst (1 / eta)
  have hleft_pos : 0 < y / wdst := div_pos hy hwdst_pos
  have hright_pos : 0 < x / wsrc := div_pos hx hwsrc_pos
  have hpow_lt :
      (y / wdst) ^ eta < (x / wsrc) ^ eta :=
    Real.rpow_lt_rpow (le_of_lt hleft_pos)
      (by simpa [wsrc, wdst] using hscaled) heta
  have hsrc_pow :
      (x / wsrc) ^ eta = x ^ eta / p_src := by
    dsimp [wsrc]
    rw [Real.div_rpow (le_of_lt hx) (le_of_lt hwsrc_pos) eta]
    rw [← Real.rpow_mul (le_of_lt hp_src) (1 / eta) eta]
    have hmul : (1 / eta) * eta = 1 := by field_simp [ne_of_gt heta]
    rw [hmul, Real.rpow_one]
  have hdst_pow :
      (y / wdst) ^ eta = y ^ eta / p_dst := by
    dsimp [wdst]
    rw [Real.div_rpow (le_of_lt hy) (le_of_lt hwdst_pos) eta]
    rw [← Real.rpow_mul (le_of_lt hp_dst) (1 / eta) eta]
    have hmul : (1 / eta) * eta = 1 := by field_simp [ne_of_gt heta]
    rw [hmul, Real.rpow_one]
  have hpow_ratio_lt :
      y ^ eta / p_dst < x ^ eta / p_src := by
    simpa [hsrc_pow, hdst_pow] using hpow_lt
  have hxpow_pos : 0 < x ^ eta := Real.rpow_pos_of_pos hx eta
  have hypow_pos : 0 < y ^ eta := Real.rpow_pos_of_pos hy eta
  have hscaled_marginal :
      p_src * x ^ (-eta) < p_dst * y ^ (-eta) := by
    have hinv_lt :
        1 / (x ^ eta / p_src) < 1 / (y ^ eta / p_dst) :=
      one_div_lt_one_div_of_lt (div_pos hypow_pos hp_dst) hpow_ratio_lt
    have hleft :
        1 / (x ^ eta / p_src) = p_src / x ^ eta := by
      field_simp [ne_of_gt hp_src, ne_of_gt hxpow_pos]
    have hright :
        1 / (y ^ eta / p_dst) = p_dst / y ^ eta := by
      field_simp [ne_of_gt hp_dst, ne_of_gt hypow_pos]
    calc
      p_src * x ^ (-eta) = p_src / x ^ eta := by
        rw [Real.rpow_neg (le_of_lt hx)]
        ring
      _ = 1 / (x ^ eta / p_src) := by rw [hleft]
      _ < 1 / (y ^ eta / p_dst) := hinv_lt
      _ = p_dst / y ^ eta := hright
      _ = p_dst * y ^ (-eta) := by
        rw [Real.rpow_neg (le_of_lt hy)]
        ring
  nlinarith [mul_lt_mul_of_pos_right hscaled_marginal hc]

end Math
end EconCSLib
