import EconCSLib.Foundations.Math.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Topology
open scoped BigOperators

namespace EconCSLib
namespace Math

/-- A number in `(0,1)` is not an integer pole of `Gamma` after negation. -/
theorem gamma_neg_delta_ne_zero_of_pos_lt_one
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) :
    Real.Gamma (-δ) ≠ 0 := by
  refine Real.Gamma_ne_zero ?_
  intro m hm
  cases m with
  | zero =>
      norm_num at hm
      linarith
  | succ m =>
      have hm_ge_one : (1 : ℝ) ≤ (m.succ : ℝ) := by
        exact_mod_cast Nat.succ_pos m
      have hneg_le : -((m.succ : ℝ)) ≤ -1 := by linarith
      have hgt : -1 < -δ := by linarith
      linarith

/--
Finite gamma recurrence product for a shift `-δ` with `0 < δ < 1`.

This rewrites Euler's `GammaSeq (-δ)` product into the gamma-ratio form often
needed for fixed-rank order-statistic tails.
-/
theorem gamma_neg_delta_prod_range_eq_gamma_div
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (q : ℕ) :
    (∏ j ∈ Finset.range (q + 1), (-δ + (j : ℝ))) =
      Real.Gamma ((q : ℝ) + 1 - δ) / Real.Gamma (-δ) := by
  have hG_ne : Real.Gamma (-δ) ≠ 0 :=
    gamma_neg_delta_ne_zero_of_pos_lt_one hδ_pos hδ_lt_one
  induction q with
  | zero =>
      have hδ_ne : -δ ≠ 0 := by linarith
      rw [Finset.prod_range_one, Nat.cast_zero, add_zero, zero_add,
        show (1 : ℝ) - δ = -δ + 1 by ring]
      rw [Real.Gamma_add_one hδ_ne]
      field_simp [hG_ne]
  | succ q ih =>
      rw [Finset.prod_range_succ, ih]
      rw [show -δ + (((q + 1 : ℕ) : ℝ)) = (q : ℝ) + 1 - δ by
        rw [Nat.cast_add, Nat.cast_one]
        ring]
      have harg_pos : 0 < (q : ℝ) + 1 - δ := by
        have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
        linarith
      have harg_ne : (q : ℝ) + 1 - δ ≠ 0 := ne_of_gt harg_pos
      rw [show ((q.succ : ℕ) : ℝ) + 1 - δ =
            ((q : ℝ) + 1 - δ) + 1 by
              rw [Nat.cast_succ]
              ring,
        Real.Gamma_add_one harg_ne]
      field_simp [hG_ne]

/-- Gamma-ratio asymptotic: `Γ(q+1) / Γ(q+1-δ) ~ q^δ`. -/
theorem gamma_ratio_nat_add_one_sub_asymptoticEquivalent
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) :
    AsymptoticEquivalent
      (fun q : ℕ =>
        Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((q : ℝ) + 1 - δ))
      (fun q : ℕ => (q : ℝ) ^ δ) := by
  rw [AsymptoticEquivalent]
  have hG_ne : Real.Gamma (-δ) ≠ 0 :=
    gamma_neg_delta_ne_zero_of_pos_lt_one hδ_pos hδ_lt_one
  have hseq :
      Filter.Tendsto
        (fun q : ℕ => Real.GammaSeq (-δ) q / Real.Gamma (-δ))
        Filter.atTop (nhds 1) := by
    have h := (Real.GammaSeq_tendsto_Gamma (-δ)).div_const (Real.Gamma (-δ))
    simpa [hG_ne] using h
  refine Filter.Tendsto.congr' ?_ hseq
  filter_upwards [Filter.eventually_gt_atTop 0] with q hq
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq_nonneg : 0 ≤ (q : ℝ) := le_of_lt hq_pos
  have hqpow_ne : (q : ℝ) ^ δ ≠ 0 :=
    (Real.rpow_pos_of_pos hq_pos δ).ne'
  have hqdelta_neg : (q : ℝ) ^ (-δ) = ((q : ℝ) ^ δ)⁻¹ := by
    exact Real.rpow_neg hq_nonneg δ
  have hden_pos : 0 < (q : ℝ) + 1 - δ := by
    linarith
  have hden_gamma_ne : Real.Gamma ((q : ℝ) + 1 - δ) ≠ 0 :=
    (Real.Gamma_pos_of_pos hden_pos).ne'
  rw [Real.GammaSeq, gamma_neg_delta_prod_range_eq_gamma_div hδ_pos hδ_lt_one q,
    ← Real.Gamma_nat_eq_factorial q, hqdelta_neg]
  field_simp [hG_ne, hden_gamma_ne, hqpow_ne]

/--
Finite-difference bridge from a value asymptotic and an explicit scaled-drop
limit.

If `value q ~ C*q^δ` and
`(q+1) * (value (q+1)-value q) / value q -> δ`, then the finite difference has
the natural scale `(q+1)^(-(1-δ))` and limit `C*δ`.
-/
theorem scaled_difference_limit_of_value_asymptotic_and_scaled_drop
    {value : ℕ → ℝ} {δ C : ℝ}
    (hC_ne : C ≠ 0)
    (hvalue :
      AsymptoticEquivalent
        value
        (fun q : ℕ => C * ((q : ℝ) ^ δ)))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) * ((value (q + 1) - value q) / value q)))
        Filter.atTop (nhds δ)) :
    Filter.Tendsto
      (fun q : ℕ =>
        (value (q + 1) - value q) /
          (((q + 1 : ℕ) : ℝ) ^ (-(1 - δ))))
      Filter.atTop (nhds (C * δ)) := by
  rw [AsymptoticEquivalent] at hvalue
  have hscale :
      Filter.Tendsto
        (fun q : ℕ =>
          ((q : ℝ) ^ δ) /
            (((q + 1 : ℕ) : ℝ) *
              (((q + 1 : ℕ) : ℝ) ^ (-(1 - δ)))))
        Filter.atTop (nhds 1) := by
    have hratio :
        Filter.Tendsto
          (fun q : ℕ => (q : ℝ) / (((q + 1 : ℕ) : ℝ)))
          Filter.atTop (nhds 1) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (1 : ℝ))
    have hrpow :
        Filter.Tendsto
          (fun q : ℕ => (((q : ℝ) / (((q + 1 : ℕ) : ℝ))) ^ δ))
          Filter.atTop (nhds 1) := by
      have h := hratio.rpow_const (p := δ)
        (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
      simpa using h
    refine Filter.Tendsto.congr' ?_ hrpow
    filter_upwards [Filter.eventually_gt_atTop 0] with q hq
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    have hq_succ_pos : 0 < (((q + 1 : ℕ) : ℝ)) := by positivity
    have hq_succ_nonneg : 0 ≤ (((q + 1 : ℕ) : ℝ)) := le_of_lt hq_succ_pos
    have hden_eq :
        (((q + 1 : ℕ) : ℝ) *
          (((q + 1 : ℕ) : ℝ) ^ (-(1 - δ)))) =
          (((q + 1 : ℕ) : ℝ) ^ δ) := by
      nth_rewrite 1 [← Real.rpow_one (((q + 1 : ℕ) : ℝ))]
      rw [← Real.rpow_add hq_succ_pos]
      ring_nf
    rw [hden_eq]
    rw [Real.div_rpow hq_nonneg hq_succ_nonneg]
  have hprod :
      Filter.Tendsto
        (fun q : ℕ =>
          ((((q + 1 : ℕ) : ℝ) *
              ((value (q + 1) - value q) / value q)) *
            (value q / (C * ((q : ℝ) ^ δ)))) *
            (C *
              (((q : ℝ) ^ δ) /
                (((q + 1 : ℕ) : ℝ) *
                  (((q + 1 : ℕ) : ℝ) ^ (-(1 - δ)))))))
        Filter.atTop (nhds (C * δ)) := by
    have h := (hdrop.mul hvalue).mul (hscale.const_mul C)
    simpa [mul_assoc, one_mul, mul_comm, mul_left_comm, mul_right_comm] using h
  have hvalue_ne_eventually : ∀ᶠ q in Filter.atTop, value q ≠ 0 := by
    filter_upwards
      [hvalue.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with q hratio_ne
    intro hzero
    rw [hzero] at hratio_ne
    simp at hratio_ne
  refine Filter.Tendsto.congr' ?_ hprod
  filter_upwards
    [hvalue_ne_eventually, Filter.eventually_gt_atTop 0] with q hvalue_ne hq
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqpow_ne : ((q : ℝ) ^ δ) ≠ 0 :=
    (Real.rpow_pos_of_pos hq_pos δ).ne'
  have hq_succ_pos : 0 < (((q + 1 : ℕ) : ℝ)) := by positivity
  have hscale_ne : (((q + 1 : ℕ) : ℝ) ^ (-(1 - δ))) ≠ 0 :=
    (Real.rpow_pos_of_pos hq_succ_pos (-(1 - δ))).ne'
  have hq_succ_ne : (((q + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hq_succ_pos
  field_simp [hvalue_ne, hqpow_ne, hq_succ_ne, hscale_ne, hC_ne]

end Math
end EconCSLib
