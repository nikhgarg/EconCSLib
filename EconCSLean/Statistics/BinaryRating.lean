import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace EconCSLean
namespace Statistics

/-!
# Binary Prior-Weighted Rating Algebra

Reusable algebra for binary-review Bayesian/prior-weighted rating systems.
-/

/--
Variance term for the prior-weighted posterior mean estimator in the fixed
binary-rating model.

The parameters are real-valued here to keep this lemma reusable for paper
wrappers. In paper notation, `alpha` and `beta` are prior-shape parameters,
`eta` is prior strength, `t` is the number of reviews, and `q` is true quality.
-/
noncomputable def priorWeightedVariance
    (alpha beta eta t q : ℝ) : ℝ :=
  t * q * (1 - q) / (eta * alpha + eta * beta + t) ^ 2

@[simp] theorem priorWeightedVariance_quality_zero
    (alpha beta eta t : ℝ) :
    priorWeightedVariance alpha beta eta t 0 = 0 := by
  simp [priorWeightedVariance]

@[simp] theorem priorWeightedVariance_quality_one
    (alpha beta eta t : ℝ) :
    priorWeightedVariance alpha beta eta t 1 = 0 := by
  simp [priorWeightedVariance]

/--
At boundary quality `q = 0`, the variance term cannot be strictly decreasing in
prior strength, since it is identically zero.
-/
theorem not_strictly_decreasing_priorWeightedVariance_quality_zero
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ priorWeightedVariance alpha beta etaHigh t 0 <
      priorWeightedVariance alpha beta etaLow t 0 := by
  simp

/--
At boundary quality `q = 1`, the variance term cannot be strictly decreasing in
prior strength, since it is identically zero.
-/
theorem not_strictly_decreasing_priorWeightedVariance_quality_one
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ priorWeightedVariance alpha beta etaHigh t 1 <
      priorWeightedVariance alpha beta etaLow t 1 := by
  simp

/--
Interior-quality corrected strict variance decrease for the fixed binary-rating
model.

If prior shape has positive total mass, the number of reviews is positive, and
true quality is not at a Bernoulli boundary, then increasing prior strength
strictly decreases the variance term from Theorem 3.1.
-/
theorem priorWeightedVariance_strict_decrease_of_interior_quality
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hq0 : 0 < q)
    (hq1 : q < 1)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_lt : etaLow < etaHigh) :
    priorWeightedVariance alpha beta etaHigh t q <
      priorWeightedVariance alpha beta etaLow t q := by
  have hq_gap : 0 < 1 - q := sub_pos.mpr hq1
  have hnum_pos : 0 < t * q * (1 - q) := by
    exact mul_pos (mul_pos ht hq0) hq_gap
  have hden_low_pos : 0 < etaLow * alpha + etaLow * beta + t := by
    calc
      0 < etaLow * (alpha + beta) + t :=
        add_pos_of_nonneg_of_pos
          (mul_nonneg hetaLow_nonneg hshape.le) ht
      _ = etaLow * alpha + etaLow * beta + t := by ring
  have hden_lt :
      etaLow * alpha + etaLow * beta + t <
        etaHigh * alpha + etaHigh * beta + t := by
    calc
      etaLow * alpha + etaLow * beta + t
          = etaLow * (alpha + beta) + t := by ring
      _ < etaHigh * (alpha + beta) + t := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_lt_add_right
              (mul_lt_mul_of_pos_right heta_lt hshape) t
      _ = etaHigh * alpha + etaHigh * beta + t := by ring
  have hsq_lt :
      (etaLow * alpha + etaLow * beta + t) ^ 2 <
        (etaHigh * alpha + etaHigh * beta + t) ^ 2 :=
    pow_lt_pow_left₀ hden_lt hden_low_pos.le (by decide : (2 : ℕ) ≠ 0)
  unfold priorWeightedVariance
  exact div_lt_div_of_pos_left hnum_pos
    (sq_pos_of_pos hden_low_pos) hsq_lt

end Statistics
end EconCSLean
