import Mathlib.Data.Real.Basic

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

end Statistics
end EconCSLean
