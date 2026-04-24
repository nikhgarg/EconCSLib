import ProducerFairness.MainTheorems

/-!
# Paper-Facing Theorem Ledger: Bayesian Rating Fairness

This file is the single-file Lean audit surface for the ICWSM 2025
*Balancing Producer Fairness and Efficiency via Bayesian Rating System Design*
formalization. The declarations are ordered to match paper presentation:

1. fixed binary-rating model definitions,
2. Theorem 3.1 claims,
3. Theorem 3.2 claims,
4. boundary caveats.

If this file typechecks and the commented statements match your paper notes, the
folder has a consistent paper-facing proof surface.
-/

namespace ProducerFairness

/-! ## 1) Binary-rating model primitives - -/

noncomputable abbrev priorWeightedPosteriorMean :=
  EconCSLean.Statistics.priorWeightedPosteriorMean
noncomputable abbrev priorWeightedBias :=
  EconCSLean.Statistics.priorWeightedBias
noncomputable abbrev priorWeightedVariance :=
  EconCSLean.Statistics.priorWeightedVariance
noncomputable abbrev priorWeightedSquaredBias :=
  EconCSLean.Statistics.priorWeightedSquaredBias

abbrev JensenConvex := EconCSLean.Statistics.JensenConvex
abbrev JensenConcave := EconCSLean.Statistics.JensenConcave
abbrev GlobalMinAt := EconCSLean.Statistics.GlobalMinAt
abbrev GlobalMaxAt := EconCSLean.Statistics.GlobalMaxAt

/-! ## 2) Theorem 3.1 statements -/

/--
Theorem 3.1, variance weakly decreases in prior strength:
for full quality interval `0 ≤ q_v ≤ 1`, if prior strength increases the
posterior-mean variance is nonincreasing.
-/
theorem paper_facing_theorem3_1_variance_weak_decrease
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_le : etaLow ≤ etaHigh) :
    EconCSLean.Statistics.priorWeightedVariance alpha beta etaHigh t q ≤
      EconCSLean.Statistics.priorWeightedVariance alpha beta etaLow t q := by
  exact paper_theorem3_1_variance_weak_decrease
    hshape ht hq0 hq1 hetaLow_nonneg heta_le

/--
Theorem 3.1, strict decrease on interior quality values.
For `0 < q_v < 1`, positive prior-shape mass, positive number of prior samples,
and stronger prior strength `η_high > η_low`, variance is strictly decreasing.
-/
theorem paper_facing_theorem3_1_variance_strict_decrease_interior
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hq0 : 0 < q)
    (hq1 : q < 1)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_lt : etaLow < etaHigh) :
    EconCSLean.Statistics.priorWeightedVariance alpha beta etaHigh t q <
      EconCSLean.Statistics.priorWeightedVariance alpha beta etaLow t q := by
  exact paper_theorem3_1_variance_strict_decrease_interior
    hshape ht hq0 hq1 hetaLow_nonneg heta_lt

/--
Theorem 3.1, squared posterior-mean bias is nondecreasing in prior strength.
With stronger prior (`η_high ≥ η_low`) and basic nonnegativity assumptions,
the squared bias term does not decrease.
-/
theorem paper_facing_theorem3_1_squared_bias_nondecreasing
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_le : etaLow ≤ etaHigh) :
    EconCSLean.Statistics.priorWeightedSquaredBias alpha beta etaLow t q ≤
      EconCSLean.Statistics.priorWeightedSquaredBias alpha beta etaHigh t q := by
  exact paper_theorem3_1_squared_bias_nondecreasing
    hshape ht hetaLow_nonneg heta_le

/-! ## 3) Theorem 3.2 statements -/

/--
Theorem 3.2, squared-bias Jensen convexity in true quality.
The squared bias is Jensen-convex as a function of quality.
-/
theorem paper_facing_theorem3_2_squared_bias_convex_in_quality
    {alpha beta eta t : ℝ}
    (hden : eta * alpha + eta * beta + t ≠ 0) :
    EconCSLean.Statistics.JensenConvex
      (fun q => EconCSLean.Statistics.priorWeightedSquaredBias
        alpha beta eta t q) := by
  exact paper_theorem3_2_squared_bias_convex_in_quality hden

/--
Theorem 3.2, squared-bias global minimizer.
On the full quality interval, squared bias is minimized at the prior mean
`alpha / (alpha + beta)` under positive shape mass and positive sample weight.
-/
theorem paper_facing_theorem3_2_squared_bias_global_min_at_prior_mean
    {alpha beta eta t : ℝ}
    (hshape : 0 < alpha + beta)
    (heta_nonneg : 0 ≤ eta)
    (ht : 0 < t) :
    EconCSLean.Statistics.GlobalMinAt
      (fun q => EconCSLean.Statistics.priorWeightedSquaredBias
        alpha beta eta t q)
      (alpha / (alpha + beta)) := by
  exact paper_theorem3_2_squared_bias_global_min_at_prior_mean
    hshape heta_nonneg ht

/--
Theorem 3.2, posterior-mean variance Jensen concavity in true quality.
This holds when the prior-weighted sample mass is nonnegative (`t ≥ 0`).
-/
theorem paper_facing_theorem3_2_variance_concave_in_quality
    {alpha beta eta t : ℝ}
    (ht : 0 ≤ t) :
    EconCSLean.Statistics.JensenConcave
      (fun q => EconCSLean.Statistics.priorWeightedVariance
        alpha beta eta t q) := by
  exact paper_theorem3_2_variance_concave_in_quality ht

/--
Theorem 3.2, posterior-mean variance global maximum at `q = 1/2`.
For nonnegative prior-weighted sample mass, variance is globally maximized at
`q_v = 1/2`.
-/
theorem paper_facing_theorem3_2_variance_global_max_at_half
    {alpha beta eta t : ℝ}
    (ht : 0 ≤ t) :
    EconCSLean.Statistics.GlobalMaxAt
      (fun q => EconCSLean.Statistics.priorWeightedVariance
        alpha beta eta t q)
      (1 / 2) := by
  exact paper_theorem3_2_variance_global_max_at_half ht

/-! ## 4) Boundary caveats -/

/--
Boundary caution for Theorem 3.1 strict decrease:
at `q_v = 0`, posterior-mean variance is identically zero for any prior strength,
so strict decrease cannot hold unconditionally.
-/
theorem paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_zero
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ EconCSLean.Statistics.priorWeightedVariance alpha beta etaHigh t 0 <
      EconCSLean.Statistics.priorWeightedVariance alpha beta etaLow t 0 := by
  exact paper_theorem3_1_variance_strict_decrease_counterexample_quality_zero
    alpha beta t etaLow etaHigh

/--
Boundary caution for Theorem 3.1 strict decrease:
at `q_v = 1`, posterior-mean variance is identically zero for any prior strength,
so strict decrease cannot hold unconditionally.
-/
theorem paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_one
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ EconCSLean.Statistics.priorWeightedVariance alpha beta etaHigh t 1 <
      EconCSLean.Statistics.priorWeightedVariance alpha beta etaLow t 1 := by
  exact paper_theorem3_1_variance_strict_decrease_counterexample_quality_one
    alpha beta t etaLow etaHigh

end ProducerFairness
