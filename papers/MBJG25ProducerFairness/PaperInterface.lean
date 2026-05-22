import MBJG25ProducerFairness.MainTheorems
import MBJG25ProducerFairness.ResponsiveMarket
import EconCSLib.Learning.Bandits.ThompsonSampling
import EconCSLib.Algorithms.Online.Regret

/-!
# Paper Interface: Bayesian Rating Fairness

This file is the single-file human-facing Lean interface for the ICWSM 2025
*Balancing Producer Fairness and Efficiency via Bayesian Rating System Design*
formalization. The declarations are ordered to match paper presentation:

1. fixed binary-rating model definitions,
2. Theorem 3.1 claims,
3. Theorem 3.2 claims,
4. boundary caveats.

If this file typechecks and the commented statements match your paper notes, the
folder has a consistent paper-facing proof surface.
-/

namespace MBJG25ProducerFairness

/-! ## 1) Binary-rating model primitives - -/

/-- The posterior mean estimated quality in the fixed binary rating model.
    Paper Definition: $\frac{\eta \alpha + t q_v}{\eta (\alpha + \beta) + t}$
-/
noncomputable def paper_posterior_mean (alpha beta eta t q_v : ℝ) : ℝ :=
  (eta * alpha + t * q_v) / (eta * alpha + eta * beta + t)

/-- The bias of the estimated quality.
    Paper Definition: $E[\hat{q}_v] - q_v$
-/
noncomputable def paper_bias (alpha beta eta t q_v : ℝ) : ℝ :=
  paper_posterior_mean alpha beta eta t q_v - q_v

/-- The variance of the estimated quality.
    Paper Definition: $\frac{t q_v (1 - q_v)}{(\eta (\alpha + \beta) + t)^2}$
-/
noncomputable def paper_variance (alpha beta eta t q_v : ℝ) : ℝ :=
  t * q_v * (1 - q_v) / (eta * alpha + eta * beta + t) ^ 2

/-- The squared bias of the estimated quality.
    Paper Definition: $(E[\hat{q}_v] - q_v)^2$
-/
noncomputable def paper_squared_bias (alpha beta eta t q_v : ℝ) : ℝ :=
  (paper_bias alpha beta eta t q_v) ^ 2

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
    EconCSLib.Statistics.priorWeightedVariance alpha beta etaHigh t q ≤
      EconCSLib.Statistics.priorWeightedVariance alpha beta etaLow t q := by
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
    EconCSLib.Statistics.priorWeightedVariance alpha beta etaHigh t q <
      EconCSLib.Statistics.priorWeightedVariance alpha beta etaLow t q := by
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
    EconCSLib.Statistics.priorWeightedSquaredBias alpha beta etaLow t q ≤
      EconCSLib.Statistics.priorWeightedSquaredBias alpha beta etaHigh t q := by
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
    EconCSLib.Statistics.JensenConvex
      (fun q => EconCSLib.Statistics.priorWeightedSquaredBias
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
    EconCSLib.Statistics.GlobalMinAt
      (fun q => EconCSLib.Statistics.priorWeightedSquaredBias
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
    EconCSLib.Statistics.JensenConcave
      (fun q => EconCSLib.Statistics.priorWeightedVariance
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
    EconCSLib.Statistics.GlobalMaxAt
      (fun q => EconCSLib.Statistics.priorWeightedVariance
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
    ¬ EconCSLib.Statistics.priorWeightedVariance alpha beta etaHigh t 0 <
      EconCSLib.Statistics.priorWeightedVariance alpha beta etaLow t 0 := by
  exact paper_theorem3_1_variance_strict_decrease_counterexample_quality_zero
    alpha beta t etaLow etaHigh

/--
Boundary caution for Theorem 3.1 strict decrease:
at `q_v = 1`, posterior-mean variance is identically zero for any prior strength,
so strict decrease cannot hold unconditionally.
-/
theorem paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_one
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ EconCSLib.Statistics.priorWeightedVariance alpha beta etaHigh t 1 <
      EconCSLib.Statistics.priorWeightedVariance alpha beta etaLow t 1 := by
  exact paper_theorem3_1_variance_strict_decrease_counterexample_quality_one
    alpha beta t etaLow etaHigh

/-! ## 5) Section 4 & Appendix C: Responsive Market and Dynamic Model -/

/-- Section 4: Individual Producer Unfairness.
Defined as the standard deviation in Selection Rate (SR) among producers with
the same true quality `q`.
-/
noncomputable def paper_facing_individual_producer_unfairness
    {V : Type*} [Fintype V] [DecidableEq V] :=
  @MBJG25ProducerFairness.Responsive.producerUnfairness V _ _

/-- Section 4: Thompson Sampling.
A dynamic policy that selects an arm by drawing from a belief distribution
and picking the argmax.
-/
def paper_facing_thompson_sampling_mechanism
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] :=
  @EconCSLib.Decision.IsThompsonSampling V _ _ _

/-- Section 4: Expected Regret (Efficiency).
The total expected regret across a finite time horizon.
-/
noncomputable def paper_facing_expected_regret
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] :=
  @EconCSLib.Online.expectedRegret V _ _ _

/-- Appendix C: MSE Decomposition in the responsive setting.
When the number of reviews $N$ is a random variable, the expected mean squared error
conditional on true quality decomposes into the expected squared bias and the expected variance.
-/
theorem paper_facing_responsive_mse_decomposition
    {α : Type*} [Fintype α] [DecidableEq α]
    {alpha beta eta q_v : ℝ}
    (state_dist : PMF α)
    (N : α → ℝ)
    (posterior_rating : α → ℝ)
    (h_cond_mean : ∀ s,
      posterior_rating s - q_v =
      EconCSLib.Statistics.priorWeightedBias alpha beta eta (N s) q_v)
    (h_cond_var : ∀ s,
      (posterior_rating s - q_v) ^ 2 -
      (EconCSLib.Statistics.priorWeightedBias alpha beta eta (N s) q_v) ^ 2 =
      EconCSLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v) :
    EconCSLib.pmfExp state_dist (fun s => (posterior_rating s - q_v) ^ 2) =
      EconCSLib.pmfExp state_dist (fun s =>
        EconCSLib.Statistics.priorWeightedSquaredBias alpha beta eta (N s) q_v) +
      EconCSLib.pmfExp state_dist (fun s =>
        EconCSLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v) := by
  exact MBJG25ProducerFairness.Responsive.paper_responsive_mse_decomposition
    state_dist N posterior_rating h_cond_mean h_cond_var

end MBJG25ProducerFairness
