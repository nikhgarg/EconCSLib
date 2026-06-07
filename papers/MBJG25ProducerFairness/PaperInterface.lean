import MBJG25ProducerFairness.MainTheorems
import MBJG25ProducerFairness.ResponsiveMarket
import EconCSLib.Learning.Bandits.ThompsonSampling
import EconCSLib.Algorithms.Online.Regret

/-!
# Paper Interface: Prior-Weighted Rating Fairness

This file is the single-file human-facing Lean interface for the ICWSM 2025
*Balancing Producer Fairness and Efficiency via Prior-Weighted Rating System Design*
formalization. The declarations are ordered to match paper presentation:

1. fixed binary-rating model definitions,
2. Theorem 3.1 claims,
3. Theorem 3.2 claims,
4. boundary caveats.

If this file typechecks and the commented statements match your paper notes, the
folder has a consistent paper-facing proof surface.
-/

namespace MBJG25ProducerFairness

open scoped BigOperators

/-! ## 1) Binary-rating model primitives - -/

/-- The posterior mean estimated quality in the fixed binary rating model.
    Source status: direct paper formula
    Paper Definition:
    $\frac{\eta \widetilde{\alpha} + t q_v}
            {\eta(\widetilde{\alpha}+\widetilde{\beta}) + t}$
-/
noncomputable def paper_posterior_mean (alpha beta eta t q_v : ℝ) : ℝ :=
  (eta * alpha + t * q_v) / (eta * alpha + eta * beta + t)

/-- The bias of the estimated quality.
    Source status: direct paper formula
    Paper Definition: $E[\hat{q}_v] - q_v$
-/
noncomputable def paper_bias (alpha beta eta t q_v : ℝ) : ℝ :=
  paper_posterior_mean alpha beta eta t q_v - q_v

/-- The variance of the estimated quality.
    Source status: direct paper formula
    Paper Definition:
    $\frac{t q_v (1 - q_v)}
            {(\eta(\widetilde{\alpha}+\widetilde{\beta}) + t)^2}$
-/
noncomputable def paper_variance (alpha beta eta t q_v : ℝ) : ℝ :=
  t * q_v * (1 - q_v) / (eta * alpha + eta * beta + t) ^ 2

/-- The squared bias of the estimated quality.
    Source status: direct paper formula
    Paper Definition: $(E[\hat{q}_v] - q_v)^2$
-/
noncomputable def paper_squared_bias (alpha beta eta t q_v : ℝ) : ℝ :=
  (paper_bias alpha beta eta t q_v) ^ 2

/-! ## 2) Theorem 3.1 statements -/

/--
Theorem 3.1, variance weakly decreases in prior strength:
for full quality interval `0 ≤ q_v ≤ 1`, if prior strength increases the
posterior-mean variance is nonincreasing.
Source status: corrected source statement
Source note: The paper's Theorem 3.1 variance monotonicity claim is split here into a weak full-interval statement and a strict interior statement because the unqualified strict statement fails at `q_v = 0` and `q_v = 1`.
-/
theorem paper_facing_theorem3_1_variance_weak_decrease
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_le : etaLow ≤ etaHigh) :
    paper_variance alpha beta etaHigh t q ≤
      paper_variance alpha beta etaLow t q := by
  simpa [paper_variance, EconCSLib.Statistics.priorWeightedVariance] using
    paper_theorem3_1_variance_weak_decrease
      hshape ht hq0 hq1 hetaLow_nonneg heta_le

/--
Theorem 3.1, strict decrease on interior quality values.
For `0 < q_v < 1`, positive prior-shape mass, positive number of prior samples,
and stronger prior strength `η_high > η_low`, variance is strictly decreasing.
Source status: corrected source statement
Source note: The paper states strict variance decrease without excluding boundary qualities; this formal statement adds `0 < q_v < 1` because variance is identically zero at `q_v = 0` and `q_v = 1`.
-/
theorem paper_facing_theorem3_1_variance_strict_decrease_interior
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hq0 : 0 < q)
    (hq1 : q < 1)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_lt : etaLow < etaHigh) :
    paper_variance alpha beta etaHigh t q <
      paper_variance alpha beta etaLow t q := by
  simpa [paper_variance, EconCSLib.Statistics.priorWeightedVariance] using
    paper_theorem3_1_variance_strict_decrease_interior
      hshape ht hq0 hq1 hetaLow_nonneg heta_lt

/--
Theorem 3.1, squared posterior-mean bias is nondecreasing in prior strength.
With stronger prior (`η_high ≥ η_low`) and basic nonnegativity assumptions,
the squared bias term does not decrease.
Source status: direct paper statement
-/
theorem paper_facing_theorem3_1_squared_bias_nondecreasing
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_le : etaLow ≤ etaHigh) :
    paper_squared_bias alpha beta etaLow t q ≤
      paper_squared_bias alpha beta etaHigh t q := by
  simpa [paper_squared_bias, paper_bias, paper_posterior_mean,
    EconCSLib.Statistics.priorWeightedSquaredBias,
    EconCSLib.Statistics.priorWeightedBias,
    EconCSLib.Statistics.priorWeightedPosteriorMean] using
    paper_theorem3_1_squared_bias_nondecreasing
      hshape ht hetaLow_nonneg heta_le

/-! ## 3) Theorem 3.2 statements -/

/--
Theorem 3.2, squared-bias Jensen convexity in true quality.
The squared bias is Jensen-convex as a function of quality.
Source status: direct paper statement
-/
theorem paper_facing_theorem3_2_squared_bias_convex_in_quality
    {alpha beta eta t : ℝ}
    (hden : eta * alpha + eta * beta + t ≠ 0) :
    EconCSLib.Statistics.JensenConvex
      (fun q => paper_squared_bias alpha beta eta t q) := by
  simpa [paper_squared_bias, paper_bias, paper_posterior_mean,
    EconCSLib.Statistics.priorWeightedSquaredBias,
    EconCSLib.Statistics.priorWeightedBias,
    EconCSLib.Statistics.priorWeightedPosteriorMean] using
    paper_theorem3_2_squared_bias_convex_in_quality hden

/--
Theorem 3.2, squared-bias global minimizer.
On the full quality interval, squared bias is minimized at the prior mean
`alpha / (alpha + beta)` under positive shape mass and positive sample weight.
Source status: direct paper statement
-/
theorem paper_facing_theorem3_2_squared_bias_global_min_at_prior_mean
    {alpha beta eta t : ℝ}
    (hshape : 0 < alpha + beta)
    (heta_nonneg : 0 ≤ eta)
    (ht : 0 < t) :
    EconCSLib.Statistics.GlobalMinAt
      (fun q => paper_squared_bias alpha beta eta t q)
      (alpha / (alpha + beta)) := by
  simpa [paper_squared_bias, paper_bias, paper_posterior_mean,
    EconCSLib.Statistics.priorWeightedSquaredBias,
    EconCSLib.Statistics.priorWeightedBias,
    EconCSLib.Statistics.priorWeightedPosteriorMean] using
    paper_theorem3_2_squared_bias_global_min_at_prior_mean
      hshape heta_nonneg ht

/--
Theorem 3.2, posterior-mean variance Jensen concavity in true quality.
This holds when the prior-weighted sample mass is nonnegative (`t ≥ 0`).
Source status: direct paper statement
-/
theorem paper_facing_theorem3_2_variance_concave_in_quality
    {alpha beta eta t : ℝ}
    (ht : 0 ≤ t) :
    EconCSLib.Statistics.JensenConcave
      (fun q => paper_variance alpha beta eta t q) := by
  simpa [paper_variance, EconCSLib.Statistics.priorWeightedVariance] using
    paper_theorem3_2_variance_concave_in_quality
      (alpha := alpha) (beta := beta) (eta := eta) ht

/--
Theorem 3.2, posterior-mean variance global maximum at `q = 1/2`.
For nonnegative prior-weighted sample mass, variance is globally maximized at
`q_v = 1/2`.
Source status: direct paper statement
-/
theorem paper_facing_theorem3_2_variance_global_max_at_half
    {alpha beta eta t : ℝ}
    (ht : 0 ≤ t) :
    EconCSLib.Statistics.GlobalMaxAt
      (fun q => paper_variance alpha beta eta t q)
      (1 / 2) := by
  simpa [paper_variance, EconCSLib.Statistics.priorWeightedVariance] using
    paper_theorem3_2_variance_global_max_at_half
      (alpha := alpha) (beta := beta) (eta := eta) ht

/-! ## 4) Boundary caveats -/

/--
Boundary caution for Theorem 3.1 strict decrease:
at `q_v = 0`, posterior-mean variance is identically zero for any prior strength,
so strict decrease cannot hold unconditionally.
Source status: added audit row
Source note: This is not a source theorem; it is included to make the Theorem 3.1 strict-decrease source deviation reviewable.
-/
theorem paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_zero
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ paper_variance alpha beta etaHigh t 0 <
      paper_variance alpha beta etaLow t 0 := by
  simpa [paper_variance, EconCSLib.Statistics.priorWeightedVariance] using
    paper_theorem3_1_variance_strict_decrease_counterexample_quality_zero
      alpha beta t etaLow etaHigh

/--
Boundary caution for Theorem 3.1 strict decrease:
at `q_v = 1`, posterior-mean variance is identically zero for any prior strength,
so strict decrease cannot hold unconditionally.
Source status: added audit row
Source note: This is not a source theorem; it is included to make the Theorem 3.1 strict-decrease source deviation reviewable.
-/
theorem paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_one
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ paper_variance alpha beta etaHigh t 1 <
      paper_variance alpha beta etaLow t 1 := by
  simpa [paper_variance, EconCSLib.Statistics.priorWeightedVariance] using
    paper_theorem3_1_variance_strict_decrease_counterexample_quality_one
      alpha beta t etaLow etaHigh

/-! ## 5) Section 4 & Appendix C: Responsive Market and Dynamic Model -/

/-- Section 4: Individual Producer Unfairness.
Defined as the standard deviation in Selection Rate (SR) among producers with
the same true quality `q`.
Source status: direct paper definition
-/
noncomputable def paper_facing_individual_producer_unfairness
    {V : Type*} [Fintype V] [DecidableEq V]
    (selections : V → ℝ)
    (lifespan : V → ℝ)
    (q_v : V → ℝ)
    (q : ℝ) : ℝ :=
  Real.sqrt
    (EconCSLib.Statistics.finsetVariance
      (Finset.univ.filter (fun v => q_v v = q))
      (fun v => selections v / lifespan v))

/-- Section 4: Thompson Sampling.
A dynamic policy that selects an arm by drawing from a belief distribution
and picking the argmax.
Source status: direct paper definition
-/
def paper_facing_thompson_sampling_mechanism
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (belief : PMF (V → ℝ))
    (policy : PMF V) : Prop :=
  ∃ tie_breaker : (V → ℝ) → V,
    (∀ (profile : V → ℝ) (v : V), profile v ≤ profile (tie_breaker profile)) ∧
    policy = belief.bind (fun profile => PMF.pure (tie_breaker profile))

/-- Section 4: Expected Regret (Efficiency).
The total expected regret across a finite time horizon.
Source status: direct paper definition
-/
noncomputable def paper_facing_expected_regret
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (T : ℕ)
    (M : Fin T → Finset V)
    (h_nonempty : ∀ t, (M t).Nonempty)
    (q : V → ℝ)
    (pi : (t : Fin T) → PMF V) : ℝ :=
  ∑ t : Fin T, ((M t).sup' (h_nonempty t) q - EconCSLib.pmfExp (pi t) q)

/-- Appendix C: MSE Decomposition in the responsive setting.
When the number of reviews $N$ is a random variable, the expected mean squared error
conditional on true quality decomposes into the expected squared bias and the expected variance.
Source status: direct paper statement
-/
theorem paper_facing_responsive_mse_decomposition
    {α : Type*} [Fintype α] [DecidableEq α]
    {alpha beta eta q_v : ℝ}
    (state_dist : PMF α)
    (N : α → ℝ)
    (posterior_rating : α → ℝ)
    (h_cond_mean : ∀ s,
      posterior_rating s - q_v =
      paper_bias alpha beta eta (N s) q_v)
    (h_cond_var : ∀ s,
      (posterior_rating s - q_v) ^ 2 -
      (paper_bias alpha beta eta (N s) q_v) ^ 2 =
      paper_variance alpha beta eta (N s) q_v) :
    EconCSLib.pmfExp state_dist (fun s => (posterior_rating s - q_v) ^ 2) =
      EconCSLib.pmfExp state_dist (fun s =>
        paper_squared_bias alpha beta eta (N s) q_v) +
      EconCSLib.pmfExp state_dist (fun s =>
        paper_variance alpha beta eta (N s) q_v) := by
  have h_mean_lib : ∀ s,
      posterior_rating s - q_v =
      EconCSLib.Statistics.priorWeightedBias alpha beta eta (N s) q_v := by
    intro s
    simpa [paper_bias, paper_posterior_mean,
      EconCSLib.Statistics.priorWeightedBias,
      EconCSLib.Statistics.priorWeightedPosteriorMean] using h_cond_mean s
  have h_var_lib : ∀ s,
      (posterior_rating s - q_v) ^ 2 -
      (EconCSLib.Statistics.priorWeightedBias alpha beta eta (N s) q_v) ^ 2 =
      EconCSLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v := by
    intro s
    simpa [paper_bias, paper_posterior_mean, paper_variance,
      EconCSLib.Statistics.priorWeightedBias,
      EconCSLib.Statistics.priorWeightedPosteriorMean,
      EconCSLib.Statistics.priorWeightedVariance] using h_cond_var s
  simpa [paper_squared_bias, paper_bias, paper_posterior_mean, paper_variance,
    EconCSLib.Statistics.priorWeightedSquaredBias,
    EconCSLib.Statistics.priorWeightedBias,
    EconCSLib.Statistics.priorWeightedPosteriorMean,
    EconCSLib.Statistics.priorWeightedVariance] using
    MBJG25ProducerFairness.Responsive.paper_responsive_mse_decomposition
      state_dist N posterior_rating h_mean_lib h_var_lib

end MBJG25ProducerFairness
