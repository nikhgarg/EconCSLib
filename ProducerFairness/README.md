# Balancing Producer Fairness and Efficiency via Bayesian Rating System Design

## Source Version

- Paper: *Balancing Producer Fairness and Efficiency via Bayesian Rating System Design*
- Authors: Thomas Ma, Michael S. Bernstein, Ramesh Johari, and Nikhil Garg
- Version formalized: arXiv:2207.04369 / ICWSM 2025 version
- arXiv URL: https://arxiv.org/abs/2207.04369
- PDF URL: https://arxiv.org/pdf/2207.04369
- Official URL: https://ojs.aaai.org/index.php/ICWSM/article/view/35865
- Accessed: 2026-04-24

The PDF is not committed to git. Use the arXiv URL above as the source version
for theorem-number and definition comparisons.

## Central Theorem File

- `ProducerFairness/PaperFacingTheorems.lean`
  (imports and re-exports the wrappers in `ProducerFairness/MainTheorems.lean` for a
  single-file audit target)

That file contains the paper-facing theorem wrappers. Reusable binary-rating
algebra lives in `EconCSLean/Statistics/BinaryRating.lean`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Theorem 3.1, variance weakly decreases in prior strength | `paper_theorem3_1_variance_weak_decrease` | formalized with corrected weak statement | `ProducerFairness/MainTheorems.lean` | assumes `0 ≤ q_v ≤ 1`, `0 < t`, `0 < alpha + beta`, `0 ≤ etaLow`, and `etaLow ≤ etaHigh` |
| Theorem 3.1, variance strictly decreases in prior strength | `paper_theorem3_1_variance_strict_decrease_interior`; boundary checks `paper_theorem3_1_variance_strict_decrease_counterexample_quality_zero`, `paper_theorem3_1_variance_strict_decrease_counterexample_quality_one` | formalized with corrected interior assumption; boundary bug found | `ProducerFairness/MainTheorems.lean` | The corrected strict theorem assumes `0 < q_v < 1`, `0 < t`, `0 < alpha + beta`, `0 ≤ etaLow`, and `etaLow < etaHigh`. |
| Theorem 3.1, squared bias nondecreases in prior strength | `paper_theorem3_1_squared_bias_nondecreasing` | formalized | `ProducerFairness/MainTheorems.lean` | assumes `0 < t`, `0 < alpha + beta`, `0 ≤ etaLow`, and `etaLow ≤ etaHigh` |
| Theorem 3.2, squared bias convex in true quality | `paper_theorem3_2_squared_bias_convex_in_quality` | formalized | `ProducerFairness/MainTheorems.lean` | denominator nonzero |
| Theorem 3.2, squared bias minimized at prior mean | `paper_theorem3_2_squared_bias_global_min_at_prior_mean` | formalized | `ProducerFairness/MainTheorems.lean` | assumes `0 < alpha + beta`, `0 ≤ eta`, and `0 < t` |
| Theorem 3.2, variance concave in true quality | `paper_theorem3_2_variance_concave_in_quality` | formalized | `ProducerFairness/MainTheorems.lean` | assumes `0 ≤ t` |
| Theorem 3.2, variance maximized at `1/2` | `paper_theorem3_2_variance_global_max_at_half` | formalized | `ProducerFairness/MainTheorems.lean` | assumes `0 ≤ t` |

### Dynamic and Responsive Extensions

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Section 4, Individual Producer Unfairness | `paper_facing_individual_producer_unfairness` | formalized | `ProducerFairness/ResponsiveMarket.lean` | - |
| Section 4, Thompson Sampling | `paper_facing_thompson_sampling_mechanism` | formalized | `EconCSLean/Decision/ThompsonSampling.lean` | - |
| Section 4, Expected Regret | `paper_facing_expected_regret` | formalized | `EconCSLean/Online/Regret.lean` | - |
| Appendix C, MSE Decomposition | `paper_facing_responsive_mse_decomposition` | formalized | `ProducerFairness/ResponsiveMarket.lean` | - |
| Appendix E, Ordinal Rating | `EconCSLean.Statistics.dirichletCategoricalPosteriorMean_eq_weighted_sum` | formalized | `EconCSLean/Statistics/OrdinalRating.lean` | `∑ (alpha + N) ≠ 0` |

## Fix Needed In Paper Statement

The published strict variance-decrease statement should explicitly exclude
boundary qualities. The formalized corrected version assumes `0 < q_v < 1`.
Alternatively, the paper could state weak decrease on `0 ≤ q_v ≤ 1` and reserve
strict decrease for the interior case; the weak version is now formalized as
`paper_theorem3_1_variance_weak_decrease`.
