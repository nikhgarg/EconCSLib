# Balancing Producer Fairness and Efficiency via Bayesian Rating System Design

Machine-readable status source: [`status.json`](status.json).

## Source Version

- Paper: *Balancing Producer Fairness and Efficiency via Bayesian Rating System Design*
- Authors: Thomas Ma, Michael S. Bernstein, Ramesh Johari, and Nikhil Garg
- Version formalized: arXiv:2207.04369 / ICWSM 2025 version
- arXiv URL: https://arxiv.org/abs/2207.04369
- PDF URL: https://arxiv.org/pdf/2207.04369
- Official URL: https://ojs.aaai.org/index.php/ICWSM/article/view/35865
- Accessed: 2026-04-24

The PDF is cached locally as `MBJG25ProducerFairness.pdf` and ignored by the
paper-folder `.gitignore`. The extracted text cache
`MBJG25ProducerFairness.txt` is used for named-statement searches; refresh it
only if the source PDF changes. Use the arXiv URL above as the source version
for theorem-number and definition comparisons.

## Central Theorem File

- `MBJG25ProducerFairness/PaperInterface.lean`
  (imports and re-exports the wrappers in `MBJG25ProducerFairness/MainTheorems.lean` for a
  single-file audit target)

That file contains the paper-facing theorem wrappers. Reusable binary-rating
algebra lives in `EconCSLib/Statistics/BinaryRating.lean`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Theorem 3.1, variance weakly decreases in prior strength | `paper_theorem3_1_variance_weak_decrease` | formalized with caveat | `MBJG25ProducerFairness/MainTheorems.lean` | Previous status: formalized with corrected weak statement; assumes `0 ≤ q_v ≤ 1`, `0 < t`, `0 < alpha + beta`, `0 ≤ etaLow`, and `etaLow ≤ etaHigh` |
| Theorem 3.1, variance strictly decreases in prior strength | `paper_theorem3_1_variance_strict_decrease_interior`; boundary checks `paper_theorem3_1_variance_strict_decrease_counterexample_quality_zero`, `paper_theorem3_1_variance_strict_decrease_counterexample_quality_one` | formalized with caveat | `MBJG25ProducerFairness/MainTheorems.lean` | Previous status: formalized with corrected interior assumption; boundary bug found; The corrected strict theorem assumes `0 < q_v < 1`, `0 < t`, `0 < alpha + beta`, `0 ≤ etaLow`, and `etaLow < etaHigh`. |
| Theorem 3.1, squared bias nondecreases in prior strength | `paper_theorem3_1_squared_bias_nondecreasing` | formalized | `MBJG25ProducerFairness/MainTheorems.lean` | None |
| Theorem 3.2, squared bias convex in true quality | `paper_theorem3_2_squared_bias_convex_in_quality` | formalized | `MBJG25ProducerFairness/MainTheorems.lean` | None |
| Theorem 3.2, squared bias minimized at prior mean | `paper_theorem3_2_squared_bias_global_min_at_prior_mean` | formalized | `MBJG25ProducerFairness/MainTheorems.lean` | None |
| Theorem 3.2, variance concave in true quality | `paper_theorem3_2_variance_concave_in_quality` | formalized | `MBJG25ProducerFairness/MainTheorems.lean` | None |
| Theorem 3.2, variance maximized at `1/2` | `paper_theorem3_2_variance_global_max_at_half` | formalized | `MBJG25ProducerFairness/MainTheorems.lean` | None |

### Dynamic and Responsive Extensions

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Section 4, Individual Producer Unfairness | `paper_facing_individual_producer_unfairness` | formalized | `MBJG25ProducerFairness/ResponsiveMarket.lean` | None |
| Section 4, Thompson Sampling | `paper_facing_thompson_sampling_mechanism` | formalized | `EconCSLib/Decision/ThompsonSampling.lean` | None |
| Section 4, Expected Regret | `paper_facing_expected_regret` | formalized | `EconCSLib/Online/Regret.lean` | None |
| Appendix C, MSE Decomposition | `paper_facing_responsive_mse_decomposition` | formalized | `MBJG25ProducerFairness/ResponsiveMarket.lean` | None |
| Appendix E, Ordinal Rating | `EconCSLib.Statistics.dirichletCategoricalPosteriorMean_eq_weighted_sum` | formalized | `EconCSLib/Statistics/OrdinalRating.lean` | None |

## Fix Needed In Paper Statement

The published strict variance-decrease statement should explicitly exclude
boundary qualities. The formalized corrected version assumes `0 < q_v < 1`.
Alternatively, the paper could state weak decrease on `0 ≤ q_v ≤ 1` and reserve
strict decrease for the interior case; the weak version is now formalized as
`paper_theorem3_1_variance_weak_decrease`.

## Source-Audit Notes

The cached text contains Theorem 3.1 and Theorem 3.2 as the only numbered
source theorems, repeated in the appendix proofs. The theorem table above
covers both named source theorems. Section 4 and appendix entries are
formalized as paper-facing definitions/results, but they are not source-numbered
theorem wrappers.
