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

- `ProducerFairness/MainTheorems.lean`

That file contains the paper-facing theorem wrappers. Reusable binary-rating
algebra lives in `EconCSLean/Statistics/BinaryRating.lean`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Theorem 3.1, variance strictly decreases in prior strength | `paper_theorem3_1_variance_strict_decrease_interior`; boundary checks `paper_theorem3_1_variance_strict_decrease_counterexample_quality_zero`, `paper_theorem3_1_variance_strict_decrease_counterexample_quality_one` | formalized with corrected interior assumption; boundary bug found | `ProducerFairness/MainTheorems.lean` | The corrected strict theorem assumes `0 < q_v < 1`, `0 < t`, `0 < alpha + beta`, `0 ≤ etaLow`, and `etaLow < etaHigh`. |
| Theorem 3.1, squared bias nondecreases in prior strength | none | not formalized | none | likely true under positive prior-shape/review-count assumptions; not pursued after the strict-variance bug was found |
| Theorem 3.2, bias convex and variance concave in true quality | none | not formalized | none | should be formalized after restating Theorem 3.1 with boundary cases handled |

## Fix Needed In Paper Statement

The published strict variance-decrease statement should explicitly exclude
boundary qualities. The formalized corrected version assumes `0 < q_v < 1`.
Alternatively, the paper could state weak decrease on `0 ≤ q_v ≤ 1` and reserve
strict decrease for the interior case.
