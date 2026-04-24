import EconCSLean.Statistics.BinaryRating

/-!
# Paper-Facing Theorems: Balancing Producer Fairness and Efficiency

This file records the current theorem-status finding for the prior-weighted
rating-system paper. The strict-variance clause of Theorem 3.1 is formalized
with an interior-quality assumption; the unqualified published statement has
boundary-quality counterexamples.
-/

namespace ProducerFairness

/--
Corrected interior-quality version of the strict variance-decrease clause of
Theorem 3.1.

The paper-facing statement is intentionally close to the theorem claim: in the
binary-rating posterior mean model, increasing prior strength strictly decreases
the variance term when true quality is interior, the review count is positive,
the prior-shape total mass is positive, and the lower prior strength is
nonnegative.
-/
theorem paper_theorem3_1_variance_strict_decrease_interior
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hq0 : 0 < q)
    (hq1 : q < 1)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_lt : etaLow < etaHigh) :
    EconCSLean.Statistics.priorWeightedVariance alpha beta etaHigh t q <
      EconCSLean.Statistics.priorWeightedVariance alpha beta etaLow t q := by
  exact EconCSLean.Statistics.priorWeightedVariance_strict_decrease_of_interior_quality
    hshape ht hq0 hq1 hetaLow_nonneg heta_lt

/--
Boundary counterexample to the strict variance-decrease clause of Theorem 3.1.

At true quality `q_v = 0`, the Bernoulli variance term is zero for every prior
strength, so the variance cannot be strictly decreasing as prior strength
increases.
-/
theorem paper_theorem3_1_variance_strict_decrease_counterexample_quality_zero
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ EconCSLean.Statistics.priorWeightedVariance alpha beta etaHigh t 0 <
      EconCSLean.Statistics.priorWeightedVariance alpha beta etaLow t 0 := by
  exact EconCSLean.Statistics.not_strictly_decreasing_priorWeightedVariance_quality_zero
    alpha beta t etaLow etaHigh

/--
Boundary counterexample to the strict variance-decrease clause of Theorem 3.1.

At true quality `q_v = 1`, the Bernoulli variance term is zero for every prior
strength, so the variance cannot be strictly decreasing as prior strength
increases.
-/
theorem paper_theorem3_1_variance_strict_decrease_counterexample_quality_one
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ EconCSLean.Statistics.priorWeightedVariance alpha beta etaHigh t 1 <
      EconCSLean.Statistics.priorWeightedVariance alpha beta etaLow t 1 := by
  exact EconCSLean.Statistics.not_strictly_decreasing_priorWeightedVariance_quality_one
    alpha beta t etaLow etaHigh

end ProducerFairness
