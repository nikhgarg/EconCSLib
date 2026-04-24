import EconCSLean.Statistics.BinaryRating

/-!
# Paper-Facing Theorems: Balancing Producer Fairness and Efficiency

This file records the current theorem-status finding for the prior-weighted
rating-system paper. The unqualified strict-variance claim in Theorem 3.1 has a
boundary-quality counterexample.
-/

namespace ProducerFairness

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
