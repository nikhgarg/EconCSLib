import ProducerFairness.MainTheorems

/-!
# Paper-Facing Theorem Ledger: Bayesian Rating Fairness

This file is the single-file Lean audit surface for the ICWSM 2025
*Balancing Producer Fairness and Efficiency via Bayesian Rating System Design*
formalization.
Declarations are grouped in paper order (fixed binary-rating model
definitions, Theorem 3.1, Theorem 3.2, and the boundary-correctness note).

The core reusable model is in `EconCSLean.Statistics.BinaryRating`; this file
only re-surfaces the canonical declarations used by the paper-facing wrappers.
-/

namespace ProducerFairness

-- 1) Fixed binary-rating model definitions

-- True quality q_v and prior strength eta; posterior mean and derived terms.
#check EconCSLean.Statistics.priorWeightedPosteriorMean
#check EconCSLean.Statistics.priorWeightedBias
#check EconCSLean.Statistics.priorWeightedVariance
#check EconCSLean.Statistics.priorWeightedSquaredBias

-- Jensen/global-shape predicates used for paper Theorem 3.2.
#check EconCSLean.Statistics.JensenConvex
#check EconCSLean.Statistics.JensenConcave
#check EconCSLean.Statistics.GlobalMinAt
#check EconCSLean.Statistics.GlobalMaxAt

-- Core monotonic and algebraic lemmas used in the wrappers below.
#check EconCSLean.Statistics.priorWeightedVariance_weak_decrease
#check EconCSLean.Statistics.priorWeightedVariance_strict_decrease_of_interior_quality
#check EconCSLean.Statistics.priorWeightedSquaredBias_mono
#check EconCSLean.Statistics.priorWeightedSquaredBias_jensenConvex_quality
#check EconCSLean.Statistics.priorWeightedSquaredBias_globalMin_priorMean
#check EconCSLean.Statistics.priorWeightedVariance_jensenConcave_quality
#check EconCSLean.Statistics.priorWeightedVariance_globalMax_half
#check EconCSLean.Statistics.not_strictly_decreasing_priorWeightedVariance_quality_zero
#check EconCSLean.Statistics.not_strictly_decreasing_priorWeightedVariance_quality_one

-- 2) Theorem 3.1: posterior-mean variance and bias shape

-- Theorem 3.1 variance clause on the full binary-quality interval:
-- variance is weakly nonincreasing in prior strength.
#check paper_theorem3_1_variance_weak_decrease

-- Corrected strict version for interior quality `0 < q_v < 1` (boundary cases
-- require a separate note).
#check paper_theorem3_1_variance_strict_decrease_interior

-- Theorem 3.1 squared-bias monotonicity clause.
#check paper_theorem3_1_squared_bias_nondecreasing

-- 3) Theorem 3.2: shape of squared bias and variance in true quality

-- Theorem 3.2 first clause: squared bias is Jensen-convex in `q_v`.
#check paper_theorem3_2_squared_bias_convex_in_quality

-- Theorem 3.2 second clause: squared bias minimized at prior mean.
#check paper_theorem3_2_squared_bias_global_min_at_prior_mean

-- Theorem 3.2 third clause: variance is Jensen-concave in `q_v`.
#check paper_theorem3_2_variance_concave_in_quality

-- Theorem 3.2 final clause: variance maximized at `q_v = 1/2`.
#check paper_theorem3_2_variance_global_max_at_half

-- 4) Boundary-quality counterexamples to the unqualified strict form of
-- Theorem 3.1 (as noted in README and status notes).
#check paper_theorem3_1_variance_strict_decrease_counterexample_quality_zero
#check paper_theorem3_1_variance_strict_decrease_counterexample_quality_one

end ProducerFairness
