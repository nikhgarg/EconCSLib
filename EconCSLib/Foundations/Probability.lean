import EconCSLib.Foundations.Probability.Admissions
import EconCSLib.Foundations.Probability.Averaging
import EconCSLib.Foundations.Probability.Bernoulli
import EconCSLib.Foundations.Probability.BivariateGaussian
import EconCSLib.Foundations.Probability.CTMC
import EconCSLib.Foundations.Probability.Conditional
import EconCSLib.Foundations.Probability.ContinuousReward
import EconCSLib.Foundations.Probability.Exponential
import EconCSLib.Foundations.Probability.FairCoin
import EconCSLib.Foundations.Probability.FiniteExpectation
import EconCSLib.Foundations.Probability.FiniteEmpiricalMultinomialCounts
import EconCSLib.Foundations.Probability.FiniteLabel
import EconCSLib.Foundations.Probability.FiniteMixture
import EconCSLib.Foundations.Probability.FiniteProductMultinomialCounts
import EconCSLib.Foundations.Probability.FiniteProductTernaryCounts
import EconCSLib.Foundations.Probability.FiniteRatingComparison
import EconCSLib.Foundations.Probability.FiniteRankingEvents
import EconCSLib.Foundations.Probability.FiniteSupportMGF
import EconCSLib.Foundations.Probability.FiniteTypeLogMass
import EconCSLib.Foundations.Probability.FinsetVariance
import EconCSLib.Foundations.Probability.Gaussian
import EconCSLib.Foundations.Probability.GaussianDerivatives
import EconCSLib.Foundations.Probability.GaussianHazardInverse
import EconCSLib.Foundations.Probability.GaussianMathlib
import EconCSLib.Foundations.Probability.GaussianMills
import EconCSLib.Foundations.Probability.GaussianQuantile
import EconCSLib.Foundations.Probability.InformationOrder
import EconCSLib.Foundations.Probability.IIDLargeDeviations
import EconCSLib.Foundations.Probability.IndependentProduct
import EconCSLib.Foundations.Probability.Kernel
import EconCSLib.Foundations.Probability.LargeDeviations
import EconCSLib.Foundations.Probability.MarkovChain
import EconCSLib.Foundations.Probability.MDP
import EconCSLib.Foundations.Probability.MeasureAtoms
import EconCSLib.Foundations.Probability.MeasureInequalities
import EconCSLib.Foundations.Probability.Occupancy
import EconCSLib.Foundations.Probability.OrderStatistics
import EconCSLib.Foundations.Probability.Pareto
import EconCSLib.Foundations.Probability.RandomUtility
import EconCSLib.Foundations.Probability.RandomUtilityDensity
import EconCSLib.Foundations.Probability.RealDistribution
import EconCSLib.Foundations.Probability.RealIntervalPartition
import EconCSLib.Foundations.Probability.RenewalReward
import EconCSLib.Foundations.Probability.StochasticDominance
import EconCSLib.Foundations.Probability.Symmetry
import EconCSLib.Foundations.Probability.Weighted
import EconCSLib.Foundations.Probability.WithoutReplacement

/-!
# Probability Foundations

Aggregate import for reusable probability infrastructure.

## Main declarations

- Finite PMF expectation/probability APIs:
  `EconCSLib.Foundations.Probability.FiniteExpectation`,
  `EconCSLib.Foundations.Probability.Conditional`,
  `EconCSLib.Foundations.Probability.Kernel`,
  `EconCSLib.Foundations.Probability.FiniteMixture`, and
  `EconCSLib.Foundations.Probability.FiniteLabel`.
  `FiniteExpectation` includes iid finite-product PMFs, coordinate-dependent
  product-event factorization, option-extension product decompositions, and
  finite-product reindexing/binomial success-count formulas.
- Continuous measure and concentration helpers:
  `EconCSLib.Foundations.Probability.Averaging`,
  `EconCSLib.Foundations.Probability.Bernoulli`,
  `EconCSLib.Foundations.Probability.ContinuousReward`,
  `EconCSLib.Foundations.Probability.MeasureInequalities`,
  `EconCSLib.Foundations.Probability.FairCoin`, and
  `EconCSLib.Foundations.Probability.FinsetVariance`.
- Large-deviation scaffolding:
  `EconCSLib.Foundations.Probability.FiniteSupportMGF`,
  `EconCSLib.Foundations.Probability.FiniteProductMultinomialCounts`,
  `EconCSLib.Foundations.Probability.IIDLargeDeviations`, and
  `EconCSLib.Foundations.Probability.LargeDeviations`.
- Finite information orders:
  `EconCSLib.Foundations.Probability.InformationOrder`.
- Order-statistic interfaces:
  `EconCSLib.Foundations.Probability.OrderStatistics`.
  This includes finite at-most-`k` top-sum maximization and tuple-level
  order-statistic integration interfaces, plus pointwise top-k sample-extension
  and two-level top-mass marginal bounds. It also provides the bridge from an
  upper-order-statistic threshold event to an iid strict-success count, finite
  iid expected top-k wrappers, and option-step marginal identities for adding
  one iid draw.
- Real distribution tail/CDF helpers:
  `EconCSLib.Foundations.Probability.RealDistribution`.
- Continuous heavy-tail distribution helpers:
  `EconCSLib.Foundations.Probability.Pareto`, including finite iid
  product-measure wrappers, closed-form Pareto upper-tail/CDF mass, and
  threshold-count and upper-order-statistic survival binomial formulas, plus
  support-scale tail-integral reductions.
- Dynamic and stochastic-process support:
  `EconCSLib.Foundations.Probability.MarkovChain`,
  `EconCSLib.Foundations.Probability.MDP`,
  `EconCSLib.Foundations.Probability.CTMC`, and
  `EconCSLib.Foundations.Probability.RenewalReward`.
- Finite sampling and occupancy tools:
  `EconCSLib.Foundations.Probability.Weighted`,
  `EconCSLib.Foundations.Probability.WithoutReplacement`, and
  `EconCSLib.Foundations.Probability.Occupancy`.
- Admissions/testing and stochastic-order wrappers:
  `EconCSLib.Foundations.Probability.Admissions`,
  `EconCSLib.Foundations.Probability.BivariateGaussian`,
  `EconCSLib.Foundations.Probability.Gaussian`,
  `EconCSLib.Foundations.Probability.GaussianMathlib`,
  `EconCSLib.Foundations.Probability.GaussianMills`,
  `EconCSLib.Foundations.Probability.GaussianDerivatives`,
  `EconCSLib.Foundations.Probability.GaussianQuantile`,
  `EconCSLib.Foundations.Probability.GaussianHazardInverse`, and
  `EconCSLib.Foundations.Probability.StochasticDominance`.
  `BivariateGaussian` includes correlated standard-Gaussian laws and
  independent two-coordinate Gaussian product/variance-scaling bridges for
  RUM-style conditional winner-ratio proofs.
- Random-utility noise, contraction, and density-product inequalities:
  `EconCSLib.Foundations.Probability.RandomUtility` and
  `EconCSLib.Foundations.Probability.RandomUtilityDensity`.
-/
