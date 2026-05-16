import EconCSLib.Foundations.Probability.Admissions
import EconCSLib.Foundations.Probability.BivariateGaussian
import EconCSLib.Foundations.Probability.CTMC
import EconCSLib.Foundations.Probability.Conditional
import EconCSLib.Foundations.Probability.FairCoin
import EconCSLib.Foundations.Probability.FiniteExpectation
import EconCSLib.Foundations.Probability.FiniteLabel
import EconCSLib.Foundations.Probability.FiniteSupportMGF
import EconCSLib.Foundations.Probability.FinsetVariance
import EconCSLib.Foundations.Probability.Gaussian
import EconCSLib.Foundations.Probability.GaussianDerivatives
import EconCSLib.Foundations.Probability.GaussianHazardInverse
import EconCSLib.Foundations.Probability.GaussianMathlib
import EconCSLib.Foundations.Probability.GaussianMills
import EconCSLib.Foundations.Probability.GaussianQuantile
import EconCSLib.Foundations.Probability.Kernel
import EconCSLib.Foundations.Probability.LargeDeviations
import EconCSLib.Foundations.Probability.MarkovChain
import EconCSLib.Foundations.Probability.MDP
import EconCSLib.Foundations.Probability.MeasureInequalities
import EconCSLib.Foundations.Probability.Occupancy
import EconCSLib.Foundations.Probability.OrderStatistics
import EconCSLib.Foundations.Probability.RandomUtility
import EconCSLib.Foundations.Probability.RealDistribution
import EconCSLib.Foundations.Probability.RenewalReward
import EconCSLib.Foundations.Probability.StochasticDominance
import EconCSLib.Foundations.Probability.Weighted
import EconCSLib.Foundations.Probability.WithoutReplacement

/-!
# Probability Foundations

Aggregate import for reusable probability infrastructure.

## Main declarations

- Finite PMF expectation/probability APIs:
  `EconCSLib.Foundations.Probability.FiniteExpectation`,
  `EconCSLib.Foundations.Probability.Conditional`,
  `EconCSLib.Foundations.Probability.Kernel`, and
  `EconCSLib.Foundations.Probability.FiniteLabel`.
- Continuous measure and concentration helpers:
  `EconCSLib.Foundations.Probability.MeasureInequalities`,
  `EconCSLib.Foundations.Probability.FairCoin`, and
  `EconCSLib.Foundations.Probability.FinsetVariance`.
- Large-deviation scaffolding:
  `EconCSLib.Foundations.Probability.FiniteSupportMGF` and
  `EconCSLib.Foundations.Probability.LargeDeviations`.
- Order-statistic interfaces:
  `EconCSLib.Foundations.Probability.OrderStatistics`.
- Real distribution tail/CDF helpers:
  `EconCSLib.Foundations.Probability.RealDistribution`.
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
- Random-utility noise, contraction, and density-product inequalities:
  `EconCSLib.Foundations.Probability.RandomUtility`.
-/
