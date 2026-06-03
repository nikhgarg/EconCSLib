# Probability Library Roadmap

This tracks reusable probability work suggested by the current paper queue.

## Immediate Reuse Targets

- DSWG discretization: finite-label posterior vectors, aggregate posterior
  masses, indicator integrals, bounded-measurable integrability dischargers,
  and Bayes/tower-property bridges.
- testing papers: finite signal kernels, conditional
  resampling, posterior estimates, equality of pushforward distributions, and
  eventually Gaussian posterior/CDF/hazard-rate certificates.
- diversity-aware recommendation: order-statistic expectations, top-`k` value
  asymptotics, Bernoulli/product-law identities, and distribution-family
  certificate wrappers.
- GN21 driver surge pricing: continuous set-integral algebra, with-density
  positivity, finite-measure integrability, CTMC kernels, and renewal-reward
  quotient comparisons.

## Current Additions

- `EconCSLib.Foundations.Probability.FiniteLabel` now contains the stable
  finite-label API copied out of the mature DSWG proof pattern: label
  indicators and shares, aggregate score mass, posterior-simplex algebra,
  finite-label MAE bounds/integrability, and the PMF-expectation bridge to
  `Decision.FiniteLinearExpectation`.
- `EconCSLib.Foundations.Probability.Kernel` now exposes finite Bayesian
  posterior expectation algebra for positive signal probabilities:
  denominator-clearing, constant-one normalization, nonnegativity, upper
  bounds, and interval preservation. `Admissions` has thin wrappers around
  these lemmas for GLM/LG-style admissions models.
- `EconCSLib.Foundations.Probability.Conditional` now has the matching finite
  conditional-expectation API: denominator-clearing, constant-one
  normalization, indicator-expectation bounds, nonnegativity, upper bounds,
  and interval preservation.
- `EconCSLib.Foundations.Probability.FiniteExpectation` now includes generic
  finite-PMF indicator expectation helpers: pointwise domination by
  `C * 1_E` bounds an expectation by `C * P(E)`, and independent pair
  indicator events factor as a product of marginal event probabilities.
- `EconCSLib.Foundations.Probability.MeasureInequalities` now includes generic
  continuous-measure helpers for finite subset mass, positivity of real-valued
  measure from nonzero finite `ENNReal` mass, positive real mass under positive
  finite `withDensity` measures, and boundary-null a.e. congruence:
  properties/functions/predicates that agree off a null set, Boolean and
  set-indicator congruence, strict-vs-weak real cutoff conversion from a null
  level set, and generic positive-mass contradiction/zero-mass lemmas for
  a.e. weak or strict inequalities. It also has null symmetric-difference
  set-congruence lemmas for adding/removing a common context set and for
  merging touching open intervals/rays up to a null endpoint.
- `EconCSLib.Foundations.Probability.Gaussian` now provides the reusable
  algebraic layer needed by GLM/LG-style testing papers: Gaussian
  location-scale standardization, an abstract standard-normal CDF/density API,
  single-signal conjugate posterior precision/variance/mean formulas,
  posterior-mean monotonicity, finite signal-family posterior mean monotonicity,
  finite multi-signal posterior weights and posterior-mean law wrappers,
  posterior-variance reduction under finite signals, nonzero-noise-mean signal
  centering, posterior/raw-signal threshold conversion, threshold
  pass-probability monotonicity in the cutoff and mean, finite-mixture tail
  mass/capacity certificates, positive-affine location-scale transformations,
  and a hazard-rate certificate boundary with location-scale tail positivity,
  density/tail hazard conversion, upper-tail conditional mean monotonicity,
  strict upper-tail mean-above-threshold certificates for positive standardized
  cutoffs, and finite-mixture admitted-mean accounting.
- `EconCSLib.Foundations.Probability.FiniteSupportMGF` now provides
  finite-support moment-generating functions, log-MGFs, Legendre objectives,
  rate-function scaffolding, and a finite rating-scale LDP model interface.
- `EconCSLib.Foundations.Probability.LargeDeviations` now provides reusable
  exponential-rate certificate plumbing: negative normalized log decay,
  exact-rate certificates, eventual exponential upper bounds with constants,
  eventual exponential lower bounds with constants, conversion from exact rates
  to weaker upper/lower-bound rates, finite weighted-sum aggregation, and
  pairwise ranking-error aggregation certificates, including finite-sum lower
  bounds from a single positive-weight component and pairwise aggregate lower
  bounds from one certified pair.
- `EconCSLib.Foundations.Probability.OrderStatistics` now provides the
  reusable probability-facing interface for diversity-aware recommendation arguments:
  top-`k` expected-value oracles, marginal top-`k` values, diminishing and
  nonnegative marginal predicates, and finite-type scaled-marginal limit
  certificates that yield eventual multiplicative marginal sandwiches and
  strict marginal comparisons from scaled weight gaps.  It also now includes
  the bottom-indexed `μ(rank, sampleSize)` bridge for papers that state
  expected order-statistic means directly, connecting those means to tuple-level
  `sampleTopKSum` and reflected endpoint-loss expectations.
- `EconCSLib.Foundations.Math.Asymptotics` now has the fixed finite-sum
  asymptotic assembly used by PRPKG-style order-statistic calculations:
  common-scale summation of finitely many equivalent terms and addition of a
  negligible remainder on the same scale.
- `EconCSLib.Foundations.Probability.RealDistribution` now provides thin
  wrappers around Mathlib's real CDF API: lower CDF mass, upper-tail mass,
  monotonicity, `cdf` identification, the upper-tail complement formula, and
  upper-tail threshold/capacity certificates.
- `EconCSLib.Foundations.Probability.FiniteMixture` now provides the reusable
  finite-mixture/event-share layer used by LG-style testing policies: binary
  PMF mixtures, finite event shares, indexed full-support-to-positive-share
  bridges, blank-on-zero-share indexed values, positive-share cancellation for
  PMFs and extensional laws, PMF pushforward support lemmas, and raw-relevance
  equivalences for event-share binary mixtures.

## Next Library Work

- Conditional expectation API for finite labels over arbitrary feature spaces:
  posterior score maps, calibration predicates, aggregate-posterior/tower
  identities, and finite-score/fiber calibration dischargers.
- Indicator/set-integral automation: more standard lemmas for
  `if p then 1 else 0`, finite sums of indicators, finite partitions, and
  bounded measurable integrands under finite measures.  The first boundary-null
  a.e. indicator congruence and null symmetric-difference interval-merging
  lemmas now live in `MeasureInequalities`; future work should build on those
  rather than duplicating paper-local cutoff/tie rewrites.
- PMF-to-measure transfer: wrappers moving finite PMF facts to
  `Measure.toPMF`, `PMF.toMeasure`, and finite measurable pushforwards.
- Kernel/disintegration bridge: finite and standard-Borel Markov-kernel
  wrappers for joint laws, marginals, posterior kernels, and law-of-total
  probability identities.
- Order-statistic analytic layer for diversity-aware recommendation papers:
  prove the concrete bounded, exponential, and Pareto integral/order-statistic
  asymptotics and instantiate
  `TopKExpectationOracle.ScaledMarginalLimitCertificate`; then connect those
  probability certificates to the existing separable optimization/FOC bridges.
  The generic bottom-indexed order-statistic mean bridge has been promoted, so
  future work should target distribution-specific finite-sample means and
  asymptotics rather than rebuilding the `μ(rank,a)` interface.
- Large-deviation analytic layer: instantiate finite-support log-MGF
  certificates with concrete Cramer/Gartner-Ellis or Laplace-principle proofs
  for rating-system and recommender asymptotic papers. The current library
  handles MGF algebra and finite union/aggregation of rates; the remaining
  work is the analytic theorem that turns a distribution family into an exact
  `ExponentialRateCertificate`.
- Gaussian testing layer for GLM/LG: extend the mathlib-backed concrete
  standard-normal CDF/density/hazard layer with true truncated-normal
  expectation derivations, threshold existence/comparison certificates, and
  source-facing admission/diversity endpoints beyond the current finite-mixture
  threshold witness interface.
- Finite-mixture thin wrappers for continuous law families: `FiniteMixture`
  already has extensional-law cancellation, but future papers may need reusable
  instantiated wrappers for Gaussian/real-distribution laws rather than
  paper-local extensionality arguments.

## Deferred Cleanup

- Do not reorganize `papers/GN21DriverSurgePricing` while another agent is
  actively working there. It is fine to copy stable set-integral or
  with-density patterns into `EconCSLib`; after the paper stabilizes, thin the
  GN file by replacing local copies with imports from the reusable probability
  modules.
