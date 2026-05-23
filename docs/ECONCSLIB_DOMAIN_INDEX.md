# EconCSLib Domain Index

This file tracks where reusable declarations live and where to start reading
when you need material from a domain quickly.

## Foundations

- Entrypoint: `EconCSLib.Foundations`
- Narrow entrypoints: `EconCSLib.Foundations.Math`,
  `EconCSLib.Foundations.Graph`, `EconCSLib.Foundations.Probability`,
  `EconCSLib.Foundations.Optimization`,
  `EconCSLib.Foundations.Econometrics`
- Modules:
  - `EconCSLib.Foundations.Math`:
    `FiniteSum`, `FiniteRanking`, `FiniteRounding`, `FiniteSigns`,
    `Sequence`, `Asymptotics`, `IntervalCrossing`,
    `EpsilonContinuity`, `PositiveDenominator`, `AffineThreshold`,
    `ThresholdCharacterization`, `ExponentialBounds`
    - `FiniteSum`: finite weighted-sum bounds, injective subfamily sum
      comparisons, weighted-share race bounds, finite averaging/cardinality
      lower bounds, Cauchy-Schwarz, and finite telescoping/crossing helpers.
    - `FiniteRanking`: finite-set ranking by real scores with deterministic
      tie-breaking, lower/upper rank prefix sets, rank-prefix cardinalities,
      rank-prefix monotonicity, and lower-vs-upper score comparisons.
    - `Asymptotics`: `TendsToZero` helpers, inverse-rate and inverse-square-root
      rate bridges, `1 / log n` and `log n / sqrt n` limit helpers,
      asymptotic-equivalence ratio/sandwich helpers, bounded-ratio-to-zero
      lemmas, nonnegative `C / n` domination, and order-closed limit comparison
      for real sequences.
    - `ExponentialBounds`: elementary `exp`/`log` inequalities for finite
      probability products, including `exp(-2/x) <= 1 - 1/x` for `x >= 2` and
      its finite-power form.
  - `EconCSLib.Foundations.Graph`
  - `EconCSLib.Foundations.Optimization`
    (`Approximation`, `Argmax`, `Certificate`, `FiniteSearch`,
    `LinearProgram`, `MoveGraph`, `ChoiceEquilibrium`, `BinaryChoice`,
    `Endpoint`)
    - `Approximation`: benchmark/dual upper-bound sandwich certificates for
      approximation and competitive-ratio proofs, including additive-error
      variants.
    - `Argmax`: finite argmax, pointwise maximization, average/expected
      objective wrappers, monotone and finite-linear expectation interfaces,
      and finite posterior-score decision optimality.
    - `Certificate`: feasible-value sets, maximizer/minimizer predicates,
      candidate-plus-upper-bound and candidate-plus-lower-bound certificates,
      and strict variants for uniqueness/structure proofs.
    - `FiniteSearch`: optimizer existence over nonempty finite feasible
      subtypes, decidable finite feasible predicates, and finite codes that
      cover a feasible region.
    - `LinearProgram`: standard finite maximization LPs with nonnegative
      variables and `Ax <= b`, primal/dual feasibility, finite weak duality,
      support/active-constraint scaffolds, and primal/dual optimality
      certificates.
    - `MoveGraph`: reusable exchange/local-move optimality, proving global
      maximization or minimization from reachability and objective monotonicity
      along feasible moves.
    - `ChoiceEquilibrium`: static choice-equilibrium data, feasibility,
      best-response, and consistency projections.
    - `BinaryChoice`: two-action no-profitable-deviation predicates,
      projections from static choice equilibria, and threshold/tiebreak
      consequences for binary choice rules.
    - `Endpoint`: one-dimensional endpoint-move calculus from derivative
      signs, first/last-zero stopping lemmas, and one-sided local
      improvement/decrease steps for cutoff and interval-endpoint proofs.
    - Roadmap: [`docs/OPTIMIZATION_LIBRARY_ROADMAP.md`](OPTIMIZATION_LIBRARY_ROADMAP.md)
      tracks finite feasible search, exchange optimality, LP certificates,
      convexity/Jensen wrappers, threshold policies, minimax/Yao certificates,
      and asymptotic allocation profiles.
  - `EconCSLib.Foundations.Probability`
    (`FiniteExpectation`, `FiniteMixture`, `FiniteLabel`, `FiniteSupportMGF`, `Kernel`, `Conditional`,
    `LargeDeviations`, `OrderStatistics`, `RealDistribution`, `MarkovChain`, `CTMC`, `MDP`,
    `RenewalReward`, `ContinuousReward`, `Gaussian`, `StochasticDominance`, `MeasureInequalities`,
    `Occupancy`, `Admissions`, `FairCoin`, `Weighted`, `WithoutReplacement`)
    - `FiniteExpectation`: finite PMF expectations/probabilities, relabeling,
      product-uniform decompositions, event-probability congruence, finite
      identical-product PMFs and all-coordinate event probabilities,
      singleton/product atom probabilities, PMF map/bind probability and
      expectation decompositions,
      uniform product collision probabilities, prescribed-coordinate
      probabilities and collision probabilities for uniform finite functions,
      uniform event-probability relabeling, pointwise range relabeling for
      uniform finite function spaces and injective finite-function subtypes,
      expected finite-count linearity, finite union bounds, reciprocal-count
      perturbation bounds, expected-count lower bounds from uniformly likely
      finite subfamilies, finite-PMF variance, second-moment formulas for
      indicator counts, pairwise-negative-correlation variance bounds, and
      Chebyshev lower-tail wrappers.
    - `FiniteMixture`: binary PMF mixtures, finite event shares, indexed
      positive-event-or-blank splits, blank-on-zero-share indexed values,
      positive-share mixture cancellation, PMF pushforward support lemmas, and
      raw-relevance equivalences for event-share binary mixtures.
    - `FiniteLabel`: finite-label indicator integrals, label shares, aggregate
      score masses, pointwise posterior-simplex API, bounded finite-label
      score integrability, simplex mass-sum identities, finite-label MAE
      bounds/integrability, and the bridge from finite PMF expectations to the
      abstract `Decision.FiniteLinearExpectation` optimizer interface.
    - `Kernel`: finite prior/signal-kernel joint laws and signal marginals,
      real signal probabilities, posterior expectation formulas,
      denominator-clearing and constant-one posterior identities, posterior
      nonnegativity/upper/interval bounds, and finite law-of-iterated
      expectation for kernel joint laws.
    - `Conditional`: finite PMF conditional expectations and conditional
      probabilities, denominator-clearing and constant-one conditional
      expectation identities, indicator-expectation bounds,
      nonnegativity/upper/interval conditional-expectation bounds,
      event-intersection/product/complement formulas,
      congruence of conditional target events on the conditioning event,
      full conditional-probability congruence for equivalent conditioning
      events, conditioning-on-sure-event simplification,
      nested-event product lower bounds from per-step conditional lower bounds,
      finite-state conditional-mixture/refinement upper bounds and equalities,
      and the algebraic bridge from conditional negative dependence to pairwise
      negative correlation.
    - `MeasureInequalities`: real-valued measure/probability wrappers,
      finite-subset mass transfer, positivity bridges from nonzero finite
      `ENNReal` mass to real-valued mass, positive finite `withDensity` mass,
      finite-intersection probability lower bounds, and Hoeffding-style
      independent bounded-sum bounds.
    - `ContinuousReward`: accepted-set mass/time/reward primitives over
      positive real domains, renewal-reward and average-reward aliases, and
      positive-domain bridges from zero accepted time to zero accepted mass.
    - `Gaussian`: Gaussian location-scale standardization, an abstract
      standard-normal CDF/density API, conjugate one-signal posterior
      precision/variance/mean formulas, posterior-mean monotonicity, finite
      signal-family posterior mean monotonicity, posterior weights, and
      posterior-mean law wrappers, posterior-variance reduction under finite
      signals, nonzero-noise-mean signal centering, posterior/raw-signal
      threshold conversion, positive-affine location-scale transformations,
      threshold pass-probability monotonicity in cutoffs and means,
      finite-mixture tail mass/capacity certificates, and a hazard-rate
      certificate boundary with location-scale tail positivity, density/tail
      hazard conversion, upper-tail conditional mean monotonicity, and
      finite-mixture admitted-mean accounting for GLM/LG-style testing papers.
    - `FiniteSupportMGF`: finite-support MGF/log-MGF algebra, Legendre
      objectives, rate-function scaffolding, and finite rating-scale LDP model
      wrappers for rating-system large-deviation proofs.
    - `LargeDeviations`: negative normalized log-decay rates, exact
      exponential-rate certificates, eventual exponential upper-bound
      and lower-bound certificates, conversion from exact rates to weaker
      upper/lower bounds, finite weighted-sum aggregation, and pairwise
      ranking-error aggregation certificates, with aggregate lower bounds from
      a single positive-weight component or one certified pairwise error.
    - `OrderStatistics`: top-`k` expected-value oracles, marginal top-`k`
      values, diminishing/nonnegative marginal predicates, finite-type
      scaled-marginal limit certificates, and eventual multiplicative marginal
      sandwiches and strict marginal comparisons from scaled weight gaps for
      diversity-aware recommendation style order-statistic proofs.
    - `RealDistribution`: lower CDF mass, upper-tail mass, CDF/tail
      monotonicity, `ProbabilityTheory.cdf` identification, and upper-tail
      complement formulas plus threshold/capacity certificates for real-valued
      threshold and order-statistic proofs.
    - `Weighted`: finite normalized weighted PMFs over nonnegative real
      weights, filtered/excluding-set weighted PMFs, available-mass splitting,
      available-subtype weighted PMFs, full-support available-mass positivity,
      constant-scaling of available mass, and the `p_w / (1 - prevMass)` atom
      formula for finite without-replacement deferred-decision draws.
    - `WithoutReplacement`: recursive finite weighted sampling without
      replacement over structurally fresh lists, cons/tail projection helpers,
      finite prefix sets, omission-event positivity under full support,
      first/head-tail/conditional-tail laws, atom product and atom-sum event
      formulas, positive constant-scaling invariance for event and conditional
      probabilities, pointwise-weight convergence for fixed fresh-list events,
      and the positive prefix-set next-draw law
      `finiteWithoutReplacementPMF_prefixSet_conditional_next_prob_excluding`.
    - `Occupancy`: used/empty-bin sets, ordered first-hit balls and first-hit
      cardinality, occupancy PMF, reciprocal empty-bin expectations, used-bin
      subset/equality comparisons, bin/domain relabeling for used and empty
      bins, one-ball recurrence bounds.
  - `EconCSLib.Foundations.Econometrics`
    (`RatingModels`)

## Applications

- Entrypoint: `EconCSLib.Applications.RecommenderSystems`
- Modules:
  - `Policy`, `Allocation`
  - `Classwise`, `PolicyAveraging`

## Mechanism Design

- Entrypoint: `EconCSLib.MechanismDesign.Auctions`
- Modules:
  - `DigitalGoods`, `Position`, `Combinatorial`
  - `EconCSLib.MechanismDesign.Auctions.MainTheorems`

## Markets

- Entrypoint: `EconCSLib.Markets.Matching`
- Modules:
  - `Matching/Basic`, `Matching/DeferredAcceptance`, `Matching/ManyToOne`
    - `Basic`: one-to-one assignment API, side swapping, woman-side relabeling
      of assignments, stability, and stability invariance under side swapping
      and woman-side relabeling.
    - `DeferredAcceptance`: one-to-one DA, strict/all-acceptable domains,
      proposer optimality, uniqueness of men-optimal stable matchings,
      women-proposing role reversal, women-optimality, women-pessimality,
      men-pessimality of women-proposing DA, stability, DA completeness, and
      stable-completeness on equal-size all-acceptable markets.

## Learning

- Entrypoint: `EconCSLib.Learning.Bandits.ThompsonSampling`
- Modules:
  - Bayesian-bandit primitives and posterior update lemmas used by papers

## Algorithms

- Entrypoints: `EconCSLib.Algorithms.Online`, `EconCSLib.Algorithms.Complexity.Yao`
- Modules:
  - `Online/AdWords`, `Online/Regret`

## Social Choice

- Entrypoint: `EconCSLib.SocialChoice.FairDivision`
- Modules:
  - `FairDivision/IndivisibleGoods`, `LMMSAlgorithm`

## Navigation tips

- Use the domain entrypoint as the first import from that area.
- Then import narrower modules only when you need paper-specific helper lemmas.
- New reusable theorems should land under `EconCSLib/`; paper-specific proof
  code should remain in `papers/`.
