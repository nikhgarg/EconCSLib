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
    `Sequence`, `Asymptotics`, `ConvexCombination`, `IntervalCrossing`,
    `EpsilonContinuity`, `PositiveDenominator`, `AffineThreshold`,
    `ThresholdCharacterization`, `ExponentialBounds`
    - `FiniteSum`: finite weighted-sum bounds, injective subfamily sum
      comparisons, weighted-share race bounds, finite averaging/cardinality
      lower bounds, Cauchy-Schwarz, ordered-pair double-sum regrouping by an
      injective key, pairwise cross-ratio-to-weighted-average comparisons, and
      finite telescoping/crossing helpers.
    - `FiniteRanking`: finite-set ranking by real scores with deterministic
      tie-breaking, lower/upper rank prefix sets, rank-prefix cardinalities,
      rank-prefix monotonicity, and lower-vs-upper score comparisons.
    - `Asymptotics`: `TendsToZero` helpers, inverse-rate and inverse-square-root
      rate bridges, `1 / log n` and `log n / sqrt n` limit helpers,
      asymptotic-equivalence ratio/sandwich helpers, bounded-ratio-to-zero
      lemmas, fixed finite-sum assembly over a common scale, negligible
      remainder addition on that scale, nonnegative `C / n` domination,
      finite-prefix replacement for zero-convergent schedules, and
      order-closed limit comparison for real sequences.
    - `ConvexCombination`: two-point weighted averages, denominator
      positivity from positive/nonnegative weights, componentwise above/below
      target comparisons, weighted-gap sign comparisons, and continuity of
      parameterized weighted averages. Use this for LG-style pooled estimates
      before adding paper-local fraction algebra.
    - `ThresholdCharacterization`: one-dimensional monotone cutoff lemmas,
      lower/upper cutoff strategies, compact interval crossings, unbounded
      continuous strict-monotone/strict-antitone crossing, and strict-antitone
      capacity cutoffs with the upper-region characterization
      `{z | f z <= level} = {z | cutoff <= z}`.
    - `ExponentialBounds`: elementary `exp`/`log` inequalities for finite
      probability products, including `exp(-2/x) <= 1 - 1/x` for `x >= 2` and
      its finite-power form.
  - `EconCSLib.Foundations.Graph`
  - `EconCSLib.Foundations.Optimization`
    (`Approximation`, `Argmax`, `Certificate`, `FiniteSearch`,
    `LinearProgram`, `MoveGraph`, `ChoiceEquilibrium`, `ChoiceEquilibriumAE`,
    `BinaryChoice`, `BinaryChoiceAE`, `Endpoint`)
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
    - `ChoiceEquilibriumAE`: almost-everywhere choice-equilibrium data for
      continuous or mixed information laws, including a constructor from
      pointwise feasibility and best response outside a null exception set.
    - `BinaryChoice`: two-action no-profitable-deviation predicates,
      projections from static choice equilibria, and threshold/tiebreak
      consequences for binary choice rules.
    - `BinaryChoiceAE`: almost-everywhere binary no-profitable-deviation
      predicates, conversions to and from raw Boolean best-response clauses,
      off-null-set constructors, a.e. projection from choice equilibria,
      no-tie/null-tie threshold identification, and affine cutoff consequences.
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
    `RenewalReward`, `ContinuousReward`, `Gaussian`, `BivariateGaussian`,
    `StochasticDominance`, `MeasureInequalities`,
    `Occupancy`, `Admissions`, `FairCoin`, `Weighted`, `WithoutReplacement`,
    `RandomUtility`, `RandomUtilityDensity`)
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
      finite subfamilies, event-indicator expectation upper bounds, independent
      pair indicator-event factorization, finite-PMF variance, second-moment
      formulas for indicator counts, pairwise-negative-correlation variance
      bounds, and Chebyshev lower-tail wrappers.
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
      boundary-null a.e. congruence for functions, predicates, Boolean
      indicators, set indicators, and strict/weak real cutoffs, positive-mass
      contradictions for a.e. weak/strict inequalities, selected-below-
      reference a.e. implication contradictions and cutoff-event positive-mass
      transfers, null
      symmetric-difference congruence for adding/removing common context sets
      and merging touching intervals/rays up to null endpoints, plus
      finite-intersection probability lower bounds and Hoeffding-style
      independent bounded-sum bounds.
    - `ContinuousReward`: accepted-set mass/time/reward primitives over
      positive real domains, reward/time union and difference formulas,
      measure-zero component simplifications, average-reward comparison from
      pointwise inequalities, renewal-reward and average-reward aliases,
      add/remove marginal renewal-rate comparisons, zero-component
      union/difference invariance, and positive-domain bridges from zero
      accepted time to zero accepted mass.
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
      hazard conversion, upper-tail conditional mean monotonicity, hazard
      domination of positive standardized thresholds, upper-tail mean-above-
      threshold certificates, positive Gaussian mass from a threshold to its
      upper-tail conditional mean, and finite-mixture admitted-mean accounting
      for GLM/LG-style testing papers.
    - `BivariateGaussian`: correlated standard-Gaussian product laws,
      coordinate projections/no-atoms, Owen affine standardization and
      vertical/horizontal boundary-zero helpers, plus independent Gaussian pair
      measures with arbitrary standard deviation, canonical variance-`1/2`
      scaling, strict winner-below-cutoff and both-below-cutoff events, and the
      reusable strict conditional winner-ratio scaling bridge for KR-style RUM
      Gaussian reductions.
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
      scaled-marginal limit certificates, bottom-indexed
      `μ(rank, sampleSize)` mean bridges, and eventual multiplicative
      marginal sandwiches and strict marginal comparisons from scaled weight
      gaps for diversity-aware recommendation style order-statistic proofs.
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
    - `RandomUtility`: additive-noise well-ordering predicates, Gaussian and
      Laplacian density kernels, one-coordinate contraction geometry,
      three-alternative top/bottom preservation and swap-middle geometry, and
      pointwise `swap12`/`swap23` density-product comparisons for continuous
      RUM proofs.
    - `RandomUtilityDensity`: three-coordinate additive-RUM score densities,
      density measurability/positivity/normalization helpers, finite atom
      density-swap mass comparisons, and continuous `withDensity` swap
      comparisons for measure-preserving score-coordinate maps.
  - `EconCSLib.Foundations.Econometrics`
    (`RatingModels`)

## Applications

- Entrypoint: `EconCSLib.Applications.RecommenderSystems`
- Modules:
  - `Policy`, `Allocation`, `AllocationSequence`
  - `Classwise`, `PolicyAveraging`
  - `Allocation`: finite integer allocations, total/support/share/objective
    primitives, one-unit move/marginal interfaces, weighted forward/backward
    marginals, exchange conditions, fixed-total optimality, exact exchange
    objective accounting, finite FOC lemmas, diminishing-returns marginal
    monotonicity, large scaled-gap-to-FOC contradiction bridges, finite-prefix
    scaled-count bounds from positive weight floors, share nonnegativity and
    sum-to-one facts, finite count-pigeonhole facts, plus the generic pairwise
    scaled-count to weighted target count-closeness bridge, scaled-count to
    target-share closeness bridges, and uniform-average count-balance bridges
    `Allocation.exists_count_gt_of_card_mul_lt_total` and
    `Allocation.count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded`,
    `Allocation.count_abs_sub_uniform_average_le_C_of_pairwise_bounded`, and
    `Allocation.count_abs_sub_uniform_average_le_one_of_pairwise_balanced`;
    it also includes `Allocation.FeasibleCode` and
    `Allocation.exists_isOptimalAtTotal` for finite fixed-total count-objective
    maximization.
  - `AllocationSequence`: feasible and optimal fixed-total allocation
    sequences, uniform target-share approximation, coordinatewise convergence
    to target profiles, asymptotic profile targets over generic fixed-total
    objectives, and reusable endpoints turning sublinear pairwise scaled-count
    bounds, FOC large-gap dominance, or floor-aware/eventual FOC dominance into
    asymptotic profile convergence. Use
    `Allocation.PairwiseScaledSublinearProfileCertificate`,
    `Allocation.PairwiseScaledSublinearFOCCertificate`, and
    `Allocation.PairwiseScaledEventualSublinearFOCCertificate` when a paper
    wants certificate-shaped hypotheses with conversion methods.

## Mechanism Design

- Entrypoint: `EconCSLib.MechanismDesign.Auctions`
- Modules:
  - `DigitalGoods`, `Combinatorial`
    - `DigitalGoods`: prior-free digital-goods auction primitives and
      paper-facing revenue/truthfulness support.
    - `Combinatorial`: direct combinatorial auctions, generalized Vickrey
      auctions, single-minded bid profiles, weighted set-packing encodings,
      LOS02 greedy allocation/payment support, and abstract reduction/complexity
      wrappers.

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

- Entrypoints: `EconCSLib.Algorithms.Online`,
  `EconCSLib.Algorithms.Complexity.Classes`,
  `EconCSLib.Algorithms.Complexity.Yao`
- Modules:
  - `Online/AdWords`, `Online/Regret`
  - `Complexity/Classes`: abstract decision-problem, reduction,
    reduction-closed hardness, randomized-class collapse, and
    complexity-consequence interfaces for paper-local reductions
  - `Complexity/Yao`: finite expectation algebra for Yao-style lower-bound
    certificates

## Social Choice

- Entrypoint: `EconCSLib.SocialChoice`
- Narrow entrypoints: `EconCSLib.SocialChoice.FairDivision`,
  `EconCSLib.SocialChoice.Ranking`
- Modules:
  - `FairDivision/IndivisibleGoods`, `LMMSAlgorithm`
  - `Ranking/Basic`, `Ranking/Kendall`, `Ranking/Probability`,
    `Ranking/Mallows`, `Ranking/MallowsRankFactorization`,
    `Ranking/MallowsSequential`, `Ranking/Payoff`, `Ranking/RankPower`,
    `Ranking/Score`, `Ranking/Sequential`, `Ranking/SequentialPayoff`
    - `Ranking/Basic`: finite candidate universes with at least two
      candidates, full rankings as permutations, top-two choices, top-two
      swaps, rank lookup, and the "best remaining after one candidate is
      removed" primitive used by KR21-style sequential selection proofs.
    - `Ranking/Kendall`: inversion predicates/finsets, Kendall tau distance,
      first/second-choice deletion formulas, relabeling through `cycleRange`
      and `cycleIcc`, center-transposition invariance, and center-order value
      gap predicates.
    - `Ranking/Probability`: discrete measurable-space instance for ranking
      spaces, `firstChoiceProb`, pushforward PMFs from continuous ranking maps,
      and event-probability bridges for first-choice and best-remaining events.
    - `Ranking/Mallows`: finite Mallows weights and partition functions,
      normalized Mallows-law specifications, first/first-second/pair-correct
      and pair-wrong weights/probabilities, and finite partition/probability
      normalization identities.
    - `Ranking/MallowsRankFactorization`: assumption-driven Mallows
      rank-factorization packages and algebra for first-choice tails,
      removal-renormalized rank sums, and first-weight prefixes. Concrete
      source-specific factorization constructors stay in paper files until
      their fiber decompositions are reusable.
    - `Ranking/MallowsSequential`: Mallows best-in-feasible-set fiber weights,
      pair/correct-wrong fiber identities, swap-reindexed fiber sums,
      fiber-partition normalization, expected best-in-set payoff normalization,
      and the cross-ratio bridge from Mallows fibers to expected best-in-set
      dominance.
    - `Ranking/Payoff`: first-choice miss probabilities, top-vs-runner-up
      value gaps, first/second-mover utility primitives, pair-lifted
      reranking gains, first-choice gap masses, collision-probability
      differences, finite first-choice fiber decompositions, and
      first-mover-law switch payoff identities for ranking laws.
    - `Ranking/RankPower`: finite geometric rank-power sums, prefix sums,
      removal-renormalized rank sums, best-after-removal rank weights,
      positivity/closed-form geometric identities, and rank-power
      cross-ratio helpers used by Mallows rank-factorization proofs.
    - `Ranking/Score`: pure three-score ranking maps for three-candidate
      comparisons, concrete score-induced rankings, no-tie and score-order
      predicates, first/second-choice simplification, best-remaining-after-one
      simplification, and score-order implications from first-choice or
      best-remaining outcomes.
    - `Ranking/Sequential`: probability-free best-in-set and
      candidate-position swap helpers for sequential choice proofs, including
      `bestInSet`, rank-minimality/membership lemmas, center-rank relabeling,
      `swapCandidatePositions`, its involutive equivalence, rank extensionality
      helpers, deterministic best-in-set value improvement from correcting an
      inverted pair, and adjacent-correction reachability/monotonicity
      predicates such as `AdjacentSwapImproves`, `AdjacentCorrection`,
      `WeakBruhatLe`, and `SwapImprovesOn`; it also owns bounded prefix-cut
      indicators such as `deleteFirstChoicePrefixCut`,
      `bestInSetPrefixCutIndicator`, `centerPrefixCutValue`, and
      `adjacentSwapImproves_bestInSetPrefixCutIndicator`.
    - `Ranking/SequentialPayoff`: finite PMF expectations of the best feasible
      candidate, including `expectedBestInSet`, `expectedBestAfterRemoval`,
      and full-set/singleton/removed-singleton simplification lemmas.

## Navigation tips

- Use the domain entrypoint as the first import from that area.
- Then import narrower modules only when you need paper-specific helper lemmas.
- New reusable theorems should land under `EconCSLib/`; paper-specific proof
  code should remain in `papers/`.
