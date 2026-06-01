# Paper Map

## 1. Algorithmic Monoculture and Social Welfare

Implemented or scaffolded modules:

- `Monoculture/README.md`
- `Monoculture/MainTheorems.lean`
- `Monoculture/Basic.lean`
- `Monoculture/Expectation.lean`
- `Monoculture/Game.lean`
- `Monoculture/PaperDefinitions.lean`
- `Monoculture/RerankingGain.lean`
- `Monoculture/ConditionalForm.lean`
- `Monoculture/WelfareDecomposition.lean`
- `Monoculture/FirstChoice.lean`
- `Monoculture/FirstChoiceDecomposition.lean`
- `Monoculture/FiberSigns.lean`
- `Monoculture/WeakCompetition.lean`
- `Monoculture/Kendall.lean`
- `Monoculture/Mallows.lean`
- `Monoculture/MallowsSupport.lean`
- `Monoculture/MallowsCenterCertificate.lean`
- `Monoculture/MallowsFiniteLemmas.lean`
- `Monoculture/Family.lean`

Main current milestones:

- the finite-sum Equation-(3) reranking-gain identity
- the disagreement-event conditional reformulation
- the welfare decomposition linking reranking gain to welfare
- candidate-sum decompositions for the paper definitions
- center-fiber positivity lemmas
- top-two-swap Mallows support lemmas proving center miss probability is
  positive and center first-choice probability is below one
- `CenterMallowsCertificate`, a reduced Mallows/Theorem-3 certificate interface
- direct certificate-to-paper theorem
  `MallowsComparison.paperHypotheses_of_centerMallowsCertificate`
- constructors from finite gap-mass sign inequalities into
  `CenterMallowsCertificate`
- weight-level Mallows certificate
  `MallowsComparison.CenterMallowsWeightCertificate`
- denominator-cleared finite-sum Mallows certificate
  `MallowsComparison.CenterMallowsFiniteSumCertificate`
- equivalence between normalized candidate sums and denominator-cleared finite
  sums through
  `MallowsSpec.firstChoice_miss_gap_sum_pos_iff_weight_sum_pos`,
  `MallowsComparison.firstChoice_collision_gap_sum_pos_iff_cross_weight_sum_pos`,
  and
  `MallowsComparison.centerMallowsFiniteSumCertificate_of_candidateSumCertificate`
- pointwise finite-sum theorem
  `MallowsComparison.theorem3_pointwise_of_centerMallowsFiniteSumCertificate`
- cleared-denominator product-sign Mallows certificate
  `MallowsComparison.CenterMallowsProductCrossWeightCertificate`
- direct finite-inequality-to-paper theorem
  `MallowsComparison.paperHypotheses_of_centerMallowsProductCrossWeightCertificate`
- reduced product-sign certificate
  `MallowsComparison.CenterMallowsReducedProductCrossWeightCertificate`
- pointwise paper-facing theorem
  `MallowsComparison.theorem3_pointwise_of_centerMallowsReducedProductCrossWeightCertificate`

Next target:

- if continuing this track, encode concrete family-regularity assumptions that
  produce the theorem-1 witness `θA > θH` from paper-relevant properties of `F`
  (the paper-facing target surface is currently complete).

## 2. User-item Fairness Tradeoffs In Recommendations

Implemented or scaffolded modules:

- `UserItemFairness/README.md`
- `UserItemFairness/MainTheorems.lean`
- `UserItemFairness/Basic.lean`
- `UserItemFairness/Optimization.lean`
- `UserItemFairness/Symmetry.lean`
- `UserItemFairness/LPReduction.lean`
- `UserItemFairness/ReductionPreservation.lean`

Main current milestones:

- exact definitions of user/item utility and fairness functionals
- `S_symm`-style user-type machinery
- sparse-support target propositions
- reduced type-weighted optimization scaffolds
- pointwise preservation lemmas for user-side utility under lifted policies
- exact item-side preservation under lifted reduced policies
- minimum user-fairness and item-fairness preservation under lifted policies
- every type-symmetric user policy has a reduced representative preserving both
  fairness functionals exactly
- symmetric user-level item-fairness attainable values equal reduced
  item-fairness attainable values
- symmetric user-level optimal item fairness equals reduced optimal item
  fairness
- conditional reduced-optimum-to-original-optimum theorem
  `ReductionWitness.isOptimalAtLevel_liftedPolicy_of_reduced`
- conditional symmetric-original-optimum-to-reduced-optimum theorem
  `ReductionWitness.exists_reducedOptimalAtLevel_of_original_symmetric_optimal`

Next targets:

- prove original/reduced optimal-value equality, or restrict the theorem to the
  symmetric feasible region
- sparse-support proofs

## 3. Reconciling The Accuracy-Diversity Trade-off In Recommendations

Implemented or scaffolded modules:

- `AccuracyDiversity/README.md`
- `AccuracyDiversity/MainTheorems.lean`
- `AccuracyDiversity/Basic.lean`
- `AccuracyDiversity/Representation.lean`
- `AccuracyDiversity/TopKOracle.lean`
- `AccuracyDiversity/Bernoulli.lean`
- `AccuracyDiversity/Optimization.lean`
- `AccuracyDiversity/Exchange.lean`
- `AccuracyDiversity/Examples.lean`

Main current milestones:

- count allocations over finite item types
- representation shares and target homogeneity profiles
- a generic consumption-constrained objective
- an abstract top-`k` oracle interface
- Bernoulli satisfaction closed forms and marginal-return facts
- theorem-target scaffolds for finite and asymptotic claims
- one-step exchange targets for finite count-allocation optimality
- top-`k` oracle marginal assumptions instantiate generic consumption-model
  marginal assumptions
- exact one-step exchange objective accounting
- finite exchange-improvement theorem
  `ConsumptionModel.exchangeImprovementTarget`
- no-profitable-exchange theorem at finite optima
  `ConsumptionModel.noProfitableExchangeAtOptimumTarget`
- generic finite first-order exchange inequality
  `ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum`
- Bernoulli first-order inequality
  `BernoulliSatisfactionModel.forwardMarginal_le_backwardMarginal_of_optimum`
- two-type objective/total expansions and two-type Bernoulli exchange
  inequalities

Next targets:

- discrete top-`k` oracle instantiations
- asymptotic homogeneity from finite exchange inequalities

## 4. Approximately Fair Allocations Of Indivisible Goods

Implemented modules:

- `EconCSLib/FairDivision/README.md`
- `EconCSLib/FairDivision/MainTheorems.lean`
- `EconCSLib/FairDivision/IndivisibleGoods.lean`

Main current milestones:

- finite bundles, allocations, monotone valuations, envy, envy-freeness, and
  bounded envy
- exact finite allocation predicate `IsAllocationOf`
- local preservation lemmas for adding a good to an unenvied owner
- explicit envy graph predicates and the acyclic-source theorem
- bounded-envy existence theorem through
  `exists_envyBounded_allocation_of_acyclicReduction`
- self-value potential maximization for finite allocations
- explicit envy-cycle permutation seam and finite bounded-envy theorem through
  `exists_envyBounded_allocation_of_envyCyclePermutationExtraction`
- finite closed-walk extraction in transitive closure through
  `hasTransitiveEnvyCycleExtraction_of_finite`
- simple-cycle list seam and finite bounded-envy theorem through
  `exists_envyBounded_allocation_of_envyCycleListExtraction`
- generic shortest-closed-walk extraction of a nodup simple cycle through
  `EconCSLib.Graph.exists_simple_cycle_list_of_stepCycle`
- finite simple-cycle extraction through
  `hasEnvyCycleListExtraction_of_finite`
- finite paper-level bounded-envy theorem
  `exists_envyBounded_allocation_of_finite`
- paper-facing theorem alias `lmms_theorem_2_1_finite`
- maximum-marginal finite theorem
  `lmms_theorem_2_1_finite_maxMarginal`

Next target:

- add an executable version of the LMMS iterative algorithm, and then connect
  the existence theorem to EF1-style corollaries if desired

## 5. Auction Theory Test-of-Time Papers

Implemented modules:

- `EconCSLib/Auction/README.md`
- `EconCSLib/Auction/MainTheorems.lean`
- `EconCSLib/Auction/DigitalGoods.lean`
- `EconCSLib/Auction/Position.lean`
- `EconCSLib/Auction/Combinatorial.lean`

Main current milestones:

- unlimited-supply digital-goods auction interface
- quasilinear utility, DSIC, individual rationality, and no-positive-transfer
  predicates
- posted-price truthfulness, individual-rationality, and no-positive-transfer
  theorems
- digital-goods revenue, single-price revenue, sale-count, and fixed-price
  benchmark certificate predicates
- finite bidder-value candidate benchmark and own-erased-threshold DSIC theorem
- arbitrary feasible fixed-price revenue dominated by bidder-value benchmark,
  yielding the two-winner fixed-price benchmark under nonempty feasibility
- deterministic RSOP-style cross-sample candidate threshold truthfulness
- nonnegative-offer cross-sample DSIC/NPT and uniform partition-average revenue
  nonnegativity
- explicit RSOP approximation certificate interface against `F^(2)`
- own-bid-independent threshold-price auction DSIC/IR/NPT theorem
- finite position-auction outcomes with utility, revenue, welfare, and
  feasibility predicates
- position-mechanism truthfulness/Nash predicates, slot-envy-freeness, and
  concrete two-slot GSP non-truthfulness witnesses
- concrete sorted three-bidder/two-slot GSP mechanism-level
  non-truthfulness theorem
- local-envy-free assigned-slot deviation certificate for position outcomes
- direct combinatorial-auction interface reusing fair-division bundles and
  allocations
- feasible partial bundle allocations, single-minded bidder valuations, and a
  reject-all truthful baseline theorem
- normalized-profile critical-price truthfulness and pairwise-disjoint
  accepted-set feasibility for single-minded bidders
- target-bundle threshold allocation feasibility from pairwise-disjoint winners

Next targets:

- prove the RSOP approximation certificate lower-bounding uniform
  partition-average revenue against `F^(2)` for a concrete ratio
- generalize from the concrete sorted three-bidder/two-slot GSP mechanism to
  finite ordered slots, then add symmetric Nash equilibrium and
  revenue/welfare comparison predicates for the 2018 position-auction papers
- formalize the greedy single-minded combinatorial-auction rule, its
  pairwise-disjoint accepted-set invariant, and own-report-independent critical
  prices for the 2017 paper

## 6. AdWords And Generalized Online Matching

Implemented modules:

- `EconCSLib/Online/README.md`
- `EconCSLib/Online/MainTheorems.lean`
- `EconCSLib/Online/AdWords.lean`
- `EconCSLib/Online/AdWordsExtensions.lean`
- `EconCSLib/Online/AdWordsLowerBound.lean`
- `EconCSLib/Decision/Yao.lean`

Main current milestones:

- finite AdWords instances with budgets and bids
- offline assignments, spend, revenue, budget feasibility, residual budget, and
  feasible next-query assignment predicates
- finite feasible-assignment set and offline optimum existence theorem
- revenue/spend accounting and total-budget upper bound for feasible revenue
- Balance/MSVV used-budget fraction, discount factor, scaled bid, feasible
  advertiser set, and next-query maximizing-choice existence theorem
- named MSVV ratio `1 - 1/e`, auxiliary exact certificate wrappers, and the
  final paper-facing small-bids limiting theorem for the Balance run
- slack-score dual-feasibility builder connecting Balance scores to LP dual
  covering constraints
- finite max-slack query dual construction for dual-feasible LP solutions
- assignment-induced MSVV dual variables from spent fractions
- normalized MSVV dual-fitting variables and the identity that
  `msvvRatio * normalized slack = Balance score`
- final finite objective-bound certificate interfaces for the Balance/MSVV run
- online history state/fold and feasibility preservation for any feasible choice
  rule, including the canonical Balance/MSVV choice rule
- history support invariants showing final assignments only use query IDs that
  appeared in the input history
- spend/spent-fraction/MSVV-dual monotonicity along feasible online histories
- final-slack-to-earlier-Balance-score comparison
- non-exhausted-query beta charge bound from the Balance maximizer
- exhausted-advertiser alpha/slack charge from the small-bids boundary
- mixed max-slack query-dual bound by chosen Balance score plus a max-bid
  small-bids error
- normalized recursive history-summed beta charge and finite query-dual sum
  bound for nodup histories covering the query type
- online revenue trace and proof that recursive Balance charges are bounded by
  actual run revenue
- history-accounting certificate and concrete advertiser-alpha increment
  accounting for the finite small-bids theorem
- approximate objective-bound certificate and approximate competitive theorem
  with an explicit finite small-bids error term
- standard finite AdWords LP dual feasibility and objective
- fractional AdWords LP feasibility/revenue plus integral-to-fractional
  embedding
- weak duality: every feasible fractional assignment revenue is bounded by every
  dual-feasible objective
- first small-bids boundary lemma for blocked advertisers
- primal-dual competitive-ratio certificate interface and paper-facing theorem
  wrapper
- final small-bids limiting family interface
  `MsvvSmallBidsLimitFamily` and paper-facing theorem
  `paper_adwords_balance_msvv_competitive_of_small_bids_limit_family`
- Section 6 effective-bid reductions for arbitrary effective charges,
  click-through rates, delayed-entry/availability masks, and independent
  slot-query expansion
- Section 8 advertiser-weighted effective-bid reduction
- Section 7 finite Yao lower-bound lemma, uniform permutation distribution,
  explicit harmonic revenue cap, round-allocation and pointwise-allocation
  certificates, asymptotic additive-`δ` wrapper, and Theorem 9 b-matching
  family certificates

Paper-facing endpoint:

- The model-level limiting theorem is stated using
  `balance_msvv_approx_competitive_with_error_bound`, where the additive term
  is `ε * (Real.exp 1 + 1) * historyMaxBidSum`; the query-sum variant is
  `balance_msvv_approx_competitive_with_query_sum_error_bound`. The current
  delta-form endpoint is `balance_msvv_approx_competitive_up_to_delta`, with
  explicit small-bids threshold in
  `balance_msvv_approx_competitive_up_to_delta_of_smallBids_threshold`; the
  current limit-style endpoint is
  `balance_msvv_competitive_of_arbitrarily_smallBids_threshold`. Canonical
  `Fin n` wrappers use `List.finRange n` to discharge the nodup-cover
  assumptions and state the additive error directly as a finite query sum.
  The family-level wrappers
  `balance_msvv_finRange_family_eventually_up_to_delta` and
  `balance_msvv_finRange_family_eventually_up_to_delta_of_smallBids_threshold`
  now state the limiting seam over dependent query sizes `Fin (n k)`. The
  limit wrappers
  `balance_msvv_finRange_family_limit_competitive_of_error_eventually` and
  `balance_msvv_finRange_family_limit_competitive_of_smallBids_threshold` use
  `Sequence.SeqTendsTo` to turn eventual additive guarantees and convergence of
  both sides into a limiting inequality. The ordinary offline-optimum
  convergence wrappers state the final conclusion as
  `msvvRatio * optLimit ≤ revenueLimit`. The final public theorem is
  `paper_adwords_balance_msvv_competitive_of_small_bids_limit_family`, whose
  hypothesis is the explicit structure `MsvvSmallBidsLimitFamily`. Section 6
  variants and the Section 8 weighted-bid proposal reduce to transformed
  AdWords instances through `withEffectiveBids`, `withClickThroughRates`,
  `withAdvertiserWeights`, `withAvailability`, and `withSlots`; the slot-query
  expansion does not encode an additional same-page distinct-advertiser
  constraint. Theorem 9 is exposed through
  `paper_adwords_theorem9_no_randomized_algorithm_beats_msvv_ratio_of_certificate`
  and the permutation-specialized
  `paper_adwords_theorem9_no_randomized_algorithm_beats_msvv_ratio_of_permutation_certificate`;
  the revenue-bound wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_revenue_bound_certificate`
  names the paper's harmonic cap through `theorem9NormalizedRevenueUpperBound`.
  The round-allocation wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_round_allocation_certificate`
  proves that the paper's `E[q_ij]` inequalities imply that cap.
  The pointwise-allocation wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_pointwise_allocation_certificate`
  derives the expected-allocation certificate from realized per-permutation
  allocation variables using finite expectation algebra.
  The symmetry/capacity wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_symmetric_pointwise_allocation_certificate`
  proves the paper's per-position expected-allocation bound from ineligible
  zero allocation, per-round capacity, symmetry among eligible positions, and
  `theorem9EligibleBidders_card`.
  The relabeling wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_relabel_symmetric_pointwise_allocation_certificate`
  derives that eligible-position expected symmetry from pointwise input
  relabeling and uniform-permutation invariance.
  The observed-prefix wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_observed_prefix_allocation_certificate`
  derives the pointwise relabeling identity from the hard input's visible
  prefix, using `theorem9ObservedPrefix_mul_swap_eq`.
  The feasible observed-prefix wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_feasible_observed_prefix_allocation_certificate`
  derives position-level capacity and ineligible-zero facts from actual-bidder
  feasibility on the visible set.
  The harmonic-cap side is closed: `theorem9BidderSpendUpperBound_le_log_tail`
  proves the logarithmic tail-spend bound,
  `theorem9HarmonicLayerCountBound_of_pos` proves the finite layer-count
  estimate, `theorem9ExponentialGridUpperSum_le_msvvRatio` proves the finite
  geometric grid bound, and
  `paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta` exposes
  the eventual additive comparison to `1 - 1/e`.
  The asymptotic wrapper
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta`
  packages the large-market lower-bound statement from the deterministic
  round-allocation inequalities; the public family endpoint is
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_family_certificate`,
  with the closer pointwise family endpoint
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_pointwise_family_certificate`,
  symmetry/capacity endpoint
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_symmetric_pointwise_family_certificate`,
  and relabel-symmetry endpoint
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_relabel_symmetric_pointwise_family_certificate`,
  and observed-prefix endpoint
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_observed_prefix_family_certificate`,
  and feasible observed-prefix endpoint
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_observed_prefix_family_certificate`,
  plus the capped-payoff prefix-rule endpoint
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_prefix_rule_family`,
  and the concrete integral choice-rule endpoint
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family`
  and its realized-payoff bridge
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family_of_realized_revenue`.
  The finite Yao step and uniform permutation distribution are proved.

## 7. Bayesian Rating Fairness (ICWSM 2025)

Implemented modules:

- `ProducerFairness/README.md`
- `ProducerFairness/MainTheorems.lean`
- `ProducerFairness/PaperFacingTheorems.lean`
- `EconCSLib/Statistics/BinaryRating.lean`

Main current milestones:

- binary-rating posterior-mean model and derived bias/variance primitives are
  formalized
- Theorem 3.1 variance monotonicity and the strict interior variant are
  formalized with boundary counterexamples
- Theorem 3.2 shape claims (Jensen convexity/concavity, minimizer, maximizer) are
  formalized

Current status:

- the core corrected paper-facing theorem ladder is exposed in
  `ProducerFairness/PaperFacingTheorems.lean` and backed by
  `ProducerFairness/MainTheorems.lean`

## Shared Layer

Shared reusable code currently lives in:

- `EconCSLib/Graph/Cycle.lean`
- `EconCSLib/Math/PositiveDenominator.lean`
- `EconCSLib/Math/Sequence.lean`
- `EconCSLib/Decision/Yao.lean`
- `EconCSLib/FairDivision/IndivisibleGoods.lean`
- `EconCSLib/Auction/DigitalGoods.lean`
- `DecisionCore/FiniteExpectation.lean`
- `DecisionCore/FiniteSigns.lean`
- `DecisionCore/Policy.lean`
- `DecisionCore/Conditional.lean`
- `DecisionCore/Classwise.lean`
- `DecisionCore/Allocation.lean`

This is the first reusable core inside `EconCSLib` that future EC-style papers
should build on.
