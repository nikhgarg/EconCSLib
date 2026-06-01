# EC Test of Time Formalization Plan

This plan uses the official SIGecom Test of Time Award page as the source of
truth for the latest ten posted award years. As of April 23, 2026, the SIGecom
page lists winners through 2025, so the ten-year window here is 2016-2025.

Source: https://www.sigecom.org/award-tot.html

## Recommended First Paper

Start with the 2025 winner:

Richard J. Lipton, Evangelos Markakis, Elchanan Mossel, and Amin Saberi,
*On approximately fair allocations of indivisible goods*, EC 2004.

Why this is the best first candidate:

- It is finite and discrete: finite agents, finite indivisible goods, finite
  bundles, finite envy graph.
- Its first main theorem has a constructive proof with local invariants:
  repeatedly eliminate envy cycles, pick an unenvied agent, add one good, and
  preserve the maximum-envy bound.
- It builds primitives that many later EC papers need: valuations over bundles,
  allocations, envy, EF1/approximate envy-freeness, envy graphs, and allocation
  algorithms.
- The first target theorem can be decomposed into small Lean lemmas before the
  full algorithm is mechanized.

Immediate Lean target:

- Build `EconCSLib.FairDivision.IndivisibleGoods`.
- Prove local invariants for cycle rotation and adding a good to an unenvied
  agent.
- Next prove existence of an unenvied agent in any finite acyclic envy graph.
- Then assemble the iterative algorithm and the bounded-envy theorem.

Current implementation status:

- Added `EconCSLib.FairDivision.IndivisibleGoods`.
- Added finite bundles, allocations, monotone valuation profiles, envy,
  envy-freeness, bounded envy, marginal bounds, and "nobody envies owner".
- Added `IsAllocationOf` for exact finite allocations of a goods set.
- Proved basic envy equivalences and local invariants from the constructive
  proof: rotation weakly reduces a rotating agent's outgoing envy baseline,
  adding one good to an unenvied owner creates envy toward that owner bounded by
  the marginal bound, and adding one good to an unenvied owner preserves a global
  envy bound.
- Added the explicit directed envy graph interface:
  `EnvyEdge`, `AcyclicEnvyGraph`, and
  `exists_noOneEnvies_of_acyclicEnvyGraph`.
- Proved the reusable cycle-elimination local facts
  `envyBoundedBy_rotate_of_self_improves` and
  `isAllocationOf_rotate_of_bijective`.
- Proved the main bounded-envy induction theorem
  `exists_envyBounded_allocation_of_unenviedReduction`. This is Theorem 2.1's
  existence conclusion conditional on the paper's cycle-elimination/source step,
  packaged as `HasUnenviedReduction`.
- Added the sharper theorem
  `exists_envyBounded_allocation_of_acyclicReduction`, where the remaining
  theorem seam is specifically the paper's claim that envy-cycle elimination
  reaches an acyclic envy graph.
- Added the self-value potential machinery for finite cycle elimination:
  `selfValueSum`, `ImprovingBundleRotation`, `PotentialMaximal`, and
  `exists_potentialMaximal`.
- Added the explicit graph seam `EnvyCyclePermutation` and proved that an
  extractor for such cycles implies `HasAcyclicReduction`.
- Proved finite non-acyclicity gives a closed envy walk in transitive closure:
  `hasTransitiveEnvyCycleExtraction_of_finite`.
- Upgraded the repository to Lean/mathlib/CSLib `v4.30.0-rc2` and imported
  `Cslib.Foundations.Data.RelatesInSteps` for the next graph seam.
- Added `HasStepEnvyCycle` and `hasStepEnvyCycleExtraction_of_finite`, which
  convert the transitive-closure envy cycle into a positive-length
  step-indexed closed envy walk.
- Added `EnvyCycleList`, a nodup simple-cycle list interface based on
  `List.formPerm`, and proved that a list extractor implies the permutation
  extractor.
- Added the finite paper-level theorem
  `exists_envyBounded_allocation_of_envyCyclePermutationExtraction`, so the only
  remaining fair-division proof obligation is the pure finite graph extraction
  from non-acyclic envy graphs to explicit envy-cycle permutations.
- Added the list-facing theorem
  `exists_envyBounded_allocation_of_envyCycleListExtraction`; the remaining
  graph obligation can now be stated as extraction of a simple nodup cycle list
  from the closed transitive-cycle witness.
- Proved the pure finite graph extraction step:
  `exists_simple_cycle_list_of_stepCycle` converts a shortest positive closed
  step-walk into a nodup simple cycle list, and
  `hasEnvyCycleListExtraction_of_finite` instantiates it for finite envy graphs.
- Closed the finite paper-level existence theorem:
  `exists_envyBounded_allocation_of_finite`, with paper-facing alias
  `lmms_theorem_2_1_finite`.
- Added the maximum-marginal-value paper corollary:
  `maxMarginal`, `marginalBound_maxMarginal`, `maxMarginal_nonneg`, and
  `lmms_theorem_2_1_finite_maxMarginal`.
- Moved the closed-walk/simple-cycle extraction theorem into the reusable
  library module `EconCSLib.Graph.Cycle`; the LMMS paper file now applies that
  generic theorem.
- Implemented the actual LMMS algorithm as a functional `List.foldr` over the items in `EconCSLib.FairDivision.LMMSAlgorithm` (`lmmsAlgorithm`) and proved that its output is a valid allocation bounded by the maximum marginal value (`paper_lmms_algorithm_isAllocationOf_and_envyBoundedBy`).
- Verified with `lake build EconCSLib.FairDivision.IndivisibleGoods` and
  `lake build EconCSLib`.

## First Follow-On Paper Track

The first move beyond the 2025 fair-division paper is the 2021 Test-of-Time
digital-goods auction track:

- Added `EconCSLib.Auction.DigitalGoods`.
- Added an unlimited-supply `DigitalGoodsAuction` interface with quasilinear
  utility, dominant-strategy truthfulness, individual rationality, and
  no-positive-transfer predicates.
- Proved posted-price facts:
  `postedPrice_truthful`, `postedPrice_individuallyRational`, and
  `postedPrice_noPositiveTransfers`.
- Added revenue and fixed-price benchmark primitives:
  `DigitalGoodsAuction.revenue`, `singlePriceRevenue`, `saleCount`,
  `IsFixedPriceBenchmark`, and `IsTwoWinnerFixedPriceBenchmark`.
- Added the finite bidder-value candidate benchmark
  `finiteCandidateFixedPriceBenchmark`, with nonnegativity and candidate-price
  upper-bound lemmas.
- Proved the benchmark-reduction layer:
  `singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible`,
  `finiteCandidateFixedPriceBenchmark_isFixedPriceBenchmark_of_feasible`, and
  `finiteCandidateFixedPriceBenchmark_isTwoWinnerFixedPriceBenchmark_of_feasible`.
- Proved the posted-price revenue bridge
  `postedPrice_const_revenue_eq_singlePriceRevenue`.
- Added own-bid-independent threshold-price auctions and proved their DSIC/IR/NPT
  facts:
  `thresholdPriceAuction_truthful`,
  `thresholdPriceAuction_individuallyRational`, and
  `thresholdPriceAuction_noPositiveTransfers`.
- Added `eraseOwnBid`, `ownErasedThreshold`, and
  `ownErasedThresholdPriceAuction_truthful`, which directly models prices
  computed from all bids except the bidder's own report.
- Added the deterministic RSOP-style cross-sample skeleton
  `crossSampleCandidateThreshold` and proved
  `crossSampleCandidateThresholdPriceAuction_truthful`.
- Added the nonnegative-offer cross-sample skeleton
  `crossSampleCandidateOfferThreshold`, proved DSIC/NPT, and defined uniform
  average revenue over all deterministic partitions with
  `averageCrossSampleCandidateOfferRevenue_nonneg`.
- Added the explicit final approximation seam
  `CrossSampleOfferApproximationCertificate` and the conditional paper wrapper
  `paper_cross_sample_offer_competitive_of_certificate`.
- This creates reusable auction primitives for the 2021 digital-goods paper,
  2018 GSP/position-auction papers, and 2017 combinatorial-auction paper.

The auction-only continuation now covers three Test-of-Time auction tracks:

- 2021 digital goods/prior-free auctions:
  the deterministic fixed-price benchmark layer and deterministic cross-sample
  truthfulness/NPT skeleton are closed, including uniform average revenue over
  partitions. Next prove the RSOP approximation certificate lower-bounding that
  average revenue against `F^(2)` for a concrete ratio.
- 2018 GSP/position auctions:
  added `EconCSLib.Auction.Position`, including `PositionEnvironment`,
  `PositionOutcome`, `PositionMechanism`, revenue/welfare definitions, Nash and
  truthfulness predicates, slot-envy-freeness, and concrete two-slot GSP
  non-truthfulness witnesses
  `gspCounterexample_lowerBid_profitable` and
  `gspCounterexampleMechanism_not_truthful`. The concrete sorted
  three-bidder/two-slot GSP mechanism `gsp3TwoSlotMechanism` now has the
  mechanism-level non-truthfulness theorem `gsp3TwoSlot_not_truthful`. The
  local-envy-free outcome layer includes
  `PositionOutcome.NoProfitableAssignedSlotDeviation` and
  `paper_position_slot_envy_free_no_profitable_assigned_slot_deviation`.
- 2017 combinatorial auctions:
  added `EconCSLib.Auction.Combinatorial`, including direct bundle-value
  reports, direct combinatorial auctions, feasible partial allocations,
  single-minded valuations, and a reject-all truthful baseline theorem. The
  single-minded layer now includes normalized-profile critical-price
  truthfulness and pairwise-disjoint accepted-set feasibility via
  `targetBundleThresholdAuction_truthfulOn_singleMindedProfiles` and
  `singleMindedAllocation_feasible`. Target-bundle threshold allocation
  feasibility is packaged as
  `targetBundleThresholdAuction_feasible_of_pairwiseDisjoint`.

## Current AdWords / Online Matching Track

The 2024 Test-of-Time paper, Mehta-Saberi-Vazirani-Vazirani,
*AdWords and Generalized Online Matching*, is now the active single-paper track.

- Added `EconCSLib.Online.AdWords`.
- Added finite AdWords instances with advertiser budgets, query bids, offline
  assignments, spend, revenue, budget feasibility, residual budgets, and
  feasible next-query assignment predicates.
- Proved basic finite benchmark facts:
  `revenue_eq_sum_spend`,
  `revenue_le_totalBudget_of_feasible`,
  `exists_optimalAssignment`,
  `revenue_le_offlineOptimumValue`, and
  `offlineOptimumValue_le_totalBudget`.
- Added the Balance/MSVV scaled-bid primitives
  `spentFraction`, `balanceDiscount`, `msvvDualAlpha`, `slackScore`,
  `msvvRatio`, `balanceScore`, `feasibleAdvertisers`, and `IsBalanceChoice`,
  with existence of a maximizing Balance choice whenever at least one advertiser
  can accept the query.
- Proved the slack-score dual-feasibility builder
  `dualFeasible_of_slackScore_le_beta`, which is the LP side of the
  Balance/MSVV primal-dual proof.
- Added finite max-slack query duals via `maxSlackBeta` and proved
  `dualFeasible_maxSlackBeta`.
- Added assignment-induced MSVV advertiser duals
  `msvvAlphaFromAssignment` and proved `dualFeasible_msvvAssignment`.
- Added the normalized dual-fitting advertiser duals
  `msvvNormalizedAlphaFromAssignment` and proved
  `dualFeasible_msvvNormalizedAssignment`.
- Added the final finite objective-bound certificate interface
  `MsvvObjectiveBoundCertificate`, with paper-facing wrapper
  `paper_adwords_balance_msvv_competitive_of_objective_bound`.
- Added the online history layer:
  `HistoryState`, `stepHistoryState`, `runHistoryState`, `runAssignment`, and
  `balanceChoiceRule`, with feasibility preservation for every
  `ChoiceRuleFeasible` rule and for the canonical Balance/MSVV choice rule, plus
  "assigned only if seen in the history" support lemmas.
- Added run-monotonicity lemmas showing spend, spent fractions, and assignment
  induced MSVV advertiser duals are monotone over feasible online histories.
- Proved `final_slackScore_le_initial_balanceScore`, the bridge from final
  assignment-induced dual slack to earlier Balance scores.
- Proved the normalized scaling identity
  `msvvRatio_mul_slackScore_msvvNormalizedAlphaFromAssignment_eq_balanceScore`,
  which is the corrected dual-fitting bridge between Balance scores and the LP
  dual.
- Proved the non-exhausted-query beta charge
  `maxSlackBeta_runHistoryStateFrom_le_balanceScore_of_all_canAssign`.
- Proved the exhausted-advertiser beta-charge layer:
  blocked advertisers have final alpha at least `exp (-ε)` and final slack at
  most `bid * (1 - exp (-ε))`.
- Added `maxBidForQuery` and the mixed query-dual bounds
  `maxSlackBeta_runHistoryStateFrom_le_max_balanceScore_maxBidError_of_choice`
  and
  `maxSlackBeta_runHistoryStateFrom_le_balanceScore_add_maxBidError_of_choice`.
- Added the recursive history charge sums
  `historyMaxSlackBetaSum`, `historyMaxBidErrorSum`, and
  `historyBalanceChargeFrom`, then proved
  `historyMaxSlackBetaSum_balanceChoiceRun_le_balanceCharge_add_maxBidError`.
- Added the finite query-set reindexing theorem
  `sum_maxSlackBeta_balanceRun_le_balanceCharge_add_maxBidError_of_cover` for
  nodup histories that cover the finite query type.
- Added the normalized scaled query-dual summation theorem
  `msvvRatio_mul_sum_maxSlackBeta_normalized_balanceRun_le_balanceCharge_add_maxBidError_of_cover`.
- Added the online revenue trace
  `revenue_runAssignment_eq_historyRevenueChargeFrom` and proved the recursive
  Balance charge is bounded by actual run revenue via
  `historyBalanceChargeFrom_initial_le_runAssignment_revenue`.
- Added `MsvvHistoryAccountingCertificate` and proved
  `msvvObjectiveBoundCertificate_of_historyAccounting`, so the query-dual
  summation and LP-objective algebra now automatically reduce the final
  objective-bound certificate to the advertiser-alpha accounting inequality.
- Added the finite small-bids approximate theorem seam:
  `MsvvHistoryApproxAccountingCertificate`,
  `MsvvApproxObjectiveBoundCertificate`, and
  `balance_msvv_approx_competitive_of_approxObjectiveBound`.
- Closed the finite small-bids explicit-error certificate for Balance/MSVV:
  `msvvHistoryApproxAccountingCertificate_balanceChoiceRun`,
  `msvvApproxObjectiveBoundCertificate_balanceChoiceRun`, and
  `balance_msvv_approx_competitive_with_history_error`. The additive error is
  `historyMaxBidAlphaErrorSum ε history + historyMaxBidErrorSum ε history`.
- Added the algebraic small-bids error bound
  `balance_msvv_approx_competitive_with_error_bound`, which replaces that
  explicit history error by
  `ε * (Real.exp 1 + 1) * historyMaxBidSum`.
- Added the query-sum version
  `balance_msvv_approx_competitive_with_query_sum_error_bound`, replacing
  `historyMaxBidSum` by `∑ q, maxBidForQuery q` under the same nodup-cover
  assumption.
- Added canonical finite-query wrappers for the standard `Fin n` model:
  `historyFinset_finRange`, `finRange_history_nodup`,
  `balance_msvv_approx_competitive_finRange_with_query_sum_error_bound`,
  `balance_msvv_approx_competitive_finRange_up_to_delta`,
  `balance_msvv_approx_competitive_finRange_up_to_delta_of_smallBids_threshold`,
  and `balance_msvv_finRange_competitive_of_arbitrarily_smallBids_threshold`.
  These discharge the nodup-cover obligations for `List.finRange n` and state
  the additive error using the finite query sum directly.
- Added family-level finite-query wrappers:
  `balance_msvv_finRange_family_eventually_up_to_delta` and
  `balance_msvv_finRange_family_eventually_up_to_delta_of_smallBids_threshold`.
  These quantify over dependent query sizes `Fin (n k)` and prove the eventual
  additive-`δ` guarantee once the explicit error, or the threshold small-bids
  assumption, is eventually below every positive target.
- Added the reusable real-sequence limit seam
  `Sequence.SeqTendsTo` and `Sequence.le_of_seqTendsTo_eventually_le_add`,
  then used it to prove
  `balance_msvv_finRange_family_limit_competitive_of_error_eventually` and
  `balance_msvv_finRange_family_limit_competitive_of_smallBids_threshold`.
  These convert eventual additive guarantees plus convergence of the scaled
  benchmark and online revenue into an exact limiting inequality.
- Added `Sequence.SeqTendsTo.const_mul_of_nonneg` and the ordinary
  offline-optimum convergence wrappers
  `balance_msvv_finRange_family_limit_competitive_of_error_eventually_of_offlineOpt_convergence`
  and
  `balance_msvv_finRange_family_limit_competitive_of_smallBids_threshold_of_offlineOpt_convergence`,
  whose conclusion is the paper-facing inequality
  `msvvRatio * optLimit ≤ revenueLimit`.
- Added the paper-level small-bids limiting family interface
  `MsvvSmallBidsLimitFamily` and final wrapper
  `balance_msvv_competitive_of_smallBidsLimitFamily` /
  `paper_adwords_balance_msvv_competitive_of_small_bids_limit_family`.
  The structure packages the finite instance family, eventual small-bids
  threshold, and convergence assumptions; the theorem proves the limiting
  `1 - 1/e` guarantee from those fields.
- Added Section 6 effective-bid reductions in
  `EconCSLib.Online.AdWordsExtensions`: arbitrary effective charges
  (`withEffectiveBids`), click-through rates (`withClickThroughRates`),
  delayed-entry/availability masks (`withAvailability`), independent
  slot-query expansion (`withSlots`), and the Section 8 advertiser-weighted
  effective-bid proposal (`withAdvertiserWeights`). The public wrappers
  `paper_adwords_effective_bids_small_bids`,
  `paper_adwords_click_through_rates_small_bids`,
  `paper_adwords_weighted_bids_small_bids`,
  `paper_adwords_availability_small_bids`, and
  `paper_adwords_multiple_slots_small_bids` prove that the small-bids
  hypotheses transfer to the transformed instances.
- Added the Section 7 finite Yao lower-bound layer:
  `Decision.exists_input_randomized_payoff_le_of_forall_deterministic_average_le`
  and the paper-facing certificate wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_msvv_ratio_of_certificate`.
  The paper's uniform permutation distribution is now represented by
  `uniformPermutationDistribution`, with a specialized certificate
  `BMatchingPermutationLowerBoundCertificate` and wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_msvv_ratio_of_permutation_certificate`.
  The explicit finite harmonic bound is represented by
  `theorem9BidderSpendUpperBound` and
  `theorem9NormalizedRevenueUpperBound`; the wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_revenue_bound_certificate`
  reduces Theorem 9 to the deterministic average-revenue inequality and the
  finite/asymptotic harmonic comparison against a requested ratio. The
  round-allocation wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_round_allocation_certificate`
  isolates the paper's `E[q_ij] <= 1 / (N - i + 1)` step and mechanically
  derives the harmonic revenue cap from those inequalities. The pointwise
  allocation wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_pointwise_allocation_certificate`
  starts from realized per-permutation allocations and proves the finite
  expectation algebra needed to reach the round-allocation certificate. The
  symmetry/capacity wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_symmetric_pointwise_allocation_certificate`
  derives the paper's `1 / (N - i + 1)` expected-allocation bound from
  ineligible-zero allocation, per-round capacity, and equal expected allocation
  across eligible positions; `theorem9EligibleBidders_card` proves the
  denominator cardinality. The relabeling wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_relabel_symmetric_pointwise_allocation_certificate`
  derives that expected-allocation equality from pointwise input relabeling
  and `uniformPermutationExpectation_eq_of_relabel`. The observed-prefix
  wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_observed_prefix_allocation_certificate`
  proves that pointwise relabeling identity from the hard instance's prefix
  observation model and `theorem9ObservedPrefix_mul_swap_eq`. The feasible
  observed-prefix wrapper
  `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_feasible_observed_prefix_allocation_certificate`
  derives the position-level capacity and ineligible-zero fields from
  actual-bidder feasibility over the visible set. The harmonic side is now
  closed:
  `theorem9BidderSpendUpperBound_le_log_tail` proves the logarithmic
  tail-spend bound, `theorem9HarmonicLayerCountBound_of_pos` proves the finite
  layer-count estimate, and `theorem9ExponentialGridUpperSum_le_msvvRatio`
  proves the finite geometric grid inequality for `exp(-x)`. The asymptotic
  wrapper
  `paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta`
  exposes the unconditional harmonic-cap limit, and
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta`
  states the large-market form: under the round-allocation inequalities, no
  randomized algorithm family beats `1 - 1/e + δ` on all sufficiently large
  permutation instances. The public packaged endpoint is
  `BMatchingTheorem9FamilyCertificate` together with
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_family_certificate`.
  The closest paper-facing endpoint is now the feasible observed-prefix family
  certificate `BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate` and
  wrapper
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_observed_prefix_family_certificate`;
  instantiating it leaves the concrete deterministic prefix allocation and
  capped-revenue field. The capped-payoff endpoint
  `BMatchingTheorem9FeasiblePrefixRuleFamily` and wrapper
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_prefix_rule_family`
  remove that final field by defining payoff as the paper's capped normalized
  spend expression. The concrete finite choice-rule endpoint
  `BMatchingTheorem9IntegralPrefixChoiceFamily` and wrapper
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family`
  specialize this to deterministic rules that choose at most one visible actual
  bidder in each round. The realized-payoff bridge
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family_of_realized_revenue`
  handles richer algorithm models whose realized revenue is pointwise bounded by
  the capped normalized spend expression.
- Added the delta-form wrapper
  `balance_msvv_approx_competitive_up_to_delta`: if the algebraic error bound
  is at most `δ`, Balance/MSVV is competitive up to additive `δ`.
- Added the explicit-threshold wrapper
  `balance_msvv_approx_competitive_up_to_delta_of_smallBids_threshold`: for
  positive `historyMaxBidSum`, `SmallBids` at
  `min 1 (δ / ((Real.exp 1 + 1) * historyMaxBidSum))` is enough for the
  additive-`δ` guarantee.
- Added the limit-style wrapper
  `balance_msvv_competitive_of_arbitrarily_smallBids_threshold`, which removes
  the additive term under an arbitrarily-small-threshold assumption.
- Added the finite AdWords LP dual layer:
  `DualFeasible`, `dualObjective`, `assignedWeightedSpend`,
  `revenue_le_dualObjective_of_dualFeasible`, and
  `offlineOptimumValue_le_dualObjective_of_dualFeasible`.
- Added the standard fractional AdWords LP layer:
  `FractionalAssignment`, `FractionalFeasible`, `fractionalRevenue`,
  integral-to-fractional embedding, and
  `fractionalRevenue_le_dualObjective_of_dualFeasible`.
- Added the first small-bids boundary lemma:
  if an advertiser cannot accept a query and every bid is at most an `ε`
  fraction of budget, then the advertiser's spent fraction is already above
  `1 - ε`.
- Added certificate wrappers:
  `CompetitiveRatioCertificate`,
  `PrimalDualCompetitiveCertificate`,
  `competitiveRatioCertificate_of_primalDual`, and
  `competitive_of_primalDual`.
- Added `EconCSLib.Online.MainTheorems` and `EconCSLib/Online/README.md`
  with the paper-facing theorem-status table.

Current endpoint:

- The finite offline benchmark, fractional LP weak-duality, small-bids
  boundary, online-history, run-feasibility, run-monotonicity, normalized
  per-query beta-charge, normalized query-dual summation, and revenue-trace
  layers are closed. The advertiser-alpha increment accounting inequality is
  also formalized, so the finite small-bids theorem now has an explicit
  additive error in
  `balance_msvv_approx_competitive_with_history_error`, and that error is
  bounded by the simpler algebraic term used in
  `balance_msvv_approx_competitive_with_error_bound`; the query-sum variant is
  `balance_msvv_approx_competitive_with_query_sum_error_bound`. The delta-form theorem
  `balance_msvv_approx_competitive_up_to_delta` isolates the limit-facing
  small-bids threshold, and
  `balance_msvv_approx_competitive_up_to_delta_of_smallBids_threshold` gives an
  explicit small-bids threshold for any additive `δ`. The limit-style wrapper
  `balance_msvv_competitive_of_arbitrarily_smallBids_threshold` removes the
  additive term if those thresholds are available for all positive `δ`. The
  `Fin n` wrappers close the nodup-cover bookkeeping for the canonical finite
  query model by using `List.finRange n`. The family-level theorems now state
  the small-bids limiting seam over `Fin (n k)` instance families and convert
  that seam to a limiting real inequality under explicit `SeqTendsTo`
  convergence assumptions, with ordinary offline-optimum convergence wrappers
  yielding the paper-facing form `msvvRatio * optLimit ≤ revenueLimit`. The
  final public interface is
  `paper_adwords_balance_msvv_competitive_of_small_bids_limit_family`.
  Section 6's realistic variants and Section 8's weighted-bid proposal are
  formalized as reductions to the same theorem through effective bids. The
  multiple-slot theorem is the independent slot-query expansion; per-page
  distinct-advertiser feasibility would require a stronger model if needed.
  Section 7's Yao/minimax step, uniform permutation distribution, pointwise,
  symmetry/capacity, relabel-symmetry, observed-prefix, and feasible
  observed-prefix allocation certificates, explicit harmonic revenue cap,
  logarithmic tail-spend bound, layer-count estimate, and exponential-grid
  upper bound are formalized. The integral prefix-choice family and lower-bound
  endpoint are now complete, including the realized-payoff bridge
  `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family_of_realized_revenue`.

## Award-Year Triage

| Award year | Paper(s) | Domain | Formalization priority | First theorem seam | Shared library payoff |
|---|---|---|---|---|---|
| 2025 | *On approximately fair allocations of indivisible goods* | Fair division | Highest | Bounded maximum envy via envy-cycle elimination | Fair-division core: bundles, valuations, allocations, envy, EF1, envy graphs |
| 2024 | *AdWords and generalized online matching* | Online matching, ads | Family-level endpoint formalized | Balance/MSVV competitive ratio via finite LP weak duality, finite small-bids accounting, and `MsvvSmallBidsLimitFamily` | Online allocation, budgets, competitive ratio, matching with capacities |
| 2023 | *Marriage, honesty, and stability*; *Unbalanced random matching markets* | Matching markets | High, but split finite from asymptotic parts | Stable matching definitions, DA, truncation/strategic behavior seams | Preferences, matchings, stability, deferred acceptance, random markets |
| 2022 | Nash equilibrium complexity papers | Game complexity | Low initially | Define finite games, Nash, two-player normal form; defer PPAD proof | Normal-form games, equilibria, reductions eventually |
| 2021 | *Competitive auctions and digital goods* | Prior-free auctions | Medium | Truthfulness and benchmark revenue for unlimited-supply auctions | Auction outcomes, revenue, truthful mechanisms, randomized mechanisms |
| 2020 | Calibration/correlated equilibrium papers | Learning in games | Medium | Regret/calibration implies correlated-equilibrium empirical distribution | Finite games, correlated equilibrium, regret, empirical distributions |
| 2019 | *Communication Requirements of Efficient Allocations and Supporting Prices* | Communication complexity, prices | Low-medium | Encode allocations, welfare maximization, supporting prices; defer lower bounds | Allocation language, price systems, communication protocols |
| 2018 | GSP/position auction papers | Sponsored search auctions | High after basic auctions | GSP equilibrium/welfare/revenue statements in finite position auctions | Position auctions, click-through rates, payments, equilibrium notions |
| 2017 | *Truth Revelation in Approximately Efficient Combinatorial Auctions* | Combinatorial auctions | Medium-high after mechanism primitives | Greedy allocation plus payment rule truthfulness for restricted bidders | Combinatorial valuations, direct mechanisms, DSIC, approximation |
| 2016 | STV manipulation/control papers | Computational social choice | Low-medium | STV definitions and finite voting primitives; defer NP-hardness reductions | Ballots, rankings, voting rules, manipulation/control interfaces |

## Shared Library Roadmap

CSLib compatibility note:

- See `docs/CSLIB_COMPATIBILITY_NOTES.md`.
- The repo now pins CSLib `v4.30.0-rc2`. The most useful immediate CSLib
  primitive has been step-indexed relation reachability from
  `Cslib.Foundations.Data.RelatesInSteps`. It was used to close the
  fair-division graph seam by extracting a shortest positive closed envy walk
  and converting it into a simple nodup `EnvyCycleList`.
- CSLib automata, regular-language, and URM modules are relevant for the
  voting/complexity tracks, but they should not drive the near-term fair
  division or monoculture proofs.

The reusable library should grow in this order:

1. `EconCSLib.FairDivision`
   Finite bundles, monotone valuations, allocations, envy, EF1, envy graphs,
   approximate envy bounds, and fair-allocation algorithms.

2. `EconCSLib.Mechanism`
   Agents, types, reports, outcomes, utilities, direct mechanisms, payments,
   dominant-strategy truthfulness, Bayesian variants, and certificates for
   approximate mechanisms.

3. `EconCSLib.Auction`
   Single-item, digital-goods, position/GSP, VCG, and combinatorial-auction
   interfaces. This should reuse `Mechanism` instead of defining truthfulness
   again.

4. `EconCSLib.Matching`
   Preferences, matchings, capacities, stability, deferred acceptance, truncation,
   and market-size/random-market interfaces.

5. `EconCSLib.Game`
   Finite normal-form games, mixed strategies, Nash equilibrium, correlated
   equilibrium, regret, calibration, and welfare.

6. `EconCSLib.Online`
   Online instances, histories, irrevocable allocation algorithms, budgets,
   competitive ratios, and primal-dual certificates.

7. `EconCSLib.Complexity`
   Reductions, oracle/query lower bounds, NP-hardness/PPAD interfaces. This is
   important but should come after the finite model libraries are stable.

## Best Next Steps (Informed by Recent Machinery)

Based on the successful patterns established in the Fair Division and Producer Fairness tracks (e.g., iterative algorithmic folds, "No Hidden Definitions" transparency, and finite PMF state spaces), here is the prioritized roadmap for the remaining tracks:

1. **2023 Matching-Paper Track (*Marriage, honesty, and stability*) - Highest Priority (Foundational Gap)**
   - **Library Note:** There are currently no existing `Mathlib` or `CSLib` modules for stable matching or Gale-Shapley (Mathlib only contains undirected simple graph matching). All foundational definitions must be built from scratch.
   - Build finite matching primitives (`Preferences`, `Matching`).
   - Apply the **"No Hidden Definitions"** mandate to expose the mathematical definition of `IsStable` (no blocking pairs) directly in the paper-facing ledger so human reviewers can audit it immediately.
   - Implement the **Deferred Acceptance (Gale-Shapley)** algorithm using the exact same `List.fold` / state-passing functional pattern we used to close the LMMS fair division algorithm.
   - Prove stability/strategyproofness seams before touching asymptotic random-market arguments.

2. **2017 Combinatorial Auctions Track (*Truth Revelation in Approximately Efficient...*)**
   - **Reuse Fair Division Primitives:** We now have robust finite bundles, allocations, and valuations from the 2025 track. Directly bridge these into the combinatorial auction model rather than creating a separate interface.
   - **Greedy Allocation via Folds:** Implement the greedy allocation algorithm for single-minded bidders using the `List.foldr` pattern to track the running feasible set.
   - Prove the "Critical Value" payment rule is dominant-strategy truthful for these single-minded bidders.

3. **2021 Digital Goods / Prior-Free Auctions (*Competitive auctions and digital goods*)**
   - The deterministic mechanism is complete, but the approximation bound (`CrossSampleOfferApproximationCertificate`) remains an open seam.
   - **Apply Finite Probability Patterns:** Use the generic finite state space `PMF` mapping pattern (successfully used for random review counts in Producer Fairness) to model the "Random Sampling" partition distribution of RSOP. This allows proving the expected revenue bound using simple finite expectation (`DecisionCore.pmfExp`) algebra without needing measure theory.
