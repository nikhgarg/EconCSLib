# AdWords and Generalized Online Matching — Paper-Facing Verification Dossier

This file is the single-file confidence checkpoint for the paper formalization.
It is ordered in paper order and includes only paper-facing declarations, with the
paper-style statement and the exact assumptions of the formal theorem form in each
entry.

Concretely, a human should be able to audit this file alone by checking that:
- every declaration exists in `MainTheorems.lean`,
- every item has a paper-statement and assumptions,
- sections follow the paper’s flow,
- and the final competitiveness conclusion appears exactly as the paper form.

## 1) Model and LP primitives

- `AdWordsInstance`
  - Paper object: finite AdWords instance with advertiser budgets and query bids.
- `AdWordsInstance.Assignment`
  - Paper object: integral online assignment `A : Query → Option Advertiser`.
- `AdWordsInstance.FractionalAssignment`
  - Paper object: fractional LP variables `x : Advertiser → Query → ℝ`.
- `AdWordsInstance.emptyAssignment`, `AdWordsInstance.assignQuery`
  - Paper object: base assignment and one-step assignment update.
- `AdWordsInstance.HistoryState`, `initialHistoryState`, `stepHistoryState`,
  `runHistoryState`, `runHistoryStateFrom`, `runAssignment`
  - Paper object: online state transition system and folded history run.
- `AdWordsInstance.historyFinset`, `historyFinset_finRange`, `finRange_history_nodup`
  - Paper object: finite history set interpretation and `Fin`-range helper lemmas.
- `AdWordsInstance.spend`, `AdWordsInstance.revenue`, `AdWordsInstance.fractionalRevenue`
  - Paper object: advertiser spent budget and integral/fractional revenue benchmarks.
- `AdWordsInstance.Feasible`, `FractionalFeasible`, `ChoiceRuleFeasible`,
  `StateInvariant`
  - Paper object: feasibility predicates for assignments/choice rules/state.
- `AdWordsInstance.DualFeasible`, `AdWordsInstance.dualObjective`, `AdWordsInstance.assignedWeightedSpend`
  - Paper object: dual LP constraints/objective and weighted spend notation.
- `AdWordsInstance.offlineOptimumAssignment`, `AdWordsInstance.offlineOptimumValue`
  - Paper object: finite offline benchmark assignment and optimum value.
- `AdWordsInstance.NonnegativeBids`, `NonnegativeBudgets`, `PositiveBudgets`, `SmallBids`
  - Paper object: baseline positivity and small-bids assumptions.
- `AdWordsInstance.maxBidForQuery`, `maxBidAlphaError`, `maxBidAlphaErrorSum`,
  `historyMaxBidErrorSum`, `historyMaxBidAlphaErrorSum`, `historyMaxBidSum`,
  `historyMsvvSmallBidsErrorSum`
  - Paper object: per-query and history-level small-bids error terms.
- `AdWordsInstance.balanceDiscount`, `msvvDualAlpha`, `msvvNormalizedDualAlpha`
  - Paper object: Balance and MSVV dual constructions.
- `AdWordsInstance.balanceScore`, `slackScore`
  - Paper object: balance score and per-query slack score in the dual analysis.
- `AdWordsInstance.msvvAlphaFromAssignment`, `msvvNormalizedAlphaFromAssignment`,
  `msvvNormalizedAlphaBudgetMass`, `msvvRatio`
  - Paper object: assignment-induced MSVV duals and constant ratio `1 - 1/e`.
- `AdWordsInstance.IsBalanceChoice`, `balanceChoiceRule`
  - Paper object: choice rule maximizing the Balance/MSVV score.
- `AdWordsInstance.ChoiceRule` wrappers
  - Paper object: Section 6/8 reductions:
    `withEffectiveBids`, `withClickThroughRates`, `withAdvertiserWeights`,
    `withAvailability`, `withSlots`, `withSlotsPerPageDistinct`,
    `withSlotsDistinctChoice`.

## 2) Finite LP and dual-sewing lemmas

- `paper_adwords_empty_assignment_feasible`
  - Paper statement: `I.Feasible (AdWordsInstance.emptyAssignment)`.
  - Assumptions: `hbudget : I.NonnegativeBudgets`.
- `paper_adwords_offline_optimum_exists`
  - Paper statement: `∃ A, I.IsOptimalAssignment A`.
  - Assumptions: finite advertiser/query types, `hbudget : I.NonnegativeBudgets`.
- `paper_adwords_revenue_le_total_budget_of_feasible`
  - Paper statement: `I.revenue A ≤ ∑ a, I.budget a`.
  - Assumptions: `hfeasible : I.Feasible A`.
- `paper_adwords_lp_weak_duality`
  - Paper statement: if `hfeasible : I.Feasible A` and `hdual : I.DualFeasible α β`,
    then `I.revenue A ≤ I.dualObjective α β`.
  - Assumptions: LP feasibility on primal and dual side.
- `paper_adwords_integral_assignment_fractional_feasible`
  - Paper statement: integral feasible assignments are fractional-feasible embeddings.
  - Assumptions: `hfeasible : I.Feasible A`.
- `paper_adwords_fractional_lp_weak_duality`
  - Paper statement: fractional weak duality
    `I.fractionalRevenue X ≤ I.dualObjective α β`.
  - Assumptions: `I.FractionalFeasible X` and `I.DualFeasible α β`.
- `paper_adwords_dual_feasible_of_slack_score_bound`
  - Paper statement: if `∀ q, slackScore α a q ≤ β q` and nonnegativity
    hypotheses hold, then `I.DualFeasible α β`.
  - Assumptions: `halpha : ∀ a, 0 ≤ α a`, `hbeta : ∀ q, 0 ≤ β q`.
- `paper_adwords_dual_feasible_max_slack_beta`
  - Paper statement:
    `I.DualFeasible α (I.maxSlackBeta α)` from nonnegative advertiser duals.
  - Assumptions: `Fintype Advertiser`, `Nonempty Advertiser`, `halpha`.
- `paper_adwords_dual_feasible_msvv_assignment`
  - Paper statement:
    `I.DualFeasible (I.msvvAlphaFromAssignment A) (I.maxSlackBeta (...))`.
  - Assumptions: finite nonempty advertiser/query types, choice of assignment.
- `paper_adwords_dual_feasible_msvv_normalized_assignment`
  - Paper statement:
    normalized MSVV duals are dual feasible.
  - Assumptions: `hbid : I.NonnegativeBids`, `hbudget : I.PositiveBudgets`.
- `paper_adwords_balance_choice_exists`
  - Paper statement: if some advertiser can accept query `q`, then
    `∃ a, I.IsBalanceChoice A q a`.

## 3) Online run correctness

- `paper_adwords_run_assignment_feasible`
  - Paper statement: `I.Feasible (I.runAssignment rule history)`.
  - Assumptions: finite/decidable types, nonnegative budgets, `ChoiceRuleFeasible`.
- `paper_adwords_balance_run_assignment_feasible`
  - Paper statement: balance run stays feasible on any finite history.
  - Assumptions: `hbudget : I.NonnegativeBudgets`.
- `paper_adwords_balance_assignment_assigned_only_from_history`
  - Paper statement: if `hassigned : runAssignment ... q = some a`, then
    `q ∈ historyFinset history`.
  - Assumptions: `q` in the observed history.
- `paper_adwords_spend_monotone_over_history`
  - Paper statement: spend is monotone over online history execution.
  - Assumptions: `I.NonnegativeBids`, `ChoiceRuleFeasible`, state invariants.
- `paper_adwords_run_revenue_eq_history_revenue_charge`
  - Paper statement: `runAssignment` revenue equals recursive history charge from
    `initialHistoryState`.
- `paper_adwords_balance_charge_le_run_revenue`
  - Paper statement: recursive `historyBalanceCharge` is bounded by actual revenue.
  - Assumptions: nonnegative bids/budgets, Balance choice feasibility.

## 4) Dual comparison and charging inequalities

- `paper_adwords_final_slack_score_le_initial_balance_score`
  - Paper statement:
    final MSVV slack is bounded by the earlier Balance score at the same query:
    `slackScore final ≤ balanceScore initial`.
  - Assumptions: nonnegative bids and state invariants.
- `paper_adwords_max_slack_beta_le_balance_score_of_all_can_assign`
  - Paper statement: for `q` where all advertisers can accept,
    final max-slack query beta is no larger than chosen Balance score.
- `paper_adwords_msvv_ratio_mul_normalized_max_slack_beta_le_balance_score_of_all_can_assign`
  - Paper statement: same bound under normalized MSVV scaling by `msvvRatio`.
- `paper_adwords_blocked_advertiser_final_alpha_ge_exp_neg_epsilon`
  - Paper statement: blocked advertisers satisfy
    `msvvAlphaFromAssignment ... a ≥ exp (-ε)`.
  - Assumptions: nonnegative bids, `SmallBids ε`, positive budget of `a`.
- `paper_adwords_blocked_advertiser_final_slack_score_le_error`
  - Paper statement:
    blocked slack score is bounded by `bid a q * (1 - exp (-ε))`.
  - Assumptions: nonnegative bids, `SmallBids ε`, positive budget of `a`, blockedness.
- `paper_adwords_msvv_ratio_mul_blocked_advertiser_normalized_final_slack_score_le_error`
  - Paper statement: normalized blocked slack score satisfies the same error bound
    after scaling by `msvvRatio`.
- `paper_adwords_msvv_ratio_mul_normalized_max_slack_beta_le_balance_score_add_max_bid_error`
  - Paper statement: normalized final query dual is bounded by
    `balanceScore + maxBidForQuery * (1 - exp (-ε))`.
  - Assumptions: `0 ≤ ε`, `SmallBids ε`, positive budgets.
- `paper_adwords_max_slack_beta_le_balance_score_or_max_bid_error`
  - Paper statement: unnormalized final query dual is bounded by
    `max (balanceScore) (maxBidForQuery * (1 - exp (-ε)))`.
- `paper_adwords_max_slack_beta_le_balance_score_add_max_bid_error`
  - Paper statement: same decomposition in additive form.
- `paper_adwords_balance_history_max_slack_beta_sum_le_charge_add_error`
  - Paper statement: nodup-history sum of final max-slack duals
    `≤ balanceCharge + historyMaxBidErrorSum`.
  - Assumptions: nodup history, nonnegative bids, positive budgets, `SmallBids ε`.
- `paper_adwords_balance_query_dual_sum_le_charge_add_error_of_history_cover`
  - Paper statement: if `historyFinset history = Finset.univ`, finite query sum dual
    has the same bound plus error sum.
  - Assumptions: same as above plus cover condition.
- `paper_adwords_msvv_ratio_mul_normalized_query_dual_sum_le_charge_add_error_of_history_cover`
  - Paper statement: normalized query-dual sum version with multiplicative `msvvRatio`.

## 5) Section 6 / 8 reductions

- `paper_adwords_small_bids_blocked_advertiser_spent_fraction`
  - Paper statement: if `a` is blocked on query `q`, then
    `1 - ε < I.spentFraction A a`.
  - Assumptions: positive budget and `SmallBids ε`.
- `paper_adwords_effective_bids_small_bids`
  - Paper statement: pointwise effective bids with bound `ε * budget`
    preserve `SmallBids ε`.
- `paper_adwords_click_through_rates_small_bids`
  - Paper statement: CTR-scaled instance preserves `SmallBids ε` when
    `ctr ≤ 1` and base bids are nonnegative and `SmallBids ε`.
- `paper_adwords_weighted_bids_small_bids`
  - Paper statement: advertiser-weighted bids preserve `SmallBids ε` when
    each weight is ≤ 1.
- `paper_adwords_availability_small_bids`
  - Paper statement: delayed-entry availability masking preserves `SmallBids ε`.
  - Assumptions: `0 ≤ ε`, `PositiveBudgets`, `hsmall : SmallBids ε`.
- `paper_adwords_multiple_slots_small_bids`
  - Paper statement: slot expansion preserves `SmallBids ε`.
  - Assumptions: base `SmallBids ε`.

## 6) Section 7 lower bound certificates

- `AdWordsLowerBound.UniformPermutationDistribution`
  - Paper object: uniform distribution over `Equiv.Perm (Fin N)`.
- `AdWordsLowerBound.theorem9EligibleBidders`, `theorem9ActualEligibleBidders`,
  `theorem9ObservedPrefix`
  - Paper object: observed-prefix eligible-bidder definitions/lemmas.
- `AdWordsLowerBound.BMatchingYaoLowerBoundCertificate`,
  `BMatchingPermutationLowerBoundCertificate`,
  `BMatchingPermutationRevenueBoundCertificate`
  - Paper object: Yao-style finite lower-bound certificate hierarchy.
- `AdWordsLowerBound.BMatchingRoundAllocationRevenueCertificate`,
  `BMatchingPointwiseAllocationRevenueCertificate`,
  `BMatchingSymmetricPointwiseAllocationRevenueCertificate`,
  `BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate`,
  `BMatchingObservedPrefixAllocationRevenueCertificate`,
  `BMatchingFeasibleObservedPrefixAllocationRevenueCertificate`
  - Paper object: deterministic-to-randomized reductions for increasingly structured assumptions.
- `AdWordsLowerBound.BMatchingTheorem9FamilyCertificate`,
  `BMatchingTheorem9PointwiseFamilyCertificate`,
  `BMatchingTheorem9SymmetricPointwiseFamilyCertificate`,
  `BMatchingTheorem9RelabelSymmetricPointwiseFamilyCertificate`,
  `BMatchingTheorem9ObservedPrefixFamilyCertificate`,
  `BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate`,
  `BMatchingTheorem9FeasiblePrefixRuleFamily`,
  `BMatchingTheorem9IntegralPrefixChoiceFamily`,
  `BMatchingTheorem9LayerCountFamilyCertificate`,
  `BMatchingTheorem9PointwiseLayerCountFamilyCertificate`,
  `BMatchingTheorem9SymmetricPointwiseLayerCountFamilyCertificate`
  - Paper object: family certificates for pointwise/symmetric/feasible/integral-prefix and layer-count variants.
- `theorem9HarmonicLayerCountBound`
  - Paper object: finite harmonic layer-count inequality used in the lower-bound chain.
- `BMatchingIntegralPrefixChoice`, `BMatchingIntegralPrefixAlgorithm`
  - Paper object: concrete finite integral-prefix algorithm family.
- `AdWordsLowerBound.BMatchingIntegralPrefixChoice.Feasible`
  - Paper object: feasibility for concrete integral-prefix choices.
- `AdWordsLowerBound.BMatchingTheorem9IntegralPrefixChoiceFamily.normalizedRevenue`
  - Paper object: capped normalized revenue used by the concrete family endpoint.
- `paper_adwords_theorem9_no_randomized_algorithm_beats_msvv_ratio_of_certificate`
  - Paper statement: generic lower-bound certificate implies no randomized algorithm
    exceeds `msvvRatio`.
- `paper_adwords_theorem9_no_randomized_algorithm_beats_msvv_ratio_of_permutation_certificate`
  - Paper statement: same for hard distribution of permutations.
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_revenue_bound_certificate`
  - Paper statement: explicit finite deterministic revenue bound implies ratio bound for all randomized algorithms.
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_round_allocation_certificate`
  - Paper statement: finite per-round allocation bound implies ratio bound.
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_pointwise_allocation_certificate`
  - Paper statement: pointwise allocation form of the same lower-bound wrapper.
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_symmetric_pointwise_allocation_certificate`
  - Paper statement: symmetric pointwise allocation wrapper.
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_relabel_symmetric_pointwise_allocation_certificate`
  - Paper statement: relabeling-symmetric pointwise wrapper.
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_observed_prefix_allocation_certificate`
  - Paper statement: observed-prefix allocation wrapper.
- `paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_feasible_observed_prefix_allocation_certificate`
  - Paper statement: feasible observed-prefix wrapper.
- `paper_adwords_theorem9_harmonic_layer_count_bound_of_log_spend_cap`
  - Paper statement: `theorem9HarmonicLayerCountBound` follows from log-tail spend cap.
- `paper_adwords_theorem9_bidder_spend_upper_bound_le_log_tail`
  - Paper statement: bidder capped spend is at most a log tail term.
- `paper_adwords_theorem9_harmonic_layer_count_bound`
  - Paper statement: finite harmonic layer-count bound for all `N, M > 0`.
- `paper_adwords_theorem9_normalized_revenue_upper_bound_le_msvv_ratio_add_grid_errors`
  - Paper statement:
    `theorem9NormalizedRevenueUpperBound N ≤ msvvRatio + 1/M + 1/N`.
- `paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta_of_layer_count_bound`
  - Paper statement: eventual theorem from layer-count bound.
- `paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta`
  - Paper statement: `theorem9NormalizedRevenueUpperBound N ≤ msvvRatio + δ` eventually.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta`
  - Paper statement: with round allocation hypothesis, no randomized algorithm beats
    `msvvRatio + δ` on all sufficiently large permutations.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_family_certificate`
  - Paper statement: same from `BMatchingTheorem9FamilyCertificate`.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_pointwise_family_certificate`
  - Paper statement: same from `BMatchingTheorem9PointwiseFamilyCertificate`.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_symmetric_pointwise_family_certificate`
  - Paper statement: same from `BMatchingTheorem9SymmetricPointwiseFamilyCertificate`.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_relabel_symmetric_pointwise_family_certificate`
  - Paper statement: same from relabeling-symmetric family certificate.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_observed_prefix_family_certificate`
  - Paper statement: same from observed-prefix family certificate.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_observed_prefix_family_certificate`
  - Paper statement: same from feasible observed-prefix family certificate.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_prefix_rule_family`
  - Paper statement: same from feasible-prefix-rule family certificate.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family`
  - Paper statement: same from integral-prefix-choice family certificate.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family_of_realized_revenue`
  - Paper statement: same with pointwise realized-revenue bridge.
- `paper_adwords_theorem9_integral_prefix_algorithm_family`
  - Paper object: concrete finite family of integral-prefix algorithms.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms`
  - Paper statement: endpoint for concrete finite integral-prefix family.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms_of_realized_revenue`
  - Paper statement: same endpoint with realized-payoff comparison bridge.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_layer_count_family_certificate`
  - Paper statement: from layer-count family certificate.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_pointwise_layer_count_family_certificate`
  - Paper statement: pointwise layer-count family strengthening.
- `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_symmetric_pointwise_layer_count_family_certificate`
  - Paper statement: symmetric pointwise layer-count family strengthening.

## 7) Balance/MSVV objective and limit chain

- `paper_adwords_competitive_of_primal_dual_certificate`
  - Paper statement:
    `ratio * I.offlineOptimumValue hbudget ≤ revenue A` from a primal-dual certificate.
- `paper_adwords_balance_msvv_competitive_of_primal_dual_certificate`
  - Paper statement: Balance run is `msvvRatio`-competitive under a primal-dual certificate.
- `paper_adwords_balance_msvv_objective_bound_of_history_accounting`
  - Paper statement: ideal history accounting yields a finite objective-bound certificate.
- `paper_adwords_balance_msvv_approx_objective_bound_of_history_accounting`
  - Paper statement:
    history-accounting with explicit finite error yields approximate objective-bound certificate.
- `paper_adwords_balance_msvv_history_approx_accounting_with_explicit_error`
  - Paper statement: explicit error is
    `historyMaxBidAlphaErrorSum ε history + historyMaxBidErrorSum ε history`.
- `paper_adwords_balance_msvv_approx_objective_bound_with_explicit_error`
  - Paper statement: the explicit error yields approximate objective-bound certificate.
- `paper_adwords_balance_msvv_competitive_of_objective_bound`
  - Paper statement:
    `msvvRatio * opt ≤ revenue run`.
- `paper_adwords_balance_msvv_approx_competitive_of_approx_objective_bound`
  - Paper statement: approximate objective bound implies additive competitiveness slack.
- `paper_adwords_balance_msvv_approx_competitive_with_explicit_history_error`
  - Paper statement:
    `msvvRatio * opt ≤ revenue + historyMaxBidAlphaErrorSum + historyMaxBidErrorSum`.
- `paper_adwords_balance_msvv_approx_competitive_with_error_bound`
  - Paper statement:
    `historyMaxBidAlphaErrorSum + historyMaxBidErrorSum ≤ ε * (exp 1 + 1) * historyMaxBidSum`.
- `paper_adwords_balance_msvv_approx_competitive_with_query_sum_error_bound`
  - Paper statement:
    same error bound with right side `ε * (exp 1 + 1) * (∑ q, maxBidForQuery q)`.
- `paper_adwords_balance_msvv_finRange_approx_competitive_with_query_sum_error_bound`
  - Paper statement: canonical `Fin n` version, history = `List.finRange n`.
- `paper_adwords_balance_msvv_approx_competitive_up_to_delta`
  - Paper statement: if error ≤ `δ`, then competitiveness is up to additive `δ`.
- `paper_adwords_balance_msvv_finRange_approx_competitive_up_to_delta`
  - Paper statement: finite-`n` `Fin` history version of the above.
- `paper_adwords_balance_msvv_approx_competitive_up_to_delta_of_small_bids_threshold`
  - Paper statement: threshold form
    `SmallBids (min 1 (δ / ((exp 1 + 1) * historyMaxBidSum))`.
- `paper_adwords_balance_msvv_finRange_approx_competitive_up_to_delta_of_small_bids_threshold`
  - Paper statement: canonical `Fin n` threshold finite theorem.
- `paper_adwords_balance_msvv_competitive_of_arbitrarily_small_bids_threshold`
  - Paper statement: if threshold holds for every positive `δ`, the additive term vanishes.
- `paper_adwords_balance_msvv_finRange_competitive_of_arbitrarily_small_bids_threshold`
  - Paper statement: finite `Fin n` limit-style version.
- `paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta`
  - Paper statement: family-level eventual additive competitiveness with explicit error.
- `paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta_of_small_bids_threshold`
  - Paper statement: family-level eventual additive competitiveness from eventual threshold.
- `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_error_eventually`
  - Paper statement: limits from eventual explicit error control.
- `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_small_bids_threshold`
  - Paper statement: limits from eventual small-bids threshold.
- `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_error_eventually_of_offline_opt_convergence`
  - Paper statement: as above, with ordinary offline-opt convergence assumptions.
- `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_small_bids_threshold_of_offline_opt_convergence`
  - Paper statement: same with ordinary offline-opt convergence and threshold.
- `paper_adwords_balance_msvv_competitive_of_small_bids_limit_family`
  - Paper statement (paper theorem): `msvvRatio * optLimit ≤ revenueLimit`.

## Verification checklist for this dossier file

- Every paper-facing declaration in this file has a corresponding declaration in
  `MainTheorems.lean` with the same name.
- For each theorem-like entry, assumptions are explicit in this file and agree with
  the Lean theorem signature.
- Sections match paper order, including model primitives, LP/duality, online run,
  charging lemmas, reductions, Section 7 lower-bound chain, and MSVV limit chain.
- The final line is the paper-level theorem statement
  `msvvRatio * optLimit ≤ revenueLimit`.
- No placeholder text or unresolved handwave appears here.
