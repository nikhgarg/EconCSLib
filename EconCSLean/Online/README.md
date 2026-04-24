# AdWords and Generalized Online Matching

## Source Version

- Paper: *AdWords and Generalized Online Matching*
- Authors: Aranyak Mehta, Amin Saberi, Umesh Vazirani, and Vijay V. Vazirani
- Version formalized: Journal of the ACM 54(5), 2007, Article 22
- Official DOI: https://doi.org/10.1145/1284320.1284321
- Official ACM URL: https://dl.acm.org/doi/10.1145/1284320.1284321
- Award listing: https://www.sigecom.org/award-tot.html
- Public author PDF: https://people.eecs.berkeley.edu/~vazirani/pubs/adwords.pdf
- Accessed: 2026-04-24

The PDF is not committed to git. Use the ACM DOI/JACM version as the source
version; the author PDF is listed only for easier access.

## Central Theorem File

- `EconCSLean/Online/MainTheorems.lean`

That file contains the paper-facing theorem wrappers currently available.
Detailed finite assignment, Balance/MSVV choice, and LP-duality lemmas live in
`AdWords.lean`. Section 6 effective-bid reductions live in
`AdWordsExtensions.lean`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Finite AdWords instance | `AdWordsInstance` | formalized | `EconCSLean/Online/AdWords.lean` | none |
| Offline assignment, spend, revenue, budget feasibility | `Assignment`, `spend`, `revenue`, `Feasible` | formalized | `EconCSLean/Online/AdWords.lean` | finite query type for sums |
| Empty feasible assignment | `paper_adwords_empty_assignment_feasible` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative budgets |
| Revenue equals sum of advertiser spends | `revenue_eq_sum_spend` | formalized | `EconCSLean/Online/AdWords.lean` | finite advertisers and queries |
| Feasible revenue bounded by total budget | `paper_adwords_revenue_le_total_budget_of_feasible` | formalized | `EconCSLean/Online/MainTheorems.lean` | assignment must be feasible |
| Finite offline optimum exists | `paper_adwords_offline_optimum_exists` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative budgets; finite advertisers and queries |
| Residual budget and feasible next-query assignment | `residualBudget`, `CanAssign`, `canAssign_iff_bid_le_residualBudget` | formalized | `EconCSLean/Online/AdWords.lean` | finite query type |
| Small-bids condition | `SmallBids`, `paper_adwords_small_bids_blocked_advertiser_spent_fraction` | formalized boundary lemma | `EconCSLean/Online/MainTheorems.lean` | positive budget for blocked advertiser |
| Section 6 arbitrary effective charges | `withEffectiveBids`, `paper_adwords_effective_bids_small_bids` | formalized reduction | `EconCSLean/Online/AdWordsExtensions.lean`, `EconCSLean/Online/MainTheorems.lean` | effective charges must satisfy the target small-bids bound |
| Section 6 click-through rates | `withClickThroughRates`, `paper_adwords_click_through_rates_small_bids` | formalized reduction | `EconCSLean/Online/AdWordsExtensions.lean`, `EconCSLean/Online/MainTheorems.lean` | CTRs at most one; original bids nonnegative and small |
| Section 8 advertiser-weighted effective bids | `withAdvertiserWeights`, `paper_adwords_weighted_bids_small_bids` | formalized reduction | `EconCSLean/Online/AdWordsExtensions.lean`, `EconCSLean/Online/MainTheorems.lean` | weights at most one; original bids nonnegative and small |
| Section 6 advertiser availability / delayed entry | `withAvailability`, `paper_adwords_availability_small_bids` | formalized reduction | `EconCSLean/Online/AdWordsExtensions.lean`, `EconCSLean/Online/MainTheorems.lean` | nonnegative `ε`, positive budgets, original small-bids condition |
| Section 6 slot-query expansion | `withSlots`, `paper_adwords_multiple_slots_small_bids` | formalized reduction | `EconCSLean/Online/AdWordsExtensions.lean`, `EconCSLean/Online/MainTheorems.lean` | models independent slot queries; per-page distinct-advertiser feasibility is not encoded |
| Section 7 finite Yao lower-bound lemma | `Decision.exists_input_randomized_payoff_le_of_forall_deterministic_average_le` | formalized generic lemma | `EconCSLean/Decision/Yao.lean` | finite deterministic algorithm and input types |
| Theorem 9 randomized b-matching lower bound | `theorem9BidderSpendUpperBound`, `theorem9BidderHarmonicPrefixNat`, `theorem9BidderSpendUpperBound_le_log_tail`, `theorem9NormalizedRevenueUpperBound`, `theorem9HarmonicLayerCountBound_of_pos`, `theorem9NormalizedRevenueUpperBound_le_msvvRatio_add_gridErrors`, `theorem9_harmonic_eventually_le_msvvRatio_add`, `theorem9_eventually_no_randomized_algorithm_beats_msvvRatio_add_delta`, `theorem9ActualEligibleBidders`, `theorem9ObservedPrefix`, `theorem9ActualEligibleBidders_sum_eq`, `theorem9ObservedPrefix_mul_swap_eq`, `uniformPermutationExpectation_eq_of_relabel`, `BMatchingYaoLowerBoundCertificate`, `BMatchingPermutationLowerBoundCertificate`, `BMatchingRoundAllocationRevenueCertificate`, `BMatchingPointwiseAllocationRevenueCertificate`, `BMatchingSymmetricPointwiseAllocationRevenueCertificate`, `BMatchingRelabelSymmetricPointwiseAllocationRevenueCertificate`, `BMatchingObservedPrefixAllocationRevenueCertificate`, `BMatchingFeasibleObservedPrefixAllocationRevenueCertificate`, `BMatchingTheorem9FamilyCertificate`, `BMatchingTheorem9PointwiseFamilyCertificate`, `BMatchingTheorem9SymmetricPointwiseFamilyCertificate`, `BMatchingTheorem9RelabelSymmetricPointwiseFamilyCertificate`, `BMatchingTheorem9ObservedPrefixFamilyCertificate`, `BMatchingTheorem9FeasibleObservedPrefixFamilyCertificate`, `BMatchingTheorem9FeasiblePrefixRuleFamily`, `BMatchingTheorem9IntegralPrefixChoiceFamily`, `eventually_no_randomized_algorithm_beats_msvvRatio_add_delta_of_realized_revenue`, `paper_adwords_theorem9_bidder_spend_upper_bound_le_log_tail`, `paper_adwords_theorem9_harmonic_layer_count_bound`, `paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta`, `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta`, `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family`, `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family_of_realized_revenue` | harmonic cap and finite integral prefix-choice endpoint formalized for capped normalized spend | `EconCSLean/Online/AdWordsLowerBound.lean`, `EconCSLean/Online/MainTheorems.lean` | none |
| Balance/MSVV discount, dual-alpha, and scaled bid | `balanceDiscount`, `msvvDualAlpha`, `msvvNormalizedDualAlpha`, `balanceScore`, `slackScore` | formalized | `EconCSLean/Online/AdWords.lean` | none |
| Slack-score dual-feasibility builder | `paper_adwords_dual_feasible_of_slack_score_bound` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative alpha/beta and pointwise slack-score cover |
| Max-slack query duals | `maxSlackBeta`, `paper_adwords_dual_feasible_max_slack_beta` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonempty finite advertiser type |
| Assignment-induced MSVV duals | `msvvAlphaFromAssignment`, `paper_adwords_dual_feasible_msvv_assignment` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonempty finite advertiser type |
| Normalized assignment-induced MSVV duals | `msvvNormalizedAlphaFromAssignment`, `paper_adwords_dual_feasible_msvv_normalized_assignment` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonempty finite advertiser type, nonnegative bids, positive budgets |
| MSVV ratio | `msvvRatio`, `msvvRatio_pos`, `msvvRatio_lt_one` | formalized | `EconCSLean/Online/AdWords.lean` | none |
| Balance/MSVV next-query choice exists | `paper_adwords_balance_choice_exists` | formalized | `EconCSLean/Online/MainTheorems.lean` | at least one advertiser can accept the query |
| Online history state and run fold | `HistoryState`, `stepHistoryState`, `runHistoryState`, `runAssignment` | formalized | `EconCSLean/Online/AdWords.lean` | repeated query IDs are skipped after first sighting |
| Canonical finite query history | `historyFinset_finRange`, `finRange_history_nodup` | formalized | `EconCSLean/Online/AdWords.lean` | query type is `Fin n`; history is `List.finRange n` |
| Feasible choice rules preserve feasibility | `paper_adwords_run_assignment_feasible` | formalized | `EconCSLean/Online/MainTheorems.lean` | choice rule must satisfy `ChoiceRuleFeasible` |
| Balance/MSVV run is feasible | `paper_adwords_balance_run_assignment_feasible` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative budgets |
| Balance/MSVV assigns only seen query IDs | `paper_adwords_balance_assignment_assigned_only_from_history` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative budgets |
| Spend monotone over online histories | `paper_adwords_spend_monotone_over_history` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative bids and feasible choice rule |
| Online revenue trace | `paper_adwords_run_revenue_eq_history_revenue_charge` | formalized | `EconCSLean/Online/MainTheorems.lean` | feasible choice rule and nonnegative budgets |
| Balance charge bounded by revenue | `paper_adwords_balance_charge_le_run_revenue` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative bids and budgets |
| Final MSVV slack bounded by earlier Balance score | `paper_adwords_final_slack_score_le_initial_balance_score` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative bids, feasible choice rule, positive advertiser budget |
| Non-exhausted-query beta charge | `paper_adwords_max_slack_beta_le_balance_score_of_all_can_assign` | formalized | `EconCSLean/Online/MainTheorems.lean` | all advertisers can still accept the query |
| Normalized non-exhausted-query beta charge | `paper_adwords_msvv_ratio_mul_normalized_max_slack_beta_le_balance_score_of_all_can_assign` | formalized | `EconCSLean/Online/MainTheorems.lean` | all advertisers can still accept the query |
| Exhausted-advertiser alpha/slack charge | `paper_adwords_blocked_advertiser_final_alpha_ge_exp_neg_epsilon`, `paper_adwords_blocked_advertiser_final_slack_score_le_error` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative bids, positive blocked-advertiser budget, `ε`-small bids |
| Normalized exhausted-advertiser slack charge | `paper_adwords_msvv_ratio_mul_blocked_advertiser_normalized_final_slack_score_le_error` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative bids, positive blocked-advertiser budget, `ε`-small bids |
| Mixed query beta charge | `paper_adwords_max_slack_beta_le_balance_score_or_max_bid_error`, `paper_adwords_max_slack_beta_le_balance_score_add_max_bid_error` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative bids, positive budgets, `0 ≤ ε`, `ε`-small bids, Balance choice at the query state |
| Normalized mixed query beta charge | `paper_adwords_msvv_ratio_mul_normalized_max_slack_beta_le_balance_score_add_max_bid_error` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative bids, positive budgets, `0 ≤ ε`, `ε`-small bids, Balance choice at the query state |
| History-summed beta charge | `paper_adwords_balance_history_max_slack_beta_sum_le_charge_add_error` | formalized | `EconCSLean/Online/MainTheorems.lean` | nodup history; positive budgets; nonnegative bids; `0 ≤ ε`; `ε`-small bids |
| Query-dual sum charge | `paper_adwords_balance_query_dual_sum_le_charge_add_error_of_history_cover` | formalized | `EconCSLean/Online/MainTheorems.lean` | nodup history that covers the finite query type; positive budgets; nonnegative bids; `0 ≤ ε`; `ε`-small bids |
| Normalized query-dual sum charge | `paper_adwords_msvv_ratio_mul_normalized_query_dual_sum_le_charge_add_error_of_history_cover` | formalized | `EconCSLean/Online/MainTheorems.lean` | nodup history that covers the finite query type; positive budgets; nonnegative bids; `0 ≤ ε`; `ε`-small bids |
| Standard AdWords LP dual feasibility | `DualFeasible`, `dualObjective` | formalized | `EconCSLean/Online/AdWords.lean` | none |
| AdWords LP weak duality | `paper_adwords_lp_weak_duality` | formalized | `EconCSLean/Online/MainTheorems.lean` | feasible assignment and dual-feasible variables |
| Fractional AdWords LP primal | `FractionalAssignment`, `FractionalFeasible`, `fractionalRevenue` | formalized | `EconCSLean/Online/AdWords.lean` | finite advertisers and queries |
| Integral-to-fractional embedding | `paper_adwords_integral_assignment_fractional_feasible` | formalized | `EconCSLean/Online/MainTheorems.lean` | integral assignment must be feasible |
| Fractional AdWords LP weak duality | `paper_adwords_fractional_lp_weak_duality` | formalized | `EconCSLean/Online/MainTheorems.lean` | fractional feasible assignment and dual-feasible variables |
| Competitive-ratio certificate | `CompetitiveRatioCertificate` | formalized certificate interface | `EconCSLean/Online/AdWords.lean` | supply a certificate only when using this reusable exact interface |
| Primal-dual competitive certificate | `paper_adwords_competitive_of_primal_dual_certificate` | auxiliary exact wrapper formalized | `EconCSLean/Online/MainTheorems.lean` | not needed for the final small-bids limiting theorem |
| Balance/MSVV exact finite certificate form | `paper_adwords_balance_msvv_competitive_of_primal_dual_certificate` | auxiliary exact wrapper formalized | `EconCSLean/Online/MainTheorems.lean` | not needed for the final small-bids limiting theorem |
| History-accounting objective seam | `MsvvHistoryAccountingCertificate`, `paper_adwords_balance_msvv_objective_bound_of_history_accounting` | auxiliary exact wrapper formalized | `EconCSLean/Online/MainTheorems.lean` | zero-error idealization; approximate accounting theorem below is proved |
| Balance/MSVV objective-bound seam | `MsvvObjectiveBoundCertificate`, `paper_adwords_balance_msvv_competitive_of_objective_bound` | auxiliary exact wrapper formalized | `EconCSLean/Online/MainTheorems.lean` | zero-error idealization; finite small-bids theorem below is proved |
| Approximate small-bids objective seam | `MsvvHistoryApproxAccountingCertificate`, `MsvvApproxObjectiveBoundCertificate`, `paper_adwords_balance_msvv_history_approx_accounting_with_explicit_error`, `paper_adwords_balance_msvv_approx_objective_bound_with_explicit_error`, `paper_adwords_balance_msvv_approx_competitive_with_explicit_history_error`, `paper_adwords_balance_msvv_approx_competitive_with_error_bound`, `paper_adwords_balance_msvv_approx_competitive_with_query_sum_error_bound`, `paper_adwords_balance_msvv_finRange_approx_competitive_with_query_sum_error_bound`, `paper_adwords_balance_msvv_approx_competitive_up_to_delta`, `paper_adwords_balance_msvv_finRange_approx_competitive_up_to_delta`, `paper_adwords_balance_msvv_approx_competitive_up_to_delta_of_small_bids_threshold`, `paper_adwords_balance_msvv_finRange_approx_competitive_up_to_delta_of_small_bids_threshold`, `paper_adwords_balance_msvv_competitive_of_arbitrarily_small_bids_threshold`, `paper_adwords_balance_msvv_finRange_competitive_of_arbitrarily_small_bids_threshold`, `paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta`, `paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta_of_small_bids_threshold`, `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_error_eventually`, `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_small_bids_threshold`, `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_error_eventually_of_offline_opt_convergence`, `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_small_bids_threshold_of_offline_opt_convergence` | finite explicit-error theorem, algebraic/query-sum error bounds, canonical `Fin n` query-sum wrappers, delta-form theorem, explicit small-bids threshold, limit-style wrapper, family-level eventual additive-`δ` theorem, and sequence-limit theorem formalized | `EconCSLean/Online/MainTheorems.lean` | none beyond theorem hypotheses |
| Small-bids limit family | `MsvvSmallBidsLimitFamily` | formalized | `EconCSLean/Online/AdWords.lean` | a user supplies the finite instance family, vanishing threshold, and convergence fields |
| Full MSVV competitive theorem | `paper_adwords_balance_msvv_competitive_of_small_bids_limit_family` | formalized family-level theorem | `EconCSLean/Online/MainTheorems.lean` | none beyond `MsvvSmallBidsLimitFamily` fields |

## Current Formalization Plan

1. Keep the finite LP and offline benchmark layer stable: `offlineOptimumValue`,
   `FractionalFeasible`, `DualFeasible`, and
   `paper_adwords_fractional_lp_weak_duality` are the reusable core.
2. The online history/fold for feasible choice rules and the canonical
   Balance/MSVV choice rule is formalized. Next connect per-query choices to
   primal and dual variable updates.
3. The stepwise/primal-dual charging argument is formalized for the finite
   small-bids statement. The non-exhausted and exhausted query-dual charges,
   history/query-dual summation, revenue trace, normalized advertiser-alpha
   increment bound, and explicit history error are packaged as
   `MsvvHistoryApproxAccountingCertificate` and derive
   `paper_adwords_balance_msvv_approx_competitive_with_explicit_history_error`.
   The combined explicit error is bounded by
   `ε * (Real.exp 1 + 1) * historyMaxBidSum`, exposed through
   `paper_adwords_balance_msvv_approx_competitive_with_error_bound` and
   reindexed as a finite query sum in
   `paper_adwords_balance_msvv_approx_competitive_with_query_sum_error_bound`;
   the delta-form wrapper is
   `paper_adwords_balance_msvv_approx_competitive_up_to_delta`, and the
   explicit-threshold wrapper is
   `paper_adwords_balance_msvv_approx_competitive_up_to_delta_of_small_bids_threshold`.
   The limit-style wrapper
   `paper_adwords_balance_msvv_competitive_of_arbitrarily_small_bids_threshold`
   removes the additive term under an arbitrarily-small-threshold assumption.
   Canonical `Fin n` wrappers now use `List.finRange n` to discharge nodup and
   coverage assumptions and state the error directly as
   `ε * (Real.exp 1 + 1) * ∑ q, maxBidForQuery q`.
   The family-level wrappers
   `paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta` and
   `paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta_of_small_bids_threshold`
   state the small-bids limiting seam over dependent finite query types
   `Fin (n k)`.
   The sequence-limit wrappers
   `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_error_eventually`
   and
   `paper_adwords_balance_msvv_finRange_family_limit_competitive_of_small_bids_threshold`
   use `Sequence.SeqTendsTo` to convert eventual additive guarantees and
   convergence of the two real sides into a limiting inequality.
   The ordinary-offline-optimum wrappers use
   `Sequence.SeqTendsTo.const_mul_of_nonneg` to state the conclusion in the
   paper-facing form `msvvRatio * optLimit ≤ revenueLimit`.
   The ideal exact seam `MsvvHistoryAccountingCertificate` remains available for
   a zero-error limiting theorem.
4. The paper-facing limiting theorem is
   `paper_adwords_balance_msvv_competitive_of_small_bids_limit_family`: any
   `MsvvSmallBidsLimitFamily` has limiting guarantee
   `msvvRatio * optLimit ≤ revenueLimit`.
5. Section 6 and Section 8 extension reductions are now formalized as
   effective-bid transformations: arbitrary effective charges, click-through
   rates, advertiser weights, delayed-entry/availability masks, and slot-query
   expansion. The slot expansion is the independent slot-query reduction; a
   stronger per-page distinct-advertiser model would require an additional
   feasibility layer.
6. Section 7 now has the finite Yao/minimax expectation lemma, the uniform
   permutation distribution over bidders, a uniform-permutation relabeling
   theorem, an observed-prefix suffix-swap invariance theorem, the paper's
   explicit finite harmonic revenue-bound expression, the logarithmic
   tail-spend proof, the finite layer-count estimate, and the eventual
   harmonic-cap theorem
   `theorem9_harmonic_eventually_le_msvvRatio_add`. The public wrapper
   `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta`
   now needs only the deterministic round-allocation inequalities. The concrete
   endpoint for realized-payoff models is now formalized via
   `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family_of_realized_revenue`.
