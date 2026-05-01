import MSVV07AdWords.MainTheorems

/-!
# Quiet Paper-Facing Theorem Ledger

This file is the Lean-oriented declaration index for the AdWords paper
formalization. It intentionally avoids top-level `#check` commands because this
module is imported by `MSVV07AdWords` and bare `#check` commands print every
theorem type during aggregate builds. Each check is wrapped in
`#guard_msgs(drop info)`, so missing or renamed declarations still fail the
build, while successful builds produce no declaration-ledger spam.
-/

namespace EconCSLib
namespace Online

-- 1) Core model and LP primitives

-- Finite AdWords instance with advertiser budgets and query bids.
#guard_msgs(drop info) in
#check AdWordsInstance

-- A concrete integral assignment map `Query → Option Advertiser` (`none` means no assignment).
#guard_msgs(drop info) in
#check AdWordsInstance.Assignment

-- A fractional LP assignment `Advertiser → Query → ℝ`.
#guard_msgs(drop info) in
#check AdWordsInstance.FractionalAssignment

-- Budget feasibility and related LP predicates used throughout the paper.
#guard_msgs(drop info) in
#check AdWordsInstance.Feasible
#guard_msgs(drop info) in
#check AdWordsInstance.FractionalFeasible
#guard_msgs(drop info) in
#check AdWordsInstance.ChoiceRuleFeasible
#guard_msgs(drop info) in
#check AdWordsInstance.StateInvariant

-- The finite offline benchmark: integral and fractional value terms.
#guard_msgs(drop info) in
#check AdWordsInstance.offlineOptimumAssignment
#guard_msgs(drop info) in
#check AdWordsInstance.offlineOptimumValue
#guard_msgs(drop info) in
#check AdWordsInstance.revenue
#guard_msgs(drop info) in
#check AdWordsInstance.fractionalRevenue

-- Dual LP side: `dualObjective α β` and `DualFeasible α β`.
#guard_msgs(drop info) in
#check AdWordsInstance.DualFeasible
#guard_msgs(drop info) in
#check AdWordsInstance.dualObjective

-- LP setup and weak duality wrappers.
#guard_msgs(drop info) in
#check paper_adwords_empty_assignment_feasible
#guard_msgs(drop info) in
#check paper_adwords_offline_optimum_exists
#guard_msgs(drop info) in
#check paper_adwords_revenue_le_total_budget_of_feasible
#guard_msgs(drop info) in
#check paper_adwords_lp_weak_duality
#guard_msgs(drop info) in
#check paper_adwords_integral_assignment_fractional_feasible
#guard_msgs(drop info) in
#check paper_adwords_fractional_lp_weak_duality

-- Slack and max-slack dual constructors used in the Balance/MSVV reduction.
#guard_msgs(drop info) in
#check paper_adwords_dual_feasible_of_slack_score_bound
#guard_msgs(drop info) in
#check paper_adwords_dual_feasible_max_slack_beta
#guard_msgs(drop info) in
#check paper_adwords_dual_feasible_msvv_assignment
#guard_msgs(drop info) in
#check paper_adwords_dual_feasible_msvv_normalized_assignment

-- Choice rule existence and basic online run feasibility.
#guard_msgs(drop info) in
#check paper_adwords_balance_choice_exists
#guard_msgs(drop info) in
#check paper_adwords_run_assignment_feasible
#guard_msgs(drop info) in
#check paper_adwords_balance_run_assignment_feasible

-- 2) Online semantics and history accounting

-- The online run history state and assignment unfold.
#guard_msgs(drop info) in
#check AdWordsInstance.HistoryState
#guard_msgs(drop info) in
#check AdWordsInstance.historyFinset
#guard_msgs(drop info) in
#check AdWordsInstance.initialHistoryState
#guard_msgs(drop info) in
#check AdWordsInstance.stepHistoryState
#guard_msgs(drop info) in
#check AdWordsInstance.runHistoryState
#guard_msgs(drop info) in
#check AdWordsInstance.runHistoryStateFrom
#guard_msgs(drop info) in
#check AdWordsInstance.runAssignment

-- History-local properties used by the proof.
#guard_msgs(drop info) in
#check paper_adwords_balance_assignment_assigned_only_from_history
#guard_msgs(drop info) in
#check paper_adwords_spend_monotone_over_history
#guard_msgs(drop info) in
#check paper_adwords_run_revenue_eq_history_revenue_charge
#guard_msgs(drop info) in
#check paper_adwords_balance_charge_le_run_revenue

-- 3) Per-query dual charge lemmas

-- Final slack-score and beta bound lemmas for admissible/exhausted advertisers.
#guard_msgs(drop info) in
#check paper_adwords_final_slack_score_le_initial_balance_score
#guard_msgs(drop info) in
#check paper_adwords_max_slack_beta_le_balance_score_of_all_can_assign
#guard_msgs(drop info) in
#check paper_adwords_msvv_ratio_mul_normalized_max_slack_beta_le_balance_score_of_all_can_assign
#guard_msgs(drop info) in
#check paper_adwords_blocked_advertiser_final_alpha_ge_exp_neg_epsilon
#guard_msgs(drop info) in
#check paper_adwords_blocked_advertiser_final_slack_score_le_error
#guard_msgs(drop info) in
#check paper_adwords_msvv_ratio_mul_blocked_advertiser_normalized_final_slack_score_le_error
#guard_msgs(drop info) in
#check paper_adwords_msvv_ratio_mul_normalized_max_slack_beta_le_balance_score_add_max_bid_error
#guard_msgs(drop info) in
#check paper_adwords_max_slack_beta_le_balance_score_or_max_bid_error
#guard_msgs(drop info) in
#check paper_adwords_max_slack_beta_le_balance_score_add_max_bid_error

-- Summed and normalized query-dual bounds over histories.
#guard_msgs(drop info) in
#check paper_adwords_balance_history_max_slack_beta_sum_le_charge_add_error
#guard_msgs(drop info) in
#check paper_adwords_balance_query_dual_sum_le_charge_add_error_of_history_cover
#guard_msgs(drop info) in
#check paper_adwords_msvv_ratio_mul_normalized_query_dual_sum_le_charge_add_error_of_history_cover

-- 4) Small-bids bridge and section-6/8 reductions

-- Blocking-advertiser spent-fraction bound under ε-small bids.
#guard_msgs(drop info) in
#check paper_adwords_small_bids_blocked_advertiser_spent_fraction

-- Effective-bid transformation wrappers: small-bids preserved by each mapping.
#guard_msgs(drop info) in
#check paper_adwords_effective_bids_small_bids
#guard_msgs(drop info) in
#check paper_adwords_click_through_rates_small_bids
#guard_msgs(drop info) in
#check paper_adwords_weighted_bids_small_bids
#guard_msgs(drop info) in
#check paper_adwords_availability_small_bids
#guard_msgs(drop info) in
#check paper_adwords_multiple_slots_small_bids
#guard_msgs(drop info) in
#check AdWordsInstance.withEffectiveBids
#guard_msgs(drop info) in
#check AdWordsInstance.withClickThroughRates
#guard_msgs(drop info) in
#check AdWordsInstance.withAdvertiserWeights
#guard_msgs(drop info) in
#check AdWordsInstance.withAvailability
#guard_msgs(drop info) in
#check AdWordsInstance.withSlots
#guard_msgs(drop info) in
#check AdWordsInstance.withSlotsPerPageDistinct
#guard_msgs(drop info) in
#check AdWordsInstance.withSlotsDistinctChoice

-- 5) Section-7 lower-bound reductions

-- Primitive reduction chain from paper certificates to lower-bound claim.
#guard_msgs(drop info) in
#check paper_adwords_theorem9_no_randomized_algorithm_beats_msvv_ratio_of_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_no_randomized_algorithm_beats_msvv_ratio_of_permutation_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_revenue_bound_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_round_allocation_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_pointwise_allocation_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_symmetric_pointwise_allocation_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_relabel_symmetric_pointwise_allocation_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_observed_prefix_allocation_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_no_randomized_algorithm_beats_ratio_of_feasible_observed_prefix_allocation_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_harmonic_layer_count_bound_of_log_spend_cap
#guard_msgs(drop info) in
#check paper_adwords_theorem9_bidder_spend_upper_bound_le_log_tail
#guard_msgs(drop info) in
#check paper_adwords_theorem9_harmonic_layer_count_bound
#guard_msgs(drop info) in
#check paper_adwords_theorem9_normalized_revenue_upper_bound_le_msvv_ratio_add_grid_errors
#guard_msgs(drop info) in
#check paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta_of_layer_count_bound
#guard_msgs(drop info) in
#check paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_family_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_pointwise_family_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_symmetric_pointwise_family_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_relabel_symmetric_pointwise_family_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_observed_prefix_family_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_observed_prefix_family_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_prefix_rule_family
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_choice_family_of_realized_revenue
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms_of_realized_revenue
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_layer_count_family_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_pointwise_layer_count_family_certificate
#guard_msgs(drop info) in
#check paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_symmetric_pointwise_layer_count_family_certificate

-- 6) Main Balance/MSVV primal-dual and approximation chain

-- Primal-dual template wrappers used by the finite and asymptotic analyses.
#guard_msgs(drop info) in
#check paper_adwords_competitive_of_primal_dual_certificate
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_competitive_of_primal_dual_certificate
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_objective_bound_of_history_accounting
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_competitive_of_objective_bound
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_approx_objective_bound_of_history_accounting
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_approx_competitive_of_approx_objective_bound
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_history_approx_accounting_with_explicit_error
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_approx_objective_bound_with_explicit_error
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_approx_competitive_with_explicit_history_error
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_approx_competitive_with_error_bound
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_approx_competitive_with_query_sum_error_bound
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_finRange_approx_competitive_with_query_sum_error_bound
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_approx_competitive_up_to_delta
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_finRange_approx_competitive_up_to_delta
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_approx_competitive_up_to_delta_of_small_bids_threshold
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_finRange_approx_competitive_up_to_delta_of_small_bids_threshold
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_competitive_of_arbitrarily_small_bids_threshold
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_finRange_competitive_of_arbitrarily_small_bids_threshold
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_finRange_family_eventually_up_to_delta_of_small_bids_threshold
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_finRange_family_limit_competitive_of_error_eventually
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_finRange_family_limit_competitive_of_small_bids_threshold
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_finRange_family_limit_competitive_of_error_eventually_of_offline_opt_convergence
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_finRange_family_limit_competitive_of_small_bids_threshold_of_offline_opt_convergence
#guard_msgs(drop info) in
#check paper_adwords_balance_msvv_competitive_of_small_bids_limit_family

end Online
end EconCSLib
