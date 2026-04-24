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
`AdWords.lean`.

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
| Balance/MSVV discount, dual-alpha, and scaled bid | `balanceDiscount`, `msvvDualAlpha`, `balanceScore`, `slackScore` | formalized | `EconCSLean/Online/AdWords.lean` | analytic competitive proof not included |
| Slack-score dual-feasibility builder | `paper_adwords_dual_feasible_of_slack_score_bound` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative alpha/beta and pointwise slack-score cover |
| Max-slack query duals | `maxSlackBeta`, `paper_adwords_dual_feasible_max_slack_beta` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonempty finite advertiser type |
| Assignment-induced MSVV duals | `msvvAlphaFromAssignment`, `paper_adwords_dual_feasible_msvv_assignment` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonempty finite advertiser type |
| MSVV ratio | `msvvRatio`, `msvvRatio_pos`, `msvvRatio_lt_one` | formalized | `EconCSLean/Online/AdWords.lean` | none |
| Balance/MSVV next-query choice exists | `paper_adwords_balance_choice_exists` | formalized | `EconCSLean/Online/MainTheorems.lean` | at least one advertiser can accept the query |
| Online history state and run fold | `HistoryState`, `stepHistoryState`, `runHistoryState`, `runAssignment` | formalized | `EconCSLean/Online/AdWords.lean` | repeated query IDs are skipped after first sighting |
| Feasible choice rules preserve feasibility | `paper_adwords_run_assignment_feasible` | formalized | `EconCSLean/Online/MainTheorems.lean` | choice rule must satisfy `ChoiceRuleFeasible` |
| Balance/MSVV run is feasible | `paper_adwords_balance_run_assignment_feasible` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative budgets |
| Balance/MSVV assigns only seen query IDs | `paper_adwords_balance_assignment_assigned_only_from_history` | formalized | `EconCSLean/Online/MainTheorems.lean` | nonnegative budgets |
| Standard AdWords LP dual feasibility | `DualFeasible`, `dualObjective` | formalized | `EconCSLean/Online/AdWords.lean` | none |
| AdWords LP weak duality | `paper_adwords_lp_weak_duality` | formalized | `EconCSLean/Online/MainTheorems.lean` | feasible assignment and dual-feasible variables |
| Fractional AdWords LP primal | `FractionalAssignment`, `FractionalFeasible`, `fractionalRevenue` | formalized | `EconCSLean/Online/AdWords.lean` | finite advertisers and queries |
| Integral-to-fractional embedding | `paper_adwords_integral_assignment_fractional_feasible` | formalized | `EconCSLean/Online/MainTheorems.lean` | integral assignment must be feasible |
| Fractional AdWords LP weak duality | `paper_adwords_fractional_lp_weak_duality` | formalized | `EconCSLean/Online/MainTheorems.lean` | fractional feasible assignment and dual-feasible variables |
| Competitive-ratio certificate | `CompetitiveRatioCertificate` | formalized certificate interface | `EconCSLean/Online/AdWords.lean` | certificate must be supplied by algorithm analysis |
| Primal-dual competitive certificate | `paper_adwords_competitive_of_primal_dual_certificate` | conditional theorem wrapper formalized | `EconCSLean/Online/MainTheorems.lean` | construct the Balance/MSVV certificate for ratio `1 - 1 / Real.exp 1` and formalize small-bids limiting argument |
| Balance/MSVV `1 - 1/e` theorem seam | `paper_adwords_balance_msvv_competitive_of_primal_dual_certificate` | conditional theorem wrapper formalized | `EconCSLean/Online/MainTheorems.lean` | construct the Balance/MSVV primal-dual certificate |
| Balance/MSVV objective-bound seam | `MsvvObjectiveBoundCertificate`, `paper_adwords_balance_msvv_competitive_of_objective_bound` | conditional theorem wrapper formalized | `EconCSLean/Online/MainTheorems.lean` | prove the scaled dual-objective bound for the assignment-induced MSVV duals |
| Full MSVV competitive theorem | none | not started | none | online history/algorithm execution, tradeoff-revealing LP, and small-bids analysis |

## Current Formalization Plan

1. Keep the finite LP and offline benchmark layer stable: `offlineOptimumValue`,
   `FractionalFeasible`, `DualFeasible`, and
   `paper_adwords_fractional_lp_weak_duality` are the reusable core.
2. The online history/fold for feasible choice rules and the canonical
   Balance/MSVV choice rule is formalized. Next connect per-query choices to
   primal and dual variable updates.
3. Then prove the stepwise/primal-dual charging argument as
   `MsvvObjectiveBoundCertificate` for the Balance run.
4. Finally connect that certificate to the paper's `1 - 1/e` guarantee and
   isolate the small-bids limiting argument as a separate theorem seam.
