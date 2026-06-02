# AdWords and Generalized Online Matching

Machine-readable status source: [`status.json`](status.json).

## Source Version

- Paper: *AdWords and Generalized Online Matching*
- Authors: Aranyak Mehta, Amin Saberi, Umesh Vazirani, and Vijay V. Vazirani
- Version formalized: Journal of the ACM 54(5), 2007, Article 22
- Official DOI: https://doi.org/10.1145/1284320.1284321
- Official ACM URL: https://dl.acm.org/doi/10.1145/1284320.1284321
- Award listing: https://www.sigecom.org/award-tot.html
- Public author PDF: https://people.eecs.berkeley.edu/~vazirani/pubs/adwords.pdf
- Accessed: 2026-04-24

The PDF is cached locally as `MSVV07AdWords.pdf` and ignored by the
paper-folder `.gitignore`. A local extracted text cache may be regenerated for
named-statement searches, but is ignored in the public repository.

## Central Theorem Files

- `papers/MSVV07AdWords/PaperInterface.lean`: compact human-facing Lean ledger
  with the compact paper-facing review declarations.
  It exposes the paper formulas for budgets, bids, revenue, feasibility,
  small bids, Balance/MSVV scaled bids, Theorem 8's small-bids limit family,
  Section 6/8 composed guarantees, both the slot-expanded and page-level
  multiple-slot guarantees, and Theorem 9's finite hard distribution and
  lower-bound endpoints.
- `papers/MSVV07AdWords/ProofInterface.lean`: broader source-route and
  proof-facing interface retained for audit aliases.
- `papers/MSVV07AdWords/PostPaperAudit.lean`: importable post-verification
  endpoint ledger with thin wrappers around the human-facing theorem surface.
- `papers/MSVV07AdWords/SourceLemmas.lean`: source-route Section 4--5
  Lemmas 1--7 as standalone order/algebra/limit lemmas.
- `papers/MSVV07AdWords/MainTheorems.lean`: detailed paper-facing wrappers.
- `EconCSLib/Algorithms/Online/AdWords.lean`: reusable finite AdWords model,
  LP weak duality, online history, Balance/MSVV accounting, and small-bids
  limiting theorem.
- `papers/MSVV07AdWords/AdWordsExtensions.lean`: Section 6 and Section 8
  effective-bid reductions and slot-expanded distinctness support.
- `papers/MSVV07AdWords/AdWordsBatch.lean`: source-shaped Section 6 page-level
  multiple-slot model, top-`n_q` Balance rule, page offline optimum, and finite
  explicit MSVV guarantee.
- `papers/MSVV07AdWords/AdWordsLowerBound.lean`: Section 7 Yao/permutation
  lower-bound interface and concrete integral-prefix endpoint.
- `papers/MSVV07AdWords/START_HERE_NEXT_AGENT.md`: validation handoff note.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Sections 2--3 finite AdWords model | `MSVV07PaperFacing.PaperInstance`, `MSVV07PaperFacing.paperSpend`, `MSVV07PaperFacing.paperRevenue`, `MSVV07PaperFacing.paperFeasible`, `AdWordsInstance` | formalized | `PaperInterface.lean`, `AdWords.lean` | None |
| Small-bids condition | `MSVV07PaperFacing.paperSmallBids`, `AdWordsInstance.SmallBids`, `paper_adwords_small_bids_blocked_advertiser_spent_fraction` | formalized | `PaperInterface.lean`, `MainTheorems.lean` | None |
| Balance/MSVV tradeoff and scaled bid | `MSVV07PaperFacing.paperTradeoff`, `MSVV07PaperFacing.paperBalanceScore`, `MSVV07PaperFacing.paperIsBalanceChoice`, `AdWordsInstance.balanceDiscount`, `AdWordsInstance.balanceScore`, `AdWordsInstance.IsBalanceChoice` | formalized | `PaperInterface.lean`, `AdWords.lean` | None |
| Offline optimum and LP weak duality | `Proof.section2_offline_optimum_exists`, `Proof.section2_fractional_lp_weak_duality`, `paper_adwords_lp_weak_duality`, `paper_adwords_fractional_lp_weak_duality` | formalized | `ProofInterface.lean`, `MainTheorems.lean` | None |
| Balance/MSVV online feasibility and revenue accounting | `Proof.section3_balance_choice_score_ge_of_can_assign`, `Proof.section3_balance_run_assignment_feasible`, `paper_adwords_balance_run_assignment_feasible`, `paper_adwords_run_revenue_eq_history_revenue_charge`, `paper_adwords_balance_charge_le_run_revenue` | formalized | `ProofInterface.lean`, `MainTheorems.lean` | None |
| Section 4 Lemmas 1--3, equal-bids factor-revealing LP route | `Proof.paperTradeoff_antitone`, `Proof.paperTradeoff_strictAnti`, `Proof.section4_lemma1_balance_pays_no_later_slab`, `Proof.section4_lemma1_balance_pays_no_later_spent_fraction_of_balance_choice`, `Proof.section4_lemma2_factor_revealing_lp_constraint`, `Proof.section4_lemma3_factor_revealing_lp_value_tends`, `Proof.section4_lemma3_primal_candidate_row_tight`, `Proof.section4_lemma3_dual_candidate_row_tight`, `Proof.section4_lemma3_primal_candidate_objective_value`, `Proof.section4_lemma3_dual_candidate_objective_value`, `Proof.section4_lemma3_factor_revealing_lp_optimal`, `Proof.section4_lemma3_factor_revealing_lp_primal_candidate_is_maximizer`, `Proof.section4_lemma3_factor_revealing_lp_upper_bound`, corresponding `MSVV07PaperFacing.PostPaperAudit.audit_section4_lemma*` wrappers | formalized | `ProofInterface.lean`, `SourceLemmas.lean`, `PostPaperAudit.lean` | None |
| Section 5 closed Balance aggregate accounting | `Proof.section5_lemma6_per_query_tradeoff_of_balance_choice_spent_fraction`, `Proof.section5_balance_msvv_scaled_dual_objective_le_revenue_add_explicit_error`, corresponding `MSVV07PaperFacing.PostPaperAudit.audit_section5_*` wrappers | formalized | `ProofInterface.lean`, `PostPaperAudit.lean` | None |
| Theorem 8, Balance/MSVV competitive ratio | `MSVV07PaperFacing.theorem8_finite_explicit_error`, `MSVV07PaperFacing.PaperSmallBidsLimitFamily`, `MSVV07PaperFacing.theorem8_balance_msvv_competitive_of_small_bids_limit_family`, `paper_adwords_balance_msvv_competitive_of_small_bids_limit_family`, corresponding audit wrappers | formalized | `PaperInterface.lean`, `MainTheorems.lean`, `AdWords.lean`, `PostPaperAudit.lean` | None |
| Section 6 different budgets and nonexhaustive optimum | `section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error` | formalized | `PaperInterface.lean`, `PostPaperAudit.lean` | None; both are absorbed by the base finite AdWords model |
| Section 6 arbitrary effective charges | `section6_effective_bids_small_bids`, `section6_effective_bids_theorem8_finite_explicit_error`, `paper_adwords_effective_bids_small_bids` | formalized | `PaperInterface.lean`, `ProofInterface.lean`, `MainTheorems.lean` | None |
| Section 6 next-highest-bid charges | `section6_next_highest_bid_all`, `section6_next_highest_bid_alive`, `section6_next_highest_bid_all_theorem8_finite_explicit_error`, `section6_next_highest_bid_alive_theorem8_finite_explicit_error` | formalized | `PaperInterface.lean`, `PostPaperAudit.lean` | None |
| Section 6 click-through rates | `section6_click_through_rates_small_bids`, `section6_click_through_rates_theorem8_finite_explicit_error`, `paper_adwords_click_through_rates_small_bids` | formalized | `PaperInterface.lean`, `ProofInterface.lean`, `MainTheorems.lean` | None |
| Section 6 advertiser availability / delayed entry | `section6_availability_small_bids`, `section6_availability_theorem8_finite_explicit_error`, `paper_adwords_availability_small_bids` | formalized | `PaperInterface.lean`, `ProofInterface.lean`, `MainTheorems.lean` | None |
| Section 6 multiple slots | `section6_multiple_slots_small_bids`, `section6_multiple_slots_theorem8_finite_explicit_error`, `section6_page_top_balance_theorem8_finite_explicit_error`, `section6_multiple_slots_distinct_choice_run_assignment_per_page_distinct`, `paper_adwords_multiple_slots_small_bids`, `AdWordsInstance.pageTopBalanceRule`, `AdWordsInstance.withSlotsDistinctChoice` | formalized | `PaperInterface.lean`, `ProofInterface.lean`, `MainTheorems.lean`, `AdWordsBatch.lean`, `AdWordsExtensions.lean`, `PostPaperAudit.lean` | None; the source-shaped page-level top-`n_q` distinct-bidder rule and the slot-expanded finite guarantee are both closed. |
| Section 8 advertiser weights | `section8_weighted_bids_small_bids`, `section8_weighted_bids_theorem8_finite_explicit_error`, `section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids`, `paper_adwords_weighted_bids_small_bids` | formalized | `PaperInterface.lean`, `ProofInterface.lean`, `MainTheorems.lean` | None; the theorem is stated for the weighted effective-bid small-bids regime |
| Section 7 Yao/permutation hard distribution | `theorem9HardDistribution`, `uniformPermutationDistribution`, `uniformPermutationExpectation_eq_of_relabel`, `theorem9ActualEligibleBidders`, `theorem9ObservedPrefix` | formalized | `PaperInterface.lean`, `AdWordsLowerBound.lean` | None |
| Theorem 9 harmonic cap | `theorem9_harmonic_eventually_le_msvv_ratio_add_delta`, `paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta`, `MSVV07PaperFacing.PostPaperAudit.audit_theorem9_harmonic_eventually_le_msvv_ratio_add_delta` | formalized | `ProofInterface.lean`, `MainTheorems.lean`, `AdWordsLowerBound.lean`, `PostPaperAudit.lean` | None |
| Theorem 9 lower bound | `theorem9FeasiblePrefixRuleFamily`, `theorem9_no_randomized_feasible_prefix_rule_family_beats_msvv_ratio`, `theorem9IntegralPrefixAlgorithm`, `theorem9RandomizedOnlineAlgorithm`, `theorem9_capped_normalized_revenue_eq_prefix_spend`, `theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio`, `theorem9_no_randomized_online_algorithm_beats_msvv_ratio`, `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_prefix_rule_family`, `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms`, `MSVV07PaperFacing.PostPaperAudit.audit_theorem9_no_randomized_feasible_prefix_rule_family_beats_msvv_ratio` | formalized | `PaperInterface.lean`, `ProofInterface.lean`, `MainTheorems.lean`, `AdWordsLowerBound.lean`, `PostPaperAudit.lean` | None; the broad endpoint covers finite feasible observed-prefix allocation rules, with integral prefix algorithms retained as a concrete specialization |

## Source-Audit Notes

The source audit identified the active-slab/query-type definitions, Lemmas 1--7,
Theorem 8, Section 6 extensions, Theorem 9, and Section 8 weighted-bid
extension. The formalization closes the paper-facing theorem surfaces and
separately exposes the source-route factor-revealing and tradeoff-revealing LP
lemmas as proof-route audit declarations. The source-route Theorem 8 surface
includes exact finite wrappers for the displayed dual candidate `y*`, including
dual feasibility, exact base value, pointwise/fiber accounting composition, and
query-accounting composition into the tradeoff-LP upper bound. These local
proof-route lemmas are not conditional substitutes for the paper theorem; the
closed competitive-ratio endpoint is the finite LP/dual-fitting small-bids
theorem and its limit wrapper. Removing the local transcript/accounting
hypotheses from the generic source-route helpers would make those helper
statements false for arbitrary vectors; the concrete paper endpoint is closed
through the Balance history-accounting theorem.

Auxiliary source-route helper surfaces:

- Section 5 source tradeoff-revealing LP helpers: `section5_lemma4_*`,
  `section5_lemma5_*`, `section5_lemma6_*`, and `section5_lemma7_*`.
  These are checked algebra/accounting wrappers for the source proof route.
- Theorem 8 source-route LP certificate helpers:
  `theorem8_delta_dot_y_eq_weighted_perturbation`,
  `theorem8_dual_induced_tradeoff_antitone`,
  `theorem8_dual_candidate_psi_nonnegative`,
  `theorem8_dual_candidate_psi_closed_form`, and `theorem8_source_route_*`.
  These helper declarations audit the source proof route; the non-conditional
  Theorem 8 endpoint is the finite explicit theorem plus the small-bids limit.

`PaperInterface.lean` is now the compact human audit target. A reviewer can
inspect that file to see the concrete formulas used in the Lean statements and
the exact assumptions on the final Theorem 8 and Theorem 9 endpoints. The
source-route proof ledger remains importable through `ProofInterface.lean` and
`PostPaperAudit.lean`.

## Validation

- Last targeted build: `lake build MSVV07AdWords`
  (with `PostPaperAudit.lean` imported by the root paper module).
- Last no-placeholder audit: `rg -n "\\bsorry\\b|\\badmit\\b|axiom" papers/MSVV07AdWords EconCSLib/Algorithms/Online --glob '*.lean'`
  (no hits).
- Last dashboard precheck: `python3 scripts/review_dashboard.py --paper MSVV07AdWords --precheck` (`0/39`
  human review entries, no stale rows, no mismatches; external review state,
  not a Lean formalization gap).
- Post-paper audit ledger: `PostPaperAudit.lean`, imported by
  `papers/MSVV07AdWords.lean`.
- DAG artifact status: TikZ source exists, and `DependencyDAG.pdf` was
  regenerated locally with `latexmk` for artifact inspection.
- Final report: `FINAL_VALIDATION_REPORT.md`
