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

The PDF is cached locally as `MSVV07AdWords.pdf` and ignored by the
paper-folder `.gitignore`. The extracted text cache `MSVV07AdWords.txt` is used
for named-statement searches; refresh it only if the source PDF changes.

## Central Theorem Files

- `papers/MSVV07AdWords/PaperFacingTheorems.lean`: human-facing Lean ledger.
  It exposes the paper formulas for budgets, bids, revenue, feasibility,
  small bids, Balance/MSVV scaled bids, Theorem 8's small-bids limit family,
  and Theorem 9's finite hard distribution endpoint.
- `papers/MSVV07AdWords/MainTheorems.lean`: detailed paper-facing wrappers.
- `EconCSLib/Algorithms/Online/AdWords.lean`: reusable finite AdWords model,
  LP weak duality, online history, Balance/MSVV accounting, and small-bids
  limiting theorem.
- `papers/MSVV07AdWords/AdWordsExtensions.lean`: Section 6 and Section 8
  effective-bid reductions.
- `papers/MSVV07AdWords/AdWordsLowerBound.lean`: Section 7 Yao/permutation
  lower-bound interface and concrete integral-prefix endpoint.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Sections 2--3 finite AdWords model | `MSVV07PaperFacing.PaperInstance`, `MSVV07PaperFacing.paperSpend`, `MSVV07PaperFacing.paperRevenue`, `MSVV07PaperFacing.paperFeasible`, `AdWordsInstance` | formalized | `PaperFacingTheorems.lean`, `AdWords.lean` | None |
| Small-bids condition | `MSVV07PaperFacing.paperSmallBids`, `AdWordsInstance.SmallBids`, `paper_adwords_small_bids_blocked_advertiser_spent_fraction` | formalized | `PaperFacingTheorems.lean`, `MainTheorems.lean` | None |
| Balance/MSVV tradeoff and scaled bid | `MSVV07PaperFacing.paperTradeoff`, `MSVV07PaperFacing.paperBalanceScore`, `MSVV07PaperFacing.paperIsBalanceChoice`, `AdWordsInstance.balanceDiscount`, `AdWordsInstance.balanceScore`, `AdWordsInstance.IsBalanceChoice` | formalized | `PaperFacingTheorems.lean`, `AdWords.lean` | None |
| Offline optimum and LP weak duality | `section2_offline_optimum_exists`, `section2_fractional_lp_weak_duality`, `paper_adwords_lp_weak_duality`, `paper_adwords_fractional_lp_weak_duality` | formalized | `PaperFacingTheorems.lean`, `MainTheorems.lean` | None |
| Balance/MSVV online feasibility and revenue accounting | `section3_balance_run_assignment_feasible`, `paper_adwords_balance_run_assignment_feasible`, `paper_adwords_run_revenue_eq_history_revenue_charge`, `paper_adwords_balance_charge_le_run_revenue` | formalized | `PaperFacingTheorems.lean`, `MainTheorems.lean` | None |
| Section 4 Lemmas 1--3, equal-bids factor-revealing LP route | none source-numbered | not formalized | none | Previous status: not formalized one-for-one; bypassed by the finite LP/dual-fitting route |
| Section 5 Lemmas 4--7, source tradeoff-revealing LP route | none source-numbered | not formalized | none | Previous status: not formalized one-for-one; bypassed by the finite LP/dual-fitting route |
| Theorem 8, Balance/MSVV competitive ratio | `MSVV07PaperFacing.theorem8_finite_explicit_error`, `MSVV07PaperFacing.PaperSmallBidsLimitFamily`, `MSVV07PaperFacing.theorem8_balance_msvv_competitive_of_small_bids_limit_family`, `paper_adwords_balance_msvv_competitive_of_small_bids_limit_family` | formalized with caveat | `PaperFacingTheorems.lean`, `MainTheorems.lean`, `AdWords.lean` | Previous status: formalized with proof-strategy deviation; no extra certificate; theorem assumes the paper-level finite small-bids limiting family fields |
| Section 6 arbitrary effective charges | `section6_effective_bids_small_bids`, `paper_adwords_effective_bids_small_bids` | formalized | `PaperFacingTheorems.lean`, `MainTheorems.lean` | None |
| Section 6 click-through rates | `section6_click_through_rates_small_bids`, `paper_adwords_click_through_rates_small_bids` | formalized | `PaperFacingTheorems.lean`, `MainTheorems.lean` | None |
| Section 6 advertiser availability / delayed entry | `section6_availability_small_bids`, `paper_adwords_availability_small_bids` | formalized | `PaperFacingTheorems.lean`, `MainTheorems.lean` | None |
| Section 6 multiple slots | `section6_multiple_slots_small_bids`, `paper_adwords_multiple_slots_small_bids`, `AdWordsInstance.withSlotsDistinctChoice` | formalized | `PaperFacingTheorems.lean`, `MainTheorems.lean`, `AdWordsExtensions.lean` | None |
| Section 8 advertiser weights | `section8_weighted_bids_small_bids`, `paper_adwords_weighted_bids_small_bids` | formalized | `PaperFacingTheorems.lean`, `MainTheorems.lean` | None |
| Section 7 Yao/permutation hard distribution | `theorem9HardDistribution`, `uniformPermutationDistribution`, `uniformPermutationExpectation_eq_of_relabel`, `theorem9ActualEligibleBidders`, `theorem9ObservedPrefix` | formalized | `PaperFacingTheorems.lean`, `AdWordsLowerBound.lean` | None |
| Theorem 9 harmonic cap | `theorem9_harmonic_eventually_le_msvv_ratio_add_delta`, `paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta` | formalized | `PaperFacingTheorems.lean`, `MainTheorems.lean`, `AdWordsLowerBound.lean` | None |
| Theorem 9 lower bound | `theorem9IntegralPrefixAlgorithm`, `theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio`, `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms` | formalized with caveat | `PaperFacingTheorems.lean`, `MainTheorems.lean`, `AdWordsLowerBound.lean` | Previous status: formalized for the finite integral-prefix model and capped normalized spend; source's broad "no randomized online algorithm" is represented by the finite prefix-algorithm model; richer realized revenue uses the explicit pointwise bound below |
| Theorem 9 realized-revenue bridge | `theorem9_no_randomized_realized_revenue_algorithm_beats_msvv_ratio`, `paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms_of_realized_revenue` | conditional | `PaperFacingTheorems.lean`, `MainTheorems.lean` | requires pointwise `normalizedRevenue ≤ theorem9CappedNormalizedRevenue` |

## Source-Audit Notes

The cached text contains the active-slab/query-type definitions, Lemmas 1--7,
Theorem 8, Section 6 extensions, Theorem 9, and Section 8 weighted-bid
extension. The formalization closes the main theorem surfaces through a direct
finite LP/dual-fitting and history-accounting route rather than reproducing the
paper's factor-revealing and tradeoff-revealing LP derivation line-by-line.

`PaperFacingTheorems.lean` is now the single-file human audit target. A reviewer
can inspect that file to see the concrete formulas used in the Lean statements
and the exact assumptions on the final Theorem 8 and Theorem 9 endpoints.

## Validation

- Last targeted build: `lake build MSVV07AdWords`
- Last placeholder audit: `rg -n "\\bsorry\\b|\\badmit\\b|axiom" papers/MSVV07AdWords EconCSLib/Algorithms/Online --glob '*.lean'`
- Final report: `FINAL_VALIDATION_REPORT.md`
