# Competitive Auctions and Digital Goods

## Source Version

- Paper: *Competitive Auctions and Digital Goods*
- Authors: Andrew V. Goldberg, Jason D. Hartline, and Andrew Wright
- Version checked locally: public InterTrust technical report STAR-TR-99-01, revised November 2000; folder name follows the SODA 2001 citation
- SODA listing: https://sigmod.org/publications/dblp/db/conf/soda/soda2001.html
- Public PDF mirror: https://www.cs.miami.edu/home/burt/learning/Csc597.052/docs/goldberg.pdf

The PDF is cached locally as `GHW01DigitalGoods.pdf` and ignored by the
paper-folder `.gitignore`. The extracted text cache `GHW01DigitalGoods.txt` is
used for named-statement searches; refresh it only if the source PDF changes.

## Central Theorem File

- `GHW01DigitalGoods/MainTheorems.lean`

Reusable auction definitions and theorem bodies live in
`EconCSLib/MechanismDesign/Auctions`.

## Formalization Plan

1. Close Section 8 first. Prove the reusable single-parameter mechanism fact
   that DSIC implies monotone allocation in a bidder's own bid, expose it as
   Lemma 8.1, then use the same interface for the expected-revenue upper bound
   in Theorem 8.2.
2. Use the Section 8 utilities to support the Section 9 deterministic
   characterization: formalize bid-independent deterministic auctions,
   prove Lemma 9.2, then derive Theorem 9.3 from the Section 9.1 adversarial
   construction.
3. Formalize Section 4 with a dyadic-bin certificate for the relationship
   between the multi-price benchmark `T` and fixed-price benchmark `F`, then
   discharge Corollary 4.2.
4. Return to Sections 7--9: build the weighted-pairing expectation model for
   Theorems 7.1--7.2, then discharge the remaining Section 8 and Section 9
   conditional wrappers.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Digital-goods auction interface, revenue, DSIC | `paper_digital_goods_revenue`, `paper_digital_goods_truthful` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; status note: formalized definitions; finite bidder model |
| Posted-price and threshold-auction truthfulness/IR/NPT | `paper_posted_price_truthful`, `paper_threshold_price_truthful`, `paper_own_erased_threshold_price_truthful` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; status note: formalized support; threshold must be own-bid independent; NPT needs nonnegative prices |
| Fixed-price benchmark and two-winner benchmark | `paper_two_winner_benchmark`, `paper_two_winner_fixed_price_benchmark`, `paper_single_price_revenue_le_candidate_benchmark_of_feasible` | formalized with caveat | `GHW01DigitalGoods/MainTheorems.lean` | Previous status: formalized finite support; assumes a feasible nonnegative two-winner price where needed |
| Theorem 4.1 and Corollary 4.2, fixed-price revenue lower bounds | `paper_theorem4_1_finite_candidate_benchmark_from_power_two_bins`, `paper_theorem4_1_finite_candidate_benchmark_from_log_certificate`, `paper_theorem4_1_finite_candidate_benchmark_from_logb_high_value`, `paper_corollary4_2_fixed_price_lower_bound_from_truncation` | formalized with caveat | `GHW01DigitalGoods/MainTheorems.lean` | Theorem 4.1 is closed in the natural-number dyadic form for the finite one-winner candidate fixed-price benchmark: if bids lie in `[1, 2^(m+1)]`, then `T <= 2 * (m+1) * F`; the log-certificate wrapper gives `T <= 2 * logH * F` from `(m+1 : R) <= logH`; the newest bridge derives `T <= 2 * (Real.logb 2 h + 2) * F` directly from normalized bids in `[1,h]` by taking `ceil (logb 2 h)`. The proof constructs the power-of-two classifier bins internally, proves price `1` feasible under the paper normalization, and uses an empty-bin-safe factor-two partition lemma. Corollary 4.2 truncation algebra is formalized; remaining caveat is exact paper notation/constant packaging if one requires the unrounded `log h` or `log n` presentation. |
| Lemma 6.1, random subset revenue split | `paper_aux_theorem6_2_fair_coin_lower_tail_relaxed` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; status note: formalized independent fair-coin analogue; paper states a fixed-size sample lemma; Section 6 uses the independent half-sampling variant implemented here |
| Theorem 6.2, random sampling auction guarantee | `paper_theorem6_2_deterministic_six_revenue_bound_of_large_sale_count`, `paper_aux_theorem6_2_side_sale_sample_good_probability`, `paper_aux_theorem6_2_selected_price_bad_large_sample_top_prefix_le_exp`, `paper_aux_theorem6_2_selected_offer_large_sample_count_of_alpha_h`, `paper_theorem6_2_fair_coin_revenue_bound_top_prefix_alpha_h_fin_sorted`, `paper_theorem6_2_random_sampling_measure_union_bound` | formalized with caveat | `GHW01DigitalGoods/MainTheorems.lean` | Previous status: formalized sorted-bid fair-coin form; deterministic `F <= 6R`, fair-coin sample-good probability, selected-price top-prefix `40 * exp(-alpha/72)` bound, geometric tail constant, concrete sorted `Fin n` top prefixes, and `alpha h <= F` selected-large bridge are formalized; statement uses independent half-sampling, sorted bid indexing, and a `minWinners` feasibility side condition (`3 * minWinners <= alpha`), with the finite-candidate analogue `paper_theorem6_2_fair_coin_revenue_bound_candidate_union` retained |
| Theorem 7.1, weighted pairing auction revenue | `weightedPairingExpectedRevenue`, `paper_theorem7_1_weighted_pairing_log_bound_from_classifier`, `paper_theorem7_1_weighted_pairing_log_bound_from_power_two_bins` | conditional | `GHW01DigitalGoods/MainTheorems.lean` | Weighted-pairing expected-payment/revenue formula, singleton-bin deletion algebra, per-bin constant algebra, Cauchy square-sum bridge, factor-two ranked-bin geometry, same-bin probability bound, embedding of same-bin ranked double sums into the concrete weighted-pairing revenue, log-bin-count algebra, singleton floor-sum deletion, value-sorted finset-bin ranking/injectivity, active/singleton splitting, classifier-fiber coverage/disjointness, and internally constructed `m+1` power-of-two dyadic bins for bids in `[1, 2^(m+1)]` are formalized; remaining proof boundary is converting arbitrary paper `log h` notation to this natural-number log certificate when no such certificate is supplied |
| Theorem 7.2, weighted auction benchmark bound | `paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark`, `paper_theorem7_2_tightness_ratio_certificate_of_benchmark_ge`, `paper_theorem7_2_tightness_revenue_split_by_classifier`, `paper_theorem7_2_tightness_ratio_from_classifier_benchmark_ge`, `GhwTightAgent`, `ghwTightValue`, `ghwTightTwoWinnerBenchmarkValue`, `paper_theorem7_2_tightness_totalBidValue`, `paper_theorem7_2_tightness_singlePriceRevenue_top`, `paper_theorem7_2_tightness_top_revenue_le_twoWinnerBenchmark`, `paper_theorem7_2_tightness_square_sum_le`, `paper_theorem7_2_tightness_lower_payment_le`, `paper_theorem7_2_tightness_lowerContribution_le`, `paper_theorem7_2_tightness_topContribution_le`, `paper_theorem7_2_tightness_ratio_for_repeated_bid_family` | formalized with caveat | `GHW01DigitalGoods/MainTheorems.lean` | The main lower bound is closed for the finite two-winner fixed-price benchmark: if bids lie in `[1, 2^(m+1)]`, `F^(2) >= 2 * 2^(m+1)`, `2 <= s`, and `(m+1 : R) <= s^2`, then `F^(2) <= 576 * s * W`. The proof includes the first/second case split, branch-local `4h <= T`, internally constructed power-of-two dyadic bins, canonical dyadic fixed-price tail buckets, selected-largest bucket construction, the strict finite geometric-tail proof that the largest bucket has at least two bidders, the high/low rank split, and the concrete weighted-pairing revenue bridge. The tightness construction is now closed for the repeated-bid family: lower levels are modeled as dependent finite types, each lower level contributes at most `2*2^k/(k-1)`, top-level contribution is at most `2^k` when `s^2+2 <= k`, the actual two-winner benchmark is at least the top-price revenue `s*2^k`, and the resulting weighted-pairing revenue ratio is at most `3/s` without an external nonempty typeclass assumption. Remaining caveat for the lower-bound side: exact paper `log h` notation is represented by the natural-number dyadic certificate `(m+1 : R) <= s^2`. |
| Lemma 8.1, monotone win probabilities in truthful auctions | `paper_lemma8_1_truthful_win_probability_monotone`, `paper_lemma8_1_truthful_win_probability_monotone_payments`, `paper_lemma8_1_allocation_mono_own_bid_of_truthful` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None |
| Theorem 8.2, any truthful auction has expected revenue at most fixed-price benchmark | `paper_ranked_fixed_price_revenue_le_finite_candidate_benchmark`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_certificate`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_monotone_probabilities`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_gain_bounds`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_adjacent_gain_recursion`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_truthful_cost_comparisons`, `paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_truthful_cost_comparisons`, `paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_pairwise_truthfulness`, `paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_pairwise_truthful_payments` | conditional | `GHW01DigitalGoods/MainTheorems.lean` | Current status: conditional scaffold with paper algebra formalized; the ranked fixed-price terms `V_j` are proved bounded by the actual one-winner finite fixed-price benchmark, monotone adjacent win probabilities are proved from the two Lemma 8.1-style adjacent truthfulness comparisons, and the newest wrapper uses direct expected-payment comparisons `b*p - payment` rather than a separate conditional expected-cost variable. Remaining gap is a concrete ranked randomized truthful-auction interface deriving the ranked revenue decomposition and adjacent payment comparisons from DSIC and the paper's anonymous sorted-bid model. |
| Theorem 9.1, deterministic bid-independent lower bound | `paper_theorem9_1_bid_independent_threshold_transition`, `paper_theorem9_1_transition_witness_revenue_bound`, `paper_theorem9_1_start_high_witness_revenue_bound`, `paper_theorem9_1_two_value_bid_independent_lower_bound`, `paper_theorem9_1_arbitrary_threshold_bid_independent_lower_bound`, `paper_theorem9_1_arbitrary_threshold_scaled_lower_bound`, `paper_theorem9_1_arbitrary_threshold_scaled_lower_bound_fixed_price_benchmark`, `paper_theorem9_1_bid_independent_list_rule_scaled_lower_bound_fixed_price_benchmark`, `paper_theorem9_1_count_threshold_revenue_eq_concrete_auction`, `paper_theorem9_1_concrete_count_threshold_scaled_lower_bound_fixed_price_benchmark`, `paper_theorem9_1_ratio_le_one_over_h_of_mul_revenue_le_benchmark` | formalized with caveat | `GHW01DigitalGoods/MainTheorems.lean` | Discrete threshold-transition, arbitrary-threshold binary revenue construction, concrete threshold-auction revenue bridge, canonical erased-bid-list bridge for the paper's anonymous bid-independent function `f(B_i)`, paper scale `m = h^2 alpha`, exact `R/F ≤ 1/h` ratio packaging, both witness revenue-ratio cases, and the strengthened actual one-winner finite fixed-price benchmark witness are formalized. Caveat: this is the paper's anonymous/list-of-bids model on binary inputs, not the more general identity-aware threshold interface used elsewhere in the library. |
| Lemma 9.2, truthful deterministic auctions are bid-independent | `paper_lemma9_2_deterministic_offer_payment_constant`, `paper_lemma9_2_deterministic_offer_winning_monotone`, `paper_lemma9_2_deterministic_offer_losing_prefix`, `paper_lemma9_2_deterministic_offer_bid_independent`, `paper_lemma9_2_deterministic_truthful_auction_bid_independent_slices` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None |
| Theorem 9.3, deterministic truthful lower bound | `paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold`, `paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_fixed_price_benchmark`, `paper_theorem9_3_binary_anonymous_bid_independent_revenue_representation`, `paper_theorem9_3_count_threshold_binary_anonymous_bid_independent_revenue_representation`, `paper_theorem9_3_deterministic_truthful_lower_bound_of_anonymous_bid_independent_representation`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_bid_independent_representation`, `paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_via_anonymous_bid_list`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_via_anonymous_bid_list` | conditional | `GHW01DigitalGoods/MainTheorems.lean` | Current status: conditional scaffold; reduction from count-threshold and anonymous erased-bid-list bid-independent representations to the Theorem 9.1 lower-bound witness is formalized against the actual one-winner finite fixed-price benchmark; the count-threshold-to-anonymous-list bridge is closed by counting high/low values in the erased list; the paper ratio `R/F <= 1/h` is packaged with the side condition `alpha*h <= F`; Lemma 9.2 auction-level slices are closed; remaining gap is conversion from general critical-price slices to the anonymous binary bid-list representation. |

## Source-Audit Notes

The cached text contains Theorem 4.1, Corollary 4.2, Lemma 6.1, Theorem 6.2,
Theorems 7.1--7.2, Lemma 8.1, Theorem 8.2, Theorem 9.1, Lemma 9.2, and Theorem
9.3. Current Lean coverage includes the reusable digital-goods mechanism layer,
fixed-price benchmark support, deterministic RSOP-style truthfulness skeleton,
Section 6 deterministic/probabilistic independent-sampling bridges with the
paper's top-prefix exponential constants, the Section 7 concrete factor-two
ranked-bin weighted-pairing bridge, the closed Theorem 4.1 natural-number
dyadic and `Real.logb 2 h + 2` forms, the closed Theorem 7.2 natural-number
dyadic lower-bound and repeated-bid tightness-family endpoints, Lemma 8.1, and
Lemma 9.2. The remaining open endpoints are exact paper `log h` notation
packaging for Section 7, the concrete randomized-auction DSIC-to-ranked-payment
bridge for Section 8.2, and the Section 9.3 critical-slice-to-anonymous-bid-list
conversion.

## Handoff Notes

- Last passing paper build: `lake build GHW01DigitalGoods`.
- Do not redo: Section 7.2 tightness for `ghwTightValue`; it is closed through
  `paper_theorem7_2_tightness_ratio_for_repeated_bid_family`.
- Do not redo: Theorem 4.1 now has a verified base-two real-log wrapper,
  `paper_theorem4_1_finite_candidate_benchmark_from_logb_high_value`.
- Current best Section 8 endpoint:
  `paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_pairwise_truthful_payments`.
  It removes the artificial expected-cost variable and assumes only ranked
  revenue decomposition, adjacent payment-form truthfulness inequalities,
  strict adjacent rank values, and endpoint probability mass. The next proof
  bridge is a concrete randomized anonymous/sorted-bid DSIC interface deriving
  those hypotheses from `DigitalGoodsAuction.TruthfulDominantStrategy`.
- Current best Section 9.3 endpoint:
  `paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_via_anonymous_bid_list`.
  The remaining bridge is from general deterministic critical-price slices to
  the anonymous binary erased-bid-list representation.
- There are unrelated dirty files in the repository. A future commit for this
  paper should stage only the GHW auction files and any skill/documentation
  files intentionally updated for the handoff.
