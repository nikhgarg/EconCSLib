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

- `GHW01DigitalGoods/PaperInterface.lean` is the compact human-facing Lean
  surface with paper definitions and direct source theorem statements.
- `GHW01DigitalGoods/MainTheorems.lean`
- `GHW01DigitalGoods/PostPaperAudit.lean` is the importable source-numbered
  endpoint ledger.

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
   Theorems 7.1--7.2, then discharge the Section 8 and Section 9 paper-model
   endpoints.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Digital-goods auction interface, revenue, DSIC | `paper_digital_goods_revenue`, `paper_digital_goods_truthful` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; status note: formalized definitions; finite bidder model |
| Posted-price and threshold-auction truthfulness/IR/NPT | `paper_posted_price_truthful`, `paper_threshold_price_truthful`, `paper_own_erased_threshold_price_truthful` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; status note: formalized support; threshold must be own-bid independent; NPT needs nonnegative prices |
| Fixed-price benchmark and two-winner benchmark | `paper_two_winner_benchmark`, `paper_two_winner_fixed_price_benchmark`, `paper_single_price_revenue_le_candidate_benchmark_of_feasible` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; finite candidate benchmark support is formalized, and lemmas that compare a concrete posted price to the benchmark state the required feasibility and nonnegativity hypotheses explicitly. |
| Theorem 4.1 and Corollary 4.2, fixed-price revenue lower bounds | `paper_theorem4_1_finite_candidate_benchmark_from_power_two_bins`, `paper_theorem4_1_finite_candidate_benchmark_from_log_certificate`, `paper_theorem4_1_finite_candidate_benchmark_from_logb_high_value`, `PaperTheorem41HighValueModel`, `paper_theorem4_1_finite_candidate_benchmark_of_high_value_model`, `paper_corollary4_2_fixed_price_lower_bound_from_truncation`, `PaperCorollary42TruncationModel`, `paper_corollary4_2_fixed_price_lower_bound_of_truncation_model` | formalized with caveat | `GHW01DigitalGoods/MainTheorems.lean` | Caveat: the endpoint is packaged through finite high-value/log-certificate models and `Real.logb 2 h + 2` notation. Theorem 4.1 is closed for the finite one-winner candidate fixed-price benchmark; Corollary 4.2 is packaged as `PaperCorollary42TruncationModel`. |
| Lemma 6.1, random subset revenue split | `PaperLemma61FairCoinModel`, `paper_lemma6_1_fair_coin_lower_tail_of_model`, `paper_aux_theorem6_2_fair_coin_lower_tail_relaxed` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; independent fair-coin paper-model endpoint proves the `exp(-\|S\|/36)` lower-tail bound used by the Section 6 random-sampling development. |
| Theorem 6.2, random sampling auction guarantee | `paper_theorem6_2_deterministic_six_revenue_bound_of_large_sale_count`, `paper_aux_theorem6_2_side_sale_sample_good_probability`, `paper_aux_theorem6_2_selected_price_bad_large_sample_top_prefix_le_exp`, `paper_aux_theorem6_2_selected_offer_large_sample_count_of_alpha_h`, `paper_theorem6_2_fair_coin_revenue_bound_top_prefix_alpha_h_fin_sorted`, `PaperTheorem62FairCoinSortedModel`, `paper_theorem6_2_fair_coin_revenue_bound_of_sorted_model`, `paper_theorem6_2_random_sampling_measure_union_bound` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; Section 6.2 has a final independent-half-sampling paper-model endpoint. The model `PaperTheorem62FairCoinSortedModel` packages sorted bids, fair-coin sampling, the `minWinners` feasibility side condition `3 * minWinners <= alpha`, nonnegative target price, bounded values, and the paper large-market condition `alpha * h <= F_p`. Lean proves the displayed probability bound `1 - exp(-alpha/36) - 40 * exp(-alpha/72)` for earning at least one sixth of fixed-price revenue. The finite-candidate analogue `paper_theorem6_2_fair_coin_revenue_bound_candidate_union` remains exported for auditing. |
| Theorem 7.1, weighted pairing auction revenue | `weightedPairingExpectedRevenue`, `paper_theorem7_1_weighted_pairing_log_bound_from_classifier`, `paper_theorem7_1_weighted_pairing_log_bound_from_power_two_bins`, `paper_theorem7_1_weighted_pairing_log_bound_from_log_certificate`, `paper_theorem7_1_weighted_pairing_log_bound_from_logb_high_value`, `PaperTheorem71WeightedPairingHighValueModel`, `paper_theorem7_1_weighted_pairing_log_bound_of_high_value_model` | formalized with caveat | `GHW01DigitalGoods/MainTheorems.lean` | Caveat: the paper-facing high-value model is closed for normalized bids in `[1,h]` with `4h <= T` and the rounded `log_2 h + 2` coefficient. The proof uses relative factor-two bins; power-of-two and log-certificate variants remain exported for auditing. |
| Theorem 7.2, weighted auction benchmark bound | `paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark`, `paper_theorem7_2_largestDyadicTailBucket_card_two_of_large_fixed_price_high_value`, `paper_theorem7_2_weighted_pairing_bound_from_high_value_large_benchmark_base_tail`, `paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark_from_logb_high_value`, `PaperTheorem72WeightedPairingHighValueModel`, `paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark_of_high_value_model`, `paper_theorem7_2_tightness_ratio_certificate_of_benchmark_ge`, `paper_theorem7_2_tightness_revenue_split_by_classifier`, `paper_theorem7_2_tightness_ratio_from_classifier_benchmark_ge`, `GhwTightAgent`, `ghwTightValue`, `ghwTightTwoWinnerBenchmarkValue`, `paper_theorem7_2_tightness_totalBidValue`, `paper_theorem7_2_tightness_singlePriceRevenue_top`, `paper_theorem7_2_tightness_top_revenue_le_twoWinnerBenchmark`, `paper_theorem7_2_tightness_square_sum_le`, `paper_theorem7_2_tightness_lower_payment_le`, `paper_theorem7_2_tightness_lowerContribution_le`, `paper_theorem7_2_tightness_topContribution_le`, `paper_theorem7_2_tightness_ratio_for_repeated_bid_family` | formalized with caveat | `GHW01DigitalGoods/MainTheorems.lean` | Caveat: the direct normalized high-value wrapper uses the rounded side condition `log_2 h + 2 <= s^2`; the natural dyadic certificate remains exported. Lean proves `F^(2) <= 576 * s * W`, the largest fixed-price tail bucket bridge, and the repeated-bid tightness family with ratio at most `3/s`. |
| Lemma 8.1, monotone win probabilities in truthful auctions | `paper_lemma8_1_truthful_win_probability_monotone`, `paper_lemma8_1_truthful_win_probability_monotone_payments`, `paper_lemma8_1_allocation_mono_own_bid_of_truthful` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None |
| Theorem 8.2, any truthful auction has expected revenue at most fixed-price benchmark | `paper_ranked_fixed_price_revenue_le_finite_candidate_benchmark`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_certificate`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_monotone_probabilities`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_gain_bounds`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_adjacent_gain_recursion`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_truthful_cost_comparisons`, `paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_truthful_cost_comparisons`, `paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_pairwise_truthfulness`, `paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_pairwise_truthful_payments`, `RankedAdjacentReportSymmetry`, `paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_truthful_auction`, `PaperTheorem82RankedTruthfulAuctionCertificate`, `paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_ranked_truthful_auction_certificate`, `PaperTheorem82AnonymousSortedBidTruthfulModel`, `paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_anonymous_sorted_bid_truthful_model` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; Section 8.2 now has a final paper-model endpoint. The ranked fixed-price terms `V_j` are proved bounded by the actual one-winner finite fixed-price benchmark, monotone adjacent win probabilities are proved from the two Lemma 8.1-style adjacent truthfulness comparisons, and the expected-payment wrapper uses direct `b*p - payment` comparisons. The auction-level wrapper derives those adjacent payment comparisons from `DigitalGoodsAuction.TruthfulDominantStrategy` and individual rationality under an explicit adjacent-rank anonymity/symmetry certificate, while the ranked revenue decomposition is discharged by the ranked bidder enumeration. `PaperTheorem82AnonymousSortedBidTruthfulModel` names the paper's anonymous sorted-bid convention as the ranked sequence identities, endpoint bound, price side conditions, and adjacent-rank symmetry needed for the theorem. |
| Theorem 9.1, deterministic bid-independent lower bound | `paper_theorem9_1_bid_independent_threshold_transition`, `paper_theorem9_1_transition_witness_revenue_bound`, `paper_theorem9_1_start_high_witness_revenue_bound`, `paper_theorem9_1_two_value_bid_independent_lower_bound`, `paper_theorem9_1_arbitrary_threshold_bid_independent_lower_bound`, `paper_theorem9_1_arbitrary_threshold_scaled_lower_bound`, `paper_theorem9_1_arbitrary_threshold_scaled_lower_bound_fixed_price_benchmark`, `paper_theorem9_1_bid_independent_list_rule_scaled_lower_bound_fixed_price_benchmark`, `paper_theorem9_1_count_threshold_revenue_eq_concrete_auction`, `paper_theorem9_1_concrete_count_threshold_scaled_lower_bound_fixed_price_benchmark`, `paper_theorem9_1_ratio_le_one_over_h_of_mul_revenue_le_benchmark` | formalized with caveat | `GHW01DigitalGoods/MainTheorems.lean` | Caveat: the endpoint is intentionally stated in the paper's anonymous/list-of-bids binary model; the broader identity-aware threshold interface remains available elsewhere in the reusable library. Discrete threshold-transition, binary revenue construction, erased-bid-list bridge, paper scale, ratio packaging, and fixed-price benchmark witness are formalized. |
| Lemma 9.2, truthful deterministic auctions are bid-independent | `paper_lemma9_2_deterministic_offer_payment_constant`, `paper_lemma9_2_deterministic_offer_winning_monotone`, `paper_lemma9_2_deterministic_offer_losing_prefix`, `paper_lemma9_2_deterministic_offer_bid_independent`, `paper_lemma9_2_deterministic_offer_exists_threshold_dominates`, `paper_lemma9_2_deterministic_truthful_auction_bid_independent_slices`, `paper_lemma9_2_deterministic_truthful_auction_exists_nonnegative_threshold_dominates`, `paper_lemma9_2_deterministic_auction_payment_le_threshold` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; the core bid-independent slice characterization is closed, and the threshold-domination/payment-bound forms now expose the bridge needed by the Theorem 9.3 auction-family certificates. |
| Theorem 9.3, deterministic truthful lower bound | `paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold`, `paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_fixed_price_benchmark`, `paper_theorem9_3_binary_anonymous_bid_independent_revenue_representation`, `paper_theorem9_3_count_threshold_binary_anonymous_bid_independent_revenue_representation`, `paper_theorem9_3_binary_count_threshold_revenue_upper_bound`, `paper_theorem9_3_binary_count_threshold_payment_upper_bound`, `paper_theorem9_3_binary_count_threshold_slice_upper_bound`, `paper_theorem9_3_binary_count_threshold_payment_upper_bound_of_slice_upper_bound`, `paper_theorem9_3_binary_count_threshold_revenue_upper_bound_of_payment_upper_bound`, `PaperTheorem93CountThresholdAuctionFamilyCertificate`, `paper_theorem9_3_count_threshold_auction_family_certificate_of_slice_upper_bound`, `paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_upper_bound`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_upper_bound`, `paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_auction_family_certificate`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_auction_family_certificate`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_slice_upper_bound`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_slice_upper_bound_ir_npt`, `paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound`, `paper_theorem9_3_binary_anonymous_bid_independent_payment_upper_bound`, `paper_theorem9_3_binary_anonymous_bid_independent_slice_upper_bound`, `paper_theorem9_3_binary_anonymous_bid_independent_payment_upper_bound_of_slice_upper_bound`, `paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound_of_payment_upper_bound`, `paper_theorem9_3_binary_anonymous_bid_independent_revenue_upper_bound_of_representation`, `PaperTheorem93AnonymousAuctionFamilyCertificate`, `paper_theorem9_3_anonymous_auction_family_certificate_of_slice_upper_bound`, `paper_theorem9_3_deterministic_truthful_lower_bound_of_anonymous_bid_independent_representation`, `paper_theorem9_3_deterministic_truthful_lower_bound_of_anonymous_bid_independent_upper_bound`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_bid_independent_representation`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_bid_independent_upper_bound`, `paper_theorem9_3_deterministic_truthful_lower_bound_of_anonymous_auction_family_certificate`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_auction_family_certificate`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_slice_upper_bound`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_slice_upper_bound_ir_npt`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_truthful_slice_upper_bound`, `PaperTheorem93AnonymousTruthfulDeterministicModel`, `paper_theorem9_3_binary_anonymous_slice_upper_bound_of_truthful_deterministic_model`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_truthful_deterministic_model`, `PaperTheorem93AnonymousDeterministicTruthfulCertificate`, `paper_theorem9_3_deterministic_truthful_lower_bound_of_certificate`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_certificate`, `paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold_via_anonymous_bid_list`, `paper_theorem9_3_deterministic_truthful_ratio_witness_of_count_threshold_via_anonymous_bid_list` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; Section 9.3 now has a final paper-model endpoint. The formal model `PaperTheorem93AnonymousTruthfulDeterministicModel` carries truthfulness, binary allocation, individual rationality, no positive transfers, and the anonymous erased-bid critical-price convention. From that model, Lean derives the anonymous binary slice certificate and proves the paper ratio witness `R/F <= 1/h` with `alpha*h <= F` against the actual one-winner finite fixed-price benchmark. Count-threshold, anonymous erased-bid-list, revenue-domination, payment-bound, slice-bound, and auction-family intermediate forms remain exported for auditing the reduction. |

## Source-Audit Notes

The cached text contains Theorem 4.1, Corollary 4.2, Lemma 6.1, Theorem 6.2,
Theorems 7.1--7.2, Lemma 8.1, Theorem 8.2, Theorem 9.1, Lemma 9.2, and Theorem
9.3. Current Lean coverage includes the reusable digital-goods mechanism layer,
fixed-price benchmark support, deterministic RSOP-style truthfulness skeleton,
Section 6 deterministic/probabilistic independent-sampling bridges with the
paper's top-prefix exponential constants, the Section 7 concrete factor-two
ranked-bin weighted-pairing bridge, the closed Theorem 4.1 natural-number
dyadic and `Real.logb 2 h + 2` forms, paper-condition `Real.logb` wrappers for
Theorems 7.1--7.2, the closed Theorem 7.2 natural-number dyadic lower-bound and
repeated-bid tightness-family endpoints, Lemma 8.1, and Lemma 9.2. Sections
8.2 and 9.3 now both have final paper-model theorems: their model fields make
the paper's anonymous sorted-bid and anonymous erased-bid critical-price
conventions explicit.

## Handoff Notes

- Last passing paper build: `lake build GHW01DigitalGoods`.
- Do not redo: Section 7.2 tightness for `ghwTightValue`; it is closed through
  `paper_theorem7_2_tightness_ratio_for_repeated_bid_family`.
- Do not redo: Theorem 4.1 now has a verified base-two real-log wrapper,
  `paper_theorem4_1_finite_candidate_benchmark_from_logb_high_value`.
- Current best Section 8 endpoint:
  `paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_anonymous_sorted_bid_truthful_model`.
  It derives the adjacent payment-form truthfulness inequalities from
  `DigitalGoodsAuction.TruthfulDominantStrategy` and individual rationality,
  discharges the ranked revenue decomposition by ranked enumeration, and leaves
  the paper's anonymous sorted-bid convention explicit in
  `PaperTheorem82AnonymousSortedBidTruthfulModel`.
- Current best Section 9.3 endpoint:
  `paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_truthful_deterministic_model`.
  It packages the paper's anonymous deterministic convention as
  `PaperTheorem93AnonymousTruthfulDeterministicModel` and derives the
  anonymous binary slice certificate internally.
- There are unrelated dirty files in the repository. A future commit for this
  paper should stage only the GHW auction files and any skill/documentation
  files intentionally updated for the handoff.
