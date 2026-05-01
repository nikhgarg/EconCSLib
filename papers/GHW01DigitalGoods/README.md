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
| Theorem 4.1 and Corollary 4.2, fixed-price revenue lower bounds | `paper_theorem4_1_fixed_price_lower_bound_of_factor_two_bin`, `paper_theorem4_1_fixed_price_lower_bound_of_factor_two_partition`, `paper_corollary4_2_fixed_price_lower_bound_from_truncation` | conditional | `GHW01DigitalGoods/MainTheorems.lean` | Previous status: conditional scaffold; factor-two bin, finite averaging, and truncation-loss algebra formalized; needs construction of the paper's log-h/log-n dyadic partitions |
| Lemma 6.1, random subset revenue split | `paper_aux_theorem6_2_fair_coin_lower_tail_relaxed` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None; status note: formalized independent fair-coin analogue; paper states a fixed-size sample lemma; Section 6 uses the independent half-sampling variant implemented here |
| Theorem 6.2, random sampling auction guarantee | `paper_theorem6_2_deterministic_six_revenue_bound_of_large_sale_count`, `paper_aux_theorem6_2_side_sale_sample_good_probability`, `paper_aux_theorem6_2_selected_price_bad_large_sample_top_prefix_le_exp`, `paper_aux_theorem6_2_selected_offer_large_sample_count_of_alpha_h`, `paper_theorem6_2_fair_coin_revenue_bound_top_prefix_alpha_h_fin_sorted`, `paper_theorem6_2_random_sampling_measure_union_bound` | formalized with caveat | `GHW01DigitalGoods/MainTheorems.lean` | Previous status: formalized sorted-bid fair-coin form; deterministic `F <= 6R`, fair-coin sample-good probability, selected-price top-prefix `40 * exp(-alpha/72)` bound, geometric tail constant, concrete sorted `Fin n` top prefixes, and `alpha h <= F` selected-large bridge are formalized; statement uses independent half-sampling, sorted bid indexing, and a `minWinners` feasibility side condition (`3 * minWinners <= alpha`), with the finite-candidate analogue `paper_theorem6_2_fair_coin_revenue_bound_candidate_union` retained |
| Theorem 7.1, weighted pairing auction revenue | `weightedPairingExpectedRevenue`, `paper_theorem7_1_weighted_pairing_log_bound_from_classifier` | conditional | `GHW01DigitalGoods/MainTheorems.lean` | Weighted-pairing expected-payment/revenue formula, singleton-bin deletion algebra, per-bin constant algebra, Cauchy square-sum bridge, factor-two ranked-bin geometry, same-bin probability bound, embedding of same-bin ranked double sums into the concrete weighted-pairing revenue, log-bin-count algebra, singleton floor-sum deletion, value-sorted finset-bin ranking/injectivity, active/singleton splitting, and classifier-fiber coverage/disjointness are formalized; remaining proof boundary is constructing the paper's dyadic classifier and log-count certificate from an arbitrary bid vector |
| Theorem 7.2, weighted auction benchmark bound | `paper_theorem7_2_weighted_pairing_bound_from_classifier_and_tail_certificates` | conditional | `GHW01DigitalGoods/MainTheorems.lean` | First/second case split, first case from Theorem 7.1 (`F <= T/s`), classifier-bin derivation of the Section 7.1 premise, second-case high-low selected-pair revenue certificate, rank-split bucket halves, finite geometric-tail proof of `\|M\|t = Ω(F)`, fixed-price-to-tail bridge, tail-set inclusion bridge, largest-total-bucket floor-mass bridge, and concrete `F <= 576 s W` certificate are formalized; remaining proof boundary is instantiating the dyadic classifier, tail/bucket certificates, and bucket-size fact from an arbitrary bid vector, plus the tightness example |
| Lemma 8.1, monotone win probabilities in truthful auctions | `paper_lemma8_1_truthful_win_probability_monotone`, `paper_lemma8_1_allocation_mono_own_bid_of_truthful` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None |
| Theorem 8.2, any truthful auction has expected revenue at most fixed-price benchmark | `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_certificate`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_monotone_probabilities`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_gain_bounds`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_adjacent_gain_recursion`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_truthful_cost_comparisons` | conditional | `GHW01DigitalGoods/MainTheorems.lean` | Previous status: conditional scaffold with paper algebra formalized; needs a concrete ranked randomized truthful-auction interface deriving the adjacent cost/gain comparisons from DSIC and sorted bid profiles |
| Theorem 9.1, deterministic bid-independent lower bound | `paper_theorem9_1_bid_independent_threshold_transition`, `paper_theorem9_1_transition_witness_revenue_bound`, `paper_theorem9_1_start_high_witness_revenue_bound`, `paper_theorem9_1_two_value_bid_independent_lower_bound`, `paper_theorem9_1_arbitrary_threshold_bid_independent_lower_bound`, `paper_theorem9_1_arbitrary_threshold_scaled_lower_bound`, `paper_theorem9_1_count_threshold_revenue_eq_concrete_auction`, `paper_theorem9_1_ratio_le_one_over_h_of_mul_revenue_le_benchmark` | conditional | `GHW01DigitalGoods/MainTheorems.lean` | Previous status: conditional scaffold; discrete threshold-transition, arbitrary-threshold binary revenue construction, concrete threshold-auction revenue bridge, paper scale `m = h^2 alpha`, exact `R/F ≤ 1/h` ratio packaging, and both witness revenue-ratio cases formalized; needs packaging from a fully general deterministic bid-independent auction to the count-threshold model |
| Lemma 9.2, truthful deterministic auctions are bid-independent | `paper_lemma9_2_deterministic_offer_payment_constant`, `paper_lemma9_2_deterministic_offer_winning_monotone`, `paper_lemma9_2_deterministic_offer_losing_prefix`, `paper_lemma9_2_deterministic_offer_bid_independent`, `paper_lemma9_2_deterministic_truthful_auction_bid_independent_slices` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | None |
| Theorem 9.3, deterministic truthful lower bound | `paper_theorem9_3_deterministic_truthful_lower_bound_of_count_threshold` | conditional | `GHW01DigitalGoods/MainTheorems.lean` | Previous status: conditional scaffold; reduction from count-threshold bid-independent rule to the Theorem 9.1 lower-bound witness formalized; Lemma 9.2 auction-level slices are closed; needs conversion from general critical-price slices to the count-threshold lower-bound model |

## Source-Audit Notes

The cached text contains Theorem 4.1, Corollary 4.2, Lemma 6.1, Theorem 6.2,
Theorems 7.1--7.2, Lemma 8.1, Theorem 8.2, Theorem 9.1, Lemma 9.2, and Theorem
9.3. Current Lean coverage includes the reusable digital-goods mechanism layer,
fixed-price benchmark support, deterministic RSOP-style truthfulness skeleton,
Section 6 deterministic/probabilistic independent-sampling bridges with the
paper's top-prefix exponential constants, the Section 7 concrete factor-two
ranked-bin weighted-pairing bridge, Lemma 8.1, and Lemma 9.2. The source
approximation and lower-bound endpoints remain open except for the conditional
theorem wrappers and deterministic reductions listed above.
