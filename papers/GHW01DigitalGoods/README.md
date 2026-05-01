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
4. Return to Sections 6--7 once the generic probability layer is strong enough:
   prove the fixed-size sample bound for Lemma 6.1, remove the explicit
   `CrossSampleOfferApproximationCertificate` assumption from Theorem 6.2, and
   then build the weighted-pairing expectation model for Theorems 7.1--7.2.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Digital-goods auction interface, revenue, DSIC | `paper_digital_goods_revenue`, `paper_digital_goods_truthful` | formalized definitions | `GHW01DigitalGoods/MainTheorems.lean` | finite bidder model |
| Posted-price and threshold-auction truthfulness/IR/NPT | `paper_posted_price_truthful`, `paper_threshold_price_truthful`, `paper_own_erased_threshold_price_truthful` | formalized support | `GHW01DigitalGoods/MainTheorems.lean` | threshold must be own-bid independent; NPT needs nonnegative prices |
| Fixed-price benchmark and two-winner benchmark | `paper_two_winner_benchmark`, `paper_two_winner_fixed_price_benchmark`, `paper_single_price_revenue_le_candidate_benchmark_of_feasible` | formalized finite support | `GHW01DigitalGoods/MainTheorems.lean` | assumes a feasible nonnegative two-winner price where needed |
| Theorem 4.1 and Corollary 4.2, fixed-price revenue lower bounds | none | not started | none | requires paper's utility-range assumptions and logarithmic bound |
| Lemma 6.1, random subset revenue split | none | not started | none | probabilistic subset lemma |
| Theorem 6.2, random sampling auction guarantee | `paper_cross_sample_offer_competitive_of_certificate` | conditional scaffold | `GHW01DigitalGoods/MainTheorems.lean` | needs `CrossSampleOfferApproximationCertificate` with concrete ratio |
| Theorem 7.1, weighted pairing auction revenue | none | not started | none | weighted pairing auction and expectation analysis |
| Theorem 7.2, weighted auction benchmark bound | none | not started | none | weighted auction model and logarithmic guarantee |
| Lemma 8.1, monotone win probabilities in truthful auctions | `paper_lemma8_1_truthful_win_probability_monotone`, `paper_lemma8_1_allocation_mono_own_bid_of_truthful` | formalized | `GHW01DigitalGoods/MainTheorems.lean` | algebraic paper proof plus direct DSIC own-bid monotonicity form |
| Theorem 8.2, any truthful auction has expected revenue at most fixed-price benchmark | `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_certificate`, `paper_theorem8_2_expected_revenue_le_fixed_price_benchmark_of_monotone_probabilities` | conditional scaffold | `GHW01DigitalGoods/MainTheorems.lean` | needs the paper's revenue rearrangement from truthful auction payoffs into adjacent win-probability increments |
| Theorem 9.1, deterministic bid-independent lower bound | none | not started | none | deterministic bid-independent adversarial input |
| Lemma 9.2, truthful deterministic auctions are bid-independent | none | not started | none | deterministic truthfulness characterization |
| Theorem 9.3, deterministic truthful lower bound | none | not started | none | reduction through Lemma 9.2 |

## Source-Audit Notes

The cached text contains Theorem 4.1, Corollary 4.2, Lemma 6.1, Theorem 6.2,
Theorems 7.1--7.2, Lemma 8.1, Theorem 8.2, Theorem 9.1, Lemma 9.2, and Theorem
9.3. Current Lean coverage is mainly the reusable digital-goods mechanism layer,
fixed-price benchmark support, and deterministic RSOP-style truthfulness
skeleton; the source approximation and lower-bound theorems remain open except
for the conditional approximation-certificate wrapper.
