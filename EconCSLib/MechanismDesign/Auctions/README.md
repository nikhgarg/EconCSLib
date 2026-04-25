# Auction Theory Test-of-Time Track

## Source Version

Current auction-theory sources from the SIGecom Test-of-Time list:

- 2021: *Competitive Auctions and Digital Goods*, Andrew V. Goldberg,
  Jason D. Hartline, and Andrew Wright, SODA 2001.
- 2018: the GSP/position-auction series:
  Hal R. Varian, *Position Auctions*; Benjamin Edelman, Michael Ostrovsky, and
  Michael Schwarz, *Internet Advertising and the Generalized Second-Price
  Auction*; Gagan Aggarwal, Ashish Goel, and Rajeev Motwani, *Truthful Auctions
  for Pricing Search Keywords*.
- 2017: *Truth Revelation in Approximately Efficient Combinatorial Auctions*,
  Daniel Lehmann, Liadan Ita O'Callaghan, and Yoav Shoham, JACM 2002.

Primary award listing: https://www.sigecom.org/award-tot.html.
The PDFs are not committed to git.

## Central Theorem File

- `EconCSLib/Auction/MainTheorems.lean`

That file contains the core paper-facing theorem wrappers currently available.

For a single-file declaration-ordered human-audit surface (theorems in paper
order, with status-facing comments and all required assumptions tracked), see:

- `EconCSLib/Auction/PaperFacingTheorems.lean`

The full competitive-auction approximation, GSP equilibrium/revenue, and
combinatorial-auction approximation/truthfulness theorems are not yet
formalized.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions |
|---|---|---|---|---|
| Unlimited-supply digital-goods auction interface | `DigitalGoodsAuction` | formalized | `EconCSLib/Auction/DigitalGoods.lean` | none |
| Quasilinear utility | `DigitalGoodsAuction.utility` | formalized | `EconCSLib/Auction/DigitalGoods.lean` | none |
| Posted-price truthfulness | `paper_posted_price_truthful` | formalized | `EconCSLib/Auction/MainTheorems.lean` | none |
| Posted-price individual rationality | `paper_posted_price_individually_rational` | formalized | `EconCSLib/Auction/MainTheorems.lean` | none |
| Posted-price no-positive-transfers theorem | `paper_posted_price_no_positive_transfers` | formalized | `EconCSLib/Auction/MainTheorems.lean` | nonnegative prices |
| Posted-price revenue equals single-price revenue | `paper_posted_price_revenue_eq_single_price` | formalized | `EconCSLib/Auction/MainTheorems.lean` | none |
| Fixed-price benchmark interface | `IsFixedPriceBenchmark`, `IsTwoWinnerFixedPriceBenchmark` | formalized | `EconCSLib/Auction/DigitalGoods.lean` | feasible price set must be nonempty |
| Finite bidder-value candidate benchmark | `finiteCandidateFixedPriceBenchmark`, `paper_finite_candidate_fixed_price_benchmark_nonneg` | formalized | `EconCSLib/Auction/MainTheorems.lean` | none |
| Feasible fixed price dominated by bidder-value benchmark | `paper_single_price_revenue_le_candidate_benchmark_of_feasible` | formalized | `EconCSLib/Auction/MainTheorems.lean` | requires at least one required winner |
| Two-winner fixed-price benchmark | `paper_two_winner_fixed_price_benchmark` | formalized | `EconCSLib/Auction/MainTheorems.lean` | assumes there exists a nonnegative price selling to at least two bidders |
| Own-bid-independent threshold auction truthfulness | `paper_threshold_price_truthful` | formalized | `EconCSLib/Auction/MainTheorems.lean` | threshold offered to each bidder must be independent of that bidder's own report |
| Other-bid computed threshold truthfulness | `paper_own_erased_threshold_price_truthful` | formalized | `EconCSLib/Auction/MainTheorems.lean` | price rule sees the bid profile with the bidder's own report erased |
| Cross-sample candidate threshold truthfulness | `paper_cross_sample_candidate_threshold_truthful` | formalized deterministic RSOP-style skeleton | `EconCSLib/Auction/MainTheorems.lean` | approximation guarantee and randomized partition expectation not formalized |
| Cross-sample candidate offer truthfulness/NPT | `paper_cross_sample_candidate_offer_threshold_truthful`, `paper_cross_sample_candidate_offer_no_positive_transfers` | formalized deterministic RSOP-style skeleton with nonnegative offers | `EconCSLib/Auction/MainTheorems.lean` | approximation guarantee not formalized |
| Uniform partition-average revenue nonnegativity | `paper_average_cross_sample_candidate_offer_revenue_nonneg` | formalized | `EconCSLib/Auction/MainTheorems.lean` | lower-bound approximation guarantee not formalized |
| RSOP approximation certificate interface | `paper_cross_sample_offer_competitive_of_certificate` | conditional theorem wrapper formalized | `EconCSLib/Auction/MainTheorems.lean` | must prove `CrossSampleOfferApproximationCertificate` for a concrete ratio |
| Threshold auction individual rationality | `paper_threshold_price_individually_rational` | formalized | `EconCSLib/Auction/MainTheorems.lean` | none |
| Threshold auction no-positive-transfers | `paper_threshold_price_no_positive_transfers` | formalized | `EconCSLib/Auction/MainTheorems.lean` | nonnegative thresholds |
| Position-auction interface | `PositionEnvironment`, `PositionOutcome` | formalized | `EconCSLib/Auction/Position.lean` | none |
| Position-mechanism truthfulness/Nash predicates | `PositionMechanism.TruthfulDominantStrategy`, `PositionMechanism.IsNashEquilibrium` | formalized | `EconCSLib/Auction/Position.lean` | none |
| Local-envy-free outcome deviation certificate | `paper_position_slot_envy_free_no_profitable_assigned_slot_deviation` | formalized | `EconCSLib/Auction/MainTheorems.lean` | only covers assigned-slot deviations at current per-click prices |
| GSP is not truthful | `paper_gsp_truthful_bidding_not_dominant_example` | formalized as concrete two-slot witness | `EconCSLib/Auction/MainTheorems.lean` | full generic GSP mechanism and equilibrium theory not yet formalized |
| GSP mechanism is not truthful | `paper_gsp_mechanism_not_truthful` | formalized as concrete two-slot mechanism witness | `EconCSLib/Auction/MainTheorems.lean` | full generic sorted-bid GSP not yet formalized |
| Sorted three-bidder/two-slot GSP is not truthful | `paper_sorted_gsp_three_bidder_two_slot_not_truthful` | formalized for a concrete sorted GSP mechanism | `EconCSLib/Auction/MainTheorems.lean` | equilibrium and revenue/welfare comparison theorems not yet formalized |
| Direct combinatorial-auction interface | `CombinatorialAuction` | formalized | `EconCSLib/Auction/Combinatorial.lean` | none |
| Feasible partial bundle allocation | `IsFeasibleBundleAllocation` | formalized | `EconCSLib/Auction/Combinatorial.lean` | none |
| Single-minded bidder valuation | `SingleMindedBid.valuation` | formalized | `EconCSLib/Auction/Combinatorial.lean` | none |
| Reject-all combinatorial auction truthfulness | `paper_combinatorial_reject_all_truthful` | formalized baseline theorem | `EconCSLib/Auction/MainTheorems.lean` | none |
| Target-bundle critical-price truthfulness | `paper_combinatorial_target_bundle_threshold_truthful_on_normalized` | formalized on normalized valuations | `EconCSLib/Auction/MainTheorems.lean` | offered bundle price must be own-report independent |
| Target-bundle critical-price truthfulness for single-minded profiles | `paper_combinatorial_target_bundle_threshold_truthful_on_single_minded` | formalized | `EconCSLib/Auction/MainTheorems.lean` | desired bundles must be nonempty |
| Pairwise-disjoint accepted single-minded allocation feasibility | `singleMindedAllocation_feasible` | formalized | `EconCSLib/Auction/Combinatorial.lean` | accepted desired bundles must be pairwise disjoint and contained in goods |
| Target-bundle threshold allocation feasibility | `paper_combinatorial_target_bundle_threshold_feasible_of_pairwise_disjoint` | formalized | `EconCSLib/Auction/MainTheorems.lean` | accepted target bundles must be contained in goods and pairwise disjoint |

## Current Formalization Plan

1. Digital goods: the deterministic fixed-price benchmark layer and the
   deterministic RSOP-style truthfulness skeleton are now closed through
   `paper_two_winner_fixed_price_benchmark` and
   `paper_cross_sample_candidate_offer_threshold_truthful` and
   `paper_average_cross_sample_candidate_offer_revenue_nonneg`. The remaining
   major seam for the 2021 paper is the RSOP approximation certificate:
   instantiate `CrossSampleOfferApproximationCertificate` with a concrete ratio
   by lower-bounding the uniform partition-average revenue relative to `F^(2)`.
2. GSP/position auctions: the concrete sorted three-bidder/two-slot GSP
   non-truthfulness theorem and the local-envy-free assigned-slot deviation
   certificate are closed. Next define the generic sorted-bid GSP mechanism for
   finite ordered slots and formalize symmetric Nash equilibrium revenue/welfare
   comparisons in certificate form.
3. Combinatorial auctions: build on `CombinatorialAuction`,
   `IsFeasibleBundleAllocation`, `SingleMindedBid.valuation`, and the
   single-minded critical-price/feasibility lemmas; next add the greedy
   allocation rule for single-minded bidders and prove its pairwise-disjoint
   accepted-set invariant. Reuse `FairDivision.Bundle` throughout.
