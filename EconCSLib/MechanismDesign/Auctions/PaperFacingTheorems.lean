import EconCSLib.MechanismDesign.Auctions.MainTheorems

/-!
# Paper-Facing Theorem Ledger

This file is the Lean-oriented audit surface for the auction Test-of-Time
formalization.  It is declaration-ordered by source paper section.
Each entry is documented with the corresponding paper-facing wrapper already
available in `MainTheorems.lean`.
-/

namespace EconCSLib
namespace Auction

-- 1) 2021: Competitive Auctions and Digital Goods

-- 1.1 Posted-price mechanism primitives.

-- Theorem (2021): A posted-price digital-goods auction is dominant-strategy truthful.
#check paper_posted_price_truthful

-- Theorem (2021): A posted-price digital-goods auction is individually rational.
#check paper_posted_price_individually_rational

-- Theorem (2021): Posted-price mechanisms have no positive transfers under
-- nonnegative posted prices.
#check paper_posted_price_no_positive_transfers

-- Theorem (2021): Posted-price revenue equals single-price benchmark revenue.
#check paper_posted_price_revenue_eq_single_price

-- 1.2 Fixed-price benchmark reduction and nonnegative bound.

-- Definitions from the paper's fixed-price benchmark layer.
#check IsFixedPriceBenchmark
#check IsTwoWinnerFixedPriceBenchmark
#check finiteCandidateFixedPriceBenchmark

-- Paper theorem: finite bidder-value candidate benchmark is nonnegative.
#check paper_finite_candidate_fixed_price_benchmark_nonneg

-- Paper theorem: every feasible fixed price is dominated by the finite bidder-value
-- candidate benchmark (requires at least one required winner).
#check paper_single_price_revenue_le_candidate_benchmark_of_feasible

-- Paper theorem: when feasible, this candidate benchmark equals the two-winner
-- fixed-price benchmark definition.
#check paper_two_winner_fixed_price_benchmark

-- 1.3 Cross-sample/RSOP-style skeleton.

-- Own-bid-independent threshold mechanisms are DSIC.
#check paper_threshold_price_truthful

-- Own-bid-erased threshold-price auctions are DSIC.
#check paper_own_erased_threshold_price_truthful

-- Deterministic RSOP-style cross-sample candidate thresholds are DSIC.
#check paper_cross_sample_candidate_threshold_truthful

-- Deterministic RSOP-style cross-sample candidate offers are DSIC and NPT.
#check paper_cross_sample_candidate_offer_threshold_truthful
#check paper_cross_sample_candidate_offer_no_positive_transfers

-- Revenue of the uniform partition-averaged cross-sample offer auction is
-- nonnegative.
#check paper_average_cross_sample_candidate_offer_revenue_nonneg

-- Paper-facing approximation seam for the 2021 paper:
-- once a concrete certificate is proved, competitive ratio follows.
#check CrossSampleOfferApproximationCertificate
#check paper_cross_sample_offer_competitive_of_certificate

-- 1.4 Threshold auctions with generic monotonicity.

-- Threshold auction is individually rational.
#check paper_threshold_price_individually_rational

-- Threshold auction has no positive transfers under nonnegative thresholds.
#check paper_threshold_price_no_positive_transfers

-- 2) 2018: Position auctions and GSP non-truthfulness

-- Paper-facing non-truthfulness witness and concrete mechanism-level counterexample.
#check paper_gsp_truthful_bidding_not_dominant_example
#check paper_gsp_mechanism_not_truthful
#check paper_sorted_gsp_three_bidder_two_slot_not_truthful

-- Local envy condition implies no profitable assigned-slot deviation.
#check paper_position_slot_envy_free_no_profitable_assigned_slot_deviation

-- 3) 2017: Combinatorial auctions and critical-price thresholds

-- Reject-all baseline direct combinatorial auction is DSIC.
#check paper_combinatorial_reject_all_truthful

-- Reject-all has no positive transfers.
#check paper_combinatorial_reject_all_no_positive_transfers

-- Target-bundle threshold DSIC on normalized valuations.
#check paper_combinatorial_target_bundle_threshold_truthful_on_normalized

-- Target-bundle threshold DSIC on single-minded profiles.
#check paper_combinatorial_target_bundle_threshold_truthful_on_single_minded

-- Target-bundle allocations are feasible under pairwise-disjoint accepted bundles.
#check paper_combinatorial_target_bundle_threshold_feasible_of_pairwise_disjoint

end Auction
end EconCSLib
