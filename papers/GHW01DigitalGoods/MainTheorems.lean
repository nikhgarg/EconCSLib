import EconCSLib.MechanismDesign.Auctions.MainTheorems

/-!
# Paper-Facing Theorems: Competitive Auctions and Digital Goods

This folder owns the Goldberg-Hartline-Wright 2001 digital-goods track. The
closed Lean statements currently live in the reusable auction library; this file
re-exports only the digital-goods surface under the citation-specific namespace.
-/

namespace GHW01DigitalGoods

export EconCSLib.Auction (
  paper_digital_goods_revenue
  paper_digital_goods_revenue_eq
  paper_digital_goods_truthful
  paper_digital_goods_truthful_eq
  paper_two_winner_benchmark
  paper_two_winner_benchmark_eq
  paper_posted_price_truthful
  paper_posted_price_individually_rational
  paper_posted_price_no_positive_transfers
  paper_posted_price_revenue_eq_single_price
  paper_threshold_price_truthful
  paper_own_erased_threshold_price_truthful
  paper_cross_sample_candidate_threshold_truthful
  paper_cross_sample_candidate_offer_threshold_truthful
  paper_cross_sample_candidate_offer_no_positive_transfers
  paper_average_cross_sample_candidate_offer_revenue_nonneg
  paper_cross_sample_offer_competitive_of_certificate
  paper_finite_candidate_fixed_price_benchmark_nonneg
  paper_single_price_revenue_le_candidate_benchmark_of_feasible
  paper_two_winner_fixed_price_benchmark
  paper_threshold_price_individually_rational
  paper_threshold_price_no_positive_transfers
)

end GHW01DigitalGoods
