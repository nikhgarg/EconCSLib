import EconCSLean.Auction.DigitalGoods

/-!
# Paper-Facing Theorems: Competitive Auctions and Digital Goods

This file is the public theorem interface for the current digital-goods auction
formalization. The full competitive-auction guarantee remains future work; this
file exposes the closed posted-price mechanism facts.
-/

namespace EconCSLean
namespace Auction

/--
Posted-price digital-goods auctions are dominant-strategy truthful.
-/
theorem paper_posted_price_truthful
    {Agent : Type*} [DecidableEq Agent] (price : Agent → ℝ) :
    (postedPrice price).TruthfulDominantStrategy := by
  exact postedPrice_truthful price

/--
Posted-price digital-goods auctions are individually rational.
-/
theorem paper_posted_price_individually_rational
    {Agent : Type*} (price : Agent → ℝ) :
    (postedPrice price).IndividuallyRational := by
  exact postedPrice_individuallyRational price

/--
Posted-price digital-goods auctions have no positive transfers when all prices
are nonnegative.
-/
theorem paper_posted_price_no_positive_transfers
    {Agent : Type*} (price : Agent → ℝ) (hprice : ∀ i, 0 ≤ price i) :
    (postedPrice price).NoPositiveTransfers := by
  exact postedPrice_noPositiveTransfers price hprice

end Auction
end EconCSLean
