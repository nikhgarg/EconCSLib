import EconCSLean.Auction.DigitalGoods
import EconCSLean.Auction.Position
import EconCSLean.Auction.Combinatorial

/-!
# Paper-Facing Theorems: Auction Test-of-Time Tracks

This file is the public theorem interface for the current auction-theory
formalization work around SIGecom Test-of-Time papers:

- the 2021 digital-goods/prior-free-auction paper,
- the 2018 GSP/position-auction paper series,
- the 2017 combinatorial-auction paper.

The full approximation/equilibrium theorems remain future work; this file
exposes the closed unconditional theorem surface now available.
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

/--
For a fixed anonymous posted price, digital-goods auction revenue is the
single-price revenue benchmark expression.
-/
theorem paper_posted_price_revenue_eq_single_price
    {Agent : Type*} [Fintype Agent] (values : Agent → ℝ) (p : ℝ) :
    (postedPrice fun _ : Agent => p).revenue values =
      singlePriceRevenue values p := by
  exact postedPrice_const_revenue_eq_singlePriceRevenue values p

/--
Own-bid-independent threshold-price digital-goods auctions are
dominant-strategy truthful.
-/
theorem paper_threshold_price_truthful
    {Agent : Type*} [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ)
    (hind : OwnBidIndependent threshold) :
    (thresholdPriceAuction threshold).TruthfulDominantStrategy := by
  exact thresholdPriceAuction_truthful threshold hind

/--
If a digital-goods offer price is computed after erasing the bidder's own bid,
the resulting threshold-price auction is dominant-strategy truthful.
-/
theorem paper_own_erased_threshold_price_truthful
    {Agent : Type*} [DecidableEq Agent]
    (priceRule : Agent → (Agent → ℝ) → ℝ) :
    (thresholdPriceAuction
      (ownErasedThreshold priceRule)).TruthfulDominantStrategy := by
  exact ownErasedThresholdPriceAuction_truthful priceRule

/--
The finite bidder-value candidate benchmark is nonnegative.
-/
theorem paper_finite_candidate_fixed_price_benchmark_nonneg
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    0 ≤ finiteCandidateFixedPriceBenchmark values minWinners := by
  exact finiteCandidateFixedPriceBenchmark_nonneg values minWinners

/--
Own-bid-independent threshold-price digital-goods auctions are individually
rational.
-/
theorem paper_threshold_price_individually_rational
    {Agent : Type*} [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) :
    (thresholdPriceAuction threshold).IndividuallyRational := by
  exact thresholdPriceAuction_individuallyRational threshold

/--
Threshold-price digital-goods auctions have no positive transfers when all
thresholds are nonnegative.
-/
theorem paper_threshold_price_no_positive_transfers
    {Agent : Type*} [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ)
    (hthreshold : ∀ bids i, 0 ≤ threshold bids i) :
    (thresholdPriceAuction threshold).NoPositiveTransfers := by
  exact thresholdPriceAuction_noPositiveTransfers threshold hthreshold

/--
Concrete two-slot GSP witness: truthful bidding is not a dominant strategy in
the position-auction model.
-/
theorem paper_gsp_truthful_bidding_not_dominant_example :
    gspCounterexampleTruthfulOutcome.utility
      gspCounterexampleEnvironment gspCounterexampleValues (0 : Fin 3) <
    gspCounterexampleLowerBidOutcome.utility
      gspCounterexampleEnvironment gspCounterexampleValues (0 : Fin 3) := by
  exact gspCounterexample_lowerBid_profitable

/--
The reject-all direct combinatorial auction is dominant-strategy truthful.
-/
theorem paper_combinatorial_reject_all_truthful
    {Bidder Item : Type*} [DecidableEq Bidder] :
    (rejectAllAuction : CombinatorialAuction Bidder Item).TruthfulDominantStrategy := by
  exact rejectAllAuction_truthful

/--
The reject-all direct combinatorial auction has no positive transfers.
-/
theorem paper_combinatorial_reject_all_no_positive_transfers
    {Bidder Item : Type*} :
    (rejectAllAuction : CombinatorialAuction Bidder Item).NoPositiveTransfers := by
  exact rejectAllAuction_noPositiveTransfers

end Auction
end EconCSLean
