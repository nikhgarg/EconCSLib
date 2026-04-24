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

/-! ## 1) Paper-Facing Definitions: 2021 Digital Goods -/

/-- Paper Definition: The revenue of a digital goods auction outcome.
    $\sum_{i \in \text{winners}} p_i$
-/
noncomputable def paper_digital_goods_revenue {Agent : Type*} [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, M.payment values i

theorem paper_digital_goods_revenue_eq {Agent : Type*} [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) :
    paper_digital_goods_revenue M values = M.revenue values := by
  rfl

/-- Paper Definition: Dominant Strategy Truthful (DSIC).
    $v_i x_i(v_i, b_{-i}) - p_i(v_i, b_{-i}) \ge v_i x_i(b_i, b_{-i}) - p_i(b_i, b_{-i})$
-/
def paper_digital_goods_truthful {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (values : Agent → ℝ) (i : Agent) (report : ℝ),
    M.utility values i (Function.update values i report) ≤
      M.utility values i values

theorem paper_digital_goods_truthful_eq {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) :
    paper_digital_goods_truthful M ↔ M.TruthfulDominantStrategy := by
  rfl

/-- Paper Definition: Two-winner Fixed Price Benchmark $\mathcal{F}^{(2)}(v)$.
    The maximum revenue obtainable from a single price that sells to at least two bidders.
-/
noncomputable def paper_two_winner_benchmark {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) : ℝ :=
  twoWinnerFixedPriceBenchmarkValue values

theorem paper_two_winner_benchmark_eq {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) :
    paper_two_winner_benchmark values = twoWinnerFixedPriceBenchmarkValue values := by
  rfl

/-! ## 2) 2021 Digital Goods Theorems -/

/--
Posted-price digital-goods auctions are dominant-strategy truthful.
-/
theorem paper_posted_price_truthful
    {Agent : Type*} [DecidableEq Agent] (price : Agent → ℝ) :
    paper_digital_goods_truthful (postedPrice price) := by
  rw [paper_digital_goods_truthful_eq]
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
    paper_digital_goods_truthful (thresholdPriceAuction threshold) := by
  rw [paper_digital_goods_truthful_eq]
  exact thresholdPriceAuction_truthful threshold hind

/--
If a digital-goods offer price is computed after erasing the bidder's own bid,
the resulting threshold-price auction is dominant-strategy truthful.
-/
theorem paper_own_erased_threshold_price_truthful
    {Agent : Type*} [DecidableEq Agent]
    (priceRule : Agent → (Agent → ℝ) → ℝ) :
    paper_digital_goods_truthful (thresholdPriceAuction (ownErasedThreshold priceRule)) := by
  rw [paper_digital_goods_truthful_eq]
  exact ownErasedThresholdPriceAuction_truthful priceRule

/--
RSOP-style deterministic skeleton: for any fixed sample partition, offering each
bidder the finite candidate price computed from the opposite side is
dominant-strategy truthful.
-/
theorem paper_cross_sample_candidate_threshold_truthful
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    paper_digital_goods_truthful (thresholdPriceAuction (crossSampleCandidateThreshold side minWinners)) := by
  rw [paper_digital_goods_truthful_eq]
  exact crossSampleCandidateThresholdPriceAuction_truthful side minWinners

/--
RSOP-style deterministic skeleton with nonnegative offer prices: for any fixed
sample partition, offering each bidder the finite candidate offer price computed
from the opposite side is dominant-strategy truthful.
-/
theorem paper_cross_sample_candidate_offer_threshold_truthful
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    paper_digital_goods_truthful (thresholdPriceAuction (crossSampleCandidateOfferThreshold side minWinners)) := by
  rw [paper_digital_goods_truthful_eq]
  exact crossSampleCandidateOfferThresholdPriceAuction_truthful side minWinners

/--
The deterministic cross-sample offer auction has no positive transfers.
-/
theorem paper_cross_sample_candidate_offer_no_positive_transfers
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    (thresholdPriceAuction
      (crossSampleCandidateOfferThreshold side minWinners)).NoPositiveTransfers := by
  exact crossSampleCandidateOfferThresholdPriceAuction_noPositiveTransfers
    side minWinners

/--
Uniform average revenue over all deterministic cross-sample offer partitions is
nonnegative.
-/
theorem paper_average_cross_sample_candidate_offer_revenue_nonneg
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    0 ≤ averageCrossSampleCandidateOfferRevenue values minWinners := by
  exact averageCrossSampleCandidateOfferRevenue_nonneg values minWinners

/--
Paper-facing RSOP approximation seam: once the finite probabilistic
approximation certificate is proved, the cross-sample offer auction is
competitive against the two-winner fixed-price benchmark.
-/
theorem paper_cross_sample_offer_competitive_of_certificate
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (ratio : ℝ)
    (hcert : CrossSampleOfferApproximationCertificate values ratio) :
    twoWinnerFixedPriceBenchmarkValue values ≤
      ratio * averageCrossSampleCandidateOfferRevenue values 2 := by
  exact crossSampleOffer_competitive_of_certificate values ratio hcert

/--
The finite bidder-value candidate benchmark is nonnegative.
-/
theorem paper_finite_candidate_fixed_price_benchmark_nonneg
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    0 ≤ finiteCandidateFixedPriceBenchmark values minWinners := by
  exact finiteCandidateFixedPriceBenchmark_nonneg values minWinners

/--
Any feasible nonnegative fixed price with at least one required winner is
dominated by the finite bidder-value candidate benchmark.
-/
theorem paper_single_price_revenue_le_candidate_benchmark_of_feasible
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) {minWinners : ℕ} {p : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hfeasible : minWinners ≤ saleCount values p) :
    singlePriceRevenue values p ≤
      finiteCandidateFixedPriceBenchmark values minWinners := by
  exact singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
    values hmin hp hfeasible

/--
If there is at least one feasible two-winner fixed price, the finite
bidder-value candidate benchmark is the `F^(2)` fixed-price benchmark.
-/
theorem paper_two_winner_fixed_price_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ)
    (hexists : ∃ p, 0 ≤ p ∧ 2 ≤ saleCount values p) :
    IsTwoWinnerFixedPriceBenchmark values
      (finiteCandidateFixedPriceBenchmark values 2) := by
  exact finiteCandidateFixedPriceBenchmark_isTwoWinnerFixedPriceBenchmark_of_feasible
    values hexists

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
Mechanism-level two-slot GSP witness: the GSP-style position mechanism is not
dominant-strategy truthful.
-/
theorem paper_gsp_mechanism_not_truthful :
    ¬ PositionMechanism.TruthfulDominantStrategy
      gspCounterexampleEnvironment gspCounterexampleMechanism := by
  exact gspCounterexampleMechanism_not_truthful

/--
Sorted three-bidder/two-slot GSP with next-bid payments is not
dominant-strategy truthful.
-/
theorem paper_sorted_gsp_three_bidder_two_slot_not_truthful :
    ¬ PositionMechanism.TruthfulDominantStrategy
      gspCounterexampleEnvironment gsp3TwoSlotMechanism := by
  exact gsp3TwoSlot_not_truthful

/--
Local-envy-free position outcomes have no profitable assigned-slot deviation:
no bidder would prefer another winner's slot at that winner's per-click price.
-/
theorem paper_position_slot_envy_free_no_profitable_assigned_slot_deviation
    {Bidder Slot : Type*}
    (E : PositionEnvironment Slot)
    (O : PositionOutcome Bidder Slot) (values : Bidder → ℝ)
    (h : O.SlotEnvyFree E values) :
    O.NoProfitableAssignedSlotDeviation E values := by
  exact PositionOutcome.noProfitableAssignedSlotDeviation_of_slotEnvyFree
    E O values h

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

/-- Paper Definition: Utility in a Combinatorial Auction.
    $u_i(v_i, b) = v_i(A_i(b)) - p_i(b)$
-/
def paper_combinatorial_utility {Bidder Item : Type*}
    (M : CombinatorialAuction Bidder Item)
    (values reports : CombinatorialReport Bidder Item) (i : Bidder) : ℝ :=
  values i (M.allocation reports i) - M.payment reports i

theorem paper_combinatorial_utility_eq {Bidder Item : Type*}
    (M : CombinatorialAuction Bidder Item) (values reports : CombinatorialReport Bidder Item) (i : Bidder) :
    paper_combinatorial_utility M values reports i = M.utility values reports i := by
  rfl

/-- Paper Definition: Dominant Strategy Truthful on admissible domain.
    $v_i(A_i(v_i, b_{-i})) - p_i(v_i, b_{-i}) \ge v_i(A_i(b_i, b_{-i})) - p_i(b_i, b_{-i})$
-/
def paper_combinatorial_truthful_on {Bidder Item : Type*} [DecidableEq Bidder]
    (M : CombinatorialAuction Bidder Item)
    (admissible : CombinatorialReport Bidder Item → Prop) : Prop :=
  ∀ (values : CombinatorialReport Bidder Item),
    admissible values →
      ∀ (i : Bidder) (report : Bundle Item → ℝ),
        paper_combinatorial_utility M values (Function.update values i report) i ≤
          paper_combinatorial_utility M values values i

theorem paper_combinatorial_truthful_on_eq {Bidder Item : Type*} [DecidableEq Bidder]
    (M : CombinatorialAuction Bidder Item)
    (admissible : CombinatorialReport Bidder Item → Prop) :
    paper_combinatorial_truthful_on M admissible ↔ M.TruthfulDominantStrategyOn admissible := by
  rfl

/--
Target-bundle critical-price mechanisms are truthful on normalized bundle
valuations when each bidder's offered price is independent of that bidder's own
report.
-/
theorem paper_combinatorial_target_bundle_threshold_truthful_on_normalized
    {Bidder Item : Type*} [DecidableEq Bidder]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind : BundlePriceOwnReportIndependent price) :
    paper_combinatorial_truthful_on (targetBundleThresholdAuction target price)
      CombinatorialAuction.Normalized := by
  rw [paper_combinatorial_truthful_on_eq]
  exact targetBundleThresholdAuction_truthfulOn_normalized target price hind

/--
Target-bundle critical-price mechanisms are truthful on nonempty single-minded
valuation profiles when each bidder's offered price is independent of that
bidder's own report.
-/
theorem paper_combinatorial_target_bundle_threshold_truthful_on_single_minded
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind : BundlePriceOwnReportIndependent price) :
    paper_combinatorial_truthful_on (targetBundleThresholdAuction target price)
      IsNonemptySingleMindedProfile := by
  rw [paper_combinatorial_truthful_on_eq]
  exact targetBundleThresholdAuction_truthfulOn_singleMindedProfiles
    target price hind

/--
Target-bundle threshold allocations are feasible when every accepted target is
contained in the goods set and accepted targets are pairwise disjoint.
-/
theorem paper_combinatorial_target_bundle_threshold_feasible_of_pairwise_disjoint
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder] [DecidableEq Item]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (reports : CombinatorialReport Bidder Item)
    (goods : Finset Item)
    (hgoods : ∀ i,
      i ∈ targetBundleWinners target price reports → target i ⊆ goods)
    (hdisjoint :
      PairwiseDisjointDesired
        (targetAsSingleMindedBids target reports)
        (targetBundleWinners target price reports)) :
    IsFeasibleBundleAllocation
      ((targetBundleThresholdAuction target price).allocation reports)
      goods := by
  exact targetBundleThresholdAuction_feasible_of_pairwiseDisjoint
    target price reports goods hgoods hdisjoint

end Auction
end EconCSLean
