import GHW01DigitalGoods.MainTheorems

/-!
# Paper Interface: Competitive Auctions and Digital Goods

This is the compact human-facing Lean surface for the Goldberg-Hartline-Wright
digital-goods paper.  It lists the paper definitions and direct source
theorem statements; supporting auction lemmas live in `MainTheorems.lean` and
the reusable auction library.
-/

namespace GHW01DigitalGoods
namespace PaperInterface

open EconCSLib.Auction
open scoped BigOperators

noncomputable section

/-! ## Paper Definitions -/

/-- Digital-goods auction revenue: total payments collected from all bidders. -/
def revenue {Agent : Type*} [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, M.payment values i

/--
Dominant-strategy truthfulness: truthful bidding weakly dominates replacing
one agent's value report by any alternative report.
-/
def truthful {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (values : Agent → ℝ) (i : Agent) (report : ℝ),
    M.utility values i (Function.update values i report) ≤
      M.utility values i values

/-- Single-price revenue at price `p`. -/
def singlePriceRevenue {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) : ℝ :=
  ∑ i : Agent, if p ≤ values i then p else 0

/--
Fixed-price benchmark over bidder-value candidate prices, requiring at least
`minWinners` winners.
-/
def fixedPriceBenchmark {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) : ℝ :=
  (Finset.univ : Finset Agent).sup'
    (by
      obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
      exact ⟨i, by simp⟩)
    (candidateFixedPriceRevenue values minWinners)

/--
Two-winner fixed-price benchmark `F^(2)`: the best single-price revenue selling
to at least two bidders.
-/
def twoWinnerBenchmark {Agent : Type*}
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) : ℝ :=
  twoWinnerFixedPriceBenchmarkValue values

/-- Total bid value `T = sum_i v_i`. -/
def totalValue {Agent : Type*} [Fintype Agent] (values : Agent → ℝ) : ℝ :=
  ∑ i : Agent, values i

/-- Expected revenue of the weighted-pairing auction. -/
def weightedPairingRevenue {Agent : Type*}
    [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) : ℝ :=
  weightedPairingExpectedRevenue values

/-! ## Source Theorems -/

/-- Theorem 4.1: high-value profiles have a logarithmic fixed-price lower bound. -/
theorem theorem4_1_high_value
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) {h : ℝ}
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    totalValue values ≤
      (2 * (Real.logb 2 h + 2)) * fixedPriceBenchmark values 1 := by
  simpa [totalValue, fixedPriceBenchmark] using
    paper_theorem4_1_finite_candidate_benchmark_from_logb_high_value
      values hh_ge_one hvalue_ge_one hvalue_le_h

/-- Corollary 4.2: truncation gives a fixed-price lower bound in terms of `n`. -/
theorem corollary4_2_truncation
    (model : PaperCorollary42TruncationModel) :
    model.totalValue ≤
      (4 * model.binCount) * model.fixedPriceBenchmark := by
  exact paper_corollary4_2_fixed_price_lower_bound_of_truncation_model model

/-- Lemma 6.1: fair-coin random sampling lower-tail estimate. -/
theorem lemma6_1_fair_coin
    {Index : Type*} (s : Finset Index) (keep : Bool) :
    (EconCSLib.FairCoin.productMeasure Index).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
      Real.exp (-(s.card : ℝ) / 36) := by
  exact paper_aux_theorem6_2_fair_coin_lower_tail_relaxed s keep

/-- Theorem 6.2: random-sampling auction revenue guarantee. -/
theorem theorem6_2_random_sampling
    {n : ℕ} [NeZero n]
    (model : PaperTheorem62FairCoinSortedModel n) :
    1 - Real.exp (-(model.alpha : ℝ) / 36) -
        40 * Real.exp (-(model.alpha : ℝ) / 72) ≤
      (EconCSLib.FairCoin.productMeasure (Fin n)).real
        {side |
          singlePriceRevenue model.values model.price ≤
            6 *
              (thresholdPriceAuction
                (crossSampleCandidateOfferThreshold
                  side model.minWinners)).revenue model.values} := by
  simpa [singlePriceRevenue] using
    paper_theorem6_2_fair_coin_revenue_bound_of_sorted_model model

/-- Theorem 7.1: weighted pairing gets a logarithmic guarantee when `4h <= T`. -/
theorem theorem7_1_weighted_pairing
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) {h total : ℝ}
    (htotal : total = totalValue values)
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hlarge : 4 * h ≤ total) :
    total ≤ 192 * (Real.logb 2 h + 2) * weightedPairingRevenue values := by
  simpa [totalValue, weightedPairingRevenue] using
    paper_theorem7_1_weighted_pairing_log_bound_from_logb_high_value
      values htotal hh_ge_one hvalue_ge_one hvalue_le_h hlarge

/-- Theorem 7.2: weighted pairing competes with the two-winner benchmark. -/
theorem theorem7_2_weighted_pairing_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) {h total s : ℝ}
    (htotal : total = totalValue values)
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hF_ge_two_h : 2 * h ≤ twoWinnerBenchmark values)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : Real.logb 2 h + 2 ≤ s ^ 2) :
    twoWinnerBenchmark values ≤ 576 * s * weightedPairingRevenue values := by
  simpa [totalValue, twoWinnerBenchmark, weightedPairingRevenue] using
    paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark_from_logb_high_value
      values htotal hh_ge_one hvalue_ge_one hvalue_le_h hF_ge_two_h
      hs_ge_two hlog_le_s_sq

/-- Lemma 8.1: truthfulness implies monotone own-bid allocation. -/
theorem lemma8_1_truthful_monotone
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (hM : truthful M)
    (bids : Agent → ℝ) (i : Agent) {low high : ℝ} (hlt : low < high) :
    M.allocation (Function.update bids i low) i ≤
      M.allocation (Function.update bids i high) i := by
  simpa [truthful, paper_digital_goods_truthful] using
    paper_lemma8_1_allocation_mono_own_bid_of_truthful M hM bids i hlt

/-- Theorem 8.2: every truthful auction's revenue is bounded by `F`. -/
theorem theorem8_2_truthful_revenue_upper_bound
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (model :
      PaperTheorem82AnonymousSortedBidTruthfulModel M values hcard) :
    M.revenue values ≤ fixedPriceBenchmark values 1 := by
  change M.revenue values ≤ finiteCandidateFixedPriceBenchmark values 1
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_anonymous_sorted_bid_truthful_model
      M values hcard model

/-- Theorem 9.1: bid-independent auctions have a lower-bound witness. -/
theorem theorem9_1_bid_independent_lower_bound
    (priceRule : List ℝ → ℝ) {highValue alpha : ℕ}
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (highValue : ℝ) *
          twoValueBidIndependentPriceRevenue
            (twoValueListBidIndependentThresholdPrice priceRule highValue)
            highValue highCount lowCount ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_1_bid_independent_list_rule_scaled_lower_bound_fixed_price_benchmark
      priceRule hhigh_ge_two halpha_pos

/-- Lemma 9.2: deterministic truthful binary auctions admit threshold offers. -/
theorem lemma9_2_threshold_domination
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (htruth : truthful M)
    (hIR : M.IndividuallyRational)
    (hNPT : M.NoPositiveTransfers)
    (hbinary : M.BinaryAllocation)
    (bids : Agent → ℝ) (i : Agent) :
    ∃ threshold,
      0 ≤ threshold ∧
        DeterministicOfferThresholdDominates
          (deterministicAuctionOffer M bids i) threshold := by
  simpa [truthful, paper_digital_goods_truthful] using
    paper_lemma9_2_deterministic_truthful_auction_exists_nonnegative_threshold_dominates
      M htruth hIR hNPT hbinary bids i

/-- Theorem 9.3: deterministic truthful auctions have a lower-bound witness. -/
theorem theorem9_3_deterministic_truthful_lower_bound
    {highValue alpha : ℕ}
    (model : PaperTheorem93AnonymousTruthfulDeterministicModel highValue)
    (hhigh_ge_two : 2 ≤ highValue) (halpha_pos : 0 < alpha) :
    ∃ highCount lowCount : ℕ,
      (model.auctionFamily highCount lowCount).revenue
          (twoValueBidProfile highValue highCount lowCount) /
          twoValueFixedPriceBenchmark highValue highCount lowCount ≤
        1 / (highValue : ℝ) ∧
      (highValue : ℝ) * (alpha : ℝ) ≤
        twoValueFixedPriceBenchmark highValue highCount lowCount := by
  exact
    paper_theorem9_3_deterministic_truthful_ratio_witness_of_anonymous_truthful_deterministic_model
      model hhigh_ge_two halpha_pos

end

end PaperInterface
end GHW01DigitalGoods
