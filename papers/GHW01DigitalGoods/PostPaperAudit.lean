import GHW01DigitalGoods.MainTheorems

/-!
# Post-paper audit: Competitive Auctions and Digital Goods

This file is the Lean-side endpoint ledger for the Goldberg-Hartline-Wright
digital-goods paper. For the compact human-facing statement surface, read
`PaperInterface.lean`; each theorem below is an importable source-numbered
endpoint delegated to the paper-facing theorem exported by
`GHW01DigitalGoods.MainTheorems`.

Cached source text inventory checked by this audit:

- Theorem 4.1, line 359: `F >= T / (2 log h)`.
- Corollary 4.2, line 301: `F >= T / (4 log n)`.
- Lemma 6.1, line 428: random subset split lower-tail estimate.
- Theorem 6.2, line 479: random sampling auction revenue guarantee.
- Theorem 7.1, line 563: weighted pairing gets `Omega(T / log h)` when `4h <= T`.
- Theorem 7.2, line 626: weighted pairing gets `Omega(F / log h)` when `F >= 2h`.
- Lemma 8.1, line 747: truthfulness implies monotone win probabilities.
- Theorem 8.2, line 833: any truthful auction has expected revenue at most `F`.
- Theorem 9.1, line 979: bid-independent lower-bound witness.
- Lemma 9.2, line 1105: truthful deterministic auctions are bid-independent.
- Theorem 9.3, line 1100: deterministic truthful lower-bound witness.

The corresponding README rows and DAG nodes are checked in
`FINAL_VALIDATION_REPORT.md`.
-/

namespace GHW01DigitalGoods

open EconCSLib.Auction
open scoped BigOperators

/-- Audit endpoint for GHW Theorem 4.1: normalized `[1,h]` high-value model. -/
theorem audit_theorem4_1_high_value
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) {h : ℝ}
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h) :
    totalBidValue values ≤
      (2 * (Real.logb 2 h + 2)) *
        finiteCandidateFixedPriceBenchmark values 1 := by
  exact
    paper_theorem4_1_finite_candidate_benchmark_from_logb_high_value
      values hh_ge_one hvalue_ge_one hvalue_le_h

/-- Audit endpoint for GHW Corollary 4.2: truncation plus Theorem 4.1. -/
theorem audit_corollary4_2_truncation
    (model : PaperCorollary42TruncationModel) :
    model.totalValue ≤
      (4 * model.binCount) * model.fixedPriceBenchmark := by
  exact paper_corollary4_2_fixed_price_lower_bound_of_truncation_model model

/-- Audit endpoint for GHW Lemma 6.1: independent fair-coin lower-tail form. -/
theorem audit_lemma6_1_fair_coin
    {Index : Type*} (s : Finset Index) (keep : Bool) :
    (EconCSLib.FairCoin.productMeasure Index).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
      Real.exp (-(s.card : ℝ) / 36) := by
  exact paper_aux_theorem6_2_fair_coin_lower_tail_relaxed s keep

/--
Audit endpoint for GHW Theorem 6.2. The model packages sorted bids,
independent fair-coin sampling, the feasible sample-size side condition, and
the paper large-market condition `alpha * h <= F_p`.
-/
theorem audit_theorem6_2_random_sampling
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
  exact paper_theorem6_2_fair_coin_revenue_bound_of_sorted_model model

/-- Audit endpoint for GHW Theorem 7.1 under the paper condition `4h <= T`. -/
theorem audit_theorem7_1_weighted_pairing
    {Agent : Type*} [Fintype Agent] [DecidableEq Agent] [LinearOrder Agent]
    (values : Agent → ℝ) {h totalValue : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hlarge : 4 * h ≤ totalValue) :
    totalValue ≤
      192 * (Real.logb 2 h + 2) *
        weightedPairingExpectedRevenue values := by
  exact
    paper_theorem7_1_weighted_pairing_log_bound_from_logb_high_value
      values htotal hh_ge_one hvalue_ge_one hvalue_le_h hlarge

/-- Audit endpoint for GHW Theorem 7.2 under the paper condition `F^(2) >= 2h`. -/
theorem audit_theorem7_2_weighted_pairing_benchmark
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (values : Agent → ℝ) {h totalValue s : ℝ}
    (htotal : totalValue = totalBidValue values)
    (hh_ge_one : 1 ≤ h)
    (hvalue_ge_one : ∀ i : Agent, 1 ≤ values i)
    (hvalue_le_h : ∀ i : Agent, values i ≤ h)
    (hF_ge_two_h :
      2 * h ≤ twoWinnerFixedPriceBenchmarkValue values)
    (hs_ge_two : 2 ≤ s)
    (hlog_le_s_sq : Real.logb 2 h + 2 ≤ s ^ 2) :
    twoWinnerFixedPriceBenchmarkValue values ≤
      576 * s * weightedPairingExpectedRevenue values := by
  exact
    paper_theorem7_2_weighted_pairing_bound_for_two_winner_benchmark_from_logb_high_value
      values htotal hh_ge_one hvalue_ge_one hvalue_le_h hF_ge_two_h
      hs_ge_two hlog_le_s_sq

/-- Audit endpoint for GHW Lemma 8.1: own-bid monotonicity from truthfulness. -/
theorem audit_lemma8_1_truthful_monotone
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (hM : paper_digital_goods_truthful M)
    (bids : Agent → ℝ) (i : Agent) {low high : ℝ} (hlt : low < high) :
    M.allocation (Function.update bids i low) i ≤
      M.allocation (Function.update bids i high) i := by
  exact paper_lemma8_1_allocation_mono_own_bid_of_truthful M hM bids i hlt

/--
Audit endpoint for GHW Theorem 8.2. The model packages the paper's anonymous
sorted-bid convention, adjacent-rank symmetry, endpoint identities, and
truthfulness/IR payment comparisons.
-/
theorem audit_theorem8_2_truthful_revenue_upper_bound
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [LinearOrder Agent]
    (M : DigitalGoodsAuction Agent) (values : Agent → ℝ) {n : ℕ}
    (hcard : (Finset.univ : Finset Agent).card = n)
    (model :
      PaperTheorem82AnonymousSortedBidTruthfulModel M values hcard) :
    M.revenue values ≤ finiteCandidateFixedPriceBenchmark values 1 := by
  exact
    paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_anonymous_sorted_bid_truthful_model
      M values hcard model

/--
Audit endpoint for GHW Theorem 9.1 in the paper anonymous erased-bid-list
model for deterministic bid-independent auctions.
-/
theorem audit_theorem9_1_bid_independent_lower_bound
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

/--
Audit endpoint for GHW Lemma 9.2: truthful deterministic IR/NPT binary auction
slices admit nonnegative critical-price thresholds.
-/
theorem audit_lemma9_2_threshold_domination
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent)
    (htruth : paper_digital_goods_truthful M)
    (hIR : M.IndividuallyRational)
    (hNPT : M.NoPositiveTransfers)
    (hbinary : M.BinaryAllocation)
    (bids : Agent → ℝ) (i : Agent) :
    ∃ threshold,
      0 ≤ threshold ∧
        DeterministicOfferThresholdDominates
          (deterministicAuctionOffer M bids i) threshold := by
  exact
    paper_lemma9_2_deterministic_truthful_auction_exists_nonnegative_threshold_dominates
      M htruth hIR hNPT hbinary bids i

/--
Audit endpoint for GHW Theorem 9.3. The model packages anonymous truthful
deterministic binary auctions with IR, NPT, binary allocation, and the paper's
erased-bid critical-price convention.
-/
theorem audit_theorem9_3_deterministic_truthful_lower_bound
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

end GHW01DigitalGoods
