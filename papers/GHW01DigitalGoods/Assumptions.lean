import GHW01DigitalGoods.MainTheorems

/-!
# Paper Assumptions: GHW01 Digital Goods

This file records source theorem conditions used by the compact paper-facing
interface: normalized bid ranges, benchmark prerequisites, truthfulness
conditions, and lower-bound parameter conditions.
-/

namespace GHW01DigitalGoods

open EconCSLib.Auction
open scoped BigOperators

/-- The paper normalizes the lowest/highest bid scale in the high-value theorems. -/
-- audit-premise: hh_ge_one : 1 ≤ h
-- audit-premise: hhigh_pos : 0 < highValue
-- audit-premise: hh_pos : 0 < h
-- audit-premise: hhigh_ge_two : 2 ≤ highValue
abbrev assumption_high_value_scale_conditions
    (h sampleHighValue : ℝ) (lowerBoundHighValue : ℕ) : Prop :=
  1 ≤ h ∧ 0 < sampleHighValue ∧ 0 < h ∧ 2 ≤ lowerBoundHighValue

/-- High-value theorem inputs have bids in the normalized range. -/
-- audit-premise: hvalue_ge_one : ∀ i : Agent, 1 ≤ values i
-- audit-premise: hvalue_le_h : ∀ i : Agent, values i ≤ h
-- audit-premise: hvalues_nonneg : ∀ i : Agent, 0 ≤ values i
-- audit-premise: hvalue_bound : ∀ i, values i ≤ highValue
abbrev assumption_bid_value_range_conditions {Agent : Type*}
    (values : Agent → ℝ) (h highValue : ℝ) : Prop :=
  (∀ i : Agent, 1 ≤ values i) ∧
    (∀ i : Agent, values i ≤ h) ∧
      (∀ i : Agent, 0 ≤ values i) ∧
        (∀ i : Agent, values i ≤ highValue)

/-- Corollary 4.2 fixes `h` as a maximum bid. -/
-- audit-premise: hmax : ∃ i : Agent, values i = h
abbrev assumption_high_value_attained {Agent : Type*}
    (values : Agent → ℝ) (h : ℝ) : Prop :=
  ∃ i : Agent, values i = h

/-- Weighted-pairing statements expose the paper's total-value notation. -/
-- audit-premise: htotal : total = totalValue values
abbrev assumption_total_value_notation {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (total : ℝ) : Prop :=
  total = ∑ i : Agent, values i

/-- Theorem 7.1 assumes the high-bid value is small relative to total value. -/
-- audit-premise: hlarge : 4 * h ≤ total
abbrev assumption_weighted_pairing_large_market (h total : ℝ) : Prop :=
  4 * h ≤ total

/-- Theorem 7.2 assumes the two-winner benchmark is at least twice the high bid. -/
-- audit-premise: hF_ge_two_h : 2 * h ≤ twoWinnerBenchmark values
abbrev assumption_two_winner_benchmark_large_enough
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : Agent → ℝ) (h : ℝ) : Prop :=
  2 * h ≤ twoWinnerFixedPriceBenchmarkValue values

/-- Theorem 7.2 packages the logarithmic factor with `s`. -/
-- audit-premise: hs_ge_two : 2 ≤ s
-- audit-premise: hlog_le_s_sq : Real.logb 2 h + 2 ≤ s ^ 2
abbrev assumption_weighted_pairing_log_factor (h s : ℝ) : Prop :=
  2 ≤ s ∧ Real.logb 2 h + 2 ≤ s ^ 2

/-- Lemma 8.1 and Lemma 9.2 are stated for truthful auctions. -/
-- audit-premise: hM : truthful M
-- audit-premise: htruth : truthful M
abbrev assumption_truthful_auction_condition
    {Agent : Type*} [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) : Prop :=
  paper_digital_goods_truthful M

/-- Lemma 8.1 compares a lower bid with a higher bid. -/
-- audit-premise: hlt : low < high
abbrev assumption_low_bid_below_high_bid (low high : ℝ) : Prop :=
  low < high

/-- Lower-bound theorems quantify over positive constants. -/
-- audit-premise: halpha_pos : 0 < alpha
abbrev assumption_lower_bound_positive_alpha (alpha : ℕ) : Prop :=
  0 < alpha

end GHW01DigitalGoods
