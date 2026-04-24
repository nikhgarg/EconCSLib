import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace EconCSLean
namespace Auction

/--
An unlimited-supply digital-goods auction.

The allocation quantity is represented as a real number so this same interface
can later admit fractional relaxations, lotteries in expectation, or position
auction click-through weights.  For the posted-price theorem below, allocations
are always `0` or `1`.
-/
structure DigitalGoodsAuction (Agent : Type*) where
  allocation : (Agent → ℝ) → Agent → ℝ
  payment : (Agent → ℝ) → Agent → ℝ

namespace DigitalGoodsAuction

variable {Agent : Type*}

/-- Quasilinear utility for a digital-good bidder with value `values i`. -/
def utility (M : DigitalGoodsAuction Agent)
    (values : Agent → ℝ) (i : Agent) (bids : Agent → ℝ) : ℝ :=
  values i * M.allocation bids i - M.payment bids i

/--
Dominant-strategy truthfulness for direct-report single-parameter auctions:
holding other reports fixed, replacing agent `i`'s truthful report by any
`report` cannot improve `i`'s utility.
-/
def TruthfulDominantStrategy [DecidableEq Agent]
    (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (values : Agent → ℝ) (i : Agent) (report : ℝ),
    M.utility values i (Function.update values i report) ≤
      M.utility values i values

/-- Truthful utility is always nonnegative. -/
def IndividuallyRational (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (values : Agent → ℝ) (i : Agent), 0 ≤ M.utility values i values

/-- The mechanism never pays money to agents. -/
def NoPositiveTransfers (M : DigitalGoodsAuction Agent) : Prop :=
  ∀ (bids : Agent → ℝ) (i : Agent), 0 ≤ M.payment bids i

/-- Total auction revenue under a bid profile. -/
noncomputable def revenue [Fintype Agent]
    (M : DigitalGoodsAuction Agent) (bids : Agent → ℝ) : ℝ :=
  ∑ i : Agent, M.payment bids i

end DigitalGoodsAuction

variable {Agent : Type*}

/--
An anonymous or personalized take-it-or-leave-it posted-price auction for an
unlimited-supply digital good.
-/
noncomputable def postedPrice (price : Agent → ℝ) : DigitalGoodsAuction Agent where
  allocation bids i := if price i ≤ bids i then 1 else 0
  payment bids i := if price i ≤ bids i then price i else 0

theorem postedPrice_utility_eq
    (price : Agent → ℝ) (values bids : Agent → ℝ) (i : Agent) :
    (postedPrice price).utility values i bids =
      if price i ≤ bids i then values i - price i else 0 := by
  by_cases h : price i ≤ bids i <;>
    simp [DigitalGoodsAuction.utility, postedPrice, h]

/--
Posted prices are dominant-strategy truthful in the unlimited-supply
digital-goods model.  This is the first reusable truthfulness lemma for the
2021 Test-of-Time digital-goods auction track.
-/
theorem postedPrice_truthful [DecidableEq Agent] (price : Agent → ℝ) :
    (postedPrice price).TruthfulDominantStrategy := by
  intro values i report
  have htruthUtility :
      (postedPrice price).utility values i values =
        if price i ≤ values i then values i - price i else 0 := by
    exact postedPrice_utility_eq price values values i
  have hreportUtility :
      (postedPrice price).utility values i (Function.update values i report) =
        if price i ≤ report then values i - price i else 0 := by
    rw [postedPrice_utility_eq]
    simp [Function.update]
  rw [htruthUtility, hreportUtility]
  by_cases htruth : price i ≤ values i
  · by_cases hreport : price i ≤ report
    · simp [htruth, hreport]
    · simp [htruth, hreport]
  · by_cases hreport : price i ≤ report
    · simpa only [htruth, hreport, ↓reduceIte, ge_iff_le]
        using sub_nonpos.mpr (le_of_lt (lt_of_not_ge htruth))
    · simp [htruth, hreport]

theorem postedPrice_individuallyRational (price : Agent → ℝ) :
    (postedPrice price).IndividuallyRational := by
  intro values i
  rw [postedPrice_utility_eq]
  by_cases h : price i ≤ values i
  · simp [h, sub_nonneg.mpr h]
  · simp [h]

theorem postedPrice_noPositiveTransfers
    (price : Agent → ℝ) (hprice : ∀ i, 0 ≤ price i) :
    (postedPrice price).NoPositiveTransfers := by
  intro bids i
  by_cases h : price i ≤ bids i
  · simpa [postedPrice, h] using hprice i
  · simp [postedPrice, h]

theorem postedPrice_revenue_eq [Fintype Agent]
    (price : Agent → ℝ) (bids : Agent → ℝ) :
    (postedPrice price).revenue bids =
      ∑ i : Agent, if price i ≤ bids i then price i else 0 := by
  simp [DigitalGoodsAuction.revenue, postedPrice]

/--
Revenue of a single anonymous posted price against a valuation/bid profile.
For the 2021 digital-goods paper this is the basic fixed-price benchmark term.
-/
noncomputable def singlePriceRevenue [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) : ℝ :=
  ∑ i : Agent, if p ≤ values i then p else 0

/-- Number of bidders who accept a single price. -/
noncomputable def saleCount [Fintype Agent] (values : Agent → ℝ) (p : ℝ) : ℕ :=
  ((Finset.univ : Finset Agent).filter fun i => p ≤ values i).card

theorem singlePriceRevenue_eq_saleCount_mul [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) :
    singlePriceRevenue values p = (saleCount values p : ℝ) * p := by
  classical
  rw [singlePriceRevenue, saleCount, ← Finset.sum_filter]
  simp

theorem singlePriceRevenue_nonneg [Fintype Agent]
    (values : Agent → ℝ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ singlePriceRevenue values p := by
  classical
  rw [singlePriceRevenue_eq_saleCount_mul]
  exact mul_nonneg (Nat.cast_nonneg _) hp

theorem postedPrice_const_revenue_eq_singlePriceRevenue [Fintype Agent]
    (values : Agent → ℝ) (p : ℝ) :
    (postedPrice fun _ : Agent => p).revenue values =
      singlePriceRevenue values p := by
  simp [postedPrice_revenue_eq, singlePriceRevenue]

/--
Certificate-style fixed-price benchmark for digital goods.

The Goldberg-Hartline-Wright benchmark is a maximum over prices satisfying
extra sale-count restrictions.  This predicate records the exact upper-bound
property without committing yet to the finite maximizer proof.
-/
def IsFixedPriceBenchmark [Fintype Agent]
    (values : Agent → ℝ) (minWinners : ℕ) (benchmark : ℝ) : Prop :=
  (∃ p, 0 ≤ p ∧ minWinners ≤ saleCount values p ∧
    benchmark = singlePriceRevenue values p) ∧
  ∀ p, 0 ≤ p → minWinners ≤ saleCount values p →
    singlePriceRevenue values p ≤ benchmark

/-- The `F^(2)`-style benchmark interface: one price, at least two winners. -/
def IsTwoWinnerFixedPriceBenchmark [Fintype Agent]
    (values : Agent → ℝ) (benchmark : ℝ) : Prop :=
  IsFixedPriceBenchmark values 2 benchmark

/--
A threshold price rule is own-bid independent when changing bidder `i`'s report
does not change the price offered to `i`.
-/
def OwnBidIndependent [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) : Prop :=
  ∀ (bids : Agent → ℝ) (i : Agent) (report : ℝ),
    threshold (Function.update bids i report) i = threshold bids i

/--
Digital-goods auction that offers every bidder a threshold price and sells iff
the bid meets that threshold.
-/
noncomputable def thresholdPriceAuction [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) : DigitalGoodsAuction Agent where
  allocation bids i := if threshold bids i ≤ bids i then 1 else 0
  payment bids i := if threshold bids i ≤ bids i then threshold bids i else 0

theorem thresholdPriceAuction_utility_eq [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ)
    (values bids : Agent → ℝ) (i : Agent) :
    (thresholdPriceAuction threshold).utility values i bids =
      if threshold bids i ≤ bids i then values i - threshold bids i else 0 := by
  by_cases h : threshold bids i ≤ bids i <;>
    simp [DigitalGoodsAuction.utility, thresholdPriceAuction, h]

/--
Own-bid independent threshold-price auctions are dominant-strategy truthful.
This is the reusable DSIC core for random-sampling and market-price
digital-goods auctions.
-/
theorem thresholdPriceAuction_truthful [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ)
    (hind : OwnBidIndependent threshold) :
    (thresholdPriceAuction threshold).TruthfulDominantStrategy := by
  intro values i report
  have htruthUtility :
      (thresholdPriceAuction threshold).utility values i values =
        if threshold values i ≤ values i then
          values i - threshold values i
        else 0 := by
    exact thresholdPriceAuction_utility_eq threshold values values i
  have hreportUtility :
      (thresholdPriceAuction threshold).utility values i
          (Function.update values i report) =
        if threshold values i ≤ report then
          values i - threshold values i
        else 0 := by
    rw [thresholdPriceAuction_utility_eq]
    simp [Function.update, hind values i report]
  rw [htruthUtility, hreportUtility]
  by_cases htruth : threshold values i ≤ values i
  · by_cases hreport : threshold values i ≤ report
    · simp [htruth, hreport]
    · simp [htruth, hreport]
  · by_cases hreport : threshold values i ≤ report
    · simpa only [htruth, hreport, ↓reduceIte, ge_iff_le]
        using sub_nonpos.mpr (le_of_lt (lt_of_not_ge htruth))
    · simp [htruth, hreport]

theorem thresholdPriceAuction_individuallyRational [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) :
    (thresholdPriceAuction threshold).IndividuallyRational := by
  intro values i
  rw [thresholdPriceAuction_utility_eq]
  by_cases h : threshold values i ≤ values i
  · simp [h, sub_nonneg.mpr h]
  · simp [h]

theorem thresholdPriceAuction_noPositiveTransfers [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ)
    (hthreshold : ∀ bids i, 0 ≤ threshold bids i) :
    (thresholdPriceAuction threshold).NoPositiveTransfers := by
  intro bids i
  by_cases h : threshold bids i ≤ bids i
  · simpa [thresholdPriceAuction, h] using hthreshold bids i
  · simp [thresholdPriceAuction, h]

end Auction
end EconCSLean
