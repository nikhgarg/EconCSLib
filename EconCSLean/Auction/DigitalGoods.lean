import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

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

end Auction
end EconCSLean
