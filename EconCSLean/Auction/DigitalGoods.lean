import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
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
Revenue from using bidder `i`'s value as the candidate single price, with
infeasible prices assigned value `0`.
-/
noncomputable def candidateFixedPriceRevenue [Fintype Agent]
    (values : Agent → ℝ) (minWinners : ℕ) (i : Agent) : ℝ :=
  if 0 ≤ values i ∧ minWinners ≤ saleCount values (values i) then
    singlePriceRevenue values (values i)
  else 0

theorem candidateFixedPriceRevenue_nonneg [Fintype Agent]
    (values : Agent → ℝ) (minWinners : ℕ) (i : Agent) :
    0 ≤ candidateFixedPriceRevenue values minWinners i := by
  classical
  by_cases h : 0 ≤ values i ∧ minWinners ≤ saleCount values (values i)
  · simpa [candidateFixedPriceRevenue, h] using
      singlePriceRevenue_nonneg values h.1
  · simp [candidateFixedPriceRevenue, h]

/--
Finite candidate-price benchmark obtained by maximizing over bidder values.

The full `F^(2)` theorem still needs the paper lemma that a globally optimal
single price may be chosen from a bidder value. This definition provides the
finite maximizer needed once that reduction is proved.
-/
noncomputable def finiteCandidateFixedPriceBenchmark [Fintype Agent]
    [Nonempty Agent] (values : Agent → ℝ) (minWinners : ℕ) : ℝ :=
  (Finset.univ : Finset Agent).sup'
    (by
      obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
      exact ⟨i, by simp⟩)
    (candidateFixedPriceRevenue values minWinners)

theorem candidateFixedPriceRevenue_le_finiteCandidateFixedPriceBenchmark
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) (i : Agent) :
    candidateFixedPriceRevenue values minWinners i ≤
      finiteCandidateFixedPriceBenchmark values minWinners := by
  unfold finiteCandidateFixedPriceBenchmark
  exact Finset.le_sup'
    (s := (Finset.univ : Finset Agent))
    (f := candidateFixedPriceRevenue values minWinners)
    (b := i) (by simp)

theorem finiteCandidateFixedPriceBenchmark_nonneg
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    0 ≤ finiteCandidateFixedPriceBenchmark values minWinners := by
  obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
  exact le_trans (candidateFixedPriceRevenue_nonneg values minWinners i)
    (candidateFixedPriceRevenue_le_finiteCandidateFixedPriceBenchmark
      values minWinners i)

theorem singlePriceRevenue_candidate_le_finiteCandidateFixedPriceBenchmark
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) (i : Agent)
    (hprice : 0 ≤ values i)
    (hwinners : minWinners ≤ saleCount values (values i)) :
    singlePriceRevenue values (values i) ≤
      finiteCandidateFixedPriceBenchmark values minWinners := by
  have hcand :
      candidateFixedPriceRevenue values minWinners i =
        singlePriceRevenue values (values i) := by
    simp [candidateFixedPriceRevenue, hprice, hwinners]
  rw [← hcand]
  exact candidateFixedPriceRevenue_le_finiteCandidateFixedPriceBenchmark
    values minWinners i

/--
Any nonnegative feasible fixed price is dominated by a feasible bidder-value
candidate price, provided at least one winner is required.

This is the finite benchmark-reduction lemma for the digital-goods track: after
this point, it is enough to maximize over bidder values.
-/
theorem singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) {minWinners : ℕ} {p : ℝ}
    (hmin : 1 ≤ minWinners)
    (hp : 0 ≤ p)
    (hfeasible : minWinners ≤ saleCount values p) :
    singlePriceRevenue values p ≤
      finiteCandidateFixedPriceBenchmark values minWinners := by
  classical
  let winners : Finset Agent :=
    (Finset.univ : Finset Agent).filter fun i => p ≤ values i
  have hwinners_card : winners.card = saleCount values p := by
    simp [winners, saleCount]
  have hmin_pos : 0 < minWinners :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one hmin
  have hwinners_nonempty : winners.Nonempty := by
    apply Finset.card_pos.mp
    rw [hwinners_card]
    exact lt_of_lt_of_le hmin_pos hfeasible
  let winnerValues : Finset ℝ := winners.image values
  have hwinnerValues_nonempty : winnerValues.Nonempty :=
    hwinners_nonempty.image values
  let q : ℝ := winnerValues.min' hwinnerValues_nonempty
  have hq_mem : q ∈ winnerValues := by
    exact Finset.min'_mem winnerValues hwinnerValues_nonempty
  obtain ⟨i, hi_winner, hiq⟩ := Finset.mem_image.mp hq_mem
  have hp_le_of_winnerValue : ∀ x ∈ winnerValues, p ≤ x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
    exact (Finset.mem_filter.mp hj).2
  have hpq : p ≤ q := by
    exact Finset.le_min' (s := winnerValues)
      (H := hwinnerValues_nonempty) p hp_le_of_winnerValue
  have hq_le_of_winner : ∀ j, j ∈ winners → q ≤ values j := by
    intro j hj
    have hmem : values j ∈ winnerValues :=
      Finset.mem_image.mpr ⟨j, hj, rfl⟩
    exact Finset.min'_le winnerValues (values j) hmem
  have hwinners_subset_q :
      winners ⊆
        ((Finset.univ : Finset Agent).filter fun j => q ≤ values j) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨by simp, hq_le_of_winner j hj⟩
  have hcount_le : saleCount values p ≤ saleCount values q := by
    rw [← hwinners_card]
    unfold saleCount
    exact Finset.card_le_card hwinners_subset_q
  have hrev_le_q : singlePriceRevenue values p ≤ singlePriceRevenue values q := by
    rw [singlePriceRevenue_eq_saleCount_mul values p,
      singlePriceRevenue_eq_saleCount_mul values q]
    have hcount_cast :
        (saleCount values p : ℝ) ≤ (saleCount values q : ℝ) := by
      exact_mod_cast hcount_le
    have hq_nonneg : 0 ≤ q := le_trans hp hpq
    calc
      (saleCount values p : ℝ) * p
          ≤ (saleCount values p : ℝ) * q :=
            mul_le_mul_of_nonneg_left hpq (Nat.cast_nonneg _)
      _ ≤ (saleCount values q : ℝ) * q :=
            mul_le_mul_of_nonneg_right hcount_cast hq_nonneg
  have hq_nonneg : 0 ≤ q := le_trans hp hpq
  have hq_feasible : minWinners ≤ saleCount values q :=
    le_trans hfeasible hcount_le
  have hq_rev_le_benchmark :
      singlePriceRevenue values q ≤
        finiteCandidateFixedPriceBenchmark values minWinners := by
    rw [← hiq]
    exact singlePriceRevenue_candidate_le_finiteCandidateFixedPriceBenchmark
      values minWinners i (by simpa [hiq] using hq_nonneg)
      (by simpa [hiq] using hq_feasible)
  exact le_trans hrev_le_q hq_rev_le_benchmark

theorem exists_candidateFixedPriceRevenue_eq_finiteCandidateFixedPriceBenchmark
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    ∃ i : Agent,
      finiteCandidateFixedPriceBenchmark values minWinners =
        candidateFixedPriceRevenue values minWinners i := by
  classical
  let H : (Finset.univ : Finset Agent).Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty Agent)
    exact ⟨i, by simp⟩
  obtain ⟨i, _hi, hmax⟩ :=
    (Finset.univ : Finset Agent).exists_mem_eq_sup'
      (f := candidateFixedPriceRevenue values minWinners) H
  exact ⟨i, hmax⟩

/-- A bidder whose value attains the finite candidate-price benchmark. -/
noncomputable def finiteCandidateBenchmarkBidder [Fintype Agent]
    [Nonempty Agent] (values : Agent → ℝ) (minWinners : ℕ) : Agent :=
  Classical.choose
    (exists_candidateFixedPriceRevenue_eq_finiteCandidateFixedPriceBenchmark
      values minWinners)

/-- Candidate price selected from a benchmark-attaining bidder value. -/
noncomputable def finiteCandidateBenchmarkPrice [Fintype Agent]
    [Nonempty Agent] (values : Agent → ℝ) (minWinners : ℕ) : ℝ :=
  values (finiteCandidateBenchmarkBidder values minWinners)

theorem finiteCandidateFixedPriceBenchmark_eq_selected_candidateRevenue
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) (minWinners : ℕ) :
    finiteCandidateFixedPriceBenchmark values minWinners =
      candidateFixedPriceRevenue values minWinners
        (finiteCandidateBenchmarkBidder values minWinners) := by
  exact Classical.choose_spec
    (exists_candidateFixedPriceRevenue_eq_finiteCandidateFixedPriceBenchmark
      values minWinners)

theorem finiteCandidateFixedPriceBenchmark_isFixedPriceBenchmark_of_feasible
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ) {minWinners : ℕ}
    (hmin : 1 ≤ minWinners)
    (hexists : ∃ p, 0 ≤ p ∧ minWinners ≤ saleCount values p) :
    IsFixedPriceBenchmark values minWinners
      (finiteCandidateFixedPriceBenchmark values minWinners) := by
  classical
  constructor
  · let i := finiteCandidateBenchmarkBidder values minWinners
    have hbench :
        finiteCandidateFixedPriceBenchmark values minWinners =
          candidateFixedPriceRevenue values minWinners i := by
      simpa [i] using
        finiteCandidateFixedPriceBenchmark_eq_selected_candidateRevenue
          values minWinners
    by_cases hsel : 0 ≤ values i ∧
        minWinners ≤ saleCount values (values i)
    · refine ⟨values i, hsel.1, hsel.2, ?_⟩
      simpa [candidateFixedPriceRevenue, hsel] using hbench
    · have hbench_zero :
          finiteCandidateFixedPriceBenchmark values minWinners = 0 := by
        simpa [candidateFixedPriceRevenue, hsel] using hbench
      obtain ⟨p, hp, hfeasible⟩ := hexists
      have hrev_le :
          singlePriceRevenue values p ≤
            finiteCandidateFixedPriceBenchmark values minWinners :=
        singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
          values hmin hp hfeasible
      have hrev_nonneg : 0 ≤ singlePriceRevenue values p :=
        singlePriceRevenue_nonneg values hp
      have hrev_zero : singlePriceRevenue values p = 0 := by
        exact le_antisymm (by simpa [hbench_zero] using hrev_le) hrev_nonneg
      refine ⟨p, hp, hfeasible, ?_⟩
      rw [hbench_zero, hrev_zero]
  · intro p hp hfeasible
    exact singlePriceRevenue_le_finiteCandidateFixedPriceBenchmark_of_feasible
      values hmin hp hfeasible

theorem finiteCandidateFixedPriceBenchmark_isTwoWinnerFixedPriceBenchmark_of_feasible
    [Fintype Agent] [Nonempty Agent]
    (values : Agent → ℝ)
    (hexists : ∃ p, 0 ≤ p ∧ 2 ≤ saleCount values p) :
    IsTwoWinnerFixedPriceBenchmark values
      (finiteCandidateFixedPriceBenchmark values 2) := by
  exact finiteCandidateFixedPriceBenchmark_isFixedPriceBenchmark_of_feasible
    values (minWinners := 2) (by decide) hexists

/--
A threshold price rule is own-bid independent when changing bidder `i`'s report
does not change the price offered to `i`.
-/
def OwnBidIndependent [DecidableEq Agent]
    (threshold : (Agent → ℝ) → Agent → ℝ) : Prop :=
  ∀ (bids : Agent → ℝ) (i : Agent) (report : ℝ),
    threshold (Function.update bids i report) i = threshold bids i

/-- Bid profile with bidder `i`'s own bid erased to `0`. -/
def eraseOwnBid [DecidableEq Agent]
    (bids : Agent → ℝ) (i : Agent) : Agent → ℝ :=
  Function.update bids i 0

theorem eraseOwnBid_update_self [DecidableEq Agent]
    (bids : Agent → ℝ) (i : Agent) (report : ℝ) :
    eraseOwnBid (Function.update bids i report) i = eraseOwnBid bids i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [eraseOwnBid]
  · simp [eraseOwnBid, Function.update, h]

/--
Build a threshold rule from a pricing rule that only sees bidder `i`'s own bid
after it has been erased. This is the direct formal hook for random-sampling
and market-price auctions whose offer to `i` is computed from other bidders.
-/
def ownErasedThreshold [DecidableEq Agent]
    (priceRule : Agent → (Agent → ℝ) → ℝ) :
    (Agent → ℝ) → Agent → ℝ :=
  fun bids i => priceRule i (eraseOwnBid bids i)

theorem ownErasedThreshold_ownBidIndependent [DecidableEq Agent]
    (priceRule : Agent → (Agent → ℝ) → ℝ) :
    OwnBidIndependent (ownErasedThreshold priceRule) := by
  intro bids i report
  exact congrArg (priceRule i) (eraseOwnBid_update_self bids i report)

/-- Keep bids on one side of a sample partition and zero the rest. -/
def restrictBidsBySide (side : Agent → Bool) (keep : Bool)
    (bids : Agent → ℝ) : Agent → ℝ :=
  fun j => if side j = keep then bids j else 0

theorem restrictBidsBySide_update_of_not_kept [DecidableEq Agent]
    (side : Agent → Bool) (keep : Bool)
    (bids : Agent → ℝ) (i : Agent) (report : ℝ)
    (hkeep : side i ≠ keep) :
    restrictBidsBySide side keep (Function.update bids i report) =
      restrictBidsBySide side keep bids := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [restrictBidsBySide, hkeep]
  · simp [restrictBidsBySide, Function.update, hji]

/--
Finite-candidate cross-sample threshold rule: each bidder is offered the
candidate benchmark price computed from the opposite side of the partition.
-/
noncomputable def crossSampleCandidateThreshold
    [Fintype Agent] [Nonempty Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    (Agent → ℝ) → Agent → ℝ :=
  fun bids i =>
    finiteCandidateBenchmarkPrice
      (restrictBidsBySide side (!side i) bids) minWinners

theorem crossSampleCandidateThreshold_ownBidIndependent
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    OwnBidIndependent (crossSampleCandidateThreshold side minWinners) := by
  intro bids i report
  unfold crossSampleCandidateThreshold
  apply congrArg (fun profile =>
    finiteCandidateBenchmarkPrice profile minWinners)
  apply restrictBidsBySide_update_of_not_kept
  cases side i <;> simp

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

theorem ownErasedThresholdPriceAuction_truthful [DecidableEq Agent]
    (priceRule : Agent → (Agent → ℝ) → ℝ) :
    (thresholdPriceAuction
      (ownErasedThreshold priceRule)).TruthfulDominantStrategy := by
  exact thresholdPriceAuction_truthful _
    (ownErasedThreshold_ownBidIndependent priceRule)

theorem crossSampleCandidateThresholdPriceAuction_truthful
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (side : Agent → Bool) (minWinners : ℕ) :
    (thresholdPriceAuction
      (crossSampleCandidateThreshold side minWinners)).TruthfulDominantStrategy := by
  exact thresholdPriceAuction_truthful _
    (crossSampleCandidateThreshold_ownBidIndependent side minWinners)

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
