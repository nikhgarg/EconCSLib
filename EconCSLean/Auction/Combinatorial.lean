import EconCSLean.FairDivision.IndivisibleGoods
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace EconCSLean
namespace Auction

/-- Bundles in combinatorial auctions reuse the fair-division bundle model. -/
abbrev Bundle (Item : Type*) := FairDivision.Bundle Item

/-- Bundle allocations reuse the fair-division allocation model. -/
abbrev BundleAllocation (Bidder Item : Type*) :=
  FairDivision.Allocation Bidder Item

/-- A direct combinatorial-auction report is a value for every bundle. -/
abbrev CombinatorialReport (Bidder Item : Type*) :=
  Bidder → Bundle Item → ℝ

/--
A direct-revelation combinatorial auction over indivisible goods.

The allocation is intentionally allowed to leave goods unallocated; feasibility
is a separate predicate because approximation algorithms often reason about
partial allocations.
-/
structure CombinatorialAuction (Bidder Item : Type*) where
  allocation : CombinatorialReport Bidder Item → BundleAllocation Bidder Item
  payment : CombinatorialReport Bidder Item → Bidder → ℝ

namespace CombinatorialAuction

variable {Bidder Item : Type*}

/-- Quasilinear utility for a combinatorial-auction bidder. -/
def utility (M : CombinatorialAuction Bidder Item)
    (values reports : CombinatorialReport Bidder Item) (i : Bidder) : ℝ :=
  values i (M.allocation reports i) - M.payment reports i

/-- Dominant-strategy truthfulness for direct bundle-value reports. -/
def TruthfulDominantStrategy [DecidableEq Bidder]
    (M : CombinatorialAuction Bidder Item) : Prop :=
  ∀ (values : CombinatorialReport Bidder Item)
      (i : Bidder) (report : Bundle Item → ℝ),
    M.utility values (Function.update values i report) i ≤
      M.utility values values i

/-- Truthfulness restricted to an admissible class of valuation profiles. -/
def TruthfulDominantStrategyOn [DecidableEq Bidder]
    (M : CombinatorialAuction Bidder Item)
    (admissible : CombinatorialReport Bidder Item → Prop) : Prop :=
  ∀ (values : CombinatorialReport Bidder Item),
    admissible values →
      ∀ (i : Bidder) (report : Bundle Item → ℝ),
        M.utility values (Function.update values i report) i ≤
          M.utility values values i

/-- Bundle valuations normalized to give the empty bundle value zero. -/
def Normalized (values : CombinatorialReport Bidder Item) : Prop :=
  ∀ i, values i ∅ = 0

/-- Truthful utility is always nonnegative. -/
def IndividuallyRational (M : CombinatorialAuction Bidder Item) : Prop :=
  ∀ (values : CombinatorialReport Bidder Item) (i : Bidder),
    0 ≤ M.utility values values i

/-- The mechanism never pays money to bidders. -/
def NoPositiveTransfers (M : CombinatorialAuction Bidder Item) : Prop :=
  ∀ (reports : CombinatorialReport Bidder Item) (i : Bidder),
    0 ≤ M.payment reports i

/-- Total payments collected by the auction. -/
noncomputable def revenue [Fintype Bidder]
    (M : CombinatorialAuction Bidder Item)
    (reports : CombinatorialReport Bidder Item) : ℝ :=
  ∑ i : Bidder, M.payment reports i

end CombinatorialAuction

variable {Bidder Item : Type*}

/--
Feasible partial allocation of a finite good set: every allocated good belongs
to `goods`, and no good is assigned to two different bidders.
-/
def IsFeasibleBundleAllocation [DecidableEq Item]
    (A : BundleAllocation Bidder Item) (goods : Finset Item) : Prop :=
  (∀ i g, g ∈ A i → g ∈ goods) ∧
    ∀ ⦃i j : Bidder⦄ ⦃g : Item⦄,
      i ≠ j → g ∈ A i → g ∈ A j → False

theorem feasible_emptyAllocation [DecidableEq Item] (goods : Finset Item) :
    IsFeasibleBundleAllocation
      (FairDivision.emptyAllocation Bidder Item) goods := by
  constructor
  · intro i g hmem
    simp [FairDivision.emptyAllocation] at hmem
  · intro i j g hij hgi hgj
    simp [FairDivision.emptyAllocation] at hgi

theorem feasible_of_isAllocationOf [DecidableEq Item]
    (A : BundleAllocation Bidder Item) (goods : Finset Item)
    (halloc : FairDivision.IsAllocationOf A goods) :
    IsFeasibleBundleAllocation A goods := by
  constructor
  · exact halloc.1
  · intro i j g hij hgi hgj
    obtain ⟨owner, howner, huniq⟩ := halloc.2 g (halloc.1 i g hgi)
    have hi : i = owner := huniq i hgi
    have hj : j = owner := huniq j hgj
    exact hij (hi.trans hj.symm)

/-- Social welfare of an allocation under reported bundle values. -/
noncomputable def allocationValue [Fintype Bidder]
    (values : CombinatorialReport Bidder Item)
    (A : BundleAllocation Bidder Item) : ℝ :=
  ∑ i : Bidder, values i (A i)

theorem allocationValue_nonneg [Fintype Bidder]
    (values : CombinatorialReport Bidder Item)
    (A : BundleAllocation Bidder Item)
    (hvalue : ∀ i, 0 ≤ values i (A i)) :
    0 ≤ allocationValue values A := by
  classical
  exact Finset.sum_nonneg fun i _ => hvalue i

/--
Reject-all combinatorial auction. It is a useful baseline and a sanity check for
the direct-revelation interface: reports cannot affect anyone's allocation or
payment.
-/
def rejectAllAuction : CombinatorialAuction Bidder Item where
  allocation _ := FairDivision.emptyAllocation Bidder Item
  payment _ _ := 0

theorem rejectAllAuction_truthful [DecidableEq Bidder] :
    (rejectAllAuction : CombinatorialAuction Bidder Item).TruthfulDominantStrategy := by
  intro values i report
  simp [CombinatorialAuction.utility, rejectAllAuction]

theorem rejectAllAuction_noPositiveTransfers :
    (rejectAllAuction : CombinatorialAuction Bidder Item).NoPositiveTransfers := by
  intro reports i
  simp [rejectAllAuction]

/-! ## Critical-price target-bundle mechanisms -/

/--
A bundle price rule is own-report independent when changing bidder `i`'s report
does not change the price offered to bidder `i`.
-/
def BundlePriceOwnReportIndependent [DecidableEq Bidder]
    (price : CombinatorialReport Bidder Item → Bidder → ℝ) : Prop :=
  ∀ (reports : CombinatorialReport Bidder Item)
      (i : Bidder) (report : Bundle Item → ℝ),
    price (Function.update reports i report) i = price reports i

/--
Target-bundle threshold auction: bidder `i` either receives `target i` at the
offered price, or receives the empty bundle and pays zero.
-/
noncomputable def targetBundleThresholdAuction
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ) :
    CombinatorialAuction Bidder Item where
  allocation reports i :=
    if price reports i ≤ reports i (target i) then target i else ∅
  payment reports i :=
    if price reports i ≤ reports i (target i) then price reports i else 0

theorem targetBundleThresholdAuction_utility_eq
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (values reports : CombinatorialReport Bidder Item) (i : Bidder) :
    (targetBundleThresholdAuction target price).utility values reports i =
      if price reports i ≤ reports i (target i) then
        values i (target i) - price reports i
      else
        values i ∅ := by
  by_cases h : price reports i ≤ reports i (target i) <;>
    simp [CombinatorialAuction.utility, targetBundleThresholdAuction, h]

/--
Critical-price truthfulness for target-bundle mechanisms on normalized
valuations. This is the reusable theorem shape for single-minded combinatorial
auction critical-value payments.
-/
theorem targetBundleThresholdAuction_truthfulOn_normalized [DecidableEq Bidder]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind : BundlePriceOwnReportIndependent price) :
    (targetBundleThresholdAuction target price).TruthfulDominantStrategyOn
      CombinatorialAuction.Normalized := by
  intro values hnorm i report
  have htruthUtility :
      (targetBundleThresholdAuction target price).utility values values i =
        if price values i ≤ values i (target i) then
          values i (target i) - price values i
        else 0 := by
    rw [targetBundleThresholdAuction_utility_eq]
    simp [hnorm i]
  have hreportUtility :
      (targetBundleThresholdAuction target price).utility values
          (Function.update values i report) i =
        if price values i ≤ report (target i) then
          values i (target i) - price values i
        else 0 := by
    rw [targetBundleThresholdAuction_utility_eq]
    simp [Function.update, hind values i report, hnorm i]
  rw [htruthUtility, hreportUtility]
  by_cases htruth : price values i ≤ values i (target i)
  · by_cases hreport : price values i ≤ report (target i)
    · simp [htruth, hreport]
    · simp [htruth, hreport]
  · by_cases hreport : price values i ≤ report (target i)
    · simpa only [htruth, hreport, ↓reduceIte, ge_iff_le]
        using sub_nonpos.mpr (le_of_lt (lt_of_not_ge htruth))
    · simp [htruth, hreport]

/--
Single-minded bundle value: the bidder has value `value` exactly when the
allocated bundle contains the desired bundle.
-/
structure SingleMindedBid (Item : Type*) where
  desired : Bundle Item
  value : ℝ

namespace SingleMindedBid

variable [DecidableEq Item]

/-- Bundle valuation induced by a single-minded bid. -/
def valuation (b : SingleMindedBid Item) : Bundle Item → ℝ :=
  fun S => if b.desired ⊆ S then b.value else 0

theorem valuation_of_contains (b : SingleMindedBid Item) {S : Bundle Item}
    (h : b.desired ⊆ S) :
    b.valuation S = b.value := by
  simp [valuation, h]

theorem valuation_of_not_contains (b : SingleMindedBid Item) {S : Bundle Item}
    (h : ¬ b.desired ⊆ S) :
    b.valuation S = 0 := by
  simp [valuation, h]

theorem valuation_empty_eq_zero_of_nonempty
    (b : SingleMindedBid Item) (hb : b.desired.Nonempty) :
    b.valuation ∅ = 0 := by
  have hnot : ¬ b.desired ⊆ (∅ : Bundle Item) := by
    intro hsub
    rcases hb with ⟨g, hg⟩
    have hempty : g ∈ (∅ : Bundle Item) := hsub hg
    simp at hempty
  exact valuation_of_not_contains b hnot

end SingleMindedBid

/-- Profile of bundle valuations induced by single-minded bids. -/
def singleMindedValuationProfile [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) :
    CombinatorialReport Bidder Item :=
  fun i => (bids i).valuation

theorem singleMindedValuationProfile_empty_eq_zero_of_nonempty
    [DecidableEq Item] (bids : Bidder → SingleMindedBid Item)
    (hb : ∀ i, (bids i).desired.Nonempty) (i : Bidder) :
    singleMindedValuationProfile bids i ∅ = 0 := by
  exact SingleMindedBid.valuation_empty_eq_zero_of_nonempty (bids i) (hb i)

theorem singleMindedValuationProfile_normalized_of_nonempty
    [DecidableEq Item] (bids : Bidder → SingleMindedBid Item)
    (hb : ∀ i, (bids i).desired.Nonempty) :
    CombinatorialAuction.Normalized
      (singleMindedValuationProfile bids) := by
  intro i
  exact singleMindedValuationProfile_empty_eq_zero_of_nonempty bids hb i

/--
Single-minded valuation profiles with nonempty desired bundles form an
admissible class for normalized-profile critical-price truthfulness.
-/
def IsNonemptySingleMindedProfile [DecidableEq Item]
    (values : CombinatorialReport Bidder Item) : Prop :=
  ∃ bids : Bidder → SingleMindedBid Item,
    (∀ i, (bids i).desired.Nonempty) ∧
      values = singleMindedValuationProfile bids

theorem targetBundleThresholdAuction_truthfulOn_singleMindedProfiles
    [DecidableEq Bidder] [DecidableEq Item]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (hind : BundlePriceOwnReportIndependent price) :
    (targetBundleThresholdAuction target price).TruthfulDominantStrategyOn
      IsNonemptySingleMindedProfile := by
  intro values hvalues i report
  rcases hvalues with ⟨bids, hb, rfl⟩
  exact targetBundleThresholdAuction_truthfulOn_normalized target price hind
    (singleMindedValuationProfile bids)
    (singleMindedValuationProfile_normalized_of_nonempty bids hb)
    i report

/-! ## Feasible allocations for accepted single-minded bidders -/

/-- Accepted single-minded bidders receive their desired bundles; others receive nothing. -/
def singleMindedAllocation [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) (accepted : Finset Bidder) :
    BundleAllocation Bidder Item :=
  fun i => if i ∈ accepted then (bids i).desired else ∅

/-- Accepted desired bundles are pairwise disjoint. -/
def PairwiseDisjointDesired [DecidableEq Bidder]
    [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (accepted : Finset Bidder) : Prop :=
  ∀ ⦃i j : Bidder⦄,
    i ∈ accepted → j ∈ accepted → i ≠ j →
      Disjoint (bids i).desired (bids j).desired

theorem singleMindedAllocation_feasible [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item)
    (accepted : Finset Bidder) (goods : Finset Item)
    (hgoods : ∀ i, i ∈ accepted → (bids i).desired ⊆ goods)
    (hdisjoint : PairwiseDisjointDesired bids accepted) :
    IsFeasibleBundleAllocation
      (singleMindedAllocation bids accepted) goods := by
  constructor
  · intro i g hg
    by_cases hi : i ∈ accepted
    · have hgdesired : g ∈ (bids i).desired := by
        simpa [singleMindedAllocation, hi] using hg
      exact hgoods i hi hgdesired
    · simp [singleMindedAllocation, hi] at hg
  · intro i j g hij hgi hgj
    by_cases hi : i ∈ accepted
    · by_cases hj : j ∈ accepted
      · have hgiDesired : g ∈ (bids i).desired := by
          simpa [singleMindedAllocation, hi] using hgi
        have hgjDesired : g ∈ (bids j).desired := by
          simpa [singleMindedAllocation, hj] using hgj
        exact (Finset.disjoint_left.mp (hdisjoint hi hj hij))
          hgiDesired hgjDesired
      · simp [singleMindedAllocation, hj] at hgj
    · simp [singleMindedAllocation, hi] at hgi

/-! ## Feasibility of target-bundle threshold outcomes -/

/-- Winners of a target-bundle threshold auction under a report profile. -/
noncomputable def targetBundleWinners [Fintype Bidder]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (reports : CombinatorialReport Bidder Item) : Finset Bidder :=
  (Finset.univ : Finset Bidder).filter fun i =>
    price reports i ≤ reports i (target i)

/--
View a target-bundle threshold report profile as a single-minded bid profile
whose desired bundle is the mechanism target and whose value is the reported
value for that target.
-/
def targetAsSingleMindedBids
    (target : Bidder → Bundle Item)
    (reports : CombinatorialReport Bidder Item) :
    Bidder → SingleMindedBid Item :=
  fun i => { desired := target i, value := reports i (target i) }

theorem targetBundleThresholdAuction_allocation_eq_singleMindedAllocation
    [Fintype Bidder] [DecidableEq Bidder]
    (target : Bidder → Bundle Item)
    (price : CombinatorialReport Bidder Item → Bidder → ℝ)
    (reports : CombinatorialReport Bidder Item) :
    (targetBundleThresholdAuction target price).allocation reports =
      singleMindedAllocation
        (targetAsSingleMindedBids target reports)
        (targetBundleWinners target price reports) := by
  funext i
  by_cases hwin : price reports i ≤ reports i (target i)
  · simp [targetBundleThresholdAuction, singleMindedAllocation,
      targetBundleWinners, targetAsSingleMindedBids, hwin]
  · simp [targetBundleThresholdAuction, singleMindedAllocation,
      targetBundleWinners, hwin]

theorem targetBundleThresholdAuction_feasible_of_pairwiseDisjoint
    [Fintype Bidder] [DecidableEq Bidder] [DecidableEq Item]
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
  rw [targetBundleThresholdAuction_allocation_eq_singleMindedAllocation]
  exact singleMindedAllocation_feasible
    (targetAsSingleMindedBids target reports)
    (targetBundleWinners target price reports)
    goods
    (by
      intro i hi
      exact hgoods i hi)
    hdisjoint

end Auction
end EconCSLean
