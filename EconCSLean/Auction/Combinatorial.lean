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

end Auction
end EconCSLean
