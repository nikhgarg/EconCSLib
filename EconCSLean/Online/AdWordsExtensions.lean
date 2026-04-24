import EconCSLean.Online.AdWords

/-!
# Paper Extensions for AdWords and Generalized Online Matching

The JACM paper explains that several realistic variants are handled by running
the same Balance/MSVV proof on suitable effective bids. This file records those
finite reductions without disturbing the core AdWords proof.
-/

namespace EconCSLean
namespace Online

namespace AdWordsInstance

variable {Advertiser Query Slot : Type*}

/--
Replace bids by an externally supplied effective charge/revenue function while
keeping advertiser budgets unchanged.
-/
def withEffectiveBids
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ) :
    AdWordsInstance Advertiser Query where
  budget := I.budget
  bid := effectiveBid

@[simp]
theorem withEffectiveBids_budget
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ) :
    (I.withEffectiveBids effectiveBid).budget = I.budget :=
  rfl

@[simp]
theorem withEffectiveBids_bid
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ) (a : Advertiser) (q : Query) :
    (I.withEffectiveBids effectiveBid).bid a q = effectiveBid a q :=
  rfl

theorem withEffectiveBids_positiveBudgets
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ)
    (hbudget : I.PositiveBudgets) :
    (I.withEffectiveBids effectiveBid).PositiveBudgets :=
  hbudget

theorem withEffectiveBids_nonnegativeBids
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ)
    (hbid : ∀ a q, 0 ≤ effectiveBid a q) :
    (I.withEffectiveBids effectiveBid).NonnegativeBids :=
  hbid

theorem withEffectiveBids_smallBids
    (I : AdWordsInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ) {ε : ℝ}
    (hsmall : ∀ a q, effectiveBid a q ≤ ε * I.budget a) :
    (I.withEffectiveBids effectiveBid).SmallBids ε :=
  hsmall

/--
Click-through-rate variant: the expected effective bid is actual bid times CTR.
-/
def withClickThroughRates
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) :
    AdWordsInstance Advertiser Query :=
  I.withEffectiveBids fun a q => ctr a q * I.bid a q

@[simp]
theorem withClickThroughRates_budget
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) :
    (I.withClickThroughRates ctr).budget = I.budget :=
  rfl

@[simp]
theorem withClickThroughRates_bid
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) (a : Advertiser) (q : Query) :
    (I.withClickThroughRates ctr).bid a q = ctr a q * I.bid a q :=
  rfl

theorem withClickThroughRates_nonnegativeBids
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ)
    (hctr : ∀ a q, 0 ≤ ctr a q)
    (hbid : I.NonnegativeBids) :
    (I.withClickThroughRates ctr).NonnegativeBids := by
  intro a q
  exact mul_nonneg (hctr a q) (hbid a q)

theorem withClickThroughRates_positiveBudgets
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ)
    (hbudget : I.PositiveBudgets) :
    (I.withClickThroughRates ctr).PositiveBudgets :=
  hbudget

theorem withClickThroughRates_smallBids_of_ctr_le_one
    (I : AdWordsInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) {ε : ℝ}
    (hctr_le_one : ∀ a q, ctr a q ≤ 1)
    (hbid : I.NonnegativeBids)
    (hsmall : I.SmallBids ε) :
    (I.withClickThroughRates ctr).SmallBids ε := by
  intro a q
  have hmul : ctr a q * I.bid a q ≤ 1 * I.bid a q :=
    mul_le_mul_of_nonneg_right (hctr_le_one a q) (hbid a q)
  calc
    (I.withClickThroughRates ctr).bid a q = ctr a q * I.bid a q := rfl
    _ ≤ 1 * I.bid a q := hmul
    _ = I.bid a q := by ring
    _ ≤ ε * I.budget a := hsmall a q

/--
Advertiser-availability variant: inactive advertisers have effective bid zero.
This models delayed entry, scheduled eligibility, or other exogenous activity
constraints expressible at the query level.
-/
def withAvailability
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)] :
    AdWordsInstance Advertiser Query :=
  I.withEffectiveBids fun a q => if active a q then I.bid a q else 0

@[simp]
theorem withAvailability_budget
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)] :
    (I.withAvailability active).budget = I.budget :=
  rfl

@[simp]
theorem withAvailability_bid
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)]
    (a : Advertiser) (q : Query) :
    (I.withAvailability active).bid a q =
      if active a q then I.bid a q else 0 :=
  rfl

theorem withAvailability_nonnegativeBids
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)]
    (hbid : I.NonnegativeBids) :
    (I.withAvailability active).NonnegativeBids := by
  intro a q
  by_cases hactive : active a q
  · simp [withAvailability, hactive, hbid a q]
  · simp [withAvailability, hactive]

theorem withAvailability_positiveBudgets
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)]
    (hbudget : I.PositiveBudgets) :
    (I.withAvailability active).PositiveBudgets :=
  hbudget

theorem withAvailability_smallBids
    (I : AdWordsInstance Advertiser Query)
    (active : Advertiser → Query → Prop)
    [∀ a q, Decidable (active a q)] {ε : ℝ}
    (hε : 0 ≤ ε)
    (hbudget : I.PositiveBudgets)
    (hsmall : I.SmallBids ε) :
    (I.withAvailability active).SmallBids ε := by
  intro a q
  by_cases hactive : active a q
  · simpa [withAvailability, hactive] using hsmall a q
  · have hnonneg : 0 ≤ ε * I.budget a :=
      mul_nonneg hε (le_of_lt (hbudget a))
    simpa [withAvailability, hactive] using hnonneg

/--
Multiple-slot expansion: a query with several ad slots is represented by one
ordinary AdWords query per slot. Slot-specific click-through or position effects
can be composed with `withEffectiveBids`.
-/
def withSlots
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*) :
    AdWordsInstance Advertiser (Σ q : Query, Slot q) where
  budget := I.budget
  bid := fun a qs => I.bid a qs.1

@[simp]
theorem withSlots_budget
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*) :
    (I.withSlots Slot).budget = I.budget :=
  rfl

@[simp]
theorem withSlots_bid
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*) (a : Advertiser) (qs : Σ q : Query, Slot q) :
    (I.withSlots Slot).bid a qs = I.bid a qs.1 :=
  rfl

theorem withSlots_nonnegativeBids
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*)
    (hbid : I.NonnegativeBids) :
    (I.withSlots Slot).NonnegativeBids := by
  intro a qs
  exact hbid a qs.1

theorem withSlots_positiveBudgets
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*)
    (hbudget : I.PositiveBudgets) :
    (I.withSlots Slot).PositiveBudgets :=
  hbudget

theorem withSlots_smallBids
    (I : AdWordsInstance Advertiser Query)
    (Slot : Query → Type*) {ε : ℝ}
    (hsmall : I.SmallBids ε) :
    (I.withSlots Slot).SmallBids ε := by
  intro a qs
  exact hsmall a qs.1

end AdWordsInstance

end Online
end EconCSLean
