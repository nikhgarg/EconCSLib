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
Section 8 weighted-bid variant: advertiser weights scale all bids from the
same advertiser.
-/
def withAdvertiserWeights
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ) :
    AdWordsInstance Advertiser Query :=
  I.withEffectiveBids fun a q => weight a * I.bid a q

@[simp]
theorem withAdvertiserWeights_budget
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ) :
    (I.withAdvertiserWeights weight).budget = I.budget :=
  rfl

@[simp]
theorem withAdvertiserWeights_bid
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ) (a : Advertiser) (q : Query) :
    (I.withAdvertiserWeights weight).bid a q = weight a * I.bid a q :=
  rfl

theorem withAdvertiserWeights_nonnegativeBids
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ)
    (hweight : ∀ a, 0 ≤ weight a)
    (hbid : I.NonnegativeBids) :
    (I.withAdvertiserWeights weight).NonnegativeBids := by
  intro a q
  exact mul_nonneg (hweight a) (hbid a q)

theorem withAdvertiserWeights_positiveBudgets
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ)
    (hbudget : I.PositiveBudgets) :
    (I.withAdvertiserWeights weight).PositiveBudgets :=
  hbudget

theorem withAdvertiserWeights_smallBids_of_weight_le_one
    (I : AdWordsInstance Advertiser Query)
    (weight : Advertiser → ℝ) {ε : ℝ}
    (hweight_le_one : ∀ a, weight a ≤ 1)
    (hbid : I.NonnegativeBids)
    (hsmall : I.SmallBids ε) :
    (I.withAdvertiserWeights weight).SmallBids ε := by
  intro a q
  have hmul : weight a * I.bid a q ≤ 1 * I.bid a q :=
    mul_le_mul_of_nonneg_right (hweight_le_one a) (hbid a q)
  calc
    (I.withAdvertiserWeights weight).bid a q = weight a * I.bid a q := rfl
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

/-- Distinct-advertiser condition for slot-expanded queries. -/
def withSlotsPerPageDistinct
    (Slot : Query → Type*) (A : Assignment Advertiser (Σ q : Query, Slot q)) : Prop :=
  ∀ q s₁ s₂ a,
    A ⟨q, s₁⟩ = some a →
    A ⟨q, s₂⟩ = some a →
    s₁ = s₂

theorem withSlotsPerPageDistinct_empty :
    (Slot : Query → Type*) →
    withSlotsPerPageDistinct
      Slot
      (emptyAssignment : Assignment Advertiser (Σ q : Query, Slot q)) := by
  intro Slot q s₁ s₂ a h1 h2
  simpa [emptyAssignment] using h1

/--
Choice rule wrapper for slot-expanded queries that forbids assigning the same
advertiser twice to different slots of the same original query.
-/
noncomputable def withSlotsDistinctChoice
    (Slot : Query → Type*) (rule : ChoiceRule Advertiser (Σ q : Query, Slot q))
    (A : Assignment Advertiser (Σ q : Query, Slot q)) :
    (Σ q : Query, Slot q) → Option Advertiser :=
  by
    classical
    intro qs
    exact
    match rule A qs with
    | none => none
    | some a =>
      if hrepeat : ∃ s : Slot qs.1, A ⟨qs.1, s⟩ = some a then
        none
      else
        some a

theorem withSlotsDistinctChoice_rejects_used_advertiser
    (Slot : Query → Type*) (rule : ChoiceRule Advertiser (Σ q : Query, Slot q))
    (A : Assignment Advertiser (Σ q : Query, Slot q))
    (qs : Σ q : Query, Slot q) (a : Advertiser)
    (hchoice : withSlotsDistinctChoice Slot rule A qs = some a) :
    ¬ ∃ s : Slot qs.1, A ⟨qs.1, s⟩ = some a := by
  classical
  unfold withSlotsDistinctChoice at hchoice
  cases h : rule A qs with
  | none =>
      simp [h] at hchoice
  | some a' =>
    by_cases hrepeat : ∃ s : Slot qs.1, A ⟨qs.1, s⟩ = some a'
    · simp [h, hrepeat] at hchoice
    · have hEq' : some a' = some a := by
        simpa [h, hrepeat] using hchoice
      have hEq : a' = a := by simpa using hEq'
      intro hUsed
      exact hrepeat <| by simpa [hEq] using hUsed

theorem withSlotsDistinctChoice_allows_if_unused
    (Slot : Query → Type*) (rule : ChoiceRule Advertiser (Σ q : Query, Slot q))
    (A : Assignment Advertiser (Σ q : Query, Slot q))
    (qs : Σ q : Query, Slot q) (a : Advertiser)
    (hfree : ¬ ∃ s : Slot qs.1, A ⟨qs.1, s⟩ = some a)
    (hrule : rule A qs = some a) :
    withSlotsDistinctChoice Slot rule A qs = some a := by
  classical
  unfold withSlotsDistinctChoice
  rw [hrule]
  have hrepeat : ¬ ∃ s : Slot qs.1, A ⟨qs.1, s⟩ = some a := hfree
  simp [hrepeat]

end AdWordsInstance

end Online
end EconCSLean
