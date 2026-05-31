import MSVV07AdWords.ProofInterface

/-!
# Paper Interface: MSVV07 AdWords

This file is the compact human-facing statement surface for Mehta, Saberi,
Vazirani, and Vazirani, *AdWords and Generalized Online Matching* (JACM 2007).

It exposes the paper model formulas and the closed paper-facing theorem
endpoints. The broader source-route LP and accounting audit ledger is retained
in `ProofInterface.lean` and `PostPaperAudit.lean`.
-/

open scoped BigOperators

namespace EconCSLib
namespace Online
namespace MSVV07PaperFacing

/-! ## Sections 2--3: finite AdWords model and Balance/MSVV rule -/

/-- Paper model: advertiser budgets and query bids. -/
abbrev PaperInstance (Advertiser Query : Type*) :=
  Proof.PaperInstance Advertiser Query

/-- Paper assignment: every query is assigned to one advertiser or left unmatched. -/
abbrev PaperAssignment (Advertiser Query : Type*) :=
  Proof.PaperAssignment Advertiser Query

/-- Paper multiple-slot distinctness: no advertiser appears twice on one page. -/
abbrev paperSlotsPerPageDistinct
    {Advertiser Query : Type*} (Slot : Query → Type*)
    (A : PaperAssignment Advertiser (Σ q : Query, Slot q)) : Prop :=
  Proof.paperSlotsPerPageDistinct Slot A

/-- Paper spend formula for advertiser `a` under assignment `A`. -/
noncomputable abbrev paperSpend
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) : ℝ :=
  Proof.paperSpend I A a

/-- Paper revenue formula for an assignment. -/
noncomputable abbrev paperRevenue
    {Advertiser Query : Type*} [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) : ℝ :=
  Proof.paperRevenue I A

/-- Paper budget feasibility: no advertiser spends more than her budget. -/
abbrev paperFeasible
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) : Prop :=
  Proof.paperFeasible I A

/-- Paper small-bids condition: every bid is at most an `epsilon` budget fraction. -/
abbrev paperSmallBids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) (epsilon : ℝ) : Prop :=
  Proof.paperSmallBids I epsilon

/-- Paper fractional LP value. -/
noncomputable abbrev paperFractionalRevenue
    {Advertiser Query : Type*} [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ) : ℝ :=
  Proof.paperFractionalRevenue I x

/-- Paper fractional LP feasibility. -/
abbrev PaperFractionalFeasible
    {Advertiser Query : Type*} [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ) : Prop :=
  Proof.PaperFractionalFeasible I x

/-- The paper's MSVV/Balance tradeoff function at spent fraction `s`. -/
noncomputable abbrev paperTradeoff (s : ℝ) : ℝ :=
  Proof.paperTradeoff s

/-- The paper's competitive ratio `1 - 1/e`. -/
noncomputable abbrev paperMsvvRatio : ℝ :=
  Proof.paperMsvvRatio

/-- Paper Balance/MSVV scaled bid. -/
noncomputable abbrev paperBalanceScore
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) (q : Query) : ℝ :=
  Proof.paperBalanceScore I A a q

/-- Paper feasibility for assigning query `q` next to advertiser `a`. -/
abbrev paperCanAssign
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  Proof.paperCanAssign I A q a

/--
Paper Balance/MSVV choice rule: assign the query to a feasible advertiser with
maximum scaled bid.
-/
abbrev paperIsBalanceChoice
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  Proof.paperIsBalanceChoice I A q a

/-! ## Section 5 / Theorem 8: Balance/MSVV is `1 - 1/e` competitive -/

/--
Paper-facing small-bids limiting family. The paper's limiting theorem is about
a sequence of finite instances whose bids become small relative to budgets.
-/
abbrev PaperSmallBidsLimitFamily
    (Advertiser : Type*) [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser] :=
  Proof.PaperSmallBidsLimitFamily Advertiser

/--
Theorem 8, finite explicit-error form. For a complete finite query history,
Balance/MSVV gets the `1 - 1/e` scaled offline optimum up to the explicit
small-bids error.
-/
theorem theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperMsvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      paperRevenue I (I.runAssignment I.balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, I.maxBidForQuery q) := by
  exact
    Proof.theorem8_finite_explicit_error
      I hbid hbudget history hnodup hcover hepsilon hepsilon_le_one hsmall

/--
Theorem 8, paper-level limiting endpoint. Any finite-query small-bids family
satisfying the explicit threshold eventually has limiting competitive ratio
`1 - 1/e`.
-/
theorem theorem8_balance_msvv_competitive_of_small_bids_limit_family
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (F : PaperSmallBidsLimitFamily Advertiser) :
    paperMsvvRatio * F.optLimit ≤ F.revenueLimit := by
  exact Proof.theorem8_balance_msvv_competitive_of_small_bids_limit_family F

/-! ## Section 6 and Section 8: model extensions by effective bids -/

/--
Section 6 items 1--2. Different advertiser budgets and nonexhaustive optima are
already part of the base AdWords model, so the finite explicit Theorem 8
guarantee applies without changing the instance.
-/
theorem section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperMsvvRatio *
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      paperRevenue I (I.runAssignment I.balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, I.maxBidForQuery q) := by
  exact
    Proof.section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error
      I hbid hbudget history hnodup hcover hepsilon hepsilon_le_one hsmall

/-- Section 6 next-price charge from all bidders, floored at zero. -/
noncomputable abbrev section6_next_highest_bid_all
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (a : Advertiser) (q : Query) : ℝ :=
  Proof.section6_next_highest_bid_all I a q

/-- Section 6 next-price charge among alive bidders, floored at zero. -/
noncomputable abbrev section6_next_highest_bid_alive
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (alive : Advertiser → Query → Prop) [∀ a q, Decidable (alive a q)]
    (a : Advertiser) (q : Query) : ℝ :=
  Proof.section6_next_highest_bid_alive I alive a q

/-- Section 6 effective-bid reduction: finite explicit Theorem 8 guarantee. -/
theorem section6_effective_bids_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ)
    (hbid : ∀ a q, 0 ≤ effectiveBid a q)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : ∀ a q, effectiveBid a q ≤ epsilon * I.budget a) :
    paperMsvvRatio *
        (I.withEffectiveBids effectiveBid).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      (I.withEffectiveBids effectiveBid).revenue
        ((I.withEffectiveBids effectiveBid).runAssignment
          (I.withEffectiveBids effectiveBid).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, (I.withEffectiveBids effectiveBid).maxBidForQuery q) := by
  exact
    Proof.section6_effective_bids_theorem8_finite_explicit_error
      I effectiveBid hbid hbudget history hnodup hcover
      hepsilon hepsilon_le_one hsmall

/-- Section 6 next-highest-bid charges, all-bidders variant. -/
theorem section6_next_highest_bid_all_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover :
      AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hnext_small :
      ∀ a q, section6_next_highest_bid_all I a q ≤ epsilon * I.budget a) :
    paperMsvvRatio *
        (I.withEffectiveBids (section6_next_highest_bid_all I)).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue (I.withEffectiveBids (section6_next_highest_bid_all I))
        ((I.withEffectiveBids (section6_next_highest_bid_all I)).runAssignment
          (I.withEffectiveBids
            (section6_next_highest_bid_all I)).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query,
            (I.withEffectiveBids
              (section6_next_highest_bid_all I)).maxBidForQuery q) := by
  exact
    Proof.section6_next_highest_bid_all_theorem8_finite_explicit_error
      I hbudget history hnodup hcover hepsilon hepsilon_le_one hnext_small

/-- Section 6 next-highest-bid charges, alive-bidders variant. -/
theorem section6_next_highest_bid_alive_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (alive : Advertiser → Query → Prop) [∀ a q, Decidable (alive a q)]
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover :
      AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hnext_small :
      ∀ a q, section6_next_highest_bid_alive I alive a q ≤
        epsilon * I.budget a) :
    paperMsvvRatio *
        (I.withEffectiveBids
          (section6_next_highest_bid_alive I alive)).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue
        (I.withEffectiveBids (section6_next_highest_bid_alive I alive))
        ((I.withEffectiveBids
          (section6_next_highest_bid_alive I alive)).runAssignment
          (I.withEffectiveBids
            (section6_next_highest_bid_alive I alive)).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query,
            (I.withEffectiveBids
              (section6_next_highest_bid_alive I alive)).maxBidForQuery q) := by
  exact
    Proof.section6_next_highest_bid_alive_theorem8_finite_explicit_error
      I alive hbudget history hnodup hcover hepsilon hepsilon_le_one hnext_small

/-- Section 6 click-through rates: finite explicit Theorem 8 guarantee. -/
theorem section6_click_through_rates_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ)
    (hctr_nonneg : ∀ a q, 0 ≤ ctr a q)
    (hctr_le_one : ∀ a q, ctr a q ≤ 1)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperMsvvRatio *
        (I.withClickThroughRates ctr).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      (I.withClickThroughRates ctr).revenue
        ((I.withClickThroughRates ctr).runAssignment
          (I.withClickThroughRates ctr).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, (I.withClickThroughRates ctr).maxBidForQuery q) := by
  exact
    Proof.section6_click_through_rates_theorem8_finite_explicit_error
      I ctr hctr_nonneg hctr_le_one hbid hbudget history hnodup hcover
      hepsilon hepsilon_le_one hsmall

/-- Section 6 delayed-entry availability: finite explicit Theorem 8 guarantee. -/
theorem section6_availability_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (available : Advertiser → Query → Prop)
    [∀ a q, Decidable (available a q)]
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperMsvvRatio *
        (I.withAvailability available).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      (I.withAvailability available).revenue
        ((I.withAvailability available).runAssignment
          (I.withAvailability available).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, (I.withAvailability available).maxBidForQuery q) := by
  exact
    Proof.section6_availability_theorem8_finite_explicit_error
      I available hbid hbudget history hnodup hcover hepsilon hepsilon_le_one hsmall

/-- Section 6 multiple slots: finite explicit Theorem 8 guarantee. -/
theorem section6_multiple_slots_theorem8_finite_explicit_error
    {Advertiser Query : Type*} {Slot : Query → Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype (Σ q : Query, Slot q)]
    [DecidableEq Advertiser] [DecidableEq (Σ q : Query, Slot q)]
    (I : PaperInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List (Σ q : Query, Slot q))
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperMsvvRatio *
        (I.withSlots Slot).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue (I.withSlots Slot)
        ((I.withSlots Slot).runAssignment
          (I.withSlots Slot).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Σ q : Query, Slot q, (I.withSlots Slot).maxBidForQuery q) := by
  exact
    Proof.section6_multiple_slots_theorem8_finite_explicit_error
      I hbid hbudget history hnodup hcover hepsilon hepsilon_le_one hsmall

/--
Section 6 multiple slots: source-shaped page-level finite explicit Theorem 8
guarantee. On each page `q`, Balance chooses the top `slots q` distinct feasible
advertisers by current scaled bid, and competes with the page-level offline
optimum subject to the same per-page cardinality and advertiser-budget
constraints.
-/
theorem section6_page_top_balance_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (slots : Query → ℕ)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperMsvvRatio *
        I.pageOfflineOptimumValue slots (fun a => (hbudget a).le) ≤
      I.pageRevenue
        (I.runPageAssignment slots (I.pageTopBalanceRule slots) history) +
        epsilon * (Real.exp 1 + 1) *
          I.pageHistoryMaxBidSum slots history := by
  exact
    Proof.section6_page_top_balance_theorem8_finite_explicit_error
      I slots hbid hbudget history hnodup hcover
      hepsilon hepsilon_le_one hsmall

/--
Section 6 multiple slots: the distinct-choice wrapper assigns any advertiser to
at most one slot of each original query during the slot-expanded online run.
-/
theorem section6_multiple_slots_distinct_choice_run_assignment_per_page_distinct
    {Advertiser Query : Type*} {Slot : Query → Type*}
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)]
    [DecidableEq Advertiser] [DecidableEq (Σ q : Query, Slot q)]
    (I : PaperInstance Advertiser Query)
    (history : List (Σ q : Query, Slot q)) :
    paperSlotsPerPageDistinct Slot
      ((I.withSlots Slot).runAssignment
        (AdWordsInstance.withSlotsDistinctChoice Slot
          (I.withSlots Slot).balanceChoiceRule)
        history) := by
  exact
    Proof.section6_multiple_slots_distinct_choice_run_per_page_distinct
      I (I.withSlots Slot).balanceChoiceRule history

/-- Section 8 advertiser weights: finite explicit Theorem 8 guarantee. -/
theorem section8_weighted_bids_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (weight : Advertiser → ℝ)
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (hweight_le_one : ∀ a, weight a ≤ 1)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperMsvvRatio *
        (I.withAdvertiserWeights weight).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      (I.withAdvertiserWeights weight).revenue
        ((I.withAdvertiserWeights weight).runAssignment
          (I.withAdvertiserWeights weight).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, (I.withAdvertiserWeights weight).maxBidForQuery q) := by
  exact
    Proof.section8_weighted_bids_theorem8_finite_explicit_error
      I weight hweight_nonneg hweight_le_one hbid hbudget history hnodup hcover
      hepsilon hepsilon_le_one hsmall

/--
Section 8 advertiser weights, stated directly for the weighted effective-bid
small-bids regime.
-/
theorem section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (weight : Advertiser → ℝ)
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hweighted_small :
      ∀ a q, weight a * I.bid a q ≤ epsilon * I.budget a) :
    paperMsvvRatio *
        (I.withAdvertiserWeights weight).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      (I.withAdvertiserWeights weight).revenue
        ((I.withAdvertiserWeights weight).runAssignment
          (I.withAdvertiserWeights weight).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, (I.withAdvertiserWeights weight).maxBidForQuery q) := by
  exact
    Proof.section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids
      I weight hweight_nonneg hbid hbudget history hnodup hcover
      hepsilon hepsilon_le_one hweighted_small

/-! ## Section 7 / Theorem 9: lower bound -/

/-- The hard distribution in Theorem 9 is uniform over bidder permutations. -/
noncomputable abbrev theorem9HardDistribution (N : ℕ) :
    PMF (Equiv.Perm (Fin N)) :=
  Proof.theorem9HardDistribution N

/--
Deterministic online integral prefix algorithms used as the concrete Theorem 9
algorithm model.
-/
abbrev theorem9IntegralPrefixAlgorithm (N : ℕ) :=
  Proof.theorem9IntegralPrefixAlgorithm N

/--
Randomized online integral prefix algorithms: distributions over deterministic
prefix algorithms.
-/
abbrev theorem9RandomizedOnlineAlgorithm (N : ℕ) :=
  Proof.theorem9RandomizedOnlineAlgorithm N

/--
The broader finite online-information model for Theorem 9: feasible allocation
rules that depend only on the observed prefix of the permutation instance.
-/
abbrev theorem9FeasiblePrefixRuleFamily
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] :=
  Proof.theorem9FeasiblePrefixRuleFamily Algorithm

/-- The capped normalized revenue expression used in the Section 7 proof. -/
noncomputable abbrev theorem9CappedNormalizedRevenue
    (N : ℕ) (algorithm : theorem9IntegralPrefixAlgorithm N)
    (permutation : Equiv.Perm (Fin N)) : ℝ :=
  Proof.theorem9CappedNormalizedRevenue N algorithm permutation

/--
The canonical payoff for integral prefix algorithms is definitionally the
paper's capped normalized spend.
-/
theorem theorem9_capped_normalized_revenue_eq_prefix_spend
    (N : ℕ) (algorithm : theorem9IntegralPrefixAlgorithm N)
    (permutation : Equiv.Perm (Fin N)) :
    theorem9CappedNormalizedRevenue N algorithm permutation =
      (∑ bidder : Fin N,
        min 1
          (∑ round : Fin N,
            BMatchingIntegralPrefixAlgorithm.prefixAllocation algorithm
              (theorem9ObservedPrefix N permutation round)
              round (permutation bidder))) /
        (N : ℝ) := by
  exact
    Proof.theorem9_capped_normalized_revenue_eq_prefix_spend
      N algorithm permutation

/--
Theorem 9, broad observed-prefix lower-bound endpoint. No randomized
distribution over any finite family of feasible observed-prefix allocation rules
can beat the MSVV ratio on every sufficiently large hard instance.
-/
theorem theorem9_no_randomized_feasible_prefix_rule_family_beats_msvv_ratio
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : theorem9FeasiblePrefixRuleFamily Algorithm) :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            paperMsvvRatio + delta <
              EconCSLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  C.normalizedRevenue N algorithm permutation) := by
  exact
    Proof.theorem9_no_randomized_feasible_prefix_rule_family_beats_msvv_ratio C

/--
Theorem 9, lower-bound endpoint for randomized distributions over deterministic
integral prefix algorithms.
-/
theorem theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (theorem9IntegralPrefixAlgorithm N),
          ¬ ∀ permutation,
            paperMsvvRatio + delta <
              EconCSLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  theorem9CappedNormalizedRevenue N algorithm permutation) := by
  exact Proof.theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio

/--
Theorem 9, paper-facing randomized online algorithm endpoint in the finite
prefix model.
-/
theorem theorem9_no_randomized_online_algorithm_beats_msvv_ratio :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : theorem9RandomizedOnlineAlgorithm N,
          ¬ ∀ permutation,
            paperMsvvRatio + delta <
              EconCSLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  theorem9CappedNormalizedRevenue N algorithm permutation) := by
  exact Proof.theorem9_no_randomized_online_algorithm_beats_msvv_ratio

end MSVV07PaperFacing
end Online
end EconCSLib
