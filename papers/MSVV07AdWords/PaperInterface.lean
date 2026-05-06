import MSVV07AdWords.MainTheorems

/-!
# Paper Interface: MSVV07 AdWords

This file is the single Lean file intended for human audit of the formalized
surface of Mehta, Saberi, Vazirani, and Vazirani, *AdWords and Generalized
Online Matching* (JACM 2007).

The declarations below deliberately expose the paper-facing formulas for the
finite AdWords model, Balance/MSVV rule, small-bids limit, and Section 7
b-matching lower bound. The proofs are thin wrappers around the detailed
formalization in `MainTheorems.lean`, `AdWords.lean`, `AdWordsExtensions.lean`,
and `AdWordsLowerBound.lean`.
-/

open scoped BigOperators

namespace EconCSLib
namespace Online
namespace MSVV07PaperFacing

/-! ## Sections 2--3: finite AdWords model and Balance/MSVV rule -/

/--
Paper model. An AdWords instance consists of advertiser budgets `budget a` and
query bids `bid a q`, where assigning query `q` to advertiser `a` earns
`bid a q` and charges the same amount to `a`.
-/
abbrev PaperInstance (Advertiser Query : Type*) :=
  AdWordsInstance Advertiser Query

/-- Paper assignment: every query is assigned to one advertiser or left unmatched. -/
abbrev PaperAssignment (Advertiser Query : Type*) :=
  Query → Option Advertiser

/-- Paper spend formula for advertiser `a` under assignment `A`. -/
noncomputable abbrev paperSpend
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) : ℝ :=
  ∑ q : Query,
    match A q with
    | none => 0
    | some a' => if a' = a then I.bid a q else 0

/-- Paper revenue formula for an assignment. -/
noncomputable abbrev paperRevenue
    {Advertiser Query : Type*} [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) : ℝ :=
  ∑ q : Query,
    match A q with
    | none => 0
    | some a => I.bid a q

/-- Paper budget feasibility: no advertiser spends more than her budget. -/
abbrev paperFeasible
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) : Prop :=
  ∀ a, paperSpend I A a ≤ I.budget a

/-- Paper small-bids condition: every bid is at most an `epsilon` budget fraction. -/
abbrev paperSmallBids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) (epsilon : ℝ) : Prop :=
  ∀ a q, I.bid a q ≤ epsilon * I.budget a

/--
Paper fractional LP value: the relaxed assignment variable `x a q` contributes
`bid a q * x a q`.
-/
noncomputable abbrev paperFractionalRevenue
    {Advertiser Query : Type*} [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ) : ℝ :=
  ∑ q : Query, ∑ a : Advertiser, I.bid a q * x a q

/--
Paper fractional LP feasibility: nonnegative assignment, at most one unit per
query, and budget feasibility for every advertiser.
-/
structure PaperFractionalFeasible
    {Advertiser Query : Type*} [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ) : Prop where
  nonneg : ∀ a q, 0 ≤ x a q
  query : ∀ q, (∑ a : Advertiser, x a q) ≤ 1
  budget : ∀ a, (∑ q : Query, I.bid a q * x a q) ≤ I.budget a

/-- The paper's MSVV/Balance tradeoff function at spent fraction `s`. -/
noncomputable abbrev paperTradeoff (s : ℝ) : ℝ :=
  1 - Real.exp (s - 1)

/-- The paper's competitive ratio `1 - 1/e`. -/
noncomputable abbrev paperMsvvRatio : ℝ :=
  1 - 1 / Real.exp 1

/-- Paper Balance/MSVV scaled bid. -/
noncomputable abbrev paperBalanceScore
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) (q : Query) : ℝ :=
  I.bid a q * paperTradeoff (paperSpend I A a / I.budget a)

/-- Paper feasibility for assigning query `q` next to advertiser `a`. -/
abbrev paperCanAssign
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  paperSpend I A a + I.bid a q ≤ I.budget a

/--
Paper Balance/MSVV choice rule: assign the query to a feasible advertiser with
maximum scaled bid.
-/
abbrev paperIsBalanceChoice
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  paperCanAssign I A q a ∧
    ∀ b, paperCanAssign I A q b →
      paperBalanceScore I A b q ≤ paperBalanceScore I A a q

theorem paperSpend_eq_library
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) :
    paperSpend I A a = I.spend A a := by
  rfl

theorem paperRevenue_eq_library
    {Advertiser Query : Type*} [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) :
    paperRevenue I A = I.revenue A := by
  rfl

theorem paperFeasible_eq_library
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) :
    paperFeasible I A = I.Feasible A := by
  rfl

theorem paperSmallBids_eq_library
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) (epsilon : ℝ) :
    paperSmallBids I epsilon = I.SmallBids epsilon := by
  rfl

theorem paperFractionalRevenue_eq_library
    {Advertiser Query : Type*} [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ) :
    paperFractionalRevenue I x = I.fractionalRevenue x := by
  rfl

theorem paperTradeoff_eq_library (s : ℝ) :
    paperTradeoff s = AdWordsInstance.balanceDiscount s := by
  rfl

theorem paperMsvvRatio_eq_library :
    paperMsvvRatio = AdWordsInstance.msvvRatio := by
  rfl

theorem paperBalanceScore_eq_library
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) (q : Query) :
    paperBalanceScore I A a q = I.balanceScore A a q := by
  rfl

theorem paperCanAssign_eq_library
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) :
    paperCanAssign I A q a = I.CanAssign A q a := by
  rfl

theorem paperIsBalanceChoice_eq_library
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) :
    paperIsBalanceChoice I A q a = I.IsBalanceChoice A q a := by
  rfl

/-! ## Core LP and online-run support used by the paper proof -/

/-- Empty assignments are feasible under nonnegative budgets. -/
theorem section2_empty_assignment_feasible
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbudget : ∀ a, 0 ≤ I.budget a) :
    paperFeasible I
      (AdWordsInstance.emptyAssignment :
        PaperAssignment Advertiser Query) := by
  simpa [paperFeasible_eq_library] using
    paper_adwords_empty_assignment_feasible I hbudget

/-- Finite instances have an offline optimum assignment. -/
theorem section2_offline_optimum_exists
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbudget : ∀ a, 0 ≤ I.budget a) :
    ∃ A : PaperAssignment Advertiser Query,
      I.IsOptimalAssignment A := by
  exact paper_adwords_offline_optimum_exists I hbudget

/-- Paper LP weak duality for the fractional AdWords relaxation. -/
theorem section2_fractional_lp_weak_duality
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hfeasible : I.FractionalFeasible x)
    (hdual : I.DualFeasible alpha beta) :
    paperFractionalRevenue I x ≤ I.dualObjective alpha beta := by
  simpa [paperFractionalRevenue_eq_library] using
    paper_adwords_fractional_lp_weak_duality I x alpha beta hfeasible hdual

/-- A Balance/MSVV maximizer exists whenever some advertiser can accept the query. -/
theorem section3_balance_choice_exists
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query)
    (h : ∃ a, paperCanAssign I A q a) :
    ∃ a, paperIsBalanceChoice I A q a := by
  simpa [paperCanAssign_eq_library, paperIsBalanceChoice_eq_library] using
    paper_adwords_balance_choice_exists I A q h

/-- The canonical Balance/MSVV online run is budget-feasible. -/
theorem section3_balance_run_assignment_feasible
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (hbudget : ∀ a, 0 ≤ I.budget a)
    (history : List Query) :
    paperFeasible I (I.runAssignment I.balanceChoiceRule history) := by
  simpa [paperFeasible_eq_library] using
    paper_adwords_balance_run_assignment_feasible I hbudget history

/-! ## Section 5 / Theorem 8: Balance/MSVV is `1 - 1/e` competitive -/

/--
Paper-facing small-bids limiting family. The paper's limiting theorem is about
a sequence of finite instances whose bids become small relative to budgets;
these fields spell out that limiting model.
-/
structure PaperSmallBidsLimitFamily
    (Advertiser : Type*) [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser] where
  queryCount : ℕ → ℕ
  instanceAt : (k : ℕ) → PaperInstance Advertiser (Fin (queryCount k))
  optLimit : ℝ
  revenueLimit : ℝ
  nonnegative_bids : ∀ k, (instanceAt k).NonnegativeBids
  positive_budgets : ∀ k, (instanceAt k).PositiveBudgets
  maxBidSum_pos :
    ∀ k, 0 < ∑ q : Fin (queryCount k), (instanceAt k).maxBidForQuery q
  small_bids_eventually :
    ∀ delta : ℝ, 0 < delta →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        paperSmallBids (instanceAt k)
          (min 1
            (delta / ((Real.exp 1 + 1) *
              (∑ q : Fin (queryCount k), (instanceAt k).maxBidForQuery q))))
  offlineOptimum_tendsTo :
    Sequence.SeqTendsTo
      (fun k =>
        (instanceAt k).offlineOptimumValue
          (fun a => (positive_budgets k a).le))
      optLimit
  revenue_tendsTo :
    Sequence.SeqTendsTo
      (fun k =>
        (instanceAt k).revenue
          ((instanceAt k).runAssignment (instanceAt k).balanceChoiceRule
            (List.finRange (queryCount k))))
      revenueLimit

namespace PaperSmallBidsLimitFamily

noncomputable def toLibrary
    {Advertiser : Type*} [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser]
    (F : PaperSmallBidsLimitFamily Advertiser) :
    AdWordsInstance.MsvvSmallBidsLimitFamily Advertiser where
  queryCount := F.queryCount
  instanceAt := F.instanceAt
  optLimit := F.optLimit
  revenueLimit := F.revenueLimit
  nonnegative_bids := F.nonnegative_bids
  positive_budgets := F.positive_budgets
  maxBidSum_pos := F.maxBidSum_pos
  small_bids_eventually := by
    intro delta hdelta
    obtain ⟨N, hN⟩ := F.small_bids_eventually delta hdelta
    exact ⟨N, fun k hk => by
      simpa [paperSmallBids_eq_library] using hN k hk⟩
  offlineOptimum_tendsTo := F.offlineOptimum_tendsTo
  revenue_tendsTo := F.revenue_tendsTo

end PaperSmallBidsLimitFamily

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
  rw [paperMsvvRatio_eq_library, paperRevenue_eq_library]
  exact
    paper_adwords_balance_msvv_approx_competitive_with_query_sum_error_bound
      I hbid hbudget history hnodup hcover hepsilon hepsilon_le_one
      (by simpa [paperSmallBids_eq_library] using hsmall)

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
  rw [paperMsvvRatio_eq_library]
  exact
    paper_adwords_balance_msvv_competitive_of_small_bids_limit_family
      F.toLibrary

/-! ## Section 6 and Section 8: model extensions by effective bids -/

/-- Section 6: arbitrary effective charges preserve the paper small-bids condition. -/
theorem section6_effective_bids_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ) {epsilon : ℝ}
    (hsmall : ∀ a q, effectiveBid a q ≤ epsilon * I.budget a) :
    paperSmallBids (I.withEffectiveBids effectiveBid) epsilon := by
  simpa [paperSmallBids_eq_library] using
    paper_adwords_effective_bids_small_bids I effectiveBid hsmall

/-- Section 6: click-through-rate effective bids preserve small bids when CTRs are at most one. -/
theorem section6_click_through_rates_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) {epsilon : ℝ}
    (hbid : I.NonnegativeBids)
    (hctr_le_one : ∀ a q, ctr a q ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (I.withClickThroughRates ctr) epsilon := by
  simpa [paperSmallBids_eq_library] using
    paper_adwords_click_through_rates_small_bids I ctr hctr_le_one hbid
      (by simpa [paperSmallBids_eq_library] using hsmall)

/-- Section 6: delayed-entry availability masks preserve small bids. -/
theorem section6_availability_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (available : Advertiser → Query → Prop) {epsilon : ℝ}
    [∀ a q, Decidable (available a q)]
    (hepsilon : 0 ≤ epsilon)
    (hbudget : I.PositiveBudgets)
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (I.withAvailability available) epsilon := by
  simpa [paperSmallBids_eq_library] using
    paper_adwords_availability_small_bids I available hepsilon hbudget
      (by simpa [paperSmallBids_eq_library] using hsmall)

/-- Section 6: multiple slots per query reduce to distinct slot-query IDs. -/
theorem section6_multiple_slots_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) {epsilon : ℝ}
    (Slot : Query → Type*)
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (I.withSlots Slot) epsilon := by
  simpa [paperSmallBids_eq_library] using
    paper_adwords_multiple_slots_small_bids I Slot
      (by simpa [paperSmallBids_eq_library] using hsmall)

/-- Section 8: advertiser-weighted effective bids preserve small bids for weights in `[0,1]`. -/
theorem section8_weighted_bids_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (weight : Advertiser → ℝ) {epsilon : ℝ}
    (hbid : I.NonnegativeBids)
    (hweight_le_one : ∀ a, weight a ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (I.withAdvertiserWeights weight) epsilon := by
  simpa [paperSmallBids_eq_library] using
    paper_adwords_weighted_bids_small_bids I weight hweight_le_one hbid
      (by simpa [paperSmallBids_eq_library] using hsmall)

/-! ## Section 7 / Theorem 9: b-matching randomized lower bound -/

/-- The hard distribution in Theorem 9 is uniform over bidder permutations. -/
noncomputable abbrev theorem9HardDistribution (N : ℕ) :
    PMF (Equiv.Perm (Fin N)) :=
  uniformPermutationDistribution N

/--
Theorem 9 deterministic algorithms in this formalization: a finite integral
prefix algorithm sees only the observed prefix and chooses at most one visible
eligible bidder each round.
-/
abbrev theorem9IntegralPrefixAlgorithm (N : ℕ) :=
  BMatchingIntegralPrefixAlgorithm N

/-- The capped normalized revenue expression used in the Section 7 proof. -/
noncomputable abbrev theorem9CappedNormalizedRevenue
    (N : ℕ) (algorithm : theorem9IntegralPrefixAlgorithm N)
    (permutation : Equiv.Perm (Fin N)) : ℝ :=
  paper_adwords_theorem9_integral_prefix_algorithm_family.normalizedRevenue
    N algorithm permutation

/--
Theorem 9 harmonic-cap lemma: the finite normalized hard-instance revenue cap
is eventually within every positive additive error of `1 - 1/e`.
-/
theorem theorem9_harmonic_eventually_le_msvv_ratio_add_delta :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        theorem9NormalizedRevenueUpperBound N ≤
          paperMsvvRatio + delta := by
  rw [paperMsvvRatio_eq_library]
  exact paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta

/--
Theorem 9, concrete integral-prefix endpoint. No randomized distribution over
finite prefix algorithms can beat `1 - 1/e + delta` on every sufficiently large
permutation instance of the hard b-matching family.
-/
theorem theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio
    :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (theorem9IntegralPrefixAlgorithm N),
          ¬ ∀ permutation,
            paperMsvvRatio + delta <
              EconCSLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  theorem9CappedNormalizedRevenue N algorithm permutation) := by
  rw [paperMsvvRatio_eq_library]
  exact
    paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms

/--
Theorem 9, realized-revenue endpoint. The same lower bound applies to any
richer realized-revenue model bounded pointwise by the capped prefix payoff.
-/
theorem theorem9_no_randomized_realized_revenue_algorithm_beats_msvv_ratio
    (normalizedRevenue :
      (N : ℕ) → theorem9IntegralPrefixAlgorithm N →
        Equiv.Perm (Fin N) → ℝ)
    (hrealized_le_capped :
      ∀ N algorithm permutation,
        normalizedRevenue N algorithm permutation ≤
          theorem9CappedNormalizedRevenue N algorithm permutation) :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (theorem9IntegralPrefixAlgorithm N),
          ¬ ∀ permutation,
            paperMsvvRatio + delta <
              EconCSLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  normalizedRevenue N algorithm permutation) := by
  rw [paperMsvvRatio_eq_library]
  exact
    paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms_of_realized_revenue
      normalizedRevenue hrealized_le_capped

end MSVV07PaperFacing
end Online
end EconCSLib
