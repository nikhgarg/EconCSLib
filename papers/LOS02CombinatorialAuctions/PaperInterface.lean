import LOS02CombinatorialAuctions.ProofInterface
import LOS02CombinatorialAuctions.Assumptions

/-!
# Paper Interface: Truth Revelation in Approximately Efficient Combinatorial Auctions

Compact human-facing review surface for the LOS 2002 combinatorial-auction
formalization. Broad proof-facing aliases and migration endpoints live in
`ProofInterface.lean`.
-/

namespace LOS02CombinatorialAuctions
namespace PaperInterface

open EconCSLib.Auction

/-! ## Source Definitions -/

/-- Paper utility in a combinatorial auction. -/
abbrev utility {Bidder Item : Type*}
    (M : CombinatorialAuction Bidder Item)
    (values reports : CombinatorialReport Bidder Item) (i : Bidder) : ℝ :=
  LOS02CombinatorialAuctions.paper_combinatorial_utility M values reports i

/--
Utility is value for the allocated bundle minus the bidder's payment.
Source status: direct source formula
-/
theorem utility_formula {Bidder Item : Type*}
    (M : CombinatorialAuction Bidder Item)
    (values reports : CombinatorialReport Bidder Item) (i : Bidder) :
    utility M values reports i =
      values i (M.allocation reports i) - M.payment reports i := by
  rfl

/-- Paper dominant-strategy truthfulness predicate on an admissible domain. -/
abbrev truthfulOn {Bidder Item : Type*} [DecidableEq Bidder]
    (M : CombinatorialAuction Bidder Item)
    (admissible : CombinatorialReport Bidder Item → Prop) : Prop :=
  LOS02CombinatorialAuctions.paper_combinatorial_truthful_on M admissible

/--
Truthfulness means every admissible value profile weakly prefers reporting
truthfully to replacing bidder `i`'s report by any alternative bundle valuation.
Source status: direct source definition
-/
theorem truthfulOn_iff {Bidder Item : Type*} [DecidableEq Bidder]
    (M : CombinatorialAuction Bidder Item)
    (admissible : CombinatorialReport Bidder Item → Prop) :
    truthfulOn M admissible ↔
      ∀ values, admissible values →
        ∀ (i : Bidder) (report : Bundle Item → ℝ),
          utility M values (Function.update values i report) i ≤
            utility M values values i := by
  rfl

/-- Section 4 generalized Vickrey auction from a supplied allocation rule. -/
noncomputable abbrev generalizedVickreyAuction
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item) :
    CombinatorialAuction Bidder Item :=
  LOS02CombinatorialAuctions.paper_generalized_vickrey_auction alloc

/--
The generalized Vickrey auction uses the supplied allocation rule and Clarke
pivot payments.
Source status: direct source formula
-/
theorem generalizedVickreyAuction_allocation_payment
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item)
    (reports : CombinatorialReport Bidder Item) (i : Bidder) :
    (generalizedVickreyAuction alloc).allocation reports = alloc reports ∧
      (generalizedVickreyAuction alloc).payment reports i =
        allocationValueExcept reports (alloc (reportsWithoutBidder reports i)) i -
          allocationValueExcept reports (alloc reports) i := by
  exact ⟨rfl, rfl⟩

/-- Paper-facing accepted-set mechanism for single-minded bid profiles. -/
abbrev singleMindedAcceptedMechanism (Bidder Item : Type*) :=
  SingleMindedAcceptedMechanism Bidder Item

/--
A single-minded accepted-set mechanism consists of an accepted-bidder rule and
a payment rule.
Source status: direct source definition
-/
theorem singleMindedAcceptedMechanism_fields
    (Bidder Item : Type*) (M : singleMindedAcceptedMechanism Bidder Item) :
    M = { accepted := M.accepted, payment := M.payment } := by
  cases M
  rfl

/-- Truthfulness predicate for single-minded bid-profile mechanisms. -/
abbrev singleMindedTruthfulOn
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (admissible : (Bidder → SingleMindedBid Item) → Prop) : Prop :=
  M.TruthfulOn admissible

/--
Single-minded truthfulness allows no admissible single-bidder deviation to
raise the true single-minded utility.
Source status: direct source definition
-/
theorem singleMindedTruthfulOn_iff
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (admissible : (Bidder → SingleMindedBid Item) → Prop) :
    singleMindedTruthfulOn M admissible ↔
      ∀ values, admissible values →
        ∀ i report,
          admissible (Function.update values i report) →
            M.utility values (Function.update values i report) i ≤
              M.utility values values i := by
  rfl

/-- Nonempty, nonnegative single-minded bid profiles. -/
abbrev nonnegativeNonemptySingleMindedProfile
    {Bidder Item : Type*} [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) : Prop :=
  SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile bids

/--
Every single-minded bid has a nonempty desired bundle and nonnegative value.
Source status: direct source condition
-/
theorem nonnegativeNonemptySingleMindedProfile_iff
    {Bidder Item : Type*} [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) :
    nonnegativeNonemptySingleMindedProfile bids ↔
      ∀ i, (bids i).desired.Nonempty ∧ 0 ≤ (bids i).value := by
  rfl

/-- Weighted set-packing objective used in Theorem 6.1's reduction. -/
noncomputable abbrev weightedSetPackingValue
    {Bidder : Type*} [DecidableEq Bidder]
    (weights : Bidder → ℝ) (selected : Finset Bidder) : ℝ :=
  LOS02CombinatorialAuctions.paper_weighted_set_packing_value weights selected

/--
The weighted set-packing objective sums the selected bidders' weights.
Source status: direct source formula
-/
theorem weightedSetPackingValue_formula
    {Bidder : Type*} [DecidableEq Bidder]
    (weights : Bidder → ℝ) (selected : Finset Bidder) :
    weightedSetPackingValue weights selected =
      ∑ i ∈ selected, weights i := by
  rfl

/-- Encode a weighted set-packing instance as single-minded bids. -/
abbrev setPackingSingleMindedBids
    {Bidder Item : Type*}
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ) :
    Bidder → SingleMindedBid Item :=
  LOS02CombinatorialAuctions.paper_set_packing_single_minded_bids sets weights

/--
The set-packing encoding gives bidder `i` desired set `sets i` and value
`weights i`.
Source status: direct source formula
-/
theorem setPackingSingleMindedBids_formula
    {Bidder Item : Type*}
    (sets : Bidder → Finset Item) (weights : Bidder → ℝ) (i : Bidder) :
    setPackingSingleMindedBids sets weights i =
      { desired := sets i, value := weights i } := by
  rfl

/-- Definition 7.1: average amount per good for a single-minded bid. -/
noncomputable abbrev averageAmountPerGood {Item : Type*} [DecidableEq Item]
    (b : SingleMindedBid Item) : ℝ :=
  LOS02CombinatorialAuctions.paper_average_amount_per_good b

/--
Average amount per good is the bid value divided by the desired-bundle size.
Source status: direct source formula
-/
theorem averageAmountPerGood_formula {Item : Type*} [DecidableEq Item]
    (b : SingleMindedBid Item) :
    averageAmountPerGood b = b.value / b.bundleSize := by
  rfl

/-- Concrete LOS02 order: decreasing average amount per good with deterministic tie-breaks. -/
noncomputable abbrev averageOrderOf
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) : List Bidder :=
  LOS02CombinatorialAuctions.paper_average_order_of bids

/--
The concrete average order lists every bidder exactly once and is weakly
descending in average amount per good.
Source status: direct source rule
-/
theorem averageOrderOf_rule
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Item]
    [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    (averageOrderOf bids).Nodup ∧
      (∀ i : Bidder, i ∈ averageOrderOf bids) ∧
        SingleMindedAverageAmountDescending bids (averageOrderOf bids) := by
  exact
    ⟨LOS02CombinatorialAuctions.paper_average_order_of_nodup bids,
      LOS02CombinatorialAuctions.paper_average_order_of_mem bids,
      LOS02CombinatorialAuctions.paper_average_order_of_average_descending bids⟩

/-- Greedy accepted set from an explicit bid order. -/
abbrev greedyAcceptedFromOrder
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) :
    Finset Bidder :=
  LOS02CombinatorialAuctions.paper_single_minded_greedy_accepted_from_order
    bids order

/--
The greedy accepted set starts empty and folds through the order, accepting a
bid iff it conflicts with no already accepted bid.
Source status: direct source formula
-/
theorem greedyAcceptedFromOrder_formula
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) :
    greedyAcceptedFromOrder bids order =
      order.foldl (singleMindedGreedyStep bids) ∅ := by
  rfl

/-- The paper's concrete average-order greedy accepted set. -/
noncomputable abbrev averageGreedyAcceptedSet
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) : Finset Bidder :=
  LOS02CombinatorialAuctions.paper_average_greedy_accepted_set bids

/--
Average-greedy accepts the greedy set from the concrete average order.
Source status: direct source formula
-/
theorem averageGreedyAcceptedSet_formula
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    averageGreedyAcceptedSet bids =
      greedyAcceptedFromOrder bids (averageOrderOf bids) := by
  rfl

/-- The paper's concrete average-order Definition 10.1 payment rule. -/
noncomputable abbrev averageGreedyPayment
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) : ℝ :=
  LOS02CombinatorialAuctions.paper_average_greedy_payment bids j

/--
Definition 10.1 payment: denied bidders pay zero; accepted bidders pay zero
when there is no later denied blocker, and otherwise pay their bundle size
times that blocker bid's average amount per good.
Source status: direct source formula
-/
theorem averageGreedyPayment_formula
    {Bidder Item : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (j : Bidder) :
    averageGreedyPayment bids j =
      if j ∈ averageGreedyAcceptedSet bids then
        match
          LOS02CombinatorialAuctions.paper_greedy_next_denied_from_order
            bids (averageOrderOf bids) j with
        | none => 0
        | some n => (bids j).bundleSize * (bids n).averageAmountPerGood
      else
        0 := by
  rfl

/-! ## Sections 4--6 -/

/-- Theorem 4.1: generalized Vickrey auctions are truthful. -/
abbrev theorem4_1_generalized_vickrey_truthful :=
  @LOS02CombinatorialAuctions.ProofInterface.theorem4_1_generalized_vickrey_truthful

/-- Proposition 4.2: truthful GVA bidder utility is nonnegative. -/
abbrev proposition4_2_generalized_vickrey_truthful_utility_nonneg :=
  @LOS02CombinatorialAuctions.ProofInterface.proposition4_2_generalized_vickrey_truthful_utility_nonneg

/-- Theorem 6.1 set-packing feasibility encoding. -/
abbrev theorem6_1_set_packing_feasibility_encoding_correct :=
  @LOS02CombinatorialAuctions.ProofInterface.theorem6_1_set_packing_feasibility_encoding_correct

/-- Theorem 6.1 set-packing value encoding. -/
abbrev theorem6_1_set_packing_value_encoding_correct :=
  @LOS02CombinatorialAuctions.ProofInterface.theorem6_1_set_packing_value_encoding_correct

/-- Theorem 6.1 weighted set-packing reduction. -/
abbrev theorem6_1_weighted_set_packing_reduction :=
  @LOS02CombinatorialAuctions.ProofInterface.theorem6_1_weighted_set_packing_reduction

/-- Theorem 6.1 clique-to-single-minded welfare reduction. -/
abbrev theorem6_1_clique_decision_single_minded_welfare_reduction :=
  @LOS02CombinatorialAuctions.ProofInterface.theorem6_1_clique_decision_single_minded_welfare_reduction

/--
Theorem 6.1 external exact-solver complexity consequence.
Source status: partial external complexity boundary
-/
abbrev theorem6_1_external_optimal_solver_np_eq_zpp :=
  @LOS02CombinatorialAuctions.ProofInterface.theorem6_1_external_optimal_solver_np_eq_zpp

/--
Theorem 6.1 external approximation-solver complexity consequence.
Source status: partial external complexity boundary
-/
abbrev theorem6_1_external_approximation_solver_np_eq_zpp :=
  @LOS02CombinatorialAuctions.ProofInterface.theorem6_1_external_approximation_solver_np_eq_zpp

/--
Complexity-class note: `NP = ZPP` implies the randomized collapse.
Source status: partial external complexity boundary
-/
abbrev complexity_note_np_eq_zpp_implies_randomized_collapse :=
  @LOS02CombinatorialAuctions.ProofInterface.complexity_note_np_eq_zpp_implies_randomized_collapse

/-! ## Sections 7--10 -/

/-- Theorem 7.2 greedy allocation square-root approximation. -/
abbrev theorem7_2_sqrt_norm_approx_of_sorted_order :=
  @LOS02CombinatorialAuctions.ProofInterface.theorem7_2_sqrt_norm_approx_of_sorted_order

/-- Lemma 9.1 critical-value existence from monotonicity. -/
abbrev lemma9_1_exists_nonnegative_critical_value_of_monotonicity :=
  @LOS02CombinatorialAuctions.ProofInterface.lemma9_1_exists_nonnegative_critical_value_of_monotonicity

/--
Lemma 9.2 denied-bidder utility is zero.
Source status: direct source lemma endpoint
-/
abbrev lemma9_2_denied_bidder_utility_eq_zero :=
  @LOS02CombinatorialAuctions.ProofInterface.lemma9_2_denied_bidder_utility_eq_zero

/-- Lemma 9.3 truth-telling utility is nonnegative under critical-value certificates. -/
abbrev lemma9_3_truthful_utility_nonnegative_of_nonnegative_infinity_certificate :=
  @LOS02CombinatorialAuctions.ProofInterface.lemma9_3_truthful_utility_nonnegative_of_nonnegative_infinity_certificate

/--
Lemma 9.3 truth-telling utility is nonnegative under critical-value conditions.
Source status: direct source lemma endpoint with visible certificate boundary
-/
abbrev lemma9_3_truthful_utility_nonnegative_condition :=
  @LOS02CombinatorialAuctions.ProofInterface.lemma9_3_truthful_utility_nonnegative_of_nonnegative_infinity_certificate

/-- Lemma 9.4 no profitable value-only lie under nonnegative infinity axioms. -/
abbrev lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms :=
  @LOS02CombinatorialAuctions.ProofInterface.lemma9_4_no_profitable_value_only_lie_of_nonnegative_infinity_axioms

/--
Lemma 9.5 finite threshold monotonicity.
Source status: direct source lemma endpoint
-/
abbrev lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate :=
  @LOS02CombinatorialAuctions.ProofInterface.lemma9_5_finite_threshold_mono_of_nonnegative_infinity_certificate

/-- Theorem 9.6 critical axioms imply truthfulness for single-minded bidders. -/
abbrev theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms :=
  @LOS02CombinatorialAuctions.ProofInterface.theorem9_6_single_minded_truthful_of_nonnegative_infinity_axioms

/-- Theorem 10.2 average-order greedy mechanism truthfulness. -/
abbrev theorem10_2_averageGreedy_truthful :=
  @LOS02CombinatorialAuctions.ProofInterface.theorem10_2_averageGreedy_truthful

end PaperInterface
end LOS02CombinatorialAuctions
