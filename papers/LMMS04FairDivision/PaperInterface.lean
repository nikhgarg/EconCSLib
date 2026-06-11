import LMMS04FairDivision.ProofInterface

/-!
# Paper Interface: Approximately Fair Allocations of Indivisible Goods

Compact human-facing review surface for the LMMS 2004 formalization. Broad
proof-facing aliases and migration endpoints live in `ProofInterface.lean`.
-/

open MeasureTheory
open Filter
open scoped BigOperators
open EconCSLib.FairDivision

namespace LMMS04FairDivision
namespace PaperInterface

variable {Agent Item : Type*} [Fintype Agent] [Fintype Item] [DecidableEq Agent]
  [DecidableEq Item] [Nonempty Agent] [Nonempty Item]

noncomputable section

/-! ## Paper Definitions -/

/-- Envy of agent `i` toward agent `j`: positive part of the value difference. -/
def envy (v : Valuation Agent Item) (A : Allocation Agent Item)
    (i j : Agent) : ℝ :=
  max 0 (v.value i (A j) - v.value i (A i))

/-- Envy-free allocations have no positive envy between any ordered pair. -/
def envyFree (v : Valuation Agent Item) (A : Allocation Agent Item) : Prop :=
  ∀ i j, v.value i (A j) ≤ v.value i (A i)

/-- Bounded-envy predicate used in Theorem 2.1. -/
def envyBoundedBy (v : Valuation Agent Item) (A : Allocation Agent Item)
    (alpha : ℝ) : Prop :=
  ∀ i j, envy v A i j ≤ alpha

/-- Maximum marginal item value. -/
def maxMarginal (v : Valuation Agent Item) : ℝ :=
  LMMS04FairDivision.paper_max_marginal v

/-- Allocation of exactly the specified finite set of goods. -/
def isAllocationOf (A : Allocation Agent Item) (goods : Finset Item) : Prop :=
  IsAllocationOf A goods

/-! ## Section 2: Bounded Envy -/

/-- Lemma 2.2: envy-cycle elimination produces an acyclic envy graph. -/
abbrev lemma2_2_acyclic_reduction :=
  @LMMS04FairDivision.ProofInterface.lemma2_2_acyclic_reduction

/-- Theorem 2.1: bounded-envy allocation existence. -/
abbrev theorem2_1_bounded_envy_allocation_exists :=
  @LMMS04FairDivision.ProofInterface.theorem2_1_bounded_envy_allocation_exists

/-- Theorem 2.1 alpha-bounded form. -/
abbrev theorem2_1_alpha_bounded_allocation_exists :=
  @LMMS04FairDivision.ProofInterface.theorem2_1_alpha_bounded_allocation_exists

/-- Theorem 2.1 constructive list algorithm form. -/
abbrev theorem2_1_algorithm_correct_list_toFinset :=
  @LMMS04FairDivision.ProofInterface.theorem2_1_algorithm_correct_list_toFinset

/-- Theorem 2.3 real-interval supported atom-bound endpoint. -/
abbrev theorem2_3_real_interval_supported_atom_bound :=
  @LMMS04FairDivision.ProofInterface.theorem2_3_real_interval_supported_atom_bound

/-! ## Section 3: Approximation and PTAS Boundary -/

/-- Theorem 3.1 adaptive-query lower bound. -/
abbrev theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries :=
  @LMMS04FairDivision.ProofInterface.theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries

/-- Theorem 3.1 adaptive-query ratio lower bound. -/
abbrev theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries :=
  @LMMS04FairDivision.ProofInterface.theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries

/-- Theorem 3.2 Graham-certificate fair-division consequence. -/
abbrev theorem3_2_graham_certificate_to_envy_ratio_bound :=
  @LMMS04FairDivision.ProofInterface.theorem3_2_graham_certificate_to_envy_ratio_bound

/-- Theorem 3.2 evaluates the Graham factor as seven fifths. -/
abbrev theorem3_2_graham_factor_eq_seven_fifths :=
  @LMMS04FairDivision.ProofInterface.theorem3_2_graham_factor_eq_seven_fifths

/-- Theorem 3.3 conditional fixed-dimension IP summary. -/
abbrev theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee

/-- Claim 3.4 fixed-rounding ratio endpoint. -/
abbrev theorem3_3_claim34_fixed_rounding_ratio_endpoint :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_claim34_fixed_rounding_ratio_endpoint

/-- Claim 3.4 capped weighted-supply endpoint. -/
abbrev theorem3_3_claim34_capped_weighted_supply_ratio_endpoint :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_claim34_capped_weighted_supply_ratio_endpoint

/-- Claim 3.4 min/max-search certificate endpoint. -/
abbrev theorem3_3_claim34_min_max_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_claim34_min_max_search_certificate_ratio_endpoint

/-- Claim 3.4 bounded-optimal certificate. -/
abbrev claim3_4_bounded_optimal_certificate :=
  @LMMS04FairDivision.ProofInterface.claim3_4_bounded_optimal_certificate

/-- Claim 3.4 exact-allocation bounded optimum endpoint. -/
abbrev claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods :=
  @LMMS04FairDivision.ProofInterface.claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods

/-- Claim 3.4 identical-utilities bounded optimum endpoint. -/
abbrev claim3_4_bounded_optimal_of_identical_utilities_model :=
  @LMMS04FairDivision.ProofInterface.claim3_4_bounded_optimal_of_identical_utilities_model

/-- Theorem 3.3 additive-load ratio transfer. -/
abbrev theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads

/-- Lemma 3.5 additive transfer endpoint. -/
abbrev lemma3_5_additive_transfer_certificate_epsilon_of_opt_loads :=
  @LMMS04FairDivision.ProofInterface.lemma3_5_additive_transfer_certificate_epsilon_of_opt_loads

/-! ## Section 4: Truthfulness and Random Allocation -/

/-- Direct fair-division mechanism without transfers. -/
abbrev directMechanism (Agent Item : Type*) :=
  LMMS04FairDivision.paper_direct_mechanism Agent Item

/-- A direct no-transfer mechanism consists only of an allocation rule. -/
theorem directMechanism_fields
    (Agent Item : Type*) (M : directMechanism Agent Item) :
    M = { allocation := M.allocation } := by
  cases M
  rfl

/-- Randomized direct fair-division mechanism without transfers. -/
abbrev randomizedDirectMechanism (Agent Item : Type*) :=
  LMMS04FairDivision.paper_randomized_direct_mechanism Agent Item

/-- A randomized direct no-transfer mechanism consists only of an allocation law. -/
theorem randomizedDirectMechanism_fields
    (Agent Item : Type*) (M : randomizedDirectMechanism Agent Item) :
    M = { allocationLaw := M.allocationLaw } := by
  cases M
  rfl

/-- Dominant-strategy truthfulness for direct fair-division mechanisms. -/
def truthful [DecidableEq Agent] (M : directMechanism Agent Item) : Prop :=
  LMMS04FairDivision.paper_fair_division_truthful M

/-- Expected-utility truthfulness for randomized direct mechanisms. -/
def randomizedTruthful
    [Fintype (Allocation Agent Item)] [DecidableEq (Allocation Agent Item)]
    [DecidableEq Agent]
    (M : randomizedDirectMechanism Agent Item) : Prop :=
  LMMS04FairDivision.paper_randomized_fair_division_truthful M

/-- The finite two-player/eight-egg source goods used for Theorem 4.1. -/
abbrev theorem4_1_source_goods :=
  @LMMS04FairDivision.ProofInterface.theorem4_1_source_goods

/--
Theorem 4.1 uses the full finite source universe: two named goods plus eight
egg goods, for ten goods total and two agents.
-/
theorem theorem4_1_source_goods_content :
    theorem4_1_source_goods = Finset.univ ∧
      Fintype.card Theorem41.LMMS41Agent = 2 ∧
        theorem4_1_source_goods.card = 10 ∧
          Theorem41.lmms41EggItems.card = 8 := by
  exact ⟨rfl, by decide, by decide, Theorem41.lmms41EggItems_card⟩

/-- The truthful source report used for Theorem 4.1. -/
abbrev theorem4_1_true_report :=
  @LMMS04FairDivision.ProofInterface.theorem4_1_true_report

/--
Theorem 4.1's truthful report is the additive bundle valuation generated by
the displayed two-player item weights.
-/
theorem theorem4_1_true_report_formula :
    theorem4_1_true_report =
      Theorem41.lmms41AdditiveReport Theorem41.lmms41TrueWeight ∧
      ∀ agent item,
        Theorem41.lmms41TrueWeight agent item =
          if agent = Theorem41.LMMS41Agent.player1 then
            if item = Theorem41.LMMS41Item.a then (9 : ℝ) / 20
            else if item = Theorem41.LMMS41Item.b then (7 : ℝ) / 20
            else (1 : ℝ) / 40
          else
            if item = Theorem41.LMMS41Item.a then (7 : ℝ) / 20
            else if item = Theorem41.LMMS41Item.b then (9 : ℝ) / 20
            else (1 : ℝ) / 40 := by
  exact ⟨rfl, by intro agent item; rfl⟩

/-- Theorem 4.1 envy-free mechanism impossibility. -/
abbrev theorem4_1_source_not_truthful_envy_free_whenever_exists :=
  @LMMS04FairDivision.ProofInterface.theorem4_1_source_not_truthful_envy_free_whenever_exists

/-- Theorem 4.1 minimum-envy mechanism impossibility. -/
abbrev theorem4_1_source_minimum_envy_not_truthful :=
  @LMMS04FairDivision.ProofInterface.theorem4_1_source_minimum_envy_not_truthful

/-- Theorem 4.2 uniform-random mechanism truthfulness. -/
abbrev theorem4_2_uniform_random_mechanism_truthful :=
  @LMMS04FairDivision.ProofInterface.theorem4_2_uniform_random_mechanism_truthful

/-- Theorem 4.2 uniform-random maximum-envy probability bound. -/
abbrev theorem4_2_uniform_random_max_envy_probability_bound :=
  @LMMS04FairDivision.ProofInterface.theorem4_2_uniform_random_max_envy_probability_bound

end

end PaperInterface
end LMMS04FairDivision
