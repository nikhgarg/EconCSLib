import EconCSLib.SocialChoice.FairDivision.IndivisibleGoods
import EconCSLib.SocialChoice.FairDivision.LMMSAlgorithm

/-!
# Paper-Facing Theorems: On Approximately Fair Allocations of Indivisible Goods

This file is the public theorem interface for the Lipton-Markakis-Mossel-Saberi
fair-division formalization. Detailed envy-graph and allocation lemmas live in
`IndivisibleGoods.lean`.
-/

namespace EconCSLib
namespace FairDivision

variable {Agent Item : Type*}

/-! ## 1) Paper-Facing Definitions -/

/--
The pairwise envy one agent has for another's bundle.
Paper Definition: $max \{0, v_i(A_j) - v_i(A_i)\}$
-/
noncomputable def paper_envy (v : Valuation Agent Item) (A : Allocation Agent Item) (i j : Agent) : ℝ :=
  max 0 (v.value i (A j) - v.value i (A i))

theorem paper_envy_eq_envy (v : Valuation Agent Item) (A : Allocation Agent Item) (i j : Agent) :
    paper_envy v A i j = envy v A i j := by
  rfl

/--
An allocation has envy bounded by $\alpha$ if no pairwise envy exceeds $\alpha$.
Paper Definition: $e(A) \le \alpha$
-/
def paper_envy_bounded_by (v : Valuation Agent Item) (A : Allocation Agent Item) (α : ℝ) : Prop :=
  ∀ i j, paper_envy v A i j ≤ α

theorem paper_envy_bounded_by_iff (v : Valuation Agent Item) (A : Allocation Agent Item) (α : ℝ) :
    paper_envy_bounded_by v A α ↔ EnvyBoundedBy v A α := by
  rfl

/--
The maximum marginal value of a single item to any agent over any bundle.
Paper Definition: $\alpha = \max_{i, S, g} (v_i(S \cup \{g\}) - v_i(S))$
-/
noncomputable def paper_max_marginal
    [Fintype Agent] [Fintype Item] [DecidableEq Item] [Nonempty Agent] [Nonempty Item]
    (v : Valuation Agent Item) : ℝ :=
  ((Finset.univ : Finset Agent).product
      (((Finset.univ : Finset Item).powerset).product
        (Finset.univ : Finset Item))).sup'
    (by
      obtain ⟨agent⟩ := (inferInstance : Nonempty Agent)
      obtain ⟨g⟩ := (inferInstance : Nonempty Item)
      exact ⟨(agent, (∅, g)), by simp⟩)
    (fun p => v.value p.1 (insert p.2.2 p.2.1) - v.value p.1 p.2.1)

theorem paper_max_marginal_eq_maxMarginal
    [Fintype Agent] [Fintype Item] [DecidableEq Item] [Nonempty Agent] [Nonempty Item]
    (v : Valuation Agent Item) :
    paper_max_marginal v = maxMarginal v := by
  rfl

/--
A valid allocation partition of a set of goods.
Every good in a bundle comes from the set, and every good in the set is in exactly one bundle.
-/
def paper_is_allocation_of [DecidableEq Item] (A : Allocation Agent Item) (goods : Finset Item) : Prop :=
  (∀ i g, g ∈ A i → g ∈ goods) ∧ (∀ g, g ∈ goods → ∃! i, g ∈ A i)

theorem paper_is_allocation_of_iff [DecidableEq Item] (A : Allocation Agent Item) (goods : Finset Item) :
    paper_is_allocation_of A goods ↔ IsAllocationOf A goods := by
  rfl

/-! ## 2) Main Theorems -/

/--
LMMS Theorem 2.1, finite maximum-marginal form.

For finite agents and finite indivisible goods with monotone valuations, every
finite goods set has an allocation whose pairwise envy is bounded by the maximum
one-good marginal value.
-/
theorem paper_lmms_theorem_2_1_max_marginal
    {Agent Item : Type*}
    [Fintype Agent] [Fintype Item] [DecidableEq Item]
    [Nonempty Agent] [Nonempty Item]
    (v : Valuation Agent Item) :
    ∀ goods : Finset Item,
      ∃ A : Allocation Agent Item, paper_is_allocation_of A goods ∧
        paper_envy_bounded_by v A (paper_max_marginal v) := by
  intro goods
  have ⟨A, halloc, hbound⟩ := lmms_theorem_2_1_finite_maxMarginal v goods
  use A
  rw [paper_is_allocation_of_iff, paper_envy_bounded_by_iff, paper_max_marginal_eq_maxMarginal]
  exact ⟨halloc, hbound⟩

/--
LMMS Theorem 2.1, abstract marginal-bound form.

This version keeps the paper's envy bound as an explicit parameter `α`.
-/
theorem paper_lmms_theorem_2_1_marginal_bound
    {Agent Item : Type*}
    [Finite Agent] [Finite Item] [DecidableEq Item] [Nonempty Agent]
    (v : Valuation Agent Item) {α : ℝ}
    (hαnonneg : 0 ≤ α)
    (hmargin : MarginalBound v α) :
    ∀ goods : Finset Item,
      ∃ A : Allocation Agent Item, paper_is_allocation_of A goods ∧
        paper_envy_bounded_by v A α := by
  intro goods
  have ⟨A, halloc, hbound⟩ := lmms_theorem_2_1_finite v hαnonneg hmargin goods
  use A
  rw [paper_is_allocation_of_iff, paper_envy_bounded_by_iff]
  exact ⟨halloc, hbound⟩

/--
LMMS Algorithm form: the iterative step naturally constructs the bounded-envy allocation.
-/
noncomputable def paper_lmms_algorithm
    {Agent Item : Type*}
    [Finite Agent] [Finite Item] [DecidableEq Agent] [DecidableEq Item] [Nonempty Agent]
    (v : Valuation Agent Item) {α : ℝ} (hαnonneg : 0 ≤ α) (hmargin : MarginalBound v α)
    (goodsList : List Item) : Allocation Agent Item :=
  (lmmsAlgorithm v hαnonneg hmargin goodsList).2.val

theorem paper_lmms_algorithm_isAllocationOf_and_envyBoundedBy
    {Agent Item : Type*}
    [Finite Agent] [Finite Item] [DecidableEq Agent] [DecidableEq Item] [Nonempty Agent]
    (v : Valuation Agent Item) {α : ℝ} (hαnonneg : 0 ≤ α) (hmargin : MarginalBound v α)
    (goodsList : List Item) (hnodup : goodsList.Nodup) :
    paper_is_allocation_of (paper_lmms_algorithm v hαnonneg hmargin goodsList) goodsList.toFinset ∧
    paper_envy_bounded_by v (paper_lmms_algorithm v hαnonneg hmargin goodsList) α := by
  have h_props := lmmsAlgorithm_isAllocationOf_and_envyBoundedBy v hαnonneg hmargin goodsList
  have h_goods := lmmsAlgorithm_goods_eq_list_toFinset v hαnonneg hmargin goodsList hnodup
  unfold paper_lmms_algorithm
  rw [← h_goods]
  rw [paper_is_allocation_of_iff, paper_envy_bounded_by_iff]
  exact h_props

end FairDivision
end EconCSLib
