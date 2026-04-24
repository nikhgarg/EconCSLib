import EconCSLean.FairDivision.IndivisibleGoods

/-!
# Paper-Facing Theorems: On Approximately Fair Allocations of Indivisible Goods

This file is the public theorem interface for the Lipton-Markakis-Mossel-Saberi
fair-division formalization. Detailed envy-graph and allocation lemmas live in
`IndivisibleGoods.lean`.
-/

namespace EconCSLean
namespace FairDivision

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
      ∃ A : Allocation Agent Item, IsAllocationOf A goods ∧
        EnvyBoundedBy v A (maxMarginal v) := by
  exact lmms_theorem_2_1_finite_maxMarginal v

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
      ∃ A : Allocation Agent Item, IsAllocationOf A goods ∧
        EnvyBoundedBy v A α := by
  exact lmms_theorem_2_1_finite v hαnonneg hmargin

end FairDivision
end EconCSLean
