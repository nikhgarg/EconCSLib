import LMMS04FairDivision.Theorem34BoundedOptimal
import LMMS04FairDivision.Theorem35RoundingTransfer

/-!
# LMMS Theorem 3.3: finite identical-utilities load support

Theorem 3.3 is stated for the identical-utilities setting.  This file keeps a
small source-shaped finite model around the existing Claim 3.4 and Lemma 3.5
support:

* common item values;
* additive allocation loads;
* finite minimum and maximum loads over the agents;
* the load ratio used by the rounding-transfer layer;
* the average load scale.

It is intentionally just support infrastructure: it does not assert that the
rounding instance or PTAS search has been constructed.
-/

open scoped BigOperators

namespace LMMS04FairDivision
namespace Theorem33

noncomputable section

/--
A finite identical-utilities allocation model: every agent evaluates an item
through the same common item-value function, and an allocation assigns each
agent a finite bundle.
-/
structure IdenticalUtilitiesModel (Agent Item Alloc : Type*) where
  commonValue : Item → ℝ
  bundleOf : Alloc → Agent → Finset Item

/-- Load of a bundle under the common item values. -/
def bundleLoad {Agent Item Alloc : Type*}
    (M : IdenticalUtilitiesModel Agent Item Alloc) (S : Finset Item) : ℝ :=
  Theorem34.commonLoad M.commonValue S

/-- Load assigned to an agent by an allocation. -/
def allocationLoad {Agent Item Alloc : Type*}
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) (i : Agent) : ℝ :=
  bundleLoad M (M.bundleOf A i)

/-- The allocation-load vector. -/
def allocationLoads {Agent Item Alloc : Type*}
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) : Agent → ℝ :=
  allocationLoad M A

/-- Finite minimum load across all agents. -/
def minAllocationLoad {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) : ℝ :=
  (Finset.univ : Finset Agent).inf' Finset.univ_nonempty (allocationLoad M A)

/-- Finite maximum load across all agents. -/
def maxAllocationLoad {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) : ℝ :=
  (Finset.univ : Finset Agent).sup' Finset.univ_nonempty (allocationLoad M A)

/-- Max-over-min load ratio of an allocation. -/
def allocationLoadRatio {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) : ℝ :=
  Theorem35.ratio (minAllocationLoad M A) (maxAllocationLoad M A)

/-- Average allocation load over the finite agent set. -/
def averageAllocationLoad {Agent Item Alloc : Type*} [Fintype Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) : ℝ :=
  (∑ i : Agent, allocationLoad M A i) / (Fintype.card Agent : ℝ)

/-- Bundle load is exactly the Claim 3.4 common-load definition. -/
theorem bundleLoad_eq_commonLoad {Agent Item Alloc : Type*}
    (M : IdenticalUtilitiesModel Agent Item Alloc) (S : Finset Item) :
    bundleLoad M S = Theorem34.commonLoad M.commonValue S := by
  rfl

/-- Allocation load is the Claim 3.4 common load of the allocated bundle. -/
theorem allocationLoad_eq_commonLoad {Agent Item Alloc : Type*}
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) (i : Agent) :
    allocationLoad M A i =
      Theorem34.commonLoad M.commonValue (M.bundleOf A i) := by
  rfl

/-- Removing an item from a bundle subtracts its common value from the bundle load. -/
theorem bundleLoad_erase {Agent Item Alloc : Type*} [DecidableEq Item]
    (M : IdenticalUtilitiesModel Agent Item Alloc) {S : Finset Item} {g : Item}
    (hg : g ∈ S) :
    bundleLoad M (S.erase g) = bundleLoad M S - M.commonValue g := by
  simpa [bundleLoad] using
    Theorem34.commonLoad_erase (v := M.commonValue) (S := S) (g := g) hg

/-- Adding a fresh item to a bundle adds its common value to the bundle load. -/
theorem bundleLoad_insert {Agent Item Alloc : Type*} [DecidableEq Item]
    (M : IdenticalUtilitiesModel Agent Item Alloc) {S : Finset Item} {g : Item}
    (hg : g ∉ S) :
    bundleLoad M (insert g S) = bundleLoad M S + M.commonValue g := by
  simpa [bundleLoad] using
    Theorem34.commonLoad_insert (v := M.commonValue) (S := S) (g := g) hg

/-- The finite minimum load is below every allocation load. -/
theorem minAllocationLoad_le_load {Agent Item Alloc : Type*}
    [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) (i : Agent) :
    minAllocationLoad M A ≤ allocationLoad M A i := by
  unfold minAllocationLoad
  exact
    Finset.inf'_le
      (s := (Finset.univ : Finset Agent))
      (f := allocationLoad M A)
      (by simp : i ∈ (Finset.univ : Finset Agent))

/-- Every allocation load is below the finite maximum load. -/
theorem load_le_maxAllocationLoad {Agent Item Alloc : Type*}
    [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) (i : Agent) :
    allocationLoad M A i ≤ maxAllocationLoad M A := by
  unfold maxAllocationLoad
  exact
    Finset.le_sup'
      (s := (Finset.univ : Finset Agent))
      (f := allocationLoad M A)
      (by simp : i ∈ (Finset.univ : Finset Agent))

/-- The finite minimum load is below the finite maximum load. -/
theorem minAllocationLoad_le_maxAllocationLoad {Agent Item Alloc : Type*}
    [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) :
    minAllocationLoad M A ≤ maxAllocationLoad M A := by
  let i0 : Agent := Classical.choice (inferInstance : Nonempty Agent)
  exact
    le_trans (minAllocationLoad_le_load M A i0)
      (load_le_maxAllocationLoad M A i0)

/-- If every load is nonnegative, then the finite minimum load is nonnegative. -/
theorem minAllocationLoad_nonneg_of_loads_nonneg {Agent Item Alloc : Type*}
    [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc)
    (hloads : ∀ i : Agent, 0 ≤ allocationLoad M A i) :
    0 ≤ minAllocationLoad M A := by
  unfold minAllocationLoad
  exact
    Finset.le_inf'
      (s := (Finset.univ : Finset Agent))
      (f := allocationLoad M A)
      Finset.univ_nonempty
      (by intro i _hi; exact hloads i)

/-- If every load is positive, then the finite minimum load is positive. -/
theorem minAllocationLoad_pos_of_loads_pos {Agent Item Alloc : Type*}
    [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc)
    (hloads : ∀ i : Agent, 0 < allocationLoad M A i) :
    0 < minAllocationLoad M A := by
  unfold minAllocationLoad
  rw [Finset.lt_inf'_iff]
  intro i _hi
  exact hloads i

/-- If every load is nonnegative, then the finite maximum load is nonnegative. -/
theorem maxAllocationLoad_nonneg_of_loads_nonneg {Agent Item Alloc : Type*}
    [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc)
    (hloads : ∀ i : Agent, 0 ≤ allocationLoad M A i) :
    0 ≤ maxAllocationLoad M A := by
  let i0 : Agent := Classical.choice (inferInstance : Nonempty Agent)
  exact le_trans (hloads i0) (load_le_maxAllocationLoad M A i0)

/-- The Theorem 3.3 allocation ratio is exactly the Lemma 3.5 ratio. -/
theorem allocationLoadRatio_eq_theorem35_ratio {Agent Item Alloc : Type*}
    [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) :
    allocationLoadRatio M A =
      Theorem35.ratio (minAllocationLoad M A) (maxAllocationLoad M A) := by
  rfl

/--
The Theorem 3.3 allocation ratio is also the Claim 3.4 max-over-min load
ratio, since both existing support files use the same quotient.
-/
theorem allocationLoadRatio_eq_theorem34_loadRatio {Agent Item Alloc : Type*}
    [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) :
    allocationLoadRatio M A =
      Theorem34.loadRatio (minAllocationLoad M A) (maxAllocationLoad M A) := by
  rfl

/-- The Claim 3.4 and Lemma 3.5 scalar load-ratio definitions coincide. -/
theorem theorem34_loadRatio_eq_theorem35_ratio (minLoad maxLoad : ℝ) :
    Theorem34.loadRatio minLoad maxLoad = Theorem35.ratio minLoad maxLoad := by
  rfl

/-- The allocation load ratio is nonnegative under the natural load signs. -/
theorem allocationLoadRatio_nonneg {Agent Item Alloc : Type*}
    [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc)
    (hmin : 0 < minAllocationLoad M A)
    (hmax : 0 ≤ maxAllocationLoad M A) :
    0 ≤ allocationLoadRatio M A := by
  exact Theorem35.ratio_nonneg hmin hmax

/--
Positive per-agent loads imply the allocation ratio is nonnegative.  This is
the natural sign premise needed by the final Theorem 3.3 transfer endpoint.
-/
theorem allocationLoadRatio_nonneg_of_loads_pos {Agent Item Alloc : Type*}
    [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc)
    (hloads : ∀ i : Agent, 0 < allocationLoad M A i) :
    0 ≤ allocationLoadRatio M A := by
  exact
    allocationLoadRatio_nonneg M A
      (minAllocationLoad_pos_of_loads_pos M A hloads)
      (maxAllocationLoad_nonneg_of_loads_nonneg M A
        (fun i => le_of_lt (hloads i)))

/-- Average load unfolded as a finite sum of Claim 3.4 common loads. -/
theorem averageAllocationLoad_eq_commonLoad_sum {Agent Item Alloc : Type*}
    [Fintype Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc) :
    averageAllocationLoad M A =
      (∑ i : Agent, Theorem34.commonLoad M.commonValue (M.bundleOf A i)) /
        (Fintype.card Agent : ℝ) := by
  rfl

/-- Rewriting the ratio of an allocation through an arbitrary named min/max pair. -/
theorem allocationLoadRatio_eq_of_min_max_eq {Agent Item Alloc : Type*}
    [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc) (A : Alloc)
    {minLoad maxLoad : ℝ}
    (hmin : minAllocationLoad M A = minLoad)
    (hmax : maxAllocationLoad M A = maxLoad) :
    allocationLoadRatio M A = Theorem35.ratio minLoad maxLoad := by
  rw [allocationLoadRatio_eq_theorem35_ratio, hmin, hmax]

/--
Model-level Theorem 3.3 transfer endpoint: scalar Lemma 3.5 transfer
inequalities stated directly for finite identical-utilities allocation ratios
give the paper's `(1 + epsilon)` guarantee.
-/
theorem allocationLoadRatio_transfer_certificate_epsilon
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc)
    {epsilon : ℝ} {optimal rounded output : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (hoptMin : 0 < minAllocationLoad M optimal)
    (hoptMax : 0 ≤ maxAllocationLoad M optimal)
    (hout :
      allocationLoadRatio M output ≤
        allocationLoadRatio M rounded *
          Theorem35.backwardTransferFactor (56 / epsilon))
    (hrounded_opt :
      allocationLoadRatio M rounded ≤
        allocationLoadRatio M optimal *
          Theorem35.forwardTransferFactor (56 / epsilon)) :
    allocationLoadRatio M output ≤
      allocationLoadRatio M optimal * (1 + epsilon) := by
  simpa [allocationLoadRatio_eq_theorem35_ratio] using
    Theorem35.theorem33_ratio_transfer_certificate_epsilon_of_opt_loads
      hepsilon_pos hepsilon_le_one hoptMin hoptMax hout hrounded_opt

end

end Theorem33
end LMMS04FairDivision
