import LMMS04FairDivision.Theorem34BoundedOptimal

/-!
# LMMS Claim 3.4: local reallocation step

This file adds source-specific support for the local move used in Claim 3.4.
The generic certificate in `Theorem34BoundedOptimal` already says that a move
which stays inside the old extrema is ratio-nonincreasing.  Here we discharge
the paper arithmetic: if the receiving bundle has load below `L / 2`, the
donating bundle has load above `2L`, and every moved good has value below `L`,
then moving that good keeps the new loads inside the old min/max interval.

The file also records a concrete natural-number potential for this local step:
the donor bundle cardinality strictly decreases after erasing the moved good.
-/

open scoped BigOperators

namespace LMMS04FairDivision
namespace Theorem34

noncomputable section

/-- Move an item from one finite bundle to another. -/
def moveBundle {Agent Item : Type*} [DecidableEq Agent] [DecidableEq Item]
    (bundle : Agent → Finset Item) (source target : Agent) (g : Item) :
    Agent → Finset Item :=
  fun i =>
    if i = source then (bundle i).erase g
    else if i = target then insert g (bundle i)
    else bundle i

/-- A local natural-number potential: the number of goods left in the donor bundle. -/
def donorCardPotential {Agent Item : Type*}
    (bundle : Agent → Finset Item) (source : Agent) : ℕ :=
  (bundle source).card

/-- Number of bundles attaining a specified minimum load. -/
noncomputable def minLoadMultiplicity {Agent Item : Type*} [Fintype Agent]
    (v : Item → ℝ) (bundle : Agent → Finset Item) (minLoad : ℝ) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset Agent).filter
      (fun i : Agent => commonLoad v (bundle i) = minLoad)).card

/--
Finite tie-breaker potential for the low-only Claim 3.4 route.  It ranks an
allocation first by the finite set of attainable minimum-load values above its
current minimum, then by the number of bundles attaining the current minimum.
-/
noncomputable def minLoadTiePotential
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc]
    (v : Item → ℝ) (bundleOf : Alloc → Agent → Finset Item)
    (minOf : Alloc → ℝ) (A : Alloc) : ℕ := by
  classical
  exact
    (((Finset.univ : Finset Alloc).image minOf).filter
      (fun u : ℝ => minOf A < u)).card * (Fintype.card Agent + 1) +
      minLoadMultiplicity v (bundleOf A) (minOf A)

/-- Uniform finite bound for the low-only tie-breaker potential. -/
theorem minLoadTiePotential_le_card_bound
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc]
    (v : Item → ℝ) (bundleOf : Alloc → Agent → Finset Item)
    (minOf : Alloc → ℝ) (A : Alloc) :
    minLoadTiePotential v bundleOf minOf A ≤
      Fintype.card Alloc * (Fintype.card Agent + 1) +
        Fintype.card Agent := by
  classical
  let valueSet : Finset ℝ := (Finset.univ : Finset Alloc).image minOf
  let highA : Finset ℝ := valueSet.filter fun u : ℝ => minOf A < u
  have hhigh_card_le : highA.card ≤ Fintype.card Alloc := by
    calc
      highA.card ≤ valueSet.card := by
        exact Finset.card_le_card (by
          intro u hu
          exact (Finset.mem_filter.mp hu).1)
      _ ≤ Fintype.card Alloc := by
        dsimp [valueSet]
        simpa using
          (Finset.card_image_le :
            ((Finset.univ : Finset Alloc).image minOf).card ≤
              (Finset.univ : Finset Alloc).card)
  have hmult_card_le :
      minLoadMultiplicity v (bundleOf A) (minOf A) ≤ Fintype.card Agent := by
    unfold minLoadMultiplicity
    exact Finset.card_le_card (by
      intro i hi
      exact (Finset.mem_filter.mp hi).1)
  have hmul_le :
      highA.card * (Fintype.card Agent + 1) ≤
        Fintype.card Alloc * (Fintype.card Agent + 1) :=
    Nat.mul_le_mul_right (Fintype.card Agent + 1) hhigh_card_le
  have hsum_le :
      highA.card * (Fintype.card Agent + 1) +
          minLoadMultiplicity v (bundleOf A) (minOf A) ≤
        Fintype.card Alloc * (Fintype.card Agent + 1) +
          Fintype.card Agent :=
    Nat.add_le_add hmul_le hmult_card_le
  simpa [minLoadTiePotential, valueSet, highA] using hsum_le

/--
Global finite-descent potential for Claim 3.4: count the goods currently held
by overfull bundles, i.e. bundles whose load is above `2L`.
-/
def overfullBundleCardPotential {Agent Item : Type*} [Fintype Agent]
    (v : Item → ℝ) (L : ℝ) (bundle : Agent → Finset Item) : ℕ :=
  ∑ i : Agent,
    if 2 * L < commonLoad v (bundle i) then (bundle i).card else 0

/-- If no bundle is above `2L`, the overfull-bundle potential is zero. -/
theorem overfullBundleCardPotential_eq_zero_of_no_high
    {Agent Item : Type*} [Fintype Agent]
    {v : Item → ℝ} {L : ℝ} {bundle : Agent → Finset Item}
    (hno_high : ∀ i : Agent, ¬ 2 * L < commonLoad v (bundle i)) :
    overfullBundleCardPotential v L bundle = 0 := by
  simp [overfullBundleCardPotential, hno_high]

/-- Two no-high allocations have the same zero overfull-bundle potential. -/
theorem overfullBundleCardPotential_eq_of_no_high
    {Agent Item : Type*} [Fintype Agent]
    {v : Item → ℝ} {L : ℝ}
    {bundleA bundleB : Agent → Finset Item}
    (hno_high_A : ∀ i : Agent, ¬ 2 * L < commonLoad v (bundleA i))
    (hno_high_B : ∀ i : Agent, ¬ 2 * L < commonLoad v (bundleB i)) :
    overfullBundleCardPotential v L bundleB =
      overfullBundleCardPotential v L bundleA := by
  rw [overfullBundleCardPotential_eq_zero_of_no_high hno_high_B,
    overfullBundleCardPotential_eq_zero_of_no_high hno_high_A]

/--
If a finite bundle has load above `2L`, every item has nonnegative value and
every item is smaller than `L`, then the bundle contains at least two goods.
This is the source "at least two goods" fact used before choosing a donor item.
-/
theorem two_le_card_of_commonLoad_gt_two_mul
    {Item : Type*} {v : Item → ℝ} {S : Finset Item} {L : ℝ}
    (hL : 0 < L)
    (hitem_nonneg : ∀ g ∈ S, 0 ≤ v g)
    (hitem_lt : ∀ g ∈ S, v g < L)
    (hload : 2 * L < commonLoad v S) :
    2 ≤ S.card := by
  by_contra hcard_not
  have hcases : S.card = 0 ∨ S.card = 1 := by omega
  rcases hcases with hcard_zero | hcard_one
  · have hS : S = ∅ := Finset.card_eq_zero.mp hcard_zero
    subst S
    simp [commonLoad] at hload
    nlinarith
  · rcases Finset.card_eq_one.mp hcard_one with ⟨g, hgS⟩
    have hg_mem : g ∈ S := by
      simp [hgS]
    have hsum : commonLoad v S = v g := by
      simp [commonLoad, hgS]
    have hg_lt : v g < L := hitem_lt g hg_mem
    rw [hsum] at hload
    nlinarith

/-- A finite bundle with strictly positive common load is nonempty. -/
theorem exists_mem_of_commonLoad_pos
    {Item : Type*} {v : Item → ℝ} {S : Finset Item}
    (hload : 0 < commonLoad v S) :
    ∃ g : Item, g ∈ S := by
  by_contra hnone
  have hS : S = ∅ := by
    ext g
    constructor
    · intro hg
      exact False.elim (hnone ⟨g, hg⟩)
    · simp
  subst S
  simp [commonLoad] at hload

/-- A nonnegative finite bundle with strictly positive common load has a positive item. -/
theorem exists_pos_mem_of_commonLoad_pos_of_nonneg
    {Item : Type*} {v : Item → ℝ} {S : Finset Item}
    (hload : 0 < commonLoad v S)
    (hnonneg : ∀ g ∈ S, 0 ≤ v g) :
    ∃ g : Item, g ∈ S ∧ 0 < v g := by
  classical
  by_contra hnone
  have hzero_terms : ∀ g ∈ S, v g = 0 := by
    intro g hg
    have hnonpos : v g ≤ 0 := by
      exact le_of_not_gt (by
        intro hg_pos
        exact hnone ⟨g, hg, hg_pos⟩)
    exact le_antisymm hnonpos (hnonneg g hg)
  have hsum_zero : S.sum v = 0 := by
    exact Finset.sum_eq_zero hzero_terms
  have hload_zero : commonLoad v S = 0 := by
    simpa [commonLoad] using hsum_zero
  nlinarith

/--
If the total load is `#agents * L`, some agent has load at most the average
scale `L`.
-/
theorem exists_load_le_of_sum_eq_card_mul
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    {load : Agent → ℝ} {L : ℝ}
    (hsum : (∑ i : Agent, load i) = (Fintype.card Agent : ℝ) * L) :
    ∃ i : Agent, load i ≤ L := by
  classical
  by_contra hnone
  have hlt : ∀ i : Agent, L < load i := by
    intro i
    exact lt_of_not_ge (by intro hi; exact hnone ⟨i, hi⟩)
  have hsum_lt :
      (∑ _i : Agent, L) < ∑ i : Agent, load i := by
    refine Finset.sum_lt_sum (fun i _hi => le_of_lt (hlt i)) ?_
    exact ⟨Classical.choice (inferInstance : Nonempty Agent),
      Finset.mem_univ _, hlt (Classical.choice (inferInstance : Nonempty Agent))⟩
  have hconst : (∑ _i : Agent, L) = (Fintype.card Agent : ℝ) * L := by
    simp [Finset.sum_const, nsmul_eq_mul]
  nlinarith

/-- Concrete minimum common load over all agents in a finite allocation. -/
noncomputable def minCommonLoad
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    (v : Item → ℝ) (bundle : Agent → Finset Item) : ℝ :=
  ((Finset.univ : Finset Agent).image fun i => commonLoad v (bundle i)).min'
    ((Finset.univ_nonempty : (Finset.univ : Finset Agent).Nonempty).image _)

/-- Concrete maximum common load over all agents in a finite allocation. -/
noncomputable def maxCommonLoad
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    (v : Item → ℝ) (bundle : Agent → Finset Item) : ℝ :=
  ((Finset.univ : Finset Agent).image fun i => commonLoad v (bundle i)).max'
    ((Finset.univ_nonempty : (Finset.univ : Finset Agent).Nonempty).image _)

/-- The concrete minimum load is a lower bound for every bundle load. -/
theorem minCommonLoad_le
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    {v : Item → ℝ} {bundle : Agent → Finset Item} (i : Agent) :
    minCommonLoad v bundle ≤ commonLoad v (bundle i) := by
  classical
  unfold minCommonLoad
  exact
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The concrete minimum load is attained by some agent. -/
theorem exists_commonLoad_eq_minCommonLoad
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    {v : Item → ℝ} {bundle : Agent → Finset Item} :
    ∃ i : Agent, commonLoad v (bundle i) = minCommonLoad v bundle := by
  classical
  unfold minCommonLoad
  have hmem :
      ((Finset.univ : Finset Agent).image fun i => commonLoad v (bundle i)).min'
          ((Finset.univ_nonempty : (Finset.univ : Finset Agent).Nonempty).image _) ∈
        ((Finset.univ : Finset Agent).image fun i => commonLoad v (bundle i)) :=
    Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨i, _hi, hload⟩
  exact ⟨i, hload⟩

/-- A finite bundle has positive common load if all its goods are nonnegative and one is positive. -/
theorem commonLoad_pos_of_exists_pos_of_nonneg
    {Item : Type*} [DecidableEq Item] {v : Item → ℝ} {S : Finset Item}
    (hpos : ∃ g : Item, g ∈ S ∧ 0 < v g)
    (hnonneg : ∀ g : Item, g ∈ S → 0 ≤ v g) :
    0 < commonLoad v S := by
  rcases hpos with ⟨g, hg, hvg⟩
  unfold commonLoad
  rw [← Finset.sum_erase_add _ _ hg]
  have hsum_nonneg : 0 ≤ (S.erase g).sum v := by
    exact Finset.sum_nonneg (by
      intro x hx
      exact hnonneg x (Finset.erase_subset g S hx))
  linarith

/-- If every finite bundle has positive common load, then the concrete minimum load is positive. -/
theorem minCommonLoad_pos_of_forall_commonLoad_pos
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    {v : Item → ℝ} {bundle : Agent → Finset Item}
    (hloads : ∀ i : Agent, 0 < commonLoad v (bundle i)) :
    0 < minCommonLoad v bundle := by
  rcases exists_commonLoad_eq_minCommonLoad (v := v) (bundle := bundle) with
    ⟨i, hi⟩
  rw [← hi]
  exact hloads i

/--
Concrete sufficient condition for the positive-minimum premise in Claim 3.4:
every bundle contains one positive good and all goods in bundles are
nonnegative.
-/
theorem minCommonLoad_pos_of_each_bundle_has_pos_good
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Item]
    {v : Item → ℝ} {bundle : Agent → Finset Item}
    (hpos : ∀ i : Agent, ∃ g : Item, g ∈ bundle i ∧ 0 < v g)
    (hnonneg : ∀ i : Agent, ∀ g : Item, g ∈ bundle i → 0 ≤ v g) :
    0 < minCommonLoad v bundle := by
  exact
    minCommonLoad_pos_of_forall_commonLoad_pos
      (v := v) (bundle := bundle)
      (fun i =>
        commonLoad_pos_of_exists_pos_of_nonneg
          (v := v) (S := bundle i) (hpos i) (hnonneg i))

/-- The concrete maximum load is an upper bound for every bundle load. -/
theorem commonLoad_le_maxCommonLoad
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    {v : Item → ℝ} {bundle : Agent → Finset Item} (i : Agent) :
    commonLoad v (bundle i) ≤ maxCommonLoad v bundle := by
  classical
  unfold maxCommonLoad
  let loads : Finset ℝ :=
    (Finset.univ : Finset Agent).image fun j => commonLoad v (bundle j)
  have hi : commonLoad v (bundle i) ∈ loads :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  exact Finset.le_max' loads (commonLoad v (bundle i)) hi

/-- The concrete maximum load is attained by some agent. -/
theorem exists_commonLoad_eq_maxCommonLoad
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    {v : Item → ℝ} {bundle : Agent → Finset Item} :
    ∃ i : Agent, commonLoad v (bundle i) = maxCommonLoad v bundle := by
  classical
  unfold maxCommonLoad
  have hmem :
      ((Finset.univ : Finset Agent).image fun i => commonLoad v (bundle i)).max'
          ((Finset.univ_nonempty : (Finset.univ : Finset Agent).Nonempty).image _) ∈
        ((Finset.univ : Finset Agent).image fun i => commonLoad v (bundle i)) :=
    Finset.max'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨i, _hi, hload⟩
  exact ⟨i, hload⟩

/--
If `source` is above `2L` and the total load has average `L`, there is a
distinct target bundle whose load is at most `L`.
-/
theorem exists_distinct_target_load_le_of_high_source
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    {load : Agent → ℝ} {source : Agent} {L : ℝ}
    (hL : 0 < L)
    (hsum : (∑ i : Agent, load i) = (Fintype.card Agent : ℝ) * L)
    (hsource_high : 2 * L < load source) :
    ∃ target : Agent, target ≠ source ∧ load target ≤ L := by
  obtain ⟨target, htarget_le⟩ :=
    exists_load_le_of_sum_eq_card_mul (load := load) hsum
  refine ⟨target, ?_, htarget_le⟩
  intro htarget_source
  subst target
  nlinarith

/--
Concrete witness selection for the Claim 3.4 high-source local move: from an
overfull source bundle and an allocation whose average load is `L`, choose a
distinct target of load at most `L` and a fresh good in the source bundle.
-/
theorem exists_target_good_of_high_source_average
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ} {L : ℝ}
    {source : Agent}
    (hL : 0 < L)
    (havg :
      (∑ i : Agent, commonLoad v (bundle i)) =
        (Fintype.card Agent : ℝ) * L)
    (hsource_high : 2 * L < commonLoad v (bundle source))
    (hitem_nonneg : ∀ g ∈ bundle source, 0 ≤ v g)
    (hitem_lt : ∀ g ∈ bundle source, v g < L)
    (hunique :
      ∀ {i j : Agent} {g : Item}, g ∈ bundle i → g ∈ bundle j → i = j) :
    ∃ target : Agent, ∃ g : Item,
      source ≠ target ∧
      g ∈ bundle source ∧
      g ∉ bundle target ∧
      commonLoad v (bundle target) ≤ L ∧
      0 ≤ v g ∧ v g < L := by
  obtain ⟨target, htarget_ne_source, htarget_le⟩ :=
    exists_distinct_target_load_le_of_high_source
      (load := fun i : Agent => commonLoad v (bundle i))
      hL havg hsource_high
  have hsource_load_pos : 0 < commonLoad v (bundle source) := by
    nlinarith
  obtain ⟨g, hg_source⟩ :=
    exists_mem_of_commonLoad_pos (v := v) (S := bundle source)
      hsource_load_pos
  have hsource_ne_target : source ≠ target := htarget_ne_source.symm
  have hg_target : g ∉ bundle target := by
    intro hg_target
    exact hsource_ne_target (hunique hg_source hg_target)
  exact
    ⟨target, g, hsource_ne_target, hg_source, hg_target, htarget_le,
      hitem_nonneg g hg_source, hitem_lt g hg_source⟩

/--
If one bundle is at most half the average load, while all loads are bounded
above by `maxLoad`, then `maxLoad` is strictly above the average.
-/
theorem maxLoad_gt_average_of_low_min_average
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    {load : Agent → ℝ} {L minLoad maxLoad : ℝ} {target : Agent}
    (hL : 0 < L)
    (havg : (∑ i : Agent, load i) = (Fintype.card Agent : ℝ) * L)
    (htarget_min : load target = minLoad)
    (hmin_low : minLoad ≤ L / 2)
    (hle_max : ∀ i : Agent, load i ≤ maxLoad) :
    L < maxLoad := by
  have htarget_lt_L : load target < L := by
    rw [htarget_min]
    nlinarith
  by_contra hnot
  have hmax_le_L : maxLoad ≤ L := le_of_not_gt hnot
  have hle_L : ∀ i : Agent, load i ≤ L := by
    intro i
    exact le_trans (hle_max i) hmax_le_L
  have hsum_lt :
      (∑ i : Agent, load i) < ∑ _i : Agent, L := by
    refine Finset.sum_lt_sum (fun i _hi => hle_L i) ?_
    exact ⟨target, Finset.mem_univ target, htarget_lt_L⟩
  have hconst : (∑ _i : Agent, L) = (Fintype.card Agent : ℝ) * L := by
    simp [Finset.sum_const, nsmul_eq_mul]
  nlinarith

/--
Low-only Claim 3.4 arithmetic: if a target bundle attains a load at most
`L / 2` while the allocation has average load `L`, then a max-load source
bundle contains an item small enough to move toward the low target without
overshooting the old source-target gap.

This is the local witness needed by a later finite tie-breaker proof for the
case where no bundle is above `2L`, so the overfull-bundle potential is already
zero.
-/
theorem exists_item_lt_max_sub_min_of_low_min_average
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ}
    {L minLoad maxLoad : ℝ} {source target : Agent}
    (hL : 0 < L)
    (havg :
      (∑ i : Agent, commonLoad v (bundle i)) =
        (Fintype.card Agent : ℝ) * L)
    (htarget_min : commonLoad v (bundle target) = minLoad)
    (hsource_max : commonLoad v (bundle source) = maxLoad)
    (hmin_low : minLoad ≤ L / 2)
    (_hmin_le : ∀ i : Agent, minLoad ≤ commonLoad v (bundle i))
    (hle_max : ∀ i : Agent, commonLoad v (bundle i) ≤ maxLoad)
    (hitem_lt : ∀ g ∈ bundle source, v g < L) :
    ∃ g : Item, g ∈ bundle source ∧ v g < maxLoad - minLoad := by
  classical
  have hmax_gt_L : L < maxLoad :=
    maxLoad_gt_average_of_low_min_average
      (load := fun i : Agent => commonLoad v (bundle i))
      hL havg htarget_min hmin_low hle_max
  have hsource_pos : 0 < commonLoad v (bundle source) := by
    rw [hsource_max]
    nlinarith
  have hsource_card_two : 2 ≤ (bundle source).card := by
    by_contra hnot
    have hcases : (bundle source).card = 0 ∨ (bundle source).card = 1 := by
      omega
    rcases hcases with hzero | hone
    · have hS : bundle source = ∅ := Finset.card_eq_zero.mp hzero
      have hload_zero : commonLoad v (bundle source) = 0 := by
        simp [commonLoad, hS]
      rw [hsource_max] at hload_zero
      nlinarith
    · rcases Finset.card_eq_one.mp hone with ⟨g, hgS⟩
      have hg_mem : g ∈ bundle source := by
        simp [hgS]
      have hload_eq : commonLoad v (bundle source) = v g := by
        simp [commonLoad, hgS]
      have hg_lt : v g < L := hitem_lt g hg_mem
      rw [hsource_max] at hload_eq
      nlinarith
  by_contra hnone
  push Not at hnone
  let d : ℝ := maxLoad - minLoad
  have hd_pos : 0 < d := by
    dsimp [d]
    nlinarith
  have hitem_ge : ∀ g ∈ bundle source, d ≤ v g := by
    intro g hg
    exact hnone g hg
  have hsum_lower :
      (bundle source).card * d ≤ commonLoad v (bundle source) := by
    calc
      (bundle source).card * d =
          (bundle source).sum (fun _g => d) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (bundle source).sum v :=
          Finset.sum_le_sum (fun g hg => hitem_ge g hg)
      _ = commonLoad v (bundle source) := rfl
  have htwo_d_le_card_d : 2 * d ≤ (bundle source).card * d := by
    have hcard_real : (2 : ℝ) ≤ ((bundle source).card : ℝ) := by
      exact_mod_cast hsource_card_two
    nlinarith
  have htwo_d_le_max : 2 * d ≤ maxLoad := by
    rw [← hsource_max]
    exact le_trans htwo_d_le_card_d hsum_lower
  have hmax_le_L : maxLoad ≤ L := by
    dsimp [d] at htwo_d_le_max
    nlinarith
  exact (not_lt_of_ge hmax_le_L) hmax_gt_L

/--
Low-only Claim 3.4 arithmetic with a strict move: under nonnegative item
values, the small max-bundle item can be chosen with positive value. This is
the ingredient needed for a later finite tie-breaker proof, where moving a
zero-valued item would not strictly improve the minimum-load rank.
-/
theorem exists_pos_item_lt_max_sub_min_of_low_min_average
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ}
    {L minLoad maxLoad : ℝ} {source target : Agent}
    (hL : 0 < L)
    (havg :
      (∑ i : Agent, commonLoad v (bundle i)) =
        (Fintype.card Agent : ℝ) * L)
    (htarget_min : commonLoad v (bundle target) = minLoad)
    (hsource_max : commonLoad v (bundle source) = maxLoad)
    (hmin_low : minLoad ≤ L / 2)
    (hmin_le : ∀ i : Agent, minLoad ≤ commonLoad v (bundle i))
    (hle_max : ∀ i : Agent, commonLoad v (bundle i) ≤ maxLoad)
    (hitem_nonneg : ∀ g ∈ bundle source, 0 ≤ v g)
    (hitem_lt : ∀ g ∈ bundle source, v g < L) :
    ∃ g : Item, g ∈ bundle source ∧ 0 < v g ∧
      v g < maxLoad - minLoad := by
  classical
  let positiveSource : Finset Item :=
    (bundle source).filter fun g => 0 < v g
  have hmax_gt_L : L < maxLoad :=
    maxLoad_gt_average_of_low_min_average
      (load := fun i : Agent => commonLoad v (bundle i))
      hL havg htarget_min hmin_low hle_max
  let d : ℝ := maxLoad - minLoad
  have hd_pos : 0 < d := by
    dsimp [d]
    nlinarith
  have hpositive_sum_eq :
      positiveSource.sum v = commonLoad v (bundle source) := by
    dsimp [positiveSource]
    have hsubset :
        (bundle source).filter (fun g => 0 < v g) ⊆ bundle source := by
      intro g hg
      exact (Finset.mem_filter.mp hg).1
    have hsum_subset :
        ((bundle source).filter fun g => 0 < v g).sum v =
          (bundle source).sum v := by
      exact
        Finset.sum_subset hsubset (by
          intro g hg_source hg_not_pos
          have hnot : ¬ 0 < v g := by
            intro hg_pos
            exact hg_not_pos (Finset.mem_filter.mpr ⟨hg_source, hg_pos⟩)
          exact le_antisymm (le_of_not_gt hnot) (hitem_nonneg g hg_source))
    simpa [commonLoad] using hsum_subset
  have hpositive_nonempty : positiveSource.Nonempty := by
    by_contra hempty
    have hpositive_empty : positiveSource = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hsum_zero : positiveSource.sum v = 0 := by
      simp [hpositive_empty]
    have hload_zero : commonLoad v (bundle source) = 0 := by
      rw [← hpositive_sum_eq, hsum_zero]
    rw [hsource_max] at hload_zero
    nlinarith
  by_contra hnone
  have hpos_ge :
      ∀ g ∈ positiveSource, d ≤ v g := by
    intro g hg_positive
    have hg_source : g ∈ bundle source := (Finset.mem_filter.mp hg_positive).1
    have hg_pos : 0 < v g := (Finset.mem_filter.mp hg_positive).2
    by_contra hnot_ge
    exact hnone ⟨g, hg_source, hg_pos, lt_of_not_ge hnot_ge⟩
  by_cases hcard_one_or_zero : positiveSource.card < 2
  · have hcard_one : positiveSource.card = 1 := by
      have hcard_pos : 0 < positiveSource.card :=
        Finset.card_pos.mpr hpositive_nonempty
      omega
    rcases Finset.card_eq_one.mp hcard_one with ⟨g, hg_eq⟩
    have hg_positive : g ∈ positiveSource := by
      simp [hg_eq]
    have hg_source : g ∈ bundle source := (Finset.mem_filter.mp hg_positive).1
    have hsum_eq : positiveSource.sum v = v g := by
      simp [hg_eq]
    have hsource_load_eq : commonLoad v (bundle source) = v g := by
      rw [← hpositive_sum_eq, hsum_eq]
    have hg_lt : v g < L := hitem_lt g hg_source
    rw [hsource_max] at hsource_load_eq
    nlinarith
  · have hcard_two : 2 ≤ positiveSource.card := by omega
    have hsum_lower :
        positiveSource.card * d ≤ positiveSource.sum v := by
      calc
        positiveSource.card * d = positiveSource.sum (fun _g => d) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ positiveSource.sum v :=
          Finset.sum_le_sum (fun g hg => hpos_ge g hg)
    have htwo_d_le_card_d : 2 * d ≤ positiveSource.card * d := by
      have hcard_real : (2 : ℝ) ≤ (positiveSource.card : ℝ) := by
        exact_mod_cast hcard_two
      nlinarith
    have htwo_d_le_max : 2 * d ≤ maxLoad := by
      rw [← hsource_max, ← hpositive_sum_eq]
      exact le_trans htwo_d_le_card_d hsum_lower
    dsimp [d] at htwo_d_le_max
    have hmax_le_L : maxLoad ≤ L := by nlinarith
    exact (not_lt_of_ge hmax_le_L) hmax_gt_L

/--
Fixed-minimum tie-breaker for the low-only Claim 3.4 route: after moving a
positive small item from a max-load bundle to a min-load bundle, the number of
bundles attaining the old minimum strictly decreases, provided the old minimum
is still the relevant minimum value after the move.

This is the first finite tie-breaker layer for the case where the overfull
potential is already zero.
-/
theorem minLoadMultiplicity_decreases_of_low_only_move_same_min
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ}
    {source target : Agent} {g : Item} {minLoad maxLoad : ℝ}
    (hmin_le : ∀ i : Agent, minLoad ≤ commonLoad v (bundle i))
    (htarget_min : commonLoad v (bundle target) = minLoad)
    (hsource_max : commonLoad v (bundle source) = maxLoad)
    (hsource_ne_target : source ≠ target)
    (hg_source : g ∈ bundle source)
    (hg_target : g ∉ bundle target)
    (hg_pos : 0 < v g)
    (hg_gap : v g < maxLoad - minLoad) :
    minLoadMultiplicity v (moveBundle bundle source target g) minLoad <
      minLoadMultiplicity v bundle minLoad := by
  classical
  let moved := moveBundle bundle source target g
  let oldMinSet : Finset Agent :=
    (Finset.univ : Finset Agent).filter
      (fun i : Agent => commonLoad v (bundle i) = minLoad)
  let newMinSet : Finset Agent :=
    (Finset.univ : Finset Agent).filter
      (fun i : Agent => commonLoad v (moved i) = minLoad)
  have hsource_new :
      commonLoad v (moved source) = maxLoad - v g := by
    have hmoved_source : moved source = (bundle source).erase g := by
      simp [moved, moveBundle]
    simpa [hmoved_source, hsource_max] using
      commonLoad_erase (v := v) (S := bundle source) (g := g) hg_source
  have htarget_new :
      commonLoad v (moved target) = minLoad + v g := by
    have htarget_ne_source : target ≠ source := hsource_ne_target.symm
    have hmoved_target : moved target = insert g (bundle target) := by
      simp [moved, moveBundle, htarget_ne_source]
    simpa [hmoved_target, htarget_min] using
      commonLoad_insert (v := v) (S := bundle target) (g := g) hg_target
  have hnew_subset_old : newMinSet ⊆ oldMinSet := by
    intro i hi_new
    have hi_new_eq : commonLoad v (moved i) = minLoad :=
      (Finset.mem_filter.mp hi_new).2
    by_cases hisource : i = source
    · subst i
      have hsource_gt : minLoad < commonLoad v (moved source) := by
        rw [hsource_new]
        nlinarith
      exact False.elim (ne_of_gt hsource_gt hi_new_eq)
    · by_cases hitarget : i = target
      · subst i
        have htarget_gt : minLoad < commonLoad v (moved target) := by
          rw [htarget_new]
          nlinarith
        exact False.elim (ne_of_gt htarget_gt hi_new_eq)
      · have hmoved_i : moved i = bundle i := by
          simp [moved, moveBundle, hisource, hitarget]
        have hi_old_eq : commonLoad v (bundle i) = minLoad := by
          simpa [hmoved_i] using hi_new_eq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi_old_eq⟩
  have htarget_old : target ∈ oldMinSet := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ target, htarget_min⟩
  have htarget_not_new : target ∉ newMinSet := by
    intro htarget_mem
    have htarget_eq : commonLoad v (moved target) = minLoad :=
      (Finset.mem_filter.mp htarget_mem).2
    have htarget_gt : minLoad < commonLoad v (moved target) := by
      rw [htarget_new]
      nlinarith
    exact ne_of_gt htarget_gt htarget_eq
  have hnew_ne_old : newMinSet ≠ oldMinSet := by
    intro h_eq
    exact htarget_not_new (by simpa [h_eq] using htarget_old)
  have hssub : newMinSet ⊂ oldMinSet :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hnew_subset_old, hnew_ne_old⟩
  have hcard_lt : newMinSet.card < oldMinSet.card :=
    Finset.card_lt_card hssub
  simpa [minLoadMultiplicity, moved, oldMinSet, newMinSet] using hcard_lt

/--
If the actual minimum load increases, the finite rank part of
`minLoadTiePotential` strictly decreases, regardless of the new minimum
multiplicity.
-/
theorem minLoadTiePotential_decreases_of_min_increases
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc]
    (v : Item → ℝ) (bundleOf : Alloc → Agent → Finset Item)
    (minOf : Alloc → ℝ) {A B : Alloc}
    (hmin_lt : minOf A < minOf B) :
    minLoadTiePotential v bundleOf minOf B <
      minLoadTiePotential v bundleOf minOf A := by
  classical
  let valueSet : Finset ℝ := (Finset.univ : Finset Alloc).image minOf
  let highA : Finset ℝ := valueSet.filter fun u : ℝ => minOf A < u
  let highB : Finset ℝ := valueSet.filter fun u : ℝ => minOf B < u
  have hsubset : highB ⊆ highA := by
    intro u hu
    have hu_value : u ∈ valueSet := (Finset.mem_filter.mp hu).1
    have hu_gt_B : minOf B < u := (Finset.mem_filter.mp hu).2
    exact Finset.mem_filter.mpr ⟨hu_value, lt_trans hmin_lt hu_gt_B⟩
  have hB_mem_highA : minOf B ∈ highA := by
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨B, Finset.mem_univ B, rfl⟩, hmin_lt⟩
  have hB_not_highB : minOf B ∉ highB := by
    intro hmem
    exact (lt_irrefl (minOf B)) (Finset.mem_filter.mp hmem).2
  have hne : highB ≠ highA := by
    intro h_eq
    exact hB_not_highB (by simpa [h_eq] using hB_mem_highA)
  have hssub : highB ⊂ highA :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩
  have hcard_lt : highB.card < highA.card :=
    Finset.card_lt_card hssub
  have hmultiplicity_le :
      minLoadMultiplicity v (bundleOf B) (minOf B) ≤ Fintype.card Agent := by
    unfold minLoadMultiplicity
    exact Finset.card_le_card (by
      intro i hi
      exact (Finset.mem_filter.mp hi).1)
  have hcard_succ_le : highB.card + 1 ≤ highA.card :=
    Nat.succ_le_of_lt hcard_lt
  have hnext_block :
      (highB.card + 1) * (Fintype.card Agent + 1) =
        highB.card * (Fintype.card Agent + 1) +
          (Fintype.card Agent + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
  have hleft_lt_next :
      highB.card * (Fintype.card Agent + 1) +
          minLoadMultiplicity v (bundleOf B) (minOf B) <
        (highB.card + 1) * (Fintype.card Agent + 1) := by
    rw [hnext_block]
    omega
  have hnext_le_highA :
      (highB.card + 1) * (Fintype.card Agent + 1) ≤
        highA.card * (Fintype.card Agent + 1) :=
    Nat.mul_le_mul_right (Fintype.card Agent + 1) hcard_succ_le
  have hpot :
      highB.card * (Fintype.card Agent + 1) +
          minLoadMultiplicity v (bundleOf B) (minOf B) <
        highA.card * (Fintype.card Agent + 1) +
          minLoadMultiplicity v (bundleOf A) (minOf A) := by
    exact
      lt_of_lt_of_le hleft_lt_next
        (le_trans hnext_le_highA (Nat.le_add_right _ _))
  simpa [minLoadTiePotential, valueSet, highA, highB] using hpot

/-- If the minimum value stays fixed, decreasing its multiplicity decreases the tie potential. -/
theorem minLoadTiePotential_decreases_of_same_min_multiplicity
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc]
    (v : Item → ℝ) (bundleOf : Alloc → Agent → Finset Item)
    (minOf : Alloc → ℝ) {A B : Alloc}
    (hmin_eq : minOf B = minOf A)
    (hmult :
      minLoadMultiplicity v (bundleOf B) (minOf B) <
        minLoadMultiplicity v (bundleOf A) (minOf A)) :
    minLoadTiePotential v bundleOf minOf B <
      minLoadTiePotential v bundleOf minOf A := by
  simpa [minLoadTiePotential, hmin_eq] using hmult

/--
Combined low-only tie-potential descent.  Moving a positive small item from a
max-load bundle to a min-load bundle either raises the finite minimum load
rank, or preserves that rank and strictly decreases the number of bundles
attaining it.
-/
theorem minLoadTiePotential_decreases_of_low_only_move
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc] [Nonempty Agent]
    [DecidableEq Agent] [DecidableEq Item]
    {bundleOf : Alloc → Agent → Finset Item} {v : Item → ℝ}
    {minOf : Alloc → ℝ} {A B : Alloc}
    {source target : Agent} {g : Item} {minLoad maxLoad : ℝ}
    (hmin_lower :
      ∀ C : Alloc, ∀ i : Agent, minOf C ≤ commonLoad v (bundleOf C i))
    (hmin_attains :
      ∀ C : Alloc, ∃ i : Agent, commonLoad v (bundleOf C i) = minOf C)
    (hminA : minOf A = minLoad)
    (htarget_min : commonLoad v (bundleOf A target) = minLoad)
    (hsource_max : commonLoad v (bundleOf A source) = maxLoad)
    (hsource_ne_target : source ≠ target)
    (hg_source : g ∈ bundleOf A source)
    (hg_target : g ∉ bundleOf A target)
    (hg_pos : 0 < v g)
    (hg_gap : v g < maxLoad - minLoad)
    (hbundle_B :
      bundleOf B = moveBundle (bundleOf A) source target g) :
    minLoadTiePotential v bundleOf minOf B <
      minLoadTiePotential v bundleOf minOf A := by
  classical
  let moved := moveBundle (bundleOf A) source target g
  have hsource_new :
      commonLoad v (moved source) = maxLoad - v g := by
    have hmoved_source : moved source = (bundleOf A source).erase g := by
      simp [moved, moveBundle]
    simpa [hmoved_source, hsource_max] using
      commonLoad_erase (v := v) (S := bundleOf A source) (g := g) hg_source
  have htarget_new :
      commonLoad v (moved target) = minLoad + v g := by
    have htarget_ne_source : target ≠ source := hsource_ne_target.symm
    have hmoved_target : moved target = insert g (bundleOf A target) := by
      simp [moved, moveBundle, htarget_ne_source]
    simpa [hmoved_target, htarget_min] using
      commonLoad_insert (v := v) (S := bundleOf A target) (g := g) hg_target
  have hB_loads_ge : ∀ i : Agent, minLoad ≤ commonLoad v (bundleOf B i) := by
    intro i
    rw [hbundle_B]
    by_cases hisource : i = source
    · subst i
      rw [hsource_new]
      nlinarith
    · by_cases hitarget : i = target
      · subst i
        rw [htarget_new]
        nlinarith
      · have hmoved_i : moved i = bundleOf A i := by
          simp [moved, moveBundle, hisource, hitarget]
        change minLoad ≤ commonLoad v (moved i)
        simpa [hmoved_i] using (by
          have hold := hmin_lower A i
          rw [hminA] at hold
          exact hold)
  obtain ⟨iB, hiB⟩ := hmin_attains B
  have hminA_le_minB : minOf A ≤ minOf B := by
    rw [hminA, ← hiB]
    exact hB_loads_ge iB
  rcases lt_or_eq_of_le hminA_le_minB with hmin_lt | hmin_eq
  · exact
      minLoadTiePotential_decreases_of_min_increases
        v bundleOf minOf hmin_lt
  · have hmult_raw :
        minLoadMultiplicity v (moveBundle (bundleOf A) source target g) minLoad <
          minLoadMultiplicity v (bundleOf A) minLoad :=
      minLoadMultiplicity_decreases_of_low_only_move_same_min
        (bundle := bundleOf A) (v := v)
        (source := source) (target := target) (g := g)
        (minLoad := minLoad) (maxLoad := maxLoad)
        (by
          intro i
          have hold := hmin_lower A i
          rw [hminA] at hold
          exact hold)
        htarget_min hsource_max hsource_ne_target hg_source hg_target
        hg_pos hg_gap
    have hminB : minOf B = minLoad := by
      rw [← hmin_eq, hminA]
    have hmult :
        minLoadMultiplicity v (bundleOf B) (minOf B) <
          minLoadMultiplicity v (bundleOf A) (minOf A) := by
      simpa [hbundle_B, hminB, hminA] using hmult_raw
    exact
      minLoadTiePotential_decreases_of_same_min_multiplicity
        v bundleOf minOf hmin_eq.symm hmult

/--
The donor-cardinality potential strictly decreases after moving an item out of
the donor bundle.
-/
theorem donorCardPotential_decreases_of_moveBundle
    {Agent Item : Type*} [DecidableEq Agent] [DecidableEq Item]
    {bundle : Agent → Finset Item} {source target : Agent} {g : Item}
    (hg_source : g ∈ bundle source) :
    donorCardPotential (moveBundle bundle source target g) source <
      donorCardPotential bundle source := by
  simpa [donorCardPotential, moveBundle] using
    Finset.card_erase_lt_of_mem hg_source

/--
The source local move strictly decreases the global overfull-bundle-card
potential: the donor loses one good from an overfull bundle, while the low
target remains below the overfull threshold after receiving a good of value
less than `L`.
-/
theorem overfullBundleCardPotential_decreases_of_moveBundle_low_target_high_source
    {Agent Item : Type*} [Fintype Agent] [DecidableEq Agent] [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ}
    {source target : Agent} {g : Item} {L : ℝ}
    (hsource_ne_target : source ≠ target)
    (hg_source : g ∈ bundle source)
    (hg_target : g ∉ bundle target)
    (hL : 0 < L)
    (htarget_low : commonLoad v (bundle target) < L / 2)
    (hsource_high : 2 * L < commonLoad v (bundle source))
    (hg_lt : v g < L) :
    overfullBundleCardPotential v L (moveBundle bundle source target g) <
      overfullBundleCardPotential v L bundle := by
  classical
  let moved := moveBundle bundle source target g
  let termBefore : Agent → ℕ := fun i =>
    if 2 * L < commonLoad v (bundle i) then (bundle i).card else 0
  let termAfter : Agent → ℕ := fun i =>
    if 2 * L < commonLoad v (moved i) then (moved i).card else 0
  have htarget_not_high : ¬ 2 * L < commonLoad v (bundle target) := by
    nlinarith
  have htarget_after_not_high : ¬ 2 * L < commonLoad v (moved target) := by
    have hload :
        commonLoad v (moved target) = commonLoad v (bundle target) + v g := by
      have htarget_ne_source : target ≠ source := hsource_ne_target.symm
      simpa [moved, moveBundle, htarget_ne_source] using
        commonLoad_insert (v := v) (S := bundle target) (g := g) hg_target
    rw [hload]
    nlinarith
  have hsource_strict : termAfter source < termBefore source := by
    have hbefore : termBefore source = (bundle source).card := by
      simp [termBefore, hsource_high]
    rw [hbefore]
    by_cases hafter_high : 2 * L < commonLoad v (moved source)
    · have hmoved_source : moved source = (bundle source).erase g := by
        simp [moved, moveBundle]
      have hafter_high' : 2 * L < commonLoad v ((bundle source).erase g) := by
        simpa [hmoved_source] using hafter_high
      have hafter : termAfter source = ((bundle source).erase g).card := by
        simp [termAfter, hmoved_source, hafter_high']
      rw [hafter]
      exact Finset.card_erase_lt_of_mem hg_source
    · have hafter : termAfter source = 0 := by
        simp [termAfter, hafter_high]
      rw [hafter]
      exact Finset.card_pos.mpr ⟨g, hg_source⟩
  have hterm_le : ∀ i ∈ (Finset.univ : Finset Agent), termAfter i ≤ termBefore i := by
    intro i _hi
    by_cases hisource : i = source
    · subst i
      exact le_of_lt hsource_strict
    · by_cases hitarget : i = target
      · subst i
        have hbefore : termBefore target = 0 := by
          simp [termBefore, htarget_not_high]
        have hafter : termAfter target = 0 := by
          simp [termAfter, htarget_after_not_high]
        simp [hbefore, hafter]
      · have hmoved : moved i = bundle i := by
          simp [moved, moveBundle, hisource, hitarget]
        simp [termAfter, termBefore, hmoved]
  have hsum :
      (Finset.univ : Finset Agent).sum termAfter <
        (Finset.univ : Finset Agent).sum termBefore := by
    exact
      Finset.sum_lt_sum hterm_le
        ⟨source, Finset.mem_univ source, hsource_strict⟩
  simpa [overfullBundleCardPotential, moved, termAfter, termBefore] using hsum

/--
The same global-potential descent under the weaker high-source condition used
by the source proof: if the receiving bundle has load at most the average
scale `L`, then adding a good of value below `L` cannot make it overfull.
-/
theorem overfullBundleCardPotential_decreases_of_moveBundle_le_average_target_high_source
    {Agent Item : Type*} [Fintype Agent] [DecidableEq Agent] [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ}
    {source target : Agent} {g : Item} {L : ℝ}
    (hsource_ne_target : source ≠ target)
    (hg_source : g ∈ bundle source)
    (hg_target : g ∉ bundle target)
    (hL : 0 < L)
    (htarget_le : commonLoad v (bundle target) ≤ L)
    (hsource_high : 2 * L < commonLoad v (bundle source))
    (hg_lt : v g < L) :
    overfullBundleCardPotential v L (moveBundle bundle source target g) <
      overfullBundleCardPotential v L bundle := by
  classical
  let moved := moveBundle bundle source target g
  let termBefore : Agent → ℕ := fun i =>
    if 2 * L < commonLoad v (bundle i) then (bundle i).card else 0
  let termAfter : Agent → ℕ := fun i =>
    if 2 * L < commonLoad v (moved i) then (moved i).card else 0
  have htarget_not_high : ¬ 2 * L < commonLoad v (bundle target) := by
    nlinarith
  have htarget_after_not_high : ¬ 2 * L < commonLoad v (moved target) := by
    have hload :
        commonLoad v (moved target) = commonLoad v (bundle target) + v g := by
      have htarget_ne_source : target ≠ source := hsource_ne_target.symm
      simpa [moved, moveBundle, htarget_ne_source] using
        commonLoad_insert (v := v) (S := bundle target) (g := g) hg_target
    rw [hload]
    nlinarith
  have hsource_strict : termAfter source < termBefore source := by
    have hbefore : termBefore source = (bundle source).card := by
      simp [termBefore, hsource_high]
    rw [hbefore]
    by_cases hafter_high : 2 * L < commonLoad v (moved source)
    · have hmoved_source : moved source = (bundle source).erase g := by
        simp [moved, moveBundle]
      have hafter_high' : 2 * L < commonLoad v ((bundle source).erase g) := by
        simpa [hmoved_source] using hafter_high
      have hafter : termAfter source = ((bundle source).erase g).card := by
        simp [termAfter, hmoved_source, hafter_high']
      rw [hafter]
      exact Finset.card_erase_lt_of_mem hg_source
    · have hafter : termAfter source = 0 := by
        simp [termAfter, hafter_high]
      rw [hafter]
      exact Finset.card_pos.mpr ⟨g, hg_source⟩
  have hterm_le : ∀ i ∈ (Finset.univ : Finset Agent), termAfter i ≤ termBefore i := by
    intro i _hi
    by_cases hisource : i = source
    · subst i
      exact le_of_lt hsource_strict
    · by_cases hitarget : i = target
      · subst i
        have hbefore : termBefore target = 0 := by
          simp [termBefore, htarget_not_high]
        have hafter : termAfter target = 0 := by
          simp [termAfter, htarget_after_not_high]
        simp [hbefore, hafter]
      · have hmoved : moved i = bundle i := by
          simp [moved, moveBundle, hisource, hitarget]
        simp [termAfter, termBefore, hmoved]
  have hsum :
      (Finset.univ : Finset Agent).sum termAfter <
        (Finset.univ : Finset Agent).sum termBefore := by
    exact
      Finset.sum_lt_sum hterm_le
        ⟨source, Finset.mem_univ source, hsource_strict⟩
  simpa [overfullBundleCardPotential, moved, termAfter, termBefore] using hsum

/--
Bundle-level loads after `moveBundle` agree with the scalar `moveLoad` vector.
The target freshness premise is the usual allocation invariant that the moved
good is not already in the receiving bundle.
-/
theorem commonLoad_moveBundle_eq_moveLoad
    {Agent Item : Type*} [DecidableEq Agent] [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ}
    {source target : Agent} {g : Item}
    (_hsource_ne_target : source ≠ target)
    (hg_source : g ∈ bundle source)
    (hg_target : g ∉ bundle target) :
    ∀ i : Agent,
      commonLoad v (moveBundle bundle source target g i) =
        moveLoad (fun j => commonLoad v (bundle j)) source target (v g) i := by
  intro i
  by_cases hisource : i = source
  · subst i
    simpa [moveBundle, moveLoad] using
      commonLoad_erase (v := v) (S := bundle source) (g := g) hg_source
  · by_cases hitarget : i = target
    · subst i
      simpa [moveBundle, moveLoad, hisource] using
        commonLoad_insert (v := v) (S := bundle target) (g := g) hg_target
    · simp [moveBundle, moveLoad, hisource, hitarget]

/--
A positive low-only move from a max-load bundle to a min-load bundle keeps every
new load at most the old maximum, provided the moved item is smaller than the
old max-min gap.
-/
theorem commonLoad_moveBundle_le_max_of_low_only_move
    {Agent Item : Type*} [DecidableEq Agent] [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ}
    {source target : Agent} {g : Item} {minLoad maxLoad : ℝ}
    (hsource_max : commonLoad v (bundle source) = maxLoad)
    (htarget_min : commonLoad v (bundle target) = minLoad)
    (hsource_ne_target : source ≠ target)
    (hg_source : g ∈ bundle source)
    (hg_target : g ∉ bundle target)
    (hg_nonneg : 0 ≤ v g)
    (hg_gap : v g < maxLoad - minLoad)
    (hle_max : ∀ i : Agent, commonLoad v (bundle i) ≤ maxLoad) :
    ∀ i : Agent,
      commonLoad v (moveBundle bundle source target g i) ≤ maxLoad := by
  intro i
  let moved := moveBundle bundle source target g
  by_cases hisource : i = source
  · subst i
    have hmoved_source : moved source = (bundle source).erase g := by
      simp [moved, moveBundle]
    have hsource_new :
        commonLoad v (moved source) = maxLoad - v g := by
      simpa [hmoved_source, hsource_max] using
        commonLoad_erase (v := v) (S := bundle source) (g := g) hg_source
    rw [hsource_new]
    linarith
  · by_cases hitarget : i = target
    · subst i
      have htarget_ne_source : target ≠ source := hsource_ne_target.symm
      have hmoved_target : moved target = insert g (bundle target) := by
        simp [moved, moveBundle, htarget_ne_source]
      have htarget_new :
          commonLoad v (moved target) = minLoad + v g := by
        simpa [hmoved_target, htarget_min] using
          commonLoad_insert (v := v) (S := bundle target) (g := g) hg_target
      rw [htarget_new]
      linarith
    · have hmoved_i : moved i = bundle i := by
        simp [moved, moveBundle, hisource, hitarget]
      simpa [moved, hmoved_i] using hle_max i

/--
In the low-only branch, if the old maximum is at most `2L`, moving the
max-to-min small item preserves the zero overfull-bundle potential.
-/
theorem overfullBundleCardPotential_eq_of_low_only_move_no_high
    {Agent Item : Type*} [Fintype Agent] [DecidableEq Agent] [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ}
    {source target : Agent} {g : Item} {minLoad maxLoad L : ℝ}
    (hmax_le_twoL : maxLoad ≤ 2 * L)
    (hsource_max : commonLoad v (bundle source) = maxLoad)
    (htarget_min : commonLoad v (bundle target) = minLoad)
    (hsource_ne_target : source ≠ target)
    (hg_source : g ∈ bundle source)
    (hg_target : g ∉ bundle target)
    (hg_nonneg : 0 ≤ v g)
    (hg_gap : v g < maxLoad - minLoad)
    (hle_max : ∀ i : Agent, commonLoad v (bundle i) ≤ maxLoad) :
    overfullBundleCardPotential v L (moveBundle bundle source target g) =
      overfullBundleCardPotential v L bundle := by
  have hno_high_old :
      ∀ i : Agent, ¬ 2 * L < commonLoad v (bundle i) := by
    intro i
    exact not_lt_of_ge (le_trans (hle_max i) hmax_le_twoL)
  have hmoved_le :
      ∀ i : Agent,
        commonLoad v (moveBundle bundle source target g i) ≤ maxLoad :=
    commonLoad_moveBundle_le_max_of_low_only_move
      hsource_max htarget_min hsource_ne_target hg_source hg_target
      hg_nonneg hg_gap hle_max
  have hno_high_new :
      ∀ i : Agent,
        ¬ 2 * L < commonLoad v (moveBundle bundle source target g i) := by
    intro i
    exact not_lt_of_ge (le_trans (hmoved_le i) hmax_le_twoL)
  exact overfullBundleCardPotential_eq_of_no_high hno_high_old hno_high_new

/--
Low-only Claim 3.4 branch step.  Once a concrete max-to-min move is known to
be ratio-nonincreasing, this packages the two lexicographic-potential facts:
the overfull-bundle potential is preserved in the no-high case, and the finite
min-load tie-breaker strictly decreases.
-/
theorem claim34_low_only_branch_step_of_move_certificate
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc] [Nonempty Agent]
    [DecidableEq Agent] [DecidableEq Item]
    {bundleOf : Alloc → Agent → Finset Item} {v : Item → ℝ}
    {L : ℝ} {ratioOf : Alloc → ℝ} {minOf : Alloc → ℝ} {A B : Alloc}
    {source target : Agent} {g : Item} {minLoad maxLoad : ℝ}
    (hmin_lower :
      ∀ C : Alloc, ∀ i : Agent, minOf C ≤ commonLoad v (bundleOf C i))
    (hmin_attains :
      ∀ C : Alloc, ∃ i : Agent, commonLoad v (bundleOf C i) = minOf C)
    (hminA : minOf A = minLoad)
    (htarget_min : commonLoad v (bundleOf A target) = minLoad)
    (hsource_max : commonLoad v (bundleOf A source) = maxLoad)
    (hsource_ne_target : source ≠ target)
    (hg_source : g ∈ bundleOf A source)
    (hg_target : g ∉ bundleOf A target)
    (hg_pos : 0 < v g)
    (hg_gap : v g < maxLoad - minLoad)
    (hmax_le_twoL : maxLoad ≤ 2 * L)
    (hle_max : ∀ i : Agent, commonLoad v (bundleOf A i) ≤ maxLoad)
    (hbundle_B :
      bundleOf B = moveBundle (bundleOf A) source target g)
    (hratio_BA : ratioOf B ≤ ratioOf A) :
    ratioOf B ≤ ratioOf A ∧
      overfullBundleCardPotential v L (bundleOf B) =
        overfullBundleCardPotential v L (bundleOf A) ∧
      minLoadTiePotential v bundleOf minOf B <
        minLoadTiePotential v bundleOf minOf A := by
  refine ⟨hratio_BA, ?_, ?_⟩
  · rw [hbundle_B]
    exact
      overfullBundleCardPotential_eq_of_low_only_move_no_high
        hmax_le_twoL hsource_max htarget_min hsource_ne_target
        hg_source hg_target (le_of_lt hg_pos) hg_gap hle_max
  · exact
      minLoadTiePotential_decreases_of_low_only_move
        hmin_lower hmin_attains hminA htarget_min hsource_max
        hsource_ne_target hg_source hg_target hg_pos hg_gap hbundle_B

/--
Low-only Claim 3.4 local move certificate.  From a max-load bundle to a
min-load bundle, the positive small item supplied by
`exists_pos_item_lt_max_sub_min_of_low_min_average` keeps every moved load
inside the old extrema, so the max-over-min ratio is nonincreasing.

This is the local move needed before the still-open finite tie-breaker over
optimal allocations.
-/
theorem exists_low_min_max_source_move_ratio_nonincreasing
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ}
    {L minLoad maxLoad : ℝ} {source target : Agent}
    (hL : 0 < L)
    (havg :
      (∑ i : Agent, commonLoad v (bundle i)) =
        (Fintype.card Agent : ℝ) * L)
    (htarget_min : commonLoad v (bundle target) = minLoad)
    (hsource_max : commonLoad v (bundle source) = maxLoad)
    (hmin_pos : 0 < minLoad)
    (hmin_low : minLoad ≤ L / 2)
    (hmin_le : ∀ i, minLoad ≤ commonLoad v (bundle i))
    (hle_max : ∀ i, commonLoad v (bundle i) ≤ maxLoad)
    (hitem_nonneg : ∀ g ∈ bundle source, 0 ≤ v g)
    (hitem_lt : ∀ g ∈ bundle source, v g < L)
    (hunique :
      ∀ {i j : Agent} {g : Item}, g ∈ bundle i → g ∈ bundle j → i = j) :
    ∃ g : Item,
      g ∈ bundle source ∧
        g ∉ bundle target ∧
        0 < v g ∧
        v g < maxLoad - minLoad ∧
          ∀ {newMin newMax : ℝ},
            (∀ i : Agent,
              newMin ≤ commonLoad v (moveBundle bundle source target g i)) →
            (∃ i : Agent,
              commonLoad v (moveBundle bundle source target g i) = newMin) →
            (∀ i : Agent,
              commonLoad v (moveBundle bundle source target g i) ≤ newMax) →
            (∃ i : Agent,
              commonLoad v (moveBundle bundle source target g i) = newMax) →
            loadRatio newMin newMax ≤ loadRatio minLoad maxLoad := by
  classical
  obtain ⟨g, hg_source, hg_pos, hg_small⟩ :=
    exists_pos_item_lt_max_sub_min_of_low_min_average
      (bundle := bundle) (v := v) hL havg htarget_min hsource_max
      hmin_low hmin_le hle_max hitem_nonneg hitem_lt
  have hsource_ne_target : source ≠ target := by
    intro hsource_target
    have hmax_eq_min : maxLoad = minLoad := by
      rw [← hsource_max, hsource_target, htarget_min]
    have hmax_gt_L : L < maxLoad :=
      maxLoad_gt_average_of_low_min_average
        (load := fun i : Agent => commonLoad v (bundle i))
        hL havg htarget_min hmin_low hle_max
    nlinarith
  have hg_target : g ∉ bundle target := by
    intro hg_target
    exact hsource_ne_target (hunique hg_source hg_target)
  refine ⟨g, hg_source, hg_target, hg_pos, hg_small, ?_⟩
  intro newMin newMax hnewMin_lower hnewMin_attains
    hnewMax_upper hnewMax_attains
  let load : Agent → ℝ := fun i => commonLoad v (bundle i)
  have hload_eq :
      ∀ i : Agent,
        commonLoad v (moveBundle bundle source target g i) =
          moveLoad load source target (v g) i :=
    commonLoad_moveBundle_eq_moveLoad
      hsource_ne_target hg_source hg_target
  have hwithin : ∀ i : Agent, minLoad ≤ load i ∧ load i ≤ maxLoad := by
    intro i
    exact ⟨hmin_le i, hle_max i⟩
  have hmax_nonneg : 0 ≤ maxLoad := by
    have hmin_le_max : minLoad ≤ maxLoad := by
      simpa [load, hsource_max] using hmin_le source
    exact le_trans hmin_pos.le hmin_le_max
  have hsource_bound : minLoad ≤ load source - v g := by
    dsimp [load]
    rw [hsource_max]
    nlinarith
  have htarget_bound : load target + v g ≤ maxLoad := by
    dsimp [load]
    rw [htarget_min]
    nlinarith
  have hnewMin_lower' :
      ∀ i : Agent, newMin ≤ moveLoad load source target (v g) i := by
    intro i
    rw [← hload_eq i]
    exact hnewMin_lower i
  have hnewMin_attains' :
      ∃ i : Agent, moveLoad load source target (v g) i = newMin := by
    obtain ⟨i, hi⟩ := hnewMin_attains
    exact ⟨i, by simpa [hload_eq i] using hi⟩
  have hnewMax_upper' :
      ∀ i : Agent, moveLoad load source target (v g) i ≤ newMax := by
    intro i
    rw [← hload_eq i]
    exact hnewMax_upper i
  have hnewMax_attains' :
      ∃ i : Agent, moveLoad load source target (v g) i = newMax := by
    obtain ⟨i, hi⟩ := hnewMax_attains
    exact ⟨i, by simpa [hload_eq i] using hi⟩
  exact
    loadRatio_nonincreasing_of_moveLoad_certificate
      (load := load) hmin_pos hmax_nonneg hwithin (hitem_nonneg g hg_source)
      hsource_bound htarget_bound hnewMin_lower' hnewMin_attains'
      hnewMax_upper' hnewMax_attains'

/--
Boundary Claim 3.4 local move certificate.  In the strict-window boundary
`maxLoad = 2L` with all loads above the lower threshold, a positive small good
from a max-load source to a min-load target still keeps the max-over-min ratio
nonincreasing and preserves the no-overfull primary potential.
-/
theorem exists_boundary_min_max_source_move_ratio_nonincreasing
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ}
    {L minLoad maxLoad : ℝ} {source target : Agent}
    (hL : 0 < L)
    (havg :
      (∑ i : Agent, commonLoad v (bundle i)) =
        (Fintype.card Agent : ℝ) * L)
    (htarget_min : commonLoad v (bundle target) = minLoad)
    (hsource_max : commonLoad v (bundle source) = maxLoad)
    (hmin_pos : 0 < minLoad)
    (hmax_eq_twoL : maxLoad = 2 * L)
    (hmin_le : ∀ i, minLoad ≤ commonLoad v (bundle i))
    (hle_max : ∀ i, commonLoad v (bundle i) ≤ maxLoad)
    (hitem_nonneg : ∀ g ∈ bundle source, 0 ≤ v g)
    (hitem_lt : ∀ g ∈ bundle source, v g < L)
    (hunique :
      ∀ {i j : Agent} {g : Item}, g ∈ bundle i → g ∈ bundle j → i = j) :
    ∃ g : Item,
      g ∈ bundle source ∧
        g ∉ bundle target ∧
        0 < v g ∧
        v g < maxLoad - minLoad ∧
          ∀ {newMin newMax : ℝ},
            (∀ i : Agent,
              newMin ≤ commonLoad v (moveBundle bundle source target g i)) →
            (∃ i : Agent,
              commonLoad v (moveBundle bundle source target g i) = newMin) →
            (∀ i : Agent,
              commonLoad v (moveBundle bundle source target g i) ≤ newMax) →
            (∃ i : Agent,
              commonLoad v (moveBundle bundle source target g i) = newMax) →
            loadRatio newMin newMax ≤ loadRatio minLoad maxLoad := by
  classical
  obtain ⟨avgAgent, havgAgent⟩ :=
    exists_load_le_of_sum_eq_card_mul
      (load := fun i : Agent => commonLoad v (bundle i)) havg
  have hmin_le_L : minLoad ≤ L := le_trans (hmin_le avgAgent) havgAgent
  have hsource_pos : 0 < commonLoad v (bundle source) := by
    rw [hsource_max, hmax_eq_twoL]
    nlinarith
  obtain ⟨g, hg_source, hg_pos⟩ :=
    exists_pos_mem_of_commonLoad_pos_of_nonneg
      (v := v) (S := bundle source) hsource_pos hitem_nonneg
  have hg_gap : v g < maxLoad - minLoad := by
    have hL_le_gap : L ≤ maxLoad - minLoad := by
      rw [hmax_eq_twoL]
      nlinarith
    exact lt_of_lt_of_le (hitem_lt g hg_source) hL_le_gap
  have hsource_ne_target : source ≠ target := by
    intro hsource_target
    have hmax_eq_min : maxLoad = minLoad := by
      rw [← hsource_max, hsource_target, htarget_min]
    rw [hmax_eq_twoL] at hmax_eq_min
    nlinarith
  have hg_target : g ∉ bundle target := by
    intro hg_target
    exact hsource_ne_target (hunique hg_source hg_target)
  refine ⟨g, hg_source, hg_target, hg_pos, hg_gap, ?_⟩
  intro newMin newMax hnewMin_lower hnewMin_attains
    hnewMax_upper hnewMax_attains
  let load : Agent → ℝ := fun i => commonLoad v (bundle i)
  have hload_eq :
      ∀ i : Agent,
        commonLoad v (moveBundle bundle source target g i) =
          moveLoad load source target (v g) i :=
    commonLoad_moveBundle_eq_moveLoad
      hsource_ne_target hg_source hg_target
  have hwithin : ∀ i : Agent, minLoad ≤ load i ∧ load i ≤ maxLoad := by
    intro i
    exact ⟨hmin_le i, hle_max i⟩
  have hmax_nonneg : 0 ≤ maxLoad := by
    rw [hmax_eq_twoL]
    nlinarith
  have hsource_bound : minLoad ≤ load source - v g := by
    dsimp [load]
    rw [hsource_max]
    nlinarith
  have htarget_bound : load target + v g ≤ maxLoad := by
    dsimp [load]
    rw [htarget_min]
    nlinarith
  have hnewMin_lower' :
      ∀ i : Agent, newMin ≤ moveLoad load source target (v g) i := by
    intro i
    rw [← hload_eq i]
    exact hnewMin_lower i
  have hnewMin_attains' :
      ∃ i : Agent, moveLoad load source target (v g) i = newMin := by
    obtain ⟨i, hi⟩ := hnewMin_attains
    exact ⟨i, by simpa [hload_eq i] using hi⟩
  have hnewMax_upper' :
      ∀ i : Agent, moveLoad load source target (v g) i ≤ newMax := by
    intro i
    rw [← hload_eq i]
    exact hnewMax_upper i
  have hnewMax_attains' :
      ∃ i : Agent, moveLoad load source target (v g) i = newMax := by
    obtain ⟨i, hi⟩ := hnewMax_attains
    exact ⟨i, by simpa [hload_eq i] using hi⟩
  exact
    loadRatio_nonincreasing_of_moveLoad_certificate
      (load := load) hmin_pos hmax_nonneg hwithin (le_of_lt hg_pos)
      hsource_bound htarget_bound hnewMin_lower' hnewMin_attains'
      hnewMax_upper' hnewMax_attains'

/--
Low-only source branch for Claim 3.4.  Given min/max accessors and the paper's
low-min/no-high hypotheses, the max-to-min source move supplies the low-only
branch required by the lexicographic finite-descent theorem.
-/
theorem claim34_low_only_branch_step_of_min_max_source_move
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc] [Nonempty Agent]
    [DecidableEq Agent] [DecidableEq Item]
    {bundleOf : Alloc → Agent → Finset Item} {v : Item → ℝ}
    {L : ℝ} {ratioOf : Alloc → ℝ} {minOf maxOf : Alloc → ℝ}
    (moveAlloc : Alloc → Agent → Agent → Item → Alloc)
    {A : Alloc} {source target : Agent} {minLoad maxLoad : ℝ}
    (hL : 0 < L)
    (havg :
      (∑ i : Agent, commonLoad v (bundleOf A i)) =
        (Fintype.card Agent : ℝ) * L)
    (hmin_lower :
      ∀ C : Alloc, ∀ i : Agent, minOf C ≤ commonLoad v (bundleOf C i))
    (hmin_attains :
      ∀ C : Alloc, ∃ i : Agent, commonLoad v (bundleOf C i) = minOf C)
    (hmax_upper :
      ∀ C : Alloc, ∀ i : Agent, commonLoad v (bundleOf C i) ≤ maxOf C)
    (hmax_attains :
      ∀ C : Alloc, ∃ i : Agent, commonLoad v (bundleOf C i) = maxOf C)
    (hminA : minOf A = minLoad)
    (hmaxA : maxOf A = maxLoad)
    (htarget_min : commonLoad v (bundleOf A target) = minLoad)
    (hsource_max : commonLoad v (bundleOf A source) = maxLoad)
    (hmin_pos : 0 < minLoad)
    (hmin_low : minLoad ≤ L / 2)
    (hmax_le_twoL : maxLoad ≤ 2 * L)
    (hitem_nonneg : ∀ g ∈ bundleOf A source, 0 ≤ v g)
    (hitem_lt : ∀ g ∈ bundleOf A source, v g < L)
    (hunique :
      ∀ {i j : Agent} {g : Item},
        g ∈ bundleOf A i → g ∈ bundleOf A j → i = j)
    (hratio : ∀ C : Alloc, ratioOf C = loadRatio (minOf C) (maxOf C))
    (hbundle_move :
      ∀ g : Item,
        bundleOf (moveAlloc A source target g) =
          moveBundle (bundleOf A) source target g) :
    ∃ B : Alloc,
      ratioOf B ≤ ratioOf A ∧
        overfullBundleCardPotential v L (bundleOf B) =
          overfullBundleCardPotential v L (bundleOf A) ∧
        minLoadTiePotential v bundleOf minOf B <
          minLoadTiePotential v bundleOf minOf A := by
  classical
  have hmin_le : ∀ i : Agent, minLoad ≤ commonLoad v (bundleOf A i) := by
    intro i
    rw [← hminA]
    exact hmin_lower A i
  have hle_max : ∀ i : Agent, commonLoad v (bundleOf A i) ≤ maxLoad := by
    intro i
    rw [← hmaxA]
    exact hmax_upper A i
  rcases
    exists_low_min_max_source_move_ratio_nonincreasing
      (bundle := bundleOf A) (v := v) hL havg htarget_min hsource_max
      hmin_pos hmin_low hmin_le hle_max hitem_nonneg hitem_lt hunique with
    ⟨g, hg_source, hg_target, hg_pos, hg_gap, hratio_move⟩
  let B : Alloc := moveAlloc A source target g
  have hbundle_B :
      bundleOf B = moveBundle (bundleOf A) source target g := by
    simpa [B] using hbundle_move g
  have hratio_load :
      loadRatio (minOf B) (maxOf B) ≤ loadRatio minLoad maxLoad := by
    refine hratio_move ?_ ?_ ?_ ?_
    · intro i
      rw [← hbundle_B]
      exact hmin_lower B i
    · rcases hmin_attains B with ⟨i, hi⟩
      exact ⟨i, by simpa [← hbundle_B] using hi⟩
    · intro i
      rw [← hbundle_B]
      exact hmax_upper B i
    · rcases hmax_attains B with ⟨i, hi⟩
      exact ⟨i, by simpa [← hbundle_B] using hi⟩
  have hratio_BA : ratioOf B ≤ ratioOf A := by
    calc
      ratioOf B = loadRatio (minOf B) (maxOf B) := hratio B
      _ ≤ loadRatio minLoad maxLoad := hratio_load
      _ = ratioOf A := by
        rw [hratio A, hminA, hmaxA]
  have hsource_ne_target : source ≠ target := by
    intro hsource_target
    exact hg_target (by simpa [hsource_target] using hg_source)
  have hbranch :=
    claim34_low_only_branch_step_of_move_certificate
      (v := v) (L := L) (ratioOf := ratioOf) (minOf := minOf)
      (A := A) (B := B) (source := source) (target := target) (g := g)
      (minLoad := minLoad) (maxLoad := maxLoad)
      hmin_lower hmin_attains hminA htarget_min hsource_max
      hsource_ne_target hg_source hg_target hg_pos hg_gap
      hmax_le_twoL hle_max hbundle_B hratio_BA
  exact ⟨B, hbranch.1, hbranch.2⟩

/--
Boundary source branch for Claim 3.4.  When the allocation violates the strict
upper side only by attaining `2L`, the primary overfull-bundle potential is
preserved and the finite min-load tie-breaker decreases.
-/
theorem claim34_boundary_branch_step_of_min_max_source_move
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc] [Nonempty Agent]
    [DecidableEq Agent] [DecidableEq Item]
    {bundleOf : Alloc → Agent → Finset Item} {v : Item → ℝ}
    {L : ℝ} {ratioOf : Alloc → ℝ} {minOf maxOf : Alloc → ℝ}
    (moveAlloc : Alloc → Agent → Agent → Item → Alloc)
    {A : Alloc} {source target : Agent} {minLoad maxLoad : ℝ}
    (hL : 0 < L)
    (havg :
      (∑ i : Agent, commonLoad v (bundleOf A i)) =
        (Fintype.card Agent : ℝ) * L)
    (hmin_lower :
      ∀ C : Alloc, ∀ i : Agent, minOf C ≤ commonLoad v (bundleOf C i))
    (hmin_attains :
      ∀ C : Alloc, ∃ i : Agent, commonLoad v (bundleOf C i) = minOf C)
    (hmax_upper :
      ∀ C : Alloc, ∀ i : Agent, commonLoad v (bundleOf C i) ≤ maxOf C)
    (hmax_attains :
      ∀ C : Alloc, ∃ i : Agent, commonLoad v (bundleOf C i) = maxOf C)
    (hminA : minOf A = minLoad)
    (hmaxA : maxOf A = maxLoad)
    (htarget_min : commonLoad v (bundleOf A target) = minLoad)
    (hsource_max : commonLoad v (bundleOf A source) = maxLoad)
    (hmin_pos : 0 < minLoad)
    (_hmin_gt : L / 2 < minLoad)
    (hmax_eq_twoL : maxLoad = 2 * L)
    (hitem_nonneg : ∀ g ∈ bundleOf A source, 0 ≤ v g)
    (hitem_lt : ∀ g ∈ bundleOf A source, v g < L)
    (hunique :
      ∀ {i j : Agent} {g : Item},
        g ∈ bundleOf A i → g ∈ bundleOf A j → i = j)
    (hratio : ∀ C : Alloc, ratioOf C = loadRatio (minOf C) (maxOf C))
    (hbundle_move :
      ∀ g : Item,
        bundleOf (moveAlloc A source target g) =
          moveBundle (bundleOf A) source target g) :
    ∃ B : Alloc,
      ratioOf B ≤ ratioOf A ∧
        overfullBundleCardPotential v L (bundleOf B) =
          overfullBundleCardPotential v L (bundleOf A) ∧
        minLoadTiePotential v bundleOf minOf B <
          minLoadTiePotential v bundleOf minOf A := by
  classical
  have hmin_le : ∀ i : Agent, minLoad ≤ commonLoad v (bundleOf A i) := by
    intro i
    rw [← hminA]
    exact hmin_lower A i
  have hle_max : ∀ i : Agent, commonLoad v (bundleOf A i) ≤ maxLoad := by
    intro i
    rw [← hmaxA]
    exact hmax_upper A i
  rcases
    exists_boundary_min_max_source_move_ratio_nonincreasing
      (bundle := bundleOf A) (v := v) hL havg htarget_min hsource_max
      hmin_pos hmax_eq_twoL hmin_le hle_max hitem_nonneg hitem_lt
      hunique with
    ⟨g, hg_source, hg_target, hg_pos, hg_gap, hratio_move⟩
  let B : Alloc := moveAlloc A source target g
  have hbundle_B :
      bundleOf B = moveBundle (bundleOf A) source target g := by
    simpa [B] using hbundle_move g
  have hratio_load :
      loadRatio (minOf B) (maxOf B) ≤ loadRatio minLoad maxLoad := by
    refine hratio_move ?_ ?_ ?_ ?_
    · intro i
      rw [← hbundle_B]
      exact hmin_lower B i
    · rcases hmin_attains B with ⟨i, hi⟩
      exact ⟨i, by simpa [← hbundle_B] using hi⟩
    · intro i
      rw [← hbundle_B]
      exact hmax_upper B i
    · rcases hmax_attains B with ⟨i, hi⟩
      exact ⟨i, by simpa [← hbundle_B] using hi⟩
  have hratio_BA : ratioOf B ≤ ratioOf A := by
    calc
      ratioOf B = loadRatio (minOf B) (maxOf B) := hratio B
      _ ≤ loadRatio minLoad maxLoad := hratio_load
      _ = ratioOf A := by
        rw [hratio A, hminA, hmaxA]
  have hsource_ne_target : source ≠ target := by
    intro hsource_target
    exact hg_target (by simpa [hsource_target] using hg_source)
  have hmax_le_twoL : maxLoad ≤ 2 * L := by
    rw [hmax_eq_twoL]
  have hbranch :=
    claim34_low_only_branch_step_of_move_certificate
      (v := v) (L := L) (ratioOf := ratioOf) (minOf := minOf)
      (A := A) (B := B) (source := source) (target := target) (g := g)
      (minLoad := minLoad) (maxLoad := maxLoad)
      hmin_lower hmin_attains hminA htarget_min hsource_max
      hsource_ne_target hg_source hg_target hg_pos hg_gap
      hmax_le_twoL hle_max hbundle_B hratio_BA
  exact ⟨B, hbranch.1, hbranch.2⟩

/--
Low-target/high-donor arithmetic for Claim 3.4.  If the target load is below
`L / 2`, the donor load is above `2L`, and the moved good has value in
`[0,L)`, then the scalar move stays inside the old min/max interval.
-/
theorem moveLoad_within_old_extrema_of_low_target_high_source
    {Agent : Type*} [DecidableEq Agent]
    {load : Agent → ℝ} {source target : Agent} {x oldMin oldMax L : ℝ}
    (hL : 0 < L)
    (hwithin : ∀ i : Agent, oldMin ≤ load i ∧ load i ≤ oldMax)
    (htarget_low : load target < L / 2)
    (hsource_high : 2 * L < load source)
    (hx_nonneg : 0 ≤ x)
    (hx_lt : x < L) :
    ∀ i : Agent, oldMin ≤ moveLoad load source target x i ∧
      moveLoad load source target x i ≤ oldMax := by
  have hsource : oldMin ≤ load source - x := by
    have holdMin_le_target : oldMin ≤ load target := (hwithin target).1
    nlinarith
  have htarget : load target + x ≤ oldMax := by
    have hsource_le_oldMax : load source ≤ oldMax := (hwithin source).2
    nlinarith
  exact
    moveLoad_within_old_extrema hwithin hx_nonneg hsource htarget

/--
Variant of the Claim 3.4 arithmetic with a weaker receiving-bundle premise:
moving a good of value below `L` from a bundle above `2L` into any bundle of
load at most `L` stays inside the old extrema.
-/
theorem moveLoad_within_old_extrema_of_le_average_target_high_source
    {Agent : Type*} [DecidableEq Agent]
    {load : Agent → ℝ} {source target : Agent} {x oldMin oldMax L : ℝ}
    (hL : 0 < L)
    (hwithin : ∀ i : Agent, oldMin ≤ load i ∧ load i ≤ oldMax)
    (htarget_le : load target ≤ L)
    (hsource_high : 2 * L < load source)
    (hx_nonneg : 0 ≤ x)
    (hx_lt : x < L) :
    ∀ i : Agent, oldMin ≤ moveLoad load source target x i ∧
      moveLoad load source target x i ≤ oldMax := by
  have hsource : oldMin ≤ load source - x := by
    have holdMin_le_target : oldMin ≤ load target := (hwithin target).1
    nlinarith
  have htarget : load target + x ≤ oldMax := by
    have hsource_le_oldMax : load source ≤ oldMax := (hwithin source).2
    nlinarith
  exact
    moveLoad_within_old_extrema hwithin hx_nonneg hsource htarget

/--
Concrete Claim 3.4 local step: under the source low-target/high-donor
conditions, any moved good with value in `[0,L)` is ratio-nonincreasing once the
new extrema are certified.
-/
theorem loadRatio_nonincreasing_of_low_target_high_source_moveLoad
    {Agent : Type*} [DecidableEq Agent]
    {load : Agent → ℝ} {source target : Agent}
    {x oldMin oldMax newMin newMax L : ℝ}
    (hL : 0 < L)
    (holdMin_pos : 0 < oldMin)
    (holdMax_nonneg : 0 ≤ oldMax)
    (hwithin : ∀ i : Agent, oldMin ≤ load i ∧ load i ≤ oldMax)
    (htarget_low : load target < L / 2)
    (hsource_high : 2 * L < load source)
    (hx_nonneg : 0 ≤ x)
    (hx_lt : x < L)
    (_hnewMin_lower :
      ∀ i : Agent, newMin ≤ moveLoad load source target x i)
    (hnewMin_attains :
      ∃ i : Agent, moveLoad load source target x i = newMin)
    (_hnewMax_upper :
      ∀ i : Agent, moveLoad load source target x i ≤ newMax)
    (hnewMax_attains :
      ∃ i : Agent, moveLoad load source target x i = newMax) :
    loadRatio newMin newMax ≤ loadRatio oldMin oldMax := by
  have hinside :
      ∀ i : Agent, oldMin ≤ moveLoad load source target x i ∧
        moveLoad load source target x i ≤ oldMax :=
    moveLoad_within_old_extrema_of_low_target_high_source
      hL hwithin htarget_low hsource_high hx_nonneg hx_lt
  obtain ⟨imin, himin⟩ := hnewMin_attains
  obtain ⟨imax, himax⟩ := hnewMax_attains
  have hmin : oldMin ≤ newMin := by
    simpa [himin] using (hinside imin).1
  have hmax : newMax ≤ oldMax := by
    simpa [himax] using (hinside imax).2
  exact
    loadRatio_le_of_min_increases_max_decreases
      holdMin_pos holdMax_nonneg hmin hmax

/--
Concrete Claim 3.4 local step with an at-most-average receiver.  This is the
same max-over-min monotonicity certificate as the low-target version, but it
matches the standard move from an overfull bundle into a minimum-load bundle.
-/
theorem loadRatio_nonincreasing_of_le_average_target_high_source_moveLoad
    {Agent : Type*} [DecidableEq Agent]
    {load : Agent → ℝ} {source target : Agent}
    {x oldMin oldMax newMin newMax L : ℝ}
    (hL : 0 < L)
    (holdMin_pos : 0 < oldMin)
    (holdMax_nonneg : 0 ≤ oldMax)
    (hwithin : ∀ i : Agent, oldMin ≤ load i ∧ load i ≤ oldMax)
    (htarget_le : load target ≤ L)
    (hsource_high : 2 * L < load source)
    (hx_nonneg : 0 ≤ x)
    (hx_lt : x < L)
    (_hnewMin_lower :
      ∀ i : Agent, newMin ≤ moveLoad load source target x i)
    (hnewMin_attains :
      ∃ i : Agent, moveLoad load source target x i = newMin)
    (_hnewMax_upper :
      ∀ i : Agent, moveLoad load source target x i ≤ newMax)
    (hnewMax_attains :
      ∃ i : Agent, moveLoad load source target x i = newMax) :
    loadRatio newMin newMax ≤ loadRatio oldMin oldMax := by
  have hinside :
      ∀ i : Agent, oldMin ≤ moveLoad load source target x i ∧
        moveLoad load source target x i ≤ oldMax :=
    moveLoad_within_old_extrema_of_le_average_target_high_source
      hL hwithin htarget_le hsource_high hx_nonneg hx_lt
  obtain ⟨imin, himin⟩ := hnewMin_attains
  obtain ⟨imax, himax⟩ := hnewMax_attains
  have hmin : oldMin ≤ newMin := by
    simpa [himin] using (hinside imin).1
  have hmax : newMax ≤ oldMax := by
    simpa [himax] using (hinside imax).2
  exact
    loadRatio_le_of_min_increases_max_decreases
      holdMin_pos holdMax_nonneg hmin hmax

/--
Bundle-level local reallocation certificate for Claim 3.4.  Moving a fresh item
from a bundle of load above `2L` into a bundle of load below `L / 2` is
ratio-nonincreasing, and the donor-cardinality potential strictly decreases.
-/
theorem local_reallocation_certificate_of_low_target_high_source
    {Agent Item : Type*} [DecidableEq Agent] [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ}
    {source target : Agent} {g : Item}
    {oldMin oldMax newMin newMax L : ℝ}
    (hsource_ne_target : source ≠ target)
    (hg_source : g ∈ bundle source)
    (hg_target : g ∉ bundle target)
    (hL : 0 < L)
    (holdMin_pos : 0 < oldMin)
    (holdMax_nonneg : 0 ≤ oldMax)
    (hwithin :
      ∀ i : Agent, oldMin ≤ commonLoad v (bundle i) ∧
        commonLoad v (bundle i) ≤ oldMax)
    (htarget_low : commonLoad v (bundle target) < L / 2)
    (hsource_high : 2 * L < commonLoad v (bundle source))
    (hg_nonneg : 0 ≤ v g)
    (hg_lt : v g < L)
    (hnewMin_lower :
      ∀ i : Agent, newMin ≤ commonLoad v (moveBundle bundle source target g i))
    (hnewMin_attains :
      ∃ i : Agent, commonLoad v (moveBundle bundle source target g i) = newMin)
    (hnewMax_upper :
      ∀ i : Agent, commonLoad v (moveBundle bundle source target g i) ≤ newMax)
    (hnewMax_attains :
      ∃ i : Agent, commonLoad v (moveBundle bundle source target g i) = newMax) :
    loadRatio newMin newMax ≤ loadRatio oldMin oldMax ∧
      donorCardPotential (moveBundle bundle source target g) source <
        donorCardPotential bundle source := by
  let load : Agent → ℝ := fun i => commonLoad v (bundle i)
  have hload_eq :
      ∀ i : Agent,
        commonLoad v (moveBundle bundle source target g i) =
          moveLoad load source target (v g) i :=
    commonLoad_moveBundle_eq_moveLoad
      hsource_ne_target hg_source hg_target
  have hnewMin_lower' :
      ∀ i : Agent, newMin ≤ moveLoad load source target (v g) i := by
    intro i
    rw [← hload_eq i]
    exact hnewMin_lower i
  have hnewMin_attains' :
      ∃ i : Agent, moveLoad load source target (v g) i = newMin := by
    obtain ⟨i, hi⟩ := hnewMin_attains
    exact ⟨i, by simpa [hload_eq i] using hi⟩
  have hnewMax_upper' :
      ∀ i : Agent, moveLoad load source target (v g) i ≤ newMax := by
    intro i
    rw [← hload_eq i]
    exact hnewMax_upper i
  have hnewMax_attains' :
      ∃ i : Agent, moveLoad load source target (v g) i = newMax := by
    obtain ⟨i, hi⟩ := hnewMax_attains
    exact ⟨i, by simpa [hload_eq i] using hi⟩
  constructor
  · exact
      loadRatio_nonincreasing_of_low_target_high_source_moveLoad
        (load := load) hL holdMin_pos holdMax_nonneg hwithin
        htarget_low hsource_high hg_nonneg hg_lt
        hnewMin_lower' hnewMin_attains' hnewMax_upper' hnewMax_attains'
  · exact donorCardPotential_decreases_of_moveBundle hg_source

/--
Bundle-level local reallocation certificate for the high-source/min-target
move in Claim 3.4.  Moving a fresh item of value in `[0,L)` from a bundle above
`2L` into any bundle of load at most `L` is ratio-nonincreasing, and the donor
cardinality strictly decreases.
-/
theorem local_reallocation_certificate_of_le_average_target_high_source
    {Agent Item : Type*} [DecidableEq Agent] [DecidableEq Item]
    {bundle : Agent → Finset Item} {v : Item → ℝ}
    {source target : Agent} {g : Item}
    {oldMin oldMax newMin newMax L : ℝ}
    (hsource_ne_target : source ≠ target)
    (hg_source : g ∈ bundle source)
    (hg_target : g ∉ bundle target)
    (hL : 0 < L)
    (holdMin_pos : 0 < oldMin)
    (holdMax_nonneg : 0 ≤ oldMax)
    (hwithin :
      ∀ i : Agent, oldMin ≤ commonLoad v (bundle i) ∧
        commonLoad v (bundle i) ≤ oldMax)
    (htarget_le : commonLoad v (bundle target) ≤ L)
    (hsource_high : 2 * L < commonLoad v (bundle source))
    (hg_nonneg : 0 ≤ v g)
    (hg_lt : v g < L)
    (hnewMin_lower :
      ∀ i : Agent, newMin ≤ commonLoad v (moveBundle bundle source target g i))
    (hnewMin_attains :
      ∃ i : Agent, commonLoad v (moveBundle bundle source target g i) = newMin)
    (hnewMax_upper :
      ∀ i : Agent, commonLoad v (moveBundle bundle source target g i) ≤ newMax)
    (hnewMax_attains :
      ∃ i : Agent, commonLoad v (moveBundle bundle source target g i) = newMax) :
    loadRatio newMin newMax ≤ loadRatio oldMin oldMax ∧
      donorCardPotential (moveBundle bundle source target g) source <
        donorCardPotential bundle source := by
  let load : Agent → ℝ := fun i => commonLoad v (bundle i)
  have hload_eq :
      ∀ i : Agent,
        commonLoad v (moveBundle bundle source target g i) =
          moveLoad load source target (v g) i :=
    commonLoad_moveBundle_eq_moveLoad
      hsource_ne_target hg_source hg_target
  have hnewMin_lower' :
      ∀ i : Agent, newMin ≤ moveLoad load source target (v g) i := by
    intro i
    rw [← hload_eq i]
    exact hnewMin_lower i
  have hnewMin_attains' :
      ∃ i : Agent, moveLoad load source target (v g) i = newMin := by
    obtain ⟨i, hi⟩ := hnewMin_attains
    exact ⟨i, by simpa [hload_eq i] using hi⟩
  have hnewMax_upper' :
      ∀ i : Agent, moveLoad load source target (v g) i ≤ newMax := by
    intro i
    rw [← hload_eq i]
    exact hnewMax_upper i
  have hnewMax_attains' :
      ∃ i : Agent, moveLoad load source target (v g) i = newMax := by
    obtain ⟨i, hi⟩ := hnewMax_attains
    exact ⟨i, by simpa [hload_eq i] using hi⟩
  constructor
  · exact
      loadRatio_nonincreasing_of_le_average_target_high_source_moveLoad
        (load := load) hL holdMin_pos holdMax_nonneg hwithin
        htarget_le hsource_high hg_nonneg hg_lt
        hnewMin_lower' hnewMin_attains' hnewMax_upper' hnewMax_attains'
  · exact donorCardPotential_decreases_of_moveBundle hg_source

/--
High-source branch for Claim 3.4.  Given a max-load source above `2L`, the
paper's average-load argument supplies a target of load at most `L` and a fresh
small good, producing the primary overfull-bundle descent branch.
-/
theorem claim34_high_source_branch_step_of_min_max_source_move
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc] [Nonempty Agent]
    [DecidableEq Agent] [DecidableEq Item]
    {bundleOf : Alloc → Agent → Finset Item} {v : Item → ℝ}
    {L : ℝ} {ratioOf : Alloc → ℝ} {minOf maxOf : Alloc → ℝ}
    (moveAlloc : Alloc → Agent → Agent → Item → Alloc)
    {A : Alloc} {source : Agent} {minLoad maxLoad : ℝ}
    (hL : 0 < L)
    (havg :
      (∑ i : Agent, commonLoad v (bundleOf A i)) =
        (Fintype.card Agent : ℝ) * L)
    (hmin_lower :
      ∀ C : Alloc, ∀ i : Agent, minOf C ≤ commonLoad v (bundleOf C i))
    (hmin_attains :
      ∀ C : Alloc, ∃ i : Agent, commonLoad v (bundleOf C i) = minOf C)
    (hmax_upper :
      ∀ C : Alloc, ∀ i : Agent, commonLoad v (bundleOf C i) ≤ maxOf C)
    (hmax_attains :
      ∀ C : Alloc, ∃ i : Agent, commonLoad v (bundleOf C i) = maxOf C)
    (hminA : minOf A = minLoad)
    (hmaxA : maxOf A = maxLoad)
    (hsource_max : commonLoad v (bundleOf A source) = maxLoad)
    (hsource_high : 2 * L < maxLoad)
    (hmin_pos : 0 < minLoad)
    (hitem_nonneg : ∀ g ∈ bundleOf A source, 0 ≤ v g)
    (hitem_lt : ∀ g ∈ bundleOf A source, v g < L)
    (hunique :
      ∀ {i j : Agent} {g : Item},
        g ∈ bundleOf A i → g ∈ bundleOf A j → i = j)
    (hratio : ∀ C : Alloc, ratioOf C = loadRatio (minOf C) (maxOf C))
    (hbundle_move :
      ∀ target g,
        bundleOf (moveAlloc A source target g) =
          moveBundle (bundleOf A) source target g) :
    ∃ B : Alloc,
      ratioOf B ≤ ratioOf A ∧
        overfullBundleCardPotential v L (bundleOf B) <
          overfullBundleCardPotential v L (bundleOf A) := by
  classical
  have hsource_high_load : 2 * L < commonLoad v (bundleOf A source) := by
    rw [hsource_max]
    exact hsource_high
  rcases
    exists_target_good_of_high_source_average
      (bundle := bundleOf A) (v := v) hL havg hsource_high_load
      hitem_nonneg hitem_lt hunique with
    ⟨target, g, hsource_ne_target, hg_source, hg_target,
      htarget_le, hg_nonneg, hg_lt⟩
  let B : Alloc := moveAlloc A source target g
  have hbundle_B :
      bundleOf B = moveBundle (bundleOf A) source target g := by
    simpa [B] using hbundle_move target g
  have hwithin :
      ∀ i : Agent,
        minLoad ≤ commonLoad v (bundleOf A i) ∧
          commonLoad v (bundleOf A i) ≤ maxLoad := by
    intro i
    constructor
    · rw [← hminA]
      exact hmin_lower A i
    · rw [← hmaxA]
      exact hmax_upper A i
  have hmax_nonneg : 0 ≤ maxLoad := by
    have hmin_le_max : minLoad ≤ maxLoad := by
      simpa [hsource_max] using (hwithin source).1
    exact le_trans hmin_pos.le hmin_le_max
  have hratio_load :
      loadRatio (minOf B) (maxOf B) ≤ loadRatio minLoad maxLoad := by
    exact
      (local_reallocation_certificate_of_le_average_target_high_source
        (bundle := bundleOf A) (v := v)
        hsource_ne_target hg_source hg_target hL hmin_pos hmax_nonneg
        hwithin htarget_le hsource_high_load hg_nonneg hg_lt
        (by
          intro i
          rw [← hbundle_B]
          exact hmin_lower B i)
        (by
          rcases hmin_attains B with ⟨i, hi⟩
          exact ⟨i, by simpa [← hbundle_B] using hi⟩)
        (by
          intro i
          rw [← hbundle_B]
          exact hmax_upper B i)
        (by
          rcases hmax_attains B with ⟨i, hi⟩
          exact ⟨i, by simpa [← hbundle_B] using hi⟩)).1
  have hratio_BA : ratioOf B ≤ ratioOf A := by
    calc
      ratioOf B = loadRatio (minOf B) (maxOf B) := hratio B
      _ ≤ loadRatio minLoad maxLoad := hratio_load
      _ = ratioOf A := by
        rw [hratio A, hminA, hmaxA]
  have hpotential :
      overfullBundleCardPotential v L (bundleOf B) <
        overfullBundleCardPotential v L (bundleOf A) := by
    rw [hbundle_B]
    exact
      overfullBundleCardPotential_decreases_of_moveBundle_le_average_target_high_source
        hsource_ne_target hg_source hg_target hL htarget_le
        hsource_high_load hg_lt
  exact ⟨B, hratio_BA, hpotential⟩

/--
Claim 3.4 branch trichotomy.  From an unbounded allocation, either the maximum
load is strictly above `2L`, or the minimum load is at most `L / 2`, or the
only remaining obstruction is the strict-window boundary `maxLoad = 2L` with
`L / 2 < minLoad`.
-/
theorem claim34_branch_step_of_minmax_trichotomy
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc]
    {v : Item → ℝ} {L : ℝ} {ratioOf : Alloc → ℝ}
    {bundleOf : Alloc → Agent → Finset Item}
    {minOf : Alloc → ℝ} {A : Alloc} {minLoad maxLoad : ℝ}
    (hmin_lower_A :
      ∀ i : Agent, minLoad ≤ commonLoad v (bundleOf A i))
    (hmax_upper_A :
      ∀ i : Agent, commonLoad v (bundleOf A i) ≤ maxLoad)
    (hnot_bounded :
      ¬ ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf A i)))
    (hhigh :
      2 * L < maxLoad →
        ∃ B : Alloc,
          ratioOf B ≤ ratioOf A ∧
            overfullBundleCardPotential v L (bundleOf B) <
              overfullBundleCardPotential v L (bundleOf A))
    (hlow :
      minLoad ≤ L / 2 →
        maxLoad ≤ 2 * L →
          ∃ B : Alloc,
            ratioOf B ≤ ratioOf A ∧
              overfullBundleCardPotential v L (bundleOf B) =
                overfullBundleCardPotential v L (bundleOf A) ∧
              minLoadTiePotential v bundleOf minOf B <
                minLoadTiePotential v bundleOf minOf A)
    (hboundary :
      L / 2 < minLoad →
        maxLoad = 2 * L →
          ∃ B : Alloc,
            ratioOf B ≤ ratioOf A ∧
              (overfullBundleCardPotential v L (bundleOf B) <
                  overfullBundleCardPotential v L (bundleOf A) ∨
                (overfullBundleCardPotential v L (bundleOf B) =
                    overfullBundleCardPotential v L (bundleOf A) ∧
                  minLoadTiePotential v bundleOf minOf B <
                    minLoadTiePotential v bundleOf minOf A))) :
    ∃ B : Alloc,
      ratioOf B ≤ ratioOf A ∧
        (overfullBundleCardPotential v L (bundleOf B) <
            overfullBundleCardPotential v L (bundleOf A) ∨
          (overfullBundleCardPotential v L (bundleOf B) =
              overfullBundleCardPotential v L (bundleOf A) ∧
            minLoadTiePotential v bundleOf minOf B <
              minLoadTiePotential v bundleOf minOf A)) := by
  by_cases hmax_high : 2 * L < maxLoad
  · rcases hhigh hmax_high with ⟨B, hBA, hpot⟩
    exact ⟨B, hBA, Or.inl hpot⟩
  · have hmax_le : maxLoad ≤ 2 * L := le_of_not_gt hmax_high
    by_cases hmin_low : minLoad ≤ L / 2
    · rcases hlow hmin_low hmax_le with ⟨B, hBA, hpot_eq, htie⟩
      exact ⟨B, hBA, Or.inr ⟨hpot_eq, htie⟩⟩
    · have hmin_gt : L / 2 < minLoad := lt_of_not_ge hmin_low
      have hmax_ge : 2 * L ≤ maxLoad := by
        by_contra hnot_ge
        have hmax_lt : maxLoad < 2 * L := lt_of_not_ge hnot_ge
        exact hnot_bounded (by
          intro i
          exact
            ⟨lt_of_lt_of_le hmin_gt (hmin_lower_A i),
              lt_of_le_of_lt (hmax_upper_A i) hmax_lt⟩)
      exact hboundary hmin_gt (le_antisymm hmax_le hmax_ge)

/--
Source-shaped Claim 3.4 branch step, reducing the top-level proof to the
strict upper-boundary case.  The strict high-source and low-only branches are
derived from the concrete min/max source move constructors.
-/
theorem claim34_branch_step_of_minmax_source_trichotomy
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc] [Nonempty Agent]
    [DecidableEq Agent] [DecidableEq Item]
    {bundleOf : Alloc → Agent → Finset Item} {v : Item → ℝ}
    {L : ℝ} {ratioOf : Alloc → ℝ} {minOf maxOf : Alloc → ℝ}
    (moveAlloc : Alloc → Agent → Agent → Item → Alloc)
    {A : Alloc} {minLoad maxLoad : ℝ}
    (hL : 0 < L)
    (havg :
      (∑ i : Agent, commonLoad v (bundleOf A i)) =
        (Fintype.card Agent : ℝ) * L)
    (hmin_lower :
      ∀ C : Alloc, ∀ i : Agent, minOf C ≤ commonLoad v (bundleOf C i))
    (hmin_attains :
      ∀ C : Alloc, ∃ i : Agent, commonLoad v (bundleOf C i) = minOf C)
    (hmax_upper :
      ∀ C : Alloc, ∀ i : Agent, commonLoad v (bundleOf C i) ≤ maxOf C)
    (hmax_attains :
      ∀ C : Alloc, ∃ i : Agent, commonLoad v (bundleOf C i) = maxOf C)
    (hminA : minOf A = minLoad)
    (hmaxA : maxOf A = maxLoad)
    (hmin_pos : 0 < minLoad)
    (hnot_bounded :
      ¬ ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf A i)))
    (hitem_nonneg :
      ∀ i : Agent, ∀ g : Item, g ∈ bundleOf A i → 0 ≤ v g)
    (hitem_lt :
      ∀ i : Agent, ∀ g : Item, g ∈ bundleOf A i → v g < L)
    (hunique :
      ∀ {i j : Agent} {g : Item},
        g ∈ bundleOf A i → g ∈ bundleOf A j → i = j)
    (hratio : ∀ C : Alloc, ratioOf C = loadRatio (minOf C) (maxOf C))
    (hbundle_move :
      ∀ source target g,
        bundleOf (moveAlloc A source target g) =
          moveBundle (bundleOf A) source target g) :
    ∃ B : Alloc,
      ratioOf B ≤ ratioOf A ∧
        (overfullBundleCardPotential v L (bundleOf B) <
            overfullBundleCardPotential v L (bundleOf A) ∨
          (overfullBundleCardPotential v L (bundleOf B) =
              overfullBundleCardPotential v L (bundleOf A) ∧
            minLoadTiePotential v bundleOf minOf B <
              minLoadTiePotential v bundleOf minOf A)) := by
  classical
  rcases hmax_attains A with ⟨source, hsource_max_raw⟩
  rcases hmin_attains A with ⟨target, htarget_min_raw⟩
  have hsource_max : commonLoad v (bundleOf A source) = maxLoad := by
    rw [hsource_max_raw, hmaxA]
  have htarget_min : commonLoad v (bundleOf A target) = minLoad := by
    rw [htarget_min_raw, hminA]
  refine
    claim34_branch_step_of_minmax_trichotomy
      (v := v) (L := L) (ratioOf := ratioOf) (bundleOf := bundleOf)
      (minOf := minOf) (A := A) (minLoad := minLoad) (maxLoad := maxLoad)
      ?_ ?_ hnot_bounded ?_ ?_ ?_
  · intro i
    rw [← hminA]
    exact hmin_lower A i
  · intro i
    rw [← hmaxA]
    exact hmax_upper A i
  · intro hmax_high
    exact
      claim34_high_source_branch_step_of_min_max_source_move
        (v := v) (L := L) (ratioOf := ratioOf)
        (bundleOf := bundleOf) (minOf := minOf) (maxOf := maxOf)
        moveAlloc hL havg hmin_lower hmin_attains hmax_upper hmax_attains
        hminA hmaxA hsource_max hmax_high hmin_pos
        (fun g hg => hitem_nonneg source g hg)
        (fun g hg => hitem_lt source g hg)
        hunique hratio (fun target g => hbundle_move source target g)
  · intro hmin_low hmax_le
    exact
      claim34_low_only_branch_step_of_min_max_source_move
        (v := v) (L := L) (ratioOf := ratioOf)
        (bundleOf := bundleOf) (minOf := minOf) (maxOf := maxOf)
        moveAlloc hL havg hmin_lower hmin_attains hmax_upper hmax_attains
        hminA hmaxA htarget_min hsource_max hmin_pos hmin_low hmax_le
        (fun g hg => hitem_nonneg source g hg)
        (fun g hg => hitem_lt source g hg)
        hunique hratio (fun g => hbundle_move source target g)
  · intro hmin_gt hmax_eq_twoL
    rcases
      claim34_boundary_branch_step_of_min_max_source_move
        (v := v) (L := L) (ratioOf := ratioOf)
        (bundleOf := bundleOf) (minOf := minOf) (maxOf := maxOf)
        moveAlloc hL havg hmin_lower hmin_attains hmax_upper hmax_attains
        hminA hmaxA htarget_min hsource_max hmin_pos hmin_gt hmax_eq_twoL
        (fun g hg => hitem_nonneg source g hg)
        (fun g hg => hitem_lt source g hg)
        hunique hratio (fun g => hbundle_move source target g) with
      ⟨B, hBA, hpot_eq, htie⟩
    exact ⟨B, hBA, Or.inr ⟨hpot_eq, htie⟩⟩

/--
Source-shaped Claim 3.4 step assembly.  If every optimal allocation outside
the paper load window admits a concrete low-target/high-source move, then the
finite-descent step required by `claim34_certificate_of_finite_descent` holds
for the global overfull-bundle-card potential.
-/
theorem claim34_hstep_of_local_reallocation
    {Agent Item Alloc : Type*} [Fintype Agent] [DecidableEq Agent]
    [DecidableEq Item]
    {v : Item → ℝ} {L : ℝ} {ratioOf : Alloc → ℝ}
    {bundleOf : Alloc → Agent → Finset Item}
    (moveAlloc : Alloc → Agent → Agent → Item → Alloc)
    (hL : 0 < L)
    (hlocal :
      ∀ A : Alloc,
        IsOptimalRatio ratioOf A →
          (¬ ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf A i))) →
            ∃ source target : Agent,
            ∃ g : Item,
            ∃ oldMin oldMax newMin newMax : ℝ,
              source ≠ target ∧
              g ∈ bundleOf A source ∧
              g ∉ bundleOf A target ∧
              0 < oldMin ∧
              0 ≤ oldMax ∧
              (∀ i : Agent,
                oldMin ≤ commonLoad v (bundleOf A i) ∧
                  commonLoad v (bundleOf A i) ≤ oldMax) ∧
              commonLoad v (bundleOf A target) < L / 2 ∧
              2 * L < commonLoad v (bundleOf A source) ∧
              0 ≤ v g ∧
              v g < L ∧
              (∀ i : Agent,
                newMin ≤
                  commonLoad v
                    (moveBundle (bundleOf A) source target g i)) ∧
              (∃ i : Agent,
                commonLoad v
                  (moveBundle (bundleOf A) source target g i) = newMin) ∧
              (∀ i : Agent,
                commonLoad v
                  (moveBundle (bundleOf A) source target g i) ≤ newMax) ∧
              (∃ i : Agent,
                commonLoad v
                  (moveBundle (bundleOf A) source target g i) = newMax) ∧
              ratioOf (moveAlloc A source target g) =
                loadRatio newMin newMax ∧
              ratioOf A = loadRatio oldMin oldMax ∧
              bundleOf (moveAlloc A source target g) =
                moveBundle (bundleOf A) source target g) :
    ∀ A : Alloc,
      IsOptimalRatio ratioOf A →
        (¬ ∀ i : Agent,
          boundedAroundAverage L (commonLoad v (bundleOf A i))) →
          ∃ B : Alloc,
            ratioOf B ≤ ratioOf A ∧
              overfullBundleCardPotential v L (bundleOf B) <
                overfullBundleCardPotential v L (bundleOf A) := by
  intro A hA hnot_bounded
  rcases hlocal A hA hnot_bounded with
    ⟨source, target, g, oldMin, oldMax, newMin, newMax,
      hsource_ne_target, hg_source, hg_target, holdMin_pos, holdMax_nonneg,
      hwithin, htarget_low, hsource_high, hg_nonneg, hg_lt,
      hnewMin_lower, hnewMin_attains, hnewMax_upper, hnewMax_attains,
      hratio_move, hratio_A, hbundle_move⟩
  let B : Alloc := moveAlloc A source target g
  refine ⟨B, ?_, ?_⟩
  · have hratio_le :
        loadRatio newMin newMax ≤ loadRatio oldMin oldMax :=
      (local_reallocation_certificate_of_low_target_high_source
        (bundle := bundleOf A) (v := v)
        hsource_ne_target hg_source hg_target hL holdMin_pos holdMax_nonneg
        hwithin htarget_low hsource_high hg_nonneg hg_lt
        hnewMin_lower hnewMin_attains hnewMax_upper hnewMax_attains).1
    simpa [B, hratio_move, hratio_A] using hratio_le
  · have hpotential :
        overfullBundleCardPotential v L
            (moveBundle (bundleOf A) source target g) <
          overfullBundleCardPotential v L (bundleOf A) :=
      overfullBundleCardPotential_decreases_of_moveBundle_low_target_high_source
        hsource_ne_target hg_source hg_target hL htarget_low hsource_high hg_lt
    simpa [B, hbundle_move] using hpotential

/--
Claim 3.4 assembly from concrete local reallocations: a starting optimal
allocation plus the source local-move step yields an optimal allocation whose
loads all lie in the paper window.
-/
theorem claim34_certificate_of_local_reallocation_descent
    {Agent Item Alloc : Type*} [Fintype Agent] [DecidableEq Agent]
    [DecidableEq Item]
    {v : Item → ℝ} {L : ℝ} {ratioOf : Alloc → ℝ}
    {bundleOf : Alloc → Agent → Finset Item}
    (moveAlloc : Alloc → Agent → Agent → Item → Alloc)
    (A₀ : Alloc) (hA₀ : IsOptimalRatio ratioOf A₀)
    (hL : 0 < L)
    (hlocal :
      ∀ A : Alloc,
        IsOptimalRatio ratioOf A →
          (¬ ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf A i))) →
            ∃ source target : Agent,
            ∃ g : Item,
            ∃ oldMin oldMax newMin newMax : ℝ,
              source ≠ target ∧
              g ∈ bundleOf A source ∧
              g ∉ bundleOf A target ∧
              0 < oldMin ∧
              0 ≤ oldMax ∧
              (∀ i : Agent,
                oldMin ≤ commonLoad v (bundleOf A i) ∧
                  commonLoad v (bundleOf A i) ≤ oldMax) ∧
              commonLoad v (bundleOf A target) < L / 2 ∧
              2 * L < commonLoad v (bundleOf A source) ∧
              0 ≤ v g ∧
              v g < L ∧
              (∀ i : Agent,
                newMin ≤
                  commonLoad v
                    (moveBundle (bundleOf A) source target g i)) ∧
              (∃ i : Agent,
                commonLoad v
                  (moveBundle (bundleOf A) source target g i) = newMin) ∧
              (∀ i : Agent,
                commonLoad v
                  (moveBundle (bundleOf A) source target g i) ≤ newMax) ∧
              (∃ i : Agent,
                commonLoad v
                  (moveBundle (bundleOf A) source target g i) = newMax) ∧
              ratioOf (moveAlloc A source target g) =
                loadRatio newMin newMax ∧
              ratioOf A = loadRatio oldMin oldMax ∧
              bundleOf (moveAlloc A source target g) =
                moveBundle (bundleOf A) source target g) :
    ∃ B : Alloc, Claim34Certificate v L ratioOf bundleOf B := by
  exact
    claim34_certificate_of_finite_descent
      (v := v) (L := L) (ratioOf := ratioOf) (bundleOf := bundleOf)
      (fun A : Alloc => overfullBundleCardPotential v L (bundleOf A))
      A₀ hA₀
      (claim34_hstep_of_local_reallocation
        (v := v) (L := L) (ratioOf := ratioOf) (bundleOf := bundleOf)
        moveAlloc hL hlocal)

/--
Source-shaped Claim 3.4 step assembly using the weaker high-source move: if
every not-yet-bounded optimal allocation admits a move from an overfull bundle
to a bundle of load at most `L`, then the finite-descent step holds.
-/
theorem claim34_hstep_of_high_source_reallocation
    {Agent Item Alloc : Type*} [Fintype Agent] [DecidableEq Agent]
    [DecidableEq Item]
    {v : Item → ℝ} {L : ℝ} {ratioOf : Alloc → ℝ}
    {bundleOf : Alloc → Agent → Finset Item}
    (moveAlloc : Alloc → Agent → Agent → Item → Alloc)
    (hL : 0 < L)
    (hlocal :
      ∀ A : Alloc,
        IsOptimalRatio ratioOf A →
          (¬ ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf A i))) →
            ∃ source target : Agent,
            ∃ g : Item,
            ∃ oldMin oldMax newMin newMax : ℝ,
              source ≠ target ∧
              g ∈ bundleOf A source ∧
              g ∉ bundleOf A target ∧
              0 < oldMin ∧
              0 ≤ oldMax ∧
              (∀ i : Agent,
                oldMin ≤ commonLoad v (bundleOf A i) ∧
                  commonLoad v (bundleOf A i) ≤ oldMax) ∧
              commonLoad v (bundleOf A target) ≤ L ∧
              2 * L < commonLoad v (bundleOf A source) ∧
              0 ≤ v g ∧
              v g < L ∧
              (∀ i : Agent,
                newMin ≤
                  commonLoad v
                    (moveBundle (bundleOf A) source target g i)) ∧
              (∃ i : Agent,
                commonLoad v
                  (moveBundle (bundleOf A) source target g i) = newMin) ∧
              (∀ i : Agent,
                commonLoad v
                  (moveBundle (bundleOf A) source target g i) ≤ newMax) ∧
              (∃ i : Agent,
                commonLoad v
                  (moveBundle (bundleOf A) source target g i) = newMax) ∧
              ratioOf (moveAlloc A source target g) =
                loadRatio newMin newMax ∧
              ratioOf A = loadRatio oldMin oldMax ∧
              bundleOf (moveAlloc A source target g) =
                moveBundle (bundleOf A) source target g) :
    ∀ A : Alloc,
      IsOptimalRatio ratioOf A →
        (¬ ∀ i : Agent,
          boundedAroundAverage L (commonLoad v (bundleOf A i))) →
          ∃ B : Alloc,
            ratioOf B ≤ ratioOf A ∧
              overfullBundleCardPotential v L (bundleOf B) <
                overfullBundleCardPotential v L (bundleOf A) := by
  intro A hA hnot_bounded
  rcases hlocal A hA hnot_bounded with
    ⟨source, target, g, oldMin, oldMax, newMin, newMax,
      hsource_ne_target, hg_source, hg_target, holdMin_pos, holdMax_nonneg,
      hwithin, htarget_le, hsource_high, hg_nonneg, hg_lt,
      hnewMin_lower, hnewMin_attains, hnewMax_upper, hnewMax_attains,
      hratio_move, hratio_A, hbundle_move⟩
  let B : Alloc := moveAlloc A source target g
  refine ⟨B, ?_, ?_⟩
  · have hratio_le :
        loadRatio newMin newMax ≤ loadRatio oldMin oldMax :=
      (local_reallocation_certificate_of_le_average_target_high_source
        (bundle := bundleOf A) (v := v)
        hsource_ne_target hg_source hg_target hL holdMin_pos holdMax_nonneg
        hwithin htarget_le hsource_high hg_nonneg hg_lt
        hnewMin_lower hnewMin_attains hnewMax_upper hnewMax_attains).1
    simpa [B, hratio_move, hratio_A] using hratio_le
  · have hpotential :
        overfullBundleCardPotential v L
            (moveBundle (bundleOf A) source target g) <
          overfullBundleCardPotential v L (bundleOf A) :=
      overfullBundleCardPotential_decreases_of_moveBundle_le_average_target_high_source
        hsource_ne_target hg_source hg_target hL htarget_le hsource_high hg_lt
    simpa [B, hbundle_move] using hpotential

/--
Claim 3.4 assembly from high-source local reallocations: a starting optimal
allocation plus the weaker source move premise yields an optimal allocation
whose loads all lie in the paper window.
-/
theorem claim34_certificate_of_high_source_reallocation_descent
    {Agent Item Alloc : Type*} [Fintype Agent] [DecidableEq Agent]
    [DecidableEq Item]
    {v : Item → ℝ} {L : ℝ} {ratioOf : Alloc → ℝ}
    {bundleOf : Alloc → Agent → Finset Item}
    (moveAlloc : Alloc → Agent → Agent → Item → Alloc)
    (A₀ : Alloc) (hA₀ : IsOptimalRatio ratioOf A₀)
    (hL : 0 < L)
    (hlocal :
      ∀ A : Alloc,
        IsOptimalRatio ratioOf A →
          (¬ ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf A i))) →
            ∃ source target : Agent,
            ∃ g : Item,
            ∃ oldMin oldMax newMin newMax : ℝ,
              source ≠ target ∧
              g ∈ bundleOf A source ∧
              g ∉ bundleOf A target ∧
              0 < oldMin ∧
              0 ≤ oldMax ∧
              (∀ i : Agent,
                oldMin ≤ commonLoad v (bundleOf A i) ∧
                  commonLoad v (bundleOf A i) ≤ oldMax) ∧
              commonLoad v (bundleOf A target) ≤ L ∧
              2 * L < commonLoad v (bundleOf A source) ∧
              0 ≤ v g ∧
              v g < L ∧
              (∀ i : Agent,
                newMin ≤
                  commonLoad v
                    (moveBundle (bundleOf A) source target g i)) ∧
              (∃ i : Agent,
                commonLoad v
                  (moveBundle (bundleOf A) source target g i) = newMin) ∧
              (∀ i : Agent,
                commonLoad v
                  (moveBundle (bundleOf A) source target g i) ≤ newMax) ∧
              (∃ i : Agent,
                commonLoad v
                  (moveBundle (bundleOf A) source target g i) = newMax) ∧
              ratioOf (moveAlloc A source target g) =
                loadRatio newMin newMax ∧
              ratioOf A = loadRatio oldMin oldMax ∧
              bundleOf (moveAlloc A source target g) =
                moveBundle (bundleOf A) source target g) :
    ∃ B : Alloc, Claim34Certificate v L ratioOf bundleOf B := by
  exact
    claim34_certificate_of_finite_descent
      (v := v) (L := L) (ratioOf := ratioOf) (bundleOf := bundleOf)
      (fun A : Alloc => overfullBundleCardPotential v L (bundleOf A))
      A₀ hA₀
      (claim34_hstep_of_high_source_reallocation
        (v := v) (L := L) (ratioOf := ratioOf) (bundleOf := bundleOf)
        moveAlloc hL hlocal)

/--
Claim 3.4 assembly from the two paper descent branches.  A high-source move
decreases the overfull-bundle potential; the complementary low-only move keeps
that primary potential fixed while decreasing the finite min-load tie-breaker.
-/
theorem claim34_certificate_of_branching_potential_descent
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc]
    {v : Item → ℝ} {L : ℝ} {ratioOf : Alloc → ℝ}
    {bundleOf : Alloc → Agent → Finset Item}
    (minOf : Alloc → ℝ) (A₀ : Alloc)
    (hA₀ : IsOptimalRatio ratioOf A₀)
    (hstep :
      ∀ A : Alloc,
        IsOptimalRatio ratioOf A →
          (¬ ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf A i))) →
            ∃ B : Alloc,
              ratioOf B ≤ ratioOf A ∧
                (overfullBundleCardPotential v L (bundleOf B) <
                    overfullBundleCardPotential v L (bundleOf A) ∨
                  (overfullBundleCardPotential v L (bundleOf B) =
                      overfullBundleCardPotential v L (bundleOf A) ∧
                    minLoadTiePotential v bundleOf minOf B <
                      minLoadTiePotential v bundleOf minOf A))) :
    ∃ B : Alloc, Claim34Certificate v L ratioOf bundleOf B := by
  exact
    claim34_certificate_of_lexicographic_finite_descent
      (v := v) (L := L) (ratioOf := ratioOf) (bundleOf := bundleOf)
      (fun A : Alloc => overfullBundleCardPotential v L (bundleOf A))
      (fun A : Alloc => minLoadTiePotential v bundleOf minOf A)
      (Fintype.card Alloc * (Fintype.card Agent + 1) + Fintype.card Agent)
      A₀ hA₀
      (minLoadTiePotential_le_card_bound v bundleOf minOf)
      hstep

/--
Claim 3.4 assembly from min/max source data.  Once the source model provides
average-load preservation, honest min/max accessors, positive minima along the
unbounded optimal path, small nonnegative goods, unique ownership, and the
bundle update law for a concrete move operation, the local branch step is no
longer an external premise: it is supplied by
`claim34_branch_step_of_minmax_source_trichotomy`.
-/
theorem claim34_certificate_of_minmax_source_trichotomy
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc] [Nonempty Agent]
    [DecidableEq Agent] [DecidableEq Item]
    {bundleOf : Alloc → Agent → Finset Item} {v : Item → ℝ}
    {L : ℝ} {ratioOf : Alloc → ℝ} {minOf maxOf : Alloc → ℝ}
    (moveAlloc : Alloc → Agent → Agent → Item → Alloc)
    (A₀ : Alloc) (hA₀ : IsOptimalRatio ratioOf A₀)
    (hL : 0 < L)
    (havg :
      ∀ A : Alloc,
        IsOptimalRatio ratioOf A →
          (∑ i : Agent, commonLoad v (bundleOf A i)) =
            (Fintype.card Agent : ℝ) * L)
    (hmin_lower :
      ∀ C : Alloc, ∀ i : Agent, minOf C ≤ commonLoad v (bundleOf C i))
    (hmin_attains :
      ∀ C : Alloc, ∃ i : Agent, commonLoad v (bundleOf C i) = minOf C)
    (hmax_upper :
      ∀ C : Alloc, ∀ i : Agent, commonLoad v (bundleOf C i) ≤ maxOf C)
    (hmax_attains :
      ∀ C : Alloc, ∃ i : Agent, commonLoad v (bundleOf C i) = maxOf C)
    (hmin_pos :
      ∀ A : Alloc,
        IsOptimalRatio ratioOf A →
          (¬ ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf A i))) →
            0 < minOf A)
    (hitem_nonneg :
      ∀ A : Alloc, ∀ i : Agent, ∀ g : Item, g ∈ bundleOf A i → 0 ≤ v g)
    (hitem_lt :
      ∀ A : Alloc, ∀ i : Agent, ∀ g : Item, g ∈ bundleOf A i → v g < L)
    (hunique :
      ∀ A : Alloc, ∀ {i j : Agent} {g : Item},
        g ∈ bundleOf A i → g ∈ bundleOf A j → i = j)
    (hratio : ∀ C : Alloc, ratioOf C = loadRatio (minOf C) (maxOf C))
    (hbundle_move :
      ∀ A source target g,
        bundleOf (moveAlloc A source target g) =
          moveBundle (bundleOf A) source target g) :
    ∃ B : Alloc, Claim34Certificate v L ratioOf bundleOf B := by
  refine
    claim34_certificate_of_branching_potential_descent
      (v := v) (L := L) (ratioOf := ratioOf) (bundleOf := bundleOf)
      minOf A₀ hA₀ ?_
  intro A hA hnot_bounded
  exact
    claim34_branch_step_of_minmax_source_trichotomy
      (v := v) (L := L) (ratioOf := ratioOf)
      (bundleOf := bundleOf) (minOf := minOf) (maxOf := maxOf)
      moveAlloc (A := A) (minLoad := minOf A) (maxLoad := maxOf A)
      hL (havg A hA) hmin_lower hmin_attains hmax_upper hmax_attains
      rfl rfl (hmin_pos A hA hnot_bounded) hnot_bounded
      (hitem_nonneg A) (hitem_lt A) (hunique A) hratio
      (fun source target g => hbundle_move A source target g)

/--
Claim 3.4 assembly with concrete finite min/max loads.  This specializes the
source-data assembly to the canonical minimum and maximum loads of each finite
allocation, so callers no longer need to provide separate min/max accessor
proofs.
-/
theorem claim34_certificate_of_concrete_minmax_source_trichotomy
    {Agent Item Alloc : Type*} [Fintype Agent] [Fintype Alloc] [Nonempty Agent]
    [DecidableEq Agent] [DecidableEq Item]
    {bundleOf : Alloc → Agent → Finset Item} {v : Item → ℝ}
    {L : ℝ} {ratioOf : Alloc → ℝ}
    (moveAlloc : Alloc → Agent → Agent → Item → Alloc)
    (A₀ : Alloc) (hA₀ : IsOptimalRatio ratioOf A₀)
    (hL : 0 < L)
    (havg :
      ∀ A : Alloc,
        IsOptimalRatio ratioOf A →
          (∑ i : Agent, commonLoad v (bundleOf A i)) =
            (Fintype.card Agent : ℝ) * L)
    (hmin_pos :
      ∀ A : Alloc,
        IsOptimalRatio ratioOf A →
          (¬ ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf A i))) →
            0 < minCommonLoad v (bundleOf A))
    (hitem_nonneg :
      ∀ A : Alloc, ∀ i : Agent, ∀ g : Item, g ∈ bundleOf A i → 0 ≤ v g)
    (hitem_lt :
      ∀ A : Alloc, ∀ i : Agent, ∀ g : Item, g ∈ bundleOf A i → v g < L)
    (hunique :
      ∀ A : Alloc, ∀ {i j : Agent} {g : Item},
        g ∈ bundleOf A i → g ∈ bundleOf A j → i = j)
    (hratio :
      ∀ C : Alloc,
        ratioOf C =
          loadRatio (minCommonLoad v (bundleOf C))
            (maxCommonLoad v (bundleOf C)))
    (hbundle_move :
      ∀ A source target g,
        bundleOf (moveAlloc A source target g) =
          moveBundle (bundleOf A) source target g) :
    ∃ B : Alloc, Claim34Certificate v L ratioOf bundleOf B := by
  exact
    claim34_certificate_of_minmax_source_trichotomy
      (v := v) (L := L) (ratioOf := ratioOf) (bundleOf := bundleOf)
      (minOf := fun C : Alloc => minCommonLoad v (bundleOf C))
      (maxOf := fun C : Alloc => maxCommonLoad v (bundleOf C))
      moveAlloc A₀ hA₀ hL havg
      (fun C i => minCommonLoad_le (v := v) (bundle := bundleOf C) i)
      (fun C => exists_commonLoad_eq_minCommonLoad (v := v) (bundle := bundleOf C))
      (fun C i => commonLoad_le_maxCommonLoad (v := v) (bundle := bundleOf C) i)
      (fun C => exists_commonLoad_eq_maxCommonLoad (v := v) (bundle := bundleOf C))
      hmin_pos hitem_nonneg hitem_lt hunique hratio hbundle_move

end

end Theorem34
end LMMS04FairDivision
