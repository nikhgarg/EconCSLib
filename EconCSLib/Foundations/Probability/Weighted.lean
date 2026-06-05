import EconCSLib.Foundations.Probability.FiniteExpectation
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

/-!
# Finite Weighted Probability Mass Functions

This file provides small reusable constructors for finite PMFs obtained by
normalizing nonnegative real weights.  The main paper-facing use is a
deferred-decision draw from a distribution after zeroing the mass of already
drawn alternatives.
-/

namespace EconCSLib

open scoped BigOperators

/-- A finite weighted sum of nonnegative real values is nonnegative. -/
theorem weightedSum_nonneg {ι : Type*} [Fintype ι]
    (weight value : ι → ℝ)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hvalue_nonneg : ∀ i, 0 ≤ value i) :
    0 ≤ ∑ i : ι, weight i * value i := by
  exact Finset.sum_nonneg (by
    intro i _
    exact mul_nonneg (hweight_nonneg i) (hvalue_nonneg i))

/-- Nonnegative weighted sums preserve pointwise order. -/
theorem weightedSum_le_weightedSum_of_pointwise_le {ι : Type*} [Fintype ι]
    (weight lower upper : ι → ℝ)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hle : ∀ i, lower i ≤ upper i) :
    (∑ i : ι, weight i * lower i) ≤
      ∑ i : ι, weight i * upper i := by
  exact Finset.sum_le_sum (by
    intro i _
    exact mul_le_mul_of_nonneg_left (hle i) (hweight_nonneg i))

/-- A nonnegative finite weight vector with total mass one has a positive entry. -/
theorem exists_positive_weight_of_nonneg_sum_eq_one {ι : Type*} [Fintype ι]
    (weight : ι → ℝ)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_sum : (∑ i : ι, weight i) = 1) :
    ∃ i : ι, 0 < weight i := by
  by_contra hnone
  have hzero : ∀ i : ι, weight i = 0 := by
    intro i
    exact le_antisymm
      (not_lt.mp (by
        intro hpos
        exact hnone ⟨i, hpos⟩))
      (hweight_nonneg i)
  have hsum_zero : (∑ i : ι, weight i) = 0 := by
    simp [hzero]
  linarith

/--
A convex combination of strictly positive values is strictly positive when the
weights are nonnegative and sum to one.
-/
theorem weightedSum_pos_of_nonneg_sum_eq_one {ι : Type*} [Fintype ι]
    (weight value : ι → ℝ)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_sum : (∑ i : ι, weight i) = 1)
    (hvalue_pos : ∀ i, 0 < value i) :
    0 < ∑ i : ι, weight i * value i := by
  rcases exists_positive_weight_of_nonneg_sum_eq_one
      weight hweight_nonneg hweight_sum with
    ⟨i₀, hpos₀⟩
  refine Finset.sum_pos' ?_ ?_
  · intro i _
    exact mul_nonneg (hweight_nonneg i) (le_of_lt (hvalue_pos i))
  · exact ⟨i₀, Finset.mem_univ _, mul_pos hpos₀ (hvalue_pos i₀)⟩

/--
A nonnegative finite weighted sum is positive as soon as one positive-weight
component has a positive value.
-/
theorem weightedSum_pos_of_positive_component {ι : Type*} [Fintype ι]
    (weight value : ι → ℝ)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hvalue_nonneg : ∀ i, 0 ≤ value i)
    {i₀ : ι}
    (hweight_pos : 0 < weight i₀)
    (hvalue_pos : 0 < value i₀) :
    0 < ∑ i : ι, weight i * value i := by
  refine Finset.sum_pos' ?_ ?_
  · intro i _
    exact mul_nonneg (hweight_nonneg i) (hvalue_nonneg i)
  · exact ⟨i₀, Finset.mem_univ _, mul_pos hweight_pos hvalue_pos⟩

/--
A finite mixture of two mutually exclusive one-step probabilities is still
sub-probability valued.
-/
theorem weightedPairProb_sum_le_one {ι : Type*} [Fintype ι]
    (weight p q : ι → ℝ)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_sum : (∑ i : ι, weight i) = 1)
    (hpq_le_one : ∀ i, p i + q i ≤ 1) :
    (∑ i : ι, weight i * p i) +
      (∑ i : ι, weight i * q i) ≤ 1 := by
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i : ι, (weight i * p i + weight i * q i))
        = ∑ i : ι, weight i * (p i + q i) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ ≤ ∑ i : ι, weight i * 1 := by
          refine Finset.sum_le_sum ?_
          intro i _
          exact mul_le_mul_of_nonneg_left
            (hpq_le_one i) (hweight_nonneg i)
    _ = 1 := by
          simpa using hweight_sum

/--
A finite mixture of valid two-way probabilities is again a valid two-way
probability pair.
-/
theorem weightedPairProb_valid {ι : Type*} [Fintype ι]
    (weight p q : ι → ℝ)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_sum : (∑ i : ι, weight i) = 1)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hq_nonneg : ∀ i, 0 ≤ q i)
    (hpq_le_one : ∀ i, p i + q i ≤ 1) :
    0 ≤ ∑ i : ι, weight i * p i ∧
      0 ≤ ∑ i : ι, weight i * q i ∧
        (∑ i : ι, weight i * p i) +
          (∑ i : ι, weight i * q i) ≤ 1 := by
  exact
    ⟨weightedSum_nonneg weight p hweight_nonneg hp_nonneg,
      weightedSum_nonneg weight q hweight_nonneg hq_nonneg,
      weightedPairProb_sum_le_one weight p q
        hweight_nonneg hweight_sum hpq_le_one⟩

/--
Normalize a nonnegative finite real weight vector with positive total mass into
a finite PMF.
-/
noncomputable def finiteWeightedPMF {α : Type*} [Fintype α]
    (weight : α → ℝ)
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (htotal_pos : 0 < ∑ a, weight a) : PMF α :=
  PMF.ofFintype
    (fun a => ENNReal.ofReal (weight a / ∑ b, weight b))
    (by
      have hterm_nonneg : ∀ a : α, 0 ≤ weight a / ∑ b, weight b := by
        intro a
        exact div_nonneg (hweight_nonneg a) (le_of_lt htotal_pos)
      have hsum_real :
          (∑ a : α, weight a / ∑ b, weight b) = 1 := by
        rw [← Finset.sum_div]
        field_simp [ne_of_gt htotal_pos]
      calc
        ∑ a : α, ENNReal.ofReal (weight a / ∑ b, weight b)
            = ENNReal.ofReal (∑ a : α, weight a / ∑ b, weight b) := by
              symm
              exact ENNReal.ofReal_sum_of_nonneg
                (s := (Finset.univ : Finset α))
                (f := fun a => weight a / ∑ b, weight b)
                (by intro a _; exact hterm_nonneg a)
        _ = ENNReal.ofReal 1 := by rw [hsum_real]
        _ = 1 := by norm_num)

@[simp]
theorem finiteWeightedPMF_apply_toReal {α : Type*} [Fintype α]
    (weight : α → ℝ)
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (htotal_pos : 0 < ∑ a, weight a) (a : α) :
    (finiteWeightedPMF weight hweight_nonneg htotal_pos a).toReal =
      weight a / ∑ b, weight b := by
  unfold finiteWeightedPMF
  have hterm_nonneg : 0 ≤ weight a / ∑ b, weight b := by
    exact div_nonneg (hweight_nonneg a) (le_of_lt htotal_pos)
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal hterm_nonneg

/--
Expectation under a normalized finite weighted PMF is the normalized weighted
average of the function values.
-/
theorem finiteWeightedPMF_pmfExp_eq_sum_div {α : Type*}
    [Fintype α] [DecidableEq α]
    (weight : α → ℝ)
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (htotal_pos : 0 < ∑ a, weight a)
    (f : α → ℝ) :
    pmfExp (finiteWeightedPMF weight hweight_nonneg htotal_pos) f =
      ∑ a : α, (weight a / ∑ b, weight b) * f a := by
  unfold pmfExp
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [finiteWeightedPMF_apply_toReal]

/--
Expectation under a finite weighted PMF whose weights sum to one is the
un-normalized weighted sum.
-/
theorem finiteWeightedPMF_pmfExp_eq_weighted_sum_of_sum_eq_one {α : Type*}
    [Fintype α] [DecidableEq α]
    (weight : α → ℝ)
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (hsum : (∑ a : α, weight a) = 1)
    (f : α → ℝ) :
    pmfExp
        (finiteWeightedPMF weight hweight_nonneg
          (by simpa [hsum] using zero_lt_one))
        f =
      ∑ a : α, weight a * f a := by
  rw [finiteWeightedPMF_pmfExp_eq_sum_div]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [hsum, div_one]

/--
The available mass after excluding a finite forbidden set, written as a full
type sum with zero mass on forbidden points.
-/
noncomputable def finiteAvailableWeight {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α) : ℝ :=
  ∑ a : α, if a ∈ forbidden then 0 else baseWeight a

/-- Scaling all base weights scales the available mass by the same factor. -/
theorem finiteAvailableWeight_const_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α) (c : ℝ) :
    finiteAvailableWeight (fun a => c * baseWeight a) forbidden =
      c * finiteAvailableWeight baseWeight forbidden := by
  classical
  unfold finiteAvailableWeight
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a _ha
  by_cases hmem : a ∈ forbidden <;> simp [hmem]

/--
Normalize a finite nonnegative weight vector after excluding a finite forbidden
set.  Forbidden atoms have zero weight and all other atoms retain their base
weights.
-/
noncomputable def finiteWeightedPMFExcluding {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable_pos : 0 < finiteAvailableWeight baseWeight forbidden) : PMF α :=
  finiteWeightedPMF
    (fun a => if a ∈ forbidden then 0 else baseWeight a)
    (by
      intro a
      by_cases ha : a ∈ forbidden
      · simp [ha]
      · simp [ha, hbase_nonneg a])
    (by simpa [finiteAvailableWeight] using havailable_pos)

@[simp]
theorem finiteWeightedPMFExcluding_apply_toReal_of_not_mem
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable_pos : 0 < finiteAvailableWeight baseWeight forbidden)
    {a : α} (ha : a ∉ forbidden) :
    (finiteWeightedPMFExcluding
        baseWeight forbidden hbase_nonneg havailable_pos a).toReal =
      baseWeight a / finiteAvailableWeight baseWeight forbidden := by
  simp [finiteWeightedPMFExcluding, finiteAvailableWeight, ha]

@[simp]
theorem finiteWeightedPMFExcluding_apply_toReal_of_mem
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable_pos : 0 < finiteAvailableWeight baseWeight forbidden)
    {a : α} (ha : a ∈ forbidden) :
    (finiteWeightedPMFExcluding
      baseWeight forbidden hbase_nonneg havailable_pos a).toReal = 0 := by
  simp [finiteWeightedPMFExcluding, ha]

theorem finiteAvailableWeight_eq_subtype_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α) :
    finiteAvailableWeight baseWeight forbidden =
      ∑ a : {a // a ∉ forbidden}, baseWeight a.1 := by
  classical
  calc
    finiteAvailableWeight baseWeight forbidden
        = ∑ a : α, if a ∉ forbidden then baseWeight a else 0 := by
            unfold finiteAvailableWeight
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases ha : a ∈ forbidden <;> simp [ha]
    _ = ∑ a ∈ (Finset.univ.filter fun a : α => a ∉ forbidden), baseWeight a := by
            rw [Finset.sum_filter]
    _ = ∑ a : {a // a ∉ forbidden}, baseWeight a.1 := by
            exact Finset.sum_subtype
              (s := (Finset.univ.filter fun a : α => a ∉ forbidden))
              (by intro a; simp)
              baseWeight

theorem finiteAvailableWeight_pos_of_exists_not_mem_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    {a : α} (ha : a ∉ forbidden) (hpos : 0 < baseWeight a) :
    0 < finiteAvailableWeight baseWeight forbidden := by
  classical
  unfold finiteAvailableWeight
  have hterm_nonneg :
      ∀ b ∈ (Finset.univ : Finset α),
        0 ≤ (if b ∈ forbidden then 0 else baseWeight b) := by
    intro b _hb
    by_cases hb_forbidden : b ∈ forbidden
    · simp [hb_forbidden]
    · simp [hb_forbidden, hbase_nonneg b]
  have hsingle_le :
      (if a ∈ forbidden then 0 else baseWeight a) ≤
        ∑ b : α, if b ∈ forbidden then 0 else baseWeight b :=
    Finset.single_le_sum hterm_nonneg (Finset.mem_univ a)
  have hsingle_pos : 0 < (if a ∈ forbidden then 0 else baseWeight a) := by
    simp [ha, hpos]
  exact lt_of_lt_of_le hsingle_pos hsingle_le

theorem finiteAvailableWeight_pos_of_full_support_of_card_lt
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (hfull_support : ∀ a, 0 < baseWeight a)
    (hcard_lt : forbidden.card < Fintype.card α) :
    0 < finiteAvailableWeight baseWeight forbidden := by
  classical
  have hexists : ∃ a : α, a ∉ forbidden := by
    by_contra hnot
    push Not at hnot
    have huniv_subset : (Finset.univ : Finset α) ⊆ forbidden := by
      intro a _ha
      exact hnot a
    have hcard_ge : Fintype.card α ≤ forbidden.card := by
      simpa using Finset.card_le_card huniv_subset
    omega
  rcases hexists with ⟨a, ha⟩
  exact finiteAvailableWeight_pos_of_exists_not_mem_pos
    baseWeight forbidden hbase_nonneg ha (hfull_support a)

/--
The normalized weighted draw on the subtype of points that are not forbidden.
Unlike `finiteWeightedPMFExcluding`, the sample space itself rules out
forbidden atoms.
-/
noncomputable def finiteWeightedPMFAvailable
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable_pos : 0 < finiteAvailableWeight baseWeight forbidden) :
    PMF {a // a ∉ forbidden} :=
  finiteWeightedPMF
    (fun a : {a // a ∉ forbidden} => baseWeight a.1)
    (by intro a; exact hbase_nonneg a.1)
    (by
      rw [← finiteAvailableWeight_eq_subtype_sum baseWeight forbidden]
      exact havailable_pos)

@[simp]
theorem finiteWeightedPMFAvailable_apply_toReal
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (havailable_pos : 0 < finiteAvailableWeight baseWeight forbidden)
    (a : {a // a ∉ forbidden}) :
    (finiteWeightedPMFAvailable
        baseWeight forbidden hbase_nonneg havailable_pos a).toReal =
      baseWeight a.1 / finiteAvailableWeight baseWeight forbidden := by
  rw [finiteWeightedPMFAvailable]
  rw [finiteWeightedPMF_apply_toReal]
  rw [← finiteAvailableWeight_eq_subtype_sum baseWeight forbidden]

/-- Split total mass into forbidden and available mass. -/
theorem finiteAvailableWeight_add_forbidden_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α) :
    finiteAvailableWeight baseWeight forbidden +
      ∑ a ∈ forbidden, baseWeight a =
        ∑ a : α, baseWeight a := by
  classical
  unfold finiteAvailableWeight
  calc
    (∑ a : α, if a ∈ forbidden then 0 else baseWeight a) +
        ∑ a ∈ forbidden, baseWeight a
        = (∑ a : α, if a ∈ forbidden then 0 else baseWeight a) +
            ∑ a : α, if a ∈ forbidden then baseWeight a else 0 := by
          congr 1
          symm
          rw [Finset.sum_ite]
          simp
    _ = ∑ a : α,
          ((if a ∈ forbidden then 0 else baseWeight a) +
            if a ∈ forbidden then baseWeight a else 0) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ a : α, baseWeight a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases ha : a ∈ forbidden <;> simp [ha]

/--
Adding one newly forbidden atom subtracts that atom's weight from the available
mass.
-/
theorem finiteAvailableWeight_insert_eq_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α) {a : α}
    (ha : a ∉ forbidden) :
    finiteAvailableWeight baseWeight (insert a forbidden) =
      finiteAvailableWeight baseWeight forbidden - baseWeight a := by
  classical
  unfold finiteAvailableWeight
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (s := Finset.univ) (i := a)
    (by simp)]
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (s := Finset.univ) (i := a)
    (by simp)]
  have hfilter :
      ∑ x ∈ (Finset.univ \ {a}), (if x ∈ insert a forbidden then 0 else baseWeight x) =
        ∑ x ∈ (Finset.univ \ {a}), (if x ∈ forbidden then 0 else baseWeight x) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxa : x ≠ a := by
      exact fun h => by
        have : x ∈ ({a} : Finset α) := by simp [h]
        exact (Finset.mem_sdiff.mp hx).2 this
    by_cases hxf : x ∈ forbidden <;> simp [hxf, hxa]
  rw [hfilter]
  simp [ha]

/--
If every proper forbidden set leaves positive available mass, then every atom
has positive base weight.
-/
theorem finiteWeight_pos_of_available
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ)
    (havailable : ∀ forbidden : Finset α,
      forbidden.card < Fintype.card α →
        0 < finiteAvailableWeight baseWeight forbidden)
    (a : α) :
    0 < baseWeight a := by
  classical
  let forbidden := (Finset.univ : Finset α).erase a
  have hcard :
      forbidden.card < Fintype.card α := by
    have hlt :=
      Finset.card_erase_lt_of_mem
        (s := (Finset.univ : Finset α)) (a := a)
        (by simp)
    simpa [forbidden] using hlt
  have havail := havailable forbidden hcard
  have havail_eq :
      finiteAvailableWeight baseWeight forbidden = baseWeight a := by
    dsimp [forbidden]
    simp [finiteAvailableWeight]
  simpa [havail_eq] using havail

/--
If the base weights have total mass one, the available mass after excluding a
set is `1 - prevMass`, where `prevMass` is the mass of that set.
-/
theorem finiteAvailableWeight_eq_one_sub_forbidden_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α) (prevMass : ℝ)
    (hbase_sum : ∑ a : α, baseWeight a = 1)
    (hprevMass : prevMass = ∑ a ∈ forbidden, baseWeight a) :
    finiteAvailableWeight baseWeight forbidden = 1 - prevMass := by
  have hsplit := finiteAvailableWeight_add_forbidden_sum baseWeight forbidden
  linarith

/--
Filtered weighted draw formula in the `1 - prevMass` form used by
without-replacement deferred-decision arguments.
-/
theorem finiteWeightedPMFExcluding_apply_toReal_eq_div_one_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    (baseWeight : α → ℝ) (forbidden : Finset α) (prevMass : ℝ)
    (hbase_nonneg : ∀ a, 0 ≤ baseWeight a)
    (hbase_sum : ∑ a : α, baseWeight a = 1)
    (hprevMass : prevMass = ∑ a ∈ forbidden, baseWeight a)
    (havailable_pos : 0 < finiteAvailableWeight baseWeight forbidden)
    {a : α} (ha : a ∉ forbidden) :
    (finiteWeightedPMFExcluding
        baseWeight forbidden hbase_nonneg havailable_pos a).toReal =
      baseWeight a / (1 - prevMass) := by
  rw [finiteWeightedPMFExcluding_apply_toReal_of_not_mem
    baseWeight forbidden hbase_nonneg havailable_pos ha]
  rw [finiteAvailableWeight_eq_one_sub_forbidden_mass
    baseWeight forbidden prevMass hbase_sum hprevMass]

end EconCSLib
