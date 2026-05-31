import LMMS04FairDivision.Theorem33IdenticalUtilities

/-!
# LMMS Theorem 3.3: rounded-instance construction certificate

The proof of Theorem 3.3 rounds an identical-utilities instance, searches a
finite set of rounded bundle types with an integer program, then transfers the
rounded optimum back to the original instance using Lemma 3.5.

This file formalizes that source-shaped seam.  The construction and IP search
remain certificate fields; the closed theorem says that such a certificate is
enough to obtain the model-level `(1 + epsilon)` ratio guarantee from the
existing Theorem 3.3 / Lemma 3.5 transfer algebra.
-/

open scoped BigOperators

namespace LMMS04FairDivision
namespace Theorem33

noncomputable section

/-- Rounded value indices `k` with `lambda ≤ k ≤ lambda^2`. -/
abbrev RoundedValueIndex (lambda : ℕ) :=
  {k : Fin (lambda ^ 2 + 1) // lambda ≤ k.val}

instance roundedValueIndexFintype (lambda : ℕ) :
    Fintype (RoundedValueIndex lambda) :=
  inferInstance

/-- The number of rounded value indices is at most the ambient `lambda^2 + 1` box. -/
theorem roundedValueIndex_card_le (lambda : ℕ) :
    Fintype.card (RoundedValueIndex lambda) ≤ lambda ^ 2 + 1 := by
  simpa [RoundedValueIndex] using
    Fintype.card_subtype_le
      (fun k : Fin (lambda ^ 2 + 1) => lambda ≤ k.val)

/-- The natural-number value of a rounded value index. -/
def roundedValueIndexValue {lambda : ℕ} (k : RoundedValueIndex lambda) : ℕ :=
  k.1.val

/-- A rounded value index is at least `lambda`. -/
theorem roundedValueIndexValue_lower {lambda : ℕ}
    (k : RoundedValueIndex lambda) :
    lambda ≤ roundedValueIndexValue k := by
  exact k.2

/-- A rounded value index is at most `lambda^2`. -/
theorem roundedValueIndexValue_upper {lambda : ℕ}
    (k : RoundedValueIndex lambda) :
    roundedValueIndexValue k ≤ lambda ^ 2 := by
  exact Nat.le_of_lt_succ k.1.isLt

/-- The rounded value `k L / lambda^2` attached to a finite rounded index. -/
def roundedValue (L : ℝ) (lambda : ℕ) (k : RoundedValueIndex lambda) : ℝ :=
  (roundedValueIndexValue k : ℝ) * L / ((lambda : ℝ) ^ 2)

/--
A player bundle type in the rounded instance: for every rounded value index,
the type records how many goods of that value the player receives.
-/
structure RoundedBundleType (lambda : ℕ) where
  count : RoundedValueIndex lambda → ℕ

/-- Utility/load of a rounded bundle type. -/
def roundedBundleTypeLoad (L : ℝ) {lambda : ℕ}
    (t : RoundedBundleType lambda) : ℝ :=
  ∑ k : RoundedValueIndex lambda, (t.count k : ℝ) * roundedValue L lambda k

/-- Rounded values are nonnegative when the average load scale is nonnegative. -/
theorem roundedValue_nonneg {L : ℝ} {lambda : ℕ}
    (hL : 0 ≤ L) (k : RoundedValueIndex lambda) :
    0 ≤ roundedValue L lambda k := by
  unfold roundedValue
  positivity

/--
Every rounded value index has value at least `L / lambda` when `lambda > 0`
and `L > 0`.
-/
theorem roundedValue_ge_L_div_lambda {L : ℝ} {lambda : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (k : RoundedValueIndex lambda) :
    L / (lambda : ℝ) ≤ roundedValue L lambda k := by
  have hlambda_real_pos : 0 < (lambda : ℝ) := by
    exact_mod_cast hlambda
  have hk_lower : (lambda : ℝ) ≤ (roundedValueIndexValue k : ℝ) := by
    exact_mod_cast roundedValueIndexValue_lower k
  calc
    L / (lambda : ℝ) =
        (lambda : ℝ) * L / ((lambda : ℝ) ^ 2) := by
          field_simp [ne_of_gt hlambda_real_pos]
    _ ≤ (roundedValueIndexValue k : ℝ) * L / ((lambda : ℝ) ^ 2) := by
          gcongr
    _ = roundedValue L lambda k := rfl

/--
High-good scalar rounding: any source value in `(L / lambda, L)` can be rounded
up to one of the finite indices `lambda, ..., lambda^2` with additive error
strictly below `L / lambda^2`.
-/
theorem exists_roundedValueIndex_of_high_good
    {L x : ℝ} {lambda : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (hx_lower : L / (lambda : ℝ) < x)
    (hx_upper : x < L) :
    ∃ k : RoundedValueIndex lambda,
      x ≤ roundedValue L lambda k ∧
        roundedValue L lambda k < x + L / ((lambda : ℝ) ^ 2) := by
  classical
  let q : ℝ := x * ((lambda : ℝ) ^ 2) / L
  let n : ℕ := Nat.ceil q
  have hlambda_real_pos : 0 < (lambda : ℝ) := by
    exact_mod_cast hlambda
  have hlambda_sq_pos : 0 < (lambda : ℝ) ^ 2 := sq_pos_of_pos hlambda_real_pos
  have hscale_pos : 0 < ((lambda : ℝ) ^ 2 / L) :=
    div_pos hlambda_sq_pos hL
  have hunit_pos : 0 < L / ((lambda : ℝ) ^ 2) :=
    div_pos hL hlambda_sq_pos
  have hq_lower : (lambda : ℝ) < q := by
    have hscaled := mul_lt_mul_of_pos_right hx_lower hscale_pos
    have hleft :
        (L / (lambda : ℝ)) * (((lambda : ℝ) ^ 2) / L) =
          (lambda : ℝ) := by
      field_simp [ne_of_gt hL, ne_of_gt hlambda_real_pos]
    have hright :
        x * (((lambda : ℝ) ^ 2) / L) = q := by
      simp [q, div_eq_mul_inv, mul_assoc]
    simpa [hleft, hright] using hscaled
  have hq_upper : q < (lambda : ℝ) ^ 2 := by
    have hscaled := mul_lt_mul_of_pos_right hx_upper hscale_pos
    have hleft :
        x * (((lambda : ℝ) ^ 2) / L) = q := by
      simp [q, div_eq_mul_inv, mul_assoc]
    have hright :
        L * (((lambda : ℝ) ^ 2) / L) = (lambda : ℝ) ^ 2 := by
      field_simp [ne_of_gt hL]
    simpa [hleft, hright] using hscaled
  have hn_lower : lambda ≤ n := by
    have hreal : (lambda : ℝ) ≤ (n : ℝ) :=
      le_trans (le_of_lt hq_lower) (by simpa [n] using Nat.le_ceil q)
    exact_mod_cast hreal
  have hn_upper : n ≤ lambda ^ 2 := by
    apply Nat.ceil_le.mpr
    have hcast :
        ((lambda ^ 2 : ℕ) : ℝ) = (lambda : ℝ) ^ 2 := by
      norm_num
    exact le_of_lt (by simpa [hcast] using hq_upper)
  let k : RoundedValueIndex lambda :=
    ⟨⟨n, Nat.lt_succ_of_le hn_upper⟩, hn_lower⟩
  refine ⟨k, ?_, ?_⟩
  · have hceil : q ≤ (n : ℝ) := by
      simpa [n] using Nat.le_ceil q
    have hmul :
        q * (L / ((lambda : ℝ) ^ 2)) ≤
          (n : ℝ) * (L / ((lambda : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hceil hunit_pos.le
    have hq_unit :
        q * (L / ((lambda : ℝ) ^ 2)) = x := by
      dsimp [q]
      field_simp [ne_of_gt hL, ne_of_gt hlambda_sq_pos]
    calc
      x = q * (L / ((lambda : ℝ) ^ 2)) := hq_unit.symm
      _ ≤ (n : ℝ) * (L / ((lambda : ℝ) ^ 2)) := hmul
      _ = roundedValue L lambda k := by
        simp [roundedValue, roundedValueIndexValue, k, div_eq_mul_inv,
          mul_assoc]
  · have hq_nonneg : 0 ≤ q :=
      le_of_lt (lt_trans hlambda_real_pos hq_lower)
    have hceil_lt : (n : ℝ) < q + 1 := by
      simpa [n] using Nat.ceil_lt_add_one hq_nonneg
    have hmul :
        (n : ℝ) * (L / ((lambda : ℝ) ^ 2)) <
          (q + 1) * (L / ((lambda : ℝ) ^ 2)) :=
      mul_lt_mul_of_pos_right hceil_lt hunit_pos
    have hq_unit :
        q * (L / ((lambda : ℝ) ^ 2)) = x := by
      dsimp [q]
      field_simp [ne_of_gt hL, ne_of_gt hlambda_sq_pos]
    have hq_add_unit :
        (q + 1) * (L / ((lambda : ℝ) ^ 2)) =
          x + L / ((lambda : ℝ) ^ 2) := by
      rw [add_mul, one_mul, hq_unit]
    calc
      roundedValue L lambda k =
          (n : ℝ) * (L / ((lambda : ℝ) ^ 2)) := by
            simp [roundedValue, roundedValueIndexValue, k, div_eq_mul_inv,
              mul_assoc]
      _ < (q + 1) * (L / ((lambda : ℝ) ^ 2)) := hmul
      _ = x + L / ((lambda : ℝ) ^ 2) := hq_add_unit

/-- The rounded value index `k = lambda`, i.e. the low-good value `L / lambda`. -/
def lowGoodRoundedValueIndex (lambda : ℕ) : RoundedValueIndex lambda :=
  ⟨⟨lambda,
      Nat.lt_succ_of_le
        (Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) lambda)⟩,
    le_rfl⟩

/-- The low-good rounded value index has rounded value exactly `L / lambda`. -/
theorem roundedValue_lowGoodRoundedValueIndex_eq
    {L : ℝ} {lambda : ℕ} (hlambda : 0 < lambda) :
    roundedValue L lambda (lowGoodRoundedValueIndex lambda) =
      L / (lambda : ℝ) := by
  have hlambda_real_pos : 0 < (lambda : ℝ) := by
    exact_mod_cast hlambda
  unfold roundedValue roundedValueIndexValue lowGoodRoundedValueIndex
  field_simp [ne_of_gt hlambda_real_pos]

/--
Number of artificial low goods in the rounded instance.  If the total low-good
value is `S`, this is `ceil (S / (L / lambda))`.
-/
noncomputable def roundedLowGoodsCount (L : ℝ) (lambda : ℕ) (S : ℝ) : ℕ :=
  Nat.ceil (S / (L / (lambda : ℝ)))

/-- The aggregate low-good value is no larger than the rounded low-good total. -/
theorem lowGoods_total_le_roundedLowGoodsCount_value
    {L S : ℝ} {lambda : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L) :
    S ≤ (roundedLowGoodsCount L lambda S : ℝ) * (L / (lambda : ℝ)) := by
  let unit : ℝ := L / (lambda : ℝ)
  have hunit_pos : 0 < unit := by
    dsimp [unit]
    exact div_pos hL (by exact_mod_cast hlambda)
  have hceil :
      S / unit ≤ (roundedLowGoodsCount L lambda S : ℝ) := by
    simpa [roundedLowGoodsCount, unit]
      using Nat.le_ceil (S / unit)
  have hmul :
      (S / unit) * unit ≤
        (roundedLowGoodsCount L lambda S : ℝ) * unit :=
    mul_le_mul_of_nonneg_right hceil hunit_pos.le
  have hunit_ne : unit ≠ 0 := ne_of_gt hunit_pos
  calc
    S = (S / unit) * unit := by field_simp [hunit_ne]
    _ ≤ (roundedLowGoodsCount L lambda S : ℝ) * unit := hmul
    _ = (roundedLowGoodsCount L lambda S : ℝ) * (L / (lambda : ℝ)) := rfl

/--
The rounded low-good total overshoots the source low-good total by less than
one low-good unit `L / lambda`, provided the total source low-good value is
nonnegative.
-/
theorem roundedLowGoodsCount_value_lt_total_add_unit
    {L S : ℝ} {lambda : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L) (hS_nonneg : 0 ≤ S) :
    (roundedLowGoodsCount L lambda S : ℝ) * (L / (lambda : ℝ)) <
      S + L / (lambda : ℝ) := by
  let unit : ℝ := L / (lambda : ℝ)
  have hunit_pos : 0 < unit := by
    dsimp [unit]
    exact div_pos hL (by exact_mod_cast hlambda)
  have hq_nonneg : 0 ≤ S / unit := div_nonneg hS_nonneg hunit_pos.le
  have hceil_lt :
      (roundedLowGoodsCount L lambda S : ℝ) < S / unit + 1 := by
    simpa [roundedLowGoodsCount, unit]
      using Nat.ceil_lt_add_one hq_nonneg
  have hmul :
      (roundedLowGoodsCount L lambda S : ℝ) * unit <
        (S / unit + 1) * unit :=
    mul_lt_mul_of_pos_right hceil_lt hunit_pos
  have hunit_ne : unit ≠ 0 := ne_of_gt hunit_pos
  have hright : (S / unit + 1) * unit = S + unit := by
    rw [add_mul, one_mul]
    field_simp [hunit_ne]
  calc
    (roundedLowGoodsCount L lambda S : ℝ) * (L / (lambda : ℝ)) =
        (roundedLowGoodsCount L lambda S : ℝ) * unit := rfl
    _ < (S / unit + 1) * unit := hmul
    _ = S + unit := hright
    _ = S + L / (lambda : ℝ) := rfl

/--
The goods-supply vector contributed by aggregating low goods: all artificial
goods have rounded value index `lambda`, i.e. value `L / lambda`.
-/
noncomputable def lowGoodsAggregatedSupply
    (L : ℝ) (lambda : ℕ) (S : ℝ) :
    RoundedValueIndex lambda → ℕ :=
  fun k =>
    if k = lowGoodRoundedValueIndex lambda then
      roundedLowGoodsCount L lambda S
    else
      0

/-- Low-good aggregation contributes no goods away from the low-good index. -/
theorem lowGoodsAggregatedSupply_eq_zero_of_ne
    {L S : ℝ} {lambda : ℕ} {k : RoundedValueIndex lambda}
    (hk : k ≠ lowGoodRoundedValueIndex lambda) :
    lowGoodsAggregatedSupply L lambda S k = 0 := by
  simp [lowGoodsAggregatedSupply, hk]

/-- The weighted value of the low-good supply is its rounded low-good total. -/
theorem lowGoodsAggregatedSupply_weighted_sum_eq
    {L S : ℝ} {lambda : ℕ} (hlambda : 0 < lambda) :
    (∑ k : RoundedValueIndex lambda,
        (lowGoodsAggregatedSupply L lambda S k : ℝ) *
          roundedValue L lambda k) =
      (roundedLowGoodsCount L lambda S : ℝ) * (L / (lambda : ℝ)) := by
  classical
  simp [lowGoodsAggregatedSupply, roundedValue_lowGoodRoundedValueIndex_eq hlambda]

/--
The low-good supply vector has total rounded value in `[S, S + L/lambda)`.
-/
theorem lowGoodsAggregatedSupply_weighted_sum_bounds
    {L S : ℝ} {lambda : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L) (hS_nonneg : 0 ≤ S) :
    S ≤
        (∑ k : RoundedValueIndex lambda,
          (lowGoodsAggregatedSupply L lambda S k : ℝ) *
            roundedValue L lambda k) ∧
      (∑ k : RoundedValueIndex lambda,
          (lowGoodsAggregatedSupply L lambda S k : ℝ) *
            roundedValue L lambda k) <
        S + L / (lambda : ℝ) := by
  rw [lowGoodsAggregatedSupply_weighted_sum_eq (L := L) (S := S) hlambda]
  exact
    ⟨lowGoods_total_le_roundedLowGoodsCount_value hlambda hL,
      roundedLowGoodsCount_value_lt_total_add_unit hlambda hL hS_nonneg⟩

/--
Source finite-search-space bound: if a rounded bundle type has load below
`2L`, then each count is below `2 * lambda`. Thus the source set `U` of bundle
types satisfying the Claim 3.4 load window is contained in a finite bounded
count box depending only on `lambda`.
-/
theorem roundedBundleType_count_lt_two_mul_lambda_of_load_lt_two_mul_L
    {L : ℝ} {lambda : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (t : RoundedBundleType lambda)
    (hload : roundedBundleTypeLoad L t < 2 * L)
    (k : RoundedValueIndex lambda) :
    t.count k < 2 * lambda := by
  have hlambda_real_pos : 0 < (lambda : ℝ) := by
    exact_mod_cast hlambda
  have hcoef_pos : 0 < L / (lambda : ℝ) :=
    div_pos hL hlambda_real_pos
  have hterm_nonneg :
      ∀ j : RoundedValueIndex lambda,
        0 ≤ (t.count j : ℝ) * roundedValue L lambda j := by
    intro j
    exact mul_nonneg (Nat.cast_nonneg _) (roundedValue_nonneg hL.le j)
  have hterm_le_load :
      (t.count k : ℝ) * roundedValue L lambda k ≤
        roundedBundleTypeLoad L t := by
    simpa [roundedBundleTypeLoad] using
      Finset.single_le_sum
        (fun j _hj => hterm_nonneg j)
        (Finset.mem_univ k)
  have hcount_coef_le_term :
      (t.count k : ℝ) * (L / (lambda : ℝ)) ≤
        (t.count k : ℝ) * roundedValue L lambda k :=
    mul_le_mul_of_nonneg_left
      (roundedValue_ge_L_div_lambda hlambda hL k)
      (Nat.cast_nonneg _)
  have hcount_coef_lt : (t.count k : ℝ) * (L / (lambda : ℝ)) < 2 * L :=
    lt_of_le_of_lt (le_trans hcount_coef_le_term hterm_le_load) hload
  have htarget :
      (2 * (lambda : ℝ)) * (L / (lambda : ℝ)) = 2 * L := by
    field_simp [ne_of_gt hlambda_real_pos]
  have hreal_lt : (t.count k : ℝ) < 2 * (lambda : ℝ) := by
    have hmul_lt :
        (t.count k : ℝ) * (L / (lambda : ℝ)) <
          (2 * (lambda : ℝ)) * (L / (lambda : ℝ)) := by
      simpa [htarget] using hcount_coef_lt
    exact lt_of_mul_lt_mul_right hmul_lt (le_of_lt hcoef_pos)
  exact_mod_cast hreal_lt

/--
General count-box bound: if a rounded type's load is below
`(maxCount + 1) * L / lambda`, then every per-value count is at most
`maxCount`.
-/
theorem roundedBundleType_count_lt_succ_of_load_lt_count_bound
    {L : ℝ} {lambda maxCount : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (t : RoundedBundleType lambda)
    (hload :
      roundedBundleTypeLoad L t <
        (maxCount + 1 : ℝ) * (L / (lambda : ℝ)))
    (k : RoundedValueIndex lambda) :
    t.count k < maxCount + 1 := by
  have hlambda_real_pos : 0 < (lambda : ℝ) := by
    exact_mod_cast hlambda
  have hcoef_pos : 0 < L / (lambda : ℝ) :=
    div_pos hL hlambda_real_pos
  have hterm_nonneg :
      ∀ j : RoundedValueIndex lambda,
        0 ≤ (t.count j : ℝ) * roundedValue L lambda j := by
    intro j
    exact mul_nonneg (Nat.cast_nonneg _) (roundedValue_nonneg hL.le j)
  have hterm_le_load :
      (t.count k : ℝ) * roundedValue L lambda k ≤
        roundedBundleTypeLoad L t := by
    simpa [roundedBundleTypeLoad] using
      Finset.single_le_sum
        (fun j _hj => hterm_nonneg j)
        (Finset.mem_univ k)
  have hcount_coef_le_term :
      (t.count k : ℝ) * (L / (lambda : ℝ)) ≤
        (t.count k : ℝ) * roundedValue L lambda k :=
    mul_le_mul_of_nonneg_left
      (roundedValue_ge_L_div_lambda hlambda hL k)
      (Nat.cast_nonneg _)
  have hcount_coef_lt :
      (t.count k : ℝ) * (L / (lambda : ℝ)) <
        (maxCount + 1 : ℝ) * (L / (lambda : ℝ)) :=
    lt_of_le_of_lt (le_trans hcount_coef_le_term hterm_le_load) hload
  have hreal_lt : (t.count k : ℝ) < (maxCount + 1 : ℝ) :=
    lt_of_mul_lt_mul_right hcount_coef_lt (le_of_lt hcoef_pos)
  exact_mod_cast hreal_lt

/-- A bounded rounded bundle type, represented by per-rounded-value counts. -/
abbrev BoundedRoundedBundleType (lambda maxCount : ℕ) :=
  RoundedValueIndex lambda → Fin (maxCount + 1)

instance boundedRoundedBundleTypeFintype (lambda maxCount : ℕ) :
    Fintype (BoundedRoundedBundleType lambda maxCount) :=
  inferInstance

/-- Forget the explicit count bound and view a bounded type as a rounded bundle type. -/
def BoundedRoundedBundleType.toRoundedBundleType {lambda maxCount : ℕ}
    (t : BoundedRoundedBundleType lambda maxCount) : RoundedBundleType lambda where
  count k := (t k).val

/-- Every count in a bounded rounded bundle type is at most `maxCount`. -/
theorem BoundedRoundedBundleType.count_le {lambda maxCount : ℕ}
    (t : BoundedRoundedBundleType lambda maxCount) (k : RoundedValueIndex lambda) :
    (t.toRoundedBundleType.count k) ≤ maxCount := by
  exact Nat.le_of_lt_succ (t k).isLt

/--
Package a rounded type with load below `2L` as a bounded rounded type with
per-value counts bounded by `2 * lambda`.
-/
def boundedRoundedBundleTypeOfLoadLtTwoMulL
    {L : ℝ} {lambda : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (t : RoundedBundleType lambda)
    (hload : roundedBundleTypeLoad L t < 2 * L) :
    BoundedRoundedBundleType lambda (2 * lambda) :=
  fun k =>
    ⟨t.count k,
      Nat.lt_succ_of_lt
        (roundedBundleType_count_lt_two_mul_lambda_of_load_lt_two_mul_L
          hlambda hL t hload k)⟩

/-- The bounded package forgets back to the original rounded type. -/
theorem boundedRoundedBundleTypeOfLoadLtTwoMulL_toRoundedBundleType
    {L : ℝ} {lambda : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (t : RoundedBundleType lambda)
    (hload : roundedBundleTypeLoad L t < 2 * L) :
    (boundedRoundedBundleTypeOfLoadLtTwoMulL hlambda hL t hload).toRoundedBundleType = t := by
  rfl

/--
Package a rounded type as a bounded type using an explicit load/count-box
budget.
-/
def boundedRoundedBundleTypeOfLoadLtCountBound
    {L : ℝ} {lambda maxCount : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (t : RoundedBundleType lambda)
    (hload :
      roundedBundleTypeLoad L t <
        (maxCount + 1 : ℝ) * (L / (lambda : ℝ))) :
    BoundedRoundedBundleType lambda maxCount :=
  fun k =>
    ⟨t.count k,
      roundedBundleType_count_lt_succ_of_load_lt_count_bound
        hlambda hL t hload k⟩

/-- The explicit count-bound package forgets back to the original rounded type. -/
theorem boundedRoundedBundleTypeOfLoadLtCountBound_toRoundedBundleType
    {L : ℝ} {lambda maxCount : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (t : RoundedBundleType lambda)
    (hload :
      roundedBundleTypeLoad L t <
        (maxCount + 1 : ℝ) * (L / (lambda : ℝ))) :
    (boundedRoundedBundleTypeOfLoadLtCountBound hlambda hL t hload).toRoundedBundleType = t := by
  rfl

/-- The bounded rounded bundle type space is finite with the expected product cardinality. -/
theorem boundedRoundedBundleType_card (lambda maxCount : ℕ) :
    Fintype.card (BoundedRoundedBundleType lambda maxCount) =
      (maxCount + 1) ^ Fintype.card (RoundedValueIndex lambda) := by
  simp [BoundedRoundedBundleType]

/-- Extensionality for bounded rounded bundle types through the unbounded view. -/
theorem BoundedRoundedBundleType.ext_of_toRoundedBundleType_eq
    {lambda maxCount : ℕ} {s t : BoundedRoundedBundleType lambda maxCount}
    (h : s.toRoundedBundleType = t.toRoundedBundleType) : s = t := by
  funext k
  apply Fin.ext
  exact congrFun (congrArg RoundedBundleType.count h) k

/-- The forgetful map from bounded types to rounded bundle types is injective. -/
theorem BoundedRoundedBundleType.toRoundedBundleType_injective
    (lambda maxCount : ℕ) :
    Function.Injective
      (BoundedRoundedBundleType.toRoundedBundleType
        (lambda := lambda) (maxCount := maxCount)) := by
  intro s t h
  exact BoundedRoundedBundleType.ext_of_toRoundedBundleType_eq h

/-- Finite set of all bounded rounded bundle types, as unbounded rounded bundle types. -/
noncomputable def boundedRoundedBundleTypeSet (lambda maxCount : ℕ) :
    Finset (RoundedBundleType lambda) := by
  classical
  exact Finset.univ.image
    (BoundedRoundedBundleType.toRoundedBundleType
      (lambda := lambda) (maxCount := maxCount))

/--
Every rounded bundle type with load below `2L` belongs to the finite bounded
type set with per-value counts bounded by `2 * lambda`.
-/
theorem roundedBundleType_mem_boundedRoundedBundleTypeSet_of_load_lt_two_mul_L
    {L : ℝ} {lambda : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (t : RoundedBundleType lambda)
    (hload : roundedBundleTypeLoad L t < 2 * L) :
    t ∈ boundedRoundedBundleTypeSet lambda (2 * lambda) := by
  classical
  unfold boundedRoundedBundleTypeSet
  refine Finset.mem_image.mpr ?_
  exact
    ⟨boundedRoundedBundleTypeOfLoadLtTwoMulL hlambda hL t hload,
      Finset.mem_univ _,
      boundedRoundedBundleTypeOfLoadLtTwoMulL_toRoundedBundleType
        hlambda hL t hload⟩

/--
Membership in an arbitrary bounded count box from an explicit load/count-box
budget.
-/
theorem roundedBundleType_mem_boundedRoundedBundleTypeSet_of_load_lt_count_bound
    {L : ℝ} {lambda maxCount : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (t : RoundedBundleType lambda)
    (hload :
      roundedBundleTypeLoad L t <
        (maxCount + 1 : ℝ) * (L / (lambda : ℝ))) :
    t ∈ boundedRoundedBundleTypeSet lambda maxCount := by
  classical
  unfold boundedRoundedBundleTypeSet
  refine Finset.mem_image.mpr ?_
  exact
    ⟨boundedRoundedBundleTypeOfLoadLtCountBound hlambda hL t hload,
      Finset.mem_univ _,
      boundedRoundedBundleTypeOfLoadLtCountBound_toRoundedBundleType
        hlambda hL t hload⟩

/-- The finite bounded-type set has the expected cardinality. -/
theorem boundedRoundedBundleTypeSet_card (lambda maxCount : ℕ) :
    (boundedRoundedBundleTypeSet lambda maxCount).card =
      (maxCount + 1) ^ Fintype.card (RoundedValueIndex lambda) := by
  classical
  rw [boundedRoundedBundleTypeSet, Finset.card_image_of_injective]
  · exact boundedRoundedBundleType_card lambda maxCount
  · exact BoundedRoundedBundleType.toRoundedBundleType_injective lambda maxCount

/-- The finite bounded rounded-type box is monotone in the count cap. -/
theorem boundedRoundedBundleTypeSet_mono_of_le
    {lambda smallCap largeCap : ℕ} (hcap : smallCap ≤ largeCap) :
    boundedRoundedBundleTypeSet lambda smallCap ⊆
      boundedRoundedBundleTypeSet lambda largeCap := by
  classical
  intro t ht
  unfold boundedRoundedBundleTypeSet at ht ⊢
  rcases Finset.mem_image.mp ht with ⟨s, _hs, hst⟩
  let lifted : BoundedRoundedBundleType lambda largeCap :=
    fun k =>
      ⟨(s k).val,
        Nat.lt_succ_of_le
          (le_trans (Nat.le_of_lt_succ (s k).isLt) hcap)⟩
  refine Finset.mem_image.mpr ⟨lifted, Finset.mem_univ _, ?_⟩
  simpa [lifted, BoundedRoundedBundleType.toRoundedBundleType] using hst

/--
The finite set `U` from the source proof: rounded bundle types whose load lies
inside the Claim 3.4 window.  It is represented as a filter of the bounded
count box above.
-/
noncomputable def roundedAdmissibleTypeSet (L : ℝ) (lambda : ℕ) :
    Finset (RoundedBundleType lambda) := by
  classical
  exact
    (boundedRoundedBundleTypeSet lambda (2 * lambda)).filter
      (fun t => L / 2 < roundedBundleTypeLoad L t ∧
        roundedBundleTypeLoad L t < 2 * L)

/-- Membership in the source finite type set is exactly boundedness plus the load window. -/
theorem mem_roundedAdmissibleTypeSet_iff
    {L : ℝ} {lambda : ℕ} (t : RoundedBundleType lambda) :
    t ∈ roundedAdmissibleTypeSet L lambda ↔
      t ∈ boundedRoundedBundleTypeSet lambda (2 * lambda) ∧
        L / 2 < roundedBundleTypeLoad L t ∧
          roundedBundleTypeLoad L t < 2 * L := by
  classical
  simp [roundedAdmissibleTypeSet]

/--
Any rounded bundle type satisfying the source Claim 3.4 load window belongs to
the finite set `U`.
-/
theorem roundedBundleType_mem_roundedAdmissibleTypeSet_of_load_window
    {L : ℝ} {lambda : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (t : RoundedBundleType lambda)
    (hlow : L / 2 < roundedBundleTypeLoad L t)
    (hhigh : roundedBundleTypeLoad L t < 2 * L) :
    t ∈ roundedAdmissibleTypeSet L lambda := by
  classical
  have hbounded :
      t ∈ boundedRoundedBundleTypeSet lambda (2 * lambda) :=
    roundedBundleType_mem_boundedRoundedBundleTypeSet_of_load_lt_two_mul_L
      hlambda hL t hhigh
  exact
    (mem_roundedAdmissibleTypeSet_iff t).mpr
      ⟨hbounded, hlow, hhigh⟩

/--
The source finite type set has cardinality bounded by a function only of
`lambda`.
-/
theorem roundedAdmissibleTypeSet_card_le
    (L : ℝ) (lambda : ℕ) :
    (roundedAdmissibleTypeSet L lambda).card ≤
      (2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda) := by
  classical
  calc
    (roundedAdmissibleTypeSet L lambda).card
        ≤ (boundedRoundedBundleTypeSet lambda (2 * lambda)).card := by
          unfold roundedAdmissibleTypeSet
          exact Finset.card_filter_le _ _
    _ = (2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda) := by
          rw [boundedRoundedBundleTypeSet_card]

/--
Explicit source finite-type cardinality bound with the rounded-index exponent
expanded to `lambda^2 + 1`.
-/
theorem roundedAdmissibleTypeSet_card_le_explicit
    (L : ℝ) (lambda : ℕ) :
    (roundedAdmissibleTypeSet L lambda).card ≤
      (2 * lambda + 1) ^ (lambda ^ 2 + 1) := by
  exact
    le_trans (roundedAdmissibleTypeSet_card_le L lambda)
      (Nat.pow_le_pow_right (Nat.succ_pos _) (roundedValueIndex_card_le lambda))

/--
The source value set `V(U)`: rounded utility values attained by some bundle
type in the finite set `U`.
-/
noncomputable def roundedAdmissibleValueSet (L : ℝ) (lambda : ℕ) :
    Finset ℝ := by
  classical
  exact (roundedAdmissibleTypeSet L lambda).image
    (roundedBundleTypeLoad L)

/-- Membership in `V(U)` is exactly being the load of some type in `U`. -/
theorem mem_roundedAdmissibleValueSet_iff
    {L : ℝ} {lambda : ℕ} (u : ℝ) :
    u ∈ roundedAdmissibleValueSet L lambda ↔
      ∃ t ∈ roundedAdmissibleTypeSet L lambda,
        roundedBundleTypeLoad L t = u := by
  classical
  constructor
  · intro hu
    rcases Finset.mem_image.mp hu with ⟨t, ht, htu⟩
    exact ⟨t, ht, htu⟩
  · rintro ⟨t, ht, htu⟩
    exact Finset.mem_image.mpr ⟨t, ht, htu⟩

/-- The load of any admissible type belongs to the source value set `V(U)`. -/
theorem roundedBundleTypeLoad_mem_roundedAdmissibleValueSet_of_mem
    {L : ℝ} {lambda : ℕ} {t : RoundedBundleType lambda}
    (ht : t ∈ roundedAdmissibleTypeSet L lambda) :
    roundedBundleTypeLoad L t ∈ roundedAdmissibleValueSet L lambda := by
  classical
  exact
    (mem_roundedAdmissibleValueSet_iff
      (L := L) (lambda := lambda) (roundedBundleTypeLoad L t)).mpr
      ⟨t, ht, rfl⟩

/--
Any rounded bundle type satisfying the source load window contributes its load
to `V(U)`.
-/
theorem roundedBundleTypeLoad_mem_roundedAdmissibleValueSet_of_load_window
    {L : ℝ} {lambda : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (t : RoundedBundleType lambda)
    (hlow : L / 2 < roundedBundleTypeLoad L t)
    (hhigh : roundedBundleTypeLoad L t < 2 * L) :
    roundedBundleTypeLoad L t ∈ roundedAdmissibleValueSet L lambda := by
  exact
    roundedBundleTypeLoad_mem_roundedAdmissibleValueSet_of_mem
      (roundedBundleType_mem_roundedAdmissibleTypeSet_of_load_window
        hlambda hL t hlow hhigh)

/-- The source value set has cardinality bounded by the same finite type box. -/
theorem roundedAdmissibleValueSet_card_le
    (L : ℝ) (lambda : ℕ) :
    (roundedAdmissibleValueSet L lambda).card ≤
      (2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda) := by
  classical
  calc
    (roundedAdmissibleValueSet L lambda).card
        ≤ (roundedAdmissibleTypeSet L lambda).card := by
          unfold roundedAdmissibleValueSet
          exact Finset.card_image_le
    _ ≤ (2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda) :=
          roundedAdmissibleTypeSet_card_le L lambda

/-- Ordered pairs of rounded utility values searched by the source IP layer. -/
noncomputable def roundedAdmissibleValuePairSet (L : ℝ) (lambda : ℕ) :
    Finset (ℝ × ℝ) := by
  classical
  exact (roundedAdmissibleValueSet L lambda).product
    (roundedAdmissibleValueSet L lambda)

/-- Membership in the finite value-pair search space. -/
theorem mem_roundedAdmissibleValuePairSet_iff
    {L : ℝ} {lambda : ℕ} (p : ℝ × ℝ) :
    p ∈ roundedAdmissibleValuePairSet L lambda ↔
      p.1 ∈ roundedAdmissibleValueSet L lambda ∧
        p.2 ∈ roundedAdmissibleValueSet L lambda := by
  classical
  simp [roundedAdmissibleValuePairSet]

/-- Loads of two admissible types form an admissible value pair for the IP search. -/
theorem roundedBundleTypeLoad_pair_mem_roundedAdmissibleValuePairSet_of_mem
    {L : ℝ} {lambda : ℕ} {s t : RoundedBundleType lambda}
    (hs : s ∈ roundedAdmissibleTypeSet L lambda)
    (ht : t ∈ roundedAdmissibleTypeSet L lambda) :
    (roundedBundleTypeLoad L s, roundedBundleTypeLoad L t) ∈
      roundedAdmissibleValuePairSet L lambda := by
  classical
  exact
    (mem_roundedAdmissibleValuePairSet_iff
      (L := L) (lambda := lambda)
      (roundedBundleTypeLoad L s, roundedBundleTypeLoad L t)).mpr
      ⟨roundedBundleTypeLoad_mem_roundedAdmissibleValueSet_of_mem hs,
        roundedBundleTypeLoad_mem_roundedAdmissibleValueSet_of_mem ht⟩

/--
Loads of two rounded bundle types in the source load window form an admissible
value pair for the IP search.
-/
theorem roundedBundleTypeLoad_pair_mem_roundedAdmissibleValuePairSet_of_load_window
    {L : ℝ} {lambda : ℕ}
    (hlambda : 0 < lambda) (hL : 0 < L)
    (s t : RoundedBundleType lambda)
    (hs_low : L / 2 < roundedBundleTypeLoad L s)
    (hs_high : roundedBundleTypeLoad L s < 2 * L)
    (ht_low : L / 2 < roundedBundleTypeLoad L t)
    (ht_high : roundedBundleTypeLoad L t < 2 * L) :
    (roundedBundleTypeLoad L s, roundedBundleTypeLoad L t) ∈
      roundedAdmissibleValuePairSet L lambda := by
  exact
    roundedBundleTypeLoad_pair_mem_roundedAdmissibleValuePairSet_of_mem
      (roundedBundleType_mem_roundedAdmissibleTypeSet_of_load_window
        hlambda hL s hs_low hs_high)
      (roundedBundleType_mem_roundedAdmissibleTypeSet_of_load_window
        hlambda hL t ht_low ht_high)

/-- Values in `V(U)` inherit the source Claim 3.4 load window. -/
theorem roundedAdmissibleValueSet_bounds
    {L : ℝ} {lambda : ℕ} {u : ℝ}
    (hu : u ∈ roundedAdmissibleValueSet L lambda) :
    L / 2 < u ∧ u < 2 * L := by
  classical
  rcases (mem_roundedAdmissibleValueSet_iff
    (L := L) (lambda := lambda) u).mp hu with ⟨t, ht, htu⟩
  have ht_window :=
    (mem_roundedAdmissibleTypeSet_iff
      (L := L) (lambda := lambda) t).mp ht
  constructor
  · simpa [← htu] using ht_window.2.1
  · simpa [← htu] using ht_window.2.2

/-- A source value pair has both coordinates inside the Claim 3.4 load window. -/
theorem roundedAdmissibleValuePairSet_bounds
    {L : ℝ} {lambda : ℕ} {p : ℝ × ℝ}
    (hp : p ∈ roundedAdmissibleValuePairSet L lambda) :
    L / 2 < p.1 ∧ p.1 < 2 * L ∧
      L / 2 < p.2 ∧ p.2 < 2 * L := by
  classical
  have hp_mem :=
    (mem_roundedAdmissibleValuePairSet_iff
      (L := L) (lambda := lambda) p).mp hp
  have hleft := roundedAdmissibleValueSet_bounds hp_mem.1
  have hright := roundedAdmissibleValueSet_bounds hp_mem.2
  exact ⟨hleft.1, hleft.2, hright.1, hright.2⟩

/-- The rounded value-pair search space has bounded cardinality. -/
theorem roundedAdmissibleValuePairSet_card_le
    (L : ℝ) (lambda : ℕ) :
    (roundedAdmissibleValuePairSet L lambda).card ≤
      ((2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda)) ^ 2 := by
  classical
  have hvalue :=
    roundedAdmissibleValueSet_card_le L lambda
  have hmul :
      (roundedAdmissibleValueSet L lambda).card *
          (roundedAdmissibleValueSet L lambda).card ≤
        ((2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda)) *
          ((2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda)) :=
    Nat.mul_le_mul hvalue hvalue
  simpa [roundedAdmissibleValuePairSet, pow_two] using hmul

/--
Explicit source value-pair cardinality bound with the rounded-index exponent
expanded to `lambda^2 + 1`.
-/
theorem roundedAdmissibleValuePairSet_card_le_explicit
    (L : ℝ) (lambda : ℕ) :
    (roundedAdmissibleValuePairSet L lambda).card ≤
      ((2 * lambda + 1) ^ (lambda ^ 2 + 1)) ^ 2 := by
  have hbase :
      (2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda) ≤
        (2 * lambda + 1) ^ (lambda ^ 2 + 1) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (roundedValueIndex_card_le lambda)
  exact
    le_trans (roundedAdmissibleValuePairSet_card_le L lambda)
      (pow_le_pow_left₀ (Nat.zero_le _) hbase 2)

/--
The filtered type set `U_{u1,u2}` used by the source integer program: all
admissible rounded bundle types whose utility lies between the selected value
pair.
-/
noncomputable def roundedTypesInValueWindow
    (L : ℝ) (lambda : ℕ) (lower upper : ℝ) :
    Finset (RoundedBundleType lambda) := by
  classical
  exact (roundedAdmissibleTypeSet L lambda).filter
    (fun t => lower ≤ roundedBundleTypeLoad L t ∧
      roundedBundleTypeLoad L t ≤ upper)

/-- Membership in the source filtered type set `U_{u1,u2}`. -/
theorem mem_roundedTypesInValueWindow_iff
    {L : ℝ} {lambda : ℕ} {lower upper : ℝ}
    (t : RoundedBundleType lambda) :
    t ∈ roundedTypesInValueWindow L lambda lower upper ↔
      t ∈ roundedAdmissibleTypeSet L lambda ∧
        lower ≤ roundedBundleTypeLoad L t ∧
          roundedBundleTypeLoad L t ≤ upper := by
  classical
  simp [roundedTypesInValueWindow]

/-- The selected-window type set is a subset of the global source type set `U`. -/
theorem roundedTypesInValueWindow_subset_admissible
    (L : ℝ) (lambda : ℕ) (lower upper : ℝ) :
    roundedTypesInValueWindow L lambda lower upper ⊆
      roundedAdmissibleTypeSet L lambda := by
  intro t ht
  exact ((mem_roundedTypesInValueWindow_iff
    (L := L) (lambda := lambda) (lower := lower) (upper := upper) t).mp ht).1

/-- The selected-window type set has cardinality bounded by the same type box. -/
theorem roundedTypesInValueWindow_card_le
    (L : ℝ) (lambda : ℕ) (lower upper : ℝ) :
    (roundedTypesInValueWindow L lambda lower upper).card ≤
      (2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda) := by
  classical
  calc
    (roundedTypesInValueWindow L lambda lower upper).card
        ≤ (roundedAdmissibleTypeSet L lambda).card := by
          unfold roundedTypesInValueWindow
          exact Finset.card_filter_le _ _
    _ ≤ (2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda) :=
          roundedAdmissibleTypeSet_card_le L lambda

/--
Finite integer-program feasibility certificate for the rounded instance.

`admissibleTypes` is the finite set `U` searched by the source proof;
`typeMultiplicity` is the integer solution assigning a number of players to
each type.  The two abstract feasibility fields are the paper's per-value goods
constraints and the selected lower/upper utility interval constraints.
-/
structure RoundedTypeIPCertificate (lambda : ℕ) (Agent : Type*) [Fintype Agent] where
  admissibleTypes : Finset (RoundedBundleType lambda)
  typeMultiplicity : RoundedBundleType lambda → ℕ
  allUsedTypesEnumerated :
    ∀ t : RoundedBundleType lambda, 0 < typeMultiplicity t → t ∈ admissibleTypes
  allPlayersAssigned :
    admissibleTypes.sum typeMultiplicity = Fintype.card Agent
  goodsFeasible : Prop
  goodsFeasible_proof : goodsFeasible
  intervalFeasible : Prop
  intervalFeasible_proof : intervalFeasible

/--
Certificate for feasibility of the source IP associated with one selected
value pair `(u1,u2)`.

The certificate keeps the actual IP feasibility abstract, but pins the listed
type variables to the source set `U_{u1,u2}`.
-/
structure RoundedValuePairIPCertificate
    (L : ℝ) (lambda : ℕ) (Agent : Type*) [Fintype Agent]
    (p : ℝ × ℝ) where
  pair_mem : p ∈ roundedAdmissibleValuePairSet L lambda
  ip : RoundedTypeIPCertificate lambda Agent
  admissibleTypes_eq :
    ip.admissibleTypes = roundedTypesInValueWindow L lambda p.1 p.2

/-- The type variables used by a pair-IP certificate are exactly `U_{u1,u2}`. -/
theorem RoundedValuePairIPCertificate.admissibleTypes_eq_window
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ}
    (cert : RoundedValuePairIPCertificate L lambda Agent p) :
    cert.ip.admissibleTypes =
      roundedTypesInValueWindow L lambda p.1 p.2 :=
  cert.admissibleTypes_eq

/-- Any positive-multiplicity type in a pair IP lies in the selected value window. -/
theorem RoundedValuePairIPCertificate.used_type_mem_window
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ}
    (cert : RoundedValuePairIPCertificate L lambda Agent p)
    {t : RoundedBundleType lambda}
    (ht : 0 < cert.ip.typeMultiplicity t) :
    t ∈ roundedTypesInValueWindow L lambda p.1 p.2 := by
  have ht_enum := cert.ip.allUsedTypesEnumerated t ht
  simpa [cert.admissibleTypes_eq] using ht_enum

/-- A used type in a pair IP has load inside the selected value interval. -/
theorem RoundedValuePairIPCertificate.used_type_load_window
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ}
    (cert : RoundedValuePairIPCertificate L lambda Agent p)
    {t : RoundedBundleType lambda}
    (ht : 0 < cert.ip.typeMultiplicity t) :
    p.1 ≤ roundedBundleTypeLoad L t ∧
      roundedBundleTypeLoad L t ≤ p.2 := by
  have hmem := cert.used_type_mem_window ht
  exact ((mem_roundedTypesInValueWindow_iff
    (L := L) (lambda := lambda) (lower := p.1) (upper := p.2) t).mp hmem).2

/-- The selected pair-IP's type-variable set has bounded cardinality. -/
theorem RoundedValuePairIPCertificate.admissibleTypes_card_le
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ}
    (cert : RoundedValuePairIPCertificate L lambda Agent p) :
    cert.ip.admissibleTypes.card ≤
      (2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda) := by
  rw [cert.admissibleTypes_eq]
  exact roundedTypesInValueWindow_card_le L lambda p.1 p.2

/-- The selected pair's values lie in the Claim 3.4 load window. -/
theorem RoundedValuePairIPCertificate.pair_bounds
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ}
    (cert : RoundedValuePairIPCertificate L lambda Agent p) :
    L / 2 < p.1 ∧ p.1 < 2 * L ∧
      L / 2 < p.2 ∧ p.2 < 2 * L :=
  roundedAdmissibleValuePairSet_bounds cert.pair_mem

/--
Concrete source IP certificate for one value pair.

The source IP has variables `X_t`, one for each type in `U`, sets variables
outside `U_{u1,u2}` to zero, assigns all players, and matches the number `n_k`
of rounded goods of each value class.
-/
structure RoundedConcreteIPCertificate
    (L : ℝ) (lambda : ℕ) (Agent : Type*) [Fintype Agent]
    (p : ℝ × ℝ) (goodsSupply : RoundedValueIndex lambda → ℕ) where
  pair_mem : p ∈ roundedAdmissibleValuePairSet L lambda
  typeMultiplicity : RoundedBundleType lambda → ℕ
  zeroOutsideWindow :
    ∀ t : RoundedBundleType lambda,
      t ∉ roundedTypesInValueWindow L lambda p.1 p.2 →
        typeMultiplicity t = 0
  allPlayersAssigned :
    (roundedTypesInValueWindow L lambda p.1 p.2).sum typeMultiplicity =
      Fintype.card Agent
  allGoodsAssigned :
    ∀ k : RoundedValueIndex lambda,
      (roundedTypesInValueWindow L lambda p.1 p.2).sum
          (fun t => typeMultiplicity t * t.count k) =
        goodsSupply k

/-- The concrete source IP's per-value goods equations as a reusable predicate. -/
def RoundedConcreteIPCertificate.goodsFeasible
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ} {goodsSupply : RoundedValueIndex lambda → ℕ}
    (cert : RoundedConcreteIPCertificate L lambda Agent p goodsSupply) : Prop :=
  ∀ k : RoundedValueIndex lambda,
    (roundedTypesInValueWindow L lambda p.1 p.2).sum
        (fun t => cert.typeMultiplicity t * t.count k) =
      goodsSupply k

/-- Concrete source IP certificates satisfy their goods-feasibility predicate. -/
theorem RoundedConcreteIPCertificate.goodsFeasible_proof
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ} {goodsSupply : RoundedValueIndex lambda → ℕ}
    (cert : RoundedConcreteIPCertificate L lambda Agent p goodsSupply) :
    cert.goodsFeasible := by
  exact cert.allGoodsAssigned

/--
Multiplicity of a rounded bundle type induced by an explicit assignment of a
rounded type to each agent.
-/
noncomputable def roundedTypeMultiplicityOfAssignment
    {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    (typeOf : Agent → RoundedBundleType lambda)
    (t : RoundedBundleType lambda) : ℕ := by
  classical
  exact ((Finset.univ : Finset Agent).filter fun i => typeOf i = t).card

/--
If every assigned rounded type lies in a finite window, then summing the
induced type multiplicities over that window assigns exactly all agents.
-/
theorem roundedTypeMultiplicityOfAssignment_sum_eq_card
    {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {types : Finset (RoundedBundleType lambda)}
    (typeOf : Agent → RoundedBundleType lambda)
    (htypes : ∀ i : Agent, typeOf i ∈ types) :
    types.sum (roundedTypeMultiplicityOfAssignment typeOf) =
      Fintype.card Agent := by
  classical
  symm
  simpa [roundedTypeMultiplicityOfAssignment] using
    (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset Agent)) (t := types) (f := typeOf)
      (fun i _hi => htypes i))

/--
Types outside the selected window have zero induced multiplicity when every
agent's assigned type lies inside the window.
-/
theorem roundedTypeMultiplicityOfAssignment_eq_zero_of_not_mem
    {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {types : Finset (RoundedBundleType lambda)}
    (typeOf : Agent → RoundedBundleType lambda)
    (htypes : ∀ i : Agent, typeOf i ∈ types)
    {t : RoundedBundleType lambda} (hnot : t ∉ types) :
    roundedTypeMultiplicityOfAssignment typeOf t = 0 := by
  classical
  have hempty :
      ((Finset.univ : Finset Agent).filter fun i => typeOf i = t) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hit : typeOf i = t := (Finset.mem_filter.mp hi).2
    have htype_i : typeOf i ∈ types := htypes i
    rw [hit] at htype_i
    exact hnot htype_i
  simp [roundedTypeMultiplicityOfAssignment, hempty]

/--
The induced type multiplicities reproduce the per-rounded-value goods counts
obtained by summing each assigned type over all agents.
-/
theorem roundedTypeMultiplicityOfAssignment_goods_count_eq_sum_agents
    {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {types : Finset (RoundedBundleType lambda)}
    (typeOf : Agent → RoundedBundleType lambda)
    (htypes : ∀ i : Agent, typeOf i ∈ types)
    (k : RoundedValueIndex lambda) :
    types.sum
        (fun t => roundedTypeMultiplicityOfAssignment typeOf t * t.count k) =
      ∑ i : Agent, (typeOf i).count k := by
  classical
  calc
    types.sum
        (fun t => roundedTypeMultiplicityOfAssignment typeOf t * t.count k)
        =
      ∑ t ∈ types,
        ∑ i ∈ (Finset.univ : Finset Agent) with typeOf i = t,
          t.count k := by
        apply Finset.sum_congr rfl
        intro t ht
        simp [roundedTypeMultiplicityOfAssignment]
    _ =
      ∑ t ∈ types,
        ∑ i ∈ (Finset.univ : Finset Agent) with typeOf i = t,
          (typeOf i).count k := by
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro i hi
        have hit : typeOf i = t := (Finset.mem_filter.mp hi).2
        rw [hit]
    _ = ∑ i : Agent, (typeOf i).count k := by
        simpa using
          (Finset.sum_fiberwise_of_maps_to
            (s := (Finset.univ : Finset Agent)) (t := types)
            (g := typeOf) (f := fun i => (typeOf i).count k)
            (fun i _hi => htypes i))

/--
Concrete source IP certificate induced by an explicit rounded-type assignment
to agents.  This is the finite accounting step behind the paper's integer
program: type multiplicities are fibers of the assignment, all players are
assigned, and goods counts are the coordinate-wise sums of assigned types.
-/
def roundedConcreteIPCertificateOfTypeAssignment
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ}
    (hpair : p ∈ roundedAdmissibleValuePairSet L lambda)
    (typeOf : Agent → RoundedBundleType lambda)
    (htypes :
      ∀ i : Agent, typeOf i ∈ roundedTypesInValueWindow L lambda p.1 p.2) :
    RoundedConcreteIPCertificate L lambda Agent p
      (fun k : RoundedValueIndex lambda => ∑ i : Agent, (typeOf i).count k) where
  pair_mem := hpair
  typeMultiplicity := roundedTypeMultiplicityOfAssignment typeOf
  zeroOutsideWindow := by
    intro t hnot
    exact roundedTypeMultiplicityOfAssignment_eq_zero_of_not_mem
      typeOf htypes hnot
  allPlayersAssigned :=
    roundedTypeMultiplicityOfAssignment_sum_eq_card typeOf htypes
  allGoodsAssigned := by
    intro k
    exact roundedTypeMultiplicityOfAssignment_goods_count_eq_sum_agents
      typeOf htypes k

/-- Positive multiplicity in a concrete IP is confined to the selected value window. -/
theorem RoundedConcreteIPCertificate.used_type_mem_window
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ} {goodsSupply : RoundedValueIndex lambda → ℕ}
    (cert : RoundedConcreteIPCertificate L lambda Agent p goodsSupply)
    {t : RoundedBundleType lambda}
    (ht : 0 < cert.typeMultiplicity t) :
    t ∈ roundedTypesInValueWindow L lambda p.1 p.2 := by
  by_contra hnot
  have hzero := cert.zeroOutsideWindow t hnot
  simp [hzero] at ht

/-- A used type in a concrete IP has load inside the selected value interval. -/
theorem RoundedConcreteIPCertificate.used_type_load_window
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ} {goodsSupply : RoundedValueIndex lambda → ℕ}
    (cert : RoundedConcreteIPCertificate L lambda Agent p goodsSupply)
    {t : RoundedBundleType lambda}
    (ht : 0 < cert.typeMultiplicity t) :
    p.1 ≤ roundedBundleTypeLoad L t ∧
      roundedBundleTypeLoad L t ≤ p.2 := by
  have hmem := cert.used_type_mem_window ht
  exact ((mem_roundedTypesInValueWindow_iff
    (L := L) (lambda := lambda) (lower := p.1) (upper := p.2) t).mp hmem).2

/--
Forget the concrete goods equations and obtain the abstract pair-IP certificate
used by the rounded-instance search seam.
-/
def RoundedConcreteIPCertificate.toValuePairIPCertificate
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ} {goodsSupply : RoundedValueIndex lambda → ℕ}
    (cert : RoundedConcreteIPCertificate L lambda Agent p goodsSupply) :
    RoundedValuePairIPCertificate L lambda Agent p where
  pair_mem := cert.pair_mem
  ip :=
    { admissibleTypes := roundedTypesInValueWindow L lambda p.1 p.2
      typeMultiplicity := cert.typeMultiplicity
      allUsedTypesEnumerated := by
        intro t ht
        exact cert.used_type_mem_window ht
      allPlayersAssigned := cert.allPlayersAssigned
      goodsFeasible := cert.goodsFeasible
      goodsFeasible_proof := cert.goodsFeasible_proof
      intervalFeasible := p ∈ roundedAdmissibleValuePairSet L lambda
      intervalFeasible_proof := cert.pair_mem }
  admissibleTypes_eq := rfl

/--
The concrete goods-supply IP bridge preserves the player-assignment equation,
the rounded goods equations, and the source type-box cardinality bound.
-/
theorem RoundedConcreteIPCertificate.toValuePairIPCertificate_feasibility_summary
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ} {goodsSupply : RoundedValueIndex lambda → ℕ}
    (cert : RoundedConcreteIPCertificate L lambda Agent p goodsSupply) :
    cert.toValuePairIPCertificate.ip.admissibleTypes.card ≤
        (2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda) ∧
      cert.toValuePairIPCertificate.ip.admissibleTypes.sum
          cert.toValuePairIPCertificate.ip.typeMultiplicity = Fintype.card Agent ∧
      (∀ k : RoundedValueIndex lambda,
        cert.toValuePairIPCertificate.ip.admissibleTypes.sum
            (fun t => cert.toValuePairIPCertificate.ip.typeMultiplicity t * t.count k) =
          goodsSupply k) := by
  exact
    ⟨RoundedValuePairIPCertificate.admissibleTypes_card_le
        cert.toValuePairIPCertificate,
      cert.allPlayersAssigned,
      cert.allGoodsAssigned⟩

/-- Ratio attached to a selected rounded value pair. -/
def roundedValuePairRatio (p : ℝ × ℝ) : ℝ :=
  p.2 / p.1

/--
Certificate for the source scan over all value pairs in `V(U) × V(U)`: a
chosen feasible pair whose ratio is no larger than any other feasible pair.
-/
structure RoundedValuePairSearchCertificate
    (L : ℝ) (lambda : ℕ) (Agent : Type*) [Fintype Agent] where
  chosenPair : ℝ × ℝ
  chosenIP : RoundedValuePairIPCertificate L lambda Agent chosenPair
  optimalAmongFeasible :
    ∀ p : ℝ × ℝ,
      RoundedValuePairIPCertificate L lambda Agent p →
        roundedValuePairRatio chosenPair ≤ roundedValuePairRatio p

/-- The chosen pair in a value-pair search certificate belongs to `V(U) × V(U)`. -/
theorem RoundedValuePairSearchCertificate.chosenPair_mem
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    (cert : RoundedValuePairSearchCertificate L lambda Agent) :
    cert.chosenPair ∈ roundedAdmissibleValuePairSet L lambda :=
  cert.chosenIP.pair_mem

/-- The chosen pair's values lie in the Claim 3.4 load window. -/
theorem RoundedValuePairSearchCertificate.chosenPair_bounds
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    (cert : RoundedValuePairSearchCertificate L lambda Agent) :
    L / 2 < cert.chosenPair.1 ∧ cert.chosenPair.1 < 2 * L ∧
      L / 2 < cert.chosenPair.2 ∧ cert.chosenPair.2 < 2 * L :=
  cert.chosenIP.pair_bounds

/-- The chosen pair has no larger ratio than any other feasible source pair. -/
theorem RoundedValuePairSearchCertificate.ratio_le_of_feasible_pair
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    (cert : RoundedValuePairSearchCertificate L lambda Agent)
    {p : ℝ × ℝ}
    (other : RoundedValuePairIPCertificate L lambda Agent p) :
    roundedValuePairRatio cert.chosenPair ≤ roundedValuePairRatio p :=
  cert.optimalAmongFeasible p other

/--
Concrete goods-supply IP feasibility is one of the finite value-pair search
candidates, so the chosen pair's ratio is no worse than any concrete feasible
pair.
-/
theorem RoundedValuePairSearchCertificate.ratio_le_of_concrete_feasible_pair
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    (cert : RoundedValuePairSearchCertificate L lambda Agent)
    {p : ℝ × ℝ} {goodsSupply : RoundedValueIndex lambda → ℕ}
    (other : RoundedConcreteIPCertificate L lambda Agent p goodsSupply) :
    roundedValuePairRatio cert.chosenPair ≤ roundedValuePairRatio p := by
  exact cert.ratio_le_of_feasible_pair other.toValuePairIPCertificate

/--
Classical finite search over `V(U) × V(U)`: any feasible value-pair IP
certificate can be compared against a globally best feasible rounded pair.
-/
theorem exists_roundedValuePairSearchCertificate_of_feasible_pair
    {L : ℝ} {lambda : ℕ} {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ}
    (ip : RoundedValuePairIPCertificate L lambda Agent p) :
    ∃ search : RoundedValuePairSearchCertificate L lambda Agent,
      roundedValuePairRatio search.chosenPair ≤ roundedValuePairRatio p := by
  classical
  let feasiblePairs : Finset (ℝ × ℝ) :=
    (roundedAdmissibleValuePairSet L lambda).filter
      (fun q => Nonempty (RoundedValuePairIPCertificate L lambda Agent q))
  have hp_mem : p ∈ feasiblePairs := by
    refine Finset.mem_filter.mpr ⟨ip.pair_mem, ?_⟩
    exact ⟨ip⟩
  have hnonempty : feasiblePairs.Nonempty := ⟨p, hp_mem⟩
  rcases Finset.exists_min_image feasiblePairs roundedValuePairRatio hnonempty with
    ⟨best, hbest_mem, hbest_le⟩
  have hbest_nonempty :
      Nonempty (RoundedValuePairIPCertificate L lambda Agent best) :=
    (Finset.mem_filter.mp hbest_mem).2
  let bestIP : RoundedValuePairIPCertificate L lambda Agent best :=
    Classical.choice hbest_nonempty
  let search : RoundedValuePairSearchCertificate L lambda Agent :=
    { chosenPair := best
      chosenIP := bestIP
      optimalAmongFeasible := by
        intro q qip
        have hq_mem : q ∈ feasiblePairs := by
          refine Finset.mem_filter.mpr ⟨qip.pair_mem, ?_⟩
          exact ⟨qip⟩
        exact hbest_le q hq_mem }
  refine ⟨search, ?_⟩
  exact hbest_le p hp_mem

/-! ### Two-scale rounded value-pair search

The paper's rounded instance uses the original average `L` to define the
rounded value grid `kL / lambda^2`, but Claim 3.4 and the finite set `U` use
the rounded instance's average `LR`.  The following parallel API separates
those two scales while retaining an explicit finite count cap.
-/

/--
Two-scale finite type set: rounded bundle types whose loads, computed on the
`valueScale` grid, lie in the Claim 3.4 window around `averageScale`, and whose
per-value counts are bounded by `maxCount`.
-/
noncomputable def roundedAdmissibleTypeSetWithCap
    (valueScale averageScale : ℝ) (lambda maxCount : ℕ) :
    Finset (RoundedBundleType lambda) := by
  classical
  exact
    (boundedRoundedBundleTypeSet lambda maxCount).filter
      (fun t => averageScale / 2 < roundedBundleTypeLoad valueScale t ∧
        roundedBundleTypeLoad valueScale t < 2 * averageScale)

/-- Membership in the two-scale finite type set. -/
theorem mem_roundedAdmissibleTypeSetWithCap_iff
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ}
    (t : RoundedBundleType lambda) :
    t ∈ roundedAdmissibleTypeSetWithCap valueScale averageScale lambda maxCount ↔
      t ∈ boundedRoundedBundleTypeSet lambda maxCount ∧
        averageScale / 2 < roundedBundleTypeLoad valueScale t ∧
          roundedBundleTypeLoad valueScale t < 2 * averageScale := by
  classical
  simp [roundedAdmissibleTypeSetWithCap]

/--
A type in the average-window belongs to the two-scale finite type set once the
chosen count cap is large enough for the upper load bound.
-/
theorem roundedBundleType_mem_roundedAdmissibleTypeSetWithCap_of_load_window
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ}
    (hlambda : 0 < lambda) (hvalueScale : 0 < valueScale)
    (hcap :
      2 * averageScale ≤
        (maxCount + 1 : ℝ) * (valueScale / (lambda : ℝ)))
    (t : RoundedBundleType lambda)
    (hlow : averageScale / 2 < roundedBundleTypeLoad valueScale t)
    (hhigh : roundedBundleTypeLoad valueScale t < 2 * averageScale) :
    t ∈ roundedAdmissibleTypeSetWithCap valueScale averageScale lambda maxCount := by
  classical
  have hload_bound :
      roundedBundleTypeLoad valueScale t <
        (maxCount + 1 : ℝ) * (valueScale / (lambda : ℝ)) :=
    lt_of_lt_of_le hhigh hcap
  have hbounded :
      t ∈ boundedRoundedBundleTypeSet lambda maxCount :=
    roundedBundleType_mem_boundedRoundedBundleTypeSet_of_load_lt_count_bound
      hlambda hvalueScale t hload_bound
  exact
    (mem_roundedAdmissibleTypeSetWithCap_iff t).mpr
      ⟨hbounded, hlow, hhigh⟩

/-- Cardinality bound for the two-scale finite type set. -/
theorem roundedAdmissibleTypeSetWithCap_card_le
    (valueScale averageScale : ℝ) (lambda maxCount : ℕ) :
    (roundedAdmissibleTypeSetWithCap valueScale averageScale lambda maxCount).card ≤
      (maxCount + 1) ^ Fintype.card (RoundedValueIndex lambda) := by
  classical
  calc
    (roundedAdmissibleTypeSetWithCap valueScale averageScale lambda maxCount).card
        ≤ (boundedRoundedBundleTypeSet lambda maxCount).card := by
          unfold roundedAdmissibleTypeSetWithCap
          exact Finset.card_filter_le _ _
    _ = (maxCount + 1) ^ Fintype.card (RoundedValueIndex lambda) := by
          rw [boundedRoundedBundleTypeSet_card]

/--
Explicit two-scale finite-type cardinality bound with the rounded-index
exponent expanded to `lambda^2 + 1`.
-/
theorem roundedAdmissibleTypeSetWithCap_card_le_explicit
    (valueScale averageScale : ℝ) (lambda maxCount : ℕ) :
    (roundedAdmissibleTypeSetWithCap valueScale averageScale lambda maxCount).card ≤
      (maxCount + 1) ^ (lambda ^ 2 + 1) := by
  exact
    le_trans
      (roundedAdmissibleTypeSetWithCap_card_le
        valueScale averageScale lambda maxCount)
      (Nat.pow_le_pow_right (Nat.succ_pos _) (roundedValueIndex_card_le lambda))

/-- Two-scale value set `V(U)`. -/
noncomputable def roundedAdmissibleValueSetWithCap
    (valueScale averageScale : ℝ) (lambda maxCount : ℕ) :
    Finset ℝ := by
  classical
  exact (roundedAdmissibleTypeSetWithCap valueScale averageScale lambda maxCount).image
    (roundedBundleTypeLoad valueScale)

/-- Membership in the two-scale value set. -/
theorem mem_roundedAdmissibleValueSetWithCap_iff
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ} (u : ℝ) :
    u ∈ roundedAdmissibleValueSetWithCap valueScale averageScale lambda maxCount ↔
      ∃ t ∈ roundedAdmissibleTypeSetWithCap valueScale averageScale lambda maxCount,
        roundedBundleTypeLoad valueScale t = u := by
  classical
  constructor
  · intro hu
    rcases Finset.mem_image.mp hu with ⟨t, ht, htu⟩
    exact ⟨t, ht, htu⟩
  · rintro ⟨t, ht, htu⟩
    exact Finset.mem_image.mpr ⟨t, ht, htu⟩

/-- Loads of two-scale admissible types belong to the two-scale value set. -/
theorem roundedBundleTypeLoad_mem_roundedAdmissibleValueSetWithCap_of_mem
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ}
    {t : RoundedBundleType lambda}
    (ht : t ∈ roundedAdmissibleTypeSetWithCap valueScale averageScale lambda maxCount) :
    roundedBundleTypeLoad valueScale t ∈
      roundedAdmissibleValueSetWithCap valueScale averageScale lambda maxCount := by
  classical
  exact
    (mem_roundedAdmissibleValueSetWithCap_iff
      (valueScale := valueScale) (averageScale := averageScale)
      (lambda := lambda) (maxCount := maxCount)
      (roundedBundleTypeLoad valueScale t)).mpr
      ⟨t, ht, rfl⟩

/-- Two-scale value-pair search space. -/
noncomputable def roundedAdmissibleValuePairSetWithCap
    (valueScale averageScale : ℝ) (lambda maxCount : ℕ) :
    Finset (ℝ × ℝ) := by
  classical
  exact (roundedAdmissibleValueSetWithCap valueScale averageScale lambda maxCount).product
    (roundedAdmissibleValueSetWithCap valueScale averageScale lambda maxCount)

/-- Membership in the two-scale value-pair search space. -/
theorem mem_roundedAdmissibleValuePairSetWithCap_iff
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ} (p : ℝ × ℝ) :
    p ∈ roundedAdmissibleValuePairSetWithCap valueScale averageScale lambda maxCount ↔
      p.1 ∈ roundedAdmissibleValueSetWithCap valueScale averageScale lambda maxCount ∧
        p.2 ∈ roundedAdmissibleValueSetWithCap valueScale averageScale lambda maxCount := by
  classical
  simp [roundedAdmissibleValuePairSetWithCap]

/--
Loads of two types in the two-scale Claim 3.4 window form a searched value pair
once the count cap covers the window.
-/
theorem roundedBundleTypeLoad_pair_mem_roundedAdmissibleValuePairSetWithCap_of_load_window
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ}
    (hlambda : 0 < lambda) (hvalueScale : 0 < valueScale)
    (hcap :
      2 * averageScale ≤
        (maxCount + 1 : ℝ) * (valueScale / (lambda : ℝ)))
    (s t : RoundedBundleType lambda)
    (hs_low : averageScale / 2 < roundedBundleTypeLoad valueScale s)
    (hs_high : roundedBundleTypeLoad valueScale s < 2 * averageScale)
    (ht_low : averageScale / 2 < roundedBundleTypeLoad valueScale t)
    (ht_high : roundedBundleTypeLoad valueScale t < 2 * averageScale) :
    (roundedBundleTypeLoad valueScale s, roundedBundleTypeLoad valueScale t) ∈
      roundedAdmissibleValuePairSetWithCap valueScale averageScale lambda maxCount := by
  classical
  let hs_mem :=
    roundedBundleType_mem_roundedAdmissibleTypeSetWithCap_of_load_window
      hlambda hvalueScale hcap s hs_low hs_high
  let ht_mem :=
    roundedBundleType_mem_roundedAdmissibleTypeSetWithCap_of_load_window
      hlambda hvalueScale hcap t ht_low ht_high
  exact
    (mem_roundedAdmissibleValuePairSetWithCap_iff
      (valueScale := valueScale) (averageScale := averageScale)
      (lambda := lambda) (maxCount := maxCount)
      (roundedBundleTypeLoad valueScale s, roundedBundleTypeLoad valueScale t)).mpr
      ⟨roundedBundleTypeLoad_mem_roundedAdmissibleValueSetWithCap_of_mem hs_mem,
        roundedBundleTypeLoad_mem_roundedAdmissibleValueSetWithCap_of_mem ht_mem⟩

/-- Two-scale admissible type sets are monotone in the count cap. -/
theorem roundedAdmissibleTypeSetWithCap_mono_of_le
    {valueScale averageScale : ℝ} {lambda smallCap largeCap : ℕ}
    (hcap : smallCap ≤ largeCap) :
    roundedAdmissibleTypeSetWithCap valueScale averageScale lambda smallCap ⊆
      roundedAdmissibleTypeSetWithCap valueScale averageScale lambda largeCap := by
  classical
  intro t ht
  have ht' :=
    (mem_roundedAdmissibleTypeSetWithCap_iff
      (valueScale := valueScale) (averageScale := averageScale)
      (lambda := lambda) (maxCount := smallCap) t).mp ht
  exact
    (mem_roundedAdmissibleTypeSetWithCap_iff
      (valueScale := valueScale) (averageScale := averageScale)
      (lambda := lambda) (maxCount := largeCap) t).mpr
      ⟨boundedRoundedBundleTypeSet_mono_of_le hcap ht'.1, ht'.2⟩

/-- Two-scale admissible value sets are monotone in the count cap. -/
theorem roundedAdmissibleValueSetWithCap_mono_of_le
    {valueScale averageScale : ℝ} {lambda smallCap largeCap : ℕ}
    (hcap : smallCap ≤ largeCap) :
    roundedAdmissibleValueSetWithCap valueScale averageScale lambda smallCap ⊆
      roundedAdmissibleValueSetWithCap valueScale averageScale lambda largeCap := by
  classical
  intro u hu
  rcases
      (mem_roundedAdmissibleValueSetWithCap_iff
        (valueScale := valueScale) (averageScale := averageScale)
        (lambda := lambda) (maxCount := smallCap) u).mp hu with
    ⟨t, ht, htu⟩
  exact
    (mem_roundedAdmissibleValueSetWithCap_iff
      (valueScale := valueScale) (averageScale := averageScale)
      (lambda := lambda) (maxCount := largeCap) u).mpr
      ⟨t, roundedAdmissibleTypeSetWithCap_mono_of_le hcap ht, htu⟩

/-- Two-scale admissible value-pair sets are monotone in the count cap. -/
theorem roundedAdmissibleValuePairSetWithCap_mono_of_le
    {valueScale averageScale : ℝ} {lambda smallCap largeCap : ℕ}
    (hcap : smallCap ≤ largeCap) :
    roundedAdmissibleValuePairSetWithCap valueScale averageScale lambda smallCap ⊆
      roundedAdmissibleValuePairSetWithCap valueScale averageScale lambda largeCap := by
  classical
  intro p hp
  have hp' :=
    (mem_roundedAdmissibleValuePairSetWithCap_iff
      (valueScale := valueScale) (averageScale := averageScale)
      (lambda := lambda) (maxCount := smallCap) p).mp hp
  exact
    (mem_roundedAdmissibleValuePairSetWithCap_iff
      (valueScale := valueScale) (averageScale := averageScale)
      (lambda := lambda) (maxCount := largeCap) p).mpr
      ⟨roundedAdmissibleValueSetWithCap_mono_of_le hcap hp'.1,
        roundedAdmissibleValueSetWithCap_mono_of_le hcap hp'.2⟩

/-- Cardinality bound for the two-scale value-pair search space. -/
theorem roundedAdmissibleValuePairSetWithCap_card_le
    (valueScale averageScale : ℝ) (lambda maxCount : ℕ) :
    (roundedAdmissibleValuePairSetWithCap valueScale averageScale lambda maxCount).card ≤
      ((maxCount + 1) ^ Fintype.card (RoundedValueIndex lambda)) ^ 2 := by
  classical
  have hvalue :
      (roundedAdmissibleValueSetWithCap valueScale averageScale lambda maxCount).card ≤
        (roundedAdmissibleTypeSetWithCap valueScale averageScale lambda maxCount).card := by
    unfold roundedAdmissibleValueSetWithCap
    exact Finset.card_image_le
  have htype :=
    roundedAdmissibleTypeSetWithCap_card_le valueScale averageScale lambda maxCount
  have hvalue_bound :
      (roundedAdmissibleValueSetWithCap valueScale averageScale lambda maxCount).card ≤
        (maxCount + 1) ^ Fintype.card (RoundedValueIndex lambda) :=
    le_trans hvalue htype
  have hmul :
      (roundedAdmissibleValueSetWithCap valueScale averageScale lambda maxCount).card *
          (roundedAdmissibleValueSetWithCap valueScale averageScale lambda maxCount).card ≤
        ((maxCount + 1) ^ Fintype.card (RoundedValueIndex lambda)) *
          ((maxCount + 1) ^ Fintype.card (RoundedValueIndex lambda)) :=
    Nat.mul_le_mul hvalue_bound hvalue_bound
  simpa [roundedAdmissibleValuePairSetWithCap, pow_two] using hmul

/--
Explicit two-scale value-pair cardinality bound with the rounded-index
exponent expanded to `lambda^2 + 1`.
-/
theorem roundedAdmissibleValuePairSetWithCap_card_le_explicit
    (valueScale averageScale : ℝ) (lambda maxCount : ℕ) :
    (roundedAdmissibleValuePairSetWithCap valueScale averageScale lambda maxCount).card ≤
      ((maxCount + 1) ^ (lambda ^ 2 + 1)) ^ 2 := by
  have hbase :
      (maxCount + 1) ^ Fintype.card (RoundedValueIndex lambda) ≤
        (maxCount + 1) ^ (lambda ^ 2 + 1) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (roundedValueIndex_card_le lambda)
  exact
    le_trans
      (roundedAdmissibleValuePairSetWithCap_card_le
        valueScale averageScale lambda maxCount)
      (pow_le_pow_left₀ (Nat.zero_le _) hbase 2)

/--
Two-scale selected type set `U_{u1,u2}`: filter the average-window type set by
the chosen min/max utility values.
-/
noncomputable def roundedTypesInValueWindowWithCap
    (valueScale averageScale : ℝ) (lambda maxCount : ℕ)
    (lower upper : ℝ) :
    Finset (RoundedBundleType lambda) := by
  classical
  exact
    (roundedAdmissibleTypeSetWithCap valueScale averageScale lambda maxCount).filter
      (fun t => lower ≤ roundedBundleTypeLoad valueScale t ∧
        roundedBundleTypeLoad valueScale t ≤ upper)

/-- Membership in the two-scale selected type set. -/
theorem mem_roundedTypesInValueWindowWithCap_iff
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ}
    {lower upper : ℝ} (t : RoundedBundleType lambda) :
    t ∈ roundedTypesInValueWindowWithCap
        valueScale averageScale lambda maxCount lower upper ↔
      t ∈ roundedAdmissibleTypeSetWithCap valueScale averageScale lambda maxCount ∧
        lower ≤ roundedBundleTypeLoad valueScale t ∧
          roundedBundleTypeLoad valueScale t ≤ upper := by
  classical
  simp [roundedTypesInValueWindowWithCap]

/-- Two-scale selected type windows are monotone in the count cap. -/
theorem roundedTypesInValueWindowWithCap_mono_of_le
    {valueScale averageScale : ℝ} {lambda smallCap largeCap : ℕ}
    {lower upper : ℝ} (hcap : smallCap ≤ largeCap) :
    roundedTypesInValueWindowWithCap
        valueScale averageScale lambda smallCap lower upper ⊆
      roundedTypesInValueWindowWithCap
        valueScale averageScale lambda largeCap lower upper := by
  classical
  intro t ht
  have ht' :=
    (mem_roundedTypesInValueWindowWithCap_iff
      (valueScale := valueScale) (averageScale := averageScale)
      (lambda := lambda) (maxCount := smallCap)
      (lower := lower) (upper := upper) t).mp ht
  exact
    (mem_roundedTypesInValueWindowWithCap_iff
      (valueScale := valueScale) (averageScale := averageScale)
      (lambda := lambda) (maxCount := largeCap)
      (lower := lower) (upper := upper) t).mpr
      ⟨roundedAdmissibleTypeSetWithCap_mono_of_le hcap ht'.1, ht'.2⟩

/--
Concrete IP certificate for the two-scale value-pair search, for one rounded
goods-supply vector.
-/
structure RoundedConcreteIPCertificateWithCap
    (valueScale averageScale : ℝ) (lambda maxCount : ℕ)
    (Agent : Type*) [Fintype Agent]
    (p : ℝ × ℝ) (goodsSupply : RoundedValueIndex lambda → ℕ) where
  pair_mem :
    p ∈ roundedAdmissibleValuePairSetWithCap valueScale averageScale lambda maxCount
  typeMultiplicity : RoundedBundleType lambda → ℕ
  zeroOutsideWindow :
    ∀ t : RoundedBundleType lambda,
      t ∉ roundedTypesInValueWindowWithCap
          valueScale averageScale lambda maxCount p.1 p.2 →
        typeMultiplicity t = 0
  allPlayersAssigned :
    (roundedTypesInValueWindowWithCap
        valueScale averageScale lambda maxCount p.1 p.2).sum typeMultiplicity =
      Fintype.card Agent
  allGoodsAssigned :
    ∀ k : RoundedValueIndex lambda,
      (roundedTypesInValueWindowWithCap
          valueScale averageScale lambda maxCount p.1 p.2).sum
          (fun t => typeMultiplicity t * t.count k) =
        goodsSupply k

/-- Positive multiplicity in a capped concrete IP is confined to the selected value window. -/
theorem RoundedConcreteIPCertificateWithCap.used_type_mem_window
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ}
    {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ} {goodsSupply : RoundedValueIndex lambda → ℕ}
    (cert :
      RoundedConcreteIPCertificateWithCap
        valueScale averageScale lambda maxCount Agent p goodsSupply)
    {t : RoundedBundleType lambda}
    (ht : 0 < cert.typeMultiplicity t) :
    t ∈ roundedTypesInValueWindowWithCap
      valueScale averageScale lambda maxCount p.1 p.2 := by
  classical
  by_contra hnot
  have hzero := cert.zeroOutsideWindow t hnot
  omega

/--
A concrete capped IP certificate remains feasible at any larger count cap.
The multiplicities are unchanged; the larger window contributes only zero
outside the smaller feasible window.
-/
def RoundedConcreteIPCertificateWithCap.mono_of_le
    {valueScale averageScale : ℝ} {lambda smallCap largeCap : ℕ}
    {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ} {goodsSupply : RoundedValueIndex lambda → ℕ}
    (cert :
      RoundedConcreteIPCertificateWithCap
        valueScale averageScale lambda smallCap Agent p goodsSupply)
    (hcap : smallCap ≤ largeCap) :
    RoundedConcreteIPCertificateWithCap
      valueScale averageScale lambda largeCap Agent p goodsSupply where
  pair_mem :=
    roundedAdmissibleValuePairSetWithCap_mono_of_le hcap cert.pair_mem
  typeMultiplicity := cert.typeMultiplicity
  zeroOutsideWindow := by
    intro t hnot_large
    exact cert.zeroOutsideWindow t
      (fun ht_small =>
        hnot_large
          (roundedTypesInValueWindowWithCap_mono_of_le hcap ht_small))
  allPlayersAssigned := by
    classical
    let smallWindow :=
      roundedTypesInValueWindowWithCap
        valueScale averageScale lambda smallCap p.1 p.2
    let largeWindow :=
      roundedTypesInValueWindowWithCap
        valueScale averageScale lambda largeCap p.1 p.2
    have hsubset : smallWindow ⊆ largeWindow :=
      roundedTypesInValueWindowWithCap_mono_of_le
        (valueScale := valueScale) (averageScale := averageScale)
        (lambda := lambda) (smallCap := smallCap) (largeCap := largeCap)
        (lower := p.1) (upper := p.2) hcap
    have hsum :
        smallWindow.sum cert.typeMultiplicity =
          largeWindow.sum cert.typeMultiplicity :=
      Finset.sum_subset hsubset
        (fun t _ht_large ht_not_small =>
          cert.zeroOutsideWindow t ht_not_small)
    dsimp [smallWindow, largeWindow] at hsum
    exact hsum.symm.trans cert.allPlayersAssigned
  allGoodsAssigned := by
    classical
    intro k
    let smallWindow :=
      roundedTypesInValueWindowWithCap
        valueScale averageScale lambda smallCap p.1 p.2
    let largeWindow :=
      roundedTypesInValueWindowWithCap
        valueScale averageScale lambda largeCap p.1 p.2
    have hsubset : smallWindow ⊆ largeWindow :=
      roundedTypesInValueWindowWithCap_mono_of_le
        (valueScale := valueScale) (averageScale := averageScale)
        (lambda := lambda) (smallCap := smallCap) (largeCap := largeCap)
        (lower := p.1) (upper := p.2) hcap
    have hsum :
        smallWindow.sum
            (fun t => cert.typeMultiplicity t * t.count k) =
          largeWindow.sum
            (fun t => cert.typeMultiplicity t * t.count k) :=
      Finset.sum_subset hsubset
        (fun t _ht_large ht_not_small => by
          simp [cert.zeroOutsideWindow t ht_not_small])
    dsimp [smallWindow, largeWindow] at hsum
    exact hsum.symm.trans (cert.allGoodsAssigned k)

/-- Concrete two-scale IP certificate induced by a type assignment. -/
def roundedConcreteIPCertificateWithCapOfTypeAssignment
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ}
    {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ}
    (hpair :
      p ∈ roundedAdmissibleValuePairSetWithCap valueScale averageScale lambda maxCount)
    (typeOf : Agent → RoundedBundleType lambda)
    (htypes :
      ∀ i : Agent,
        typeOf i ∈ roundedTypesInValueWindowWithCap
          valueScale averageScale lambda maxCount p.1 p.2) :
    RoundedConcreteIPCertificateWithCap
      valueScale averageScale lambda maxCount Agent p
      (fun k : RoundedValueIndex lambda => ∑ i : Agent, (typeOf i).count k) where
  pair_mem := hpair
  typeMultiplicity := roundedTypeMultiplicityOfAssignment typeOf
  zeroOutsideWindow := by
    intro t hnot
    exact roundedTypeMultiplicityOfAssignment_eq_zero_of_not_mem
      typeOf htypes hnot
  allPlayersAssigned :=
    roundedTypeMultiplicityOfAssignment_sum_eq_card typeOf htypes
  allGoodsAssigned := by
    intro k
    exact roundedTypeMultiplicityOfAssignment_goods_count_eq_sum_agents
      typeOf htypes k

/--
Concrete two-scale IP certificate induced by a type assignment for an external
rounded goods-supply vector.
-/
def roundedConcreteIPCertificateWithCapOfSupplyTypeAssignment
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ}
    {Agent : Type*} [Fintype Agent]
    {p : ℝ × ℝ} {goodsSupply : RoundedValueIndex lambda → ℕ}
    (hpair :
      p ∈ roundedAdmissibleValuePairSetWithCap valueScale averageScale lambda maxCount)
    (typeOf : Agent → RoundedBundleType lambda)
    (htypes :
      ∀ i : Agent,
        typeOf i ∈ roundedTypesInValueWindowWithCap
          valueScale averageScale lambda maxCount p.1 p.2)
    (hcounts :
      ∀ k : RoundedValueIndex lambda,
        (∑ i : Agent, (typeOf i).count k) = goodsSupply k) :
    RoundedConcreteIPCertificateWithCap
      valueScale averageScale lambda maxCount Agent p goodsSupply where
  pair_mem := hpair
  typeMultiplicity := roundedTypeMultiplicityOfAssignment typeOf
  zeroOutsideWindow := by
    intro t hnot
    exact roundedTypeMultiplicityOfAssignment_eq_zero_of_not_mem
      typeOf htypes hnot
  allPlayersAssigned :=
    roundedTypeMultiplicityOfAssignment_sum_eq_card typeOf htypes
  allGoodsAssigned := by
    intro k
    rw [roundedTypeMultiplicityOfAssignment_goods_count_eq_sum_agents
      typeOf htypes k]
    exact hcounts k

/--
Search certificate for the two-scale scan over feasible value pairs for one
rounded goods-supply vector.
-/
structure RoundedValuePairSearchCertificateWithCap
    (valueScale averageScale : ℝ) (lambda maxCount : ℕ)
    (Agent : Type*) [Fintype Agent]
    (goodsSupply : RoundedValueIndex lambda → ℕ) where
  chosenPair : ℝ × ℝ
  chosenIP :
    RoundedConcreteIPCertificateWithCap
      valueScale averageScale lambda maxCount Agent chosenPair goodsSupply
  optimalAmongFeasible :
    ∀ p : ℝ × ℝ,
      RoundedConcreteIPCertificateWithCap
        valueScale averageScale lambda maxCount Agent p goodsSupply →
        roundedValuePairRatio chosenPair ≤ roundedValuePairRatio p

/-- The chosen pair in a two-scale search certificate is in the searched set. -/
theorem RoundedValuePairSearchCertificateWithCap.chosenPair_mem
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ}
    {Agent : Type*} [Fintype Agent]
    {goodsSupply : RoundedValueIndex lambda → ℕ}
    (cert :
      RoundedValuePairSearchCertificateWithCap
        valueScale averageScale lambda maxCount Agent goodsSupply) :
    cert.chosenPair ∈
      roundedAdmissibleValuePairSetWithCap valueScale averageScale lambda maxCount :=
  cert.chosenIP.pair_mem

/-- A two-scale search certificate is no worse than any concrete feasible pair. -/
theorem RoundedValuePairSearchCertificateWithCap.ratio_le_of_concrete_feasible_pair
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ}
    {Agent : Type*} [Fintype Agent]
    {goodsSupply : RoundedValueIndex lambda → ℕ}
    (cert :
      RoundedValuePairSearchCertificateWithCap
        valueScale averageScale lambda maxCount Agent goodsSupply)
    {p : ℝ × ℝ}
    (other :
      RoundedConcreteIPCertificateWithCap
        valueScale averageScale lambda maxCount Agent p goodsSupply) :
    roundedValuePairRatio cert.chosenPair ≤ roundedValuePairRatio p :=
  cert.optimalAmongFeasible p other

/--
Classical finite search over the two-scale pair set: any concrete feasible pair
for the current rounded supply can be compared against a best feasible pair.
-/
theorem exists_roundedValuePairSearchCertificateWithCap_of_feasible_pair
    {valueScale averageScale : ℝ} {lambda maxCount : ℕ}
    {Agent : Type*} [Fintype Agent]
    {goodsSupply : RoundedValueIndex lambda → ℕ} {p : ℝ × ℝ}
    (ip :
      RoundedConcreteIPCertificateWithCap
        valueScale averageScale lambda maxCount Agent p goodsSupply) :
    ∃ search :
      RoundedValuePairSearchCertificateWithCap
        valueScale averageScale lambda maxCount Agent goodsSupply,
      roundedValuePairRatio search.chosenPair ≤ roundedValuePairRatio p := by
  classical
  let feasiblePairs : Finset (ℝ × ℝ) :=
    (roundedAdmissibleValuePairSetWithCap valueScale averageScale lambda maxCount).filter
      (fun q =>
        Nonempty
          (RoundedConcreteIPCertificateWithCap
            valueScale averageScale lambda maxCount Agent q goodsSupply))
  have hp_mem : p ∈ feasiblePairs := by
    refine Finset.mem_filter.mpr ⟨ip.pair_mem, ?_⟩
    exact ⟨ip⟩
  have hnonempty : feasiblePairs.Nonempty := ⟨p, hp_mem⟩
  rcases Finset.exists_min_image feasiblePairs roundedValuePairRatio hnonempty with
    ⟨best, hbest_mem, hbest_le⟩
  have hbest_nonempty :
      Nonempty
        (RoundedConcreteIPCertificateWithCap
          valueScale averageScale lambda maxCount Agent best goodsSupply) :=
    (Finset.mem_filter.mp hbest_mem).2
  let bestIP :
      RoundedConcreteIPCertificateWithCap
        valueScale averageScale lambda maxCount Agent best goodsSupply :=
    Classical.choice hbest_nonempty
  let search :
      RoundedValuePairSearchCertificateWithCap
        valueScale averageScale lambda maxCount Agent goodsSupply :=
    { chosenPair := best
      chosenIP := bestIP
      optimalAmongFeasible := by
        intro q qip
        have hq_mem : q ∈ feasiblePairs := by
          refine Finset.mem_filter.mpr ⟨qip.pair_mem, ?_⟩
          exact ⟨qip⟩
        exact hbest_le q hq_mem }
  refine ⟨search, ?_⟩
  exact hbest_le p hp_mem

/--
If a concrete feasible pair is certified at a smaller cap, the finite search at
any larger cap can compare against the same pair.
-/
theorem exists_roundedValuePairSearchCertificateWithCap_of_smaller_cap_feasible_pair
    {valueScale averageScale : ℝ} {lambda smallCap largeCap : ℕ}
    {Agent : Type*} [Fintype Agent]
    {goodsSupply : RoundedValueIndex lambda → ℕ} {p : ℝ × ℝ}
    (hcap : smallCap ≤ largeCap)
    (ip :
      RoundedConcreteIPCertificateWithCap
        valueScale averageScale lambda smallCap Agent p goodsSupply) :
    ∃ search :
      RoundedValuePairSearchCertificateWithCap
        valueScale averageScale lambda largeCap Agent goodsSupply,
      roundedValuePairRatio search.chosenPair ≤ roundedValuePairRatio p :=
  exists_roundedValuePairSearchCertificateWithCap_of_feasible_pair
    (ip.mono_of_le hcap)

/--
Source-shaped rounded-instance certificate for Theorem 3.3.

The rounded allocation is the IP optimum in the rounded instance, the output
allocation is its Lemma 3.5 transfer back to the original instance, and the two
ratio inequalities are exactly the two transfer estimates used in the source
proof before the final algebraic simplification.
-/
structure RoundedInstanceCertificate
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc)
    (epsilon : ℝ) (lambda : ℕ) (optimal : Alloc) where
  roundedAllocation : Alloc
  outputAllocation : Alloc
  ipFeasible : RoundedTypeIPCertificate lambda Agent
  optimalMin_pos : 0 < minAllocationLoad M optimal
  optimalMax_nonneg : 0 ≤ maxAllocationLoad M optimal
  roundedToSourceTransfer :
    allocationLoadRatio M outputAllocation ≤
      allocationLoadRatio M roundedAllocation *
        Theorem35.backwardTransferFactor (56 / epsilon)
  sourceToRoundedOptimal :
    allocationLoadRatio M roundedAllocation ≤
      allocationLoadRatio M optimal *
        Theorem35.forwardTransferFactor (56 / epsilon)

/-- The allocation produced by a rounded-instance certificate. -/
def RoundedInstanceCertificate.output
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (cert : RoundedInstanceCertificate M epsilon lambda optimal) : Alloc :=
  cert.outputAllocation

/-- The rounded allocation found by the finite type/IP search certificate. -/
def RoundedInstanceCertificate.rounded
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (cert : RoundedInstanceCertificate M epsilon lambda optimal) : Alloc :=
  cert.roundedAllocation

/--
The finite type/IP certificate carried by a rounded-instance certificate is
available as a standalone witness.
-/
def RoundedInstanceCertificate.ipCertificate
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (cert : RoundedInstanceCertificate M epsilon lambda optimal) :
    RoundedTypeIPCertificate lambda Agent :=
  cert.ipFeasible

/--
Source-shaped rounded-instance search certificate for Theorem 3.3.

This strengthens `RoundedInstanceCertificate` by including the finite scan over
value pairs in `V(U) × V(U)`.  The rounded allocation and transfer inequalities
remain certificate fields; the pair-search layer records the source step before
the Lenstra/IP construction boundary.
-/
structure RoundedInstanceSearchCertificate
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    (M : IdenticalUtilitiesModel Agent Item Alloc)
    (L : ℝ) (epsilon : ℝ) (lambda : ℕ) (optimal : Alloc) where
  roundedAllocation : Alloc
  outputAllocation : Alloc
  pairSearch : RoundedValuePairSearchCertificate L lambda Agent
  optimalMin_pos : 0 < minAllocationLoad M optimal
  optimalMax_nonneg : 0 ≤ maxAllocationLoad M optimal
  roundedToSourceTransfer :
    allocationLoadRatio M outputAllocation ≤
      allocationLoadRatio M roundedAllocation *
        Theorem35.backwardTransferFactor (56 / epsilon)
  sourceToRoundedOptimal :
    allocationLoadRatio M roundedAllocation ≤
      allocationLoadRatio M optimal *
        Theorem35.forwardTransferFactor (56 / epsilon)

/-- The allocation produced by a rounded-instance search certificate. -/
def RoundedInstanceSearchCertificate.output
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (cert : RoundedInstanceSearchCertificate M L epsilon lambda optimal) : Alloc :=
  cert.outputAllocation

/-- The rounded allocation carried by a rounded-instance search certificate. -/
def RoundedInstanceSearchCertificate.rounded
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (cert : RoundedInstanceSearchCertificate M L epsilon lambda optimal) : Alloc :=
  cert.roundedAllocation

/-- The selected source value pair from the finite scan. -/
def RoundedInstanceSearchCertificate.chosenPair
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (cert : RoundedInstanceSearchCertificate M L epsilon lambda optimal) :
    ℝ × ℝ :=
  cert.pairSearch.chosenPair

/-- The selected IP certificate from the finite value-pair scan. -/
def RoundedInstanceSearchCertificate.ipCertificate
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (cert : RoundedInstanceSearchCertificate M L epsilon lambda optimal) :
    RoundedTypeIPCertificate lambda Agent :=
  cert.pairSearch.chosenIP.ip

/--
Forget the explicit value-pair scan and recover the earlier rounded-instance
certificate seam.
-/
def RoundedInstanceSearchCertificate.toRoundedInstanceCertificate
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (cert : RoundedInstanceSearchCertificate M L epsilon lambda optimal) :
    RoundedInstanceCertificate M epsilon lambda optimal where
  roundedAllocation := cert.roundedAllocation
  outputAllocation := cert.outputAllocation
  ipFeasible := cert.ipCertificate
  optimalMin_pos := cert.optimalMin_pos
  optimalMax_nonneg := cert.optimalMax_nonneg
  roundedToSourceTransfer := cert.roundedToSourceTransfer
  sourceToRoundedOptimal := cert.sourceToRoundedOptimal

/--
Main certificate seam for LMMS Theorem 3.3: a rounded allocation with finite
type/IP feasibility and the two Lemma 3.5 transfer inequalities yields the
model-level `(1 + epsilon)` ratio guarantee.
-/
theorem roundedInstanceCertificate_ratio_guarantee
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : RoundedInstanceCertificate M epsilon lambda optimal) :
    allocationLoadRatio M cert.output ≤
      allocationLoadRatio M optimal * (1 + epsilon) := by
  exact
    allocationLoadRatio_transfer_certificate_epsilon
      M hepsilon_pos hepsilon_le_one cert.optimalMin_pos
      cert.optimalMax_nonneg cert.roundedToSourceTransfer
      cert.sourceToRoundedOptimal

/--
Equivalent wrapper using the structure field name for the output allocation.
-/
theorem roundedInstanceCertificate_outputAllocation_ratio_guarantee
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : RoundedInstanceCertificate M epsilon lambda optimal) :
    allocationLoadRatio M cert.outputAllocation ≤
      allocationLoadRatio M optimal * (1 + epsilon) := by
  simpa [RoundedInstanceCertificate.output] using
    roundedInstanceCertificate_ratio_guarantee
      hepsilon_pos hepsilon_le_one cert

/--
Theorem 3.3 search-certificate seam: a finite scan over value pairs, together
with the rounded/source transfer inequalities, yields the same
`(1 + epsilon)` ratio guarantee.
-/
theorem roundedInstanceSearchCertificate_ratio_guarantee
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : RoundedInstanceSearchCertificate M L epsilon lambda optimal) :
    allocationLoadRatio M cert.output ≤
      allocationLoadRatio M optimal * (1 + epsilon) := by
  simpa [RoundedInstanceSearchCertificate.output,
    RoundedInstanceSearchCertificate.toRoundedInstanceCertificate,
    RoundedInstanceCertificate.output] using
    roundedInstanceCertificate_ratio_guarantee
      hepsilon_pos hepsilon_le_one
      cert.toRoundedInstanceCertificate

/--
Equivalent wrapper using the structure field name for the output allocation.
-/
theorem roundedInstanceSearchCertificate_outputAllocation_ratio_guarantee
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : RoundedInstanceSearchCertificate M L epsilon lambda optimal) :
    allocationLoadRatio M cert.outputAllocation ≤
      allocationLoadRatio M optimal * (1 + epsilon) := by
  simpa [RoundedInstanceSearchCertificate.output] using
    roundedInstanceSearchCertificate_ratio_guarantee
      hepsilon_pos hepsilon_le_one cert

/--
Bundled Theorem 3.3 search seam: a rounded-instance search certificate gives
the final ratio guarantee, and any concrete goods-supply IP candidate carries
the finite value-pair comparison plus its assignment and goods equations.
-/
theorem roundedInstanceSearchCertificate_ratio_guarantee_and_concrete_ip_summary
    {Agent Item Alloc : Type*} [Fintype Agent] [Nonempty Agent]
    {M : IdenticalUtilitiesModel Agent Item Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    {p : ℝ × ℝ} {goodsSupply : RoundedValueIndex lambda → ℕ}
    (ip : RoundedConcreteIPCertificate L lambda Agent p goodsSupply) :
    allocationLoadRatio M cert.output ≤
        allocationLoadRatio M optimal * (1 + epsilon) ∧
      roundedValuePairRatio cert.chosenPair ≤ roundedValuePairRatio p ∧
      ip.toValuePairIPCertificate.ip.admissibleTypes.card ≤
          (2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda) ∧
      ip.toValuePairIPCertificate.ip.admissibleTypes.sum
          ip.toValuePairIPCertificate.ip.typeMultiplicity =
        Fintype.card Agent ∧
      (∀ k : RoundedValueIndex lambda,
        ip.toValuePairIPCertificate.ip.admissibleTypes.sum
            (fun t => ip.toValuePairIPCertificate.ip.typeMultiplicity t * t.count k) =
          goodsSupply k) := by
  have hsummary :
      ip.toValuePairIPCertificate.ip.admissibleTypes.card ≤
          (2 * lambda + 1) ^ Fintype.card (RoundedValueIndex lambda) ∧
        ip.toValuePairIPCertificate.ip.admissibleTypes.sum
            ip.toValuePairIPCertificate.ip.typeMultiplicity =
          Fintype.card Agent ∧
        (∀ k : RoundedValueIndex lambda,
          ip.toValuePairIPCertificate.ip.admissibleTypes.sum
              (fun t => ip.toValuePairIPCertificate.ip.typeMultiplicity t * t.count k) =
            goodsSupply k) :=
    RoundedConcreteIPCertificate.toValuePairIPCertificate_feasibility_summary ip
  exact
    ⟨roundedInstanceSearchCertificate_ratio_guarantee
        hepsilon_pos hepsilon_le_one cert,
      cert.pairSearch.ratio_le_of_concrete_feasible_pair ip,
      hsummary.1, hsummary.2.1, hsummary.2.2⟩

end

end Theorem33
end LMMS04FairDivision
