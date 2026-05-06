import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Topology

namespace EconCSLib
namespace Math

/-- A sequence tends to zero. -/
def TendsToZero (ε : ℕ → ℝ) : Prop :=
  Tendsto ε atTop (nhds 0)

/-- `x n` is asymptotically equivalent to `y n`, expressed as `x n / y n -> 1`. -/
def AsymptoticEquivalent (x y : ℕ → ℝ) : Prop :=
  Tendsto (fun n => x n / y n) atTop (nhds 1)

/-- A sequence is bounded by C / N. -/
def TendsToZeroInv (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, 0 < N → |ε N| ≤ C / (N : ℝ)

/-- A sequence is bounded by C / sqrt(N). -/
def TendsToZeroInvSqrt (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, 0 < N → |ε N| ≤ C / Real.sqrt (N : ℝ)

/-- A sequence has exact paper-style `C / N` error rate. -/
def ExactInvRate (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, ε N = C / (N : ℝ)

/-- A sequence has exact paper-style `C / sqrt N` error rate. -/
def ExactInvSqrtRate (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, ε N = C / Real.sqrt (N : ℝ)

namespace AsymptoticEquivalent

theorem eventually_ratio_mem_Icc
    {x y : ℕ → ℝ} (h : AsymptoticEquivalent x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      1 - ε ≤ x n / y n ∧ x n / y n ≤ 1 + ε := by
  have hlow : ∀ᶠ n in atTop, 1 - ε ≤ x n / y n := by
    exact h.eventually_const_le (by linarith)
  have hhigh : ∀ᶠ n in atTop, x n / y n ≤ 1 + ε := by
    exact h.eventually_le_const (by linarith)
  filter_upwards [hlow, hhigh] with n hnlow hnhigh
  exact ⟨hnlow, hnhigh⟩

theorem eventually_sandwich_of_pos_right
    {x y : ℕ → ℝ} (h : AsymptoticEquivalent x y)
    (hy_pos : ∀ᶠ n in atTop, 0 < y n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (1 - ε) * y n ≤ x n ∧ x n ≤ (1 + ε) * y n := by
  filter_upwards [h.eventually_ratio_mem_Icc hε, hy_pos] with n hratio hy
  have heq : x n = (x n / y n) * y n := by
    field_simp [ne_of_gt hy]
  constructor
  · calc
      (1 - ε) * y n ≤ (x n / y n) * y n :=
        mul_le_mul_of_nonneg_right hratio.1 hy.le
      _ = x n := by rw [← heq]
  · calc
      x n = (x n / y n) * y n := heq
      _ ≤ (1 + ε) * y n :=
        mul_le_mul_of_nonneg_right hratio.2 hy.le

end AsymptoticEquivalent

theorem ExactInvRate_implies_TendsToZeroInv (ε : ℕ → ℝ) :
    ExactInvRate ε → TendsToZeroInv ε := by
  intro ⟨C, hCpos, hε⟩
  refine ⟨C, hCpos, ?_⟩
  intro N hN
  rw [hε N]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnonneg : 0 ≤ C / (N : ℝ) := div_nonneg hCpos.le hNpos.le
  rw [abs_of_nonneg hnonneg]

theorem ExactInvSqrtRate_implies_TendsToZeroInvSqrt (ε : ℕ → ℝ) :
    ExactInvSqrtRate ε → TendsToZeroInvSqrt ε := by
  intro ⟨C, hCpos, hε⟩
  refine ⟨C, hCpos, ?_⟩
  intro N hN
  rw [hε N]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hnonneg : 0 ≤ C / Real.sqrt (N : ℝ) := div_nonneg hCpos.le hsqrt_pos.le
  rw [abs_of_nonneg hnonneg]

theorem TendsToZeroInv_implies_TendsToZero (ε : ℕ → ℝ) :
    TendsToZeroInv ε → TendsToZero ε := by
  intro ⟨C, hCpos, hbound⟩
  rw [TendsToZero]
  have h_zero : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat C
  have h_neg_zero : Tendsto (fun N : ℕ => -(C / (N : ℝ))) atTop (nhds 0) := by
    have h := h_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_zero h_zero
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := hbound N hN
    rw [abs_le] at h1
    exact h1.1
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := hbound N hN
    rw [abs_le] at h1
    exact h1.2

theorem ExactInvRate_implies_TendsToZero (ε : ℕ → ℝ) :
    ExactInvRate ε → TendsToZero ε := by
  intro hε
  exact TendsToZeroInv_implies_TendsToZero ε
    (ExactInvRate_implies_TendsToZeroInv ε hε)

theorem TendsToZeroInvSqrt_implies_TendsToZero (ε : ℕ → ℝ) :
    TendsToZeroInvSqrt ε → TendsToZero ε := by
  intro ⟨C, hCpos, hbound⟩
  rw [TendsToZero]
  have h_sqrt_atTop :
      Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop := by
    exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h_zero :
      Tendsto (fun N : ℕ => C / Real.sqrt (N : ℝ)) atTop (nhds 0) := by
    exact Filter.Tendsto.const_div_atTop h_sqrt_atTop C
  have h_neg_zero :
      Tendsto (fun N : ℕ => -(C / Real.sqrt (N : ℝ))) atTop (nhds 0) := by
    have h := h_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_zero h_zero
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := hbound N hN
    rw [abs_le] at h1
    exact h1.1
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := hbound N hN
    rw [abs_le] at h1
    exact h1.2

theorem ExactInvSqrtRate_implies_TendsToZero (ε : ℕ → ℝ) :
    ExactInvSqrtRate ε → TendsToZero ε := by
  intro hε
  exact TendsToZeroInvSqrt_implies_TendsToZero ε
    (ExactInvSqrtRate_implies_TendsToZeroInvSqrt ε hε)

/-- A sequence tends to zero if it is eventually dominated by `C / N`. -/
theorem TendsToZero_of_eventually_abs_le_inv (ε : ℕ → ℝ) {C : ℝ}
    (_hC : 0 < C) (hbound : ∀ᶠ N in atTop, |ε N| ≤ C / (N : ℝ)) :
    TendsToZero ε := by
  rw [TendsToZero]
  have h_zero : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have h_neg_zero : Tendsto (fun N : ℕ => -(C / (N : ℝ))) atTop (nhds 0) := by
    have h := h_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_zero h_zero
  · filter_upwards [hbound, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    exact hN.1
  · filter_upwards [hbound, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    exact hN.2

/-- A nonnegative sequence bounded by `C / N` tends to zero. -/
theorem TendsToZero_of_nonneg_le_const_div
    (ε : ℕ → ℝ) {C : ℝ}
    (hC : 0 < C)
    (hnonneg : ∀ N, 0 ≤ ε N)
    (hbound : ∀ N, 0 < N → ε N ≤ C / (N : ℝ)) :
    TendsToZero ε := by
  refine TendsToZero_of_eventually_abs_le_inv ε hC ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [abs_of_nonneg (hnonneg N)]
  exact hbound N hN

/--
A sequence tends to zero if its absolute value is eventually bounded by another
sequence tending to zero.
-/
theorem TendsToZero_of_eventually_abs_le_tendsto_zero
    (ε bound : ℕ → ℝ)
    (hbound_zero : Tendsto bound atTop (nhds 0))
    (hbound : ∀ᶠ N in atTop, |ε N| ≤ bound N) :
    TendsToZero ε := by
  rw [TendsToZero]
  have hneg_zero : Tendsto (fun N => -bound N) atTop (nhds 0) := by
    have h := hbound_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg_zero hbound_zero
  · filter_upwards [hbound] with N hN
    exact (abs_le.mp hN).1
  · filter_upwards [hbound] with N hN
    exact (abs_le.mp hN).2

/-- `log N` tends to infinity along natural numbers. -/
theorem tendsto_log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- A constant divided by `log N` tends to zero. -/
theorem tendsto_const_div_log_nat_nhds_zero (C : ℝ) :
    Tendsto (fun N : ℕ => C / Real.log (N : ℝ)) atTop (nhds 0) :=
  Filter.Tendsto.const_div_atTop tendsto_log_nat_atTop C

/-- `log N / sqrt N` tends to zero. -/
theorem tendsto_log_div_sqrt_nat_nhds_zero :
    Tendsto
      (fun N : ℕ => Real.log (N : ℝ) / Real.sqrt (N : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (nhds 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ))
        (by norm_num)).tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- A sequence tends to zero if it is eventually dominated by `C / √N`. -/
theorem TendsToZero_of_eventually_abs_le_inv_sqrt (ε : ℕ → ℝ) {C : ℝ}
    (_hC : 0 < C) (hbound : ∀ᶠ N in atTop, |ε N| ≤ C / Real.sqrt (N : ℝ)) :
    TendsToZero ε := by
  rw [TendsToZero]
  have h_sqrt_atTop :
      Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h_zero : Tendsto (fun N : ℕ => C / Real.sqrt (N : ℝ)) atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop h_sqrt_atTop C
  have h_neg_zero : Tendsto (fun N : ℕ => -(C / Real.sqrt (N : ℝ))) atTop (nhds 0) := by
    have h := h_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_zero h_zero
  · filter_upwards [hbound, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    exact hN.1
  · filter_upwards [hbound, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    exact hN.2

/--
If a nonnegative sequence is bounded by a constant, then dividing it by `N`
tends to zero.
-/
theorem TendsToZero_ratio_of_nonneg_bounded (x : ℕ → ℝ) {C : ℝ}
    (hC : 0 < C) (hx_nonneg : ∀ N, 0 ≤ x N) (hx_bound : ∀ N, x N ≤ C) :
    TendsToZero fun N => x N / (N : ℝ) := by
  refine TendsToZero_of_eventually_abs_le_inv (fun N => x N / (N : ℝ)) hC ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNreal_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdiv_nonneg : 0 ≤ x N / (N : ℝ) :=
    div_nonneg (hx_nonneg N) hNreal_pos.le
  rw [abs_of_nonneg hdiv_nonneg]
  exact div_le_div_of_nonneg_right (hx_bound N) hNreal_pos.le

/--
Order is closed under limits of real sequences: if `x N <= y N` for every
index and the two sequences converge, then the limiting values satisfy the same
inequality.
-/
theorem le_of_tendsto_atTop_of_forall_le
    {x y : ℕ → ℝ} {X Y : ℝ}
    (hx : Tendsto x atTop (nhds X))
    (hy : Tendsto y atTop (nhds Y))
    (hle : ∀ N, x N ≤ y N) :
    X ≤ Y :=
  le_of_tendsto_of_tendsto' hx hy hle

end Math
end EconCSLib
