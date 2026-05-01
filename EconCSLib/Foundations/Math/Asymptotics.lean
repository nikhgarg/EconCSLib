import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Topology

namespace EconCSLib
namespace Math

/-- A sequence tends to zero. -/
def TendsToZero (ε : ℕ → ℝ) : Prop :=
  Tendsto ε atTop (nhds 0)

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

end Math
end EconCSLib
