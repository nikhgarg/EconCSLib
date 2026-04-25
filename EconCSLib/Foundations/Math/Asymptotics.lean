import Mathlib.Topology.Instances.Real
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

end Math
end EconCSLib
