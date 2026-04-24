import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace EconCSLean
namespace Math

/-- A sequence tends to zero. -/
def TendsToZero (ε : ℕ → ℝ) : Prop :=
  Filter.Tendsto ε Filter.atTop (nhds 0)

/-- A sequence is bounded by C / N. -/
def TendsToZeroInv (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, 0 < N → |ε N| ≤ C / (N : ℝ)

/-- A sequence is bounded by C / sqrt(N). -/
def TendsToZeroInvSqrt (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, 0 < N → |ε N| ≤ C / Real.sqrt (N : ℝ)

theorem TendsToZeroInv_implies_TendsToZero (ε : ℕ → ℝ) :
    TendsToZeroInv ε → TendsToZero ε := by
  intro ⟨C, hCpos, hbound⟩
  apply Filter.tendsto_of_abs_le_seq (fun N => C / (N : ℝ))
  · intro N hN
    have hNpos : 0 < N := by
      -- atTop filter means we only care about large N
      sorry
    exact hbound N hNpos
  · -- tendsto C/N to 0
    sorry

end Math
end EconCSLean
