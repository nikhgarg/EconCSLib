import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace EconCSLean
namespace Sequence

/--
Elementary epsilon definition of convergence for real sequences indexed by
natural numbers.
-/
def SeqTendsTo (x : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → |x k - L| ≤ δ

/--
If `x k` is eventually at most `y k + δ` for every positive `δ`, and the
two real sequences converge to `X` and `Y`, then `X ≤ Y`.
-/
theorem le_of_seqTendsTo_eventually_le_add
    {x y : ℕ → ℝ} {X Y : ℝ}
    (hx : SeqTendsTo x X)
    (hy : SeqTendsTo y Y)
    (happrox :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k → x k ≤ y k + δ) :
    X ≤ Y := by
  by_contra hnot
  have hlt : Y < X := lt_of_not_ge hnot
  have hgap_pos : 0 < X - Y := sub_pos.mpr hlt
  let η := (X - Y) / 4
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  obtain ⟨Nx, hNx⟩ := hx η hη_pos
  obtain ⟨Ny, hNy⟩ := hy η hη_pos
  obtain ⟨Na, hNa⟩ := happrox η hη_pos
  let K := max Nx (max Ny Na)
  have hxK : |x K - X| ≤ η :=
    hNx K (Nat.le_max_left Nx (max Ny Na))
  have hyK : |y K - Y| ≤ η := by
    exact hNy K
      (Nat.le_trans (Nat.le_max_left Ny Na)
        (Nat.le_max_right Nx (max Ny Na)))
  have haK : x K ≤ y K + η := by
    exact hNa K
      (Nat.le_trans (Nat.le_max_right Ny Na)
        (Nat.le_max_right Nx (max Ny Na)))
  have hX_le_x : X ≤ x K + η := by
    have hleft := (abs_le.mp hxK).1
    linarith
  have hy_le_Y : y K ≤ Y + η := by
    have hright := (abs_le.mp hyK).2
    linarith
  have hle : X ≤ Y + 3 * η := by
    linarith
  have hlt_final : Y + 3 * η < X := by
    dsimp [η]
    linarith
  exact (not_lt_of_ge hle) hlt_final

end Sequence
end EconCSLean
