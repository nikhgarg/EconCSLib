import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

namespace DecisionCore

open Set

/--
On a compact interval, if a continuous function is nonpositive at the left
endpoint and positive at the right endpoint, then there is a last nonpositive
point. Every later point in the interval is strictly positive.
-/
theorem exists_last_nonpos_with_right_pos_on_Icc
    {d : ℝ → ℝ} {lo hi : ℝ}
    (hlohi : lo < hi)
    (hd : ContinuousOn d (Icc lo hi))
    (hlo_nonpos : d lo ≤ 0)
    (hhi_pos : 0 < d hi) :
    ∃ x : ℝ, lo ≤ x ∧ x < hi ∧ d x ≤ 0 ∧
      ∀ y : ℝ, x < y → y ≤ hi → 0 < d y := by
  let S : Set ℝ := {x | x ∈ Icc lo hi ∧ d x ≤ 0}
  have hS_closed : IsClosed S := by
    dsimp [S]
    exact isClosed_Icc.isClosed_le hd continuousOn_const
  have hS_compact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hS_closed (by
      intro x hx
      exact hx.1)
  have hS_nonempty : S.Nonempty :=
    ⟨lo, ⟨⟨le_rfl, le_of_lt hlohi⟩, hlo_nonpos⟩⟩
  rcases hS_compact.exists_isMaxOn hS_nonempty continuousOn_id with
    ⟨x, hxS, hxmax⟩
  have hxlo : lo ≤ x := hxS.1.1
  have hxhi_le : x ≤ hi := hxS.1.2
  have hdx_nonpos : d x ≤ 0 := hxS.2
  have hx_ne_hi : x ≠ hi := by
    intro h
    subst x
    linarith
  have hxhi : x < hi := lt_of_le_of_ne hxhi_le hx_ne_hi
  refine ⟨x, hxlo, hxhi, hdx_nonpos, ?_⟩
  intro y hxy hyhi
  have hloy : lo ≤ y := le_trans hxlo (le_of_lt hxy)
  by_contra hy_not_pos
  have hyd_nonpos : d y ≤ 0 := le_of_not_gt hy_not_pos
  have hyS : y ∈ S := ⟨⟨hloy, hyhi⟩, hyd_nonpos⟩
  have hy_le_x : y ≤ x := (isMaxOn_iff.mp hxmax) y hyS
  linarith

end DecisionCore
