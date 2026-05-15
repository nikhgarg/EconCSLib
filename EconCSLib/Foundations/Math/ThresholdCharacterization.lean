import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# Threshold Characterizations

Reusable one-dimensional cutoff lemmas for papers that turn monotone scalar
comparisons into threshold statements.

## Main declarations

- `exists_threshold_of_continuous_strictMonoOn_Icc_crossing`
-/

namespace EconCSLib

noncomputable section

open Set

/--
If a scalar function is continuous and strictly increasing on `[0, 1]`, and a
level lies strictly between the endpoint values, then there is an interior
threshold where the function equals the level.  On `[0, 1]`, strict comparison
to the level is equivalent to being below or above that threshold.
-/
theorem exists_threshold_of_continuous_strictMonoOn_Icc_crossing
    {f : ℝ → ℝ} {level : ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_mono : StrictMonoOn f (Icc 0 1))
    (hleft : f 0 < level) (hright : level < f 1) :
    ∃ threshold : ℝ, threshold ∈ Ioo 0 1 ∧ f threshold = level ∧
      (∀ x ∈ Icc 0 1, f x < level ↔ x < threshold) ∧
      (∀ x ∈ Icc 0 1, level < f x ↔ threshold < x) ∧
      (∀ x ∈ Icc 0 1, f x ≤ level ↔ x ≤ threshold) ∧
      (∀ x ∈ Icc 0 1, level ≤ f x ↔ threshold ≤ x) := by
  have hzero_mem : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hone_mem : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hlevel_mem : level ∈ Icc (f 0) (f 1) := ⟨hleft.le, hright.le⟩
  rcases intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf_cont hlevel_mem with
    ⟨threshold, hthreshold_mem, hthreshold_eq⟩
  have hthreshold_pos : 0 < threshold := by
    have hne : threshold ≠ 0 := by
      intro h
      subst threshold
      linarith
    exact lt_of_le_of_ne hthreshold_mem.1 (Ne.symm hne)
  have hthreshold_lt_one : threshold < 1 := by
    have hne : threshold ≠ 1 := by
      intro h
      subst threshold
      linarith
    exact lt_of_le_of_ne hthreshold_mem.2 hne
  refine ⟨threshold, ⟨hthreshold_pos, hthreshold_lt_one⟩, hthreshold_eq, ?_, ?_, ?_, ?_⟩
  · intro x hx
    constructor
    · intro hxlevel
      by_contra hnot
      have htx : threshold ≤ x := le_of_not_gt hnot
      have hx_eq : x = threshold := by
        by_contra hx_ne
        have htx_strict : threshold < x := lt_of_le_of_ne htx (Ne.symm hx_ne)
        have hfx_gt : f threshold < f x :=
          hf_mono hthreshold_mem hx htx_strict
        linarith
      subst x
      linarith
    · intro hxlt
      have hfx : f x < f threshold :=
        hf_mono hx hthreshold_mem hxlt
      linarith
  · intro x hx
    constructor
    · intro hxlevel
      by_contra hnot
      have hxt : x ≤ threshold := le_of_not_gt hnot
      have hx_eq : x = threshold := by
        by_contra hx_ne
        have hxt_strict : x < threshold := lt_of_le_of_ne hxt hx_ne
        have hfx_lt : f x < f threshold :=
          hf_mono hx hthreshold_mem hxt_strict
        linarith
      subst x
      linarith
    · intro htx
      have hfx : f threshold < f x :=
        hf_mono hthreshold_mem hx htx
      linarith
  · intro x hx
    constructor
    · intro hxlevel
      by_contra hnot
      have htx : threshold < x := lt_of_not_ge hnot
      have hfx : f threshold < f x :=
        hf_mono hthreshold_mem hx htx
      linarith
    · intro hxt
      by_cases hx_eq : x = threshold
      · subst x
        linarith
      · have hxt_strict : x < threshold := lt_of_le_of_ne hxt hx_eq
        have hfx : f x < f threshold :=
          hf_mono hx hthreshold_mem hxt_strict
        linarith
  · intro x hx
    constructor
    · intro hxlevel
      by_contra hnot
      have hxt : x < threshold := lt_of_not_ge hnot
      have hfx : f x < f threshold :=
        hf_mono hx hthreshold_mem hxt
      linarith
    · intro htx
      by_cases hx_eq : x = threshold
      · subst x
        linarith
      · have htx_strict : threshold < x := lt_of_le_of_ne htx (Ne.symm hx_eq)
        have hfx : f threshold < f x :=
          hf_mono hthreshold_mem hx htx_strict
        linarith

end

end EconCSLib
