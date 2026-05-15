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
- `exists_threshold_of_continuous_strictMonoOn_Icc`
- `exists_threshold_le_of_continuous_strictMonoOn_Icc`
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

/--
If a scalar function is continuous and strictly increasing on `[0, 1]`, then
for any level there is a real threshold whose lower set on `[0, 1]` is exactly
`{x | f x < level}`.  The threshold may lie outside `[0, 1]` when the level is
outside the endpoint range.
-/
theorem exists_threshold_of_continuous_strictMonoOn_Icc
    {f : ℝ → ℝ} {level : ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_mono : StrictMonoOn f (Icc 0 1)) :
    ∃ threshold : ℝ,
      ∀ x ∈ Icc 0 1, f x < level ↔ x < threshold := by
  have hzero_mem : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hone_mem : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  by_cases hleft : f 0 < level
  · by_cases hright : level < f 1
    · rcases exists_threshold_of_continuous_strictMonoOn_Icc_crossing
        hf_cont hf_mono hleft hright with
        ⟨threshold, _hthreshold, _hroot, hlt, _hgt, _hle, _hge⟩
      exact ⟨threshold, hlt⟩
    · have hf1_le : f 1 ≤ level := le_of_not_gt hright
      by_cases hf1_lt : f 1 < level
      · refine ⟨2, ?_⟩
        intro x hx
        constructor
        · intro _hfx
          linarith [hx.2]
        · intro _hx
          by_cases hx_one : x = 1
          · simpa [hx_one] using hf1_lt
          · have hx_lt_one : x < 1 := lt_of_le_of_ne hx.2 hx_one
            have hfx_lt_one : f x < f 1 :=
              hf_mono hx hone_mem hx_lt_one
            exact lt_trans hfx_lt_one hf1_lt
      · have hf1_eq : f 1 = level :=
          le_antisymm hf1_le (le_of_not_gt hf1_lt)
        refine ⟨1, ?_⟩
        intro x hx
        constructor
        · intro hfx
          by_contra hnot
          have hle : 1 ≤ x := le_of_not_gt hnot
          have hx_eq : x = 1 := le_antisymm hx.2 hle
          subst x
          linarith
        · intro hx_lt_one
          have hfx_lt_one : f x < f 1 :=
            hf_mono hx hone_mem hx_lt_one
          simpa [hf1_eq] using hfx_lt_one
  · have hlevel_le_f0 : level ≤ f 0 := le_of_not_gt hleft
    refine ⟨0, ?_⟩
    intro x hx
    constructor
    · intro hfx
      by_cases hx_zero : x = 0
      · subst x
        linarith
      · have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx_zero)
        have hf0_lt_fx : f 0 < f x :=
          hf_mono hzero_mem hx hx_pos
        linarith
    · intro hx_lt_zero
      linarith [hx.1]

/--
If a scalar function is continuous and strictly increasing on `[0, 1]`, then
for any level there is a real threshold whose weak lower set on `[0, 1]` is
exactly `{x | f x ≤ level}`.  The threshold may lie outside `[0, 1]` when the
level is outside the endpoint range.
-/
theorem exists_threshold_le_of_continuous_strictMonoOn_Icc
    {f : ℝ → ℝ} {level : ℝ}
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_mono : StrictMonoOn f (Icc 0 1)) :
    ∃ threshold : ℝ,
      ∀ x ∈ Icc 0 1, f x ≤ level ↔ x ≤ threshold := by
  have hzero_mem : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hone_mem : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  by_cases hlevel_lt_f0 : level < f 0
  · refine ⟨-1, ?_⟩
    intro x hx
    constructor
    · intro hfx
      by_cases hx_zero : x = 0
      · subst x
        linarith
      · have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx_zero)
        have hf0_lt_fx : f 0 < f x :=
          hf_mono hzero_mem hx hx_pos
        linarith
    · intro hx_le
      linarith [hx.1, hx_le]
  · have hf0_le_level : f 0 ≤ level := le_of_not_gt hlevel_lt_f0
    by_cases hf1_le_level : f 1 ≤ level
    · refine ⟨1, ?_⟩
      intro x hx
      constructor
      · intro _hfx
        exact hx.2
      · intro _hx
        by_cases hx_one : x = 1
        · simpa [hx_one] using hf1_le_level
        · have hx_lt_one : x < 1 := lt_of_le_of_ne hx.2 hx_one
          have hfx_lt_one : f x < f 1 :=
            hf_mono hx hone_mem hx_lt_one
          exact (lt_of_lt_of_le hfx_lt_one hf1_le_level).le
    · have hlevel_lt_f1 : level < f 1 := lt_of_not_ge hf1_le_level
      by_cases hf0_lt_level : f 0 < level
      · rcases exists_threshold_of_continuous_strictMonoOn_Icc_crossing
          hf_cont hf_mono hf0_lt_level hlevel_lt_f1 with
          ⟨threshold, _hthreshold, _hroot, _hlt, _hgt, hle, _hge⟩
        exact ⟨threshold, hle⟩
      · have hf0_eq : f 0 = level :=
          le_antisymm hf0_le_level (le_of_not_gt hf0_lt_level)
        refine ⟨0, ?_⟩
        intro x hx
        constructor
        · intro hfx
          by_contra hnot
          have hx_pos : 0 < x := lt_of_not_ge hnot
          have hf0_lt_fx : f 0 < f x :=
            hf_mono hzero_mem hx hx_pos
          linarith
        · intro hx_le_zero
          have hx_eq : x = 0 := le_antisymm hx_le_zero hx.1
          subst x
          linarith

end

end EconCSLib
