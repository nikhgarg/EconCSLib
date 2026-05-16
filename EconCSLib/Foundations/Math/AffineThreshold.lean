import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Affine Thresholds

Reusable one-dimensional threshold algebra for positive-slope affine scores.

## Main declarations

- `affineCutoff`
- `threshold_le_affine_iff_cutoff_le`
- `affine_le_threshold_iff_le_cutoff`
- `affine_strictMono`
- `exists_affine_lt`
- `exists_lt_affine`
- `exists_affine_lt_before`
- `exists_lt_affine_after`
-/

namespace EconCSLib

noncomputable section

/-- Cutoff in the input variable for a positive-slope affine score. -/
def affineCutoff (intercept slope threshold : ℝ) : ℝ :=
  (threshold - intercept) / slope

/--
A positive-slope affine score exceeds a threshold exactly above the induced
cutoff.
-/
theorem threshold_le_affine_iff_cutoff_le
    {intercept slope threshold x : ℝ} (hslope : 0 < slope) :
    threshold ≤ intercept + slope * x ↔
      affineCutoff intercept slope threshold ≤ x := by
  unfold affineCutoff
  constructor
  · intro h
    have hsub : threshold - intercept ≤ slope * x := by
      linarith
    rw [div_le_iff₀ hslope]
    simpa [mul_comm] using hsub
  · intro h
    have hmul : threshold - intercept ≤ slope * x := by
      have := (div_le_iff₀ hslope).mp h
      simpa [mul_comm] using this
    linarith

/--
A positive-slope affine score is below a threshold exactly below the induced
cutoff.
-/
theorem affine_le_threshold_iff_le_cutoff
    {intercept slope threshold x : ℝ} (hslope : 0 < slope) :
    intercept + slope * x ≤ threshold ↔
      x ≤ affineCutoff intercept slope threshold := by
  unfold affineCutoff
  constructor
  · intro h
    have hsub : slope * x ≤ threshold - intercept := by
      linarith
    rw [le_div_iff₀ hslope]
    simpa [mul_comm] using hsub
  · intro h
    have hmul : slope * x ≤ threshold - intercept := by
      have := (le_div_iff₀ hslope).mp h
      simpa [mul_comm] using this
    linarith

/-- A positive-slope affine score is strictly increasing. -/
theorem affine_strictMono (intercept : ℝ) {slope : ℝ}
    (hslope : 0 < slope) :
    StrictMono (fun x : ℝ => intercept + slope * x) := by
  intro x y hxy
  simpa [add_comm, add_left_comm, add_assoc] using
    add_lt_add_left (mul_lt_mul_of_pos_left hxy hslope) intercept

/-- A positive-slope affine score eventually falls below any finite level. -/
theorem exists_affine_lt (intercept threshold : ℝ) {slope : ℝ}
    (hslope : 0 < slope) :
    ∃ x : ℝ, intercept + slope * x < threshold := by
  let cutoff : ℝ := affineCutoff intercept slope threshold
  refine ⟨cutoff - 1, ?_⟩
  have hnot_cutoff : ¬ cutoff ≤ cutoff - 1 := by
    linarith
  have hnot_threshold :
      ¬ threshold ≤ intercept + slope * (cutoff - 1) := by
    intro h
    exact hnot_cutoff
      ((threshold_le_affine_iff_cutoff_le (intercept := intercept)
        (slope := slope) (threshold := threshold) (x := cutoff - 1)
        hslope).1 h)
  exact lt_of_not_ge hnot_threshold

/-- A positive-slope affine score eventually exceeds any finite level. -/
theorem exists_lt_affine (intercept threshold : ℝ) {slope : ℝ}
    (hslope : 0 < slope) :
    ∃ x : ℝ, threshold < intercept + slope * x := by
  let cutoff : ℝ := affineCutoff intercept slope threshold
  refine ⟨cutoff + 1, ?_⟩
  have hnot_cutoff : ¬ cutoff + 1 ≤ cutoff := by
    linarith
  have hnot_affine :
      ¬ intercept + slope * (cutoff + 1) ≤ threshold := by
    intro h
    exact hnot_cutoff
      ((affine_le_threshold_iff_le_cutoff (intercept := intercept)
        (slope := slope) (threshold := threshold) (x := cutoff + 1)
        hslope).1 h)
  exact lt_of_not_ge hnot_affine

/-- A positive-slope affine score falls below any finite level before any finite bound. -/
theorem exists_affine_lt_before (upper intercept threshold : ℝ) {slope : ℝ}
    (hslope : 0 < slope) :
    ∃ x : ℝ, x < upper ∧ intercept + slope * x < threshold := by
  let cutoff : ℝ := affineCutoff intercept slope threshold
  let x : ℝ := min upper cutoff - 1
  have hx_upper : x < upper := by
    dsimp [x]
    exact (sub_lt_self _ zero_lt_one).trans_le (min_le_left _ _)
  have hx_cutoff : x < cutoff := by
    dsimp [x]
    exact (sub_lt_self _ zero_lt_one).trans_le (min_le_right _ _)
  have hnot_threshold :
      ¬ threshold ≤ intercept + slope * x := by
    intro h
    have hcutoff_le_x :
        affineCutoff intercept slope threshold ≤ x :=
      (threshold_le_affine_iff_cutoff_le (intercept := intercept)
        (slope := slope) (threshold := threshold) (x := x) hslope).1 h
    linarith
  exact ⟨x, hx_upper, lt_of_not_ge hnot_threshold⟩

/-- A positive-slope affine score exceeds any finite level after any finite bound. -/
theorem exists_lt_affine_after (lower intercept threshold : ℝ) {slope : ℝ}
    (hslope : 0 < slope) :
    ∃ x : ℝ, lower < x ∧ threshold < intercept + slope * x := by
  let cutoff : ℝ := affineCutoff intercept slope threshold
  let x : ℝ := max lower cutoff + 1
  have hlower_x : lower < x := by
    dsimp [x]
    exact (le_max_left _ _).trans_lt (lt_add_one _)
  have hcutoff_x : cutoff < x := by
    dsimp [x]
    exact (le_max_right _ _).trans_lt (lt_add_one _)
  have hnot_affine :
      ¬ intercept + slope * x ≤ threshold := by
    intro h
    have hx_le_cutoff :
        x ≤ affineCutoff intercept slope threshold :=
      (affine_le_threshold_iff_le_cutoff (intercept := intercept)
        (slope := slope) (threshold := threshold) (x := x) hslope).1 h
    linarith
  exact ⟨x, hlower_x, lt_of_not_ge hnot_affine⟩

end

end EconCSLib
