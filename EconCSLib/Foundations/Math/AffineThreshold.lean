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

end

end EconCSLib
