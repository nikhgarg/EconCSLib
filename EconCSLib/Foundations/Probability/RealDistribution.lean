import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Tactic

open MeasureTheory Set

namespace EconCSLib
namespace Probability

noncomputable section

/-!
# Real Distribution Tail Helpers

Thin wrappers around Mathlib's real CDF API.  These names are meant for
paper-facing threshold, tail, and order-statistic arguments where the proof
needs real-valued lower-CDF and upper-tail probabilities.

## Main declarations

- `lowerCDFMass`
- `upperTailMass`
- `lowerCDFMass_mono`
- `upperTailMass_antitone`
- `lowerCDFMass_eq_cdf`
- `upperTailMass_eq_one_sub_cdf`
- `UpperTailThresholdCertificate`
-/

/-- Real-valued lower CDF mass, `P[X <= x]`. -/
def lowerCDFMass (μ : Measure ℝ) (x : ℝ) : ℝ :=
  μ.real (Iic x)

/-- Real-valued upper-tail mass, `P[X > x]`. -/
def upperTailMass (μ : Measure ℝ) (x : ℝ) : ℝ :=
  μ.real (Ioi x)

theorem lowerCDFMass_nonneg (μ : Measure ℝ) (x : ℝ) :
    0 ≤ lowerCDFMass μ x := by
  simp [lowerCDFMass]

theorem upperTailMass_nonneg (μ : Measure ℝ) (x : ℝ) :
    0 ≤ upperTailMass μ x := by
  simp [upperTailMass]

theorem lowerCDFMass_mono (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Monotone (lowerCDFMass μ) := by
  intro x y hxy
  exact measureReal_mono
    (μ := μ) (fun z hz => le_trans hz hxy) (measure_ne_top μ _)

theorem upperTailMass_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Antitone (upperTailMass μ) := by
  intro x y hxy
  exact measureReal_mono
    (μ := μ) (fun z hz => lt_of_le_of_lt hxy hz) (measure_ne_top μ _)

theorem lowerCDFMass_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) :
    lowerCDFMass μ x ≤ 1 := by
  have hle :
      μ.real (Iic x) ≤ μ.real (univ : Set ℝ) :=
    measureReal_mono (μ := μ) (subset_univ _) (measure_ne_top μ _)
  simpa [lowerCDFMass, probReal_univ] using hle

theorem upperTailMass_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) :
    upperTailMass μ x ≤ 1 := by
  have hle :
      μ.real (Ioi x) ≤ μ.real (univ : Set ℝ) :=
    measureReal_mono (μ := μ) (subset_univ _) (measure_ne_top μ _)
  simpa [upperTailMass, probReal_univ] using hle

theorem lowerCDFMass_eq_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) :
    lowerCDFMass μ x = ProbabilityTheory.cdf μ x := by
  simpa [lowerCDFMass] using (ProbabilityTheory.cdf_eq_real μ x).symm

theorem upperTailMass_eq_one_sub_cdf
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    upperTailMass μ x = 1 - ProbabilityTheory.cdf μ x := by
  have hcompl :=
    probReal_compl_eq_one_sub (μ := μ) (s := Iic x) measurableSet_Iic
  simpa [upperTailMass, ProbabilityTheory.cdf_eq_real μ x, compl_Iic] using hcompl

theorem lowerCDFMass_add_upperTailMass_eq_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    lowerCDFMass μ x + upperTailMass μ x = 1 := by
  rw [lowerCDFMass_eq_cdf, upperTailMass_eq_one_sub_cdf]
  ring

/--
Certificate that a real threshold realizes a target upper-tail mass/capacity.
-/
structure UpperTailThresholdCertificate
    (μ : Measure ℝ) (capacity threshold : ℝ) : Prop where
  tail_eq_capacity : upperTailMass μ threshold = capacity

namespace UpperTailThresholdCertificate

variable {μ : Measure ℝ} {capacity threshold : ℝ}

theorem capacity_nonneg
    (C : UpperTailThresholdCertificate μ capacity threshold) :
    0 ≤ capacity := by
  rw [← C.tail_eq_capacity]
  exact upperTailMass_nonneg μ threshold

theorem capacity_le_one [IsProbabilityMeasure μ]
    (C : UpperTailThresholdCertificate μ capacity threshold) :
    capacity ≤ 1 := by
  rw [← C.tail_eq_capacity]
  exact upperTailMass_le_one μ threshold

theorem lowerCDFMass_eq_one_sub_capacity [IsProbabilityMeasure μ]
    (C : UpperTailThresholdCertificate μ capacity threshold) :
    lowerCDFMass μ threshold = 1 - capacity := by
  have hsum := lowerCDFMass_add_upperTailMass_eq_one μ threshold
  rw [C.tail_eq_capacity] at hsum
  linarith

theorem capacity_antitone_threshold [IsFiniteMeasure μ]
    {capacity₁ capacity₂ threshold₁ threshold₂ : ℝ}
    (C₁ : UpperTailThresholdCertificate μ capacity₁ threshold₁)
    (C₂ : UpperTailThresholdCertificate μ capacity₂ threshold₂)
    (hthreshold : threshold₁ ≤ threshold₂) :
    capacity₂ ≤ capacity₁ := by
  rw [← C₁.tail_eq_capacity, ← C₂.tail_eq_capacity]
  exact upperTailMass_antitone μ hthreshold

end UpperTailThresholdCertificate

end

end Probability
end EconCSLib
