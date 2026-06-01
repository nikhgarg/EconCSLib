import KR21Monoculture.FirstChoiceDecomposition
import KR21Monoculture.Kendall
import EconCSLib.Foundations.Math.FiniteSigns

open scoped BigOperators
open EconCSLib

namespace KR21Monoculture

/-- A strict reference ordering implies the corresponding weak reference ordering. -/
theorem weaklyOrderedBy_of_strictlyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (h : StrictlyOrderedBy ρ value) :
    WeaklyOrderedBy ρ value := by
  intro a b hab
  exact le_of_lt (h hab)

/--
Any candidate different from the reference top candidate is ranked strictly below it
in the reference ranking.
-/
theorem rankOf_firstChoice_lt_rankOf_of_ne {n : ℕ}
    (ρ : Ranking n) {c : Candidate n} (hc : c ≠ firstChoice ρ) :
    rankOf ρ (firstChoice ρ) < rankOf ρ c := by
  have hneq : rankOf ρ c ≠ 0 := by
    intro h0
    have hc' : c = firstChoice ρ := by
      simpa [rankOf, firstChoice] using congrArg ρ h0
    exact hc hc'
  have hpos : (0 : Candidate n) < rankOf ρ c := by
    exact Fin.pos_iff_ne_zero.mpr hneq
  simpa [rankOf, firstChoice] using hpos

/--
If a ranking shares the reference top candidate, then weak monotonicity along the
reference ranking makes its top-vs-runner-up value gap nonnegative.
-/
theorem valueGap_nonneg_on_firstFiber_of_weaklyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ} {π : Ranking n}
    (hvalue : WeaklyOrderedBy ρ value)
    (hfirst : firstChoice ρ = firstChoice π) :
    0 ≤ valueGap value π := by
  have hneq : secondChoice π ≠ firstChoice ρ := by
    intro h
    have h' : secondChoice π = firstChoice π := by
      calc
        secondChoice π = firstChoice ρ := h
        _ = firstChoice π := hfirst
    exact firstChoice_ne_secondChoice π h'.symm
  have hlt : rankOf ρ (firstChoice ρ) < rankOf ρ (secondChoice π) := by
    exact rankOf_firstChoice_lt_rankOf_of_ne (ρ := ρ) hneq
  have hle : value (secondChoice π) ≤ value (firstChoice ρ) := hvalue hlt
  have hsub : 0 ≤ value (firstChoice ρ) - value (secondChoice π) := by
    exact sub_nonneg.mpr hle
  have hfirst_raw : π 0 = ρ 0 := by
    simpa [firstChoice] using hfirst.symm
  simpa [valueGap, firstChoice, secondChoice, hfirst_raw] using hsub

/--
If a ranking shares the reference top candidate, then strict monotonicity along the
reference ranking makes its top-vs-runner-up value gap strictly positive.
-/
theorem valueGap_pos_on_firstFiber_of_strictlyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ} {π : Ranking n}
    (hvalue : StrictlyOrderedBy ρ value)
    (hfirst : firstChoice ρ = firstChoice π) :
    0 < valueGap value π := by
  have hneq : secondChoice π ≠ firstChoice ρ := by
    intro h
    have h' : secondChoice π = firstChoice π := by
      calc
        secondChoice π = firstChoice ρ := h
        _ = firstChoice π := hfirst
    exact firstChoice_ne_secondChoice π h'.symm
  have hlt : rankOf ρ (firstChoice ρ) < rankOf ρ (secondChoice π) := by
    exact rankOf_firstChoice_lt_rankOf_of_ne (ρ := ρ) hneq
  have hltv : value (secondChoice π) < value (firstChoice ρ) := hvalue hlt
  have hsub : 0 < value (firstChoice ρ) - value (secondChoice π) := by
    exact sub_pos.mpr hltv
  have hfirst_raw : π 0 = ρ 0 := by
    simpa [firstChoice] using hfirst.symm
  simpa [valueGap, firstChoice, secondChoice, hfirst_raw] using hsub

/--
Under a weak reference ordering, the gap mass of the reference top candidate is
nonnegative for every ranking law.
-/
theorem firstChoiceGapMass_nonneg_of_referenceTop_weaklyOrdered {n : ℕ}
    (μ : PMF (Ranking n)) (ρ : Ranking n) (value : Candidate n → ℝ)
    (hvalue : WeaklyOrderedBy ρ value) :
    0 ≤ firstChoiceGapMass μ value (firstChoice ρ) := by
  apply firstChoiceGapMass_nonneg_of_gap_nonneg_onFiber
  intro π hπ
  exact valueGap_nonneg_on_firstFiber_of_weaklyOrderedBy
    (ρ := ρ) (value := value) (π := π) hvalue hπ

/--
If the reference ranking has positive mass and values strictly decrease down the
reference ranking, then the gap mass attached to the reference top candidate is
strictly positive.
-/
theorem firstChoiceGapMass_pos_of_reference_mass_pos_and_strictlyOrderedBy {n : ℕ}
    (μ : PMF (Ranking n)) (ρ : Ranking n) (value : Candidate n → ℝ)
    (hmass : 0 < (μ ρ).toReal)
    (hvalue : StrictlyOrderedBy ρ value) :
    0 < firstChoiceGapMass μ value (firstChoice ρ) := by
  classical
  have hsum :
      0 < ∑ π : Ranking n,
        (μ π).toReal *
          (if firstChoice ρ = firstChoice π then valueGap value π else 0) := by
    apply EconCSLib.sum_univ_pos_of_pos_of_nonneg
      (f := fun π : Ranking n =>
        (μ π).toReal *
          (if firstChoice ρ = firstChoice π then valueGap value π else 0))
      (a₀ := ρ)
    · have hgap : 0 < valueGap value ρ :=
        center_valueGap_pos_of_strictlyOrderedBy hvalue
      simpa using mul_pos hmass hgap
    · intro π
      refine mul_nonneg ENNReal.toReal_nonneg ?_
      by_cases hπ : firstChoice ρ = firstChoice π
      · have hgap := valueGap_nonneg_on_firstFiber_of_weaklyOrderedBy
          (ρ := ρ) (value := value) (π := π)
          (weaklyOrderedBy_of_strictlyOrderedBy hvalue) hπ
        have hraw : ρ 0 = π 0 := by simpa [firstChoice] using hπ
        simp [hraw, hgap]
      · have hraw : ρ 0 ≠ π 0 := by simpa [firstChoice] using hπ
        simp [hraw]
  simpa [firstChoiceGapMass, pmfExp] using hsum

/-- Miss probability is positive exactly when first-choice probability is below one. -/
theorem firstChoiceMissProb_pos_iff_firstChoiceProb_lt_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 < firstChoiceMissProb μ c ↔ firstChoiceProb μ c < 1 := by
  unfold firstChoiceMissProb
  constructor <;> intro h <;>
    linarith [firstChoiceProb_nonneg (μ := μ) (c := c),
      firstChoiceProb_le_one (μ := μ) (c := c)]

/-- Miss probability is nonnegative exactly when first-choice probability is at most one. -/
theorem firstChoiceMissProb_nonneg_iff_firstChoiceProb_le_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceMissProb μ c ↔ firstChoiceProb μ c ≤ 1 := by
  unfold firstChoiceMissProb
  constructor <;> intro h <;> linarith

/-- Collision difference is positive exactly when the better law puts more top mass on `c`. -/
theorem firstChoiceCollisionDiff_pos_iff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (c : Candidate n) :
    0 < firstChoiceCollisionDiff μBetter μWorse c ↔
      firstChoiceProb μWorse c < firstChoiceProb μBetter c := by
  unfold firstChoiceCollisionDiff
  constructor <;> intro h <;> linarith

/--
Collision difference is nonnegative exactly when the better law puts at least as
much top mass on `c`.
-/
theorem firstChoiceCollisionDiff_nonneg_iff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceCollisionDiff μBetter μWorse c ↔
      firstChoiceProb μWorse c ≤ firstChoiceProb μBetter c := by
  unfold firstChoiceCollisionDiff
  constructor <;> intro h <;> linarith

end KR21Monoculture
