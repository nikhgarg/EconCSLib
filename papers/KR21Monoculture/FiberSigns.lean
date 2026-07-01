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
  simpa [rankOf, firstChoice, EconCSLib.SocialChoice.Ranking.rankOf,
    EconCSLib.SocialChoice.Ranking.firstChoice] using
    EconCSLib.SocialChoice.Ranking.rankOf_firstChoice_lt_rankOf_of_ne ρ
      (by
        intro h
        exact hc (by simpa [firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice] using h))

/--
If a ranking shares the reference top candidate, then weak monotonicity along the
reference ranking makes its top-vs-runner-up value gap nonnegative.
-/
theorem valueGap_nonneg_on_firstFiber_of_weaklyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ} {π : Ranking n}
    (hvalue : WeaklyOrderedBy ρ value)
    (hfirst : firstChoice ρ = firstChoice π) :
    0 ≤ valueGap value π := by
  have hvalue' :
      EconCSLib.SocialChoice.Ranking.WeaklyOrderedBy ρ value := by
    intro a b hab
    exact hvalue (by
      simpa [rankOf, EconCSLib.SocialChoice.Ranking.rankOf] using hab)
  have hfirst' :
      EconCSLib.SocialChoice.Ranking.firstChoice ρ =
        EconCSLib.SocialChoice.Ranking.firstChoice π := by
    simpa [firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice] using hfirst
  simpa [valueGap, EconCSLib.SocialChoice.Ranking.valueGap, firstChoice, secondChoice,
    EconCSLib.SocialChoice.Ranking.firstChoice, EconCSLib.SocialChoice.Ranking.secondChoice]
    using EconCSLib.SocialChoice.Ranking.valueGap_nonneg_on_firstFiber_of_weaklyOrderedBy
      (ρ := ρ) (value := value) (π := π) hvalue' hfirst'

/--
If a ranking shares the reference top candidate, then strict monotonicity along the
reference ranking makes its top-vs-runner-up value gap strictly positive.
-/
theorem valueGap_pos_on_firstFiber_of_strictlyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ} {π : Ranking n}
    (hvalue : StrictlyOrderedBy ρ value)
    (hfirst : firstChoice ρ = firstChoice π) :
    0 < valueGap value π := by
  have hvalue' :
      EconCSLib.SocialChoice.Ranking.StrictlyOrderedBy ρ value := by
    intro a b hab
    exact hvalue (by
      simpa [rankOf, EconCSLib.SocialChoice.Ranking.rankOf] using hab)
  have hfirst' :
      EconCSLib.SocialChoice.Ranking.firstChoice ρ =
        EconCSLib.SocialChoice.Ranking.firstChoice π := by
    simpa [firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice] using hfirst
  simpa [valueGap, EconCSLib.SocialChoice.Ranking.valueGap, firstChoice, secondChoice,
    EconCSLib.SocialChoice.Ranking.firstChoice, EconCSLib.SocialChoice.Ranking.secondChoice]
    using EconCSLib.SocialChoice.Ranking.valueGap_pos_on_firstFiber_of_strictlyOrderedBy
      (ρ := ρ) (value := value) (π := π) hvalue' hfirst'

/--
Under a weak reference ordering, the gap mass of the reference top candidate is
nonnegative for every ranking law.
-/
theorem firstChoiceGapMass_nonneg_of_referenceTop_weaklyOrdered {n : ℕ}
    (μ : PMF (Ranking n)) (ρ : Ranking n) (value : Candidate n → ℝ)
    (hvalue : WeaklyOrderedBy ρ value) :
    0 ≤ firstChoiceGapMass μ value (firstChoice ρ) := by
  have hvalue' :
      EconCSLib.SocialChoice.Ranking.WeaklyOrderedBy ρ value := by
    intro a b hab
    exact hvalue (by
      simpa [rankOf, EconCSLib.SocialChoice.Ranking.rankOf] using hab)
  simpa [firstChoiceGapMass, EconCSLib.SocialChoice.Ranking.firstChoiceGapMass,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice] using
    EconCSLib.SocialChoice.Ranking.firstChoiceGapMass_nonneg_of_referenceTop_weaklyOrdered
      μ ρ value hvalue'

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
  have hvalue' :
      EconCSLib.SocialChoice.Ranking.StrictlyOrderedBy ρ value := by
    intro a b hab
    exact hvalue (by
      simpa [rankOf, EconCSLib.SocialChoice.Ranking.rankOf] using hab)
  simpa [firstChoiceGapMass, EconCSLib.SocialChoice.Ranking.firstChoiceGapMass,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice] using
    EconCSLib.SocialChoice.Ranking.firstChoiceGapMass_pos_of_reference_mass_pos_and_strictlyOrderedBy
      μ ρ value hmass hvalue'

/-- Miss probability is positive exactly when first-choice probability is below one. -/
theorem firstChoiceMissProb_pos_iff_firstChoiceProb_lt_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 < firstChoiceMissProb μ c ↔ firstChoiceProb μ c < 1 := by
  simpa [firstChoiceMissProb, EconCSLib.SocialChoice.Ranking.firstChoiceMissProb,
    firstChoiceProb, EconCSLib.SocialChoice.Ranking.firstChoiceProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_pos_iff_firstChoiceProb_lt_one
      μ c

/-- Miss probability is nonnegative exactly when first-choice probability is at most one. -/
theorem firstChoiceMissProb_nonneg_iff_firstChoiceProb_le_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceMissProb μ c ↔ firstChoiceProb μ c ≤ 1 := by
  simpa [firstChoiceMissProb, EconCSLib.SocialChoice.Ranking.firstChoiceMissProb,
    firstChoiceProb, EconCSLib.SocialChoice.Ranking.firstChoiceProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_nonneg_iff_firstChoiceProb_le_one
      μ c

/-- Collision difference is positive exactly when the better law puts more top mass on `c`. -/
theorem firstChoiceCollisionDiff_pos_iff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (c : Candidate n) :
    0 < firstChoiceCollisionDiff μBetter μWorse c ↔
      firstChoiceProb μWorse c < firstChoiceProb μBetter c := by
  simpa [firstChoiceCollisionDiff, EconCSLib.SocialChoice.Ranking.firstChoiceCollisionDiff,
    firstChoiceProb, EconCSLib.SocialChoice.Ranking.firstChoiceProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceCollisionDiff_pos_iff
      μBetter μWorse c

/--
Collision difference is nonnegative exactly when the better law puts at least as
much top mass on `c`.
-/
theorem firstChoiceCollisionDiff_nonneg_iff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceCollisionDiff μBetter μWorse c ↔
      firstChoiceProb μWorse c ≤ firstChoiceProb μBetter c := by
  simpa [firstChoiceCollisionDiff, EconCSLib.SocialChoice.Ranking.firstChoiceCollisionDiff,
    firstChoiceProb, EconCSLib.SocialChoice.Ranking.firstChoiceProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceCollisionDiff_nonneg_iff
      μBetter μWorse c

end KR21Monoculture
