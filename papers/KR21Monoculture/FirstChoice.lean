import KR21Monoculture.WelfareDecomposition
import EconCSLib.Foundations.Math.FiniteSigns
import EconCSLib.Foundations.Probability.Conditional
import EconCSLib.SocialChoice.Ranking.Payoff
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open scoped BigOperators
open EconCSLib

namespace KR21Monoculture

/--
The real-valued probability that a draw from `μ` puts candidate `c` first.
-/
noncomputable def firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  EconCSLib.SocialChoice.Ranking.firstChoiceProb μ c

/-- The probability that a draw from `μ` does not put candidate `c` first. -/
noncomputable def firstChoiceMissProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  EconCSLib.SocialChoice.Ranking.firstChoiceMissProb μ c

/--
The loss from being forced down from a ranking's first candidate to its second
candidate.
-/
def valueGap {n : ℕ} (value : Candidate n → ℝ) (π : Ranking n) : ℝ :=
  EconCSLib.SocialChoice.Ranking.valueGap value π

export EconCSLib.SocialChoice.Ranking
  (secondMoverAgainst)

@[simp] theorem firstChoiceProb_pure {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    firstChoiceProb (PMF.pure π) c = if c = firstChoice π then 1 else 0 := by
  simpa [firstChoiceProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceProb_pure π c

@[simp] theorem firstChoiceProb_pure_firstChoice {n : ℕ}
    (π : Ranking n) :
    firstChoiceProb (PMF.pure π) (firstChoice π) = 1 := by
  simpa [firstChoiceProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceProb_pure_firstChoice π

@[simp] theorem firstChoiceMissProb_pure_firstChoice {n : ℕ}
    (π : Ranking n) :
    firstChoiceMissProb (PMF.pure π) (firstChoice π) = 0 := by
  simpa [firstChoiceMissProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_pure_firstChoice π

theorem firstChoiceProb_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceProb μ c := by
  simpa [firstChoiceProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceProb_nonneg μ c

theorem firstChoiceProb_le_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceProb μ c ≤ 1 := by
  simpa [firstChoiceProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceProb_le_one μ c

theorem firstChoiceMissProb_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceMissProb μ c := by
  simpa [firstChoiceMissProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_nonneg μ c

theorem firstChoiceMissProb_le_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceMissProb μ c ≤ 1 := by
  simpa [firstChoiceMissProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_le_one μ c

@[simp] theorem firstChoiceProb_add_firstChoiceMissProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceProb μ c + firstChoiceMissProb μ c = 1 := by
  simpa [firstChoiceProb, firstChoiceMissProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceProb_add_firstChoiceMissProb μ c

@[simp] theorem firstChoiceMissProb_add_firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceMissProb μ c + firstChoiceProb μ c = 1 := by
  simpa [firstChoiceProb, firstChoiceMissProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_add_firstChoiceProb μ c

theorem sum_firstChoiceProb_eq_one {n : ℕ}
    (μ : PMF (Ranking n)) :
    (∑ c : Candidate n, firstChoiceProb μ c) = 1 := by
  simpa [firstChoiceProb] using
    EconCSLib.SocialChoice.Ranking.sum_firstChoiceProb_eq_one μ

theorem expectedFirstMoverUtility_eq_sum_firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedFirstMoverUtility μ value =
      ∑ c : Candidate n, firstChoiceProb μ c * value c := by
  simpa [firstChoiceProb] using
    EconCSLib.SocialChoice.Ranking.expectedFirstMoverUtility_eq_sum_firstChoiceProb
      μ value

theorem firstChoiceMissProb_eq_pmfProb_ne {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceMissProb μ c = pmfProb μ (fun π => c ≠ firstChoice π) := by
  simpa [firstChoiceMissProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_eq_pmfProb_ne μ c

theorem firstChoiceMissProb_pos_of_mass_ne_firstChoice {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) (π₀ : Ranking n)
    (hne : c ≠ firstChoice π₀)
    (hmass : 0 < (μ π₀).toReal) :
    0 < firstChoiceMissProb μ c := by
  simpa [firstChoiceMissProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_pos_of_mass_ne_firstChoice
      μ c π₀ hne hmass

theorem innerRerankingGain_eq_missProb_mul_gap {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) :
    pmfExp μ (fun σ => rerankingGainOnPair value π σ) =
      firstChoiceMissProb μ (firstChoice π) * valueGap value π := by
  simpa [firstChoiceMissProb, valueGap,
    rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair] using
    EconCSLib.SocialChoice.Ranking.innerRerankingGain_eq_missProb_mul_gap
      (μ := μ) (value := value) (π := π)

theorem expectedRerankingGain_eq_expect_missProb_mul_gap {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedRerankingGain μ value =
      pmfExp μ (fun π =>
        firstChoiceMissProb μ (firstChoice π) * valueGap value π) := by
  simpa [expectedRerankingGain,
    EconCSLib.SocialChoice.Ranking.expectedRerankingGain,
    firstChoiceMissProb, valueGap,
    rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair] using
    EconCSLib.SocialChoice.Ranking.expectedRerankingGain_eq_expect_missProb_mul_gap
      (μ := μ) (value := value)

theorem expectedRerankingGain_nonneg_of_gap_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    0 ≤ expectedRerankingGain μ value := by
  simpa [expectedRerankingGain,
    EconCSLib.SocialChoice.Ranking.expectedRerankingGain,
    valueGap, rerankingGainOnPair,
    EconCSLib.SocialChoice.Ranking.rerankingGainOnPair] using
    EconCSLib.SocialChoice.Ranking.expectedRerankingGain_nonneg_of_gap_nonneg
      (μ := μ) (value := value) (by
        intro π
        simpa [valueGap] using hgap π)

theorem secondMoverAgainst_eq_runnerup_add_missProb_mul_gap {n : ℕ}
    (μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) :
    secondMoverAgainst μFirst value π =
      value (secondChoice π) +
        firstChoiceMissProb μFirst (firstChoice π) * valueGap value π := by
  simpa [secondMoverAgainst,
    EconCSLib.SocialChoice.Ranking.secondMoverAgainst,
    firstChoiceMissProb, valueGap] using
    EconCSLib.SocialChoice.Ranking.secondMoverAgainst_eq_runnerup_add_missProb_mul_gap
      (μFirst := μFirst) (value := value) (π := π)

theorem secondMoverAgainst_eq_top_sub_collisionProb_mul_gap {n : ℕ}
    (μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) :
    secondMoverAgainst μFirst value π =
      value (firstChoice π) -
        firstChoiceProb μFirst (firstChoice π) * valueGap value π := by
  simpa [secondMoverAgainst,
    EconCSLib.SocialChoice.Ranking.secondMoverAgainst,
    firstChoiceProb, valueGap] using
    EconCSLib.SocialChoice.Ranking.secondMoverAgainst_eq_top_sub_collisionProb_mul_gap
      (μFirst := μFirst) (value := value) (π := π)

theorem expectedSecondMoverIndependent_eq_expect_secondMoverAgainst {n : ℕ}
    (μSecond μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μSecond μFirst value =
      pmfExp μSecond (fun π => secondMoverAgainst μFirst value π) := by
  simpa [secondMoverAgainst,
    EconCSLib.SocialChoice.Ranking.secondMoverAgainst] using
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent_eq_expect_secondMoverAgainst
      (μSecond := μSecond) (μFirst := μFirst) (value := value)

theorem expectedSecondMoverIndependent_eq_expect_top_sub_collision_loss {n : ℕ}
    (μSecond μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μSecond μFirst value =
      pmfExp μSecond
        (fun π => value (firstChoice π) -
          firstChoiceProb μFirst (firstChoice π) * valueGap value π) := by
  simpa [firstChoiceProb, valueGap] using
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent_eq_expect_top_sub_collision_loss
      (μSecond := μSecond) (μFirst := μFirst) (value := value)

/-- Definition 2, rewritten using only first-choice probabilities and value gaps. -/
theorem prefersIndependentReranking_iff_expected_missGap_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersIndependentReranking μ value ↔
      0 < pmfExp μ
        (fun π => firstChoiceMissProb μ (firstChoice π) * valueGap value π) := by
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos]
  rw [expectedRerankingGain_eq_expect_missProb_mul_gap]

end KR21Monoculture
