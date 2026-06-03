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

The equality is written as `c = firstChoice π` so that later formulas read as
"the competitor takes my top candidate".
-/
noncomputable def firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  EconCSLib.SocialChoice.Ranking.firstChoiceProb μ c

/-- The probability that a draw from `μ` does *not* put candidate `c` first. -/
noncomputable def firstChoiceMissProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  EconCSLib.SocialChoice.Ranking.firstChoiceMissProb μ c

/--
The loss from being forced down from a ranking's first candidate to its second
candidate.  This is the pointwise value gap that appears in Equation (3).
-/
def valueGap {n : ℕ} (value : Candidate n → ℝ) (π : Ranking n) : ℝ :=
  EconCSLib.SocialChoice.Ranking.valueGap value π

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

/-- First-choice probabilities are nonnegative. -/
theorem firstChoiceProb_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceProb μ c := by
  exact EconCSLib.SocialChoice.Ranking.firstChoiceProb_nonneg μ c

/-- First-choice probabilities are at most one. -/
theorem firstChoiceProb_le_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceProb μ c ≤ 1 := by
  exact EconCSLib.SocialChoice.Ranking.firstChoiceProb_le_one μ c

/-- Miss probabilities are nonnegative. -/
theorem firstChoiceMissProb_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceMissProb μ c := by
  exact EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_nonneg μ c

/-- Miss probabilities are at most one. -/
theorem firstChoiceMissProb_le_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceMissProb μ c ≤ 1 := by
  exact EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_le_one μ c

@[simp] theorem firstChoiceProb_add_firstChoiceMissProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceProb μ c + firstChoiceMissProb μ c = 1 := by
  exact EconCSLib.SocialChoice.Ranking.firstChoiceProb_add_firstChoiceMissProb μ c

@[simp] theorem firstChoiceMissProb_add_firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceMissProb μ c + firstChoiceProb μ c = 1 := by
  exact EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_add_firstChoiceProb μ c

/-- The first-choice probabilities over all candidates sum to one. -/
theorem sum_firstChoiceProb_eq_one {n : ℕ}
    (μ : PMF (Ranking n)) :
    (∑ c : Candidate n, firstChoiceProb μ c) = 1 := by
  exact EconCSLib.SocialChoice.Ranking.sum_firstChoiceProb_eq_one μ

/--
First-mover expected utility can be regrouped by the candidate selected first.
-/
theorem expectedFirstMoverUtility_eq_sum_firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedFirstMoverUtility μ value =
      ∑ c : Candidate n, firstChoiceProb μ c * value c := by
  simpa [expectedFirstMoverUtility, firstChoiceProb] using
    EconCSLib.SocialChoice.Ranking.expectedFirstMoverUtility_eq_sum_firstChoiceProb
      μ value

/-- Miss probability is the probability that the first choice is not `c`. -/
theorem firstChoiceMissProb_eq_pmfProb_ne {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceMissProb μ c = pmfProb μ (fun π => c ≠ firstChoice π) := by
  simpa [firstChoiceMissProb] using
    EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_eq_pmfProb_ne μ c

/--
If a positive-mass ranking does not put `c` first, then the miss probability for
`c` is strictly positive.
-/
theorem firstChoiceMissProb_pos_of_mass_ne_firstChoice {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) (π₀ : Ranking n)
    (hne : c ≠ firstChoice π₀)
    (hmass : 0 < (μ π₀).toReal) :
    0 < firstChoiceMissProb μ c := by
  exact EconCSLib.SocialChoice.Ranking.firstChoiceMissProb_pos_of_mass_ne_firstChoice
    μ c π₀ hne hmass

/--
For a fixed second-mover ranking `π`, the expected reranking gain over the first
mover's draw equals

`Pr[first mover misses π's top candidate] * (value(top_π) - value(second_π))`.

This is the pointwise first-choice-probability form of the paper's Equation (3).
-/
theorem innerRerankingGain_eq_missProb_mul_gap {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) :
    pmfExp μ (fun σ => rerankingGainOnPair value π σ) =
      firstChoiceMissProb μ (firstChoice π) * valueGap value π := by
  simpa [firstChoiceMissProb, valueGap,
    EconCSLib.SocialChoice.Ranking.valueGap,
    rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.innerRerankingGain_eq_missProb_mul_gap
      (μ := μ) (value := value) (π := π)

/--
Equation (3) integrated over the second mover's ranking: expected reranking gain is
an expectation of a miss probability times the top-vs-runner-up value gap.
-/
theorem expectedRerankingGain_eq_expect_missProb_mul_gap {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedRerankingGain μ value =
      pmfExp μ (fun π => firstChoiceMissProb μ (firstChoice π) * valueGap value π) := by
  simpa [expectedRerankingGain, EconCSLib.SocialChoice.Ranking.expectedRerankingGain,
    firstChoiceMissProb, valueGap,
    EconCSLib.SocialChoice.Ranking.valueGap,
    rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.expectedRerankingGain_eq_expect_missProb_mul_gap
      (μ := μ) (value := value)

/-- Definition 2, rewritten using only first-choice probabilities and value gaps. -/
theorem prefersIndependentReranking_iff_expected_missGap_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersIndependentReranking μ value ↔
      0 < pmfExp μ
        (fun π => firstChoiceMissProb μ (firstChoice π) * valueGap value π) := by
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos]
  rw [expectedRerankingGain_eq_expect_missProb_mul_gap]

/--
A simple sufficient condition: if every ranking in the support order has a
nonnegative top-vs-runner-up value gap, then the expected reranking gain is
nonnegative.
-/
theorem expectedRerankingGain_nonneg_of_gap_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    0 ≤ expectedRerankingGain μ value := by
  simpa [expectedRerankingGain, EconCSLib.SocialChoice.Ranking.expectedRerankingGain,
    valueGap, EconCSLib.SocialChoice.Ranking.valueGap,
    rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.expectedRerankingGain_nonneg_of_gap_nonneg
      (μ := μ) (value := value) (by
        intro π
        simpa [valueGap, EconCSLib.SocialChoice.Ranking.valueGap,
          firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
          secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using hgap π)

/--
The utility of a fixed second-mover ranking against a first-mover distribution.
-/
noncomputable def secondMoverAgainst {n : ℕ}
    (μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) : ℝ :=
  pmfExp μFirst (fun σ => secondMoverUtility value π σ)

/--
Against a first-mover distribution, a fixed ranking gets its runner-up value plus
its expected reranking gain.
-/
theorem secondMoverAgainst_eq_runnerup_add_missProb_mul_gap {n : ℕ}
    (μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) :
    secondMoverAgainst μFirst value π =
      value (secondChoice π) +
        firstChoiceMissProb μFirst (firstChoice π) * valueGap value π := by
  simpa [secondMoverAgainst, EconCSLib.SocialChoice.Ranking.secondMoverAgainst,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    firstChoiceMissProb, valueGap,
    EconCSLib.SocialChoice.Ranking.valueGap,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.secondMoverAgainst_eq_runnerup_add_missProb_mul_gap
      (μFirst := μFirst) (value := value) (π := π)

/--
Equivalent loss form: expected utility equals top-candidate value minus the
probability that the competitor also takes that candidate times the top-second gap.
-/
theorem secondMoverAgainst_eq_top_sub_collisionProb_mul_gap {n : ℕ}
    (μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) :
    secondMoverAgainst μFirst value π =
      value (firstChoice π) -
        firstChoiceProb μFirst (firstChoice π) * valueGap value π := by
  simpa [secondMoverAgainst, EconCSLib.SocialChoice.Ranking.secondMoverAgainst,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    firstChoiceMissProb, firstChoiceProb, valueGap,
    EconCSLib.SocialChoice.Ranking.valueGap,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.secondMoverAgainst_eq_top_sub_collisionProb_mul_gap
      (μFirst := μFirst) (value := value) (π := π)

/-- Existing independent second-mover utility, rewritten by conditioning on the second ranking. -/
theorem expectedSecondMoverIndependent_eq_expect_secondMoverAgainst {n : ℕ}
    (μSecond μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μSecond μFirst value =
      pmfExp μSecond (fun π => secondMoverAgainst μFirst value π) := by
  simpa [expectedSecondMoverIndependent,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    secondMoverAgainst, EconCSLib.SocialChoice.Ranking.secondMoverAgainst,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice] using
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent_eq_expect_secondMoverAgainst
      (μSecond := μSecond) (μFirst := μFirst) (value := value)

/--
Independent second-mover utility depends on the first mover only through
first-choice collision probabilities.
-/
theorem expectedSecondMoverIndependent_eq_expect_top_sub_collision_loss {n : ℕ}
    (μSecond μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μSecond μFirst value =
      pmfExp μSecond
        (fun π => value (firstChoice π) -
          firstChoiceProb μFirst (firstChoice π) * valueGap value π) := by
  simpa [expectedSecondMoverIndependent,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    firstChoiceProb, valueGap,
    EconCSLib.SocialChoice.Ranking.valueGap,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent_eq_expect_top_sub_collision_loss
      (μSecond := μSecond) (μFirst := μFirst) (value := value)

end KR21Monoculture
