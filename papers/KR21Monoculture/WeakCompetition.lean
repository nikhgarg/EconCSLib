import KR21Monoculture.FirstChoice

open scoped BigOperators
open EconCSLib

namespace KR21Monoculture

/--
The second-mover utility gain from facing the weaker/noisier competition
`μWorse` rather than the stronger/more accurate competition `μBetter`, while the
second mover's own ranking is drawn from `μWorse`.
-/
noncomputable def weakerCompetitionGain {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  expectedSecondMoverIndependent μWorse μWorse value -
    expectedSecondMoverIndependent μWorse μBetter value

/-- Preference for weaker competition is positivity of the weaker-competition gain. -/
theorem prefersWeakerCompetition_iff_weakerCompetitionGain_pos {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersWeakerCompetition μBetter μWorse value ↔
      0 < weakerCompetitionGain μBetter μWorse value := by
  unfold Model.PrefersWeakerCompetition weakerCompetitionGain
  constructor <;> intro h <;> linarith

/--
First-choice-probability decomposition of Definition 3.

The gain from weaker competition is the expected value, over the weaker ranking,
of

`(Pr_better[competitor takes my top] - Pr_worse[competitor takes my top]) * valueGap`.

This isolates the economics: weaker competition is valuable when the stronger
competitor is more likely to collide with the second mover's top candidate.
-/
theorem weakerCompetitionGain_eq_expected_collision_loss_diff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    weakerCompetitionGain μBetter μWorse value =
      pmfExp μWorse
        (fun π =>
          (firstChoiceProb μBetter (firstChoice π) -
              firstChoiceProb μWorse (firstChoice π)) * valueGap value π) := by
  simpa [weakerCompetitionGain,
    EconCSLib.SocialChoice.Ranking.secondMoverFirstLawSwitchGain,
    expectedSecondMoverIndependent,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    firstChoiceProb, valueGap,
    EconCSLib.SocialChoice.Ranking.valueGap,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.secondMoverFirstLawSwitchGain_eq_expected_collision_loss_diff
      (μSecond := μWorse) (μFrom := μBetter) (μTo := μWorse) (value := value)

/-- Definition 3, rewritten using first-choice collision probabilities and value gaps. -/
theorem prefersWeakerCompetition_iff_expected_collision_loss_diff_pos {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersWeakerCompetition μBetter μWorse value ↔
      0 < pmfExp μWorse
        (fun π =>
          (firstChoiceProb μBetter (firstChoice π) -
              firstChoiceProb μWorse (firstChoice π)) * valueGap value π) := by
  rw [prefersWeakerCompetition_iff_weakerCompetitionGain_pos]
  rw [weakerCompetitionGain_eq_expected_collision_loss_diff]

/--
A sufficient monotonicity condition for weak competition to be weakly valuable.
If the better competitor collides at least as often with every relevant first
choice and all top-second gaps are nonnegative, then facing the worse competitor
weakly improves second-mover utility.
-/
theorem weakerCompetitionGain_nonneg_of_collisionProb_le_and_gap_nonneg {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hprob : ∀ π : Ranking n,
      firstChoiceProb μWorse (firstChoice π) ≤ firstChoiceProb μBetter (firstChoice π))
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    0 ≤ weakerCompetitionGain μBetter μWorse value := by
  simpa [weakerCompetitionGain,
    EconCSLib.SocialChoice.Ranking.secondMoverFirstLawSwitchGain,
    expectedSecondMoverIndependent,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    valueGap, EconCSLib.SocialChoice.Ranking.valueGap,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.secondMoverFirstLawSwitchGain_nonneg_of_collisionProb_le_and_gap_nonneg
      (μSecond := μWorse) (μFrom := μBetter) (μTo := μWorse) (value := value)
      (by
        intro π
        simpa [firstChoiceProb, firstChoice,
          EconCSLib.SocialChoice.Ranking.firstChoice] using hprob π)
      (by
        intro π
        simpa [valueGap, EconCSLib.SocialChoice.Ranking.valueGap,
          firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
          secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using hgap π)

/-- Utility-side corollary of the sufficient monotonicity condition. -/
theorem expectedSecondMoverIndependent_le_of_collisionProb_le_and_gap_nonneg {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hprob : ∀ π : Ranking n,
      firstChoiceProb μWorse (firstChoice π) ≤ firstChoiceProb μBetter (firstChoice π))
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    expectedSecondMoverIndependent μWorse μBetter value ≤
      expectedSecondMoverIndependent μWorse μWorse value := by
  simpa [expectedSecondMoverIndependent,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent_le_of_collisionProb_le_and_gap_nonneg
      (μSecond := μWorse) (μFrom := μBetter) (μTo := μWorse) (value := value)
      (by
        intro π
        simpa [firstChoiceProb, firstChoice,
          EconCSLib.SocialChoice.Ranking.firstChoice] using hprob π)
      (by
        intro π
        simpa [valueGap, EconCSLib.SocialChoice.Ranking.valueGap,
          firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
          secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using hgap π)

end KR21Monoculture
