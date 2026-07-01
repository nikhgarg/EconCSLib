import KR21Monoculture.Payoff

open EconCSLib

namespace KR21Monoculture

/--
If every ranking in the outer expectation has zero miss probability for its own
first choice, independent reranking has zero expected gain.
-/
theorem expectedRerankingGain_eq_zero_of_all_missProb_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hmiss : ∀ π : Ranking n, firstChoiceMissProb μ (firstChoice π) = 0) :
    expectedRerankingGain μ value = 0 := by
  simpa [expectedRerankingGain, EconCSLib.SocialChoice.Ranking.expectedRerankingGain,
    firstChoiceMissProb, EconCSLib.SocialChoice.Ranking.firstChoiceMissProb,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice] using
    EconCSLib.SocialChoice.Ranking.expectedRerankingGain_eq_zero_of_all_missProb_zero
      (μ := μ) (value := value) (by
        intro π
        simpa [firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
          firstChoiceMissProb, EconCSLib.SocialChoice.Ranking.firstChoiceMissProb]
          using hmiss π)

/--
If every top-vs-runner-up value gap is zero, independent reranking has zero
expected gain.
-/
theorem expectedRerankingGain_eq_zero_of_all_valueGap_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, valueGap value π = 0) :
    expectedRerankingGain μ value = 0 := by
  simpa [expectedRerankingGain, EconCSLib.SocialChoice.Ranking.expectedRerankingGain,
    valueGap, EconCSLib.SocialChoice.Ranking.valueGap] using
    EconCSLib.SocialChoice.Ranking.expectedRerankingGain_eq_zero_of_all_valueGap_zero
      (μ := μ) (value := value) (by
        intro π
        simpa [valueGap, EconCSLib.SocialChoice.Ranking.valueGap] using hgap π)

/--
Zero miss probability collapses independent and shared second-mover utility.
-/
theorem expectedSecondMoverIndependent_eq_shared_of_all_missProb_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hmiss : ∀ π : Ranking n, firstChoiceMissProb μ (firstChoice π) = 0) :
    expectedSecondMoverIndependent μ μ value = expectedSecondMoverShared μ value := by
  simpa [expectedSecondMoverIndependent,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    expectedSecondMoverShared,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverShared] using
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent_eq_shared_of_all_missProb_zero
      (μ := μ) (value := value) (by
        intro π
        simpa [firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
          firstChoiceMissProb, EconCSLib.SocialChoice.Ranking.firstChoiceMissProb]
          using hmiss π)

/--
Zero value gaps also collapse independent and shared second-mover utility.
-/
theorem expectedSecondMoverIndependent_eq_shared_of_all_valueGap_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, valueGap value π = 0) :
    expectedSecondMoverIndependent μ μ value = expectedSecondMoverShared μ value := by
  simpa [expectedSecondMoverIndependent,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    expectedSecondMoverShared,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverShared] using
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent_eq_shared_of_all_valueGap_zero
      (μ := μ) (value := value) (by
        intro π
        simpa [valueGap, EconCSLib.SocialChoice.Ranking.valueGap] using hgap π)

/-- No independent-reranking preference is possible when all relevant miss probabilities vanish. -/
theorem not_prefersIndependentReranking_of_all_missProb_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hmiss : ∀ π : Ranking n, firstChoiceMissProb μ (firstChoice π) = 0) :
    ¬ Model.PrefersIndependentReranking μ value := by
  simpa [Model.PrefersIndependentReranking,
    EconCSLib.SocialChoice.Ranking.PrefersIndependentReranking] using
    EconCSLib.SocialChoice.Ranking.not_prefersIndependentReranking_of_all_missProb_zero
      (μ := μ) (value := value) (by
        intro π
        simpa [firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
          firstChoiceMissProb, EconCSLib.SocialChoice.Ranking.firstChoiceMissProb]
          using hmiss π)

/-- No independent-reranking preference is possible when every top-second gap is zero. -/
theorem not_prefersIndependentReranking_of_all_valueGap_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, valueGap value π = 0) :
    ¬ Model.PrefersIndependentReranking μ value := by
  simpa [Model.PrefersIndependentReranking,
    EconCSLib.SocialChoice.Ranking.PrefersIndependentReranking] using
    EconCSLib.SocialChoice.Ranking.not_prefersIndependentReranking_of_all_valueGap_zero
      (μ := μ) (value := value) (by
        intro π
        simpa [valueGap, EconCSLib.SocialChoice.Ranking.valueGap] using hgap π)

end KR21Monoculture
