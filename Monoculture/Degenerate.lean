import Monoculture.Payoff

open DecisionCore

namespace Monoculture

/--
If every ranking in the outer expectation has zero miss probability for its own
first choice, independent reranking has zero expected gain.
-/
theorem expectedRerankingGain_eq_zero_of_all_missProb_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hmiss : ∀ π : Ranking n, firstChoiceMissProb μ (firstChoice π) = 0) :
    expectedRerankingGain μ value = 0 := by
  classical
  rw [expectedRerankingGain_eq_expect_missProb_mul_gap]
  unfold pmfExp
  refine Finset.sum_eq_zero ?_
  intro π _
  have hπ : firstChoiceMissProb μ (π 0) = 0 := by
    simpa [firstChoice] using hmiss π
  simp [hπ]

/--
If every top-vs-runner-up value gap is zero, independent reranking has zero
expected gain.
-/
theorem expectedRerankingGain_eq_zero_of_all_valueGap_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, valueGap value π = 0) :
    expectedRerankingGain μ value = 0 := by
  classical
  rw [expectedRerankingGain_eq_expect_missProb_mul_gap]
  unfold pmfExp
  simp [hgap]

/--
Zero miss probability collapses independent and shared second-mover utility.
-/
theorem expectedSecondMoverIndependent_eq_shared_of_all_missProb_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hmiss : ∀ π : Ranking n, firstChoiceMissProb μ (firstChoice π) = 0) :
    expectedSecondMoverIndependent μ μ value = expectedSecondMoverShared μ value := by
  have hgain := expectedRerankingGain_eq_zero_of_all_missProb_zero
    (μ := μ) (value := value) hmiss
  have hmain := expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    (μ := μ) (value := value)
  linarith

/--
Zero value gaps also collapse independent and shared second-mover utility.
-/
theorem expectedSecondMoverIndependent_eq_shared_of_all_valueGap_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, valueGap value π = 0) :
    expectedSecondMoverIndependent μ μ value = expectedSecondMoverShared μ value := by
  have hgain := expectedRerankingGain_eq_zero_of_all_valueGap_zero
    (μ := μ) (value := value) hgap
  have hmain := expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    (μ := μ) (value := value)
  linarith

/-- No independent-reranking preference is possible when all relevant miss probabilities vanish. -/
theorem not_prefersIndependentReranking_of_all_missProb_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hmiss : ∀ π : Ranking n, firstChoiceMissProb μ (firstChoice π) = 0) :
    ¬ Model.PrefersIndependentReranking μ value := by
  intro hpref
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos] at hpref
  have hgain := expectedRerankingGain_eq_zero_of_all_missProb_zero
    (μ := μ) (value := value) hmiss
  linarith

/-- No independent-reranking preference is possible when every top-second gap is zero. -/
theorem not_prefersIndependentReranking_of_all_valueGap_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, valueGap value π = 0) :
    ¬ Model.PrefersIndependentReranking μ value := by
  intro hpref
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos] at hpref
  have hgain := expectedRerankingGain_eq_zero_of_all_valueGap_zero
    (μ := μ) (value := value) hgap
  linarith

end Monoculture
