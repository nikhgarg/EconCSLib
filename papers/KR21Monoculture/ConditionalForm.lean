import KR21Monoculture.RerankingGain
import EconCSLib.Foundations.Probability.Conditional

open EconCSLib

namespace KR21Monoculture

/-- A pair of i.i.d. ranking draws. -/
abbrev RankingPair (n : ℕ) := Ranking n × Ranking n

/-- The event that two rankings disagree on the first-position candidate. -/
def disagreementEvent {n : ℕ} : RankingPair n → Prop := fun p => firstChoice p.1 ≠ firstChoice p.2

instance decidableDisagreementEvent {n : ℕ} : DecidablePred (@disagreementEvent n) := by
  intro p
  unfold disagreementEvent
  infer_instance

/-- The reranking-gain integrand viewed as a function on ranking pairs. -/
def pairRerankingGain {n : ℕ} (value : Candidate n → ℝ) : RankingPair n → ℝ := fun p => rerankingGainOnPair value p.1 p.2

/-- Probability that two i.i.d. ranking draws disagree on the first choice. -/
noncomputable def disagreementProb {n : ℕ} (μ : PMF (Ranking n)) : ℝ := pmfPairProb μ μ disagreementEvent

/-- Conditional expected reranking gain given disagreement on the first choice. -/
noncomputable def disagreementConditionalGain {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ := pmfPairConditionalExp μ μ disagreementEvent (pairRerankingGain value)

@[simp] theorem pairRerankingGain_apply {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) :
    pairRerankingGain value (π, σ) = rerankingGainOnPair value π σ := rfl

/-- Since `rerankingGainOnPair` is already `0` on agreement, the indicator form is exact. -/
theorem expectedRerankingGain_eq_pairIndicatorExp {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedRerankingGain μ value =
      pmfPairIndicatorExp μ μ disagreementEvent (pairRerankingGain value) := by
  unfold expectedRerankingGain pmfPairIndicatorExp pmfPairExp pmfExp
    disagreementEvent pairRerankingGain
  refine Finset.sum_congr rfl ?_
  intro π _
  congr 1
  refine Finset.sum_congr rfl ?_
  intro σ _
  by_cases h : firstChoice π = firstChoice σ
  · have h' : π 0 = σ 0 := by simpa [firstChoice] using h
    simp [rerankingGainOnPair, firstChoice, h']
  · have h' : π 0 ≠ σ 0 := by simpa [firstChoice] using h
    simp [rerankingGainOnPair, firstChoice, secondChoice, h']

/-- On a positive-probability disagreement event, the conditional gain is a simple ratio. -/
theorem disagreementConditionalGain_eq_expectedRerankingGain_div_of_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (h : 0 < disagreementProb μ) :
    disagreementConditionalGain μ value =
      expectedRerankingGain μ value / disagreementProb μ := by
  unfold disagreementConditionalGain disagreementProb at *
  rw [pmfPairConditionalExp_eq_div_of_pos (μ := μ) (ν := μ)
    (p := disagreementEvent) (f := pairRerankingGain value) h]
  rw [← expectedRerankingGain_eq_pairIndicatorExp (μ := μ) (value := value)]

/-- Positive reranking preference is equivalent to positive conditional gain on disagreement. -/
theorem prefersIndependentReranking_iff_conditionalGain_pos_of_disagreementPos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (h : 0 < disagreementProb μ) :
    Model.PrefersIndependentReranking μ value ↔ 0 < disagreementConditionalGain μ value := by
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos]
  rw [disagreementConditionalGain_eq_expectedRerankingGain_div_of_pos (μ := μ) (value := value) h]
  exact (zero_lt_div_iff_pos_right h).symm

@[simp] theorem disagreementProb_pure {n : ℕ} (π : Ranking n) :
    disagreementProb (PMF.pure π) = 0 := by
  unfold disagreementProb pmfPairProb disagreementEvent
  simp [firstChoice]

@[simp] theorem disagreementConditionalGain_pure {n : ℕ}
    (π : Ranking n) (value : Candidate n → ℝ) :
    disagreementConditionalGain (PMF.pure π) value = 0 := by
  unfold disagreementConditionalGain
  rw [pmfPairConditionalExp_of_prob_zero]
  exact disagreementProb_pure (π := π)

end KR21Monoculture
