import Monoculture.RerankingGain

open DecisionCore

namespace Monoculture

/--
Expected welfare when both firms are forced to use the same realized ranking draw.
This is the shared-ranking welfare counterpart to the independent ordered welfare.
-/
noncomputable def expectedWelfareShared {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfExp μ (fun π => welfareOrdered value π π)

/-- Shared-ranking welfare is first-position utility plus second-position utility. -/
theorem expectedWelfareShared_eq_firstMover_add_secondMoverShared {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedWelfareShared μ value =
      expectedFirstMoverUtility μ value + expectedSecondMoverShared μ value := by
  unfold expectedWelfareShared expectedFirstMoverUtility expectedSecondMoverShared
  rw [← pmfExp_add]
  congr 1
  funext π
  simp [welfareOrdered]

/--
Ordered independent welfare decomposes into the first mover's expected first-position
utility plus the second mover's independent-ranking utility.
-/
theorem expectedWelfareOrdered_eq_firstMover_add_secondMoverIndependent {n : ℕ}
    (μ₂ μ₁ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedWelfareOrdered μ₂ μ₁ value =
      expectedFirstMoverUtility μ₁ value + expectedSecondMoverIndependent μ₂ μ₁ value := by
  unfold expectedWelfareOrdered welfareOrdered expectedFirstMoverUtility
    expectedSecondMoverIndependent
  rw [pmfPairExp_add]
  rw [pmfPairExp_ignore_left]

/--
For a single ranking distribution, the welfare gain from independent reranking over a
shared realized ranking is exactly the expected reranking gain of the second mover.
-/
theorem expectedWelfareOrdered_self_sub_expectedWelfareShared_eq_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedWelfareOrdered μ μ value - expectedWelfareShared μ value =
      expectedRerankingGain μ value := by
  rw [expectedWelfareOrdered_eq_firstMover_add_secondMoverIndependent]
  rw [expectedWelfareShared_eq_firstMover_add_secondMoverShared]
  have h := expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    (μ := μ) (value := value)
  linarith

/-- Additive version of the shared-vs-independent welfare decomposition. -/
theorem expectedWelfareOrdered_self_eq_expectedWelfareShared_add_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedWelfareOrdered μ μ value =
      expectedWelfareShared μ value + expectedRerankingGain μ value := by
  have h := expectedWelfareOrdered_self_sub_expectedWelfareShared_eq_expectedRerankingGain
    (μ := μ) (value := value)
  linarith

namespace Model

/-- Model-level ordered welfare decomposition. -/
theorem welfareOrdered_eq_firstMoverEU_add_secondMoverEU {n : ℕ}
    (M : Model n) (s₁ s₂ : Strategy) :
    welfareOrdered M s₁ s₂ = firstMoverEU M s₁ + secondMoverEU M s₁ s₂ := by
  unfold welfareOrdered firstMoverEU secondMoverEU
  exact expectedWelfareOrdered_eq_firstMover_add_secondMoverIndependent
    (μ₂ := M.rankingDist s₂) (μ₁ := M.rankingDist s₁) (value := M.value)

end Model

end Monoculture
