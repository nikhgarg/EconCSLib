import KR21Monoculture.PaperDefinitions
import EconCSLib.Foundations.Probability.FiniteExpectation
import EconCSLib.SocialChoice.Ranking.Payoff

open scoped BigOperators
open EconCSLib

namespace KR21Monoculture

/--
For a pair of rankings `(π, σ)`, this is the second mover's gain from being allowed
an independent reranking `π` instead of being forced to reuse the common ranking `π`
when the first mover uses `σ`.

This is the pointwise integrand that appears in the finite-sum form of Equation (3)
from the paper.
-/
def rerankingGainOnPair {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) : ℝ :=
  if firstChoice π = firstChoice σ then 0
  else value (firstChoice π) - value (secondChoice π)

@[simp] theorem rerankingGainOnPair_self {n : ℕ} (value : Candidate n → ℝ)
    (π : Ranking n) :
    rerankingGainOnPair value π π = 0 := by
  simpa [rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.rerankingGainOnPair_self value π

@[simp] theorem rerankingGainOnPair_of_sameFirst {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) (h : firstChoice π = firstChoice σ) :
    rerankingGainOnPair value π σ = 0 := by
  simpa [rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.rerankingGainOnPair_of_sameFirst
      value π σ h

@[simp] theorem rerankingGainOnPair_of_neFirst {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) (h : firstChoice π ≠ firstChoice σ) :
    rerankingGainOnPair value π σ =
      value (firstChoice π) - value (secondChoice π) := by
  simpa [rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.rerankingGainOnPair_of_neFirst
      value π σ h

/--
Pointwise decomposition of the second mover's utility under an independent reranking
into the shared-ranking utility plus the reranking gain.
-/
theorem secondMoverUtility_eq_shared_add_rerankingGain {n : ℕ}
    (value : Candidate n → ℝ) (π σ : Ranking n) :
    secondMoverUtility value π σ =
      secondMoverUtility value π π + rerankingGainOnPair value π σ := by
  simpa [secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.secondMoverUtility_eq_shared_add_rerankingGain
      value π σ

/--
Subtractive form of `secondMoverUtility_eq_shared_add_rerankingGain`.
-/
theorem secondMoverUtility_sub_self_eq_rerankingGain {n : ℕ}
    (value : Candidate n → ℝ) (π σ : Ranking n) :
    secondMoverUtility value π σ - secondMoverUtility value π π =
      rerankingGainOnPair value π σ := by
  simpa [secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.secondMoverUtility_sub_self_eq_rerankingGain
      value π σ

/--
A pair-lifted version of shared-reranking utility. This keeps both terms on the same
product space `μ × μ`, which is convenient for finite-sum manipulations.
-/
noncomputable def expectedSecondMoverSharedOnPairs {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ μ (fun π _σ => secondMoverUtility value π π)

/--
The expected gain from independent reranking over a pair of i.i.d. ranking draws.
-/
noncomputable def expectedRerankingGain {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ μ (fun π σ => rerankingGainOnPair value π σ)

/--
Finite-sum Equation (3) on the common product space `μ × μ`.

This is the algebraic heart of the paper's Definition 2 reformulation before the
final normalization step back to the one-variable shared expectation.
-/
theorem expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value - expectedSecondMoverSharedOnPairs μ value =
      expectedRerankingGain μ value := by
  simpa [expectedSecondMoverIndependent,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    expectedSecondMoverSharedOnPairs,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverSharedOnPairs,
    expectedRerankingGain, EconCSLib.SocialChoice.Ranking.expectedRerankingGain,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
      (μ := μ) (value := value)

/--
Additive form of the pair-lifted Equation (3).
-/
theorem expectedSecondMoverIndependent_eq_sharedOnPairs_add_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value =
      expectedSecondMoverSharedOnPairs μ value + expectedRerankingGain μ value := by
  simpa [expectedSecondMoverIndependent,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    expectedSecondMoverSharedOnPairs,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverSharedOnPairs,
    expectedRerankingGain, EconCSLib.SocialChoice.Ranking.expectedRerankingGain,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent_eq_sharedOnPairs_add_expectedRerankingGain
      (μ := μ) (value := value)

/--
A positivity reformulation of the pair-lifted reranking preference.
-/
noncomputable def PrefersIndependentRerankingOnPairs {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : Prop :=
  0 < expectedRerankingGain μ value

/--
The pair-lifted version of Definition 2 is equivalent to positivity of the expected
reranking gain.
-/
theorem prefersIndependentRerankingOnPairs_iff {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    PrefersIndependentRerankingOnPairs μ value ↔
      expectedSecondMoverSharedOnPairs μ value < expectedSecondMoverIndependent μ μ value := by
  unfold PrefersIndependentRerankingOnPairs
  have h :=
    expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
      (μ := μ) (value := value)
  constructor
  · intro hpos
    linarith
  · intro hlt
    linarith

@[simp] theorem expectedSecondMoverSharedOnPairs_eq_expectedSecondMoverShared
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverSharedOnPairs μ value = expectedSecondMoverShared μ value := by
  simpa [expectedSecondMoverSharedOnPairs,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverSharedOnPairs,
    expectedSecondMoverShared,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverShared,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice] using
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverSharedOnPairs_eq_expectedSecondMoverShared
      (μ := μ) (value := value)

/--
The exact finite-sum Equation (3) identity for the shared-vs-independent formulation.
-/
theorem expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value - expectedSecondMoverShared μ value =
      expectedRerankingGain μ value := by
  simpa [expectedSecondMoverIndependent,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    expectedSecondMoverShared,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverShared,
    expectedRerankingGain, EconCSLib.SocialChoice.Ranking.expectedRerankingGain,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
      (μ := μ) (value := value)

/--
Definition 2 in utility form is exactly positivity of the expected reranking gain.
-/
theorem prefersIndependentReranking_iff_expectedRerankingGain_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersIndependentReranking μ value ↔ 0 < expectedRerankingGain μ value := by
  unfold Model.PrefersIndependentReranking
  have h := expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    (μ := μ) (value := value)
  constructor
  · intro hlt
    linarith
  · intro hpos
    linarith

/--
The pair-lifted positivity formulation is equivalent to the original utility-side
Definition 2.
-/
theorem prefersIndependentReranking_iff_onPairs {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersIndependentReranking μ value ↔ PrefersIndependentRerankingOnPairs μ value := by
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos]
  rfl

@[simp] theorem expectedRerankingGain_pure {n : ℕ}
    (π : Ranking n) (value : Candidate n → ℝ) :
    expectedRerankingGain (PMF.pure π) value = 0 := by
  simpa [expectedRerankingGain, EconCSLib.SocialChoice.Ranking.expectedRerankingGain,
    rerankingGainOnPair, EconCSLib.SocialChoice.Ranking.rerankingGainOnPair,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.expectedRerankingGain_pure π value

end KR21Monoculture
