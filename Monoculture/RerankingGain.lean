import Monoculture.PaperDefinitions
import DecisionCore

open scoped BigOperators
open DecisionCore

namespace Monoculture

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
  simp [rerankingGainOnPair]

@[simp] theorem rerankingGainOnPair_of_sameFirst {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) (h : firstChoice π = firstChoice σ) :
    rerankingGainOnPair value π σ = 0 := by
  have h' : π 0 = σ 0 := by
    simpa [firstChoice] using h
  simp [rerankingGainOnPair, firstChoice, h']

@[simp] theorem rerankingGainOnPair_of_neFirst {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) (h : firstChoice π ≠ firstChoice σ) :
    rerankingGainOnPair value π σ =
      value (firstChoice π) - value (secondChoice π) := by
  have h' : π 0 ≠ σ 0 := by
    simpa [firstChoice] using h
  simp [rerankingGainOnPair, firstChoice, secondChoice, h']

/--
Pointwise decomposition of the second mover's utility under an independent reranking
into the shared-ranking utility plus the reranking gain.
-/
theorem secondMoverUtility_eq_shared_add_rerankingGain {n : ℕ}
    (value : Candidate n → ℝ) (π σ : Ranking n) :
    secondMoverUtility value π σ =
      secondMoverUtility value π π + rerankingGainOnPair value π σ := by
  by_cases h : firstChoice π = firstChoice σ
  · have h' : π 0 = σ 0 := by
      simpa [firstChoice] using h
    simp [secondMoverUtility_eq_if, rerankingGainOnPair, firstChoice, secondChoice, h']
  · have h' : π 0 ≠ σ 0 := by
      simpa [firstChoice] using h
    simp [secondMoverUtility_eq_if, rerankingGainOnPair, firstChoice, secondChoice, h']

/--
Subtractive form of `secondMoverUtility_eq_shared_add_rerankingGain`.
-/
theorem secondMoverUtility_sub_self_eq_rerankingGain {n : ℕ}
    (value : Candidate n → ℝ) (π σ : Ranking n) :
    secondMoverUtility value π σ - secondMoverUtility value π π =
      rerankingGainOnPair value π σ := by
  rw [secondMoverUtility_eq_shared_add_rerankingGain]
  ring

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
  unfold expectedSecondMoverIndependent expectedSecondMoverSharedOnPairs
    expectedRerankingGain pmfPairExp
  rw [← pmfExp_sub]
  congr 1
  funext π
  rw [← pmfExp_sub]
  congr 1
  funext σ
  exact secondMoverUtility_sub_self_eq_rerankingGain (value := value) π σ

/--
Additive form of the pair-lifted Equation (3).
-/
theorem expectedSecondMoverIndependent_eq_sharedOnPairs_add_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value =
      expectedSecondMoverSharedOnPairs μ value + expectedRerankingGain μ value := by
  have h :=
    expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
      (μ := μ) (value := value)
  linarith

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
  unfold expectedSecondMoverSharedOnPairs expectedSecondMoverShared pmfPairExp
  simp [pmfExp_const]

/--
The exact finite-sum Equation (3) identity for the shared-vs-independent formulation.
-/
theorem expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value - expectedSecondMoverShared μ value =
      expectedRerankingGain μ value := by
  rw [← expectedSecondMoverSharedOnPairs_eq_expectedSecondMoverShared]
  exact expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
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
  unfold expectedRerankingGain pmfPairExp
  simp [pmfExp_pure]

end Monoculture
