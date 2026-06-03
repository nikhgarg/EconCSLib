import EconCSLib.Foundations.Math.FiniteSigns
import EconCSLib.SocialChoice.Ranking.Probability
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Payoff Decompositions for Ranking Laws

Reusable finite PMF algebra for ranking laws with first-choice probabilities
and top-vs-runner-up value gaps.

These lemmas are paper-neutral.  Paper-specific welfare models, strategy names,
and theorem-number wrappers should remain in paper folders and call this layer.

## Main declarations

- `firstChoiceMissProb`
- `valueGap`
- `firstChoiceGapMass`
- `firstChoiceCollisionDiff`
- `secondMoverUtility`
- `expectedSecondMoverIndependent`
- `rerankingGainOnPair`
- `expectedRerankingGain`
- `secondMoverFirstLawSwitchGain`
- `sum_firstChoiceProb_eq_one`
- `sum_firstChoiceGapMass_eq_expectedGap`
-/

open scoped BigOperators

namespace EconCSLib
namespace SocialChoice
namespace Ranking

noncomputable section

/-- The probability that a draw from `μ` does not put candidate `c` first. -/
def firstChoiceMissProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  1 - firstChoiceProb μ c

/--
The loss from being forced down from a ranking's first candidate to its second
candidate.
-/
def valueGap {n : ℕ} (value : Candidate n → ℝ) (π : Ranking n) : ℝ :=
  value (firstChoice π) - value (secondChoice π)

/-- Expected value of the candidate selected by the firm that chooses first. -/
def expectedFirstMoverUtility {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfExp μ (fun π => value (firstChoice π))

/-- Expected value of the candidate hired by the second mover when both firms use
the same realized ranking. -/
def expectedSecondMoverShared {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfExp μ (fun π => value (secondChoice π))

/-- The real-valued probability that a draw from `μ` puts candidate `c` second. -/
def secondChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  pmfProb μ (fun π => c = secondChoice π)

/-- Pointwise utility to the second mover when the first mover uses `σ`
and the second mover uses `π`. -/
def secondMoverUtility {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) : ℝ :=
  value (bestRemainingAfter π (firstChoice σ))

/-- Expected utility to the second mover when the second mover draws `π` from
`μ₂` and the first mover draws `σ` from `μ₁`. -/
def expectedSecondMoverIndependent {n : ℕ}
    (μ₂ μ₁ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ₂ μ₁ (fun π σ => secondMoverUtility value π σ)

/--
Gain to a fixed second-mover law from switching the first-mover law from
`μFrom` to `μTo`.
-/
def secondMoverFirstLawSwitchGain {n : ℕ}
    (μSecond μFrom μTo : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  expectedSecondMoverIndependent μSecond μTo value -
    expectedSecondMoverIndependent μSecond μFrom value

/-- Social welfare in the ordered version of the game where the `σ`-firm chooses
first and the `π`-firm chooses second. -/
def welfareOrdered {n : ℕ} (value : Candidate n → ℝ) (π σ : Ranking n) : ℝ :=
  value (firstChoice σ) + secondMoverUtility value π σ

/-- Social welfare when the first mover uses `μ₁` and the second mover uses `μ₂`. -/
def expectedWelfareOrdered {n : ℕ}
    (μ₂ μ₁ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ₂ μ₁ (fun π σ => welfareOrdered value π σ)

/--
For a pair of rankings `(π, σ)`, this is the second mover's gain from using an
independent ranking `π` instead of sharing `π` when the first mover uses `σ`.
-/
def rerankingGainOnPair {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) : ℝ :=
  if firstChoice π = firstChoice σ then 0
  else value (firstChoice π) - value (secondChoice π)

/-- A pair-lifted version of shared-reranking utility on the common product
space `μ × μ`. -/
def expectedSecondMoverSharedOnPairs {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ μ (fun π _σ => secondMoverUtility value π π)

/-- The expected gain from independent reranking over a pair of i.i.d. ranking
draws. -/
def expectedRerankingGain {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ μ (fun π σ => rerankingGainOnPair value π σ)

@[simp] theorem firstChoiceProb_pure {n : ℕ}
    (π : Ranking n) (c : Candidate n) :
    firstChoiceProb (PMF.pure π) c = if c = firstChoice π then 1 else 0 := by
  classical
  unfold firstChoiceProb pmfProb
  simp [pmfExp_pure]

@[simp] theorem firstChoiceProb_pure_firstChoice {n : ℕ}
    (π : Ranking n) :
    firstChoiceProb (PMF.pure π) (firstChoice π) = 1 := by
  simp

@[simp] theorem firstChoiceMissProb_pure_firstChoice {n : ℕ}
    (π : Ranking n) :
    firstChoiceMissProb (PMF.pure π) (firstChoice π) = 0 := by
  simp [firstChoiceMissProb]

/-- First-choice probabilities are nonnegative. -/
theorem firstChoiceProb_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceProb μ c := by
  classical
  unfold firstChoiceProb pmfProb pmfExp
  refine Finset.sum_nonneg ?_
  intro π _
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  by_cases h : c = firstChoice π
  · have h' : c = π 0 := by simpa [firstChoice] using h
    simp [h']
  · have h' : c ≠ π 0 := by simpa [firstChoice] using h
    simp [h']

/-- First-choice probabilities are at most one. -/
theorem firstChoiceProb_le_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceProb μ c ≤ 1 := by
  classical
  unfold firstChoiceProb pmfProb pmfExp
  calc
    ∑ π : Ranking n, (μ π).toReal * (if c = firstChoice π then (1 : ℝ) else 0)
        ≤ ∑ π : Ranking n, (μ π).toReal * 1 := by
          refine Finset.sum_le_sum ?_
          intro π _
          refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          by_cases h : c = firstChoice π
          · have h' : c = π 0 := by simpa [firstChoice] using h
            simp [h']
          · have h' : c ≠ π 0 := by simpa [firstChoice] using h
            simp [h']
    _ = ∑ π : Ranking n, (μ π).toReal := by simp
    _ = 1 := pmfToRealSum μ

/-- Miss probabilities are nonnegative. -/
theorem firstChoiceMissProb_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    0 ≤ firstChoiceMissProb μ c := by
  unfold firstChoiceMissProb
  have h := firstChoiceProb_le_one (μ := μ) (c := c)
  linarith

/-- Miss probabilities are at most one. -/
theorem firstChoiceMissProb_le_one {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceMissProb μ c ≤ 1 := by
  unfold firstChoiceMissProb
  have h := firstChoiceProb_nonneg (μ := μ) (c := c)
  linarith

@[simp] theorem firstChoiceProb_add_firstChoiceMissProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceProb μ c + firstChoiceMissProb μ c = 1 := by
  unfold firstChoiceMissProb
  ring

@[simp] theorem firstChoiceMissProb_add_firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceMissProb μ c + firstChoiceProb μ c = 1 := by
  rw [add_comm]
  exact firstChoiceProb_add_firstChoiceMissProb (μ := μ) (c := c)

/-- The first-choice probabilities over all candidates sum to one. -/
theorem sum_firstChoiceProb_eq_one {n : ℕ}
    (μ : PMF (Ranking n)) :
    (∑ c : Candidate n, firstChoiceProb μ c) = 1 := by
  classical
  unfold firstChoiceProb pmfProb pmfExp
  rw [Finset.sum_comm]
  calc
    ∑ π : Ranking n, ∑ c : Candidate n,
        (μ π).toReal * (if c = firstChoice π then (1 : ℝ) else 0)
        = ∑ π : Ranking n,
            (μ π).toReal *
              (∑ c : Candidate n, (if c = firstChoice π then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [Finset.mul_sum]
    _ = ∑ π : Ranking n, (μ π).toReal * 1 := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsum :
              (∑ c : Candidate n, (if c = firstChoice π then (1 : ℝ) else 0)) = 1 := by
            simpa using
              (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                (fun _ : Candidate n => (1 : ℝ)))
          rw [hsum]
    _ = ∑ π : Ranking n, (μ π).toReal := by simp
    _ = 1 := pmfToRealSum μ

/--
First-mover expected utility can be regrouped by the candidate selected first.
-/
theorem expectedFirstMoverUtility_eq_sum_firstChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedFirstMoverUtility μ value =
      ∑ c : Candidate n, firstChoiceProb μ c * value c := by
  classical
  unfold expectedFirstMoverUtility firstChoiceProb pmfProb pmfExp
  calc
    ∑ π : Ranking n, (μ π).toReal * value (firstChoice π)
        = ∑ π : Ranking n, ∑ c : Candidate n,
            if c = firstChoice π then (μ π).toReal * value c else 0 := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsum :
              (∑ c : Candidate n,
                if c = firstChoice π then (μ π).toReal * value c else 0) =
                (μ π).toReal * value (firstChoice π) := by
            simpa using
              (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                (fun c : Candidate n => (μ π).toReal * value c))
          rw [hsum]
    _ = ∑ c : Candidate n, ∑ π : Ranking n,
            if c = firstChoice π then (μ π).toReal * value c else 0 := by
          exact Finset.sum_comm
    _ = ∑ c : Candidate n, ∑ π : Ranking n,
            ((μ π).toReal *
              (if c = firstChoice π then (1 : ℝ) else 0)) * value c := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = firstChoice π
          · simp [h]
          · simp
    _ = ∑ c : Candidate n,
          (∑ π : Ranking n,
            (μ π).toReal *
              (if c = firstChoice π then (1 : ℝ) else 0)) * value c := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.sum_mul]

/-- Shared second-mover utility can be regrouped by the second-position candidate. -/
theorem expectedSecondMoverShared_eq_sum_secondChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverShared μ value =
      ∑ c : Candidate n, secondChoiceProb μ c * value c := by
  classical
  unfold expectedSecondMoverShared secondChoiceProb pmfProb pmfExp
  calc
    ∑ π : Ranking n, (μ π).toReal * value (secondChoice π)
        = ∑ π : Ranking n, ∑ c : Candidate n,
            if c = secondChoice π then (μ π).toReal * value c else 0 := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsum :
              (∑ c : Candidate n,
                if c = secondChoice π then (μ π).toReal * value c else 0) =
                (μ π).toReal * value (secondChoice π) := by
            simpa using
              (Finset.sum_ite_eq' Finset.univ (secondChoice π)
                (fun c : Candidate n => (μ π).toReal * value c))
          rw [hsum]
    _ = ∑ c : Candidate n, ∑ π : Ranking n,
            if c = secondChoice π then (μ π).toReal * value c else 0 := by
          exact Finset.sum_comm
    _ = ∑ c : Candidate n, ∑ π : Ranking n,
            ((μ π).toReal *
              (if c = secondChoice π then (1 : ℝ) else 0)) * value c := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = secondChoice π
          · simp [h]
          · simp
    _ = ∑ c : Candidate n,
          (∑ π : Ranking n,
            (μ π).toReal *
              (if c = secondChoice π then (1 : ℝ) else 0)) * value c := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.sum_mul]

@[simp] theorem secondMoverUtility_self {n : ℕ} (value : Candidate n → ℝ)
    (π : Ranking n) :
    secondMoverUtility value π π = value (secondChoice π) := by
  simp [secondMoverUtility, bestRemainingAfter]

@[simp] theorem secondMoverUtility_eq_if {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) :
    secondMoverUtility value π σ =
      if firstChoice π = firstChoice σ then value (secondChoice π)
      else value (firstChoice π) := by
  by_cases h : firstChoice π = firstChoice σ
  · have h' : π 0 = σ 0 := by
      simpa [firstChoice] using h
    simp [secondMoverUtility, bestRemainingAfter, firstChoice, secondChoice, h']
  · have h' : π 0 ≠ σ 0 := by
      simpa [firstChoice] using h
    simp [secondMoverUtility, bestRemainingAfter, firstChoice, h']

@[simp] theorem welfareOrdered_eq {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) :
    welfareOrdered value π σ =
      value (firstChoice σ) + value (bestRemainingAfter π (firstChoice σ)) := rfl

@[simp] theorem welfareOrdered_self {n : ℕ} (value : Candidate n → ℝ)
    (π : Ranking n) :
    welfareOrdered value π π = value (firstChoice π) + value (secondChoice π) := by
  simp [welfareOrdered, secondMoverUtility, bestRemainingAfter]

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
Pointwise decomposition of second-mover utility into the shared-ranking utility
plus the reranking gain.
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

theorem secondMoverUtility_sub_self_eq_rerankingGain {n : ℕ}
    (value : Candidate n → ℝ) (π σ : Ranking n) :
    secondMoverUtility value π σ - secondMoverUtility value π π =
      rerankingGainOnPair value π σ := by
  rw [secondMoverUtility_eq_shared_add_rerankingGain]
  ring

/-- Finite-sum equation on the common product space `μ × μ`. -/
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

theorem expectedSecondMoverIndependent_eq_sharedOnPairs_add_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value =
      expectedSecondMoverSharedOnPairs μ value + expectedRerankingGain μ value := by
  have h :=
    expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
      (μ := μ) (value := value)
  linarith

@[simp] theorem expectedSecondMoverSharedOnPairs_eq_expectedSecondMoverShared
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverSharedOnPairs μ value = expectedSecondMoverShared μ value := by
  unfold expectedSecondMoverSharedOnPairs expectedSecondMoverShared pmfPairExp
  simp [pmfExp_const]

theorem expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value - expectedSecondMoverShared μ value =
      expectedRerankingGain μ value := by
  rw [← expectedSecondMoverSharedOnPairs_eq_expectedSecondMoverShared]
  exact expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
    (μ := μ) (value := value)

@[simp] theorem expectedRerankingGain_pure {n : ℕ}
    (π : Ranking n) (value : Candidate n → ℝ) :
    expectedRerankingGain (PMF.pure π) value = 0 := by
  unfold expectedRerankingGain pmfPairExp
  simp [pmfExp_pure]

private theorem pmf_compl_indicator_sum {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    (∑ a : α, (μ a).toReal * (if p a then (0 : ℝ) else 1)) =
      1 - ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
  classical
  calc
    ∑ a : α, (μ a).toReal * (if p a then (0 : ℝ) else 1)
        = ∑ a : α,
            ((μ a).toReal * 1 -
              (μ a).toReal * (if p a then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases h : p a <;> simp [h]
    _ = (∑ a : α, (μ a).toReal * 1) -
          ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
          simp [pmfToRealSum μ]

/-- Miss probability is the probability that the first choice is not `c`. -/
theorem firstChoiceMissProb_eq_pmfProb_ne {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) :
    firstChoiceMissProb μ c = pmfProb μ (fun π => c ≠ firstChoice π) := by
  classical
  unfold firstChoiceMissProb firstChoiceProb pmfProb pmfExp
  rw [← pmf_compl_indicator_sum μ (fun π : Ranking n => c = firstChoice π)]
  refine Finset.sum_congr rfl ?_
  intro π _
  by_cases h : c = firstChoice π <;> simp [h]

/--
If a positive-mass ranking does not put `c` first, then the miss probability for
`c` is strictly positive.
-/
theorem firstChoiceMissProb_pos_of_mass_ne_firstChoice {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) (π₀ : Ranking n)
    (hne : c ≠ firstChoice π₀)
    (hmass : 0 < (μ π₀).toReal) :
    0 < firstChoiceMissProb μ c := by
  classical
  rw [firstChoiceMissProb_eq_pmfProb_ne]
  unfold pmfProb pmfExp
  refine EconCSLib.sum_univ_pos_of_pos_of_nonneg
    (f := fun π : Ranking n =>
      (μ π).toReal * if c ≠ firstChoice π then (1 : ℝ) else 0)
    (a₀ := π₀) ?hpos ?hnonneg
  · have hne' : c ≠ π₀ 0 := by simpa [firstChoice] using hne
    simpa [firstChoice, hne'] using hmass
  · intro π
    refine mul_nonneg ENNReal.toReal_nonneg ?_
    by_cases h : c = π 0 <;> simp [firstChoice, h]

/--
The contribution to expected value gap coming from rankings whose first choice
is `c`.
-/
def firstChoiceGapMass {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n) : ℝ :=
  pmfExp μ (fun π => if c = firstChoice π then valueGap value π else 0)

/--
The collision-probability difference between a better and worse ranking law,
viewed candidate-by-candidate.
-/
def firstChoiceCollisionDiff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  firstChoiceProb μBetter c - firstChoiceProb μWorse c

/-- Summing the first-choice fibers recovers the full expected value gap. -/
theorem sum_firstChoiceGapMass_eq_expectedGap {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    (∑ c : Candidate n, firstChoiceGapMass μ value c) =
      pmfExp μ (fun π => valueGap value π) := by
  classical
  unfold firstChoiceGapMass pmfExp
  rw [Finset.sum_comm]
  calc
    ∑ π : Ranking n, ∑ c : Candidate n,
        (μ π).toReal * (if c = firstChoice π then valueGap value π else 0)
        = ∑ π : Ranking n,
            (μ π).toReal *
              (∑ c : Candidate n,
                if c = firstChoice π then valueGap value π else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [← Finset.mul_sum]
    _ = ∑ π : Ranking n, (μ π).toReal * valueGap value π := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsum :
              (∑ c : Candidate n,
                if c = firstChoice π then valueGap value π else 0) =
                valueGap value π := by
            simpa using
              (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                (fun _ : Candidate n => valueGap value π))
          rw [hsum]
    _ = pmfExp μ (fun π => valueGap value π) := by
          rfl

/--
If every ranking in the first-choice fiber of `c` has nonnegative value gap,
then the corresponding first-choice gap mass is nonnegative.
-/
theorem firstChoiceGapMass_nonneg_of_gap_nonneg_onFiber {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n)
    (hgap : ∀ π : Ranking n, c = firstChoice π → 0 ≤ valueGap value π) :
    0 ≤ firstChoiceGapMass μ value c := by
  classical
  unfold firstChoiceGapMass pmfExp
  refine Finset.sum_nonneg ?_
  intro π _
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  by_cases h : c = firstChoice π
  · simpa [h] using hgap π h
  · have h' : c ≠ π 0 := by simpa [firstChoice] using h
    simp [h']

/--
For a fixed second-mover ranking, the expected reranking gain over the first
mover's draw is the miss probability for the fixed top candidate times the
fixed top-vs-runner-up value gap.
-/
theorem innerRerankingGain_eq_missProb_mul_gap {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) :
    pmfExp μ (fun σ => rerankingGainOnPair value π σ) =
      firstChoiceMissProb μ (firstChoice π) * valueGap value π := by
  classical
  unfold firstChoiceMissProb firstChoiceProb pmfProb valueGap rerankingGainOnPair pmfExp
  set gap : ℝ := value (firstChoice π) - value (secondChoice π)
  change
    (∑ σ : Ranking n, (μ σ).toReal *
        (if firstChoice π = firstChoice σ then (0 : ℝ) else gap)) =
      (1 - ∑ σ : Ranking n, (μ σ).toReal *
        (if firstChoice π = firstChoice σ then (1 : ℝ) else 0)) * gap
  calc
    ∑ σ : Ranking n, (μ σ).toReal *
        (if firstChoice π = firstChoice σ then (0 : ℝ) else gap)
        = ∑ σ : Ranking n,
            ((μ σ).toReal *
              (if firstChoice π = firstChoice σ then (0 : ℝ) else 1)) * gap := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          by_cases h : firstChoice π = firstChoice σ <;> simp
    _ = (∑ σ : Ranking n, (μ σ).toReal *
            (if firstChoice π = firstChoice σ then (0 : ℝ) else 1)) * gap := by
          rw [Finset.sum_mul]
    _ = (1 - ∑ σ : Ranking n, (μ σ).toReal *
            (if firstChoice π = firstChoice σ then (1 : ℝ) else 0)) * gap := by
          rw [pmf_compl_indicator_sum]

/-- The utility of a fixed second-mover ranking against a first-mover distribution. -/
def secondMoverAgainst {n : ℕ}
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
  classical
  unfold secondMoverAgainst
  calc
    pmfExp μFirst (fun σ => secondMoverUtility value π σ)
        = pmfExp μFirst
            (fun σ => value (secondChoice π) + rerankingGainOnPair value π σ) := by
          congr 1
          funext σ
          rw [secondMoverUtility_eq_shared_add_rerankingGain]
          simp
    _ = pmfExp μFirst (fun _ => value (secondChoice π)) +
          pmfExp μFirst (fun σ => rerankingGainOnPair value π σ) := by
          rw [pmfExp_add]
    _ = value (secondChoice π) +
          firstChoiceMissProb μFirst (firstChoice π) * valueGap value π := by
          simp [innerRerankingGain_eq_missProb_mul_gap]

/--
Equivalent loss form: expected utility equals top-candidate value minus the
probability that the competitor also takes that candidate times the top-second gap.
-/
theorem secondMoverAgainst_eq_top_sub_collisionProb_mul_gap {n : ℕ}
    (μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) :
    secondMoverAgainst μFirst value π =
      value (firstChoice π) -
        firstChoiceProb μFirst (firstChoice π) * valueGap value π := by
  rw [secondMoverAgainst_eq_runnerup_add_missProb_mul_gap]
  unfold firstChoiceMissProb valueGap firstChoice secondChoice
  ring

/-- Independent second-mover utility, rewritten by conditioning on the second ranking. -/
theorem expectedSecondMoverIndependent_eq_expect_secondMoverAgainst {n : ℕ}
    (μSecond μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μSecond μFirst value =
      pmfExp μSecond (fun π => secondMoverAgainst μFirst value π) := by
  rfl

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
  rw [expectedSecondMoverIndependent_eq_expect_secondMoverAgainst]
  congr 1
  funext π
  rw [secondMoverAgainst_eq_top_sub_collisionProb_mul_gap]

/--
Expected reranking gain is an expectation of a miss probability times the
top-vs-runner-up value gap.
-/
theorem expectedRerankingGain_eq_expect_missProb_mul_gap {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedRerankingGain μ value =
      pmfExp μ (fun π => firstChoiceMissProb μ (firstChoice π) * valueGap value π) := by
  classical
  unfold expectedRerankingGain pmfPairExp
  congr 1
  funext π
  exact innerRerankingGain_eq_missProb_mul_gap (μ := μ) (value := value) (π := π)

theorem expectedRerankingGain_nonneg_of_gap_nonneg {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    0 ≤ expectedRerankingGain μ value := by
  classical
  rw [expectedRerankingGain_eq_expect_missProb_mul_gap]
  unfold pmfExp
  refine Finset.sum_nonneg ?_
  intro π _
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  exact mul_nonneg
    (firstChoiceMissProb_nonneg (μ := μ) (c := firstChoice π))
    (hgap π)

/--
Equation grouped by the second mover's first-choice candidate rather than by full
rankings.
-/
theorem expectedRerankingGain_eq_sum_firstChoiceMissProb_mul_firstChoiceGapMass
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedRerankingGain μ value =
      ∑ c : Candidate n,
        firstChoiceMissProb μ c * firstChoiceGapMass μ value c := by
  classical
  rw [expectedRerankingGain_eq_expect_missProb_mul_gap]
  unfold firstChoiceGapMass pmfExp
  calc
    ∑ π : Ranking n,
        (μ π).toReal *
          (firstChoiceMissProb μ (firstChoice π) * valueGap value π)
        = ∑ π : Ranking n,
            (μ π).toReal *
              (∑ c : Candidate n,
                firstChoiceMissProb μ c *
                  (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsplit :
              firstChoiceMissProb μ (firstChoice π) * valueGap value π =
                ∑ c : Candidate n,
                  firstChoiceMissProb μ c *
                    (if c = firstChoice π then valueGap value π else 0) := by
            calc
              firstChoiceMissProb μ (firstChoice π) * valueGap value π
                  = ∑ c : Candidate n,
                      if c = firstChoice π
                      then firstChoiceMissProb μ c * valueGap value π
                      else 0 := by
                        symm
                        simpa using
                          (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                            (fun c : Candidate n =>
                              firstChoiceMissProb μ c * valueGap value π))
              _ = ∑ c : Candidate n,
                    firstChoiceMissProb μ c *
                      (if c = firstChoice π then valueGap value π else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro c _
                    by_cases h : c = firstChoice π <;> simp [h]
          rw [hsplit]
    _ = ∑ π : Ranking n,
          ∑ c : Candidate n,
            (μ π).toReal *
              (firstChoiceMissProb μ c *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [Finset.mul_sum]
    _ = ∑ π : Ranking n,
          ∑ c : Candidate n,
            firstChoiceMissProb μ c *
              ((μ π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          refine Finset.sum_congr rfl ?_
          intro c _
          ring
    _ = ∑ c : Candidate n,
          ∑ π : Ranking n,
            firstChoiceMissProb μ c *
              ((μ π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          rw [Finset.sum_comm]
    _ = ∑ c : Candidate n,
          firstChoiceMissProb μ c *
            (∑ π : Ranking n,
              (μ π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.mul_sum]
    _ = ∑ c : Candidate n,
          firstChoiceMissProb μ c * firstChoiceGapMass μ value c := by
          rfl

/--
First-mover utility minus independent second-mover utility, grouped by the
second mover's first-choice candidate.
-/
theorem expectedFirstMover_sub_secondMoverIndependent_eq_sum_firstChoiceProb_mul_firstChoiceGapMass
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedFirstMoverUtility μ value - expectedSecondMoverIndependent μ μ value =
      ∑ c : Candidate n,
        firstChoiceProb μ c * firstChoiceGapMass μ value c := by
  classical
  rw [expectedSecondMoverIndependent_eq_expect_top_sub_collision_loss]
  unfold expectedFirstMoverUtility firstChoiceGapMass pmfExp
  calc
    (∑ π : Ranking n, (μ π).toReal * value (firstChoice π)) -
        (∑ π : Ranking n,
          (μ π).toReal *
            (value (firstChoice π) -
              firstChoiceProb μ (firstChoice π) * valueGap value π))
        =
        ∑ π : Ranking n,
          (μ π).toReal *
            (firstChoiceProb μ (firstChoice π) * valueGap value π) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro π _
          ring
    _ = ∑ π : Ranking n,
          (μ π).toReal *
            (∑ c : Candidate n,
              firstChoiceProb μ c *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsplit :
              firstChoiceProb μ (firstChoice π) * valueGap value π =
                ∑ c : Candidate n,
                  firstChoiceProb μ c *
                    (if c = firstChoice π then valueGap value π else 0) := by
            calc
              firstChoiceProb μ (firstChoice π) * valueGap value π
                  = ∑ c : Candidate n,
                      if c = firstChoice π
                      then firstChoiceProb μ c * valueGap value π
                      else 0 := by
                        symm
                        simpa using
                          (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                            (fun c : Candidate n =>
                              firstChoiceProb μ c * valueGap value π))
              _ = ∑ c : Candidate n,
                    firstChoiceProb μ c *
                      (if c = firstChoice π then valueGap value π else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro c _
                    by_cases h : c = firstChoice π <;> simp [h]
          rw [hsplit]
    _ = ∑ π : Ranking n,
          ∑ c : Candidate n,
            (μ π).toReal *
              (firstChoiceProb μ c *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [Finset.mul_sum]
    _ = ∑ π : Ranking n,
          ∑ c : Candidate n,
            firstChoiceProb μ c *
              ((μ π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          refine Finset.sum_congr rfl ?_
          intro c _
          ring
    _ = ∑ c : Candidate n,
          ∑ π : Ranking n,
            firstChoiceProb μ c *
              ((μ π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          rw [Finset.sum_comm]
    _ = ∑ c : Candidate n,
          firstChoiceProb μ c *
            (∑ π : Ranking n,
              (μ π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.mul_sum]
    _ = ∑ c : Candidate n,
          firstChoiceProb μ c * firstChoiceGapMass μ value c := by
          rfl

/--
Collision-loss differences between two first-mover laws, grouped by first-choice
candidate.
-/
theorem expectedCollisionLossDiff_eq_sum_collisionDiff_mul_firstChoiceGapMass
    {n : ℕ} (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    pmfExp μWorse
      (fun π =>
        (firstChoiceProb μBetter (firstChoice π) -
            firstChoiceProb μWorse (firstChoice π)) * valueGap value π) =
      ∑ c : Candidate n,
        firstChoiceCollisionDiff μBetter μWorse c *
          firstChoiceGapMass μWorse value c := by
  classical
  unfold firstChoiceCollisionDiff firstChoiceGapMass pmfExp
  calc
    ∑ π : Ranking n,
        (μWorse π).toReal *
          ((firstChoiceProb μBetter (firstChoice π) -
              firstChoiceProb μWorse (firstChoice π)) * valueGap value π)
        = ∑ π : Ranking n,
            (μWorse π).toReal *
              (∑ c : Candidate n,
                (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
                  (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          have hsplit :
              (firstChoiceProb μBetter (firstChoice π) -
                  firstChoiceProb μWorse (firstChoice π)) * valueGap value π =
                ∑ c : Candidate n,
                  (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
                    (if c = firstChoice π then valueGap value π else 0) := by
            calc
              (firstChoiceProb μBetter (firstChoice π) -
                  firstChoiceProb μWorse (firstChoice π)) * valueGap value π
                  = ∑ c : Candidate n,
                      if c = firstChoice π
                      then (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
                        valueGap value π
                      else 0 := by
                        symm
                        simpa using
                          (Finset.sum_ite_eq' Finset.univ (firstChoice π)
                            (fun c : Candidate n =>
                              (firstChoiceProb μBetter c -
                                  firstChoiceProb μWorse c) *
                                valueGap value π))
              _ = ∑ c : Candidate n,
                    (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
                      (if c = firstChoice π then valueGap value π else 0) := by
                    refine Finset.sum_congr rfl ?_
                    intro c _
                    by_cases h : c = firstChoice π <;> simp [h]
          rw [hsplit]
    _ = ∑ π : Ranking n,
          ∑ c : Candidate n,
            (μWorse π).toReal *
              ((firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [Finset.mul_sum]
    _ = ∑ π : Ranking n,
          ∑ c : Candidate n,
            (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
              ((μWorse π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          refine Finset.sum_congr rfl ?_
          intro c _
          ring
    _ = ∑ c : Candidate n,
          ∑ π : Ranking n,
            (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
              ((μWorse π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          rw [Finset.sum_comm]
    _ = ∑ c : Candidate n,
          (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
            (∑ π : Ranking n,
              (μWorse π).toReal *
                (if c = firstChoice π then valueGap value π else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.mul_sum]
    _ = ∑ c : Candidate n,
          firstChoiceCollisionDiff μBetter μWorse c *
            firstChoiceGapMass μWorse value c := by
          rfl

/--
Switching the first-mover law changes the second mover's payoff only through
first-choice collision probabilities.
-/
theorem secondMoverFirstLawSwitchGain_eq_expected_collision_loss_diff {n : ℕ}
    (μSecond μFrom μTo : PMF (Ranking n)) (value : Candidate n → ℝ) :
    secondMoverFirstLawSwitchGain μSecond μFrom μTo value =
      pmfExp μSecond
        (fun π =>
          (firstChoiceProb μFrom (firstChoice π) -
              firstChoiceProb μTo (firstChoice π)) * valueGap value π) := by
  classical
  unfold secondMoverFirstLawSwitchGain
  rw [expectedSecondMoverIndependent_eq_expect_top_sub_collision_loss
        (μSecond := μSecond) (μFirst := μTo) (value := value)]
  rw [expectedSecondMoverIndependent_eq_expect_top_sub_collision_loss
        (μSecond := μSecond) (μFirst := μFrom) (value := value)]
  rw [← pmfExp_sub]
  congr 1
  funext π
  ring

/--
If the target first-mover law collides weakly less often with every relevant top
choice, then switching to it weakly increases the second mover's payoff.
-/
theorem secondMoverFirstLawSwitchGain_nonneg_of_collisionProb_le_and_gap_nonneg
    {n : ℕ} (μSecond μFrom μTo : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hprob : ∀ π : Ranking n,
      firstChoiceProb μTo (firstChoice π) ≤ firstChoiceProb μFrom (firstChoice π))
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    0 ≤ secondMoverFirstLawSwitchGain μSecond μFrom μTo value := by
  classical
  rw [secondMoverFirstLawSwitchGain_eq_expected_collision_loss_diff]
  unfold pmfExp
  refine Finset.sum_nonneg ?_
  intro π _
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  refine mul_nonneg ?_ (hgap π)
  exact sub_nonneg.mpr (hprob π)

theorem expectedSecondMoverIndependent_le_of_collisionProb_le_and_gap_nonneg
    {n : ℕ} (μSecond μFrom μTo : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hprob : ∀ π : Ranking n,
      firstChoiceProb μTo (firstChoice π) ≤ firstChoiceProb μFrom (firstChoice π))
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    expectedSecondMoverIndependent μSecond μFrom value ≤
      expectedSecondMoverIndependent μSecond μTo value := by
  have hgain :=
    secondMoverFirstLawSwitchGain_nonneg_of_collisionProb_le_and_gap_nonneg
      (μSecond := μSecond) (μFrom := μFrom) (μTo := μTo) (value := value)
      hprob hgap
  unfold secondMoverFirstLawSwitchGain at hgain
  linarith

end

end Ranking
end SocialChoice
end EconCSLib
