import KR21Monoculture.WelfareDecomposition
import EconCSLib.Foundations.Math.FiniteSigns
import EconCSLib.Foundations.Probability.Conditional
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
  pmfProb μ (fun π => c = firstChoice π)

/-- The probability that a draw from `μ` does *not* put candidate `c` first. -/
noncomputable def firstChoiceMissProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  1 - firstChoiceProb μ c

/--
The loss from being forced down from a ranking's first candidate to its second
candidate.  This is the pointwise value gap that appears in Equation (3).
-/
def valueGap {n : ℕ} (value : Candidate n → ℝ) (π : Ranking n) : ℝ :=
  value (firstChoice π) - value (secondChoice π)

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
For a fixed second-mover ranking `π`, the expected reranking gain over the first
mover's draw equals

`Pr[first mover misses π's top candidate] * (value(top_π) - value(second_π))`.

This is the pointwise first-choice-probability form of the paper's Equation (3).
-/
theorem innerRerankingGain_eq_missProb_mul_gap {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (π : Ranking n) :
    pmfExp μ (fun σ => rerankingGainOnPair value π σ) =
      firstChoiceMissProb μ (firstChoice π) * valueGap value π := by
  classical
  unfold pmfExp firstChoiceMissProb firstChoiceProb pmfProb valueGap rerankingGainOnPair
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

/--
Equation (3) integrated over the second mover's ranking: expected reranking gain is
an expectation of a miss probability times the top-vs-runner-up value gap.
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
  unfold firstChoiceMissProb valueGap
  ring

/-- Existing independent second-mover utility, rewritten by conditioning on the second ranking. -/
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

end KR21Monoculture
