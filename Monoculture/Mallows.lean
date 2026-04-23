import Monoculture.WeakCompetition
import Monoculture.Kendall
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators
open DecisionCore

namespace Monoculture

/--
Unnormalised real Mallows weight.  This file uses the inverse of the paper
parameter: if the paper writes mass proportional to `Φ^{-d}` with `Φ > 1`,
then this file writes the same mass as `q^d` with `q = Φ⁻¹` and `0 < q < 1`.
-/
noncomputable def mallowsWeight {n : ℕ} (q : ℝ) (ρ π : Ranking n) : ℝ :=
  q ^ kendallTau ρ π

@[simp] theorem mallowsWeight_center {n : ℕ} (q : ℝ) (ρ : Ranking n) :
    mallowsWeight q ρ ρ = 1 := by
  simp [mallowsWeight]

/-- The finite partition function for the real-weight Mallows kernel. -/
noncomputable def mallowsPartition {n : ℕ} (q : ℝ) (ρ : Ranking n) : ℝ :=
  ∑ π : Ranking n, mallowsWeight q ρ π

/--
A Mallows distribution packaged as an actual `PMF` plus the real finite-sum facts
that identify its probabilities with normalized Mallows weights.

This deliberately avoids making the first implementation depend on a delicate
`ENNReal` construction.  A later file can replace this specification with a
constructor using `PMF.ofFintype` or `PMF.normalize`.
-/
structure MallowsSpec (n : ℕ) where
  center : Ranking n
  /-- Inverse Mallows parameter `q`; the paper's parameter is `q⁻¹`. -/
  q : ℝ
  law : PMF (Ranking n)
  partition : ℝ
  q_pos : 0 < q
  partition_pos : 0 < partition
  partition_eq_sum : partition = mallowsPartition q center
  law_apply_toReal : ∀ π : Ranking n,
    (law π).toReal = mallowsWeight q center π / partition

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/-- The true/central first candidate. -/
def centerFirst : Candidate n := firstChoice M.center

/-- The true/central second candidate. -/
def centerSecond : Candidate n := secondChoice M.center

@[simp] theorem partition_ne_zero : M.partition ≠ 0 := by
  exact ne_of_gt M.partition_pos

/-- The unnormalised mass of rankings whose first choice is `c`. -/
noncomputable def firstWeight (c : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if c = firstChoice π then mallowsWeight M.q M.center π else 0

/-- The unnormalised mass of rankings whose first two choices are `c,d`. -/
noncomputable def firstSecondWeight (c d : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if c = firstChoice π ∧ d = secondChoice π
    then mallowsWeight M.q M.center π
    else 0

/-- First-choice probabilities reduce to finite Mallows weights. -/
theorem firstChoiceProb_eq_firstWeight_div_partition (c : Candidate n) :
    firstChoiceProb M.law c = M.firstWeight c / M.partition := by
  classical
  unfold firstChoiceProb pmfProb pmfExp firstWeight
  calc
    ∑ π : Ranking n, (M.law π).toReal *
        (if c = firstChoice π then (1 : ℝ) else 0)
        = ∑ π : Ranking n,
            (mallowsWeight M.q M.center π / M.partition) *
              (if c = firstChoice π then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking n,
          (if c = firstChoice π then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = firstChoice π
          · have h' : c = π 0 := by simpa [firstChoice] using h
            simp [h']
          · have h' : c ≠ π 0 := by simpa [firstChoice] using h
            simp [h']
    _ = (∑ π : Ranking n,
          if c = firstChoice π then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          rw [Finset.sum_div]

/-- Probability that a Mallows draw begins with the ordered pair `(c,d)`. -/
noncomputable def firstSecondChoiceProb (c d : Candidate n) : ℝ :=
  pmfProb M.law (fun π => c = firstChoice π ∧ d = secondChoice π)

/-- First/second-choice probabilities reduce to finite Mallows weights. -/
theorem firstSecondChoiceProb_eq_firstSecondWeight_div_partition
    (c d : Candidate n) :
    M.firstSecondChoiceProb c d = M.firstSecondWeight c d / M.partition := by
  classical
  unfold firstSecondChoiceProb pmfProb pmfExp firstSecondWeight
  calc
    ∑ π : Ranking n, (M.law π).toReal *
        (if c = firstChoice π ∧ d = secondChoice π then (1 : ℝ) else 0)
        = ∑ π : Ranking n,
            (mallowsWeight M.q M.center π / M.partition) *
              (if c = firstChoice π ∧ d = secondChoice π then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking n,
          (if c = firstChoice π ∧ d = secondChoice π
            then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = firstChoice π ∧ d = secondChoice π
          · have hc : c = π 0 := by simpa [firstChoice] using h.1
            have hd : d = π 1 := by simpa [secondChoice] using h.2
            simp [hc, hd]
          · have h' : ¬(c = π 0 ∧ d = π 1) := by
              intro hraw
              apply h
              exact ⟨by simpa [firstChoice] using hraw.1,
                by simpa [secondChoice] using hraw.2⟩
            simp [h']
    _ = (∑ π : Ranking n,
          if c = firstChoice π ∧ d = secondChoice π
            then mallowsWeight M.q M.center π else 0) /
            M.partition := by
          rw [Finset.sum_div]

/-- The first-choice weights partition the Mallows partition function. -/
theorem sum_firstWeight_eq_partition :
    (∑ c : Candidate n, M.firstWeight c) = M.partition := by
  classical
  unfold firstWeight
  rw [M.partition_eq_sum]
  unfold mallowsPartition
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro π _
  have hsum :
      (∑ c : Candidate n,
        if c = firstChoice π then mallowsWeight M.q M.center π else 0) =
        mallowsWeight M.q M.center π := by
    simpa using
      (Finset.sum_ite_eq' Finset.univ (firstChoice π)
        (fun _ : Candidate n => mallowsWeight M.q M.center π))
  rw [hsum]

/-- For a fixed first candidate, summing over second candidates recovers first mass. -/
theorem sum_firstSecondWeight_right_eq_firstWeight (c : Candidate n) :
    (∑ d : Candidate n, M.firstSecondWeight c d) = M.firstWeight c := by
  classical
  unfold firstSecondWeight firstWeight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro π _
  by_cases hc : c = firstChoice π
  · have hsum :
      (∑ d : Candidate n,
        if d = secondChoice π then mallowsWeight M.q M.center π else 0) =
        mallowsWeight M.q M.center π := by
        simpa using
          (Finset.sum_ite_eq' Finset.univ (secondChoice π)
            (fun _ : Candidate n => mallowsWeight M.q M.center π))
    simpa [hc] using hsum
  · have hc' : c ≠ π 0 := by simpa [firstChoice] using hc
    simp [hc']

/-- The probability version of `sum_firstSecondWeight_right_eq_firstWeight`. -/
theorem sum_firstSecondChoiceProb_right_eq_firstChoiceProb (c : Candidate n) :
    (∑ d : Candidate n, M.firstSecondChoiceProb c d) = firstChoiceProb M.law c := by
  classical
  rw [M.firstChoiceProb_eq_firstWeight_div_partition c]
  calc
    ∑ d : Candidate n, M.firstSecondChoiceProb c d
        = ∑ d : Candidate n, M.firstSecondWeight c d / M.partition := by
          refine Finset.sum_congr rfl ?_
          intro d _
          rw [M.firstSecondChoiceProb_eq_firstSecondWeight_div_partition c d]
    _ = (∑ d : Candidate n, M.firstSecondWeight c d) / M.partition := by
          rw [Finset.sum_div]
    _ = M.firstWeight c / M.partition := by
          rw [M.sum_firstSecondWeight_right_eq_firstWeight c]

/-- First-choice probability of the center's first candidate in weight form. -/
theorem centerFirstProb_eq :
    firstChoiceProb M.law M.centerFirst = M.firstWeight M.centerFirst / M.partition :=
  M.firstChoiceProb_eq_firstWeight_div_partition M.centerFirst

/-- First/second probability of the center's first two candidates in weight form. -/
theorem centerFirstSecondProb_eq :
    M.firstSecondChoiceProb M.centerFirst M.centerSecond =
      M.firstSecondWeight M.centerFirst M.centerSecond / M.partition :=
  M.firstSecondChoiceProb_eq_firstSecondWeight_div_partition M.centerFirst M.centerSecond

end MallowsSpec

/--
Two Mallows laws meant to represent the algorithmic and human rankings around the
same central/true ranking.
-/
structure MallowsComparison (n : ℕ) where
  algorithm : MallowsSpec n
  human : MallowsSpec n
  same_center : algorithm.center = human.center

namespace MallowsComparison

variable {n : ℕ} (C : MallowsComparison n)

/-- The induced two-strategy model for a fixed pointwise value vector. -/
noncomputable def toModel (value : Candidate n → ℝ) : Model n where
  algorithmRanking := C.algorithm.law
  humanRanking := C.human.law
  value := value

/--
Algorithm is the lower-`q` / more concentrated law, as a data-level predicate.
Here `q` is the inverse of the paper's `Φ`, so lower means more accurate.
-/
def AlgorithmNoiselessOrMoreConcentrated : Prop :=
  C.algorithm.q ≤ C.human.q

/--
The finite Mallows lemmas needed by the existing algebraic core.

The paper proves these from the Mallows finite-sum formulas.  In this repo they
are isolated as the exact local proof obligations that remain after the reusable
utility identities are in place.
-/
structure FiniteLemmaCertificate (value : Candidate n → ℝ) : Prop where
  independent_reranking_gain_pos_algorithm :
    0 < expectedRerankingGain C.algorithm.law value
  independent_reranking_gain_pos_human :
    0 < expectedRerankingGain C.human.law value
  weaker_competition_collision_sum_pos :
    0 < pmfExp C.human.law
      (fun π =>
        (firstChoiceProb C.algorithm.law (firstChoice π) -
            firstChoiceProb C.human.law (firstChoice π)) * valueGap value π)

/-- The certificate gives Definition 2 for the algorithm/Mallows law. -/
theorem algorithm_prefersIndependentReranking_of_certificate
    {value : Candidate n → ℝ} (cert : C.FiniteLemmaCertificate value) :
    Model.PrefersIndependentReranking C.algorithm.law value := by
  exact (prefersIndependentReranking_iff_expectedRerankingGain_pos
    (μ := C.algorithm.law) (value := value)).2
      cert.independent_reranking_gain_pos_algorithm

/-- The certificate also records Definition 2 for the human/Mallows law. -/
theorem human_prefersIndependentReranking_of_certificate
    {value : Candidate n → ℝ} (cert : C.FiniteLemmaCertificate value) :
    Model.PrefersIndependentReranking C.human.law value := by
  exact (prefersIndependentReranking_iff_expectedRerankingGain_pos
    (μ := C.human.law) (value := value)).2
      cert.independent_reranking_gain_pos_human

/-- The certificate gives Definition 3 for algorithmic-vs-human Mallows laws. -/
theorem prefersWeakerCompetition_of_certificate
    {value : Candidate n → ℝ} (cert : C.FiniteLemmaCertificate value) :
    Model.PrefersWeakerCompetition C.algorithm.law C.human.law value := by
  exact (prefersWeakerCompetition_iff_expected_collision_loss_diff_pos
    (μBetter := C.algorithm.law) (μWorse := C.human.law) (value := value)).2
      cert.weaker_competition_collision_sum_pos

/-- The local Mallows finite lemmas imply the paper-level fixed-parameter hypotheses. -/
theorem paperHypotheses_of_certificate
    {value : Candidate n → ℝ} (cert : C.FiniteLemmaCertificate value) :
    Model.PaperHypotheses (C.toModel value) := by
  constructor
  · exact C.algorithm_prefersIndependentReranking_of_certificate cert
  · exact C.prefersWeakerCompetition_of_certificate cert

end MallowsComparison

end Monoculture
