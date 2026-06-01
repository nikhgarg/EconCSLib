import KR21Monoculture.WeakCompetition

open scoped BigOperators
open EconCSLib

namespace KR21Monoculture

/--
The contribution to expected reranking gain coming from rankings whose top
candidate is `c`.

This packages the part of the expectation that depends on the first-choice fiber
`{ π | firstChoice π = c }`. It is the right object for the Mallows branch,
where finite lemmas are typically stated in terms of top-candidate probabilities.
-/
noncomputable def firstChoiceGapMass {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n) : ℝ :=
  pmfExp μ (fun π => if c = firstChoice π then valueGap value π else 0)

/--
The collision-probability difference between a better and worse ranking law,
viewed candidate-by-candidate.
-/
noncomputable def firstChoiceCollisionDiff {n : ℕ}
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
Equation (3) grouped by the second mover's first-choice candidate rather than by
full rankings.
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
          simp [firstChoiceGapMass, pmfExp]

/--
First-mover utility minus the expected utility of an independent second mover
with the same ranking law, grouped by the second mover's first-choice candidate.

This is the collision-loss companion to Equation (3): the first mover loses no
candidate, while the second mover loses their top candidate exactly when the
first mover independently chooses the same top candidate.
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
          simp [firstChoiceGapMass, pmfExp]

/-- Candidate-sum version of the utility-side Definition 2. -/
theorem prefersIndependentReranking_iff_firstChoiceGapMassSum_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersIndependentReranking μ value ↔
      0 < ∑ c : Candidate n,
        firstChoiceMissProb μ c * firstChoiceGapMass μ value c := by
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos]
  rw [expectedRerankingGain_eq_sum_firstChoiceMissProb_mul_firstChoiceGapMass]

/--
The collision-loss expression from Definition 3, grouped by the second mover's
first-choice candidate.
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
          simp [firstChoiceCollisionDiff, firstChoiceGapMass, pmfExp]

/-- Definition 3 grouped by first-choice candidate rather than full rankings. -/
theorem weakerCompetitionGain_eq_sum_collisionDiff_mul_firstChoiceGapMass
    {n : ℕ} (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    weakerCompetitionGain μBetter μWorse value =
      ∑ c : Candidate n,
        firstChoiceCollisionDiff μBetter μWorse c *
          firstChoiceGapMass μWorse value c := by
  rw [weakerCompetitionGain_eq_expected_collision_loss_diff]
  exact expectedCollisionLossDiff_eq_sum_collisionDiff_mul_firstChoiceGapMass
    (μBetter := μBetter) (μWorse := μWorse) (value := value)

/-- Candidate-sum version of the utility-side Definition 3. -/
theorem prefersWeakerCompetition_iff_firstChoiceCollisionDiffSum_pos {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersWeakerCompetition μBetter μWorse value ↔
      0 < ∑ c : Candidate n,
        firstChoiceCollisionDiff μBetter μWorse c *
          firstChoiceGapMass μWorse value c := by
  rw [prefersWeakerCompetition_iff_weakerCompetitionGain_pos]
  rw [weakerCompetitionGain_eq_sum_collisionDiff_mul_firstChoiceGapMass]

end KR21Monoculture
