import Monoculture.MallowsFiniteLemmas

open scoped BigOperators
open DecisionCore

namespace Monoculture

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/--
Top-two expansion of the unnormalised first-choice gap numerator.

This is the paper's Appendix-E decomposition step: a ranking whose first two
candidates are `(c,d)` contributes exactly `value c - value d` to the
first-choice gap attached to `c`.
-/
theorem firstChoiceGapWeight_eq_sum_firstSecondWeight
    (value : Candidate n → ℝ) (c : Candidate n) :
    M.firstChoiceGapWeight value c =
      ∑ d : Candidate n, M.firstSecondWeight c d * (value c - value d) := by
  classical
  unfold firstChoiceGapWeight firstSecondWeight
  calc
    ∑ π : Ranking n,
        (if c = firstChoice π then
          mallowsWeight M.q M.center π * valueGap value π
        else
          0)
        = ∑ π : Ranking n,
            ∑ d : Candidate n,
              (if c = firstChoice π ∧ d = secondChoice π then
                mallowsWeight M.q M.center π * (value c - value d)
              else
                0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases hc : c = firstChoice π
          · have hraw : c = π 0 := by
              simpa [firstChoice] using hc
            have hsum :
                (∑ d : Candidate n,
                  if d = secondChoice π then
                    mallowsWeight M.q M.center π * (value c - value d)
                  else
                    0) =
                  mallowsWeight M.q M.center π *
                    (value c - value (secondChoice π)) := by
              simpa using
                (Finset.sum_ite_eq' Finset.univ (secondChoice π)
                  (fun d : Candidate n =>
                    mallowsWeight M.q M.center π * (value c - value d)))
            calc
              (if c = firstChoice π then
                  mallowsWeight M.q M.center π * valueGap value π
                else
                  0)
                  = mallowsWeight M.q M.center π *
                      (value c - value (secondChoice π)) := by
                    simp [hc, valueGap]
              _ = ∑ d : Candidate n,
                    (if c = firstChoice π ∧ d = secondChoice π then
                      mallowsWeight M.q M.center π * (value c - value d)
                    else
                      0) := by
                    rw [← hsum]
                    refine Finset.sum_congr rfl ?_
                    intro d _
                    by_cases hd : d = secondChoice π <;> simp [hc, hd]
          · have hraw : c ≠ π 0 := by
              simpa [firstChoice] using hc
            simp [hraw]
    _ = ∑ d : Candidate n,
          ∑ π : Ranking n,
            (if c = firstChoice π ∧ d = secondChoice π then
              mallowsWeight M.q M.center π * (value c - value d)
            else
              0) := by
          rw [Finset.sum_comm]
    _ = ∑ d : Candidate n,
          (∑ π : Ranking n,
            (if c = firstChoice π ∧ d = secondChoice π then
              mallowsWeight M.q M.center π
            else
              0)) * (value c - value d) := by
          refine Finset.sum_congr rfl ?_
          intro d _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = firstChoice π ∧ d = secondChoice π
          · simp [h]
          · have h' : ¬(c = π 0 ∧ d = π 1) := by
              intro hraw
              apply h
              exact ⟨by simpa [firstChoice] using hraw.1,
                by simpa [secondChoice] using hraw.2⟩
            simp [h']

/--
The denominator-cleared independent-reranking sum can be written as a sum over
ordered top-two candidate pairs.
-/
theorem independent_weight_sum_eq_pair_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c) =
      ∑ c : Candidate n, ∑ d : Candidate n,
        (M.partition - M.firstWeight c) *
          M.firstSecondWeight c d * (value c - value d) := by
  classical
  calc
    ∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c
        = ∑ c : Candidate n,
            (M.partition - M.firstWeight c) *
              (∑ d : Candidate n,
                M.firstSecondWeight c d * (value c - value d)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [M.firstChoiceGapWeight_eq_sum_firstSecondWeight value c]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
        (M.partition - M.firstWeight c) *
          (M.firstSecondWeight c d * (value c - value d)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.mul_sum]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
        (M.partition - M.firstWeight c) *
          M.firstSecondWeight c d * (value c - value d) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro d _
          ring

end MallowsSpec

namespace MallowsComparison

variable {n : ℕ} (C : MallowsComparison n)

end MallowsComparison

end Monoculture
