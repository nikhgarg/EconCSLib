import Monoculture.MallowsFiniteLemmas

open scoped BigOperators
open DecisionCore

namespace Monoculture

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/-- The ordered-pair summand in the cleared independent-reranking numerator. -/
noncomputable def independentPairTerm
    (value : Candidate n → ℝ) (c d : Candidate n) : ℝ :=
  (M.partition - M.firstWeight c) *
    M.firstSecondWeight c d * (value c - value d)

/--
The antisymmetrized top-two bracket for the unordered pair `{c,d}`.

Appendix E compares the `(c,d)` and `(d,c)` top-two fibers through exactly this
quantity after clearing Mallows denominators.
-/
noncomputable def independentPairBracket (c d : Candidate n) : ℝ :=
  (M.partition - M.firstWeight c) * M.firstSecondWeight c d -
    (M.partition - M.firstWeight d) * M.firstSecondWeight d c

@[simp] theorem independentPairTerm_apply
    (value : Candidate n → ℝ) (c d : Candidate n) :
    M.independentPairTerm value c d =
      (M.partition - M.firstWeight c) *
        M.firstSecondWeight c d * (value c - value d) := rfl

@[simp] theorem independentPairBracket_apply (c d : Candidate n) :
    M.independentPairBracket c d =
      (M.partition - M.firstWeight c) * M.firstSecondWeight c d -
        (M.partition - M.firstWeight d) * M.firstSecondWeight d c := rfl

/-- No ranking has the same candidate as both first and second choice. -/
@[simp] theorem firstSecondWeight_self (c : Candidate n) :
    M.firstSecondWeight c c = 0 := by
  classical
  unfold firstSecondWeight
  apply Finset.sum_eq_zero
  intro π _
  have hnot : ¬(c = firstChoice π ∧ c = secondChoice π) := by
    intro h
    have hfs : firstChoice π = secondChoice π := h.1.symm.trans h.2
    exact firstChoice_ne_secondChoice π hfs
  have hraw : ¬(c = π 0 ∧ c = π 1) := by
    intro h
    apply hnot
    exact ⟨by simpa [firstChoice] using h.1,
      by simpa [secondChoice] using h.2⟩
  simp [firstChoice, secondChoice, hraw]

/--
Pairing the ordered top-two events `(c,d)` and `(d,c)` produces a single
bracket times the value difference.
-/
theorem independentPairTerm_add_swap
    (value : Candidate n → ℝ) (c d : Candidate n) :
    M.independentPairTerm value c d + M.independentPairTerm value d c =
      M.independentPairBracket c d * (value c - value d) := by
  unfold independentPairTerm independentPairBracket
  ring

/--
If a pair is ordered by value and its Mallows pair bracket is nonnegative, then
the paired `(c,d)`/`(d,c)` contribution is nonnegative.
-/
theorem independentPairTerm_add_swap_nonneg
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hbracket : 0 ≤ M.independentPairBracket c d)
    (hvalue : value d ≤ value c) :
    0 ≤ M.independentPairTerm value c d + M.independentPairTerm value d c := by
  rw [M.independentPairTerm_add_swap value c d]
  exact mul_nonneg hbracket (sub_nonneg.mpr hvalue)

/--
If a pair is strictly ordered by value and its Mallows pair bracket is positive,
then the paired `(c,d)`/`(d,c)` contribution is positive.
-/
theorem independentPairTerm_add_swap_pos
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hbracket : 0 < M.independentPairBracket c d)
    (hvalue : value d < value c) :
    0 < M.independentPairTerm value c d + M.independentPairTerm value d c := by
  rw [M.independentPairTerm_add_swap value c d]
  exact mul_pos hbracket (sub_pos.mpr hvalue)

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
        M.independentPairTerm value c d := by
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
        M.independentPairTerm value c d := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro d _
          unfold independentPairTerm
          ring

end MallowsSpec

namespace MallowsComparison

variable {n : ℕ} (C : MallowsComparison n)

end MallowsComparison

end Monoculture
