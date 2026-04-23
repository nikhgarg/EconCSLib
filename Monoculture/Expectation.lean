import Monoculture.Basic
import DecisionCore

open DecisionCore

namespace Monoculture

/-- Expected value of the candidate hired by the firm that chooses first. -/
noncomputable def expectedFirstMoverUtility {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfExp μ (fun π => value (firstChoice π))

/-- Expected value of the candidate hired by the second mover when both firms use
the same realized ranking. -/
noncomputable def expectedSecondMoverShared {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfExp μ (fun π => value (secondChoice π))

/-- Pointwise utility to the second mover when the first mover uses `σ`
and the second mover uses `π`. -/
def secondMoverUtility {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) : ℝ :=
  value (bestRemainingAfter π (firstChoice σ))

/-- Expected utility to the second mover when the second mover draws `π` from `μ₂`
and the first mover draws `σ` from `μ₁`. -/
noncomputable def expectedSecondMoverIndependent {n : ℕ}
    (μ₂ μ₁ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ₂ μ₁ (fun π σ => secondMoverUtility value π σ)

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

/-- Social welfare in the ordered version of the game where the `σ`-firm chooses
first and the `π`-firm chooses second. -/
def welfareOrdered {n : ℕ} (value : Candidate n → ℝ) (π σ : Ranking n) : ℝ :=
  value (firstChoice σ) + secondMoverUtility value π σ

/-- Social welfare when the first mover uses `μ₁` and the second mover uses `μ₂`. -/
noncomputable def expectedWelfareOrdered {n : ℕ}
    (μ₂ μ₁ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ₂ μ₁ (fun π σ => welfareOrdered value π σ)

@[simp] theorem welfareOrdered_eq {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) :
    welfareOrdered value π σ =
      value (firstChoice σ) + value (bestRemainingAfter π (firstChoice σ)) := rfl

@[simp] theorem welfareOrdered_self {n : ℕ} (value : Candidate n → ℝ)
    (π : Ranking n) :
    welfareOrdered value π π = value (firstChoice π) + value (secondChoice π) := by
  simp [welfareOrdered, secondMoverUtility, bestRemainingAfter]

end Monoculture
