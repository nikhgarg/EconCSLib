import KR21Monoculture.Basic
import EconCSLib.Foundations.Probability.FiniteExpectation
import EconCSLib.SocialChoice.Ranking.Payoff

open EconCSLib

namespace KR21Monoculture

/-- Expected value of the candidate hired by the firm that chooses first. -/
noncomputable def expectedFirstMoverUtility {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfExp μ (fun π => value (firstChoice π))

/-- Expected value of the candidate hired by the second mover when both firms use
the same realized ranking. -/
noncomputable def expectedSecondMoverShared {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfExp μ (fun π => value (secondChoice π))

/-- The real-valued probability that a draw from `μ` puts candidate `c` second. -/
noncomputable def secondChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  pmfProb μ (fun π => c = secondChoice π)

/-- Shared second-mover utility regrouped by the candidate in second position. -/
theorem expectedSecondMoverShared_eq_sum_secondChoiceProb {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverShared μ value =
      ∑ c : Candidate n, secondChoiceProb μ c * value c := by
  simpa [expectedSecondMoverShared, secondChoiceProb,
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverShared,
    EconCSLib.SocialChoice.Ranking.secondChoiceProb,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.expectedSecondMoverShared_eq_sum_secondChoiceProb
      μ value

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
  simpa [secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.secondMoverUtility_self value π

@[simp] theorem secondMoverUtility_eq_if {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) :
    secondMoverUtility value π σ =
      if firstChoice π = firstChoice σ then value (secondChoice π)
      else value (firstChoice π) := by
  simpa [secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.secondMoverUtility_eq_if value π σ

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
      value (firstChoice σ) + value (bestRemainingAfter π (firstChoice σ)) := by
  simpa [welfareOrdered, EconCSLib.SocialChoice.Ranking.welfareOrdered,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice] using
    EconCSLib.SocialChoice.Ranking.welfareOrdered_eq value π σ

@[simp] theorem welfareOrdered_self {n : ℕ} (value : Candidate n → ℝ)
    (π : Ranking n) :
    welfareOrdered value π π = value (firstChoice π) + value (secondChoice π) := by
  simpa [welfareOrdered, EconCSLib.SocialChoice.Ranking.welfareOrdered,
    secondMoverUtility, EconCSLib.SocialChoice.Ranking.secondMoverUtility,
    bestRemainingAfter, EconCSLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, EconCSLib.SocialChoice.Ranking.firstChoice,
    secondChoice, EconCSLib.SocialChoice.Ranking.secondChoice] using
    EconCSLib.SocialChoice.Ranking.welfareOrdered_self value π

end KR21Monoculture
