import EconCSLib.Foundations.Probability.FiniteExpectation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace EconCSLib
namespace Probability

noncomputable section

/-!
# Finite-Support Moment Generating Functions

Reusable log-MGF and Legendre-transform scaffolding for finite rating-scale
and finite signal laws.  This is the algebraic surface used by large-deviation
arguments in rating-system papers; the deep analytic large-deviation theorem is
kept in `LargeDeviations.lean` as a certificate boundary.

## Main declarations

- `finiteMGF`
- `finiteLogMGF`
- `finiteLegendreValue`
- `finiteRateFunction`
- `FiniteRatingLDPModel`
-/

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_pmf_toReal_pos (μ : PMF α) :
    ∃ a : α, 0 < (μ a).toReal := by
  by_contra h
  have hzero : ∀ a : α, (μ a).toReal = 0 := by
    intro a
    have hnot : ¬ 0 < (μ a).toReal := by
      intro ha
      exact h ⟨a, ha⟩
    exact le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
  have hsum := pmfToRealSum μ
  have hsum_zero : ∑ a : α, (μ a).toReal = 0 := by
    simp [hzero]
  linarith

/-- Finite moment-generating function for a real score under a finite PMF. -/
def finiteMGF (μ : PMF α) (score : α → ℝ) (z : ℝ) : ℝ :=
  ∑ a : α, (μ a).toReal * Real.exp (z * score a)

theorem finiteMGF_pos (μ : PMF α) (score : α → ℝ) (z : ℝ) :
    0 < finiteMGF μ score z := by
  rcases exists_pmf_toReal_pos μ with ⟨a, ha⟩
  dsimp [finiteMGF]
  exact Finset.sum_pos' (by
    intro b _
    exact mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) (by
    exact ⟨a, Finset.mem_univ a, mul_pos ha (Real.exp_pos _)⟩)

theorem finiteMGF_nonneg (μ : PMF α) (score : α → ℝ) (z : ℝ) :
    0 ≤ finiteMGF μ score z :=
  (finiteMGF_pos μ score z).le

theorem finiteMGF_zero (μ : PMF α) (score : α → ℝ) :
    finiteMGF μ score 0 = 1 := by
  dsimp [finiteMGF]
  simpa using pmfToRealSum μ

/-- Finite log moment-generating function. -/
def finiteLogMGF (μ : PMF α) (score : α → ℝ) (z : ℝ) : ℝ :=
  Real.log (finiteMGF μ score z)

theorem finiteLogMGF_zero (μ : PMF α) (score : α → ℝ) :
    finiteLogMGF μ score 0 = 0 := by
  rw [finiteLogMGF, finiteMGF_zero, Real.log_one]

theorem exp_finiteLogMGF (μ : PMF α) (score : α → ℝ) (z : ℝ) :
    Real.exp (finiteLogMGF μ score z) = finiteMGF μ score z := by
  rw [finiteLogMGF]
  exact Real.exp_log (finiteMGF_pos μ score z)

theorem finiteMGF_const_score (μ : PMF α) (c z : ℝ) :
    finiteMGF μ (fun _ => c) z = Real.exp (z * c) := by
  dsimp [finiteMGF]
  rw [← Finset.sum_mul]
  rw [pmfToRealSum]
  ring

theorem finiteLogMGF_const_score (μ : PMF α) (c z : ℝ) :
    finiteLogMGF μ (fun _ => c) z = z * c := by
  rw [finiteLogMGF, finiteMGF_const_score, Real.log_exp]

/-- Legendre-transform objective at a fixed dual parameter `z`. -/
def finiteLegendreValue (μ : PMF α) (score : α → ℝ)
    (a z : ℝ) : ℝ :=
  z * a - finiteLogMGF μ score z

/--
Finite-support Cramer-style rate function written as the supremum of the
Legendre objective.
-/
def finiteRateFunction (μ : PMF α) (score : α → ℝ)
    (a : ℝ) : ℝ :=
  sSup (Set.range fun z : ℝ => finiteLegendreValue μ score a z)

theorem finiteRateFunction_ge_eval
    (μ : PMF α) (score : α → ℝ) (a z : ℝ)
    (hbdd : BddAbove (Set.range fun t : ℝ =>
      finiteLegendreValue μ score a t)) :
    finiteLegendreValue μ score a z ≤ finiteRateFunction μ score a := by
  exact le_csSup hbdd ⟨z, rfl⟩

/--
Finite rating-scale model for large-deviation calculations.  `typeLaw θ` is
the rating distribution for a seller/item of latent type `θ`, and `score`
assigns a real-valued score to each rating category.
-/
structure FiniteRatingLDPModel (θ Rating : Type*) [Fintype Rating]
    [DecidableEq Rating] where
  typeLaw : θ → PMF Rating
  score : Rating → ℝ

namespace FiniteRatingLDPModel

variable {θ Rating : Type*} [Fintype Rating] [DecidableEq Rating]

def mgf (M : FiniteRatingLDPModel θ Rating) (t : θ) (z : ℝ) : ℝ :=
  finiteMGF (M.typeLaw t) M.score z

def logMGF (M : FiniteRatingLDPModel θ Rating) (t : θ) (z : ℝ) : ℝ :=
  finiteLogMGF (M.typeLaw t) M.score z

def rateFunction (M : FiniteRatingLDPModel θ Rating)
    (t : θ) (a : ℝ) : ℝ :=
  finiteRateFunction (M.typeLaw t) M.score a

def pairwiseRateObjective (M : FiniteRatingLDPModel θ Rating)
    (sampleRate : θ → ℝ) (hi lo : θ) (a : ℝ) : ℝ :=
  sampleRate hi * M.rateFunction hi a +
    sampleRate lo * M.rateFunction lo a

theorem mgf_pos (M : FiniteRatingLDPModel θ Rating)
    (t : θ) (z : ℝ) :
    0 < M.mgf t z :=
  finiteMGF_pos (M.typeLaw t) M.score z

theorem logMGF_zero (M : FiniteRatingLDPModel θ Rating)
    (t : θ) :
    M.logMGF t 0 = 0 :=
  finiteLogMGF_zero (M.typeLaw t) M.score

theorem exp_logMGF (M : FiniteRatingLDPModel θ Rating)
    (t : θ) (z : ℝ) :
    Real.exp (M.logMGF t z) = M.mgf t z :=
  exp_finiteLogMGF (M.typeLaw t) M.score z

end FiniteRatingLDPModel

end

end Probability
end EconCSLib
