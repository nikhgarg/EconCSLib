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
- `finiteChernoffRate`
- `FiniteScoreGapLDPModel`
- `FiniteRatingLDPModel`
- `bernoulliKL`
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

/--
Finite-support Chernoff exponent for the left-tail event of a score with
positive mean, written in the source-paper form `- inf_z log E exp(z X)`.
The actual tail theorem is supplied by a paper-specific LDP/Chernoff
certificate; this definition fixes the reusable formula.
-/
def finiteChernoffRate (μ : PMF α) (score : α → ℝ) : ℝ :=
  -sInf (Set.range fun z : ℝ => finiteLogMGF μ score z)

theorem finiteRateFunction_ge_eval
    (μ : PMF α) (score : α → ℝ) (a z : ℝ)
    (hbdd : BddAbove (Set.range fun t : ℝ =>
      finiteLegendreValue μ score a t)) :
    finiteLegendreValue μ score a z ≤ finiteRateFunction μ score a := by
  exact le_csSup hbdd ⟨z, rfl⟩

theorem neg_finiteLogMGF_le_finiteChernoffRate
    (μ : PMF α) (score : α → ℝ) (z : ℝ)
    (hbdd : BddBelow (Set.range fun t : ℝ => finiteLogMGF μ score t)) :
    -finiteLogMGF μ score z ≤ finiteChernoffRate μ score := by
  dsimp [finiteChernoffRate]
  exact neg_le_neg (csInf_le hbdd ⟨z, rfl⟩)

/-- MGF of a finite signal's score gap. -/
def finiteScoreGapMGF (μ : PMF α) (hiScore loScore : α → ℝ)
    (z : ℝ) : ℝ :=
  finiteMGF μ (fun a => hiScore a - loScore a) z

/-- Log-MGF of a finite signal's score gap. -/
def finiteScoreGapLogMGF (μ : PMF α) (hiScore loScore : α → ℝ)
    (z : ℝ) : ℝ :=
  finiteLogMGF μ (fun a => hiScore a - loScore a) z

/--
Chernoff exponent for a finite score-gap law.  This is the source formula used
by finite positional-score election papers after choosing two candidates.
-/
def finiteScoreGapChernoffRate (μ : PMF α) (hiScore loScore : α → ℝ) :
    ℝ :=
  finiteChernoffRate μ (fun a => hiScore a - loScore a)

theorem finiteScoreGapMGF_pos (μ : PMF α) (hiScore loScore : α → ℝ)
    (z : ℝ) :
    0 < finiteScoreGapMGF μ hiScore loScore z :=
  finiteMGF_pos μ (fun a => hiScore a - loScore a) z

/--
MGF for a ternary score gap taking values `+1`, `0`, and `-1`, where `pUp`
is the probability of `+1` and `pDown` is the probability of `-1`.
This is the algebraic surface behind approval-voting pair rates.
-/
def ternaryGapMGF (pUp pDown z : ℝ) : ℝ :=
  pUp * Real.exp z + pDown * Real.exp (-z) + (1 - pUp - pDown)

/-- Log-MGF for the ternary gap law with values plus one, zero, and minus one. -/
def ternaryGapLogMGF (pUp pDown z : ℝ) : ℝ :=
  Real.log (ternaryGapMGF pUp pDown z)

/--
Closed-form Chernoff exponent for a ternary approval gap, in the paper form
`-log(2 sqrt(pUp pDown) + 1 - pUp - pDown)`.
-/
def ternaryGapClosedChernoffRate (pUp pDown : ℝ) : ℝ :=
  -Real.log (2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown)

/-- Bernoulli KL divergence, written with real arithmetic for source formulas. -/
def bernoulliKL (a b : ℝ) : ℝ :=
  a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))

/--
Two-population threshold rate used by binary-rating and rating-scale papers:
the two populations are sampled at rates `gHi`, `gLo`, have Bernoulli means
`tHi`, `tLo`, and are compared at threshold `a`.
-/
def twoBernoulliThresholdRate
    (gHi gLo tHi tLo a : ℝ) : ℝ :=
  gHi * bernoulliKL a tHi + gLo * bernoulliKL a tLo

/--
Finite signal model for pairwise score-gap LDP calculations, e.g. election
papers comparing the two candidates' per-voter score contributions under a
single finite law.
-/
structure FiniteScoreGapLDPModel (Signal : Type*) [Fintype Signal]
    [DecidableEq Signal] where
  law : PMF Signal
  hiScore : Signal → ℝ
  loScore : Signal → ℝ

namespace FiniteScoreGapLDPModel

variable {Signal : Type*} [Fintype Signal] [DecidableEq Signal]

def gapScore (M : FiniteScoreGapLDPModel Signal) (s : Signal) : ℝ :=
  M.hiScore s - M.loScore s

def mgf (M : FiniteScoreGapLDPModel Signal) (z : ℝ) : ℝ :=
  finiteMGF M.law M.gapScore z

def logMGF (M : FiniteScoreGapLDPModel Signal) (z : ℝ) : ℝ :=
  finiteLogMGF M.law M.gapScore z

def chernoffRate (M : FiniteScoreGapLDPModel Signal) : ℝ :=
  finiteChernoffRate M.law M.gapScore

theorem mgf_pos (M : FiniteScoreGapLDPModel Signal) (z : ℝ) :
    0 < M.mgf z :=
  finiteMGF_pos M.law M.gapScore z

theorem logMGF_zero (M : FiniteScoreGapLDPModel Signal) :
    M.logMGF 0 = 0 :=
  finiteLogMGF_zero M.law M.gapScore

end FiniteScoreGapLDPModel

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
