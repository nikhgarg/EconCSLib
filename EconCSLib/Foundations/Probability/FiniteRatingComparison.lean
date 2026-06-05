import EconCSLib.Foundations.Probability.FiniteSupportMGF
import EconCSLib.Foundations.Probability.FiniteTypeLogMass
import EconCSLib.Foundations.Probability.IndependentProduct
import EconCSLib.Foundations.Probability.IIDLargeDeviations
import EconCSLib.Foundations.Probability.FiniteRankingEvents
import EconCSLib.Foundations.Probability.LargeDeviations
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite Rating Comparison Infrastructure

Reusable finite-rating large-deviation and pairwise-comparison infrastructure
extracted from rating-system formalizations. The module provides source-facing
log-MGF/rate wrappers, support-safe pairwise threshold rates, finite tilted
score means, two-sample comparison probabilities, floor-count bridges, and
finite pairwise LDP certificate constructors.
-/

open scoped BigOperators
open Filter

namespace EconCSLib
namespace Probability

noncomputable section

/-- Source log-MGF `Λ(z | θ) = log sum_y rho(θ,y|Y) exp(z phi(y))`. -/
def sourceLogMGF {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller) (z : ℝ) : ℝ :=
  M.logMGF θ z

/-- Source rate function `I(a | θ) = sup_z {z a - Λ(z | θ)}`. -/
def sourceRateFunction {Seller Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller) (a : ℝ) : ℝ :=
  M.rateFunction θ a

/--
Extended source rate function. Thresholds outside the finite score hull have
rate `⊤`, avoiding the real-valued `sSup` boundary that appears in unrestricted
Legendre transforms.
-/
def sourceRateFunctionTop {Seller Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller) (a : ℝ) :
    WithTop ℝ :=
  M.rateFunctionTop θ a

/--
If the finite source log-MGF has derivative `a` at `z0`, then the extended
source rate at threshold `a` is finite and attained at `z0`.
-/
theorem sourceRateFunctionTop_eq_eval_of_logMGF_hasDerivAt
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller) (a z0 : ℝ)
    (hderiv : HasDerivAt (fun z : ℝ => M.logMGF θ z) a z0) :
    sourceRateFunctionTop M θ a =
      (finiteLegendreValue (M.typeLaw θ) M.score a z0 : WithTop ℝ) := by
  simpa [sourceRateFunctionTop] using
    M.rateFunctionTop_eq_eval_of_logMGF_hasDerivAt θ a z0 hderiv

/--
A seller type's finite rating law places positive mass on both sides of a
threshold score. This is the nondegeneracy condition used by the finite
empirical-type Cramer lower bound.
-/
def ratingLawStraddlesThreshold
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller) (a : ℝ) : Prop :=
  M.straddlesThreshold θ a

/--
A finite log-MGF derivative is the expected score under the exponential tilt.
Therefore, if the finite rating scale has positive mass at a bottom and top
score for this seller type, the derivative threshold lies strictly between
those scores and the rating law straddles it.
-/
theorem ratingLawStraddlesThreshold_of_logMGF_hasDerivAt_of_score_bounds
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller)
    {a z0 : ℝ}
    (hderiv : HasDerivAt (fun z : ℝ => M.logMGF θ z) a z0)
    {rLow rHigh : Rating}
    (hmass_low : 0 < (M.typeLaw θ rLow).toReal)
    (hmass_high : 0 < (M.typeLaw θ rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_lt : M.score rLow < M.score rHigh) :
    ratingLawStraddlesThreshold M θ a := by
  have hderiv_finite :
      HasDerivAt
        (fun z : ℝ => finiteLogMGF (M.typeLaw θ) M.score z) a z0 := by
    simpa [FiniteRatingLDPModel.logMGF] using hderiv
  have hderiv_formula := finiteLogMGF_hasDerivAt (M.typeLaw θ) M.score z0
  have ha_formula :
      ((∑ r : Rating,
          (M.typeLaw θ r).toReal *
            (M.score r * Real.exp (z0 * M.score r))) /
        finiteMGF (M.typeLaw θ) M.score z0) = a :=
    hderiv_formula.unique hderiv_finite
  have ha_tilt :
      a =
        EconCSLib.pmfExp
          (finiteExponentialTilt (M.typeLaw θ) M.score z0) M.score := by
    rw [pmfExp_finiteExponentialTilt_eq]
    exact ha_formula.symm
  have htilt_low :
      0 <
        (finiteExponentialTilt (M.typeLaw θ) M.score z0 rLow).toReal :=
    (finiteExponentialTilt_apply_toReal_pos_iff
      (M.typeLaw θ) M.score z0 rLow).2 hmass_low
  have htilt_high :
      0 <
        (finiteExponentialTilt (M.typeLaw θ) M.score z0 rHigh).toReal :=
    (finiteExponentialTilt_apply_toReal_pos_iff
      (M.typeLaw θ) M.score z0 rHigh).2 hmass_high
  have hlow_lt_a : M.score rLow < a := by
    rw [ha_tilt]
    exact
      EconCSLib.cutoff_lt_pmfExp_of_all_ge_exists_gt
        (finiteExponentialTilt (M.typeLaw θ) M.score z0)
        M.score (M.score rLow)
        hscore_low_le
        ⟨rHigh, htilt_high, hscore_lt⟩
  have ha_lt_high : a < M.score rHigh := by
    rw [ha_tilt]
    exact
      EconCSLib.pmfExp_lt_of_forall_le_exists_lt
        (finiteExponentialTilt (M.typeLaw θ) M.score z0)
        M.score (M.score rHigh)
        hscore_le_high
        ⟨rLow, htilt_low, hscore_lt⟩
  exact ⟨⟨rLow, hmass_low, hlow_lt_a⟩,
    ⟨rHigh, hmass_high, ha_lt_high⟩⟩

/--
Appendix pairwise threshold rate for comparing two seller types.  This is the
right-hand side of Lemma C.1 / Lemma C.2 before the analytic LDP certificate is
supplied.
-/
def pairwiseSellerThresholdRate {Seller Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) : ℝ :=
  M.pairwiseThresholdRate sampleRate hi lo

/--
Pairwise regularity package for the paper's threshold-rate step.  It records
exactly the remaining source-side data needed to turn every finite floor-count
pairwise comparison into an exact exponential-rate certificate at the real
source threshold rate.
-/
structure PairwiseThresholdRateRegularity
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) where
  threshold : Pair → ℝ
  dual : Pair → ℝ
  dual_nonpos : ∀ p : Pair, dual p ≤ 0
  deriv_hi :
    ∀ p : Pair,
      HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (threshold p)
        (dual p * (sampleRate (pairHi p))⁻¹)
  deriv_lo :
    ∀ p : Pair,
      HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (threshold p)
        (-(dual p * (sampleRate (pairLo p))⁻¹))
  threshold_rate_eq :
    ∀ p : Pair,
      M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p)
          (threshold p) =
        pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)
  straddles_hi :
    ∀ p : Pair, ratingLawStraddlesThreshold M (pairHi p) (threshold p)
  straddles_lo :
    ∀ p : Pair, ratingLawStraddlesThreshold M (pairLo p) (threshold p)

/--
Extended pairwise source objective. This is the `WithTop` version of
`FiniteRatingLDPModel.pairwiseRateObjective`; out-of-support one-population
threshold rates contribute `⊤` instead of relying on a real-valued supremum.
-/
def pairwiseRateObjectiveTop {Seller Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (a : ℝ) : WithTop ℝ :=
  M.pairwiseRateObjectiveTop sampleRate hi lo a

/--
Extended Appendix pairwise threshold rate. This is the support-safe version of
`pairwiseSellerThresholdRate`: thresholds outside the finite score hull carry
rate `⊤` instead of forcing the Legendre supremum into a real number.
-/
noncomputable def pairwiseSellerThresholdRateTop
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) : WithTop ℝ :=
  M.pairwiseThresholdRateTop sampleRate hi lo

/--
Two-population Chernoff dual log-MGF for real-valued sample rates.  Its
stationary points are the source-side common-dual witnesses used in Appendix C.
-/
def pairwiseDualLogMGF {Seller Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (z : ℝ) : ℝ :=
  sampleRate hi * M.logMGF hi (z * (sampleRate hi)⁻¹) +
    sampleRate lo * M.logMGF lo (-(z * (sampleRate lo)⁻¹))

/-- Mean score under the finite exponential tilt at dual parameter `z`. -/
def finiteTiltedScoreMean {Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (μ : PMF Rating) (score : Rating → ℝ) (z : ℝ) : ℝ :=
  EconCSLib.pmfExp (finiteExponentialTilt μ score z) score

/--
The tilted score mean is continuous in the dual parameter for finite support.
-/
theorem finiteTiltedScoreMean_continuous
    {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (μ : PMF Rating) (score : Rating → ℝ) :
    Continuous (fun z : ℝ => finiteTiltedScoreMean μ score z) := by
  have hrepr :
      (fun z : ℝ => finiteTiltedScoreMean μ score z) =
        fun z : ℝ =>
          (∑ r : Rating,
            (μ r).toReal * (score r * Real.exp (z * score r))) /
            finiteMGF μ score z := by
    funext z
    simp [finiteTiltedScoreMean, pmfExp_finiteExponentialTilt_eq]
  rw [hrepr]
  have hnum :
      Continuous (fun z : ℝ =>
        ∑ r : Rating,
          (μ r).toReal * (score r * Real.exp (z * score r))) :=
    continuous_finset_sum Finset.univ (fun r _ =>
      continuous_const.mul
        (continuous_const.mul
          (Real.continuous_exp.comp
            (continuous_id.mul continuous_const))))
  exact hnum.div (finiteMGF_continuous μ score)
    (fun z => (finiteMGF_pos μ score z).ne')

/-- At dual zero, the finite tilted score mean is the ordinary score mean. -/
theorem finiteTiltedScoreMean_zero
    {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (μ : PMF Rating) (score : Rating → ℝ) :
    finiteTiltedScoreMean μ score 0 = EconCSLib.pmfExp μ score := by
  rw [finiteTiltedScoreMean, pmfExp_finiteExponentialTilt_eq]
  simp [finiteMGF_zero, EconCSLib.pmfExp, mul_comm]

/--
Tilting by a score shifted down by a constant only shifts the tilted mean by
that constant.
-/
theorem finiteTiltedScoreMean_sub_const
    {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (μ : PMF Rating) (score : Rating → ℝ) (c z : ℝ) :
    finiteTiltedScoreMean μ (fun r : Rating => score r - c) z =
      finiteTiltedScoreMean μ score z - c := by
  rw [finiteTiltedScoreMean, finiteTiltedScoreMean]
  rw [pmfExp_finiteExponentialTilt_eq,
    pmfExp_finiteExponentialTilt_eq]
  rw [finiteMGF_sub_const]
  have hnum :
      (∑ r : Rating,
        (μ r).toReal *
          ((score r - c) * Real.exp (z * (score r - c)))) =
        Real.exp (-(z * c)) *
            (∑ r : Rating,
              (μ r).toReal * (score r * Real.exp (z * score r))) -
          c * Real.exp (-(z * c)) * finiteMGF μ score z := by
    unfold finiteMGF
    calc
      ∑ r : Rating,
          (μ r).toReal *
            ((score r - c) * Real.exp (z * (score r - c)))
          =
          ∑ r : Rating,
            (Real.exp (-(z * c)) *
                  ((μ r).toReal * (score r * Real.exp (z * score r))) -
                c * Real.exp (-(z * c)) *
                  ((μ r).toReal * Real.exp (z * score r))) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [show z * (score r - c) = -(z * c) + z * score r by ring]
            rw [Real.exp_add]
            ring
      _ =
          Real.exp (-(z * c)) *
              (∑ r : Rating,
                (μ r).toReal * (score r * Real.exp (z * score r))) -
            c * Real.exp (-(z * c)) *
              (∑ r : Rating, (μ r).toReal * Real.exp (z * score r)) := by
            rw [Finset.sum_sub_distrib]
            rw [Finset.mul_sum, Finset.mul_sum]
  have hden_ne : finiteMGF μ score z ≠ 0 :=
    (finiteMGF_pos μ score z).ne'
  have hexp_ne : Real.exp (-(z * c)) ≠ 0 :=
    (Real.exp_pos _).ne'
  rw [hnum]
  field_simp [hden_ne, hexp_ne]

/-- For finite support, the tilted score mean is monotone in the dual. -/
theorem finiteTiltedScoreMean_mono
    {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (μ : PMF Rating) (score : Rating → ℝ) :
    Monotone (fun z : ℝ => finiteTiltedScoreMean μ score z) := by
  intro x y hxy
  have hx :
      HasDerivAt (fun z : ℝ => finiteLogMGF μ score z)
        (finiteTiltedScoreMean μ score x) x := by
    have hformula := finiteLogMGF_hasDerivAt μ score x
    rw [finiteTiltedScoreMean, pmfExp_finiteExponentialTilt_eq]
    exact hformula
  have hy :
      HasDerivAt (fun z : ℝ => finiteLogMGF μ score z)
        (finiteTiltedScoreMean μ score y) y := by
    have hformula := finiteLogMGF_hasDerivAt μ score y
    rw [finiteTiltedScoreMean, pmfExp_finiteExponentialTilt_eq]
    exact hformula
  exact convex_hasDerivAt_mono_of_le
    (finiteLogMGF_convex μ score) hxy hx hy

/--
Finite support at a bottom score gives a nonpositive tilt whose score mean is
within any positive error of that bottom score.
-/
theorem exists_nonpos_finiteTiltedScoreMean_le_bottom_add
    {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (μ : PMF Rating) (score : Rating → ℝ) (rLow : Rating)
    (hmassLow : 0 < (μ rLow).toReal)
    (hscore_low_le : ∀ r : Rating, score rLow ≤ score r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℝ, z ≤ 0 ∧
      finiteTiltedScoreMean μ score z ≤ score rLow + ε := by
  classical
  let shift : Rating → ℝ := fun r => score r - score rLow
  let tail : ℝ → ℝ :=
    fun z =>
      ∑ r : Rating,
        (μ r).toReal * (shift r * Real.exp (z * shift r))
  have hshift_nonneg : ∀ r : Rating, 0 ≤ shift r := by
    intro r
    exact sub_nonneg.mpr (hscore_low_le r)
  have htail_tendsto : Filter.Tendsto tail Filter.atBot (nhds 0) := by
    have hsum :
        Filter.Tendsto
          (fun z : ℝ =>
            ∑ r : Rating,
              (μ r).toReal * (shift r * Real.exp (z * shift r)))
          Filter.atBot (nhds (∑ _r : Rating, (0 : ℝ))) := by
      refine tendsto_finset_sum (Finset.univ : Finset Rating) ?_
      intro r _hr
      show Filter.Tendsto
        (fun z : ℝ =>
          (μ r).toReal * (shift r * Real.exp (z * shift r)))
        Filter.atBot (nhds 0)
      by_cases hzero : shift r = 0
      · have hterm_zero :
            (fun z : ℝ =>
              (μ r).toReal * (shift r * Real.exp (z * shift r))) =
              fun _ : ℝ => 0 := by
            funext z
            simp [hzero]
        rw [hterm_zero]
        exact
          (tendsto_const_nhds (x := (0 : ℝ)) :
            Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
              Filter.atBot (nhds 0))
      · have hshift_pos : 0 < shift r :=
          lt_of_le_of_ne (hshift_nonneg r) (Ne.symm hzero)
        have harg :
            Filter.Tendsto (fun z : ℝ => z * shift r)
              Filter.atBot Filter.atBot :=
          Filter.tendsto_id.atBot_mul_const hshift_pos
        have hexp :
            Filter.Tendsto (fun z : ℝ => Real.exp (z * shift r))
              Filter.atBot (nhds 0) :=
          Real.tendsto_exp_atBot.comp harg
        have hterm :=
          hexp.const_mul ((μ r).toReal * shift r)
        simpa [mul_assoc, mul_comm, mul_left_comm] using hterm
    simpa [tail] using hsum
  have hεmass : 0 < ε * (μ rLow).toReal :=
    mul_pos hε hmassLow
  have htail_small :
      ∀ᶠ z in Filter.atBot, tail z < ε * (μ rLow).toReal :=
    htail_tendsto.eventually_lt_const hεmass
  have hz_nonpos_event :
      Filter.Eventually (fun z : ℝ => z ≤ 0) Filter.atBot :=
    Filter.eventually_le_atBot (0 : ℝ)
  rcases (htail_small.and hz_nonpos_event).exists with
    ⟨z, htail_z, hz_nonpos⟩
  refine ⟨z, hz_nonpos, ?_⟩
  have htail_nonneg : 0 ≤ tail z := by
    dsimp [tail]
    refine Finset.sum_nonneg ?_
    intro r _hr
    exact mul_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (hshift_nonneg r) (Real.exp_pos _).le)
  have hshift_mean_bound :
      finiteTiltedScoreMean μ shift z ≤ tail z / (μ rLow).toReal := by
    have hrepr :
        finiteTiltedScoreMean μ shift z =
          tail z / finiteMGF μ shift z := by
      rw [finiteTiltedScoreMean, pmfExp_finiteExponentialTilt_eq]
    have hden_lower :
        (μ rLow).toReal ≤ finiteMGF μ shift z := by
      have hatom := finiteMGF_ge_atom μ shift z rLow
      simpa [shift] using hatom
    rw [hrepr]
    exact div_le_div_of_nonneg_left htail_nonneg hmassLow hden_lower
  have htail_div_lt : tail z / (μ rLow).toReal < ε := by
    rw [div_lt_iff₀ hmassLow]
    simpa [mul_comm] using htail_z
  have hshift_lt : finiteTiltedScoreMean μ shift z < ε :=
    lt_of_le_of_lt hshift_mean_bound htail_div_lt
  have hshift_eq :
      finiteTiltedScoreMean μ shift z =
        finiteTiltedScoreMean μ score z - score rLow := by
    simpa [shift] using
      finiteTiltedScoreMean_sub_const μ score (score rLow) z
  linarith

/-- Tilting the negated score at `z` is the same as tilting the original score at `-z`. -/
theorem finiteTiltedScoreMean_neg_score
    {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (μ : PMF Rating) (score : Rating → ℝ) (z : ℝ) :
    finiteTiltedScoreMean μ (fun r => -score r) z =
      -finiteTiltedScoreMean μ score (-z) := by
  rw [finiteTiltedScoreMean, finiteTiltedScoreMean,
    pmfExp_finiteExponentialTilt_eq, pmfExp_finiteExponentialTilt_eq]
  have hden :
      finiteMGF μ (fun r : Rating => -score r) z =
        finiteMGF μ score (-z) := by
    unfold finiteMGF
    refine Finset.sum_congr rfl ?_
    intro r _hr
    ring_nf
  have hnum :
      (∑ r : Rating,
        (μ r).toReal *
          ((-score r) * Real.exp (z * (-score r)))) =
        -∑ r : Rating,
          (μ r).toReal *
            (score r * Real.exp ((-z) * score r)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    rw [show z * (-score r) = (-z) * score r by ring]
    ring
  rw [hden, hnum]
  ring

/--
Finite support at a top score gives a nonnegative tilt whose score mean is
within any positive error of that top score.
-/
theorem exists_nonneg_top_sub_le_finiteTiltedScoreMean
    {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (μ : PMF Rating) (score : Rating → ℝ) (rHigh : Rating)
    (hmassHigh : 0 < (μ rHigh).toReal)
    (hscore_le_high : ∀ r : Rating, score r ≤ score rHigh)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℝ, 0 ≤ z ∧
      score rHigh - ε ≤ finiteTiltedScoreMean μ score z := by
  rcases
      exists_nonpos_finiteTiltedScoreMean_le_bottom_add
        μ (fun r : Rating => -score r) rHigh hmassHigh
        (by
          intro r
          exact neg_le_neg (hscore_le_high r))
        hε with
    ⟨z, hz_nonpos, hz_mean⟩
  refine ⟨-z, neg_nonneg.mpr hz_nonpos, ?_⟩
  have hneg :=
    finiteTiltedScoreMean_neg_score μ score z
  linarith

/--
Gap between high and low tilted score means along the real-rate pairwise dual
path used by the source Chernoff objective.
-/
def pairwiseTiltedScoreMeanGap {Seller Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (z : ℝ) : ℝ :=
  finiteTiltedScoreMean (M.typeLaw hi) M.score
      (z * (sampleRate hi)⁻¹) -
    finiteTiltedScoreMean (M.typeLaw lo) M.score
      (-(z * (sampleRate lo)⁻¹))

/-- The pairwise tilted score-mean gap is continuous in the common dual. -/
theorem pairwiseTiltedScoreMeanGap_continuous
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) :
    Continuous (fun z : ℝ =>
      pairwiseTiltedScoreMeanGap M sampleRate hi lo z) := by
  unfold pairwiseTiltedScoreMeanGap
  exact
    ((finiteTiltedScoreMean_continuous (M.typeLaw hi) M.score).comp
        (continuous_id.mul continuous_const)).sub
      ((finiteTiltedScoreMean_continuous (M.typeLaw lo) M.score).comp
        ((continuous_id.mul continuous_const).neg))

/--
Along the common pairwise dual, the high tilted mean moves up and the low
tilted mean moves down as the dual increases, so their gap is monotone.
-/
theorem pairwiseTiltedScoreMeanGap_mono
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo) :
    Monotone (fun z : ℝ =>
      pairwiseTiltedScoreMeanGap M sampleRate hi lo z) := by
  intro x y hxy
  have hhi_arg :
      x * (sampleRate hi)⁻¹ ≤ y * (sampleRate hi)⁻¹ :=
    mul_le_mul_of_nonneg_right hxy (inv_nonneg.mpr hgHi.le)
  have hlo_arg :
      -(y * (sampleRate lo)⁻¹) ≤ -(x * (sampleRate lo)⁻¹) := by
    exact neg_le_neg
      (mul_le_mul_of_nonneg_right hxy (inv_nonneg.mpr hgLo.le))
  have hhi :=
    finiteTiltedScoreMean_mono (M.typeLaw hi) M.score hhi_arg
  have hlo :=
    finiteTiltedScoreMean_mono (M.typeLaw lo) M.score hlo_arg
  dsimp [pairwiseTiltedScoreMeanGap]
  linarith

/-- At dual zero, the tilted mean gap is the ordinary expected-score gap. -/
theorem pairwiseTiltedScoreMeanGap_zero
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) :
    pairwiseTiltedScoreMeanGap M sampleRate hi lo 0 =
      EconCSLib.pmfExp (M.typeLaw hi) M.score -
        EconCSLib.pmfExp (M.typeLaw lo) M.score := by
  simp [pairwiseTiltedScoreMeanGap, finiteTiltedScoreMean_zero]

/--
At dual parameter zero, the derivative of the real-rate pairwise Chernoff
log-MGF is exactly the high-type mean score minus the low-type mean score.
-/
theorem pairwiseDualLogMGF_hasDerivAt_zero_at_zero
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo) :
    HasDerivAt
      (fun t : ℝ => pairwiseDualLogMGF M sampleRate hi lo t)
      (EconCSLib.pmfExp (M.typeLaw hi) M.score -
        EconCSLib.pmfExp (M.typeLaw lo) M.score) 0 := by
  have hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t)
        (EconCSLib.pmfExp (M.typeLaw hi) M.score) 0 := by
    simpa [FiniteRatingLDPModel.logMGF] using
      finiteLogMGF_hasDerivAt_zero (M.typeLaw hi) M.score
  have hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t)
        (EconCSLib.pmfExp (M.typeLaw lo) M.score) 0 := by
    simpa [FiniteRatingLDPModel.logMGF] using
      finiteLogMGF_hasDerivAt_zero (M.typeLaw lo) M.score
  have hhi_inner :
      HasDerivAt (fun t : ℝ => t * (sampleRate hi)⁻¹)
        ((sampleRate hi)⁻¹) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const ((sampleRate hi)⁻¹)
  have hlo_inner :
      HasDerivAt (fun t : ℝ => -(t * (sampleRate lo)⁻¹))
        (-(sampleRate lo)⁻¹) 0 := by
    simpa using
      ((hasDerivAt_id (0 : ℝ)).mul_const ((sampleRate lo)⁻¹)).neg
  have hderiv_hi_scaled :
      HasDerivAt (fun t : ℝ => M.logMGF hi t)
        (EconCSLib.pmfExp (M.typeLaw hi) M.score)
        (0 * (sampleRate hi)⁻¹) := by
    simpa using hderiv_hi
  have hderiv_lo_scaled :
      HasDerivAt (fun t : ℝ => M.logMGF lo t)
        (EconCSLib.pmfExp (M.typeLaw lo) M.score)
        (-(0 * (sampleRate lo)⁻¹)) := by
    simpa using hderiv_lo
  have hhi_comp :
      HasDerivAt
        (fun t : ℝ => M.logMGF hi (t * (sampleRate hi)⁻¹))
        (EconCSLib.pmfExp (M.typeLaw hi) M.score *
          (sampleRate hi)⁻¹) 0 :=
    hderiv_hi_scaled.comp 0 hhi_inner
  have hlo_comp :
      HasDerivAt
        (fun t : ℝ => M.logMGF lo (-(t * (sampleRate lo)⁻¹)))
        (EconCSLib.pmfExp (M.typeLaw lo) M.score *
          (-(sampleRate lo)⁻¹)) 0 :=
    hderiv_lo_scaled.comp 0 hlo_inner
  have hsum :
      HasDerivAt
        (fun t : ℝ =>
          sampleRate hi * M.logMGF hi (t * (sampleRate hi)⁻¹) +
            sampleRate lo * M.logMGF lo (-(t * (sampleRate lo)⁻¹)))
        (sampleRate hi *
            (EconCSLib.pmfExp (M.typeLaw hi) M.score *
              (sampleRate hi)⁻¹) +
          sampleRate lo *
            (EconCSLib.pmfExp (M.typeLaw lo) M.score *
              (-(sampleRate lo)⁻¹))) 0 :=
    (hhi_comp.const_mul (sampleRate hi)).add
      (hlo_comp.const_mul (sampleRate lo))
  have hsum_dual :
      HasDerivAt
        (fun t : ℝ => pairwiseDualLogMGF M sampleRate hi lo t)
        (sampleRate hi *
            (EconCSLib.pmfExp (M.typeLaw hi) M.score *
              (sampleRate hi)⁻¹) +
          sampleRate lo *
            (EconCSLib.pmfExp (M.typeLaw lo) M.score *
              (-(sampleRate lo)⁻¹))) 0 := by
    simpa [pairwiseDualLogMGF] using hsum
  convert hsum_dual using 1
  field_simp [ne_of_gt hgHi, ne_of_gt hgLo]
  ring

/--
Derivative formula for the real-rate pairwise Chernoff log-MGF.  At dual
parameter `z`, the derivative is the difference between the high and low
score means under their corresponding exponential tilts.
-/
theorem pairwiseDualLogMGF_hasDerivAt
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo) (z : ℝ) :
    HasDerivAt
      (fun t : ℝ => pairwiseDualLogMGF M sampleRate hi lo t)
      (EconCSLib.pmfExp
          (finiteExponentialTilt (M.typeLaw hi) M.score
            (z * (sampleRate hi)⁻¹)) M.score -
        EconCSLib.pmfExp
          (finiteExponentialTilt (M.typeLaw lo) M.score
            (-(z * (sampleRate lo)⁻¹))) M.score) z := by
  let zHi : ℝ := z * (sampleRate hi)⁻¹
  let zLo : ℝ := -(z * (sampleRate lo)⁻¹)
  have hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t)
        (EconCSLib.pmfExp
          (finiteExponentialTilt (M.typeLaw hi) M.score zHi) M.score)
        zHi := by
    have hformula := finiteLogMGF_hasDerivAt (M.typeLaw hi) M.score zHi
    rw [pmfExp_finiteExponentialTilt_eq]
    simpa [FiniteRatingLDPModel.logMGF] using hformula
  have hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t)
        (EconCSLib.pmfExp
          (finiteExponentialTilt (M.typeLaw lo) M.score zLo) M.score)
        zLo := by
    have hformula := finiteLogMGF_hasDerivAt (M.typeLaw lo) M.score zLo
    rw [pmfExp_finiteExponentialTilt_eq]
    simpa [FiniteRatingLDPModel.logMGF] using hformula
  have hhi_inner :
      HasDerivAt (fun t : ℝ => t * (sampleRate hi)⁻¹)
        ((sampleRate hi)⁻¹) z := by
    simpa using (hasDerivAt_id z).mul_const ((sampleRate hi)⁻¹)
  have hlo_inner :
      HasDerivAt (fun t : ℝ => -(t * (sampleRate lo)⁻¹))
        (-(sampleRate lo)⁻¹) z := by
    simpa using ((hasDerivAt_id z).mul_const ((sampleRate lo)⁻¹)).neg
  have hhi_comp :
      HasDerivAt
        (fun t : ℝ => M.logMGF hi (t * (sampleRate hi)⁻¹))
        (EconCSLib.pmfExp
            (finiteExponentialTilt (M.typeLaw hi) M.score zHi) M.score *
          (sampleRate hi)⁻¹) z :=
    hderiv_hi.comp z hhi_inner
  have hlo_comp :
      HasDerivAt
        (fun t : ℝ => M.logMGF lo (-(t * (sampleRate lo)⁻¹)))
        (EconCSLib.pmfExp
            (finiteExponentialTilt (M.typeLaw lo) M.score zLo) M.score *
          (-(sampleRate lo)⁻¹)) z :=
    hderiv_lo.comp z hlo_inner
  have hsum :
      HasDerivAt
        (fun t : ℝ =>
          sampleRate hi * M.logMGF hi (t * (sampleRate hi)⁻¹) +
            sampleRate lo * M.logMGF lo (-(t * (sampleRate lo)⁻¹)))
        (sampleRate hi *
            (EconCSLib.pmfExp
                (finiteExponentialTilt (M.typeLaw hi) M.score zHi) M.score *
              (sampleRate hi)⁻¹) +
          sampleRate lo *
            (EconCSLib.pmfExp
                (finiteExponentialTilt (M.typeLaw lo) M.score zLo) M.score *
              (-(sampleRate lo)⁻¹))) z :=
    (hhi_comp.const_mul (sampleRate hi)).add
      (hlo_comp.const_mul (sampleRate lo))
  have hsum_dual :
      HasDerivAt
        (fun t : ℝ => pairwiseDualLogMGF M sampleRate hi lo t)
        (sampleRate hi *
            (EconCSLib.pmfExp
                (finiteExponentialTilt (M.typeLaw hi) M.score zHi) M.score *
              (sampleRate hi)⁻¹) +
          sampleRate lo *
            (EconCSLib.pmfExp
                (finiteExponentialTilt (M.typeLaw lo) M.score zLo) M.score *
              (-(sampleRate lo)⁻¹))) z := by
    simpa [pairwiseDualLogMGF] using hsum
  convert hsum_dual using 1
  dsimp [zHi, zLo]
  field_simp [ne_of_gt hgHi, ne_of_gt hgLo]
  ring_nf

/--
If the high and low tilted score means agree at a real-rate pairwise dual,
then that dual is stationary for the pairwise Chernoff log-MGF.
-/
theorem pairwiseDualLogMGF_hasDerivAt_zero_of_tilted_score_means_eq
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo) {z : ℝ}
    (hmean_eq :
      EconCSLib.pmfExp
          (finiteExponentialTilt (M.typeLaw hi) M.score
            (z * (sampleRate hi)⁻¹)) M.score =
        EconCSLib.pmfExp
          (finiteExponentialTilt (M.typeLaw lo) M.score
            (-(z * (sampleRate lo)⁻¹))) M.score) :
    HasDerivAt
      (fun t : ℝ => pairwiseDualLogMGF M sampleRate hi lo t) 0 z := by
  convert pairwiseDualLogMGF_hasDerivAt M sampleRate hi lo hgHi hgLo z using 1
  linarith

/--
If the pairwise tilted score-mean gap is nonnegative at zero and nonpositive
at some nonpositive dual, continuity gives a stationary nonpositive pairwise
dual.
-/
theorem exists_nonpos_pairwiseDualLogMGF_stationary_of_tilted_score_mean_gap_crossing
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hzero : 0 ≤ pairwiseTiltedScoreMeanGap M sampleRate hi lo 0)
    {zNeg : ℝ} (hzNeg : zNeg ≤ 0)
    (hcross : pairwiseTiltedScoreMeanGap M sampleRate hi lo zNeg ≤ 0) :
    ∃ z : ℝ, z ≤ 0 ∧
      HasDerivAt
        (fun t : ℝ => pairwiseDualLogMGF M sampleRate hi lo t) 0 z := by
  let gap : ℝ → ℝ := fun z =>
    pairwiseTiltedScoreMeanGap M sampleRate hi lo z
  have hcont : Continuous gap := by
    simpa [gap] using
      pairwiseTiltedScoreMeanGap_continuous M sampleRate hi lo
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (gap zNeg) (gap 0) := by
    exact ⟨by simpa [gap] using hcross, by simpa [gap] using hzero⟩
  rcases intermediate_value_Icc hzNeg hcont.continuousOn hzero_mem with
    ⟨z, hz_mem, hz_gap⟩
  have hmean_eq :
      finiteTiltedScoreMean (M.typeLaw hi) M.score
          (z * (sampleRate hi)⁻¹) =
        finiteTiltedScoreMean (M.typeLaw lo) M.score
          (-(z * (sampleRate lo)⁻¹)) := by
    have hgap_zero :
        pairwiseTiltedScoreMeanGap M sampleRate hi lo z = 0 := by
      simpa [gap] using hz_gap
    dsimp [pairwiseTiltedScoreMeanGap] at hgap_zero
    linarith
  exact ⟨z, hz_mem.2,
    pairwiseDualLogMGF_hasDerivAt_zero_of_tilted_score_means_eq
      M sampleRate hi lo hgHi hgLo
      (by simpa [finiteTiltedScoreMean] using hmean_eq)⟩

/--
Expected-score ordering supplies the zero-end of the IVT crossing argument for
the pairwise dual.
-/
theorem exists_nonpos_pairwiseDualLogMGF_stationary_of_expected_score_gap_and_tilted_crossing
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hmean_gap :
      EconCSLib.pmfExp (M.typeLaw lo) M.score ≤
        EconCSLib.pmfExp (M.typeLaw hi) M.score)
    {zNeg : ℝ} (hzNeg : zNeg ≤ 0)
    (hcross : pairwiseTiltedScoreMeanGap M sampleRate hi lo zNeg ≤ 0) :
    ∃ z : ℝ, z ≤ 0 ∧
      HasDerivAt
        (fun t : ℝ => pairwiseDualLogMGF M sampleRate hi lo t) 0 z := by
  refine
    exists_nonpos_pairwiseDualLogMGF_stationary_of_tilted_score_mean_gap_crossing
      M sampleRate hi lo hgHi hgLo ?_ hzNeg hcross
  rw [pairwiseTiltedScoreMeanGap_zero]
  linarith

/--
Common bottom/top finite support gives an explicit nonpositive crossing of the
pairwise tilted score-mean gap.  The bottom/top hypotheses are exactly the
finite rating-scale extreme-tilt inputs; expected-score ordering is used by
the downstream IVT stationarity wrapper, not by this crossing itself.
-/
theorem exists_nonpos_pairwiseTiltedScoreMeanGap_nonpos_of_common_extreme_support
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (rLow rHigh : Rating)
    (hmassHiLow : 0 < (M.typeLaw hi rLow).toReal)
    (_hmassHiHigh : 0 < (M.typeLaw hi rHigh).toReal)
    (_hmassLoLow : 0 < (M.typeLaw lo rLow).toReal)
    (hmassLoHigh : 0 < (M.typeLaw lo rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_low_lt_high : M.score rLow < M.score rHigh) :
    ∃ z : ℝ, z ≤ 0 ∧
      pairwiseTiltedScoreMeanGap M sampleRate hi lo z ≤ 0 := by
  let ε : ℝ := (M.score rHigh - M.score rLow) / 3
  have hε_pos : 0 < ε := by
    dsimp [ε]
    linarith
  rcases
      exists_nonpos_finiteTiltedScoreMean_le_bottom_add
        (M.typeLaw hi) M.score rLow hmassHiLow hscore_low_le hε_pos with
    ⟨zHi, hzHi_nonpos, hHi_mean⟩
  rcases
      exists_nonneg_top_sub_le_finiteTiltedScoreMean
        (M.typeLaw lo) M.score rHigh hmassLoHigh hscore_le_high hε_pos with
    ⟨zLo, hzLo_nonneg, hLo_mean⟩
  let z : ℝ := min (sampleRate hi * zHi) (-(sampleRate lo * zLo))
  have hz_le_hi : z ≤ sampleRate hi * zHi := by
    dsimp [z]
    exact min_le_left _ _
  have hz_le_lo : z ≤ -(sampleRate lo * zLo) := by
    dsimp [z]
    exact min_le_right _ _
  have hz_nonpos : z ≤ 0 := by
    have hhi_nonpos : sampleRate hi * zHi ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hgHi.le hzHi_nonpos
    exact hz_le_hi.trans hhi_nonpos
  have hhi_arg_le : z * (sampleRate hi)⁻¹ ≤ zHi := by
    have hmul :=
      mul_le_mul_of_nonneg_right hz_le_hi (inv_nonneg.mpr hgHi.le)
    have hcancel :
        (sampleRate hi * zHi) * (sampleRate hi)⁻¹ = zHi := by
      field_simp [ne_of_gt hgHi]
    simpa [hcancel, mul_assoc] using hmul
  have hlo_arg_ge : zLo ≤ -(z * (sampleRate lo)⁻¹) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hz_le_lo (inv_nonneg.mpr hgLo.le)
    have hcancel :
        (-(sampleRate lo * zLo)) * (sampleRate lo)⁻¹ = -zLo := by
      field_simp [ne_of_gt hgLo]
    have hz_scaled : z * (sampleRate lo)⁻¹ ≤ -zLo := by
      simpa [hcancel, mul_assoc] using hmul
    linarith
  have hHi_arg_mean :
      finiteTiltedScoreMean (M.typeLaw hi) M.score
          (z * (sampleRate hi)⁻¹) ≤ M.score rLow + ε := by
    exact
      (finiteTiltedScoreMean_mono (M.typeLaw hi) M.score hhi_arg_le).trans
        hHi_mean
  have hLo_arg_mean :
      M.score rHigh - ε ≤
        finiteTiltedScoreMean (M.typeLaw lo) M.score
          (-(z * (sampleRate lo)⁻¹)) := by
    exact hLo_mean.trans
      (finiteTiltedScoreMean_mono (M.typeLaw lo) M.score hlo_arg_ge)
  refine ⟨z, hz_nonpos, ?_⟩
  dsimp [pairwiseTiltedScoreMeanGap]
  have hε_gap : 2 * ε ≤ M.score rHigh - M.score rLow := by
    dsimp [ε]
    linarith
  linarith

/--
Expected-score ordering plus common finite bottom/top support derives a
stationary nonpositive pairwise dual, eliminating the previous opaque
stationarity premise for this GJ18 finite-support bridge.
-/
theorem exists_nonpos_pairwiseDualLogMGF_stationary_of_expected_score_gap_and_common_extreme_support
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hmean_gap :
      EconCSLib.pmfExp (M.typeLaw lo) M.score ≤
        EconCSLib.pmfExp (M.typeLaw hi) M.score)
    (rLow rHigh : Rating)
    (hmassHiLow : 0 < (M.typeLaw hi rLow).toReal)
    (hmassHiHigh : 0 < (M.typeLaw hi rHigh).toReal)
    (hmassLoLow : 0 < (M.typeLaw lo rLow).toReal)
    (hmassLoHigh : 0 < (M.typeLaw lo rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_low_lt_high : M.score rLow < M.score rHigh) :
    ∃ z : ℝ, z ≤ 0 ∧
      HasDerivAt
        (fun t : ℝ => pairwiseDualLogMGF M sampleRate hi lo t) 0 z := by
  rcases
      exists_nonpos_pairwiseTiltedScoreMeanGap_nonpos_of_common_extreme_support
        M sampleRate hi lo hgHi hgLo rLow rHigh
        hmassHiLow hmassHiHigh hmassLoLow hmassLoHigh
        hscore_low_le hscore_le_high hscore_low_lt_high with
    ⟨zCross, hzCross, hcross⟩
  exact
    exists_nonpos_pairwiseDualLogMGF_stationary_of_expected_score_gap_and_tilted_crossing
      M sampleRate hi lo hgHi hgLo hmean_gap hzCross hcross

/-- The extended pairwise source objective is nonnegative for nonnegative rates. -/
theorem pairwiseRateObjectiveTop_nonneg
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (a : ℝ)
    (hgHi : 0 ≤ sampleRate hi) (hgLo : 0 ≤ sampleRate lo) :
    (0 : WithTop ℝ) ≤ pairwiseRateObjectiveTop M sampleRate hi lo a := by
  simpa [pairwiseRateObjectiveTop] using
    M.pairwiseRateObjectiveTop_nonneg sampleRate hi lo a hgHi hgLo

/--
If a displayed common threshold minimizes the pairwise source objective over
all thresholds, then evaluating at that threshold realizes the source
threshold rate.
-/
theorem pairwiseSellerThresholdRate_eq_of_pairwiseRateObjective_minimizer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (a : ℝ)
    (hmin :
      ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate hi lo a ≤
          M.pairwiseRateObjective sampleRate hi lo b) :
    M.pairwiseRateObjective sampleRate hi lo a =
      pairwiseSellerThresholdRate M sampleRate hi lo := by
  simpa [pairwiseSellerThresholdRate] using
    M.pairwiseThresholdRate_eq_of_pairwiseRateObjective_minimizer
      sampleRate hi lo a hmin

/--
Fenchel optimality for the pairwise source objective. If the high and low
log-MGF derivatives meet at the same threshold with opposite scaled duals,
then that threshold minimizes the pairwise source-rate objective. The
all-threshold boundedness hypotheses are the current real-valued
`finiteRateFunction` API requirement for using Fenchel's inequality at
arbitrary comparison thresholds.
-/
theorem pairwiseRateObjective_minimizer_of_common_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hbdd_hi :
      ∀ b : ℝ, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score b t))
    (hbdd_lo :
      ∀ b : ℝ, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score b t))
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹))) :
    ∀ b : ℝ,
      M.pairwiseRateObjective sampleRate hi lo a ≤
        M.pairwiseRateObjective sampleRate hi lo b := by
  intro b
  have hhi_rate_a :
      M.rateFunction hi a =
        (z * (sampleRate hi)⁻¹) * a -
          M.logMGF hi (z * (sampleRate hi)⁻¹) := by
    simpa [FiniteRatingLDPModel.rateFunction,
      FiniteRatingLDPModel.logMGF, finiteLegendreValue] using
      finiteRateFunction_eq_eval_of_logMGF_hasDerivAt
        (M.typeLaw hi) M.score a (z * (sampleRate hi)⁻¹)
        (hbdd_hi a) hderiv_hi
  have hlo_rate_a :
      M.rateFunction lo a =
        (-(z * (sampleRate lo)⁻¹)) * a -
          M.logMGF lo (-(z * (sampleRate lo)⁻¹)) := by
    simpa [FiniteRatingLDPModel.rateFunction,
      FiniteRatingLDPModel.logMGF, finiteLegendreValue] using
      finiteRateFunction_eq_eval_of_logMGF_hasDerivAt
        (M.typeLaw lo) M.score a (-(z * (sampleRate lo)⁻¹))
        (hbdd_lo a) hderiv_lo
  have hhi_ge_b :
      (z * (sampleRate hi)⁻¹) * b -
          M.logMGF hi (z * (sampleRate hi)⁻¹) ≤
        M.rateFunction hi b := by
    simpa [FiniteRatingLDPModel.rateFunction,
      FiniteRatingLDPModel.logMGF, finiteLegendreValue] using
      finiteRateFunction_ge_eval
        (M.typeLaw hi) M.score b (z * (sampleRate hi)⁻¹)
        (hbdd_hi b)
  have hlo_ge_b :
      (-(z * (sampleRate lo)⁻¹)) * b -
          M.logMGF lo (-(z * (sampleRate lo)⁻¹)) ≤
        M.rateFunction lo b := by
    simpa [FiniteRatingLDPModel.rateFunction,
      FiniteRatingLDPModel.logMGF, finiteLegendreValue] using
      finiteRateFunction_ge_eval
        (M.typeLaw lo) M.score b (-(z * (sampleRate lo)⁻¹))
        (hbdd_lo b)
  have hscaled_b :
      sampleRate hi *
            ((z * (sampleRate hi)⁻¹) * b -
              M.logMGF hi (z * (sampleRate hi)⁻¹)) +
          sampleRate lo *
            ((-(z * (sampleRate lo)⁻¹)) * b -
              M.logMGF lo (-(z * (sampleRate lo)⁻¹))) ≤
        M.pairwiseRateObjective sampleRate hi lo b := by
    have hhi_scaled :=
      mul_le_mul_of_nonneg_left hhi_ge_b hgHi.le
    have hlo_scaled :=
      mul_le_mul_of_nonneg_left hlo_ge_b hgLo.le
    simpa [FiniteRatingLDPModel.pairwiseRateObjective] using
      add_le_add hhi_scaled hlo_scaled
  have hcancel :
      sampleRate hi *
            ((z * (sampleRate hi)⁻¹) * a -
              M.logMGF hi (z * (sampleRate hi)⁻¹)) +
          sampleRate lo *
            ((-(z * (sampleRate lo)⁻¹)) * a -
              M.logMGF lo (-(z * (sampleRate lo)⁻¹))) =
        sampleRate hi *
            ((z * (sampleRate hi)⁻¹) * b -
              M.logMGF hi (z * (sampleRate hi)⁻¹)) +
          sampleRate lo *
            ((-(z * (sampleRate lo)⁻¹)) * b -
              M.logMGF lo (-(z * (sampleRate lo)⁻¹))) := by
    have hhi_ne : sampleRate hi ≠ 0 := ne_of_gt hgHi
    have hlo_ne : sampleRate lo ≠ 0 := ne_of_gt hgLo
    field_simp [hhi_ne, hlo_ne]
    ring
  calc
    M.pairwiseRateObjective sampleRate hi lo a
        =
          sampleRate hi *
              ((z * (sampleRate hi)⁻¹) * a -
                M.logMGF hi (z * (sampleRate hi)⁻¹)) +
            sampleRate lo *
              ((-(z * (sampleRate lo)⁻¹)) * a -
                M.logMGF lo (-(z * (sampleRate lo)⁻¹))) := by
          rw [FiniteRatingLDPModel.pairwiseRateObjective,
            hhi_rate_a, hlo_rate_a]
    _ =
          sampleRate hi *
              ((z * (sampleRate hi)⁻¹) * b -
                M.logMGF hi (z * (sampleRate hi)⁻¹)) +
            sampleRate lo *
              ((-(z * (sampleRate lo)⁻¹)) * b -
                M.logMGF lo (-(z * (sampleRate lo)⁻¹))) := hcancel
    _ ≤ M.pairwiseRateObjective sampleRate hi lo b := hscaled_b

/--
`WithTop` Fenchel optimality for the pairwise source objective. Unlike
`pairwiseRateObjective_minimizer_of_common_logMGF_derivatives`, this theorem
does not require all-threshold real-valued boundedness side conditions:
thresholds outside the finite score hull simply have extended rate `⊤`.
-/
theorem pairwiseRateObjectiveTop_minimizer_of_common_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹))) :
    ∀ b : ℝ,
      pairwiseRateObjectiveTop M sampleRate hi lo a ≤
        pairwiseRateObjectiveTop M sampleRate hi lo b := by
  intro b
  let zHi : ℝ := z * (sampleRate hi)⁻¹
  let zLo : ℝ := -(z * (sampleRate lo)⁻¹)
  have hhi_rate_a :
      sourceRateFunctionTop M hi a =
        (finiteLegendreValue (M.typeLaw hi) M.score a zHi : WithTop ℝ) := by
    dsimp [zHi]
    exact sourceRateFunctionTop_eq_eval_of_logMGF_hasDerivAt
      M hi a (z * (sampleRate hi)⁻¹) hderiv_hi
  have hlo_rate_a :
      sourceRateFunctionTop M lo a =
        (finiteLegendreValue (M.typeLaw lo) M.score a zLo : WithTop ℝ) := by
    dsimp [zLo]
    exact sourceRateFunctionTop_eq_eval_of_logMGF_hasDerivAt
      M lo a (-(z * (sampleRate lo)⁻¹)) hderiv_lo
  have hhi_rate_a' :
      M.rateFunctionTop hi a =
        (finiteLegendreValue (M.typeLaw hi) M.score a zHi : WithTop ℝ) := by
    simpa [sourceRateFunctionTop] using hhi_rate_a
  have hlo_rate_a' :
      M.rateFunctionTop lo a =
        (finiteLegendreValue (M.typeLaw lo) M.score a zLo : WithTop ℝ) := by
    simpa [sourceRateFunctionTop] using hlo_rate_a
  have hhi_ge_b :
      withTopRealScale (sampleRate hi)
          (finiteLegendreValue (M.typeLaw hi) M.score b zHi : WithTop ℝ) ≤
        withTopRealScale (sampleRate hi) (sourceRateFunctionTop M hi b) :=
    withTopRealScale_mono_of_nonneg hgHi.le
      (finiteRateFunctionTop_ge_eval (M.typeLaw hi) M.score b zHi)
  have hlo_ge_b :
      withTopRealScale (sampleRate lo)
          (finiteLegendreValue (M.typeLaw lo) M.score b zLo : WithTop ℝ) ≤
        withTopRealScale (sampleRate lo) (sourceRateFunctionTop M lo b) :=
    withTopRealScale_mono_of_nonneg hgLo.le
      (finiteRateFunctionTop_ge_eval (M.typeLaw lo) M.score b zLo)
  have hscaled_b :
      withTopRealScale (sampleRate hi)
          (finiteLegendreValue (M.typeLaw hi) M.score b zHi : WithTop ℝ) +
        withTopRealScale (sampleRate lo)
          (finiteLegendreValue (M.typeLaw lo) M.score b zLo : WithTop ℝ) ≤
      pairwiseRateObjectiveTop M sampleRate hi lo b := by
    simpa [pairwiseRateObjectiveTop] using add_le_add hhi_ge_b hlo_ge_b
  have hcancel_real :
      sampleRate hi * finiteLegendreValue (M.typeLaw hi) M.score a zHi +
          sampleRate lo * finiteLegendreValue (M.typeLaw lo) M.score a zLo =
        sampleRate hi * finiteLegendreValue (M.typeLaw hi) M.score b zHi +
          sampleRate lo * finiteLegendreValue (M.typeLaw lo) M.score b zLo := by
    have hhi_ne : sampleRate hi ≠ 0 := ne_of_gt hgHi
    have hlo_ne : sampleRate lo ≠ 0 := ne_of_gt hgLo
    dsimp [finiteLegendreValue, FiniteRatingLDPModel.logMGF, zHi, zLo]
    field_simp [hhi_ne, hlo_ne]
    ring_nf
  have hcancel :
      withTopRealScale (sampleRate hi)
          (finiteLegendreValue (M.typeLaw hi) M.score a zHi : WithTop ℝ) +
        withTopRealScale (sampleRate lo)
          (finiteLegendreValue (M.typeLaw lo) M.score a zLo : WithTop ℝ) =
      withTopRealScale (sampleRate hi)
          (finiteLegendreValue (M.typeLaw hi) M.score b zHi : WithTop ℝ) +
        withTopRealScale (sampleRate lo)
          (finiteLegendreValue (M.typeLaw lo) M.score b zLo : WithTop ℝ) := by
    have hcancel_top :
        (sampleRate hi * finiteLegendreValue (M.typeLaw hi) M.score a zHi +
            sampleRate lo * finiteLegendreValue (M.typeLaw lo) M.score a zLo : WithTop ℝ) =
          (sampleRate hi * finiteLegendreValue (M.typeLaw hi) M.score b zHi +
            sampleRate lo * finiteLegendreValue (M.typeLaw lo) M.score b zLo : WithTop ℝ) := by
      exact_mod_cast hcancel_real
    simpa [withTopRealScale] using hcancel_top
  calc
    pairwiseRateObjectiveTop M sampleRate hi lo a
        =
      withTopRealScale (sampleRate hi)
          (finiteLegendreValue (M.typeLaw hi) M.score a zHi : WithTop ℝ) +
        withTopRealScale (sampleRate lo)
          (finiteLegendreValue (M.typeLaw lo) M.score a zLo : WithTop ℝ) := by
          simp [pairwiseRateObjectiveTop,
            FiniteRatingLDPModel.pairwiseRateObjectiveTop, withTopRealScale,
            hhi_rate_a', hlo_rate_a']
    _ =
      withTopRealScale (sampleRate hi)
          (finiteLegendreValue (M.typeLaw hi) M.score b zHi : WithTop ℝ) +
        withTopRealScale (sampleRate lo)
          (finiteLegendreValue (M.typeLaw lo) M.score b zLo : WithTop ℝ) :=
          hcancel
    _ ≤ pairwiseRateObjectiveTop M sampleRate hi lo b := hscaled_b

/--
If a displayed common threshold minimizes the extended pairwise source objective
over all thresholds, then evaluating at that threshold realizes the extended
source threshold rate.
-/
theorem pairwiseSellerThresholdRateTop_eq_of_pairwiseRateObjectiveTop_minimizer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (a : ℝ)
    (hgHi : 0 ≤ sampleRate hi) (hgLo : 0 ≤ sampleRate lo)
    (hmin :
      ∀ b : ℝ,
        pairwiseRateObjectiveTop M sampleRate hi lo a ≤
          pairwiseRateObjectiveTop M sampleRate hi lo b) :
    pairwiseRateObjectiveTop M sampleRate hi lo a =
      pairwiseSellerThresholdRateTop M sampleRate hi lo := by
  unfold pairwiseSellerThresholdRateTop
  have hnonempty :
      (Set.range fun b : ℝ =>
        pairwiseRateObjectiveTop M sampleRate hi lo b).Nonempty :=
    ⟨pairwiseRateObjectiveTop M sampleRate hi lo a, ⟨a, rfl⟩⟩
  have hbdd :
      BddBelow
        (Set.range fun b : ℝ =>
          pairwiseRateObjectiveTop M sampleRate hi lo b) := by
    refine ⟨(0 : WithTop ℝ), ?_⟩
    intro y hy
    rcases hy with ⟨b, rfl⟩
    exact pairwiseRateObjectiveTop_nonneg M sampleRate hi lo b hgHi hgLo
  have hle_inf :
      pairwiseRateObjectiveTop M sampleRate hi lo a ≤
        sInf (Set.range fun b : ℝ =>
          pairwiseRateObjectiveTop M sampleRate hi lo b) := by
    refine le_csInf hnonempty ?_
    intro y hy
    rcases hy with ⟨b, rfl⟩
    exact hmin b
  have hinf_le :
      sInf (Set.range fun b : ℝ =>
          pairwiseRateObjectiveTop M sampleRate hi lo b) ≤
        pairwiseRateObjectiveTop M sampleRate hi lo a :=
    csInf_le hbdd ⟨a, rfl⟩
  exact le_antisymm hle_inf hinf_le

/--
Common-derivative Fenchel optimality realizes the extended pairwise source
threshold rate, without any all-threshold real-valued boundedness assumptions.
-/
theorem pairwiseSellerThresholdRateTop_eq_of_common_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹))) :
    pairwiseRateObjectiveTop M sampleRate hi lo a =
      pairwiseSellerThresholdRateTop M sampleRate hi lo :=
  pairwiseSellerThresholdRateTop_eq_of_pairwiseRateObjectiveTop_minimizer
    M sampleRate hi lo a hgHi.le hgLo.le
    (pairwiseRateObjectiveTop_minimizer_of_common_logMGF_derivatives
      M sampleRate hi lo hgHi hgLo a z hderiv_hi hderiv_lo)

/--
At a common-dual derivative threshold, the support-safe extended pairwise
objective is finite and agrees with the real displayed pairwise objective.
-/
theorem pairwiseRateObjectiveTop_eq_coe_of_common_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹))) :
    pairwiseRateObjectiveTop M sampleRate hi lo a =
      (M.pairwiseRateObjective sampleRate hi lo a : WithTop ℝ) := by
  let zHi : ℝ := z * (sampleRate hi)⁻¹
  let zLo : ℝ := -(z * (sampleRate lo)⁻¹)
  have hhi_top :
      M.rateFunctionTop hi a =
        (finiteLegendreValue (M.typeLaw hi) M.score a zHi : WithTop ℝ) := by
    dsimp [zHi]
    simpa [sourceRateFunctionTop] using
      sourceRateFunctionTop_eq_eval_of_logMGF_hasDerivAt
        M hi a (z * (sampleRate hi)⁻¹) hderiv_hi
  have hlo_top :
      M.rateFunctionTop lo a =
        (finiteLegendreValue (M.typeLaw lo) M.score a zLo : WithTop ℝ) := by
    dsimp [zLo]
    simpa [sourceRateFunctionTop] using
      sourceRateFunctionTop_eq_eval_of_logMGF_hasDerivAt
        M lo a (-(z * (sampleRate lo)⁻¹)) hderiv_lo
  have hhi_real :
      M.rateFunction hi a =
        finiteLegendreValue (M.typeLaw hi) M.score a zHi := by
    dsimp [zHi]
    simpa [FiniteRatingLDPModel.rateFunction,
      FiniteRatingLDPModel.logMGF] using
      finiteRateFunction_eq_eval_of_logMGF_hasDerivAt_no_bdd
        (M.typeLaw hi) M.score a (z * (sampleRate hi)⁻¹)
        (by simpa [FiniteRatingLDPModel.logMGF] using hderiv_hi)
  have hlo_real :
      M.rateFunction lo a =
        finiteLegendreValue (M.typeLaw lo) M.score a zLo := by
    dsimp [zLo]
    simpa [FiniteRatingLDPModel.rateFunction,
      FiniteRatingLDPModel.logMGF] using
      finiteRateFunction_eq_eval_of_logMGF_hasDerivAt_no_bdd
        (M.typeLaw lo) M.score a (-(z * (sampleRate lo)⁻¹))
        (by simpa [FiniteRatingLDPModel.logMGF] using hderiv_lo)
  simp [pairwiseRateObjectiveTop,
    FiniteRatingLDPModel.pairwiseRateObjectiveTop,
    FiniteRatingLDPModel.pairwiseRateObjective,
    EconCSLib.Probability.withTopRealScale,
    hhi_top, hlo_top, hhi_real, hlo_real]

/--
Common-dual derivative data identifies the support-safe source threshold rate
with the displayed real pairwise objective value.
-/
theorem pairwiseSellerThresholdRateTop_eq_coe_pairwiseRateObjective_of_common_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹))) :
    pairwiseSellerThresholdRateTop M sampleRate hi lo =
      (M.pairwiseRateObjective sampleRate hi lo a : WithTop ℝ) := by
  have htop :
      pairwiseRateObjectiveTop M sampleRate hi lo a =
        pairwiseSellerThresholdRateTop M sampleRate hi lo :=
    pairwiseSellerThresholdRateTop_eq_of_common_logMGF_derivatives
      M sampleRate hi lo hgHi hgLo a z hderiv_hi hderiv_lo
  have hfinite :
      pairwiseRateObjectiveTop M sampleRate hi lo a =
        (M.pairwiseRateObjective sampleRate hi lo a : WithTop ℝ) :=
    pairwiseRateObjectiveTop_eq_coe_of_common_logMGF_derivatives
      M sampleRate hi lo a z hderiv_hi hderiv_lo
  exact htop.symm.trans hfinite

/--
A stationary point of the real-rate two-population dual log-MGF gives common
one-rating derivative data at the scaled high/low dual parameters.
-/
theorem exists_common_logMGF_derivatives_of_pairwiseDualLogMGF_hasDerivAt_zero
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    {z : ℝ}
    (hderiv_dual :
      HasDerivAt
        (fun t : ℝ => pairwiseDualLogMGF M sampleRate hi lo t)
        0 z) :
    ∃ a : ℝ,
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹) ∧
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)) := by
  let zHi : ℝ := z * (sampleRate hi)⁻¹
  let zLo : ℝ := -(z * (sampleRate lo)⁻¹)
  let aHi : ℝ :=
    (∑ r : Rating,
      (M.typeLaw hi r).toReal *
        (M.score r * Real.exp (zHi * M.score r))) /
      finiteMGF (M.typeLaw hi) M.score zHi
  let aLo : ℝ :=
    (∑ r : Rating,
      (M.typeLaw lo r).toReal *
        (M.score r * Real.exp (zLo * M.score r))) /
      finiteMGF (M.typeLaw lo) M.score zLo
  have hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) aHi zHi := by
    simpa [FiniteRatingLDPModel.logMGF, zHi, aHi] using
      finiteLogMGF_hasDerivAt (M.typeLaw hi) M.score zHi
  have hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) aLo zLo := by
    simpa [FiniteRatingLDPModel.logMGF, zLo, aLo] using
      finiteLogMGF_hasDerivAt (M.typeLaw lo) M.score zLo
  have hhi_inner :
      HasDerivAt (fun t : ℝ => t * (sampleRate hi)⁻¹)
        ((sampleRate hi)⁻¹) z := by
    simpa using (hasDerivAt_id z).mul_const ((sampleRate hi)⁻¹)
  have hlo_inner :
      HasDerivAt (fun t : ℝ => -(t * (sampleRate lo)⁻¹))
        (-(sampleRate lo)⁻¹) z := by
    simpa using ((hasDerivAt_id z).mul_const ((sampleRate lo)⁻¹)).neg
  have hhi_comp :
      HasDerivAt (fun t : ℝ => M.logMGF hi (t * (sampleRate hi)⁻¹))
        (aHi * (sampleRate hi)⁻¹) z :=
    hderiv_hi.comp z hhi_inner
  have hlo_comp :
      HasDerivAt (fun t : ℝ => M.logMGF lo (-(t * (sampleRate lo)⁻¹)))
        (aLo * (-(sampleRate lo)⁻¹)) z :=
    hderiv_lo.comp z hlo_inner
  have hsum :
      HasDerivAt
        (fun t : ℝ =>
          sampleRate hi * M.logMGF hi (t * (sampleRate hi)⁻¹) +
            sampleRate lo * M.logMGF lo (-(t * (sampleRate lo)⁻¹)))
        (sampleRate hi * (aHi * (sampleRate hi)⁻¹) +
          sampleRate lo * (aLo * (-(sampleRate lo)⁻¹))) z :=
    (hhi_comp.const_mul (sampleRate hi)).add
      (hlo_comp.const_mul (sampleRate lo))
  have hsum_dual :
      HasDerivAt
        (fun t : ℝ => pairwiseDualLogMGF M sampleRate hi lo t)
        (sampleRate hi * (aHi * (sampleRate hi)⁻¹) +
          sampleRate lo * (aLo * (-(sampleRate lo)⁻¹))) z := by
    simpa [pairwiseDualLogMGF] using hsum
  have hderiv_eq_zero :
      sampleRate hi * (aHi * (sampleRate hi)⁻¹) +
          sampleRate lo * (aLo * (-(sampleRate lo)⁻¹)) = 0 :=
    hsum_dual.unique hderiv_dual
  have ha_eq : aHi = aLo := by
    field_simp [ne_of_gt hgHi, ne_of_gt hgLo] at hderiv_eq_zero
    linarith
  exact ⟨aHi, hderiv_hi, by simpa [ha_eq, zLo] using hderiv_lo⟩

/--
Common-derivative Fenchel optimality realizes the pairwise source threshold
rate. This packages the minimizer proof with the `sInf` evaluation lemma.
-/
theorem pairwiseSellerThresholdRate_eq_of_common_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hbdd_hi :
      ∀ b : ℝ, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score b t))
    (hbdd_lo :
      ∀ b : ℝ, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score b t))
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹))) :
    M.pairwiseRateObjective sampleRate hi lo a =
      pairwiseSellerThresholdRate M sampleRate hi lo :=
  pairwiseSellerThresholdRate_eq_of_pairwiseRateObjective_minimizer
    M sampleRate hi lo a
    (pairwiseRateObjective_minimizer_of_common_logMGF_derivatives
      M sampleRate hi lo hgHi hgLo hbdd_hi hbdd_lo a z
      hderiv_hi hderiv_lo)

namespace PairwiseThresholdRateRegularity

/--
Build the pairwise regularity package from displayed source-threshold
minimizers.  This is the preferred finite endpoint when the source analysis
has already identified the minimizing thresholds.
-/
def of_threshold_minimizers
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    {M : FiniteRatingLDPModel Seller Rating} {sampleRate : Seller → ℝ}
    {pairHi pairLo : Pair → Seller}
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (sampleRate (pairLo p))⁻¹)))
    (hthreshold_min :
      ∀ p : Pair, ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p) (a p) ≤
          M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p) b)
    (hstraddle_hi :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairHi p) (a p))
    (hstraddle_lo :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairLo p) (a p)) :
    PairwiseThresholdRateRegularity M sampleRate pairHi pairLo where
  threshold := a
  dual := z
  dual_nonpos := hz
  deriv_hi := hderiv_hi
  deriv_lo := hderiv_lo
  threshold_rate_eq := fun p =>
    pairwiseSellerThresholdRate_eq_of_pairwiseRateObjective_minimizer
      M sampleRate (pairHi p) (pairLo p) (a p) (hthreshold_min p)
  straddles_hi := hstraddle_hi
  straddles_lo := hstraddle_lo

/--
Build the pairwise regularity package from common-dual log-MGF derivatives and
the current real-valued finite-rate boundedness side condition.
-/
def of_common_logMGF_derivatives
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    {M : FiniteRatingLDPModel Seller Rating} {sampleRate : Seller → ℝ}
    {pairHi pairLo : Pair → Seller}
    (hgHi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hgLo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (hbdd_hi :
      ∀ p : Pair, ∀ b : ℝ, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw (pairHi p)) M.score b t))
    (hbdd_lo :
      ∀ p : Pair, ∀ b : ℝ, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw (pairLo p)) M.score b t))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (sampleRate (pairLo p))⁻¹)))
    (hstraddle_hi :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairHi p) (a p))
    (hstraddle_lo :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairLo p) (a p)) :
    PairwiseThresholdRateRegularity M sampleRate pairHi pairLo where
  threshold := a
  dual := z
  dual_nonpos := hz
  deriv_hi := hderiv_hi
  deriv_lo := hderiv_lo
  threshold_rate_eq := fun p =>
    pairwiseSellerThresholdRate_eq_of_common_logMGF_derivatives
      M sampleRate (pairHi p) (pairLo p) (hgHi p) (hgLo p)
      (hbdd_hi p) (hbdd_lo p) (a p) (z p)
      (hderiv_hi p) (hderiv_lo p)
  straddles_hi := hstraddle_hi
  straddles_lo := hstraddle_lo

/--
Build the pairwise regularity package from exact threshold-rate identities and
primitive finite support at common bottom/top ratings.  The straddling
conditions used by the finite Cramer lower bound are derived from the
log-MGF derivative formula under exponential tilting.
-/
def of_threshold_rate_eq_and_score_bounds
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    {M : FiniteRatingLDPModel Seller Rating} {sampleRate : Seller → ℝ}
    {pairHi pairLo : Pair → Seller}
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (sampleRate (pairLo p))⁻¹)))
    (hthreshold_eq :
      ∀ p : Pair,
        M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p) (a p) =
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p))
    (rLow rHigh : Rating)
    (hmass_low_hi :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) rLow).toReal)
    (hmass_high_hi :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) rHigh).toReal)
    (hmass_low_lo :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) rLow).toReal)
    (hmass_high_lo :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_lt : M.score rLow < M.score rHigh) :
    PairwiseThresholdRateRegularity M sampleRate pairHi pairLo where
  threshold := a
  dual := z
  dual_nonpos := hz
  deriv_hi := hderiv_hi
  deriv_lo := hderiv_lo
  threshold_rate_eq := hthreshold_eq
  straddles_hi := fun p =>
    ratingLawStraddlesThreshold_of_logMGF_hasDerivAt_of_score_bounds
      M (pairHi p) (hderiv_hi p) (hmass_low_hi p) (hmass_high_hi p)
      hscore_low_le hscore_le_high hscore_lt
  straddles_lo := fun p =>
    ratingLawStraddlesThreshold_of_logMGF_hasDerivAt_of_score_bounds
      M (pairLo p) (hderiv_lo p) (hmass_low_lo p) (hmass_high_lo p)
      hscore_low_le hscore_le_high hscore_lt

end PairwiseThresholdRateRegularity

/--
Finite minimum of the displayed pairwise threshold rates over the comparison
pair family used in the paper's ranking objective.
-/
noncomputable def minPairwiseSellerThresholdRate
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [Nonempty Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) : ℝ :=
  (Finset.univ : Finset Pair).inf' Finset.univ_nonempty
    (fun p : Pair =>
      pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p))

/--
Independent paired-rating law for the equal-sample finite comparison model:
one high-type rating and one low-type rating are drawn independently.
-/
noncomputable def pairedRatingLaw
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller) :
    PMF (Rating × Rating) :=
  EconCSLib.pmfProd (M.typeLaw hi) (M.typeLaw lo)

theorem pairedRatingLaw_apply_toReal
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (p : Rating × Rating) :
    (pairedRatingLaw M hi lo p).toReal =
      ((M.typeLaw hi p.1).toReal) * ((M.typeLaw lo p.2).toReal) := by
  simp [pairedRatingLaw]

/-- Expectations under the paired-rating law are independent pair expectations. -/
theorem pairedRatingLaw_pmfExp_eq_pairExp
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (f : Rating × Rating → ℝ) :
    EconCSLib.pmfExp (pairedRatingLaw M hi lo) f =
      EconCSLib.pmfPairExp (M.typeLaw hi) (M.typeLaw lo)
        (fun x y => f (x, y)) := by
  simpa [pairedRatingLaw] using
    EconCSLib.pmfExp_pmfProd_eq_pairExp
      (M.typeLaw hi) (M.typeLaw lo) f

/-- Score gap for the paired-rating finite comparison model. -/
def pairedRatingGapScore
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) : Rating × Rating → ℝ :=
  fun p => M.score p.1 - M.score p.2

/-- The paired-rating gap mean is the high-type mean score minus the low-type mean. -/
theorem pairedRatingGapMean_eq_sub
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller) :
    EconCSLib.pmfExp (pairedRatingLaw M hi lo) (pairedRatingGapScore M) =
      EconCSLib.pmfExp (M.typeLaw hi) M.score -
        EconCSLib.pmfExp (M.typeLaw lo) M.score := by
  rw [pairedRatingLaw_pmfExp_eq_pairExp]
  have hsub :=
    EconCSLib.pmfPairExp_sub (M.typeLaw hi) (M.typeLaw lo)
      (fun x _ => M.score x) (fun _ y => M.score y)
  simpa [pairedRatingGapScore] using
    hsub

/-- Equal-sample pairwise comparison error probability. -/
def equalSamplePairwiseErrorProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller) (n : ℕ) : ℝ :=
  finiteIidScoreLeftTailProb
    (pairedRatingLaw M hi lo) (pairedRatingGapScore M) 0 n

/-- Equal-sample pairwise Chernoff exponent for the paired-rating model. -/
def equalSamplePairwiseChernoffRate
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller) : ℝ :=
  finiteChernoffRate (pairedRatingLaw M hi lo) (pairedRatingGapScore M)

/--
Independent high/low rating samples with possibly different sample counts.
This is the finite object behind the source counts `k g(theta_hi)` and
`k g(theta_lo)`.
-/
noncomputable def twoSampleRatingLaw
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) :
    PMF ((Fin nHi → Rating) × (Fin nLo → Rating)) :=
  EconCSLib.pmfProd
    (EconCSLib.pmfProduct (Fin nHi) Rating (M.typeLaw hi))
    (EconCSLib.pmfProduct (Fin nLo) Rating (M.typeLaw lo))

/-- Scaled high-low sample-score gap for independent finite samples. -/
def twoSampleScoreGapSum
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) {nHi nLo : ℕ}
    (cHi cLo : ℝ)
    (sample : (Fin nHi → Rating) × (Fin nLo → Rating)) : ℝ :=
  cHi * finiteIidScoreSum M.score sample.1 -
    cLo * finiteIidScoreSum M.score sample.2

/-- Left-tail comparison probability for the scaled two-sample score gap. -/
def twoSampleScoreGapLeftTailProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) : ℝ :=
  EconCSLib.pmfProb (twoSampleRatingLaw M hi lo nHi nLo)
    (fun sample => twoSampleScoreGapSum M cHi cLo sample ≤ 0)

/-- Strict-left comparison probability for the scaled two-sample score gap. -/
def twoSampleScoreGapStrictLeftProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) : ℝ :=
  EconCSLib.pmfProb (twoSampleRatingLaw M hi lo nHi nLo)
    (fun sample => twoSampleScoreGapSum M cHi cLo sample < 0)

/-- Strict-right comparison probability for the scaled two-sample score gap. -/
def twoSampleScoreGapStrictRightProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) : ℝ :=
  EconCSLib.pmfProb (twoSampleRatingLaw M hi lo nHi nLo)
    (fun sample => 0 < twoSampleScoreGapSum M cHi cLo sample)

/-- Tie probability for the scaled two-sample score gap. -/
def twoSampleScoreGapTieProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) : ℝ :=
  EconCSLib.pmfProb (twoSampleRatingLaw M hi lo nHi nLo)
    (fun sample => twoSampleScoreGapSum M cHi cLo sample = 0)

/--
Paper pairwise objective `P_k`: strict correct-order probability minus strict
inversion probability.
-/
def twoSamplePkObjectiveProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) : ℝ :=
  twoSampleScoreGapStrictRightProb M hi lo nHi nLo cHi cLo -
    twoSampleScoreGapStrictLeftProb M hi lo nHi nLo cHi cLo

/--
Paper `1 - P_k` comparison error for a fixed pair: twice the strict inversion
probability plus the tie probability.
-/
def twoSamplePkComplementErrorProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) : ℝ :=
  2 * twoSampleScoreGapStrictLeftProb M hi lo nHi nLo cHi cLo +
    twoSampleScoreGapTieProb M hi lo nHi nLo cHi cLo

/-- Paper sample count `n_k(theta) = floor(k * g(theta))`. -/
def floorSampleCount {Seller : Type*} (sampleRate : Seller → ℝ)
    (θ : Seller) (k : ℕ) : ℕ :=
  Nat.floor ((k : ℝ) * sampleRate θ)

/-- `floor(k * g(theta)) / k` converges to `g(theta)`. -/
theorem floorSampleCount_div_tendsto_sampleRate
    {Seller : Type*} (sampleRate : Seller → ℝ) (θ : Seller)
    (h_nonneg : 0 ≤ sampleRate θ) :
    Filter.Tendsto
      (fun k : ℕ =>
        ((floorSampleCount sampleRate θ k : ℕ) : ℝ) / (k : ℝ))
      Filter.atTop (nhds (sampleRate θ)) :=
  EconCSLib.Math.tendsto_nat_floor_mul_const_div_nat h_nonneg

/-- If the sampling rate is natural-valued, the source floor count is exact. -/
theorem floorSampleCount_eq_mul_of_nat_sampleRate
    {Seller : Type*} (sampleRate : Seller → ℝ) (θ : Seller)
    (g k : ℕ) (hsample : sampleRate θ = (g : ℝ)) :
    floorSampleCount sampleRate θ k = k * g := by
  unfold floorSampleCount
  rw [hsample]
  rw [← Nat.cast_mul]
  exact Nat.floor_natCast (k * g)

/--
Source-shaped floor-count left-tail comparison probability for the two-seller
score-average gap.
-/
def twoSampleFloorScoreGapLeftTailProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (k : ℕ) : ℝ :=
  let nHi := floorSampleCount sampleRate hi k
  let nLo := floorSampleCount sampleRate lo k
  twoSampleScoreGapLeftTailProb M hi lo nHi nLo
    ((nHi : ℝ)⁻¹) ((nLo : ℝ)⁻¹)

/--
Source-shaped floor-count `1 - P_k` comparison error for a two-seller pair.
-/
def twoSampleFloorPkComplementErrorProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (k : ℕ) : ℝ :=
  let nHi := floorSampleCount sampleRate hi k
  let nLo := floorSampleCount sampleRate lo k
  twoSamplePkComplementErrorProb M hi lo nHi nLo
    ((nHi : ℝ)⁻¹) ((nLo : ℝ)⁻¹)

/--
Support-safe pairwise LDP certificate for the paper's finite-support
threshold-rate convention.  It records a finite real representative of the
extended threshold rate and the exact floor-count left-tail certificate at that
rate.  This is the reusable boundary needed when the source proof invokes a
finite-alphabet Cramer/Laplace principle instead of displaying derivative
witnesses.
-/
structure PairwiseThresholdRateTopLdpCertificate
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) where
  rate : Pair → ℝ
  threshold_rate_top_eq :
    ∀ p : Pair,
      pairwiseSellerThresholdRateTop M sampleRate (pairHi p) (pairLo p) =
        (rate p : WithTop ℝ)
  leftTail :
    ∀ p : Pair,
      ExponentialRateCertificate
        (twoSampleFloorScoreGapLeftTailProb M sampleRate (pairHi p) (pairLo p))
        (rate p)

/--
Source-shaped floor-count paper pairwise objective `P_k`.
-/
def twoSampleFloorPkObjectiveProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (k : ℕ) : ℝ :=
  let nHi := floorSampleCount sampleRate hi k
  let nLo := floorSampleCount sampleRate lo k
  twoSamplePkObjectiveProb M hi lo nHi nLo
    ((nHi : ℝ)⁻¹) ((nLo : ℝ)⁻¹)

/--
Joint floor-count rating sample for a finite seller chain.  Coordinate `θ`
contains exactly `floor(k * g θ)` ratings for seller type `θ`.
-/
abbrev finiteChainJointFloorRatingSample
    {n : ℕ} (Rating : Type*) (sampleRate : Fin n → ℝ) (k : ℕ) :=
  (θ : Fin n) → Fin (floorSampleCount sampleRate θ k) → Rating

/--
Independent joint law over all finite-chain seller samples at horizon `k`.
This is the concrete finite PMF counterpart of the paper's system-state score
law before projecting each seller's sample to its aggregate score.
-/
noncomputable def finiteChainJointFloorRatingLaw
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (k : ℕ) : PMF (finiteChainJointFloorRatingSample Rating sampleRate k) :=
  EconCSLib.pmfPi (fun θ : Fin n =>
    EconCSLib.pmfProduct (Fin (floorSampleCount sampleRate θ k)) Rating
      (M.typeLaw θ))

/-- Aggregate score projection from the joint floor-count rating sample. -/
def finiteChainJointFloorAverageScore
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (k : ℕ) (sample : finiteChainJointFloorRatingSample Rating sampleRate k)
    (θ : Fin n) : ℝ :=
  ((floorSampleCount sampleRate θ k : ℕ) : ℝ)⁻¹ *
    finiteIidScoreSum M.score (sample θ)

/--
The transformed proof quantity `2 Pr(gap < 0) + Pr(gap = 0)` is exactly
`1 - P_k` for the paper's definition
`P_k = Pr(gap > 0) - Pr(gap < 0)`.
-/
theorem twoSamplePkComplementErrorProb_eq_one_sub_pkObjectiveProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) :
    twoSamplePkComplementErrorProb M hi lo nHi nLo cHi cLo =
      1 - twoSamplePkObjectiveProb M hi lo nHi nLo cHi cLo := by
  classical
  let μ := twoSampleRatingLaw M hi lo nHi nLo
  let gap :
      (Fin nHi → Rating) × (Fin nLo → Rating) → ℝ :=
    fun sample => twoSampleScoreGapSum M cHi cLo sample
  have hdisjoint :
      ∀ sample, 0 < gap sample → gap sample < 0 → False := by
    intro sample hgt hlt
    linarith
  have htie_eq :
      twoSampleScoreGapTieProb M hi lo nHi nLo cHi cLo =
        EconCSLib.pmfProb μ (fun sample => ¬ 0 < gap sample ∧ ¬ gap sample < 0) := by
    refine EconCSLib.pmfProb_congr μ ?_
    intro sample
    constructor
    · intro hzero
      constructor <;> linarith
    · intro hneither
      exact le_antisymm
        (le_of_not_gt hneither.1)
        (not_lt.mp hneither.2)
  have hneither :
      EconCSLib.pmfProb μ (fun sample => ¬ 0 < gap sample ∧ ¬ gap sample < 0) =
        1 - EconCSLib.pmfProb μ (fun sample => 0 < gap sample) -
          EconCSLib.pmfProb μ (fun sample => gap sample < 0) :=
    EconCSLib.pmfProb_not_and_not_eq_one_sub_add_of_disjoint
      μ (fun sample => 0 < gap sample) (fun sample => gap sample < 0)
      hdisjoint
  unfold twoSamplePkComplementErrorProb twoSamplePkObjectiveProb
  rw [htie_eq, hneither]
  simp [twoSampleScoreGapStrictRightProb,
    twoSampleScoreGapStrictLeftProb, μ, gap]
  ring

/--
Floor-count source version of
`twoSamplePkComplementErrorProb_eq_one_sub_pkObjectiveProb`.
-/
theorem twoSampleFloorPkComplementErrorProb_eq_one_sub_pkObjectiveProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (k : ℕ) :
    twoSampleFloorPkComplementErrorProb M sampleRate hi lo k =
      1 - twoSampleFloorPkObjectiveProb M sampleRate hi lo k := by
  unfold twoSampleFloorPkComplementErrorProb twoSampleFloorPkObjectiveProb
  exact
    twoSamplePkComplementErrorProb_eq_one_sub_pkObjectiveProb
      M hi lo
      (floorSampleCount sampleRate hi k)
      (floorSampleCount sampleRate lo k)
      (((floorSampleCount sampleRate hi k : ℕ) : ℝ)⁻¹)
      (((floorSampleCount sampleRate lo k : ℕ) : ℝ)⁻¹)

/-- Scaling both score-gap coefficients by a positive constant preserves the left-tail event. -/
theorem twoSampleScoreGapLeftTailProb_scale_pos
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo s : ℝ) (hs : 0 < s) :
    twoSampleScoreGapLeftTailProb M hi lo nHi nLo (s * cHi) (s * cLo) =
      twoSampleScoreGapLeftTailProb M hi lo nHi nLo cHi cLo := by
  classical
  let μ := twoSampleRatingLaw M hi lo nHi nLo
  have hgap :
      ∀ sample : (Fin nHi → Rating) × (Fin nLo → Rating),
        twoSampleScoreGapSum M (s * cHi) (s * cLo) sample =
          s * twoSampleScoreGapSum M cHi cLo sample := by
    intro sample
    unfold twoSampleScoreGapSum
    ring
  refine EconCSLib.pmfProb_congr μ ?_
  intro sample
  rw [hgap sample]
  constructor
  · intro h
    have hdiv :
        (s * twoSampleScoreGapSum M cHi cLo sample) / s ≤ 0 / s :=
      div_le_div_of_nonneg_right h hs.le
    simpa [hs.ne'] using hdiv
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hs.le h

/-- Scaling both score-gap coefficients by a positive constant preserves `P_k`. -/
theorem twoSamplePkObjectiveProb_scale_pos
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo s : ℝ) (hs : 0 < s) :
    twoSamplePkObjectiveProb M hi lo nHi nLo (s * cHi) (s * cLo) =
      twoSamplePkObjectiveProb M hi lo nHi nLo cHi cLo := by
  classical
  let μ := twoSampleRatingLaw M hi lo nHi nLo
  have hgap :
      ∀ sample : (Fin nHi → Rating) × (Fin nLo → Rating),
        twoSampleScoreGapSum M (s * cHi) (s * cLo) sample =
          s * twoSampleScoreGapSum M cHi cLo sample := by
    intro sample
    unfold twoSampleScoreGapSum
    ring
  have hright :
      twoSampleScoreGapStrictRightProb M hi lo nHi nLo (s * cHi) (s * cLo) =
        twoSampleScoreGapStrictRightProb M hi lo nHi nLo cHi cLo := by
    refine EconCSLib.pmfProb_congr μ ?_
    intro sample
    rw [hgap sample]
    constructor
    · intro h
      exact pos_of_mul_pos_left (by simpa [mul_comm] using h) hs.le
    · intro h
      exact mul_pos hs h
  have hleft :
      twoSampleScoreGapStrictLeftProb M hi lo nHi nLo (s * cHi) (s * cLo) =
        twoSampleScoreGapStrictLeftProb M hi lo nHi nLo cHi cLo := by
    refine EconCSLib.pmfProb_congr μ ?_
    intro sample
    rw [hgap sample]
    constructor
    · intro h
      have hneg : 0 < s * (-twoSampleScoreGapSum M cHi cLo sample) := by
        simpa [mul_neg, neg_pos] using h
      exact neg_pos.mp
        (pos_of_mul_pos_left (by simpa [mul_comm] using hneg) hs.le)
    · intro h
      have hneg : 0 < -twoSampleScoreGapSum M cHi cLo sample := by
        exact neg_pos.mpr h
      have hmul := mul_pos hs hneg
      simpa [mul_neg, neg_pos] using hmul
  unfold twoSamplePkObjectiveProb
  rw [hright, hleft]

/-- Scaling both score-gap coefficients by a positive constant preserves `1 - P_k`. -/
theorem twoSamplePkComplementErrorProb_scale_pos
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo s : ℝ) (hs : 0 < s) :
    twoSamplePkComplementErrorProb M hi lo nHi nLo (s * cHi) (s * cLo) =
      twoSamplePkComplementErrorProb M hi lo nHi nLo cHi cLo := by
  rw [twoSamplePkComplementErrorProb_eq_one_sub_pkObjectiveProb,
    twoSamplePkComplementErrorProb_eq_one_sub_pkObjectiveProb,
    twoSamplePkObjectiveProb_scale_pos M hi lo nHi nLo cHi cLo s hs]

/--
Weighted floor-count ranking objective, i.e. the finite version of the
paper's `W_k`.
-/
def finiteFloorPkObjective
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) (weight : Pair → ℝ) (k : ℕ) : ℝ :=
  ∑ p : Pair,
    weight p *
      twoSampleFloorPkObjectiveProb M sampleRate (pairHi p) (pairLo p) k

/-- Uniform pair weight for the paper's finite Kendall-style average. -/
def uniformPairWeight (Pair : Type*) [Fintype Pair] : Pair → ℝ :=
  fun _ => (Fintype.card Pair : ℝ)⁻¹

theorem uniformPairWeight_nonneg (Pair : Type*) [Fintype Pair] :
    ∀ p : Pair, 0 ≤ uniformPairWeight Pair p := by
  intro p
  unfold uniformPairWeight
  exact inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card Pair))

theorem uniformPairWeight_pos (Pair : Type*) [Fintype Pair] [Nonempty Pair]
    (p : Pair) :
    0 < uniformPairWeight Pair p := by
  have hcard_pos_nat : 0 < Fintype.card Pair :=
    Fintype.card_pos_iff.mpr inferInstance
  unfold uniformPairWeight
  exact inv_pos.mpr (by exact_mod_cast hcard_pos_nat)

theorem uniformPairWeight_sum_eq_one (Pair : Type*) [Fintype Pair]
    [Nonempty Pair] :
    ∑ p : Pair, uniformPairWeight Pair p = 1 := by
  classical
  have hcard_pos_nat : 0 < Fintype.card Pair :=
    Fintype.card_pos_iff.mpr inferInstance
  have hcard_ne : (Fintype.card Pair : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcard_pos_nat)
  calc
    ∑ p : Pair, uniformPairWeight Pair p =
        (Fintype.card Pair : ℝ) * (Fintype.card Pair : ℝ)⁻¹ := by
      simp [uniformPairWeight, Finset.sum_const, nsmul_eq_mul]
    _ = 1 := by
      field_simp [hcard_ne]

/--
Uniform-weight floor-count ranking objective, i.e. the paper's finite `W_k`
once `Pair` is instantiated as the finite family of ordered comparison pairs.
-/
def finiteUniformFloorPkObjective
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) (k : ℕ) : ℝ :=
  finiteFloorPkObjective M sampleRate pairHi pairLo (uniformPairWeight Pair) k

/--
Weighted floor-count ranking error, i.e. the finite version of `1 - W_k`
after rewriting each pair as `1 - P_k`.
-/
def finiteFloorPkComplementError
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) (weight : Pair → ℝ) (k : ℕ) : ℝ :=
  ∑ p : Pair,
    weight p *
      twoSampleFloorPkComplementErrorProb M sampleRate
        (pairHi p) (pairLo p) k

/--
If the finite pair weights sum to one, the weighted sum of pairwise
`1 - P_k` errors is exactly `1 - W_k`.
-/
theorem finiteFloorPkComplementError_eq_one_sub_objective
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) (weight : Pair → ℝ)
    (hweight_sum : ∑ p : Pair, weight p = 1) (k : ℕ) :
    finiteFloorPkComplementError M sampleRate pairHi pairLo weight k =
      1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k := by
  classical
  unfold finiteFloorPkComplementError finiteFloorPkObjective
  calc
    ∑ p : Pair,
        weight p *
          twoSampleFloorPkComplementErrorProb M sampleRate
            (pairHi p) (pairLo p) k
        =
        ∑ p : Pair,
          weight p *
            (1 -
              twoSampleFloorPkObjectiveProb M sampleRate
                (pairHi p) (pairLo p) k) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [twoSampleFloorPkComplementErrorProb_eq_one_sub_pkObjectiveProb]
    _ =
        ∑ p : Pair,
          (weight p -
            weight p *
              twoSampleFloorPkObjectiveProb M sampleRate
                (pairHi p) (pairLo p) k) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          ring
    _ =
        (∑ p : Pair, weight p) -
          ∑ p : Pair,
            weight p *
              twoSampleFloorPkObjectiveProb M sampleRate
                (pairHi p) (pairLo p) k := by
          rw [Finset.sum_sub_distrib]
    _ =
        1 -
          ∑ p : Pair,
            weight p *
              twoSampleFloorPkObjectiveProb M sampleRate
                (pairHi p) (pairLo p) k := by
          rw [hweight_sum]

/-- Integer-rate finite ranking objective for `n * g(theta)` samples. -/
def finiteIntegerRatePkObjective
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating)
    (pairHi pairLo : Pair → Seller) (gHi gLo : Pair → ℕ)
    (weight : Pair → ℝ) (n : ℕ) : ℝ :=
  ∑ p : Pair,
    weight p *
      twoSamplePkObjectiveProb M (pairHi p) (pairLo p)
        (n * gHi p) (n * gLo p)
        (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹)

/-- Integer-rate finite ranking error for `n * g(theta)` samples. -/
def finiteIntegerRatePkComplementError
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating)
    (pairHi pairLo : Pair → Seller) (gHi gLo : Pair → ℕ)
    (weight : Pair → ℝ) (n : ℕ) : ℝ :=
  ∑ p : Pair,
    weight p *
      twoSamplePkComplementErrorProb M (pairHi p) (pairLo p)
        (n * gHi p) (n * gLo p)
        (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹)

/--
Integer-rate version of the objective algebra: when finite pair weights sum
to one, the expanded `1 - P_n` error equals `1 - W_n`.
-/
theorem finiteIntegerRatePkComplementError_eq_one_sub_objective
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating)
    (pairHi pairLo : Pair → Seller) (gHi gLo : Pair → ℕ)
    (weight : Pair → ℝ)
    (hweight_sum : ∑ p : Pair, weight p = 1) (n : ℕ) :
    finiteIntegerRatePkComplementError M pairHi pairLo gHi gLo weight n =
      1 - finiteIntegerRatePkObjective M pairHi pairLo gHi gLo weight n := by
  classical
  unfold finiteIntegerRatePkComplementError finiteIntegerRatePkObjective
  calc
    ∑ p : Pair,
        weight p *
          twoSamplePkComplementErrorProb M (pairHi p) (pairLo p)
            (n * gHi p) (n * gLo p)
            (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹)
        =
        ∑ p : Pair,
          weight p *
            (1 -
              twoSamplePkObjectiveProb M (pairHi p) (pairLo p)
                (n * gHi p) (n * gLo p)
                (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹)) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [twoSamplePkComplementErrorProb_eq_one_sub_pkObjectiveProb]
    _ =
        ∑ p : Pair,
          (weight p -
            weight p *
              twoSamplePkObjectiveProb M (pairHi p) (pairLo p)
                (n * gHi p) (n * gLo p)
                (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹)) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          ring
    _ =
        (∑ p : Pair, weight p) -
          ∑ p : Pair,
            weight p *
              twoSamplePkObjectiveProb M (pairHi p) (pairLo p)
                (n * gHi p) (n * gLo p)
                (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹) := by
          rw [Finset.sum_sub_distrib]
    _ =
        1 -
          ∑ p : Pair,
            weight p *
              twoSamplePkObjectiveProb M (pairHi p) (pairLo p)
                (n * gHi p) (n * gLo p)
                (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹) := by
          rw [hweight_sum]

/--
Natural-valued sampling rates make the source floor-count objective coincide
with the integer-rate objective at every positive horizon.
-/
theorem finiteFloorPkObjective_eq_integerRatePkObjective_of_nat_sampleRates
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) (gHi gLo : Pair → ℕ)
    (weight : Pair → ℝ)
    (hsample_hi :
      ∀ p : Pair, sampleRate (pairHi p) = (gHi p : ℝ))
    (hsample_lo :
      ∀ p : Pair, sampleRate (pairLo p) = (gLo p : ℝ))
    (hgHi : ∀ p : Pair, 0 < gHi p)
    (hgLo : ∀ p : Pair, 0 < gLo p)
    (n : ℕ) (hnpos_nat : 0 < n) :
    finiteFloorPkObjective M sampleRate pairHi pairLo weight n =
      finiteIntegerRatePkObjective M pairHi pairLo gHi gLo weight n := by
  classical
  unfold finiteFloorPkObjective finiteIntegerRatePkObjective
    twoSampleFloorPkObjectiveProb
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [floorSampleCount_eq_mul_of_nat_sampleRate
      sampleRate (pairHi p) (gHi p) n (hsample_hi p),
    floorSampleCount_eq_mul_of_nat_sampleRate
      sampleRate (pairLo p) (gLo p) n (hsample_lo p)]
  change
    weight p *
        twoSamplePkObjectiveProb M (pairHi p) (pairLo p)
          (n * gHi p) (n * gLo p)
          (((n * gHi p : ℕ) : ℝ)⁻¹)
          (((n * gLo p : ℕ) : ℝ)⁻¹) =
      weight p *
        twoSamplePkObjectiveProb M (pairHi p) (pairLo p)
          (n * gHi p) (n * gLo p)
          (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hs : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
  have hgHi_pos : 0 < ((gHi p : ℕ) : ℝ) := by
    exact_mod_cast hgHi p
  have hgLo_pos : 0 < ((gLo p : ℕ) : ℝ) := by
    exact_mod_cast hgLo p
  have hcoeff_hi :
      (((n * gHi p : ℕ) : ℝ)⁻¹) =
        (n : ℝ)⁻¹ * (((gHi p : ℕ) : ℝ)⁻¹) := by
    rw [Nat.cast_mul]
    field_simp [hnpos.ne', hgHi_pos.ne']
  have hcoeff_lo :
      (((n * gLo p : ℕ) : ℝ)⁻¹) =
        (n : ℝ)⁻¹ * (((gLo p : ℕ) : ℝ)⁻¹) := by
    rw [Nat.cast_mul]
    field_simp [hnpos.ne', hgLo_pos.ne']
  rw [hcoeff_hi, hcoeff_lo]
  rw [twoSamplePkObjectiveProb_scale_pos
    M (pairHi p) (pairLo p) (n * gHi p) (n * gLo p)
    (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹)
    ((n : ℝ)⁻¹) hs]

/--
Natural-valued sampling rates make the source floor-count complement error
coincide with the integer-rate complement error at every positive horizon.
-/
theorem finiteFloorPkComplementError_eq_integerRatePkComplementError_of_nat_sampleRates
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) (gHi gLo : Pair → ℕ)
    (weight : Pair → ℝ)
    (hsample_hi :
      ∀ p : Pair, sampleRate (pairHi p) = (gHi p : ℝ))
    (hsample_lo :
      ∀ p : Pair, sampleRate (pairLo p) = (gLo p : ℝ))
    (hgHi : ∀ p : Pair, 0 < gHi p)
    (hgLo : ∀ p : Pair, 0 < gLo p)
    (n : ℕ) (hnpos_nat : 0 < n) :
    finiteFloorPkComplementError M sampleRate pairHi pairLo weight n =
      finiteIntegerRatePkComplementError M pairHi pairLo gHi gLo weight n := by
  classical
  unfold finiteFloorPkComplementError finiteIntegerRatePkComplementError
    twoSampleFloorPkComplementErrorProb
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [floorSampleCount_eq_mul_of_nat_sampleRate
      sampleRate (pairHi p) (gHi p) n (hsample_hi p),
    floorSampleCount_eq_mul_of_nat_sampleRate
      sampleRate (pairLo p) (gLo p) n (hsample_lo p)]
  change
    weight p *
        twoSamplePkComplementErrorProb M (pairHi p) (pairLo p)
          (n * gHi p) (n * gLo p)
          (((n * gHi p : ℕ) : ℝ)⁻¹)
          (((n * gLo p : ℕ) : ℝ)⁻¹) =
      weight p *
        twoSamplePkComplementErrorProb M (pairHi p) (pairLo p)
          (n * gHi p) (n * gLo p)
          (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hs : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
  have hgHi_pos : 0 < ((gHi p : ℕ) : ℝ) := by
    exact_mod_cast hgHi p
  have hgLo_pos : 0 < ((gLo p : ℕ) : ℝ) := by
    exact_mod_cast hgLo p
  have hcoeff_hi :
      (((n * gHi p : ℕ) : ℝ)⁻¹) =
        (n : ℝ)⁻¹ * (((gHi p : ℕ) : ℝ)⁻¹) := by
    rw [Nat.cast_mul]
    field_simp [hnpos.ne', hgHi_pos.ne']
  have hcoeff_lo :
      (((n * gLo p : ℕ) : ℝ)⁻¹) =
        (n : ℝ)⁻¹ * (((gLo p : ℕ) : ℝ)⁻¹) := by
    rw [Nat.cast_mul]
    field_simp [hnpos.ne', hgLo_pos.ne']
  rw [hcoeff_hi, hcoeff_lo]
  rw [twoSamplePkComplementErrorProb_scale_pos
    M (pairHi p) (pairLo p) (n * gHi p) (n * gLo p)
    (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹)
    ((n : ℝ)⁻¹) hs]

/--
The paper's `1 - P_k` pairwise error is within fixed constants of the
nonpositive score-gap probability used by the large-deviation bridge.
-/
theorem twoSamplePkComplementErrorProb_sandwich_leftTail
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) :
    twoSampleScoreGapLeftTailProb M hi lo nHi nLo cHi cLo ≤
        twoSamplePkComplementErrorProb M hi lo nHi nLo cHi cLo ∧
      twoSamplePkComplementErrorProb M hi lo nHi nLo cHi cLo ≤
        2 * twoSampleScoreGapLeftTailProb M hi lo nHi nLo cHi cLo := by
  classical
  let μ := twoSampleRatingLaw M hi lo nHi nLo
  let gap :
      (Fin nHi → Rating) × (Fin nLo → Rating) → ℝ :=
    fun sample => twoSampleScoreGapSum M cHi cLo sample
  have hleft_eq :
      twoSampleScoreGapLeftTailProb M hi lo nHi nLo cHi cLo =
        twoSampleScoreGapStrictLeftProb M hi lo nHi nLo cHi cLo +
          twoSampleScoreGapTieProb M hi lo nHi nLo cHi cLo := by
    have hcongr :
        EconCSLib.pmfProb μ (fun sample => gap sample ≤ 0) =
          EconCSLib.pmfProb μ
            (fun sample => gap sample < 0 ∨ gap sample = 0) :=
      EconCSLib.pmfProb_congr μ (by
        intro sample
        constructor
        · intro hle
          exact lt_or_eq_of_le hle
        · intro h
          cases h with
          | inl hlt => exact le_of_lt hlt
          | inr heq => simpa [heq])
    have hdisjoint :
        ∀ sample, gap sample < 0 → gap sample = 0 → False := by
      intro sample hlt heq
      linarith
    have hor :
        EconCSLib.pmfProb μ
            (fun sample => gap sample < 0 ∨ gap sample = 0) =
          EconCSLib.pmfProb μ (fun sample => gap sample < 0) +
            EconCSLib.pmfProb μ (fun sample => gap sample = 0) :=
      EconCSLib.pmfProb_or_eq_add_of_disjoint μ
        (fun sample => gap sample < 0)
        (fun sample => gap sample = 0)
        hdisjoint
    simpa [twoSampleScoreGapLeftTailProb,
      twoSampleScoreGapStrictLeftProb, twoSampleScoreGapTieProb, μ, gap]
      using hcongr.trans hor
  have hstrict_nonneg :
      0 ≤ twoSampleScoreGapStrictLeftProb M hi lo nHi nLo cHi cLo :=
    EconCSLib.pmfProb_nonneg μ (fun sample => gap sample < 0)
  have htie_nonneg :
      0 ≤ twoSampleScoreGapTieProb M hi lo nHi nLo cHi cLo :=
    EconCSLib.pmfProb_nonneg μ (fun sample => gap sample = 0)
  unfold twoSamplePkComplementErrorProb
  constructor <;> nlinarith [hleft_eq, hstrict_nonneg, htie_nonneg]

/--
Floor-count version of the `Pk_LD` constant-factor comparison.
-/
theorem twoSampleFloorPkComplementErrorProb_sandwich_leftTail
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (k : ℕ) :
    twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo k ≤
        twoSampleFloorPkComplementErrorProb M sampleRate hi lo k ∧
      twoSampleFloorPkComplementErrorProb M sampleRate hi lo k ≤
        2 * twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo k := by
  unfold twoSampleFloorScoreGapLeftTailProb
    twoSampleFloorPkComplementErrorProb
  exact
    twoSamplePkComplementErrorProb_sandwich_leftTail
      M hi lo
      (floorSampleCount sampleRate hi k)
      (floorSampleCount sampleRate lo k)
      (((floorSampleCount sampleRate hi k : ℕ) : ℝ)⁻¹)
      (((floorSampleCount sampleRate lo k : ℕ) : ℝ)⁻¹)

/--
Two-population finite MGF factorization.  For independent high and low samples,
the exponential moment of the scaled score-gap sum is the product of the
corresponding finite-rating MGFs raised to the two sample counts.
-/
theorem twoSampleScoreGapSum_exp_mgf_eq_product
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo z : ℝ) :
    EconCSLib.pmfExp (twoSampleRatingLaw M hi lo nHi nLo)
        (fun sample =>
          Real.exp (z * twoSampleScoreGapSum M cHi cLo sample)) =
      (M.mgf hi (z * cHi)) ^ nHi *
        (M.mgf lo (-(z * cLo))) ^ nLo := by
  classical
  rw [twoSampleRatingLaw, EconCSLib.pmfExp_pmfProd_eq_pairExp]
  have hpoint :
      ∀ hiSample : Fin nHi → Rating,
        ∀ loSample : Fin nLo → Rating,
          Real.exp
              (z * twoSampleScoreGapSum M cHi cLo (hiSample, loSample)) =
            Real.exp
                ((z * cHi) * finiteIidScoreSum M.score hiSample) *
              Real.exp
                ((-(z * cLo)) * finiteIidScoreSum M.score loSample) := by
    intro hiSample loSample
    rw [← Real.exp_add]
    congr 1
    unfold twoSampleScoreGapSum
    ring
  simp_rw [hpoint]
  rw [EconCSLib.pmfPairExp_mul_separable]
  have hhi :=
    iid_sum_mgf
      (ι := Fin nHi) (μ := M.typeLaw hi) (score := M.score) (z := z * cHi)
  have hlo :=
    iid_sum_mgf
      (ι := Fin nLo) (μ := M.typeLaw lo) (score := M.score)
      (z := -(z * cLo))
  simpa [FiniteRatingLDPModel.mgf] using congrArg₂ (fun a b => a * b) hhi hlo

/--
Two-population Chernoff upper bound for a finite scaled comparison event.  If
`z <= 0`, then on the event that the scaled high-low gap is nonpositive, the
indicator is bounded by `exp(z * gap)`.
-/
theorem twoSampleScoreGapLeftTailProb_le_mgf_product_of_nonpos
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) {z : ℝ}
    (hz : z ≤ 0) :
    twoSampleScoreGapLeftTailProb M hi lo nHi nLo cHi cLo ≤
      (M.mgf hi (z * cHi)) ^ nHi *
        (M.mgf lo (-(z * cLo))) ^ nLo := by
  classical
  let gap :
      (Fin nHi → Rating) × (Fin nLo → Rating) → ℝ :=
    fun sample => twoSampleScoreGapSum M cHi cLo sample
  have hpoint :
      ∀ sample : (Fin nHi → Rating) × (Fin nLo → Rating),
        (if gap sample ≤ 0 then (1 : ℝ) else 0) ≤
          Real.exp (z * gap sample) := by
    intro sample
    by_cases htail : gap sample ≤ 0
    · have hnonneg : 0 ≤ z * gap sample :=
        mul_nonneg_of_nonpos_of_nonpos hz htail
      simpa [htail] using Real.one_le_exp hnonneg
    · simp [htail, (Real.exp_pos _).le]
  calc
    twoSampleScoreGapLeftTailProb M hi lo nHi nLo cHi cLo
        =
        EconCSLib.pmfExp (twoSampleRatingLaw M hi lo nHi nLo)
          (fun sample => if gap sample ≤ 0 then (1 : ℝ) else 0) := by
          rfl
    _ ≤
        EconCSLib.pmfExp (twoSampleRatingLaw M hi lo nHi nLo)
          (fun sample => Real.exp (z * gap sample)) :=
          EconCSLib.pmfExp_le_pmfExp_of_forall_le
            (twoSampleRatingLaw M hi lo nHi nLo) _ _ hpoint
    _ =
        (M.mgf hi (z * cHi)) ^ nHi *
          (M.mgf lo (-(z * cLo))) ^ nLo := by
          simpa [gap] using
            twoSampleScoreGapSum_exp_mgf_eq_product
              M hi lo nHi nLo cHi cLo z

/--
Two-population Chernoff upper certificate for integer-linear sample rates.
With `n * gHi` high-type samples and `n * gLo` low-type samples, any
nonpositive dual parameter gives an exponential upper bound at every target
rate no larger than the displayed dual exponent.
-/
theorem twoSampleAverageGapLeftTail_hasExpUpperBoundWithConst_of_dual
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) {z targetRate : ℝ}
    (hz : z ≤ 0)
    (hrate :
      targetRate ≤
        -((gHi : ℝ) * M.logMGF hi (z * (gHi : ℝ)⁻¹) +
          (gLo : ℝ) * M.logMGF lo (-(z * (gLo : ℝ)⁻¹)))) :
    HasExpUpperBoundWithConst
      (fun n : ℕ =>
        twoSampleScoreGapLeftTailProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
      targetRate := by
  refine ⟨1, zero_lt_one, ?_⟩
  filter_upwards with n
  constructor
  · exact
      EconCSLib.pmfProb_nonneg
        (twoSampleRatingLaw M hi lo (n * gHi) (n * gLo))
        (fun sample =>
          twoSampleScoreGapSum M ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹) sample ≤ 0)
  · let LHi : ℝ := M.logMGF hi (z * (gHi : ℝ)⁻¹)
    let LLo : ℝ := M.logMGF lo (-(z * (gLo : ℝ)⁻¹))
    let dualLog : ℝ := (gHi : ℝ) * LHi + (gLo : ℝ) * LLo
    have hdual_le : dualLog ≤ -targetRate := by
      dsimp [dualLog, LHi, LLo]
      linarith
    have hchernoff :=
      twoSampleScoreGapLeftTailProb_le_mgf_product_of_nonpos
        M hi lo (n * gHi) (n * gLo)
        ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹) hz
    have hprod_eq :
        (M.mgf hi (z * (gHi : ℝ)⁻¹)) ^ (n * gHi) *
            (M.mgf lo (-(z * (gLo : ℝ)⁻¹))) ^ (n * gLo) =
          Real.exp ((n : ℝ) * dualLog) := by
      have hhi_pow :
          Real.exp LHi ^ (n * gHi) =
            Real.exp (((n * gHi : ℕ) : ℝ) * LHi) := by
        rw [Real.exp_nat_mul]
      have hlo_pow :
          Real.exp LLo ^ (n * gLo) =
            Real.exp (((n * gLo : ℕ) : ℝ) * LLo) := by
        rw [Real.exp_nat_mul]
      dsimp [dualLog, LHi, LLo]
      rw [← M.exp_logMGF hi (z * (gHi : ℝ)⁻¹)]
      rw [← M.exp_logMGF lo (-(z * (gLo : ℝ)⁻¹))]
      rw [hhi_pow, hlo_pow]
      rw [← Real.exp_add]
      congr 1
      norm_num [Nat.cast_mul]
      ring
    have hexp_le :
        Real.exp ((n : ℝ) * dualLog) ≤
          Real.exp (-(n : ℝ) * targetRate) := by
      apply Real.exp_le_exp.mpr
      calc
        (n : ℝ) * dualLog ≤ (n : ℝ) * (-targetRate) :=
          mul_le_mul_of_nonneg_left hdual_le (Nat.cast_nonneg n)
        _ = -(n : ℝ) * targetRate := by ring
    calc
      twoSampleScoreGapLeftTailProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹)
          ≤
          (M.mgf hi (z * (gHi : ℝ)⁻¹)) ^ (n * gHi) *
            (M.mgf lo (-(z * (gLo : ℝ)⁻¹))) ^ (n * gLo) := hchernoff
      _ = Real.exp ((n : ℝ) * dualLog) := hprod_eq
      _ ≤ 1 * Real.exp (-(n : ℝ) * targetRate) := by
        simpa using hexp_le

/--
Floor-count Chernoff upper bound for the source sample counts
`floor(k * g(theta))`.  Because the floor counts only converge to their sample
rates, the target exponent must be strictly below the displayed dual exponent.
-/
theorem twoSampleFloorAverageGapLeftTail_hasExpUpperBoundWithConst_of_dual
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    {z targetRate : ℝ}
    (hz : z ≤ 0)
    (hrate :
      targetRate <
        -((sampleRate hi) * M.logMGF hi (z * (sampleRate hi)⁻¹) +
          (sampleRate lo) * M.logMGF lo (-(z * (sampleRate lo)⁻¹)))) :
    HasExpUpperBoundWithConst
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      targetRate := by
  let nHi : ℕ → ℕ := fun k => floorSampleCount sampleRate hi k
  let nLo : ℕ → ℕ := fun k => floorSampleCount sampleRate lo k
  let fracHi : ℕ → ℝ := fun k => ((nHi k : ℕ) : ℝ) / (k : ℝ)
  let fracLo : ℕ → ℝ := fun k => ((nLo k : ℕ) : ℝ) / (k : ℝ)
  let coeffHi : ℕ → ℝ := fun k => (k : ℝ) * (((nHi k : ℕ) : ℝ)⁻¹)
  let coeffLo : ℕ → ℝ := fun k => (k : ℝ) * (((nLo k : ℕ) : ℝ)⁻¹)
  let limitLog : ℝ :=
    (sampleRate hi) * M.logMGF hi (z * (sampleRate hi)⁻¹) +
      (sampleRate lo) * M.logMGF lo (-(z * (sampleRate lo)⁻¹))
  let floorLog : ℕ → ℝ := fun k =>
    fracHi k * M.logMGF hi (z * coeffHi k) +
      fracLo k * M.logMGF lo (-(z * coeffLo k))
  have hfracHi :
      Filter.Tendsto fracHi Filter.atTop (nhds (sampleRate hi)) := by
    simpa [fracHi, nHi] using
      floorSampleCount_div_tendsto_sampleRate sampleRate hi hgHi.le
  have hfracLo :
      Filter.Tendsto fracLo Filter.atTop (nhds (sampleRate lo)) := by
    simpa [fracLo, nLo] using
      floorSampleCount_div_tendsto_sampleRate sampleRate lo hgLo.le
  have hcoeffHi :
      Filter.Tendsto coeffHi Filter.atTop (nhds ((sampleRate hi)⁻¹)) := by
    have hinv := hfracHi.inv₀ (ne_of_gt hgHi)
    refine Filter.Tendsto.congr' ?_ hinv
    have hfrac_pos : ∀ᶠ k in Filter.atTop, 0 < fracHi k :=
      hfracHi.eventually (Ioi_mem_nhds hgHi)
    filter_upwards [Filter.eventually_gt_atTop 0, hfrac_pos] with k hk hfrac
    have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
    have hn_pos : 0 < ((nHi k : ℕ) : ℝ) := by
      have hmul : 0 < fracHi k * (k : ℝ) :=
        mul_pos hfrac hk_pos
      simpa [fracHi, div_eq_mul_inv, hk_pos.ne'] using hmul
    dsimp [coeffHi, fracHi]
    field_simp [hk_pos.ne', hn_pos.ne']
  have hcoeffLo :
      Filter.Tendsto coeffLo Filter.atTop (nhds ((sampleRate lo)⁻¹)) := by
    have hinv := hfracLo.inv₀ (ne_of_gt hgLo)
    refine Filter.Tendsto.congr' ?_ hinv
    have hfrac_pos : ∀ᶠ k in Filter.atTop, 0 < fracLo k :=
      hfracLo.eventually (Ioi_mem_nhds hgLo)
    filter_upwards [Filter.eventually_gt_atTop 0, hfrac_pos] with k hk hfrac
    have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
    have hn_pos : 0 < ((nLo k : ℕ) : ℝ) := by
      have hmul : 0 < fracLo k * (k : ℝ) :=
        mul_pos hfrac hk_pos
      simpa [fracLo, div_eq_mul_inv, hk_pos.ne'] using hmul
    dsimp [coeffLo, fracLo]
    field_simp [hk_pos.ne', hn_pos.ne']
  have hlogHi :
      Filter.Tendsto
        (fun k : ℕ => M.logMGF hi (z * coeffHi k))
        Filter.atTop
        (nhds (M.logMGF hi (z * (sampleRate hi)⁻¹))) := by
    have harg :
        Filter.Tendsto (fun k : ℕ => z * coeffHi k)
          Filter.atTop (nhds (z * (sampleRate hi)⁻¹)) :=
      hcoeffHi.const_mul z
    simpa [FiniteRatingLDPModel.logMGF] using
      (finiteLogMGF_continuous (M.typeLaw hi) M.score).continuousAt.tendsto.comp
        harg
  have hlogLo :
      Filter.Tendsto
        (fun k : ℕ => M.logMGF lo (-(z * coeffLo k)))
        Filter.atTop
        (nhds (M.logMGF lo (-(z * (sampleRate lo)⁻¹)))) := by
    have harg :
        Filter.Tendsto (fun k : ℕ => -(z * coeffLo k))
          Filter.atTop (nhds (-(z * (sampleRate lo)⁻¹))) :=
      (hcoeffLo.const_mul z).neg
    simpa [FiniteRatingLDPModel.logMGF] using
      (finiteLogMGF_continuous (M.typeLaw lo) M.score).continuousAt.tendsto.comp
        harg
  have hfloorLog :
      Filter.Tendsto floorLog Filter.atTop (nhds limitLog) := by
    dsimp [floorLog, limitLog]
    exact (hfracHi.mul hlogHi).add (hfracLo.mul hlogLo)
  have hfloorLog_lt :
      ∀ᶠ k in Filter.atTop, floorLog k < -targetRate := by
    have hlimit_lt : limitLog < -targetRate := by
      dsimp [limitLog] at hrate ⊢
      linarith
    exact hfloorLog.eventually_lt_const hlimit_lt
  refine HasExpUpperBoundWithConst.of_eventually_le (C := 1) zero_lt_one ?_
  filter_upwards [hfloorLog_lt, Filter.eventually_gt_atTop 0] with k hlog_bound hk
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hscale_eq :
      twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo k =
        twoSampleScoreGapLeftTailProb M hi lo (nHi k) (nLo k)
          (coeffHi k) (coeffLo k) := by
    dsimp [twoSampleFloorScoreGapLeftTailProb, nHi, nLo, coeffHi, coeffLo]
    rw [← twoSampleScoreGapLeftTailProb_scale_pos
      M hi lo (floorSampleCount sampleRate hi k)
      (floorSampleCount sampleRate lo k)
      (((floorSampleCount sampleRate hi k : ℕ) : ℝ)⁻¹)
      (((floorSampleCount sampleRate lo k : ℕ) : ℝ)⁻¹)
      (k : ℝ) hk_pos]
  have hchernoff :
      twoSampleScoreGapLeftTailProb M hi lo (nHi k) (nLo k)
          (coeffHi k) (coeffLo k) ≤
        (M.mgf hi (z * coeffHi k)) ^ (nHi k) *
          (M.mgf lo (-(z * coeffLo k))) ^ (nLo k) :=
    twoSampleScoreGapLeftTailProb_le_mgf_product_of_nonpos
      M hi lo (nHi k) (nLo k) (coeffHi k) (coeffLo k) hz
  have hprod_eq :
      (M.mgf hi (z * coeffHi k)) ^ (nHi k) *
          (M.mgf lo (-(z * coeffLo k))) ^ (nLo k) =
        Real.exp ((k : ℝ) * floorLog k) := by
    have hhi_pow :
        Real.exp (M.logMGF hi (z * coeffHi k)) ^ (nHi k) =
          Real.exp (((nHi k : ℕ) : ℝ) * M.logMGF hi (z * coeffHi k)) := by
      rw [Real.exp_nat_mul]
    have hlo_pow :
        Real.exp (M.logMGF lo (-(z * coeffLo k))) ^ (nLo k) =
          Real.exp (((nLo k : ℕ) : ℝ) * M.logMGF lo (-(z * coeffLo k))) := by
      rw [Real.exp_nat_mul]
    rw [← M.exp_logMGF hi (z * coeffHi k)]
    rw [← M.exp_logMGF lo (-(z * coeffLo k))]
    rw [hhi_pow, hlo_pow]
    rw [← Real.exp_add]
    congr 1
    dsimp [floorLog, fracHi, fracLo]
    field_simp [hk_pos.ne']
  have hexp_le :
      Real.exp ((k : ℝ) * floorLog k) ≤
        Real.exp (-(k : ℝ) * targetRate) := by
    apply Real.exp_le_exp.mpr
    calc
      (k : ℝ) * floorLog k ≤ (k : ℝ) * (-targetRate) :=
        mul_le_mul_of_nonneg_left hlog_bound.le hk_pos.le
      _ = -(k : ℝ) * targetRate := by ring
  constructor
  · rw [hscale_eq]
    exact
      EconCSLib.pmfProb_nonneg
        (twoSampleRatingLaw M hi lo (nHi k) (nLo k))
        (fun sample =>
          twoSampleScoreGapSum M (coeffHi k) (coeffLo k) sample ≤ 0)
  · calc
      twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo k
          =
          twoSampleScoreGapLeftTailProb M hi lo (nHi k) (nLo k)
            (coeffHi k) (coeffLo k) := hscale_eq
      _ ≤
          (M.mgf hi (z * coeffHi k)) ^ (nHi k) *
            (M.mgf lo (-(z * coeffLo k))) ^ (nLo k) := hchernoff
      _ = Real.exp ((k : ℝ) * floorLog k) := hprod_eq
      _ ≤ 1 * Real.exp (-(k : ℝ) * targetRate) := by
        simpa using hexp_le

/--
Two one-population shifted left-tail events imply the two-population
nonpositive score-gap event: high average at most `a` and low average at
least `a` force high average minus low average to be nonpositive.
-/
theorem twoSampleScoreGapLeftTailProb_ge_shifted_tail_product
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (a : ℝ)
    (hnHi : 0 < nHi) (hnLo : 0 < nLo) :
    finiteIidScoreLeftTailProb (M.typeLaw hi)
        (fun r : Rating => M.score r - a) 0 nHi *
      finiteIidScoreLeftTailProb (M.typeLaw lo)
        (fun r : Rating => a - M.score r) 0 nLo ≤
      twoSampleScoreGapLeftTailProb M hi lo nHi nLo
        ((nHi : ℝ)⁻¹) ((nLo : ℝ)⁻¹) := by
  classical
  let μHi := EconCSLib.pmfProduct (Fin nHi) Rating (M.typeLaw hi)
  let μLo := EconCSLib.pmfProduct (Fin nLo) Rating (M.typeLaw lo)
  let hiEvent : (Fin nHi → Rating) → Prop :=
    fun sample =>
      finiteIidScoreSum (fun r : Rating => M.score r - a) sample ≤ 0
  let loEvent : (Fin nLo → Rating) → Prop :=
    fun sample =>
      finiteIidScoreSum (fun r : Rating => a - M.score r) sample ≤ 0
  let gapEvent : (Fin nHi → Rating) × (Fin nLo → Rating) → Prop :=
    fun sample =>
      twoSampleScoreGapSum M ((nHi : ℝ)⁻¹) ((nLo : ℝ)⁻¹) sample ≤ 0
  have hprod_eq :
      finiteIidScoreLeftTailProb (M.typeLaw hi)
          (fun r : Rating => M.score r - a) 0 nHi *
        finiteIidScoreLeftTailProb (M.typeLaw lo)
          (fun r : Rating => a - M.score r) 0 nLo =
      EconCSLib.pmfProb (twoSampleRatingLaw M hi lo nHi nLo)
        (fun sample => hiEvent sample.1 ∧ loEvent sample.2) := by
    rw [twoSampleRatingLaw]
    rw [EconCSLib.pmfProb_pmfProd_and_eq_mul_pmfProb]
    rfl
  have himp :
      ∀ sample : (Fin nHi → Rating) × (Fin nLo → Rating),
        hiEvent sample.1 ∧ loEvent sample.2 → gapEvent sample := by
    intro sample hsample
    rcases hsample with ⟨hhi, hlo⟩
    dsimp [hiEvent] at hhi
    dsimp [loEvent] at hlo
    have hnHi_pos : 0 < (nHi : ℝ) := by exact_mod_cast hnHi
    have hnLo_pos : 0 < (nLo : ℝ) := by exact_mod_cast hnLo
    have hhi_sum_eq :
        finiteIidScoreSum (fun r : Rating => M.score r - a) sample.1 =
          finiteIidScoreSum M.score sample.1 - (nHi : ℝ) * a := by
      unfold finiteIidScoreSum
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hlo_sum_eq :
        finiteIidScoreSum (fun r : Rating => a - M.score r) sample.2 =
          (nLo : ℝ) * a - finiteIidScoreSum M.score sample.2 := by
      unfold finiteIidScoreSum
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hhi_bound :
        finiteIidScoreSum M.score sample.1 ≤ (nHi : ℝ) * a := by
      rw [hhi_sum_eq] at hhi
      linarith
    have hlo_bound :
        (nLo : ℝ) * a ≤ finiteIidScoreSum M.score sample.2 := by
      rw [hlo_sum_eq] at hlo
      linarith
    have hhi_avg :
        (nHi : ℝ)⁻¹ * finiteIidScoreSum M.score sample.1 ≤ a := by
      calc
        (nHi : ℝ)⁻¹ * finiteIidScoreSum M.score sample.1
            ≤ (nHi : ℝ)⁻¹ * ((nHi : ℝ) * a) :=
              mul_le_mul_of_nonneg_left hhi_bound (inv_nonneg.mpr hnHi_pos.le)
        _ = a := by
          field_simp [hnHi_pos.ne']
    have hlo_avg :
        a ≤ (nLo : ℝ)⁻¹ * finiteIidScoreSum M.score sample.2 := by
      calc
        a = (nLo : ℝ)⁻¹ * ((nLo : ℝ) * a) := by
          field_simp [hnLo_pos.ne']
        _ ≤ (nLo : ℝ)⁻¹ * finiteIidScoreSum M.score sample.2 :=
          mul_le_mul_of_nonneg_left hlo_bound (inv_nonneg.mpr hnLo_pos.le)
    dsimp [gapEvent, twoSampleScoreGapSum]
    linarith
  calc
    finiteIidScoreLeftTailProb (M.typeLaw hi)
          (fun r : Rating => M.score r - a) 0 nHi *
        finiteIidScoreLeftTailProb (M.typeLaw lo)
          (fun r : Rating => a - M.score r) 0 nLo
        =
        EconCSLib.pmfProb (twoSampleRatingLaw M hi lo nHi nLo)
          (fun sample => hiEvent sample.1 ∧ loEvent sample.2) := hprod_eq
    _ ≤
        EconCSLib.pmfProb (twoSampleRatingLaw M hi lo nHi nLo) gapEvent :=
          EconCSLib.pmfProb_le_of_imp
            (twoSampleRatingLaw M hi lo nHi nLo)
            (fun sample => hiEvent sample.1 ∧ loEvent sample.2)
            gapEvent himp
    _ =
        twoSampleScoreGapLeftTailProb M hi lo nHi nLo
          ((nHi : ℝ)⁻¹) ((nLo : ℝ)⁻¹) := by
          rfl

/--
Floor-count lower-bound bridge from separate high and low shifted iid
left-tail lower bounds.
-/
theorem twoSampleFloorScoreGapLeftTail_hasExpLowerBoundWithConst_of_shifted_tail_bounds
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (a : ℝ)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    {rateHi rateLo targetRate : ℝ}
    (hHi :
      HasExpLowerBoundWithConst
        (fun n : ℕ =>
          finiteIidScoreLeftTailProb (M.typeLaw hi)
            (fun r : Rating => M.score r - a) 0 n)
        rateHi)
    (hLo :
      HasExpLowerBoundWithConst
        (fun n : ℕ =>
          finiteIidScoreLeftTailProb (M.typeLaw lo)
            (fun r : Rating => a - M.score r) 0 n)
        rateLo)
    (hrate :
      sampleRate hi * rateHi + sampleRate lo * rateLo < targetRate) :
    HasExpLowerBoundWithConst
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      targetRate := by
  let baseRate : ℝ := sampleRate hi * rateHi + sampleRate lo * rateLo
  let slack : ℝ := (targetRate - baseRate) / 3
  let targetHi : ℝ := sampleRate hi * rateHi + slack
  let targetLo : ℝ := sampleRate lo * rateLo + slack
  have hslack_pos : 0 < slack := by
    dsimp [slack, baseRate]
    linarith
  have hHi_scaled :
      HasExpLowerBoundWithConst
        (fun k : ℕ =>
          finiteIidScoreLeftTailProb (M.typeLaw hi)
            (fun r : Rating => M.score r - a) 0
            (floorSampleCount sampleRate hi k))
        targetHi := by
    simpa [floorSampleCount, targetHi] using
      HasExpLowerBoundWithConst.comp_nat_floor_mul_const
        hHi hgHi (by linarith [hslack_pos])
  have hLo_scaled :
      HasExpLowerBoundWithConst
        (fun k : ℕ =>
          finiteIidScoreLeftTailProb (M.typeLaw lo)
            (fun r : Rating => a - M.score r) 0
            (floorSampleCount sampleRate lo k))
        targetLo := by
    simpa [floorSampleCount, targetLo] using
      HasExpLowerBoundWithConst.comp_nat_floor_mul_const
        hLo hgLo (by linarith [hslack_pos])
  have hprod :
      HasExpLowerBoundWithConst
        (fun k : ℕ =>
          finiteIidScoreLeftTailProb (M.typeLaw hi)
            (fun r : Rating => M.score r - a) 0
            (floorSampleCount sampleRate hi k) *
          finiteIidScoreLeftTailProb (M.typeLaw lo)
            (fun r : Rating => a - M.score r) 0
            (floorSampleCount sampleRate lo k))
        (targetHi + targetLo) :=
    HasExpLowerBoundWithConst.mul hHi_scaled hLo_scaled
  have hnHi_pos :
      ∀ᶠ k : ℕ in Filter.atTop, 0 < floorSampleCount sampleRate hi k := by
    simpa [floorSampleCount] using
      (EconCSLib.Math.tendsto_nat_floor_mul_const_atTop hgHi).eventually
        (Filter.eventually_gt_atTop 0)
  have hnLo_pos :
      ∀ᶠ k : ℕ in Filter.atTop, 0 < floorSampleCount sampleRate lo k := by
    simpa [floorSampleCount] using
      (EconCSLib.Math.tendsto_nat_floor_mul_const_atTop hgLo).eventually
        (Filter.eventually_gt_atTop 0)
  have htarget_sum_le : targetHi + targetLo ≤ targetRate := by
    dsimp [targetHi, targetLo, slack, baseRate]
    linarith
  have hfloor_lower :
      HasExpLowerBoundWithConst
        (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
        (targetHi + targetLo) := by
    rcases hprod with ⟨c, hcpos, hprod_bound⟩
    refine HasExpLowerBoundWithConst.of_eventually_ge hcpos ?_
    filter_upwards [hprod_bound, hnHi_pos, hnLo_pos] with k hprod_k hnHi_k hnLo_k
    exact hprod_k.trans
      (by
        unfold twoSampleFloorScoreGapLeftTailProb
        exact
          twoSampleScoreGapLeftTailProb_ge_shifted_tail_product
            M hi lo
            (floorSampleCount sampleRate hi k)
            (floorSampleCount sampleRate lo k)
            a hnHi_k hnLo_k)
  exact hfloor_lower.weaken_rate htarget_sum_le

/--
Floor-count lower-bound bridge from separate high and low shifted finite iid
Cramer certificates.
-/
theorem twoSampleFloorScoreGapLeftTail_hasExpLowerBoundWithConst_of_shifted_cramer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (a : ℝ)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (C_hi :
      FiniteIidScoreCramerCertificate (M.typeLaw hi)
        (fun r : Rating => M.score r - a))
    (C_lo :
      FiniteIidScoreCramerCertificate (M.typeLaw lo)
        (fun r : Rating => a - M.score r))
    (rateHi rateLo : ℝ)
    (hrateHi :
      finiteChernoffRate (M.typeLaw hi)
        (fun r : Rating => M.score r - a) < rateHi)
    (hrateLo :
      finiteChernoffRate (M.typeLaw lo)
        (fun r : Rating => a - M.score r) < rateLo)
    {targetRate : ℝ}
    (hrate :
      sampleRate hi * rateHi + sampleRate lo * rateLo < targetRate) :
    HasExpLowerBoundWithConst
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      targetRate :=
  twoSampleFloorScoreGapLeftTail_hasExpLowerBoundWithConst_of_shifted_tail_bounds
    M sampleRate hi lo a hgHi hgLo
    (C_hi.lower_bounds rateHi hrateHi)
    (C_lo.lower_bounds rateLo hrateLo)
    hrate

/--
Exact floor-count pairwise score-gap certificate assembled from:
1. Chernoff upper bounds witnessed by source dual parameters, and
2. lower bounds for shifted high/low one-population tails.

This is the reusable arbitrary-real floor-count pairwise LDP connector.
-/
theorem twoSampleFloorScoreGapLeftTail_exponentialRateCertificate_of_dual_upper_and_shifted_lower_bounds
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    {rate : ℝ}
    (hupperDual :
      ∀ targetRate : ℝ, targetRate < rate →
        ∃ z : ℝ,
          z ≤ 0 ∧
            targetRate <
              -((sampleRate hi) *
                  M.logMGF hi (z * (sampleRate hi)⁻¹) +
                (sampleRate lo) *
                  M.logMGF lo (-(z * (sampleRate lo)⁻¹))))
    (hlowerShifted :
      ∀ targetRate : ℝ, rate < targetRate →
        ∃ a rateHi rateLo : ℝ,
          HasExpLowerBoundWithConst
            (fun n : ℕ =>
              finiteIidScoreLeftTailProb (M.typeLaw hi)
                (fun r : Rating => M.score r - a) 0 n)
            rateHi ∧
          HasExpLowerBoundWithConst
            (fun n : ℕ =>
              finiteIidScoreLeftTailProb (M.typeLaw lo)
                (fun r : Rating => a - M.score r) 0 n)
            rateLo ∧
          sampleRate hi * rateHi + sampleRate lo * rateLo < targetRate) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      rate := by
  refine ExponentialRateCertificate.of_expUpperLowerBounds ?_ ?_
  · intro targetRate htarget
    rcases hupperDual targetRate htarget with ⟨z, hz, hdual⟩
    exact
      twoSampleFloorAverageGapLeftTail_hasExpUpperBoundWithConst_of_dual
        M sampleRate hi lo hgHi hgLo hz hdual
  · intro targetRate htarget
    rcases hlowerShifted targetRate htarget with
      ⟨a, rateHi, rateLo, hHi, hLo, hrate⟩
    exact
      twoSampleFloorScoreGapLeftTail_hasExpLowerBoundWithConst_of_shifted_tail_bounds
        M sampleRate hi lo a hgHi hgLo hHi hLo hrate

/--
Exact floor-count pairwise score-gap certificate from a fixed shifted-Cramer
minimizer.  The equality hypothesis identifies the weighted high/low shifted
Chernoff exponents with the named pairwise source rate.
-/
theorem twoSampleFloorScoreGapLeftTail_exponentialRateCertificate_of_dual_upper_and_shifted_cramer_minimizer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a : ℝ)
    (C_hi :
      FiniteIidScoreCramerCertificate (M.typeLaw hi)
        (fun r : Rating => M.score r - a))
    (C_lo :
      FiniteIidScoreCramerCertificate (M.typeLaw lo)
        (fun r : Rating => a - M.score r))
    {rate : ℝ}
    (hrate_eq :
      sampleRate hi *
          finiteChernoffRate (M.typeLaw hi)
            (fun r : Rating => M.score r - a) +
        sampleRate lo *
          finiteChernoffRate (M.typeLaw lo)
            (fun r : Rating => a - M.score r) =
        rate)
    (hupperDual :
      ∀ targetRate : ℝ, targetRate < rate →
        ∃ z : ℝ,
          z ≤ 0 ∧
            targetRate <
              -((sampleRate hi) *
                  M.logMGF hi (z * (sampleRate hi)⁻¹) +
                (sampleRate lo) *
                  M.logMGF lo (-(z * (sampleRate lo)⁻¹)))) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      rate := by
  refine
    twoSampleFloorScoreGapLeftTail_exponentialRateCertificate_of_dual_upper_and_shifted_lower_bounds
      M sampleRate hi lo hgHi hgLo hupperDual ?_
  intro targetRate htarget
  let cherHi : ℝ :=
    finiteChernoffRate (M.typeLaw hi)
      (fun r : Rating => M.score r - a)
  let cherLo : ℝ :=
    finiteChernoffRate (M.typeLaw lo)
      (fun r : Rating => a - M.score r)
  let S : ℝ := sampleRate hi + sampleRate lo
  let eps : ℝ := (targetRate - rate) / (2 * (S + 1))
  have hrate_eq' : sampleRate hi * cherHi + sampleRate lo * cherLo = rate := by
    simpa [cherHi, cherLo] using hrate_eq
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    linarith [hgHi.le, hgLo.le]
  have hden_pos : 0 < 2 * (S + 1) := by
    nlinarith
  have heps_pos : 0 < eps := by
    dsimp [eps]
    exact div_pos (sub_pos.mpr htarget) hden_pos
  have hS_eps_le :
      S * eps ≤ (targetRate - rate) / 2 := by
    have hS_le : S ≤ S + 1 := by linarith
    calc
      S * eps ≤ (S + 1) * eps :=
        mul_le_mul_of_nonneg_right hS_le heps_pos.le
      _ = (targetRate - rate) / 2 := by
        dsimp [eps]
        field_simp [hden_pos.ne']
  refine
    ⟨a, cherHi + eps, cherLo + eps,
      C_hi.lower_bounds (cherHi + eps) (by dsimp [cherHi]; linarith),
      C_lo.lower_bounds (cherLo + eps) (by dsimp [cherLo]; linarith),
      ?_⟩
  calc
    sampleRate hi * (cherHi + eps) +
        sampleRate lo * (cherLo + eps)
        =
        rate + S * eps := by
          dsimp [S]
          rw [← hrate_eq']
          ring
    _ < targetRate := by
      have hhalf_lt : (targetRate - rate) / 2 < targetRate - rate := by
        linarith
      linarith

/--
Displayed-objective specialization of the arbitrary-real floor-count pairwise
score-gap certificate. Common-dual log-MGF derivative data at threshold `a`
gives the exact floor-count pairwise exponent
`g_hi I_hi(a) + g_lo I_lo(a)`, without appealing to the global source
threshold-rate infimum.
-/
theorem twoSampleFloorScoreGapLeftTail_pairwiseObjective_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_pos_neg_atoms
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)))
    {hiPos hiNeg loPos loNeg : Rating}
    (hmass_hi_pos : 0 < (M.typeLaw hi hiPos).toReal)
    (hscore_hi_pos : 0 < M.score hiPos - a)
    (hmass_hi_neg : 0 < (M.typeLaw hi hiNeg).toReal)
    (hscore_hi_neg : M.score hiNeg - a < 0)
    (hmass_lo_pos : 0 < (M.typeLaw lo loPos).toReal)
    (hscore_lo_pos : 0 < a - M.score loPos)
    (hmass_lo_neg : 0 < (M.typeLaw lo loNeg).toReal)
    (hscore_lo_neg : a - M.score loNeg < 0) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (M.pairwiseRateObjective sampleRate hi lo a) := by
  have hderiv_hi_finite :
      HasDerivAt (fun t : ℝ => finiteLogMGF (M.typeLaw hi) M.score t) a
        (z * (sampleRate hi)⁻¹) := by
    simpa [FiniteRatingLDPModel.logMGF] using hderiv_hi
  have hderiv_lo_finite :
      HasDerivAt (fun t : ℝ => finiteLogMGF (M.typeLaw lo) M.score t) a
        (-(z * (sampleRate lo)⁻¹)) := by
    simpa [FiniteRatingLDPModel.logMGF] using hderiv_lo
  have hdual_hi_nonpos : z * (sampleRate hi)⁻¹ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hz (inv_nonneg.mpr hgHi.le)
  have hdual_lo_nonneg : 0 ≤ -(z * (sampleRate lo)⁻¹) := by
    exact neg_nonneg.mpr
      (mul_nonpos_of_nonpos_of_nonneg hz (inv_nonneg.mpr hgLo.le))
  have hbdd_hi : BddAbove (Set.range fun t : ℝ =>
      finiteLegendreValue (M.typeLaw hi) M.score a t) :=
    finiteLegendreValue_bddAbove_of_logMGF_hasDerivAt
      (M.typeLaw hi) M.score a (z * (sampleRate hi)⁻¹)
      hderiv_hi_finite
  have hbdd_lo : BddAbove (Set.range fun t : ℝ =>
      finiteLegendreValue (M.typeLaw lo) M.score a t) :=
    finiteLegendreValue_bddAbove_of_logMGF_hasDerivAt
      (M.typeLaw lo) M.score a (-(z * (sampleRate lo)⁻¹))
      hderiv_lo_finite
  have hmean_hi_score :
      a ≤ EconCSLib.pmfExp (M.typeLaw hi) M.score :=
    finiteLogMGF_hasDerivAt_le_mean_of_nonpos
      (M.typeLaw hi) M.score hdual_hi_nonpos hderiv_hi_finite
  have hmean_lo_score :
      EconCSLib.pmfExp (M.typeLaw lo) M.score ≤ a :=
    finiteLogMGF_mean_le_hasDerivAt_of_nonneg
      (M.typeLaw lo) M.score hdual_lo_nonneg hderiv_lo_finite
  have hmean_hi :
      0 ≤
        EconCSLib.pmfExp (M.typeLaw hi)
          (fun r : Rating => M.score r - a) := by
    have hmean_eq :
        EconCSLib.pmfExp (M.typeLaw hi)
            (fun r : Rating => M.score r - a) =
          EconCSLib.pmfExp (M.typeLaw hi) M.score - a := by
      simpa using
        (EconCSLib.pmfExp_sub (M.typeLaw hi) M.score
          (fun _ : Rating => a))
    rw [hmean_eq]
    linarith
  have hmean_lo :
      0 ≤
        EconCSLib.pmfExp (M.typeLaw lo)
          (fun r : Rating => a - M.score r) := by
    have hmean_eq :
        EconCSLib.pmfExp (M.typeLaw lo)
            (fun r : Rating => a - M.score r) =
          a - EconCSLib.pmfExp (M.typeLaw lo) M.score := by
      simpa using
        (EconCSLib.pmfExp_sub (M.typeLaw lo)
          (fun _ : Rating => a) M.score)
    rw [hmean_eq]
    linarith
  letI : Nonempty Rating := ⟨hiPos⟩
  have C_hi :
      FiniteIidScoreCramerCertificate (M.typeLaw hi)
        (fun r : Rating => M.score r - a) :=
    finiteIidScoreCramerCertificate_of_logMGF_hasDerivAt_zero_empiricalTypes_of_pos_neg_atoms
      (M.typeLaw hi) (fun r : Rating => M.score r - a)
      hmean_hi hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
      (finiteLogMGF_sub_const_hasDerivAt_zero
        (M.typeLaw hi) M.score hderiv_hi_finite)
  have C_lo :
      FiniteIidScoreCramerCertificate (M.typeLaw lo)
        (fun r : Rating => a - M.score r) :=
    finiteIidScoreCramerCertificate_of_logMGF_hasDerivAt_zero_empiricalTypes_of_pos_neg_atoms
      (M.typeLaw lo) (fun r : Rating => a - M.score r)
      hmean_lo hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg
      (finiteLogMGF_const_sub_hasDerivAt_zero
        (M.typeLaw lo) M.score hderiv_lo_finite)
  have hchern_hi :
      finiteChernoffRate (M.typeLaw hi)
          (fun r : Rating => M.score r - a) =
        M.rateFunction hi a := by
    simpa [FiniteRatingLDPModel.rateFunction] using
      finiteChernoffRate_sub_const_eq_finiteRateFunction_of_logMGF_hasDerivAt
        (M.typeLaw hi) M.score a (z * (sampleRate hi)⁻¹)
        hbdd_hi hderiv_hi_finite
  have hchern_lo :
      finiteChernoffRate (M.typeLaw lo)
          (fun r : Rating => a - M.score r) =
        M.rateFunction lo a := by
    simpa [FiniteRatingLDPModel.rateFunction] using
      finiteChernoffRate_const_sub_eq_finiteRateFunction_of_logMGF_hasDerivAt
        (M.typeLaw lo) M.score a (z * (sampleRate lo)⁻¹)
        hbdd_lo hderiv_lo_finite
  have hshifted_rate :
      sampleRate hi *
          finiteChernoffRate (M.typeLaw hi)
            (fun r : Rating => M.score r - a) +
        sampleRate lo *
          finiteChernoffRate (M.typeLaw lo)
            (fun r : Rating => a - M.score r) =
        M.pairwiseRateObjective sampleRate hi lo a := by
    rw [hchern_hi, hchern_lo]
    rfl
  have hrate_hi :
      M.rateFunction hi a =
        (z * (sampleRate hi)⁻¹) * a -
          M.logMGF hi (z * (sampleRate hi)⁻¹) := by
    simpa [FiniteRatingLDPModel.rateFunction,
      FiniteRatingLDPModel.logMGF, finiteLegendreValue] using
      finiteRateFunction_eq_eval_of_logMGF_hasDerivAt
        (M.typeLaw hi) M.score a (z * (sampleRate hi)⁻¹)
        hbdd_hi hderiv_hi_finite
  have hrate_lo :
      M.rateFunction lo a =
        (-(z * (sampleRate lo)⁻¹)) * a -
          M.logMGF lo (-(z * (sampleRate lo)⁻¹)) := by
    simpa [FiniteRatingLDPModel.rateFunction,
      FiniteRatingLDPModel.logMGF, finiteLegendreValue] using
      finiteRateFunction_eq_eval_of_logMGF_hasDerivAt
        (M.typeLaw lo) M.score a (-(z * (sampleRate lo)⁻¹))
        hbdd_lo hderiv_lo_finite
  have hdual_rate :
      -((sampleRate hi) *
          M.logMGF hi (z * (sampleRate hi)⁻¹) +
        (sampleRate lo) *
          M.logMGF lo (-(z * (sampleRate lo)⁻¹))) =
        M.pairwiseRateObjective sampleRate hi lo a := by
    rw [FiniteRatingLDPModel.pairwiseRateObjective, hrate_hi, hrate_lo]
    field_simp [ne_of_gt hgHi, ne_of_gt hgLo]
    ring
  exact
    twoSampleFloorScoreGapLeftTail_exponentialRateCertificate_of_dual_upper_and_shifted_cramer_minimizer
      M sampleRate hi lo hgHi hgLo a C_hi C_lo hshifted_rate
      (fun targetRate htarget =>
        ⟨z, hz, by simpa [hdual_rate] using htarget⟩)

/--
Displayed-objective pairwise certificate using the compact two-sided-support
predicate around the derivative threshold.
-/
theorem twoSampleFloorScoreGapLeftTail_pairwiseObjective_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_straddling_support
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)))
    (hstraddle_hi : ratingLawStraddlesThreshold M hi a)
    (hstraddle_lo : ratingLawStraddlesThreshold M lo a) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (M.pairwiseRateObjective sampleRate hi lo a) := by
  rcases hstraddle_hi with
    ⟨⟨hiBelow, hmass_hi_below, hscore_hi_below⟩,
      ⟨hiAbove, hmass_hi_above, hscore_hi_above⟩⟩
  rcases hstraddle_lo with
    ⟨⟨loBelow, hmass_lo_below, hscore_lo_below⟩,
      ⟨loAbove, hmass_lo_above, hscore_lo_above⟩⟩
  exact
    twoSampleFloorScoreGapLeftTail_pairwiseObjective_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_pos_neg_atoms
      M sampleRate hi lo hgHi hgLo a z hz
      hderiv_hi hderiv_lo
      hmass_hi_above (by linarith)
      hmass_hi_below (by linarith)
      hmass_lo_below (by linarith)
      hmass_lo_above (by linarith)

/--
Support-safe pairwise LDP certificate directly from common-dual derivative
witnesses and finite two-sided support.  This avoids routing the finite-support
statement through the older all-real source threshold-rate equality.
-/
def PairwiseThresholdRateTopLdpCertificate.of_common_logMGF_derivatives_of_straddling_support
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (sampleRate (pairLo p))⁻¹)))
    (hstraddle_hi :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairHi p) (a p))
    (hstraddle_lo :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairLo p) (a p)) :
    PairwiseThresholdRateTopLdpCertificate M sampleRate pairHi pairLo where
  rate := fun p =>
    M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p) (a p)
  threshold_rate_top_eq := by
    intro p
    exact
      pairwiseSellerThresholdRateTop_eq_coe_pairwiseRateObjective_of_common_logMGF_derivatives
        M sampleRate (pairHi p) (pairLo p)
        (hpositive_hi p) (hpositive_lo p)
        (a p) (z p) (hderiv_hi p) (hderiv_lo p)
  leftTail := by
    intro p
    exact
      twoSampleFloorScoreGapLeftTail_pairwiseObjective_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_straddling_support
        M sampleRate (pairHi p) (pairLo p)
        (hpositive_hi p) (hpositive_lo p)
        (a p) (z p) (hz p)
        (hderiv_hi p) (hderiv_lo p)
        (hstraddle_hi p) (hstraddle_lo p)

/--
Support-safe pairwise LDP certificate from common-dual derivative witnesses
and primitive bottom/top rating support.
-/
def PairwiseThresholdRateTopLdpCertificate.of_common_logMGF_derivatives_and_score_bounds
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (sampleRate (pairLo p))⁻¹)))
    (rLow rHigh : Rating)
    (hmass_low_hi :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) rLow).toReal)
    (hmass_high_hi :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) rHigh).toReal)
    (hmass_low_lo :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) rLow).toReal)
    (hmass_high_lo :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_lt : M.score rLow < M.score rHigh) :
    PairwiseThresholdRateTopLdpCertificate M sampleRate pairHi pairLo :=
  PairwiseThresholdRateTopLdpCertificate.of_common_logMGF_derivatives_of_straddling_support
    M sampleRate pairHi pairLo hpositive_hi hpositive_lo a z hz
    hderiv_hi hderiv_lo
    (fun p =>
      ratingLawStraddlesThreshold_of_logMGF_hasDerivAt_of_score_bounds
        M (pairHi p) (hderiv_hi p)
        (hmass_low_hi p) (hmass_high_hi p)
        hscore_low_le hscore_le_high hscore_lt)
    (fun p =>
      ratingLawStraddlesThreshold_of_logMGF_hasDerivAt_of_score_bounds
        M (pairLo p) (hderiv_lo p)
        (hmass_low_lo p) (hmass_high_lo p)
        hscore_low_le hscore_le_high hscore_lt)

/--
Support-safe pairwise LDP certificate from stationary real-rate pairwise duals
and primitive bottom/top rating support.  The common threshold for each pair is
derived internally from the stationary dual equation.
-/
def PairwiseThresholdRateTopLdpCertificate.of_pairwise_dual_stationary_and_score_bounds
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hdual_stationary :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            pairwiseDualLogMGF M sampleRate (pairHi p) (pairLo p) t)
          0 (z p))
    (rLow rHigh : Rating)
    (hmass_low_hi :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) rLow).toReal)
    (hmass_high_hi :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) rHigh).toReal)
    (hmass_low_lo :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) rLow).toReal)
    (hmass_high_lo :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_lt : M.score rLow < M.score rHigh) :
    PairwiseThresholdRateTopLdpCertificate M sampleRate pairHi pairLo := by
  classical
  let hcommon :
      ∀ p : Pair, ∃ a : ℝ,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) a
          (z p * (sampleRate (pairHi p))⁻¹) ∧
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) a
          (-(z p * (sampleRate (pairLo p))⁻¹)) :=
    fun p =>
      exists_common_logMGF_derivatives_of_pairwiseDualLogMGF_hasDerivAt_zero
        M sampleRate (pairHi p) (pairLo p)
        (hpositive_hi p) (hpositive_lo p) (hdual_stationary p)
  let a : Pair → ℝ := fun p => Classical.choose (hcommon p)
  have hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (sampleRate (pairHi p))⁻¹) :=
    fun p => (Classical.choose_spec (hcommon p)).1
  have hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (sampleRate (pairLo p))⁻¹)) :=
    fun p => (Classical.choose_spec (hcommon p)).2
  exact
    PairwiseThresholdRateTopLdpCertificate.of_common_logMGF_derivatives_and_score_bounds
      M sampleRate pairHi pairLo hpositive_hi hpositive_lo
      a z hz hderiv_hi hderiv_lo
      rLow rHigh hmass_low_hi hmass_high_hi hmass_low_lo hmass_high_lo
      hscore_low_le hscore_le_high hscore_lt

/--
Support-safe pairwise LDP certificate from expected-score ordering plus a
nonpositive tilted-mean crossing.  The stationary duals are selected by the
finite IVT bridge and then fed into the common-threshold constructor.
-/
def PairwiseThresholdRateTopLdpCertificate.of_expected_score_gap_and_tilted_crossing_and_score_bounds
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (hmean_gap :
      ∀ p : Pair,
        EconCSLib.pmfExp (M.typeLaw (pairLo p)) M.score ≤
          EconCSLib.pmfExp (M.typeLaw (pairHi p)) M.score)
    (zCross : Pair → ℝ)
    (hzCross : ∀ p : Pair, zCross p ≤ 0)
    (hcross :
      ∀ p : Pair,
        pairwiseTiltedScoreMeanGap M sampleRate (pairHi p) (pairLo p)
          (zCross p) ≤ 0)
    (rLow rHigh : Rating)
    (hmass_low_hi :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) rLow).toReal)
    (hmass_high_hi :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) rHigh).toReal)
    (hmass_low_lo :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) rLow).toReal)
    (hmass_high_lo :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_lt : M.score rLow < M.score rHigh) :
    PairwiseThresholdRateTopLdpCertificate M sampleRate pairHi pairLo := by
  classical
  let hstationary :
      ∀ p : Pair, ∃ z : ℝ, z ≤ 0 ∧
        HasDerivAt
          (fun t : ℝ =>
            pairwiseDualLogMGF M sampleRate (pairHi p) (pairLo p) t)
          0 z :=
    fun p =>
      exists_nonpos_pairwiseDualLogMGF_stationary_of_expected_score_gap_and_tilted_crossing
        M sampleRate (pairHi p) (pairLo p)
        (hpositive_hi p) (hpositive_lo p)
        (hmean_gap p) (hzCross p) (hcross p)
  let z : Pair → ℝ := fun p => Classical.choose (hstationary p)
  have hz : ∀ p : Pair, z p ≤ 0 :=
    fun p => (Classical.choose_spec (hstationary p)).1
  have hdual_stationary :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            pairwiseDualLogMGF M sampleRate (pairHi p) (pairLo p) t)
          0 (z p) :=
    fun p => (Classical.choose_spec (hstationary p)).2
  exact
    PairwiseThresholdRateTopLdpCertificate.of_pairwise_dual_stationary_and_score_bounds
      M sampleRate pairHi pairLo hpositive_hi hpositive_lo
      z hz hdual_stationary rLow rHigh
      hmass_low_hi hmass_high_hi hmass_low_lo hmass_high_lo
      hscore_low_le hscore_le_high hscore_lt

/--
Support-safe pairwise LDP certificate from expected-score ordering and
primitive common bottom/top finite support.  The nonpositive stationary duals
are derived internally from the finite extreme-support tilt bridge.
-/
def PairwiseThresholdRateTopLdpCertificate.of_expected_score_gap_and_common_extreme_support
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (hmean_gap :
      ∀ p : Pair,
        EconCSLib.pmfExp (M.typeLaw (pairLo p)) M.score ≤
          EconCSLib.pmfExp (M.typeLaw (pairHi p)) M.score)
    (rLow rHigh : Rating)
    (hmass_low_hi :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) rLow).toReal)
    (hmass_high_hi :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) rHigh).toReal)
    (hmass_low_lo :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) rLow).toReal)
    (hmass_high_lo :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_lt : M.score rLow < M.score rHigh) :
    PairwiseThresholdRateTopLdpCertificate M sampleRate pairHi pairLo := by
  classical
  let hstationary :
      ∀ p : Pair, ∃ z : ℝ, z ≤ 0 ∧
        HasDerivAt
          (fun t : ℝ =>
            pairwiseDualLogMGF M sampleRate (pairHi p) (pairLo p) t)
          0 z :=
    fun p =>
      exists_nonpos_pairwiseDualLogMGF_stationary_of_expected_score_gap_and_common_extreme_support
        M sampleRate (pairHi p) (pairLo p)
        (hpositive_hi p) (hpositive_lo p)
        (hmean_gap p) rLow rHigh
        (hmass_low_hi p) (hmass_high_hi p)
        (hmass_low_lo p) (hmass_high_lo p)
        hscore_low_le hscore_le_high hscore_lt
  let z : Pair → ℝ := fun p => Classical.choose (hstationary p)
  have hz : ∀ p : Pair, z p ≤ 0 :=
    fun p => (Classical.choose_spec (hstationary p)).1
  have hdual_stationary :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            pairwiseDualLogMGF M sampleRate (pairHi p) (pairLo p) t)
          0 (z p) :=
    fun p => (Classical.choose_spec (hstationary p)).2
  exact
    PairwiseThresholdRateTopLdpCertificate.of_pairwise_dual_stationary_and_score_bounds
      M sampleRate pairHi pairLo hpositive_hi hpositive_lo
      z hz hdual_stationary rLow rHigh
      hmass_low_hi hmass_high_hi hmass_low_lo hmass_high_lo
      hscore_low_le hscore_le_high hscore_lt

/--
Source-threshold specialization of the arbitrary-real floor-count pairwise
score-gap certificate.
-/
theorem twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_shifted_cramer_minimizer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (C_hi :
      FiniteIidScoreCramerCertificate (M.typeLaw hi)
        (fun r : Rating => M.score r - a))
    (C_lo :
      FiniteIidScoreCramerCertificate (M.typeLaw lo)
        (fun r : Rating => a - M.score r))
    (hshifted_rate :
      sampleRate hi *
          finiteChernoffRate (M.typeLaw hi)
            (fun r : Rating => M.score r - a) +
        sampleRate lo *
          finiteChernoffRate (M.typeLaw lo)
            (fun r : Rating => a - M.score r) =
        pairwiseSellerThresholdRate M sampleRate hi lo)
    (hdual_rate :
      -((sampleRate hi) *
          M.logMGF hi (z * (sampleRate hi)⁻¹) +
        (sampleRate lo) *
          M.logMGF lo (-(z * (sampleRate lo)⁻¹))) =
        pairwiseSellerThresholdRate M sampleRate hi lo) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleFloorScoreGapLeftTail_exponentialRateCertificate_of_dual_upper_and_shifted_cramer_minimizer
    M sampleRate hi lo hgHi hgLo a C_hi C_lo hshifted_rate
    (fun targetRate htarget =>
      ⟨z, hz, by simpa [hdual_rate] using htarget⟩)

/--
Source-threshold floor-count pairwise certificate from the paper's common
threshold derivative data.  The shifted one-population Cramer certificates and
the shifted/source-rate identities are discharged internally from finite-MGF
shift algebra.
-/
theorem twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (hbdd_hi : BddAbove (Set.range fun t : ℝ =>
      finiteLegendreValue (M.typeLaw hi) M.score a t))
    (hbdd_lo : BddAbove (Set.range fun t : ℝ =>
      finiteLegendreValue (M.typeLaw lo) M.score a t))
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)))
    (hthreshold_eq :
      M.pairwiseRateObjective sampleRate hi lo a =
        pairwiseSellerThresholdRate M sampleRate hi lo)
    (hmean_hi :
      0 ≤
        EconCSLib.pmfExp (M.typeLaw hi)
          (fun r : Rating => M.score r - a))
    (hmean_lo :
      0 ≤
        EconCSLib.pmfExp (M.typeLaw lo)
          (fun r : Rating => a - M.score r))
    {hiPos hiNeg loPos loNeg : Rating}
    (hmass_hi_pos : 0 < (M.typeLaw hi hiPos).toReal)
    (hscore_hi_pos : 0 < M.score hiPos - a)
    (hmass_hi_neg : 0 < (M.typeLaw hi hiNeg).toReal)
    (hscore_hi_neg : M.score hiNeg - a < 0)
    (hmass_lo_pos : 0 < (M.typeLaw lo loPos).toReal)
    (hscore_lo_pos : 0 < a - M.score loPos)
    (hmass_lo_neg : 0 < (M.typeLaw lo loNeg).toReal)
    (hscore_lo_neg : a - M.score loNeg < 0) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) := by
  letI : Nonempty Rating := ⟨hiPos⟩
  have hderiv_hi_finite :
      HasDerivAt (fun t : ℝ => finiteLogMGF (M.typeLaw hi) M.score t) a
        (z * (sampleRate hi)⁻¹) := by
    simpa [FiniteRatingLDPModel.logMGF] using hderiv_hi
  have hderiv_lo_finite :
      HasDerivAt (fun t : ℝ => finiteLogMGF (M.typeLaw lo) M.score t) a
        (-(z * (sampleRate lo)⁻¹)) := by
    simpa [FiniteRatingLDPModel.logMGF] using hderiv_lo
  have C_hi :
      FiniteIidScoreCramerCertificate (M.typeLaw hi)
        (fun r : Rating => M.score r - a) :=
    finiteIidScoreCramerCertificate_of_logMGF_hasDerivAt_zero_empiricalTypes_of_pos_neg_atoms
      (M.typeLaw hi) (fun r : Rating => M.score r - a)
      hmean_hi hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
      (finiteLogMGF_sub_const_hasDerivAt_zero
        (M.typeLaw hi) M.score hderiv_hi_finite)
  have C_lo :
      FiniteIidScoreCramerCertificate (M.typeLaw lo)
        (fun r : Rating => a - M.score r) :=
    finiteIidScoreCramerCertificate_of_logMGF_hasDerivAt_zero_empiricalTypes_of_pos_neg_atoms
      (M.typeLaw lo) (fun r : Rating => a - M.score r)
      hmean_lo hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg
      (finiteLogMGF_const_sub_hasDerivAt_zero
        (M.typeLaw lo) M.score hderiv_lo_finite)
  have hchern_hi :
      finiteChernoffRate (M.typeLaw hi)
          (fun r : Rating => M.score r - a) =
        M.rateFunction hi a := by
    simpa [FiniteRatingLDPModel.rateFunction] using
      finiteChernoffRate_sub_const_eq_finiteRateFunction_of_logMGF_hasDerivAt
        (M.typeLaw hi) M.score a (z * (sampleRate hi)⁻¹)
        hbdd_hi hderiv_hi_finite
  have hchern_lo :
      finiteChernoffRate (M.typeLaw lo)
          (fun r : Rating => a - M.score r) =
        M.rateFunction lo a := by
    simpa [FiniteRatingLDPModel.rateFunction] using
      finiteChernoffRate_const_sub_eq_finiteRateFunction_of_logMGF_hasDerivAt
        (M.typeLaw lo) M.score a (z * (sampleRate lo)⁻¹)
        hbdd_lo hderiv_lo_finite
  have hshifted_rate :
      sampleRate hi *
          finiteChernoffRate (M.typeLaw hi)
            (fun r : Rating => M.score r - a) +
        sampleRate lo *
          finiteChernoffRate (M.typeLaw lo)
            (fun r : Rating => a - M.score r) =
        pairwiseSellerThresholdRate M sampleRate hi lo := by
    rw [hchern_hi, hchern_lo]
    simpa [FiniteRatingLDPModel.pairwiseRateObjective] using hthreshold_eq
  have hrate_hi :
      M.rateFunction hi a =
        (z * (sampleRate hi)⁻¹) * a -
          M.logMGF hi (z * (sampleRate hi)⁻¹) := by
    simpa [FiniteRatingLDPModel.rateFunction,
      FiniteRatingLDPModel.logMGF, finiteLegendreValue] using
      finiteRateFunction_eq_eval_of_logMGF_hasDerivAt
        (M.typeLaw hi) M.score a (z * (sampleRate hi)⁻¹)
        hbdd_hi hderiv_hi_finite
  have hrate_lo :
      M.rateFunction lo a =
        (-(z * (sampleRate lo)⁻¹)) * a -
          M.logMGF lo (-(z * (sampleRate lo)⁻¹)) := by
    simpa [FiniteRatingLDPModel.rateFunction,
      FiniteRatingLDPModel.logMGF, finiteLegendreValue] using
      finiteRateFunction_eq_eval_of_logMGF_hasDerivAt
        (M.typeLaw lo) M.score a (-(z * (sampleRate lo)⁻¹))
        hbdd_lo hderiv_lo_finite
  have hdual_rate :
      -((sampleRate hi) *
          M.logMGF hi (z * (sampleRate hi)⁻¹) +
        (sampleRate lo) *
          M.logMGF lo (-(z * (sampleRate lo)⁻¹))) =
        pairwiseSellerThresholdRate M sampleRate hi lo := by
    calc
      -((sampleRate hi) *
          M.logMGF hi (z * (sampleRate hi)⁻¹) +
        (sampleRate lo) *
          M.logMGF lo (-(z * (sampleRate lo)⁻¹)))
          =
          M.pairwiseRateObjective sampleRate hi lo a := by
            rw [FiniteRatingLDPModel.pairwiseRateObjective,
              hrate_hi, hrate_lo]
            field_simp [ne_of_gt hgHi, ne_of_gt hgLo]
            ring
      _ = pairwiseSellerThresholdRate M sampleRate hi lo := hthreshold_eq
  exact
    twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_shifted_cramer_minimizer
      M sampleRate hi lo hgHi hgLo a z hz
      C_hi C_lo hshifted_rate hdual_rate

/--
Source-threshold floor-count pairwise certificate from the paper's common
threshold derivative data, with Legendre boundedness and shifted mean signs
derived internally from finite log-MGF convexity.  The remaining support-atom
hypotheses are the finite-support nondegeneracy inputs needed by the empirical
type Cramer certificate.
-/
theorem twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_pos_neg_atoms
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)))
    (hthreshold_eq :
      M.pairwiseRateObjective sampleRate hi lo a =
        pairwiseSellerThresholdRate M sampleRate hi lo)
    {hiPos hiNeg loPos loNeg : Rating}
    (hmass_hi_pos : 0 < (M.typeLaw hi hiPos).toReal)
    (hscore_hi_pos : 0 < M.score hiPos - a)
    (hmass_hi_neg : 0 < (M.typeLaw hi hiNeg).toReal)
    (hscore_hi_neg : M.score hiNeg - a < 0)
    (hmass_lo_pos : 0 < (M.typeLaw lo loPos).toReal)
    (hscore_lo_pos : 0 < a - M.score loPos)
    (hmass_lo_neg : 0 < (M.typeLaw lo loNeg).toReal)
    (hscore_lo_neg : a - M.score loNeg < 0) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) := by
  have hderiv_hi_finite :
      HasDerivAt (fun t : ℝ => finiteLogMGF (M.typeLaw hi) M.score t) a
        (z * (sampleRate hi)⁻¹) := by
    simpa [FiniteRatingLDPModel.logMGF] using hderiv_hi
  have hderiv_lo_finite :
      HasDerivAt (fun t : ℝ => finiteLogMGF (M.typeLaw lo) M.score t) a
        (-(z * (sampleRate lo)⁻¹)) := by
    simpa [FiniteRatingLDPModel.logMGF] using hderiv_lo
  have hdual_hi_nonpos : z * (sampleRate hi)⁻¹ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hz (inv_nonneg.mpr hgHi.le)
  have hdual_lo_nonneg : 0 ≤ -(z * (sampleRate lo)⁻¹) := by
    exact neg_nonneg.mpr
      (mul_nonpos_of_nonpos_of_nonneg hz (inv_nonneg.mpr hgLo.le))
  have hbdd_hi : BddAbove (Set.range fun t : ℝ =>
      finiteLegendreValue (M.typeLaw hi) M.score a t) :=
    finiteLegendreValue_bddAbove_of_logMGF_hasDerivAt
      (M.typeLaw hi) M.score a (z * (sampleRate hi)⁻¹)
      hderiv_hi_finite
  have hbdd_lo : BddAbove (Set.range fun t : ℝ =>
      finiteLegendreValue (M.typeLaw lo) M.score a t) :=
    finiteLegendreValue_bddAbove_of_logMGF_hasDerivAt
      (M.typeLaw lo) M.score a (-(z * (sampleRate lo)⁻¹))
      hderiv_lo_finite
  have hmean_hi_score :
      a ≤ EconCSLib.pmfExp (M.typeLaw hi) M.score :=
    finiteLogMGF_hasDerivAt_le_mean_of_nonpos
      (M.typeLaw hi) M.score hdual_hi_nonpos hderiv_hi_finite
  have hmean_lo_score :
      EconCSLib.pmfExp (M.typeLaw lo) M.score ≤ a :=
    finiteLogMGF_mean_le_hasDerivAt_of_nonneg
      (M.typeLaw lo) M.score hdual_lo_nonneg hderiv_lo_finite
  have hmean_hi :
      0 ≤
        EconCSLib.pmfExp (M.typeLaw hi)
          (fun r : Rating => M.score r - a) := by
    have hmean_eq :
        EconCSLib.pmfExp (M.typeLaw hi)
            (fun r : Rating => M.score r - a) =
          EconCSLib.pmfExp (M.typeLaw hi) M.score - a := by
      simpa using
        (EconCSLib.pmfExp_sub (M.typeLaw hi) M.score
          (fun _ : Rating => a))
    rw [hmean_eq]
    linarith
  have hmean_lo :
      0 ≤
        EconCSLib.pmfExp (M.typeLaw lo)
          (fun r : Rating => a - M.score r) := by
    have hmean_eq :
        EconCSLib.pmfExp (M.typeLaw lo)
            (fun r : Rating => a - M.score r) =
          a - EconCSLib.pmfExp (M.typeLaw lo) M.score := by
      simpa using
        (EconCSLib.pmfExp_sub (M.typeLaw lo)
          (fun _ : Rating => a) M.score)
    rw [hmean_eq]
    linarith
  exact
    twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer
      M sampleRate hi lo hgHi hgLo a z hz hbdd_hi hbdd_lo
      hderiv_hi hderiv_lo hthreshold_eq hmean_hi hmean_lo
      hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
      hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg

/--
Source-threshold floor-count pairwise certificate from common threshold
derivative data and a compact two-sided-support predicate for each type law.
-/
theorem twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_straddling_support
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)))
    (hthreshold_eq :
      M.pairwiseRateObjective sampleRate hi lo a =
        pairwiseSellerThresholdRate M sampleRate hi lo)
    (hstraddle_hi : ratingLawStraddlesThreshold M hi a)
    (hstraddle_lo : ratingLawStraddlesThreshold M lo a) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) := by
  rcases hstraddle_hi with
    ⟨⟨hiBelow, hmass_hi_below, hscore_hi_below⟩,
      ⟨hiAbove, hmass_hi_above, hscore_hi_above⟩⟩
  rcases hstraddle_lo with
    ⟨⟨loBelow, hmass_lo_below, hscore_lo_below⟩,
      ⟨loAbove, hmass_lo_above, hscore_lo_above⟩⟩
  exact
    twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_pos_neg_atoms
      M sampleRate hi lo hgHi hgLo a z hz
      hderiv_hi hderiv_lo hthreshold_eq
      hmass_hi_above (by linarith)
      hmass_hi_below (by linarith)
      hmass_lo_below (by linarith)
      hmass_lo_above (by linarith)

/--
Source-threshold floor-count pairwise certificate where the common threshold is
specified as a minimizer of the source pairwise rate objective, rather than by
an already-evaluated `sInf` equality.
-/
theorem twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivative_threshold_minimizer_of_straddling_support
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)))
    (hthreshold_min :
      ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate hi lo a ≤
          M.pairwiseRateObjective sampleRate hi lo b)
    (hstraddle_hi : ratingLawStraddlesThreshold M hi a)
    (hstraddle_lo : ratingLawStraddlesThreshold M lo a) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_straddling_support
    M sampleRate hi lo hgHi hgLo a z hz hderiv_hi hderiv_lo
    (pairwiseSellerThresholdRate_eq_of_pairwiseRateObjective_minimizer
      M sampleRate hi lo a hthreshold_min)
    hstraddle_hi hstraddle_lo

/--
The paper-facing pairwise regularity package supplies the support-safe LDP
certificate used by the extended-rate Theorem 1 endpoint.  This packages the
finite source threshold representative together with the exact floor-count
left-tail LDP certificate.
-/
def PairwiseThresholdRateTopLdpCertificate.of_regularity
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (C : PairwiseThresholdRateRegularity M sampleRate pairHi pairLo) :
    PairwiseThresholdRateTopLdpCertificate M sampleRate pairHi pairLo where
  rate := fun p =>
    pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)
  threshold_rate_top_eq := by
    intro p
    have htop :
        pairwiseSellerThresholdRateTop M sampleRate (pairHi p) (pairLo p) =
          (M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p)
            (C.threshold p) : WithTop ℝ) :=
      pairwiseSellerThresholdRateTop_eq_coe_pairwiseRateObjective_of_common_logMGF_derivatives
        M sampleRate (pairHi p) (pairLo p)
        (hpositive_hi p) (hpositive_lo p)
        (C.threshold p) (C.dual p) (C.deriv_hi p) (C.deriv_lo p)
    simpa [C.threshold_rate_eq p] using htop
  leftTail := by
    intro p
    exact
      twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_straddling_support
        M sampleRate (pairHi p) (pairLo p)
        (hpositive_hi p) (hpositive_lo p)
        (C.threshold p) (C.dual p) (C.dual_nonpos p)
        (C.deriv_hi p) (C.deriv_lo p)
        (C.threshold_rate_eq p) (C.straddles_hi p) (C.straddles_lo p)

/--
Source-threshold floor-count pairwise certificate from common threshold
derivative data and compact two-sided support. The displayed threshold is
proved to minimize the source pairwise objective by Fenchel optimality; the
all-threshold boundedness hypotheses are the current real-valued rate-function
API side condition for that minimizer proof.
-/
theorem twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivatives_of_straddling_support
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hbdd_hi :
      ∀ b : ℝ, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score b t))
    (hbdd_lo :
      ∀ b : ℝ, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score b t))
    (a z : ℝ) (hz : z ≤ 0)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)))
    (hstraddle_hi : ratingLawStraddlesThreshold M hi a)
    (hstraddle_lo : ratingLawStraddlesThreshold M lo a) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_straddling_support
    M sampleRate hi lo hgHi hgLo a z hz hderiv_hi hderiv_lo
    (pairwiseSellerThresholdRate_eq_of_common_logMGF_derivatives
      M sampleRate hi lo hgHi hgLo hbdd_hi hbdd_lo a z
      hderiv_hi hderiv_lo)
    hstraddle_hi hstraddle_lo

/--
One integer-rate comparison block: `gHi` high-type ratings and `gLo` low-type
ratings, drawn independently.  Repeating this block `n` times represents the
source integer sample-rate regime `n * gHi`, `n * gLo`.
-/
abbrev twoSampleRateBlockLaw
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) :
    PMF ((Fin gHi → Rating) × (Fin gLo → Rating)) :=
  twoSampleRatingLaw M hi lo gHi gLo

/-- Average-score gap for one integer-rate comparison block. -/
def twoSampleRateBlockScore
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (gHi gLo : ℕ)
    (sample : (Fin gHi → Rating) × (Fin gLo → Rating)) : ℝ :=
  twoSampleScoreGapSum M ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹) sample

/--
Block-grouped integer-rate comparison error.  This is the finite iid sequence
whose one-step law is `twoSampleRateBlockLaw`.
-/
def twoSampleRateBlockErrorProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) (n : ℕ) : ℝ :=
  finiteIidScoreLeftTailProb
    (twoSampleRateBlockLaw M hi lo gHi gLo)
    (twoSampleRateBlockScore M gHi gLo) 0 n

/--
Flatten `n` integer-rate comparison blocks into the ungrouped two-sample
arrays with `n * gHi` high ratings and `n * gLo` low ratings.
-/
def flattenRateBlockSample
    {Rating : Type*} (n gHi gLo : ℕ)
    (sample : Fin n → (Fin gHi → Rating) × (Fin gLo → Rating)) :
    (Fin (n * gHi) → Rating) × (Fin (n * gLo) → Rating) :=
  (fun j => (sample ((finProdFinEquiv (m := n) (n := gHi)).symm j).1).1
      ((finProdFinEquiv (m := n) (n := gHi)).symm j).2,
    fun j => (sample ((finProdFinEquiv (m := n) (n := gLo)).symm j).1).2
      ((finProdFinEquiv (m := n) (n := gLo)).symm j).2)

/-- Regroup flattened two-sample arrays into integer-rate comparison blocks. -/
def unflattenRateBlockSample
    {Rating : Type*} (n gHi gLo : ℕ)
    (sample : (Fin (n * gHi) → Rating) × (Fin (n * gLo) → Rating)) :
    Fin n → (Fin gHi → Rating) × (Fin gLo → Rating) :=
  fun b =>
    (fun r => sample.1 ((finProdFinEquiv (m := n) (n := gHi)) (b, r)),
      fun r => sample.2 ((finProdFinEquiv (m := n) (n := gLo)) (b, r)))

/-- Block samples and ungrouped integer-rate two-sample arrays are equivalent. -/
def twoSampleRateBlockSampleEquiv
    (Rating : Type*) (n gHi gLo : ℕ) :
    (Fin n → (Fin gHi → Rating) × (Fin gLo → Rating)) ≃
      (Fin (n * gHi) → Rating) × (Fin (n * gLo) → Rating) where
  toFun := flattenRateBlockSample n gHi gLo
  invFun := unflattenRateBlockSample n gHi gLo
  left_inv sample := by
    funext b
    ext r
    · change
        (sample
          (((finProdFinEquiv (m := n) (n := gHi)).symm
            ((finProdFinEquiv (m := n) (n := gHi)) (b, r))).1)).1
          (((finProdFinEquiv (m := n) (n := gHi)).symm
            ((finProdFinEquiv (m := n) (n := gHi)) (b, r))).2) =
          (sample b).1 r
      rw [Equiv.symm_apply_apply]
    · change
        (sample
          (((finProdFinEquiv (m := n) (n := gLo)).symm
            ((finProdFinEquiv (m := n) (n := gLo)) (b, r))).1)).2
          (((finProdFinEquiv (m := n) (n := gLo)).symm
            ((finProdFinEquiv (m := n) (n := gLo)) (b, r))).2) =
          (sample b).2 r
      rw [Equiv.symm_apply_apply]
  right_inv sample := by
    ext j
    · change
        sample.1
          ((finProdFinEquiv (m := n) (n := gHi))
            ((finProdFinEquiv (m := n) (n := gHi)).symm j)) =
          sample.1 j
      rw [Equiv.apply_symm_apply]
    · change
        sample.2
          ((finProdFinEquiv (m := n) (n := gLo))
            ((finProdFinEquiv (m := n) (n := gLo)).symm j)) =
          sample.2 j
      rw [Equiv.apply_symm_apply]

/--
The flattened ungrouped score gap is the same sum as the repeated block score.
-/
theorem finiteIidScoreSum_rateBlockScore_eq_twoSampleScoreGapSum_flatten
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (gHi gLo n : ℕ)
    (sample : Fin n → (Fin gHi → Rating) × (Fin gLo → Rating)) :
    finiteIidScoreSum (twoSampleRateBlockScore M gHi gLo) sample =
      twoSampleScoreGapSum M ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹)
        (flattenRateBlockSample n gHi gLo sample) := by
  classical
  let eHi := finProdFinEquiv (m := n) (n := gHi)
  let eLo := finProdFinEquiv (m := n) (n := gLo)
  have hhi_flat :
      (∑ j : Fin (n * gHi),
        M.score ((sample ((eHi.symm j).1)).1 ((eHi.symm j).2))) =
        ∑ b : Fin n, ∑ r : Fin gHi, M.score ((sample b).1 r) := by
    calc
      (∑ j : Fin (n * gHi),
        M.score ((sample ((eHi.symm j).1)).1 ((eHi.symm j).2)))
          =
          ∑ p : Fin n × Fin gHi,
            M.score ((sample p.1).1 p.2) := by
            symm
            simpa [eHi] using
              (Equiv.sum_comp eHi
                (fun j : Fin (n * gHi) =>
                  M.score ((sample ((eHi.symm j).1)).1 ((eHi.symm j).2))))
      _ = ∑ b : Fin n, ∑ r : Fin gHi,
            M.score ((sample b).1 r) := by
            rw [Fintype.sum_prod_type]
  have hlo_flat :
      (∑ j : Fin (n * gLo),
        M.score ((sample ((eLo.symm j).1)).2 ((eLo.symm j).2))) =
        ∑ b : Fin n, ∑ r : Fin gLo, M.score ((sample b).2 r) := by
    calc
      (∑ j : Fin (n * gLo),
        M.score ((sample ((eLo.symm j).1)).2 ((eLo.symm j).2)))
          =
          ∑ p : Fin n × Fin gLo,
            M.score ((sample p.1).2 p.2) := by
            symm
            simpa [eLo] using
              (Equiv.sum_comp eLo
                (fun j : Fin (n * gLo) =>
                  M.score ((sample ((eLo.symm j).1)).2 ((eLo.symm j).2))))
      _ = ∑ b : Fin n, ∑ r : Fin gLo,
            M.score ((sample b).2 r) := by
            rw [Fintype.sum_prod_type]
  unfold finiteIidScoreSum twoSampleRateBlockScore twoSampleScoreGapSum
    flattenRateBlockSample
  simp only [finiteIidScoreSum] at hhi_flat hlo_flat ⊢
  dsimp [eHi, eLo] at hhi_flat hlo_flat ⊢
  rw [hhi_flat, hlo_flat]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

/--
Flattening preserves the finite product probability mass of repeated
integer-rate blocks.
-/
theorem twoSampleRateBlockSample_mass_eq_flatten_mass
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo n : ℕ)
    (sample : Fin n → (Fin gHi → Rating) × (Fin gLo → Rating)) :
    (EconCSLib.pmfProduct (Fin n)
        ((Fin gHi → Rating) × (Fin gLo → Rating))
        (twoSampleRateBlockLaw M hi lo gHi gLo) sample).toReal =
      (twoSampleRatingLaw M hi lo (n * gHi) (n * gLo)
        (flattenRateBlockSample n gHi gLo sample)).toReal := by
  classical
  let eHi := finProdFinEquiv (m := n) (n := gHi)
  let eLo := finProdFinEquiv (m := n) (n := gLo)
  let hiMass : Fin n → Fin gHi → ℝ :=
    fun b r => (M.typeLaw hi ((sample b).1 r)).toReal
  let loMass : Fin n → Fin gLo → ℝ :=
    fun b r => (M.typeLaw lo ((sample b).2 r)).toReal
  have hhi_flat :
      (∏ j : Fin (n * gHi), hiMass (eHi.symm j).1 (eHi.symm j).2) =
        ∏ b : Fin n, ∏ r : Fin gHi, hiMass b r := by
    calc
      (∏ j : Fin (n * gHi), hiMass (eHi.symm j).1 (eHi.symm j).2)
          =
          ∏ p : Fin n × Fin gHi, hiMass p.1 p.2 := by
            symm
            simpa [eHi] using
              (Equiv.prod_comp eHi
                (fun j : Fin (n * gHi) =>
                  hiMass (eHi.symm j).1 (eHi.symm j).2))
      _ = ∏ b : Fin n, ∏ r : Fin gHi, hiMass b r := by
            rw [Fintype.prod_prod_type]
  have hlo_flat :
      (∏ j : Fin (n * gLo), loMass (eLo.symm j).1 (eLo.symm j).2) =
        ∏ b : Fin n, ∏ r : Fin gLo, loMass b r := by
    calc
      (∏ j : Fin (n * gLo), loMass (eLo.symm j).1 (eLo.symm j).2)
          =
          ∏ p : Fin n × Fin gLo, loMass p.1 p.2 := by
            symm
            simpa [eLo] using
              (Equiv.prod_comp eLo
                (fun j : Fin (n * gLo) =>
                  loMass (eLo.symm j).1 (eLo.symm j).2))
      _ = ∏ b : Fin n, ∏ r : Fin gLo, loMass b r := by
            rw [Fintype.prod_prod_type]
  have hsource :
      (EconCSLib.pmfProduct (Fin n)
          ((Fin gHi → Rating) × (Fin gLo → Rating))
          (twoSampleRateBlockLaw M hi lo gHi gLo) sample).toReal =
        ∏ b : Fin n,
          ((∏ r : Fin gHi, hiMass b r) *
            (∏ r : Fin gLo, loMass b r)) := by
    simp [twoSampleRateBlockLaw, twoSampleRatingLaw, hiMass, loMass]
  have htarget :
      (twoSampleRatingLaw M hi lo (n * gHi) (n * gLo)
          (flattenRateBlockSample n gHi gLo sample)).toReal =
        (∏ j : Fin (n * gHi), hiMass (eHi.symm j).1 (eHi.symm j).2) *
          (∏ j : Fin (n * gLo), loMass (eLo.symm j).1 (eLo.symm j).2) := by
    simp [twoSampleRatingLaw, flattenRateBlockSample, hiMass, loMass, eHi, eLo]
  calc
    (EconCSLib.pmfProduct (Fin n)
        ((Fin gHi → Rating) × (Fin gLo → Rating))
        (twoSampleRateBlockLaw M hi lo gHi gLo) sample).toReal
        =
        ∏ b : Fin n,
          ((∏ r : Fin gHi, hiMass b r) *
            (∏ r : Fin gLo, loMass b r)) := hsource
    _ =
        (∏ b : Fin n, ∏ r : Fin gHi, hiMass b r) *
          (∏ b : Fin n, ∏ r : Fin gLo, loMass b r) := by
          rw [Finset.prod_mul_distrib]
    _ =
        (∏ j : Fin (n * gHi), hiMass (eHi.symm j).1 (eHi.symm j).2) *
          (∏ j : Fin (n * gLo), loMass (eLo.symm j).1 (eLo.symm j).2) := by
          rw [hhi_flat, hlo_flat]
    _ =
        (twoSampleRatingLaw M hi lo (n * gHi) (n * gLo)
          (flattenRateBlockSample n gHi gLo sample)).toReal := htarget.symm

/--
The grouped block error probability is exactly the ungrouped two-sample
left-tail probability with integer sample counts.
-/
theorem twoSampleRateBlockErrorProb_eq_twoSampleScoreGapLeftTailProb
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo n : ℕ) :
    twoSampleRateBlockErrorProb M hi lo gHi gLo n =
      twoSampleScoreGapLeftTailProb M hi lo
        (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹) := by
  classical
  let e := twoSampleRateBlockSampleEquiv Rating n gHi gLo
  unfold twoSampleRateBlockErrorProb finiteIidScoreLeftTailProb
    twoSampleScoreGapLeftTailProb EconCSLib.pmfProb EconCSLib.pmfExp
  calc
    ∑ sample : Fin n → (Fin gHi → Rating) × (Fin gLo → Rating),
        (EconCSLib.pmfProduct (Fin n)
          ((Fin gHi → Rating) × (Fin gLo → Rating))
          (twoSampleRateBlockLaw M hi lo gHi gLo) sample).toReal *
          (if finiteIidScoreSum (twoSampleRateBlockScore M gHi gLo) sample ≤ 0
            then (1 : ℝ) else 0)
        =
        ∑ flat : (Fin (n * gHi) → Rating) × (Fin (n * gLo) → Rating),
          (EconCSLib.pmfProduct (Fin n)
            ((Fin gHi → Rating) × (Fin gLo → Rating))
            (twoSampleRateBlockLaw M hi lo gHi gLo) (e.symm flat)).toReal *
            (if finiteIidScoreSum (twoSampleRateBlockScore M gHi gLo)
                (e.symm flat) ≤ 0 then (1 : ℝ) else 0) := by
          simpa [e] using
            (Equiv.sum_comp e.symm
              (fun sample : Fin n →
                  (Fin gHi → Rating) × (Fin gLo → Rating) =>
                (EconCSLib.pmfProduct (Fin n)
                  ((Fin gHi → Rating) × (Fin gLo → Rating))
                  (twoSampleRateBlockLaw M hi lo gHi gLo) sample).toReal *
                  (if finiteIidScoreSum (twoSampleRateBlockScore M gHi gLo)
                      sample ≤ 0 then (1 : ℝ) else 0))).symm
    _ =
        ∑ flat : (Fin (n * gHi) → Rating) × (Fin (n * gLo) → Rating),
          (twoSampleRatingLaw M hi lo (n * gHi) (n * gLo) flat).toReal *
            (if twoSampleScoreGapSum M ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹)
                flat ≤ 0 then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro flat _
          have hflat :
              flattenRateBlockSample n gHi gLo (e.symm flat) = flat :=
            Equiv.apply_symm_apply e flat
          have hmass :
              (EconCSLib.pmfProduct (Fin n)
                ((Fin gHi → Rating) × (Fin gLo → Rating))
                (twoSampleRateBlockLaw M hi lo gHi gLo) (e.symm flat)).toReal =
                (twoSampleRatingLaw M hi lo (n * gHi) (n * gLo)
                  flat).toReal := by
            simpa [hflat] using
              twoSampleRateBlockSample_mass_eq_flatten_mass
                M hi lo gHi gLo n (e.symm flat)
          have hscore :
              finiteIidScoreSum (twoSampleRateBlockScore M gHi gLo)
                (e.symm flat) =
                twoSampleScoreGapSum M ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹)
                  flat := by
            simpa [hflat] using
              finiteIidScoreSum_rateBlockScore_eq_twoSampleScoreGapSum_flatten
                M gHi gLo n (e.symm flat)
          rw [hmass, hscore]

/--
Any exact rate certificate for the grouped integer-rate block error transfers
to the ungrouped two-sample integer-rate error probability.
-/
theorem twoSampleIntegerRateLeftTail_exponentialRateCertificate_of_block
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) {rate : ℝ}
    (C :
      ExponentialRateCertificate
        (twoSampleRateBlockErrorProb M hi lo gHi gLo) rate) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        twoSampleScoreGapLeftTailProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
      rate := by
  refine
    ExponentialRateCertificate.of_eventually_const_sandwich
      (p := fun n : ℕ =>
        twoSampleScoreGapLeftTailProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
      (q := twoSampleRateBlockErrorProb M hi lo gHi gLo)
      C zero_lt_one zero_lt_one ?_
  filter_upwards with n
  have h :=
    twoSampleRateBlockErrorProb_eq_twoSampleScoreGapLeftTailProb
      M hi lo gHi gLo n
  constructor <;> simp [h]

/-- Chernoff exponent for the block-grouped integer-rate comparison error. -/
def twoSampleRateBlockChernoffRate
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) : ℝ :=
  finiteChernoffRate
    (twoSampleRateBlockLaw M hi lo gHi gLo)
    (twoSampleRateBlockScore M gHi gLo)

/--
The one-block MGF has the two-population product form used in Appendix C.
-/
theorem twoSampleRateBlock_finiteMGF_eq_product
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) (z : ℝ) :
    finiteMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
        (twoSampleRateBlockScore M gHi gLo) z =
      (M.mgf hi (z * (gHi : ℝ)⁻¹)) ^ gHi *
        (M.mgf lo (-(z * (gLo : ℝ)⁻¹))) ^ gLo := by
  simpa [finiteMGF, EconCSLib.pmfExp, twoSampleRateBlockLaw,
    twoSampleRateBlockScore] using
    twoSampleScoreGapSum_exp_mgf_eq_product
      M hi lo gHi gLo ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹) z

/--
The block log-MGF is the sum of the high and low one-rating log-MGFs scaled
by the integer sample rates.
-/
theorem twoSampleRateBlock_finiteLogMGF_eq
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) (z : ℝ) :
    finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
        (twoSampleRateBlockScore M gHi gLo) z =
      (gHi : ℝ) * M.logMGF hi (z * (gHi : ℝ)⁻¹) +
        (gLo : ℝ) * M.logMGF lo (-(z * (gLo : ℝ)⁻¹)) := by
  rw [finiteLogMGF, twoSampleRateBlock_finiteMGF_eq_product]
  rw [Real.log_mul]
  · rw [Real.log_pow, Real.log_pow]
    simp [FiniteRatingLDPModel.logMGF, FiniteRatingLDPModel.mgf,
      finiteLogMGF]
  · exact pow_ne_zero gHi (M.mgf_pos hi (z * (gHi : ℝ)⁻¹)).ne'
  · exact pow_ne_zero gLo (M.mgf_pos lo (-(z * (gLo : ℝ)⁻¹))).ne'

/--
If the high and low one-rating log-MGFs have the same derivative at the scaled
dual parameters, then the integer-rate block log-MGF has derivative zero at
the corresponding block dual.
-/
theorem twoSampleRateBlock_finiteLogMGF_hasDerivAt_zero_of_common_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (gHi : ℝ)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (gLo : ℝ)⁻¹))) :
    HasDerivAt
      (fun t : ℝ =>
        finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo) t)
      0 z := by
  have hhi_inner :
      HasDerivAt (fun t : ℝ => t * (gHi : ℝ)⁻¹)
        ((gHi : ℝ)⁻¹) z := by
    simpa using (hasDerivAt_id z).mul_const ((gHi : ℝ)⁻¹)
  have hlo_inner :
      HasDerivAt (fun t : ℝ => -(t * (gLo : ℝ)⁻¹))
        (-(gLo : ℝ)⁻¹) z := by
    simpa using ((hasDerivAt_id z).mul_const ((gLo : ℝ)⁻¹)).neg
  have hhi_comp :
      HasDerivAt (fun t : ℝ => M.logMGF hi (t * (gHi : ℝ)⁻¹))
        (a * (gHi : ℝ)⁻¹) z :=
    hderiv_hi.comp z hhi_inner
  have hlo_comp :
      HasDerivAt (fun t : ℝ => M.logMGF lo (-(t * (gLo : ℝ)⁻¹)))
        (a * (-(gLo : ℝ)⁻¹)) z :=
    hderiv_lo.comp z hlo_inner
  have hsum :
      HasDerivAt
        (fun t : ℝ =>
          (gHi : ℝ) * M.logMGF hi (t * (gHi : ℝ)⁻¹) +
            (gLo : ℝ) * M.logMGF lo (-(t * (gLo : ℝ)⁻¹)))
        ((gHi : ℝ) * (a * (gHi : ℝ)⁻¹) +
          (gLo : ℝ) * (a * (-(gLo : ℝ)⁻¹))) z :=
    (hhi_comp.const_mul (gHi : ℝ)).add
      (hlo_comp.const_mul (gLo : ℝ))
  have hderiv_zero :
      (gHi : ℝ) * (a * (gHi : ℝ)⁻¹) +
          (gLo : ℝ) * (a * (-(gLo : ℝ)⁻¹)) = 0 := by
    have hghi_ne : (gHi : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hgHi)
    have hglo_ne : (gLo : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hgLo)
    field_simp [hghi_ne, hglo_ne]
    ring
  convert hsum using 1
  · ext t
    exact twoSampleRateBlock_finiteLogMGF_eq M hi lo gHi gLo t
  · exact hderiv_zero.symm

/--
Conversely, a zero derivative of the integer-rate block log-MGF gives a common
one-rating threshold derivative for the high and low populations at the scaled
dual parameters.
-/
theorem exists_common_logMGF_derivatives_of_twoSampleRateBlock_hasDerivAt_zero
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    {z : ℝ}
    (hderiv_block :
      HasDerivAt
        (fun t : ℝ =>
          finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
            (twoSampleRateBlockScore M gHi gLo) t)
        0 z) :
    ∃ a : ℝ,
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (gHi : ℝ)⁻¹) ∧
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (gLo : ℝ)⁻¹)) := by
  let zHi : ℝ := z * (gHi : ℝ)⁻¹
  let zLo : ℝ := -(z * (gLo : ℝ)⁻¹)
  let aHi : ℝ :=
    (∑ r : Rating,
      (M.typeLaw hi r).toReal *
        (M.score r * Real.exp (zHi * M.score r))) /
      finiteMGF (M.typeLaw hi) M.score zHi
  let aLo : ℝ :=
    (∑ r : Rating,
      (M.typeLaw lo r).toReal *
        (M.score r * Real.exp (zLo * M.score r))) /
      finiteMGF (M.typeLaw lo) M.score zLo
  have hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) aHi zHi := by
    simpa [FiniteRatingLDPModel.logMGF, zHi, aHi] using
      finiteLogMGF_hasDerivAt (M.typeLaw hi) M.score zHi
  have hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) aLo zLo := by
    simpa [FiniteRatingLDPModel.logMGF, zLo, aLo] using
      finiteLogMGF_hasDerivAt (M.typeLaw lo) M.score zLo
  have hhi_inner :
      HasDerivAt (fun t : ℝ => t * (gHi : ℝ)⁻¹)
        ((gHi : ℝ)⁻¹) z := by
    simpa using (hasDerivAt_id z).mul_const ((gHi : ℝ)⁻¹)
  have hlo_inner :
      HasDerivAt (fun t : ℝ => -(t * (gLo : ℝ)⁻¹))
        (-(gLo : ℝ)⁻¹) z := by
    simpa using ((hasDerivAt_id z).mul_const ((gLo : ℝ)⁻¹)).neg
  have hhi_comp :
      HasDerivAt (fun t : ℝ => M.logMGF hi (t * (gHi : ℝ)⁻¹))
        (aHi * (gHi : ℝ)⁻¹) z :=
    hderiv_hi.comp z hhi_inner
  have hlo_comp :
      HasDerivAt (fun t : ℝ => M.logMGF lo (-(t * (gLo : ℝ)⁻¹)))
        (aLo * (-(gLo : ℝ)⁻¹)) z :=
    hderiv_lo.comp z hlo_inner
  have hsum :
      HasDerivAt
        (fun t : ℝ =>
          (gHi : ℝ) * M.logMGF hi (t * (gHi : ℝ)⁻¹) +
            (gLo : ℝ) * M.logMGF lo (-(t * (gLo : ℝ)⁻¹)))
        ((gHi : ℝ) * (aHi * (gHi : ℝ)⁻¹) +
          (gLo : ℝ) * (aLo * (-(gLo : ℝ)⁻¹))) z :=
    (hhi_comp.const_mul (gHi : ℝ)).add
      (hlo_comp.const_mul (gLo : ℝ))
  have hsum_block :
      HasDerivAt
        (fun t : ℝ =>
          finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
            (twoSampleRateBlockScore M gHi gLo) t)
        ((gHi : ℝ) * (aHi * (gHi : ℝ)⁻¹) +
          (gLo : ℝ) * (aLo * (-(gLo : ℝ)⁻¹))) z := by
    convert hsum using 1
    ext t
    exact twoSampleRateBlock_finiteLogMGF_eq M hi lo gHi gLo t
  have hderiv_eq_zero :
      (gHi : ℝ) * (aHi * (gHi : ℝ)⁻¹) +
          (gLo : ℝ) * (aLo * (-(gLo : ℝ)⁻¹)) = 0 :=
    hsum_block.unique hderiv_block
  have ha_eq : aHi = aLo := by
    have hghi_ne : (gHi : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hgHi)
    have hglo_ne : (gLo : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hgLo)
    field_simp [hghi_ne, hglo_ne] at hderiv_eq_zero
    linarith
  exact ⟨aHi, hderiv_hi, by simpa [ha_eq, zLo] using hderiv_lo⟩

/--
A stationary weighted-exponential equation for the integer-rate block law gives
common one-rating threshold derivatives at the scaled dual parameters.
-/
theorem exists_common_logMGF_derivatives_of_twoSampleRateBlock_stationary
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    {z : ℝ}
    (hstationary :
      (∑ sample : (Fin gHi → Rating) × (Fin gLo → Rating),
        (twoSampleRateBlockLaw M hi lo gHi gLo sample).toReal *
          (twoSampleRateBlockScore M gHi gLo sample *
            Real.exp (z * twoSampleRateBlockScore M gHi gLo sample))) = 0) :
    ∃ a : ℝ,
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (gHi : ℝ)⁻¹) ∧
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (gLo : ℝ)⁻¹)) :=
  exists_common_logMGF_derivatives_of_twoSampleRateBlock_hasDerivAt_zero
    M hi lo gHi gLo hgHi hgLo
    (finiteLogMGF_hasDerivAt_zero_of_weighted_exp_score_sum_eq_zero
      (twoSampleRateBlockLaw M hi lo gHi gLo)
      (twoSampleRateBlockScore M gHi gLo)
      hstationary)

/--
Exact integer-rate block comparison exponent from the reusable finite iid
Cramer certificate for the block law.
-/
theorem twoSampleRateBlock_exponentialRateCertificate_of_cramer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ)
    (C :
      FiniteIidScoreCramerCertificate
        (twoSampleRateBlockLaw M hi lo gHi gLo)
        (twoSampleRateBlockScore M gHi gLo)) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (twoSampleRateBlockChernoffRate M hi lo gHi gLo) := by
  simpa [twoSampleRateBlockErrorProb, twoSampleRateBlockChernoffRate] using
    C.exponentialRateCertificate

/--
Finite empirical-type Cramer certificate for the integer-rate block law from a
stationary Chernoff tilt and positive-mass block outcomes on both sides of the
comparison threshold.
-/
theorem twoSampleRateBlock_cramerCertificate_of_stationary_tilt
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ)
    (hmean :
      0 ≤
        EconCSLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0)
    {z : ℝ}
    (hstationary :
      (∑ sample : (Fin gHi → Rating) × (Fin gLo → Rating),
        (twoSampleRateBlockLaw M hi lo gHi gLo sample).toReal *
          (twoSampleRateBlockScore M gHi gLo sample *
            Real.exp (z * twoSampleRateBlockScore M gHi gLo sample))) = 0) :
    FiniteIidScoreCramerCertificate
      (twoSampleRateBlockLaw M hi lo gHi gLo)
      (twoSampleRateBlockScore M gHi gLo) := by
  classical
  letI : Nonempty ((Fin gHi → Rating) × (Fin gLo → Rating)) :=
    ⟨samplePos⟩
  exact
    finiteIidScoreCramerCertificate_of_stationary_tilted_empiricalTypes_of_pos_neg_atoms
      (twoSampleRateBlockLaw M hi lo gHi gLo)
      (twoSampleRateBlockScore M gHi gLo)
      hmean hmassPos hscorePos hmassNeg hscoreNeg hstationary

/--
Finite support supplies a nonpositive stationary Chernoff dual for the
integer-rate block law whenever its expected score gap is nonnegative and the
block law has positive-mass outcomes on both sides of the comparison threshold.
-/
theorem exists_nonpos_twoSampleRateBlock_stationary_tilt_of_mean_nonneg_pos_neg_atoms
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ)
    (hmean :
      0 ≤
        EconCSLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0) :
    ∃ z : ℝ, z ≤ 0 ∧
      (∑ sample : (Fin gHi → Rating) × (Fin gLo → Rating),
        (twoSampleRateBlockLaw M hi lo gHi gLo sample).toReal *
          (twoSampleRateBlockScore M gHi gLo sample *
            Real.exp (z * twoSampleRateBlockScore M gHi gLo sample))) = 0 :=
  exists_nonpos_weighted_exp_score_sum_eq_zero_of_pmfExp_nonneg_pos_neg_atoms
    (twoSampleRateBlockLaw M hi lo gHi gLo)
    (twoSampleRateBlockScore M gHi gLo)
    hmean hmassPos hscorePos hmassNeg hscoreNeg

/--
Finite empirical-type Cramer certificate for the integer-rate block law with
the stationary Chernoff tilt derived internally from finite support.
-/
theorem twoSampleRateBlock_cramerCertificate_of_mean_nonneg_pos_neg_atoms
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ)
    (hmean :
      0 ≤
        EconCSLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0) :
    FiniteIidScoreCramerCertificate
      (twoSampleRateBlockLaw M hi lo gHi gLo)
      (twoSampleRateBlockScore M gHi gLo) := by
  rcases
    exists_nonpos_twoSampleRateBlock_stationary_tilt_of_mean_nonneg_pos_neg_atoms
      M hi lo gHi gLo hmean hmassPos hscorePos hmassNeg hscoreNeg with
    ⟨_z, _hz, hstationary⟩
  exact
    twoSampleRateBlock_cramerCertificate_of_stationary_tilt
      M hi lo gHi gLo hmean hmassPos hscorePos hmassNeg hscoreNeg
      hstationary

/--
Finite empirical-type Cramer certificate for the integer-rate block law from a
zero derivative of the block log-MGF.
-/
theorem twoSampleRateBlock_cramerCertificate_of_logMGF_hasDerivAt_zero
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ)
    (hmean :
      0 ≤
        EconCSLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0)
    {z : ℝ}
    (hderiv :
      HasDerivAt
        (fun t : ℝ =>
          finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
            (twoSampleRateBlockScore M gHi gLo) t)
        0 z) :
    FiniteIidScoreCramerCertificate
      (twoSampleRateBlockLaw M hi lo gHi gLo)
      (twoSampleRateBlockScore M gHi gLo) := by
  classical
  letI : Nonempty ((Fin gHi → Rating) × (Fin gLo → Rating)) :=
    ⟨samplePos⟩
  exact
    finiteIidScoreCramerCertificate_of_logMGF_hasDerivAt_zero_empiricalTypes_of_pos_neg_atoms
      (twoSampleRateBlockLaw M hi lo gHi gLo)
      (twoSampleRateBlockScore M gHi gLo)
      hmean hmassPos hscorePos hmassNeg hscoreNeg hderiv

/--
Exact integer-rate block comparison exponent from a stationary Chernoff tilt.
This discharges the block-law `FiniteIidScoreCramerCertificate` using the
shared finite-alphabet empirical-type Cramer theorem.
-/
theorem twoSampleRateBlock_exponentialRateCertificate_of_stationary_tilt
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ)
    (hmean :
      0 ≤
        EconCSLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0)
    {z : ℝ}
    (hstationary :
      (∑ sample : (Fin gHi → Rating) × (Fin gLo → Rating),
        (twoSampleRateBlockLaw M hi lo gHi gLo sample).toReal *
          (twoSampleRateBlockScore M gHi gLo sample *
            Real.exp (z * twoSampleRateBlockScore M gHi gLo sample))) = 0) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (twoSampleRateBlockChernoffRate M hi lo gHi gLo) :=
  twoSampleRateBlock_exponentialRateCertificate_of_cramer
    M hi lo gHi gLo
    (twoSampleRateBlock_cramerCertificate_of_stationary_tilt
      M hi lo gHi gLo hmean hmassPos hscorePos hmassNeg hscoreNeg
      hstationary)

/--
One direction of the Appendix C contraction/Fenchel bridge.  Every common
threshold `a` gives an upper bound on the best block Chernoff dual value, so
the block Chernoff exponent is no larger than the source infimum over common
thresholds.

The bounded-Legendre assumptions are the finite-real side conditions needed by
the current `finiteRateFunction` API to evaluate the supremum at a chosen dual
parameter.
-/
theorem twoSampleRateBlockChernoffRate_le_pairwiseSellerThresholdRate
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z)) :
    twoSampleRateBlockChernoffRate M hi lo gHi gLo ≤
      pairwiseSellerThresholdRate M sampleRate hi lo := by
  unfold pairwiseSellerThresholdRate
  refine le_csInf
    ⟨M.pairwiseRateObjective sampleRate hi lo 0, ⟨0, rfl⟩⟩ ?_
  intro objective hobjective
  rcases hobjective with ⟨a, rfl⟩
  have hpoint :
      ∀ z : ℝ,
        -M.pairwiseRateObjective sampleRate hi lo a ≤
          finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
            (twoSampleRateBlockScore M gHi gLo) z := by
    intro z
    have hhi_eval :
        (z * (gHi : ℝ)⁻¹) * a -
            M.logMGF hi (z * (gHi : ℝ)⁻¹) ≤
          M.rateFunction hi a := by
      simpa [FiniteRatingLDPModel.rateFunction,
        FiniteRatingLDPModel.logMGF, finiteLegendreValue] using
        finiteRateFunction_ge_eval
          (M.typeLaw hi) M.score a (z * (gHi : ℝ)⁻¹) (hbdd_hi a)
    have hlo_eval :
        (-(z * (gLo : ℝ)⁻¹)) * a -
            M.logMGF lo (-(z * (gLo : ℝ)⁻¹)) ≤
          M.rateFunction lo a := by
      simpa [FiniteRatingLDPModel.rateFunction,
        FiniteRatingLDPModel.logMGF, finiteLegendreValue] using
        finiteRateFunction_ge_eval
          (M.typeLaw lo) M.score a (-(z * (gLo : ℝ)⁻¹)) (hbdd_lo a)
    have hhi_scaled :=
      mul_le_mul_of_nonneg_left hhi_eval (Nat.cast_nonneg gHi : 0 ≤ (gHi : ℝ))
    have hlo_scaled :=
      mul_le_mul_of_nonneg_left hlo_eval (Nat.cast_nonneg gLo : 0 ≤ (gLo : ℝ))
    have hsum :
        (gHi : ℝ) *
              ((z * (gHi : ℝ)⁻¹) * a -
            M.logMGF hi (z * (gHi : ℝ)⁻¹)) +
            (gLo : ℝ) *
              (-(z * (gLo : ℝ)⁻¹ * a) -
                M.logMGF lo (-(z * (gLo : ℝ)⁻¹))) ≤
          M.pairwiseRateObjective sampleRate hi lo a := by
      simpa [FiniteRatingLDPModel.pairwiseRateObjective,
        hsample_hi, hsample_lo] using add_le_add hhi_scaled hlo_scaled
    have hleft_eq :
        (gHi : ℝ) *
              ((z * (gHi : ℝ)⁻¹) * a -
                M.logMGF hi (z * (gHi : ℝ)⁻¹)) +
            (gLo : ℝ) *
              (-(z * (gLo : ℝ)⁻¹ * a) -
                M.logMGF lo (-(z * (gLo : ℝ)⁻¹))) =
          -finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
            (twoSampleRateBlockScore M gHi gLo) z := by
      rw [twoSampleRateBlock_finiteLogMGF_eq]
      have hghi_ne : (gHi : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hgHi)
      have hglo_ne : (gLo : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hgLo)
      field_simp [hghi_ne, hglo_ne]
      ring
    have hneglog_le :
        -finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
            (twoSampleRateBlockScore M gHi gLo) z ≤
          M.pairwiseRateObjective sampleRate hi lo a := by
      simpa [hleft_eq] using hsum
    linarith
  have hinf_ge :
      -M.pairwiseRateObjective sampleRate hi lo a ≤
        sInf (Set.range fun z : ℝ =>
          finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
            (twoSampleRateBlockScore M gHi gLo) z) := by
    refine le_csInf
      ⟨finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo) 0, ⟨0, rfl⟩⟩ ?_
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact hpoint z
  change
    -sInf (Set.range fun z : ℝ =>
      finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
        (twoSampleRateBlockScore M gHi gLo) z) ≤
      M.pairwiseRateObjective sampleRate hi lo a
  linarith

/--
Reverse Appendix C Fenchel bridge from first-order data.  If a common threshold
`a` is realized as the derivative of the high and low finite log-MGFs at the
displayed dual parameters, and the corresponding block dual is stationary,
then the source threshold infimum is no larger than the block Chernoff
exponent.
-/
theorem pairwiseSellerThresholdRate_le_twoSampleRateBlockChernoffRate_of_common_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (gHi : ℝ)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (gLo : ℝ)⁻¹)))
    (hstationary_block :
      (∑ sample : (Fin gHi → Rating) × (Fin gLo → Rating),
        (twoSampleRateBlockLaw M hi lo gHi gLo sample).toReal *
          (twoSampleRateBlockScore M gHi gLo sample *
            Real.exp (z * twoSampleRateBlockScore M gHi gLo sample))) = 0) :
    pairwiseSellerThresholdRate M sampleRate hi lo ≤
      twoSampleRateBlockChernoffRate M hi lo gHi gLo := by
  classical
  have hobjective_bdd :
      BddBelow (Set.range fun a0 : ℝ =>
        M.pairwiseRateObjective sampleRate hi lo a0) := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨a0, rfl⟩
    have hhi_nonneg : 0 ≤ M.rateFunction hi a0 := by
      simpa [FiniteRatingLDPModel.rateFunction] using
        finiteRateFunction_nonneg (M.typeLaw hi) M.score a0 (hbdd_hi a0)
    have hlo_nonneg : 0 ≤ M.rateFunction lo a0 := by
      simpa [FiniteRatingLDPModel.rateFunction] using
        finiteRateFunction_nonneg (M.typeLaw lo) M.score a0 (hbdd_lo a0)
    have hsample_hi_nonneg : 0 ≤ sampleRate hi := by
      rw [hsample_hi]
      exact Nat.cast_nonneg gHi
    have hsample_lo_nonneg : 0 ≤ sampleRate lo := by
      rw [hsample_lo]
      exact Nat.cast_nonneg gLo
    exact
      add_nonneg
        (mul_nonneg hsample_hi_nonneg hhi_nonneg)
        (mul_nonneg hsample_lo_nonneg hlo_nonneg)
  have hthreshold_le :
      pairwiseSellerThresholdRate M sampleRate hi lo ≤
        M.pairwiseRateObjective sampleRate hi lo a := by
    unfold pairwiseSellerThresholdRate
    exact csInf_le hobjective_bdd ⟨a, rfl⟩
  have hhi_rate :
      M.rateFunction hi a =
        (z * (gHi : ℝ)⁻¹) * a -
          M.logMGF hi (z * (gHi : ℝ)⁻¹) := by
    simpa [FiniteRatingLDPModel.rateFunction,
      FiniteRatingLDPModel.logMGF, finiteLegendreValue] using
      finiteRateFunction_eq_eval_of_logMGF_hasDerivAt
        (M.typeLaw hi) M.score a (z * (gHi : ℝ)⁻¹)
        (hbdd_hi a) hderiv_hi
  have hlo_rate :
      M.rateFunction lo a =
        (-(z * (gLo : ℝ)⁻¹)) * a -
          M.logMGF lo (-(z * (gLo : ℝ)⁻¹)) := by
    simpa [FiniteRatingLDPModel.rateFunction,
      FiniteRatingLDPModel.logMGF, finiteLegendreValue] using
      finiteRateFunction_eq_eval_of_logMGF_hasDerivAt
        (M.typeLaw lo) M.score a (-(z * (gLo : ℝ)⁻¹))
        (hbdd_lo a) hderiv_lo
  have hobjective_eq :
      M.pairwiseRateObjective sampleRate hi lo a =
        -finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo) z := by
    rw [FiniteRatingLDPModel.pairwiseRateObjective, hsample_hi, hsample_lo,
      hhi_rate, hlo_rate, twoSampleRateBlock_finiteLogMGF_eq]
    have hghi_ne : (gHi : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hgHi)
    have hglo_ne : (gLo : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hgLo)
    field_simp [hghi_ne, hglo_ne]
    ring
  have hderiv_block :
      HasDerivAt
        (fun t : ℝ =>
          finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
            (twoSampleRateBlockScore M gHi gLo) t)
        0 z :=
    finiteLogMGF_hasDerivAt_zero_of_weighted_exp_score_sum_eq_zero
      (twoSampleRateBlockLaw M hi lo gHi gLo)
      (twoSampleRateBlockScore M gHi gLo)
      hstationary_block
  have hblock_min :
      ∀ t : ℝ,
        finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
            (twoSampleRateBlockScore M gHi gLo) z ≤
          finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
            (twoSampleRateBlockScore M gHi gLo) t :=
    finiteLogMGF_global_min_of_convex_hasDerivAt_zero
      (twoSampleRateBlockLaw M hi lo gHi gLo)
      (twoSampleRateBlockScore M gHi gLo)
      (finiteLogMGF_convex
        (twoSampleRateBlockLaw M hi lo gHi gLo)
        (twoSampleRateBlockScore M gHi gLo))
      hderiv_block
  have hblock_rate :
      twoSampleRateBlockChernoffRate M hi lo gHi gLo =
        -finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo) z := by
    simpa [twoSampleRateBlockChernoffRate] using
      finiteChernoffRate_eq_neg_of_logMGF_global_min
        (twoSampleRateBlockLaw M hi lo gHi gLo)
        (twoSampleRateBlockScore M gHi gLo)
        hblock_min rfl
  calc
    pairwiseSellerThresholdRate M sampleRate hi lo
        ≤ M.pairwiseRateObjective sampleRate hi lo a := hthreshold_le
    _ =
        -finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo) z := hobjective_eq
    _ = twoSampleRateBlockChernoffRate M hi lo gHi gLo := hblock_rate.symm

/--
Exact source-threshold rate for the block comparison, provided the remaining
reverse Fenchel/no-duality-gap inequality is supplied.  The forward inequality
is discharged by `twoSampleRateBlockChernoffRate_le_pairwiseSellerThresholdRate`.
-/
theorem twoSampleRateBlock_sourceThresholdRate_exponentialRateCertificate
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (hreverse :
      pairwiseSellerThresholdRate M sampleRate hi lo ≤
        twoSampleRateBlockChernoffRate M hi lo gHi gLo)
    (C :
      FiniteIidScoreCramerCertificate
        (twoSampleRateBlockLaw M hi lo gHi gLo)
        (twoSampleRateBlockScore M gHi gLo)) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) := by
  have hforward :
      twoSampleRateBlockChernoffRate M hi lo gHi gLo ≤
        pairwiseSellerThresholdRate M sampleRate hi lo :=
    twoSampleRateBlockChernoffRate_le_pairwiseSellerThresholdRate
      M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
      hbdd_hi hbdd_lo
  have hrate_eq :
      twoSampleRateBlockChernoffRate M hi lo gHi gLo =
        pairwiseSellerThresholdRate M sampleRate hi lo :=
    le_antisymm hforward hreverse
  simpa [hrate_eq] using
    twoSampleRateBlock_exponentialRateCertificate_of_cramer
      M hi lo gHi gLo C

/--
Exact source-threshold rate for the integer-rate block comparison from a
stationary Chernoff tilt, once the reverse Fenchel/no-duality-gap inequality is
available.  The finite block Cramer side is discharged by the shared
empirical-type theorem.
-/
theorem twoSampleRateBlock_sourceThresholdRate_exponentialRateCertificate_of_stationary_tilt
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (hreverse :
      pairwiseSellerThresholdRate M sampleRate hi lo ≤
        twoSampleRateBlockChernoffRate M hi lo gHi gLo)
    (hmean :
      0 ≤
        EconCSLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0)
    {z : ℝ}
    (hstationary :
      (∑ sample : (Fin gHi → Rating) × (Fin gLo → Rating),
        (twoSampleRateBlockLaw M hi lo gHi gLo sample).toReal *
          (twoSampleRateBlockScore M gHi gLo sample *
            Real.exp (z * twoSampleRateBlockScore M gHi gLo sample))) = 0) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleRateBlock_sourceThresholdRate_exponentialRateCertificate
    M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
    hbdd_hi hbdd_lo hreverse
    (twoSampleRateBlock_cramerCertificate_of_stationary_tilt
      M hi lo gHi gLo hmean hmassPos hscorePos hmassNeg hscoreNeg
      hstationary)

/--
Exact source-threshold rate for the integer-rate block comparison from
first-order Fenchel data and a stationary Chernoff tilt.  This removes the
opaque reverse no-duality-gap input from the stationary-tilt route.
-/
theorem twoSampleRateBlock_sourceThresholdRate_exponentialRateCertificate_of_common_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (gHi : ℝ)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (gLo : ℝ)⁻¹)))
    (hmean :
      0 ≤
        EconCSLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0)
    (hstationary :
      (∑ sample : (Fin gHi → Rating) × (Fin gLo → Rating),
        (twoSampleRateBlockLaw M hi lo gHi gLo sample).toReal *
          (twoSampleRateBlockScore M gHi gLo sample *
            Real.exp (z * twoSampleRateBlockScore M gHi gLo sample))) = 0) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) := by
  have hreverse :
      pairwiseSellerThresholdRate M sampleRate hi lo ≤
        twoSampleRateBlockChernoffRate M hi lo gHi gLo :=
    pairwiseSellerThresholdRate_le_twoSampleRateBlockChernoffRate_of_common_derivatives
      M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
      hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo hstationary
  exact
    twoSampleRateBlock_sourceThresholdRate_exponentialRateCertificate_of_stationary_tilt
      M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
      hbdd_hi hbdd_lo hreverse hmean hmassPos hscorePos hmassNeg hscoreNeg
      hstationary

/--
Exact source-threshold rate for the integer-rate block comparison from a
stationary Chernoff tilt.  The common one-rating derivative threshold is
derived from stationarity of the block log-MGF, so it is not an external
witness.
-/
theorem twoSampleRateBlock_sourceThresholdRate_exponentialRateCertificate_of_stationary_tilt_common_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (hmean :
      0 ≤
        EconCSLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0)
    {z : ℝ}
    (hstationary :
      (∑ sample : (Fin gHi → Rating) × (Fin gLo → Rating),
        (twoSampleRateBlockLaw M hi lo gHi gLo sample).toReal *
          (twoSampleRateBlockScore M gHi gLo sample *
            Real.exp (z * twoSampleRateBlockScore M gHi gLo sample))) = 0) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) := by
  rcases
    exists_common_logMGF_derivatives_of_twoSampleRateBlock_stationary
      M hi lo gHi gLo hgHi hgLo hstationary with
    ⟨a, hderiv_hi, hderiv_lo⟩
  exact
    twoSampleRateBlock_sourceThresholdRate_exponentialRateCertificate_of_common_derivatives
      M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
      hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo
      hmean hmassPos hscorePos hmassNeg hscoreNeg hstationary

/--
Exact source-threshold rate for the integer-rate block comparison with the
stationary Chernoff tilt derived internally from finite two-sided support.
-/
theorem twoSampleRateBlock_sourceThresholdRate_exponentialRateCertificate_of_mean_nonneg_pos_neg_atoms
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (hmean :
      0 ≤
        EconCSLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) := by
  rcases
    exists_nonpos_twoSampleRateBlock_stationary_tilt_of_mean_nonneg_pos_neg_atoms
      M hi lo gHi gLo hmean hmassPos hscorePos hmassNeg hscoreNeg with
    ⟨z, _hz, hstationary⟩
  exact
    twoSampleRateBlock_sourceThresholdRate_exponentialRateCertificate_of_stationary_tilt_common_derivatives
      M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
      hbdd_hi hbdd_lo hmean hmassPos hscorePos hmassNeg hscoreNeg
      hstationary

/--
Exact source-threshold rate for the integer-rate block comparison from common
one-rating log-MGF derivatives.  The common-derivative equations imply the
block dual is stationary, so no separate stationary-sum premise is needed.
-/
theorem twoSampleRateBlock_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (gHi : ℝ)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (gLo : ℝ)⁻¹)))
    (hmean :
      0 ≤
        EconCSLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) := by
  have hderiv_block :
      HasDerivAt
        (fun t : ℝ =>
          finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
            (twoSampleRateBlockScore M gHi gLo) t)
        0 z :=
    twoSampleRateBlock_finiteLogMGF_hasDerivAt_zero_of_common_derivatives
      M hi lo gHi gLo hgHi hgLo a z hderiv_hi hderiv_lo
  have hstationary :
      (∑ sample : (Fin gHi → Rating) × (Fin gLo → Rating),
        (twoSampleRateBlockLaw M hi lo gHi gLo sample).toReal *
          (twoSampleRateBlockScore M gHi gLo sample *
            Real.exp (z * twoSampleRateBlockScore M gHi gLo sample))) = 0 :=
    finiteLogMGF_weighted_exp_score_sum_eq_zero_of_hasDerivAt_zero
      (twoSampleRateBlockLaw M hi lo gHi gLo)
      (twoSampleRateBlockScore M gHi gLo)
      hderiv_block
  exact
    twoSampleRateBlock_sourceThresholdRate_exponentialRateCertificate_of_common_derivatives
      M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
      hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo hmean
      hmassPos hscorePos hmassNeg hscoreNeg hstationary

/--
Exact source-threshold rate for the ungrouped two-sample integer-rate
comparison error from common one-rating log-MGF derivatives.
-/
theorem twoSampleIntegerRateLeftTail_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (gHi : ℝ)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (gLo : ℝ)⁻¹)))
    (hmean :
      0 ≤
        EconCSLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        twoSampleScoreGapLeftTailProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleIntegerRateLeftTail_exponentialRateCertificate_of_block
    M hi lo gHi gLo
    (twoSampleRateBlock_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivatives
      M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
      hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo hmean
      hmassPos hscorePos hmassNeg hscoreNeg)

/--
Exact source-threshold rate for the paper's pairwise `1 - P_k` error from an
exact rate certificate for the nonpositive two-sample score-gap probability.
-/
theorem twoSamplePkComplementError_exponentialRateCertificate_of_leftTail
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) {rate : ℝ}
    (C :
      ExponentialRateCertificate
        (fun n : ℕ =>
          twoSampleScoreGapLeftTailProb M hi lo
            (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
        rate) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        twoSamplePkComplementErrorProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
      rate := by
  refine
    ExponentialRateCertificate.of_eventually_const_sandwich
      (p := fun n : ℕ =>
        twoSamplePkComplementErrorProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
      (q := fun n : ℕ =>
        twoSampleScoreGapLeftTailProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
      (rate := rate)
      (lower := 1)
      (upper := 2)
      C zero_lt_one (by norm_num) ?_
  filter_upwards with n
  have hsandwich :=
    twoSamplePkComplementErrorProb_sandwich_leftTail
      M hi lo (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹)
  simpa using hsandwich

/--
Floor-count `Pk_LD` rate bridge: an exact rate for the floor-count
nonpositive score-gap event transfers to the paper's floor-count `1 - P_k`
pairwise error.
-/
theorem twoSampleFloorPkComplementError_exponentialRateCertificate_of_leftTail
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) {rate : ℝ}
    (C :
      ExponentialRateCertificate
        (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
        rate) :
    ExponentialRateCertificate
      (twoSampleFloorPkComplementErrorProb M sampleRate hi lo)
      rate := by
  refine
    ExponentialRateCertificate.of_eventually_const_sandwich
      (p := twoSampleFloorPkComplementErrorProb M sampleRate hi lo)
      (q := twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (rate := rate)
      (lower := 1)
      (upper := 2)
      C zero_lt_one (by norm_num) ?_
  filter_upwards with k
  have hsandwich :=
    twoSampleFloorPkComplementErrorProb_sandwich_leftTail
      M sampleRate hi lo k
  simpa using hsandwich

/--
Source-threshold floor-count `Pk_LD` certificate from shifted high/low Cramer
certificates and the dual/rate identities.
-/
theorem twoSampleFloorPkComplementError_sourceThresholdRate_exponentialRateCertificate_of_shifted_cramer_minimizer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (C_hi :
      FiniteIidScoreCramerCertificate (M.typeLaw hi)
        (fun r : Rating => M.score r - a))
    (C_lo :
      FiniteIidScoreCramerCertificate (M.typeLaw lo)
        (fun r : Rating => a - M.score r))
    (hshifted_rate :
      sampleRate hi *
          finiteChernoffRate (M.typeLaw hi)
            (fun r : Rating => M.score r - a) +
        sampleRate lo *
          finiteChernoffRate (M.typeLaw lo)
            (fun r : Rating => a - M.score r) =
        pairwiseSellerThresholdRate M sampleRate hi lo)
    (hdual_rate :
      -((sampleRate hi) *
          M.logMGF hi (z * (sampleRate hi)⁻¹) +
        (sampleRate lo) *
          M.logMGF lo (-(z * (sampleRate lo)⁻¹))) =
        pairwiseSellerThresholdRate M sampleRate hi lo) :
    ExponentialRateCertificate
      (twoSampleFloorPkComplementErrorProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleFloorPkComplementError_exponentialRateCertificate_of_leftTail
    M sampleRate hi lo
    (twoSampleFloorScoreGapLeftTail_sourceThresholdRate_exponentialRateCertificate_of_shifted_cramer_minimizer
      M sampleRate hi lo hgHi hgLo a z hz C_hi C_lo
      hshifted_rate hdual_rate)

/--
Lemma `Pk_LD` in the integer-rate finite model: the paper's pairwise
`1 - P_k` error has the source threshold exponent derived from common
one-rating log-MGF derivatives.
-/
theorem twoSamplePkComplementError_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (gHi : ℝ)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (gLo : ℝ)⁻¹)))
    (hmean :
      0 ≤
        EconCSLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        twoSamplePkComplementErrorProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSamplePkComplementError_exponentialRateCertificate_of_leftTail
    M hi lo gHi gLo
    (twoSampleIntegerRateLeftTail_sourceThresholdRate_exponentialRateCertificate_of_logMGF_derivatives
      M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
      hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo hmean
      hmassPos hscorePos hmassNeg hscoreNeg)

/--
The paired-rating MGF factorizes into the high-type MGF at `z` and the
low-type MGF at `-z`.
-/
theorem pairedRatingGapMGF_eq_product
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller) (z : ℝ) :
    finiteMGF (pairedRatingLaw M hi lo) (pairedRatingGapScore M) z =
      M.mgf hi z * M.mgf lo (-z) := by
  classical
  unfold finiteMGF pairedRatingGapScore FiniteRatingLDPModel.mgf
  rw [Fintype.sum_prod_type]
  simp_rw [pairedRatingLaw_apply_toReal]
  calc
    ∑ x : Rating, ∑ y : Rating,
        ((M.typeLaw hi x).toReal * (M.typeLaw lo y).toReal) *
          Real.exp (z * (M.score x - M.score y))
        =
        ∑ x : Rating, ∑ y : Rating,
          ((M.typeLaw hi x).toReal * Real.exp (z * M.score x)) *
            ((M.typeLaw lo y).toReal * Real.exp ((-z) * M.score y)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          refine Finset.sum_congr rfl ?_
          intro y _
          have hexp :
              Real.exp (z * (M.score x - M.score y)) =
                Real.exp (z * M.score x) *
                  Real.exp ((-z) * M.score y) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hexp]
          ring
    _ =
        (∑ x : Rating,
          (M.typeLaw hi x).toReal * Real.exp (z * M.score x)) *
        (∑ y : Rating,
          (M.typeLaw lo y).toReal * Real.exp ((-z) * M.score y)) := by
          rw [Fintype.sum_mul_sum]

/--
Lemma C finite equal-sample bridge: a finite iid Cramer certificate for the
paired high/low rating gap gives the exact pairwise comparison exponent.
-/
theorem equalSamplePairwiseError_exponentialRateCertificate_of_cramer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (C :
      FiniteIidScoreCramerCertificate
        (pairedRatingLaw M hi lo) (pairedRatingGapScore M)) :
    ExponentialRateCertificate
      (equalSamplePairwiseErrorProb M hi lo)
      (equalSamplePairwiseChernoffRate M hi lo) := by
  simpa [equalSamplePairwiseErrorProb, equalSamplePairwiseChernoffRate] using
    C.exponentialRateCertificate

theorem sourceLogMGF_eq_finite_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller) (z : ℝ) :
    sourceLogMGF M θ z =
      Real.log (∑ y : Rating,
        ((M.typeLaw θ) y).toReal * Real.exp (z * M.score y)) := by
  rfl

theorem sourceRateFunction_eq_finite_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller) (a : ℝ) :
    sourceRateFunction M θ a =
      sSup (Set.range fun z : ℝ =>
        z * a - sourceLogMGF M θ z) := by
  rfl

theorem pairwiseSellerThresholdRate_eq_source_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) :
    pairwiseSellerThresholdRate M sampleRate hi lo =
      sInf (Set.range fun a : ℝ =>
        sampleRate hi * sourceRateFunction M hi a +
          sampleRate lo * sourceRateFunction M lo a) := by
  rfl


end

end Probability
end EconCSLib
