import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import EconCSLib.Foundations.Probability.Gaussian

namespace EconCSLib
namespace Probability

/-!
# Gaussian CDF Derivative Interfaces

Derivative-facing wrappers for the abstract Gaussian CDF API.

## Main declarations

- `StandardGaussianDerivativeAPI`
- `StandardGaussianDerivativeAPI.affineUpperTail`
- `StandardGaussianDerivativeAPI.density_mul_slope_pos`
- `StandardGaussianDerivativeAPI.affineUpperTail_continuous`
- `StandardGaussianDerivativeAPI.affineUpperTail_hasDerivAt`
- `StandardGaussianDerivativeAPI.affineUpperTail_gt_iff_standardized_lt`
- `StandardGaussianDerivativeAPI.affineUpperTail_gt_iff_cutoff_lt_of_slope_lt`
- `StandardGaussianDerivativeAPI.affineUpperTailDifference_continuous`
- `StandardGaussianDerivativeAPI.affineUpperTailDifference_hasDerivAt`
- `StandardGaussianDoubledLogDensityAPI`
- `StandardGaussianDoubledLogDensityAPI.doubled_log_density_mul_slope_eq`
- `StandardGaussianTailLimitAPI`
- `StandardGaussianTailLimitAPI.affineUpperTail_tendsto_one_atTop_of_slope_pos`
- `StandardGaussianAnalyticAPI`
-/

noncomputable section

/--
Analytic derivative extension of `StandardGaussianCDFAPI`: the standard CDF has
the declared density as its derivative, and the density is positive.
-/
structure StandardGaussianDerivativeAPI where
  api : StandardGaussianCDFAPI
  cdf_hasDerivAt_density : ∀ z : ℝ, HasDerivAt api.cdf (api.density z) z
  density_pos : ∀ z : ℝ, 0 < api.density z

namespace StandardGaussianDerivativeAPI

/-- Upper-tail probability of an affine standardization `intercept - slope * q`. -/
def affineUpperTail (A : StandardGaussianDerivativeAPI)
    (intercept slope q : ℝ) : ℝ :=
  1 - A.api.cdf (intercept - slope * q)

/--
Affine upper-tail probabilities are larger exactly when their standardized
cutoffs are smaller.
-/
theorem affineUpperTail_gt_iff_standardized_lt
    (A : StandardGaussianDerivativeAPI)
    {interceptA slopeA interceptB slopeB q : ℝ} :
    A.affineUpperTail interceptA slopeA q >
        A.affineUpperTail interceptB slopeB q ↔
      interceptA - slopeA * q < interceptB - slopeB * q := by
  constructor
  · intro htail
    have hcdf :
        A.api.cdf (interceptA - slopeA * q) <
          A.api.cdf (interceptB - slopeB * q) := by
      dsimp [affineUpperTail] at htail
      linarith
    exact A.api.cdf_strictMono.lt_iff_lt.mp hcdf
  · intro hstd
    have hcdf :
        A.api.cdf (interceptA - slopeA * q) <
          A.api.cdf (interceptB - slopeB * q) :=
      A.api.cdf_strictMono hstd
    dsimp [affineUpperTail]
    linarith

/--
Two affine standardized cutoffs with different slopes cross at the displayed
cutoff.
-/
theorem affineStandardized_lt_iff_cutoff_lt_of_slope_lt
    {interceptA slopeA interceptB slopeB q : ℝ}
    (hslope : slopeB < slopeA) :
    interceptA - slopeA * q < interceptB - slopeB * q ↔
      (interceptA - interceptB) / (slopeA - slopeB) < q := by
  have hden_pos : 0 < slopeA - slopeB := sub_pos.mpr hslope
  constructor
  · intro h
    rw [div_lt_iff₀ hden_pos]
    nlinarith
  · intro h
    rw [div_lt_iff₀ hden_pos] at h
    nlinarith

/--
Affine upper-tail probabilities cross exactly above the affine cutoff when the
first standardized cutoff has the larger skill slope.
-/
theorem affineUpperTail_gt_iff_cutoff_lt_of_slope_lt
    (A : StandardGaussianDerivativeAPI)
    {interceptA slopeA interceptB slopeB q : ℝ}
    (hslope : slopeB < slopeA) :
    A.affineUpperTail interceptA slopeA q >
        A.affineUpperTail interceptB slopeB q ↔
      (interceptA - interceptB) / (slopeA - slopeB) < q := by
  rw [A.affineUpperTail_gt_iff_standardized_lt]
  exact affineStandardized_lt_iff_cutoff_lt_of_slope_lt hslope

/-- A positive affine slope gives a positive density-weighted derivative factor. -/
theorem density_mul_slope_pos
    (A : StandardGaussianDerivativeAPI)
    {z slope : ℝ} (hslope : 0 < slope) :
    0 < A.api.density z * slope :=
  mul_pos (A.density_pos z) hslope

/-- Derivative of an affine standardized upper tail. -/
theorem affineUpperTail_hasDerivAt
    (A : StandardGaussianDerivativeAPI)
    {intercept slope q : ℝ} :
    HasDerivAt (fun x : ℝ => A.affineUpperTail intercept slope x)
      (A.api.density (intercept - slope * q) * slope) q := by
  have hlin :
      HasDerivAt (fun x : ℝ => intercept - slope * x) (-slope) q := by
    simpa using (hasDerivAt_const q intercept).sub
      ((hasDerivAt_id q).const_mul slope)
  have hcdf :
      HasDerivAt (fun x : ℝ => A.api.cdf (intercept - slope * x))
        (A.api.density (intercept - slope * q) * (-slope)) q :=
    (A.cdf_hasDerivAt_density (intercept - slope * q)).comp q hlin
  have htail := (hasDerivAt_const q (1 : ℝ)).sub hcdf
  simpa [affineUpperTail, mul_comm, mul_left_comm, mul_assoc] using htail

/-- Continuity of an affine standardized upper tail. -/
theorem affineUpperTail_continuous
    (A : StandardGaussianDerivativeAPI)
    {intercept slope : ℝ} :
    Continuous (fun x : ℝ => A.affineUpperTail intercept slope x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (A.affineUpperTail_hasDerivAt (intercept := intercept)
    (slope := slope) (q := x)).continuousAt

/-- Continuity of the difference of two affine standardized upper tails. -/
theorem affineUpperTailDifference_continuous
    (A : StandardGaussianDerivativeAPI)
    {interceptA slopeA interceptB slopeB : ℝ} :
    Continuous
      (fun x : ℝ =>
        A.affineUpperTail interceptA slopeA x -
          A.affineUpperTail interceptB slopeB x) :=
  (A.affineUpperTail_continuous (intercept := interceptA)
    (slope := slopeA)).sub
    (A.affineUpperTail_continuous (intercept := interceptB)
      (slope := slopeB))

/-- Derivative of the difference of two affine standardized upper tails. -/
theorem affineUpperTailDifference_hasDerivAt
    (A : StandardGaussianDerivativeAPI)
    {interceptA slopeA interceptB slopeB q : ℝ} :
    HasDerivAt
      (fun x : ℝ =>
        A.affineUpperTail interceptA slopeA x -
          A.affineUpperTail interceptB slopeB x)
      (A.api.density (interceptA - slopeA * q) * slopeA -
        A.api.density (interceptB - slopeB * q) * slopeB) q := by
  exact A.affineUpperTail_hasDerivAt.sub A.affineUpperTail_hasDerivAt

end StandardGaussianDerivativeAPI

/--
Standard Gaussian derivative API with the usual doubled-log density formula.

For a standard normal density `φ`, this records
`2 * log (φ z) = -z^2 + constant`; the normalizing constant cancels in the
density comparisons used by threshold-admissions proofs.
-/
structure StandardGaussianDoubledLogDensityAPI where
  derivativeAPI : StandardGaussianDerivativeAPI
  logDensityConstant : ℝ
  doubled_log_density_eq :
    ∀ z : ℝ,
      2 * Real.log (derivativeAPI.api.density z) =
        - z ^ 2 + logDensityConstant

namespace StandardGaussianDoubledLogDensityAPI

/--
Doubled log of a density-weighted positive affine slope.  The normalizing
constant is retained explicitly so paired comparisons can cancel it.
-/
theorem doubled_log_density_mul_slope_eq
    (A : StandardGaussianDoubledLogDensityAPI)
    {z slope : ℝ} (hslope : 0 < slope) :
    2 * Real.log (A.derivativeAPI.api.density z * slope) =
      - z ^ 2 + 2 * Real.log slope + A.logDensityConstant := by
  have hdensity_pos : 0 < A.derivativeAPI.api.density z :=
    A.derivativeAPI.density_pos z
  have hlog_mul :
      Real.log (A.derivativeAPI.api.density z * slope) =
        Real.log (A.derivativeAPI.api.density z) + Real.log slope :=
    Real.log_mul hdensity_pos.ne' hslope.ne'
  calc
    2 * Real.log (A.derivativeAPI.api.density z * slope)
        = 2 * (Real.log (A.derivativeAPI.api.density z) + Real.log slope) := by
          rw [hlog_mul]
    _ = 2 * Real.log (A.derivativeAPI.api.density z) +
          2 * Real.log slope := by
          ring
    _ = (- z ^ 2 + A.logDensityConstant) + 2 * Real.log slope := by
          rw [A.doubled_log_density_eq z]
    _ = - z ^ 2 + 2 * Real.log slope + A.logDensityConstant := by
          ring

end StandardGaussianDoubledLogDensityAPI

/--
Standard Gaussian CDF tail-limit API.  For admissions threshold proofs, the
needed analytic fact is that `cdf z -> 0` as `z -> -∞`, so affine upper-tail
admission probabilities with positive skill slope tend to one.
-/
structure StandardGaussianTailLimitAPI where
  derivativeAPI : StandardGaussianDerivativeAPI
  cdf_tendsto_atBot_zero :
    Filter.Tendsto derivativeAPI.api.cdf Filter.atBot (nhds 0)

namespace StandardGaussianTailLimitAPI

/-- Affine standardized upper-tail probabilities tend to one for high skill. -/
theorem affineUpperTail_tendsto_one_atTop_of_slope_pos
    (A : StandardGaussianTailLimitAPI)
    {intercept slope : ℝ} (hslope : 0 < slope) :
    Filter.Tendsto
      (fun q : ℝ => A.derivativeAPI.affineUpperTail intercept slope q)
      Filter.atTop (nhds 1) := by
  have hneg : -slope < 0 := by
    linarith
  have hlin :
      Filter.Tendsto (fun q : ℝ => intercept - slope * q)
        Filter.atTop Filter.atBot := by
    have hmul :
        Filter.Tendsto (fun q : ℝ => (-slope) * q + intercept)
          Filter.atTop Filter.atBot :=
      (Filter.Tendsto.const_mul_atTop_of_neg hneg Filter.tendsto_id).atBot_add
        tendsto_const_nhds
    convert hmul using 1
    ext q
    ring
  have hcdf :
      Filter.Tendsto
        (fun q : ℝ => A.derivativeAPI.api.cdf (intercept - slope * q))
        Filter.atTop (nhds 0) :=
    A.cdf_tendsto_atBot_zero.comp hlin
  simpa [StandardGaussianDerivativeAPI.affineUpperTail] using
    tendsto_const_nhds.sub hcdf

/--
The difference of two affine standardized upper-tail probabilities with
positive skill slopes tends to zero for high skill.
-/
theorem affineUpperTailDifference_tendsto_zero_atTop_of_slope_pos
    (A : StandardGaussianTailLimitAPI)
    {interceptA slopeA interceptB slopeB : ℝ}
    (hslopeA : 0 < slopeA) (hslopeB : 0 < slopeB) :
    Filter.Tendsto
      (fun q : ℝ =>
        A.derivativeAPI.affineUpperTail interceptA slopeA q -
          A.derivativeAPI.affineUpperTail interceptB slopeB q)
      Filter.atTop (nhds 0) := by
  have hA :=
    A.affineUpperTail_tendsto_one_atTop_of_slope_pos
      (intercept := interceptA) (slope := slopeA) hslopeA
  have hB :=
    A.affineUpperTail_tendsto_one_atTop_of_slope_pos
      (intercept := interceptB) (slope := slopeB) hslopeB
  simpa using hA.sub hB

end StandardGaussianTailLimitAPI

/--
Combined standard Gaussian analytic API for threshold-admissions papers:
differentiability, positive density, doubled-log density, and the left-tail CDF
limit share the same CDF/density implementation.
-/
structure StandardGaussianAnalyticAPI where
  logAPI : StandardGaussianDoubledLogDensityAPI
  cdf_tendsto_atBot_zero :
    Filter.Tendsto logAPI.derivativeAPI.api.cdf Filter.atBot (nhds 0)

namespace StandardGaussianAnalyticAPI

/-- Forget the doubled-log fields and expose the tail-limit API. -/
def tailLimitAPI (A : StandardGaussianAnalyticAPI) :
    StandardGaussianTailLimitAPI where
  derivativeAPI := A.logAPI.derivativeAPI
  cdf_tendsto_atBot_zero := A.cdf_tendsto_atBot_zero

end StandardGaussianAnalyticAPI

end

end Probability
end EconCSLib
