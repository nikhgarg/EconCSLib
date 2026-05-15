import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
- `StandardGaussianDerivativeAPI.affineUpperTailDifference_continuous`
- `StandardGaussianDerivativeAPI.affineUpperTailDifference_hasDerivAt`
- `StandardGaussianDoubledLogDensityAPI`
- `StandardGaussianDoubledLogDensityAPI.doubled_log_density_mul_slope_eq`
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

end

end Probability
end EconCSLib
