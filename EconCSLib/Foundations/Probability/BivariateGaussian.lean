import EconCSLib.Foundations.Probability.GaussianMathlib
import EconCSLib.Foundations.Probability.MeasureInequalities

/-!
# Bivariate Gaussian Source Laws

Reusable correlated standard-Gaussian laws for two-dimensional probability
bookkeeping.

## Main declarations

- `correlatedStandardGaussianLaw`
- `standardBivariateGaussianCDF`
- `correlatedStandardGaussianLaw_firstCoordinateLowerMass`
- `correlatedStandardGaussianLaw_horizontalBoundaryLeft_real_eq_zero`
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Real

namespace EconCSLib
namespace Probability

noncomputable section

/--
The measurable map sending independent standard normals `(U,V)` to the
correlated standard-normal pair `(U, rho * U + sqrt(1-rho^2) * V)`.
-/
def correlatedStandardGaussianMap (rho : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, rho * p.1 + Real.sqrt (1 - rho ^ 2) * p.2)

theorem measurable_correlatedStandardGaussianMap (rho : ℝ) :
    Measurable (correlatedStandardGaussianMap rho) := by
  unfold correlatedStandardGaussianMap
  fun_prop

/--
The standard bivariate normal law with correlation parameter `rho`, constructed
as `(U, rho * U + sqrt(1-rho^2) * V)` for independent standard normals `U,V`.

When `rho^2 < 1`, this is the usual nondegenerate correlated standard-normal
law.  The definition is still meaningful at degenerate parameters; lemmas that
need a nonzero second-coordinate noise scale assume `rho^2 < 1`.
-/
def correlatedStandardGaussianLaw (rho : ℝ) : Measure (ℝ × ℝ) :=
  (standardGaussianMeasure.prod standardGaussianMeasure).map
    (correlatedStandardGaussianMap rho)

instance correlatedStandardGaussianLaw_isProbabilityMeasure (rho : ℝ) :
    IsProbabilityMeasure (correlatedStandardGaussianLaw rho) := by
  unfold correlatedStandardGaussianLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_correlatedStandardGaussianMap rho).aemeasurable

/--
The bivariate standard-normal CDF `Phi_2(x,y;rho)`, defined as the lower-left
rectangle mass of the correlated standard-Gaussian law.
-/
def standardBivariateGaussianCDF (x y rho : ℝ) : ℝ :=
  EconCSLib.lowerLeftRectangleMass (correlatedStandardGaussianLaw rho) x y

/-- The canonical correlation transform `-z / sqrt(1+z^2)` lies in `(-1,1)`. -/
theorem neg_div_sqrt_one_add_sq_sq_lt_one (z : ℝ) :
    ((-z) / Real.sqrt (1 + z ^ 2)) ^ 2 < 1 := by
  have hnonneg : 0 ≤ 1 + z ^ 2 := by positivity
  have hpos : 0 < 1 + z ^ 2 := by nlinarith [sq_nonneg z]
  have hsqrt_sq : (Real.sqrt (1 + z ^ 2)) ^ 2 = 1 + z ^ 2 := by
    exact Real.sq_sqrt hnonneg
  have hsqrt_ne : Real.sqrt (1 + z ^ 2) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hpos)
  calc
    ((-z) / Real.sqrt (1 + z ^ 2)) ^ 2 =
        z ^ 2 / (1 + z ^ 2) := by
          field_simp [hsqrt_ne]
          rw [hsqrt_sq]
    _ < 1 := by
      rw [div_lt_one hpos]
      linarith

/-- The first coordinate of `correlatedStandardGaussianLaw rho` is standard normal. -/
theorem correlatedStandardGaussianLaw_firstCoordinateLowerMass
    (rho x : ℝ) :
    EconCSLib.firstCoordinateLowerMass
        (correlatedStandardGaussianLaw rho) x =
      standardGaussianCDF x := by
  have hpre :
      (correlatedStandardGaussianMap rho) ⁻¹'
          {p : ℝ × ℝ | p.1 ≤ x} =
        (Set.Iic x) ×ˢ (Set.univ : Set ℝ) := by
    ext p
    simp [correlatedStandardGaussianMap]
  rw [EconCSLib.firstCoordinateLowerMass, correlatedStandardGaussianLaw,
    measureReal_def, Measure.map_apply
      (measurable_correlatedStandardGaussianMap rho)
      (EconCSLib.measurableSet_firstCoordinateLower x),
    hpre, Measure.prod_prod, standardGaussianCDF,
    ProbabilityTheory.cdf_eq_real]
  simp [measureReal_def]

/--
For `rho^2 < 1`, the correlated standard-Gaussian law assigns zero mass to
every horizontal boundary clipped by a left half-space.
-/
theorem correlatedStandardGaussianLaw_horizontalBoundaryLeft_real_eq_zero
    {rho : ℝ} (hrho : rho ^ 2 < 1) (x y : ℝ) :
    (correlatedStandardGaussianLaw rho).real
        {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 = y} = 0 := by
  let scale := Real.sqrt (1 - rho ^ 2)
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact Real.sqrt_pos.2 (sub_pos.mpr hrho)
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  haveI : NoAtoms standardGaussianMeasure := by
    unfold standardGaussianMeasure
    exact ProbabilityTheory.noAtoms_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  let boundary : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 = y}
  have hboundary_meas : MeasurableSet boundary := by
    simpa [boundary] using EconCSLib.measurableSet_horizontalBoundaryLeft x y
  have hpre_meas :
      MeasurableSet ((correlatedStandardGaussianMap rho) ⁻¹' boundary) :=
    hboundary_meas.preimage (measurable_correlatedStandardGaussianMap rho)
  have hsection :
      ∀ u : ℝ,
        standardGaussianMeasure
            {v : ℝ |
              (u, v) ∈
                (correlatedStandardGaussianMap rho) ⁻¹' boundary} = 0 := by
    intro u
    by_cases hu : u ≤ x
    · have hset :
          {v : ℝ |
              (u, v) ∈
                (correlatedStandardGaussianMap rho) ⁻¹' boundary} =
            {((y - rho * u) / scale)} := by
        ext v
        constructor
        · intro hv
          have heq : rho * u + scale * v = y := by
            simpa [boundary, correlatedStandardGaussianMap, scale, hu] using hv.2
          have hv_eq : v = (y - rho * u) / scale := by
            field_simp [hscale_ne] at heq ⊢
            linarith
          simpa [hv_eq]
        · intro hv
          have hv_eq : v = (y - rho * u) / scale := by simpa using hv
          refine ⟨hu, ?_⟩
          calc
            (correlatedStandardGaussianMap rho (u, v)).2 =
                rho * u + scale * v := by
                  simp [correlatedStandardGaussianMap, scale]
            _ = rho * u + scale * ((y - rho * u) / scale) := by
                  rw [hv_eq]
            _ = y := by
                  field_simp [hscale_ne]
                  ring_nf
      rw [hset]
      exact measure_singleton ((y - rho * u) / scale)
    · have hset :
          {v : ℝ |
              (u, v) ∈
                (correlatedStandardGaussianMap rho) ⁻¹' boundary} =
            (∅ : Set ℝ) := by
        ext v
        simp [boundary, correlatedStandardGaussianMap, hu]
      rw [hset]
      simp
  have hmass :
      (standardGaussianMeasure.prod standardGaussianMeasure)
          ((correlatedStandardGaussianMap rho) ⁻¹' boundary) = 0 := by
    rw [Measure.prod_apply hpre_meas]
    change
      (∫⁻ u : ℝ,
          standardGaussianMeasure
            (Prod.mk u ⁻¹'
              ((correlatedStandardGaussianMap rho) ⁻¹' boundary))
          ∂standardGaussianMeasure) = 0
    have hfun :
        (fun u : ℝ =>
          standardGaussianMeasure
            (Prod.mk u ⁻¹'
              ((correlatedStandardGaussianMap rho) ⁻¹' boundary))) =
          fun _ : ℝ => 0 := by
      funext u
      simpa [Set.preimage] using hsection u
    rw [hfun]
    exact lintegral_zero
  rw [correlatedStandardGaussianLaw, measureReal_def,
    Measure.map_apply (measurable_correlatedStandardGaussianMap rho) hboundary_meas,
    hmass]
  simp

end

end Probability
end EconCSLib
