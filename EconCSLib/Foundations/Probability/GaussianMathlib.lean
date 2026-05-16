import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Hom.Set
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic
import EconCSLib.Foundations.Probability.Gaussian
import EconCSLib.Foundations.Probability.GaussianDerivatives
import EconCSLib.Foundations.Probability.GaussianHazardInverse
import EconCSLib.Foundations.Probability.GaussianMills
import EconCSLib.Foundations.Probability.GaussianQuantile

/-!
# Mathlib-backed Gaussian facts

Reusable bridges from mathlib's real Gaussian measure API to the smaller
standard-normal interfaces used by admissions and testing formalizations.

## Main declarations

- `continuous_cdf_of_noAtoms`
- `standardGaussianMeasure`
- `standardGaussianCDFAPI`
- `standardGaussianCDFOrderIso`
- `standardGaussianLowerTailMeanCertificate`
- `standardGaussianHazardInverseCertificate`
-/

open Filter MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal Real Topology

namespace EconCSLib
namespace Probability

noncomputable section

/-- The standard real Gaussian measure, as supplied by mathlib. -/
def standardGaussianMeasure : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

/-- The standard Gaussian CDF, using mathlib's CDF construction. -/
def standardGaussianCDF (x : ℝ) : ℝ :=
  ProbabilityTheory.cdf standardGaussianMeasure x

/-- The standard Gaussian density, using mathlib's PDF construction. -/
def standardGaussianDensity (x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x

private theorem standardGaussianVariance_ne_zero : (1 : ℝ≥0) ≠ 0 := by
  norm_num

private instance : IsProbabilityMeasure standardGaussianMeasure := by
  unfold standardGaussianMeasure
  infer_instance

private instance : NoAtoms standardGaussianMeasure := by
  unfold standardGaussianMeasure
  exact ProbabilityTheory.noAtoms_gaussianReal standardGaussianVariance_ne_zero

/--
The CDF of a nonatomic real probability measure is continuous.

Mathlib's CDF is a Stieltjes function and is therefore right-continuous.  The
missing left-continuity at `x` is exactly the assertion that the singleton
`{x}` has zero mass.
-/
theorem continuous_cdf_of_noAtoms
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    Continuous (ProbabilityTheory.cdf μ) := by
  refine continuous_iff_continuousAt.2 ?_
  intro x
  rw [(ProbabilityTheory.monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim]
  rw [StieltjesFunction.rightLim_eq (ProbabilityTheory.cdf μ) x]
  have hsingle_cdf : (ProbabilityTheory.cdf μ).measure ({x} : Set ℝ) = 0 := by
    rw [ProbabilityTheory.measure_cdf μ]
    exact measure_singleton x
  rw [(ProbabilityTheory.cdf μ).measure_singleton x] at hsingle_cdf
  have hleft_le :
      Function.leftLim (ProbabilityTheory.cdf μ) x ≤ ProbabilityTheory.cdf μ x :=
    (ProbabilityTheory.cdf μ).mono.leftLim_le le_rfl
  have hsub_nonneg :
      0 ≤ ProbabilityTheory.cdf μ x - Function.leftLim (ProbabilityTheory.cdf μ) x :=
    sub_nonneg.mpr hleft_le
  have hsub_nonpos :
      ProbabilityTheory.cdf μ x - Function.leftLim (ProbabilityTheory.cdf μ) x ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hsingle_cdf
  linarith

/-- The mathlib-backed standard Gaussian CDF is continuous. -/
theorem standardGaussianCDF_continuous : Continuous standardGaussianCDF := by
  unfold standardGaussianCDF
  exact continuous_cdf_of_noAtoms standardGaussianMeasure

/-- The mathlib-backed standard Gaussian CDF is monotone. -/
theorem standardGaussianCDF_mono : Monotone standardGaussianCDF := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.monotone_cdf standardGaussianMeasure

/-- Every nonempty half-open interval has positive standard Gaussian mass. -/
theorem standardGaussianMeasure_Ioc_pos {x y : ℝ} (hxy : x < y) :
    0 < standardGaussianMeasure (Ioc x y) := by
  unfold standardGaussianMeasure
  rw [ProbabilityTheory.gaussianReal_apply 0 standardGaussianVariance_ne_zero (Ioc x y)]
  rw [MeasureTheory.setLIntegral_pos_iff
    (ProbabilityTheory.measurable_gaussianPDF 0 (1 : ℝ≥0))]
  rw [ProbabilityTheory.support_gaussianPDF
    (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) standardGaussianVariance_ne_zero]
  rw [univ_inter, Real.volume_Ioc]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)

/-- The standard Gaussian measure gives positive mass to every nonempty open set. -/
instance standardGaussianMeasure_isOpenPosMeasure :
    Measure.IsOpenPosMeasure standardGaussianMeasure := by
  refine ⟨fun U hU hUne hzero => ?_⟩
  rcases hUne with ⟨x, hxU⟩
  rcases Metric.isOpen_iff.1 hU x hxU with ⟨ε, hε_pos, hball⟩
  let a : ℝ := x - ε / 2
  let b : ℝ := x + ε / 2
  have hab : a < b := by
    dsimp [a, b]
    linarith
  have hIoc_subset : Set.Ioc a b ⊆ U := by
    intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hleft : x - ε / 2 < y := by
      simpa [a] using hy.1
    have hright : y ≤ x + ε / 2 := by
      simpa [b] using hy.2
    have h_abs : |y - x| ≤ ε / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hhalf_lt : ε / 2 < ε := by
      linarith
    exact lt_of_le_of_lt h_abs hhalf_lt
  have hpos : 0 < standardGaussianMeasure (Set.Ioc a b) :=
    standardGaussianMeasure_Ioc_pos hab
  exact (ne_of_gt (hpos.trans_le (measure_mono hIoc_subset))) hzero

/-- The mathlib-backed standard Gaussian CDF is strictly monotone. -/
theorem standardGaussianCDF_strictMono : StrictMono standardGaussianCDF := by
  intro x y hxy
  have hmass : 0 < standardGaussianMeasure (Ioc x y) :=
    standardGaussianMeasure_Ioc_pos hxy
  have hmeasure_cdf :
      (ProbabilityTheory.cdf standardGaussianMeasure).measure (Ioc x y) =
        standardGaussianMeasure (Ioc x y) := by
    rw [ProbabilityTheory.measure_cdf standardGaussianMeasure]
  have hst := (ProbabilityTheory.cdf standardGaussianMeasure).measure_Ioc x y
  have hofReal_pos :
      0 < ENNReal.ofReal (standardGaussianCDF y - standardGaussianCDF x) := by
    change
      0 < ENNReal.ofReal
        (ProbabilityTheory.cdf standardGaussianMeasure y -
          ProbabilityTheory.cdf standardGaussianMeasure x)
    rw [← hst, hmeasure_cdf]
    exact hmass
  have hsub_pos : 0 < standardGaussianCDF y - standardGaussianCDF x :=
    ENNReal.ofReal_pos.mp hofReal_pos
  linarith

/-- The standard Gaussian measure is symmetric around zero. -/
theorem standardGaussianMeasure_map_neg :
    standardGaussianMeasure.map (fun x : ℝ => -x) = standardGaussianMeasure := by
  unfold standardGaussianMeasure
  simpa using
    (ProbabilityTheory.gaussianReal_map_neg
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))

/-- The mathlib-backed standard Gaussian CDF takes value `1 / 2` at zero. -/
theorem standardGaussianCDF_zero_eq_half :
    standardGaussianCDF 0 = (1 / 2 : ℝ) := by
  unfold standardGaussianCDF
  rw [ProbabilityTheory.cdf_eq_real]
  have hIicIci_measure :
      standardGaussianMeasure (Iic (0 : ℝ)) =
        standardGaussianMeasure (Ici (0 : ℝ)) := by
    calc
      standardGaussianMeasure (Iic (0 : ℝ))
          = (standardGaussianMeasure.map (fun x : ℝ => -x)) (Iic (0 : ℝ)) := by
              rw [standardGaussianMeasure_map_neg]
      _ = standardGaussianMeasure
          ((fun x : ℝ => -x) ⁻¹' Iic (0 : ℝ)) := by
              rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
      _ = standardGaussianMeasure (Ici (0 : ℝ)) := by
              congr 1
              ext x
              simp
  have hIicIci_real :
      standardGaussianMeasure.real (Iic (0 : ℝ)) =
        standardGaussianMeasure.real (Ici (0 : ℝ)) := by
    simp [measureReal_def, hIicIci_measure]
  have hIciIoi_real :
      standardGaussianMeasure.real (Ici (0 : ℝ)) =
        standardGaussianMeasure.real (Ioi (0 : ℝ)) := by
    simpa using
      (MeasureTheory.measureReal_congr
        (μ := standardGaussianMeasure)
        ((MeasureTheory.Ioi_ae_eq_Ici
          (μ := standardGaussianMeasure) (a := (0 : ℝ))).symm))
  have hsym :
      standardGaussianMeasure.real (Iic (0 : ℝ)) =
        standardGaussianMeasure.real (Ioi (0 : ℝ)) :=
    hIicIci_real.trans hIciIoi_real
  have hcompl :
      standardGaussianMeasure.real (Ioi (0 : ℝ)) =
        1 - standardGaussianMeasure.real (Iic (0 : ℝ)) := by
    simpa using
      (MeasureTheory.probReal_compl_eq_one_sub
        (μ := standardGaussianMeasure) (s := Iic (0 : ℝ)) measurableSet_Iic)
  linarith

/-- The mathlib-backed standard Gaussian density is nonnegative. -/
theorem standardGaussianDensity_nonneg (z : ℝ) :
    0 ≤ standardGaussianDensity z := by
  unfold standardGaussianDensity
  exact ProbabilityTheory.gaussianPDFReal_nonneg 0 (1 : ℝ≥0) z

/-- The mathlib-backed standard Gaussian density is strictly positive. -/
theorem standardGaussianDensity_pos (z : ℝ) :
    0 < standardGaussianDensity z := by
  unfold standardGaussianDensity
  exact ProbabilityTheory.gaussianPDFReal_pos
    0 (1 : ℝ≥0) z standardGaussianVariance_ne_zero

/--
The mathlib-backed standard Gaussian density in elementary normalized form.
-/
theorem standardGaussianDensity_eq_mills_integrand (z : ℝ) :
    standardGaussianDensity z =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2) := by
  unfold standardGaussianDensity
  rw [ProbabilityTheory.gaussianPDFReal_def]
  simp

/-- The mathlib-backed standard Gaussian CDF is nonnegative. -/
theorem standardGaussianCDF_nonneg (z : ℝ) :
    0 ≤ standardGaussianCDF z := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.cdf_nonneg standardGaussianMeasure z

/-- The mathlib-backed standard Gaussian CDF is bounded by one. -/
theorem standardGaussianCDF_le_one (z : ℝ) :
    standardGaussianCDF z ≤ 1 := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.cdf_le_one standardGaussianMeasure z

/-- The mathlib-backed standard Gaussian CDF is strictly positive. -/
theorem standardGaussianCDF_pos (z : ℝ) :
    0 < standardGaussianCDF z := by
  have hmono := standardGaussianCDF_strictMono
    (show z - 1 < z by linarith)
  have hnonneg := standardGaussianCDF_nonneg (z - 1)
  linarith

/-- The mathlib-backed standard Gaussian CDF is strictly below one. -/
theorem standardGaussianCDF_lt_one (z : ℝ) :
    standardGaussianCDF z < 1 := by
  have hmono := standardGaussianCDF_strictMono
    (show z < z + 1 by linarith)
  have hle := standardGaussianCDF_le_one (z + 1)
  linarith

/-- The mathlib-backed standard Gaussian upper tail is strictly positive. -/
theorem standardGaussianTail_pos (z : ℝ) :
    0 < 1 - standardGaussianCDF z := by
  have hlt := standardGaussianCDF_lt_one z
  linarith

/--
The mathlib-backed standard Gaussian upper tail equals the normalized
unnormalized tail integral used by the Mills ratio.
-/
theorem standardGaussianTail_eq_const_mul_millsTail (z : ℝ) :
    1 - standardGaussianCDF z =
      (Real.sqrt (2 * Real.pi))⁻¹ * gaussianMillsTail z := by
  have hcompl :
      standardGaussianMeasure.real (Ioi z) = 1 - standardGaussianCDF z := by
    simpa [standardGaussianCDF, ProbabilityTheory.cdf_eq_real, compl_Iic] using
      (MeasureTheory.probReal_compl_eq_one_sub
        (μ := standardGaussianMeasure) (s := Iic z) measurableSet_Iic)
  have hmeasure :
      standardGaussianMeasure (Ioi z) =
        ENNReal.ofReal (∫ x in Ioi z, standardGaussianDensity x) := by
    unfold standardGaussianMeasure standardGaussianDensity
    simpa using
      (ProbabilityTheory.gaussianReal_apply_eq_integral
        0 standardGaussianVariance_ne_zero (Ioi z))
  have htail_integral :
      standardGaussianMeasure.real (Ioi z) =
        ∫ x in Ioi z, standardGaussianDensity x := by
    rw [measureReal_def, hmeasure]
    rw [ENNReal.toReal_ofReal]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun x _hx => standardGaussianDensity_nonneg x)
  have hintegral :
      (∫ x in Ioi z, standardGaussianDensity x) =
        (Real.sqrt (2 * Real.pi))⁻¹ * gaussianMillsTail z := by
    calc
      (∫ x in Ioi z, standardGaussianDensity x)
          = ∫ x in Ioi z,
              (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
                (fun x _hx => standardGaussianDensity_eq_mills_integrand x)
      _ = (Real.sqrt (2 * Real.pi))⁻¹ *
            ∫ x in Ioi z, Real.exp (-(x ^ 2) / 2) := by
              rw [integral_const_mul]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * gaussianMillsTail z := by
              rfl
  rw [← hcompl, htail_integral, hintegral]

/-- The mathlib-backed standard Gaussian CDF tends to zero at `-∞`. -/
theorem standardGaussianCDF_tendsto_atBot :
    Tendsto standardGaussianCDF atBot (𝓝 0) := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.tendsto_cdf_atBot standardGaussianMeasure

/-- The mathlib-backed standard Gaussian CDF tends to one at `+∞`. -/
theorem standardGaussianCDF_tendsto_atTop :
    Tendsto standardGaussianCDF atTop (𝓝 1) := by
  unfold standardGaussianCDF
  exact ProbabilityTheory.tendsto_cdf_atTop standardGaussianMeasure

/-- Every probability in `(0,1)` is hit by the standard Gaussian CDF. -/
theorem standardGaussianCDF_mem_range_of_mem_Ioo {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    p ∈ Set.range standardGaussianCDF := by
  exact mem_range_of_exists_le_of_exists_ge standardGaussianCDF_continuous
    (by
      have hlt :
          ∀ᶠ x in atBot, standardGaussianCDF x < p :=
        standardGaussianCDF_tendsto_atBot.eventually
          (eventually_lt_nhds hp.1)
      rcases hlt.exists with ⟨x, hx⟩
      exact ⟨x, le_of_lt hx⟩)
    (by
      have hgt :
          ∀ᶠ x in atTop, p < standardGaussianCDF x :=
        standardGaussianCDF_tendsto_atTop.eventually
          (eventually_gt_nhds hp.2)
      rcases hgt.exists with ⟨x, hx⟩
      exact ⟨x, le_of_lt hx⟩)

/-- The image of the standard Gaussian CDF is exactly `(0,1)`. -/
theorem standardGaussianCDF_image_univ :
    standardGaussianCDF '' (Set.univ : Set ℝ) = Ioo (0 : ℝ) 1 := by
  ext p
  constructor
  · rintro ⟨x, _hx, rfl⟩
    exact ⟨standardGaussianCDF_pos x, standardGaussianCDF_lt_one x⟩
  · intro hp
    rcases standardGaussianCDF_mem_range_of_mem_Ioo hp with ⟨x, hx⟩
    exact ⟨x, mem_univ x, hx⟩

/--
The standard Gaussian CDF as an order isomorphism from `ℝ` to probabilities in
`(0,1)`.
-/
def standardGaussianCDFOrderIso : ℝ ≃o Ioo (0 : ℝ) 1 :=
  (standardGaussianCDF_strictMono.orderIso standardGaussianCDF).trans
    (OrderIso.setCongr _ _
      (by simpa [Set.image_univ] using standardGaussianCDF_image_univ))

/-- The true standard-normal quantile on probabilities in `(0,1)`. -/
def standardGaussianQuantileIoo (p : Ioo (0 : ℝ) 1) : ℝ :=
  standardGaussianCDFOrderIso.symm p

@[simp] theorem standardGaussianCDF_quantileIoo
    (p : Ioo (0 : ℝ) 1) :
    standardGaussianCDF (standardGaussianQuantileIoo p) = p := by
  exact Subtype.ext_iff.mp
    (standardGaussianCDFOrderIso.apply_symm_apply p)

@[simp] theorem standardGaussianQuantileIoo_cdf (z : ℝ) :
    standardGaussianQuantileIoo
      ⟨standardGaussianCDF z,
        standardGaussianCDF_pos z, standardGaussianCDF_lt_one z⟩ = z := by
  exact standardGaussianCDFOrderIso.symm_apply_apply z

/-- The true standard-normal quantile is monotone on `(0,1)`. -/
theorem standardGaussianQuantileIoo_mono :
    Monotone standardGaussianQuantileIoo :=
  standardGaussianCDFOrderIso.symm.monotone

/-- The true standard-normal quantile is continuous on `(0,1)`. -/
theorem standardGaussianQuantileIoo_continuous :
    Continuous standardGaussianQuantileIoo :=
  standardGaussianCDFOrderIso.symm.continuous

/-- Quantiles above the median are positive. -/
theorem standardGaussianQuantileIoo_pos_of_half_lt
    {p : Ioo (0 : ℝ) 1} (hp : (1 / 2 : ℝ) < p) :
    0 < standardGaussianQuantileIoo p := by
  have hcdf :
      standardGaussianCDF 0 < standardGaussianCDF (standardGaussianQuantileIoo p) := by
    rw [standardGaussianCDF_zero_eq_half,
      standardGaussianCDF_quantileIoo]
    exact hp
  exact standardGaussianCDF_strictMono.lt_iff_lt.mp hcdf

/--
The true standard-normal quantile, extended arbitrarily outside `(0,1)`.

The extension value is irrelevant for paper proofs; the API only uses
monotonicity and continuity on `(0,1)`.
-/
def standardGaussianQuantile (p : ℝ) : ℝ :=
  if hp : p ∈ Ioo (0 : ℝ) 1 then
    standardGaussianQuantileIoo ⟨p, hp⟩
  else
    0

@[simp] theorem standardGaussianQuantile_of_mem_Ioo
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    standardGaussianQuantile p =
      standardGaussianQuantileIoo ⟨p, hp⟩ := by
  simp [standardGaussianQuantile, hp]

/-- The extended true standard-normal quantile is monotone on `(0,1)`. -/
theorem standardGaussianQuantile_monoOn :
    MonotoneOn standardGaussianQuantile (Ioo (0 : ℝ) 1) := by
  intro p hp q hq hpq
  rw [standardGaussianQuantile_of_mem_Ioo hp,
    standardGaussianQuantile_of_mem_Ioo hq]
  exact standardGaussianQuantileIoo_mono hpq

/-- The extended true standard-normal quantile is continuous on `(0,1)`. -/
theorem standardGaussianQuantile_continuousOn :
    ContinuousOn standardGaussianQuantile (Ioo (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  exact standardGaussianQuantileIoo_continuous.congr (by
    intro p
    exact (standardGaussianQuantile_of_mem_Ioo p.property).symm)

/-- The extended true standard-normal quantile is positive above the median. -/
theorem standardGaussianQuantile_pos_of_half_lt
    {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) :
    0 < standardGaussianQuantile p := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  rw [standardGaussianQuantile_of_mem_Ioo hp01]
  exact standardGaussianQuantileIoo_pos_of_half_lt
    (p := ⟨p, hp01⟩) hp.1

/-- The extended true standard-normal quantile inverts the CDF on `(0,1)`. -/
theorem standardGaussianCDF_standardGaussianQuantile
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    standardGaussianCDF (standardGaussianQuantile p) = p := by
  rw [standardGaussianQuantile_of_mem_Ioo hp]
  exact standardGaussianCDF_quantileIoo ⟨p, hp⟩

/-- The standard normal hazard rate using the mathlib-backed CDF and PDF. -/
def standardGaussianHazard (z : ℝ) : ℝ :=
  standardGaussianDensity z / (1 - standardGaussianCDF z)

@[simp] theorem standardGaussianHazard_eq (z : ℝ) :
    standardGaussianHazard z =
      standardGaussianDensity z / (1 - standardGaussianCDF z) := rfl

/-- The mathlib-backed standard normal hazard rate is strictly positive. -/
theorem standardGaussianHazard_pos (z : ℝ) :
    0 < standardGaussianHazard z := by
  rw [standardGaussianHazard_eq]
  exact div_pos (standardGaussianDensity_pos z) (standardGaussianTail_pos z)

/--
The mathlib-backed standard-normal hazard is the reciprocal of the unnormalized
Gaussian Mills ratio.
-/
theorem standardGaussianHazard_eq_millsHazard (z : ℝ) :
    standardGaussianHazard z = gaussianMillsHazard z := by
  rw [standardGaussianHazard_eq, standardGaussianDensity_eq_mills_integrand,
    standardGaussianTail_eq_const_mul_millsTail]
  unfold gaussianMillsHazard gaussianMillsRatio
  field_simp [Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi),
    gaussianMillsTail_pos z, Real.exp_pos (z ^ 2 / 2)]
  rw [← Real.exp_add]
  have hsum : -(z ^ 2 / 2) + z ^ 2 / 2 = 0 := by ring
  rw [hsum, Real.exp_zero]

/--
Concrete lower-tail conditional mean for a location-scale standard-normal law,
expressed by symmetry through the upper-tail hazard.
-/
def standardGaussianLowerTailMean
    (L : GaussianScaleLaw) (threshold : ℝ) : ℝ :=
  L.mean - L.scale * standardGaussianHazard (-(L.standardize threshold))

/--
The concrete Gaussian lower-tail mean is strictly below the threshold.
-/
theorem standardGaussianLowerTailMean_lt_threshold
    (L : GaussianScaleLaw) (threshold : ℝ) :
    standardGaussianLowerTailMean L threshold < threshold := by
  let z : ℝ := L.standardize threshold
  have hthreshold_std :
      L.mean + L.scale * L.standardize threshold = threshold := by
    simpa [GaussianScaleLaw.unstandardize] using
      L.unstandardize_standardize threshold
  have hcore : -standardGaussianHazard (-z) < z := by
    by_cases hz_nonneg : 0 ≤ z
    · have hhaz_pos : 0 < standardGaussianHazard (-z) :=
        standardGaussianHazard_pos (-z)
      linarith
    · have hz_neg : z < 0 := lt_of_not_ge hz_nonneg
      have hneg_pos : 0 < -z := by linarith
      have hhaz_gt : -z < standardGaussianHazard (-z) := by
        rw [standardGaussianHazard_eq_millsHazard]
        exact gaussianMillsHazard_gt_arg_of_pos hneg_pos
      linarith
  have hmul :
      L.scale * (-standardGaussianHazard (-z)) < L.scale * z :=
    mul_lt_mul_of_pos_left hcore L.scale_pos
  calc
    standardGaussianLowerTailMean L threshold =
        L.mean + L.scale * (-standardGaussianHazard (-z)) := by
      dsimp [standardGaussianLowerTailMean, z]
      ring
    _ < L.mean + L.scale * z := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_lt_add_left hmul L.mean
    _ = threshold := by
      dsimp [z]
      exact hthreshold_std

/--
Concrete Gaussian lower-tail mean certificate backed by mathlib's Gaussian CDF
and the Mills-ratio hazard facts.
-/
def standardGaussianLowerTailMeanCertificate :
    GaussianLowerTailMeanCertificate where
  lowerTailMean := standardGaussianLowerTailMean
  lowerTailMean_lt_threshold := standardGaussianLowerTailMean_lt_threshold

/-- The mathlib-backed standard-normal hazard is strictly increasing. -/
theorem standardGaussianHazard_strictMono :
    StrictMono standardGaussianHazard := by
  intro x y hxy
  rw [standardGaussianHazard_eq_millsHazard x,
    standardGaussianHazard_eq_millsHazard y]
  exact gaussianMillsHazard_strictMono hxy

/-- The mathlib-backed standard-normal hazard is monotone. -/
theorem standardGaussianHazard_mono :
    Monotone standardGaussianHazard :=
  standardGaussianHazard_strictMono.monotone

/-- The mathlib-backed standard Gaussian density is continuous. -/
theorem standardGaussianDensity_continuous :
    Continuous standardGaussianDensity := by
  unfold standardGaussianDensity ProbabilityTheory.gaussianPDFReal
  fun_prop

/-- The standard Gaussian probability of `(-∞, x]` is the integral of its density. -/
theorem standardGaussianMeasure_real_Iic_eq_integral_density (x : ℝ) :
    standardGaussianMeasure.real (Iic x) =
      ∫ y in Iic x, standardGaussianDensity y := by
  have hmeasure :
      standardGaussianMeasure (Iic x) =
        ENNReal.ofReal (∫ y in Iic x, standardGaussianDensity y) := by
    unfold standardGaussianMeasure standardGaussianDensity
    simpa using
      (ProbabilityTheory.gaussianReal_apply_eq_integral
        0 standardGaussianVariance_ne_zero (Iic x))
  rw [measureReal_def, hmeasure]
  rw [ENNReal.toReal_ofReal]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Iic
    (fun y _hy => standardGaussianDensity_nonneg y)

/-- The mathlib-backed standard Gaussian CDF is the integral of its density. -/
theorem standardGaussianCDF_eq_integral_Iic (x : ℝ) :
    standardGaussianCDF x =
      ∫ y in Iic x, standardGaussianDensity y := by
  rw [standardGaussianCDF, ProbabilityTheory.cdf_eq_real]
  exact standardGaussianMeasure_real_Iic_eq_integral_density x

/-- Derivative of the mathlib-backed standard Gaussian CDF. -/
theorem standardGaussianCDF_hasDerivAt_density (x : ℝ) :
    HasDerivAt standardGaussianCDF (standardGaussianDensity x) x := by
  let f : ℝ → ℝ := standardGaussianDensity
  have hfint : Integrable f := by
    simpa [f, standardGaussianDensity] using
      (ProbabilityTheory.integrable_gaussianPDFReal 0 (1 : ℝ≥0))
  have hcont : Continuous f := by
    simpa [f] using standardGaussianDensity_continuous
  have hIic_eq (u : ℝ) :
      (∫ y : ℝ in Iic u, f y) =
        (∫ y : ℝ in Iic (0 : ℝ), f y) + ∫ y : ℝ in (0 : ℝ)..u, f y := by
    have hfi0 : IntegrableOn f (Iic (0 : ℝ)) := hfint.integrableOn
    have hfiu : IntegrableOn f (Iic u) := hfint.integrableOn
    have hsub := intervalIntegral.integral_Iic_sub_Iic
      (f := f) (a := (0 : ℝ)) (b := u) hfi0 hfiu
    linarith
  have hIic_deriv :
      HasDerivAt (fun u : ℝ => ∫ y : ℝ in Iic u, f y) (f x) x := by
    have hderiv : HasDerivAt
        (fun u : ℝ =>
          (∫ y : ℝ in Iic (0 : ℝ), f y) + ∫ y : ℝ in (0 : ℝ)..u, f y)
        (f x) x := by
      exact (hcont.integral_hasStrictDerivAt (0 : ℝ) x).hasDerivAt.const_add
        (∫ y : ℝ in Iic (0 : ℝ), f y)
    refine hderiv.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun u => hIic_eq u
  refine hIic_deriv.congr_of_eventuallyEq ?_
  exact Eventually.of_forall fun u => by
    simp [standardGaussianCDF_eq_integral_Iic, f]

/-- Doubled-log elementary form of the mathlib-backed standard Gaussian density. -/
theorem standardGaussianDoubledLogDensity_eq (z : ℝ) :
    2 * Real.log (standardGaussianDensity z) =
      - z ^ 2 + 2 * Real.log ((Real.sqrt (2 * Real.pi))⁻¹) := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hcpos : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi))
  have hexppos : 0 < Real.exp (-(z ^ 2) / 2) := Real.exp_pos _
  have hlog :
      Real.log (standardGaussianDensity z) =
        Real.log c + (-(z ^ 2) / 2) := by
    rw [standardGaussianDensity_eq_mills_integrand]
    dsimp [c]
    rw [Real.log_mul hcpos.ne' hexppos.ne']
    rw [Real.log_exp]
  calc
    2 * Real.log (standardGaussianDensity z)
        = 2 * (Real.log c + (-(z ^ 2) / 2)) := by rw [hlog]
    _ = - z ^ 2 + 2 * Real.log c := by ring
    _ = - z ^ 2 + 2 * Real.log ((Real.sqrt (2 * Real.pi))⁻¹) := by rfl

/-- The mathlib-backed standard normal hazard rate is continuous. -/
theorem standardGaussianHazard_continuous :
    Continuous standardGaussianHazard := by
  unfold standardGaussianHazard
  exact standardGaussianDensity_continuous.div
    (continuous_const.sub standardGaussianCDF_continuous)
    (fun z => (standardGaussianTail_pos z).ne')

/--
For a fixed Gaussian location-scale law, the concrete lower-tail conditional
mean is continuous in the finite threshold.
-/
theorem standardGaussianLowerTailMean_continuous (L : GaussianScaleLaw) :
    Continuous (fun threshold : ℝ =>
      standardGaussianLowerTailMean L threshold) := by
  dsimp [standardGaussianLowerTailMean]
  have hstd : Continuous (fun threshold : ℝ => L.standardize threshold) := by
    unfold GaussianScaleLaw.standardize
    fun_prop
  exact continuous_const.sub
    (continuous_const.mul (standardGaussianHazard_continuous.comp hstd.neg))

/-- The standard Gaussian density tends to zero at `-∞`. -/
theorem standardGaussianDensity_tendsto_atBot_zero :
    Tendsto standardGaussianDensity atBot (𝓝 0) := by
  have harg :
      Tendsto (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) atBot (𝓝 0) := by
    have hcomp := gaussianExpFactor_tendsto_atTop_zero.comp tendsto_neg_atBot_atTop
    refine hcomp.congr' ?_
    filter_upwards with t
    simp
  have hconst :=
    (tendsto_const_nhds
      (x := (Real.sqrt (2 * Real.pi))⁻¹)).mul harg
  have hdensity :
      Tendsto standardGaussianDensity atBot
        (𝓝 ((Real.sqrt (2 * Real.pi))⁻¹ * 0)) := by
    refine hconst.congr' ?_
    filter_upwards with t
    rw [standardGaussianDensity_eq_mills_integrand]
  simpa using hdensity

/-- The standard normal hazard tends to zero at `-∞`. -/
theorem standardGaussianHazard_tendsto_atBot_zero :
    Tendsto standardGaussianHazard atBot (𝓝 0) := by
  have htail :
      Tendsto (fun z : ℝ => 1 - standardGaussianCDF z) atBot (𝓝 1) :=
    by simpa using
      (tendsto_const_nhds (x := (1 : ℝ))).sub
        standardGaussianCDF_tendsto_atBot
  have hdiv :=
    standardGaussianDensity_tendsto_atBot_zero.div htail (by norm_num : (1 : ℝ) ≠ 0)
  simpa [standardGaussianHazard_eq] using hdiv

/-- The standard normal hazard tends to `+∞` at `+∞`. -/
theorem standardGaussianHazard_tendsto_atTop_atTop :
    Tendsto standardGaussianHazard atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  rw [standardGaussianHazard_eq_millsHazard z]
  exact le_of_lt (gaussianMillsHazard_gt_arg_of_pos hz)

/-- Every positive real is attained by the standard Gaussian hazard. -/
theorem standardGaussianHazard_mem_range_of_pos {y : ℝ} (hy : 0 < y) :
    y ∈ Set.range standardGaussianHazard := by
  exact mem_range_of_exists_le_of_exists_ge standardGaussianHazard_continuous
    (by
      have hlt :
          ∀ᶠ x in atBot, standardGaussianHazard x < y :=
        standardGaussianHazard_tendsto_atBot_zero.eventually
          (eventually_lt_nhds hy)
      rcases hlt.exists with ⟨x, hx⟩
      exact ⟨x, le_of_lt hx⟩)
    (by
      have hgt :
          ∀ᶠ x in atTop, y < standardGaussianHazard x :=
        standardGaussianHazard_tendsto_atTop_atTop.eventually
          (eventually_gt_atTop y)
      rcases hgt.exists with ⟨x, hx⟩
      exact ⟨x, le_of_lt hx⟩)

/-- The image of the standard Gaussian hazard is exactly `(0,∞)`. -/
theorem standardGaussianHazard_image_univ :
    standardGaussianHazard '' (Set.univ : Set ℝ) = Set.Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨x, _hx, rfl⟩
    exact standardGaussianHazard_pos x
  · intro hy
    rcases standardGaussianHazard_mem_range_of_pos hy with ⟨x, hx⟩
    exact ⟨x, Set.mem_univ x, hx⟩

/-- The standard Gaussian hazard as an order isomorphism from `ℝ` to `(0,∞)`. -/
def standardGaussianHazardOrderIso : ℝ ≃o Set.Ioi (0 : ℝ) :=
  (standardGaussianHazard_strictMono.orderIso standardGaussianHazard).trans
    (OrderIso.setCongr _ _
      (by simpa [Set.image_univ] using standardGaussianHazard_image_univ))

/-- The concrete inverse of the standard Gaussian hazard on positive thresholds. -/
def standardGaussianHazardInv (y : ℝ) : ℝ :=
  if hy : y ∈ Set.Ioi (0 : ℝ) then
    standardGaussianHazardOrderIso.symm ⟨y, hy⟩
  else
    0

/-- Applying the concrete positive-threshold hazard inverse. -/
theorem standardGaussianHazard_le_iff_le_inv
    {z y : ℝ} (hy : 0 < y) :
    standardGaussianHazard z ≤ y ↔ z ≤ standardGaussianHazardInv y := by
  have hyIoi : y ∈ Set.Ioi (0 : ℝ) := hy
  rw [standardGaussianHazardInv, dif_pos hyIoi]
  change standardGaussianHazardOrderIso z ≤ (⟨y, hyIoi⟩ : Set.Ioi (0 : ℝ)) ↔
    z ≤ standardGaussianHazardOrderIso.symm ⟨y, hyIoi⟩
  exact (standardGaussianHazardOrderIso.le_symm_apply).symm

/-- Scaled standard-normal hazard monotonicity, proved through the Mills ratio. -/
theorem standardGaussian_scaled_hazard_mono
    {a x y : ℝ} (ha : 0 < a) (hx : 0 < x) (hxy : x ≤ y) :
    x * standardGaussianHazard (a / x) ≤
      y * standardGaussianHazard (a / y) := by
  rw [standardGaussianHazard_eq_millsHazard (a / x),
    standardGaussianHazard_eq_millsHazard (a / y)]
  exact gaussianMillsHazard_scaled_mono ha hx hxy

/-- Strict scaled standard-normal hazard monotonicity, proved through the Mills ratio. -/
theorem standardGaussian_scaled_hazard_strictMono
    {a x y : ℝ} (ha : 0 < a) (hx : 0 < x) (hxy : x < y) :
    x * standardGaussianHazard (a / x) <
      y * standardGaussianHazard (a / y) := by
  rw [standardGaussianHazard_eq_millsHazard (a / x),
    standardGaussianHazard_eq_millsHazard (a / y)]
  exact gaussianMillsHazard_scaled_strictMono ha hx hxy

/--
Concrete standard-normal CDF/density API backed by mathlib's `gaussianReal`
and `gaussianPDFReal`.
-/
def standardGaussianCDFAPI : StandardGaussianCDFAPI where
  cdf := standardGaussianCDF
  density := standardGaussianDensity
  cdf_continuous := standardGaussianCDF_continuous
  cdf_mono := standardGaussianCDF_mono
  cdf_strictMono := standardGaussianCDF_strictMono
  cdf_zero_eq_half := standardGaussianCDF_zero_eq_half
  density_nonneg := standardGaussianDensity_nonneg
  cdf_nonneg := standardGaussianCDF_nonneg
  cdf_le_one := standardGaussianCDF_le_one

/-- Concrete standard-normal derivative API backed by mathlib's Gaussian CDF/PDF. -/
def standardGaussianDerivativeAPI : StandardGaussianDerivativeAPI where
  api := standardGaussianCDFAPI
  cdf_hasDerivAt_density := standardGaussianCDF_hasDerivAt_density
  density_pos := standardGaussianDensity_pos

/-- Concrete standard-normal doubled-log-density API. -/
def standardGaussianDoubledLogDensityAPI : StandardGaussianDoubledLogDensityAPI where
  derivativeAPI := standardGaussianDerivativeAPI
  logDensityConstant := 2 * Real.log ((Real.sqrt (2 * Real.pi))⁻¹)
  doubled_log_density_eq := standardGaussianDoubledLogDensity_eq

/-- Concrete standard-normal analytic API used by admissions threshold proofs. -/
def standardGaussianAnalyticAPI : StandardGaussianAnalyticAPI where
  logAPI := standardGaussianDoubledLogDensityAPI
  cdf_tendsto_atBot_zero := standardGaussianCDF_tendsto_atBot

/-- Concrete standard-normal quantile API backed by the mathlib CDF bridge. -/
def standardGaussianQuantileAPI : StandardGaussianQuantileAPI where
  cdfAPI := standardGaussianCDFAPI
  quantile := standardGaussianQuantile
  cdf_quantile := standardGaussianCDF_standardGaussianQuantile
  quantile_mono := standardGaussianQuantile_monoOn
  quantile_continuous := standardGaussianQuantile_continuousOn
  quantile_pos_of_half_lt := standardGaussianQuantile_pos_of_half_lt

/--
Concrete standard-normal hazard-inverse certificate backed by mathlib's
`gaussianReal` CDF/PDF API and the Mills-ratio analytic facts in
`GaussianMills`.
-/
def standardGaussianHazardInverseCertificate :
    GaussianHazardInverseCertificate where
  api := standardGaussianCDFAPI
  hazard := standardGaussianHazard
  tail_pos := standardGaussianTail_pos
  hazard_eq := by
    intro z
    rfl
  hazard_pos := standardGaussianHazard_pos
  hazard_mono := standardGaussianHazard_mono
  scaled_hazard_mono := standardGaussian_scaled_hazard_mono
  scaled_hazard_strictMono := standardGaussian_scaled_hazard_strictMono
  hazardInv := standardGaussianHazardInv
  hazard_le_iff_le_inv := standardGaussianHazard_le_iff_le_inv

end

end Probability
end EconCSLib
