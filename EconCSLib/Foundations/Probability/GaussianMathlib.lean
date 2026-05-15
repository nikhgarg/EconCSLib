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
import EconCSLib.Foundations.Probability.GaussianHazardInverse
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

/-- The standard normal hazard rate using the mathlib-backed CDF and PDF. -/
def standardGaussianHazard (z : ℝ) : ℝ :=
  standardGaussianDensity z / (1 - standardGaussianCDF z)

@[simp] theorem standardGaussianHazard_eq (z : ℝ) :
    standardGaussianHazard z =
      standardGaussianDensity z / (1 - standardGaussianCDF z) := rfl

/--
The remaining analytic facts needed to turn the concrete standard-normal
hazard into the paper-facing hazard-inverse certificate.

All CDF, density, strict-tail-positivity, quantile, and definitional hazard
facts are supplied by this file; these fields are the inverse-Mills monotonicity
and inversion statements that still need a real analytic proof.
-/
structure StandardGaussianHazardInverseAnalyticFacts where
  hazardInv : ℝ → ℝ
  hazard_mono : Monotone standardGaussianHazard
  scaled_hazard_mono :
    ∀ {a x y : ℝ}, 0 < a → 0 < x → x ≤ y →
      x * standardGaussianHazard (a / x) ≤
        y * standardGaussianHazard (a / y)
  scaled_hazard_strictMono :
    ∀ {a x y : ℝ}, 0 < a → 0 < x → x < y →
      x * standardGaussianHazard (a / x) <
        y * standardGaussianHazard (a / y)
  hazard_le_iff_le_inv :
    ∀ {z y : ℝ}, standardGaussianHazard z ≤ y ↔ z ≤ hazardInv y

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

/-- Concrete standard-normal quantile API backed by the mathlib CDF bridge. -/
def standardGaussianQuantileAPI : StandardGaussianQuantileAPI where
  cdfAPI := standardGaussianCDFAPI
  quantile := standardGaussianQuantile
  quantile_mono := standardGaussianQuantile_monoOn
  quantile_continuous := standardGaussianQuantile_continuousOn
  quantile_pos_of_half_lt := standardGaussianQuantile_pos_of_half_lt

/--
Concrete standard-normal hazard-inverse certificate, conditional only on the
remaining inverse-Mills monotonicity and inversion facts.
-/
def standardGaussianHazardInverseCertificate
    (A : StandardGaussianHazardInverseAnalyticFacts) :
    GaussianHazardInverseCertificate where
  api := standardGaussianCDFAPI
  hazard := standardGaussianHazard
  tail_pos := standardGaussianTail_pos
  hazard_eq := by
    intro z
    rfl
  hazard_mono := A.hazard_mono
  scaled_hazard_mono := A.scaled_hazard_mono
  scaled_hazard_strictMono := A.scaled_hazard_strictMono
  hazardInv := A.hazardInv
  hazard_le_iff_le_inv := A.hazard_le_iff_le_inv

end

end Probability
end EconCSLib
