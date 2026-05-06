import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace EconCSLib
namespace Probability

noncomputable section

/-!
# Gaussian Algebra and Testing-Paper Interfaces

Reusable Gaussian-facing algebra for admissions/testing papers.

This file deliberately separates two layers:

1. exact conjugate-normal precision algebra, which is formalized here; and
2. analytic normal CDF/density/hazard facts, which are exposed through an API
   record because Mathlib does not currently provide a full normal-distribution
   measure/CDF surface in this repository.

## Main declarations

- `GaussianVarianceLaw`, `GaussianScaleLaw`
- `StandardGaussianCDFAPI`
- `GaussianPriorSignal`
- `GaussianSignalFamily`
- `GaussianOffsetSignalFamily`
- `GaussianHazardCertificate`
-/

/-- A Gaussian law represented by mean and variance. -/
structure GaussianVarianceLaw where
  mean : ℝ
  variance : ℝ
  variance_pos : 0 < variance

/-- A Gaussian location-scale law represented by mean and positive scale. -/
structure GaussianScaleLaw where
  mean : ℝ
  scale : ℝ
  scale_pos : 0 < scale

namespace GaussianScaleLaw

/-- Standardize a value relative to a Gaussian location-scale law. -/
def standardize (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  (x - L.mean) / L.scale

/-- Undo standardization relative to a Gaussian location-scale law. -/
def unstandardize (L : GaussianScaleLaw) (z : ℝ) : ℝ :=
  L.mean + L.scale * z

theorem standardize_unstandardize (L : GaussianScaleLaw) (z : ℝ) :
    L.standardize (L.unstandardize z) = z := by
  rw [standardize, unstandardize]
  calc
    (L.mean + L.scale * z - L.mean) / L.scale =
        (L.scale * z) / L.scale := by
      congr
      ring
    _ = z := by
      exact mul_div_cancel_left₀ z (ne_of_gt L.scale_pos)

theorem unstandardize_standardize (L : GaussianScaleLaw) (x : ℝ) :
    L.unstandardize (L.standardize x) = x := by
  rw [standardize, unstandardize]
  calc
    L.mean + L.scale * ((x - L.mean) / L.scale) =
        L.mean + (x - L.mean) := by
      rw [mul_div_cancel₀ _ (ne_of_gt L.scale_pos)]
    _ = x := by
      ring

theorem standardize_mono (L : GaussianScaleLaw) :
    Monotone L.standardize := by
  intro x y hxy
  exact div_le_div_of_nonneg_right
    (sub_le_sub_right hxy L.mean) L.scale_pos.le

theorem standardize_le_standardize_of_mean_le_same_scale
    {L1 L2 : GaussianScaleLaw} (hscale : L1.scale = L2.scale)
    (hmean : L1.mean ≤ L2.mean) (x : ℝ) :
    L2.standardize x ≤ L1.standardize x := by
  rw [standardize, standardize, hscale]
  exact div_le_div_of_nonneg_right (sub_le_sub_left hmean x) L2.scale_pos.le

/-- Positive affine image of a Gaussian location-scale law. -/
def affineImage (L : GaussianScaleLaw) (a b : ℝ) (hb : 0 < b) :
    GaussianScaleLaw where
  mean := a + b * L.mean
  scale := b * L.scale
  scale_pos := mul_pos hb L.scale_pos

@[simp] theorem affineImage_mean (L : GaussianScaleLaw)
    (a b : ℝ) (hb : 0 < b) :
    (L.affineImage a b hb).mean = a + b * L.mean := rfl

@[simp] theorem affineImage_scale (L : GaussianScaleLaw)
    (a b : ℝ) (hb : 0 < b) :
    (L.affineImage a b hb).scale = b * L.scale := rfl

theorem standardize_affineImage_map (L : GaussianScaleLaw)
    (a : ℝ) {b : ℝ} (hb : 0 < b) (x : ℝ) :
    (L.affineImage a b hb).standardize (a + b * x) =
      L.standardize x := by
  rw [standardize, standardize, affineImage]
  field_simp [ne_of_gt hb, ne_of_gt L.scale_pos]
  ring

theorem standardize_affineImage_threshold (L : GaussianScaleLaw)
    (a : ℝ) {b : ℝ} (hb : 0 < b) (threshold : ℝ) :
    (L.affineImage a b hb).standardize threshold =
      L.standardize ((threshold - a) / b) := by
  rw [standardize, standardize, affineImage]
  field_simp [ne_of_gt hb, ne_of_gt L.scale_pos]
  ring

end GaussianScaleLaw

/--
Abstract standard-normal CDF/density API.

Analytic papers can instantiate this once a concrete normal CDF/density library
is available. Until then, paper-specific Gaussian proofs can state exactly
which normal facts they require without hiding them in theorem conclusions.
-/
structure StandardGaussianCDFAPI where
  cdf : ℝ → ℝ
  density : ℝ → ℝ
  cdf_mono : Monotone cdf
  density_nonneg : ∀ z, 0 ≤ density z
  cdf_nonneg : ∀ z, 0 ≤ cdf z
  cdf_le_one : ∀ z, cdf z ≤ 1

namespace StandardGaussianCDFAPI

/-- Normal CDF for an arbitrary location-scale law by standardization. -/
def normalCDF (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  api.cdf (L.standardize x)

/-- Normal upper tail for an arbitrary location-scale law. -/
def normalTail (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  1 - api.normalCDF L x

/-- Normal density for an arbitrary location-scale law, up to the usual scale factor. -/
def normalDensity (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) : ℝ :=
  api.density (L.standardize x) / L.scale

theorem normalCDF_mono (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) :
    Monotone (api.normalCDF L) := by
  intro x y hxy
  exact api.cdf_mono (L.standardize_mono hxy)

theorem normalCDF_nonneg (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) :
    0 ≤ api.normalCDF L x :=
  api.cdf_nonneg (L.standardize x)

theorem normalCDF_le_one (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) :
    api.normalCDF L x ≤ 1 :=
  api.cdf_le_one (L.standardize x)

theorem normalTail_nonneg (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) :
    0 ≤ api.normalTail L x := by
  dsimp [normalTail]
  exact sub_nonneg.mpr (api.normalCDF_le_one L x)

theorem normalTail_le_one (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) :
    api.normalTail L x ≤ 1 := by
  dsimp [normalTail]
  exact sub_le_self 1 (api.normalCDF_nonneg L x)

theorem normalTail_antitone (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) :
    Antitone (api.normalTail L) := by
  intro x y hxy
  dsimp [normalTail, normalCDF]
  exact sub_le_sub_left (api.cdf_mono (L.standardize_mono hxy)) 1

theorem normalCDF_le_of_mean_le_same_scale (api : StandardGaussianCDFAPI)
    {L1 L2 : GaussianScaleLaw} (hscale : L1.scale = L2.scale)
    (hmean : L1.mean ≤ L2.mean) (x : ℝ) :
    api.normalCDF L2 x ≤ api.normalCDF L1 x := by
  exact api.cdf_mono
    (GaussianScaleLaw.standardize_le_standardize_of_mean_le_same_scale
      hscale hmean x)

theorem normalTail_le_of_mean_le_same_scale (api : StandardGaussianCDFAPI)
    {L1 L2 : GaussianScaleLaw} (hscale : L1.scale = L2.scale)
    (hmean : L1.mean ≤ L2.mean) (x : ℝ) :
    api.normalTail L1 x ≤ api.normalTail L2 x := by
  dsimp [normalTail]
  exact sub_le_sub_left
    (api.normalCDF_le_of_mean_le_same_scale hscale hmean x) 1

/-- Pass probability above a threshold for a Gaussian location-scale law. -/
def thresholdPassProb (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (threshold : ℝ) : ℝ :=
  api.normalTail L threshold

theorem thresholdPassProb_antitone_threshold
    (api : StandardGaussianCDFAPI) (L : GaussianScaleLaw) :
    Antitone (api.thresholdPassProb L) := by
  exact api.normalTail_antitone L

theorem thresholdPassProb_le_of_mean_le_same_scale
    (api : StandardGaussianCDFAPI)
    {L1 L2 : GaussianScaleLaw} (hscale : L1.scale = L2.scale)
    (hmean : L1.mean ≤ L2.mean) (threshold : ℝ) :
    api.thresholdPassProb L1 threshold ≤ api.thresholdPassProb L2 threshold := by
  exact api.normalTail_le_of_mean_le_same_scale hscale hmean threshold

theorem normalCDF_affineImage_pos (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (threshold : ℝ) :
    api.normalCDF (L.affineImage a b hb) threshold =
      api.normalCDF L ((threshold - a) / b) := by
  rw [normalCDF, normalCDF,
    GaussianScaleLaw.standardize_affineImage_threshold]

theorem normalTail_affineImage_pos (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (threshold : ℝ) :
    api.normalTail (L.affineImage a b hb) threshold =
      api.normalTail L ((threshold - a) / b) := by
  rw [normalTail, normalTail, api.normalCDF_affineImage_pos L a hb threshold]

theorem thresholdPassProb_affineImage_pos (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (a : ℝ) {b : ℝ} (hb : 0 < b)
    (threshold : ℝ) :
    api.thresholdPassProb (L.affineImage a b hb) threshold =
      api.thresholdPassProb L ((threshold - a) / b) := by
  exact api.normalTail_affineImage_pos L a hb threshold

section Mixture

variable {γ : Type*} [Fintype γ]

/-- Weighted admission mass above a common threshold for finitely many Gaussian groups. -/
def mixtureTailMass (api : StandardGaussianCDFAPI)
    (weight : γ → ℝ) (law : γ → GaussianScaleLaw)
    (threshold : ℝ) : ℝ :=
  ∑ g : γ, weight g * api.thresholdPassProb (law g) threshold

theorem mixtureTailMass_nonneg (api : StandardGaussianCDFAPI)
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw}
    (hweight : ∀ g, 0 ≤ weight g) (threshold : ℝ) :
    0 ≤ api.mixtureTailMass weight law threshold := by
  dsimp [mixtureTailMass]
  exact Finset.sum_nonneg (by
    intro g _
    exact mul_nonneg (hweight g)
      (api.normalTail_nonneg (law g) threshold))

theorem mixtureTailMass_le_sum_weights (api : StandardGaussianCDFAPI)
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw}
    (hweight : ∀ g, 0 ≤ weight g) (threshold : ℝ) :
    api.mixtureTailMass weight law threshold ≤ ∑ g : γ, weight g := by
  dsimp [mixtureTailMass]
  exact Finset.sum_le_sum (by
    intro g _
    simpa using
      mul_le_mul_of_nonneg_left
        (api.normalTail_le_one (law g) threshold)
        (hweight g))

theorem mixtureTailMass_antitone_threshold (api : StandardGaussianCDFAPI)
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw}
    (hweight : ∀ g, 0 ≤ weight g) :
    Antitone (api.mixtureTailMass weight law) := by
  intro x y hxy
  dsimp [mixtureTailMass]
  exact Finset.sum_le_sum (by
    intro g _
    exact mul_le_mul_of_nonneg_left
      (api.thresholdPassProb_antitone_threshold (law g) hxy)
      (hweight g))

/--
Certificate that a common Gaussian admission threshold realizes a target
capacity for a finite mixture of group score laws.
-/
structure MixtureThresholdCertificate
    (api : StandardGaussianCDFAPI) (γ : Type*) [Fintype γ] where
  weight : γ → ℝ
  law : γ → GaussianScaleLaw
  threshold : ℝ
  capacity : ℝ
  weight_nonneg : ∀ g, 0 ≤ weight g
  capacity_eq : api.mixtureTailMass weight law threshold = capacity

namespace MixtureThresholdCertificate

theorem capacity_nonneg {api : StandardGaussianCDFAPI}
    {γ : Type*} [Fintype γ]
    (C : MixtureThresholdCertificate api γ) :
    0 ≤ C.capacity := by
  rw [← C.capacity_eq]
  exact api.mixtureTailMass_nonneg C.weight_nonneg C.threshold

theorem capacity_le_sum_weights {api : StandardGaussianCDFAPI}
    {γ : Type*} [Fintype γ]
    (C : MixtureThresholdCertificate api γ) :
    C.capacity ≤ ∑ g : γ, C.weight g := by
  rw [← C.capacity_eq]
  exact api.mixtureTailMass_le_sum_weights C.weight_nonneg C.threshold

end MixtureThresholdCertificate

end Mixture

theorem normalDensity_nonneg (api : StandardGaussianCDFAPI)
    (L : GaussianScaleLaw) (x : ℝ) :
    0 ≤ api.normalDensity L x := by
  exact div_nonneg (api.density_nonneg (L.standardize x)) L.scale_pos.le

end StandardGaussianCDFAPI

namespace GaussianVarianceLaw

/-- Nondegenerate affine image of a Gaussian variance law. -/
def affineImage (L : GaussianVarianceLaw) (a b : ℝ) (hb : b ≠ 0) :
    GaussianVarianceLaw where
  mean := a + b * L.mean
  variance := b ^ 2 * L.variance
  variance_pos := by
    exact mul_pos (sq_pos_of_ne_zero hb) L.variance_pos

@[simp] theorem affineImage_mean (L : GaussianVarianceLaw)
    (a b : ℝ) (hb : b ≠ 0) :
    (L.affineImage a b hb).mean = a + b * L.mean := rfl

@[simp] theorem affineImage_variance (L : GaussianVarianceLaw)
    (a b : ℝ) (hb : b ≠ 0) :
    (L.affineImage a b hb).variance = b ^ 2 * L.variance := rfl

end GaussianVarianceLaw

/--
Conjugate Gaussian model with one noisy signal:

`θ ~ N(priorMean, priorVar)` and `x = θ + noise`, `noiseVar > 0`.
-/
structure GaussianPriorSignal where
  priorMean : ℝ
  priorVar : ℝ
  noiseVar : ℝ
  priorVar_pos : 0 < priorVar
  noiseVar_pos : 0 < noiseVar

namespace GaussianPriorSignal

def priorPrecision (M : GaussianPriorSignal) : ℝ :=
  M.priorVar⁻¹

def noisePrecision (M : GaussianPriorSignal) : ℝ :=
  M.noiseVar⁻¹

def posteriorPrecision (M : GaussianPriorSignal) : ℝ :=
  M.priorPrecision + M.noisePrecision

def posteriorVariance (M : GaussianPriorSignal) : ℝ :=
  M.posteriorPrecision⁻¹

def priorWeight (M : GaussianPriorSignal) : ℝ :=
  M.noiseVar / (M.priorVar + M.noiseVar)

def signalWeight (M : GaussianPriorSignal) : ℝ :=
  M.priorVar / (M.priorVar + M.noiseVar)

/-- Posterior mean after observing signal value `x`. -/
def posteriorMean (M : GaussianPriorSignal) (x : ℝ) : ℝ :=
  M.posteriorVariance *
    (M.priorPrecision * M.priorMean + M.noisePrecision * x)

/-- Marginal variance of the posterior mean as a random variable. -/
def posteriorMeanVariance (M : GaussianPriorSignal) : ℝ :=
  M.priorVar - M.posteriorVariance

/-- Marginal variance of the observed signal. -/
def signalVariance (M : GaussianPriorSignal) : ℝ :=
  M.priorVar + M.noiseVar

/-- Signal value whose posterior mean is exactly `threshold`. -/
def posteriorMeanSignalCutoff (M : GaussianPriorSignal)
    (threshold : ℝ) : ℝ :=
  M.priorMean + (threshold - M.priorMean) / M.signalWeight

theorem priorPrecision_pos (M : GaussianPriorSignal) :
    0 < M.priorPrecision := by
  exact inv_pos.mpr M.priorVar_pos

theorem noisePrecision_pos (M : GaussianPriorSignal) :
    0 < M.noisePrecision := by
  exact inv_pos.mpr M.noiseVar_pos

theorem posteriorPrecision_pos (M : GaussianPriorSignal) :
    0 < M.posteriorPrecision := by
  exact add_pos M.priorPrecision_pos M.noisePrecision_pos

theorem posteriorVariance_pos (M : GaussianPriorSignal) :
    0 < M.posteriorVariance := by
  exact inv_pos.mpr M.posteriorPrecision_pos

theorem signalVariance_pos (M : GaussianPriorSignal) :
    0 < M.signalVariance := by
  exact add_pos M.priorVar_pos M.noiseVar_pos

theorem priorWeight_pos (M : GaussianPriorSignal) :
    0 < M.priorWeight := by
  exact div_pos M.noiseVar_pos (add_pos M.priorVar_pos M.noiseVar_pos)

theorem signalWeight_pos (M : GaussianPriorSignal) :
    0 < M.signalWeight := by
  exact div_pos M.priorVar_pos (add_pos M.priorVar_pos M.noiseVar_pos)

theorem priorWeight_nonneg (M : GaussianPriorSignal) :
    0 ≤ M.priorWeight :=
  M.priorWeight_pos.le

theorem signalWeight_nonneg (M : GaussianPriorSignal) :
    0 ≤ M.signalWeight :=
  M.signalWeight_pos.le

theorem priorWeight_lt_one (M : GaussianPriorSignal) :
    M.priorWeight < 1 := by
  exact (div_lt_one (add_pos M.priorVar_pos M.noiseVar_pos)).mpr
    (lt_add_of_pos_left M.noiseVar M.priorVar_pos)

theorem signalWeight_lt_one (M : GaussianPriorSignal) :
    M.signalWeight < 1 := by
  exact (div_lt_one (add_pos M.priorVar_pos M.noiseVar_pos)).mpr
    (lt_add_of_pos_right M.priorVar M.noiseVar_pos)

theorem priorWeight_add_signalWeight (M : GaussianPriorSignal) :
    M.priorWeight + M.signalWeight = 1 := by
  have hsum : M.priorVar + M.noiseVar ≠ 0 :=
    ne_of_gt (add_pos M.priorVar_pos M.noiseVar_pos)
  rw [priorWeight, signalWeight]
  field_simp [hsum]
  ring_nf

theorem posteriorVariance_eq_mul_div (M : GaussianPriorSignal) :
    M.posteriorVariance =
      M.priorVar * M.noiseVar / (M.priorVar + M.noiseVar) := by
  have hp : M.priorVar ≠ 0 := ne_of_gt M.priorVar_pos
  have hn : M.noiseVar ≠ 0 := ne_of_gt M.noiseVar_pos
  have hsum : M.priorVar + M.noiseVar ≠ 0 :=
    ne_of_gt (add_pos M.priorVar_pos M.noiseVar_pos)
  rw [posteriorVariance, posteriorPrecision, priorPrecision, noisePrecision]
  field_simp [hp, hn, hsum]
  rw [add_comm M.noiseVar M.priorVar]
  exact div_self hsum

theorem posteriorVariance_lt_priorVar (M : GaussianPriorSignal) :
    M.posteriorVariance < M.priorVar := by
  have hlt : M.priorPrecision < M.posteriorPrecision := by
    dsimp [posteriorPrecision]
    exact lt_add_of_pos_right M.priorPrecision M.noisePrecision_pos
  have h :=
    one_div_lt_one_div_of_lt M.priorPrecision_pos hlt
  simpa [posteriorVariance, priorPrecision, one_div] using h

theorem posteriorVariance_lt_noiseVar (M : GaussianPriorSignal) :
    M.posteriorVariance < M.noiseVar := by
  have hlt : M.noisePrecision < M.posteriorPrecision := by
    dsimp [posteriorPrecision]
    exact lt_add_of_pos_left M.noisePrecision M.priorPrecision_pos
  have h :=
    one_div_lt_one_div_of_lt M.noisePrecision_pos hlt
  simpa [posteriorVariance, noisePrecision, posteriorPrecision, add_comm, one_div] using h

theorem posteriorMean_eq_weightedAverage (M : GaussianPriorSignal) (x : ℝ) :
    M.posteriorMean x =
      M.priorWeight * M.priorMean + M.signalWeight * x := by
  have hp : M.priorVar ≠ 0 := ne_of_gt M.priorVar_pos
  have hn : M.noiseVar ≠ 0 := ne_of_gt M.noiseVar_pos
  have hsum : M.priorVar + M.noiseVar ≠ 0 :=
    ne_of_gt (add_pos M.priorVar_pos M.noiseVar_pos)
  rw [posteriorMean, M.posteriorVariance_eq_mul_div, priorPrecision,
    noisePrecision, priorWeight, signalWeight]
  field_simp [hp, hn, hsum]

theorem posteriorMean_eq_priorMean_add_signalWeight_mul
    (M : GaussianPriorSignal) (x : ℝ) :
    M.posteriorMean x =
      M.priorMean + M.signalWeight * (x - M.priorMean) := by
  rw [M.posteriorMean_eq_weightedAverage x]
  have h : M.priorWeight = 1 - M.signalWeight := by
    linarith [M.priorWeight_add_signalWeight]
  rw [h]
  ring

theorem posteriorMean_mono (M : GaussianPriorSignal) :
    Monotone M.posteriorMean := by
  intro x y hxy
  rw [M.posteriorMean_eq_priorMean_add_signalWeight_mul x,
    M.posteriorMean_eq_priorMean_add_signalWeight_mul y]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hxy M.priorMean)
        M.signalWeight_nonneg) M.priorMean

theorem posteriorMean_posteriorMeanSignalCutoff
    (M : GaussianPriorSignal) (threshold : ℝ) :
    M.posteriorMean (M.posteriorMeanSignalCutoff threshold) =
      threshold := by
  rw [M.posteriorMean_eq_priorMean_add_signalWeight_mul,
    posteriorMeanSignalCutoff]
  calc
    M.priorMean +
        M.signalWeight *
          (M.priorMean +
              (threshold - M.priorMean) / M.signalWeight -
            M.priorMean) =
        M.priorMean +
          M.signalWeight *
            ((threshold - M.priorMean) / M.signalWeight) := by
      congr
      ring
    _ = M.priorMean + (threshold - M.priorMean) := by
      rw [mul_div_cancel₀ _ (ne_of_gt M.signalWeight_pos)]
    _ = threshold := by
      ring

theorem posteriorMean_le_threshold_iff
    (M : GaussianPriorSignal) {x threshold : ℝ} :
    M.posteriorMean x ≤ threshold ↔
      x ≤ M.posteriorMeanSignalCutoff threshold := by
  rw [M.posteriorMean_eq_priorMean_add_signalWeight_mul,
    posteriorMeanSignalCutoff]
  constructor
  · intro h
    have hsub :
        M.signalWeight * (x - M.priorMean) ≤
          threshold - M.priorMean := by
      linarith
    have hdiv :
        x - M.priorMean ≤
          (threshold - M.priorMean) / M.signalWeight := by
      rw [le_div_iff₀ M.signalWeight_pos]
      simpa [mul_comm] using hsub
    linarith
  · intro h
    have hsub :
        x - M.priorMean ≤
          (threshold - M.priorMean) / M.signalWeight := by
      linarith
    have hmul :
        M.signalWeight * (x - M.priorMean) ≤
          threshold - M.priorMean := by
      have := (le_div_iff₀ M.signalWeight_pos).mp hsub
      simpa [mul_comm] using this
    linarith

theorem threshold_le_posteriorMean_iff
    (M : GaussianPriorSignal) {x threshold : ℝ} :
    threshold ≤ M.posteriorMean x ↔
      M.posteriorMeanSignalCutoff threshold ≤ x := by
  rw [M.posteriorMean_eq_priorMean_add_signalWeight_mul,
    posteriorMeanSignalCutoff]
  constructor
  · intro h
    have hsub :
        threshold - M.priorMean ≤
          M.signalWeight * (x - M.priorMean) := by
      linarith
    have hdiv :
        (threshold - M.priorMean) / M.signalWeight ≤
          x - M.priorMean := by
      rw [div_le_iff₀ M.signalWeight_pos]
      simpa [mul_comm] using hsub
    linarith
  · intro h
    have hsub :
        (threshold - M.priorMean) / M.signalWeight ≤
          x - M.priorMean := by
      linarith
    have hmul :
        threshold - M.priorMean ≤
          M.signalWeight * (x - M.priorMean) := by
      have := (div_le_iff₀ M.signalWeight_pos).mp hsub
      simpa [mul_comm] using this
    linarith

theorem posteriorMeanVariance_pos (M : GaussianPriorSignal) :
    0 < M.posteriorMeanVariance := by
  dsimp [posteriorMeanVariance]
  exact sub_pos.mpr M.posteriorVariance_lt_priorVar

theorem posteriorMeanVariance_eq_priorVar_sq_div
    (M : GaussianPriorSignal) :
    M.posteriorMeanVariance =
      M.priorVar ^ 2 / (M.priorVar + M.noiseVar) := by
  rw [posteriorMeanVariance, posteriorVariance_eq_mul_div]
  have hsum : M.priorVar + M.noiseVar ≠ 0 :=
    ne_of_gt (add_pos M.priorVar_pos M.noiseVar_pos)
  field_simp [hsum]
  ring_nf

/-- Law of the raw signal as a Gaussian variance law. -/
def signalLaw (M : GaussianPriorSignal) : GaussianVarianceLaw where
  mean := M.priorMean
  variance := M.signalVariance
  variance_pos := M.signalVariance_pos

theorem posteriorMeanVariance_eq_signalWeight_sq_mul_signalVariance
    (M : GaussianPriorSignal) :
    M.posteriorMeanVariance =
      M.signalWeight ^ 2 * M.signalVariance := by
  rw [M.posteriorMeanVariance_eq_priorVar_sq_div, signalWeight,
    signalVariance]
  have hsum : M.priorVar + M.noiseVar ≠ 0 :=
    ne_of_gt (add_pos M.priorVar_pos M.noiseVar_pos)
  field_simp [hsum]

/-- Law of the posterior mean as a Gaussian variance law, using the standard conjugate formula. -/
def posteriorMeanLaw (M : GaussianPriorSignal) : GaussianVarianceLaw where
  mean := M.priorMean
  variance := M.posteriorMeanVariance
  variance_pos := M.posteriorMeanVariance_pos

/--
Location-scale law of the posterior mean obtained by applying the affine
posterior-mean map to a location-scale signal law.
-/
def posteriorMeanScaleLaw (M : GaussianPriorSignal)
    (signalLaw : GaussianScaleLaw) : GaussianScaleLaw :=
  signalLaw.affineImage (M.priorWeight * M.priorMean)
    M.signalWeight M.signalWeight_pos

theorem posteriorMeanScaleLaw_mean_of_signal_mean_eq
    (M : GaussianPriorSignal) {signalLaw : GaussianScaleLaw}
    (hmean : signalLaw.mean = M.priorMean) :
    (M.posteriorMeanScaleLaw signalLaw).mean = M.priorMean := by
  rw [posteriorMeanScaleLaw, GaussianScaleLaw.affineImage_mean, hmean]
  calc
    M.priorWeight * M.priorMean + M.signalWeight * M.priorMean =
        (M.priorWeight + M.signalWeight) * M.priorMean := by
      ring
    _ = M.priorMean := by
      rw [M.priorWeight_add_signalWeight]
      ring

theorem posteriorMeanSignalCutoff_eq_affineCutoff
    (M : GaussianPriorSignal) (threshold : ℝ) :
    M.posteriorMeanSignalCutoff threshold =
      (threshold - M.priorWeight * M.priorMean) / M.signalWeight := by
  rw [posteriorMeanSignalCutoff]
  have h : M.priorWeight = 1 - M.signalWeight := by
    linarith [M.priorWeight_add_signalWeight]
  rw [h]
  field_simp [ne_of_gt M.signalWeight_pos]
  ring

theorem thresholdPassProb_posteriorMeanScaleLaw
    (api : StandardGaussianCDFAPI) (M : GaussianPriorSignal)
    (signalLaw : GaussianScaleLaw) (threshold : ℝ) :
    api.thresholdPassProb (M.posteriorMeanScaleLaw signalLaw) threshold =
      api.thresholdPassProb signalLaw
        (M.posteriorMeanSignalCutoff threshold) := by
  rw [posteriorMeanScaleLaw,
    api.thresholdPassProb_affineImage_pos signalLaw
      (M.priorWeight * M.priorMean) M.signalWeight_pos threshold,
    M.posteriorMeanSignalCutoff_eq_affineCutoff threshold]

/-- Posterior mean from a raw signal whose noise has known mean. -/
def posteriorMeanOfSignalWithNoiseMean (M : GaussianPriorSignal)
    (noiseMean signal : ℝ) : ℝ :=
  M.posteriorMean (signal - noiseMean)

/-- Raw-signal cutoff corresponding to a posterior-mean threshold. -/
def posteriorMeanRawSignalCutoff (M : GaussianPriorSignal)
    (noiseMean threshold : ℝ) : ℝ :=
  noiseMean + M.posteriorMeanSignalCutoff threshold

theorem posteriorMeanOfSignalWithNoiseMean_eq
    (M : GaussianPriorSignal) (noiseMean signal : ℝ) :
    M.posteriorMeanOfSignalWithNoiseMean noiseMean signal =
      M.priorMean +
        M.signalWeight * (signal - noiseMean - M.priorMean) := by
  rw [posteriorMeanOfSignalWithNoiseMean,
    M.posteriorMean_eq_priorMean_add_signalWeight_mul]

theorem posteriorMeanOfSignalWithNoiseMean_le_threshold_iff
    (M : GaussianPriorSignal) {noiseMean signal threshold : ℝ} :
    M.posteriorMeanOfSignalWithNoiseMean noiseMean signal ≤ threshold ↔
      signal ≤ M.posteriorMeanRawSignalCutoff noiseMean threshold := by
  rw [posteriorMeanOfSignalWithNoiseMean,
    M.posteriorMean_le_threshold_iff,
    posteriorMeanRawSignalCutoff]
  constructor <;> intro h <;> linarith

theorem threshold_le_posteriorMeanOfSignalWithNoiseMean_iff
    (M : GaussianPriorSignal) {noiseMean signal threshold : ℝ} :
    threshold ≤ M.posteriorMeanOfSignalWithNoiseMean noiseMean signal ↔
      M.posteriorMeanRawSignalCutoff noiseMean threshold ≤ signal := by
  rw [posteriorMeanOfSignalWithNoiseMean,
    M.threshold_le_posteriorMean_iff,
    posteriorMeanRawSignalCutoff]
  constructor <;> intro h <;> linarith

/--
Location-scale law of the posterior mean obtained from a raw signal with
nonzero noise mean.
-/
def posteriorMeanRawSignalScaleLaw (M : GaussianPriorSignal)
    (noiseMean : ℝ) (rawSignalLaw : GaussianScaleLaw) :
    GaussianScaleLaw :=
  rawSignalLaw.affineImage
    (M.priorWeight * M.priorMean - M.signalWeight * noiseMean)
    M.signalWeight M.signalWeight_pos

theorem posteriorMeanRawSignalScaleLaw_mean_of_signal_mean_eq
    (M : GaussianPriorSignal) {noiseMean : ℝ}
    {rawSignalLaw : GaussianScaleLaw}
    (hmean : rawSignalLaw.mean = M.priorMean + noiseMean) :
    (M.posteriorMeanRawSignalScaleLaw noiseMean rawSignalLaw).mean =
      M.priorMean := by
  rw [posteriorMeanRawSignalScaleLaw, GaussianScaleLaw.affineImage_mean,
    hmean]
  calc
    M.priorWeight * M.priorMean - M.signalWeight * noiseMean +
        M.signalWeight * (M.priorMean + noiseMean) =
        (M.priorWeight + M.signalWeight) * M.priorMean := by
      ring
    _ = M.priorMean := by
      rw [M.priorWeight_add_signalWeight]
      ring

theorem posteriorMeanRawSignalCutoff_eq_affineCutoff
    (M : GaussianPriorSignal) (noiseMean threshold : ℝ) :
    M.posteriorMeanRawSignalCutoff noiseMean threshold =
      (threshold -
          (M.priorWeight * M.priorMean -
            M.signalWeight * noiseMean)) / M.signalWeight := by
  rw [posteriorMeanRawSignalCutoff,
    M.posteriorMeanSignalCutoff_eq_affineCutoff threshold]
  field_simp [ne_of_gt M.signalWeight_pos]
  ring

theorem thresholdPassProb_posteriorMeanRawSignalScaleLaw
    (api : StandardGaussianCDFAPI) (M : GaussianPriorSignal)
    (noiseMean : ℝ) (rawSignalLaw : GaussianScaleLaw)
    (threshold : ℝ) :
    api.thresholdPassProb
        (M.posteriorMeanRawSignalScaleLaw noiseMean rawSignalLaw)
        threshold =
      api.thresholdPassProb rawSignalLaw
        (M.posteriorMeanRawSignalCutoff noiseMean threshold) := by
  rw [posteriorMeanRawSignalScaleLaw,
    api.thresholdPassProb_affineImage_pos rawSignalLaw
      (M.priorWeight * M.priorMean - M.signalWeight * noiseMean)
      M.signalWeight_pos threshold,
    M.posteriorMeanRawSignalCutoff_eq_affineCutoff noiseMean threshold]

end GaussianPriorSignal

/-- Conjugate Gaussian model with a finite family of noisy signals. -/
structure GaussianSignalFamily (ι : Type*) [Fintype ι] where
  priorMean : ℝ
  priorVar : ℝ
  noiseVar : ι → ℝ
  priorVar_pos : 0 < priorVar
  noiseVar_pos : ∀ i, 0 < noiseVar i

namespace GaussianSignalFamily

variable {ι : Type*} [Fintype ι]

def priorPrecision (M : GaussianSignalFamily ι) : ℝ :=
  M.priorVar⁻¹

def signalPrecision (M : GaussianSignalFamily ι) (i : ι) : ℝ :=
  (M.noiseVar i)⁻¹

def posteriorPrecision (M : GaussianSignalFamily ι) : ℝ :=
  M.priorPrecision + ∑ i : ι, M.signalPrecision i

def posteriorVariance (M : GaussianSignalFamily ι) : ℝ :=
  M.posteriorPrecision⁻¹

def priorWeight (M : GaussianSignalFamily ι) : ℝ :=
  M.posteriorVariance * M.priorPrecision

def signalWeight (M : GaussianSignalFamily ι) (i : ι) : ℝ :=
  M.posteriorVariance * M.signalPrecision i

/-- Posterior mean from a finite vector of observed signal values. -/
def posteriorMean (M : GaussianSignalFamily ι) (x : ι → ℝ) : ℝ :=
  M.posteriorVariance *
    (M.priorPrecision * M.priorMean +
      ∑ i : ι, M.signalPrecision i * x i)

theorem priorPrecision_pos (M : GaussianSignalFamily ι) :
    0 < M.priorPrecision := by
  exact inv_pos.mpr M.priorVar_pos

theorem signalPrecision_pos (M : GaussianSignalFamily ι) (i : ι) :
    0 < M.signalPrecision i := by
  exact inv_pos.mpr (M.noiseVar_pos i)

theorem posteriorPrecision_pos (M : GaussianSignalFamily ι) :
    0 < M.posteriorPrecision := by
  have hsum_nonneg : 0 ≤ ∑ i : ι, M.signalPrecision i := by
    exact Finset.sum_nonneg (by
      intro i _
      exact (M.signalPrecision_pos i).le)
  exact add_pos_of_pos_of_nonneg M.priorPrecision_pos hsum_nonneg

theorem posteriorVariance_pos (M : GaussianSignalFamily ι) :
    0 < M.posteriorVariance := by
  exact inv_pos.mpr M.posteriorPrecision_pos

theorem posteriorVariance_le_priorVar (M : GaussianSignalFamily ι) :
    M.posteriorVariance ≤ M.priorVar := by
  have hsum_nonneg : 0 ≤ ∑ i : ι, M.signalPrecision i := by
    exact Finset.sum_nonneg (by
      intro i _
      exact (M.signalPrecision_pos i).le)
  have hle : M.priorPrecision ≤ M.posteriorPrecision := by
    dsimp [posteriorPrecision]
    exact le_add_of_nonneg_right hsum_nonneg
  have h := one_div_le_one_div_of_le M.priorPrecision_pos hle
  simpa [posteriorVariance, priorPrecision, one_div] using h

theorem posteriorVariance_lt_priorVar [Nonempty ι]
    (M : GaussianSignalFamily ι) :
    M.posteriorVariance < M.priorVar := by
  have hsum_pos : 0 < ∑ i : ι, M.signalPrecision i := by
    exact Finset.sum_pos
      (fun i _ => M.signalPrecision_pos i)
      Finset.univ_nonempty
  have hlt : M.priorPrecision < M.posteriorPrecision := by
    dsimp [posteriorPrecision]
    exact lt_add_of_pos_right M.priorPrecision hsum_pos
  have h := one_div_lt_one_div_of_lt M.priorPrecision_pos hlt
  simpa [posteriorVariance, priorPrecision, one_div] using h

/-- Marginal variance of the posterior mean for a finite centered signal family. -/
def posteriorMeanVariance (M : GaussianSignalFamily ι) : ℝ :=
  M.priorVar - M.posteriorVariance

theorem posteriorMeanVariance_nonneg (M : GaussianSignalFamily ι) :
    0 ≤ M.posteriorMeanVariance := by
  dsimp [posteriorMeanVariance]
  exact sub_nonneg.mpr M.posteriorVariance_le_priorVar

theorem posteriorMeanVariance_pos [Nonempty ι]
    (M : GaussianSignalFamily ι) :
    0 < M.posteriorMeanVariance := by
  dsimp [posteriorMeanVariance]
  exact sub_pos.mpr M.posteriorVariance_lt_priorVar

/-- Law of the finite-feature posterior mean as a Gaussian variance law. -/
def posteriorMeanLaw [Nonempty ι]
    (M : GaussianSignalFamily ι) : GaussianVarianceLaw where
  mean := M.priorMean
  variance := M.posteriorMeanVariance
  variance_pos := M.posteriorMeanVariance_pos

theorem priorWeight_pos (M : GaussianSignalFamily ι) :
    0 < M.priorWeight := by
  exact mul_pos M.posteriorVariance_pos M.priorPrecision_pos

theorem signalWeight_pos (M : GaussianSignalFamily ι) (i : ι) :
    0 < M.signalWeight i := by
  exact mul_pos M.posteriorVariance_pos (M.signalPrecision_pos i)

theorem priorWeight_nonneg (M : GaussianSignalFamily ι) :
    0 ≤ M.priorWeight :=
  M.priorWeight_pos.le

theorem signalWeight_nonneg (M : GaussianSignalFamily ι) (i : ι) :
    0 ≤ M.signalWeight i :=
  (M.signalWeight_pos i).le

theorem priorWeight_add_sum_signalWeight_eq_one
    (M : GaussianSignalFamily ι) :
    M.priorWeight + ∑ i : ι, M.signalWeight i = 1 := by
  change M.posteriorVariance * M.priorPrecision +
      ∑ i : ι, M.posteriorVariance * M.signalPrecision i = 1
  rw [← Finset.mul_sum, ← mul_add,
    posteriorVariance, posteriorPrecision]
  exact inv_mul_cancel₀ (ne_of_gt M.posteriorPrecision_pos)

theorem posteriorMean_eq_weighted_sum
    (M : GaussianSignalFamily ι) (x : ι → ℝ) :
    M.posteriorMean x =
      M.priorWeight * M.priorMean +
        ∑ i : ι, M.signalWeight i * x i := by
  change
    M.posteriorVariance *
        (M.priorPrecision * M.priorMean +
          ∑ i : ι, M.signalPrecision i * x i) =
      (M.posteriorVariance * M.priorPrecision) * M.priorMean +
        ∑ i : ι, (M.posteriorVariance * M.signalPrecision i) * x i
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl (by
      intro i _
      ring)

/-- The posterior mean is monotone in every observed signal coordinate. -/
theorem posteriorMean_mono_of_pointwise_le
    (M : GaussianSignalFamily ι) {x y : ι → ℝ}
    (hxy : ∀ i, x i ≤ y i) :
    M.posteriorMean x ≤ M.posteriorMean y := by
  dsimp [posteriorMean]
  refine mul_le_mul_of_nonneg_left ?_ M.posteriorVariance_pos.le
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left
      (Finset.sum_le_sum (by
        intro i _
        exact mul_le_mul_of_nonneg_left (hxy i) (M.signalPrecision_pos i).le))
      (M.priorPrecision * M.priorMean)

end GaussianSignalFamily

/--
Finite Gaussian signal family with nonzero signal-specific noise means.

The observed signal has the source-paper form `x i = q + noiseMean i + error i`;
posterior formulas are delegated to `GaussianSignalFamily` after centering each
coordinate by `noiseMean i`.
-/
structure GaussianOffsetSignalFamily (ι : Type*) [Fintype ι] where
  priorMean : ℝ
  priorVar : ℝ
  noiseMean : ι → ℝ
  noiseVar : ι → ℝ
  priorVar_pos : 0 < priorVar
  noiseVar_pos : ∀ i, 0 < noiseVar i

namespace GaussianOffsetSignalFamily

variable {ι : Type*} [Fintype ι]

def centeredFamily (M : GaussianOffsetSignalFamily ι) :
    GaussianSignalFamily ι where
  priorMean := M.priorMean
  priorVar := M.priorVar
  noiseVar := M.noiseVar
  priorVar_pos := M.priorVar_pos
  noiseVar_pos := M.noiseVar_pos

def centeredSignal (M : GaussianOffsetSignalFamily ι)
    (x : ι → ℝ) (i : ι) : ℝ :=
  x i - M.noiseMean i

def posteriorMean (M : GaussianOffsetSignalFamily ι)
    (x : ι → ℝ) : ℝ :=
  M.centeredFamily.posteriorMean (M.centeredSignal x)

theorem posteriorMean_eq_centered
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) :
    M.posteriorMean x =
      M.centeredFamily.posteriorMean (M.centeredSignal x) := rfl

theorem priorWeight_add_sum_signalWeight_eq_one
    (M : GaussianOffsetSignalFamily ι) :
    M.centeredFamily.priorWeight +
        ∑ i : ι, M.centeredFamily.signalWeight i = 1 :=
  M.centeredFamily.priorWeight_add_sum_signalWeight_eq_one

/-- Marginal variance of the offset-family posterior mean. -/
def posteriorMeanVariance (M : GaussianOffsetSignalFamily ι) : ℝ :=
  M.centeredFamily.posteriorMeanVariance

theorem posteriorMeanVariance_nonneg
    (M : GaussianOffsetSignalFamily ι) :
    0 ≤ M.posteriorMeanVariance :=
  M.centeredFamily.posteriorMeanVariance_nonneg

theorem posteriorMeanVariance_pos [Nonempty ι]
    (M : GaussianOffsetSignalFamily ι) :
    0 < M.posteriorMeanVariance :=
  M.centeredFamily.posteriorMeanVariance_pos

/-- Law of the offset-family posterior mean as a Gaussian variance law. -/
def posteriorMeanLaw [Nonempty ι]
    (M : GaussianOffsetSignalFamily ι) : GaussianVarianceLaw where
  mean := M.priorMean
  variance := M.posteriorMeanVariance
  variance_pos := M.posteriorMeanVariance_pos

theorem posteriorMean_eq_weighted_sum
    (M : GaussianOffsetSignalFamily ι) (x : ι → ℝ) :
    M.posteriorMean x =
      M.centeredFamily.priorWeight * M.priorMean +
        ∑ i : ι,
          M.centeredFamily.signalWeight i *
            (x i - M.noiseMean i) := by
  rw [posteriorMean, GaussianSignalFamily.posteriorMean_eq_weighted_sum]
  rfl

/-- The offset-family posterior mean is monotone in every raw signal coordinate. -/
theorem posteriorMean_mono_of_pointwise_le
    (M : GaussianOffsetSignalFamily ι) {x y : ι → ℝ}
    (hxy : ∀ i, x i ≤ y i) :
    M.posteriorMean x ≤ M.posteriorMean y := by
  rw [posteriorMean, posteriorMean]
  exact M.centeredFamily.posteriorMean_mono_of_pointwise_le
    (fun i => sub_le_sub_right (hxy i) (M.noiseMean i))

end GaussianOffsetSignalFamily

/--
Reusable certificate for normal-density/tail analytic facts.

GLM/LG-style papers can use this as the boundary between algebraic Gaussian
formalization and the hard analytic facts about inverse Mills ratios or hazard
rates.
-/
structure GaussianHazardCertificate where
  api : StandardGaussianCDFAPI
  hazard : ℝ → ℝ
  tail_pos : ∀ z, 0 < 1 - api.cdf z
  hazard_eq : ∀ z, hazard z = api.density z / (1 - api.cdf z)
  hazard_mono : Monotone hazard

namespace GaussianHazardCertificate

theorem normalTail_pos (C : GaussianHazardCertificate)
    (L : GaussianScaleLaw) (threshold : ℝ) :
    0 < C.api.normalTail L threshold := by
  exact C.tail_pos (L.standardize threshold)

theorem normalDensity_div_normalTail_eq_hazard_div_scale
    (C : GaussianHazardCertificate) (L : GaussianScaleLaw)
    (threshold : ℝ) :
    C.api.normalDensity L threshold / C.api.normalTail L threshold =
      C.hazard (L.standardize threshold) / L.scale := by
  rw [StandardGaussianCDFAPI.normalDensity,
    StandardGaussianCDFAPI.normalTail,
    StandardGaussianCDFAPI.normalCDF,
    C.hazard_eq]
  field_simp [ne_of_gt (C.tail_pos (L.standardize threshold)),
    ne_of_gt L.scale_pos]

/--
Certificate-level formula for the conditional mean above a threshold for a
location-scale Gaussian, expressed through the standard-normal hazard.
-/
def normalUpperTailMean (C : GaussianHazardCertificate)
    (L : GaussianScaleLaw) (threshold : ℝ) : ℝ :=
  L.mean + L.scale * C.hazard (L.standardize threshold)

theorem normalUpperTailMean_mono_threshold
    (C : GaussianHazardCertificate) (L : GaussianScaleLaw) :
    Monotone (C.normalUpperTailMean L) := by
  intro x y hxy
  dsimp [normalUpperTailMean]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left
      (mul_le_mul_of_nonneg_left
        (C.hazard_mono (L.standardize_mono hxy)) L.scale_pos.le)
      L.mean

section Mixture

variable {γ : Type*} [Fintype γ]

theorem mixtureTailMass_pos
    (C : GaussianHazardCertificate)
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw}
    (hweight : ∀ g, 0 ≤ weight g) (hpos : ∃ g, 0 < weight g)
    (threshold : ℝ) :
    0 < C.api.mixtureTailMass weight law threshold := by
  dsimp [StandardGaussianCDFAPI.mixtureTailMass]
  exact Finset.sum_pos' (by
    intro g _
    exact mul_nonneg (hweight g)
      (C.normalTail_pos (law g) threshold).le) (by
    rcases hpos with ⟨g, hg⟩
    exact ⟨g, Finset.mem_univ g,
      mul_pos hg (C.normalTail_pos (law g) threshold)⟩)

/-- Numerator for the finite-mixture mean of Gaussian scores above a threshold. -/
def mixtureUpperTailMeanNumerator
    (C : GaussianHazardCertificate)
    (weight : γ → ℝ) (law : γ → GaussianScaleLaw)
    (threshold : ℝ) : ℝ :=
  ∑ g : γ,
    weight g * C.api.thresholdPassProb (law g) threshold *
      C.normalUpperTailMean (law g) threshold

/-- Mean score among admitted students in a finite Gaussian mixture. -/
def mixtureUpperTailMean
    (C : GaussianHazardCertificate)
    (weight : γ → ℝ) (law : γ → GaussianScaleLaw)
    (threshold : ℝ) : ℝ :=
  C.mixtureUpperTailMeanNumerator weight law threshold /
    C.api.mixtureTailMass weight law threshold

theorem mixtureUpperTailMean_mul_tailMass_eq_numerator
    (C : GaussianHazardCertificate)
    {weight : γ → ℝ} {law : γ → GaussianScaleLaw}
    {threshold : ℝ}
    (hmass : 0 < C.api.mixtureTailMass weight law threshold) :
    C.mixtureUpperTailMean weight law threshold *
        C.api.mixtureTailMass weight law threshold =
      C.mixtureUpperTailMeanNumerator weight law threshold := by
  rw [mixtureUpperTailMean]
  exact div_mul_cancel₀ _ (ne_of_gt hmass)

end Mixture

end GaussianHazardCertificate

end

end Probability
end EconCSLib
