import EconCSLib.Foundations.Probability.GaussianMathlib
import EconCSLib.Foundations.Probability.MeasureInequalities

/-!
# Bivariate Gaussian Source Laws

Reusable correlated standard-Gaussian laws for two-dimensional probability
bookkeeping.

## Main declarations

- `correlatedStandardGaussianLaw`
- `standardBivariateGaussianCDF`
- `owenAffineUpperSelectionMass`
- `correlatedStandardGaussianLaw_map_fst`
- `correlatedStandardGaussianLaw_map_snd`
- `correlatedStandardGaussianLaw_noAtoms_map_fst`
- `correlatedStandardGaussianLaw_noAtoms_map_snd`
- `correlatedStandardGaussianLaw_isOpenPosMeasure`
- `standardBivariateGaussianCDF_continuous_of_rho_sq_le_one`
- `correlatedStandardGaussianLaw_firstCoordinateLowerMass`
- `correlatedStandardGaussianLaw_verticalUpperStripMass_pos`
- `owenAffineUpperSelectionMass_eq_correlatedStandardGaussian_verticalUpperStripMass`
- `correlatedStandardGaussianLaw_verticalBoundaryLeft_real_eq_zero`
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

/--
Continuous-linear version of `correlatedStandardGaussianMap`.

This is useful for characteristic-function proofs, while the function-valued
map remains the public definition used by existing paper files.
-/
noncomputable def correlatedStandardGaussianCLM (rho : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (rho • (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      Real.sqrt (1 - rho ^ 2) • (ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp]
theorem correlatedStandardGaussianCLM_apply (rho : ℝ) (p : ℝ × ℝ) :
    correlatedStandardGaussianCLM rho p =
      correlatedStandardGaussianMap rho p := by
  simp [correlatedStandardGaussianCLM, correlatedStandardGaussianMap]

/--
Owen's affine standardization map.  For independent standard normals `(X,Z)`,
this sends `(X,Z)` to `((X - c Z)/sqrt(1+c^2), Z)`.
-/
noncomputable def owenStandardizingGaussianCLM (c : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  let denom := Real.sqrt (1 + c ^ 2)
  ((denom⁻¹) • (ContinuousLinearMap.fst ℝ ℝ ℝ) -
      (c / denom) • (ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp]
theorem owenStandardizingGaussianCLM_apply (c : ℝ) (p : ℝ × ℝ) :
    owenStandardizingGaussianCLM c p =
      ((p.1 - c * p.2) / Real.sqrt (1 + c ^ 2), p.2) := by
  simp [owenStandardizingGaussianCLM]
  ring

theorem measurable_correlatedStandardGaussianMap (rho : ℝ) :
    Measurable (correlatedStandardGaussianMap rho) := by
  unfold correlatedStandardGaussianMap
  fun_prop

/-- The correlated standard-Gaussian source map is continuous. -/
theorem continuous_correlatedStandardGaussianMap (rho : ℝ) :
    Continuous (correlatedStandardGaussianMap rho) := by
  unfold correlatedStandardGaussianMap
  fun_prop

/-- For `rho^2 < 1`, the correlated standard-Gaussian source map is onto. -/
theorem correlatedStandardGaussianMap_surjective_of_rho_sq_lt_one
    {rho : ℝ} (hrho : rho ^ 2 < 1) :
    Function.Surjective (correlatedStandardGaussianMap rho) := by
  intro z
  let scale : ℝ := Real.sqrt (1 - rho ^ 2)
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact Real.sqrt_pos.2 (sub_pos.mpr hrho)
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  refine ⟨(z.1, (z.2 - rho * z.1) / scale), ?_⟩
  ext
  · simp [correlatedStandardGaussianMap]
  · simp [correlatedStandardGaussianMap]
    field_simp [hscale_ne]
    ring

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

/-- The function-valued and continuous-linear definitions induce the same correlated law. -/
theorem correlatedStandardGaussianLaw_eq_map_correlatedStandardGaussianCLM (rho : ℝ) :
    correlatedStandardGaussianLaw rho =
      (standardGaussianMeasure.prod standardGaussianMeasure).map
        (correlatedStandardGaussianCLM rho) := by
  rw [correlatedStandardGaussianLaw]
  congr 1

/-- Characteristic function of a standard normal against an arbitrary continuous linear form. -/
theorem charFunDual_standardGaussianMeasure (L : StrongDual ℝ ℝ) :
    charFunDual standardGaussianMeasure L =
      Complex.exp (-((L 1 : ℝ) ^ 2) / 2) := by
  rw [charFunDual_eq_charFun_map_one]
  rw [standardGaussianMeasure]
  rw [ProbabilityTheory.gaussianReal_map_continuousLinearMap]
  rw [ProbabilityTheory.charFun_gaussianReal]
  simp [Real.toNNReal_of_nonneg (sq_nonneg (L 1))]
  ring_nf

/--
Characteristic function of independent standard normals in coordinates.  This
small lemma keeps later bivariate Gaussian map-identification proofs from
repeating product-measure bookkeeping.
-/
theorem charFunDual_standardGaussianProduct (L : StrongDual ℝ (ℝ × ℝ)) :
    charFunDual (standardGaussianMeasure.prod standardGaussianMeasure) L =
      Complex.exp
        (-(((L (1, 0) : ℝ) ^ 2 + (L (0, 1) : ℝ) ^ 2) / 2)) := by
  rw [charFunDual_prod]
  rw [charFunDual_standardGaussianMeasure
    (L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ))]
  rw [charFunDual_standardGaussianMeasure
    (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ))]
  simp
  rw [← Complex.exp_add]
  congr
  ring

/-- Algebra for the Owen correlation scale. -/
theorem sqrt_one_sub_neg_div_sqrt_one_add_sq_sq (c : ℝ) :
    Real.sqrt (1 - ((-c) / Real.sqrt (1 + c ^ 2)) ^ 2) =
      (Real.sqrt (1 + c ^ 2))⁻¹ := by
  let denom : ℝ := Real.sqrt (1 + c ^ 2)
  have hpos : 0 < 1 + c ^ 2 := by nlinarith [sq_nonneg c]
  have hdenom_pos : 0 < denom := by
    dsimp [denom]
    exact Real.sqrt_pos.2 hpos
  have hdenom_ne : denom ≠ 0 := ne_of_gt hdenom_pos
  have hdenom_sq : denom ^ 2 = 1 + c ^ 2 := by
    dsimp [denom]
    exact Real.sq_sqrt (by positivity)
  have hinside :
      1 - ((-c) / denom) ^ 2 = denom⁻¹ ^ 2 := by
    field_simp [hdenom_ne]
    rw [hdenom_sq]
    ring
  rw [show Real.sqrt (1 - ((-c) / Real.sqrt (1 + c ^ 2)) ^ 2) =
      Real.sqrt (1 - ((-c) / denom) ^ 2) by rfl]
  rw [hinside]
  exact Real.sqrt_sq_eq_abs (denom⁻¹) |>.trans (abs_of_pos (inv_pos.mpr hdenom_pos))

/--
The Owen standardization map has the same law as the correlated
standard-Gaussian map with `rho = -c/sqrt(1+c^2)`.

This is the probabilistic content behind the bivariate-normal/Owen
admissions papers.
-/
theorem owenStandardizingGaussianLaw_eq_correlatedStandardGaussianLaw (c : ℝ) :
    (standardGaussianMeasure.prod standardGaussianMeasure).map
        (owenStandardizingGaussianCLM c) =
      correlatedStandardGaussianLaw ((-c) / Real.sqrt (1 + c ^ 2)) := by
  let base : Measure (ℝ × ℝ) :=
    standardGaussianMeasure.prod standardGaussianMeasure
  let denom : ℝ := Real.sqrt (1 + c ^ 2)
  let rho : ℝ := (-c) / denom
  have hpos : 0 < 1 + c ^ 2 := by nlinarith [sq_nonneg c]
  have hdenom_pos : 0 < denom := by
    dsimp [denom]
    exact Real.sqrt_pos.2 hpos
  have hdenom_ne : denom ≠ 0 := ne_of_gt hdenom_pos
  have hscale :
      Real.sqrt (1 - rho ^ 2) = denom⁻¹ := by
    simpa [rho, denom] using sqrt_one_sub_neg_div_sqrt_one_add_sq_sq c
  rw [correlatedStandardGaussianLaw_eq_map_correlatedStandardGaussianCLM rho]
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_map (owenStandardizingGaussianCLM c) L]
  rw [charFunDual_map (correlatedStandardGaussianCLM rho) L]
  rw [charFunDual_standardGaussianProduct]
  rw [charFunDual_standardGaussianProduct]
  congr 1
  have hsum :
      (((L.comp (owenStandardizingGaussianCLM c)) (1, 0) : ℝ) ^ 2 +
          ((L.comp (owenStandardizingGaussianCLM c)) (0, 1) : ℝ) ^ 2) =
        (((L.comp (correlatedStandardGaussianCLM rho)) (1, 0) : ℝ) ^ 2 +
          ((L.comp (correlatedStandardGaussianCLM rho)) (0, 1) : ℝ) ^ 2) := by
    have hdenom_sq : denom ^ 2 = 1 + c ^ 2 := by
      dsimp [denom]
      exact Real.sq_sqrt (by positivity)
    have hLpair :
        ∀ x y : ℝ, L (x, y) = x * L (1, 0) + y * L (0, 1) := by
      intro x y
      have hdecomp : (x, y) =
          x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by
        ext <;> simp
      rw [hdecomp, map_add, map_smul, map_smul]
      ring
    have hO1 :
        ((L.comp (owenStandardizingGaussianCLM c)) (1, 0) : ℝ) =
          denom⁻¹ * L (1, 0) := by
      change L (owenStandardizingGaussianCLM c (1, 0)) = denom⁻¹ * L (1, 0)
      have harg :
          owenStandardizingGaussianCLM c (1, 0) = (denom⁻¹, 0) := by
        simp [owenStandardizingGaussianCLM_apply, denom]
      rw [harg, hLpair denom⁻¹ 0]
      ring
    have hO2 :
        ((L.comp (owenStandardizingGaussianCLM c)) (0, 1) : ℝ) =
          (-c / denom) * L (1, 0) + L (0, 1) := by
      change L (owenStandardizingGaussianCLM c (0, 1)) =
        (-c / denom) * L (1, 0) + L (0, 1)
      have harg :
          owenStandardizingGaussianCLM c (0, 1) = (-c / denom, 1) := by
        simp [owenStandardizingGaussianCLM_apply, denom]
      rw [harg, hLpair (-c / denom) 1]
      ring
    have hC1 :
        ((L.comp (correlatedStandardGaussianCLM rho)) (1, 0) : ℝ) =
          L (1, 0) + rho * L (0, 1) := by
      change L (correlatedStandardGaussianCLM rho (1, 0)) =
        L (1, 0) + rho * L (0, 1)
      have harg :
          correlatedStandardGaussianCLM rho (1, 0) = (1, rho) := by
        simp [correlatedStandardGaussianCLM_apply, correlatedStandardGaussianMap]
      rw [harg, hLpair 1 rho]
      ring
    have hC2 :
        ((L.comp (correlatedStandardGaussianCLM rho)) (0, 1) : ℝ) =
          denom⁻¹ * L (0, 1) := by
      change L (correlatedStandardGaussianCLM rho (0, 1)) =
        denom⁻¹ * L (0, 1)
      have harg :
          correlatedStandardGaussianCLM rho (0, 1) = (0, denom⁻¹) := by
        simp [correlatedStandardGaussianCLM_apply, correlatedStandardGaussianMap, hscale]
      rw [harg, hLpair 0 denom⁻¹]
      ring
    rw [hO1, hO2, hC1, hC2]
    dsimp [rho]
    field_simp [hdenom_ne]
    nlinarith [hdenom_sq]
  exact_mod_cast
    (by
      simpa [ContinuousLinearMap.comp_apply, correlatedStandardGaussianCLM_apply]
        using hsum)

/--
Source-side affine selection mass behind Owen's formula:
`P(X <= A * sqrt(1+c^2) + c Z, B <= Z)` for independent standard normals.
-/
noncomputable def owenAffineUpperSelectionMass (c A B : ℝ) : ℝ :=
  (standardGaussianMeasure.prod standardGaussianMeasure).real
    {p : ℝ × ℝ | p.1 ≤ A * Real.sqrt (1 + c ^ 2) + c * p.2 ∧ B ≤ p.2}

/--
Owen affine upper-selection mass equals the correlated-Gaussian vertical strip.

This is a measure-theoretic replacement for repeatedly invoking Owen's
tabulated integral identity: standardize the affine half-space, identify the
resulting bivariate Gaussian law by characteristic functions, and then read off
the vertical strip.
-/
theorem owenAffineUpperSelectionMass_eq_correlatedStandardGaussian_verticalUpperStripMass
    (c A B : ℝ) :
    owenAffineUpperSelectionMass c A B =
      verticalUpperStripMass
        (correlatedStandardGaussianLaw ((-c) / Real.sqrt (1 + c ^ 2))) A B := by
  let base : Measure (ℝ × ℝ) :=
    standardGaussianMeasure.prod standardGaussianMeasure
  let denom : ℝ := Real.sqrt (1 + c ^ 2)
  have hpos : 0 < 1 + c ^ 2 := by nlinarith [sq_nonneg c]
  have hdenom_pos : 0 < denom := by
    dsimp [denom]
    exact Real.sqrt_pos.2 hpos
  have hdenom_ne : denom ≠ 0 := ne_of_gt hdenom_pos
  have hpre :
      (owenStandardizingGaussianCLM c) ⁻¹'
          {p : ℝ × ℝ | p.1 ≤ A ∧ B ≤ p.2} =
        {p : ℝ × ℝ | p.1 ≤ A * denom + c * p.2 ∧ B ≤ p.2} := by
    ext p
    constructor
    · intro hp
      constructor
      · have hle : (p.1 - c * p.2) / denom ≤ A := by
          simpa [denom] using hp.1
        have hle' : p.1 - c * p.2 ≤ A * denom := by
          exact (div_le_iff₀ hdenom_pos).mp hle
        linarith
      · simpa using hp.2
    · intro hp
      constructor
      · have hp1 : p.1 ≤ A * denom + c * p.2 := hp.1
        have hle' : p.1 - c * p.2 ≤ A * denom := by linarith
        have hle : (p.1 - c * p.2) / denom ≤ A :=
          (div_le_iff₀ hdenom_pos).mpr hle'
        simpa [denom] using hle
      · simpa using hp.2
  calc
    owenAffineUpperSelectionMass c A B
        =
          (base.map (owenStandardizingGaussianCLM c)).real
            {p : ℝ × ℝ | p.1 ≤ A ∧ B ≤ p.2} := by
          rw [owenAffineUpperSelectionMass, measureReal_def, measureReal_def,
            Measure.map_apply (by fun_prop) (measurableSet_verticalUpperStrip A B),
            hpre]
    _ =
          (correlatedStandardGaussianLaw ((-c) / Real.sqrt (1 + c ^ 2))).real
            {p : ℝ × ℝ | p.1 ≤ A ∧ B ≤ p.2} := by
          rw [owenStandardizingGaussianLaw_eq_correlatedStandardGaussianLaw c]
    _ =
          verticalUpperStripMass
            (correlatedStandardGaussianLaw ((-c) / Real.sqrt (1 + c ^ 2))) A B := rfl

/--
For `rho^2 < 1`, the correlated standard-Gaussian law gives positive mass to
every nonempty open set.
-/
theorem correlatedStandardGaussianLaw_isOpenPosMeasure
    {rho : ℝ} (hrho : rho ^ 2 < 1) :
    Measure.IsOpenPosMeasure (correlatedStandardGaussianLaw rho) := by
  unfold correlatedStandardGaussianLaw
  exact
    (continuous_correlatedStandardGaussianMap rho).isOpenPosMeasure_map
      (correlatedStandardGaussianMap_surjective_of_rho_sq_lt_one hrho)

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

/-- The first-coordinate marginal of `correlatedStandardGaussianLaw rho` is standard normal. -/
theorem correlatedStandardGaussianLaw_map_fst (rho : ℝ) :
    (correlatedStandardGaussianLaw rho).map Prod.fst =
      standardGaussianMeasure := by
  rw [correlatedStandardGaussianLaw, Measure.map_map measurable_fst
    (measurable_correlatedStandardGaussianMap rho)]
  have hcomp :
      Prod.fst ∘ correlatedStandardGaussianMap rho =
        (fun p : ℝ × ℝ => p.1) := by
    funext p
    simp [correlatedStandardGaussianMap]
  rw [hcomp]
  rw [Measure.map_fst_prod]
  simp [standardGaussianMeasure]

/--
If `rho` is a valid correlation parameter, the second-coordinate marginal of
`correlatedStandardGaussianLaw rho` is also standard normal.
-/
theorem correlatedStandardGaussianLaw_map_snd {rho : ℝ} (hrho : rho ^ 2 ≤ 1) :
    (correlatedStandardGaussianLaw rho).map Prod.snd =
      standardGaussianMeasure := by
  let scale : ℝ := Real.sqrt (1 - rho ^ 2)
  let base : Measure (ℝ × ℝ) :=
    standardGaussianMeasure.prod standardGaussianMeasure
  let vRho : ℝ≥0 := ⟨rho ^ 2, sq_nonneg rho⟩
  let vScale : ℝ≥0 := ⟨scale ^ 2, sq_nonneg scale⟩
  have hscale_sq : scale ^ 2 = 1 - rho ^ 2 := by
    dsimp [scale]
    exact Real.sq_sqrt (sub_nonneg.mpr hrho)
  have hvar : vRho + vScale = (1 : ℝ≥0) := by
    ext
    change rho ^ 2 + scale ^ 2 = (1 : ℝ)
    rw [hscale_sq]
    linarith
  have hX :
      base.map (fun p : ℝ × ℝ => rho * p.1) =
        ProbabilityTheory.gaussianReal 0 vRho := by
    calc
      base.map (fun p : ℝ × ℝ => rho * p.1)
          = (base.map Prod.fst).map (fun u : ℝ => rho * u) := by
              rw [← Function.comp_def,
                ← Measure.map_map (measurable_const_mul rho) measurable_fst]
      _ = standardGaussianMeasure.map (fun u : ℝ => rho * u) := by
              rw [Measure.map_fst_prod]
              simp [standardGaussianMeasure]
      _ = ProbabilityTheory.gaussianReal 0 vRho := by
              simpa [standardGaussianMeasure, vRho] using
                (ProbabilityTheory.gaussianReal_map_const_mul
                  (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) rho)
  have hY :
      base.map (fun p : ℝ × ℝ => scale * p.2) =
        ProbabilityTheory.gaussianReal 0 vScale := by
    calc
      base.map (fun p : ℝ × ℝ => scale * p.2)
          = (base.map Prod.snd).map (fun u : ℝ => scale * u) := by
              rw [← Function.comp_def,
                ← Measure.map_map (measurable_const_mul scale) measurable_snd]
      _ = standardGaussianMeasure.map (fun u : ℝ => scale * u) := by
              rw [Measure.map_snd_prod]
              simp [standardGaussianMeasure]
      _ = ProbabilityTheory.gaussianReal 0 vScale := by
              simpa [standardGaussianMeasure, vScale] using
                (ProbabilityTheory.gaussianReal_map_const_mul
                  (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) scale)
  have hindep :
      IndepFun (fun p : ℝ × ℝ => rho * p.1)
        (fun p : ℝ × ℝ => scale * p.2) base := by
    dsimp [base]
    exact ProbabilityTheory.indepFun_prod
      (μ := standardGaussianMeasure) (ν := standardGaussianMeasure)
      (X := fun u : ℝ => rho * u) (Y := fun u : ℝ => scale * u)
      (by fun_prop) (by fun_prop)
  have hsum :
      base.map
          ((fun p : ℝ × ℝ => rho * p.1) +
            (fun p : ℝ × ℝ => scale * p.2)) =
        ProbabilityTheory.gaussianReal 0 1 := by
    have hraw :=
      ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
        (P := base)
        (X := fun p : ℝ × ℝ => rho * p.1)
        (Y := fun p : ℝ × ℝ => scale * p.2)
        (m₁ := (0 : ℝ)) (m₂ := (0 : ℝ))
        (v₁ := vRho) (v₂ := vScale)
        hindep hX hY
    simpa [hvar] using hraw
  rw [correlatedStandardGaussianLaw, Measure.map_map measurable_snd
    (measurable_correlatedStandardGaussianMap rho)]
  change
    base.map
        (Prod.snd ∘ correlatedStandardGaussianMap rho) =
      standardGaussianMeasure
  simpa [base, standardGaussianMeasure, correlatedStandardGaussianMap, scale]
    using hsum

/-- The first-coordinate marginal of the correlated standard-Gaussian law is nonatomic. -/
theorem correlatedStandardGaussianLaw_noAtoms_map_fst (rho : ℝ) :
    NoAtoms ((correlatedStandardGaussianLaw rho).map Prod.fst) := by
  rw [correlatedStandardGaussianLaw_map_fst rho]
  infer_instance

/-- The second-coordinate marginal of a nondegenerate correlated standard-Gaussian law is nonatomic. -/
theorem correlatedStandardGaussianLaw_noAtoms_map_snd
    {rho : ℝ} (hrho : rho ^ 2 ≤ 1) :
    NoAtoms ((correlatedStandardGaussianLaw rho).map Prod.snd) := by
  rw [correlatedStandardGaussianLaw_map_snd hrho]
  infer_instance

/--
Moving upper-orthant masses under a correlated standard-Gaussian law are
continuous along the diagonal once `rho` is a valid correlation parameter.
-/
theorem correlatedStandardGaussianLaw_upperOrthantMass_diagonal_continuous
    {rho : ℝ} (hrho : rho ^ 2 ≤ 1) (offset : ℝ) :
    Continuous fun q : ℝ =>
      EconCSLib.upperOrthantMass (correlatedStandardGaussianLaw rho)
        (q - offset) q := by
  letI : NoAtoms ((correlatedStandardGaussianLaw rho).map Prod.fst) :=
    correlatedStandardGaussianLaw_noAtoms_map_fst rho
  letI : NoAtoms ((correlatedStandardGaussianLaw rho).map Prod.snd) :=
    correlatedStandardGaussianLaw_noAtoms_map_snd hrho
  exact
    EconCSLib.upperOrthantMass_diagonal_continuous_of_noAtoms_marginals
      (correlatedStandardGaussianLaw rho) offset

/--
For every valid correlation parameter, the concrete bivariate Gaussian CDF is
continuous in its two threshold coordinates.
-/
theorem standardBivariateGaussianCDF_continuous_of_rho_sq_le_one
    {rho : ℝ} (hrho : rho ^ 2 ≤ 1) :
    Continuous fun p : ℝ × ℝ =>
      standardBivariateGaussianCDF p.1 p.2 rho := by
  letI : NoAtoms ((correlatedStandardGaussianLaw rho).map Prod.fst) :=
    correlatedStandardGaussianLaw_noAtoms_map_fst rho
  letI : NoAtoms ((correlatedStandardGaussianLaw rho).map Prod.snd) :=
    correlatedStandardGaussianLaw_noAtoms_map_snd hrho
  simpa [standardBivariateGaussianCDF] using
    EconCSLib.lowerLeftRectangleMass_continuous_of_noAtoms_marginals
      (correlatedStandardGaussianLaw rho)

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

/-- Nondegenerate correlated standard-Gaussian laws give positive mass to every vertical upper strip. -/
theorem correlatedStandardGaussianLaw_verticalUpperStripMass_pos
    {rho : ℝ} (hrho : rho ^ 2 < 1) (x y : ℝ) :
    0 < EconCSLib.verticalUpperStripMass
      (correlatedStandardGaussianLaw rho) x y := by
  letI : Measure.IsOpenPosMeasure (correlatedStandardGaussianLaw rho) :=
    correlatedStandardGaussianLaw_isOpenPosMeasure hrho
  exact
    EconCSLib.verticalUpperStripMass_pos_of_isOpenPosMeasure
      (correlatedStandardGaussianLaw rho) x y

/--
The correlated standard-Gaussian law assigns zero mass to every vertical
boundary clipped by a lower half-space.
-/
theorem correlatedStandardGaussianLaw_verticalBoundaryLeft_real_eq_zero
    (rho x y : ℝ) :
    (correlatedStandardGaussianLaw rho).real
        {p : ℝ × ℝ | p.1 = x ∧ p.2 ≤ y} = 0 := by
  have hline :
      correlatedStandardGaussianLaw rho
          {p : ℝ × ℝ | p.1 = x} = 0 := by
    calc
      correlatedStandardGaussianLaw rho {p : ℝ × ℝ | p.1 = x}
          =
            (correlatedStandardGaussianLaw rho).map Prod.fst
              ({x} : Set ℝ) := by
              rw [Measure.map_apply measurable_fst (measurableSet_singleton x)]
              rfl
      _ = standardGaussianMeasure ({x} : Set ℝ) := by
              rw [correlatedStandardGaussianLaw_map_fst rho]
      _ = 0 := by
              haveI : NoAtoms standardGaussianMeasure := by
                unfold standardGaussianMeasure
                exact ProbabilityTheory.noAtoms_gaussianReal
                  (by norm_num : (1 : ℝ≥0) ≠ 0)
              exact measure_singleton x
  have hclip :
      correlatedStandardGaussianLaw rho
          {p : ℝ × ℝ | p.1 = x ∧ p.2 ≤ y} = 0 := by
    exact measure_mono_null (by intro p hp; exact hp.1) hline
  simp [measureReal_def, hclip]

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
