import EconCSLib.Foundations.Math.FiniteSum
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace EconCSLib
namespace Probability

noncomputable section

/-!
# Real Distribution Tail Helpers

Thin wrappers around Mathlib's real CDF API.  These names are meant for
paper-facing threshold, tail, and order-statistic arguments where the proof
needs real-valued lower-CDF and upper-tail probabilities.

## Main declarations

- `lowerCDFMass`
- `upperTailMass`
- `lowerCDFMass_mono`
- `upperTailMass_antitone`
- `lowerCDFMass_eq_cdf`
- `upperTailMass_eq_one_sub_cdf`
- `intervalOCMass_eq_cdf_sub`
- `UpperTailThresholdCertificate`
- `CDFPowerTailSandwich`
-/

/-- Real-valued lower CDF mass, `P[X <= x]`. -/
def lowerCDFMass (μ : Measure ℝ) (x : ℝ) : ℝ :=
  μ.real (Iic x)

/-- Real-valued upper-tail mass, `P[X > x]`. -/
def upperTailMass (μ : Measure ℝ) (x : ℝ) : ℝ :=
  μ.real (Ioi x)

/--
Positive mean from nonnegative support and positive mass above a positive
threshold.
-/
theorem integral_id_pos_of_ae_nonneg_of_measure_Ici_pos
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h_nonneg : ∀ᵐ x ∂μ, 0 ≤ x)
    (h_int : Integrable (fun x : ℝ => x) μ)
    {a : ℝ} (ha_pos : 0 < a)
    (hmass : 0 < μ (Set.Ici a)) :
    0 < ∫ x, x ∂μ := by
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae h_nonneg h_int]
  exact lt_of_lt_of_le hmass (measure_mono (by
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le ha_pos hx)))

/--
Bounded-support version of
`integral_id_pos_of_ae_nonneg_of_measure_Ici_pos`, deriving integrability from
an a.e. interval bound.
-/
theorem integral_id_pos_of_ae_nonneg_of_measure_Ici_pos_of_ae_bounds
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {L M a : ℝ}
    (h_bounds : ∀ᵐ x ∂μ, L ≤ x ∧ x ≤ M)
    (h_nonneg : ∀ᵐ x ∂μ, 0 ≤ x)
    (ha_pos : 0 < a)
    (hmass : 0 < μ (Set.Ici a)) :
    0 < ∫ x, x ∂μ := by
  have h_int : Integrable (fun x : ℝ => x) μ := by
    exact Integrable.of_mem_Icc L M measurable_id.aemeasurable h_bounds
  exact integral_id_pos_of_ae_nonneg_of_measure_Ici_pos
    μ h_nonneg h_int ha_pos hmass

/--
Positive one-dimensional mass gives positive mass to the corresponding finite
product rectangle.
-/
theorem pi_univ_const_set_measure_pos
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] {s : Set α}
    (hs : MeasurableSet s) (hpos : 0 < μ s) :
    0 < (Measure.pi (fun _ : ι => μ))
      (Set.pi Set.univ (fun _ : ι => s)) := by
  rw [Measure.pi_pi]
  rw [CanonicallyOrderedAdd.prod_pos]
  intro i _hi
  exact hpos

theorem pi_univ_Iio_measure_pos
    {ι : Type*} [Fintype ι] (μ : Measure ℝ) [SigmaFinite μ] {b : ℝ}
    (hpos : 0 < μ (Set.Iio b)) :
    0 < (Measure.pi (fun _ : ι => μ))
      (Set.pi Set.univ (fun _ : ι => Set.Iio b)) :=
  pi_univ_const_set_measure_pos μ measurableSet_Iio hpos

theorem pi_univ_Ici_measure_pos
    {ι : Type*} [Fintype ι] (μ : Measure ℝ) [SigmaFinite μ] {a : ℝ}
    (hpos : 0 < μ (Set.Ici a)) :
    0 < (Measure.pi (fun _ : ι => μ))
      (Set.pi Set.univ (fun _ : ι => Set.Ici a)) :=
  pi_univ_const_set_measure_pos μ measurableSet_Ici hpos

/-- Real-valued reflected CDF mass, `P[M - X <= x]`. -/
def reflectedCDFMass (μ : Measure ℝ) (M x : ℝ) : ℝ :=
  μ.real {y : ℝ | M ≤ x + y}

theorem reflectedCDFMass_eq_sub_event
    (μ : Measure ℝ) (M x : ℝ) :
    reflectedCDFMass μ M x = μ.real {y : ℝ | M - y ≤ x} := by
  have hset : {y : ℝ | M ≤ x + y} = {y : ℝ | M - y ≤ x} := by
    ext y
    constructor
    · intro hy
      change M - y ≤ x
      change M ≤ x + y at hy
      linarith
    · intro hy
      change M ≤ x + y
      change M - y ≤ x at hy
      linarith
  simp [reflectedCDFMass, hset]

theorem lowerCDFMass_nonneg (μ : Measure ℝ) (x : ℝ) :
    0 ≤ lowerCDFMass μ x := by
  simp [lowerCDFMass]

theorem upperTailMass_nonneg (μ : Measure ℝ) (x : ℝ) :
    0 ≤ upperTailMass μ x := by
  simp [upperTailMass]

theorem reflectedCDFMass_nonneg (μ : Measure ℝ) (M x : ℝ) :
    0 ≤ reflectedCDFMass μ M x := by
  simp [reflectedCDFMass]

theorem lowerCDFMass_mono (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Monotone (lowerCDFMass μ) := by
  intro x y hxy
  exact measureReal_mono
    (μ := μ) (fun z hz => le_trans hz hxy) (measure_ne_top μ _)

theorem upperTailMass_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Antitone (upperTailMass μ) := by
  intro x y hxy
  exact measureReal_mono
    (μ := μ) (fun z hz => lt_of_le_of_lt hxy hz) (measure_ne_top μ _)

theorem reflectedCDFMass_mono (μ : Measure ℝ) [IsFiniteMeasure μ] (M : ℝ) :
    Monotone (reflectedCDFMass μ M) := by
  intro x y hxy
  exact measureReal_mono
    (μ := μ)
    (by
      intro z hz
      change M ≤ y + z
      change M ≤ x + z at hz
      linarith)
    (measure_ne_top μ _)

theorem reflectedCDFMass_measurable
    (μ : Measure ℝ) [IsFiniteMeasure μ] (M : ℝ) :
    Measurable (reflectedCDFMass μ M) :=
  (reflectedCDFMass_mono μ M).measurable

theorem lowerCDFMass_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) :
    lowerCDFMass μ x ≤ 1 := by
  have hle :
      μ.real (Iic x) ≤ μ.real (univ : Set ℝ) :=
    measureReal_mono (μ := μ) (subset_univ _) (measure_ne_top μ _)
  simpa [lowerCDFMass, probReal_univ] using hle

theorem upperTailMass_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) :
    upperTailMass μ x ≤ 1 := by
  have hle :
      μ.real (Ioi x) ≤ μ.real (univ : Set ℝ) :=
    measureReal_mono (μ := μ) (subset_univ _) (measure_ne_top μ _)
  simpa [upperTailMass, probReal_univ] using hle

theorem reflectedCDFMass_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M x : ℝ) :
    reflectedCDFMass μ M x ≤ 1 := by
  have hle :
      μ.real {y : ℝ | M ≤ x + y} ≤ μ.real (univ : Set ℝ) :=
    measureReal_mono (μ := μ) (subset_univ _) (measure_ne_top μ _)
  simpa [reflectedCDFMass, probReal_univ] using hle

theorem reflectedCDFMass_eq_one_of_ae_bounds
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {L M x : ℝ}
    (h_bounds : ∀ᵐ y ∂μ, L ≤ y ∧ y ≤ M)
    (hx : M - L ≤ x) :
    reflectedCDFMass μ M x = 1 := by
  have hset :
      {y : ℝ | M ≤ x + y} =ᵐ[μ] (univ : Set ℝ) := by
    filter_upwards [h_bounds] with y hy
    have hevent : M ≤ x + y := by linarith
    exact propext ⟨fun _hy_event => trivial, fun _hy_univ => hevent⟩
  calc
    reflectedCDFMass μ M x =
        μ.real (univ : Set ℝ) := by
          simpa [reflectedCDFMass] using measureReal_congr (μ := μ) hset
    _ = 1 := probReal_univ

/--
Near-zero CDF power-law sandwich.

This records the reusable source convention used by bounded-support
order-statistic arguments: near zero, a CDF-like mass `G` is sandwiched between
`(1 ± ε) * (c / beta) * x^beta` on a right-neighborhood of zero.
-/
structure CDFPowerTailSandwich
    (G : ℝ → ℝ) (beta c : ℝ) where
  beta_pos : 0 < beta
  c_pos : 0 < c
  cdf_power_sandwich :
    ∀ {ε : ℝ}, 0 < ε →
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        (1 - ε) * (c / beta) * x ^ beta ≤ G x ∧
          G x ≤ (1 + ε) * (c / beta) * x ^ beta

namespace CDFPowerTailSandwich

/--
Build the power-tail sandwich when the CDF-like function is eventually exactly
the limiting power law near zero.
-/
theorem of_eventually_eq_const_mul_power
    {G : ℝ → ℝ} {beta c : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hG :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        G x = (c / beta) * x ^ beta) :
    CDFPowerTailSandwich G beta c where
  beta_pos := hbeta_pos
  c_pos := hc_pos
  cdf_power_sandwich := by
    intro ε hε
    filter_upwards [hG, self_mem_nhdsWithin] with x hx_eq hx_pos
    have hcoeff_nonneg : 0 ≤ c / beta :=
      (div_pos hc_pos hbeta_pos).le
    have hxpow_nonneg : 0 ≤ x ^ beta :=
      Real.rpow_nonneg (le_of_lt hx_pos) beta
    have hmain_nonneg : 0 ≤ (c / beta) * x ^ beta :=
      mul_nonneg hcoeff_nonneg hxpow_nonneg
    have hleft : 1 - ε ≤ (1 : ℝ) := by linarith
    have hright : (1 : ℝ) ≤ 1 + ε := by linarith
    constructor
    · rw [hx_eq]
      calc
        (1 - ε) * (c / beta) * x ^ beta
            = (1 - ε) * ((c / beta) * x ^ beta) := by ring
        _ ≤ 1 * ((c / beta) * x ^ beta) :=
            mul_le_mul_of_nonneg_right hleft hmain_nonneg
        _ = (c / beta) * x ^ beta := by ring
    · rw [hx_eq]
      calc
        (c / beta) * x ^ beta
            = 1 * ((c / beta) * x ^ beta) := by ring
        _ ≤ (1 + ε) * ((c / beta) * x ^ beta) :=
            mul_le_mul_of_nonneg_right hright hmain_nonneg
        _ = (1 + ε) * (c / beta) * x ^ beta := by ring

/--
Build the reflected-CDF power-tail sandwich from a source-style upper-endpoint
tail mass sandwich.

The upper-tail event `M - x ≤ y` is the same as the reflected-CDF event
`M ≤ x + y`.
-/
theorem of_reflectedCDFMass_upper_endpoint_tail_sandwich
    {μ : Measure ℝ} {M beta c : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (htail :
      ∀ {ε : ℝ}, 0 < ε →
        ∀ᶠ x in 𝓝[>] (0 : ℝ),
          (1 - ε) * (c / beta) * x ^ beta ≤
              μ.real (Set.Ici (M - x)) ∧
            μ.real (Set.Ici (M - x)) ≤
              (1 + ε) * (c / beta) * x ^ beta) :
    CDFPowerTailSandwich (reflectedCDFMass μ M) beta c where
  beta_pos := hbeta_pos
  c_pos := hc_pos
  cdf_power_sandwich := by
    intro ε hε
    filter_upwards [htail hε] with x hx
    have hset : {y : ℝ | M ≤ x + y} = Set.Ici (M - x) := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_Ici]
      constructor <;> intro hy <;> linarith
    simpa [reflectedCDFMass, hset] using hx

/--
Build the reflected-CDF power-tail sandwich when the source law gives an
eventual exact upper-endpoint power identity near zero.
-/
theorem of_reflectedCDFMass_upper_endpoint_eventually_eq_power
    {μ : Measure ℝ} {M beta c : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (htail :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        μ.real (Set.Ici (M - x)) = (c / beta) * x ^ beta) :
    CDFPowerTailSandwich (reflectedCDFMass μ M) beta c := by
  refine of_eventually_eq_const_mul_power hbeta_pos hc_pos ?_
  filter_upwards [htail] with x hx
  have hset : {y : ℝ | M ≤ x + y} = Set.Ici (M - x) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    constructor <;> intro hy <;> linarith
  simpa [reflectedCDFMass, hset] using hx

/-- The identity CDF has the power-tail sandwich with `beta = c = 1`. -/
theorem identity_beta_one :
    CDFPowerTailSandwich (fun x : ℝ => x) 1 1 := by
  refine of_eventually_eq_const_mul_power (by norm_num) (by norm_num) ?_
  filter_upwards with x
  norm_num

/--
The asymptotic CDF sandwich supplies concrete local power bounds on a
right-neighborhood of zero.
-/
theorem exists_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : CDFPowerTailSandwich G beta c) :
    ∃ delta A B : ℝ,
      0 < delta ∧ 0 < A ∧ 0 ≤ B ∧
        (∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x) ∧
        (∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) := by
  let ε : ℝ := 1 / 2
  have hε : 0 < ε := by positivity
  let A : ℝ := (1 - ε) * (c / beta)
  let B : ℝ := (1 + ε) * (c / beta)
  have hA_pos : 0 < A := by
    have hcdiv_pos : 0 < c / beta := div_pos C.c_pos C.beta_pos
    dsimp [A, ε]
    positivity
  have hB_nonneg : 0 ≤ B := by
    have hcdiv_pos : 0 < c / beta := div_pos C.c_pos C.beta_pos
    dsimp [B, ε]
    positivity
  have hnear := C.cdf_power_sandwich hε
  rcases Metric.mem_nhdsWithin_iff.mp hnear with ⟨delta, hdelta_pos, hdelta⟩
  refine ⟨delta, A, B, hdelta_pos, hA_pos, hB_nonneg, ?_, ?_⟩
  · intro x hx_pos hx_lt
    have hx_ball : x ∈ Metric.ball (0 : ℝ) delta := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_of_nonneg hx_pos.le]
      exact hx_lt
    have hx_side : x ∈ Set.Ioi (0 : ℝ) := hx_pos
    have hx_prop := hdelta ⟨hx_ball, hx_side⟩
    simpa [A, mul_assoc] using hx_prop.1
  · intro x hx_pos hx_lt
    have hx_ball : x ∈ Metric.ball (0 : ℝ) delta := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_of_nonneg hx_pos.le]
      exact hx_lt
    have hx_side : x ∈ Set.Ioi (0 : ℝ) := hx_pos
    have hx_prop := hdelta ⟨hx_ball, hx_side⟩
    simpa [B, mul_assoc] using hx_prop.2

/--
A reflected-CDF power-tail law at a positive endpoint supplies positive source
mass above some positive threshold.
-/
theorem exists_positive_Ici_mass_of_reflectedCDFMass_tail
    {μ : Measure ℝ} {M beta c : ℝ}
    (C : CDFPowerTailSandwich (reflectedCDFMass μ M) beta c)
    (hM_pos : 0 < M) :
    ∃ a : ℝ, 0 < a ∧ 0 < μ (Set.Ici a) := by
  rcases C.exists_local_cdf_power_bounds with
    ⟨delta, A, _B, hdelta_pos, hA_pos, _hB_nonneg, hlower, _hupper⟩
  let x : ℝ := min delta M / 2
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hx_lt_delta : x < delta := by
    dsimp [x]
    have hmin_le : min delta M ≤ delta := min_le_left _ _
    nlinarith [hdelta_pos, hM_pos, hmin_le]
  have hx_lt_M : x < M := by
    dsimp [x]
    have hmin_le : min delta M ≤ M := min_le_right _ _
    nlinarith [hdelta_pos, hM_pos, hmin_le]
  have hxpow_pos : 0 < x ^ beta := Real.rpow_pos_of_pos hx_pos beta
  have hG_pos : 0 < reflectedCDFMass μ M x := by
    have hlower_x := hlower x hx_pos hx_lt_delta
    exact lt_of_lt_of_le (mul_pos hA_pos hxpow_pos) hlower_x
  have hset : {y : ℝ | M ≤ x + y} = Set.Ici (M - x) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    constructor <;> intro hy <;> linarith
  have hreal_pos : 0 < μ.real (Set.Ici (M - x)) := by
    simpa [reflectedCDFMass, hset] using hG_pos
  have hmass : 0 < μ (Set.Ici (M - x)) :=
    (ENNReal.toReal_pos_iff.mp hreal_pos).1
  exact ⟨M - x, by linarith, hmass⟩

theorem tendsto_zero
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : CDFPowerTailSandwich G beta c) :
    Tendsto G (𝓝[>] (0 : ℝ)) (nhds 0) := by
  refine tendsto_order.2 ?_
  constructor
  · intro a ha
    let ε : ℝ := 1 / 2
    have hε : 0 < ε := by positivity
    let A : ℝ := (1 - ε) * (c / beta)
    have hA_nonneg : 0 ≤ A := by
      have hcdiv_pos : 0 < c / beta := div_pos C.c_pos C.beta_pos
      dsimp [A, ε]
      positivity
    have hnear := C.cdf_power_sandwich hε
    filter_upwards [hnear, self_mem_nhdsWithin] with x hx hx_pos
    have hxpow_nonneg : 0 ≤ x ^ beta :=
      Real.rpow_nonneg (le_of_lt hx_pos) beta
    have hG_nonneg : 0 ≤ G x := by
      have hmain_nonneg : 0 ≤ A * x ^ beta :=
        mul_nonneg hA_nonneg hxpow_nonneg
      exact le_trans hmain_nonneg (by simpa [A, mul_assoc] using hx.1)
    linarith
  · intro b hb
    let ε : ℝ := 1 / 2
    have hε : 0 < ε := by positivity
    let B : ℝ := (1 + ε) * (c / beta)
    have hpow_zero :
        Tendsto (fun x : ℝ => B * x ^ beta)
          (𝓝[>] (0 : ℝ)) (nhds 0) := by
      have hxpow_zero :
          Tendsto (fun x : ℝ => x ^ beta)
            (𝓝[>] (0 : ℝ)) (nhds 0) := by
        have hcont :=
          (Real.continuousAt_rpow_const
            (0 : ℝ) beta (Or.inr C.beta_pos.le)).tendsto
        simpa [Real.zero_rpow C.beta_pos.ne'] using
          hcont.mono_left nhdsWithin_le_nhds
      simpa using hxpow_zero.const_mul B
    have hsmall :
        ∀ᶠ x in 𝓝[>] (0 : ℝ), B * x ^ beta < b :=
      hpow_zero.eventually (eventually_lt_nhds hb)
    have hnear := C.cdf_power_sandwich hε
    filter_upwards [hnear, hsmall] with x hx hxsmall
    exact lt_of_le_of_lt (by simpa [B, mul_assoc] using hx.2) hxsmall

/--
A reflected-CDF power-tail law at a positive endpoint supplies positive source
mass strictly below some point before the endpoint.

Together with `exists_positive_Ici_mass_of_reflectedCDFMass_tail`, this gives
the low/high positive-mass split used by finite-prefix top-`k` positivity
arguments.
-/
theorem exists_positive_Iio_mass_below_endpoint_of_reflectedCDFMass_tail
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {M beta c : ℝ}
    (C : CDFPowerTailSandwich (reflectedCDFMass μ M) beta c)
    (hM_pos : 0 < M) :
    ∃ b : ℝ, b < M ∧ 0 < μ (Set.Iio b) := by
  have hsmall :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        reflectedCDFMass μ M x < 1 :=
    C.tendsto_zero.eventually (eventually_lt_nhds zero_lt_one)
  rcases Metric.mem_nhdsWithin_iff.mp hsmall with
    ⟨delta, hdelta_pos, hdelta⟩
  let x : ℝ := min delta M / 2
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hx_lt_delta : x < delta := by
    dsimp [x]
    have hmin_le : min delta M ≤ delta := min_le_left _ _
    nlinarith [hdelta_pos, hM_pos, hmin_le]
  have hx_lt_M : x < M := by
    dsimp [x]
    have hmin_le : min delta M ≤ M := min_le_right _ _
    nlinarith [hdelta_pos, hM_pos, hmin_le]
  have hx_ball : x ∈ Metric.ball (0 : ℝ) delta := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero,
      Real.norm_of_nonneg hx_pos.le]
    exact hx_lt_delta
  have hG_lt_one : reflectedCDFMass μ M x < 1 :=
    hdelta ⟨hx_ball, hx_pos⟩
  let b : ℝ := M - x
  have hset : {y : ℝ | M ≤ x + y} = Set.Ici b := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    dsimp [b]
    constructor <;> intro hy <;> linarith
  have hIci_real_lt_one : μ.real (Set.Ici b) < 1 := by
    simpa [reflectedCDFMass, hset, b] using hG_lt_one
  have hcompl_real : μ.real (Set.Iio b) = 1 - μ.real (Set.Ici b) := by
    have hcompl :=
      probReal_compl_eq_one_sub (μ := μ) (s := Set.Ici b)
        measurableSet_Ici
    simpa [compl_Ici] using hcompl
  have hIio_real_pos : 0 < μ.real (Set.Iio b) := by
    rw [hcompl_real]
    linarith
  have hmass : 0 < μ (Set.Iio b) :=
    (ENNReal.toReal_pos_iff.mp hIio_real_pos).1
  exact ⟨b, by dsimp [b]; linarith, hmass⟩

/--
A reflected-CDF power-tail law at a positive endpoint supplies a strict
low/high positive-mass split: some low interval `(-∞, b)` and some high tail
`[a, ∞)` both have positive mass, with `0 < b < a`.
-/
theorem exists_positive_Iio_Ici_mass_gap_of_reflectedCDFMass_tail
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {M beta c : ℝ}
    (C : CDFPowerTailSandwich (reflectedCDFMass μ M) beta c)
    (hM_pos : 0 < M) :
    ∃ b a : ℝ, 0 < b ∧ b < a ∧ 0 < μ (Set.Iio b) ∧ 0 < μ (Set.Ici a) := by
  rcases C.exists_local_cdf_power_bounds with
    ⟨delta_bound, A, _B, hdelta_bound_pos, hA_pos, _hB_nonneg,
      hlower, _hupper⟩
  have hsmall :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        reflectedCDFMass μ M x < 1 :=
    C.tendsto_zero.eventually (eventually_lt_nhds zero_lt_one)
  rcases Metric.mem_nhdsWithin_iff.mp hsmall with
    ⟨delta_small, hdelta_small_pos, hdelta_small⟩
  let x : ℝ := min (min delta_small delta_bound) M / 2
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hx_lt_small : x < delta_small := by
    dsimp [x]
    have hmin_le : min (min delta_small delta_bound) M ≤ delta_small := by
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    nlinarith [hdelta_small_pos, hdelta_bound_pos, hM_pos, hmin_le]
  have hx_lt_bound : x < delta_bound := by
    dsimp [x]
    have hmin_le : min (min delta_small delta_bound) M ≤ delta_bound := by
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith [hdelta_small_pos, hdelta_bound_pos, hM_pos, hmin_le]
  have hx_lt_M : x < M := by
    dsimp [x]
    have hmin_le : min (min delta_small delta_bound) M ≤ M :=
      min_le_right _ _
    nlinarith [hdelta_small_pos, hdelta_bound_pos, hM_pos, hmin_le]
  have hx_half_pos : 0 < x / 2 := by positivity
  have hx_half_lt_bound : x / 2 < delta_bound := by linarith
  have hx_ball : x ∈ Metric.ball (0 : ℝ) delta_small := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero,
      Real.norm_of_nonneg hx_pos.le]
    exact hx_lt_small
  have hGx_lt_one : reflectedCDFMass μ M x < 1 :=
    hdelta_small ⟨hx_ball, hx_pos⟩
  let b : ℝ := M - x
  have hset_low : {y : ℝ | M ≤ x + y} = Set.Ici b := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    dsimp [b]
    constructor <;> intro hy <;> linarith
  have hIci_b_real_lt_one : μ.real (Set.Ici b) < 1 := by
    simpa [reflectedCDFMass, hset_low, b] using hGx_lt_one
  have hcompl_real : μ.real (Set.Iio b) = 1 - μ.real (Set.Ici b) := by
    have hcompl :=
      probReal_compl_eq_one_sub (μ := μ) (s := Set.Ici b)
        measurableSet_Ici
    simpa [compl_Ici] using hcompl
  have hIio_b_real_pos : 0 < μ.real (Set.Iio b) := by
    rw [hcompl_real]
    linarith
  have hlow_mass : 0 < μ (Set.Iio b) :=
    (ENNReal.toReal_pos_iff.mp hIio_b_real_pos).1
  let a : ℝ := M - x / 2
  have hset_high : {y : ℝ | M ≤ (x / 2) + y} = Set.Ici a := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    dsimp [a]
    constructor <;> intro hy <;> linarith
  have hG_half_pos : 0 < reflectedCDFMass μ M (x / 2) := by
    have hlower_half := hlower (x / 2) hx_half_pos hx_half_lt_bound
    have hxpow_pos : 0 < (x / 2) ^ beta :=
      Real.rpow_pos_of_pos hx_half_pos beta
    exact lt_of_lt_of_le (mul_pos hA_pos hxpow_pos) hlower_half
  have hIci_a_real_pos : 0 < μ.real (Set.Ici a) := by
    simpa [reflectedCDFMass, hset_high, a] using hG_half_pos
  have hhigh_mass : 0 < μ (Set.Ici a) :=
    (ENNReal.toReal_pos_iff.mp hIci_a_real_pos).1
  refine ⟨b, a, ?_, ?_, hlow_mass, hhigh_mass⟩
  · dsimp [b]
    linarith
  · dsimp [a, b]
    linarith

end CDFPowerTailSandwich

theorem lowerCDFMass_eq_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) :
    lowerCDFMass μ x = ProbabilityTheory.cdf μ x := by
  simpa [lowerCDFMass] using (ProbabilityTheory.cdf_eq_real μ x).symm

theorem upperTailMass_eq_one_sub_cdf
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    upperTailMass μ x = 1 - ProbabilityTheory.cdf μ x := by
  have hcompl :=
    probReal_compl_eq_one_sub (μ := μ) (s := Iic x) measurableSet_Iic
  simpa [upperTailMass, ProbabilityTheory.cdf_eq_real μ x, compl_Iic] using hcompl

theorem lowerCDFMass_add_upperTailMass_eq_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    lowerCDFMass μ x + upperTailMass μ x = 1 := by
  rw [lowerCDFMass_eq_cdf, upperTailMass_eq_one_sub_cdf]
  ring

/-- Real-valued mass of `(a, b]`. -/
def intervalOCMass (μ : Measure ℝ) (a b : ℝ) : ℝ :=
  μ.real (Ioc a b)

theorem intervalOCMass_nonneg (μ : Measure ℝ) (a b : ℝ) :
    0 ≤ intervalOCMass μ a b := by
  simp [intervalOCMass]

/-- Additivity of adjacent right-closed intervals for finite real measures. -/
theorem intervalOCMass_add_intervalOCMass_eq
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a c b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) :
    intervalOCMass μ a c + intervalOCMass μ c b =
      intervalOCMass μ a b := by
  have hdisj : Disjoint (Ioc a c) (Ioc c b) := by
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    exact (not_lt_of_ge hx₁.2) hx₂.1
  have hunion : Ioc a c ∪ Ioc c b = Ioc a b := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, hx.2.trans hcb⟩
      · exact ⟨lt_of_le_of_lt hac hx.1, hx.2⟩
    · intro hx
      by_cases hxc : x ≤ c
      · exact Or.inl ⟨hx.1, hxc⟩
      · exact Or.inr ⟨lt_of_not_ge hxc, hx.2⟩
  calc
    intervalOCMass μ a c + intervalOCMass μ c b =
        μ.real (Ioc a c ∪ Ioc c b) := by
      rw [measureReal_union hdisj measurableSet_Ioc]
      rfl
    _ = intervalOCMass μ a b := by
      rw [hunion]
      rfl

/--
For a real probability measure, the mass of `(a, b]` is the difference of the
CDF values, when `a ≤ b`.
-/
theorem intervalOCMass_eq_cdf_sub
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℝ} (hab : a ≤ b) :
    intervalOCMass μ a b =
      ProbabilityTheory.cdf μ b - ProbabilityTheory.cdf μ a := by
  have hmeasure :
      μ (Ioc a b) =
        ENNReal.ofReal (ProbabilityTheory.cdf μ b - ProbabilityTheory.cdf μ a) := by
    simpa [ProbabilityTheory.measure_cdf μ] using
      (ProbabilityTheory.cdf μ).measure_Ioc a b
  have hnonneg :
      0 ≤ ProbabilityTheory.cdf μ b - ProbabilityTheory.cdf μ a := by
    have hmono := ProbabilityTheory.monotone_cdf μ hab
    linarith
  simp [intervalOCMass, Measure.real, hmeasure, ENNReal.toReal_ofReal hnonneg]

/--
The mass of `(a, b]` tends to zero as `b` approaches `a` from the right.
This is the local-continuity fact used by moving-cut partition arguments.
-/
theorem tendsto_intervalOCMass_right
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) :
    Tendsto (fun b => intervalOCMass μ a b) (𝓝[≥] a) (𝓝 0) := by
  have hcdf :
      Tendsto (fun b => ProbabilityTheory.cdf μ b) (𝓝[≥] a)
        (𝓝 (ProbabilityTheory.cdf μ a)) :=
    (ProbabilityTheory.cdf μ).right_continuous a
  have hsub :
      Tendsto
        (fun b => ProbabilityTheory.cdf μ b - ProbabilityTheory.cdf μ a)
        (𝓝[≥] a) (𝓝 0) := by
    simpa using
      (hcdf.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => ProbabilityTheory.cdf μ a) (𝓝[≥] a)
          (𝓝 (ProbabilityTheory.cdf μ a))))
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with b hb
  exact (intervalOCMass_eq_cdf_sub μ hb).symm

/-- There is a nontrivial right interval of arbitrarily small probability mass. -/
theorem exists_right_intervalOCMass_lt
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ b : ℝ, a < b ∧ intervalOCMass μ a b < ε := by
  have htend :
      Tendsto (fun b => intervalOCMass μ a b) (𝓝[>] a) (𝓝 0) :=
    (tendsto_intervalOCMass_right μ a).mono_left
      (nhdsWithin_mono a Ioi_subset_Ici_self)
  have hevent : ∀ᶠ b in 𝓝[>] a, intervalOCMass μ a b < ε :=
    htend.eventually (eventually_lt_nhds hε)
  rcases (hevent.and self_mem_nhdsWithin).exists with ⟨b, hbmass, hba⟩
  exact ⟨b, hba, hbmass⟩

/--
Finite-measure version of right-continuity for interval masses.  This avoids
renormalizing aggregate measures into probability measures in cake-cutting
partition arguments.
-/
theorem tendsto_intervalOCMass_right_finite
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) :
    Tendsto (fun b => intervalOCMass μ a b) (𝓝[>] a) (𝓝 0) := by
  have h_inter_empty : (⋂ r > a, Ioc a r) = (∅ : Set ℝ) := by
    ext x
    constructor
    · intro hx
      have hx_all : ∀ r, a < r → x ∈ Ioc a r := by
        simpa using hx
      have hax : a < x := (hx_all (a + 1) (by linarith)).1
      let r : ℝ := (a + x) / 2
      have har : a < r := by
        dsimp [r]
        linarith
      have hxr : x ≤ r := (hx_all r har).2
      dsimp [r] at hxr
      linarith
    · intro hx
      simp at hx
  have hmeasure :
      Tendsto (fun b => μ (Ioc a b)) (𝓝[>] a) (𝓝 0) := by
    have h :=
      tendsto_measure_biInter_gt
        (μ := μ) (a := a) (s := fun b : ℝ => Ioc a b)
        (by
          intro r hr
          exact measurableSet_Ioc.nullMeasurableSet)
        (by
          intro i j _ hij x hx
          exact ⟨hx.1, hx.2.trans hij⟩)
        (by
          refine ⟨a + 1, by linarith, ?_⟩
          exact measure_ne_top μ (Ioc a (a + 1)))
    simpa [h_inter_empty] using h
  have hreal :
      Tendsto (fun b => (μ (Ioc a b)).toReal) (𝓝[>] a) (𝓝 0) :=
    (ENNReal.tendsto_toReal (by simp)).comp hmeasure
  simpa [intervalOCMass, Measure.real] using hreal

/-- There is a nontrivial right interval of arbitrarily small finite-measure mass. -/
theorem exists_right_intervalOCMass_lt_finite
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ b : ℝ, a < b ∧ intervalOCMass μ a b < ε := by
  have htend :
      Tendsto (fun b => intervalOCMass μ a b) (𝓝[>] a) (𝓝 0) :=
    tendsto_intervalOCMass_right_finite μ a
  have hevent : ∀ᶠ b in 𝓝[>] a, intervalOCMass μ a b < ε :=
    htend.eventually (eventually_lt_nhds hε)
  rcases (hevent.and self_mem_nhdsWithin).exists with ⟨b, hbmass, hba⟩
  exact ⟨b, hba, hbmass⟩

/--
If all left-truncated intervals `(a, y]` with `y < c` have real mass at most
`M`, then the open interval `(a, c)` has mass at most `M`.  The proof takes the
union over rational endpoints below `c`, avoiding a separate left-continuity
API for finite measures.
-/
theorem measureReal_Ioo_le_of_forall_intervalOCMass_le
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a c M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ y : ℝ, y < c → intervalOCMass μ a y ≤ M) :
    μ.real (Ioo a c) ≤ M := by
  let Qc := {q : ℚ // (q : ℝ) < c}
  have hUnion : (⋃ q : Qc, Ioc a (q : ℝ)) = Ioo a c := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨q, hxq⟩
      exact ⟨hxq.1, hxq.2.trans_lt q.2⟩
    · intro hx
      rcases exists_rat_btwn hx.2 with ⟨q, hxq, hqc⟩
      exact Set.mem_iUnion.mpr ⟨⟨q, hqc⟩, ⟨hx.1, le_of_lt hxq⟩⟩
  have hdir : Directed (· ⊆ ·) (fun q : Qc => Ioc a (q : ℝ)) := by
    intro q r
    refine ⟨⟨max q.1 r.1, ?_⟩, ?_, ?_⟩
    · exact_mod_cast max_lt q.2 r.2
    · intro x hx
      exact ⟨hx.1, hx.2.trans (by exact_mod_cast le_max_left q.1 r.1)⟩
    · intro x hx
      exact ⟨hx.1, hx.2.trans (by exact_mod_cast le_max_right q.1 r.1)⟩
  have hmeasure :
      μ (Ioo a c) = ⨆ q : Qc, μ (Ioc a (q : ℝ)) := by
    rw [← hUnion]
    exact hdir.measure_iUnion
  have hmeasure_le : μ (Ioo a c) ≤ ENNReal.ofReal M := by
    rw [hmeasure]
    refine iSup_le ?_
    intro q
    exact
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ (Ioc a (q : ℝ))) hM).2
        (by simpa [intervalOCMass, Measure.real] using hbound (q : ℝ) q.2)
  exact
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ (Ioo a c)) hM).1
      hmeasure_le

/--
First-crossing cut lemma for a finite real measure.  If the interval `(a, b]`
has mass above `α` and every point mass is at most `α / 2`, then some initial
subinterval `(a, c]` has mass strictly above `α / 2` but at most `α`.

This is the local moving-knife step used for finite termination: each
non-final cut removes more than `α / 2` mass while preserving the desired
one-piece `α` bound.
-/
theorem exists_intervalOCMass_gt_half_le_of_gt
    (μ : Measure ℝ) [IsFiniteMeasure μ] {a b α : ℝ}
    (hα : 0 < α)
    (hsingleton : ∀ x : ℝ, μ.real ({x} : Set ℝ) ≤ α / 2)
    (hbig : α < intervalOCMass μ a b) :
    ∃ c : ℝ,
      a ≤ c ∧ c ≤ b ∧
        α / 2 < intervalOCMass μ a c ∧ intervalOCMass μ a c ≤ α := by
  classical
  let T : Set ℝ := {x | a ≤ x ∧ x ≤ b ∧ α / 2 < intervalOCMass μ a x}
  have hhalf_nonneg : 0 ≤ α / 2 := by linarith
  have hhalf_lt : α / 2 < α := by linarith
  have hab : a ≤ b := by
    by_contra h
    have hba : b < a := lt_of_not_ge h
    have hempty : Ioc a b = (∅ : Set ℝ) := by
      ext x
      constructor
      · intro hx
        exact False.elim (by linarith [hx.1, hx.2, hba])
      · intro hx
        simp at hx
    have hzero : intervalOCMass μ a b = 0 := by
      simp [intervalOCMass, hempty]
    linarith
  have hb_mem : b ∈ T := by
    exact ⟨hab, le_rfl, hhalf_lt.trans hbig⟩
  have hT_nonempty : T.Nonempty := ⟨b, hb_mem⟩
  have hT_bddBelow : BddBelow T := ⟨a, by intro x hx; exact hx.1⟩
  let c₀ : ℝ := sInf T
  have ha_c₀ : a ≤ c₀ := by
    exact le_csInf hT_nonempty (by intro x hx; exact hx.1)
  have hc₀_b : c₀ ≤ b := by
    exact csInf_le hT_bddBelow hb_mem
  have hleft_bound :
      μ.real (Ioo a c₀) ≤ α / 2 := by
    refine measureReal_Ioo_le_of_forall_intervalOCMass_le μ hhalf_nonneg ?_
    intro y hyc
    by_cases hay : a ≤ y
    · have hyb : y ≤ b := le_trans (le_of_lt hyc) hc₀_b
      have hy_not_mem : y ∉ T := notMem_of_lt_csInf hyc hT_bddBelow
      have hnot : ¬ α / 2 < intervalOCMass μ a y := by
        intro hyhalf
        exact hy_not_mem ⟨hay, hyb, hyhalf⟩
      exact le_of_not_gt hnot
    · have hempty : Ioc a y = (∅ : Set ℝ) := by
        ext z
        constructor
        · intro hz
          exact False.elim (hay (le_trans (le_of_lt hz.1) hz.2))
        · intro hz
          simp at hz
      have hzero : intervalOCMass μ a y = 0 := by
        simp [intervalOCMass, hempty]
      linarith
  have hpiece_c₀_le : intervalOCMass μ a c₀ ≤ α := by
    have hsubset : Ioc a c₀ ⊆ Ioo a c₀ ∪ ({c₀} : Set ℝ) := by
      intro x hx
      by_cases hxc : x = c₀
      · exact Or.inr (by simp [hxc])
      · exact Or.inl ⟨hx.1, lt_of_le_of_ne hx.2 hxc⟩
    calc
      intervalOCMass μ a c₀ = μ.real (Ioc a c₀) := rfl
      _ ≤ μ.real (Ioo a c₀ ∪ ({c₀} : Set ℝ)) :=
        measureReal_mono hsubset (measure_ne_top μ _)
      _ ≤ μ.real (Ioo a c₀) + μ.real ({c₀} : Set ℝ) :=
        measureReal_union_le _ _
      _ ≤ α / 2 + α / 2 := add_le_add hleft_bound (hsingleton c₀)
      _ = α := by ring
  by_cases hcross : α / 2 < intervalOCMass μ a c₀
  · exact ⟨c₀, ha_c₀, hc₀_b, hcross, hpiece_c₀_le⟩
  · have hc₀_mass_le : intervalOCMass μ a c₀ ≤ α / 2 := le_of_not_gt hcross
    have hgap_pos : 0 < α - intervalOCMass μ a c₀ := by
      have hle_alpha : intervalOCMass μ a c₀ < α := lt_of_le_of_lt hc₀_mass_le hhalf_lt
      linarith
    rcases exists_right_intervalOCMass_lt_finite μ c₀ hgap_pos with
      ⟨u, hc₀u, hu_mass⟩
    rcases (csInf_lt_iff hT_bddBelow hT_nonempty).1 hc₀u with ⟨d, hdT, hdu⟩
    have hc₀d : c₀ ≤ d := csInf_le hT_bddBelow hdT
    have hdu_le : d ≤ u := le_of_lt hdu
    have hsubset : Ioc a d ⊆ Ioc a c₀ ∪ Ioc c₀ u := by
      intro x hx
      by_cases hxc : x ≤ c₀
      · exact Or.inl ⟨hx.1, hxc⟩
      · exact Or.inr ⟨lt_of_not_ge hxc, hx.2.trans hdu_le⟩
    have hd_lt_alpha : intervalOCMass μ a d < α := by
      calc
        intervalOCMass μ a d = μ.real (Ioc a d) := rfl
        _ ≤ μ.real (Ioc a c₀ ∪ Ioc c₀ u) :=
          measureReal_mono hsubset (measure_ne_top μ _)
        _ ≤ μ.real (Ioc a c₀) + μ.real (Ioc c₀ u) :=
          measureReal_union_le _ _
        _ < intervalOCMass μ a c₀ + (α - intervalOCMass μ a c₀) :=
          add_lt_add_of_le_of_lt le_rfl (by simpa [intervalOCMass] using hu_mass)
        _ = α := by ring
    exact ⟨d, hdT.1, hdT.2.1, hdT.2.2, le_of_lt hd_lt_alpha⟩

/--
Certificate that a real threshold realizes a target upper-tail mass/capacity.
-/
structure UpperTailThresholdCertificate
    (μ : Measure ℝ) (capacity threshold : ℝ) : Prop where
  tail_eq_capacity : upperTailMass μ threshold = capacity

namespace UpperTailThresholdCertificate

variable {μ : Measure ℝ} {capacity threshold : ℝ}

theorem capacity_nonneg
    (C : UpperTailThresholdCertificate μ capacity threshold) :
    0 ≤ capacity := by
  rw [← C.tail_eq_capacity]
  exact upperTailMass_nonneg μ threshold

theorem capacity_le_one [IsProbabilityMeasure μ]
    (C : UpperTailThresholdCertificate μ capacity threshold) :
    capacity ≤ 1 := by
  rw [← C.tail_eq_capacity]
  exact upperTailMass_le_one μ threshold

theorem lowerCDFMass_eq_one_sub_capacity [IsProbabilityMeasure μ]
    (C : UpperTailThresholdCertificate μ capacity threshold) :
    lowerCDFMass μ threshold = 1 - capacity := by
  have hsum := lowerCDFMass_add_upperTailMass_eq_one μ threshold
  rw [C.tail_eq_capacity] at hsum
  linarith

theorem capacity_antitone_threshold [IsFiniteMeasure μ]
    {capacity₁ capacity₂ threshold₁ threshold₂ : ℝ}
    (C₁ : UpperTailThresholdCertificate μ capacity₁ threshold₁)
    (C₂ : UpperTailThresholdCertificate μ capacity₂ threshold₂)
    (hthreshold : threshold₁ ≤ threshold₂) :
    capacity₂ ≤ capacity₁ := by
  rw [← C₁.tail_eq_capacity, ← C₂.tail_eq_capacity]
  exact upperTailMass_antitone μ hthreshold

end UpperTailThresholdCertificate

/-- Product of a two-valued coordinate weight over a finite type. -/
theorem prod_ite_mem_eq_pow_mul_pow {ι : Type*}
    [Fintype ι] [DecidableEq ι] (s : Finset ι) (q rho : ℝ) :
    (∏ i : ι, if i ∈ s then q else rho) =
      q ^ s.card * rho ^ (Fintype.card ι - s.card) := by
  exact EconCSLib.FiniteSum.prod_ite_mem_eq_pow_mul_pow s q rho

/-! ## Finite iid threshold counts -/

theorem productMeasure_forall_bounds_ae
    {ι : Type*} [Fintype ι] (μ : Measure ℝ) {L M : ℝ}
    [SigmaFinite μ]
    (h_bounds : ∀ᵐ x ∂μ, L ≤ x ∧ x ≤ M) :
    ∀ᵐ sample ∂Measure.pi (fun _ : ι => μ),
      ∀ i : ι, L ≤ sample i ∧ sample i ≤ M := by
  have hlower :
      ∀ i : ι, (fun _ : ℝ => L) ≤ᵐ[μ] (fun x : ℝ => x) := by
    intro _i
    filter_upwards [h_bounds] with x hx
    exact hx.1
  have hupper :
      ∀ i : ι, (fun x : ℝ => x) ≤ᵐ[μ] (fun _ : ℝ => M) := by
    intro _i
    filter_upwards [h_bounds] with x hx
    exact hx.2
  have hlower_pi :
      (fun sample : ι → ℝ => fun _ : ι => L) ≤ᵐ[
        Measure.pi (fun _ : ι => μ)] fun sample => sample :=
    Measure.ae_le_pi (μ := fun _ : ι => μ) hlower
  have hupper_pi :
      (fun sample : ι → ℝ => sample) ≤ᵐ[
        Measure.pi (fun _ : ι => μ)] fun _sample => fun _ : ι => M :=
    Measure.ae_le_pi (μ := fun _ : ι => μ) hupper
  filter_upwards [hlower_pi, hupper_pi] with sample hsample_lower hsample_upper i
  exact ⟨hsample_lower i, hsample_upper i⟩

theorem iidProductMeasure_forall_bounds_ae
    {n : ℕ} (μ : Measure ℝ) {L M : ℝ}
    [SigmaFinite μ]
    (h_bounds : ∀ᵐ x ∂μ, L ≤ x ∧ x ≤ M) :
    ∀ᵐ sample ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ M :=
  productMeasure_forall_bounds_ae (ι := Fin n) μ h_bounds

/-- Coordinates whose sample value falls in a designated measurable event. -/
noncomputable def iidSuccessIndexSet {α : Type*} {n : ℕ}
    (s : Set α) (sample : Fin n → α) : Finset (Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin n)).filter (fun i => sample i ∈ s)

theorem mem_iidSuccessIndexSet {α : Type*} {n : ℕ}
    (s : Set α) (sample : Fin n → α) (i : Fin n) :
    i ∈ iidSuccessIndexSet s sample ↔ sample i ∈ s := by
  classical
  simp [iidSuccessIndexSet]

/-- Number of iid coordinates whose sample value falls in a designated event. -/
noncomputable def iidSuccessCount {α : Type*} {n : ℕ}
    (s : Set α) (sample : Fin n → α) : ℕ :=
  (iidSuccessIndexSet s sample).card

/-- The fixed-success-index event is a product cylinder. -/
theorem iidSuccessIndexSet_eq_pi {α : Type*} {n : ℕ}
    (s : Set α) (active : Finset (Fin n)) :
    {sample : Fin n → α | iidSuccessIndexSet s sample = active} =
      Set.pi Set.univ
        (fun i : Fin n => if i ∈ active then s else sᶜ) := by
  classical
  ext sample
  constructor
  · intro hsample i _hi
    have hsample_eq : iidSuccessIndexSet s sample = active := hsample
    by_cases hi : i ∈ active
    · have hmem : i ∈ iidSuccessIndexSet s sample := by
        rw [hsample_eq]
        exact hi
      exact by
        simpa [hi] using (mem_iidSuccessIndexSet s sample i).1 hmem
    · have hnot : sample i ∉ s := by
        intro hs
        have hmem : i ∈ iidSuccessIndexSet s sample :=
          (mem_iidSuccessIndexSet s sample i).2 hs
        exact hi (by
          rw [← hsample_eq]
          exact hmem)
      simpa [hi] using hnot
  · intro hpi
    ext i
    by_cases hi : i ∈ active
    · have hmem := hpi i trivial
      simpa [mem_iidSuccessIndexSet, hi] using hmem
    · have hmem := hpi i trivial
      simpa [mem_iidSuccessIndexSet, hi] using hmem

theorem iidSuccessIndexSet_measurableSet {α : Type*} [MeasurableSpace α]
    {n : ℕ} {s : Set α} (hs : MeasurableSet s) (active : Finset (Fin n)) :
    MeasurableSet
      {sample : Fin n → α | iidSuccessIndexSet s sample = active} := by
  rw [iidSuccessIndexSet_eq_pi s active]
  refine MeasurableSet.pi Set.countable_univ ?_
  intro i _hi
  by_cases hactive : i ∈ active <;> simp [hactive, hs, hs.compl]

theorem iidSuccessCount_eq_measurableSet {α : Type*} [MeasurableSpace α]
    {n : ℕ} {s : Set α} (hs : MeasurableSet s) (j : ℕ) :
    MeasurableSet
      {sample : Fin n → α | iidSuccessCount s sample = j} := by
  classical
  let exactSets : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard j
  have hcard_set :
      {sample : Fin n → α | iidSuccessCount s sample = j} =
        ⋃ active ∈ exactSets,
          {sample : Fin n → α | iidSuccessIndexSet s sample = active} := by
    ext sample
    constructor
    · intro hcard
      refine Set.mem_iUnion.2 ⟨iidSuccessIndexSet s sample, ?_⟩
      refine Set.mem_iUnion.2 ⟨?_, rfl⟩
      exact Finset.mem_powersetCard.mpr
        ⟨by intro i _hi; simp, by simpa [iidSuccessCount] using hcard⟩
    · intro hmem
      rcases Set.mem_iUnion.mp hmem with ⟨active, hactive_mem⟩
      rcases Set.mem_iUnion.mp hactive_mem with ⟨hactive_exact, hactive_eq⟩
      have hactive_card : active.card = j :=
        (Finset.mem_powersetCard.mp hactive_exact).2
      change (iidSuccessIndexSet s sample).card = j
      rw [hactive_eq, hactive_card]
  rw [hcard_set]
  exact Finset.measurableSet_biUnion exactSets
    (fun active _hactive => iidSuccessIndexSet_measurableSet hs active)

theorem iidSuccessCount_le_measurableSet {α : Type*} [MeasurableSpace α]
    {n : ℕ} {s : Set α} (hs : MeasurableSet s) (r : ℕ) :
    MeasurableSet
      {sample : Fin n → α | iidSuccessCount s sample ≤ r} := by
  classical
  let exactCounts : Finset ℕ := Finset.Icc 0 (min r n)
  have hle_set :
      {sample : Fin n → α | iidSuccessCount s sample ≤ r} =
        ⋃ j ∈ exactCounts,
          {sample : Fin n → α | iidSuccessCount s sample = j} := by
    ext sample
    constructor
    · intro hle
      have hcount_le_n : iidSuccessCount s sample ≤ n := by
        simpa [iidSuccessCount, Finset.card_univ] using
          (iidSuccessIndexSet s sample).card_le_univ
      refine Set.mem_iUnion.2 ⟨iidSuccessCount s sample, ?_⟩
      refine Set.mem_iUnion.2 ⟨?_, rfl⟩
      exact Finset.mem_Icc.mpr
        ⟨Nat.zero_le _, le_min hle hcount_le_n⟩
    · intro hmem
      rcases Set.mem_iUnion.mp hmem with ⟨j, hj_mem⟩
      rcases Set.mem_iUnion.mp hj_mem with ⟨hj_exact, hj_eq⟩
      have hj_le_r : j ≤ r :=
        le_trans (Finset.mem_Icc.mp hj_exact).2 (min_le_left r n)
      have hj_eq' : iidSuccessCount s sample = j := hj_eq
      exact by
        change iidSuccessCount s sample ≤ r
        rw [hj_eq']
        exact hj_le_r
  rw [hle_set]
  exact Finset.measurableSet_biUnion exactCounts
    (fun j _hj => iidSuccessCount_eq_measurableSet hs j)

theorem iidSuccessCount_measurable {α : Type*} [MeasurableSpace α]
    {n : ℕ} {s : Set α} (hs : MeasurableSet s) :
    Measurable (fun sample : Fin n → α => iidSuccessCount s sample) := by
  refine measurable_to_countable' ?_
  intro j
  simpa [Set.preimage, Set.mem_setOf_eq, Set.mem_singleton_iff] using
    iidSuccessCount_eq_measurableSet (n := n) hs j

/--
For iid product samples, the real probability of a fixed success-index set
factors into success and failure masses.
-/
theorem iidProductMeasure_successIndexSet_eq_real
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {n : ℕ} {s : Set α} (hs : MeasurableSet s)
    (active : Finset (Fin n)) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {sample : Fin n → α | iidSuccessIndexSet s sample = active} =
      (μ.real s) ^ active.card *
        (1 - μ.real s) ^ (n - active.card) := by
  classical
  have hset :
      {sample : Fin n → α | iidSuccessIndexSet s sample = active} =
        Set.pi Set.univ
          (fun i : Fin n => if i ∈ active then s else sᶜ) :=
    iidSuccessIndexSet_eq_pi s active
  have hmeasure :
      (Measure.pi (fun _ : Fin n => μ))
          {sample : Fin n → α | iidSuccessIndexSet s sample = active} =
        ∏ i : Fin n, μ (if i ∈ active then s else sᶜ) := by
    rw [hset, Measure.pi_pi]
  have hcompl : μ.real sᶜ = 1 - μ.real s :=
    probReal_compl_eq_one_sub (μ := μ) hs
  rw [Measure.real, hmeasure, ENNReal.toReal_prod]
  calc
    ∏ i : Fin n, (μ (if i ∈ active then s else sᶜ)).toReal =
      ∏ i : Fin n, if i ∈ active then μ.real s else 1 - μ.real s := by
        refine Finset.prod_congr rfl ?_
        intro i _hi
        by_cases hactive : i ∈ active
        · simp [hactive, Measure.real]
        · simp [hactive]
          simpa [Measure.real] using hcompl
    _ =
      (μ.real s) ^ active.card *
        (1 - μ.real s) ^ (n - active.card) := by
        simpa [Fintype.card_fin] using
          prod_ite_mem_eq_pow_mul_pow
            (s := active) (q := μ.real s) (rho := 1 - μ.real s)

/--
For iid product samples, the real probability that exactly `j` coordinates
fall in `s` is the corresponding binomial mass.
-/
theorem iidProductMeasure_successCount_eq_real
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {n : ℕ} {s : Set α} (hs : MeasurableSet s) (j : ℕ) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {sample : Fin n → α | iidSuccessCount s sample = j} =
      (Nat.choose n j : ℝ) *
        (μ.real s) ^ j * (1 - μ.real s) ^ (n - j) := by
  classical
  let productMeasure : Measure (Fin n → α) :=
    Measure.pi (fun _ : Fin n => μ)
  haveI : IsProbabilityMeasure productMeasure := by
    dsimp [productMeasure]
    infer_instance
  let exactSets : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powersetCard j
  have hcard_set :
      {sample : Fin n → α | iidSuccessCount s sample = j} =
        ⋃ active ∈ exactSets,
          {sample : Fin n → α | iidSuccessIndexSet s sample = active} := by
    ext sample
    constructor
    · intro hcard
      refine Set.mem_iUnion.2 ⟨iidSuccessIndexSet s sample, ?_⟩
      refine Set.mem_iUnion.2 ⟨?_, rfl⟩
      exact Finset.mem_powersetCard.mpr
        ⟨by intro i _hi; simp, by simpa [iidSuccessCount] using hcard⟩
    · intro hmem
      rcases Set.mem_iUnion.mp hmem with ⟨active, hactive_mem⟩
      rcases Set.mem_iUnion.mp hactive_mem with ⟨hactive_exact, hactive_eq⟩
      have hactive_card : active.card = j :=
        (Finset.mem_powersetCard.mp hactive_exact).2
      change (iidSuccessIndexSet s sample).card = j
      rw [hactive_eq, hactive_card]
  have hdisj :
      (↑exactSets : Set (Finset (Fin n))).PairwiseDisjoint
          (fun active =>
            {sample : Fin n → α | iidSuccessIndexSet s sample = active}) := by
    intro active _hactive other _hother hne
    change Disjoint
      {sample : Fin n → α | iidSuccessIndexSet s sample = active}
      {sample : Fin n → α | iidSuccessIndexSet s sample = other}
    rw [Set.disjoint_left]
    intro sample hactive_eq hother_eq
    exact hne (hactive_eq.symm.trans hother_eq)
  have hmeas :
      ∀ active ∈ exactSets,
        MeasurableSet
          {sample : Fin n → α | iidSuccessIndexSet s sample = active} := by
    intro active _hactive
    exact iidSuccessIndexSet_measurableSet hs active
  calc
    (Measure.pi (fun _ : Fin n => μ)).real
        {sample : Fin n → α | iidSuccessCount s sample = j}
        =
        productMeasure.real
          (⋃ active ∈ exactSets,
            {sample : Fin n → α | iidSuccessIndexSet s sample = active}) := by
          rw [hcard_set]
    _ =
        ∑ active ∈ exactSets,
          productMeasure.real
            {sample : Fin n → α | iidSuccessIndexSet s sample = active} := by
          exact measureReal_biUnion_finset hdisj hmeas
    _ =
        ∑ active ∈ exactSets,
          (μ.real s) ^ active.card *
            (1 - μ.real s) ^ (n - active.card) := by
          refine Finset.sum_congr rfl ?_
          intro active _hactive
          exact iidProductMeasure_successIndexSet_eq_real μ hs active
    _ =
        ∑ _active ∈ exactSets,
          (μ.real s) ^ j * (1 - μ.real s) ^ (n - j) := by
          refine Finset.sum_congr rfl ?_
          intro active hactive
          have hactive_card : active.card = j :=
            (Finset.mem_powersetCard.mp hactive).2
          simp [hactive_card]
    _ =
      (Nat.choose n j : ℝ) *
        (μ.real s) ^ j * (1 - μ.real s) ^ (n - j) := by
        simp [exactSets, Finset.card_powersetCard, mul_assoc]

/--
For iid product samples, the real probability that at most `r` coordinates
fall in `s` is the finite sum of binomial masses.
-/
theorem iidProductMeasure_successCount_le_real
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {n : ℕ} {s : Set α} (hs : MeasurableSet s) (r : ℕ) :
    (Measure.pi (fun _ : Fin n => μ)).real
        {sample : Fin n → α | iidSuccessCount s sample ≤ r} =
      ∑ j ∈ Finset.Icc 0 (min r n),
        (Nat.choose n j : ℝ) *
          (μ.real s) ^ j * (1 - μ.real s) ^ (n - j) := by
  classical
  let productMeasure : Measure (Fin n → α) :=
    Measure.pi (fun _ : Fin n => μ)
  haveI : IsProbabilityMeasure productMeasure := by
    dsimp [productMeasure]
    infer_instance
  let exactCounts : Finset ℕ := Finset.Icc 0 (min r n)
  have hle_set :
      {sample : Fin n → α | iidSuccessCount s sample ≤ r} =
        ⋃ j ∈ exactCounts,
          {sample : Fin n → α | iidSuccessCount s sample = j} := by
    ext sample
    constructor
    · intro hle
      have hcount_le_n : iidSuccessCount s sample ≤ n := by
        simpa [iidSuccessCount, Finset.card_univ] using
          (iidSuccessIndexSet s sample).card_le_univ
      refine Set.mem_iUnion.2 ⟨iidSuccessCount s sample, ?_⟩
      refine Set.mem_iUnion.2 ⟨?_, rfl⟩
      exact Finset.mem_Icc.mpr
        ⟨Nat.zero_le _, le_min hle hcount_le_n⟩
    · intro hmem
      rcases Set.mem_iUnion.mp hmem with ⟨j, hj_mem⟩
      rcases Set.mem_iUnion.mp hj_mem with ⟨hj_exact, hj_eq⟩
      have hj_le_r : j ≤ r :=
        le_trans (Finset.mem_Icc.mp hj_exact).2 (min_le_left r n)
      have hj_eq' : iidSuccessCount s sample = j := hj_eq
      exact by
        change iidSuccessCount s sample ≤ r
        rw [hj_eq']
        exact hj_le_r
  have hdisj :
      (↑exactCounts : Set ℕ).PairwiseDisjoint
          (fun j =>
            {sample : Fin n → α | iidSuccessCount s sample = j}) := by
    intro j _hj k _hk hne
    change Disjoint
      {sample : Fin n → α | iidSuccessCount s sample = j}
      {sample : Fin n → α | iidSuccessCount s sample = k}
    rw [Set.disjoint_left]
    intro sample hj hk
    exact hne (hj.symm.trans hk)
  have hmeas :
      ∀ j ∈ exactCounts,
        MeasurableSet
          {sample : Fin n → α | iidSuccessCount s sample = j} := by
    intro j _hj
    exact iidSuccessCount_eq_measurableSet hs j
  calc
    (Measure.pi (fun _ : Fin n => μ)).real
        {sample : Fin n → α | iidSuccessCount s sample ≤ r}
        =
        productMeasure.real
          (⋃ j ∈ exactCounts,
            {sample : Fin n → α | iidSuccessCount s sample = j}) := by
          rw [hle_set]
    _ =
        ∑ j ∈ exactCounts,
          productMeasure.real
            {sample : Fin n → α | iidSuccessCount s sample = j} := by
          exact measureReal_biUnion_finset hdisj hmeas
    _ =
      ∑ j ∈ Finset.Icc 0 (min r n),
        (Nat.choose n j : ℝ) *
          (μ.real s) ^ j * (1 - μ.real s) ^ (n - j) := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact iidProductMeasure_successCount_eq_real μ hs j

/--
Integral-of-indicator version of the exact-count binomial mass formula.
-/
theorem iidProductMeasure_successCount_eq_indicator_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {n : ℕ} {s : Set α} (hs : MeasurableSet s) (j : ℕ) :
    ∫ sample : Fin n → α,
        ({sample : Fin n → α | iidSuccessCount s sample = j}.indicator
          (fun _sample => (1 : ℝ)) sample)
        ∂Measure.pi (fun _ : Fin n => μ) =
      (Nat.choose n j : ℝ) *
        (μ.real s) ^ j * (1 - μ.real s) ^ (n - j) := by
  rw [MeasureTheory.integral_indicator_const]
  · simp [iidProductMeasure_successCount_eq_real μ hs j]
  · exact iidSuccessCount_eq_measurableSet hs j

end

end Probability
end EconCSLib
