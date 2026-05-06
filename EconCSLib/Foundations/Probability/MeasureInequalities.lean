import EconCSLib.Foundations.Probability.FiniteExpectation
import Mathlib.Data.Set.Disjoint
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace EconCSLib

/-!
# Measure Inequalities

Small reusable measure-theoretic probability lemmas for continuous
change-of-variables arguments.
-/

/-- Real-valued probability/mass of an event under a measure. -/
noncomputable def measureProb {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → Prop) : ℝ :=
  (μ {a | p a}).toReal

theorem measureProb_le_of_measure_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop)
    (h : μ {a | p a} ≤ μ {a | q a}) :
    measureProb μ p ≤ measureProb μ q := by
  exact ENNReal.toReal_mono (measure_ne_top μ {a | q a}) h

theorem measureProb_lt_of_measure_lt
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop)
    (h : μ {a | p a} < μ {a | q a}) :
    measureProb μ p < measureProb μ q := by
  exact (ENNReal.toReal_lt_toReal
    (measure_ne_top μ {a | p a}) (measure_ne_top μ {a | q a})).2 h

theorem measureProb_pos_of_measure_ne_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p : α → Prop)
    (h : μ {a | p a} ≠ 0) :
    0 < measureProb μ p := by
  exact ENNReal.toReal_pos h (measure_ne_top μ {a | p a})

/-- Finite measure of a larger set transfers to every subset. -/
theorem measure_ne_top_of_subset_of_ne_top
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {s t : Set α}
    (hsub : s ⊆ t) (hfinite : μ t ≠ ∞) :
    μ s ≠ ∞ := by
  exact ne_top_of_le_ne_top hfinite (measure_mono hsub)

/-- Real-valued measure is positive when the underlying `ENNReal` mass is nonzero and finite. -/
theorem measureReal_pos_of_measure_ne_zero_ne_top
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α)
    (h_ne_zero : μ s ≠ 0)
    (h_ne_top : μ s ≠ ∞) :
    0 < μ.real s :=
  ENNReal.toReal_pos h_ne_zero h_ne_top

/-- Positive real-valued measure implies positive underlying `ENNReal` mass. -/
theorem measure_pos_of_measureReal_pos
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α)
    (h : 0 < μ.real s) :
    0 < μ s := by
  exact (ENNReal.toReal_pos_iff.mp h).1

theorem measureReal_inter_ge_one_sub_add
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {P Q : Set α}
    (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    {epsP epsQ : ℝ}
    (hprobP : 1 - epsP ≤ μ.real P)
    (hprobQ : 1 - epsQ ≤ μ.real Q) :
    1 - epsP - epsQ ≤ μ.real (P ∩ Q) := by
  have hPcompl :
      μ.real Pᶜ ≤ epsP := by
    have hcompl :
        μ.real Pᶜ = 1 - μ.real P :=
      probReal_compl_eq_one_sub (μ := μ) hP
    linarith
  have hQcompl :
      μ.real Qᶜ ≤ epsQ := by
    have hcompl :
        μ.real Qᶜ = 1 - μ.real Q :=
      probReal_compl_eq_one_sub (μ := μ) hQ
    linarith
  have hbad :
      μ.real (Pᶜ ∪ Qᶜ) ≤ epsP + epsQ := by
    exact (measureReal_union_le (μ := μ) Pᶜ Qᶜ).trans
      (add_le_add hPcompl hQcompl)
  have hcompl_inter :
      μ.real (P ∩ Q)ᶜ = 1 - μ.real (P ∩ Q) :=
    probReal_compl_eq_one_sub (μ := μ) (hP.inter hQ)
  have hdeMorgan : (P ∩ Q)ᶜ = Pᶜ ∪ Qᶜ := by
    ext a
    by_cases hpa : a ∈ P <;> by_cases hqa : a ∈ Q <;> simp [hpa, hqa]
  have hbad_inter :
      μ.real (P ∩ Q)ᶜ ≤ epsP + epsQ := by
    rwa [hdeMorgan]
  linarith

theorem isProbabilityMeasure_withDensity_of_lintegral_eq_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (D : α → ENNReal)
    (hD : ∫⁻ a, D a ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity D) := by
  refine ⟨?_⟩
  rw [withDensity_apply D MeasurableSet.univ]
  simpa using hD

theorem setLIntegral_ne_top_of_lintegral_eq_one
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (D : α → ENNReal)
    (hD : ∫⁻ a, D a ∂μ = 1) (s : Set α) :
    (∫⁻ a in s, D a ∂μ) ≠ ∞ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [← hD]
  exact setLIntegral_le_lintegral s D

theorem withDensity_measure_ne_zero_of_pos_on
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (D : α → ENNReal)
    {s : Set α} (hD : Measurable D) (hs : MeasurableSet s)
    (hμ : μ s ≠ 0) (hpos : ∀ a, a ∈ s → D a ≠ 0) :
    μ.withDensity D s ≠ 0 := by
  have hsupport_inter : Function.support D ∩ s = s := by
    ext a
    constructor
    · intro ha
      exact ha.2
    · intro ha
      exact ⟨hpos a ha, ha⟩
  have hμpos : 0 < μ s := by
    rwa [pos_iff_ne_zero]
  have hlin : 0 < ∫⁻ a in s, D a ∂μ := by
    rw [setLIntegral_pos_iff hD, hsupport_inter]
    exact hμpos
  rw [withDensity_apply D hs]
  exact ne_of_gt hlin

/--
Positive density on a measurable set gives positive real mass under a finite
`withDensity` measure.
-/
theorem withDensity_measureReal_pos_of_pos_on
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (D : α → ENNReal)
    {s : Set α} (hD : Measurable D) (hs : MeasurableSet s)
    (hμ : μ s ≠ 0) (hfinite : μ.withDensity D s ≠ ∞)
    (hpos : ∀ a, a ∈ s → D a ≠ 0) :
    0 < (μ.withDensity D).real s :=
  measureReal_pos_of_measure_ne_zero_ne_top (μ.withDensity D) s
    (withDensity_measure_ne_zero_of_pos_on μ D hD hs hμ hpos)
    hfinite

/--
Hoeffding upper-tail bound for a finite sum of independent bounded variables,
centered by their expectations.

This is a thin finite-sum wrapper around Mathlib's sub-Gaussian Hoeffding
inequality. It keeps EC paper proofs from repeatedly unpacking
`HasSubgaussianMGF` when they only need a concentration bound for a finite
family of bounded independent random variables.
-/
theorem measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {X : ι → α → ℝ}
    (h_indep : iIndepFun X μ)
    {s : Finset ι} {a b ε : ℝ}
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b)
    (hε : 0 ≤ ε) :
    μ.real
        {ω | ε ≤
          ∑ i ∈ s, (X i ω - ∫ x, X i x ∂μ)} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ((∑ _ ∈ s, ((‖b - a‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  let centered : ι → α → ℝ :=
    fun i ω => X i ω - ∫ x, X i x ∂μ
  have hcenter_indep : iIndepFun centered μ := by
    exact h_indep.comp
      (fun i x => x - ∫ y, X i y ∂μ)
      (fun _ => measurable_id.sub measurable_const)
  have hsub :
      ∀ i ∈ s,
        HasSubgaussianMGF
          (centered i)
          ((‖b - a‖₊ / 2) ^ 2) μ := by
    intro i hi
    exact hasSubgaussianMGF_of_mem_Icc (h_meas i hi) (h_bound i hi)
  simpa [centered] using
    (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := μ) hcenter_indep (s := s) hsub hε)

/--
Lower-tail Hoeffding bound for independent `[0,1]` indicators with mean
`1/2`, in the form used by random half-sample arguments: the probability that
the observed count is at most one third of the set size is bounded by the
corresponding centered Hoeffding exponential.
-/
theorem measure_sum_half_mean_indicator_le_third_le_exp
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {X : ι → α → ℝ}
    (h_indep : iIndepFun X μ)
    {s : Finset ι}
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean_neg :
      ∀ i ∈ s, (∫ ω, (-X i ω) ∂μ) = -(1 / 2 : ℝ)) :
    μ.real
        {ω | (∑ i ∈ s, X i ω) ≤ (s.card : ℝ) / 3} ≤
      Real.exp
        (-((s.card : ℝ) / 6) ^ 2 /
          (2 * ((∑ _ ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  let Y : ι → α → ℝ := fun i ω => -X i ω
  have hY_indep : iIndepFun Y μ := by
    exact h_indep.comp (fun _ x => -x) (fun _ => measurable_id.neg)
  have hY_meas : ∀ i ∈ s, AEMeasurable (Y i) μ := by
    intro i hi
    exact (h_meas i hi).neg
  have hY_bound : ∀ i ∈ s, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-1 : ℝ) 0 := by
    intro i hi
    filter_upwards [h_bound i hi] with ω hω
    exact ⟨by linarith [hω.2], by linarith [hω.1]⟩
  have htail :=
    measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
      (μ := μ) (X := Y) hY_indep (s := s)
      (a := (-1 : ℝ)) (b := 0) (ε := (s.card : ℝ) / 6)
      hY_meas hY_bound (by positivity)
  refine le_trans ?_ htail
  refine measureReal_mono (μ := μ) ?_ (measure_ne_top μ _)
  intro ω hω
  have hsum_eq :
      (∑ i ∈ s, (Y i ω - ∫ x, Y i x ∂μ)) =
        (s.card : ℝ) / 2 - ∑ i ∈ s, X i ω := by
    calc
      (∑ i ∈ s, (Y i ω - ∫ x, Y i x ∂μ))
          = ∑ i ∈ s, (-X i ω + (1 / 2 : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hmean_neg i hi]
              simp [Y]
      _ = (s.card : ℝ) / 2 - ∑ i ∈ s, X i ω := by
              rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
              simp
              ring
  change (s.card : ℝ) / 3 ≥ ∑ i ∈ s, X i ω at hω
  change (s.card : ℝ) / 6 ≤
    ∑ i ∈ s, (Y i ω - ∫ x, Y i x ∂μ)
  rw [hsum_eq]
  nlinarith

/-- Fair-coin measure on `Bool`, with mass `1/2` on `true`. -/
noncomputable def fairBoolMeasure : Measure Bool :=
  ((PMF.bernoulli (1 / 2 : NNReal) (by norm_num)).toMeasure : Measure Bool)

/-- Product fair-coin measure on Boolean side assignments. -/
noncomputable def fairBoolProductMeasure (ι : Type*) : Measure (ι → Bool) :=
  Measure.infinitePi (fun _ : ι => fairBoolMeasure)

theorem fairBoolMeasure_isProbabilityMeasure : IsProbabilityMeasure fairBoolMeasure := by
  simpa [fairBoolMeasure] using
    (inferInstance : IsProbabilityMeasure (PMF.bernoulli (1 / 2 : NNReal) (by norm_num)).toMeasure)

theorem fairBoolProductMeasure_isProbabilityMeasure (ι : Type*) :
    IsProbabilityMeasure (fairBoolProductMeasure ι) := by
  let P : ι → Measure Bool := fun _ => fairBoolMeasure
  let hμ : ∀ i : ι, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using fairBoolMeasure_isProbabilityMeasure
  simpa [fairBoolProductMeasure, P] using
    @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (ι := ι) (X := fun _ : ι => Bool)
      (mX := fun _ => by infer_instance) (μ := P) hμ

theorem fairBoolProduct_indicator_iIndepFun
    {ι : Type*} (keep : Bool) :
    iIndepFun
      (fun i (side : ι → Bool) => if side i = keep then (1 : ℝ) else 0)
      (fairBoolProductMeasure ι) := by
  let P : ι → Measure Bool := fun _ => fairBoolMeasure
  let hμ : ∀ i : ι, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using fairBoolMeasure_isProbabilityMeasure
  have hcoord :
      iIndepFun (fun i (side : ι → Bool) => side i)
        (Measure.infinitePi P) := by
    exact
      @ProbabilityTheory.iIndepFun_infinitePi
        (ι := ι) (𝓧 := fun _ => Bool)
        (m𝓧 := fun _ => by infer_instance)
        (Ω := fun _ => Bool) (mΩ := fun _ => by infer_instance)
        (P := P) hμ (X := fun i : ι => (fun b : Bool => b))
        (mX := fun _ => measurable_id)
  simpa [fairBoolProductMeasure, P] using hcoord.comp
    (fun _ b => if b = keep then (1 : ℝ) else 0)
    (fun _ => measurable_of_finite _)

theorem fairBoolProduct_indicator_integral
    {ι : Type*} (i : ι) (keep : Bool) :
  (∫ side : ι → Bool,
        (if side i = keep then (1 : ℝ) else 0) ∂fairBoolProductMeasure ι) =
      1 / 2 := by
  let P : ι → Measure Bool := fun _ => fairBoolMeasure
  let hμ : ∀ i : ι, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using fairBoolMeasure_isProbabilityMeasure
  haveI : IsProbabilityMeasure (Measure.infinitePi P) :=
    @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (ι := ι) (X := fun _ : ι => Bool)
      (mX := fun _ => by infer_instance) (μ := P) hμ
  let f : Bool → ℝ := fun b => if b = keep then 1 else 0
  have hf :
      AEStronglyMeasurable f
        (Measure.map (fun side : ι → Bool => side i)
          (fairBoolProductMeasure ι)) :=
    (measurable_of_finite f).aestronglyMeasurable
  calc
    (∫ side : ι → Bool,
        (if side i = keep then (1 : ℝ) else 0) ∂fairBoolProductMeasure ι)
        = ∫ side : ι → Bool, f (side i) ∂fairBoolProductMeasure ι := by rfl
    _ = ∫ b : Bool, f b ∂Measure.map
          (fun side : ι → Bool => side i) (fairBoolProductMeasure ι) := by
        exact (integral_map
          (μ := fairBoolProductMeasure ι)
          (φ := fun side : ι → Bool => side i)
          (f := f) (measurable_pi_apply i).aemeasurable hf).symm
    _ = ∫ b : Bool, f b ∂Measure.map
          (fun side : ι → Bool => side i) (Measure.infinitePi P) := by
      simp [fairBoolProductMeasure, P]
    _ = ∫ b : Bool, f b ∂fairBoolMeasure := by
        rw [show
            (Measure.map (fun side : ι → Bool => side i) (Measure.infinitePi P))
              = fairBoolMeasure from by
              simpa [P] using
                (@MeasureTheory.Measure.infinitePi_map_eval
                  (ι := ι) (X := fun _ : ι => Bool)
                  (mX := fun _ => by infer_instance) (μ := P) hμ i)]
    _ = 1 / 2 := by
        cases keep <;>
          simp [f, fairBoolMeasure, PMF.integral_eq_sum, PMF.bernoulli]

theorem fairBoolProduct_indicator_lower_tail_le_exp
    {ι : Type*} (s : Finset ι) (keep : Bool) :
    (fairBoolProductMeasure ι).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
    Real.exp
        (-((s.card : ℝ) / 6) ^ 2 /
          (2 * ((∑ _ ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  let P : ι → Measure Bool := fun _ => fairBoolMeasure
  letI hμ : ∀ i : ι, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using fairBoolMeasure_isProbabilityMeasure
  letI : IsProbabilityMeasure (Measure.infinitePi P) :=
    @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (ι := ι) (X := fun _ : ι => Bool)
      (mX := fun _ => by infer_instance) (μ := P) hμ
  haveI : IsProbabilityMeasure (fairBoolProductMeasure ι) := by
    simpa [fairBoolProductMeasure, P] using
      @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
        (ι := ι) (X := fun _ : ι => Bool)
        (mX := fun _ => by infer_instance) (μ := P) hμ
  refine measure_sum_half_mean_indicator_le_third_le_exp
    (μ := fairBoolProductMeasure ι)
    (X := fun i side => if side i = keep then (1 : ℝ) else 0)
    (fairBoolProduct_indicator_iIndepFun keep)
    (s := s) ?_ ?_ ?_
  · intro i _hi
    exact ((measurable_of_finite
      (fun b : Bool => if b = keep then (1 : ℝ) else 0)).comp
        (measurable_pi_apply i)).aemeasurable
  · intro i _hi
    exact ae_of_all _ fun side => by
      by_cases h : side i = keep <;> simp [h]
  · intro i _hi
    rw [integral_neg]
    simp [fairBoolProduct_indicator_integral i keep]

theorem fairBoolProduct_indicator_lower_tail_le_exp_card
    {ι : Type*} (s : Finset ι) (keep : Bool) :
    (fairBoolProductMeasure ι).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
    Real.exp (-(s.card : ℝ) / 18) := by
  have hraw := fairBoolProduct_indicator_lower_tail_le_exp s keep
  have hsum :
      ((∑ _i ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ) =
        (s.card : ℝ) / 4 := by
    simp
    ring
  have hexp :
      -((s.card : ℝ) / 6) ^ 2 / (2 * ((s.card : ℝ) / 4)) =
        -(s.card : ℝ) / 18 := by
    by_cases hcard : s.card = 0
    · simp [hcard]
    · have hcard_ne : (s.card : ℝ) ≠ 0 := by
        exact_mod_cast hcard
      field_simp [hcard_ne]
      ring
  rw [hsum] at hraw
  simpa [hexp]
    using hraw

theorem fairBoolProduct_indicator_lower_tail_le_exp_card_relaxed
    {ι : Type*} (s : Finset ι) (keep : Bool) :
    (fairBoolProductMeasure ι).real
        {side | (∑ i ∈ s, if side i = keep then (1 : ℝ) else 0) ≤
          (s.card : ℝ) / 3} ≤
    Real.exp (-(s.card : ℝ) / 36) := by
  exact le_trans (fairBoolProduct_indicator_lower_tail_le_exp_card s keep)
    (Real.exp_le_exp.mpr (by
      have hnonneg : 0 ≤ (s.card : ℝ) := by exact_mod_cast Nat.zero_le s.card
      nlinarith))

@[simp] theorem measureProb_false
    {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    measureProb μ (fun _ => False) = 0 := by
  simp [measureProb]

theorem measure_le_of_imp
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p q : α → Prop)
    (h : ∀ a, p a → q a) :
    μ {a | p a} ≤ μ {a | q a} :=
  measure_mono (by intro a ha; exact h a ha)

/-- Direct monotonicity lemma for `measureProb` under predicate implication. -/
theorem measureProb_mono
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (himp : ∀ a, p a → q a) :
    measureProb μ p ≤ measureProb μ q :=
  measureProb_le_of_measure_le μ p q (measure_le_of_imp μ p q himp)

theorem measure_lt_of_imp_of_diff_ne_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop)
    (hp : MeasurableSet {a | p a}) (hq : MeasurableSet {a | q a})
    (himp : ∀ a, p a → q a)
    (hpos : μ ({a | q a} ∩ {a | p a}ᶜ) ≠ 0) :
    μ {a | p a} < μ {a | q a} := by
  let P : Set α := {a | p a}
  let Q : Set α := {a | q a}
  have hdiff_meas : MeasurableSet (Q ∩ Pᶜ) := hq.inter hp.compl
  have hsplit : Q = P ∪ (Q ∩ Pᶜ) := by
    ext a
    constructor
    · intro hqa
      by_cases hpa : a ∈ P
      · exact Or.inl hpa
      · exact Or.inr ⟨hqa, hpa⟩
    · intro ha
      rcases ha with hpa | hdiff
      · exact himp a hpa
      · exact hdiff.1
  have hdisj : Disjoint P (Q ∩ Pᶜ) := by
    exact Set.disjoint_left.2 (by
      intro a hpa hdiff
      exact hdiff.2 hpa)
  have hdiff_pos : 0 < μ (Q ∩ Pᶜ) := by
    rwa [pos_iff_ne_zero]
  calc
    μ {a | p a} = μ P + 0 := by simp [P]
    _ < μ P + μ (Q ∩ Pᶜ) := by
      exact ENNReal.add_lt_add_left (measure_ne_top μ P) hdiff_pos
    _ = μ (P ∪ (Q ∩ Pᶜ)) := (measure_union hdisj hdiff_meas).symm
    _ = μ {a | q a} := by rw [← hsplit]

theorem measure_lt_of_cross_event_measure_lt
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop)
    (hp : MeasurableSet {a | p a}) (hq : MeasurableSet {a | q a})
    (hcross :
      μ ({a | p a} ∩ {a | q a}ᶜ) <
        μ ({a | q a} ∩ {a | p a}ᶜ)) :
    μ {a | p a} < μ {a | q a} := by
  let P : Set α := {a | p a}
  let Q : Set α := {a | q a}
  have hcommon : MeasurableSet (P ∩ Q) := hp.inter hq
  have hPnotQ : MeasurableSet (P ∩ Qᶜ) := hp.inter hq.compl
  have hQnotP : MeasurableSet (Q ∩ Pᶜ) := hq.inter hp.compl
  have hP_split : μ P = μ (P ∩ Q) + μ (P ∩ Qᶜ) := by
    have hunion : P = (P ∩ Q) ∪ (P ∩ Qᶜ) := by
      ext a
      by_cases hqa : a ∈ Q <;> simp [P, Q]
    conv_lhs => rw [hunion]
    exact measure_union (μ := μ) (s₁ := P ∩ Q) (s₂ := P ∩ Qᶜ)
      (Set.disjoint_left.2 (by
      intro a (ha : a ∈ P ∩ Q) (hb : a ∈ P ∩ Qᶜ)
      exact hb.2 ha.2)) hPnotQ
  have hQ_split : μ Q = μ (P ∩ Q) + μ (Q ∩ Pᶜ) := by
    have hunion : Q = (P ∩ Q) ∪ (Q ∩ Pᶜ) := by
      ext a
      by_cases hpa : a ∈ P <;> simp [P, Q, hpa, and_comm]
    conv_lhs => rw [hunion]
    exact measure_union (μ := μ) (s₁ := P ∩ Q) (s₂ := Q ∩ Pᶜ)
      (Set.disjoint_left.2 (by
      intro a (ha : a ∈ P ∩ Q) (hb : a ∈ Q ∩ Pᶜ)
      exact hb.2 ha.1)) hQnotP
  calc
    μ {a | p a} = μ (P ∩ Q) + μ (P ∩ Qᶜ) := hP_split
    _ < μ (P ∩ Q) + μ (Q ∩ Pᶜ) := by
      exact ENNReal.add_lt_add_left (measure_ne_top μ (P ∩ Q)) hcross
    _ = μ {a | q a} := hQ_split.symm

theorem measureProb_lt_of_cross_event_measure_lt
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop)
    (hp : MeasurableSet {a | p a}) (hq : MeasurableSet {a | q a})
    (hcross :
      μ ({a | p a} ∩ {a | q a}ᶜ) <
        μ ({a | q a} ∩ {a | p a}ᶜ)) :
    measureProb μ p < measureProb μ q :=
  measureProb_lt_of_measure_lt μ p q
    (measure_lt_of_cross_event_measure_lt μ p q hp hq hcross)

/-- Strict monotonicity for `measureProb` from a nonzero residual. -/
theorem measureProb_lt_of_imp_of_residual_ne_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hp : MeasurableSet {a | p a}) (hq : MeasurableSet {a | q a})
    (himp : ∀ a, p a → q a) (hres : μ ({a | q a} \ {a | p a}) ≠ 0) :
    measureProb μ p < measureProb μ q := by
  refine measureProb_lt_of_cross_event_measure_lt μ p q hp hq ?_
  have hleft : μ ({a | p a} ∩ {a | q a}ᶜ) = 0 := by
    apply measure_mono_null
      (s := ({a | p a} ∩ {a | q a}ᶜ : Set α))
      (t := (∅ : Set α))
    · intro a ha
      exact False.elim (ha.2 (himp a ha.1))
    · simp
  have hright : μ ({a | q a} ∩ {a | p a}ᶜ) ≠ 0 := by
    have hres' : ({a | q a} \ {a | p a}) = ({a | q a} ∩ {a | p a}ᶜ) := by
      ext a
      simp
    simpa [hres'] using hres
  rw [hleft]
  exact lt_of_le_of_ne (bot_le) hright.symm

/--
If a probability measure is pushed forward to a countable measurable space and
then converted to a `PMF`, finite `pmfProb` agrees with the source-measure
preimage mass.
-/
theorem pmfProb_toPMF_map_eq_measureProb
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype β] [DecidableEq β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f)
    (p : β → Prop) [DecidablePred p]
    (hp : MeasurableSet {b | p b}) :
    pmfProb
        (@Measure.toPMF β _ _ _ (μ.map f)
          (Measure.isProbabilityMeasure_map hf.aemeasurable)) p =
      measureProb μ (fun a => p (f a)) := by
  classical
  haveI : IsProbabilityMeasure (μ.map f) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  unfold measureProb
  rw [pmfProb_eq_toOuterMeasure_toReal]
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply ((μ.map f).toPMF) hp]
  rw [Measure.toPMF_toMeasure]
  rw [Measure.map_apply hf hp]
  rfl

/--
Compare continuous probability deltas by reducing to the finite image of a
measurable summary map.

This is the measure-level analogue of
`pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le`: the pointwise
indicator comparison only needs to hold on the source space, not on every value
of the finite codomain.
-/
theorem measureProb_sub_le_measureProb_sub_of_forall_indicator_sub_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype β] [DecidableEq β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f)
    (p q r s : β → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r] [DecidablePred s]
    (hp : MeasurableSet {b | p b}) (hq : MeasurableSet {b | q b})
    (hr : MeasurableSet {b | r b}) (hs : MeasurableSet {b | s b})
    (h : ∀ a,
      (if p (f a) then (1 : ℝ) else 0) - (if q (f a) then (1 : ℝ) else 0) ≤
        (if r (f a) then (1 : ℝ) else 0) - (if s (f a) then (1 : ℝ) else 0)) :
    measureProb μ (fun a => p (f a)) - measureProb μ (fun a => q (f a)) ≤
      measureProb μ (fun a => r (f a)) - measureProb μ (fun a => s (f a)) := by
  classical
  let γ : Type _ := {b : β // b ∈ Set.range f}
  let g : α → γ := fun a => ⟨f a, ⟨a, rfl⟩⟩
  have hg : Measurable g := hf.subtype_mk
  have hpγ : MeasurableSet {b : γ | p b.1} :=
    hp.preimage measurable_subtype_coe
  have hqγ : MeasurableSet {b : γ | q b.1} :=
    hq.preimage measurable_subtype_coe
  have hrγ : MeasurableSet {b : γ | r b.1} :=
    hr.preimage measurable_subtype_coe
  have hsγ : MeasurableSet {b : γ | s b.1} :=
    hs.preimage measurable_subtype_coe
  let ν : PMF γ := @Measure.toPMF γ _ _ _ (μ.map g)
    (Measure.isProbabilityMeasure_map hg.aemeasurable)
  have hpmf :
      pmfProb ν (fun b : γ => p b.1) - pmfProb ν (fun b : γ => q b.1) ≤
        pmfProb ν (fun b : γ => r b.1) - pmfProb ν (fun b : γ => s b.1) := by
    refine pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le ν
      (fun b : γ => p b.1) (fun b : γ => q b.1)
      (fun b : γ => r b.1) (fun b : γ => s b.1) ?_
    intro b
    rcases b with ⟨b, hb⟩
    rcases hb with ⟨a, ha⟩
    subst b
    exact h a
  have hp_eq :
      pmfProb ν (fun b : γ => p b.1) = measureProb μ (fun a => p (f a)) := by
    simpa [ν, g] using pmfProb_toPMF_map_eq_measureProb μ g hg
      (fun b : γ => p b.1) hpγ
  have hq_eq :
      pmfProb ν (fun b : γ => q b.1) = measureProb μ (fun a => q (f a)) := by
    simpa [ν, g] using pmfProb_toPMF_map_eq_measureProb μ g hg
      (fun b : γ => q b.1) hqγ
  have hr_eq :
      pmfProb ν (fun b : γ => r b.1) = measureProb μ (fun a => r (f a)) := by
    simpa [ν, g] using pmfProb_toPMF_map_eq_measureProb μ g hg
      (fun b : γ => r b.1) hrγ
  have hs_eq :
      pmfProb ν (fun b : γ => s b.1) = measureProb μ (fun a => s (f a)) := by
    simpa [ν, g] using pmfProb_toPMF_map_eq_measureProb μ g hg
      (fun b : γ => s b.1) hsγ
  rw [hp_eq, hq_eq, hr_eq, hs_eq] at hpmf
  exact hpmf

/--
Change-of-variables mass comparison for a with-density measure.

If `e` preserves the base measure `μ`, maps source set `s` into target set `t`,
and the density at each source point is at most the density at its image, then
the `μ.withDensity D` mass of `s` is at most the mass of `t`.
-/
theorem withDensity_measure_le_of_measurableEquiv_image_subset_density_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (e : α ≃ᵐ α) (hmp : MeasurePreserving e μ μ)
    (D : α → ℝ≥0∞) {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hmap : ∀ a, a ∈ s → e a ∈ t)
    (hdens : ∀ a, a ∈ s → D a ≤ D (e a)) :
    μ.withDensity D s ≤ μ.withDensity D t := by
  rw [withDensity_apply D hs, withDensity_apply D ht]
  calc
    ∫⁻ a in s, D a ∂μ ≤ ∫⁻ a in s, D (e a) ∂μ := by
      exact setLIntegral_mono' hs hdens
    _ = ∫⁻ b in e '' s, D b ∂μ := by
      exact hmp.setLIntegral_comp_emb e.measurableEmbedding D s
    _ ≤ ∫⁻ b in t, D b ∂μ := by
      exact lintegral_mono_set (Set.image_subset_iff.mpr hmap)

/--
Strict change-of-variables mass comparison for a with-density measure.

This strengthens `withDensity_measure_le_of_measurableEquiv_image_subset_density_le`:
if the density inequality is strict on a positive-base-measure subset `u` of
`s`, and the source integral is finite, then the with-density mass comparison
is strict.
-/
theorem withDensity_measure_lt_of_measurableEquiv_image_subset_density_lt_on
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (e : α ≃ᵐ α) (hmp : MeasurePreserving e μ μ)
    (D : α → ℝ≥0∞) (hD : Measurable D)
    {s t u : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u)
    (hmap : ∀ a, a ∈ s → e a ∈ t)
    (hdens_le : ∀ a, a ∈ s → D a ≤ D (e a))
    (hfi : ∫⁻ a in s, D a ∂μ ≠ ∞)
    (hu_subset : u ⊆ s)
    (hu_pos : μ u ≠ 0)
    (hdens_lt : ∀ a, a ∈ u → D a < D (e a)) :
    μ.withDensity D s < μ.withDensity D t := by
  rw [withDensity_apply D hs, withDensity_apply D ht]
  have hstrict :
      ∫⁻ a in s, D a ∂μ < ∫⁻ a in s, D (e a) ∂μ := by
    refine lintegral_strict_mono_of_ae_le_of_ae_lt_on
      (μ := μ.restrict s) (s := u)
      ((hD.comp e.measurable).aemeasurable)
      hfi
      ((ae_restrict_iff' hs).2 (ae_of_all μ hdens_le))
      ?_ ?_
    · rw [Measure.restrict_apply hu]
      rwa [Set.inter_eq_left.mpr hu_subset]
    · exact ae_of_all _ (fun a ha => hdens_lt a ha)
  calc
    ∫⁻ a in s, D a ∂μ < ∫⁻ a in s, D (e a) ∂μ := hstrict
    _ = ∫⁻ b in e '' s, D b ∂μ := by
      exact hmp.setLIntegral_comp_emb e.measurableEmbedding D s
    _ ≤ ∫⁻ b in t, D b ∂μ := by
      exact lintegral_mono_set (Set.image_subset_iff.mpr hmap)


--  Bonferroni inequalities

/-- First-order union bound for finite families. -/
theorem measureProb_biUnion_finset_le
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (p : ι → α → Prop) :
    measureProb μ (fun a => ∃ i ∈ s, p i a) ≤
      ∑ i ∈ s, measureProb μ (fun a => p i a) := by
  let U : Set α := {a : α | ∃ i ∈ s, p i a}
  have hset : U = ⋃ i ∈ s, {a : α | p i a} := by
    ext a
    simp [U]
  change (μ U).toReal ≤ ∑ i ∈ s, measureProb μ (fun a => p i a)
  rw [hset]
  simpa [measureProb] using
    (measureReal_biUnion_finset_le (μ := μ) (s := s) (f := fun i => {a : α | p i a}))

/-- First-order complement lower bound for finite intersections. -/
theorem measureProb_inter_ge_one_sub_sum_compl
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (s : Finset ι) (p : ι → α → Prop)
    (hm : ∀ i ∈ s, MeasurableSet {a : α | p i a}) :
    1 - ∑ i ∈ s, measureProb μ (fun a => ¬ p i a) ≤
      measureProb μ (fun a => ∀ i ∈ s, p i a) := by
  classical
  let U : Set α := {a : α | ∀ i ∈ s, p i a}
  let C : Set α := ⋃ i ∈ s, {a : α | ¬ p i a}
  have hU : MeasurableSet U := by
    have hU' : U = ⋂ i ∈ s, {a : α | p i a} := by
      ext a
      simp [U]
    rw [hU']
    exact Finset.measurableSet_biInter (s := s)
      (f := fun i : ι => {a : α | p i a}) hm
  have hC : MeasurableSet C := by
    simpa [C] using Finset.measurableSet_biUnion (s := s)
      (f := fun i : ι => {a : α | ¬ p i a})
      (fun i hi => (hm i hi).compl)
  have hdeMorgan : Uᶜ = C := by
    ext a
    constructor
    · intro ha
      by_cases hC : a ∈ C
      · exact hC
      · exfalso
        apply ha
        simp [U]
        intro i hi
        by_contra hpi
        apply hC
        change a ∈ ⋃ i ∈ s, {a : α | ¬ p i a}
        exact Set.mem_iUnion.mpr
          ⟨i, Set.mem_iUnion.mpr ⟨hi, by simpa using hpi⟩⟩
    · intro hC
      change a ∈ ⋃ i ∈ s, {a : α | ¬ p i a} at hC
      rcases Set.mem_iUnion.mp hC with ⟨i, hCi⟩
      rcases Set.mem_iUnion.mp hCi with ⟨hi, hpi⟩
      intro hUA
      exact hpi (hUA i hi)
  have hcomp : μ.real C ≤ ∑ i ∈ s, measureProb μ (fun a => ¬ p i a) := by
    have hCset : C = ⋃ i ∈ s, {a : α | ¬ p i a} := by
      ext a
      simp [C]
    rw [hCset]
    simpa [measureProb, Measure.real] using
      (measureReal_biUnion_finset_le (μ := μ) (s := s)
        (f := fun i => {a : α | ¬ p i a}))
  have hprob : 1 - ∑ i ∈ s, measureProb μ (fun a => ¬ p i a) ≤ μ.real U := by
    have hCeq : μ.real C = 1 - μ.real U := by
      have hcompl := probReal_compl_eq_one_sub (μ := μ) hU
      simpa [hdeMorgan] using hcompl
    calc
      1 - ∑ i ∈ s, measureProb μ (fun a => ¬ p i a) ≤ 1 - μ.real C := by
        nlinarith [hcomp]
      _ = μ.real U := by linarith [hCeq]
  simpa [measureProb, U] using hprob

private theorem sum_filter_choose_eq
    {ι α : Type*} (s : Finset ι) (p : ι → α → Prop) (ω : α) (k : ℕ)
    [DecidablePred (fun i => p i ω)] :
    (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) =
      ((s.filter (fun i => p i ω)).card.choose k : ℝ) := by
  have hfilter :
      (s.powersetCard k).filter (fun t => ∀ i ∈ t, p i ω) =
        (s.filter (fun i => p i ω)).powersetCard k := by
    ext t
    constructor
    · intro ht
      rcases Finset.mem_filter.mp ht with ⟨ht, hpt⟩
      rcases Finset.mem_powersetCard.mp ht with ⟨hts, htk⟩
      exact Finset.mem_powersetCard.mpr
        ⟨fun i hi => Finset.mem_filter.mpr ⟨hts hi, hpt i hi⟩, htk⟩
    · intro ht
      rcases Finset.mem_powersetCard.mp ht with ⟨hts, htk⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_powersetCard.mpr
        ⟨fun i hi => (Finset.mem_filter.mp (hts hi)).1, htk⟩, ?_⟩
      intro i hi
      exact (Finset.mem_filter.mp (hts hi)).2
  calc
    (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
        = ∑ t ∈ (s.powersetCard k).filter (fun t => ∀ i ∈ t, p i ω), (1 : ℝ) := by
          simpa [Finset.sum_filter]
    _ = (((s.powersetCard k).filter (fun t => ∀ i ∈ t, p i ω)).card : ℝ) := by simp
    _ = (((s.filter (fun i => p i ω)).powersetCard k).card : ℝ) := by rw [hfilter]
    _ = ((s.filter (fun i => p i ω)).card.choose k : ℝ) := by
      simp [Finset.card_powersetCard]

private theorem sum_choose_zero_eq_one (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * ((0 : ℕ).choose k : ℝ)) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp [Finset.sum_range_succ, ih, Nat.choose_eq_zero_of_lt (Nat.succ_pos m)]

private theorem alternating_sum_choose_real_eq_odd
    {n m : ℕ} (hn : 0 < n) (hm : Odd m) :
    (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * (n.choose k : ℝ))
      = -((n - 1).choose m : ℝ) := by
  have hcast :
      (∑ k ∈ Finset.range (m + 1), ((-1 : ℤ)^k * (n.choose k : ℤ) : ℤ))
          = (-1 : ℤ)^m * (n - 1).choose m := by
    simpa [Nat.sub_add_cancel hn] using
      (Int.alternating_sum_range_choose_eq_choose (n := n - 1) (m := m))
  have hcast' :
      (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * (n.choose k : ℝ))
      = (∑ k ∈ Finset.range (m + 1), (((-1 : ℤ)^k * (n.choose k : ℤ) : ℤ) : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    norm_num [Int.cast_mul, Int.cast_pow]
  calc
    (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * (n.choose k : ℝ))
        = (∑ k ∈ Finset.range (m + 1),
            (((-1 : ℤ)^k * (n.choose k : ℤ) : ℤ) : ℝ)) := hcast'
    _ = ((-1 : ℝ)^m) * (n - 1).choose m := by
      exact_mod_cast hcast
    _ = -((n - 1).choose m : ℝ) := by simpa [hm.neg_one_pow]

private theorem alternating_sum_choose_real_eq_even
    {n m : ℕ} (hn : 0 < n) (hm : Even m) :
    (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * (n.choose k : ℝ))
      = ((n - 1).choose m : ℝ) := by
  have hcast :
      (∑ k ∈ Finset.range (m + 1), ((-1 : ℤ)^k * (n.choose k : ℤ) : ℤ))
          = (-1 : ℤ)^m * (n - 1).choose m := by
    simpa [Nat.sub_add_cancel hn] using
      (Int.alternating_sum_range_choose_eq_choose (n := n - 1) (m := m))
  have hcast' :
      (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * (n.choose k : ℝ))
      = (∑ k ∈ Finset.range (m + 1), (((-1 : ℤ)^k * (n.choose k : ℤ) : ℤ) : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    norm_num [Int.cast_mul, Int.cast_pow]
  calc
    (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) * (n.choose k : ℝ))
        = (∑ k ∈ Finset.range (m + 1),
            (((-1 : ℤ)^k * (n.choose k : ℤ) : ℤ) : ℝ)) := hcast'
    _ = ((-1 : ℝ)^m) * (n - 1).choose m := by
      exact_mod_cast hcast
    _ = ((n - 1).choose m : ℝ) := by simpa [hm.neg_one_pow]

--  Bonferroni (finite odd-order truncation upper bound)
theorem measureProb_biUnion_finset_bonferroni_odd
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (s : Finset ι) (p : ι → α → Prop)
    (m : ℕ) (hm : ∀ i ∈ s, MeasurableSet {a : α | p i a}) (hodd : Odd m) :
    measureProb μ (fun a => ∃ i ∈ s, p i a) ≤
      1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
      ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
  classical
  let U : Set α := {a : α | ∃ i ∈ s, p i a}
  have hU : MeasurableSet U := by
    have hU' : U = ⋃ i ∈ s, {a : α | p i a} := by
      ext a
      simp [U]
    rw [hU']
    exact Finset.measurableSet_biUnion (s := s)
      (f := fun i : ι => {a : α | p i a}) hm
  let LHS : α → ℝ := U.indicator (fun _ : α => (1 : ℝ))
  let RHS : α → ℝ :=
    fun ω =>
      1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
        ∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
  have hpoint :
      ∀ ω, LHS ω ≤ RHS ω := by
    intro ω
    by_cases hUω : ω ∈ U
    · have hnzero : 0 < (s.filter (fun i => p i ω)).card := by
        rcases hUω with ⟨i, his, hp⟩
        exact Finset.card_pos.mpr ⟨i, by simp [his, hp]⟩
      have hsum :
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
            ) ) = -((s.filter (fun i => p i ω)).card - 1).choose m := by
        calc
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
              )
              = (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
                  ((s.filter (fun i => p i ω)).card.choose k : ℝ)) := by
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  rw [sum_filter_choose_eq (s := s) (p := p) (ω := ω) (k := k)]
          _ = -((s.filter (fun i => p i ω)).card - 1).choose m := by
                exact alternating_sum_choose_real_eq_odd
                  (hm := hodd) (n := (s.filter (fun i => p i ω)).card) hnzero
      have hchoose_nonneg : 0 ≤ (((s.filter (fun i => p i ω)).card - 1).choose m : ℝ) := by
        exact_mod_cast (Nat.zero_le (((s.filter (fun i => p i ω)).card - 1).choose m))
      have hrhs :
          RHS ω = 1 + (((s.filter (fun i => p i ω)).card - 1).choose m : ℝ) := by
        dsimp [RHS]
        nlinarith [hsum]
      have hLHS : LHS ω = (1 : ℝ) := by simp [LHS, hUω]
      rw [hLHS, hrhs]
      exact le_add_of_nonneg_right hchoose_nonneg
    · have hcard : (s.filter (fun i => p i ω)).card = 0 := by
        by_contra hcard
        rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hcard) with ⟨i, hi⟩
        exact hUω ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
      have hsum :
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
            ) ) = 1 := by
        calc
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
              )
              )
              = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
                  ((s.filter (fun i => p i ω)).card.choose k : ℝ) := by
                    refine Finset.sum_congr rfl ?_
                    intro k hk
                    rw [sum_filter_choose_eq (s := s) (p := p) (ω := ω) (k := k)]
              _ = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
                    ((0 : ℕ).choose k : ℝ) := by simp [hcard]
              _ = 1 := sum_choose_zero_eq_one m
      have hrhs : RHS ω = 0 := by
        dsimp [RHS]
        nlinarith [hsum]
      have hLHS : LHS ω = 0 := by simp [LHS, hUω]
      simpa [hLHS, hrhs]
  have hLInt : Integrable LHS μ := by
    refine (MeasureTheory.integrable_indicator_iff hU).2 ?_
    exact MeasureTheory.integrableOn_const (μ := μ) (s := U)
      (hs := measure_ne_top_of_subset (by simp) (measure_ne_top μ Set.univ))
  have hindicator_eq :
      ∀ (t : Finset ι), ∀ (ω : α),
        (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) =
          (⋂ i ∈ t, {a : α | p i a}).indicator (fun _ : α => (1 : ℝ)) ω := by
    intro t ω
    by_cases hforall : ∀ i ∈ t, p i ω
    · have hmem : ω ∈ ⋂ i ∈ t, {a : α | p i a} := by
        simpa [Set.mem_iInter] using hforall
      rw [if_pos hforall]
      simp [hmem]
    · have hnotmem : ω ∉ ⋂ i ∈ t, {a : α | p i a} := by
        intro hmem
        exact hforall (by simpa [Set.mem_iInter] using hmem)
      rw [if_neg hforall]
      simp [hnotmem]
  have hInnerInt :
      ∀ k, ∀ t ∈ s.powersetCard k,
      Integrable (fun ω => (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) μ := by
    intro k t ht
    let A : Set α := ⋂ i ∈ t, {a : α | p i a}
    have hA : MeasurableSet A := by
      refine t.measurableSet_biInter ?_
      intro i hi
      exact hm i ((Finset.mem_powersetCard.mp ht).1 hi)
    have hAint : Integrable (A.indicator (fun _ : α => (1 : ℝ))) μ := by
      refine (MeasureTheory.integrable_indicator_iff hA).2 ?_
      exact MeasureTheory.integrableOn_const (μ := μ) (s := A)
        (hs := measure_ne_top_of_subset (by simp) (measure_ne_top μ Set.univ))
    have hEq :
        (fun ω => (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
          = (fun ω => A.indicator (fun _ : α => (1 : ℝ)) ω) := by
      funext ω
      simpa [A] using hindicator_eq t ω
    exact hEq ▸ hAint
  have hInnerSumInt :
      ∀ k, Integrable (fun ω =>
        ∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) μ := by
    intro k
    refine MeasureTheory.integrable_finset_sum (s := s.powersetCard k) ?_
    intro t ht
    exact hInnerInt k t ht
  have hInnerMeasure :
      ∀ k,
      (∫ ω, (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ) =
        ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
    intro k
    calc
      (∫ ω, (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ)
          = ∑ t ∈ s.powersetCard k, ∫ ω, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) ∂μ := by
            refine MeasureTheory.integral_finset_sum (s := s.powersetCard k) ?_
            intro t ht
            exact hInnerInt k t ht
      _ = ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            let A : Set α := ⋂ i ∈ t, {a : α | p i a}
            have hA : MeasurableSet A := by
              refine t.measurableSet_biInter ?_
              intro i hi
              exact hm i ((Finset.mem_powersetCard.mp ht).1 hi)
            have hAeq : A = {a : α | ∀ i ∈ t, p i a} := by
              ext a
              simp [A, Set.mem_iInter]
            have hEq :
                (fun ω => (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
                  = (fun ω => A.indicator (fun _ : α => (1 : ℝ)) ω) := by
              funext ω
              simpa [A] using hindicator_eq t ω
            calc
              ∫ ω, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) ∂μ
                  = ∫ ω, A.indicator (fun _ : α => (1 : ℝ)) ω ∂μ := by
                    exact congrArg (fun g => ∫ ω, g ω ∂μ) hEq
              _ = ∫ ω in A, (1 : ℝ) ∂μ := by
                    rw [MeasureTheory.integral_indicator hA]
              _ = μ.real A := by
                    simpa using (MeasureTheory.setIntegral_one_eq_measureReal (μ := μ) (s := A))
              _ = measureProb μ (fun a => ∀ i ∈ t, p i a) := by
                    have hAeq' : μ.real A = μ.real {a : α | ∀ i ∈ t, p i a} := by
                      simpa [hAeq]
                    simpa [measureProb, Measure.real] using hAeq'
  have hOuterInt :
      Integrable (fun ω =>
        ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
          (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ) μ := by
    refine MeasureTheory.integrable_finset_sum (s := Finset.range (m + 1)) ?_
    intro k hk
    exact (hInnerSumInt k).const_mul ((-1 : ℝ)^k)
  have hRHSInt : Integrable RHS μ := by
    have hconstInt : Integrable (fun _ : α => (1 : ℝ)) μ := by
      simpa using (MeasureTheory.integrable_const (μ := μ) (c := (1 : ℝ)))
    exact (hconstInt.sub hOuterInt)
  have hOuterSum :
      (∫ ω, ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
        (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ)
          = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
    calc
      ∫ ω, ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
          (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ
          = ∑ k ∈ Finset.range (m + 1), ∫ ω, ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k,
                (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ := by
                exact MeasureTheory.integral_finset_sum (s := Finset.range (m + 1))
                  (f := fun k ω => ((-1 : ℝ)^k) *
                    (∑ t ∈ s.powersetCard k,
                      (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
                  ) (fun k hk => (hInnerSumInt k).const_mul ((-1 : ℝ)^k))
      _ = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
        ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          calc
            ∫ ω, ((-1 : ℝ)^k) *
                (∑ t ∈ s.powersetCard k,
                  (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ
                = ((-1 : ℝ)^k) * ∫ ω, (∑ t ∈ s.powersetCard k,
                    (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ := by
                      simpa using (MeasureTheory.integral_const_mul ((-1 : ℝ)^k)
                        (fun ω => ∑ t ∈ s.powersetCard k,
                          (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) )
              _ = ((-1 : ℝ)^k) * (∑ t ∈ s.powersetCard k,
                    measureProb μ (fun a => ∀ i ∈ t, p i a)) := by
                    rw [hInnerMeasure k]
  have hRHSIntEq :
      ∫ ω, RHS ω ∂μ =
        1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
          ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
    have hconstInt : Integrable (fun _ : α => (1 : ℝ)) μ := by
      simpa using (MeasureTheory.integrable_const (μ := μ) (c := (1 : ℝ)))
    calc
      (∫ ω, RHS ω ∂μ)
          = (∫ ω, (1 : ℝ) ∂μ) - ∫ ω, (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) ) ) ∂μ := by
                simpa [RHS] using (MeasureTheory.integral_sub hconstInt hOuterInt)
      _ = 1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
              rw [hOuterSum]
              simp [MeasureTheory.integral_const]
  have hLHSInt :
      (∫ ω, LHS ω ∂μ) = measureProb μ (fun a => ∃ i ∈ s, p i a) := by
    calc
      (∫ ω, LHS ω ∂μ) = ∫ ω, U.indicator (fun _ : α => (1 : ℝ)) ω ∂μ := by
        simp [LHS]
      _ = ∫ ω in U, (1 : ℝ) ∂μ := by
        simpa using (MeasureTheory.integral_indicator (s := U) (f := fun _ : α => (1 : ℝ)) hU)
      _ = μ.real U := by
        simpa using (MeasureTheory.setIntegral_one_eq_measureReal (μ := μ) (s := U))
      _ = measureProb μ (fun a => ∃ i ∈ s, p i a) := by
        simp [measureProb, Measure.real, U]
  have hInt := MeasureTheory.integral_mono hLInt hRHSInt hpoint
  simpa [hLHSInt, hRHSIntEq] using hInt

--  Bonferroni (finite even-order truncation lower bound)
theorem measureProb_biUnion_finset_bonferroni_even
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (s : Finset ι) (p : ι → α → Prop)
    (m : ℕ) (hm : ∀ i ∈ s, MeasurableSet {a : α | p i a}) (hme : Even m) :
    1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
      ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) ≤
      measureProb μ (fun a => ∃ i ∈ s, p i a) := by
  classical
  let U : Set α := {a : α | ∃ i ∈ s, p i a}
  have hU : MeasurableSet U := by
    have hU' : U = ⋃ i ∈ s, {a : α | p i a} := by
      ext a
      simp [U]
    rw [hU']
    exact Finset.measurableSet_biUnion (s := s) (f := fun i : ι => {a : α | p i a}) hm
  let LHS : α → ℝ := U.indicator (fun _ : α => (1 : ℝ))
  let RHS : α → ℝ :=
    fun ω =>
      1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
        ∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
  have hpoint :
      ∀ ω, RHS ω ≤ LHS ω := by
    intro ω
    by_cases hUω : ω ∈ U
    · have hnzero : 0 < (s.filter (fun i => p i ω)).card := by
        rcases hUω with ⟨i, his, hp⟩
        exact Finset.card_pos.mpr ⟨i, by simp [his, hp]⟩
      have hsum :
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
            ) ) = ((s.filter (fun i => p i ω)).card - 1).choose m := by
        calc
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
              )
              )
              = (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
                  ((s.filter (fun i => p i ω)).card.choose k : ℝ)) := by
                    refine Finset.sum_congr rfl ?_
                    intro k hk
                    rw [sum_filter_choose_eq (s := s) (p := p) (ω := ω) (k := k)]
          _ = ((s.filter (fun i => p i ω)).card - 1).choose m := by
                exact alternating_sum_choose_real_eq_even
                  (hm := hme) (n := (s.filter (fun i => p i ω)).card) hnzero
      have hchoose_nonneg : 0 ≤ (((s.filter (fun i => p i ω)).card - 1).choose m : ℝ) := by
        exact_mod_cast (Nat.zero_le (((s.filter (fun i => p i ω)).card - 1).choose m))
      have hrhs :
          RHS ω = 1 - (((s.filter (fun i => p i ω)).card - 1).choose m : ℝ) := by
        dsimp [RHS]
        nlinarith [hsum]
      have hLHS : LHS ω = (1 : ℝ) := by simp [LHS, hUω]
      rw [hrhs, hLHS]
      nlinarith
    · have hcard : (s.filter (fun i => p i ω)).card = 0 := by
        by_contra hcard
        rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hcard) with ⟨i, hi⟩
        exact hUω ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
      have hsum :
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
            ) ) = 1 := by
        calc
          (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)
              )
              )
              = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
                  ((s.filter (fun i => p i ω)).card.choose k : ℝ) := by
                    refine Finset.sum_congr rfl ?_
                    intro k hk
                    rw [sum_filter_choose_eq (s := s) (p := p) (ω := ω) (k := k)]
              _ = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
                    ((0 : ℕ).choose k : ℝ) := by simp [hcard]
              _ = 1 := sum_choose_zero_eq_one m
      have hrhs : RHS ω = 0 := by
        dsimp [RHS]
        nlinarith [hsum]
      have hLHS : LHS ω = 0 := by simp [LHS, hUω]
      simpa [hLHS, hrhs]
  have hLInt : Integrable LHS μ := by
    refine (MeasureTheory.integrable_indicator_iff hU).2 ?_
    exact MeasureTheory.integrableOn_const (μ := μ) (s := U)
      (hs := measure_ne_top_of_subset (by simp) (measure_ne_top μ Set.univ))
  have hindicator_eq :
      ∀ (t : Finset ι), ∀ (ω : α),
        (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) =
          (⋂ i ∈ t, {a : α | p i a}).indicator (fun _ : α => (1 : ℝ)) ω := by
    intro t ω
    by_cases hforall : ∀ i ∈ t, p i ω
    · have hmem : ω ∈ ⋂ i ∈ t, {a : α | p i a} := by
        simpa [Set.mem_iInter] using hforall
      rw [if_pos hforall]
      simp [hmem]
    · have hnotmem : ω ∉ ⋂ i ∈ t, {a : α | p i a} := by
        intro hmem
        exact hforall (by simpa [Set.mem_iInter] using hmem)
      rw [if_neg hforall]
      simp [hnotmem]
  have hInnerInt :
      ∀ k, ∀ t ∈ s.powersetCard k,
      Integrable (fun ω => (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) μ := by
    intro k t ht
    let A : Set α := ⋂ i ∈ t, {a : α | p i a}
    have hA : MeasurableSet A := by
      refine t.measurableSet_biInter ?_
      intro i hi
      exact hm i ((Finset.mem_powersetCard.mp ht).1 hi)
    have hAint : Integrable (A.indicator (fun _ : α => (1 : ℝ))) μ := by
      refine (MeasureTheory.integrable_indicator_iff hA).2 ?_
      exact MeasureTheory.integrableOn_const (μ := μ) (s := A)
        (hs := measure_ne_top_of_subset (by simp) (measure_ne_top μ Set.univ))
    have hEq :
        (fun ω => (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
          = (fun ω => A.indicator (fun _ : α => (1 : ℝ)) ω) := by
      funext ω
      simpa [A] using hindicator_eq t ω
    exact hEq ▸ hAint
  have hInnerSumInt :
      ∀ k, Integrable (fun ω =>
        ∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) μ := by
    intro k
    refine MeasureTheory.integrable_finset_sum (s := s.powersetCard k) ?_
    intro t ht
    exact hInnerInt k t ht
  have hInnerMeasure :
      ∀ k,
      (∫ ω, (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ) =
        ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
    intro k
    calc
      (∫ ω, (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ)
          = ∑ t ∈ s.powersetCard k, ∫ ω, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) ∂μ := by
            refine MeasureTheory.integral_finset_sum (s := s.powersetCard k) ?_
            intro t ht
            exact hInnerInt k t ht
      _ = ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            let A : Set α := ⋂ i ∈ t, {a : α | p i a}
            have hA : MeasurableSet A := by
              refine t.measurableSet_biInter ?_
              intro i hi
              exact hm i ((Finset.mem_powersetCard.mp ht).1 hi)
            have hAeq : A = {a : α | ∀ i ∈ t, p i a} := by
              ext a
              simp [A, Set.mem_iInter]
            have hEq :
                (fun ω => (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
                  = (fun ω => A.indicator (fun _ : α => (1 : ℝ)) ω) := by
              funext ω
              simpa [A] using hindicator_eq t ω
            calc
              ∫ ω, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) ∂μ
                  = ∫ ω, A.indicator (fun _ : α => (1 : ℝ)) ω ∂μ := by
                    exact congrArg (fun g => ∫ ω, g ω ∂μ) hEq
              _ = ∫ ω in A, (1 : ℝ) ∂μ := by
                    rw [MeasureTheory.integral_indicator hA]
              _ = μ.real A := by
                    simpa using (MeasureTheory.setIntegral_one_eq_measureReal (μ := μ) (s := A))
              _ = measureProb μ (fun a => ∀ i ∈ t, p i a) := by
                    have hAeq' : μ.real A = μ.real {a : α | ∀ i ∈ t, p i a} := by
                      simpa [hAeq]
                    simpa [measureProb, Measure.real] using hAeq'
  have hOuterInt :
      Integrable (fun ω =>
        ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
          (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ) μ := by
    refine MeasureTheory.integrable_finset_sum (s := Finset.range (m + 1)) ?_
    intro k hk
    exact (hInnerSumInt k).const_mul ((-1 : ℝ)^k)
  have hRHSInt : Integrable RHS μ := by
    have hconstInt : Integrable (fun _ : α => (1 : ℝ)) μ := by
      simpa using (MeasureTheory.integrable_const (μ := μ) (c := (1 : ℝ)))
    exact (hconstInt.sub hOuterInt)
  have hOuterSum :
      (∫ ω, ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
        (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ)
          = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
    calc
      ∫ ω, ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
          (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ
          = ∑ k ∈ Finset.range (m + 1), ∫ ω, ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k,
                (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ := by
                exact MeasureTheory.integral_finset_sum (s := Finset.range (m + 1))
                  (f := fun k ω => ((-1 : ℝ)^k) *
                    (∑ t ∈ s.powersetCard k,
                      (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0))
                  ) (fun k hk => (hInnerSumInt k).const_mul ((-1 : ℝ)^k))
      _ = ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
        ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          calc
            ∫ ω, ((-1 : ℝ)^k) *
                (∑ t ∈ s.powersetCard k,
                  (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ
                = ((-1 : ℝ)^k) * ∫ ω, (∑ t ∈ s.powersetCard k,
                    (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) ∂μ := by
                      simpa using (MeasureTheory.integral_const_mul ((-1 : ℝ)^k)
                        (fun ω => ∑ t ∈ s.powersetCard k,
                          (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0)) )
              _ = ((-1 : ℝ)^k) * (∑ t ∈ s.powersetCard k,
                    measureProb μ (fun a => ∀ i ∈ t, p i a)) := by
                    rw [hInnerMeasure k]
  have hRHSIntEq :
      ∫ ω, RHS ω ∂μ =
        1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
          ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
    have hconstInt : Integrable (fun _ : α => (1 : ℝ)) μ := by
      simpa using (MeasureTheory.integrable_const (μ := μ) (c := (1 : ℝ)))
    calc
      (∫ ω, RHS ω ∂μ)
          = (∫ ω, (1 : ℝ) ∂μ) - ∫ ω, (∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
              (∑ t ∈ s.powersetCard k, (if ∀ i ∈ t, p i ω then (1 : ℝ) else 0) ) ) ∂μ := by
                simpa [RHS] using (MeasureTheory.integral_sub hconstInt hOuterInt)
      _ = 1 - ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ)^k) *
            ∑ t ∈ s.powersetCard k, measureProb μ (fun a => ∀ i ∈ t, p i a) := by
              rw [hOuterSum]
              simp [MeasureTheory.integral_const]
  have hLHSInt :
      (∫ ω, LHS ω ∂μ) = measureProb μ (fun a => ∃ i ∈ s, p i a) := by
    calc
      (∫ ω, LHS ω ∂μ) = ∫ ω, U.indicator (fun _ : α => (1 : ℝ)) ω ∂μ := by
        simp [LHS]
      _ = ∫ ω in U, (1 : ℝ) ∂μ := by
        simpa using (MeasureTheory.integral_indicator (s := U) (f := fun _ : α => (1 : ℝ)) hU)
      _ = μ.real U := by
        simpa using (MeasureTheory.setIntegral_one_eq_measureReal (μ := μ) (s := U))
      _ = measureProb μ (fun a => ∃ i ∈ s, p i a) := by
        simp [measureProb, Measure.real, U]
  have hInt := MeasureTheory.integral_mono hRHSInt hLInt hpoint
  simpa [hLHSInt, hRHSIntEq] using hInt

end EconCSLib
