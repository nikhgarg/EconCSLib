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
          (2 * ((∑ i ∈ s, ((‖b - a‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
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
          (2 * ((∑ i ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
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
        simpa [fairBoolProductMeasure, P]
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
          (2 * ((∑ i ∈ s, ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
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

end EconCSLib
