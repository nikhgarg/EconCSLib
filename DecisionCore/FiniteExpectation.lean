import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace DecisionCore

/-- Finite expectation of a real-valued function under a PMF. -/
noncomputable def pmfExp {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (μ a).toReal * f a

/-- Expectation for two independent PMF draws. -/
noncomputable def pmfPairExp {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f : α → β → ℝ) : ℝ :=
  pmfExp μ (fun a => pmfExp ν (fun b => f a b))

/-- The total real mass of a PMF on a finite type is `1`. -/
theorem pmfToRealSum {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) :
    ∑ a : α, (μ a).toReal = 1 := by
  have h_univ : μ.toOuterMeasure (Set.univ : Set α) = 1 := by
    exact (PMF.toOuterMeasure_apply_eq_one_iff (p := μ) (s := (Set.univ : Set α))).2
      (by intro a _; simp)
  have h_sum_enn : ∑ a : α, μ a = 1 := by
    calc
      ∑ a : α, μ a = μ.toOuterMeasure (Set.univ : Set α) := by
        symm
        simpa using (PMF.toOuterMeasure_apply_fintype (p := μ) (s := (Set.univ : Set α)))
      _ = 1 := h_univ
  have h_ne_top : ∀ a ∈ (Finset.univ : Finset α), μ a ≠ ⊤ := by
    intro a _
    exact μ.apply_ne_top a
  calc
    ∑ a : α, (μ a).toReal = (∑ a : α, μ a).toReal := by
      symm
      simpa using (ENNReal.toReal_sum (s := (Finset.univ : Finset α)) (f := fun a => μ a) h_ne_top)
    _ = 1 := by
      simpa [h_sum_enn]

/-- Every atom of a PMF has real mass at most one. -/
theorem pmf_apply_toReal_le_one {α : Type*} (μ : PMF α) (a : α) :
    (μ a).toReal ≤ 1 := by
  have hle : μ a ≤ 1 := by
    rw [← PMF.tsum_coe μ]
    exact ENNReal.le_tsum a
  exact ENNReal.toReal_mono ENNReal.one_ne_top hle

/-- The uniform PMF over a finite nonempty type. -/
noncomputable def uniformPMF (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  PMF.ofFintype (fun _ : α => ((Fintype.card α : ENNReal)⁻¹)) (by
    rw [Finset.sum_const, Finset.card_univ]
    have hcard : (Fintype.card α : ENNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
    simpa [nsmul_eq_mul] using
      (ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top (Fintype.card α))))

@[simp] theorem uniformPMF_apply {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    uniformPMF α a = ((Fintype.card α : ENNReal)⁻¹) := by
  rfl

theorem uniformPMF_apply_toReal {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    (uniformPMF α a).toReal = (Fintype.card α : ℝ)⁻¹ := by
  simp [uniformPMF]

theorem uniformPMF_apply_toReal_pos {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    0 < (uniformPMF α a).toReal := by
  rw [uniformPMF_apply_toReal]
  exact inv_pos.mpr (by exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›))

theorem pmfExp_congr {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) {f g : α → ℝ}
    (h : ∀ a, f a = g a) :
    pmfExp μ f = pmfExp μ g := by
  unfold pmfExp
  simp [h]

/-- Uniform finite expectation is invariant under a relabeling equivalence. -/
theorem pmfExp_uniformPMF_comp_equiv {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (e : α ≃ α) (f : α → ℝ) :
    pmfExp (uniformPMF α) (fun a => f (e a)) =
      pmfExp (uniformPMF α) f := by
  unfold pmfExp
  simpa [uniformPMF_apply_toReal] using
    (Equiv.sum_comp e (fun a : α => (Fintype.card α : ℝ)⁻¹ * f a))

/--
If `g` is obtained from `f` by relabeling a uniformly drawn finite input, then
the two expectations are equal.
-/
theorem pmfExp_uniformPMF_eq_of_comp_equiv {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (e : α ≃ α) {f g : α → ℝ}
    (h : ∀ a, f (e a) = g a) :
    pmfExp (uniformPMF α) f = pmfExp (uniformPMF α) g := by
  calc
    pmfExp (uniformPMF α) f =
        pmfExp (uniformPMF α) (fun a => f (e a)) := by
          exact (pmfExp_uniformPMF_comp_equiv e f).symm
    _ = pmfExp (uniformPMF α) g := by
          exact pmfExp_congr (uniformPMF α) h

@[simp] theorem pmfExp_const {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (c : ℝ) :
    pmfExp μ (fun _ => c) = c := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * c = (∑ a : α, (μ a).toReal) * c := by
      simpa using (Finset.sum_mul (s := (Finset.univ : Finset α))
        (f := fun a => (μ a).toReal) (a := c)).symm
    _ = 1 * c := by rw [pmfToRealSum μ]
    _ = c := by ring

@[simp] theorem pmfPairExp_ignore_right {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (g : α → ℝ) :
    pmfPairExp μ ν (fun a _ => g a) = pmfExp μ g := by
  unfold pmfPairExp
  simp [pmfExp_const]

@[simp] theorem pmfPairExp_ignore_left {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (g : β → ℝ) :
    pmfPairExp μ ν (fun _ b => g b) = pmfExp ν g := by
  unfold pmfPairExp
  simp [pmfExp_const]

/-- Probability of a predicate under a finite PMF, returned as a real number. -/
noncomputable def pmfProb {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] : ℝ :=
  pmfExp μ (fun a => if p a then 1 else 0)

end DecisionCore

namespace DecisionCore

@[simp] theorem pmfExp_zero {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) :
    pmfExp μ (fun _ => 0) = 0 := by
  simpa using pmfExp_const (μ := μ) (c := 0)

/-- Linearity of finite PMF expectation. -/
theorem pmfExp_add {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) :
    pmfExp μ (fun a => f a + g a) = pmfExp μ f + pmfExp μ g := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * (f a + g a)
        = ∑ a : α, ((μ a).toReal * f a + (μ a).toReal * g a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = (∑ a : α, (μ a).toReal * f a) +
          (∑ a : α, (μ a).toReal * g a) := by
          rw [Finset.sum_add_distrib]

/-- Subtractive linearity of finite PMF expectation. -/
theorem pmfExp_sub {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) :
    pmfExp μ (fun a => f a - g a) = pmfExp μ f - pmfExp μ g := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * (f a - g a)
        = ∑ a : α, ((μ a).toReal * f a - (μ a).toReal * g a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = (∑ a : α, (μ a).toReal * f a) -
          (∑ a : α, (μ a).toReal * g a) := by
          rw [Finset.sum_sub_distrib]

@[simp] theorem pmfExp_neg {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) :
    pmfExp μ (fun a => - f a) = - pmfExp μ f := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * (- f a)
        = ∑ a : α, - ((μ a).toReal * f a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = - ∑ a : α, (μ a).toReal * f a := by
          rw [Finset.sum_neg_distrib]

/-- Multiplying the integrand by a constant on the left pulls out of expectation. -/
theorem pmfExp_const_mul {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (c : ℝ) (f : α → ℝ) :
    pmfExp μ (fun a => c * f a) = c * pmfExp μ f := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * (c * f a)
        = ∑ a : α, c * ((μ a).toReal * f a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = c * ∑ a : α, (μ a).toReal * f a := by
          rw [Finset.mul_sum]

/-- Multiplying the integrand by a constant on the right pulls out of expectation. -/
theorem pmfExp_mul_const {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfExp μ (fun a => f a * c) = pmfExp μ f * c := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * (f a * c)
        = ∑ a : α, ((μ a).toReal * f a) * c := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ = (∑ a : α, (μ a).toReal * f a) * c := by
          rw [Finset.sum_mul]

/--
If a finite random variable takes value `x` on event `p` and value `y` off that
event, its expectation is `Pr[p] * x + (1 - Pr[p]) * y`.
-/
theorem pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (x y : ℝ)
    (h : ∀ a, f a = if p a then x else y) :
    pmfExp μ f = pmfProb μ p * x + (1 - pmfProb μ p) * y := by
  classical
  have hpoint :
      ∀ a, f a = y + (if p a then (1 : ℝ) else 0) * (x - y) := by
    intro a
    rw [h a]
    by_cases hp : p a <;> simp [hp]
  calc
    pmfExp μ f =
        pmfExp μ (fun a => y + (if p a then (1 : ℝ) else 0) * (x - y)) := by
          exact pmfExp_congr μ hpoint
    _ = pmfExp μ (fun _ => y) +
          pmfExp μ (fun a => (if p a then (1 : ℝ) else 0) * (x - y)) := by
          rw [pmfExp_add]
    _ = y + pmfProb μ p * (x - y) := by
          rw [pmfExp_const]
          rw [pmfExp_mul_const]
          rfl
    _ = pmfProb μ p * x + (1 - pmfProb μ p) * y := by
          ring

/-- A finite PMF expectation is bounded above by any pointwise upper bound. -/
theorem pmfExp_le_of_forall_le {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a, f a ≤ c) :
    pmfExp μ f ≤ c := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * f a
        ≤ ∑ a : α, (μ a).toReal * c := by
          exact Finset.sum_le_sum (by
            intro a _
            exact mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)
    _ = c := by
          calc
            ∑ a : α, (μ a).toReal * c
                = (∑ a : α, (μ a).toReal) * c := by
                    simpa using (Finset.sum_mul (s := (Finset.univ : Finset α))
                      (f := fun a => (μ a).toReal) (a := c)).symm
            _ = c := by
                    rw [pmfToRealSum μ]
                    ring

/-- Finite PMF probabilities are nonnegative. -/
theorem pmfProb_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    0 ≤ pmfProb μ p := by
  classical
  unfold pmfProb pmfExp
  refine Finset.sum_nonneg ?_
  intro a _
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  by_cases hp : p a <;> simp [hp]

/-- Finite PMF probabilities are at most one. -/
theorem pmfProb_le_one {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    pmfProb μ p ≤ 1 := by
  classical
  exact pmfExp_le_of_forall_le μ (fun a => if p a then (1 : ℝ) else 0) 1
    (by intro a; by_cases hp : p a <;> simp [hp])

/-- Complement rule for finite PMF probabilities. -/
theorem pmfProb_compl {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    pmfProb μ (fun a => ¬p a) = 1 - pmfProb μ p := by
  classical
  unfold pmfProb pmfExp
  calc
    ∑ a : α, (μ a).toReal * (if ¬p a then (1 : ℝ) else 0)
        = ∑ a : α, (
            (μ a).toReal * 1 -
              (μ a).toReal * (if p a then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases hp : p a <;> simp [hp]
    _ = (∑ a : α, (μ a).toReal * 1) -
          ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
          simp [pmfToRealSum μ]

/-- Positive mass inside an event makes its finite PMF probability positive. -/
theorem pmfProb_pos_of_mass {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (a₀ : α)
    (hp : p a₀) (hmass : 0 < (μ a₀).toReal) :
    0 < pmfProb μ p := by
  classical
  unfold pmfProb pmfExp
  have hnonneg :
      ∀ a ∈ (Finset.univ : Finset α),
        0 ≤ (μ a).toReal * if p a then (1 : ℝ) else 0 := by
    intro a _
    refine mul_nonneg ENNReal.toReal_nonneg ?_
    by_cases hpa : p a <;> simp [hpa]
  have hterm :
      (μ a₀).toReal * (if p a₀ then (1 : ℝ) else 0) = (μ a₀).toReal := by
    simp [hp]
  have hle :
      (μ a₀).toReal * (if p a₀ then (1 : ℝ) else 0) ≤
        ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
    exact Finset.single_le_sum hnonneg (Finset.mem_univ a₀)
  rw [hterm] at hle
  exact lt_of_lt_of_le hmass hle

/-- Positive mass outside an event makes its finite PMF probability strictly below one. -/
theorem pmfProb_lt_one_of_mass_not {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (a₀ : α)
    (hp : ¬p a₀) (hmass : 0 < (μ a₀).toReal) :
    pmfProb μ p < 1 := by
  classical
  have hcompl :
      0 < pmfProb μ (fun a => ¬p a) :=
    pmfProb_pos_of_mass μ (fun a => ¬p a) a₀ hp hmass
  rw [pmfProb_compl μ p] at hcompl
  linarith

/-- Monotonicity of finite PMF expectation. -/
theorem pmfExp_le_pmfExp_of_forall_le {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ)
    (h : ∀ a, f a ≤ g a) :
    pmfExp μ f ≤ pmfExp μ g := by
  unfold pmfExp
  exact Finset.sum_le_sum (by
    intro a _
    exact mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)

/-- Finite sums commute with finite PMF expectation. -/
theorem pmfExp_finset_sum {α ι : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (s : Finset ι) (f : ι → α → ℝ) :
    pmfExp μ (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, pmfExp μ (f i) := by
  unfold pmfExp
  calc
    ∑ a : α, (μ a).toReal * (∑ i ∈ s, f i a)
        = ∑ a : α, ∑ i ∈ s, (μ a).toReal * f i a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ a : α, (μ a).toReal * f i a := by
          exact Finset.sum_comm

/--
The capped function `min 1` is expectation-subadditive in the only form needed
for finite allocation caps: the expectation of a capped random variable is at
most the cap of its expectation.
-/
theorem pmfExp_min_one_le_min_one_pmfExp {α : Type*}
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) :
    pmfExp μ (fun a => min 1 (f a)) ≤ min 1 (pmfExp μ f) := by
  refine le_min ?_ ?_
  · exact pmfExp_le_of_forall_le μ (fun a => min 1 (f a)) 1
      (fun a => min_le_left 1 (f a))
  · unfold pmfExp
    exact Finset.sum_le_sum (by
      intro a _
      exact mul_le_mul_of_nonneg_left (min_le_right 1 (f a))
        ENNReal.toReal_nonneg)

/-- A finite PMF expectation is strictly above a constant if every value is. -/
theorem pmfExp_lt_of_forall_lt {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (μ : PMF α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a, c < f a) :
    c < pmfExp μ f := by
  classical
  have hpos_atom : ∃ a : α, 0 < (μ a).toReal := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ a : α, (μ a).toReal = 0 := by
      intro a
      exact le_antisymm (hnone a) ENNReal.toReal_nonneg
    have hsum_zero : ∑ a : α, (μ a).toReal = 0 := by
      simp [hzero]
    have hsum_one : ∑ a : α, (μ a).toReal = 1 := pmfToRealSum μ
    linarith
  rw [← pmfExp_const μ c]
  unfold pmfExp
  refine Finset.sum_lt_sum ?_ ?_
  · intro a _
    exact mul_le_mul_of_nonneg_left (le_of_lt (h a)) ENNReal.toReal_nonneg
  · rcases hpos_atom with ⟨a, ha⟩
    exact ⟨a, Finset.mem_univ a,
      mul_lt_mul_of_pos_left (h a) ha⟩

/--
A finite PMF expectation is strictly below a constant if every atom is at most
that constant and one positive-mass atom is strictly below it.
-/
theorem pmfExp_lt_of_forall_le_exists_lt {α : Type*}
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (c : ℝ)
    (hle : ∀ a, f a ≤ c)
    (hex : ∃ a, 0 < (μ a).toReal ∧ f a < c) :
    pmfExp μ f < c := by
  classical
  rw [← pmfExp_const μ c]
  unfold pmfExp
  refine Finset.sum_lt_sum ?_ ?_
  · intro a _
    exact mul_le_mul_of_nonneg_left (hle a) ENNReal.toReal_nonneg
  · rcases hex with ⟨a, hmass, hlt⟩
    exact ⟨a, Finset.mem_univ a,
      mul_lt_mul_of_pos_left hlt hmass⟩

/--
A finite PMF expectation is strictly below a constant when every positive-mass
atom is strictly below that constant. Zero-mass atoms may have arbitrary values.
-/
theorem pmfExp_lt_of_support_forall_lt {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (μ : PMF α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a, 0 < (μ a).toReal → f a < c) :
    pmfExp μ f < c := by
  classical
  let g : α → ℝ := fun a => if (μ a).toReal = 0 then c else f a
  have hfg : pmfExp μ f = pmfExp μ g := by
    unfold pmfExp g
    refine Finset.sum_congr rfl ?_
    intro a _ha
    by_cases hzero : (μ a).toReal = 0
    · simp [hzero]
    · simp [hzero]
  have hle : ∀ a, g a ≤ c := by
    intro a
    by_cases hzero : (μ a).toReal = 0
    · simp [g, hzero]
    · have hpos : 0 < (μ a).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
      exact le_of_lt (by simpa [g, hzero] using h a hpos)
  have hex : ∃ a, 0 < (μ a).toReal ∧ g a < c := by
    by_contra hnone
    push Not at hnone
    have hzero_all : ∀ a, (μ a).toReal = 0 := by
      intro a
      by_contra hzero
      have hpos : 0 < (μ a).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
      exact (not_lt_of_ge (hnone a hpos)) (by
        simpa [g, hzero] using h a hpos)
    have hsum_zero : ∑ a : α, (μ a).toReal = 0 := by
      simp [hzero_all]
    have hsum_one : ∑ a : α, (μ a).toReal = 1 := pmfToRealSum μ
    linarith
  rw [hfg]
  exact pmfExp_lt_of_forall_le_exists_lt μ g c hle hex

@[simp] theorem pmfExp_pure {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) (f : α → ℝ) :
    pmfExp (PMF.pure a) f = f a := by
  classical
  unfold pmfExp
  calc
    ∑ x : α, (PMF.pure a x).toReal * f x = ∑ x : α, if x = a then f a else 0 := by
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases h : x = a
      · subst h
        simp [PMF.pure_apply]
      · simp [PMF.pure_apply, h]
    _ = f a := by
      simp

/-- Linearity of independent-product expectation. -/
theorem pmfPairExp_add {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f g : α → β → ℝ) :
    pmfPairExp μ ν (fun a b => f a b + g a b) =
      pmfPairExp μ ν f + pmfPairExp μ ν g := by
  unfold pmfPairExp
  simp [pmfExp_add]

/-- Subtractive linearity of independent-product expectation. -/
theorem pmfPairExp_sub {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f g : α → β → ℝ) :
    pmfPairExp μ ν (fun a b => f a b - g a b) =
      pmfPairExp μ ν f - pmfPairExp μ ν g := by
  unfold pmfPairExp
  simp [pmfExp_sub]

/-- Swap the order of two finite independent PMF expectations. -/
theorem pmfPairExp_swap {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f : α → β → ℝ) :
    pmfPairExp μ ν f = pmfPairExp ν μ (fun b a => f a b) := by
  unfold pmfPairExp pmfExp
  calc
    ∑ a : α, (μ a).toReal * (∑ b : β, (ν b).toReal * f a b)
        = ∑ a : α, ∑ b : β,
            (μ a).toReal * ((ν b).toReal * f a b) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
    _ = ∑ a : α, ∑ b : β,
            (ν b).toReal * ((μ a).toReal * f a b) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro b _
          ring
    _ = ∑ b : β, ∑ a : α,
            (ν b).toReal * ((μ a).toReal * f a b) := by
          exact Finset.sum_comm
    _ = ∑ b : β, (ν b).toReal *
            (∑ a : α, (μ a).toReal * f a b) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.mul_sum]

@[simp] theorem pmfPairExp_zero {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) :
    pmfPairExp μ ν (fun _ _ => 0) = 0 := by
  unfold pmfPairExp
  simp

@[simp] theorem pmfPairExp_pure_left {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (a : α) (ν : PMF β) (f : α → β → ℝ) :
    pmfPairExp (PMF.pure a) ν f = pmfExp ν (fun b => f a b) := by
  unfold pmfPairExp
  simp

@[simp] theorem pmfPairExp_pure_right {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (b : β) (f : α → β → ℝ) :
    pmfPairExp μ (PMF.pure b) f = pmfExp μ (fun a => f a b) := by
  unfold pmfPairExp
  simp

end DecisionCore
