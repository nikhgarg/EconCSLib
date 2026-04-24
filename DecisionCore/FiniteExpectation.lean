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
