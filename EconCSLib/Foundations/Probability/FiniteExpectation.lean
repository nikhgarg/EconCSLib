import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace EconCSLib

/-- Finite expectation of a real-valued function under a PMF. -/
noncomputable def pmfExp {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (μ a).toReal * f a

/-- Expectation for two independent PMF draws. -/
noncomputable def pmfPairExp {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f : α → β → ℝ) : ℝ :=
  pmfExp μ (fun a => pmfExp ν (fun b => f a b))

/-- Independent finite product PMF with identical coordinate law. -/
noncomputable def pmfProduct (ι α : Type*) [Fintype ι] [DecidableEq ι] [Fintype α]
    (μ : PMF α) : PMF (ι → α) :=
  PMF.ofFintype (fun f : ι → α => ∏ i : ι, μ (f i)) (by
    classical
    have hcoord : ∑ a : α, μ a = 1 := by
      rw [← PMF.tsum_coe μ, tsum_fintype]
    calc
      ∑ f : ι → α, ∏ i : ι, μ (f i)
          = ∏ i : ι, ∑ a : α, μ a := by
            symm
            simpa using
              (Finset.prod_univ_sum
                (t := fun _i : ι => (Finset.univ : Finset α))
                (f := fun _i a => μ a))
      _ = 1 := by simp [hcoord])

@[simp] theorem pmfProduct_apply {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (μ : PMF α) (f : ι → α) :
    pmfProduct ι α μ f = ∏ i : ι, μ (f i) := by
  simp [pmfProduct]

@[simp] theorem pmfProduct_apply_toReal {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α]
    (μ : PMF α) (f : ι → α) :
    (pmfProduct ι α μ f).toReal = ∏ i : ι, (μ (f i)).toReal := by
  rw [pmfProduct_apply]
  simpa using
    (ENNReal.toReal_prod
      (s := (Finset.univ : Finset ι)) (f := fun i : ι => μ (f i)))

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

/-- Uniform finite expectation is invariant under an equivalence of finite types. -/
theorem pmfExp_uniformPMF_equiv {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α ≃ β) (f : β → ℝ) :
    pmfExp (uniformPMF β) f =
      pmfExp (uniformPMF α) (fun a => f (e a)) := by
  unfold pmfExp
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  calc
    ∑ b : β, (uniformPMF β b).toReal * f b =
        ∑ b : β, (Fintype.card β : ℝ)⁻¹ * f b := by
          simp
    _ = ∑ a : α, (Fintype.card β : ℝ)⁻¹ * f (e a) := by
          simpa using
            (Equiv.sum_comp e
              (fun b : β => (Fintype.card β : ℝ)⁻¹ * f b)).symm
    _ = ∑ a : α, (Fintype.card α : ℝ)⁻¹ * f (e a) := by
          simp [hcard]
    _ = ∑ a : α, (uniformPMF α a).toReal * f (e a) := by
          simp

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

/-- Finite PMF event probability is invariant under pointwise event equivalence. -/
theorem pmfProb_congr {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ a, p a ↔ q a) :
    pmfProb μ p = pmfProb μ q := by
  unfold pmfProb
  refine pmfExp_congr μ ?_
  intro a
  by_cases hp : p a
  · have hq : q a := (h a).1 hp
    simp [hp, hq]
  · have hq : ¬ q a := fun hqa => hp ((h a).2 hqa)
    simp [hp, hq]

/-- Event probabilities computed as finite PMF expectations are nonnegative. -/
theorem pmfProb_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    0 ≤ pmfProb μ p := by
  classical
  unfold pmfProb pmfExp
  refine Finset.sum_nonneg ?_
  intro a _
  exact mul_nonneg ENNReal.toReal_nonneg (by by_cases hp : p a <;> simp [hp])

/-- The probability of a singleton event is the atom mass. -/
theorem pmfProb_singleton
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (a : α) :
    pmfProb μ (fun x => x = a) = (μ a).toReal := by
  classical
  unfold pmfProb pmfExp
  calc
    (∑ x : α, (μ x).toReal * if x = a then (1 : ℝ) else 0)
        = (μ a).toReal * (if a = a then (1 : ℝ) else 0) := by
            refine Finset.sum_eq_single
              (s := (Finset.univ : Finset α)) (a := a)
              (f := fun x => (μ x).toReal * if x = a then (1 : ℝ) else 0) ?_ ?_
            · intro b _hb hba
              simp [hba]
            · intro ha
              simp at ha
    _ = (μ a).toReal := by simp

/--
For an independent finite product PMF with identical coordinate law, the
probability that every coordinate satisfies `p` is the corresponding one-point
probability raised to the number of coordinates.
-/
theorem pmfProduct_prob_forall
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    pmfProb (pmfProduct ι α μ) (fun f : ι → α => ∀ i : ι, p (f i)) =
      (pmfProb μ p) ^ Fintype.card ι := by
  classical
  have hpoint : ∀ f : ι → α,
      (pmfProduct ι α μ f).toReal *
          (if ∀ i : ι, p (f i) then (1 : ℝ) else 0) =
        ∏ i : ι, ((μ (f i)).toReal *
          (if p (f i) then (1 : ℝ) else 0)) := by
    intro f
    by_cases hall : ∀ i : ι, p (f i)
    · simp [hall]
    · have hnotall : ¬ ∀ i : ι, p (f i) := hall
      rcases not_forall.mp hnotall with ⟨i, hi⟩
      have hprod_zero :
          ∏ j : ι, (if p (f j) then (μ (f j)).toReal else 0) = 0 := by
        rw [Finset.prod_eq_zero (Finset.mem_univ i)]
        simp [hi]
      simp [hnotall, hprod_zero]
  unfold pmfProb pmfExp
  calc
    ∑ f : ι → α, (pmfProduct ι α μ f).toReal *
        (if ∀ i : ι, p (f i) then (1 : ℝ) else 0)
        = ∑ f : ι → α, ∏ i : ι, ((μ (f i)).toReal *
            (if p (f i) then (1 : ℝ) else 0)) := by
          exact Finset.sum_congr rfl (fun f _ => hpoint f)
    _ = ∏ i : ι, ∑ a : α,
          ((μ a).toReal * (if p a then (1 : ℝ) else 0)) := by
          symm
          simpa using
            (Finset.prod_univ_sum
              (t := fun _i : ι => (Finset.univ : Finset α))
              (f := fun _i a => (μ a).toReal *
                (if p a then (1 : ℝ) else 0)))
    _ = (∑ a : α, (μ a).toReal *
          (if p a then (1 : ℝ) else 0)) ^ Fintype.card ι := by
          simp [Finset.prod_const]

/--
Uniform finite probabilities are invariant under relabeling: if an event on
`β` pulled back along an equivalence is the event on `α`, then the two uniform
probabilities are equal.
-/
theorem pmfProb_uniformPMF_equiv {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α ≃ β) (p : β → Prop) (q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (h : ∀ a, p (e a) ↔ q a) :
    pmfProb (uniformPMF β) p =
      pmfProb (uniformPMF α) q := by
  classical
  unfold pmfProb
  calc
    pmfExp (uniformPMF β) (fun b => if p b then (1 : ℝ) else 0) =
        pmfExp (uniformPMF α)
          (fun a => if p (e a) then (1 : ℝ) else 0) :=
          pmfExp_uniformPMF_equiv e
            (fun b => if p b then (1 : ℝ) else 0)
    _ = pmfExp (uniformPMF α)
          (fun a => if q a then (1 : ℝ) else 0) := by
          refine pmfExp_congr (uniformPMF α) ?_
          intro a
          by_cases hp : p (e a)
          · have hq : q a := (h a).1 hp
            simp [hp, hq]
          · have hq : ¬ q a := fun hqa => hp ((h a).2 hqa)
            simp [hp, hq]

/--
Same-space version of `pmfProb_uniformPMF_equiv`: a finite uniform probability
is unchanged by a permutation of the sample space.
-/
theorem pmfProb_uniformPMF_eq_of_comp_equiv {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (e : α ≃ α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (h : ∀ a, p (e a) ↔ q a) :
    pmfProb (uniformPMF α) p =
      pmfProb (uniformPMF α) q :=
  pmfProb_uniformPMF_equiv e p q h

/--
Function-space event exchangeability under pointwise relabeling of the range.
This is useful for random finite lists, draw prefixes, and assignment-valued
sample spaces whose coordinates are uniformly and independently drawn from a
finite type.
-/
theorem pmfProb_uniformPMF_fun_range_relabel {ι α : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Nonempty α]
    (e : α ≃ α) (p q : (ι → α) → Prop)
    [DecidablePred p] [DecidablePred q]
    (h : ∀ f : ι → α, p (fun i => e (f i)) ↔ q f) :
    pmfProb (uniformPMF (ι → α)) p =
      pmfProb (uniformPMF (ι → α)) q := by
  classical
  let relabel : (ι → α) ≃ (ι → α) :=
    { toFun := fun f i => e (f i)
      invFun := fun f i => e.symm (f i)
      left_inv := by
        intro f
        funext i
        simp
      right_inv := by
        intro f
        funext i
        simp }
  exact pmfProb_uniformPMF_eq_of_comp_equiv relabel p q h

/-- Relabel the range of an injective finite function by an equivalence. -/
def injectiveFunRangeRelabelEquiv {ι α : Type*}
    (e : α ≃ α) :
    {f : ι → α // Function.Injective f} ≃
      {f : ι → α // Function.Injective f} where
  toFun f :=
    ⟨fun i => e (f.1 i), by
      intro i j h
      exact f.2 (e.injective h)⟩
  invFun f :=
    ⟨fun i => e.symm (f.1 i), by
      intro i j h
      exact f.2 (e.symm.injective h)⟩
  left_inv := by
    intro f
    ext i
    simp
  right_inv := by
    intro f
    ext i
    simp

/--
Uniform event exchangeability on ordered without-replacement samples, modeled
as injective finite functions, under pointwise relabeling of the range.
-/
theorem pmfProb_uniformPMF_injective_fun_range_relabel {ι α : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    [Nonempty {f : ι → α // Function.Injective f}]
    (e : α ≃ α)
    (p q : {f : ι → α // Function.Injective f} → Prop)
    [DecidablePred p] [DecidablePred q]
    (h : ∀ f : {f : ι → α // Function.Injective f},
      p (injectiveFunRangeRelabelEquiv e f) ↔ q f) :
    pmfProb (uniformPMF {f : ι → α // Function.Injective f}) p =
      pmfProb (uniformPMF {f : ι → α // Function.Injective f}) q :=
  pmfProb_uniformPMF_eq_of_comp_equiv
    (injectiveFunRangeRelabelEquiv e) p q h

/--
Linearity identity for finite random counts: the expected number of elements
satisfying an outcome-dependent predicate is the sum of their event
probabilities.
-/
theorem pmfExp_card_filter_eq_sum_pmfProb {Ω α : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype α] [DecidableEq α]
    (μ : PMF Ω) (p : Ω → α → Prop)
    [∀ ω, DecidablePred (p ω)]
    [∀ a, DecidablePred fun ω => p ω a] :
    pmfExp μ
        (fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ)) =
      ∑ a : α, pmfProb μ (fun ω => p ω a) := by
  classical
  have hcard :
      ∀ ω,
        (((Finset.univ : Finset α).filter (p ω)).card : ℝ) =
          ∑ a : α, if p ω a then (1 : ℝ) else 0 := by
    intro ω
    simp
  unfold pmfExp pmfProb
  calc
    ∑ ω : Ω, (μ ω).toReal *
        (((Finset.univ : Finset α).filter (p ω)).card : ℝ) =
        ∑ ω : Ω, (μ ω).toReal *
          (∑ a : α, if p ω a then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [hcard ω]
    _ = ∑ ω : Ω, ∑ a : α,
          (μ ω).toReal * (if p ω a then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [Finset.mul_sum]
    _ = ∑ a : α, ∑ ω : Ω,
          (μ ω).toReal * (if p ω a then (1 : ℝ) else 0) := by
          exact Finset.sum_comm

end EconCSLib

namespace EconCSLib

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

/-- Finite PMF expectation is monotone under pointwise comparison. -/
theorem pmfExp_le_pmfExp_of_forall_le {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f g : α → ℝ) (h : ∀ a, f a ≤ g a) :
    pmfExp μ f ≤ pmfExp μ g := by
  unfold pmfExp
  exact Finset.sum_le_sum (by
    intro a _
    exact mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)

/-- Expectation of the reciprocal successor of a natural-valued finite random variable. -/
noncomputable def pmfExpReciprocalSucc {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℕ) : ℝ :=
  pmfExp μ (fun a => (((X a + 1 : ℕ) : ℝ)⁻¹))

theorem reciprocal_succ_nat_antitone {x y : ℕ} (hxy : x ≤ y) :
    ((((y + 1 : ℕ) : ℝ)⁻¹) ≤ (((x + 1 : ℕ) : ℝ)⁻¹)) := by
  have hxpos : 0 < ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos x
  have hypos : 0 < ((y + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos y
  have hle : ((x + 1 : ℕ) : ℝ) ≤ ((y + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hxy
  exact (inv_le_inv₀ hypos hxpos).mpr hle

theorem pmfExpReciprocalSucc_mono_of_forall_ge
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X Y : α → ℕ)
    (hge : ∀ a, Y a ≤ X a) :
    pmfExpReciprocalSucc μ X ≤ pmfExpReciprocalSucc μ Y := by
  unfold pmfExpReciprocalSucc
  refine pmfExp_le_pmfExp_of_forall_le μ _ _ ?_
  intro a
  exact reciprocal_succ_nat_antitone (hge a)

theorem pmfExpReciprocalSucc_congr
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X Y : α → ℕ)
    (heq : ∀ a, X a = Y a) :
    pmfExpReciprocalSucc μ X = pmfExpReciprocalSucc μ Y := by
  unfold pmfExpReciprocalSucc
  exact pmfExp_congr μ (by intro a; simp [heq a])

/--
If two natural-valued finite random variables agree on a good event, then their
reciprocal-successor expectations differ by at most the probability of the bad
event.  The pointwise loss is bounded by `1`.
-/
theorem pmfExpReciprocalSucc_le_add_prob_of_eq_on_event
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X Y : α → ℕ) (good : α → Prop) [DecidablePred good]
    (heq : ∀ a, good a → X a = Y a) :
    pmfExpReciprocalSucc μ X ≤
      pmfExpReciprocalSucc μ Y + pmfProb μ (fun a => ¬ good a) := by
  have hpoint :
      ∀ a,
        (((X a + 1 : ℕ) : ℝ)⁻¹) ≤
          (((Y a + 1 : ℕ) : ℝ)⁻¹) +
            (if ¬ good a then (1 : ℝ) else 0) := by
    intro a
    by_cases hg : good a
    · have hxy : X a = Y a := heq a hg
      simp [hg, hxy]
    · have hx_le_one :
          (((X a + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
        simpa using
          (reciprocal_succ_nat_antitone (x := 0) (y := X a)
            (Nat.zero_le (X a)))
      have hypos : 0 < ((Y a + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos (Y a)
      have hy_nonneg : 0 ≤ (((Y a + 1 : ℕ) : ℝ)⁻¹) :=
        le_of_lt (inv_pos.mpr hypos)
      have hone_le : (1 : ℝ) ≤ (((Y a + 1 : ℕ) : ℝ)⁻¹) + 1 := by
        simpa using add_le_add_right hy_nonneg 1
      exact le_trans hx_le_one (by simpa [hg] using hone_le)
  unfold pmfExpReciprocalSucc
  calc
    pmfExp μ (fun a => (((X a + 1 : ℕ) : ℝ)⁻¹)) ≤
        pmfExp μ
          (fun a =>
            (((Y a + 1 : ℕ) : ℝ)⁻¹) +
              (if ¬ good a then (1 : ℝ) else 0)) :=
          pmfExp_le_pmfExp_of_forall_le μ _ _ hpoint
    _ = pmfExp μ (fun a => (((Y a + 1 : ℕ) : ℝ)⁻¹)) +
          pmfExp μ (fun a => if ¬ good a then (1 : ℝ) else 0) := by
          exact pmfExp_add μ
            (fun a => (((Y a + 1 : ℕ) : ℝ)⁻¹))
            (fun a => if ¬ good a then (1 : ℝ) else 0)
    _ = pmfExp μ (fun a => (((Y a + 1 : ℕ) : ℝ)⁻¹)) +
          pmfProb μ (fun a => ¬ good a) := by
          rfl

/--
Uniform expectation on a product is the corresponding nested independent
uniform expectation.
-/
theorem pmfExp_uniformPMF_prod {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α × β → ℝ) :
    pmfExp (uniformPMF (α × β)) f =
      pmfPairExp (uniformPMF α) (uniformPMF β)
        (fun a b => f (a, b)) := by
  unfold pmfPairExp pmfExp
  classical
  calc
    ∑ p : α × β, (uniformPMF (α × β) p).toReal * f p =
        ∑ p : α × β,
          ((Fintype.card α : ℝ)⁻¹ * (Fintype.card β : ℝ)⁻¹) * f p := by
          refine Finset.sum_congr rfl ?_
          intro p _
          rw [uniformPMF_apply_toReal, Fintype.card_prod]
          have hα : (Fintype.card α : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
          have hβ : (Fintype.card β : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty β›).ne'
          field_simp [hα, hβ]
          rw [Nat.cast_mul]
          ring
    _ = ∑ a : α, ∑ b : β,
          ((Fintype.card α : ℝ)⁻¹ * (Fintype.card β : ℝ)⁻¹) *
            f (a, b) := by
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product'
              (s := (Finset.univ : Finset α))
              (t := (Finset.univ : Finset β))
              (f := fun a b =>
                ((Fintype.card α : ℝ)⁻¹ *
                    (Fintype.card β : ℝ)⁻¹) * f (a, b)))
    _ = ∑ a : α, (uniformPMF α a).toReal *
          (∑ b : β, (uniformPMF β b).toReal * f (a, b)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [uniformPMF_apply_toReal, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [uniformPMF_apply_toReal]
          ring

/-- Under the uniform PMF, a finite event has probability `card(event)/card(space)`. -/
theorem pmfProb_uniformPMF_finset {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (s : Finset α) :
    pmfProb (uniformPMF α) (fun a => a ∈ s) =
      (s.card : ℝ) / (Fintype.card α : ℝ) := by
  classical
  unfold pmfProb pmfExp
  calc
    ∑ a : α, (uniformPMF α a).toReal *
        (if a ∈ s then (1 : ℝ) else 0) =
        ∑ a : α, (Fintype.card α : ℝ)⁻¹ *
          (if a ∈ s then (1 : ℝ) else 0) := by
          simp
    _ = ∑ a : α, if a ∈ s then (Fintype.card α : ℝ)⁻¹ else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases ha : a ∈ s <;> simp [ha]
    _ = Finset.sum ((Finset.univ : Finset α).filter (fun a => a ∈ s))
          (fun _ => (Fintype.card α : ℝ)⁻¹) := by
          rw [Finset.sum_filter]
    _ = (s.card : ℝ) * (Fintype.card α : ℝ)⁻¹ := by
          have hfilter :
              (Finset.univ : Finset α).filter (fun a => a ∈ s) = s := by
            ext a
            simp
          rw [hfilter, Finset.sum_const, nsmul_eq_mul]
    _ = (s.card : ℝ) / (Fintype.card α : ℝ) := by
          rw [div_eq_mul_inv]

/--
Constant finite fiber cardinalities compose: if every fiber of `f` has size
`fiberF` and every fiber of `g` has size `fiberG`, then every fiber of
`g ∘ f` has size `fiberF * fiberG`.
-/
theorem finite_constant_fiber_card_comp
    {α β γ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (f : α → β) (g : β → γ)
    (fiberF fiberG : ℕ)
    (hfiber_f : ∀ b : β,
      ((Finset.univ : Finset α).filter fun a => f a = b).card =
        fiberF)
    (hfiber_g : ∀ c : γ,
      ((Finset.univ : Finset β).filter fun b => g b = c).card =
        fiberG)
    (c : γ) :
    ((Finset.univ : Finset α).filter fun a => g (f a) = c).card =
      fiberF * fiberG := by
  classical
  let source : Finset α :=
    (Finset.univ : Finset α).filter fun a => g (f a) = c
  let middle : Finset β :=
    (Finset.univ : Finset β).filter fun b => g b = c
  have hmaps : ∀ a ∈ source, f a ∈ middle := by
    intro a ha
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  calc
    ((Finset.univ : Finset α).filter fun a => g (f a) = c).card =
        source.card := rfl
    _ = ∑ b ∈ middle, ((source.filter fun a => f a = b).card) := by
        exact Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ _b ∈ middle, fiberF := by
        refine Finset.sum_congr rfl ?_
        intro b hb
        have hgb : g b = c := (Finset.mem_filter.mp hb).2
        have hfiber_event :
            source.filter (fun a => f a = b) =
              (Finset.univ : Finset α).filter fun a => f a = b := by
          ext a
          by_cases hfb : f a = b
          · simp [source, hfb, hgb]
          · simp [source, hfb]
        rw [hfiber_event, hfiber_f b]
    _ = fiberF * middle.card := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact Nat.mul_comm middle.card fiberF
    _ = fiberF * fiberG := by
        rw [show middle.card = fiberG from hfiber_g c]

/--
Post-composing a finite map with an equivalence preserves constant fiber
cardinality.
-/
theorem finite_constant_fiber_card_equiv_comp
    {α β γ : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (f : α → β) (e : β ≃ γ) (fiberCard : ℕ)
    (hfiber : ∀ b : β,
      ((Finset.univ : Finset α).filter fun a => f a = b).card =
        fiberCard)
    (c : γ) :
    ((Finset.univ : Finset α).filter fun a => e (f a) = c).card =
      fiberCard := by
  classical
  have hfilter :
      ((Finset.univ : Finset α).filter fun a => e (f a) = c) =
        ((Finset.univ : Finset α).filter fun a => f a = e.symm c) := by
    ext a
    constructor
    · intro ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨ha.1, by simpa using congrArg e.symm ha.2⟩
    · intro ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨ha.1, by simpa using congrArg e ha.2⟩
  rw [hfilter, hfiber]

/-- The identity map on a finite type has singleton fibers. -/
theorem finite_id_fiber_card
    {α : Type*} [Fintype α] [DecidableEq α] (a₀ : α) :
    ((Finset.univ : Finset α).filter fun a => a = a₀).card = 1 := by
  classical
  have hfilter :
      ((Finset.univ : Finset α).filter fun a => a = a₀) =
        ({a₀} : Finset α) := by
    ext a
    simp
  rw [hfilter]
  simp

/-- Every fiber of an equivalence between finite types has cardinality one. -/
theorem finite_equiv_fiber_card
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β) (b : β) :
    ((Finset.univ : Finset α).filter fun a => e a = b).card = 1 := by
  classical
  exact
    finite_constant_fiber_card_equiv_comp
      (fun a : α => a) e 1
      (fun a => finite_id_fiber_card a) b

/--
If every fiber of a finite map has the same positive cardinality, then pushing
the uniform law through that map gives the uniform law on the codomain, stated
as equality of event probabilities.
-/
theorem pmfProb_uniformPMF_comp_eq_of_constant_fiber_card
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β) (fiberCard : ℕ) (hfiber_pos : 0 < fiberCard)
    (hfiber : ∀ b : β,
      ((Finset.univ : Finset α).filter fun a => f a = b).card =
        fiberCard)
    (p : β → Prop) [DecidablePred p] :
    pmfProb (uniformPMF α) (fun a => p (f a)) =
      pmfProb (uniformPMF β) p := by
  classical
  let sourceEvent : Finset α :=
    (Finset.univ : Finset α).filter fun a => p (f a)
  let targetEvent : Finset β :=
    (Finset.univ : Finset β).filter fun b => p b
  have hsource_card :
      sourceEvent.card = fiberCard * targetEvent.card := by
    have hmaps : ∀ a ∈ sourceEvent, f a ∈ targetEvent := by
      intro a ha
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
    calc
      sourceEvent.card =
          ∑ b ∈ targetEvent,
            ((sourceEvent.filter fun a => f a = b).card) := by
            exact Finset.card_eq_sum_card_fiberwise hmaps
      _ = ∑ _b ∈ targetEvent, fiberCard := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            have hp : p b := (Finset.mem_filter.mp hb).2
            have hfiber_event :
                sourceEvent.filter (fun a => f a = b) =
                  (Finset.univ : Finset α).filter fun a => f a = b := by
              ext a
              by_cases hfb : f a = b
              · simp [sourceEvent, hfb, hp]
              · simp [sourceEvent, hfb]
            rw [hfiber_event, hfiber b]
      _ = fiberCard * targetEvent.card := by
            rw [Finset.sum_const, nsmul_eq_mul]
            exact Nat.mul_comm targetEvent.card fiberCard
  have htotal_card :
      Fintype.card α = fiberCard * Fintype.card β := by
    have hmaps : ∀ a ∈ (Finset.univ : Finset α),
        f a ∈ (Finset.univ : Finset β) := by
      intro a _ha
      exact Finset.mem_univ _
    calc
      Fintype.card α =
          (Finset.univ : Finset α).card := by simp
      _ = ∑ b : β,
            (((Finset.univ : Finset α).filter fun a => f a = b).card) := by
            simpa using
              (Finset.card_eq_sum_card_fiberwise
                (s := (Finset.univ : Finset α))
                (t := (Finset.univ : Finset β))
                (f := f) hmaps)
      _ = ∑ _b : β, fiberCard := by
            refine Finset.sum_congr rfl ?_
            intro b _hb
            exact hfiber b
      _ = fiberCard * Fintype.card β := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            exact Nat.mul_comm (Fintype.card β) fiberCard
  have hsource_prob :
      pmfProb (uniformPMF α) (fun a => p (f a)) =
        (sourceEvent.card : ℝ) / (Fintype.card α : ℝ) := by
    simpa [sourceEvent] using
      (pmfProb_uniformPMF_finset (α := α) sourceEvent)
  have htarget_prob :
      pmfProb (uniformPMF β) p =
        (targetEvent.card : ℝ) / (Fintype.card β : ℝ) := by
    simpa [targetEvent] using
      (pmfProb_uniformPMF_finset (α := β) targetEvent)
  rw [hsource_prob, htarget_prob]
  have hfiber_ne_real : (fiberCard : ℝ) ≠ 0 := by
    exact_mod_cast hfiber_pos.ne'
  have hcard_beta_pos : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty β›).ne'
  rw [hsource_card, htotal_card]
  norm_num [Nat.cast_mul]
  field_simp [hfiber_ne_real, hcard_beta_pos]

/-- Under the uniform PMF, a singleton atom has probability `1 / #space`. -/
theorem pmfProb_uniformPMF_singleton {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (a₀ : α) :
    pmfProb (uniformPMF α) (fun a => a = a₀) =
      (Fintype.card α : ℝ)⁻¹ := by
  classical
  calc
    pmfProb (uniformPMF α) (fun a => a = a₀) =
        pmfProb (uniformPMF α) (fun a => a ∈ ({a₀} : Finset α)) := by
          unfold pmfProb
          refine pmfExp_congr (uniformPMF α) ?_
          intro a
          by_cases h : a = a₀ <;> simp [h]
    _ = (({a₀} : Finset α).card : ℝ) / (Fintype.card α : ℝ) :=
        pmfProb_uniformPMF_finset ({a₀} : Finset α)
    _ = (Fintype.card α : ℝ)⁻¹ := by
          simp [div_eq_mul_inv]

/--
For a uniform draw from a finite product, the probability that the left
coordinate equals a prescribed value is `1 / #left`.
-/
theorem pmfProb_uniformPMF_prod_fst_eq {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (a₀ : α) :
    pmfProb (uniformPMF (α × β)) (fun p : α × β => p.1 = a₀) =
      (Fintype.card α : ℝ)⁻¹ := by
  classical
  unfold pmfProb
  rw [pmfExp_uniformPMF_prod]
  change
    pmfPairExp (uniformPMF α) (uniformPMF β)
        (fun a _ => if a = a₀ then (1 : ℝ) else 0) =
      (Fintype.card α : ℝ)⁻¹
  calc
    pmfPairExp (uniformPMF α) (uniformPMF β)
        (fun a _ => if a = a₀ then (1 : ℝ) else 0) =
        pmfExp (uniformPMF α)
          (fun a => if a = a₀ then (1 : ℝ) else 0) := by
          unfold pmfPairExp
          simp
    _ = (Fintype.card α : ℝ)⁻¹ :=
          pmfProb_uniformPMF_singleton a₀

/--
For a uniform draw from a finite product, an event depending only on the left
coordinate has the same probability as that event under the left-coordinate
uniform draw.
-/
theorem pmfProb_uniformPMF_prod_fst_event {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (p : α → Prop) [DecidablePred p] :
    pmfProb (uniformPMF (α × β)) (fun x : α × β => p x.1) =
      pmfProb (uniformPMF α) p := by
  classical
  calc
    pmfProb (uniformPMF (α × β)) (fun x : α × β => p x.1) =
        pmfPairExp (uniformPMF α) (uniformPMF β)
          (fun a _ => if p a then (1 : ℝ) else 0) := by
          unfold pmfProb
          rw [pmfExp_uniformPMF_prod]
    _ = pmfExp (uniformPMF α)
          (fun a => if p a then (1 : ℝ) else 0) := by
          simp
    _ = pmfProb (uniformPMF α) p := by
          rfl

/--
For two independent uniform coordinates, the probability of a prescribed pair
of values is the product of the coordinate atom probabilities.
-/
theorem pmfProb_uniformPMF_prod_eq_pair {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (a₀ : α) (b₀ : β) :
    pmfProb (uniformPMF (α × β))
        (fun p : α × β => p.1 = a₀ ∧ p.2 = b₀) =
      (Fintype.card α : ℝ)⁻¹ * (Fintype.card β : ℝ)⁻¹ := by
  classical
  calc
    pmfProb (uniformPMF (α × β))
        (fun p : α × β => p.1 = a₀ ∧ p.2 = b₀) =
        pmfProb (uniformPMF (α × β)) (fun p : α × β => p = (a₀, b₀)) := by
          unfold pmfProb
          refine pmfExp_congr (uniformPMF (α × β)) ?_
          intro p
          cases p
          simp
    _ = (Fintype.card (α × β) : ℝ)⁻¹ :=
        pmfProb_uniformPMF_singleton (α := α × β) (a₀, b₀)
    _ = (Fintype.card α : ℝ)⁻¹ * (Fintype.card β : ℝ)⁻¹ := by
          rw [Fintype.card_prod, Nat.cast_mul]
          have hα : (Fintype.card α : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
          have hβ : (Fintype.card β : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty β›).ne'
          field_simp [hα, hβ]

/--
For a uniformly drawn finite function, two distinct coordinates hit prescribed
values with probability `1 / #values ^ 2`.
-/
theorem pmfProb_uniformPMF_fun_eq_pair_of_ne {ι α : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Nonempty α]
    {i j : ι} (hij : i ≠ j) (a₀ b₀ : α) :
    pmfProb (uniformPMF (ι → α))
        (fun f : ι → α => f i = a₀ ∧ f j = b₀) =
      (Fintype.card α : ℝ)⁻¹ ^ 2 := by
  classical
  let Rest := {x : ι // x ≠ i ∧ x ≠ j}
  let e : (ι → α) ≃ ((α × α) × (Rest → α)) :=
    { toFun := fun f => ((f i, f j), fun x => f x.1)
      invFun := fun p x =>
        if hi : x = i then p.1.1
        else if hj : x = j then p.1.2
        else p.2 ⟨x, hi, hj⟩
      left_inv := by
        intro f
        funext x
        by_cases hi : x = i
        · subst x
          simp
        · by_cases hj : x = j
          · subst x
            simp [hij.symm]
          · simp [hi, hj]
      right_inv := by
        intro p
        rcases p with ⟨⟨a, b⟩, rest⟩
        apply Prod.ext
        · apply Prod.ext
          · simp
          · simp [hij.symm]
        · funext x
          simp [x.property.1, x.property.2] }
  let targetPred : ((α × α) × (Rest → α)) → Prop :=
    fun p => p.1 = (a₀, b₀)
  have hsource :
      pmfProb (uniformPMF (ι → α))
          (fun f : ι → α => f i = a₀ ∧ f j = b₀) =
        pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred := by
    unfold pmfProb
    symm
    calc
      pmfExp (uniformPMF ((α × α) × (Rest → α)))
          (fun p => if targetPred p then (1 : ℝ) else 0) =
          pmfExp (uniformPMF (ι → α))
            (fun f => if targetPred (e f) then (1 : ℝ) else 0) :=
            pmfExp_uniformPMF_equiv e
              (fun p : (α × α) × (Rest → α) =>
                if targetPred p then (1 : ℝ) else 0)
      _ = pmfExp (uniformPMF (ι → α))
            (fun f => if f i = a₀ ∧ f j = b₀ then (1 : ℝ) else 0) := by
            refine pmfExp_congr (uniformPMF (ι → α)) ?_
            intro f
            simp [targetPred, e]
  have htarget :
      pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred =
        (Fintype.card (α × α) : ℝ)⁻¹ := by
    simpa [targetPred] using
      (pmfProb_uniformPMF_prod_fst_eq
        (α := α × α) (β := Rest → α) (a₀ := (a₀, b₀)))
  calc
    pmfProb (uniformPMF (ι → α))
        (fun f : ι → α => f i = a₀ ∧ f j = b₀) =
        pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred := hsource
    _ = (Fintype.card (α × α) : ℝ)⁻¹ := htarget
    _ = (Fintype.card α : ℝ)⁻¹ ^ 2 := by
          rw [Fintype.card_prod, Nat.cast_mul]
          have hα : (Fintype.card α : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
          field_simp [hα]

/--
For two independent uniform coordinates on the same finite type, the collision
probability is `1 / #space`.
-/
theorem pmfProb_uniformPMF_prod_eq_diag {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] :
    pmfProb (uniformPMF (α × α)) (fun p : α × α => p.1 = p.2) =
      (Fintype.card α : ℝ)⁻¹ := by
  classical
  let diag : Finset (α × α) :=
    (Finset.univ : Finset α).image fun a => (a, a)
  have hdiag_mem : ∀ p : α × α, p ∈ diag ↔ p.1 = p.2 := by
    intro p
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨a, _ha, hpa⟩
      rw [← hpa]
    · intro hp
      rcases p with ⟨a, b⟩
      simp at hp
      subst b
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hdiag_card : diag.card = Fintype.card α := by
    simpa [diag] using
      (Finset.card_image_of_injective
        (s := (Finset.univ : Finset α))
        (f := fun a : α => (a, a))
        (by
          intro a b h
          exact Prod.ext_iff.mp h |>.1))
  calc
    pmfProb (uniformPMF (α × α)) (fun p : α × α => p.1 = p.2) =
        pmfProb (uniformPMF (α × α)) (fun p : α × α => p ∈ diag) := by
          unfold pmfProb
          refine pmfExp_congr (uniformPMF (α × α)) ?_
          intro p
          by_cases hp : p.1 = p.2 <;> simp [hp, hdiag_mem p]
    _ = (diag.card : ℝ) / (Fintype.card (α × α) : ℝ) :=
        pmfProb_uniformPMF_finset diag
    _ = (Fintype.card α : ℝ)⁻¹ := by
          rw [hdiag_card, Fintype.card_prod, Nat.cast_mul]
          have hα : (Fintype.card α : ℝ) ≠ 0 := by
            exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
          field_simp [hα]

/--
For a uniformly drawn finite function, two distinct coordinates collide with
probability `1 / #values`.
-/
theorem pmfProb_uniformPMF_fun_eq_of_ne {ι α : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Nonempty α]
    {i j : ι} (hij : i ≠ j) :
    pmfProb (uniformPMF (ι → α))
        (fun f : ι → α => f i = f j) =
      (Fintype.card α : ℝ)⁻¹ := by
  classical
  let Rest := {x : ι // x ≠ i ∧ x ≠ j}
  let e : (ι → α) ≃ ((α × α) × (Rest → α)) :=
    { toFun := fun f => ((f i, f j), fun x => f x.1)
      invFun := fun p x =>
        if hi : x = i then p.1.1
        else if hj : x = j then p.1.2
        else p.2 ⟨x, hi, hj⟩
      left_inv := by
        intro f
        funext x
        by_cases hi : x = i
        · subst x
          simp
        · by_cases hj : x = j
          · subst x
            simp [hij.symm]
          · simp [hi, hj]
      right_inv := by
        intro p
        rcases p with ⟨⟨a, b⟩, rest⟩
        apply Prod.ext
        · apply Prod.ext
          · simp
          · simp [hij.symm]
        · funext x
          simp [x.property.1, x.property.2] }
  let targetPred : ((α × α) × (Rest → α)) → Prop :=
    fun p => p.1.1 = p.1.2
  have hsource :
      pmfProb (uniformPMF (ι → α))
          (fun f : ι → α => f i = f j) =
        pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred := by
    unfold pmfProb
    symm
    calc
      pmfExp (uniformPMF ((α × α) × (Rest → α)))
          (fun p => if targetPred p then (1 : ℝ) else 0) =
          pmfExp (uniformPMF (ι → α))
            (fun f => if targetPred (e f) then (1 : ℝ) else 0) :=
            pmfExp_uniformPMF_equiv e
              (fun p : (α × α) × (Rest → α) =>
                if targetPred p then (1 : ℝ) else 0)
      _ = pmfExp (uniformPMF (ι → α))
            (fun f => if f i = f j then (1 : ℝ) else 0) := by
            refine pmfExp_congr (uniformPMF (ι → α)) ?_
            intro f
            simp [targetPred, e]
  have htarget :
      pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred =
        (Fintype.card α : ℝ)⁻¹ := by
    calc
      pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred =
          pmfProb (uniformPMF (α × α))
            (fun p : α × α => p.1 = p.2) := by
            exact pmfProb_uniformPMF_prod_fst_event
              (α := α × α) (β := Rest → α)
              (fun p : α × α => p.1 = p.2)
      _ = (Fintype.card α : ℝ)⁻¹ :=
          pmfProb_uniformPMF_prod_eq_diag
  calc
    pmfProb (uniformPMF (ι → α))
        (fun f : ι → α => f i = f j) =
        pmfProb (uniformPMF ((α × α) × (Rest → α))) targetPred := hsource
    _ = (Fintype.card α : ℝ)⁻¹ := htarget

/--
Lower-bound an expected finite count from a finite subfamily whose elementwise
event probabilities are uniformly bounded below.
-/
theorem pmfExp_card_filter_ge_card_mul_of_forall_mem_prob_ge
    {Ω α : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype α] [DecidableEq α]
    (μ : PMF Ω) (p : Ω → α → Prop)
    [∀ ω, DecidablePred (p ω)]
    [∀ a, DecidablePred fun ω => p ω a]
    (s : Finset α) (rate : ℝ)
    (_hrate_nonneg : 0 ≤ rate)
    (hprob : ∀ a ∈ s, rate ≤ pmfProb μ (fun ω => p ω a)) :
    (s.card : ℝ) * rate ≤
      pmfExp μ
        (fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ)) := by
  classical
  have htail_le_sum :
      (s.card : ℝ) * rate ≤
        ∑ a ∈ s, pmfProb μ (fun ω => p ω a) := by
    calc
      (s.card : ℝ) * rate = ∑ _a ∈ s, rate := by
          simp [nsmul_eq_mul]
      _ ≤ ∑ a ∈ s, pmfProb μ (fun ω => p ω a) :=
          Finset.sum_le_sum (by
            intro a ha
            exact hprob a ha)
  have htail_sum_le_univ :
      (∑ a ∈ s, pmfProb μ (fun ω => p ω a)) ≤
        ∑ a : α, pmfProb μ (fun ω => p ω a) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro a _ha
        simp)
      (fun a _ha _hnot => by
        unfold pmfProb pmfExp
        refine Finset.sum_nonneg ?_
        intro ω _
        exact mul_nonneg ENNReal.toReal_nonneg
          (by by_cases hp : p ω a <;> simp [hp]))
  calc
    (s.card : ℝ) * rate ≤
        ∑ a ∈ s, pmfProb μ (fun ω => p ω a) := htail_le_sum
    _ ≤ ∑ a : α, pmfProb μ (fun ω => p ω a) := htail_sum_le_univ
    _ =
        pmfExp μ
          (fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ)) := by
          exact (pmfExp_card_filter_eq_sum_pmfProb μ p).symm

/-- Finite PMF event probability is zero iff the event has no positive-mass witness. -/
theorem pmfProb_eq_zero_of_no_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (hzero : ∀ a, p a → (μ a).toReal = 0) :
    pmfProb μ p = 0 := by
  unfold pmfProb pmfExp
  exact Finset.sum_eq_zero (by
    intro a _
    by_cases hp : p a
    · simp [hp, hzero a hp]
    · simp [hp])

/-- Finite PMF event probability is positive iff some positive-mass atom satisfies it. -/
theorem pmfProb_pos_iff_exists_pos_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    0 < pmfProb μ p ↔ ∃ a, p a ∧ 0 < (μ a).toReal := by
  constructor
  · intro hpos
    by_contra hno
    have hzero : ∀ a, p a → (μ a).toReal = 0 := by
      intro a ha
      have hnot : ¬ 0 < (μ a).toReal := by
        intro hmass
        exact hno ⟨a, ha, hmass⟩
      exact le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
    rw [pmfProb_eq_zero_of_no_mass μ p hzero] at hpos
    exact (lt_irrefl 0 hpos)
  · rintro ⟨a, ha, hmass⟩
    have hnonneg : ∀ b : α, 0 ≤ (μ b).toReal * (if p b then (1 : ℝ) else 0) := by
      intro b
      by_cases hp : p b <;> simp [hp, ENNReal.toReal_nonneg]
    have hsingle_pos : 0 < (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
      simpa [ha] using hmass
    have hsingle_le :
        (μ a).toReal * (if p a then (1 : ℝ) else 0) ≤
          ∑ b : α, (μ b).toReal * (if p b then (1 : ℝ) else 0) :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset α))
        (f := fun b : α => (μ b).toReal * (if p b then (1 : ℝ) else 0))
        (by intro b _; exact hnonneg b)
        (Finset.mem_univ a)
    have hsum_pos : 0 < ∑ b : α, (μ b).toReal * (if p b then (1 : ℝ) else 0) :=
      lt_of_lt_of_le hsingle_pos hsingle_le
    unfold pmfProb pmfExp
    exact hsum_pos

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

/--
If a target atom is identified with the probability of a finite preimage event,
then a positive-mass source point in that preimage makes the target atom
positive.
-/
theorem pmf_apply_toReal_pos_of_pmfProb_preimage
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF β) (ν : PMF α) (f : α → β)
    (hpreimage : ∀ b, (μ b).toReal = pmfProb ν (fun a => f a = b))
    {a₀ : α} {b : β}
    (hf : f a₀ = b) (hmass : 0 < (ν a₀).toReal) :
    0 < (μ b).toReal := by
  rw [hpreimage b]
  exact pmfProb_pos_of_mass ν (fun a => f a = b) a₀ hf hmass

/--
If every target atom is identified with the probability of its finite preimage,
then every target event has probability equal to the probability of its
preimage.
-/
theorem pmfProb_eq_pmfProb_preimage_of_atom_eq
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF β) (ν : PMF α) (f : α → β)
    (hatom : ∀ b, (μ b).toReal = pmfProb ν (fun a => f a = b))
    (p : β → Prop) [DecidablePred p] :
    pmfProb μ p = pmfProb ν (fun a => p (f a)) := by
  classical
  unfold pmfProb pmfExp
  calc
    ∑ b : β, (μ b).toReal * (if p b then (1 : ℝ) else 0)
        = ∑ b : β,
            (∑ a : α, (ν a).toReal * (if f a = b then (1 : ℝ) else 0)) *
              (if p b then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [hatom b]
          rfl
    _ = ∑ b : β, ∑ a : α,
            ((ν a).toReal * (if f a = b then (1 : ℝ) else 0)) *
              (if p b then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_mul]
    _ = ∑ a : α, ∑ b : β,
            ((ν a).toReal * (if f a = b then (1 : ℝ) else 0)) *
              (if p b then (1 : ℝ) else 0) := by
          exact Finset.sum_comm
    _ = ∑ a : α, (ν a).toReal * (if p (f a) then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases hp : p (f a)
          · rw [Finset.sum_eq_single (f a)]
            · simp [hp]
            · intro b _ hb
              by_cases hfb : f a = b
              · exact False.elim (hb hfb.symm)
              · simp [hfb]
            · intro hnot
              exact False.elim (hnot (Finset.mem_univ (f a)))
          · rw [Finset.sum_eq_zero]
            · simp [hp]
            · intro b _
              by_cases hfb : f a = b
              · have hpb : ¬ p b := by simpa [hfb] using hp
                simp [hfb, hpb]
              · simp [hfb]

/-- Finite PMF event probability as the real value of the PMF outer measure. -/
theorem pmfProb_eq_toOuterMeasure_toReal
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    pmfProb μ p = (μ.toOuterMeasure {a | p a}).toReal := by
  classical
  unfold pmfProb pmfExp
  have h_ne_top :
      ∀ a ∈ (Finset.univ : Finset α),
        Set.indicator {a | p a} μ a ≠ ⊤ := by
    intro a _
    by_cases hp : p a
    · simpa [Set.indicator, hp] using μ.apply_ne_top a
    · simp [Set.indicator, hp]
  calc
    ∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0)
        = ∑ a : α, (Set.indicator {a | p a} μ a).toReal := by
          refine Finset.sum_congr rfl ?_
          intro a _
          by_cases hp : p a
          · simp [Set.indicator, hp]
          · simp [Set.indicator, hp]
    _ = (∑ a : α, Set.indicator {a | p a} μ a).toReal := by
          symm
          simpa using (ENNReal.toReal_sum (s := (Finset.univ : Finset α))
            (f := fun a => Set.indicator {a | p a} μ a) h_ne_top)
    _ = (μ.toOuterMeasure {a | p a}).toReal := by
          rw [PMF.toOuterMeasure_apply_fintype]

/-- The atom mass of a finite PMF pushforward is the probability of the preimage atom. -/
theorem pmf_map_apply_toReal_eq_pmfProb_preimage
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ν : PMF α) (f : α → β) (b : β) :
    ((ν.map f) b).toReal = pmfProb ν (fun a => f a = b) := by
  classical
  rw [pmfProb_eq_toOuterMeasure_toReal]
  have hsingleton :
      (ν.map f).toOuterMeasure ({b} : Set β) = (ν.map f) b :=
    PMF.toOuterMeasure_apply_singleton (ν.map f) b
  have hmap :
      (ν.map f).toOuterMeasure ({b} : Set β) =
        ν.toOuterMeasure (f ⁻¹' ({b} : Set β)) :=
    PMF.toOuterMeasure_map_apply f ν ({b} : Set β)
  rw [← hsingleton, hmap]
  rfl

theorem pmfExp_map {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (g : α → β) (f : β → ℝ) :
    pmfExp (μ.map g) f = pmfExp μ (fun a => f (g a)) := by
  classical
  calc
    pmfExp (μ.map g) f =
        ∑ b : β, (pmfProb μ (fun a => g a = b)) * f b := by
          unfold pmfExp
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [pmf_map_apply_toReal_eq_pmfProb_preimage]
    _ = ∑ b : β, (∑ a : α, (μ a).toReal *
          (if g a = b then (1 : ℝ) else 0)) * f b := by
          unfold pmfProb pmfExp
          rfl
    _ = ∑ b : β, ∑ a : α, ((μ a).toReal *
          (if g a = b then (1 : ℝ) else 0)) * f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_mul]
    _ = ∑ a : α, ∑ b : β, ((μ a).toReal *
          (if g a = b then (1 : ℝ) else 0)) * f b := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, (μ a).toReal * f (g a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          calc
            ∑ b : β, ((μ a).toReal *
                (if g a = b then (1 : ℝ) else 0)) * f b =
                (μ a).toReal *
                  ∑ b : β, (if g a = b then (1 : ℝ) else 0) * f b := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro b _
                  ring
            _ = (μ a).toReal * f (g a) := by
                  simp [eq_comm]
    _ = pmfExp μ (fun a => f (g a)) := by
          rfl

/-- Finite PMF event probability commutes with pushforward. -/
theorem pmfProb_map {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (g : α → β) (p : β → Prop) [DecidablePred p] :
    pmfProb (μ.map g) p = pmfProb μ (fun a => p (g a)) := by
  unfold pmfProb
  rw [pmfExp_map]

/-- Finite expectation of a PMF bind decomposes into iterated expectations. -/
theorem pmfExp_bind {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (κ : α → PMF β) (f : β → ℝ) :
    pmfExp (μ.bind κ) f = pmfExp μ (fun a => pmfExp (κ a) f) := by
  classical
  unfold pmfExp
  calc
    ∑ b : β, ((μ.bind κ) b).toReal * f b =
        ∑ b : β, (∑ a : α, (μ a).toReal * (κ a b).toReal) * f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          have hbind_toReal :
              ((μ.bind κ) b).toReal =
                ∑ a : α, (μ a).toReal * (κ a b).toReal := by
            have h_ne_top :
                ∀ a ∈ (Finset.univ : Finset α), μ a * κ a b ≠ ⊤ := by
              intro a _
              exact ENNReal.mul_ne_top (μ.apply_ne_top a) ((κ a).apply_ne_top b)
            calc
              ((μ.bind κ) b).toReal =
                  (∑ a : α, μ a * κ a b).toReal := by
                    rw [PMF.bind_apply, tsum_fintype]
              _ = ∑ a : α, (μ a * κ a b).toReal := by
                    exact
                      ENNReal.toReal_sum
                        (s := (Finset.univ : Finset α))
                        (f := fun a : α => μ a * κ a b) h_ne_top
              _ = ∑ a : α, (μ a).toReal * (κ a b).toReal := by
                    simp [ENNReal.toReal_mul]
          rw [hbind_toReal]
    _ = ∑ b : β, ∑ a : α,
          ((μ a).toReal * (κ a b).toReal) * f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_mul]
    _ = ∑ a : α, ∑ b : β,
          ((μ a).toReal * (κ a b).toReal) * f b := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, (μ a).toReal *
          ∑ b : β, (κ a b).toReal * f b := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro b _
          ring

/-- Finite event probability of a PMF bind decomposes into iterated probabilities. -/
theorem pmfProb_bind {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (κ : α → PMF β) (p : β → Prop) [DecidablePred p] :
    pmfProb (μ.bind κ) p = pmfExp μ (fun a => pmfProb (κ a) p) := by
  unfold pmfProb
  rw [pmfExp_bind]

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

/-- Monotonicity of finite PMF probabilities under event inclusion. -/
theorem pmfProb_le_of_imp {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (himp : ∀ a, p a → q a) :
    pmfProb μ p ≤ pmfProb μ q := by
  classical
  unfold pmfProb
  refine pmfExp_le_pmfExp_of_forall_le μ
    (fun a => if p a then (1 : ℝ) else 0)
    (fun a => if q a then (1 : ℝ) else 0) ?_
  intro a
  by_cases hp : p a
  · have hq : q a := himp a hp
    simp [hp, hq]
  · by_cases hq : q a <;> simp [hp, hq]

/-- A finite PMF expectation of a pointwise nonnegative function is nonnegative. -/
theorem pmfExp_nonneg_of_forall_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (h : ∀ a, 0 ≤ f a) :
    0 ≤ pmfExp μ f := by
  unfold pmfExp
  refine Finset.sum_nonneg ?_
  intro a _
  exact mul_nonneg ENNReal.toReal_nonneg (h a)

/-- Variance of a real-valued random variable under a finite PMF. -/
noncomputable def pmfVariance {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) : ℝ :=
  pmfExp μ (fun a => (X a - pmfExp μ X) ^ 2)

/-- Finite PMF variance is nonnegative. -/
theorem pmfVariance_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) :
    0 ≤ pmfVariance μ X := by
  unfold pmfVariance
  exact pmfExp_nonneg_of_forall_nonneg μ _ (fun a => sq_nonneg _)

/-- Finite-PMF variance as second moment minus the square of the mean. -/
theorem pmfVariance_eq_exp_sq_sub_sq_exp
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) :
    pmfVariance μ X =
      pmfExp μ (fun a => X a ^ 2) - (pmfExp μ X) ^ 2 := by
  let m : ℝ := pmfExp μ X
  calc
    pmfVariance μ X =
        pmfExp μ (fun a => (X a - m) ^ 2) := by
          simp [pmfVariance, m]
    _ = pmfExp μ
          (fun a => X a ^ 2 - (2 * m) * X a + m ^ 2) := by
          refine pmfExp_congr μ ?_
          intro a
          ring
    _ = pmfExp μ (fun a => X a ^ 2) -
          (2 * m) * pmfExp μ X + m ^ 2 := by
          rw [pmfExp_add]
          rw [pmfExp_sub]
          rw [pmfExp_const_mul]
          simp [pmfExp_const]
    _ = pmfExp μ (fun a => X a ^ 2) - (pmfExp μ X) ^ 2 := by
          simp [m]
          ring

/--
Finite-PMF Chebyshev inequality in centered absolute-deviation form.
-/
theorem pmfProb_abs_sub_mean_ge_le_variance_div_sq
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) {ε : ℝ} (hε : 0 < ε) :
    pmfProb μ (fun a => ε ≤ |X a - pmfExp μ X|) ≤
      pmfVariance μ X / ε ^ 2 := by
  classical
  have hε2_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hpoint :
      ∀ a,
        (if ε ≤ |X a - pmfExp μ X| then (1 : ℝ) else 0) ≤
          (X a - pmfExp μ X) ^ 2 / ε ^ 2 := by
    intro a
    by_cases hdev : ε ≤ |X a - pmfExp μ X|
    · have habs : |ε| ≤ |X a - pmfExp μ X| := by
        simpa [abs_of_pos hε] using hdev
      have hsq : ε ^ 2 ≤ (X a - pmfExp μ X) ^ 2 := by
        simpa [sq_abs] using (sq_le_sq.2 habs)
      have hone :
          (1 : ℝ) ≤ (X a - pmfExp μ X) ^ 2 / ε ^ 2 := by
        rw [le_div_iff₀ hε2_pos]
        simpa using hsq
      simpa [hdev] using hone
    · have hnonneg :
          0 ≤ (X a - pmfExp μ X) ^ 2 / ε ^ 2 := by
        exact div_nonneg (sq_nonneg _) (sq_nonneg _)
      simpa [hdev] using hnonneg
  calc
    pmfProb μ (fun a => ε ≤ |X a - pmfExp μ X|) ≤
        pmfExp μ
          (fun a => (X a - pmfExp μ X) ^ 2 / ε ^ 2) :=
          pmfExp_le_pmfExp_of_forall_le μ _ _ hpoint
    _ = pmfVariance μ X / ε ^ 2 := by
          simp [pmfVariance, div_eq_mul_inv, pmfExp_mul_const]

/-- Strict-tail version of finite-PMF Chebyshev. -/
theorem pmfProb_abs_sub_mean_gt_le_variance_div_sq
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) {ε : ℝ} (hε : 0 < ε) :
    pmfProb μ (fun a => ε < |X a - pmfExp μ X|) ≤
      pmfVariance μ X / ε ^ 2 := by
  classical
  exact le_trans
    (pmfProb_le_of_imp μ
      (fun a => ε < |X a - pmfExp μ X|)
      (fun a => ε ≤ |X a - pmfExp μ X|)
      (fun _a ha => le_of_lt ha))
    (pmfProb_abs_sub_mean_ge_le_variance_div_sq μ X hε)

/--
If a real-valued finite random variable has positive expectation and variance at
most its expectation, the lower-half tail has probability at most `4 / E[X]`.
-/
theorem pmfProb_lt_half_expectation_le_four_div_expectation_of_variance_le_expectation
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (X : α → ℝ) (EX : ℝ)
    (hmean : pmfExp μ X = EX)
    (hEX_pos : 0 < EX)
    (hvar : pmfVariance μ X ≤ EX) :
    pmfProb μ (fun a => X a < EX / 2) ≤ 4 / EX := by
  classical
  have hhalf_pos : 0 < EX / 2 := by positivity
  have htail :
      pmfProb μ (fun a => X a < EX / 2) ≤
        pmfProb μ (fun a => EX / 2 < |X a - pmfExp μ X|) := by
    refine pmfProb_le_of_imp μ
      (fun a => X a < EX / 2)
      (fun a => EX / 2 < |X a - pmfExp μ X|) ?_
    intro a ha
    rw [hmean]
    have hneg : X a - EX < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith
  have hcheb :
      pmfProb μ (fun a => EX / 2 < |X a - pmfExp μ X|) ≤
        pmfVariance μ X / (EX / 2) ^ 2 :=
    pmfProb_abs_sub_mean_gt_le_variance_div_sq μ X hhalf_pos
  have hvar_div :
      pmfVariance μ X / (EX / 2) ^ 2 ≤ EX / (EX / 2) ^ 2 :=
    div_le_div_of_nonneg_right hvar (sq_nonneg _)
  calc
    pmfProb μ (fun a => X a < EX / 2) ≤
        pmfProb μ (fun a => EX / 2 < |X a - pmfExp μ X|) := htail
    _ ≤ pmfVariance μ X / (EX / 2) ^ 2 := hcheb
    _ ≤ EX / (EX / 2) ^ 2 := hvar_div
    _ = 4 / EX := by
          field_simp [ne_of_gt hEX_pos]
          ring

/--
Second moment of a finite indicator count as the double sum of intersection
probabilities.
-/
theorem pmfExp_card_filter_sq_eq_sum_pmfProb_inter
    {Ω α : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype α] [DecidableEq α]
    (μ : PMF Ω) (p : Ω → α → Prop)
    [∀ ω, DecidablePred (p ω)]
    [∀ i, DecidablePred fun ω => p ω i] :
    pmfExp μ
        (fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ) ^ 2) =
      ∑ i : α, ∑ j : α,
        pmfProb μ (fun ω => p ω i ∧ p ω j) := by
  classical
  have hsq :
      ∀ ω,
        (((Finset.univ : Finset α).filter (p ω)).card : ℝ) ^ 2 =
          ∑ i : α, ∑ j : α,
            if p ω i ∧ p ω j then (1 : ℝ) else 0 := by
    intro ω
    have hcard :
        (((Finset.univ : Finset α).filter (p ω)).card : ℝ) =
          ∑ i : α, if p ω i then (1 : ℝ) else 0 := by
      simp
    calc
      (((Finset.univ : Finset α).filter (p ω)).card : ℝ) ^ 2 =
          (∑ i : α, if p ω i then (1 : ℝ) else 0) *
            (∑ j : α, if p ω j then (1 : ℝ) else 0) := by
            rw [hcard]
            ring
      _ = ∑ i : α,
            (if p ω i then (1 : ℝ) else 0) *
              (∑ j : α, if p ω j then (1 : ℝ) else 0) := by
            rw [Finset.sum_mul]
      _ = ∑ i : α, ∑ j : α,
            (if p ω i then (1 : ℝ) else 0) *
              (if p ω j then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
      _ = ∑ i : α, ∑ j : α,
            if p ω i ∧ p ω j then (1 : ℝ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            by_cases hi : p ω i <;> by_cases hj : p ω j <;> simp [hi, hj]
  unfold pmfExp pmfProb
  calc
    ∑ ω : Ω, (μ ω).toReal *
        ((((Finset.univ : Finset α).filter (p ω)).card : ℝ) ^ 2) =
        ∑ ω : Ω, (μ ω).toReal *
          (∑ i : α, ∑ j : α,
            if p ω i ∧ p ω j then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [hsq ω]
    _ = ∑ ω : Ω, ∑ i : α, ∑ j : α,
          (μ ω).toReal *
            (if p ω i ∧ p ω j then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
    _ = ∑ i : α, ∑ ω : Ω, ∑ j : α,
          (μ ω).toReal *
            (if p ω i ∧ p ω j then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ i : α, ∑ j : α, ∑ ω : Ω,
          (μ ω).toReal *
            (if p ω i ∧ p ω j then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_comm]

/--
For a finite sum of indicators, pairwise negative correlation bounds the
variance by the expectation.
-/
theorem pmfVariance_card_filter_le_pmfExp_card_filter_of_pairwise_inter_le_mul
    {Ω α : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype α] [DecidableEq α]
    (μ : PMF Ω) (p : Ω → α → Prop)
    [∀ ω, DecidablePred (p ω)]
    [∀ i, DecidablePred fun ω => p ω i]
    (hneg : ∀ i j : α, i ≠ j →
      pmfProb μ (fun ω => p ω i ∧ p ω j) ≤
        pmfProb μ (fun ω => p ω i) *
          pmfProb μ (fun ω => p ω j)) :
    pmfVariance μ
        (fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ)) ≤
      pmfExp μ
        (fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ)) := by
  classical
  let count : Ω → ℝ :=
    fun ω => (((Finset.univ : Finset α).filter (p ω)).card : ℝ)
  let P : α → ℝ := fun i => pmfProb μ (fun ω => p ω i)
  let P₂ : α → α → ℝ :=
    fun i j => pmfProb μ (fun ω => p ω i ∧ p ω j)
  have hmean :
      pmfExp μ count = ∑ i : α, P i := by
    simpa [count, P] using pmfExp_card_filter_eq_sum_pmfProb μ p
  have hsecond :
      pmfExp μ (fun ω => count ω ^ 2) =
        ∑ i : α, ∑ j : α, P₂ i j := by
    simpa [count, P₂] using pmfExp_card_filter_sq_eq_sum_pmfProb_inter μ p
  have hterm :
      ∀ i j : α,
        P₂ i j ≤ P i * P j + if i = j then P i else 0 := by
    intro i j
    by_cases hij : i = j
    · have hdiag : P₂ i j ≤ P i := by
        refine pmfProb_le_of_imp μ
          (fun ω => p ω i ∧ p ω j) (fun ω => p ω i) ?_
        intro ω hω
        exact hω.1
      have hprod_nonneg : 0 ≤ P i * P j :=
        mul_nonneg (pmfProb_nonneg μ (fun ω => p ω i))
          (pmfProb_nonneg μ (fun ω => p ω j))
      simpa [P₂, P, hij] using
        (le_trans hdiag (by linarith : P i ≤ P i * P j + P i))
    · simpa [P₂, P, hij] using hneg i j hij
  have hdouble_le :
      (∑ i : α, ∑ j : α, P₂ i j) ≤
        ∑ i : α, ∑ j : α, (P i * P j + if i = j then P i else 0) :=
    Finset.sum_le_sum (by
      intro i _
      exact Finset.sum_le_sum (by
        intro j _
        exact hterm i j))
  have hprod :
      (∑ i : α, ∑ j : α, P i * P j) = (∑ i : α, P i) ^ 2 := by
    calc
      (∑ i : α, ∑ j : α, P i * P j) =
          ∑ i : α, P i * (∑ j : α, P j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
      _ = (∑ i : α, P i) * (∑ j : α, P j) := by
          rw [Finset.sum_mul]
      _ = (∑ i : α, P i) ^ 2 := by ring
  have hdiag_sum :
      (∑ i : α, ∑ j : α, if i = j then P i else 0) =
        ∑ i : α, P i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simp
  have hbound_sum :
      (∑ i : α, ∑ j : α, (P i * P j + if i = j then P i else 0)) =
        (∑ i : α, P i) ^ 2 + ∑ i : α, P i := by
    calc
      (∑ i : α, ∑ j : α, (P i * P j + if i = j then P i else 0)) =
          (∑ i : α, ∑ j : α, P i * P j) +
            (∑ i : α, ∑ j : α, if i = j then P i else 0) := by
            simp [Finset.sum_add_distrib]
      _ = (∑ i : α, P i) ^ 2 + ∑ i : α, P i := by
            rw [hprod, hdiag_sum]
  have hsecond_le :
      pmfExp μ (fun ω => count ω ^ 2) ≤
        (pmfExp μ count) ^ 2 + pmfExp μ count := by
    calc
      pmfExp μ (fun ω => count ω ^ 2) =
          ∑ i : α, ∑ j : α, P₂ i j := hsecond
      _ ≤ ∑ i : α, ∑ j : α,
            (P i * P j + if i = j then P i else 0) := hdouble_le
      _ = (∑ i : α, P i) ^ 2 + ∑ i : α, P i := hbound_sum
      _ = (pmfExp μ count) ^ 2 + pmfExp μ count := by rw [hmean]
  calc
    pmfVariance μ count =
        pmfExp μ (fun ω => count ω ^ 2) - (pmfExp μ count) ^ 2 :=
          pmfVariance_eq_exp_sq_sub_sq_exp μ count
    _ ≤ pmfExp μ count := by linarith

/-- Finite union bound for real-valued PMF probabilities. -/
theorem pmfProb_exists_mem_le_sum {α ι : Type*}
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (s : Finset ι) (p : ι → α → Prop)
    [DecidablePred fun a => ∃ i, i ∈ s ∧ p i a]
    [∀ i, DecidablePred (p i)] :
    pmfProb μ (fun a => ∃ i, i ∈ s ∧ p i a) ≤
      ∑ i ∈ s, pmfProb μ (p i) := by
  classical
  have hpoint :
      ∀ a : α,
        (if ∃ i, i ∈ s ∧ p i a then (1 : ℝ) else 0) ≤
          ∑ i ∈ s, (if p i a then (1 : ℝ) else 0) := by
    intro a
    by_cases h : ∃ i, i ∈ s ∧ p i a
    · rcases h with ⟨i, hi, hp⟩
      have hnonneg :
          ∀ j ∈ s, 0 ≤ (if p j a then (1 : ℝ) else 0) := by
        intro j _hj
        by_cases hj : p j a <;> simp [hj]
      have hterm :
          (if p i a then (1 : ℝ) else 0) ≤
            ∑ j ∈ s, (if p j a then (1 : ℝ) else 0) :=
        Finset.single_le_sum
          (s := s) (f := fun j => if p j a then (1 : ℝ) else 0)
          hnonneg hi
      have hleft :
          (if ∃ i, i ∈ s ∧ p i a then (1 : ℝ) else 0) = 1 := by
        exact if_pos ⟨i, hi, hp⟩
      have hterm' :
          (1 : ℝ) ≤ ∑ j ∈ s, (if p j a then (1 : ℝ) else 0) := by
        rw [show (if p i a then (1 : ℝ) else 0) = 1 by simp [hp]] at hterm
        exact hterm
      simpa [hleft] using hterm'
    · simp [h]
  unfold pmfProb pmfExp
  calc
    ∑ a : α, (μ a).toReal *
        (if ∃ i, i ∈ s ∧ p i a then (1 : ℝ) else 0) ≤
        ∑ a : α, (μ a).toReal *
          (∑ i ∈ s, (if p i a then (1 : ℝ) else 0)) := by
          refine Finset.sum_le_sum ?_
          intro a _ha
          exact mul_le_mul_of_nonneg_left (hpoint a) ENNReal.toReal_nonneg
    _ = ∑ a : α, ∑ i ∈ s,
          (μ a).toReal * (if p i a then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ a : α,
          (μ a).toReal * (if p i a then (1 : ℝ) else 0) := by
          exact Finset.sum_comm

/--
Finite union bound with a uniform per-event upper bound over a finite index
type.
-/
theorem pmfProb_exists_le_card_mul {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι]
    (μ : PMF α) (p : ι → α → Prop)
    [DecidablePred fun a => ∃ i, p i a]
    [∀ i, DecidablePred (p i)]
    (eps : ℝ)
    (hprob : ∀ i, pmfProb μ (p i) ≤ eps) :
    pmfProb μ (fun a => ∃ i, p i a) ≤
      (Fintype.card ι : ℝ) * eps := by
  classical
  have hunion :=
    pmfProb_exists_mem_le_sum
      (μ := μ) (s := (Finset.univ : Finset ι)) (p := p)
  calc
    pmfProb μ (fun a => ∃ i, p i a) =
        pmfProb μ
          (fun a => ∃ i, i ∈ (Finset.univ : Finset ι) ∧ p i a) := by
          unfold pmfProb
          refine pmfExp_congr μ ?_
          intro a
          by_cases h : ∃ i, p i a <;> simp [h]
    _ ≤ ∑ i ∈ (Finset.univ : Finset ι), pmfProb μ (p i) := hunion
    _ ≤ ∑ _i ∈ (Finset.univ : Finset ι), eps := by
          exact Finset.sum_le_sum (by
            intro i _hi
            exact hprob i)
    _ = (Fintype.card ι : ℝ) * eps := by
          simp [nsmul_eq_mul]

@[simp] theorem pmfProb_false {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) :
    pmfProb μ (fun _ => False) = 0 := by
  simp [pmfProb]

/--
Compare finite probability deltas from a pointwise comparison of indicator
differences.
-/
theorem pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α)
    (p q r s : α → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r] [DecidablePred s]
    (h : ∀ a,
      (if p a then (1 : ℝ) else 0) - (if q a then (1 : ℝ) else 0) ≤
        (if r a then (1 : ℝ) else 0) - (if s a then (1 : ℝ) else 0)) :
    pmfProb μ p - pmfProb μ q ≤ pmfProb μ r - pmfProb μ s := by
  classical
  unfold pmfProb
  rw [← pmfExp_sub, ← pmfExp_sub]
  exact pmfExp_le_pmfExp_of_forall_le μ
    (fun a =>
      (if p a then (1 : ℝ) else 0) - (if q a then (1 : ℝ) else 0))
    (fun a =>
      (if r a then (1 : ℝ) else 0) - (if s a then (1 : ℝ) else 0))
    h

/--
If `p` is included in `q`, then `q` splits into `p` plus the finite residual
event `q ∧ ¬p`.
-/
theorem pmfProb_eq_add_diff_of_imp {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (himp : ∀ a, p a → q a) :
    pmfProb μ q = pmfProb μ p + pmfProb μ (fun a => q a ∧ ¬p a) := by
  classical
  unfold pmfProb
  rw [← pmfExp_add]
  refine pmfExp_congr μ ?_
  intro a
  by_cases hp : p a
  · have hq : q a := himp a hp
    simp [hp, hq]
  · by_cases hq : q a <;> simp [hp, hq]

/--
Strict finite probability monotonicity from event inclusion plus positive mass
in the residual event.
-/
theorem pmfProb_lt_of_imp_of_mass {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (himp : ∀ a, p a → q a) (a₀ : α)
    (hq : q a₀) (hp : ¬p a₀) (hmass : 0 < (μ a₀).toReal) :
    pmfProb μ p < pmfProb μ q := by
  classical
  have hres :
      0 < pmfProb μ (fun a => q a ∧ ¬p a) :=
    pmfProb_pos_of_mass μ (fun a => q a ∧ ¬p a) a₀ ⟨hq, hp⟩ hmass
  have hsplit := pmfProb_eq_add_diff_of_imp μ p q himp
  rw [hsplit]
  linarith

/-- Split an event by whether a second event also holds. -/
theorem pmfProb_eq_inter_add_inter_not
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    pmfProb μ p =
      pmfProb μ (fun a => p a ∧ q a) +
        pmfProb μ (fun a => p a ∧ ¬ q a) := by
  classical
  unfold pmfProb
  rw [← pmfExp_add]
  refine pmfExp_congr μ ?_
  intro a
  by_cases hp : p a
  · by_cases hq : q a <;> simp [hp, hq]
  · simp [hp]

/-- For disjoint finite-PMF events, the probability of their union is the sum. -/
theorem pmfProb_or_eq_add_of_disjoint
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hdisjoint : ∀ a, p a → q a → False) :
    pmfProb μ (fun a => p a ∨ q a) =
      pmfProb μ p + pmfProb μ q := by
  classical
  rw [pmfProb_eq_inter_add_inter_not μ (fun a => p a ∨ q a) p]
  have hleft :
      pmfProb μ (fun a => (p a ∨ q a) ∧ p a) =
        pmfProb μ p :=
    pmfProb_congr μ (by
      intro a
      constructor
      · intro h
        exact h.2
      · intro hp
        exact ⟨Or.inl hp, hp⟩)
  have hright :
      pmfProb μ (fun a => (p a ∨ q a) ∧ ¬ p a) =
        pmfProb μ q :=
    pmfProb_congr μ (by
      intro a
      constructor
      · intro h
        rcases h.1 with hp | hq
        · exact False.elim (h.2 hp)
        · exact hq
      · intro hq
        exact ⟨Or.inr hq, fun hp => hdisjoint a hp hq⟩)
  rw [hleft, hright]

/-- Inclusion-exclusion for two finite-PMF events. -/
theorem pmfProb_or_eq_add_sub_inter
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    pmfProb μ (fun a => p a ∨ q a) =
      pmfProb μ p + pmfProb μ q -
        pmfProb μ (fun a => p a ∧ q a) := by
  classical
  have hor_split :=
    pmfProb_eq_inter_add_inter_not μ (fun a => p a ∨ q a) p
  have hq_split := pmfProb_eq_inter_add_inter_not μ q p
  have hleft :
      pmfProb μ (fun a => (p a ∨ q a) ∧ p a) =
        pmfProb μ p :=
    pmfProb_congr μ (by
      intro a
      constructor
      · intro h
        exact h.2
      · intro hp
        exact ⟨Or.inl hp, hp⟩)
  have hright :
      pmfProb μ (fun a => (p a ∨ q a) ∧ ¬ p a) =
        pmfProb μ (fun a => q a ∧ ¬ p a) :=
    pmfProb_congr μ (by
      intro a
      constructor
      · intro h
        rcases h.1 with hp | hq
        · exact False.elim (h.2 hp)
        · exact ⟨hq, h.2⟩
      · intro h
        exact ⟨Or.inr h.1, h.2⟩)
  have hpq_comm :
      pmfProb μ (fun a => q a ∧ p a) =
        pmfProb μ (fun a => p a ∧ q a) :=
    pmfProb_congr μ (by intro a; constructor <;> intro h <;> exact ⟨h.2, h.1⟩)
  rw [hor_split, hleft, hright]
  rw [hq_split, hpq_comm]
  ring

/--
For disjoint finite-PMF events, the probability that neither occurs is
`1 - P(p) - P(q)`.
-/
theorem pmfProb_not_and_not_eq_one_sub_add_of_disjoint
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hdisjoint : ∀ a, p a → q a → False) :
    pmfProb μ (fun a => ¬ p a ∧ ¬ q a) =
      1 - pmfProb μ p - pmfProb μ q := by
  classical
  calc
    pmfProb μ (fun a => ¬ p a ∧ ¬ q a) =
        pmfProb μ (fun a => ¬ (p a ∨ q a)) := by
          exact pmfProb_congr μ (by intro a; tauto)
    _ = 1 - pmfProb μ (fun a => p a ∨ q a) := by
          rw [pmfProb_compl]
    _ = 1 - (pmfProb μ p + pmfProb μ q) := by
          rw [pmfProb_or_eq_add_of_disjoint μ p q hdisjoint]
    _ = 1 - pmfProb μ p - pmfProb μ q := by ring

/-- Complementing both events preserves a finite-PMF negative-correlation bound. -/
theorem pmfProb_not_and_not_le_mul_of_inter_le_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hinter : pmfProb μ (fun a => p a ∧ q a) ≤
      pmfProb μ p * pmfProb μ q) :
    pmfProb μ (fun a => ¬ p a ∧ ¬ q a) ≤
      pmfProb μ (fun a => ¬ p a) *
        pmfProb μ (fun a => ¬ q a) := by
  classical
  have hnotnot :
      pmfProb μ (fun a => ¬ p a ∧ ¬ q a) =
        1 - pmfProb μ p - pmfProb μ q +
          pmfProb μ (fun a => p a ∧ q a) := by
    calc
      pmfProb μ (fun a => ¬ p a ∧ ¬ q a) =
          pmfProb μ (fun a => ¬ (p a ∨ q a)) := by
            exact pmfProb_congr μ (by intro a; tauto)
      _ = 1 - pmfProb μ (fun a => p a ∨ q a) := by
            rw [pmfProb_compl]
      _ =
          1 - (pmfProb μ p + pmfProb μ q -
            pmfProb μ (fun a => p a ∧ q a)) := by
            rw [pmfProb_or_eq_add_sub_inter]
      _ =
          1 - pmfProb μ p - pmfProb μ q +
            pmfProb μ (fun a => p a ∧ q a) := by ring
  rw [hnotnot, pmfProb_compl, pmfProb_compl]
  nlinarith

/--
Finite union-bound lower-tail form: if two events each hold with probability at
least `1 - eps`, then their intersection holds with probability at least
`1 - epsP - epsQ`.
-/
theorem pmfProb_inter_ge_one_sub_add
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    {epsP epsQ : ℝ}
    (hp : 1 - epsP ≤ pmfProb μ p)
    (hq : 1 - epsQ ≤ pmfProb μ q) :
    1 - epsP - epsQ ≤ pmfProb μ (fun a => p a ∧ q a) := by
  classical
  have hsplit := pmfProb_eq_inter_add_inter_not μ p q
  have hres_le_notq :
      pmfProb μ (fun a => p a ∧ ¬ q a) ≤ pmfProb μ (fun a => ¬ q a) :=
    pmfProb_le_of_imp μ (fun a => p a ∧ ¬ q a) (fun a => ¬ q a)
      (by intro a ha; exact ha.2)
  have hnotq_eq := pmfProb_compl μ q
  have hnotq_le : pmfProb μ (fun a => ¬ q a) ≤ epsQ := by
    linarith
  have hres_le : pmfProb μ (fun a => p a ∧ ¬ q a) ≤ epsQ :=
    le_trans hres_le_notq hnotq_le
  linarith

/--
Finite change-of-variables bound for probabilities.

If an equivalence maps every point of event `p` into event `q`, and the target
atom has at least as much mass as the source atom on `p`, then `Pr[p] ≤ Pr[q]`.
This is the finite analogue of the injection/change-of-variables step in many
coupling proofs.
-/
theorem pmfProb_le_of_equiv_event_mass_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (e : α ≃ α)
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hmap : ∀ a, p a → q (e a))
    (hmass : ∀ a, p a → (μ a).toReal ≤ (μ (e a)).toReal) :
    pmfProb μ p ≤ pmfProb μ q := by
  classical
  unfold pmfProb pmfExp
  have hleft :
      (∑ a : α, (μ a).toReal * if p a then (1 : ℝ) else 0) =
        ∑ a : α, if p a then (μ a).toReal else 0 := by
    refine Finset.sum_congr rfl ?_
    intro a _
    by_cases hp : p a <;> simp [hp]
  have hright :
      (∑ a : α, (μ a).toReal * if q a then (1 : ℝ) else 0) =
        ∑ a : α, if q a then (μ a).toReal else 0 := by
    refine Finset.sum_congr rfl ?_
    intro a _
    by_cases hq : q a <;> simp [hq]
  rw [hleft, hright]
  calc
    ∑ a : α, (if p a then (μ a).toReal else 0)
        ≤ ∑ a : α, (if p a then (μ (e a)).toReal else 0) := by
          refine Finset.sum_le_sum ?_
          intro a _
          by_cases hp : p a
          · exact by simpa [hp] using hmass a hp
          · simp [hp]
    _ = ∑ a : α, (if p (e.symm a) then (μ a).toReal else 0) := by
          simpa using
            (Equiv.sum_comp e
              (fun a : α => if p (e.symm a) then (μ a).toReal else 0))
    _ ≤ ∑ a : α, (if q a then (μ a).toReal else 0) := by
          refine Finset.sum_le_sum ?_
          intro a _
          by_cases hp : p (e.symm a)
          · have hq : q a := by
              simpa using hmap (e.symm a) hp
            simp [hp, hq]
          · by_cases hq : q a
            · simp [hp, hq, ENNReal.toReal_nonneg]
            · simp [hp, hq]

/--
Strict finite change-of-variables bound for probabilities.

If an equivalence maps every point of event `p` into event `q`, the target atom
has at least as much mass as the source atom on `p`, and one source event atom
has strictly smaller mass than its image, then `Pr[p] < Pr[q]`.
-/
theorem pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (e : α ≃ α)
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hmap : ∀ a, p a → q (e a))
    (hmass : ∀ a, p a → (μ a).toReal ≤ (μ (e a)).toReal)
    {a₀ : α} (hp₀ : p a₀)
    (hstrict : (μ a₀).toReal < (μ (e a₀)).toReal) :
    pmfProb μ p < pmfProb μ q := by
  classical
  have himage :
      pmfProb μ (fun a => p (e.symm a)) ≤ pmfProb μ q := by
    refine pmfProb_le_of_imp μ (fun a => p (e.symm a)) q ?_
    intro a hp
    simpa using hmap (e.symm a) hp
  have hstrict_image :
      pmfProb μ p < pmfProb μ (fun a => p (e.symm a)) := by
    unfold pmfProb pmfExp
    have hleft :
        (∑ a : α, (μ a).toReal * if p a then (1 : ℝ) else 0) =
          ∑ a : α, if p a then (μ a).toReal else 0 := by
      refine Finset.sum_congr rfl ?_
      intro a _
      by_cases hp : p a <;> simp [hp]
    have hright :
        (∑ a : α, (μ a).toReal *
            if p (e.symm a) then (1 : ℝ) else 0) =
          ∑ a : α, if p (e.symm a) then (μ a).toReal else 0 := by
      refine Finset.sum_congr rfl ?_
      intro a _
      by_cases hp : p (e.symm a) <;> simp [hp]
    rw [hleft, hright]
    calc
      ∑ a : α, (if p a then (μ a).toReal else 0)
          < ∑ a : α, (if p a then (μ (e a)).toReal else 0) := by
            refine Finset.sum_lt_sum ?hle ?hlt
            · intro a _
              by_cases hp : p a
              · exact by simpa [hp] using hmass a hp
              · simp [hp]
            · exact ⟨a₀, Finset.mem_univ a₀, by simpa [hp₀] using hstrict⟩
      _ = ∑ a : α, (if p (e.symm a) then (μ a).toReal else 0) := by
            simpa using
              (Equiv.sum_comp e
              (fun a : α => if p (e.symm a) then (μ a).toReal else 0))
  exact lt_of_lt_of_le hstrict_image himage

/--
Finite cross-event change-of-variables bound.

To prove `Pr[p] ≤ Pr[q]`, it is enough to map only the asymmetric part
`p ∧ ¬q` into `q ∧ ¬p` with nondecreasing mass.  The common part
`p ∧ q` cancels on both sides.
-/
theorem pmfProb_le_of_cross_event_equiv_mass_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (e : α ≃ α)
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hmap : ∀ a, p a ∧ ¬ q a → q (e a) ∧ ¬ p (e a))
    (hmass : ∀ a, p a ∧ ¬ q a → (μ a).toReal ≤ (μ (e a)).toReal) :
    pmfProb μ p ≤ pmfProb μ q := by
  classical
  have hle := pmfProb_le_of_equiv_event_mass_le μ e
    (fun a => p a ∧ ¬ q a) (fun a => q a ∧ ¬ p a) hmap hmass
  have hp := pmfProb_eq_inter_add_inter_not μ p q
  have hq := pmfProb_eq_inter_add_inter_not μ q p
  have hpq_comm :
      pmfProb μ (fun a => q a ∧ p a) =
        pmfProb μ (fun a => p a ∧ q a) := by
    unfold pmfProb
    refine pmfExp_congr μ ?_
    intro a
    by_cases hp' : p a <;> by_cases hq' : q a <;> simp [hp', hq']
  rw [hp, hq, hpq_comm]
  linarith

/--
Strict finite cross-event change-of-variables bound.

If the asymmetric part `p ∧ ¬q` maps into `q ∧ ¬p`, mass never decreases there,
and one source atom strictly increases, then `Pr[p] < Pr[q]`.
-/
theorem pmfProb_lt_of_cross_event_equiv_mass_le_of_exists_strict
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (e : α ≃ α)
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hmap : ∀ a, p a ∧ ¬ q a → q (e a) ∧ ¬ p (e a))
    (hmass : ∀ a, p a ∧ ¬ q a → (μ a).toReal ≤ (μ (e a)).toReal)
    {a₀ : α} (hpq₀ : p a₀ ∧ ¬ q a₀)
    (hstrict : (μ a₀).toReal < (μ (e a₀)).toReal) :
    pmfProb μ p < pmfProb μ q := by
  classical
  have hlt := pmfProb_lt_of_equiv_event_mass_le_of_exists_strict μ e
    (fun a => p a ∧ ¬ q a) (fun a => q a ∧ ¬ p a)
    hmap hmass hpq₀ hstrict
  have hp := pmfProb_eq_inter_add_inter_not μ p q
  have hq := pmfProb_eq_inter_add_inter_not μ q p
  have hpq_comm :
      pmfProb μ (fun a => q a ∧ p a) =
        pmfProb μ (fun a => p a ∧ q a) := by
    unfold pmfProb
    refine pmfExp_congr μ ?_
    intro a
    by_cases hp' : p a <;> by_cases hq' : q a <;> simp [hp', hq']
  rw [hp, hq, hpq_comm]
  linarith

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

/-- Finite PMF expectation bounded by a tail decomposition of a `[0,1]`-valued
function. -/
theorem pmfExp_le_of_nonneg_le_one_of_tail
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (t : ℝ)
    (h_nonneg : ∀ a, 0 ≤ f a) (h_le_one : ∀ a, f a ≤ 1) (ht : 0 ≤ t) :
    pmfExp μ f ≤ t + pmfProb μ (fun a => t < f a) := by
  have hpoint : ∀ a, f a ≤ (if t < f a then (1 : ℝ) else 0) + t := by
    intro a
    by_cases hlt : t < f a
    · have hle : f a ≤ t + 1 := by
        nlinarith [h_le_one a, ht]
      have hle' : f a ≤ 1 + t := by
        simpa [add_comm] using hle
      simpa [hlt] using hle'
    · have hle : f a ≤ t := le_of_not_gt hlt
      simpa [hlt] using hle
  have hbound :
      pmfExp μ f ≤ pmfExp μ (fun a => (if t < f a then (1 : ℝ) else 0) + t) :=
    pmfExp_le_pmfExp_of_forall_le μ f
      (fun a => (if t < f a then (1 : ℝ) else 0) + t) hpoint
  calc
    pmfExp μ f ≤ pmfExp μ (fun a => (if t < f a then (1 : ℝ) else 0) + t) := hbound
    _ = pmfExp μ (fun a => if t < f a then (1 : ℝ) else 0) +
          pmfExp μ (fun _ : α => t) := by
        simpa using
          (pmfExp_add (μ := μ) (f := fun a => if t < f a then (1 : ℝ) else 0)
            (g := fun _ : α => t))
    _ = t + pmfProb μ (fun a => t < f a) := by
        simp [pmfProb, add_comm]

/-- Finite PMF expectation lower bound from upper-tail mass for nonnegative
functions. -/
theorem pmfExp_ge_of_nonneg_of_tail
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (t : ℝ)
    (h_nonneg : ∀ a, 0 ≤ f a) (ht : 0 ≤ t) :
    t * pmfProb μ (fun a => t < f a) ≤ pmfExp μ f := by
  have hpoint : ∀ a, t * (if t < f a then (1 : ℝ) else 0) ≤ f a := by
    intro a
    by_cases hlt : t < f a
    · have hle : t ≤ f a := le_of_lt hlt
      simpa [hlt] using hle
    · have hzero : (if t < f a then (1 : ℝ) else 0) = 0 := by simp [hlt]
      simp [hzero, h_nonneg a]
  have hbound : pmfExp μ (fun a => t * (if t < f a then (1 : ℝ) else 0)) ≤ pmfExp μ f :=
    pmfExp_le_pmfExp_of_forall_le μ
      (fun a => t * (if t < f a then (1 : ℝ) else 0)) f hpoint
  have hleft :
      pmfExp μ (fun a => t * (if t < f a then (1 : ℝ) else 0)) =
        t * pmfProb μ (fun a => t < f a) := by
    rw [pmfExp_const_mul, pmfProb]
  calc
    t * pmfProb μ (fun a => t < f a) = pmfExp μ (fun a => t * (if t < f a then (1 : ℝ) else 0)) := hleft.symm
    _ ≤ pmfExp μ f := hbound

/-- Direct concentration-style upper bound for finite expectations. -/
theorem pmfExp_le_of_tail_prob_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (f : α → ℝ) (t : ℝ) (eps : ℝ)
    (h_nonneg : ∀ a, 0 ≤ f a) (h_le_one : ∀ a, f a ≤ 1) (ht : 0 ≤ t)
    (h_tail : pmfProb μ (fun a => t < f a) ≤ eps) :
    pmfExp μ f ≤ t + eps := by
  calc
    pmfExp μ f ≤ t + pmfProb μ (fun a => t < f a) :=
      pmfExp_le_of_nonneg_le_one_of_tail μ f t h_nonneg h_le_one ht
    _ ≤ t + eps := by
      have htail' : pmfProb μ (fun a => t < f a) + t ≤ eps + t := by
        exact add_le_add_left h_tail t
      simpa [add_comm] using htail'

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

end EconCSLib
