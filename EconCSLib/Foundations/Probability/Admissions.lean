import EconCSLib.Foundations.Probability.Kernel
import EconCSLib.Foundations.Probability.Conditional
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace EconCSLib

/-- Finite admissions experiment with a latent trait and observed signal. -/
structure AdmissionsModel (Θ Ω : Type*) [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω] where
  (prior : PMF Θ)
  (signalKernel : Θ → PMF Ω)

/-- Admission process induced by the model and a binary policy on observed signals. -/
noncomputable def admissionsJointMass {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) : PMF (Θ × Ω) :=
  pmfKernelJoint m.prior m.signalKernel

/-- Signal-marginal induced by an admissions model. -/
noncomputable def admissionsSignalMarginal {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) : PMF Ω :=
  pmfKernelSignalMarginal m.prior m.signalKernel

/-- Signal probability in real form under the model. -/
noncomputable def admissionsSignalProb {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (ω : Ω) : ℝ :=
  pmfKernelSignalProb m.prior m.signalKernel ω

/-- Posterior expectation of `value` given observed signal in the model. -/
noncomputable def admissionsPosteriorExpectation {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (ω : Ω) (value : Θ → ℝ) : ℝ :=
  pmfKernelPosteriorExpectation m.prior m.signalKernel ω value

/-- Unnormalized welfare mass from applicants selected by signal policy `p`. -/
noncomputable def admissionsSelectedWelfareMass {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) : ℝ :=
  pmfIndicatorExp (admissionsJointMass m) (fun a => p a.2) (fun a => value a.1)

/-- Selection probability under policy `p`. -/
noncomputable def admissionsSelectionProb {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p] : ℝ :=
  pmfProb (admissionsJointMass m) (fun a => p a.2)

/-- Posterior expected welfare conditional on being selected by policy `p`. -/
noncomputable def admissionsSelectedWelfareConditionalExp {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) : ℝ :=
  pmfConditionalExp (admissionsJointMass m) (fun a => p a.2) (fun a => value a.1)

@[simp] theorem admissionsSelectionProb_of_false {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) :
    admissionsSelectionProb m (fun _ : Ω => False) = 0 := by
  simp [admissionsSelectionProb, pmfProb]

@[simp] theorem admissionsSelectionProb_of_true {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) :
    admissionsSelectionProb m (fun _ : Ω => True) = 1 := by
  simp [admissionsSelectionProb, pmfProb]

@[simp] theorem admissionsSelectionProb_nonneg {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p] :
    0 ≤ admissionsSelectionProb m p := by
  exact pmfProb_nonneg (μ := admissionsJointMass m)
    (p := fun a : Θ × Ω => p a.2)

@[simp] theorem admissionsSelectionProb_le_one {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p] :
    admissionsSelectionProb m p ≤ 1 := by
  exact pmfProb_le_one (μ := admissionsJointMass m)
    (p := fun a : Θ × Ω => p a.2)

@[simp] theorem admissionsSelectionProb_compl {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p] :
    admissionsSelectionProb m (fun ω => ¬ p ω) = 1 - admissionsSelectionProb m p := by
  simpa [admissionsSelectionProb] using
    (pmfProb_compl (μ := admissionsJointMass m)
      (p := fun a : Θ × Ω => p a.2))

@[simp] theorem admissionsSelectionMass_of_false {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (value : Θ → ℝ) :
    admissionsSelectedWelfareMass m (fun _ : Ω => False) value = 0 := by
  unfold admissionsSelectedWelfareMass
  simp [pmfIndicatorExp, pmfExp]

theorem admissionsSelectionMass_of_true {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (value : Θ → ℝ) :
    admissionsSelectedWelfareMass m (fun _ : Ω => True) value = pmfExp m.prior value := by
  -- With universal admission, conditioning on signal has no effect on expected welfare.
  simpa [admissionsSelectedWelfareMass, pmfIndicatorExp] using
    (pmfKernelJointExp m.prior m.signalKernel (fun θ _ => value θ))

theorem admissionsSelectedWelfareConditionalExp_of_false {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
  (m : AdmissionsModel Θ Ω) (value : Θ → ℝ) :
  admissionsSelectedWelfareConditionalExp m (fun _ : Ω => False) value = 0 := by
  have hprob : admissionsSelectionProb m (fun _ : Ω => False) = 0 := by
    simp [admissionsSelectionProb]
  rw [admissionsSelectedWelfareConditionalExp]
  exact pmfConditionalExp_of_prob_zero (μ := admissionsJointMass m) (p := fun _ : Θ × Ω => False)
    (f := fun a => value a.1) hprob

theorem admissionsSelectedWelfareConditionalExp_of_true {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (value : Θ → ℝ) :
    admissionsSelectedWelfareConditionalExp m (fun _ : Ω => True) value = pmfExp m.prior value := by
  have hden : pmfProb (admissionsJointMass m) (fun _ : Θ × Ω => True) = 1 := by
    simpa [admissionsSelectionProb] using
      (admissionsSelectionProb_of_true (m := m))
  have hprob : 0 < pmfProb (admissionsJointMass m) (fun _ : Θ × Ω => True) := by
    rw [hden]
    norm_num
  rw [admissionsSelectedWelfareConditionalExp, pmfConditionalExp_eq_div_of_pos (μ := admissionsJointMass m)
    (p := fun _ : Θ × Ω => True) (f := fun a => value a.1) hprob]
  rw [hden]
  simpa [admissionsSelectedWelfareMass, admissionsSelectedWelfareConditionalExp, pmfIndicatorExp] using
    (admissionsSelectionMass_of_true (m := m) (value := value))

theorem admissionsSelectedWelfareConditionalExp_eq_div_of_selectionProb_pos {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) (hprob : 0 < admissionsSelectionProb m p) :
    admissionsSelectedWelfareConditionalExp m p value =
      admissionsSelectedWelfareMass m p value / admissionsSelectionProb m p := by
  have hprob' : 0 < pmfProb (admissionsJointMass m) (fun a : Θ × Ω => p a.2) := by
    simpa [admissionsSelectionProb] using hprob
  rw [admissionsSelectedWelfareConditionalExp,
    pmfConditionalExp_eq_div_of_pos (μ := admissionsJointMass m)
      (p := fun a : Θ × Ω => p a.2) (f := fun a => value a.1) hprob']
  rfl

theorem admissionsSelectedWelfareConditionalExp_of_selectionProb_zero {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) (hprob : admissionsSelectionProb m p = 0) :
    admissionsSelectedWelfareConditionalExp m p value = 0 := by
  unfold admissionsSelectedWelfareConditionalExp
  apply pmfConditionalExp_of_prob_zero (μ := admissionsJointMass m)
    (p := fun a : Θ × Ω => p a.2) (f := fun a => value a.1)
  simpa [admissionsSelectionProb] using hprob

theorem admissionsSelectedWelfareMass_of_selectionProb_zero {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) (hprob : admissionsSelectionProb m p = 0) :
    admissionsSelectedWelfareMass m p value = 0 := by
  unfold admissionsSelectedWelfareMass
  exact EconCSLib.pmfIndicatorExp_eq_zero_of_pmfProb_eq_zero (μ := admissionsJointMass m)
    (p := fun a : Θ × Ω => p a.2) (f := fun a => value a.1)
    (by simpa [admissionsSelectionProb] using hprob)

theorem admissionsSelectedWelfareMass_eq_selectionProb_mul_conditionalExp {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) :
    admissionsSelectedWelfareMass m p value =
      admissionsSelectionProb m p * admissionsSelectedWelfareConditionalExp m p value := by
  by_cases h : admissionsSelectionProb m p = 0
  · rw [admissionsSelectedWelfareConditionalExp_of_selectionProb_zero (m := m) (p := p)
      (value := value) h, admissionsSelectedWelfareMass_of_selectionProb_zero (m := m)
      (p := p) (value := value) h, h]
    simp
  · have hprob : 0 < admissionsSelectionProb m p := lt_of_le_of_ne
      (pmfProb_nonneg (μ := admissionsJointMass m)
        (p := fun a : Θ × Ω => p a.2)) (by simpa [eq_comm] using h)
    rw [admissionsSelectedWelfareConditionalExp_eq_div_of_selectionProb_pos (m := m) (p := p)
      (value := value) hprob]
    have hne : admissionsSelectionProb m p ≠ 0 := by simpa [eq_comm] using h
    field_simp [hne]

theorem admissionsSelectedWelfareMass_nonneg_of_value_nonneg {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) (hvalue : ∀ θ, 0 ≤ value θ) :
    0 ≤ admissionsSelectedWelfareMass m p value := by
  unfold admissionsSelectedWelfareMass pmfIndicatorExp pmfExp
  refine Finset.sum_nonneg ?_
  intro a _
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  by_cases hp : p a.2
  · simp [hp, hvalue a.1]
  · simp [hp]

theorem admissionsSelectedWelfareConditionalExp_nonneg_of_value_nonneg {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) (hvalue : ∀ θ, 0 ≤ value θ) :
    0 ≤ admissionsSelectedWelfareConditionalExp m p value := by
  by_cases hprob : admissionsSelectionProb m p = 0
  · exact (admissionsSelectedWelfareConditionalExp_of_selectionProb_zero (m := m) (p := p)
      (value := value) hprob).symm.le
  · have hprob' : 0 < admissionsSelectionProb m p := by
      exact lt_of_le_of_ne (pmfProb_nonneg (μ := admissionsJointMass m)
          (p := fun a : Θ × Ω => p a.2)) (by simpa [eq_comm] using hprob)
    rw [admissionsSelectedWelfareConditionalExp_eq_div_of_selectionProb_pos (m := m) (p := p)
      (value := value) hprob']
    apply div_nonneg
    · exact admissionsSelectedWelfareMass_nonneg_of_value_nonneg (m := m) (p := p)
        (value := value) hvalue
    · exact le_of_lt hprob'

theorem admissionsSelectedWelfareMass_le_of_pred_le {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (value : Θ → ℝ) (hvalue : ∀ θ, 0 ≤ value θ)
    (hsub : ∀ ω, p ω → q ω) :
    admissionsSelectedWelfareMass m p value ≤ admissionsSelectedWelfareMass m q value := by
  unfold admissionsSelectedWelfareMass
  change
      pmfExp (admissionsJointMass m) (fun a => if p a.2 then value a.1 else 0) ≤
      pmfExp (admissionsJointMass m) (fun a => if q a.2 then value a.1 else 0)
  refine pmfExp_le_pmfExp_of_forall_le (μ := admissionsJointMass m)
    (f := fun a => if p a.2 then value a.1 else 0)
    (g := fun a => if q a.2 then value a.1 else 0) ?_
  intro a
  by_cases hp : p a.2
  · simp [hp, hsub a.2 hp]
  · by_cases hq : q a.2
    · simp [hp, hq, hvalue a.1]
    · simp [hp, hq]

theorem admissionsSelectedWelfareMass_of_compl {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) :
    admissionsSelectedWelfareMass m (fun ω => ¬ p ω) value =
      pmfExp m.prior value - admissionsSelectedWelfareMass m p value := by
  have hsum :
      admissionsSelectedWelfareMass m p value +
        admissionsSelectedWelfareMass m (fun ω => ¬ p ω) value
          = pmfExp m.prior value := by
    have hfull :
        pmfExp (admissionsJointMass m) (fun a : Θ × Ω => value a.1) = pmfExp m.prior value := by
      simpa [admissionsJointMass] using
        (pmfKernelJointExp (prior := m.prior) (obs := m.signalKernel)
          (f := fun θ _ => value θ))
    unfold admissionsSelectedWelfareMass pmfIndicatorExp
    calc
      pmfExp (admissionsJointMass m) (fun a : Θ × Ω => if p a.2 then value a.1 else 0) +
          pmfExp (admissionsJointMass m) (fun a : Θ × Ω => if ¬ p a.2 then value a.1 else 0)
            = pmfExp (admissionsJointMass m)
                (fun a : Θ × Ω => (if p a.2 then value a.1 else 0) +
                  (if ¬ p a.2 then value a.1 else 0)) := by
              rw [pmfExp_add]
      _ = pmfExp (admissionsJointMass m) (fun a : Θ × Ω => value a.1) := by
              refine pmfExp_congr (admissionsJointMass m) ?_
              intro a
              by_cases hp' : p a.2 <;> simp [hp']
      _ = pmfExp m.prior value := hfull
  linarith [hsum]

theorem admissionsSelectedWelfareMass_add_of_compl {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) :
    admissionsSelectedWelfareMass m p value + admissionsSelectedWelfareMass m (fun ω => ¬ p ω) value =
      pmfExp m.prior value := by
  rw [admissionsSelectedWelfareMass_of_compl (m := m) (p := p) (value := value)]
  ring

theorem admissionsSelectedWelfareConditionalExp_of_compl {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) :
    admissionsSelectedWelfareConditionalExp m (fun ω => ¬ p ω) value =
      (pmfExp m.prior value - admissionsSelectionProb m p *
          admissionsSelectedWelfareConditionalExp m p value) /
        admissionsSelectionProb m (fun ω => ¬ p ω) := by
  by_cases hcompl : admissionsSelectionProb m (fun ω => ¬ p ω) = 0
  · have hcompl_mass : admissionsSelectedWelfareMass m (fun ω => ¬ p ω) value = 0 := by
      exact admissionsSelectedWelfareMass_of_selectionProb_zero (m := m) (p := fun ω => ¬ p ω)
        (value := value) hcompl
    have hnumer : pmfExp m.prior value - admissionsSelectionProb m p *
        admissionsSelectedWelfareConditionalExp m p value = 0 := by
      calc
        pmfExp m.prior value - admissionsSelectionProb m p *
            admissionsSelectedWelfareConditionalExp m p value
            = pmfExp m.prior value - admissionsSelectedWelfareMass m p value := by
              rw [admissionsSelectedWelfareMass_eq_selectionProb_mul_conditionalExp (m := m) (p := p)
                (value := value)]
        _ = admissionsSelectedWelfareMass m (fun ω => ¬ p ω) value := by
              symm
              exact admissionsSelectedWelfareMass_of_compl (m := m) (p := p) (value := value)
        _ = 0 := hcompl_mass
    rw [admissionsSelectedWelfareConditionalExp_of_selectionProb_zero (m := m)
      (p := fun ω => ¬ p ω) (value := value) hcompl]
    rw [hcompl, hnumer]
    simp
  · have hcompl_pos : 0 < admissionsSelectionProb m (fun ω => ¬ p ω) := by
      exact lt_of_le_of_ne (admissionsSelectionProb_nonneg (m := m) (p := fun ω => ¬ p ω)) (by
        simpa [eq_comm] using hcompl)
    have hmul :
        admissionsSelectionProb m (fun ω => ¬ p ω) *
          admissionsSelectedWelfareConditionalExp m (fun ω => ¬ p ω) value =
          pmfExp m.prior value - admissionsSelectionProb m p *
            admissionsSelectedWelfareConditionalExp m p value := by
      calc
        admissionsSelectionProb m (fun ω => ¬ p ω) *
            admissionsSelectedWelfareConditionalExp m (fun ω => ¬ p ω) value
            = admissionsSelectedWelfareMass m (fun ω => ¬ p ω) value := by
              symm
              exact admissionsSelectedWelfareMass_eq_selectionProb_mul_conditionalExp (m := m)
                (p := fun ω => ¬ p ω) (value := value)
        _ = pmfExp m.prior value - admissionsSelectionProb m p *
            admissionsSelectedWelfareConditionalExp m p value := by
          rw [admissionsSelectedWelfareMass_of_compl (m := m) (p := p) (value := value)]
          rw [admissionsSelectedWelfareMass_eq_selectionProb_mul_conditionalExp (m := m) (p := p)
            (value := value)]
    exact (eq_div_iff hcompl_pos.ne').2 (by simpa [mul_comm] using hmul)

theorem admissionsSelectedWelfareExp_decompose {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) :
    pmfExp m.prior value =
      admissionsSelectionProb m p * admissionsSelectedWelfareConditionalExp m p value +
        admissionsSelectionProb m (fun ω => ¬ p ω) *
          admissionsSelectedWelfareConditionalExp m (fun ω => ¬ p ω) value := by
  rw [← admissionsSelectedWelfareMass_add_of_compl (m := m) (p := p) (value := value)]
  rw [admissionsSelectedWelfareMass_eq_selectionProb_mul_conditionalExp (m := m) (p := p)
    (value := value)]
  rw [admissionsSelectedWelfareMass_eq_selectionProb_mul_conditionalExp (m := m) (p := fun ω => ¬ p ω)
    (value := value)]

theorem admissionsSelectedWelfareMass_le_total_of_value_nonneg {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (m : AdmissionsModel Θ Ω) (p : Ω → Prop) [DecidablePred p]
    (value : Θ → ℝ) (hvalue : ∀ θ, 0 ≤ value θ) :
    admissionsSelectedWelfareMass m p value ≤ pmfExp m.prior value := by
  have htop : admissionsSelectedWelfareMass m (fun _ : Ω => True) value = pmfExp m.prior value := by
    simpa [admissionsSelectedWelfareMass] using
      (admissionsSelectionMass_of_true (m := m) (value := value))
  calc
    admissionsSelectedWelfareMass m p value ≤ admissionsSelectedWelfareMass m (fun _ : Ω => True) value := by
      exact admissionsSelectedWelfareMass_le_of_pred_le (m := m) (p := p) (q := fun _ => True)
        (value := value) hvalue (by intro ω _; trivial)
    _ = pmfExp m.prior value := htop

end EconCSLib
