import EconCSLib.Foundations.Probability.Conditional
import EconCSLib.Foundations.Probability.FiniteExpectation
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace EconCSLib

/-- Joint law of a finite latent state prior and a finite signal kernel.

For each latent state `θ`, the kernel `obs` returns a PMF over observed signal
`ω`.  The output PMF lives on pairs `(θ, ω)`.
-/
noncomputable def pmfKernelJoint {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (prior : PMF Θ) (obs : Θ → PMF Ω) : PMF (Θ × Ω) :=
  prior.bind (fun θ => (obs θ).map (fun ω => (θ, ω))
  )

@[simp] theorem pmfKernelJoint_apply {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (prior : PMF Θ) (obs : Θ → PMF Ω) (θ : Θ) (ω : Ω) :
    pmfKernelJoint prior obs (θ, ω) = prior θ * obs θ ω := by
  unfold pmfKernelJoint
  rw [PMF.bind_apply, tsum_fintype]
  rw [Finset.sum_eq_single θ]
  · simp [PMF.map_apply, Finset.sum_ite_eq]
  · intro θ' hθ' hθ'ne
    have hne : θ ≠ θ' := hθ'ne.symm
    simp [PMF.map_apply, hne]
  · intro hθ'
    simp at hθ'

/-- The induced marginal on observed signals. -/
noncomputable def pmfKernelSignalMarginal {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (prior : PMF Θ) (obs : Θ → PMF Ω) : PMF Ω :=
  (pmfKernelJoint prior obs).map Prod.snd

@[simp] theorem pmfKernelSignalMarginal_apply {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (prior : PMF Θ) (obs : Θ → PMF Ω) (ω : Ω) :
    pmfKernelSignalMarginal prior obs ω = ∑ θ : Θ, prior θ * obs θ ω := by
  unfold pmfKernelSignalMarginal
  rw [PMF.map_apply, tsum_fintype]
  rw [Fintype.sum_prod_type]
  simp [pmfKernelJoint_apply, Finset.sum_ite_eq]

/-- Real signal probability under a finite kernel experiment. -/
noncomputable def pmfKernelSignalProb {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (prior : PMF Θ) (obs : Θ → PMF Ω) (ω : Ω) : ℝ :=
  ∑ θ : Θ, (prior θ).toReal * (obs θ ω).toReal

@[simp] theorem pmfKernelSignalProb_eq_toReal
    {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (prior : PMF Θ) (obs : Θ → PMF Ω) (ω : Ω) :
    pmfKernelSignalProb prior obs ω
      = ((pmfKernelSignalMarginal prior obs) ω).toReal := by
  unfold pmfKernelSignalProb
  rw [pmfKernelSignalMarginal_apply]
  have h_ne_top : ∀ θ ∈ (Finset.univ : Finset Θ), prior θ * obs θ ω ≠ ⊤ := by
    intro θ _
    exact ENNReal.mul_ne_top (prior.apply_ne_top θ) ((obs θ).apply_ne_top ω)
  simpa [ENNReal.toReal_mul] using
    (ENNReal.toReal_sum (s := (Finset.univ : Finset Θ))
      (f := fun θ : Θ => prior θ * obs θ ω) h_ne_top).symm

theorem pmfKernelSignalProb_nonneg {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (prior : PMF Θ) (obs : Θ → PMF Ω) (ω : Ω) :
    0 ≤ pmfKernelSignalProb prior obs ω := by
  unfold pmfKernelSignalProb
  exact Finset.sum_nonneg (fun θ _ => mul_nonneg
    (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg))

/-- Expectation of `value` under the posterior state belief for signal `ω`.

This is a generic Bayes update for finite kernels used by admissions models with
and without standardized tests.
-/
noncomputable def pmfKernelPosteriorExpectation {Θ Ω : Type*}
    [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (prior : PMF Θ) (obs : Θ → PMF Ω) (ω : Ω) (value : Θ → ℝ) : ℝ :=
  let q := pmfKernelSignalProb prior obs ω
  if _h : q = 0 then 0 else
    (∑ θ : Θ, (prior θ).toReal * (obs θ ω).toReal * value θ) / q

theorem pmfKernelPosteriorExpectation_of_signal_prob_zero
    {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (prior : PMF Θ) (obs : Θ → PMF Ω) (ω : Ω) (value : Θ → ℝ)
    (h : pmfKernelSignalProb prior obs ω = 0) :
    pmfKernelPosteriorExpectation prior obs ω value = 0 := by
  change
    (if pmfKernelSignalProb prior obs ω = 0 then 0 else
        (∑ θ : Θ, (prior θ).toReal * (obs θ ω).toReal * value θ) /
          pmfKernelSignalProb prior obs ω)
      = 0
  rw [h]
  simp

theorem pmfKernelPosteriorExpectation_eq_div_of_pos
    {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype Ω] [DecidableEq Ω]
    (prior : PMF Θ) (obs : Θ → PMF Ω) (ω : Ω) (value : Θ → ℝ)
    (h : 0 < pmfKernelSignalProb prior obs ω) :
    pmfKernelPosteriorExpectation prior obs ω value =
      (∑ θ : Θ, (prior θ).toReal * (obs θ ω).toReal * value θ) /
        pmfKernelSignalProb prior obs ω := by
  have hne : pmfKernelSignalProb prior obs ω ≠ 0 := ne_of_gt h
  change
    (if pmfKernelSignalProb prior obs ω = 0 then 0 else
        (∑ θ : Θ, (prior θ).toReal * (obs θ ω).toReal * value θ) /
          pmfKernelSignalProb prior obs ω)
      = (∑ θ : Θ, (prior θ).toReal * (obs θ ω).toReal * value θ) /
          pmfKernelSignalProb prior obs ω
  rw [if_neg hne]

/-- Decomposing expectation through a finite kernel.

This is the law of iterated expectation for finite joint laws built from
`pmfKernelJoint`.
-/
theorem pmfKernelJointExp {Θ Ω : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype Ω] [DecidableEq Ω]
    (prior : PMF Θ) (obs : Θ → PMF Ω) (f : Θ → Ω → ℝ) :
    pmfExp (pmfKernelJoint prior obs) (fun p : Θ × Ω => f p.1 p.2)
      = ∑ θ, (prior θ).toReal * pmfExp (obs θ) (fun ω => f θ ω) := by
  unfold pmfExp
  rw [Fintype.sum_prod_type]
  simp [pmfKernelJoint_apply]
  refine Finset.sum_congr rfl ?_
  intro θ _hθ
  have hmul :
      (prior θ).toReal * ∑ ω : Ω, ((obs θ) ω).toReal * f θ ω
        = ∑ ω : Ω, (prior θ).toReal * (((obs θ) ω).toReal * f θ ω) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Finset.mul_sum (s := (Finset.univ : Finset Ω))
        (f := fun ω : Ω => ((obs θ) ω).toReal * f θ ω)
        (a := (prior θ).toReal))
  calc
    ∑ ω : Ω, (prior θ).toReal * ((obs θ) ω).toReal * f θ ω
        = ∑ ω : Ω, (prior θ).toReal * (((obs θ) ω).toReal * f θ ω) := by
          refine Finset.sum_congr rfl ?_
          intro ω _hω
          ring
    _ = (prior θ).toReal * ∑ ω : Ω, ((obs θ) ω).toReal * f θ ω := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul.symm

end EconCSLib
