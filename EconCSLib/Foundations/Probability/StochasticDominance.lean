import EconCSLib.Foundations.Probability.MDP
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace EconCSLib

/-!
# Finite stochastic dominance and monotone couplings

This module provides lightweight finite first-order stochastic dominance
interfaces for PMFs on ordered finite types. The core definition is by monotone
test functions, with a monotone-coupling certificate interface that later papers
can instantiate from explicit constructions.

## Main declarations

- `PMF.FirstOrderLe`: expectation order against every monotone observable.
- `PMF.MonotoneCoupling`: joint-distribution certificate for stochastic
  dominance.
- `PMF.FirstOrderLe.map`: first-order dominance is preserved by monotone maps.
- `PMF.firstOrderLe_of_monotoneCoupling`: monotone coupling implies first-order
  stochastic dominance.
- `FiniteMarkovKernel.FirstOrderLe`: pointwise stochastic dominance of kernels.
-/

namespace PMF

variable {α : Type*} [Fintype α] [DecidableEq α] [Preorder α]

/--
First-order stochastic dominance, stated as expectation comparison against
every monotone real observable. `FirstOrderLe μ ν` means that `ν` is at least as
large as `μ` in the first-order stochastic order.
-/
def FirstOrderLe (μ ν : PMF α) : Prop :=
  ∀ f : α → ℝ, Monotone f → pmfExp μ f ≤ pmfExp ν f

theorem FirstOrderLe.refl (μ : PMF α) : FirstOrderLe μ μ := by
  intro f hf
  rfl

theorem FirstOrderLe.trans {μ ν ξ : PMF α}
    (hμν : FirstOrderLe μ ν) (hνξ : FirstOrderLe ν ξ) :
    FirstOrderLe μ ξ := by
  intro f hf
  exact le_trans (hμν f hf) (hνξ f hf)

theorem FirstOrderLe.expectation_le {μ ν : PMF α}
    (hμν : FirstOrderLe μ ν) {f : α → ℝ} (hf : Monotone f) :
    pmfExp μ f ≤ pmfExp ν f :=
  hμν f hf

theorem firstOrderLe_pure_of_le {x y : α} (hxy : x ≤ y) :
    FirstOrderLe (PMF.pure x) (PMF.pure y) := by
  intro f hf
  simpa using hf hxy

theorem FirstOrderLe.exp_le_of_le {μ ν : PMF α}
    (hμν : FirstOrderLe μ ν) {f g : α → ℝ}
    (hfg : ∀ x, f x ≤ g x) (hg : Monotone g) :
    pmfExp μ f ≤ pmfExp ν g := by
  exact le_trans (FiniteMarkovKernel.pmfExp_mono μ hfg) (hμν g hg)

theorem FirstOrderLe.map
    {β : Type*} [Fintype β] [DecidableEq β] [Preorder β]
    {μ ν : PMF α} (hμν : FirstOrderLe μ ν)
    {g : α → β} (hg : Monotone g) :
    FirstOrderLe (μ.map g) (ν.map g) := by
  intro f hf
  rw [pmfExp_map μ g f, pmfExp_map ν g f]
  exact hμν (fun a => f (g a)) (hf.comp hg)

/-- Left-coordinate expectation under a joint distribution on ordered pairs. -/
noncomputable def pairLeftExp (γ : PMF (α × α)) (f : α → ℝ) : ℝ :=
  ∑ z : α × α, (γ z).toReal * f z.1

/-- Right-coordinate expectation under a joint distribution on ordered pairs. -/
noncomputable def pairRightExp (γ : PMF (α × α)) (f : α → ℝ) : ℝ :=
  ∑ z : α × α, (γ z).toReal * f z.2

/--
A monotone-coupling certificate from `μ` to `ν`.

The projection conditions are stated as expectation identities rather than raw
marginal sums; this is often the right abstraction for paper proofs, where a
coupling is introduced specifically to compare monotone observables.
-/
structure MonotoneCoupling (μ ν : PMF α) where
  joint : PMF (α × α)
  left_expectation : ∀ f : α → ℝ, pmfExp μ f = pairLeftExp joint f
  right_expectation : ∀ f : α → ℝ, pmfExp ν f = pairRightExp joint f
  ordered_support : ∀ z : α × α, 0 < (joint z).toReal → z.1 ≤ z.2

theorem pairExp_le_of_ordered
    (γ : PMF (α × α))
    (hγ : ∀ z : α × α, 0 < (γ z).toReal → z.1 ≤ z.2)
    {f : α → ℝ} (hf : Monotone f) :
    pairLeftExp γ f ≤ pairRightExp γ f := by
  unfold pairLeftExp pairRightExp
  exact Finset.sum_le_sum (fun z _ => by
    by_cases hzero : (γ z).toReal = 0
    · simp [hzero]
    · have hnonneg : 0 ≤ (γ z).toReal := ENNReal.toReal_nonneg
      have hpos : 0 < (γ z).toReal := by
        rcases lt_or_eq_of_le hnonneg with hpos | hzero'
        · exact hpos
        · exact False.elim (hzero hzero'.symm)
      exact mul_le_mul_of_nonneg_left (hf (hγ z hpos)) hnonneg)

theorem firstOrderLe_of_monotoneCoupling {μ ν : PMF α}
    (C : MonotoneCoupling μ ν) :
    FirstOrderLe μ ν := by
  intro f hf
  rw [C.left_expectation f, C.right_expectation f]
  exact pairExp_le_of_ordered C.joint C.ordered_support hf

end PMF

namespace FiniteMarkovKernel

variable {α : Type*} [Fintype α] [DecidableEq α] [Preorder α]

/--
Pointwise first-order stochastic dominance between two finite Markov kernels:
from every state, `L` produces a next-state distribution that dominates `K`.
-/
def FirstOrderLe (K L : FiniteMarkovKernel α) : Prop :=
  ∀ x, PMF.FirstOrderLe (K x) (L x)

theorem expectedNext_le_of_firstOrderLe
    {K L : FiniteMarkovKernel α} (hKL : FirstOrderLe K L)
    (x : α) {f : α → ℝ} (hf : Monotone f) :
    expectedNext K f x ≤ expectedNext L f x :=
  hKL x f hf

theorem firstOrderLe_of_stochasticallyMonotone
    {K : FiniteMarkovKernel α} (hK : StochasticallyMonotone K)
    {x y : α} (hxy : x ≤ y) :
    PMF.FirstOrderLe (K x) (K y) := by
  intro f hf
  exact hK hxy f hf

theorem FirstOrderLe.refl (K : FiniteMarkovKernel α) : FirstOrderLe K K := by
  intro x
  exact PMF.FirstOrderLe.refl (K x)

theorem FirstOrderLe.trans {K L H : FiniteMarkovKernel α}
    (hKL : FirstOrderLe K L) (hLH : FirstOrderLe L H) :
    FirstOrderLe K H := by
  intro x
  exact PMF.FirstOrderLe.trans (hKL x) (hLH x)

theorem expectedLe_of_firstOrderLe
    {K L : FiniteMarkovKernel α} (hKL : FirstOrderLe K L)
    {f : α → ℝ} (hf : Monotone f) :
    ExpectedLe K L f := by
  intro x
  exact expectedNext_le_of_firstOrderLe hKL x hf

end FiniteMarkovKernel

namespace FiniteMDP

variable {σ α : Type*}
variable [Fintype σ] [DecidableEq σ] [Preorder σ]
variable [Fintype α] [DecidableEq α]

/--
If action `b` induces a stochastically larger next-state distribution than
action `a`, and the `b` continuation payoff is monotone and pointwise dominates
the `a` continuation payoff, then `b` has weakly larger action value.
-/
theorem actionValue_le_of_firstOrderLe
    (M : FiniteMDP σ α) {V : σ → ℝ} {x : σ} {a b : α}
    (htrans : PMF.FirstOrderLe (M.transition x a) (M.transition x b))
    (hpayoff : ∀ y, M.reward x a y + V y ≤ M.reward x b y + V y)
    (hmono : Monotone (fun y => M.reward x b y + V y)) :
    actionValue M V x a ≤ actionValue M V x b := by
  exact htrans.exp_le_of_le hpayoff hmono

end FiniteMDP

end EconCSLib
