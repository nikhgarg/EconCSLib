import KR21Monoculture.MallowsFiniteLemmas
import KR21Monoculture.Theorem1
import KR21Monoculture.MallowsPairwise
import KR21Monoculture.MallowsFamily
import KR21Monoculture.Sequential
import KR21Monoculture.RUM

open EconCSLib MeasureTheory
open scoped ENNReal NNReal

/-!
# Paper-Facing Theorems: Algorithmic KR21Monoculture and Social Welfare

This file is the single, paper-oriented verification surface for the monoculture
formalization.

Declarations are arranged by the paper order so a human can read this file in one
pass, check each statement against the paper wording, and then follow the named
support lemmas below.
-/

namespace KR21Monoculture

/--
Definition 1 / Mallows atomwise continuity.

Paper statement: for the Mallows family with parameter `θ = φ - 1`, the
probability of any fixed permutation varies continuously with positive `θ`.

Lean uses the finite epsilon-delta interface required by the Theorem 1 proof.
-/
theorem paper_definition1_concreteMallowsSpec_atom_continuity
    {n : ℕ} (center : Ranking n) {θ : ℝ} (hθ : 0 < θ)
    (π : Ranking n) :
    EconCSLib.EpsilonContinuousAt
      (fun θ' => (((concreteMallowsSpec center θ').law) π).toReal) θ :=
  concreteMallowsSpec_atom_continuity center hθ π

/--
Definition 1 / Mallows asymptotic first dominance.

Paper statement: as the algorithmic Mallows accuracy tends to infinity
(`q -> 0` in Lean's inverse parameterization), the all-algorithm payoff
eventually exceeds the human-against-algorithm payoff used in Theorem 1.
-/
theorem paper_definition1_concreteMallowsSpec_asymptotic_first_dominance
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value) :
    ∀ θH lower, 0 < θH → θH < lower →
      ∃ hi, lower < hi ∧
        AccuracyFamily.theorem1_g
            ({ dist := fun θ => (concreteMallowsSpec center θ).law,
                value := value } : AccuracyFamily n)
            hi θH <
          AccuracyFamily.theorem1_f
            ({ dist := fun θ => (concreteMallowsSpec center θ).law,
                value := value } : AccuracyFamily n)
            hi θH :=
  concreteMallowsSpec_asymptotic_first_dominance center value hvalue

/--
Appendix C / Definition 4, strict well-ordered noise.

Paper statement: a noise density `f` is well-ordered when for any `a > b` and
`c > d`, the ordered assignment is more likely than the crossed assignment.
-/
theorem paper_definition4_strictlyWellOrderedNoise
    (f : ℝ → ℝ) (h : StrictlyWellOrderedNoise f) :
    StrictlyWellOrderedNoise f :=
  h

/--
Appendix C / Lemma 1, Gaussian part.

Paper statement: Gaussian noise is well-ordered.  Lean states this for the
positive-scale Gaussian density kernel `exp (-κ x^2)`; multiplying by the usual
positive normalizing constant does not change the product inequality.
-/
theorem paper_lemma1_gaussian_strictlyWellOrdered
    {κ : ℝ} (hκ : 0 < κ) :
    StrictlyWellOrderedNoise (gaussianNoiseKernel κ) :=
  gaussianNoiseKernel_strictlyWellOrdered hκ

/-- Gaussian kernel positivity, used by density-product mass comparisons. -/
theorem paper_lemma1_gaussianNoiseKernel_pos (κ x : ℝ) :
    0 < gaussianNoiseKernel κ x :=
  gaussianNoiseKernel_pos κ x

/--
Appendix C / Lemma 1, Laplacian weak form.

For the Laplacian density kernel `exp (-λ |x|)`, Lean proves the weak
well-ordering inequality.  This is the strongest globally valid pointwise form:
the strict paper inequality can be equality for separated ordered pairs.
-/
theorem paper_lemma1_laplacian_weaklyWellOrdered
    {lam : ℝ} (hlam : 0 ≤ lam) :
    WeaklyWellOrderedNoise (laplacianNoiseKernel lam) :=
  laplacianNoiseKernel_weaklyWellOrdered hlam

/-- Laplacian kernel positivity, used by density-product mass comparisons. -/
theorem paper_lemma1_laplacianNoiseKernel_pos (lam x : ℝ) :
    0 < laplacianNoiseKernel lam x :=
  laplacianNoiseKernel_pos lam x

/--
Appendix C / Lemma 1, Laplacian strict-form check.

With Definition 4 written using strict `>`, the Laplacian kernel does not satisfy
the stated pointwise condition: `a=10, b=9, c=1, d=0` gives equal products.
-/
theorem paper_lemma1_laplacian_not_strictlyWellOrdered
    (lam : ℝ) :
    ¬ StrictlyWellOrderedNoise (laplacianNoiseKernel lam) :=
  laplacianNoiseKernel_not_strictlyWellOrdered lam

/--
Appendix C / Lemma 1, Laplacian strict overlap case.

The Laplacian kernel does satisfy the strict product inequality on the region
where the ordered realized interval and ordered true-value interval overlap:
`a > b`, `c > d`, `b < c`, and `d < a`.
-/
theorem paper_lemma1_laplacian_strictlyWellOrdered_of_overlap
    {lam a b c d : ℝ} (hlam : 0 < lam)
    (hab : b < a) (hcd : d < c) (hbc : b < c) (hda : d < a) :
    laplacianNoiseKernel lam (a - c) * laplacianNoiseKernel lam (b - d) >
      laplacianNoiseKernel lam (a - d) * laplacianNoiseKernel lam (b - c) :=
  laplacianNoiseKernel_strictlyWellOrdered_of_overlap
    hlam hab hcd hbc hda

/--
Appendix C / Theorem 7, case 2 closed form.

Paper formula:
`1 - (1/2 + λ(a - x_j)) / (2 exp(λ(a - x_j)) - 1)`.
-/
noncomputable abbrev paper_theorem7_laplacian_case2_closedForm
    (lam xj a : ℝ) : ℝ :=
  1 - theorem7LaplacianCase2TailRatio lam xj a

/--
Appendix C / Theorem 7, case 3 closed form.

Paper formula after clearing the common positive factor:
`(8 - (4 + 2λ(x_i-x_j)) exp(-λ(x_i-x_j))
    - 4 exp(-λ(a-x_i)) + exp(-λ(2a-x_i-x_j))) /
  (4 - 2 exp(-λ(a-x_i)) - 2 exp(-λ(a-x_j))
    + exp(-λ(2a-x_i-x_j)))`.

Lean writes this as the same expression under
`z = λ(x_i-x_j)` and `r = exp(-λ(a-x_i))`.
-/
noncomputable abbrev paper_theorem7_laplacian_case3_closedForm
    (lam xi xj a : ℝ) : ℝ :=
  theorem7LaplacianCase3ConditionalProb lam xi xj a

/--
Appendix C / Theorem 7, Laplacian conditional pairwise derivative.

Lean proves the three closed-form derivative cases obtained in the paper after
integrating the Laplace density: the left case is constant, the middle and
right cases have strictly positive derivatives, and there is an explicit strict
witness with `x_j < a < x_i`.
-/
theorem paper_theorem7_laplacian_conditional_derivative_closed_forms
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (a ≤ xj →
      HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 a ∧ 0 ≤ (0 : ℝ)) ∧
    (xj < a → a ≤ xi →
      ∃ d,
        HasDerivAt
          (fun a => paper_theorem7_laplacian_case2_closedForm lam xj a) d a ∧
          0 < d) ∧
    (xi < a →
      ∃ d,
        HasDerivAt
          (fun a => paper_theorem7_laplacian_case3_closedForm lam xi xj a) d a ∧
          0 < d) ∧
    (∃ a d,
      xj < a ∧ a < xi ∧
        HasDerivAt
          (fun a => paper_theorem7_laplacian_case2_closedForm lam xj a) d a ∧
        0 < d) := by
  simpa [paper_theorem7_laplacian_case2_closedForm,
    paper_theorem7_laplacian_case3_closedForm] using
    (paper_theorem7_laplacian_closedForm_derivative_cases
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx)

/--
Appendix C / Theorem 7, Laplacian conditional pairwise derivative at the
split-integral layer.

Lean follows the paper's three integration regions in equation (C.3).  On the
interiors of those regions, the split-integral ratios are locally equal to the
closed forms above, so their derivatives have the same signs.  The case-3 ratio
is one half of the cleared closed form used for the sign calculation, a positive
constant factor.
-/
theorem paper_theorem7_laplacian_conditional_derivative_integral_ratios
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (a < xj →
      HasDerivAt
          (fun a => theorem7LaplacianCase1IntegralRatio lam xi xj a) 0 a ∧
        0 ≤ (0 : ℝ)) ∧
    (xj < a → a < xi →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianCase2IntegralRatio lam xi xj a) d a ∧
          0 < d) ∧
    (xi < a →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianCase3IntegralRatio lam xi xj a) d a ∧
          0 < d) ∧
    (∃ a d,
      xj < a ∧ a < xi ∧
        HasDerivAt
          (fun a => theorem7LaplacianCase2IntegralRatio lam xi xj a) d a ∧
        0 < d) :=
  paper_theorem7_laplacian_integralRatio_derivative_cases
    (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx

/--
Appendix C / Theorem 8, the C.9 bracket after defining
`g(t) = (1 + erf(t)) / exp(-t^2)`.
-/
noncomputable abbrev paper_theorem8_gaussian_c9_bracket (g : ℝ → ℝ)
    (δ t : ℝ) : ℝ :=
  theorem8GaussianC9Bracket g δ t

/--
Appendix C / Theorem 8, paper definition
`g(t) = (1 + erf(t)) / exp(-t^2)`.
-/
noncomputable abbrev paper_theorem8_gaussian_g (erf : ℝ → ℝ) (t : ℝ) : ℝ :=
  theorem8GaussianG erf t

/--
Appendix C / Theorem 8, paper's concrete error-function normalization
`erf(t) = (2 / sqrt(pi)) * ∫_0^t exp(-x^2) dx`.
-/
noncomputable abbrev paper_theorem8_erf (t : ℝ) : ℝ :=
  theorem8Erf t

/--
Appendix C / Theorem 8, derivative of the concrete `erf` interval integral.
-/
theorem paper_theorem8_erf_hasDerivAt (t : ℝ) :
    HasDerivAt paper_theorem8_erf
      ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t :=
  theorem8Erf_hasDerivAt t

/--
Appendix C / Theorem 8, left Gaussian tail in terms of the concrete `erf`.
-/
theorem paper_theorem8_gaussian_integral_Iic_eq_erf (t : ℝ) :
    (∫ x : ℝ in Set.Iic t, Real.exp (-(x ^ 2))) =
      Real.sqrt Real.pi / 2 * (1 + paper_theorem8_erf t) :=
  theorem8Gaussian_integral_Iic_eq_erf t

/--
Appendix C / Theorem 8, left-tail limit of the concrete `erf`:
`1 + erf(t) -> 0` as `t -> -∞`.
-/
theorem paper_theorem8_erf_tendsto_one_add_atBot_zero :
    Filter.Tendsto (fun t => 1 + paper_theorem8_erf t)
      Filter.atBot (nhds 0) :=
  theorem8Erf_tendsto_one_add_atBot_zero

/--
Appendix C / Theorem 8, positivity of `1 + erf(t)` for the concrete `erf`.
-/
theorem paper_theorem8_erf_one_add_pos (t : ℝ) :
    0 < 1 + paper_theorem8_erf t :=
  theorem8Erf_one_add_pos t

/--
Appendix C / Theorem 8, monotonicity of the concrete `erf` interval integral.
-/
theorem paper_theorem8_erf_strictMono : StrictMono paper_theorem8_erf :=
  theorem8Erf_strictMono

/--
Appendix C / Theorem 8, boundedness of the shifted concrete `erf` factor on
the left half-line used by `J(t)`.
-/
theorem paper_theorem8_erf_boundedOn_left_shift (δ : ℝ) :
    ∀ x ∈ Set.Iic (0 : ℝ),
      ‖paper_theorem8_erf (x + δ)‖ ≤ max 1 ‖paper_theorem8_erf δ‖ :=
  theorem8Erf_boundedOn_left_shift δ

/--
Appendix C / Theorem 8, shifted left-tail limit of the concrete `erf`.
-/
theorem paper_theorem8_erf_tendsto_one_add_atBot_zero_shift (δ : ℝ) :
    Filter.Tendsto (fun t => 1 + paper_theorem8_erf (t + δ))
      Filter.atBot (nhds 0) :=
  theorem8Erf_tendsto_one_add_atBot_zero_shift δ

/--
Appendix C / Theorem 8, rational term in equation (C.6), before subtracting
`1 + erf(t)` and the integral term.
-/
noncomputable abbrev paper_theorem8_gaussian_c6_rational_term
    (erf : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  theorem8GaussianC6RationalTerm erf δ t

/--
Appendix C / Theorem 8, equation (C.7): for the concrete `erf`, the C.6
rational term tends to zero as `t -> -∞`.
-/
theorem paper_theorem8_gaussian_c6_rational_term_tendsto_atBot_zero
    (δ : ℝ) :
    Filter.Tendsto
      (fun t => paper_theorem8_gaussian_c6_rational_term paper_theorem8_erf δ t)
      Filter.atBot (nhds 0) :=
  theorem8GaussianC6RationalTerm_tendsto_atBot_zero_concrete δ

/--
Appendix C / Theorem 8, paper integral
`J(t)=∫_{-∞}^t exp(-x^2) erf(x+δ) dx`.
-/
noncomputable abbrev paper_theorem8_gaussian_j
    (erf : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  theorem8GaussianJ erf δ t

/--
Appendix C / Theorem 8, the `J(t)` tail limit from integrability of its
left-half-line integrand.
-/
theorem paper_theorem8_gaussian_j_tendsto_atBot_zero_of_integrable
    {erf : ℝ → ℝ} {δ : ℝ}
    (hJ_integrable :
      IntegrableOn
        (fun x : ℝ => Real.exp (-(x ^ 2)) * erf (x + δ))
        (Set.Iic (0 : ℝ))) :
    Filter.Tendsto (paper_theorem8_gaussian_j erf δ)
      Filter.atBot (nhds 0) :=
  theorem8GaussianJ_tendsto_atBot_zero_of_integrableOn hJ_integrable

/--
Appendix C / Theorem 8, integrability of the concrete `J` integrand on the
left half-line.
-/
theorem paper_theorem8_gaussian_j_integrableOn_concrete (δ : ℝ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(x ^ 2)) * paper_theorem8_erf (x + δ))
      (Set.Iic (0 : ℝ)) :=
  theorem8GaussianJ_integrableOn_concrete δ

/--
Appendix C / Theorem 8, integrability of the concrete `J` integrand on any
left half-line.
-/
theorem paper_theorem8_gaussian_j_integrableOn_Iic_concrete (δ a : ℝ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(x ^ 2)) * paper_theorem8_erf (x + δ))
      (Set.Iic a) :=
  theorem8GaussianJ_integrableOn_Iic_concrete δ a

/--
Appendix C / Theorem 8, derivative of the concrete `J(t)` integral.
-/
theorem paper_theorem8_gaussian_j_hasDerivAt_concrete (δ t : ℝ) :
    HasDerivAt (paper_theorem8_gaussian_j paper_theorem8_erf δ)
      (Real.exp (-(t ^ 2)) * paper_theorem8_erf (t + δ)) t :=
  theorem8GaussianJ_hasDerivAt_concrete δ t

/--
Appendix C / Theorem 8, left-hand side of equation (C.6).

The argument `J` is the paper's integral
`J(t) = ∫_{-∞}^t exp(-x^2) erf(x + δ) dx`.
-/
noncomputable abbrev paper_theorem8_gaussian_c6_lhs
    (erf J : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  theorem8GaussianC6LHS erf J δ t

/--
Appendix C / Theorem 8, positive prefactor factored out of the derivative in
equation (C.8).
-/
noncomputable abbrev paper_theorem8_gaussian_c8_positive_factor
    (erf : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  theorem8GaussianC8PositiveFactor erf δ t

/--
Appendix C / Theorem 8, derivative from equation (C.8), after differentiating
the explicit C.6 formula and before factoring into the C.8 prefactor and C.9
bracket.
-/
noncomputable abbrev paper_theorem8_gaussian_c8_derivative (δ t : ℝ) : ℝ :=
  theorem8GaussianC8Derivative δ t

/--
Appendix C / Theorem 8, concrete C.6 left-hand side has the derivative shown
in equation (C.8).
-/
theorem paper_theorem8_gaussian_c6_lhs_hasDerivAt_concrete_c8
    (δ t : ℝ) :
    HasDerivAt
      (fun u =>
        paper_theorem8_gaussian_c6_lhs paper_theorem8_erf
          (paper_theorem8_gaussian_j paper_theorem8_erf δ) δ u)
      (paper_theorem8_gaussian_c8_derivative δ t) t :=
  theorem8GaussianC6LHS_hasDerivAt_concrete_C8 δ t

/--
Appendix C / Theorem 8, equation (C.8) factors as the positive C.8 prefactor
times the C.9 bracket.  The Lean factor is the algebraically correct factor
matching C.9; the paper's displayed prefactor appears to contain a typo.
-/
theorem paper_theorem8_gaussian_c8_derivative_factorization
    (δ t : ℝ) :
    paper_theorem8_gaussian_c8_derivative δ t =
      paper_theorem8_gaussian_c8_positive_factor paper_theorem8_erf δ t *
        paper_theorem8_gaussian_c9_bracket
          (paper_theorem8_gaussian_g paper_theorem8_erf) δ t :=
  theorem8GaussianC8Derivative_factorization δ t

/--
Appendix C / Theorem 8, Mills ratio as used in the paper:
`R(t)=exp(t^2/2)∫_t^∞ exp(-x^2/2)dx`.
-/
noncomputable abbrev paper_theorem8_mills_ratio (t : ℝ) : ℝ :=
  theorem8MillsRatio t

/-- Appendix C / Theorem 8, Gaussian tail integral inside Mills ratio. -/
noncomputable abbrev paper_theorem8_mills_tail (t : ℝ) : ℝ :=
  theorem8MillsTail t

/-- Appendix C / Theorem 8, derivative of the Mills-ratio Gaussian tail. -/
theorem paper_theorem8_mills_tail_hasDerivAt (t : ℝ) :
    HasDerivAt paper_theorem8_mills_tail
      (-(Real.exp (-(t ^ 2) / 2))) t :=
  theorem8MillsTail_hasDerivAt t

/-- Appendix C / Theorem 8, derivative of the concrete Mills ratio. -/
theorem paper_theorem8_mills_ratio_hasDerivAt (t : ℝ) :
    HasDerivAt paper_theorem8_mills_ratio
      (t * paper_theorem8_mills_ratio t - 1) t :=
  theorem8MillsRatio_hasDerivAt t

/--
Appendix C / Theorem 8, derivative of the Mills-ratio derivative expression:
`R''(t) = (t^2+1)R(t)-t`.
-/
theorem paper_theorem8_mills_ratio_derivExpr_hasDerivAt (t : ℝ) :
    HasDerivAt
      (fun u => u * paper_theorem8_mills_ratio u - 1)
      (((t ^ 2 + 1) * paper_theorem8_mills_ratio t) - t) t :=
  theorem8MillsRatio_derivExpr_hasDerivAt t

/--
Appendix C / Theorem 8, the paper's concrete value relation between Mills ratio
and `g(t)`.
-/
theorem paper_theorem8_mills_ratio_value_relation (t : ℝ) :
    paper_theorem8_mills_ratio (-(Real.sqrt 2 * t)) =
      Real.sqrt (Real.pi / 2) *
        paper_theorem8_gaussian_g paper_theorem8_erf t :=
  theorem8MillsRatio_value_relation t

/--
Appendix C / Theorem 8, change of variables in the Mills-ratio tail integral.
-/
theorem paper_theorem8_mills_ratio_tail_changeOfVariables (t : ℝ) :
    (∫ x : ℝ in Set.Ioi (-(Real.sqrt 2 * t)),
        Real.exp (-(x ^ 2) / 2)) =
      Real.sqrt 2 * ∫ x : ℝ in Set.Iic t, Real.exp (-(x ^ 2)) :=
  theorem8MillsRatio_tail_changeOfVariables t

/-- Appendix C / Theorem 8, positivity of the concrete Mills ratio. -/
theorem paper_theorem8_mills_ratio_pos (t : ℝ) :
    0 < paper_theorem8_mills_ratio t :=
  theorem8MillsRatio_pos t

/--
Appendix C / Theorem 8, external Mills-ratio input cited from Sampford:
`d/dt (1 / R(t)) < 1`.
-/
abbrev paper_theorem8_sampford_mills_bound (R : ℝ → ℝ) : Prop :=
  theorem8SampfordMillsBound R

/--
Appendix C / Theorem 8, scalar Mills inequality equivalent to Sampford's
derivative bound once `R' = tR - 1` is known.
-/
abbrev paper_theorem8_mills_quadratic_bound (R : ℝ → ℝ) : Prop :=
  theorem8MillsQuadraticBound R

/--
Appendix C / Theorem 8, Sampford's explicit lower comparison function
`(sqrt(t^2+4)-t)/2`.
-/
noncomputable abbrev paper_theorem8_sampford_lower_comparison (t : ℝ) : ℝ :=
  theorem8SampfordLowerComparison t

/-- Appendix C / Theorem 8, positivity of Sampford's lower comparison. -/
theorem paper_theorem8_sampford_lower_comparison_pos (t : ℝ) :
    0 < paper_theorem8_sampford_lower_comparison t :=
  theorem8SampfordLowerComparison_pos t

/--
Appendix C / Theorem 8, for nonnegative arguments Sampford's lower comparison
is bounded by `1`.
-/
theorem paper_theorem8_sampford_lower_comparison_le_one_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    paper_theorem8_sampford_lower_comparison t ≤ 1 :=
  theorem8SampfordLowerComparison_le_one_of_nonneg ht

/--
Appendix C / Theorem 8, the comparison function solves
`x^2 + t*x - 1 = 0`.
-/
theorem paper_theorem8_sampford_lower_comparison_quadratic_eq (t : ℝ) :
    (paper_theorem8_sampford_lower_comparison t) ^ 2 +
        t * paper_theorem8_sampford_lower_comparison t - 1 = 0 :=
  theorem8SampfordLowerComparison_quadratic_eq t

/--
Appendix C / Theorem 8, the Sampford gap tends to zero at `+∞`.
-/
theorem paper_theorem8_sampford_gap_tendsto_atTop_zero :
    Filter.Tendsto theorem8SampfordGap Filter.atTop (nhds 0) :=
  theorem8SampfordGap_tendsto_atTop_zero

/--
Appendix C / Theorem 8, Sampford's explicit lower comparison holds for the
concrete Gaussian Mills ratio.
-/
theorem paper_theorem8_sampford_lower_bound_for_concrete_mills_ratio :
    ∀ t,
      paper_theorem8_sampford_lower_comparison t <
        paper_theorem8_mills_ratio t :=
  theorem8SampfordLowerComparison_lt_millsRatio

/--
Appendix C / Theorem 8, Sampford's explicit lower bound implies the scalar
quadratic Mills inequality.
-/
theorem paper_theorem8_mills_quadratic_bound_of_sampford_lower
    {R : ℝ → ℝ}
    (hRpos : ∀ t, 0 < R t)
    (hlower : ∀ t, paper_theorem8_sampford_lower_comparison t < R t) :
    paper_theorem8_mills_quadratic_bound R :=
  theorem8MillsQuadraticBound_of_sampford_lower hRpos hlower

/--
Appendix C / Theorem 8, concrete Sampford-lower-bound reduction for the Mills
ratio used in this paper.
-/
theorem paper_theorem8_mills_quadratic_bound_of_sampford_lower_concrete
    (hlower :
      ∀ t, paper_theorem8_sampford_lower_comparison t <
        paper_theorem8_mills_ratio t) :
    paper_theorem8_mills_quadratic_bound paper_theorem8_mills_ratio :=
  theorem8MillsQuadraticBound_of_sampford_lower_concrete hlower

/--
Appendix C / Theorem 8, concrete scalar Mills quadratic inequality.
-/
theorem paper_theorem8_mills_quadratic_bound_concrete :
    paper_theorem8_mills_quadratic_bound paper_theorem8_mills_ratio :=
  theorem8MillsQuadraticBound_concrete

/--
Appendix C / Theorem 8, log-convexity/determinant form of the remaining
Mills-ratio inequality, `R R'' - (R')^2 > 0`.
-/
abbrev paper_theorem8_mills_determinant_bound (R : ℝ → ℝ) : Prop :=
  theorem8MillsDeterminantBound R

/--
Appendix C / Theorem 8, the concrete determinant/log-convexity bound implies
the scalar quadratic Mills inequality used for Sampford.
-/
theorem paper_theorem8_mills_quadratic_bound_of_determinant
    (hdet :
      paper_theorem8_mills_determinant_bound paper_theorem8_mills_ratio) :
    paper_theorem8_mills_quadratic_bound paper_theorem8_mills_ratio :=
  theorem8MillsQuadraticBound_of_determinant hdet

/--
Appendix C / Theorem 8, concrete Sampford reduction: after the Mills-ratio
calculus is formalized, the remaining external analytic input can be stated as
the scalar quadratic Mills inequality.
-/
theorem paper_theorem8_sampford_mills_bound_of_quadratic
    (hquad : paper_theorem8_mills_quadratic_bound paper_theorem8_mills_ratio) :
    paper_theorem8_sampford_mills_bound paper_theorem8_mills_ratio :=
  theorem8SampfordMillsBound_of_quadratic hquad

/--
Appendix C / Theorem 8, concrete Sampford Mills-ratio derivative bound.
-/
theorem paper_theorem8_sampford_mills_bound_concrete :
    paper_theorem8_sampford_mills_bound paper_theorem8_mills_ratio :=
  theorem8SampfordMillsBound_concrete

/--
Appendix C / Theorem 8, concrete Sampford reduction from the
determinant/log-convexity form.
-/
theorem paper_theorem8_sampford_mills_bound_of_determinant
    (hdet :
      paper_theorem8_mills_determinant_bound paper_theorem8_mills_ratio) :
    paper_theorem8_sampford_mills_bound paper_theorem8_mills_ratio :=
  theorem8SampfordMillsBound_of_determinant hdet

/--
Appendix C / Theorem 8, Mills-to-`g` relation used after the change of
variables: `1 / g(t) = c * 1 / R(-q t)`.
-/
abbrev paper_theorem8_mills_to_g_relation (R g : ℝ → ℝ) (c q : ℝ) : Prop :=
  theorem8MillsToGRelation R g c q

/--
Appendix C / Theorem 8, Gaussian conditional pairwise derivative at the C.6
scalar layer.

This is the paper's proof skeleton after reducing the conditional probability
derivative to the C.6 function `F`: the C.6 expression has limit `0` at
`-∞`, its derivative factors into a positive prefactor times the C.9 bracket,
and Sampford's Mills-ratio bound proves the C.10 inequality needed for the
C.9 bracket to be positive.
-/
theorem paper_theorem8_gaussian_c6_positive_of_sampford_mills
    {R g F F' factor : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hrel :
      paper_theorem8_mills_to_g_relation
        R g (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : paper_theorem8_sampford_mills_bound R)
    (hgpos : ∀ t, 0 < g t)
    (hcont : ∀ t, ContinuousOn (fun u => (g u)⁻¹) (Set.Icc t (t + δ)))
    (hFderiv : ∀ t, HasDerivAt F (F' t) t)
    (hFlim : Filter.Tendsto F Filter.atBot (nhds 0))
    (hfactor :
      ∀ t, F' t = factor t * paper_theorem8_gaussian_c9_bracket g δ t)
    (hfactor_pos : ∀ t, 0 < factor t) :
    ∀ t, 0 < F t :=
  paper_theorem8_c6_positive_of_sampford_mills_concrete
    (R := R) (g := g) (F := F) (F' := F') (factor := factor)
    (δ := δ) hδ hrel hsamp hgpos hcont hFderiv hFlim
    hfactor hfactor_pos

/--
Appendix C / Theorem 8, Gaussian conditional pairwise derivative at the explicit
C.6 formula layer.

This wrapper exposes the paper's C.6 formula and the C.8 positive prefactor.
The remaining assumptions are the analytic bridges still to instantiate:
Sampford's cited Mills-ratio bound, the Mills-to-`g` identity, continuity of
`1/g`, the C.6 limit at `-∞`, and the derivative/factorization calculation.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_of_sampford_mills
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hone : ∀ t, 0 < 1 + erf t)
    (hrel :
      paper_theorem8_mills_to_g_relation
        R (paper_theorem8_gaussian_g erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : paper_theorem8_sampford_mills_bound R)
    (hcont :
      ∀ t,
        ContinuousOn
          (fun u => (paper_theorem8_gaussian_g erf u)⁻¹)
          (Set.Icc t (t + δ)))
    (hlim :
      Filter.Tendsto (fun t => paper_theorem8_gaussian_c6_lhs erf J δ t)
        Filter.atBot (nhds 0))
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => paper_theorem8_gaussian_c6_lhs erf J δ u)
          (paper_theorem8_gaussian_c8_positive_factor erf δ t *
            paper_theorem8_gaussian_c9_bracket
              (paper_theorem8_gaussian_g erf) δ t) t) :
    ∀ t, 0 < paper_theorem8_gaussian_c6_lhs erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ hone hrel hsamp hcont hlim hderiv_factor

/--
Appendix C / Theorem 8, explicit C.6 formula layer with `1/g` continuity
discharged from continuity of `erf`.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_of_continuous_erf
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf : Continuous erf) (hone : ∀ t, 0 < 1 + erf t)
    (hrel :
      paper_theorem8_mills_to_g_relation
        R (paper_theorem8_gaussian_g erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : paper_theorem8_sampford_mills_bound R)
    (hlim :
      Filter.Tendsto (fun t => paper_theorem8_gaussian_c6_lhs erf J δ t)
        Filter.atBot (nhds 0))
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => paper_theorem8_gaussian_c6_lhs erf J δ u)
          (paper_theorem8_gaussian_c8_positive_factor erf δ t *
            paper_theorem8_gaussian_c9_bracket
              (paper_theorem8_gaussian_g erf) δ t) t) :
    ∀ t, 0 < paper_theorem8_gaussian_c6_lhs erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills_of_continuous_erf
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ herf hone hrel hsamp hlim hderiv_factor

/--
Appendix C / Theorem 8, explicit C.6 formula layer with continuity of `erf`
derived from the standard derivative formula for `erf`.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_of_erf_deriv
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (hone : ∀ t, 0 < 1 + erf t)
    (hrel :
      paper_theorem8_mills_to_g_relation
        R (paper_theorem8_gaussian_g erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : paper_theorem8_sampford_mills_bound R)
    (hlim :
      Filter.Tendsto (fun t => paper_theorem8_gaussian_c6_lhs erf J δ t)
        Filter.atBot (nhds 0))
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => paper_theorem8_gaussian_c6_lhs erf J δ u)
          (paper_theorem8_gaussian_c8_positive_factor erf δ t *
            paper_theorem8_gaussian_c9_bracket
              (paper_theorem8_gaussian_g erf) δ t) t) :
    ∀ t, 0 < paper_theorem8_gaussian_c6_lhs erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills_of_erf_deriv
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ herf_deriv hone hrel hsamp hlim hderiv_factor

/--
Appendix C / Theorem 8, explicit C.6 formula layer with positivity of
`1 + erf` derived from the standard left-tail limit.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_of_erf_deriv_and_tail
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (herf_tail :
      Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0))
    (hrel :
      paper_theorem8_mills_to_g_relation
        R (paper_theorem8_gaussian_g erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : paper_theorem8_sampford_mills_bound R)
    (hlim :
      Filter.Tendsto (fun t => paper_theorem8_gaussian_c6_lhs erf J δ t)
        Filter.atBot (nhds 0))
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => paper_theorem8_gaussian_c6_lhs erf J δ u)
          (paper_theorem8_gaussian_c8_positive_factor erf δ t *
            paper_theorem8_gaussian_c9_bracket
              (paper_theorem8_gaussian_g erf) δ t) t) :
    ∀ t, 0 < paper_theorem8_gaussian_c6_lhs erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills_of_erf_deriv_and_tail
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ herf_deriv herf_tail hrel hsamp hlim hderiv_factor

/--
Appendix C / Theorem 8, explicit C.6 formula layer with the C.6 limit assembled
from the component limits used after equation (C.7).
-/
theorem paper_theorem8_gaussian_c6_formula_positive_of_component_limits
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (herf_tail :
      Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0))
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hratio :
      Filter.Tendsto
        (fun t => paper_theorem8_gaussian_c6_rational_term erf δ t)
        Filter.atBot (nhds 0))
    (hrel :
      paper_theorem8_mills_to_g_relation
        R (paper_theorem8_gaussian_g erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : paper_theorem8_sampford_mills_bound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => paper_theorem8_gaussian_c6_lhs erf J δ u)
          (paper_theorem8_gaussian_c8_positive_factor erf δ t *
            paper_theorem8_gaussian_c9_bracket
              (paper_theorem8_gaussian_g erf) δ t) t) :
    ∀ t, 0 < paper_theorem8_gaussian_c6_lhs erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills_of_component_limits
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ herf_deriv herf_tail hJ_tail hratio hrel hsamp hderiv_factor

/--
Appendix C / Theorem 8, explicit C.6 formula layer with the Mills relation
stated as in the paper:
`R(-sqrt(2)t) = sqrt(pi/2) * g(t)`.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_of_mills_value_relation
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (herf_tail :
      Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0))
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hratio :
      Filter.Tendsto
        (fun t => paper_theorem8_gaussian_c6_rational_term erf δ t)
        Filter.atBot (nhds 0))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * paper_theorem8_gaussian_g erf t)
    (hsamp : paper_theorem8_sampford_mills_bound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => paper_theorem8_gaussian_c6_lhs erf J δ u)
          (paper_theorem8_gaussian_c8_positive_factor erf δ t *
            paper_theorem8_gaussian_c9_bracket
              (paper_theorem8_gaussian_g erf) δ t) t) :
    ∀ t, 0 < paper_theorem8_gaussian_c6_lhs erf J δ t :=
  paper_theorem8_c6_formula_positive_of_component_limits_value_relation
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ herf_deriv herf_tail hJ_tail hratio hrel_value hsamp
    hderiv_factor

/--
Appendix C / Theorem 8 specialized to the paper's concrete interval-integral
`erf`.  This wrapper has no separate `erf` derivative hypothesis; the remaining
assumptions are exactly the paper's tail/component-limit, Mills-ratio, and C.6
derivative-factorization bridges.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_for_concrete_erf
    {R J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_tail :
      Filter.Tendsto (fun t => 1 + paper_theorem8_erf t) Filter.atBot (nhds 0))
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hratio :
      Filter.Tendsto
        (fun t => paper_theorem8_gaussian_c6_rational_term
          paper_theorem8_erf δ t)
        Filter.atBot (nhds 0))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) *
            paper_theorem8_gaussian_g paper_theorem8_erf t)
    (hsamp : paper_theorem8_sampford_mills_bound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u => paper_theorem8_gaussian_c6_lhs paper_theorem8_erf J δ u)
          (paper_theorem8_gaussian_c8_positive_factor paper_theorem8_erf δ t *
            paper_theorem8_gaussian_c9_bracket
              (paper_theorem8_gaussian_g paper_theorem8_erf) δ t) t) :
    ∀ t, 0 < paper_theorem8_gaussian_c6_lhs paper_theorem8_erf J δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf
    (R := R) (J := J) (δ := δ)
    hδ herf_tail hJ_tail hratio hrel_value hsamp hderiv_factor

/--
Appendix C / Theorem 8 specialized to the paper's concrete interval-integral
`erf`, with the derivative and left-tail limit both proved locally.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_for_concrete_erf_of_component_limits
    {R J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hratio :
      Filter.Tendsto
        (fun t => paper_theorem8_gaussian_c6_rational_term
          paper_theorem8_erf δ t)
        Filter.atBot (nhds 0))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) *
            paper_theorem8_gaussian_g paper_theorem8_erf t)
    (hsamp : paper_theorem8_sampford_mills_bound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u => paper_theorem8_gaussian_c6_lhs paper_theorem8_erf J δ u)
          (paper_theorem8_gaussian_c8_positive_factor paper_theorem8_erf δ t *
            paper_theorem8_gaussian_c9_bracket
              (paper_theorem8_gaussian_g paper_theorem8_erf) δ t) t) :
    ∀ t, 0 < paper_theorem8_gaussian_c6_lhs paper_theorem8_erf J δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf_of_component_limits
    (R := R) (J := J) (δ := δ)
    hδ hJ_tail hratio hrel_value hsamp hderiv_factor

/--
Appendix C / Theorem 8 specialized to the concrete interval-integral `erf`,
with the derivative, left-tail limit, and C.7 rational-term limit proved
locally.  The remaining analytic assumptions are the C.6 integral tail, the
Mills-ratio value identity/Sampford input, and the C.6 derivative
factorization.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_for_concrete_erf_of_integral_tail
    {R J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) *
            paper_theorem8_gaussian_g paper_theorem8_erf t)
    (hsamp : paper_theorem8_sampford_mills_bound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u => paper_theorem8_gaussian_c6_lhs paper_theorem8_erf J δ u)
          (paper_theorem8_gaussian_c8_positive_factor paper_theorem8_erf δ t *
            paper_theorem8_gaussian_c9_bracket
              (paper_theorem8_gaussian_g paper_theorem8_erf) δ t) t) :
    ∀ t, 0 < paper_theorem8_gaussian_c6_lhs paper_theorem8_erf J δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf_of_integral_tail
    (R := R) (J := J) (δ := δ)
    hδ hJ_tail hrel_value hsamp hderiv_factor

/--
Appendix C / Theorem 8 specialized to the concrete interval-integral `erf` and
the paper's concrete `J`, deriving the `J` tail limit from integrability of its
integrand.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_for_concrete_erf_and_j_of_integrable
    {R : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hJ_integrable :
      IntegrableOn
        (fun x : ℝ => Real.exp (-(x ^ 2)) * paper_theorem8_erf (x + δ))
        (Set.Iic (0 : ℝ)))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) *
            paper_theorem8_gaussian_g paper_theorem8_erf t)
    (hsamp : paper_theorem8_sampford_mills_bound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u =>
            paper_theorem8_gaussian_c6_lhs paper_theorem8_erf
              (paper_theorem8_gaussian_j paper_theorem8_erf δ) δ u)
          (paper_theorem8_gaussian_c8_positive_factor paper_theorem8_erf δ t *
            paper_theorem8_gaussian_c9_bracket
              (paper_theorem8_gaussian_g paper_theorem8_erf) δ t) t) :
    ∀ t,
      0 <
        paper_theorem8_gaussian_c6_lhs paper_theorem8_erf
          (paper_theorem8_gaussian_j paper_theorem8_erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf_and_J_of_integrable
    (R := R) (δ := δ)
    hδ hJ_integrable hrel_value hsamp hderiv_factor

/--
Appendix C / Theorem 8 specialized to the concrete interval-integral `erf` and
the paper's concrete `J`.  The derivative of `erf`, the `erf` left-tail limit,
the C.7 rational-term limit, and the `J` left-tail limit are proved locally.
The remaining assumptions are the Mills-ratio value identity, Sampford's cited
Mills-ratio derivative bound, and the C.6 derivative factorization.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_for_concrete_erf_and_j
    {R : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) *
            paper_theorem8_gaussian_g paper_theorem8_erf t)
    (hsamp : paper_theorem8_sampford_mills_bound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u =>
            paper_theorem8_gaussian_c6_lhs paper_theorem8_erf
              (paper_theorem8_gaussian_j paper_theorem8_erf δ) δ u)
          (paper_theorem8_gaussian_c8_positive_factor paper_theorem8_erf δ t *
            paper_theorem8_gaussian_c9_bracket
              (paper_theorem8_gaussian_g paper_theorem8_erf) δ t) t) :
    ∀ t,
      0 <
        paper_theorem8_gaussian_c6_lhs paper_theorem8_erf
          (paper_theorem8_gaussian_j paper_theorem8_erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf_and_J
    (R := R) (δ := δ) hδ hrel_value hsamp hderiv_factor

/--
Appendix C / Theorem 8 specialized to the paper's concrete Mills ratio,
concrete interval-integral `erf`, and concrete `J`.  The remaining assumptions
are Sampford's cited Mills-ratio derivative bound and the C.6 derivative
factorization.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_for_concrete_mills_erf_and_j
    {δ : ℝ} (hδ : 0 < δ)
    (hsamp : paper_theorem8_sampford_mills_bound paper_theorem8_mills_ratio)
    (hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u =>
            paper_theorem8_gaussian_c6_lhs paper_theorem8_erf
              (paper_theorem8_gaussian_j paper_theorem8_erf δ) δ u)
          (paper_theorem8_gaussian_c8_positive_factor paper_theorem8_erf δ t *
            paper_theorem8_gaussian_c9_bracket
              (paper_theorem8_gaussian_g paper_theorem8_erf) δ t) t) :
    ∀ t,
      0 <
        paper_theorem8_gaussian_c6_lhs paper_theorem8_erf
          (paper_theorem8_gaussian_j paper_theorem8_erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J
    (δ := δ) hδ hsamp hderiv_factor

/--
Appendix C / Theorem 8 specialized to the paper's concrete Mills ratio,
concrete interval-integral `erf`, and concrete `J`, with the C.6 derivative
factorization discharged locally.  The remaining scalar analytic input is
Sampford's cited Mills-ratio derivative bound.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_for_concrete_mills_erf_and_j_of_sampford
    {δ : ℝ} (hδ : 0 < δ)
    (hsamp : paper_theorem8_sampford_mills_bound paper_theorem8_mills_ratio) :
    ∀ t,
      0 <
        paper_theorem8_gaussian_c6_lhs paper_theorem8_erf
          (paper_theorem8_gaussian_j paper_theorem8_erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J_of_sampford
    (δ := δ) hδ hsamp

/--
Appendix C / Theorem 8 specialized to the paper's concrete Mills ratio,
concrete interval-integral `erf`, and concrete `J`, with Sampford's
Mills-ratio derivative bound and the C.6 derivative factorization both
discharged locally.
-/
theorem paper_theorem8_gaussian_c6_formula_positive_for_concrete_mills_erf_and_j_unconditional
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ t,
      0 <
        paper_theorem8_gaussian_c6_lhs paper_theorem8_erf
          (paper_theorem8_gaussian_j paper_theorem8_erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J_unconditional
    (δ := δ) hδ

/--
Appendix C / Theorem 8, Gaussian conditional pairwise probability expression
after the paper's density/CDF integral calculation and the substitution
`t = a - x_i`, `δ = x_i - x_j`.
-/
noncomputable abbrev paper_theorem8_gaussian_conditional_integral_ratio
    (erf J : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  theorem8GaussianConditionalIntegralRatio erf J δ t

/--
Appendix C / Theorem 8, the derivative of the concrete Gaussian conditional
integral ratio is positive.  This is the C.5-to-C.6 quotient-rule bridge after
the density/CDF formula has been obtained.
-/
theorem paper_theorem8_gaussian_conditional_integral_ratio_hasDerivAt_pos
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∃ d,
      HasDerivAt
        (fun u =>
          paper_theorem8_gaussian_conditional_integral_ratio paper_theorem8_erf
            (paper_theorem8_gaussian_j paper_theorem8_erf δ) δ u) d t ∧
        0 < d :=
  theorem8GaussianConditionalIntegralRatio_hasDerivAt_pos hδ t

/--
Appendix C / Theorem 8, Gaussian conditional integral ratio in the paper's
original cutoff coordinate `a`.
-/
noncomputable abbrev paper_theorem8_gaussian_conditional_integral_ratio_at
    (xi xj a : ℝ) : ℝ :=
  theorem8GaussianConditionalIntegralRatioAt xi xj a

/--
Appendix C / Theorem 8 at the Gaussian integral-ratio layer, in the paper's
original `a, x_i, x_j` coordinates.
-/
theorem paper_theorem8_gaussian_conditional_integral_ratio_at_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => paper_theorem8_gaussian_conditional_integral_ratio_at xi xj u)
        d a ∧
        0 < d :=
  theorem8GaussianConditionalIntegralRatioAt_hasDerivAt_pos hx

/--
Appendix C / Theorem 8, Gaussian density in the paper's `σ = 1/sqrt 2`
normalization.
-/
noncomputable abbrev paper_theorem8_gaussian_pdf (μ x : ℝ) : ℝ :=
  theorem8GaussianPDF μ x

/--
Appendix C / Theorem 8, the paper Gaussian density is Mathlib's real Gaussian
PDF with variance `1/2`.
-/
theorem paper_theorem8_gaussian_pdf_eq_gaussianPDFReal_half (μ x : ℝ) :
    paper_theorem8_gaussian_pdf μ x =
      ProbabilityTheory.gaussianPDFReal μ (1 / 2 : ℝ≥0) x :=
  theorem8GaussianPDF_eq_gaussianPDFReal_half μ x

/--
Appendix C / Theorem 8, Gaussian CDF in the paper's normalization.
-/
noncomputable abbrev paper_theorem8_gaussian_cdf (μ a : ℝ) : ℝ :=
  theorem8GaussianCDF μ a

/--
Appendix C / Theorem 8, the paper CDF is the left integral of the paper
Gaussian density.
-/
theorem paper_theorem8_gaussian_pdf_integral_Iic_eq_cdf (μ a : ℝ) :
    (∫ x : ℝ in Set.Iic a, paper_theorem8_gaussian_pdf μ x) =
      paper_theorem8_gaussian_cdf μ a :=
  theorem8GaussianPDF_integral_Iic_eq_CDF μ a

/--
Appendix C / Theorem 8, Mathlib's Gaussian measure at variance `1/2` has the
paper CDF as its left-half-line mass.
-/
theorem paper_theorem8_gaussianReal_Iic_eq_cdf (μ a : ℝ) :
    ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0) (Set.Iic a) =
      ENNReal.ofReal (paper_theorem8_gaussian_cdf μ a) :=
  theorem8GaussianReal_Iic_eq_CDF μ a

/--
Appendix C / Theorem 8, the paper numerator integral after shifting to centered
coordinates and splitting into the `erf` tail plus `J`.
-/
theorem paper_theorem8_gaussian_integral_shift_split (xi xj a : ℝ) :
    (∫ x : ℝ in Set.Iic a,
        Real.exp (-((x - xi) ^ 2)) * (1 + paper_theorem8_erf (x - xj))) =
      Real.sqrt Real.pi / 2 * (1 + paper_theorem8_erf (a - xi)) +
        paper_theorem8_gaussian_j paper_theorem8_erf (xi - xj) (a - xi) :=
  theorem8Gaussian_integral_shift_split xi xj a

/--
Appendix C / Theorem 8, the paper density/CDF conditional probability integral
ratio before clearing constants.
-/
noncomputable abbrev paper_theorem8_gaussian_pdf_cdf_ratio_at
    (xi xj a : ℝ) : ℝ :=
  theorem8GaussianPDFCDFRatioAt xi xj a

/--
Appendix C / Theorem 8, the same ratio after clearing the Gaussian constants.
-/
noncomputable abbrev paper_theorem8_gaussian_density_cdf_integral_ratio_at
    (xi xj a : ℝ) : ℝ :=
  theorem8GaussianDensityCDFIntegralRatioAt xi xj a

/--
Appendix C / Theorem 8, clearing the Gaussian density/CDF constants in the
paper's integral ratio.
-/
theorem paper_theorem8_gaussian_pdf_cdf_ratio_at_eq_density_cdf
    (xi xj a : ℝ) :
    paper_theorem8_gaussian_pdf_cdf_ratio_at xi xj a =
      paper_theorem8_gaussian_density_cdf_integral_ratio_at xi xj a :=
  theorem8GaussianPDFCDFRatioAt_eq_densityCDF xi xj a

/--
Appendix C / Theorem 8, the density/CDF integral ratio equals the `erf/J`
conditional integral ratio used for the C.5--C.6 derivative proof.
-/
theorem paper_theorem8_gaussian_density_cdf_integral_ratio_at_eq_conditional
    (xi xj a : ℝ) :
    paper_theorem8_gaussian_density_cdf_integral_ratio_at xi xj a =
      paper_theorem8_gaussian_conditional_integral_ratio_at xi xj a :=
  theorem8GaussianDensityCDFIntegralRatioAt_eq_conditional xi xj a

/--
Appendix C / Theorem 8, the paper density/CDF integral ratio has strictly
positive derivative in the cutoff `a`.
-/
theorem paper_theorem8_gaussian_pdf_cdf_ratio_at_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => paper_theorem8_gaussian_pdf_cdf_ratio_at xi xj u) d a ∧
        0 < d :=
  theorem8GaussianPDFCDFRatioAt_hasDerivAt_pos hx

/--
Appendix C / Theorem 8, canonical product measure for independent Gaussian
scores with means `x_i`, `x_j` and variance `1/2`.
-/
noncomputable abbrev paper_theorem8_gaussian_pair_measure
    (xi xj : ℝ) : Measure (ℝ × ℝ) :=
  theorem8GaussianPairMeasure xi xj

/--
Appendix C / Theorem 8, product numerator event, stated with weak inequalities
on null Gaussian boundaries.
-/
abbrev paper_theorem8_gaussian_pair_numerator_event (a : ℝ) : Set (ℝ × ℝ) :=
  theorem8GaussianPairNumeratorEvent a

/--
Appendix C / Theorem 8, product conditioning event, stated with weak
inequalities on null Gaussian boundaries.
-/
abbrev paper_theorem8_gaussian_pair_denominator_event (a : ℝ) : Set (ℝ × ℝ) :=
  theorem8GaussianPairDenominatorEvent a

/--
Appendix C / Theorem 8, product numerator event in the paper's strict syntax:
`X_i < a`, `X_j < X_i`.
-/
abbrev paper_theorem8_gaussian_pair_strict_numerator_event
    (a : ℝ) : Set (ℝ × ℝ) :=
  theorem8GaussianPairStrictNumeratorEvent a

/--
Appendix C / Theorem 8, product conditioning event in the paper's strict
syntax: `X_i < a`, `X_j < a`.
-/
abbrev paper_theorem8_gaussian_pair_strict_denominator_event
    (a : ℝ) : Set (ℝ × ℝ) :=
  theorem8GaussianPairStrictDenominatorEvent a

/--
Appendix C / Theorem 8, no-atom erasure for a one-dimensional Gaussian cutoff:
strict and weak lower intervals have the same mass.
-/
theorem paper_theorem8_gaussianReal_Iio_eq_Iic (μ a : ℝ) :
    ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0) (Set.Iio a) =
      ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0) (Set.Iic a) :=
  theorem8GaussianReal_Iio_eq_Iic μ a

/--
Appendix C / Theorem 8, Fubini/density bridge for the product numerator event.
-/
theorem paper_theorem8_gaussian_pair_numerator_measure_eq_integral
    (xi xj a : ℝ) :
    paper_theorem8_gaussian_pair_measure xi xj
        (paper_theorem8_gaussian_pair_numerator_event a) =
      ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          paper_theorem8_gaussian_pdf xi x *
          paper_theorem8_gaussian_cdf xj x) :=
  theorem8GaussianPairNumerator_measure_eq_integral xi xj a

/--
Appendix C / Theorem 8, Fubini/density bridge for the strict paper-syntax
product numerator event.
-/
theorem paper_theorem8_gaussian_pair_strict_numerator_measure_eq_integral
    (xi xj a : ℝ) :
    paper_theorem8_gaussian_pair_measure xi xj
        (paper_theorem8_gaussian_pair_strict_numerator_event a) =
      ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          paper_theorem8_gaussian_pdf xi x *
            paper_theorem8_gaussian_cdf xj x) :=
  theorem8GaussianPairStrictNumerator_measure_eq_integral xi xj a

/--
Appendix C / Theorem 8, product-measure mass of the conditioning event.
-/
theorem paper_theorem8_gaussian_pair_denominator_measure_eq
    (xi xj a : ℝ) :
    paper_theorem8_gaussian_pair_measure xi xj
        (paper_theorem8_gaussian_pair_denominator_event a) =
      ENNReal.ofReal
        (paper_theorem8_gaussian_cdf xi a *
          paper_theorem8_gaussian_cdf xj a) :=
  theorem8GaussianPairDenominator_measure_eq xi xj a

/--
Appendix C / Theorem 8, product-measure mass of the strict paper-syntax
conditioning event.
-/
theorem paper_theorem8_gaussian_pair_strict_denominator_measure_eq
    (xi xj a : ℝ) :
    paper_theorem8_gaussian_pair_measure xi xj
        (paper_theorem8_gaussian_pair_strict_denominator_event a) =
      ENNReal.ofReal
        (paper_theorem8_gaussian_cdf xi a *
          paper_theorem8_gaussian_cdf xj a) :=
  theorem8GaussianPairStrictDenominator_measure_eq xi xj a

/--
Appendix C / Theorem 8, canonical product-probability conditional ratio for
the Gaussian pair.
-/
noncomputable abbrev paper_theorem8_gaussian_product_conditional_ratio_at
    (xi xj a : ℝ) : ℝ :=
  theorem8GaussianProductConditionalRatioAt xi xj a

/--
Appendix C / Theorem 8, canonical product-probability conditional ratio in the
paper's strict event syntax.
-/
noncomputable abbrev paper_theorem8_gaussian_product_strict_conditional_ratio_at
    (xi xj a : ℝ) : ℝ :=
  theorem8GaussianProductStrictConditionalRatioAt xi xj a

/--
Appendix C / Theorem 8, the product-probability ratio equals the paper's
density/CDF ratio.
-/
theorem paper_theorem8_gaussian_product_conditional_ratio_at_eq_pdf_cdf
    (xi xj a : ℝ) :
    paper_theorem8_gaussian_product_conditional_ratio_at xi xj a =
      paper_theorem8_gaussian_pdf_cdf_ratio_at xi xj a :=
  theorem8GaussianProductConditionalRatioAt_eq_pdf_cdf xi xj a

/--
Appendix C / Theorem 8, the strict product-probability ratio equals the paper's
density/CDF ratio.
-/
theorem paper_theorem8_gaussian_product_strict_conditional_ratio_at_eq_pdf_cdf
    (xi xj a : ℝ) :
    paper_theorem8_gaussian_product_strict_conditional_ratio_at xi xj a =
      paper_theorem8_gaussian_pdf_cdf_ratio_at xi xj a :=
  theorem8GaussianProductStrictConditionalRatioAt_eq_pdf_cdf xi xj a

/--
Appendix C / Theorem 8, canonical product-probability version of the Gaussian
conditional derivative theorem.
-/
theorem paper_theorem8_gaussian_product_conditional_ratio_at_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => paper_theorem8_gaussian_product_conditional_ratio_at xi xj u)
        d a ∧
        0 < d :=
  theorem8GaussianProductConditionalRatioAt_hasDerivAt_pos hx

/--
Appendix C / Theorem 8, strict paper-syntax product-probability version of the
Gaussian conditional derivative theorem.
-/
theorem paper_theorem8_gaussian_product_strict_conditional_ratio_at_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u =>
          paper_theorem8_gaussian_product_strict_conditional_ratio_at xi xj u)
        d a ∧
        0 < d :=
  theorem8GaussianProductStrictConditionalRatioAt_hasDerivAt_pos hx

/--
Appendix C / Theorem 8, variance parameter corresponding to Gaussian standard
deviation `σ`.
-/
abbrev paper_theorem8_gaussian_variance_from_std (σ : ℝ) : ℝ≥0 :=
  theorem8GaussianVarianceFromStd σ

/--
Appendix C / Theorem 8, positive scale used by the source proof's WLOG
normalization from arbitrary standard deviation `σ` to `1 / sqrt 2`.
-/
noncomputable abbrev paper_theorem8_gaussian_canonical_scale (σ : ℝ) : ℝ :=
  theorem8GaussianCanonicalScale σ

/--
Appendix C / Theorem 8, Mathlib Gaussian scaling theorem specialized to the
paper's WLOG normalization.
-/
theorem paper_theorem8_gaussianReal_map_canonical_scale
    {σ μ : ℝ} (hσ : 0 < σ) :
    (ProbabilityTheory.gaussianReal μ
        (paper_theorem8_gaussian_variance_from_std σ)).map
        (fun x => paper_theorem8_gaussian_canonical_scale σ * x) =
      ProbabilityTheory.gaussianReal
        (paper_theorem8_gaussian_canonical_scale σ * μ) (1 / 2 : ℝ≥0) :=
  theorem8GaussianReal_map_canonicalScale hσ

/--
Appendix C / Theorem 8, product measure for independent Gaussian scores with
arbitrary positive standard deviation `σ`.
-/
noncomputable abbrev paper_theorem8_gaussian_pair_measure_std
    (σ xi xj : ℝ) : Measure (ℝ × ℝ) :=
  theorem8GaussianPairMeasureStd σ xi xj

/--
Appendix C / Theorem 8, arbitrary-`σ` strict numerator mass equals the
canonical strict numerator mass after scaling values and cutoff.
-/
theorem paper_theorem8_gaussian_pair_measure_std_strict_numerator_eq_scaled
    {σ xi xj a : ℝ} (hσ : 0 < σ) :
    paper_theorem8_gaussian_pair_measure_std σ xi xj
        (paper_theorem8_gaussian_pair_strict_numerator_event a) =
      paper_theorem8_gaussian_pair_measure
        (paper_theorem8_gaussian_canonical_scale σ * xi)
        (paper_theorem8_gaussian_canonical_scale σ * xj)
        (paper_theorem8_gaussian_pair_strict_numerator_event
          (paper_theorem8_gaussian_canonical_scale σ * a)) :=
  theorem8GaussianPairMeasureStd_strict_numerator_eq_scaled hσ

/--
Appendix C / Theorem 8, arbitrary-`σ` strict denominator mass equals the
canonical strict denominator mass after scaling values and cutoff.
-/
theorem paper_theorem8_gaussian_pair_measure_std_strict_denominator_eq_scaled
    {σ xi xj a : ℝ} (hσ : 0 < σ) :
    paper_theorem8_gaussian_pair_measure_std σ xi xj
        (paper_theorem8_gaussian_pair_strict_denominator_event a) =
      paper_theorem8_gaussian_pair_measure
        (paper_theorem8_gaussian_canonical_scale σ * xi)
        (paper_theorem8_gaussian_canonical_scale σ * xj)
        (paper_theorem8_gaussian_pair_strict_denominator_event
          (paper_theorem8_gaussian_canonical_scale σ * a)) :=
  theorem8GaussianPairMeasureStd_strict_denominator_eq_scaled hσ

/--
Appendix C / Theorem 8, strict conditional probability ratio for independent
Gaussian scores with arbitrary positive standard deviation `σ`.
-/
noncomputable abbrev
    paper_theorem8_gaussian_product_strict_conditional_ratio_at_std
    (σ xi xj a : ℝ) : ℝ :=
  theorem8GaussianProductStrictConditionalRatioAtStd σ xi xj a

/--
Appendix C / Theorem 8, arbitrary-`σ` strict conditional probability ratio is
the canonical variance-`1/2` ratio after scaling values and cutoff.
-/
theorem paper_theorem8_gaussian_product_strict_conditional_ratio_at_std_eq_scaled
    {σ xi xj a : ℝ} (hσ : 0 < σ) :
    paper_theorem8_gaussian_product_strict_conditional_ratio_at_std σ xi xj a =
      paper_theorem8_gaussian_product_strict_conditional_ratio_at
        (paper_theorem8_gaussian_canonical_scale σ * xi)
        (paper_theorem8_gaussian_canonical_scale σ * xj)
        (paper_theorem8_gaussian_canonical_scale σ * a) :=
  theorem8GaussianProductStrictConditionalRatioAtStd_eq_scaled hσ

/--
Appendix C / Theorem 8, source-level strict Gaussian conditional derivative:
for independent Gaussian scores with standard deviation `σ > 0`, the strict
conditional probability ratio has positive derivative in the cutoff.
-/
theorem paper_theorem8_gaussian_product_strict_conditional_ratio_at_std_hasDerivAt_pos
    {σ xi xj a : ℝ} (hσ : 0 < σ) (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u =>
          paper_theorem8_gaussian_product_strict_conditional_ratio_at_std
            σ xi xj u)
        d a ∧
        0 < d :=
  theorem8GaussianProductStrictConditionalRatioAtStd_hasDerivAt_pos hσ hx

/--
Appendix C contraction map for one coordinate.

Paper notation: `r'ᵢ = xᵢ + (rᵢ - xᵢ) * θH / θA`.  Lean writes the contraction
factor as `t`, with later lemmas assuming `0 ≤ t ≤ 1`.
-/
noncomputable abbrev paper_appendixC_contractedScore (t x r : ℝ) : ℝ :=
  rumContractScore t x r

/-- Appendix C contraction cannot create inversions, two-candidate weak form. -/
theorem paper_appendixC_contraction_preserves_weak_order
    {t xi xj ri rj : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : xj ≤ xi) (hr : rj ≤ ri) :
    paper_appendixC_contractedScore t xj rj ≤
      paper_appendixC_contractedScore t xi ri :=
  rumContractScore_preserves_weak_order ht0 ht1 hx hr

/-- Appendix C contraction cannot create inversions, two-candidate strict form. -/
theorem paper_appendixC_contraction_preserves_strict_order
    {t xi xj ri rj : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : xj < xi) (hr : rj < ri) :
    paper_appendixC_contractedScore t xj rj <
      paper_appendixC_contractedScore t xi ri :=
  rumContractScore_preserves_strict_order ht0 ht1 hx hr

/-- Appendix C contraction top-first preservation for three candidates. -/
theorem paper_appendixC_contraction_top_first_of_original_top_first
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 ≤ x1) (hx13 : x3 ≤ x1)
    (hr12 : r2 ≤ r1) (hr13 : r3 ≤ r1) :
    paper_appendixC_contractedScore t x2 r2 ≤
        paper_appendixC_contractedScore t x1 r1 ∧
      paper_appendixC_contractedScore t x3 r3 ≤
        paper_appendixC_contractedScore t x1 r1 :=
  rum3_contract_top_first_of_original_top_first
    ht0 ht1 hx12 hx13 hr12 hr13

/--
Appendix C contraction bottom-first reflection for three candidates.

If the bottom candidate `x₃` is first after contraction, then it was already
first in the original realization.
-/
theorem paper_appendixC_contraction_bottom_first_imp_original_bottom_first
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx31 : x3 < x1) (hx32 : x3 < x2)
    (hc31 :
      paper_appendixC_contractedScore t x1 r1 ≤
        paper_appendixC_contractedScore t x3 r3)
    (hc32 :
      paper_appendixC_contractedScore t x2 r2 ≤
        paper_appendixC_contractedScore t x3 r3) :
    r1 ≤ r3 ∧ r2 ≤ r3 :=
  rum3_contract_bottom_first_imp_original_bottom_first
    ht0 ht1 hx31 hx32 hc31 hc32

/--
Appendix C / Lemma 3, deterministic `swapi` geometry for `i = 2`.

This is the score-level statement behind the paper's claim that
`swapi(r) ∈ S_{j→1}` whenever `r ∈ S_{j→i}` in the three-candidate middle case.
-/
theorem paper_lemma3_swapi_middle_transition_geometry
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hr13 : r1 ≤ r3) (hr23 : r2 ≤ r3)
    (hc12 :
      paper_appendixC_contractedScore t x1 r1 <
        paper_appendixC_contractedScore t x2 r2)
    (hc32 :
      paper_appendixC_contractedScore t x3 r3 ≤
        paper_appendixC_contractedScore t x2 r2) :
    r2 ≤ r3 ∧ r1 ≤ r3 ∧
      paper_appendixC_contractedScore t x2 r1 ≤
        paper_appendixC_contractedScore t x1 r2 ∧
      paper_appendixC_contractedScore t x3 r3 ≤
        paper_appendixC_contractedScore t x1 r2 :=
  rum3_swap_middle_transition_geometry
    ht0 ht1 hx12 hr13 hr23 hc12 hc32

/--
Appendix C / Lemma 3, pointwise density comparison under weak well-ordering.
-/
theorem paper_lemma3_swapi_density_le_of_weaklyWellOrdered
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 r1 r2 : ℝ} (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) ≤ f (r2 - x1) * f (r1 - x2) :=
  weaklyWellOrderedNoise_swap_middle_density_le hf hx12 hr12

/--
Appendix C / Lemma 3, strict pointwise density comparison under strict
well-ordering.
-/
theorem paper_lemma3_swapi_density_lt_of_strictlyWellOrdered
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 r1 r2 : ℝ} (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) < f (r2 - x1) * f (r1 - x2) :=
  strictlyWellOrderedNoise_swap_middle_density_lt hf hx12 hr12

/-- Appendix C / pointwise density comparison for the `x₁`/`x₂` lambda swap. -/
theorem paper_theorem6_lambda_swap12_density3_le_of_weaklyWellOrdered
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 ≤ f (r3 - x3))
    (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) ≤
      f (r2 - x1) * f (r1 - x2) * f (r3 - x3) :=
  weaklyWellOrderedNoise_swap12_density3_le hf hctx hx12 hr12

/-- Appendix C / strict pointwise density comparison for the `x₁`/`x₂` lambda swap. -/
theorem paper_theorem6_lambda_swap12_density3_lt_of_strictlyWellOrdered
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 < f (r3 - x3))
    (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) <
      f (r2 - x1) * f (r1 - x2) * f (r3 - x3) :=
  strictlyWellOrderedNoise_swap12_density3_lt hf hctx hx12 hr12

/-- Appendix C / pointwise density comparison for the `x₂`/`x₃` lambda swap. -/
theorem paper_theorem6_lambda_swap23_density3_le_of_weaklyWellOrdered
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 ≤ f (r1 - x1))
    (hx23 : x3 < x2) (hr23 : r2 < r3) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) ≤
      f (r1 - x1) * f (r3 - x2) * f (r2 - x3) :=
  weaklyWellOrderedNoise_swap23_density3_le hf hctx hx23 hr23

/-- Appendix C / strict pointwise density comparison for the `x₂`/`x₃` lambda swap. -/
theorem paper_theorem6_lambda_swap23_density3_lt_of_strictlyWellOrdered
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 < f (r1 - x1))
    (hx23 : x3 < x2) (hr23 : r2 < r3) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) <
      f (r1 - x1) * f (r3 - x2) * f (r2 - x3) :=
  strictlyWellOrderedNoise_swap23_density3_lt hf hctx hx23 hr23

/--
Appendix C / concrete continuous score space for three-candidate RUMs.

Paper notation: a realization vector `r ∈ ℝ³`, represented in Lean as
`((r₁, r₂), r₃)`.
-/
abbrev paper_theorem6_scoreSpace : Type := RUM3ScoreSpace

/-- Appendix C / first score coordinate `r₁`. -/
abbrev paper_theorem6_score1 : paper_theorem6_scoreSpace → ℝ := rum3Score1

/-- Appendix C / second score coordinate `r₂`. -/
abbrev paper_theorem6_score2 : paper_theorem6_scoreSpace → ℝ := rum3Score2

/-- Appendix C / third score coordinate `r₃`. -/
abbrev paper_theorem6_score3 : paper_theorem6_scoreSpace → ℝ := rum3Score3

/-- Appendix C / measurability of the concrete RUM score density. -/
theorem paper_theorem6_scoreDensity_measurable
    {f : ℝ → ℝ} (hf : Measurable f) (x1 x2 x3 : ℝ) :
    Measurable
      (rum3ScoreDensityENN f x1 x2 x3
        paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3) :=
  rum3ScoreDensityENN_measurable_scoreSpace hf x1 x2 x3

/--
Appendix C / normalization criterion for the continuous score-density law.

Paper statement: the RUM score density integrates to one.  Lean uses this
integral equality to produce the `IsProbabilityMeasure` instance required by
the continuous Theorem 6 endpoint.
-/
theorem paper_theorem6_scoreDensity_isProbabilityMeasure_of_lintegral_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hD :
      ∫⁻ ω, (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂base = 1) :
    IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)) :=
  rum3ScoreDensity_isProbabilityMeasure_of_lintegral_eq_one
    base f x1 x2 x3 r1 r2 r3 hD

/--
Appendix C / finite source-region integral from normalized score density.

This discharges the finite-integral side conditions used by the strict
continuous lambda swap lemmas whenever the full density has total mass one.
-/
theorem paper_theorem6_scoreDensity_setLIntegral_ne_top_of_lintegral_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hD :
      ∫⁻ ω, (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂base = 1)
    (s : Set Ω) :
    (∫⁻ ω in s, (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂base) ≠ ∞ :=
  rum3ScoreDensity_setLIntegral_ne_top_of_lintegral_eq_one
    base f x1 x2 x3 r1 r2 r3 hD s

/--
Appendix C / positive base mass remains positive under a strictly positive score
density.
-/
theorem paper_theorem6_scoreDensity_withDensity_measure_ne_zero_of_base_measure_ne_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) {f : ℝ → ℝ}
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hpos : ∀ z : ℝ, 0 < f z)
    {s : Set Ω} (hs : MeasurableSet s) (hbase : base s ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) s ≠ 0 :=
  rum3ScoreDensity_withDensity_measure_ne_zero_of_base_measure_ne_zero
    base x1 x2 x3 r1 r2 r3 hD hpos hs hbase

/-- Appendix C / `swapi` for `i = 2`, swapping score coordinates 1 and 2. -/
abbrev paper_theorem6_scoreSwap12 : paper_theorem6_scoreSpace ≃ᵐ paper_theorem6_scoreSpace :=
  rum3ScoreSwap12

/-- Appendix C / coordinate swap for candidates 2 and 3. -/
abbrev paper_theorem6_scoreSwap23 : paper_theorem6_scoreSpace ≃ᵐ paper_theorem6_scoreSpace :=
  rum3ScoreSwap23

/-- Appendix C / the `r₁`/`r₂` score swap preserves Lebesgue volume. -/
theorem paper_theorem6_scoreSwap12_measurePreserving_volume :
    MeasurePreserving paper_theorem6_scoreSwap12
      (volume : Measure paper_theorem6_scoreSpace) volume :=
  rum3ScoreSwap12_measurePreserving_volume

/-- Appendix C / the `r₂`/`r₃` score swap preserves Lebesgue volume. -/
theorem paper_theorem6_scoreSwap23_measurePreserving_volume :
    MeasurePreserving paper_theorem6_scoreSwap23
      (volume : Measure paper_theorem6_scoreSpace) volume :=
  rum3ScoreSwap23_measurePreserving_volume

/--
Appendix C / continuous mass comparison from the `x₁`/`x₂` density formula.

Paper statement: the coordinate-swap change of variables does not decrease the
RUM density mass of the source event.  Lean states this directly for a
`withDensity` score measure over a measurable realization space.
-/
theorem paper_theorem6_lambda_swap12_withDensity_measure_le_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} ≤
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} :=
  rum3_withDensity_swap12_measure_le_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap p q hp hq hmp hmap
    hf hswap1 hswap2 hswap3 hctx hx12 hscore

/--
Appendix C / strict continuous mass comparison from the `x₁`/`x₂` density
formula.  The positive-base-measure source set is the continuous analogue of the
finite strict witness atom.
-/
theorem paper_theorem6_lambda_swap12_withDensity_measure_lt_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω)
    (hfi :
      (∫⁻ ω in {ω | p ω},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos : base {ω | p ω} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} :=
  rum3_withDensity_swap12_measure_lt_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap p q hp hq hmp hD hmap
    hf hpos hswap1 hswap2 hswap3 hx12 hscore hfi hsource_pos

/--
Appendix C / continuous mass comparison from the `x₂`/`x₃` density formula.
-/
theorem paper_theorem6_lambda_swap23_withDensity_measure_le_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} ≤
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} :=
  rum3_withDensity_swap23_measure_le_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap p q hp hq hmp hmap
    hf hswap1 hswap2 hswap3 hctx hx23 hscore

/--
Appendix C / strict continuous mass comparison from the `x₂`/`x₃` density
formula.
-/
theorem paper_theorem6_lambda_swap23_withDensity_measure_lt_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω)
    (hfi :
      (∫⁻ ω in {ω | p ω},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos : base {ω | p ω} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} :=
  rum3_withDensity_swap23_measure_lt_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap p q hp hq hmp hD hmap
    hf hpos hswap1 hswap2 hswap3 hx23 hscore hfi hsource_pos

/--
Appendix C / continuous score-measure ranking law.

Paper statement: a RUM score distribution induces a distribution over rankings
by ranking the realized scores.  Lean exposes this as the `PMF` obtained by
pushing a probability measure through the ranking map and converting the finite
ranking measure to a `PMF`.
-/
noncomputable abbrev paper_theorem6_rankingPMFOfMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank) : PMF (Ranking 1) :=
  rumRankingPMFOfMeasure μ rank hrank

/--
Appendix C / normalized continuous score-density ranking law.

This is the paper's pushforward distribution over rankings when the base score
space is `ℝ³` and the product score density has total integral one.
-/
noncomputable abbrev paper_theorem6_normalizedScoreRankingPMF
    (f : ℝ → ℝ) (x1 x2 x3 : ℝ)
    (hnorm :
      ∫⁻ ω,
          (rum3ScoreDensityENN f x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
            ω ∂(volume : Measure paper_theorem6_scoreSpace) = 1)
    (rank : paper_theorem6_scoreSpace → Ranking 1) (hrank : Measurable rank) :
    PMF (Ranking 1) :=
  @paper_theorem6_rankingPMFOfMeasure paper_theorem6_scoreSpace _
    ((volume : Measure paper_theorem6_scoreSpace).withDensity
      (rum3ScoreDensityENN f x1 x2 x3
        paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3))
    (paper_theorem6_scoreDensity_isProbabilityMeasure_of_lintegral_eq_one
      (volume : Measure paper_theorem6_scoreSpace) f x1 x2 x3
      paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3
      hnorm)
    rank hrank

/-- Appendix C / induced ranking-law event probabilities are preimage masses. -/
theorem paper_theorem6_rankingPMF_eventProb
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (p : Ranking 1 → Prop) [DecidablePred p] :
    pmfProb (paper_theorem6_rankingPMFOfMeasure μ rank hrank) p =
      measureProb μ (fun ω => p (rank ω)) :=
  rumRankingPMFOfMeasure_eventProb μ rank hrank p

/-- Appendix C / continuous-measure form of `λ₁`. -/
theorem paper_theorem6_lambda1_rankingPMF_measure_form
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank) :
    rum3Lambda1 (paper_theorem6_rankingPMFOfMeasure μ rank hrank) =
      measureProb μ
        (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)) :=
  rum3Lambda1_rumRankingPMFOfMeasure μ rank hrank

/-- Appendix C / continuous-measure form of `λ₂`. -/
theorem paper_theorem6_lambda2_rankingPMF_measure_form
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank) :
    rum3Lambda2 (paper_theorem6_rankingPMFOfMeasure μ rank hrank) =
      measureProb μ
        (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
          (0 : Candidate 1)) :=
  rum3Lambda2_rumRankingPMFOfMeasure μ rank hrank

/-- Appendix C / continuous-measure form of `λ₃`. -/
theorem paper_theorem6_lambda3_rankingPMF_measure_form
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank) :
    rum3Lambda3 (paper_theorem6_rankingPMFOfMeasure μ rank hrank) =
      measureProb μ
        (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)) :=
  rum3Lambda3_rumRankingPMFOfMeasure μ rank hrank

/-- Appendix C / continuous-measure form of first-choice probabilities. -/
theorem paper_theorem6_firstChoiceProb_rankingPMF_measure_form
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (c : Candidate 1) :
    firstChoiceProb (paper_theorem6_rankingPMFOfMeasure μ rank hrank) c =
      measureProb μ (fun ω => c = firstChoice (rank ω)) :=
  firstChoiceProb_rumRankingPMFOfMeasure μ rank hrank c

/-- Appendix C / continuous-measure comparison proving the `x₂`/`x₃` lambda half-bound. -/
theorem paper_theorem6_lambda1_wrong_lt_correct_of_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hmeasure :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)}) :
    pmfProb (paper_theorem6_rankingPMFOfMeasure μ rank hrank)
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
      rum3Lambda1 (paper_theorem6_rankingPMFOfMeasure μ rank hrank) :=
  rum3Lambda1_wrong_lt_correct_of_measure μ rank hrank hmeasure

/-- Appendix C / continuous-measure comparison proving the `x₁`/`x₂` lambda half-bound. -/
theorem paper_theorem6_lambda3_wrong_lt_correct_of_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hmeasure :
      μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)}) :
    pmfProb (paper_theorem6_rankingPMFOfMeasure μ rank hrank)
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
      rum3Lambda3 (paper_theorem6_rankingPMFOfMeasure μ rank hrank) :=
  rum3Lambda3_wrong_lt_correct_of_measure μ rank hrank hmeasure

/-- Appendix C / continuous-measure comparison proving `λ₁ < λ₂`. -/
theorem paper_theorem6_lambda1_lt_lambda2_of_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hmeasure :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
          (0 : Candidate 1)}) :
    rum3Lambda1 (paper_theorem6_rankingPMFOfMeasure μ rank hrank) <
      rum3Lambda2 (paper_theorem6_rankingPMFOfMeasure μ rank hrank) :=
  rum3Lambda1_lt_lambda2_of_measure μ rank hrank hmeasure

/--
Appendix C / continuous-measure residual comparison proving `λ₁ < λ₂`.

Paper statement: the common part of `λ₁` and `λ₂` cancels, so it is enough to
compare the residual event `λ₁ ∧ ¬λ₂` with `λ₂ ∧ ¬λ₁`.
-/
theorem paper_theorem6_lambda1_lt_lambda2_of_cross_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hcross :
      μ ({ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)}ᶜ) <
        μ ({ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)}ᶜ)) :
    rum3Lambda1 (paper_theorem6_rankingPMFOfMeasure μ rank hrank) <
      rum3Lambda2 (paper_theorem6_rankingPMFOfMeasure μ rank hrank) :=
  rum3Lambda1_lt_lambda2_of_cross_measure μ rank hrank hcross

/--
Appendix C / continuous-measure lambda certificate from the three continuous
lambda comparisons and full support of the induced human ranking law.
-/
theorem paper_theorem6_lambdaCertificate_of_measure_facts_and_full_support
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hfull : ∀ π : Ranking 1,
      0 < (paper_theorem6_rankingPMFOfMeasure μ rank hrank π).toReal)
    (h13_gt_23 :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
          (0 : Candidate 1)})
    (h23_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)})
    (h12_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)}) :
    RUM3LambdaCertificate (paper_theorem6_rankingPMFOfMeasure μ rank hrank) :=
  rum3LambdaCertificate_of_measure_facts_and_full_support
    μ rank hrank hfull h13_gt_23 h23_wrong_lt_correct h12_wrong_lt_correct

/--
Appendix C / continuous-measure lambda certificate using the paper's residual
`λ₁ ∧ ¬λ₂` comparison for `λ₁ < λ₂`.
-/
theorem paper_theorem6_lambdaCertificate_of_cross_measure_facts_and_full_support
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hfull : ∀ π : Ranking 1,
      0 < (paper_theorem6_rankingPMFOfMeasure μ rank hrank π).toReal)
    (h13_cross :
      μ ({ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)}ᶜ) <
        μ ({ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)}ᶜ))
    (h23_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)})
    (h12_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)}) :
    RUM3LambdaCertificate (paper_theorem6_rankingPMFOfMeasure μ rank hrank) :=
  rum3LambdaCertificate_of_cross_measure_facts_and_full_support
    μ rank hrank hfull h13_cross h23_wrong_lt_correct h12_wrong_lt_correct

/--
Appendix C / continuous-measure lambda certificate using the paper's residual
`λ₁ ∧ ¬λ₂` comparison and the exact positive wrong-event mass needed for
`λ₁ < 1`.
-/
theorem paper_theorem6_lambdaCertificate_of_cross_measure_facts_and_wrong_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hwrong23_pos :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1)} ≠ 0)
    (h13_cross :
      μ ({ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)}ᶜ) <
        μ ({ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)}ᶜ))
    (h23_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)})
    (h12_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)}) :
    RUM3LambdaCertificate (paper_theorem6_rankingPMFOfMeasure μ rank hrank) :=
  rum3LambdaCertificate_of_cross_measure_facts_and_wrong_pos
    μ rank hrank hwrong23_pos h13_cross h23_wrong_lt_correct
    h12_wrong_lt_correct

/--
Appendix C / continuous RUM lambda certificate from the with-density score law.

This closes the lambda side of Theorem 6 directly in the continuous model: the
three two-candidate comparisons are derived from measure-preserving coordinate
swaps and strict well-ordered noise, not from a finite score-sample PMF.
-/
theorem paper_theorem6_lambdaCertificate_of_cross_withDensity_score_facts_and_full_support
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (r1 r2 r3 : Ω → ℝ)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hfull : ∀ π : Ranking 1,
      0 <
        (paper_theorem6_rankingPMFOfMeasure
          (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
          rank hrank π).toReal)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambdaSwap13gap : Ω ≃ᵐ Ω)
    (h13gapSourceMeas : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)})
    (h13gapTargetMeas : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)})
    (hmp13gap : MeasurePreserving lambdaSwap13gap base base)
    (hlambdaSource13gap_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hlambdaNotTarget13gap_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        r1 ω < r3 ω)
    (hlambdaTarget13gap_of_scores : ∀ ω,
      r3 ω ≤ r1 ω →
        bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hlambdaNotSource13gap_of_scores : ∀ ω,
      r2 ω < r3 ω →
        ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaSwap13gap1 : ∀ ω, r1 (lambdaSwap13gap ω) = r2 ω)
    (hlambdaSwap13gap2 : ∀ ω, r2 (lambdaSwap13gap ω) = r1 ω)
    (hlambdaSwap13gap3 : ∀ ω, r3 (lambdaSwap13gap ω) = r3 ω)
    (hfi13gap :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
                (1 : Candidate 1) ∧
              ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) =
                (0 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsourcePos13gap :
      base
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
                (1 : Candidate 1) ∧
              ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) =
                (0 : Candidate 1)} ≠ 0)
    (lambdaSwap23 : Ω ≃ᵐ Ω)
    (hwrong23Meas : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1)})
    (hcorrect23Meas : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (1 : Candidate 1)})
    (hmp23 : MeasurePreserving lambdaSwap23 base base)
    (hlambdaWrong23_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        r2 ω < r3 ω)
    (hlambdaCorrect23_of_scores : ∀ ω,
      r3 ω ≤ r2 ω →
        bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaSwap23_1 : ∀ ω, r1 (lambdaSwap23 ω) = r1 ω)
    (hlambdaSwap23_2 : ∀ ω, r2 (lambdaSwap23 ω) = r3 ω)
    (hlambdaSwap23_3 : ∀ ω, r3 (lambdaSwap23 ω) = r2 ω)
    (hfi23 :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsourcePos23 :
      base {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1)} ≠ 0)
    (lambdaSwap12 : Ω ≃ᵐ Ω)
    (hwrong12Meas : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
        (1 : Candidate 1)})
    (hcorrect12Meas : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
        (0 : Candidate 1)})
    (hmp12 : MeasurePreserving lambdaSwap12 base base)
    (hlambdaWrong12_scores : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        r1 ω < r2 ω)
    (hlambdaCorrect12_of_scores : ∀ ω,
      r2 ω ≤ r1 ω →
        bestRemainingAfter (rank ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hlambdaSwap12_1 : ∀ ω, r1 (lambdaSwap12 ω) = r2 ω)
    (hlambdaSwap12_2 : ∀ ω, r2 (lambdaSwap12 ω) = r1 ω)
    (hlambdaSwap12_3 : ∀ ω, r3 (lambdaSwap12 ω) = r3 ω)
    (hfi12 :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsourcePos12 :
      base {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
        (1 : Candidate 1)} ≠ 0) :
    RUM3LambdaCertificate
      (paper_theorem6_rankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        rank hrank) :=
  paper_theorem6_lambdaCertificate_of_cross_measure_facts_and_full_support
    (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    rank hrank hfull
    (rum3_lambda13cross_withDensity_measure_lt_of_score_facts
      base f x1 x2 x3 rank r1 r2 r3 lambdaSwap13gap
      h13gapSourceMeas h13gapTargetMeas hmp13gap hD hf hpos hx12
      hlambdaSource13gap_scores hlambdaNotTarget13gap_scores
      hlambdaTarget13gap_of_scores hlambdaNotSource13gap_of_scores
      hlambdaSwap13gap1 hlambdaSwap13gap2 hlambdaSwap13gap3
      hfi13gap hsourcePos13gap)
    (rum3_lambda23wrong_withDensity_measure_lt_of_score_facts
      base f x1 x2 x3 rank r1 r2 r3 lambdaSwap23
      hwrong23Meas hcorrect23Meas hmp23 hD hf hpos hx23
      hlambdaWrong23_scores hlambdaCorrect23_of_scores
      hlambdaSwap23_1 hlambdaSwap23_2 hlambdaSwap23_3
      hfi23 hsourcePos23)
    (rum3_lambda12wrong_withDensity_measure_lt_of_score_facts
      base f x1 x2 x3 rank r1 r2 r3 lambdaSwap12
      hwrong12Meas hcorrect12Meas hmp12 hD hf hpos hx12
      hlambdaWrong12_scores hlambdaCorrect12_of_scores
      hlambdaSwap12_1 hlambdaSwap12_2 hlambdaSwap12_3
      hfi12 hsourcePos12)

/--
Appendix C / continuous RUM lambda certificate from the with-density score law,
using a positive wrong-choice source event instead of full support of all six
rankings.
-/
theorem paper_theorem6_lambdaCertificate_of_cross_withDensity_score_facts_and_wrong_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (r1 r2 r3 : Ω → ℝ)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambdaSwap13gap : Ω ≃ᵐ Ω)
    (h13gapSourceMeas : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)})
    (h13gapTargetMeas : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)})
    (hmp13gap : MeasurePreserving lambdaSwap13gap base base)
    (hlambdaSource13gap_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hlambdaNotTarget13gap_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        r1 ω < r3 ω)
    (hlambdaTarget13gap_of_scores : ∀ ω,
      r3 ω ≤ r1 ω →
        bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hlambdaNotSource13gap_of_scores : ∀ ω,
      r2 ω < r3 ω →
        ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaSwap13gap1 : ∀ ω, r1 (lambdaSwap13gap ω) = r2 ω)
    (hlambdaSwap13gap2 : ∀ ω, r2 (lambdaSwap13gap ω) = r1 ω)
    (hlambdaSwap13gap3 : ∀ ω, r3 (lambdaSwap13gap ω) = r3 ω)
    (hfi13gap :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
                (1 : Candidate 1) ∧
              ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) =
                (0 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsourcePos13gap :
      base
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
                (1 : Candidate 1) ∧
              ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) =
                (0 : Candidate 1)} ≠ 0)
    (lambdaSwap23 : Ω ≃ᵐ Ω)
    (hwrong23Meas : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1)})
    (hcorrect23Meas : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (1 : Candidate 1)})
    (hmp23 : MeasurePreserving lambdaSwap23 base base)
    (hlambdaWrong23_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        r2 ω < r3 ω)
    (hlambdaCorrect23_of_scores : ∀ ω,
      r3 ω ≤ r2 ω →
        bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaSwap23_1 : ∀ ω, r1 (lambdaSwap23 ω) = r1 ω)
    (hlambdaSwap23_2 : ∀ ω, r2 (lambdaSwap23 ω) = r3 ω)
    (hlambdaSwap23_3 : ∀ ω, r3 (lambdaSwap23 ω) = r2 ω)
    (hfi23 :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsourcePos23 :
      base {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1)} ≠ 0)
    (lambdaSwap12 : Ω ≃ᵐ Ω)
    (hwrong12Meas : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
        (1 : Candidate 1)})
    (hcorrect12Meas : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
        (0 : Candidate 1)})
    (hmp12 : MeasurePreserving lambdaSwap12 base base)
    (hlambdaWrong12_scores : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        r1 ω < r2 ω)
    (hlambdaCorrect12_of_scores : ∀ ω,
      r2 ω ≤ r1 ω →
        bestRemainingAfter (rank ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hlambdaSwap12_1 : ∀ ω, r1 (lambdaSwap12 ω) = r2 ω)
    (hlambdaSwap12_2 : ∀ ω, r2 (lambdaSwap12 ω) = r1 ω)
    (hlambdaSwap12_3 : ∀ ω, r3 (lambdaSwap12 ω) = r3 ω)
    (hfi12 :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsourcePos12 :
      base {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
        (1 : Candidate 1)} ≠ 0) :
    RUM3LambdaCertificate
      (paper_theorem6_rankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        rank hrank) :=
  paper_theorem6_lambdaCertificate_of_cross_measure_facts_and_wrong_pos
    (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    rank hrank
    (rum3ScoreDensity_withDensity_measure_ne_zero_of_base_measure_ne_zero
      base x1 x2 x3 r1 r2 r3 hD hpos hwrong23Meas hsourcePos23)
    (rum3_lambda13cross_withDensity_measure_lt_of_score_facts
      base f x1 x2 x3 rank r1 r2 r3 lambdaSwap13gap
      h13gapSourceMeas h13gapTargetMeas hmp13gap hD hf hpos hx12
      hlambdaSource13gap_scores hlambdaNotTarget13gap_scores
      hlambdaTarget13gap_of_scores hlambdaNotSource13gap_of_scores
      hlambdaSwap13gap1 hlambdaSwap13gap2 hlambdaSwap13gap3
      hfi13gap hsourcePos13gap)
    (rum3_lambda23wrong_withDensity_measure_lt_of_score_facts
      base f x1 x2 x3 rank r1 r2 r3 lambdaSwap23
      hwrong23Meas hcorrect23Meas hmp23 hD hf hpos hx23
      hlambdaWrong23_scores hlambdaCorrect23_of_scores
      hlambdaSwap23_1 hlambdaSwap23_2 hlambdaSwap23_3
      hfi23 hsourcePos23)
    (rum3_lambda12wrong_withDensity_measure_lt_of_score_facts
      base f x1 x2 x3 rank r1 r2 r3 lambdaSwap12
      hwrong12Meas hcorrect12Meas hmp12 hD hf hpos hx12
      hlambdaWrong12_scores hlambdaCorrect12_of_scores
      hlambdaSwap12_1 hlambdaSwap12_2 hlambdaSwap12_3
      hfi12 hsourcePos12)

/--
Appendix C / continuous-measure delta certificate from the paper's top
monotonicity, Lemma 3 middle inequality, and Lemma 2 bottom inequality.
-/
theorem paper_theorem6_deltaCertificate_of_measure_probability_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    (monotonicity_top :
      μ {ω | (0 : Candidate 1) = firstChoice (worse ω)} <
        μ {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (lemma3_middle :
      measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
        measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (worse ω)))
    (lemma2_bottom :
      μ {ω | (2 : Candidate 1) = firstChoice (better ω)} ≤
        μ {ω | (2 : Candidate 1) = firstChoice (worse ω)}) :
    RUM3DeltaCertificate
      (paper_theorem6_rankingPMFOfMeasure μ better hbetter)
      (paper_theorem6_rankingPMFOfMeasure μ worse hworse) :=
  rum3DeltaCertificate_of_measure_probability_facts
    μ better worse hbetter hworse monotonicity_top lemma3_middle lemma2_bottom

/-- Appendix C / continuous top monotonicity from a contraction coupling. -/
theorem paper_theorem6_monotonicity_top_of_measure_coupling
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (worse ω)})
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hcorrected_pos :
      μ ({ω | (0 : Candidate 1) = firstChoice (better ω)} ∩
          {ω | (0 : Candidate 1) = firstChoice (worse ω)}ᶜ) ≠ 0) :
    μ {ω | (0 : Candidate 1) = firstChoice (worse ω)} <
      μ {ω | (0 : Candidate 1) = firstChoice (better ω)} :=
  rum3_monotonicity_top_of_measure_coupling
    μ better worse hbetterTopMeas hworseTopMeas hnoTopOut hcorrected_pos

/-- Appendix C / continuous Lemma 2 bottom inequality from a contraction coupling. -/
theorem paper_lemma2_bottom_of_measure_coupling
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (better worse : Ω → Ranking 1)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω)) :
    μ {ω | (2 : Candidate 1) = firstChoice (better ω)} ≤
      μ {ω | (2 : Candidate 1) = firstChoice (worse ω)} :=
  rum3_lemma2_bottom_of_measure_coupling μ better worse hbottomImp

/--
Appendix C / continuous Lemma 3 middle-candidate delta comparison from
transition mass.

Paper statement: under the contraction coupling, no realization with `x₁` first
under the human/noisier ranking leaves `x₁` first under the more accurate
ranking, and the `x₃ -> x₂` transition mass is at most the `x₃ -> x₁`
transition mass. Therefore `Δp₂ ≤ Δp₁`.
-/
theorem paper_lemma3_middle_of_measure_transition_mass
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hbottomMiddle_le_bottomTop :
      measureProb μ (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        measureProb μ (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω))) :
    measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
        measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
      measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
        measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (worse ω)) :=
  rum3_lemma3_middle_of_measure_transition_mass
    μ better worse hbetter hworse hnoTopOut hbottomMiddle_le_bottomTop

/--
Appendix C / continuous delta certificate from the contraction coupling.

This packages monotonicity of `x₁`, Lemma 3 for `x₂`, and Lemma 2 for `x₃`
from measure-level coupling facts.
-/
theorem paper_theorem6_deltaCertificate_of_measure_coupling_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (worse ω)})
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hcorrected_pos :
      μ ({ω | (0 : Candidate 1) = firstChoice (better ω)} ∩
          {ω | (0 : Candidate 1) = firstChoice (worse ω)}ᶜ) ≠ 0)
    (hbottomMiddle_le_bottomTop :
      measureProb μ (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        measureProb μ (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω)))
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω)) :
    RUM3DeltaCertificate
      (paper_theorem6_rankingPMFOfMeasure μ better hbetter)
      (paper_theorem6_rankingPMFOfMeasure μ worse hworse) :=
  paper_theorem6_deltaCertificate_of_measure_probability_facts
    μ better worse hbetter hworse
    (paper_theorem6_monotonicity_top_of_measure_coupling
      μ better worse hbetterTopMeas hworseTopMeas hnoTopOut hcorrected_pos)
    (paper_lemma3_middle_of_measure_transition_mass
      μ better worse hbetter hworse hnoTopOut hbottomMiddle_le_bottomTop)
    (paper_lemma2_bottom_of_measure_coupling μ better worse hbottomImp)

/--
Appendix C / continuous `swapi` transition-mass comparison for Lemma 3.

This is the density/integration step proving the `x₃ -> x₂` transition region
has no more probability mass than the `x₃ -> x₁` transition region under the
normalized RUM score law.
-/
theorem paper_lemma3_deltaTransition_measureProb_le_of_withDensity_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (deltaSwap : Ω ≃ᵐ Ω)
    (better worse : Ω → Ranking 1)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hsourceMeas : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω)})
    (htargetMeas : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω)})
    (hmp : MeasurePreserving deltaSwap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hdeltaSwap1 : ∀ ω, r1 (deltaSwap ω) = r2 ω)
    (hdeltaSwap2 : ∀ ω, r2 (deltaSwap ω) = r1 ω)
    (hdeltaSwap3 : ∀ ω, r3 (deltaSwap ω) = r3 ω)
    (hctx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (paper_appendixC_contractedScore t x1 (r1 ω))
          (paper_appendixC_contractedScore t x2 (r2 ω))
          (paper_appendixC_contractedScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (paper_appendixC_contractedScore t x1 (r1 ω))
          (paper_appendixC_contractedScore t x2 (r2 ω))
          (paper_appendixC_contractedScore t x3 (r3 ω))) :
    measureProb
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
      measureProb
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω)) :=
  rum3_deltaTransition_measureProb_le_of_withDensity_score_facts
    base f x1 x2 x3 t r1 r2 r3 deltaSwap better worse
    hsourceMeas htargetMeas hmp hf
    hdeltaSwap1 hdeltaSwap2 hdeltaSwap3 hctx ht0 ht1 hx12
    hbetterTop_of_scores hworseBottom_scores_of_first
    hworseBottom_of_scores hbetterMiddle_scores_of_first

/--
Appendix C / continuous delta certificate from normalized RUM score-density
and contraction/`swapi` score facts.
-/
theorem paper_theorem6_deltaCertificate_of_withDensity_score_contraction_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (deltaSwap : Ω ≃ᵐ Ω)
    (better worse : Ω → Ranking 1)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hbetter : Measurable better) (hworse : Measurable worse)
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (worse ω)})
    (hsourceMeas : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω)})
    (htargetMeas : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω)})
    (hmp : MeasurePreserving deltaSwap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hdeltaSwap1 : ∀ ω, r1 (deltaSwap ω) = r2 ω)
    (hdeltaSwap2 : ∀ ω, r2 (deltaSwap ω) = r1 ω)
    (hdeltaSwap3 : ∀ ω, r3 (deltaSwap ω) = r3 ω)
    (hctx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hcorrected_pos :
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | (0 : Candidate 1) = firstChoice (better ω)} ∩
          {ω | (0 : Candidate 1) = firstChoice (worse ω)}ᶜ) ≠ 0)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (paper_appendixC_contractedScore t x1 (r1 ω))
          (paper_appendixC_contractedScore t x2 (r2 ω))
          (paper_appendixC_contractedScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (paper_appendixC_contractedScore t x1 (r1 ω))
          (paper_appendixC_contractedScore t x2 (r2 ω))
          (paper_appendixC_contractedScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (paper_appendixC_contractedScore t x1 (r1 ω))
          (paper_appendixC_contractedScore t x2 (r2 ω))
          (paper_appendixC_contractedScore t x3 (r3 ω))) :
    RUM3DeltaCertificate
      (paper_theorem6_rankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        better hbetter)
      (paper_theorem6_rankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        worse hworse) :=
  rum3DeltaCertificate_of_withDensity_score_contraction_facts
    base f x1 x2 x3 t r1 r2 r3 deltaSwap better worse
    hbetter hworse hbetterTopMeas hworseTopMeas
    hsourceMeas htargetMeas hmp hf hdeltaSwap1 hdeltaSwap2 hdeltaSwap3
    hctx ht0 ht1 hx12 hx23 hcorrected_pos
    hbetterTop_of_scores hworseTop_scores_of_first
    hbetterBottom_scores_of_first hworseBottom_scores_of_first
    hworseBottom_of_scores hbetterMiddle_scores_of_first

/-- Appendix C / finite mass comparison from the `x₁`/`x₂` density formula. -/
theorem paper_theorem6_lambda_swap12_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    ∀ ω, p ω → (ν ω).toReal ≤ (ν (swap ω)).toReal :=
  rum3_swap12_mass_le_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap p hf hdens
    hswap1 hswap2 hswap3 hctx hx12 hscore

/-- Appendix C / strict finite mass comparison from the `x₁`/`x₂` density formula. -/
theorem paper_theorem6_lambda_swap12_mass_lt_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 < f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    ∀ ω, p ω → (ν ω).toReal < (ν (swap ω)).toReal :=
  rum3_swap12_mass_lt_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap p hf hdens
    hswap1 hswap2 hswap3 hctx hx12 hscore

/--
Appendix C / finite mass comparison for the delta-side `swapi` map from the
density formula.
-/
theorem paper_theorem6_deltaSwap_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (better worse : Ω → Ranking 1)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω))) :
    ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal :=
  rum3_deltaSwap_mass_le_of_density_formula
    ν f x1 x2 x3 t r1 r2 r3 swap better worse hf hdens
    hswap1 hswap2 hswap3 hctx ht0 ht1 hx12 hbetterMiddle_scores_of_first

/-- Appendix C / finite mass comparison from the `x₂`/`x₃` density formula. -/
theorem paper_theorem6_lambda_swap23_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    ∀ ω, p ω → (ν ω).toReal ≤ (ν (swap ω)).toReal :=
  rum3_swap23_mass_le_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap p hf hdens
    hswap1 hswap2 hswap3 hctx hx23 hscore

/-- Appendix C / strict finite mass comparison from the `x₂`/`x₃` density formula. -/
theorem paper_theorem6_lambda_swap23_mass_lt_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 < f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    ∀ ω, p ω → (ν ω).toReal < (ν (swap ω)).toReal :=
  rum3_swap23_mass_lt_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap p hf hdens
    hswap1 hswap2 hswap3 hctx hx23 hscore

/--
Appendix C / specialized finite mass comparison for the `x₂`/`x₃`
wrong-to-correct lambda swap.
-/
theorem paper_theorem6_lambda23_mass_le_of_density_and_score_facts
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        0 ≤ f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        r2 ω < r3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal :=
  paper_theorem6_lambda_swap23_mass_le_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1))
    hf hdens hswap1 hswap2 hswap3 hctx hx23 hscore

/--
Appendix C / specialized finite mass comparison for the `x₁`/`x₂`
wrong-to-correct lambda swap.
-/
theorem paper_theorem6_lambda12_mass_le_of_density_and_score_facts
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        r1 ω < r2 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal :=
  paper_theorem6_lambda_swap12_mass_le_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1))
    hf hdens hswap1 hswap2 hswap3 hctx hx12 hscore

/--
Appendix C / specialized finite mass comparison for the asymmetric
`λ₁ ∧ ¬λ₂` gap under the `x₁`/`x₂` density swap.
-/
theorem paper_theorem6_lambda13gap_mass_le_of_density_and_score_facts
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hnot_target_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        r1 ω < r3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal :=
  rum3_lambda13gap_mass_le_of_density_formula
    ν f x1 x2 x3 rank r1 r2 r3 swap hf hdens
    hswap1 hswap2 hswap3 hctx hx12 hsource_scores hnot_target_scores

/--
Appendix C / strict finite mass comparison for the asymmetric `λ₁ ∧ ¬λ₂` gap.
-/
theorem paper_theorem6_lambda13gap_mass_lt_of_density_and_score_facts
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        0 < f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hnot_target_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        r1 ω < r3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        (ν ω).toReal < (ν (swap ω)).toReal :=
  rum3_lambda13gap_mass_lt_of_density_formula
    ν f x1 x2 x3 rank r1 r2 r3 swap hf hdens
    hswap1 hswap2 hswap3 hctx hx12 hsource_scores hnot_target_scores

/--
Appendix C / Theorem 6, final three-candidate payoff algebra.

Paper statement: for three candidates with values `x1 > x2 > x3`, once the RUM
proof supplies `Δp1 > 0`, `Δp1 ≥ Δp2`, `Δp3 ≤ 0`, total first-choice mass
conservation, and the lambda inequalities for the human two-candidate
subproblems, the weaker-competition payoff difference satisfies
`UAH(θA, θH) - UHH(θA, θH) < 0`.

Lean exposes exactly that finite-dimensional final step.  The remaining
continuous RUM work is to derive these lambda and delta hypotheses from the
noise model.
-/
theorem paper_theorem6_threeCandidate_payoff_algebra
    {x1 x2 x3 ell1 ell2 ell3 d1 d2 d3 : ℝ}
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hell1_half : (1 : ℝ) / 2 < ell1) (hell1_lt_one : ell1 < 1)
    (hell12 : ell1 < ell2) (hell2_le_one : ell2 ≤ 1)
    (hell3_half : (1 : ℝ) / 2 < ell3)
    (hd1_pos : 0 < d1) (hd12 : d2 ≤ d1) (hd3_nonpos : d3 ≤ 0)
    (hd_sum : d1 + d2 + d3 = 0) :
    d1 * rum3_uMinus1 ell1 x2 x3 +
        d2 * rum3_uMinus2 ell2 x1 x3 +
        d3 * rum3_uMinus3 ell3 x1 x2 < 0 :=
  rum3_theorem6_payoff_algebra
    hx12 hx23 hell1_half hell1_lt_one hell12 hell2_le_one hell3_half
    hd1_pos hd12 hd3_nonpos hd_sum

/--
Appendix C / Theorem 6, model-level weaker-competition bridge.

This is the same three-candidate RUM algebra connected to the paper's
Definition 3 predicate.  Once the human best-after-removal values are identified
with the three `u_-i` formulas and the first-choice probability deltas satisfy
the Theorem 6 inequalities, Lean proves
`Model.PrefersWeakerCompetition μBetter μWorse value`.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_payoff_algebra
    (μBetter μWorse : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    {x1 x2 x3 ell1 ell2 ell3 : ℝ}
    (hbest1 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (0 : Candidate 1) =
        rum3_uMinus1 ell1 x2 x3)
    (hbest2 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (1 : Candidate 1) =
        rum3_uMinus2 ell2 x1 x3)
    (hbest3 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (2 : Candidate 1) =
        rum3_uMinus3 ell3 x1 x2)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hell1_half : (1 : ℝ) / 2 < ell1) (hell1_lt_one : ell1 < 1)
    (hell12 : ell1 < ell2) (hell2_le_one : ell2 ≤ 1)
    (hell3_half : (1 : ℝ) / 2 < ell3)
    (hd1_pos :
      0 <
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd12 :
      firstChoiceProb μBetter (1 : Candidate 1) -
          firstChoiceProb μWorse (1 : Candidate 1) ≤
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd3_nonpos :
      firstChoiceProb μBetter (2 : Candidate 1) -
          firstChoiceProb μWorse (2 : Candidate 1) ≤ 0) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  rum3_prefersWeakerCompetition_of_payoff_algebra
    μBetter μWorse value hbest1 hbest2 hbest3 hx12 hx23
    hell1_half hell1_lt_one hell12 hell2_le_one hell3_half
    hd1_pos hd12 hd3_nonpos

/--
Appendix C / Theorem 6, finite three-candidate endpoint.

This version derives the three `u_-i` identities from finite
best-after-removal expectations.  It leaves only the genuine RUM probability
facts from the paper: the value ordering, the lambda inequalities, and the
first-choice delta inequalities.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition
    (μBetter μWorse : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hlam1_half : (1 : ℝ) / 2 < rum3Lambda1 μWorse)
    (hlam1_lt_one : rum3Lambda1 μWorse < 1)
    (hlam12 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (hlam3_half : (1 : ℝ) / 2 < rum3Lambda3 μWorse)
    (hd1_pos :
      0 <
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd12 :
      firstChoiceProb μBetter (1 : Candidate 1) -
          firstChoiceProb μWorse (1 : Candidate 1) ≤
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd3_nonpos :
      firstChoiceProb μBetter (2 : Candidate 1) -
          firstChoiceProb μWorse (2 : Candidate 1) ≤ 0) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  rum3_prefersWeakerCompetition
    μBetter μWorse value
    hvalue1 hvalue2 hvalue3 hx12 hx23
    hlam1_half hlam1_lt_one hlam12 hlam3_half
    hd1_pos hd12 hd3_nonpos

/--
Appendix C / Theorem 6, named finite certificate form.

This is the current strongest human-facing finite endpoint for Theorem 6.  The
certificate fields correspond to the probability facts supplied in the paper by
monotonicity, Lemma 2, Lemma 3, and the two-candidate human-ranking lambda
comparisons.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_certificate
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (cert : RUM3Theorem6Certificate μBetter μWorse value x1 x2 x3) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  rum3_prefersWeakerCompetition_of_certificate cert

/--
Appendix C / Theorem 6, certificate construction from paper sublemmas.

This separates the remaining continuous RUM work into the two sources used in
the paper proof: lambda comparisons for two-candidate human subproblems and
first-choice delta comparisons from monotonicity/Lemmas 2 and 3.
-/
theorem paper_theorem6_certificate_of_lambda_delta
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda : RUM3LambdaCertificate μWorse)
    (delta : RUM3DeltaCertificate μBetter μWorse) :
    RUM3Theorem6Certificate μBetter μWorse value x1 x2 x3 :=
  rum3Theorem6Certificate_of_lambda_delta
    hvalue1 hvalue2 hvalue3 hx12 hx23 lambda delta

/--
Appendix C / Theorem 6, continuous ranking-law endpoint from named lambda and
delta certificates.

This is the paper payoff conclusion after the continuous realization measure has
been pushed forward to the algorithmic and human ranking laws.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_measure_certificates
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    {value : Candidate 1 → ℝ} {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda :
      RUM3LambdaCertificate
        (paper_theorem6_rankingPMFOfMeasure μ worse hworse))
    (delta :
      RUM3DeltaCertificate
        (paper_theorem6_rankingPMFOfMeasure μ better hbetter)
        (paper_theorem6_rankingPMFOfMeasure μ worse hworse)) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_rankingPMFOfMeasure μ better hbetter)
      (paper_theorem6_rankingPMFOfMeasure μ worse hworse) value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_certificate
    (paper_theorem6_certificate_of_lambda_delta
      hvalue1 hvalue2 hvalue3 hx12 hx23 lambda delta)

/--
Appendix C / Theorem 6, continuous endpoint from measure-level lambda and delta
facts.

The `h13_cross` hypothesis is the residual paper comparison
`λ₁ ∧ ¬λ₂ < λ₂ ∧ ¬λ₁`; `h23_wrong_lt_correct` and
`h12_wrong_lt_correct` are the two wrong-vs-correct two-candidate comparisons;
the last three hypotheses are the continuous forms of monotonicity, Lemma 3,
and Lemma 2.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_cross_measure_probability_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    {value : Candidate 1 → ℝ} {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hfull : ∀ π : Ranking 1,
      0 < (paper_theorem6_rankingPMFOfMeasure μ worse hworse π).toReal)
    (h13_cross :
      μ ({ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1)} ∩
          {ω | bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1)}ᶜ) <
        μ ({ω | bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1)} ∩
          {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1)}ᶜ))
    (h23_wrong_lt_correct :
      μ {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
          (1 : Candidate 1)})
    (h12_wrong_lt_correct :
      μ {ω | bestRemainingAfter (worse ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (worse ω) (2 : Candidate 1) =
          (0 : Candidate 1)})
    (monotonicity_top :
      μ {ω | (0 : Candidate 1) = firstChoice (worse ω)} <
        μ {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (lemma3_middle :
      measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
        measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (worse ω)))
    (lemma2_bottom :
      μ {ω | (2 : Candidate 1) = firstChoice (better ω)} ≤
        μ {ω | (2 : Candidate 1) = firstChoice (worse ω)}) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_rankingPMFOfMeasure μ better hbetter)
      (paper_theorem6_rankingPMFOfMeasure μ worse hworse) value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_measure_certificates
    μ better worse hbetter hworse hvalue1 hvalue2 hvalue3 hx12 hx23
    (paper_theorem6_lambdaCertificate_of_cross_measure_facts_and_full_support
      μ worse hworse hfull h13_cross h23_wrong_lt_correct h12_wrong_lt_correct)
    (paper_theorem6_deltaCertificate_of_measure_probability_facts
      μ better worse hbetter hworse monotonicity_top lemma3_middle lemma2_bottom)

/--
Appendix C / Theorem 6, continuous endpoint from a closed lambda certificate
and the three measure-level delta facts.

Use this with
`paper_theorem6_lambdaCertificate_of_cross_withDensity_score_facts_and_full_support`
to supply the lambda certificate directly from the continuous RUM density.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_lambdaCertificate_and_measure_delta_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    {value : Candidate 1 → ℝ} {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda :
      RUM3LambdaCertificate
        (paper_theorem6_rankingPMFOfMeasure μ worse hworse))
    (monotonicity_top :
      μ {ω | (0 : Candidate 1) = firstChoice (worse ω)} <
        μ {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (lemma3_middle :
      measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
        measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (worse ω)))
    (lemma2_bottom :
      μ {ω | (2 : Candidate 1) = firstChoice (better ω)} ≤
        μ {ω | (2 : Candidate 1) = firstChoice (worse ω)}) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_rankingPMFOfMeasure μ better hbetter)
      (paper_theorem6_rankingPMFOfMeasure μ worse hworse) value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_measure_certificates
    μ better worse hbetter hworse hvalue1 hvalue2 hvalue3 hx12 hx23
    lambda
    (paper_theorem6_deltaCertificate_of_measure_probability_facts
      μ better worse hbetter hworse monotonicity_top lemma3_middle lemma2_bottom)

/--
Appendix C / Theorem 6, continuous endpoint from a closed lambda certificate
and contraction-coupling delta facts.

Compared with
`paper_theorem6_threeCandidate_prefersWeakerCompetition_of_lambdaCertificate_and_measure_delta_facts`,
this wrapper derives the paper's three delta inequalities from the coupling
facts: no top candidate exits the top spot under contraction, positive corrected
top mass, the `x₃ -> x₂` transition mass bound, and bottom-candidate
monotonicity.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_lambdaCertificate_and_measure_coupling_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    {value : Candidate 1 → ℝ} {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda :
      RUM3LambdaCertificate
        (paper_theorem6_rankingPMFOfMeasure μ worse hworse))
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (worse ω)})
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hcorrected_pos :
      μ ({ω | (0 : Candidate 1) = firstChoice (better ω)} ∩
          {ω | (0 : Candidate 1) = firstChoice (worse ω)}ᶜ) ≠ 0)
    (hbottomMiddle_le_bottomTop :
      measureProb μ (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        measureProb μ (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω)))
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω)) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_rankingPMFOfMeasure μ better hbetter)
      (paper_theorem6_rankingPMFOfMeasure μ worse hworse) value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_measure_certificates
    μ better worse hbetter hworse hvalue1 hvalue2 hvalue3 hx12 hx23
    lambda
    (paper_theorem6_deltaCertificate_of_measure_coupling_facts
      μ better worse hbetter hworse hbetterTopMeas hworseTopMeas hnoTopOut
      hcorrected_pos hbottomMiddle_le_bottomTop hbottomImp)

/--
Appendix C / Theorem 6, continuous endpoint from a closed lambda certificate
and density-derived contraction/`swapi` delta facts.

This removes the measure-level delta assumptions: top monotonicity, Lemma 2,
and Lemma 3 are all derived from the normalized with-density score law plus the
paper's contraction and `swapi` score interfaces.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_lambdaCertificate_and_withDensity_delta_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (deltaSwap : Ω ≃ᵐ Ω)
    (better worse : Ω → Ranking 1)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hbetter : Measurable better) (hworse : Measurable worse)
    {value : Candidate 1 → ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda :
      RUM3LambdaCertificate
        (paper_theorem6_rankingPMFOfMeasure
          (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
          worse hworse))
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (worse ω)})
    (hsourceMeas : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω)})
    (htargetMeas : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω)})
    (hmp : MeasurePreserving deltaSwap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hdeltaSwap1 : ∀ ω, r1 (deltaSwap ω) = r2 ω)
    (hdeltaSwap2 : ∀ ω, r2 (deltaSwap ω) = r1 ω)
    (hdeltaSwap3 : ∀ ω, r3 (deltaSwap ω) = r3 ω)
    (hctx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hcorrected_pos :
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | (0 : Candidate 1) = firstChoice (better ω)} ∩
          {ω | (0 : Candidate 1) = firstChoice (worse ω)}ᶜ) ≠ 0)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (paper_appendixC_contractedScore t x1 (r1 ω))
          (paper_appendixC_contractedScore t x2 (r2 ω))
          (paper_appendixC_contractedScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (paper_appendixC_contractedScore t x1 (r1 ω))
          (paper_appendixC_contractedScore t x2 (r2 ω))
          (paper_appendixC_contractedScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (paper_appendixC_contractedScore t x1 (r1 ω))
          (paper_appendixC_contractedScore t x2 (r2 ω))
          (paper_appendixC_contractedScore t x3 (r3 ω))) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_rankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        better hbetter)
      (paper_theorem6_rankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        worse hworse) value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_measure_certificates
    (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    better worse hbetter hworse hvalue1 hvalue2 hvalue3 hx12 hx23
    lambda
    (paper_theorem6_deltaCertificate_of_withDensity_score_contraction_facts
      base f x1 x2 x3 t r1 r2 r3 deltaSwap better worse
      hbetter hworse hbetterTopMeas hworseTopMeas hsourceMeas htargetMeas
      hmp hf hdeltaSwap1 hdeltaSwap2 hdeltaSwap3 hctx ht0 ht1 hx12 hx23
      hcorrected_pos hbetterTop_of_scores hworseTop_scores_of_first
      hbetterBottom_scores_of_first hworseBottom_scores_of_first
      hworseBottom_of_scores hbetterMiddle_scores_of_first)

/--
Appendix C / Theorem 6, continuous RUM score-density endpoint.

This combines the continuous lambda proof and the continuous delta proof.  The
remaining assumptions are the explicit analytic/model interfaces for the
normalized score law: full support of the induced human ranking law,
measurability/finite-integral/positive-source facts for the three lambda swap
regions, and the contraction/`swapi` score interfaces for the delta side.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_withDensity_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ)
    (better worse : Ω → Ranking 1)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hbetter : Measurable better) (hworse : Measurable worse)
    {value : Candidate 1 → ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hfull : ∀ π : Ranking 1,
      0 <
        (paper_theorem6_rankingPMFOfMeasure
          (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
          worse hworse π).toReal)
    (lambdaSwap13gap : Ω ≃ᵐ Ω)
    (h13gapSourceMeas : MeasurableSet
      {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1)})
    (h13gapTargetMeas : MeasurableSet
      {ω | bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1)})
    (hmp13gap : MeasurePreserving lambdaSwap13gap base base)
    (hlambdaSource13gap_scores : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hlambdaNotTarget13gap_scores : ∀ ω,
      ¬ bestRemainingAfter (worse ω) (1 : Candidate 1) = (0 : Candidate 1) →
        r1 ω < r3 ω)
    (hlambdaTarget13gap_of_scores : ∀ ω,
      r3 ω ≤ r1 ω →
        bestRemainingAfter (worse ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hlambdaNotSource13gap_of_scores : ∀ ω,
      r2 ω < r3 ω →
        ¬ bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaSwap13gap1 : ∀ ω, r1 (lambdaSwap13gap ω) = r2 ω)
    (hlambdaSwap13gap2 : ∀ ω, r2 (lambdaSwap13gap ω) = r1 ω)
    (hlambdaSwap13gap3 : ∀ ω, r3 (lambdaSwap13gap ω) = r3 ω)
    (hfi13gap :
      (∫⁻ ω in
          {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
                (1 : Candidate 1) ∧
              ¬ bestRemainingAfter (worse ω) (1 : Candidate 1) =
                (0 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsourcePos13gap :
      base
          {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
                (1 : Candidate 1) ∧
              ¬ bestRemainingAfter (worse ω) (1 : Candidate 1) =
                (0 : Candidate 1)} ≠ 0)
    (lambdaSwap23 : Ω ≃ᵐ Ω)
    (hwrong23Meas : MeasurableSet
      {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
        (2 : Candidate 1)})
    (hcorrect23Meas : MeasurableSet
      {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
        (1 : Candidate 1)})
    (hmp23 : MeasurePreserving lambdaSwap23 base base)
    (hlambdaWrong23_scores : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        r2 ω < r3 ω)
    (hlambdaCorrect23_of_scores : ∀ ω,
      r3 ω ≤ r2 ω →
        bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaSwap23_1 : ∀ ω, r1 (lambdaSwap23 ω) = r1 ω)
    (hlambdaSwap23_2 : ∀ ω, r2 (lambdaSwap23 ω) = r3 ω)
    (hlambdaSwap23_3 : ∀ ω, r3 (lambdaSwap23 ω) = r2 ω)
    (hfi23 :
      (∫⁻ ω in
          {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (2 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsourcePos23 :
      base {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
        (2 : Candidate 1)} ≠ 0)
    (lambdaSwap12 : Ω ≃ᵐ Ω)
    (hwrong12Meas : MeasurableSet
      {ω | bestRemainingAfter (worse ω) (2 : Candidate 1) =
        (1 : Candidate 1)})
    (hcorrect12Meas : MeasurableSet
      {ω | bestRemainingAfter (worse ω) (2 : Candidate 1) =
        (0 : Candidate 1)})
    (hmp12 : MeasurePreserving lambdaSwap12 base base)
    (hlambdaWrong12_scores : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        r1 ω < r2 ω)
    (hlambdaCorrect12_of_scores : ∀ ω,
      r2 ω ≤ r1 ω →
        bestRemainingAfter (worse ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hlambdaSwap12_1 : ∀ ω, r1 (lambdaSwap12 ω) = r2 ω)
    (hlambdaSwap12_2 : ∀ ω, r2 (lambdaSwap12 ω) = r1 ω)
    (hlambdaSwap12_3 : ∀ ω, r3 (lambdaSwap12 ω) = r3 ω)
    (hfi12 :
      (∫⁻ ω in
          {ω | bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (1 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsourcePos12 :
      base {ω | bestRemainingAfter (worse ω) (2 : Candidate 1) =
        (1 : Candidate 1)} ≠ 0)
    (deltaSwap : Ω ≃ᵐ Ω)
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (worse ω)})
    (hdeltaSourceMeas : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω)})
    (hdeltaTargetMeas : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω)})
    (hmpDelta : MeasurePreserving deltaSwap base base)
    (hdeltaSwap1 : ∀ ω, r1 (deltaSwap ω) = r2 ω)
    (hdeltaSwap2 : ∀ ω, r2 (deltaSwap ω) = r1 ω)
    (hdeltaSwap3 : ∀ ω, r3 (deltaSwap ω) = r3 ω)
    (hdeltaCtx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hcorrected_pos :
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | (0 : Candidate 1) = firstChoice (better ω)} ∩
          {ω | (0 : Candidate 1) = firstChoice (worse ω)}ᶜ) ≠ 0)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (paper_appendixC_contractedScore t x1 (r1 ω))
          (paper_appendixC_contractedScore t x2 (r2 ω))
          (paper_appendixC_contractedScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (paper_appendixC_contractedScore t x1 (r1 ω))
          (paper_appendixC_contractedScore t x2 (r2 ω))
          (paper_appendixC_contractedScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (paper_appendixC_contractedScore t x1 (r1 ω))
          (paper_appendixC_contractedScore t x2 (r2 ω))
          (paper_appendixC_contractedScore t x3 (r3 ω))) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_rankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        better hbetter)
      (paper_theorem6_rankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        worse hworse) value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_lambdaCertificate_and_withDensity_delta_score_facts
    base f x1 x2 x3 t r1 r2 r3 deltaSwap better worse
    hbetter hworse hvalue1 hvalue2 hvalue3 hx12 hx23
    (paper_theorem6_lambdaCertificate_of_cross_withDensity_score_facts_and_full_support
      base f x1 x2 x3 worse hworse r1 r2 r3 hfull hD hf hpos hx12 hx23
      lambdaSwap13gap h13gapSourceMeas h13gapTargetMeas hmp13gap
      hlambdaSource13gap_scores hlambdaNotTarget13gap_scores
      hlambdaTarget13gap_of_scores hlambdaNotSource13gap_of_scores
      hlambdaSwap13gap1 hlambdaSwap13gap2 hlambdaSwap13gap3
      hfi13gap hsourcePos13gap
      lambdaSwap23 hwrong23Meas hcorrect23Meas hmp23
      hlambdaWrong23_scores hlambdaCorrect23_of_scores
      hlambdaSwap23_1 hlambdaSwap23_2 hlambdaSwap23_3 hfi23 hsourcePos23
      lambdaSwap12 hwrong12Meas hcorrect12Meas hmp12
      hlambdaWrong12_scores hlambdaCorrect12_of_scores
      hlambdaSwap12_1 hlambdaSwap12_2 hlambdaSwap12_3 hfi12 hsourcePos12)
    hbetterTopMeas hworseTopMeas hdeltaSourceMeas hdeltaTargetMeas hmpDelta
    hf.weak hdeltaSwap1 hdeltaSwap2 hdeltaSwap3 hdeltaCtx ht0 ht1
    hcorrected_pos hbetterTop_of_scores hworseTop_scores_of_first
    hbetterBottom_scores_of_first hworseBottom_scores_of_first
    hworseBottom_of_scores hbetterMiddle_scores_of_first

/--
Appendix C / Theorem 6, continuous RUM score-density endpoint with concrete
score-induced rankings.

Paper statement matched: the human ranking is obtained by ranking the raw RUM
scores, while the algorithmic ranking is obtained by ranking the contracted
scores.  Compared with
`paper_theorem6_threeCandidate_prefersWeakerCompetition_of_withDensity_score_facts`,
this wrapper discharges all score/ranking interface assumptions and all event
measurability assumptions, and the previous full-support assumption from the
concrete rank-by-score definitions.  The remaining hypotheses are analytic
positive-mass facts for the normalized continuous score law.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_withDensity_rankByScores_facts_of_t_lt_one
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ)
    (scoreSwap12 scoreSwap23 : Ω ≃ᵐ Ω)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hr1 : Measurable r1) (hr2 : Measurable r2) (hr3 : Measurable r3)
    {value : Candidate 1 → ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hmp12 : MeasurePreserving scoreSwap12 base base)
    (hswap12_1 : ∀ ω, r1 (scoreSwap12 ω) = r2 ω)
    (hswap12_2 : ∀ ω, r2 (scoreSwap12 ω) = r1 ω)
    (hswap12_3 : ∀ ω, r3 (scoreSwap12 ω) = r3 ω)
    (hmp23 : MeasurePreserving scoreSwap23 base base)
    (hswap23_1 : ∀ ω, r1 (scoreSwap23 ω) = r1 ω)
    (hswap23_2 : ∀ ω, r2 (scoreSwap23 ω) = r3 ω)
    (hswap23_3 : ∀ ω, r3 (scoreSwap23 ω) = r2 ω)
    (hfi13gap :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω)
                (0 : Candidate 1) = (1 : Candidate 1) ∧
              ¬ bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω)
                (1 : Candidate 1) = (0 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsourcePos13gap :
      base
          {ω | bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω)
                (0 : Candidate 1) = (1 : Candidate 1) ∧
              ¬ bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω)
                (1 : Candidate 1) = (0 : Candidate 1)} ≠ 0)
    (hfi23 :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω)
            (0 : Candidate 1) = (2 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsourcePos23 :
      base {ω | bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω)
        (0 : Candidate 1) = (2 : Candidate 1)} ≠ 0)
    (hfi12 :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω)
            (2 : Candidate 1) = (1 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsourcePos12 :
      base {ω | bestRemainingAfter (rum3RankByScoreFns r1 r2 r3 ω)
        (2 : Candidate 1) = (1 : Candidate 1)} ≠ 0)
    (hcorrected_pos :
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | (0 : Candidate 1) =
            firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)} ∩
          {ω | (0 : Candidate 1) =
            firstChoice (rum3RankByScoreFns r1 r2 r3 ω)}ᶜ) ≠ 0) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_rankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3)
        (rum3ContractRankByScoreFns_measurable hr1 hr2 hr3 t x1 x2 x3))
      (paper_theorem6_rankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (rum3RankByScoreFns r1 r2 r3)
        (rum3RankByScoreFns_measurable hr1 hr2 hr3)) value := by
  let better : Ω → Ranking 1 :=
    rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3
  let worse : Ω → Ranking 1 := rum3RankByScoreFns r1 r2 r3
  have hbetter : Measurable better :=
    rum3ContractRankByScoreFns_measurable hr1 hr2 hr3 t x1 x2 x3
  have hworse : Measurable worse :=
    rum3RankByScoreFns_measurable hr1 hr2 hr3
  have hbetterEvent (p : Ranking 1 → Prop) :
      MeasurableSet {ω | p (better ω)} := by
    simpa only [Set.preimage_setOf_eq] using
      hbetter (show MeasurableSet {π : Ranking 1 | p π}
        from MeasurableSet.of_discrete)
  have hworseEvent (p : Ranking 1 → Prop) :
      MeasurableSet {ω | p (worse ω)} := by
    simpa only [Set.preimage_setOf_eq] using
      hworse (show MeasurableSet {π : Ranking 1 | p π}
        from MeasurableSet.of_discrete)
  have h13gapSourceMeas : MeasurableSet
      {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1)} :=
    hworseEvent (fun π =>
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) ∧
        ¬ bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))
  have h13gapTargetMeas : MeasurableSet
      {ω | bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1)} :=
    hworseEvent (fun π =>
      bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1) ∧
        ¬ bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
  have hwrong23Meas : MeasurableSet
      {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
        (2 : Candidate 1)} :=
    hworseEvent (fun π =>
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1))
  have hcorrect23Meas : MeasurableSet
      {ω | bestRemainingAfter (worse ω) (0 : Candidate 1) =
        (1 : Candidate 1)} :=
    hworseEvent (fun π =>
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
  have hwrong12Meas : MeasurableSet
      {ω | bestRemainingAfter (worse ω) (2 : Candidate 1) =
        (1 : Candidate 1)} :=
    hworseEvent (fun π =>
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1))
  have hcorrect12Meas : MeasurableSet
      {ω | bestRemainingAfter (worse ω) (2 : Candidate 1) =
        (0 : Candidate 1)} :=
    hworseEvent (fun π =>
      bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))
  have hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (better ω)} :=
    hbetterEvent (fun π => (0 : Candidate 1) = firstChoice π)
  have hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (worse ω)} :=
    hworseEvent (fun π => (0 : Candidate 1) = firstChoice π)
  have hworseBottomMeas : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω)} :=
    hworseEvent (fun π => (2 : Candidate 1) = firstChoice π)
  have hbetterMiddleMeas : MeasurableSet
      {ω | (1 : Candidate 1) = firstChoice (better ω)} :=
    hbetterEvent (fun π => (1 : Candidate 1) = firstChoice π)
  have hdeltaSourceMeas : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω)} :=
    hworseBottomMeas.inter hbetterMiddleMeas
  have hdeltaTargetMeas : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω)} :=
    hworseBottomMeas.inter hbetterTopMeas
  have lambda :
      RUM3LambdaCertificate
        (paper_theorem6_rankingPMFOfMeasure
          (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
          worse hworse) :=
    paper_theorem6_lambdaCertificate_of_cross_withDensity_score_facts_and_wrong_pos
      base f x1 x2 x3 worse hworse r1 r2 r3
      hD hf hpos hx12 hx23
      scoreSwap12 h13gapSourceMeas h13gapTargetMeas hmp12
      (fun ω h => by
        simpa [worse, rum3RankByScoreFns] using
          (rum3RankByScores_remove0_eq1_imp_score23 h))
      (fun ω h => by
        simpa [worse, rum3RankByScoreFns] using
          (rum3RankByScores_remove1_ne0_imp_score13 h))
      (fun ω h => by
        simpa [worse, rum3RankByScoreFns] using
          (rum3RankByScores_remove1_eq0_of_score31
            (s2 := r2 ω) h))
      (fun ω h => by
        simpa [worse, rum3RankByScoreFns] using
          (rum3RankByScores_remove0_ne1_of_score23_lt
            (s1 := r1 ω) h))
      hswap12_1 hswap12_2 hswap12_3
      (by simpa [worse] using hfi13gap)
      (by simpa [worse] using hsourcePos13gap)
      scoreSwap23 hwrong23Meas hcorrect23Meas hmp23
      (fun ω h => by
        simpa [worse, rum3RankByScoreFns] using
          (rum3RankByScores_remove0_eq2_imp_score23_lt h))
      (fun ω h => by
        simpa [worse, rum3RankByScoreFns] using
          (rum3RankByScores_remove0_eq1_of_score32
            (s1 := r1 ω) h))
      hswap23_1 hswap23_2 hswap23_3
      (by simpa [worse] using hfi23)
      (by simpa [worse] using hsourcePos23)
      scoreSwap12 hwrong12Meas hcorrect12Meas hmp12
      (fun ω h => by
        simpa [worse, rum3RankByScoreFns] using
          (rum3RankByScores_remove2_eq1_imp_score12_lt h))
      (fun ω h => by
        simpa [worse, rum3RankByScoreFns] using
          (rum3RankByScores_remove2_eq0_of_score21
            (s3 := r3 ω) h))
      hswap12_1 hswap12_2 hswap12_3
      (by simpa [worse] using hfi12)
      (by simpa [worse] using hsourcePos12)
  have delta :
      RUM3DeltaCertificate
        (paper_theorem6_rankingPMFOfMeasure
          (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
          better hbetter)
        (paper_theorem6_rankingPMFOfMeasure
          (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
          worse hworse) :=
    rum3DeltaCertificate_of_withDensity_rankByScores_contraction_facts_of_t_lt_one
      base f x1 x2 x3 t r1 r2 r3 scoreSwap12
      hbetter hworse hbetterTopMeas hworseTopMeas
      hdeltaSourceMeas hdeltaTargetMeas
      hmp12 hf.weak hpos hswap12_1 hswap12_2 hswap12_3
      ht0 ht1 htlt1 hx12 hx23
      (by simpa [better, worse] using hcorrected_pos)
  change Model.PrefersWeakerCompetition
      (paper_theorem6_rankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        better hbetter)
      (paper_theorem6_rankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        worse hworse) value
  exact
    paper_theorem6_threeCandidate_prefersWeakerCompetition_of_measure_certificates
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
      better worse hbetter hworse hvalue1 hvalue2 hvalue3 hx12 hx23
      lambda delta

/--
Appendix C / Theorem 6, concrete continuous RUM score-space endpoint.

Paper statement: for three candidates with values `x₁ > x₂ > x₃`, when the
algorithm observes a contracted version of the same RUM scores and `0 ≤ t < 1`,
the second firm prefers weaker competition.  Lean instantiates the realization
space as `ℝ³` with the paper's product score density and proves the swap,
positive-source, finite-integral, and corrected-top side conditions from
concrete open regions.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_scoreSpace_density_t_lt_one
    (f : ℝ → ℝ) (x1 x2 x3 t : ℝ)
    {value : Candidate 1 → ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hfmeas : Measurable f)
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hnorm :
      ∫⁻ ω,
          (rum3ScoreDensityENN f x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
            ω ∂(volume : Measure paper_theorem6_scoreSpace) = 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_normalizedScoreRankingPMF f x1 x2 x3 hnorm
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF f x1 x2 x3 hnorm
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
      value := by
  let D : paper_theorem6_scoreSpace → ENNReal :=
    rum3ScoreDensityENN f x1 x2 x3
      paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3
  have hD : Measurable D :=
    paper_theorem6_scoreDensity_measurable hfmeas x1 x2 x3
  haveI : IsProbabilityMeasure
      ((volume : Measure paper_theorem6_scoreSpace).withDensity D) :=
    paper_theorem6_scoreDensity_isProbabilityMeasure_of_lintegral_eq_one
      (volume : Measure paper_theorem6_scoreSpace) f x1 x2 x3
      paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3
      hnorm
  have hfiniteIntegral (s : Set paper_theorem6_scoreSpace) :
      (∫⁻ ω in s, D ω ∂(volume : Measure paper_theorem6_scoreSpace)) ≠ ∞ :=
    paper_theorem6_scoreDensity_setLIntegral_ne_top_of_lintegral_eq_one
      (volume : Measure paper_theorem6_scoreSpace) f x1 x2 x3
      paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3
      hnorm s
  have hsource13gap :
      (volume : Measure paper_theorem6_scoreSpace)
        {ω | bestRemainingAfter
                (rum3RankByScoreFns
                  paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3 ω)
                (0 : Candidate 1) = (1 : Candidate 1) ∧
              ¬ bestRemainingAfter
                (rum3RankByScoreFns
                  paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3 ω)
                (1 : Candidate 1) = (0 : Candidate 1)} ≠ 0 := by
    simpa [paper_theorem6_scoreSpace, paper_theorem6_score1,
      paper_theorem6_score2, paper_theorem6_score3] using
      rum3Score_lambda13gap_source_volume_ne_zero
  have hsource23 :
      (volume : Measure paper_theorem6_scoreSpace)
        {ω | bestRemainingAfter
                (rum3RankByScoreFns
                  paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3 ω)
                (0 : Candidate 1) = (2 : Candidate 1)} ≠ 0 := by
    simpa [paper_theorem6_scoreSpace, paper_theorem6_score1,
      paper_theorem6_score2, paper_theorem6_score3] using
      rum3Score_lambda23wrong_source_volume_ne_zero
  have hsource12 :
      (volume : Measure paper_theorem6_scoreSpace)
        {ω | bestRemainingAfter
                (rum3RankByScoreFns
                  paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3 ω)
                (2 : Candidate 1) = (1 : Candidate 1)} ≠ 0 := by
    simpa [paper_theorem6_scoreSpace, paper_theorem6_score1,
      paper_theorem6_score2, paper_theorem6_score3] using
      rum3Score_lambda12wrong_source_volume_ne_zero
  have hbetter :
      Measurable
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3) :=
    rum3ContractRankByScoreFns_measurable
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
      t x1 x2 x3
  have hworse :
      Measurable
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3) :=
    rum3RankByScoreFns_measurable
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
  have hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) =
        firstChoice
          (rum3ContractRankByScoreFns
            t x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3 ω)} := by
    simpa only [Set.preimage_setOf_eq] using
      hbetter (show MeasurableSet
        {π : Ranking 1 | (0 : Candidate 1) = firstChoice π}
        from MeasurableSet.of_discrete)
  have hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) =
        firstChoice
          (rum3RankByScoreFns
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3 ω)} := by
    simpa only [Set.preimage_setOf_eq] using
      hworse (show MeasurableSet
        {π : Ranking 1 | (0 : Candidate 1) = firstChoice π}
        from MeasurableSet.of_discrete)
  have hcorrectedBase :
      (volume : Measure paper_theorem6_scoreSpace)
        ({ω | (0 : Candidate 1) =
              firstChoice
                (rum3ContractRankByScoreFns
                  t x1 x2 x3
                  paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3 ω)} ∩
          {ω | (0 : Candidate 1) =
              firstChoice
                (rum3RankByScoreFns
                  paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3 ω)}ᶜ) ≠
          0 := by
    simpa [paper_theorem6_scoreSpace, paper_theorem6_score1,
      paper_theorem6_score2, paper_theorem6_score3] using
      rum3Score_correctedTop_volume_ne_zero_of_t_lt_one
        ht0 ht1 htlt1 hx12 hx23
  have hcorrected_pos :
      (volume : Measure paper_theorem6_scoreSpace).withDensity D
        ({ω | (0 : Candidate 1) =
              firstChoice
                (rum3ContractRankByScoreFns
                  t x1 x2 x3
                  paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3 ω)} ∩
          {ω | (0 : Candidate 1) =
              firstChoice
                (rum3RankByScoreFns
                  paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3 ω)}ᶜ) ≠
          0 :=
    paper_theorem6_scoreDensity_withDensity_measure_ne_zero_of_base_measure_ne_zero
      (volume : Measure paper_theorem6_scoreSpace) x1 x2 x3
      paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3
      hD hpos (hbetterTopMeas.inter hworseTopMeas.compl) hcorrectedBase
  simpa [D, paper_theorem6_normalizedScoreRankingPMF] using
    paper_theorem6_threeCandidate_prefersWeakerCompetition_of_withDensity_rankByScores_facts_of_t_lt_one
      (volume : Measure paper_theorem6_scoreSpace) f x1 x2 x3 t
      paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3
      paper_theorem6_scoreSwap12 paper_theorem6_scoreSwap23
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
      hvalue1 hvalue2 hvalue3 hD hf hpos ht0 ht1 htlt1 hx12 hx23
      paper_theorem6_scoreSwap12_measurePreserving_volume
      (by intro ω; rfl) (by intro ω; rfl) (by intro ω; rfl)
      paper_theorem6_scoreSwap23_measurePreserving_volume
      (by intro ω; rfl) (by intro ω; rfl) (by intro ω; rfl)
      (hfiniteIntegral _)
      hsource13gap
      (hfiniteIntegral _)
      hsource23
      (hfiniteIntegral _)
      hsource12
      hcorrected_pos

/--
Appendix C / Lemmas 2 and 3 to Theorem 6 delta certificate.

Paper inputs: monotonicity gives `Pr[τ₁=x₁] > Pr[π₁=x₁]`, Lemma 3 gives
`Δp₂ ≤ Δp₁`, and Lemma 2 gives `Pr[τ₁=x₃] ≤ Pr[π₁=x₃]`.
-/
theorem paper_theorem6_deltaCertificate_of_lemmas2_3
    {μBetter μWorse : PMF (Ranking 1)}
    (monotonicity_top :
      firstChoiceProb μWorse (0 : Candidate 1) <
        firstChoiceProb μBetter (0 : Candidate 1))
    (lemma3_middle :
      firstChoiceProb μBetter (1 : Candidate 1) -
          firstChoiceProb μWorse (1 : Candidate 1) ≤
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (lemma2_bottom :
      firstChoiceProb μBetter (2 : Candidate 1) ≤
        firstChoiceProb μWorse (2 : Candidate 1)) :
    RUM3DeltaCertificate μBetter μWorse :=
  rum3DeltaCertificate_of_paper_lemmas
    monotonicity_top lemma3_middle lemma2_bottom

/--
Appendix C / Lemma 2, finite coupling form.

Paper statement: for `τ ∼ F_{θA}` and `π ∼ F_{θH}`,
`Pr[τ₁ = x₃] ≤ Pr[π₁ = x₃]`.

The continuous proof constructs a contraction coupling between the more accurate
and less accurate RUM realizations.  Lean exposes the finite probability step:
if the coupled better ranking putting `x₃` first implies the coupled worse
ranking puts `x₃` first, then the same bottom-first probability inequality
holds.
-/
theorem paper_lemma2_bottom_of_coupling
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter :
      firstChoiceProb μBetter (2 : Candidate 1) =
        EconCSLib.pmfProb ν (fun ω => (2 : Candidate 1) = firstChoice (better ω)))
    (hworse :
      firstChoiceProb μWorse (2 : Candidate 1) =
        EconCSLib.pmfProb ν (fun ω => (2 : Candidate 1) = firstChoice (worse ω)))
    (himp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω)) :
    firstChoiceProb μBetter (2 : Candidate 1) ≤
      firstChoiceProb μWorse (2 : Candidate 1) :=
  rum3_lemma2_bottom_of_coupling
    μBetter μWorse ν better worse hbetter hworse himp

/--
Appendix C / Lemma 3, finite transition-mass form for `i = 2`.

Paper statement specialized to three candidates: for `τ ∼ F_{θA}` and
`π ∼ F_{θH}`, `Pr[τ₁ = x₁] - Pr[π₁ = x₁] ≥
Pr[τ₁ = x₂] - Pr[π₁ = x₂]`.

Lean exposes the finite probability algebra used after the continuous proof
constructs the contraction map and the `swapi` comparison.  The remaining
continuous inputs are: top-first realizations do not leave the top under
contraction, and the `x₃ → x₂` transition mass is at most the `x₃ → x₁`
transition mass.
-/
theorem paper_lemma3_middle_of_transition_mass
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hbottomMiddle_le_bottomTop :
      EconCSLib.pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        EconCSLib.pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω))) :
    firstChoiceProb μBetter (1 : Candidate 1) -
        firstChoiceProb μWorse (1 : Candidate 1) ≤
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1) :=
  rum3_lemma3_middle_of_transition_mass
    μBetter μWorse ν better worse hbetter hworse hnoTopOut
    hbottomMiddle_le_bottomTop

/--
Appendix C / top-candidate monotonicity, finite coupling form.

The paper invokes monotonicity to get
`Pr[π₁ = x₁] < Pr[τ₁ = x₁]`.  Lean states the finite coupling condition that
proves this strict inequality: top-first human realizations remain top-first
after contraction, and at least one positive-mass realization is corrected into
top-first.
-/
theorem paper_monotonicity_top_of_coupling
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmass : 0 < (ν ω₀).toReal) :
    firstChoiceProb μWorse (0 : Candidate 1) <
      firstChoiceProb μBetter (0 : Candidate 1) :=
  rum3_monotonicity_top_of_coupling
    μBetter μWorse ν better worse hbetter hworse hnoTopOut
    hbetterTop hworseNotTop hmass

/--
Appendix C / Theorem 6, finite delta certificate from contraction facts.

This is the strongest finite endpoint for the first-choice-probability side of
Theorem 6.  It combines top monotonicity, Lemma 2, and Lemma 3 into the
`RUM3DeltaCertificate` required by the final payoff algebra.
-/
theorem paper_theorem6_deltaCertificate_of_finite_contraction_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmass : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbottomMiddle_le_bottomTop :
      EconCSLib.pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        EconCSLib.pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω))) :
    RUM3DeltaCertificate μBetter μWorse :=
  rum3DeltaCertificate_of_finite_contraction_facts
    μBetter μWorse ν better worse hbetter hworse hnoTopOut
    hbetterTop hworseNotTop hmass hbottomImp hbottomMiddle_le_bottomTop

/--
Appendix C / Lemma 3, finite `swapi` change-of-variables skeleton.

This is the discrete probability version of integrating the density comparison
over the swapped transition region.
-/
theorem paper_lemma3_bottomMiddle_transition_le_bottomTop_of_swap_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (ν : PMF Ω) (swap : Ω ≃ Ω)
    (better worse : Ω → Ranking 1)
    (hmap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (swap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (swap ω)))
    (hmass : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    EconCSLib.pmfProb ν (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω)) ≤
      EconCSLib.pmfProb ν (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω)) :=
  rum3_bottomMiddle_transition_le_bottomTop_of_swap_equiv
    ν swap better worse hmap hmass

/--
Appendix C / Theorem 6, delta certificate from a finite `swapi` equivalence.
-/
theorem paper_theorem6_deltaCertificate_of_finite_contraction_swap_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hmap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (swap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (swap ω)))
    (hmassSwap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    RUM3DeltaCertificate μBetter μWorse :=
  rum3DeltaCertificate_of_finite_contraction_swap_facts
    μBetter μWorse ν better worse swap hbetter hworse hnoTopOut
    hbetterTop hworseNotTop hmassTop hbottomImp hmap hmassSwap

/--
Appendix C / Theorem 6, delta certificate from score-level contraction and
finite `swapi` facts.

The ranking-level top-no-out, bottom-implication, and `x₃ → x₂` to `x₃ → x₁`
transition-map hypotheses are derived here from deterministic score geometry.
-/
theorem paper_theorem6_deltaCertificate_of_finite_score_contraction_swap_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (t x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ Ω)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hmassSwap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    RUM3DeltaCertificate μBetter μWorse :=
  rum3DeltaCertificate_of_finite_score_contraction_swap_facts
    μBetter μWorse ν better worse t x1 x2 x3 r1 r2 r3 swap
    ht0 ht1 hx12 hx23 hbetter hworse hbetterTop_of_scores
    hworseTop_scores_of_first hbetterBottom_scores_of_first
    hworseBottom_scores_of_first hworseBottom_of_scores
    hbetterMiddle_scores_of_first hswap1 hswap2 hswap3
    hbetterTop hworseNotTop hmassTop hmassSwap

/--
Appendix C / Theorem 6 from lambda facts plus finite contraction facts.

This wrapper is the current strongest non-measure-theoretic endpoint: once the
human two-candidate lambda certificate is available and the contraction coupling
supplies the finite monotonicity/Lemma 2/Lemma 3 inputs, Lean proves the paper's
weaker-competition conclusion in Definition 3 form.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_lambda_and_finite_contraction_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda : RUM3LambdaCertificate μWorse)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmass : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbottomMiddle_le_bottomTop :
      EconCSLib.pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        EconCSLib.pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω))) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_certificate
    (paper_theorem6_certificate_of_lambda_delta
      hvalue1 hvalue2 hvalue3 hx12 hx23 lambda
      (paper_theorem6_deltaCertificate_of_finite_contraction_facts
        μBetter μWorse ν better worse hbetter hworse hnoTopOut
        hbetterTop hworseNotTop hmass hbottomImp
        hbottomMiddle_le_bottomTop))

/--
Appendix C / pairwise human comparisons to Theorem 6 lambda certificate.
-/
theorem paper_theorem6_lambdaCertificate_of_pairwise_facts
    {μWorse : PMF (Ranking 1)}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_correct : (1 : ℝ) / 2 < rum3Lambda1 μWorse)
    (h23_not_sure : rum3Lambda1 μWorse < 1)
    (h12_correct : (1 : ℝ) / 2 < rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_facts
    h13_gt_23 h23_correct h23_not_sure h12_correct

/--
Appendix C / lambda upper bound: every `λᵢ` is a probability.
-/
theorem paper_theorem6_lambda1_le_one (μ : PMF (Ranking 1)) :
    rum3Lambda1 μ ≤ 1 :=
  rum3Lambda1_le_one μ

/--
Appendix C / strict `λ₁ < 1` from positive support on the wrong remaining
candidate after `x₁` is removed.
-/
theorem paper_theorem6_lambda1_lt_one_of_mass_choose_third_after_first_removed
    (μ : PMF (Ranking 1)) (π₀ : Ranking 1)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μ π₀).toReal) :
    rum3Lambda1 μ < 1 :=
  rum3Lambda1_lt_one_of_mass_choose_third_after_first_removed
    μ π₀ hchoose hmass

/--
Appendix C / strict `λ₁ < 1` from full support of the finite human ranking law.
-/
theorem paper_theorem6_lambda1_lt_one_of_full_support
    (μ : PMF (Ranking 1))
    (hfull : ∀ π : Ranking 1, 0 < (μ π).toReal) :
    rum3Lambda1 μ < 1 :=
  rum3Lambda1_lt_one_of_full_support μ hfull

/--
Appendix C / finite full-support bridge from realization preimages.
-/
theorem paper_theorem6_fullSupport_of_sample_preimages
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1)
    (hpreimage : ∀ π : Ranking 1,
      (μ π).toReal = EconCSLib.pmfProb ν (fun ω => rank ω = π))
    (hsupport : ∀ π : Ranking 1,
      ∃ ω : Ω, rank ω = π ∧ 0 < (ν ω).toReal) :
    ∀ π : Ranking 1, 0 < (μ π).toReal :=
  rum3_fullSupport_of_sample_preimages μ ν rank hpreimage hsupport

/--
Appendix C / finite preimage bridge for realization events.

If each ranking atom under `μ` is the probability of its realization preimage
under `ν`, then every ranking event has the same probability as its realization
preimage.  This is the finite pushforward layer used to discharge the marginal
identification hypotheses in the RUM Theorem 6 endpoint.
-/
theorem paper_theorem6_eventProb_of_sample_preimages
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1)
    (hpreimage : ∀ π : Ranking 1,
      (μ π).toReal = EconCSLib.pmfProb ν (fun ω => rank ω = π))
    (p : Ranking 1 → Prop) [DecidablePred p] :
    EconCSLib.pmfProb μ p =
      EconCSLib.pmfProb ν (fun ω => p (rank ω)) :=
  EconCSLib.pmfProb_eq_pmfProb_preimage_of_atom_eq
    μ ν rank hpreimage p

/--
Appendix C / finite PMF-map atom bridge.

For a finite realization law `ν`, the pushforward ranking law `ν.map rank`
assigns each ranking exactly the probability of its realization preimage.
-/
theorem paper_theorem6_map_atom_preimage
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (ν : PMF Ω) (rank : Ω → Ranking 1) (π : Ranking 1) :
    (((ν.map rank) π).toReal) =
      EconCSLib.pmfProb ν (fun ω => rank ω = π) :=
  EconCSLib.pmf_map_apply_toReal_eq_pmfProb_preimage ν rank π

/--
Appendix C / lambda certificate from pairwise facts plus support.

This version replaces the raw `λ₁ < 1` premise with a positive-mass witness that
the human law can choose `x₃` after `x₁` is removed.
-/
theorem paper_theorem6_lambdaCertificate_of_pairwise_facts_and_support
    {μWorse : PMF (Ranking 1)} {π₀ : Ranking 1}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_correct : (1 : ℝ) / 2 < rum3Lambda1 μWorse)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μWorse π₀).toReal)
    (h12_correct : (1 : ℝ) / 2 < rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_facts_and_support
    h13_gt_23 h23_correct hchoose hmass h12_correct

/--
Appendix C / lambda complement identity for the `x₂` vs `x₃` subproblem.
-/
theorem paper_theorem6_lambda1_wrong_eq_one_sub (μ : PMF (Ranking 1)) :
    EconCSLib.pmfProb μ
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
      1 - rum3Lambda1 μ :=
  rum3Lambda1_wrong_eq_one_sub μ

/--
Appendix C / lambda complement identity for the `x₁` vs `x₂` subproblem.
-/
theorem paper_theorem6_lambda3_wrong_eq_one_sub (μ : PMF (Ranking 1)) :
    EconCSLib.pmfProb μ
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
      1 - rum3Lambda3 μ :=
  rum3Lambda3_wrong_eq_one_sub μ

/--
Appendix C / pairwise correctness implies `λ₁ > 1/2`.
-/
theorem paper_theorem6_lambda1_half_of_wrong_lt_correct
    {μ : PMF (Ranking 1)}
    (hwrong :
      EconCSLib.pmfProb μ
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μ) :
    (1 : ℝ) / 2 < rum3Lambda1 μ :=
  rum3Lambda1_half_of_wrong_lt_correct hwrong

/--
Appendix C / pairwise correctness implies `λ₃ > 1/2`.
-/
theorem paper_theorem6_lambda3_half_of_wrong_lt_correct
    {μ : PMF (Ranking 1)}
    (hwrong :
      EconCSLib.pmfProb μ
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μ) :
    (1 : ℝ) / 2 < rum3Lambda3 μ :=
  rum3Lambda3_half_of_wrong_lt_correct hwrong

/--
Appendix C / lambda certificate from pairwise wrong-vs-correct comparisons.

This version states the `λ₁ > 1/2` and `λ₃ > 1/2` inputs as strict
wrong-choice-probability comparisons, which is the form naturally supplied by a
paired density argument.
-/
theorem paper_theorem6_lambdaCertificate_of_pairwise_wrong_facts_and_support
    {μWorse : PMF (Ranking 1)} {π₀ : Ranking 1}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_wrong_lt_correct :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μWorse)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μWorse π₀).toReal)
    (h12_wrong_lt_correct :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_support
    h13_gt_23 h23_wrong_lt_correct hchoose hmass h12_wrong_lt_correct

/--
Appendix C / lambda certificate from pairwise wrong-vs-correct comparisons and
full support of the finite human ranking law.
-/
theorem paper_theorem6_lambdaCertificate_of_pairwise_wrong_facts_and_full_support
    {μWorse : PMF (Ranking 1)}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_wrong_lt_correct :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μWorse)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (h12_wrong_lt_correct :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    h13_gt_23 h23_wrong_lt_correct hfull h12_wrong_lt_correct

/--
Appendix C / pairwise swap certificate for the `x₂` versus `x₃` comparison.

This is the finite change-of-variables form of the paper's paired-density
argument: a mass-improving swap from the wrong event to the correct event proves
the strict lambda comparison.
-/
theorem paper_theorem6_lambda1_wrong_lt_correct_of_pairwise_equiv
    (μ : PMF (Ranking 1)) (swap : Ranking 1 ≃ Ranking 1)
    (hmap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μ π).toReal ≤ (μ (swap π)).toReal)
    {π₀ : Ranking 1}
    (hwrong : bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict : (μ π₀).toReal < (μ (swap π₀)).toReal) :
    EconCSLib.pmfProb μ
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
      rum3Lambda1 μ :=
  rum3Lambda1_wrong_lt_correct_of_equiv
    μ swap hmap hmass hwrong hstrict

/--
Appendix C / pairwise swap certificate for the `x₁` versus `x₂` comparison.
-/
theorem paper_theorem6_lambda3_wrong_lt_correct_of_pairwise_equiv
    (μ : PMF (Ranking 1)) (swap : Ranking 1 ≃ Ranking 1)
    (hmap : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μ π).toReal ≤ (μ (swap π)).toReal)
    {π₀ : Ranking 1}
    (hwrong : bestRemainingAfter π₀ (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (μ π₀).toReal < (μ (swap π₀)).toReal) :
    EconCSLib.pmfProb μ
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
      rum3Lambda3 μ :=
  rum3Lambda3_wrong_lt_correct_of_equiv
    μ swap hmap hmass hwrong hstrict

/--
Appendix C / pairwise swap certificate for the `λ₁ < λ₂` gap.
-/
theorem paper_theorem6_lambda1_lt_lambda2_of_pairwise_equiv
    (μ : PMF (Ranking 1)) (swap : Ranking 1 ≃ Ranking 1)
    (hmap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap π) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μ π).toReal ≤ (μ (swap π)).toReal)
    {π₀ : Ranking 1}
    (hsource : bestRemainingAfter π₀ (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (μ π₀).toReal < (μ (swap π₀)).toReal) :
    rum3Lambda1 μ < rum3Lambda2 μ :=
  rum3Lambda1_lt_lambda2_of_equiv
    μ swap hmap hmass hsource hstrict

/--
Appendix C / lambda certificate from finite pairwise swap facts.

This is the paper-facing package for the two strict pairwise comparisons plus
the support witness used to prove `λ₁ < 1`.
-/
theorem paper_theorem6_lambdaCertificate_of_pairwise_swap_facts_and_support
    {μWorse : PMF (Ranking 1)}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (swap23 : Ranking 1 ≃ Ranking 1)
    (hmap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap23 π)).toReal)
    {π23 : Ranking 1}
    (hwrong23 : bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (μWorse π23).toReal < (μWorse (swap23 π23)).toReal)
    {πsupport : Ranking 1}
    (hchooseSupport :
      bestRemainingAfter πsupport (0 : Candidate 1) = (2 : Candidate 1))
    (hmassSupport : 0 < (μWorse πsupport).toReal)
    (swap12 : Ranking 1 ≃ Ranking 1)
    (hmap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap12 π)).toReal)
    {π12 : Ranking 1}
    (hwrong12 : bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (μWorse π12).toReal < (μWorse (swap12 π12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_swap_facts_and_support
    h13_gt_23 swap23 hmap23 hmass23 hwrong23 hstrict23
    hchooseSupport hmassSupport swap12 hmap12 hmass12 hwrong12 hstrict12

/--
Appendix C / lambda certificate from finite pairwise swap facts, including the
`λ₁ < λ₂` gap as a swap certificate.
-/
theorem paper_theorem6_lambdaCertificate_of_all_pairwise_swap_facts_and_support
    {μWorse : PMF (Ranking 1)}
    (swap13gap : Ranking 1 ≃ Ranking 1)
    (hmap13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap13gap π) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap13gap π)).toReal)
    {π13gap : Ranking 1}
    (hsource13gap :
      bestRemainingAfter π13gap (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict13gap :
      (μWorse π13gap).toReal < (μWorse (swap13gap π13gap)).toReal)
    (swap23 : Ranking 1 ≃ Ranking 1)
    (hmap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap23 π)).toReal)
    {π23 : Ranking 1}
    (hwrong23 : bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (μWorse π23).toReal < (μWorse (swap23 π23)).toReal)
    {πsupport : Ranking 1}
    (hchooseSupport :
      bestRemainingAfter πsupport (0 : Candidate 1) = (2 : Candidate 1))
    (hmassSupport : 0 < (μWorse πsupport).toReal)
    (swap12 : Ranking 1 ≃ Ranking 1)
    (hmap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap12 π)).toReal)
    {π12 : Ranking 1}
    (hwrong12 : bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (μWorse π12).toReal < (μWorse (swap12 π12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_all_pairwise_swap_facts_and_support
    swap13gap hmap13gap hmass13gap hsource13gap hstrict13gap
    swap23 hmap23 hmass23 hwrong23 hstrict23
    hchooseSupport hmassSupport swap12 hmap12 hmass12 hwrong12 hstrict12

/--
Appendix C / lambda certificate from finite pairwise swap facts plus full
support of the finite human ranking law.
-/
theorem paper_theorem6_lambdaCertificate_of_all_pairwise_swap_facts_and_full_support
    {μWorse : PMF (Ranking 1)}
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (swap13gap : Ranking 1 ≃ Ranking 1)
    (hmap13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap13gap π) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap13gap π)).toReal)
    {π13gap : Ranking 1}
    (hsource13gap :
      bestRemainingAfter π13gap (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict13gap :
      (μWorse π13gap).toReal < (μWorse (swap13gap π13gap)).toReal)
    (swap23 : Ranking 1 ≃ Ranking 1)
    (hmap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap23 π)).toReal)
    {π23 : Ranking 1}
    (hwrong23 : bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (μWorse π23).toReal < (μWorse (swap23 π23)).toReal)
    (swap12 : Ranking 1 ≃ Ranking 1)
    (hmap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap12 π)).toReal)
    {π12 : Ranking 1}
    (hwrong12 : bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (μWorse π12).toReal < (μWorse (swap12 π12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_all_pairwise_swap_facts_and_full_support
    hfull swap13gap hmap13gap hmass13gap hsource13gap hstrict13gap
    swap23 hmap23 hmass23 hwrong23 hstrict23
    swap12 hmap12 hmass12 hwrong12 hstrict12

/--
Appendix C / lambda certificate from finite sample-space swap facts.

The swaps act on realizations rather than directly on rankings; the marginal
equalities identify the realization events with the ranking-law lambda events.
-/
theorem paper_theorem6_lambdaCertificate_of_sample_swap_facts_and_full_support
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μWorse : PMF (Ranking 1)}
    (ν : PMF Ω) (rank : Ω → Ranking 1)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (hlambda1μ :
      rum3Lambda1 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong23μ :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hlambda3μ :
      rum3Lambda3 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong12μ :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)))
    (swap13gap : Ω ≃ Ω)
    (hmap13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap13gap ω)) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hmass13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap13gap ω)).toReal)
    {ω13gap : Ω}
    (hsource13gap :
      bestRemainingAfter (rank ω13gap) (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict13gap :
      (ν ω13gap).toReal < (ν (swap13gap ω13gap)).toReal)
    (swap23 : Ω ≃ Ω)
    (hmap23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap23 ω)) (0 : Candidate 1) =
          (1 : Candidate 1))
    (hmass23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap23 ω)).toReal)
    {ω23 : Ω}
    (hwrong23 :
      bestRemainingAfter (rank ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (ν ω23).toReal < (ν (swap23 ω23)).toReal)
    (swap12 : Ω ≃ Ω)
    (hmap12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap12 ω)) (2 : Candidate 1) =
          (0 : Candidate 1))
    (hmass12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap12 ω)).toReal)
    {ω12 : Ω}
    (hwrong12 :
      bestRemainingAfter (rank ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (ν ω12).toReal < (ν (swap12 ω12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_sample_swap_facts_and_full_support
    ν rank hfull hlambda1μ hlambda2μ hwrong23μ hlambda3μ hwrong12μ
    swap13gap hmap13gap hmass13gap hsource13gap hstrict13gap
    swap23 hmap23 hmass23 hwrong23 hstrict23
    swap12 hmap12 hmass12 hwrong12 hstrict12

/--
Appendix C / lambda certificate from sample-space swap facts, with the
`λ₁ < λ₂` gap proved only on the residual event `λ₁ ∧ ¬λ₂`.
-/
theorem paper_theorem6_lambdaCertificate_of_sample_cross_gap_and_wrong_swap_facts_and_full_support
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μWorse : PMF (Ranking 1)}
    (ν : PMF Ω) (rank : Ω → Ranking 1)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (hlambda1μ :
      rum3Lambda1 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong23μ :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hlambda3μ :
      rum3Lambda3 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong12μ :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)))
    (swap13gap : Ω ≃ Ω)
    (hmap13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (rank (swap13gap ω)) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank (swap13gap ω)) (0 : Candidate 1) =
            (1 : Candidate 1))
    (hmass13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap13gap ω)).toReal)
    {ω13gap : Ω}
    (hsource13gap :
      bestRemainingAfter (rank ω13gap) (0 : Candidate 1) = (1 : Candidate 1) ∧
        ¬ bestRemainingAfter (rank ω13gap) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hstrict13gap :
      (ν ω13gap).toReal < (ν (swap13gap ω13gap)).toReal)
    (swap23 : Ω ≃ Ω)
    (hmap23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap23 ω)) (0 : Candidate 1) =
          (1 : Candidate 1))
    (hmass23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap23 ω)).toReal)
    {ω23 : Ω}
    (hwrong23 :
      bestRemainingAfter (rank ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (ν ω23).toReal < (ν (swap23 ω23)).toReal)
    (swap12 : Ω ≃ Ω)
    (hmap12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap12 ω)) (2 : Candidate 1) =
          (0 : Candidate 1))
    (hmass12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap12 ω)).toReal)
    {ω12 : Ω}
    (hwrong12 :
      bestRemainingAfter (rank ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (ν ω12).toReal < (ν (swap12 ω12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_sample_cross_gap_and_wrong_swap_facts_and_full_support
    ν rank hfull hlambda1μ hlambda2μ hwrong23μ hlambda3μ hwrong12μ
    swap13gap hmap13gap hmass13gap hsource13gap hstrict13gap
    swap23 hmap23 hmass23 hwrong23 hstrict23
    swap12 hmap12 hmass12 hwrong12 hstrict12

/--
Appendix C / score-level map for the `x₂` versus `x₃` lambda swap.
-/
theorem paper_theorem6_lambda1_wrong_to_correct_map_of_score_swap23
    {Ω : Type*} (rank : Ω → Ranking 1) (s2 s3 : Ω → ℝ) (swap : Ω → Ω)
    (hwrong_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        s2 ω < s3 ω)
    (hcorrect_of_scores : ∀ ω,
      s3 ω ≤ s2 ω →
        bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hswap2 : ∀ ω, s2 (swap ω) = s3 ω)
    (hswap3 : ∀ ω, s3 (swap ω) = s2 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (0 : Candidate 1) =
          (1 : Candidate 1) :=
  rum3Lambda1_wrong_to_correct_map_of_score_swap23
    rank s2 s3 swap hwrong_scores hcorrect_of_scores hswap2 hswap3

/--
Appendix C / score-level map for the `x₁` versus `x₂` lambda swap.
-/
theorem paper_theorem6_lambda3_wrong_to_correct_map_of_score_swap12
    {Ω : Type*} (rank : Ω → Ranking 1) (s1 s2 : Ω → ℝ) (swap : Ω → Ω)
    (hwrong_scores : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        s1 ω < s2 ω)
    (hcorrect_of_scores : ∀ ω,
      s2 ω ≤ s1 ω →
        bestRemainingAfter (rank ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hswap1 : ∀ ω, s1 (swap ω) = s2 ω)
    (hswap2 : ∀ ω, s2 (swap ω) = s1 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (2 : Candidate 1) =
          (0 : Candidate 1) :=
  rum3Lambda3_wrong_to_correct_map_of_score_swap12
    rank s1 s2 swap hwrong_scores hcorrect_of_scores hswap1 hswap2

/--
Appendix C / score-level map for the `λ₁ < λ₂` comparison.
-/
theorem paper_theorem6_lambda1_to_lambda2_map_of_score_swap12
    {Ω : Type*} (rank : Ω → Ranking 1)
    (s1 s2 s3 : Ω → ℝ) (swap : Ω → Ω)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        s3 ω ≤ s2 ω)
    (htarget_of_scores : ∀ ω,
      s3 ω ≤ s1 ω →
        bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hswap1 : ∀ ω, s1 (swap ω) = s2 ω)
    (hswap3 : ∀ ω, s3 (swap ω) = s3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (1 : Candidate 1) =
          (0 : Candidate 1) :=
  rum3Lambda1_to_lambda2_map_of_score_swap12
    rank s1 s2 s3 swap hsource_scores htarget_of_scores hswap1 hswap3

/--
Appendix C / score-level cross-event map for the `λ₁ < λ₂` comparison.

The source is the residual event `λ₁ ∧ ¬λ₂`; after swapping the top and middle
score coordinates, the target is the residual event `λ₂ ∧ ¬λ₁`.
-/
theorem paper_theorem6_lambda1_to_lambda2_cross_map_of_score_swap12
    {Ω : Type*} (rank : Ω → Ranking 1)
    (s1 s2 s3 : Ω → ℝ) (swap : Ω → Ω)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        s3 ω ≤ s2 ω)
    (hnot_target_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        s1 ω < s3 ω)
    (htarget_of_scores : ∀ ω,
      s3 ω ≤ s1 ω →
        bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hnot_source_of_scores : ∀ ω,
      s2 ω < s3 ω →
        ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hswap1 : ∀ ω, s1 (swap ω) = s2 ω)
    (hswap2 : ∀ ω, s2 (swap ω) = s1 ω)
    (hswap3 : ∀ ω, s3 (swap ω) = s3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank (swap ω)) (0 : Candidate 1) =
            (1 : Candidate 1) :=
  rum3Lambda1_to_lambda2_cross_map_of_score_swap12
    rank s1 s2 s3 swap hsource_scores hnot_target_scores
    htarget_of_scores hnot_source_of_scores hswap1 hswap2 hswap3

/--
Appendix C / Theorem 6 from the narrowed finite/pointwise RUM inputs.

This is the strongest current paper-facing endpoint.  It replaces the raw lambda
half-bounds with wrong-vs-correct pairwise comparisons, and replaces the raw
Lemma 3 transition-mass premise with a finite `swapi` equivalence plus
mass-dominance premise.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_pairwise_wrong_and_finite_swap_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_wrong_lt_correct :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μWorse)
    {π₀ : Ranking 1}
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmassLambda : 0 < (μWorse π₀).toReal)
    (h12_wrong_lt_correct :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μWorse)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hmap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (swap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (swap ω)))
    (hmassSwap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_certificate
    (paper_theorem6_certificate_of_lambda_delta
      hvalue1 hvalue2 hvalue3 hx12 hx23
      (paper_theorem6_lambdaCertificate_of_pairwise_wrong_facts_and_support
        h13_gt_23 h23_wrong_lt_correct hchoose hmassLambda
        h12_wrong_lt_correct)
      (paper_theorem6_deltaCertificate_of_finite_contraction_swap_facts
        μBetter μWorse ν better worse swap hbetter hworse hnoTopOut
        hbetterTop hworseNotTop hmassTop hbottomImp hmap hmassSwap))

/--
Appendix C / Theorem 6 from finite pairwise and delta swap certificates.

This endpoint exposes the paired finite change-of-variables structure on both
remaining sides of the RUM proof: pairwise swaps prove the lambda half-bounds,
and the transition-region `swapi` proves Lemma 3's delta comparison.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_finite_pairwise_and_delta_swap_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1) (deltaSwap : Ω ≃ Ω)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (lambdaSwap23 : Ranking 1 ≃ Ranking 1)
    (hlambdaMap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (lambdaSwap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaMass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (lambdaSwap23 π)).toReal)
    {π23 : Ranking 1}
    (hlambdaWrong23 :
      bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hlambdaStrict23 :
      (μWorse π23).toReal < (μWorse (lambdaSwap23 π23)).toReal)
    {πsupport : Ranking 1}
    (hchooseSupport :
      bestRemainingAfter πsupport (0 : Candidate 1) = (2 : Candidate 1))
    (hmassLambda : 0 < (μWorse πsupport).toReal)
    (lambdaSwap12 : Ranking 1 ≃ Ranking 1)
    (hlambdaMap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (lambdaSwap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hlambdaMass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (lambdaSwap12 π)).toReal)
    {π12 : Ranking 1}
    (hlambdaWrong12 :
      bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict12 :
      (μWorse π12).toReal < (μWorse (lambdaSwap12 π12)).toReal)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hdeltaMap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (deltaSwap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (deltaSwap ω)))
    (hdeltaMass : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (deltaSwap ω)).toReal) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_pairwise_wrong_and_finite_swap_facts
    ν better worse deltaSwap hvalue1 hvalue2 hvalue3 hx12 hx23
    h13_gt_23
    (paper_theorem6_lambda1_wrong_lt_correct_of_pairwise_equiv
      μWorse lambdaSwap23 hlambdaMap23 hlambdaMass23
      hlambdaWrong23 hlambdaStrict23)
    hchooseSupport hmassLambda
    (paper_theorem6_lambda3_wrong_lt_correct_of_pairwise_equiv
      μWorse lambdaSwap12 hlambdaMap12 hlambdaMass12
      hlambdaWrong12 hlambdaStrict12)
    hbetter hworse hnoTopOut hbetterTop hworseNotTop hmassTop
    hbottomImp hdeltaMap hdeltaMass

/--
Appendix C / Theorem 6 from finite swap certificates only for the currently
discrete parts of the RUM proof.

All three lambda facts are supplied by finite pairwise change-of-variables
certificates, and Lemma 3's delta comparison is supplied by the finite `swapi`
certificate.  The remaining non-discrete work is to instantiate these finite
certificates from the continuous RUM density model.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_all_finite_swap_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1) (deltaSwap : Ω ≃ Ω)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambdaSwap13gap : Ranking 1 ≃ Ranking 1)
    (hlambdaMap13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (lambdaSwap13gap π) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hlambdaMass13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (lambdaSwap13gap π)).toReal)
    {π13gap : Ranking 1}
    (hlambdaSource13gap :
      bestRemainingAfter π13gap (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict13gap :
      (μWorse π13gap).toReal < (μWorse (lambdaSwap13gap π13gap)).toReal)
    (lambdaSwap23 : Ranking 1 ≃ Ranking 1)
    (hlambdaMap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (lambdaSwap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaMass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (lambdaSwap23 π)).toReal)
    {π23 : Ranking 1}
    (hlambdaWrong23 :
      bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hlambdaStrict23 :
      (μWorse π23).toReal < (μWorse (lambdaSwap23 π23)).toReal)
    {πsupport : Ranking 1}
    (hchooseSupport :
      bestRemainingAfter πsupport (0 : Candidate 1) = (2 : Candidate 1))
    (hmassLambda : 0 < (μWorse πsupport).toReal)
    (lambdaSwap12 : Ranking 1 ≃ Ranking 1)
    (hlambdaMap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (lambdaSwap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hlambdaMass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (lambdaSwap12 π)).toReal)
    {π12 : Ranking 1}
    (hlambdaWrong12 :
      bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict12 :
      (μWorse π12).toReal < (μWorse (lambdaSwap12 π12)).toReal)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hdeltaMap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (deltaSwap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (deltaSwap ω)))
    (hdeltaMass : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (deltaSwap ω)).toReal) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_finite_pairwise_and_delta_swap_facts
    ν better worse deltaSwap hvalue1 hvalue2 hvalue3 hx12 hx23
    (paper_theorem6_lambda1_lt_lambda2_of_pairwise_equiv
      μWorse lambdaSwap13gap hlambdaMap13gap hlambdaMass13gap
      hlambdaSource13gap hlambdaStrict13gap)
    lambdaSwap23 hlambdaMap23 hlambdaMass23 hlambdaWrong23 hlambdaStrict23
    hchooseSupport hmassLambda
    lambdaSwap12 hlambdaMap12 hlambdaMass12 hlambdaWrong12 hlambdaStrict12
    hbetter hworse hnoTopOut hbetterTop hworseNotTop hmassTop
    hbottomImp hdeltaMap hdeltaMass

/--
Appendix C / Theorem 6 from finite swap certificates and full finite support.

Compared with `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_all_finite_swap_facts`,
this endpoint replaces the explicit `λ₁ < 1` support witness with full support
of the finite human ranking law, matching the paper's "support everywhere"
premise at the ranking-law level.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_all_finite_swap_facts_and_full_support
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1) (deltaSwap : Ω ≃ Ω)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (lambdaSwap13gap : Ranking 1 ≃ Ranking 1)
    (hlambdaMap13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (lambdaSwap13gap π) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hlambdaMass13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (lambdaSwap13gap π)).toReal)
    {π13gap : Ranking 1}
    (hlambdaSource13gap :
      bestRemainingAfter π13gap (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict13gap :
      (μWorse π13gap).toReal < (μWorse (lambdaSwap13gap π13gap)).toReal)
    (lambdaSwap23 : Ranking 1 ≃ Ranking 1)
    (hlambdaMap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (lambdaSwap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaMass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (lambdaSwap23 π)).toReal)
    {π23 : Ranking 1}
    (hlambdaWrong23 :
      bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hlambdaStrict23 :
      (μWorse π23).toReal < (μWorse (lambdaSwap23 π23)).toReal)
    (lambdaSwap12 : Ranking 1 ≃ Ranking 1)
    (hlambdaMap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (lambdaSwap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hlambdaMass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (lambdaSwap12 π)).toReal)
    {π12 : Ranking 1}
    (hlambdaWrong12 :
      bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict12 :
      (μWorse π12).toReal < (μWorse (lambdaSwap12 π12)).toReal)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hdeltaMap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (deltaSwap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (deltaSwap ω)))
    (hdeltaMass : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (deltaSwap ω)).toReal) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_certificate
    (paper_theorem6_certificate_of_lambda_delta
      hvalue1 hvalue2 hvalue3 hx12 hx23
      (paper_theorem6_lambdaCertificate_of_all_pairwise_swap_facts_and_full_support
        hfull lambdaSwap13gap hlambdaMap13gap hlambdaMass13gap
        hlambdaSource13gap hlambdaStrict13gap
        lambdaSwap23 hlambdaMap23 hlambdaMass23
        hlambdaWrong23 hlambdaStrict23
        lambdaSwap12 hlambdaMap12 hlambdaMass12
        hlambdaWrong12 hlambdaStrict12)
      (paper_theorem6_deltaCertificate_of_finite_contraction_swap_facts
        μBetter μWorse ν better worse deltaSwap hbetter hworse hnoTopOut
        hbetterTop hworseNotTop hmassTop hbottomImp hdeltaMap hdeltaMass))

/--
Appendix C / Theorem 6 from finite lambda swaps, full support, and score-level
contraction/`swapi` geometry.

This is the strongest non-measure-theoretic endpoint currently exposed: the
remaining hypotheses are marginal identification, score-to-ranking interfaces,
finite full support, and finite mass dominance for the `swapi` map.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_all_finite_swap_and_score_contraction_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1)
    (t : ℝ) (r1 r2 r3 : Ω → ℝ) (deltaSwap : Ω ≃ Ω)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (lambdaSwap13gap : Ranking 1 ≃ Ranking 1)
    (hlambdaMap13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (lambdaSwap13gap π) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hlambdaMass13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (lambdaSwap13gap π)).toReal)
    {π13gap : Ranking 1}
    (hlambdaSource13gap :
      bestRemainingAfter π13gap (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict13gap :
      (μWorse π13gap).toReal < (μWorse (lambdaSwap13gap π13gap)).toReal)
    (lambdaSwap23 : Ranking 1 ≃ Ranking 1)
    (hlambdaMap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (lambdaSwap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaMass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (lambdaSwap23 π)).toReal)
    {π23 : Ranking 1}
    (hlambdaWrong23 :
      bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hlambdaStrict23 :
      (μWorse π23).toReal < (μWorse (lambdaSwap23 π23)).toReal)
    (lambdaSwap12 : Ranking 1 ≃ Ranking 1)
    (hlambdaMap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (lambdaSwap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hlambdaMass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (lambdaSwap12 π)).toReal)
    {π12 : Ranking 1}
    (hlambdaWrong12 :
      bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict12 :
      (μWorse π12).toReal < (μWorse (lambdaSwap12 π12)).toReal)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hdeltaSwap1 : ∀ ω, r1 (deltaSwap ω) = r2 ω)
    (hdeltaSwap2 : ∀ ω, r2 (deltaSwap ω) = r1 ω)
    (hdeltaSwap3 : ∀ ω, r3 (deltaSwap ω) = r3 ω)
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hdeltaMass : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (deltaSwap ω)).toReal) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_certificate
    (paper_theorem6_certificate_of_lambda_delta
      hvalue1 hvalue2 hvalue3 hx12 hx23
      (paper_theorem6_lambdaCertificate_of_all_pairwise_swap_facts_and_full_support
        hfull lambdaSwap13gap hlambdaMap13gap hlambdaMass13gap
        hlambdaSource13gap hlambdaStrict13gap
        lambdaSwap23 hlambdaMap23 hlambdaMass23
        hlambdaWrong23 hlambdaStrict23
        lambdaSwap12 hlambdaMap12 hlambdaMass12
        hlambdaWrong12 hlambdaStrict12)
      (paper_theorem6_deltaCertificate_of_finite_score_contraction_swap_facts
        μBetter μWorse ν better worse t x1 x2 x3 r1 r2 r3 deltaSwap
        ht0 ht1 hx12 hx23 hbetter hworse hbetterTop_of_scores
        hworseTop_scores_of_first hbetterBottom_scores_of_first
        hworseBottom_scores_of_first hworseBottom_of_scores
        hbetterMiddle_scores_of_first hdeltaSwap1 hdeltaSwap2 hdeltaSwap3
        hbetterTop hworseNotTop hmassTop hdeltaMass))

/--
Appendix C / Theorem 6 from realization-space lambda swaps and score-level
contraction/`swapi` geometry.

This endpoint uses the same finite realization law `ν` for the human ranking
lambda comparisons and for the algorithm/human contraction coupling.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_sample_swaps_and_score_contraction_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1)
    (t : ℝ) (r1 r2 r3 : Ω → ℝ) (deltaSwap : Ω ≃ Ω)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (hlambda1μ :
      rum3Lambda1 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong23μ :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hlambda3μ :
      rum3Lambda3 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong12μ :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (1 : Candidate 1)))
    (lambdaSwap13gap : Ω ≃ Ω)
    (hlambdaMap13gap : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (worse (lambdaSwap13gap ω)) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hlambdaMass13gap : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap13gap ω)).toReal)
    {ω13gap : Ω}
    (hlambdaSource13gap :
      bestRemainingAfter (worse ω13gap) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict13gap :
      (ν ω13gap).toReal < (ν (lambdaSwap13gap ω13gap)).toReal)
    (lambdaSwap23 : Ω ≃ Ω)
    (hlambdaMap23 : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (worse (lambdaSwap23 ω)) (0 : Candidate 1) =
          (1 : Candidate 1))
    (hlambdaMass23 : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap23 ω)).toReal)
    {ω23 : Ω}
    (hlambdaWrong23 :
      bestRemainingAfter (worse ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hlambdaStrict23 :
      (ν ω23).toReal < (ν (lambdaSwap23 ω23)).toReal)
    (lambdaSwap12 : Ω ≃ Ω)
    (hlambdaMap12 : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (worse (lambdaSwap12 ω)) (2 : Candidate 1) =
          (0 : Candidate 1))
    (hlambdaMass12 : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap12 ω)).toReal)
    {ω12 : Ω}
    (hlambdaWrong12 :
      bestRemainingAfter (worse ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict12 :
      (ν ω12).toReal < (ν (lambdaSwap12 ω12)).toReal)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hdeltaSwap1 : ∀ ω, r1 (deltaSwap ω) = r2 ω)
    (hdeltaSwap2 : ∀ ω, r2 (deltaSwap ω) = r1 ω)
    (hdeltaSwap3 : ∀ ω, r3 (deltaSwap ω) = r3 ω)
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hdeltaMass : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (deltaSwap ω)).toReal) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_certificate
    (paper_theorem6_certificate_of_lambda_delta
      hvalue1 hvalue2 hvalue3 hx12 hx23
      (paper_theorem6_lambdaCertificate_of_sample_swap_facts_and_full_support
        ν worse hfull hlambda1μ hlambda2μ hwrong23μ hlambda3μ hwrong12μ
        lambdaSwap13gap hlambdaMap13gap hlambdaMass13gap
        hlambdaSource13gap hlambdaStrict13gap
        lambdaSwap23 hlambdaMap23 hlambdaMass23
        hlambdaWrong23 hlambdaStrict23
        lambdaSwap12 hlambdaMap12 hlambdaMass12
        hlambdaWrong12 hlambdaStrict12)
      (paper_theorem6_deltaCertificate_of_finite_score_contraction_swap_facts
        μBetter μWorse ν better worse t x1 x2 x3 r1 r2 r3 deltaSwap
        ht0 ht1 hx12 hx23 hbetter hworse hbetterTop_of_scores
        hworseTop_scores_of_first hbetterBottom_scores_of_first
        hworseBottom_scores_of_first hworseBottom_of_scores
        hbetterMiddle_scores_of_first hdeltaSwap1 hdeltaSwap2 hdeltaSwap3
        hbetterTop hworseNotTop hmassTop hdeltaMass))

/--
Appendix C / Theorem 6 from realization preimages, sample-space lambda swaps,
and score-level contraction/`swapi` geometry.

This strengthens the sample-space endpoint by replacing the separate lambda
marginal equalities, first-choice marginal equalities, and finite full-support
premise with atom-preimage facts for the two ranking laws.  The remaining
finite hypotheses are exactly the score/ranking interfaces, realization-space
swap maps, positive witnesses, and mass dominance facts.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_sample_preimages_swaps_and_score_contraction_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1)
    (t : ℝ) (r1 r2 r3 : Ω → ℝ) (deltaSwap : Ω ≃ Ω)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hbetterPreimage : ∀ π : Ranking 1,
      (μBetter π).toReal = EconCSLib.pmfProb ν (fun ω => better ω = π))
    (hworsePreimage : ∀ π : Ranking 1,
      (μWorse π).toReal = EconCSLib.pmfProb ν (fun ω => worse ω = π))
    (hworseSupport : ∀ π : Ranking 1,
      ∃ ω : Ω, worse ω = π ∧ 0 < (ν ω).toReal)
    (lambdaSwap13gap : Ω ≃ Ω)
    (hlambdaMap13gap : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (worse (lambdaSwap13gap ω)) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hlambdaMass13gap : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap13gap ω)).toReal)
    {ω13gap : Ω}
    (hlambdaSource13gap :
      bestRemainingAfter (worse ω13gap) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict13gap :
      (ν ω13gap).toReal < (ν (lambdaSwap13gap ω13gap)).toReal)
    (lambdaSwap23 : Ω ≃ Ω)
    (hlambdaMap23 : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (worse (lambdaSwap23 ω)) (0 : Candidate 1) =
          (1 : Candidate 1))
    (hlambdaMass23 : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap23 ω)).toReal)
    {ω23 : Ω}
    (hlambdaWrong23 :
      bestRemainingAfter (worse ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hlambdaStrict23 :
      (ν ω23).toReal < (ν (lambdaSwap23 ω23)).toReal)
    (lambdaSwap12 : Ω ≃ Ω)
    (hlambdaMap12 : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (worse (lambdaSwap12 ω)) (2 : Candidate 1) =
          (0 : Candidate 1))
    (hlambdaMass12 : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap12 ω)).toReal)
    {ω12 : Ω}
    (hlambdaWrong12 :
      bestRemainingAfter (worse ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict12 :
      (ν ω12).toReal < (ν (lambdaSwap12 ω12)).toReal)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hdeltaSwap1 : ∀ ω, r1 (deltaSwap ω) = r2 ω)
    (hdeltaSwap2 : ∀ ω, r2 (deltaSwap ω) = r1 ω)
    (hdeltaSwap3 : ∀ ω, r3 (deltaSwap ω) = r3 ω)
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hdeltaMass : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (deltaSwap ω)).toReal) :
    Model.PrefersWeakerCompetition μBetter μWorse value := by
  have hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal :=
    paper_theorem6_fullSupport_of_sample_preimages
      μWorse ν worse hworsePreimage hworseSupport
  have hlambda1μ :
      rum3Lambda1 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1)) := by
    unfold rum3Lambda1
    exact paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
  have hlambda2μ :
      rum3Lambda2 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1)) := by
    unfold rum3Lambda2
    exact paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))
  have hwrong23μ :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (2 : Candidate 1)) :=
    paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1))
  have hlambda3μ :
      rum3Lambda3 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (0 : Candidate 1)) := by
    unfold rum3Lambda3
    exact paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))
  have hwrong12μ :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (1 : Candidate 1)) :=
    paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1))
  have hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)) := by
    intro c
    unfold firstChoiceProb
    exact paper_theorem6_eventProb_of_sample_preimages
      μBetter ν better hbetterPreimage
      (fun π => c = firstChoice π)
  have hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)) := by
    intro c
    unfold firstChoiceProb
    exact paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => c = firstChoice π)
  exact
    paper_theorem6_threeCandidate_prefersWeakerCompetition_of_sample_swaps_and_score_contraction_facts
      ν better worse t r1 r2 r3 deltaSwap
      hvalue1 hvalue2 hvalue3 hx12 hx23 ht0 ht1 hfull
      hlambda1μ hlambda2μ hwrong23μ hlambda3μ hwrong12μ
      lambdaSwap13gap hlambdaMap13gap hlambdaMass13gap
      hlambdaSource13gap hlambdaStrict13gap
      lambdaSwap23 hlambdaMap23 hlambdaMass23 hlambdaWrong23 hlambdaStrict23
      lambdaSwap12 hlambdaMap12 hlambdaMass12 hlambdaWrong12 hlambdaStrict12
      hbetter hworse hbetterTop_of_scores hworseTop_scores_of_first
      hbetterBottom_scores_of_first hworseBottom_scores_of_first
      hworseBottom_of_scores hbetterMiddle_scores_of_first
      hdeltaSwap1 hdeltaSwap2 hdeltaSwap3 hbetterTop hworseNotTop hmassTop
      hdeltaMass

/--
Appendix C / Theorem 6 for mapped finite realization laws.

This is the strongest finite pushforward endpoint: the better and worse ranking
laws are the actual PMF maps of the same finite realization law.  The theorem
therefore discharges the atom-preimage, event-marginal, and ranking-law support
bridges internally; the remaining assumptions are the realization support
witnesses, score/ranking interfaces, swap maps, witnesses, and mass dominance
facts.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_mapped_sample_swaps_and_score_contraction_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1)
    (t : ℝ) (r1 r2 r3 : Ω → ℝ) (deltaSwap : Ω ≃ Ω)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hworseSupport : ∀ π : Ranking 1,
      ∃ ω : Ω, worse ω = π ∧ 0 < (ν ω).toReal)
    (lambdaSwap13gap : Ω ≃ Ω)
    (hlambdaMap13gap : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (worse (lambdaSwap13gap ω)) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hlambdaMass13gap : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap13gap ω)).toReal)
    {ω13gap : Ω}
    (hlambdaSource13gap :
      bestRemainingAfter (worse ω13gap) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict13gap :
      (ν ω13gap).toReal < (ν (lambdaSwap13gap ω13gap)).toReal)
    (lambdaSwap23 : Ω ≃ Ω)
    (hlambdaMap23 : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (worse (lambdaSwap23 ω)) (0 : Candidate 1) =
          (1 : Candidate 1))
    (hlambdaMass23 : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap23 ω)).toReal)
    {ω23 : Ω}
    (hlambdaWrong23 :
      bestRemainingAfter (worse ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hlambdaStrict23 :
      (ν ω23).toReal < (ν (lambdaSwap23 ω23)).toReal)
    (lambdaSwap12 : Ω ≃ Ω)
    (hlambdaMap12 : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (worse (lambdaSwap12 ω)) (2 : Candidate 1) =
          (0 : Candidate 1))
    (hlambdaMass12 : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap12 ω)).toReal)
    {ω12 : Ω}
    (hlambdaWrong12 :
      bestRemainingAfter (worse ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict12 :
      (ν ω12).toReal < (ν (lambdaSwap12 ω12)).toReal)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hdeltaSwap1 : ∀ ω, r1 (deltaSwap ω) = r2 ω)
    (hdeltaSwap2 : ∀ ω, r2 (deltaSwap ω) = r1 ω)
    (hdeltaSwap3 : ∀ ω, r3 (deltaSwap ω) = r3 ω)
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hdeltaMass : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (deltaSwap ω)).toReal) :
    Model.PrefersWeakerCompetition (ν.map better) (ν.map worse) value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_sample_preimages_swaps_and_score_contraction_facts
    (μBetter := ν.map better) (μWorse := ν.map worse)
    ν better worse t r1 r2 r3 deltaSwap
    hvalue1 hvalue2 hvalue3 hx12 hx23 ht0 ht1
    (fun π => paper_theorem6_map_atom_preimage ν better π)
    (fun π => paper_theorem6_map_atom_preimage ν worse π)
    hworseSupport
    lambdaSwap13gap hlambdaMap13gap hlambdaMass13gap
    hlambdaSource13gap hlambdaStrict13gap
    lambdaSwap23 hlambdaMap23 hlambdaMass23 hlambdaWrong23 hlambdaStrict23
    lambdaSwap12 hlambdaMap12 hlambdaMass12 hlambdaWrong12 hlambdaStrict12
    hbetterTop_of_scores hworseTop_scores_of_first
    hbetterBottom_scores_of_first hworseBottom_scores_of_first
    hworseBottom_of_scores hbetterMiddle_scores_of_first
    hdeltaSwap1 hdeltaSwap2 hdeltaSwap3 hbetterTop hworseNotTop hmassTop
    hdeltaMass

/--
Appendix C / Theorem 6 for mapped finite realization laws with score-derived
lambda event maps.

This version derives the three lambda-event maps from score inequalities and
coordinate-swap equations.  It is closer to the paper proof than the raw
sample-map endpoint: the remaining lambda-side probability assumptions are the
finite mass dominance facts and strict witness atoms.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_mapped_score_swaps_and_score_contraction_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1)
    (t : ℝ) (r1 r2 r3 : Ω → ℝ) (deltaSwap : Ω ≃ Ω)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hworseSupport : ∀ π : Ranking 1,
      ∃ ω : Ω, worse ω = π ∧ 0 < (ν ω).toReal)
    (lambdaSwap13gap : Ω ≃ Ω)
    (hlambdaSource13gap_scores : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hlambdaTarget13gap_of_scores : ∀ ω,
      r3 ω ≤ r1 ω →
        bestRemainingAfter (worse ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hlambdaSwap13gap1 : ∀ ω, r1 (lambdaSwap13gap ω) = r2 ω)
    (hlambdaSwap13gap3 : ∀ ω, r3 (lambdaSwap13gap ω) = r3 ω)
    (hlambdaMass13gap : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap13gap ω)).toReal)
    {ω13gap : Ω}
    (hlambdaSource13gap :
      bestRemainingAfter (worse ω13gap) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict13gap :
      (ν ω13gap).toReal < (ν (lambdaSwap13gap ω13gap)).toReal)
    (lambdaSwap23 : Ω ≃ Ω)
    (hlambdaWrong23_scores : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        r2 ω < r3 ω)
    (hlambdaCorrect23_of_scores : ∀ ω,
      r3 ω ≤ r2 ω →
        bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaSwap23_2 : ∀ ω, r2 (lambdaSwap23 ω) = r3 ω)
    (hlambdaSwap23_3 : ∀ ω, r3 (lambdaSwap23 ω) = r2 ω)
    (hlambdaMass23 : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap23 ω)).toReal)
    {ω23 : Ω}
    (hlambdaWrong23 :
      bestRemainingAfter (worse ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hlambdaStrict23 :
      (ν ω23).toReal < (ν (lambdaSwap23 ω23)).toReal)
    (lambdaSwap12 : Ω ≃ Ω)
    (hlambdaWrong12_scores : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        r1 ω < r2 ω)
    (hlambdaCorrect12_of_scores : ∀ ω,
      r2 ω ≤ r1 ω →
        bestRemainingAfter (worse ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hlambdaSwap12_1 : ∀ ω, r1 (lambdaSwap12 ω) = r2 ω)
    (hlambdaSwap12_2 : ∀ ω, r2 (lambdaSwap12 ω) = r1 ω)
    (hlambdaMass12 : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap12 ω)).toReal)
    {ω12 : Ω}
    (hlambdaWrong12 :
      bestRemainingAfter (worse ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict12 :
      (ν ω12).toReal < (ν (lambdaSwap12 ω12)).toReal)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hdeltaSwap1 : ∀ ω, r1 (deltaSwap ω) = r2 ω)
    (hdeltaSwap2 : ∀ ω, r2 (deltaSwap ω) = r1 ω)
    (hdeltaSwap3 : ∀ ω, r3 (deltaSwap ω) = r3 ω)
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hdeltaMass : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (deltaSwap ω)).toReal) :
    Model.PrefersWeakerCompetition (ν.map better) (ν.map worse) value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_mapped_sample_swaps_and_score_contraction_facts
    ν better worse t r1 r2 r3 deltaSwap
    hvalue1 hvalue2 hvalue3 hx12 hx23 ht0 ht1 hworseSupport
    lambdaSwap13gap
    (paper_theorem6_lambda1_to_lambda2_map_of_score_swap12
      worse r1 r2 r3 lambdaSwap13gap
      hlambdaSource13gap_scores hlambdaTarget13gap_of_scores
      hlambdaSwap13gap1 hlambdaSwap13gap3)
    hlambdaMass13gap hlambdaSource13gap hlambdaStrict13gap
    lambdaSwap23
    (paper_theorem6_lambda1_wrong_to_correct_map_of_score_swap23
      worse r2 r3 lambdaSwap23
      hlambdaWrong23_scores hlambdaCorrect23_of_scores
      hlambdaSwap23_2 hlambdaSwap23_3)
    hlambdaMass23 hlambdaWrong23 hlambdaStrict23
    lambdaSwap12
    (paper_theorem6_lambda3_wrong_to_correct_map_of_score_swap12
      worse r1 r2 lambdaSwap12
      hlambdaWrong12_scores hlambdaCorrect12_of_scores
      hlambdaSwap12_1 hlambdaSwap12_2)
    hlambdaMass12 hlambdaWrong12 hlambdaStrict12
    hbetterTop_of_scores hworseTop_scores_of_first
    hbetterBottom_scores_of_first hworseBottom_scores_of_first
    hworseBottom_of_scores hbetterMiddle_scores_of_first
    hdeltaSwap1 hdeltaSwap2 hdeltaSwap3 hbetterTop hworseNotTop hmassTop
    hdeltaMass

/--
Appendix C / Theorem 6 for mapped finite realization laws with score-derived
lambda maps and density-derived delta mass.

Compared with
`paper_theorem6_threeCandidate_prefersWeakerCompetition_of_mapped_score_swaps_and_score_contraction_facts`,
this endpoint also derives the delta-side `swapi` mass dominance from the
finite density-product formula and weak well-ordering.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_mapped_score_swaps_and_delta_density_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1)
    (t : ℝ) (r1 r2 r3 : Ω → ℝ) (deltaSwap : Ω ≃ Ω)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hworseSupport : ∀ π : Ranking 1,
      ∃ ω : Ω, worse ω = π ∧ 0 < (ν ω).toReal)
    (lambdaSwap13gap : Ω ≃ Ω)
    (hlambdaSource13gap_scores : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hlambdaTarget13gap_of_scores : ∀ ω,
      r3 ω ≤ r1 ω →
        bestRemainingAfter (worse ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hlambdaSwap13gap1 : ∀ ω, r1 (lambdaSwap13gap ω) = r2 ω)
    (hlambdaSwap13gap3 : ∀ ω, r3 (lambdaSwap13gap ω) = r3 ω)
    (hlambdaMass13gap : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap13gap ω)).toReal)
    {ω13gap : Ω}
    (hlambdaSource13gap :
      bestRemainingAfter (worse ω13gap) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict13gap :
      (ν ω13gap).toReal < (ν (lambdaSwap13gap ω13gap)).toReal)
    (lambdaSwap23 : Ω ≃ Ω)
    (hlambdaWrong23_scores : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        r2 ω < r3 ω)
    (hlambdaCorrect23_of_scores : ∀ ω,
      r3 ω ≤ r2 ω →
        bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaSwap23_2 : ∀ ω, r2 (lambdaSwap23 ω) = r3 ω)
    (hlambdaSwap23_3 : ∀ ω, r3 (lambdaSwap23 ω) = r2 ω)
    (hlambdaMass23 : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap23 ω)).toReal)
    {ω23 : Ω}
    (hlambdaWrong23 :
      bestRemainingAfter (worse ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hlambdaStrict23 :
      (ν ω23).toReal < (ν (lambdaSwap23 ω23)).toReal)
    (lambdaSwap12 : Ω ≃ Ω)
    (hlambdaWrong12_scores : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        r1 ω < r2 ω)
    (hlambdaCorrect12_of_scores : ∀ ω,
      r2 ω ≤ r1 ω →
        bestRemainingAfter (worse ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hlambdaSwap12_1 : ∀ ω, r1 (lambdaSwap12 ω) = r2 ω)
    (hlambdaSwap12_2 : ∀ ω, r2 (lambdaSwap12 ω) = r1 ω)
    (hlambdaMass12 : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap12 ω)).toReal)
    {ω12 : Ω}
    (hlambdaWrong12 :
      bestRemainingAfter (worse ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict12 :
      (ν ω12).toReal < (ν (lambdaSwap12 ω12)).toReal)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hdeltaSwap1 : ∀ ω, r1 (deltaSwap ω) = r2 ω)
    (hdeltaSwap2 : ∀ ω, r2 (deltaSwap ω) = r1 ω)
    (hdeltaSwap3 : ∀ ω, r3 (deltaSwap ω) = r3 ω)
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (f : ℝ → ℝ)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hdeltaCtx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3)) :
    Model.PrefersWeakerCompetition (ν.map better) (ν.map worse) value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_mapped_score_swaps_and_score_contraction_facts
    ν better worse t r1 r2 r3 deltaSwap
    hvalue1 hvalue2 hvalue3 hx12 hx23 ht0 ht1 hworseSupport
    lambdaSwap13gap hlambdaSource13gap_scores hlambdaTarget13gap_of_scores
    hlambdaSwap13gap1 hlambdaSwap13gap3 hlambdaMass13gap
    hlambdaSource13gap hlambdaStrict13gap
    lambdaSwap23 hlambdaWrong23_scores hlambdaCorrect23_of_scores
    hlambdaSwap23_2 hlambdaSwap23_3 hlambdaMass23
    hlambdaWrong23 hlambdaStrict23
    lambdaSwap12 hlambdaWrong12_scores hlambdaCorrect12_of_scores
    hlambdaSwap12_1 hlambdaSwap12_2 hlambdaMass12
    hlambdaWrong12 hlambdaStrict12
    hbetterTop_of_scores hworseTop_scores_of_first
    hbetterBottom_scores_of_first hworseBottom_scores_of_first
    hworseBottom_of_scores hbetterMiddle_scores_of_first
    hdeltaSwap1 hdeltaSwap2 hdeltaSwap3 hbetterTop hworseNotTop hmassTop
    (paper_theorem6_deltaSwap_mass_le_of_density_formula
      ν f x1 x2 x3 t r1 r2 r3 deltaSwap better worse hf hdens
      hdeltaSwap1 hdeltaSwap2 hdeltaSwap3 hdeltaCtx ht0 ht1 hx12
      hbetterMiddle_scores_of_first)

/--
Appendix C / Theorem 6 with density-derived wrong-to-correct lambda masses and
density-derived delta mass.

The remaining lambda mass premise is the `λ₁ < λ₂` gap certificate, which is the
part of the paper proof that uses the separate two-candidate monotonicity
argument rather than the wrong-to-correct density swaps.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_mapped_density_wrong_swaps_and_delta_density_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1)
    (t : ℝ) (r1 r2 r3 : Ω → ℝ) (deltaSwap : Ω ≃ Ω)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hworseSupport : ∀ π : Ranking 1,
      ∃ ω : Ω, worse ω = π ∧ 0 < (ν ω).toReal)
    (f : ℝ → ℝ)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (lambdaSwap13gap : Ω ≃ Ω)
    (hlambdaSource13gap_scores : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hlambdaTarget13gap_of_scores : ∀ ω,
      r3 ω ≤ r1 ω →
        bestRemainingAfter (worse ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hlambdaSwap13gap1 : ∀ ω, r1 (lambdaSwap13gap ω) = r2 ω)
    (hlambdaSwap13gap3 : ∀ ω, r3 (lambdaSwap13gap ω) = r3 ω)
    (hlambdaMass13gap : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (lambdaSwap13gap ω)).toReal)
    {ω13gap : Ω}
    (hlambdaSource13gap :
      bestRemainingAfter (worse ω13gap) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict13gap :
      (ν ω13gap).toReal < (ν (lambdaSwap13gap ω13gap)).toReal)
    (lambdaSwap23 : Ω ≃ Ω)
    (hlambdaWrong23_scores : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        r2 ω < r3 ω)
    (hlambdaCorrect23_of_scores : ∀ ω,
      r3 ω ≤ r2 ω →
        bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaSwap23_1 : ∀ ω, r1 (lambdaSwap23 ω) = r1 ω)
    (hlambdaSwap23_2 : ∀ ω, r2 (lambdaSwap23 ω) = r3 ω)
    (hlambdaSwap23_3 : ∀ ω, r3 (lambdaSwap23 ω) = r2 ω)
    (hlambdaCtx23 : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        0 ≤ f (r1 ω - x1))
    {ω23 : Ω}
    (hlambdaWrong23 :
      bestRemainingAfter (worse ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hlambdaStrict23 :
      (ν ω23).toReal < (ν (lambdaSwap23 ω23)).toReal)
    (lambdaSwap12 : Ω ≃ Ω)
    (hlambdaWrong12_scores : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        r1 ω < r2 ω)
    (hlambdaCorrect12_of_scores : ∀ ω,
      r2 ω ≤ r1 ω →
        bestRemainingAfter (worse ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hlambdaSwap12_1 : ∀ ω, r1 (lambdaSwap12 ω) = r2 ω)
    (hlambdaSwap12_2 : ∀ ω, r2 (lambdaSwap12 ω) = r1 ω)
    (hlambdaSwap12_3 : ∀ ω, r3 (lambdaSwap12 ω) = r3 ω)
    (hlambdaCtx12 : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        0 ≤ f (r3 ω - x3))
    {ω12 : Ω}
    (hlambdaWrong12 :
      bestRemainingAfter (worse ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hlambdaStrict12 :
      (ν ω12).toReal < (ν (lambdaSwap12 ω12)).toReal)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hdeltaSwap1 : ∀ ω, r1 (deltaSwap ω) = r2 ω)
    (hdeltaSwap2 : ∀ ω, r2 (deltaSwap ω) = r1 ω)
    (hdeltaSwap3 : ∀ ω, r3 (deltaSwap ω) = r3 ω)
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hdeltaCtx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3)) :
    Model.PrefersWeakerCompetition (ν.map better) (ν.map worse) value :=
  paper_theorem6_threeCandidate_prefersWeakerCompetition_of_mapped_score_swaps_and_delta_density_facts
    ν better worse t r1 r2 r3 deltaSwap
    hvalue1 hvalue2 hvalue3 hx12 hx23 ht0 ht1 hworseSupport
    lambdaSwap13gap hlambdaSource13gap_scores hlambdaTarget13gap_of_scores
    hlambdaSwap13gap1 hlambdaSwap13gap3 hlambdaMass13gap
    hlambdaSource13gap hlambdaStrict13gap
    lambdaSwap23 hlambdaWrong23_scores hlambdaCorrect23_of_scores
    hlambdaSwap23_2 hlambdaSwap23_3
    (paper_theorem6_lambda23_mass_le_of_density_and_score_facts
      ν f x1 x2 x3 worse r1 r2 r3 lambdaSwap23 hf hdens
      hlambdaSwap23_1 hlambdaSwap23_2 hlambdaSwap23_3
      hlambdaCtx23 hx23 hlambdaWrong23_scores)
    hlambdaWrong23 hlambdaStrict23
    lambdaSwap12 hlambdaWrong12_scores hlambdaCorrect12_of_scores
    hlambdaSwap12_1 hlambdaSwap12_2
    (paper_theorem6_lambda12_mass_le_of_density_and_score_facts
      ν f x1 x2 x3 worse r1 r2 r3 lambdaSwap12 hf hdens
      hlambdaSwap12_1 hlambdaSwap12_2 hlambdaSwap12_3
      hlambdaCtx12 hx12 hlambdaWrong12_scores)
    hlambdaWrong12 hlambdaStrict12
    hbetterTop_of_scores hworseTop_scores_of_first
    hbetterBottom_scores_of_first hworseBottom_scores_of_first
    hworseBottom_of_scores hbetterMiddle_scores_of_first
    hdeltaSwap1 hdeltaSwap2 hdeltaSwap3 hbetterTop hworseNotTop hmassTop
    f hf hdens hdeltaCtx

/--
Appendix C / Theorem 6 with the residual `λ₁ ∧ ¬λ₂` gap, wrong-to-correct
lambda comparisons, and delta comparison all derived from the finite
density-product formula.

Paper statement matched: for three candidates `x₁ > x₂ > x₃`, a RUM with
strictly well-ordered positive noise, and the paper's contraction coupling from
human to algorithmic scores, the human-against-algorithm expected utility is
strictly below the human-against-human expected utility.

Lean still states the finite realization interface explicitly: `ν` is the
finite score-sample law, `better = ν.map better` is the contracted ranking law,
`worse = ν.map worse` is the original human ranking law, and the score/ranking
interface assumptions say those rankings agree with the score inequalities.
-/
theorem paper_theorem6_threeCandidate_prefersWeakerCompetition_of_mapped_density_cross_gap_and_delta_density_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (ν : PMF Ω) (better worse : Ω → Ranking 1)
    (t : ℝ) (r1 r2 r3 : Ω → ℝ) (deltaSwap : Ω ≃ Ω)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hworseSupport : ∀ π : Ranking 1,
      ∃ ω : Ω, worse ω = π ∧ 0 < (ν ω).toReal)
    (f : ℝ → ℝ)
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (lambdaSwap13gap : Ω ≃ Ω)
    (hlambdaSource13gap_scores : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hlambdaNotTarget13gap_scores : ∀ ω,
      ¬ bestRemainingAfter (worse ω) (1 : Candidate 1) = (0 : Candidate 1) →
        r1 ω < r3 ω)
    (hlambdaTarget13gap_of_scores : ∀ ω,
      r3 ω ≤ r1 ω →
        bestRemainingAfter (worse ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hlambdaNotSource13gap_of_scores : ∀ ω,
      r2 ω < r3 ω →
        ¬ bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaSwap13gap1 : ∀ ω, r1 (lambdaSwap13gap ω) = r2 ω)
    (hlambdaSwap13gap2 : ∀ ω, r2 (lambdaSwap13gap ω) = r1 ω)
    (hlambdaSwap13gap3 : ∀ ω, r3 (lambdaSwap13gap ω) = r3 ω)
    {ω13gap : Ω}
    (hlambdaSource13gap :
      bestRemainingAfter (worse ω13gap) (0 : Candidate 1) = (1 : Candidate 1) ∧
        ¬ bestRemainingAfter (worse ω13gap) (1 : Candidate 1) =
          (0 : Candidate 1))
    (lambdaSwap23 : Ω ≃ Ω)
    (hlambdaWrong23_scores : ∀ ω,
      bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
        r2 ω < r3 ω)
    (hlambdaCorrect23_of_scores : ∀ ω,
      r3 ω ≤ r2 ω →
        bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hlambdaSwap23_1 : ∀ ω, r1 (lambdaSwap23 ω) = r1 ω)
    (hlambdaSwap23_2 : ∀ ω, r2 (lambdaSwap23 ω) = r3 ω)
    (hlambdaSwap23_3 : ∀ ω, r3 (lambdaSwap23 ω) = r2 ω)
    {ω23 : Ω}
    (hlambdaWrong23 :
      bestRemainingAfter (worse ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (lambdaSwap12 : Ω ≃ Ω)
    (hlambdaWrong12_scores : ∀ ω,
      bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
        r1 ω < r2 ω)
    (hlambdaCorrect12_of_scores : ∀ ω,
      r2 ω ≤ r1 ω →
        bestRemainingAfter (worse ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hlambdaSwap12_1 : ∀ ω, r1 (lambdaSwap12 ω) = r2 ω)
    (hlambdaSwap12_2 : ∀ ω, r2 (lambdaSwap12 ω) = r1 ω)
    (hlambdaSwap12_3 : ∀ ω, r3 (lambdaSwap12 ω) = r3 ω)
    {ω12 : Ω}
    (hlambdaWrong12 :
      bestRemainingAfter (worse ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hdeltaSwap1 : ∀ ω, r1 (deltaSwap ω) = r2 ω)
    (hdeltaSwap2 : ∀ ω, r2 (deltaSwap ω) = r1 ω)
    (hdeltaSwap3 : ∀ ω, r3 (deltaSwap ω) = r3 ω)
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal) :
    Model.PrefersWeakerCompetition (ν.map better) (ν.map worse) value := by
  let μBetter : PMF (Ranking 1) := ν.map better
  let μWorse : PMF (Ranking 1) := ν.map worse
  have hfWeak : WeaklyWellOrderedNoise f := hf.weak
  have hbetterPreimage : ∀ π : Ranking 1,
      (μBetter π).toReal = EconCSLib.pmfProb ν (fun ω => better ω = π) := by
    intro π
    exact paper_theorem6_map_atom_preimage ν better π
  have hworsePreimage : ∀ π : Ranking 1,
      (μWorse π).toReal = EconCSLib.pmfProb ν (fun ω => worse ω = π) := by
    intro π
    exact paper_theorem6_map_atom_preimage ν worse π
  have hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal :=
    paper_theorem6_fullSupport_of_sample_preimages
      μWorse ν worse hworsePreimage hworseSupport
  have hlambda1μ :
      rum3Lambda1 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1)) := by
    unfold rum3Lambda1
    exact paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
  have hlambda2μ :
      rum3Lambda2 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1)) := by
    unfold rum3Lambda2
    exact paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))
  have hwrong23μ :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (2 : Candidate 1)) :=
    paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1))
  have hlambda3μ :
      rum3Lambda3 μWorse =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (0 : Candidate 1)) := by
    unfold rum3Lambda3
    exact paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))
  have hwrong12μ :
      EconCSLib.pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        EconCSLib.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (1 : Candidate 1)) :=
    paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1))
  have hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (better ω)) := by
    intro c
    unfold firstChoiceProb
    exact paper_theorem6_eventProb_of_sample_preimages
      μBetter ν better hbetterPreimage
      (fun π => c = firstChoice π)
  have hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        EconCSLib.pmfProb ν (fun ω => c = firstChoice (worse ω)) := by
    intro c
    unfold firstChoiceProb
    exact paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => c = firstChoice π)
  have hlambdaMap13gap :
      ∀ ω,
        bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
            ¬ bestRemainingAfter (worse ω) (1 : Candidate 1) =
              (0 : Candidate 1) →
          bestRemainingAfter (worse (lambdaSwap13gap ω)) (1 : Candidate 1) =
              (0 : Candidate 1) ∧
            ¬ bestRemainingAfter (worse (lambdaSwap13gap ω))
                (0 : Candidate 1) = (1 : Candidate 1) :=
    paper_theorem6_lambda1_to_lambda2_cross_map_of_score_swap12
      worse r1 r2 r3 lambdaSwap13gap hlambdaSource13gap_scores
      hlambdaNotTarget13gap_scores hlambdaTarget13gap_of_scores
      hlambdaNotSource13gap_of_scores hlambdaSwap13gap1
      hlambdaSwap13gap2 hlambdaSwap13gap3
  have hlambdaMass13gap :
      ∀ ω,
        bestRemainingAfter (worse ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
            ¬ bestRemainingAfter (worse ω) (1 : Candidate 1) =
              (0 : Candidate 1) →
          (ν ω).toReal ≤ (ν (lambdaSwap13gap ω)).toReal :=
    paper_theorem6_lambda13gap_mass_le_of_density_and_score_facts
      ν f x1 x2 x3 worse r1 r2 r3 lambdaSwap13gap hfWeak hdens
      hlambdaSwap13gap1 hlambdaSwap13gap2 hlambdaSwap13gap3
      (fun ω _ => le_of_lt (hpos (r3 ω - x3))) hx12
      hlambdaSource13gap_scores hlambdaNotTarget13gap_scores
  have hlambdaStrict13gap :
      (ν ω13gap).toReal < (ν (lambdaSwap13gap ω13gap)).toReal :=
    paper_theorem6_lambda13gap_mass_lt_of_density_and_score_facts
      ν f x1 x2 x3 worse r1 r2 r3 lambdaSwap13gap hf hdens
      hlambdaSwap13gap1 hlambdaSwap13gap2 hlambdaSwap13gap3
      (fun ω _ => hpos (r3 ω - x3)) hx12
      hlambdaSource13gap_scores hlambdaNotTarget13gap_scores
      ω13gap hlambdaSource13gap
  have hlambdaMap23 :
      ∀ ω,
        bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
          bestRemainingAfter (worse (lambdaSwap23 ω)) (0 : Candidate 1) =
            (1 : Candidate 1) :=
    paper_theorem6_lambda1_wrong_to_correct_map_of_score_swap23
      worse r2 r3 lambdaSwap23
      hlambdaWrong23_scores hlambdaCorrect23_of_scores
      hlambdaSwap23_2 hlambdaSwap23_3
  have hlambdaMass23 :
      ∀ ω,
        bestRemainingAfter (worse ω) (0 : Candidate 1) = (2 : Candidate 1) →
          (ν ω).toReal ≤ (ν (lambdaSwap23 ω)).toReal :=
    paper_theorem6_lambda23_mass_le_of_density_and_score_facts
      ν f x1 x2 x3 worse r1 r2 r3 lambdaSwap23 hfWeak hdens
      hlambdaSwap23_1 hlambdaSwap23_2 hlambdaSwap23_3
      (fun ω _ => le_of_lt (hpos (r1 ω - x1))) hx23
      hlambdaWrong23_scores
  have hlambdaStrict23 :
      (ν ω23).toReal < (ν (lambdaSwap23 ω23)).toReal :=
    paper_theorem6_lambda_swap23_mass_lt_of_density_formula
      ν f x1 x2 x3 r1 r2 r3 lambdaSwap23
      (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
        (2 : Candidate 1))
      hf hdens hlambdaSwap23_1 hlambdaSwap23_2 hlambdaSwap23_3
      (fun ω _ => hpos (r1 ω - x1)) hx23 hlambdaWrong23_scores
      ω23 hlambdaWrong23
  have hlambdaMap12 :
      ∀ ω,
        bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
          bestRemainingAfter (worse (lambdaSwap12 ω)) (2 : Candidate 1) =
            (0 : Candidate 1) :=
    paper_theorem6_lambda3_wrong_to_correct_map_of_score_swap12
      worse r1 r2 lambdaSwap12
      hlambdaWrong12_scores hlambdaCorrect12_of_scores
      hlambdaSwap12_1 hlambdaSwap12_2
  have hlambdaMass12 :
      ∀ ω,
        bestRemainingAfter (worse ω) (2 : Candidate 1) = (1 : Candidate 1) →
          (ν ω).toReal ≤ (ν (lambdaSwap12 ω)).toReal :=
    paper_theorem6_lambda12_mass_le_of_density_and_score_facts
      ν f x1 x2 x3 worse r1 r2 r3 lambdaSwap12 hfWeak hdens
      hlambdaSwap12_1 hlambdaSwap12_2 hlambdaSwap12_3
      (fun ω _ => le_of_lt (hpos (r3 ω - x3))) hx12
      hlambdaWrong12_scores
  have hlambdaStrict12 :
      (ν ω12).toReal < (ν (lambdaSwap12 ω12)).toReal :=
    paper_theorem6_lambda_swap12_mass_lt_of_density_formula
      ν f x1 x2 x3 r1 r2 r3 lambdaSwap12
      (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
        (1 : Candidate 1))
      hf hdens hlambdaSwap12_1 hlambdaSwap12_2 hlambdaSwap12_3
      (fun ω _ => hpos (r3 ω - x3)) hx12 hlambdaWrong12_scores
      ω12 hlambdaWrong12
  have hdeltaMass :
      ∀ ω,
        (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω) →
          (ν ω).toReal ≤ (ν (deltaSwap ω)).toReal :=
    paper_theorem6_deltaSwap_mass_le_of_density_formula
      ν f x1 x2 x3 t r1 r2 r3 deltaSwap better worse hfWeak hdens
      hdeltaSwap1 hdeltaSwap2 hdeltaSwap3
      (fun ω _ => le_of_lt (hpos (r3 ω - x3))) ht0 ht1 hx12
      hbetterMiddle_scores_of_first
  exact
    paper_theorem6_threeCandidate_prefersWeakerCompetition_of_certificate
      (paper_theorem6_certificate_of_lambda_delta
        hvalue1 hvalue2 hvalue3 hx12 hx23
        (paper_theorem6_lambdaCertificate_of_sample_cross_gap_and_wrong_swap_facts_and_full_support
          ν worse hfull hlambda1μ hlambda2μ hwrong23μ hlambda3μ hwrong12μ
          lambdaSwap13gap hlambdaMap13gap hlambdaMass13gap
          hlambdaSource13gap hlambdaStrict13gap
          lambdaSwap23 hlambdaMap23 hlambdaMass23
          hlambdaWrong23 hlambdaStrict23
          lambdaSwap12 hlambdaMap12 hlambdaMass12
          hlambdaWrong12 hlambdaStrict12)
        (paper_theorem6_deltaCertificate_of_finite_score_contraction_swap_facts
          μBetter μWorse ν better worse t x1 x2 x3 r1 r2 r3 deltaSwap
          ht0 ht1 hx12 hx23 hbetter hworse hbetterTop_of_scores
          hworseTop_scores_of_first hbetterBottom_scores_of_first
          hworseBottom_scores_of_first hworseBottom_of_scores
          hbetterMiddle_scores_of_first hdeltaSwap1 hdeltaSwap2 hdeltaSwap3
          hbetterTop hworseNotTop hmassTop hdeltaMass))

namespace MallowsComparison

/--
Paper Definition 2 (independent-reranking preference).

For a fixed ranking law μ and value vector v:
algorithmic second-mover policy is preferred to shared-reuse when the second
mover's expected reranking gain is positive.
-/
theorem paper_definition2_prefersIndependentReranking
    (n : ℕ) (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (h : Model.PrefersIndependentReranking μ value) :
    Model.PrefersIndependentReranking μ value := by
  simpa using h

/--
Paper Definition 3 (weaker-competition preference).

For a pair of ranking laws μBetter, μWorse, second mover is better off when the
first mover uses the noisier law μWorse rather than the more concentrated law
μBetter.
-/
theorem paper_definition3_prefersWeakerCompetition
    (n : ℕ) (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ)
    (h : Model.PrefersWeakerCompetition μBetter μWorse value) :
    Model.PrefersWeakerCompetition μBetter μWorse value := by
  exact h

/--
Paper fixed-parameter hypotheses (Definitions 2 and 3).
-/
theorem paper_definition_hypotheses (n : ℕ) (M : Model n)
    (h : Model.PaperHypotheses M) : Model.PaperHypotheses M := by
  exact h

/--
Paper Definition 2 rewritten by first-choice decomposition.

Equation (3) is equivalent to a positive first-choice-fiber weighted sum.
-/
theorem paper_definition2_iff_firstChoiceGapMassSum_pos
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersIndependentReranking μ value ↔
      0 < ∑ c : Candidate n,
        firstChoiceMissProb μ c * firstChoiceGapMass μ value c := by
  simpa using prefersIndependentReranking_iff_firstChoiceGapMassSum_pos (μ := μ) (value := value)

/--
Paper Definition 3 rewritten by first-choice decomposition.

The paper’s weak-competition comparison is equivalent to a candidatewise weighted
sum over first-choice collision probabilities.
-/
theorem paper_definition3_iff_firstChoiceCollisionDiffSum_pos
    {n : ℕ} (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersWeakerCompetition μBetter μWorse value ↔
      0 < ∑ c : Candidate n,
        firstChoiceCollisionDiff μBetter μWorse c *
          firstChoiceGapMass μWorse value c := by
  simpa using prefersWeakerCompetition_iff_firstChoiceCollisionDiffSum_pos
    (μBetter := μBetter) (μWorse := μWorse) (value := value)

/--
Appendix E (top-two expansion): numerator decomposition.

The unnormalized first-choice gap mass attached to candidate c decomposes over all
candidates d by top-two pair probabilities.
-/
theorem paper_appendixE_firstChoiceGapWeight_eq_sum_firstSecondWeight
    {n : ℕ} (M : MallowsSpec n) (value : Candidate n → ℝ) (c : Candidate n) :
    M.firstChoiceGapWeight value c =
      ∑ d : Candidate n, M.firstSecondWeight c d * (value c - value d) := by
  exact M.firstChoiceGapWeight_eq_sum_firstSecondWeight value c

/--
Appendix E (pairwise regrouping): cleared independent-reranking numerator as
ordered top-two pair sum.
-/
theorem paper_appendixE_independent_weight_sum_eq_pair_sum
    {n : ℕ} (M : MallowsSpec n) (value : Candidate n → ℝ) :
    (∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c) =
      ∑ c : Candidate n, ∑ d : Candidate n,
        M.independentPairTerm value c d := by
  exact M.independent_weight_sum_eq_pair_sum value

/--
Appendix E (pairwise swap): the (c,d)/(d,c) pair contribution factorizes into an
ordered-pair bracket.
-/
theorem paper_appendixE_independentPairTerm_add_swap
    {n : ℕ} (M : MallowsSpec n) (value : Candidate n → ℝ) (c d : Candidate n) :
    M.independentPairTerm value c d + M.independentPairTerm value d c =
      M.independentPairBracket c d * (value c - value d) := by
  exact M.independentPairTerm_add_swap value c d

/--
Appendix E (rank-factorized bracket sign): the closed-form Mallows top-fiber
formulas imply nonnegative paired independent-reranking brackets.
-/
theorem paper_appendixE_independentPairBracket_nonneg_of_rankFactorization
    {n : ℕ} (M : MallowsSpec n)
    (fac : M.RankFactorization) (hq_le_one : M.q ≤ 1)
    {c d : Candidate n} (hlt : rankOf M.center c < rankOf M.center d) :
    0 ≤ M.independentPairBracket c d := by
  exact M.independentPairBracket_nonneg_of_rankFactorization fac hq_le_one hlt

/--
Appendix E (independent-reranking finite inequality): for at least three
candidates, `0 < q < 1`, and strictly center-ordered values, the cleared
independent-reranking Mallows sum is positive.
-/
theorem paper_appendixE_independent_weight_sum_pos_of_rankFactorization
    {n : ℕ} (M : MallowsSpec n) {value : Candidate n → ℝ}
    (fac : M.RankFactorization) (hn : 0 < n) (hq_lt_one : M.q < 1)
    (hvalue : StrictlyOrderedBy M.center value) :
    0 < ∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c := by
  exact M.independent_weight_sum_pos_of_rankFactorization fac hn hq_lt_one hvalue

/--
Appendix E (independent-reranking finite inequality, finite Mallows form): the
rank factorization is constructed from the finite Kendall fibers, so the paper
inequality needs only the paper's size/noise/order assumptions.
-/
theorem paper_appendixE_independent_weight_sum_pos
    {n : ℕ} (M : MallowsSpec n) {value : Candidate n → ℝ}
    (hn : 0 < n) (hq_lt_one : M.q < 1)
    (hvalue : StrictlyOrderedBy M.center value) :
    0 < ∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c := by
  exact M.independent_weight_sum_pos_of_rankFactorization
    M.rankFactorization hn hq_lt_one hvalue

/--
Appendix E (conditional-gap factorization): after applying the Mallows top-two
rank factorization, the first-choice gap attached to a candidate is its first
rank factor times the rank-only conditional gap `x_i - V_-i`.
-/
theorem paper_appendixE_firstChoiceGapWeight_eq_rankConditionalGap
    {n : ℕ} (M : MallowsSpec n)
    (fac : M.RankFactorization) (value : Candidate n → ℝ) (c : Candidate n) :
    M.firstChoiceGapWeight value c =
      M.q ^ (rankOf M.center c : ℕ) * fac.firstSecondTail *
        candidateRankConditionalGap n M.q
          (fun r : Candidate n => value (M.center r)) (rankOf M.center c) := by
  exact M.firstChoiceGapWeight_eq_rankConditionalGap fac value c

/--
Appendix E / Lemma 4 (finite MLR comparison, cross-multiplied form).

When `q₁ < q₂` and `B` is strictly decreasing in rank, the geometric weights
`q₁^i` put more mass on better ranks than `q₂^i`, so the `B`-expectation is
strictly larger after clearing denominators.
-/
theorem paper_appendixE_candidateRankWeightedAverage_strictAnti
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {B : Candidate n → ℝ} (hB : StrictAnti B) :
    0 <
      candidateRankPowerSum n q₂ *
          (∑ i : Candidate n, q₁ ^ (i : ℕ) * B i) -
        candidateRankPowerSum n q₁ *
          (∑ i : Candidate n, q₂ ^ (i : ℕ) * B i) := by
  exact candidateRankWeightedAverage_strictAnti n hq₁_pos hq_lt hB

/--
Appendix F / Lemma 4, paper-facing cross-multiplied form.

Paper statement: if `y_i` is strictly increasing, both weight sequences sum to
one, and the likelihood ratio `p_i/q_i` is decreasing, then
`∑ i, p_i y_i < ∑ i, q_i y_i`.

Lean states the ratio monotonicity in denominator-cleared form, which is the
form used in the Mallows proof: for all `i < j`,
`p_i q_j - p_j q_i ≥ 0`, with one strict pair.
-/
theorem paper_lemma4_weighted_average_lt_of_cross_ratio
    (n : ℕ) {p q y : Candidate n → ℝ}
    (hp_sum : (∑ i : Candidate n, p i) = 1)
    (hq_sum : (∑ i : Candidate n, q i) = 1)
    (hcross_nonneg :
      ∀ i j : Candidate n, i < j → 0 ≤ p i * q j - p j * q i)
    (hcross_pos :
      ∃ i j : Candidate n, i < j ∧ 0 < p i * q j - p j * q i)
    (hy : StrictMono y) :
    (∑ i : Candidate n, p i * y i) <
      ∑ i : Candidate n, q i * y i := by
  have hanti : StrictAnti (fun i : Candidate n => -y i) := by
    intro i j hij
    exact neg_lt_neg (hy hij)
  have hmain :=
    candidateWeightedAverage_cross_pos_of_pairwise
      n (wA := p) (wH := q) (B := fun i : Candidate n => -y i)
      hcross_nonneg hcross_pos hanti
  have hpneg :
      (∑ i : Candidate n, p i * -y i) =
        -∑ i : Candidate n, p i * y i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hqneg :
      (∑ i : Candidate n, q i * -y i) =
        -∑ i : Candidate n, q i * y i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [hp_sum, hq_sum, hpneg, hqneg] at hmain
  nlinarith

/--
Appendix F / Lemma 5, Mallows top-two order-swap ratio.

Paper statement: for `x_i > x_j`,
`Pr[π₁ = x_i ∩ π₂ = x_j] = φ Pr[π₁ = x_j ∩ π₂ = x_i]`.

Lean uses the inverse Mallows parameter `q = φ⁻¹` and unnormalized top-two
weights, so the equivalent statement is that the inverted top-two weight has
one extra factor of `q`.
-/
theorem paper_lemma5_mallows_top_two_swap_ratio
    {n : ℕ} (M : MallowsSpec n) {c d : Candidate n}
    (hcd : rankOf M.center c < rankOf M.center d) :
    M.firstSecondWeight d c = M.q * M.firstSecondWeight c d := by
  rw [M.firstSecondWeight_swap_eq_q_mul_rank_mul_centerFirstSecond_of_lt hcd]
  rw [M.firstSecondWeight_eq_rank_mul_centerFirstSecond_of_lt hcd]

/--
Appendix F / Lemma 6, Mallows first-choice probability formula.

Paper statement: `Pr[π₁ = x_i] = (1 - φ⁻¹) / (φ^{i-1}(1 - φ^{-n}))`.

Lean states the same normalization in center-rank coordinates using
`q = φ⁻¹`: the probability of first choosing candidate `c` is its rank power
`q^rank(c)` divided by the geometric rank-power partition.
-/
theorem paper_lemma6_mallows_first_choice_prob_eq_rank_power
    {n : ℕ} (M : MallowsSpec n) (c : Candidate n) :
    M.firstWeight c / M.partition =
      M.q ^ (rankOf M.center c : ℕ) / candidateRankPowerSum n M.q := by
  have htail :
      M.firstWeight M.centerFirst ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one M.one_le_centerFirstWeight)
  have hsum : candidateRankPowerSum n M.q ≠ 0 :=
    ne_of_gt (candidateRankPowerSum_pos n M.q_pos)
  rw [M.firstWeight_eq_rank_mul_centerFirst c,
    M.partition_eq_rankPowerSum_mul_centerFirstWeight]
  field_simp [htail, hsum]

/--
Appendix F / Lemma 7.

Paper statement: for the Mallows model, `U_H(θ_A, θ_H) > U_HH(θ_A, θ_H)`.
In Lean's fixed-law notation, a first mover drawing from a Mallows law gets
strictly higher expected utility than an independent second mover facing another
draw from the same law.
-/
theorem paper_lemma7_mallows_first_mover_gt_second_human
    {n : ℕ} (M : MallowsSpec n) {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy M.center value) (hq_lt_one : M.q < 1) :
    expectedSecondMoverIndependent M.law M.law value <
      expectedFirstMoverUtility M.law value :=
  M.firstMoverUtility_gt_secondMoverIndependent_same_of_rankFactorization
    M.rankFactorization value hvalue hq_lt_one

/--
Appendix F.1 / Lemma 8, reduced pair-position core.

Paper statement: under the Mallows model, the probability that any two items
`i < j` are correctly ranked increases monotonically with the accuracy
parameter `φ`.

After the paper cancels the candidates outside the interval `i : j` and the
inversions among candidates inside the interval, the remaining rank-only
endpoint-position probability is `pairPositionCorrectProb`.  Lean uses the
inverse parameter `q = φ⁻¹`, so the monotonicity direction is reversed:
if `q_moreAccurate < q_lessAccurate`, then the correct-ranking probability is
larger at `q_moreAccurate`.
-/
theorem paper_lemma8_reduced_pairPositionCorrectProb_lt_of_q_lt
    (m : ℕ) {q_moreAccurate q_lessAccurate : ℝ}
    (hq_pos : 0 < q_moreAccurate)
    (hq_lt : q_moreAccurate < q_lessAccurate) :
    pairPositionCorrectProb m q_lessAccurate <
      pairPositionCorrectProb m q_moreAccurate := by
  exact pairPositionCorrectProb_strictAnti m hq_pos hq_lt

/--
Appendix F.1 / Lemma 8, conditional Mallows-probability bridge.

This is the full probability comparison once the paper's cancellation reduction
has been proved for the particular Mallows pair.  The remaining assumptions
`PairPositionReduction` assert that each actual Mallows correct/wrong pair mass
is a common positive scale times the reduced endpoint-position mass.
-/
theorem paper_lemma8_mallows_pairCorrectProb_lt_of_pairPositionReduction
    {n m : ℕ} {Mmore Mless : MallowsSpec n} {c d : Candidate n}
    (hcd_more : rankOf Mmore.center c < rankOf Mmore.center d)
    (hcd_less : rankOf Mless.center c < rankOf Mless.center d)
    (red_more : PairPositionReduction Mmore c d m)
    (red_less : PairPositionReduction Mless c d m)
    (hq_lt : Mmore.q < Mless.q) :
    Mless.pairCorrectProb c d < Mmore.pairCorrectProb c d := by
  exact pairCorrectProb_lt_of_pairPositionReduction
    hcd_more hcd_less red_more red_less hq_lt

/--
Appendix F.1 / Lemma 8, closed Mallows pairwise monotonicity.

For two Mallows laws with the same center ranking, increasing accuracy is
represented in Lean by decreasing the inverse Mallows parameter `q`.  Thus, for
any center-ordered pair `c,d`, the more accurate law has strictly larger
probability of ranking `c` before `d`.
-/
theorem paper_lemma8_mallows_pairCorrectProb_lt
    {n : ℕ} {Mmore Mless : MallowsSpec n} {c d : Candidate n}
    (hcenter : Mmore.center = Mless.center)
    (hcd_more : rankOf Mmore.center c < rankOf Mmore.center d)
    (hq_lt : Mmore.q < Mless.q) :
    Mless.pairCorrectProb c d < Mmore.pairCorrectProb c d := by
  let m : ℕ :=
    (rankOf Mmore.center d : ℕ) - (rankOf Mmore.center c : ℕ) - 1
  have hcd_less : rankOf Mless.center c < rankOf Mless.center d := by
    simpa [← hcenter] using hcd_more
  have red_more : PairPositionReduction Mmore c d m := by
    simpa [m] using Mmore.pairPositionReduction_of_center_lt hcd_more
  have red_less : PairPositionReduction Mless c d m := by
    simpa [m, ← hcenter] using
      Mless.pairPositionReduction_of_center_lt hcd_less
  exact pairCorrectProb_lt_of_pairPositionReduction
    hcd_more hcd_less red_more red_less hq_lt

/--
Section 4 / Theorem 4, Lemma-8 input in weak form.

If the human Mallows law is at least as accurate as the algorithmic law
(`q_H ≤ q_A` in Lean's inverse parameterization) and both laws share the same
center, then every center-ordered pair is weakly more likely to be correctly
ranked by the human law.  The equality case is proved by normalized finite
Mallows weights; the strict case is Lemma 8.
-/
theorem paper_theorem4_mallows_pairwise_weak_dominance_of_q_le
    {n : ℕ} {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q) :
    PairwiseWeaklyMoreAccurate human algorithm :=
  pairwiseWeaklyMoreAccurate_of_center_eq_q_le hcenter hq_le

/--
Section 4 / Theorem 4, Lemma-8 input in strict form.

When `q_H < q_A`, every center-ordered pair has strictly larger correct-ranking
probability under the human law.
-/
theorem paper_theorem4_mallows_pairwise_strict_dominance_of_q_lt
    {n : ℕ} {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_lt : human.q < algorithm.q) :
    PairwiseStrictlyMoreAccurate human algorithm :=
  pairwiseStrictlyMoreAccurate_of_center_eq_q_lt hcenter hq_lt

/--
Section 4 / Theorem 4, backward-induction core.

For a fixed-order `k`-firm sequential hiring problem, if `H` weakly dominates
`A` at every feasible history, then the all-`H` sequence is sequentially
optimal.  This is the formal backward-induction step used by the paper after it
argues that the more accurate Mallows law gives higher expected utility on each
remaining candidate set.
-/
theorem paper_theorem4_all_human_sequence_optimal_of_stepwise_dominance
    {n k : ℕ} (M : SequentialModel n)
    (hdom : M.HumanWeaklyDominatesAtAllHistories k) :
    M.IsSequentialBestResponseSequence k
      (SequentialModel.allHumanSequence k) :=
  M.allHumanSequence_isSequentialBestResponse_of_human_weaklyDominates hdom

/--
Section 4 / Theorem 4, strict uniqueness core.

If `H` strictly dominates `A` at every nonterminal feasible history, then `H` is
the unique best response at each such history.  The nonterminal guard is
necessary: if only one candidate remains, the two ranking mechanisms induce the
same hire.
-/
theorem paper_theorem4_human_unique_at_each_history_of_strict_stepwise_dominance
    {n k : ℕ} (M : SequentialModel n)
    (hdom : M.HumanStrictlyDominatesAtAllNonterminalHistories k) :
    M.HumanUniquelyOptimalAtAllNonterminalHistories k :=
  M.human_uniqueOptimal_of_human_strictlyDominates hdom

/--
Section 4 / Theorem 4, remaining-set utility bridge.

For any fixed remaining candidate set, if the more accurate Mallows law's
best-in-set fiber weights dominate the less accurate law's weights by the
center-order cross-ratio condition, then the expected value of the best
remaining candidate is weakly higher.  This reduces the open arbitrary-history
part of Theorem 4 to a precise Mallows finite-sum target.
-/
theorem paper_theorem4_remaining_utility_dominance_of_bestInSetWeight_cross
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (remaining : Finset (Candidate n)) {value : Candidate n → ℝ}
    (hvalue : WeaklyOrderedBy Mmore.center value)
    (hcross :
      ∀ c d : Candidate n, rankOf Mmore.center c < rankOf Mmore.center d →
        0 ≤
          Mmore.bestInSetWeight remaining c *
              Mless.bestInSetWeight remaining d -
            Mmore.bestInSetWeight remaining d *
              Mless.bestInSetWeight remaining c) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
  expectedBestInSet_le_of_bestInSetWeight_cross remaining hvalue hcross

/--
Section 4 / Theorem 4, identity-center best-in-set fiber MLR bridge.

It is enough to prove that, in common-center rank coordinates, the distribution
of the best remaining candidate has monotone likelihood ratios as Mallows
accuracy increases.  Lean then relabels arbitrary centers and applies the
candidatewise weighted-average bridge above.
-/
theorem paper_theorem4_remaining_utility_dominance_of_bestInSetWeight_mlr
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hmlr : ReflMallowsBestInSetWeightMLR n Mmore.q Mless.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)} (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
  expectedBestInSet_le_of_mallows_bestInSetWeightMLR
    hcenter hmlr hvalue hremaining

/--
Section 4 / Theorem 4, co-singleton remaining-set fiber bridge.

If the remaining set is all candidates except one removed candidate, the
best-in-set fiber is exactly the existing best-after-removal fiber.
-/
theorem paper_theorem4_bestInSetWeight_univ_sdiff_singleton_eq_bestAfterRemovalWeight
    {n : ℕ} (M : MallowsSpec n) (removed d : Candidate n) :
    M.bestInSetWeight (Finset.univ \ ({removed} : Finset (Candidate n))) d =
      M.bestAfterRemovalWeight removed d := by
  classical
  unfold MallowsSpec.bestInSetWeight MallowsSpec.bestAfterRemovalWeight
  refine Finset.sum_congr rfl ?_
  intro π _
  rw [bestInSet_univ_sdiff_singleton π removed]

/--
Section 4 / Theorem 4, co-singleton best-in-set fiber MLR.

The rank-only best-after-removal MLR theorem proves the best-in-set
cross-ratio inequality for histories where exactly one candidate has already
been removed.
-/
theorem paper_theorem4_bestInSetWeight_cross_univ_sdiff_singleton_of_rankFactorization
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (facMore : Mmore.RankFactorization)
    (facLess : Mless.RankFactorization)
    (hq_lt : Mmore.q < Mless.q)
    (hqLess_lt_one : Mless.q < 1)
    (removed : Candidate n) :
    ∀ c d : Candidate n, rankOf Mmore.center c < rankOf Mmore.center d →
      0 ≤
        Mmore.bestInSetWeight
            (Finset.univ \ ({removed} : Finset (Candidate n))) c *
          Mless.bestInSetWeight
            (Finset.univ \ ({removed} : Finset (Candidate n))) d -
        Mmore.bestInSetWeight
            (Finset.univ \ ({removed} : Finset (Candidate n))) d *
          Mless.bestInSetWeight
            (Finset.univ \ ({removed} : Finset (Candidate n))) c := by
  classical
  intro c d hcd
  let k : Candidate n := rankOf Mmore.center removed
  let i : Candidate n := rankOf Mmore.center c
  let j : Candidate n := rankOf Mmore.center d
  have hcore :
      0 ≤
        candidateRankBestAfterRemovalWeight n Mmore.q k i *
            candidateRankBestAfterRemovalWeight n Mless.q k j -
          candidateRankBestAfterRemovalWeight n Mmore.q k j *
            candidateRankBestAfterRemovalWeight n Mless.q k i :=
    candidateRankBestAfterRemovalWeight_pairwise_cross_nonneg
      n Mmore.q_pos hq_lt hqLess_lt_one k i j (by simpa [i, j] using hcd)
  have hscale_nonneg :
      0 ≤ facMore.firstSecondTail * facLess.firstSecondTail :=
    mul_nonneg (le_of_lt facMore.firstSecondTail_pos)
      (le_of_lt facLess.firstSecondTail_pos)
  have hremoved_less :
      rankOf Mless.center removed = k := by
    simp [k, ← hcenter]
  have hc_less :
      rankOf Mless.center c = i := by
    simp [i, ← hcenter]
  have hd_less :
      rankOf Mless.center d = j := by
    simp [j, ← hcenter]
  have hfactor :
      Mmore.bestInSetWeight
            (Finset.univ \ ({removed} : Finset (Candidate n))) c *
          Mless.bestInSetWeight
            (Finset.univ \ ({removed} : Finset (Candidate n))) d -
        Mmore.bestInSetWeight
            (Finset.univ \ ({removed} : Finset (Candidate n))) d *
          Mless.bestInSetWeight
            (Finset.univ \ ({removed} : Finset (Candidate n))) c =
        (facMore.firstSecondTail * facLess.firstSecondTail) *
          (candidateRankBestAfterRemovalWeight n Mmore.q k i *
              candidateRankBestAfterRemovalWeight n Mless.q k j -
            candidateRankBestAfterRemovalWeight n Mmore.q k j *
              candidateRankBestAfterRemovalWeight n Mless.q k i) := by
    rw [paper_theorem4_bestInSetWeight_univ_sdiff_singleton_eq_bestAfterRemovalWeight,
      paper_theorem4_bestInSetWeight_univ_sdiff_singleton_eq_bestAfterRemovalWeight,
      paper_theorem4_bestInSetWeight_univ_sdiff_singleton_eq_bestAfterRemovalWeight,
      paper_theorem4_bestInSetWeight_univ_sdiff_singleton_eq_bestAfterRemovalWeight]
    rw [Mmore.bestAfterRemovalWeight_eq_rankBestAfterRemovalWeight facMore,
      Mless.bestAfterRemovalWeight_eq_rankBestAfterRemovalWeight facLess,
      Mmore.bestAfterRemovalWeight_eq_rankBestAfterRemovalWeight facMore,
      Mless.bestAfterRemovalWeight_eq_rankBestAfterRemovalWeight facLess]
    rw [hremoved_less, hc_less, hd_less]
    simp [k, i, j]
    ring
  rw [hfactor]
  exact mul_nonneg hscale_nonneg hcore

/--
Section 4 / Theorem 4, co-singleton remaining-history dominance.

For a history that has removed exactly one candidate, the more accurate
Mallows law weakly improves expected best remaining utility.  The only extra
side condition, `algorithm.q < 1`, is the finite geometric condition used by
the existing rank-only best-after-removal MLR proof.
-/
theorem paper_theorem4_mallows_cosingleton_remaining_utility_dominance_of_q_le
    {n : ℕ} {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    (halg_q_lt_one : algorithm.q < 1)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy human.center value)
    (removed : Candidate n) :
    expectedBestInSet algorithm.law value
        (Finset.univ \ ({removed} : Finset (Candidate n))) ≤
      expectedBestInSet human.law value
        (Finset.univ \ ({removed} : Finset (Candidate n))) := by
  by_cases hq_lt : human.q < algorithm.q
  · exact
      paper_theorem4_remaining_utility_dominance_of_bestInSetWeight_cross
        (Finset.univ \ ({removed} : Finset (Candidate n)))
        hvalue
        (paper_theorem4_bestInSetWeight_cross_univ_sdiff_singleton_of_rankFactorization
          hcenter human.rankFactorization algorithm.rankFactorization
          hq_lt halg_q_lt_one removed)
  · have hq : human.q = algorithm.q :=
      le_antisymm hq_le (not_lt.mp hq_lt)
    exact
      le_of_eq
        (expectedBestInSet_eq_of_mallows_center_q_eq
          hcenter hq
          (Finset.univ \ ({removed} : Finset (Candidate n))) value).symm

/--
Section 4 / Theorem 4, prefix first-hit bridge for arbitrary remaining sets.

For non-convex histories, it is enough to prove stochastic dominance of the
identity-center prefix event: after relabeling by the common center, the
more-accurate law has at least as much unnormalised first-hit mass in every
center prefix.  The layer-cake theorem then converts those prefix inequalities
into expected best-remaining-candidate utility dominance.
-/
theorem paper_theorem4_remaining_utility_dominance_of_prefix_first_hit
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty)
    (hprefix :
      ∀ k : Fin (n + 1),
        0 ≤
          mallowsPartition Mless.q (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n Mmore.q
                (remaining.image (rankOf Mmore.center)) k -
            mallowsPartition Mmore.q (Equiv.refl (Candidate n)) *
              reflMallowsBestInSetPrefixSum n Mless.q
                (remaining.image (rankOf Mmore.center)) k) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
  expectedBestInSet_le_of_mallows_prefix
    hcenter hvalue hremaining hprefix

/--
Section 4 / Theorem 4, aggregate first-choice bracket bridge.

The arbitrary prefix first-hit route can be driven by the verified
first-choice induction: at every recursive size, it remains to prove the
aggregate off-diagonal first-choice bracket sum for prefix events.  This is
weaker than requiring every individual first-choice pair bracket to be
nonnegative.
-/
theorem paper_theorem4_remaining_utility_dominance_of_firstChoiceBracketSums
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hq_lt : Mmore.q < Mless.q)
    (hbracket :
      ∀ m : ℕ,
        ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum
          m Mmore.q Mless.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
  expectedBestInSet_le_of_mallows_firstChoiceBracketSums
    hcenter hq_lt hbracket hvalue hremaining

/--
Section 4 / Theorem 4, weighted first-choice bridge.

The aggregate bracket route further decomposes into diagonal tail dominance plus
a single weighted first-choice target with the tail law fixed at the less
accurate Mallows parameter.  Proving that weighted target at every recursive
size is enough for arbitrary remaining-set utility dominance.
-/
theorem paper_theorem4_remaining_utility_dominance_of_firstChoiceWeighted
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hq_lt : Mmore.q < Mless.q)
    (hweighted :
      ∀ m : ℕ,
        ReflMallowsBestInSetPrefixCutFirstChoiceWeighted
          m Mmore.q Mless.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
  expectedBestInSet_le_of_mallows_firstChoiceWeighted
    hcenter hq_lt hweighted hvalue hremaining

/--
Section 4 / Theorem 4, adjacent-boundary weighted first-choice bridge.

This is the current narrowest cancellation interface for the arbitrary
nonconvex remaining-set lift: adjacent outside/outside first-choice gaps are
erased, leaving only boundary terms in the first-choice weighted target.
-/
theorem paper_theorem4_remaining_utility_dominance_of_firstChoiceAdjacentBoundary
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hq_lt : Mmore.q < Mless.q)
    (hboundary :
      ∀ m : ℕ,
        ReflMallowsBestInSetPrefixCutFirstChoiceAdjacentBoundary
          m Mmore.q Mless.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
  expectedBestInSet_le_of_mallows_firstChoiceWeighted
    hcenter hq_lt
    (fun m =>
      ReflMallowsBestInSetPrefixCutFirstChoiceWeighted.of_adjacentBoundary
        (hboundary m))
    hvalue hremaining

/--
Section 4 / Theorem 4, prefix-specific Kendall-rank-layer bridge.

It is enough to prove Kendall-layer average antitonicity only for the prefix
first-hit events used by the layer-cake remaining-set proof.  This is narrower
than the generic adjacent-swap payoff route and avoids asking for a rank-layer
theorem over all weak-Bruhat monotone payoffs.
-/
theorem paper_theorem4_remaining_utility_dominance_of_prefix_kendall_layer_average
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hq_lt : Mmore.q < Mless.q)
    (hlayers : ReflKendallPrefixLayerAverageAnti n)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining := by
  refine
    expectedBestInSet_le_of_mallows_prefix
      hcenter hvalue hremaining ?_
  intro k
  exact
    reflMallowsBestInSetPrefixSum_cross_of_kendallPrefixLayerAverageAnti
      Mmore.q_pos hq_lt hlayers (Finset.image_nonempty.mpr hremaining) k

/--
Section 4 / Theorem 4, adjacent prefix Kendall-rank-layer bridge.

It is enough to prove the prefix-event layer-average inequality for consecutive
identity-center Kendall layers.  Lean chains consecutive layers into the
all-pairs prefix-layer premise used by the layer-cake proof.
-/
theorem paper_theorem4_remaining_utility_dominance_of_adjacent_prefix_kendall_layer_average
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hq_lt : Mmore.q < Mless.q)
    (hlayers : ReflKendallAdjacentPrefixLayerAverageAnti n)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
  paper_theorem4_remaining_utility_dominance_of_prefix_kendall_layer_average
    hcenter hq_lt
    (reflKendallPrefixLayerAverageAnti_of_adjacent hlayers)
    hvalue hremaining

/--
Section 4 / Theorem 4, adjacent-swap stochastic-dominance bridge.

The prefix first-hit premise above follows from a generic identity-center
Mallows theorem saying that every payoff improved by adjacent inversion
corrections has higher expectation under the more accurate Mallows law.  The
prefix indicator satisfies that pointwise adjacent-swap property unconditionally.
-/
theorem paper_theorem4_remaining_utility_dominance_of_adjacent_stochastic_dominance
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hadj : ReflMallowsAdjacentStochasticDominance n Mmore.q Mless.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
  expectedBestInSet_le_of_mallows_adjacentStochasticDominance
    hcenter hadj hvalue hremaining

/--
Section 4 / Theorem 4, monotone-coupling bridge.

An explicit coupling of the less-accurate and more-accurate identity-center
Mallows laws, supported on weak-Bruhat corrections, is sufficient for the
same remaining-set utility dominance.  This is a certificate-shaped route to
the open arbitrary-size Mallows dominance input.
-/
theorem paper_theorem4_remaining_utility_dominance_of_weakBruhat_coupling
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (C :
      ReflMallowsWeakBruhatCoupling n Mmore.q Mless.q
        Mmore.q_pos Mless.q_pos)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
  paper_theorem4_remaining_utility_dominance_of_adjacent_stochastic_dominance
    hcenter
    (reflMallowsAdjacentStochasticDominance_of_weakBruhatCoupling C)
    hvalue hremaining

/--
Section 4 / Theorem 4, Kendall-rank-layer bridge.

The arbitrary-size adjacent-swap stochastic-dominance input also follows from a
rank-layer average theorem: every payoff improved by adjacent inversion
corrections has weakly decreasing average across identity-center Kendall
layers.  The layer statement is division-free in Lean, so empty layers do not
create side conditions.
-/
theorem paper_theorem4_remaining_utility_dominance_of_kendall_layer_average
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hq_lt : Mmore.q < Mless.q)
    (hlayers : ReflKendallLayerAverageAnti n)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
  paper_theorem4_remaining_utility_dominance_of_adjacent_stochastic_dominance
    hcenter
    (reflMallowsAdjacentStochasticDominance_of_kendallLayerAverageAnti
      Mmore.q_pos hq_lt hlayers)
    hvalue hremaining

/--
Section 4 / Theorem 4, adjacent Kendall-rank-layer bridge.

It is enough to prove the Kendall-layer average theorem only for consecutive
identity-center Kendall layers.  Lean chains those adjacent inequalities across
all intermediate nonempty layers, then applies the rank-layer Mallows sum
bridge above.
-/
theorem paper_theorem4_remaining_utility_dominance_of_adjacent_kendall_layer_average
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hq_lt : Mmore.q < Mless.q)
    (hlayers : ReflKendallAdjacentLayerAverageAnti n)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet Mless.law value remaining ≤
      expectedBestInSet Mmore.law value remaining :=
  paper_theorem4_remaining_utility_dominance_of_adjacent_stochastic_dominance
    hcenter
    (reflMallowsAdjacentStochasticDominance_of_adjacent_kendallLayerAverageAnti
      Mmore.q_pos hq_lt hlayers)
    hvalue hremaining

/--
Section 4 / Theorem 4, closed three-candidate Mallows universe.

For exactly three candidates, the adjacent-swap stochastic-dominance bridge is
proved by enumerating the weak-order rank layers `1,2,2,1`; hence arbitrary
nonempty remaining sets are covered in that universe.
-/
theorem paper_theorem4_mallows_three_candidate_remaining_utility_dominance_of_q_le
    {human algorithm : MallowsSpec 1}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    {value : Candidate 1 → ℝ} (hvalue : WeaklyOrderedBy human.center value)
    {remaining : Finset (Candidate 1)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet algorithm.law value remaining ≤
      expectedBestInSet human.law value remaining := by
  by_cases hq_lt : human.q < algorithm.q
  · exact
      paper_theorem4_remaining_utility_dominance_of_adjacent_stochastic_dominance
        hcenter
        (reflMallowsAdjacentStochasticDominance_one human.q_pos hq_lt)
        hvalue hremaining
  · have hq : human.q = algorithm.q :=
      le_antisymm hq_le (not_lt.mp hq_lt)
    exact
      le_of_eq
        (expectedBestInSet_eq_of_mallows_center_q_eq
          hcenter hq remaining value).symm

/--
Section 4 / Theorem 4, closed three-candidate Mallows universe via the
best-in-set fiber MLR route.

This is the same three-candidate remaining-set dominance endpoint as
`paper_theorem4_mallows_three_candidate_remaining_utility_dominance_of_q_le`,
but it uses the narrower best-in-set fiber MLR bridge rather than the broader
adjacent stochastic-dominance interface.
-/
theorem
    paper_theorem4_mallows_three_candidate_remaining_utility_dominance_of_bestInSetWeight_mlr
    {human algorithm : MallowsSpec 1}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    {value : Candidate 1 → ℝ} (hvalue : WeaklyOrderedBy human.center value)
    {remaining : Finset (Candidate 1)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet algorithm.law value remaining ≤
      expectedBestInSet human.law value remaining := by
  by_cases hq_lt : human.q < algorithm.q
  · exact
      paper_theorem4_remaining_utility_dominance_of_bestInSetWeight_mlr
        hcenter
        (reflMallowsBestInSetWeightMLR_one human.q_pos hq_lt)
        hvalue hremaining
  · have hq : human.q = algorithm.q :=
      le_antisymm hq_le (not_lt.mp hq_lt)
    exact
      le_of_eq
        (expectedBestInSet_eq_of_mallows_center_q_eq
          hcenter hq remaining value).symm

/--
Section 4 / Theorem 4, closed four-candidate identity-center fiber MLR.

For four candidates, nonempty remaining sets have cardinality one through four:
`card ≤ 2` is the pairwise Lemma-8 route, `card = 3` is co-singleton and uses
best-after-removal MLR, and `card = 4` is the full-set first-choice route.
-/
theorem paper_theorem4_reflMallowsBestInSetWeightMLR_two_of_qLess_lt_one
    {qMore qLess : ℝ} (hqMore_pos : 0 < qMore)
    (hq_lt : qMore < qLess) (hqLess_lt_one : qLess < 1) :
    ReflMallowsBestInSetWeightMLR 2 qMore qLess := by
  classical
  intro remaining hremaining c d hc hd hcd
  by_cases hsmall : remaining.card ≤ 2
  · exact
      reflMallowsBestInSetWeight_cross_nonneg_card_le_two
        2 hqMore_pos hq_lt hremaining hsmall hc hd hcd
  have hcard_pos : 0 < remaining.card := Finset.card_pos.mpr hremaining
  have hcard_le_four : remaining.card ≤ 4 := by
    have h := Finset.card_le_univ remaining
    simpa [Candidate] using h
  have hcard_cases : remaining.card = 3 ∨ remaining.card = 4 := by
    omega
  rcases hcard_cases with hcard_three | hcard_four
  · have hcomp_card :
        (Finset.univ \ remaining : Finset (Candidate 2)).card = 1 := by
      have hsubset : remaining ⊆ (Finset.univ : Finset (Candidate 2)) := by
        intro x _
        exact Finset.mem_univ x
      have hcard :=
        Finset.card_sdiff_of_subset hsubset
          (s := remaining) (t := (Finset.univ : Finset (Candidate 2)))
      simpa [Candidate, hcard_three] using hcard
    rcases Finset.card_eq_one.mp hcomp_card with ⟨removed, hcomp_eq⟩
    have hremaining_eq :
        remaining = Finset.univ \ ({removed} : Finset (Candidate 2)) := by
      ext x
      have hnot_iff : x ∉ remaining ↔ x = removed := by
        have hmem :=
          congrArg (fun s : Finset (Candidate 2) => x ∈ s) hcomp_eq
        simpa using hmem
      constructor
      · intro hx
        have hx_ne : x ≠ removed := by
          intro hx_eq
          exact (hnot_iff.mpr hx_eq) hx
        simp [hx_ne]
      · intro hx
        have hx_ne : x ≠ removed := by
          simpa using hx
        by_contra hx_not
        exact hx_ne (hnot_iff.mp hx_not)
    subst remaining
    let Mmore : MallowsSpec 2 :=
      MallowsSpec.ofQ (Equiv.refl (Candidate 2)) qMore hqMore_pos
    have hqLess_pos : 0 < qLess := lt_trans hqMore_pos hq_lt
    let Mless : MallowsSpec 2 :=
      MallowsSpec.ofQ (Equiv.refl (Candidate 2)) qLess hqLess_pos
    have hcd_more : rankOf Mmore.center c < rankOf Mmore.center d := by
      simpa [Mmore, MallowsSpec.ofQ, rankOf] using hcd
    have hcross :
        0 ≤
          Mmore.bestInSetWeight
              (Finset.univ \ ({removed} : Finset (Candidate 2))) c *
            Mless.bestInSetWeight
              (Finset.univ \ ({removed} : Finset (Candidate 2))) d -
          Mmore.bestInSetWeight
              (Finset.univ \ ({removed} : Finset (Candidate 2))) d *
            Mless.bestInSetWeight
              (Finset.univ \ ({removed} : Finset (Candidate 2))) c :=
      paper_theorem4_bestInSetWeight_cross_univ_sdiff_singleton_of_rankFactorization
        (Mmore := Mmore) (Mless := Mless) rfl
        Mmore.rankFactorization Mless.rankFactorization
        hq_lt hqLess_lt_one removed c d hcd_more
    rw [MallowsSpec.bestInSetWeight_ofQ_refl
          (n := 2) qMore hqMore_pos
          (Finset.univ \ ({removed} : Finset (Candidate 2))) c,
        MallowsSpec.bestInSetWeight_ofQ_refl
          (n := 2) qLess hqLess_pos
          (Finset.univ \ ({removed} : Finset (Candidate 2))) d,
        MallowsSpec.bestInSetWeight_ofQ_refl
          (n := 2) qMore hqMore_pos
          (Finset.univ \ ({removed} : Finset (Candidate 2))) d,
        MallowsSpec.bestInSetWeight_ofQ_refl
          (n := 2) qLess hqLess_pos
          (Finset.univ \ ({removed} : Finset (Candidate 2))) c] at hcross
    exact hcross
  · have hcard_univ :
        remaining.card = Fintype.card (Candidate 2) := by
      simpa [Candidate] using hcard_four
    have hremaining_univ : remaining = Finset.univ :=
      remaining.eq_univ_of_card hcard_univ
    subst remaining
    exact
      reflMallowsBestInSetWeight_univ_cross_nonneg
        2 hqMore_pos hq_lt hcd

/--
Section 4 / Theorem 4, closed four-candidate remaining-history classification.

With four candidates, every nonempty remaining set is either of size at most
two, the full center-convex set, or the complement of a singleton.  Combining
the small-set, center-convex, and co-singleton routes therefore closes every
remaining history in the four-candidate universe, subject to the same
`algorithm.q < 1` side condition used by the co-singleton rank theorem.
-/
theorem paper_theorem4_mallows_four_candidate_remaining_utility_dominance_of_q_le
    {human algorithm : MallowsSpec 2}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    (halg_q_lt_one : algorithm.q < 1)
    {value : Candidate 2 → ℝ} (hvalue : WeaklyOrderedBy human.center value)
    {remaining : Finset (Candidate 2)}
    (hremaining : remaining.Nonempty) :
    expectedBestInSet algorithm.law value remaining ≤
      expectedBestInSet human.law value remaining := by
  classical
  by_cases hsmall : remaining.card ≤ 2
  · exact
      expectedBestInSet_le_of_pairwiseWeaklyMoreAccurate_card_le_two
        hcenter
        (paper_theorem4_mallows_pairwise_weak_dominance_of_q_le
          hcenter hq_le)
        hvalue hremaining hsmall
  have hcard_pos : 0 < remaining.card := Finset.card_pos.mpr hremaining
  have hcard_le_four : remaining.card ≤ 4 := by
    have h := Finset.card_le_univ remaining
    simpa [Candidate] using h
  have hcard_cases : remaining.card = 3 ∨ remaining.card = 4 := by
    omega
  rcases hcard_cases with hcard_three | hcard_four
  · have hcomp_card :
        (Finset.univ \ remaining : Finset (Candidate 2)).card = 1 := by
      have hsubset : remaining ⊆ (Finset.univ : Finset (Candidate 2)) := by
        intro c _
        exact Finset.mem_univ c
      have hcard :=
        Finset.card_sdiff_of_subset hsubset
          (s := remaining) (t := (Finset.univ : Finset (Candidate 2)))
      simpa [Candidate, hcard_three] using hcard
    rcases Finset.card_eq_one.mp hcomp_card with ⟨removed, hcomp_eq⟩
    have hremaining_eq :
        remaining = Finset.univ \ ({removed} : Finset (Candidate 2)) := by
      ext c
      have hnot_iff : c ∉ remaining ↔ c = removed := by
        have hmem :=
          congrArg (fun s : Finset (Candidate 2) => c ∈ s) hcomp_eq
        simpa using hmem
      constructor
      · intro hc
        have hc_ne : c ≠ removed := by
          intro hc_eq
          exact (hnot_iff.mpr hc_eq) hc
        simp [hc_ne]
      · intro hc
        have hc_ne : c ≠ removed := by
          simpa using hc
        by_contra hc_not
        exact hc_ne (hnot_iff.mp hc_not)
    subst remaining
    exact
      paper_theorem4_mallows_cosingleton_remaining_utility_dominance_of_q_le
        hcenter hq_le halg_q_lt_one hvalue removed
  · have hcard_univ :
        remaining.card = Fintype.card (Candidate 2) := by
      simpa [Candidate] using hcard_four
    have hremaining_univ : remaining = Finset.univ :=
      remaining.eq_univ_of_card hcard_univ
    subst remaining
    have himage_univ :
        ((Finset.univ : Finset (Candidate 2)).image (rankOf human.center)) =
          Finset.univ := by
      ext r
      constructor
      · intro _
        exact Finset.mem_univ r
      · intro _
        refine Finset.mem_image.mpr ?_
        exact ⟨human.center r, Finset.mem_univ _, by simp [rankOf]⟩
    have hconv :
        CenterConvex
          (((Finset.univ : Finset (Candidate 2)).image
            (rankOf human.center))) := by
      rw [himage_univ]
      intro a b c _ _ _ _
      exact Finset.mem_univ b
    exact
      expectedBestInSet_le_of_mallows_centerConvex_q_le
        hcenter hq_le hvalue (by simp) hconv

/--
Section 4 / Theorem 4, all-history weak dominance from a remaining-set utility
dominance theorem.

This is the sequential plumbing that turns the remaining-candidate-set
comparison into the paper's "each firm chooses H" history-by-history statement.
-/
theorem paper_theorem4_human_weakly_dominates_all_histories_of_remaining_utility_dominance
    {n k : ℕ} {algorithm human : MallowsSpec n} (value : Candidate n → ℝ)
    (hdom :
      ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet algorithm.law value remaining ≤
          expectedBestInSet human.law value remaining) :
    (SequentialModel.ofMallows algorithm human value).HumanWeaklyDominatesAtAllHistories k :=
  SequentialModel.humanWeaklyDominatesAtAllHistories_of_remaining_dominance
    (M := SequentialModel.ofMallows algorithm human value) hdom

/--
Section 4 / Theorem 4, all-human weak optimality from the adjacent-swap Mallows
dominance interface.

The only mathematical input not discharged here is the generic arbitrary-size
identity-center adjacent stochastic-dominance theorem; the three-candidate
wrapper below supplies it from the closed finite proof.
-/
theorem paper_theorem4_mallows_all_human_sequence_optimal_of_adjacent_stochastic_dominance
    {n k : ℕ} {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    (hadj_lt :
      human.q < algorithm.q →
        ReflMallowsAdjacentStochasticDominance n human.q algorithm.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy human.center value) :
    (SequentialModel.ofMallows algorithm human value).IsSequentialBestResponseSequence k
      (SequentialModel.allHumanSequence k) := by
  refine
    paper_theorem4_all_human_sequence_optimal_of_stepwise_dominance
      (SequentialModel.ofMallows algorithm human value) ?_
  refine
    paper_theorem4_human_weakly_dominates_all_histories_of_remaining_utility_dominance
      value ?_
  intro remaining hremaining
  by_cases hq_lt : human.q < algorithm.q
  · exact
      paper_theorem4_remaining_utility_dominance_of_adjacent_stochastic_dominance
        hcenter (hadj_lt hq_lt) hvalue hremaining
  · have hq : human.q = algorithm.q :=
      le_antisymm hq_le (not_lt.mp hq_lt)
    exact
      le_of_eq
        (expectedBestInSet_eq_of_mallows_center_q_eq
          hcenter hq remaining value).symm

/--
Section 4 / Theorem 4, closed three-candidate all-human weak optimality.

For the three-candidate Mallows universe, the adjacent stochastic-dominance
input is fully formalized by `reflMallowsAdjacentStochasticDominance_one`, so
all feasible histories are covered.
-/
theorem paper_theorem4_mallows_three_candidate_all_human_sequence_optimal_of_q_le
    {k : ℕ} {human algorithm : MallowsSpec 1}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    {value : Candidate 1 → ℝ} (hvalue : WeaklyOrderedBy human.center value) :
    (SequentialModel.ofMallows algorithm human value).IsSequentialBestResponseSequence k
      (SequentialModel.allHumanSequence k) :=
  paper_theorem4_mallows_all_human_sequence_optimal_of_adjacent_stochastic_dominance
    hcenter hq_le
    (fun hq_lt => reflMallowsAdjacentStochasticDominance_one human.q_pos hq_lt)
    hvalue

/--
Section 4 / Theorem 4, closed four-candidate all-human weak optimality.

This uses the finite remaining-set classification above instead of assuming the
arbitrary-size adjacent-dominance input.
-/
theorem paper_theorem4_mallows_four_candidate_all_human_sequence_optimal_of_q_le
    {k : ℕ} {human algorithm : MallowsSpec 2}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    (halg_q_lt_one : algorithm.q < 1)
    {value : Candidate 2 → ℝ} (hvalue : WeaklyOrderedBy human.center value) :
    (SequentialModel.ofMallows algorithm human value).IsSequentialBestResponseSequence k
      (SequentialModel.allHumanSequence k) := by
  refine
    paper_theorem4_all_human_sequence_optimal_of_stepwise_dominance
      (SequentialModel.ofMallows algorithm human value) ?_
  refine
    paper_theorem4_human_weakly_dominates_all_histories_of_remaining_utility_dominance
      value ?_
  intro remaining hremaining
  exact
    paper_theorem4_mallows_four_candidate_remaining_utility_dominance_of_q_le
      hcenter hq_le halg_q_lt_one hvalue hremaining

/--
Section 4 / Theorem 4, closed two-candidate remaining-history case.

When exactly two candidates remain, the next-hire expected utility is an affine
function of the probability of correctly ordering that pair.  Thus Lemma 8's
pairwise dominance is already enough to close these nonterminal histories.
-/
theorem paper_theorem4_two_remaining_utility_dominance_of_pairwise
    {n : ℕ} {Mmore Mless : MallowsSpec n}
    (hcenter : Mmore.center = Mless.center)
    (hpair : PairwiseWeaklyMoreAccurate Mmore Mless)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy Mmore.center value)
    {c d : Candidate n}
    (hcd : rankOf Mmore.center c < rankOf Mmore.center d) :
    expectedBestInSet Mless.law value ({c, d} : Finset (Candidate n)) ≤
      expectedBestInSet Mmore.law value ({c, d} : Finset (Candidate n)) :=
  expectedBestInSet_pair_le_of_pairwiseWeaklyMoreAccurate
    hcenter hpair hvalue hcd

/--
Section 4 / Theorem 4, two-candidate remaining-history Mallows parameter form.
-/
theorem paper_theorem4_mallows_two_remaining_utility_dominance_of_q_le
    {n : ℕ} {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy human.center value)
    {c d : Candidate n}
    (hcd : rankOf human.center c < rankOf human.center d) :
    expectedBestInSet algorithm.law value ({c, d} : Finset (Candidate n)) ≤
      expectedBestInSet human.law value ({c, d} : Finset (Candidate n)) :=
  paper_theorem4_two_remaining_utility_dominance_of_pairwise
    hcenter
    (paper_theorem4_mallows_pairwise_weak_dominance_of_q_le
      hcenter hq_le)
    hvalue hcd

/--
Section 4 / Theorem 4, strict two-candidate remaining-history Mallows
parameter form.
-/
theorem paper_theorem4_mallows_two_remaining_strict_utility_dominance_of_q_lt
    {n : ℕ} {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_lt : human.q < algorithm.q)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy human.center value)
    {c d : Candidate n}
    (hcd : rankOf human.center c < rankOf human.center d) :
    expectedBestInSet algorithm.law value ({c, d} : Finset (Candidate n)) <
      expectedBestInSet human.law value ({c, d} : Finset (Candidate n)) :=
  expectedBestInSet_pair_lt_of_pairwiseStrictlyMoreAccurate
    hcenter
    (paper_theorem4_mallows_pairwise_strict_dominance_of_q_lt
      hcenter hq_lt)
    hvalue hcd

/--
Section 4 / Theorem 4, all histories with at most two candidates remaining.
-/
theorem paper_theorem4_mallows_small_remaining_utility_dominance_of_q_le
    {n : ℕ} {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy human.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty) (hcard : remaining.card ≤ 2) :
    expectedBestInSet algorithm.law value remaining ≤
      expectedBestInSet human.law value remaining :=
  expectedBestInSet_le_of_pairwiseWeaklyMoreAccurate_card_le_two
    hcenter
    (paper_theorem4_mallows_pairwise_weak_dominance_of_q_le
      hcenter hq_le)
    hvalue hremaining hcard

/--
Section 4 / Theorem 4, center-convex remaining histories.

This closes histories whose remaining candidates form an interval in the common
center order.  The convexity premise is stated after relabeling candidates by
the human/common center ranking.
-/
theorem paper_theorem4_mallows_centerConvex_remaining_utility_dominance_of_q_le
    {n : ℕ} {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy human.center value)
    {remaining : Finset (Candidate n)}
    (hremaining : remaining.Nonempty)
    (hconv : CenterConvex (remaining.image (rankOf human.center))) :
    expectedBestInSet algorithm.law value remaining ≤
      expectedBestInSet human.law value remaining :=
  expectedBestInSet_le_of_mallows_centerConvex_q_le
    hcenter hq_le hvalue hremaining hconv

/--
Section 4 / Theorem 4, Mallows weak form with the remaining-set utility
dominance made explicit.

The preceding two pairwise declarations are the Lemma-8 input.  To conclude the
sequential best-response statement, Lean records the exact remaining-set
utility dominance needed at every history: the expected value of the best
available candidate under `A` is no larger than under `H`.
-/
theorem paper_theorem4_mallows_all_human_sequence_optimal_of_remaining_utility_dominance
    {n k : ℕ} {algorithm human : MallowsSpec n} (value : Candidate n → ℝ)
    (hdom :
      (SequentialModel.ofMallows algorithm human value).HumanWeaklyDominatesAtAllHistories k) :
    (SequentialModel.ofMallows algorithm human value).IsSequentialBestResponseSequence k
      (SequentialModel.allHumanSequence k) :=
  paper_theorem4_all_human_sequence_optimal_of_stepwise_dominance
    (SequentialModel.ofMallows algorithm human value) hdom

/--
Section 4 / Theorem 4, Mallows strict form with the remaining-set utility
dominance made explicit.

This is the unique-optimality half of Theorem 4 at the sequential-choice layer.
The strict dominance premise should be discharged by a Mallows
remaining-candidate-set dominance theorem; pairwise Lemma 8 is exposed above as
the paper's stated input.
-/
theorem paper_theorem4_mallows_human_unique_at_each_history_of_remaining_utility_dominance
    {n k : ℕ} {algorithm human : MallowsSpec n} (value : Candidate n → ℝ)
    (hdom :
      SequentialModel.HumanStrictlyDominatesAtAllNonterminalHistories
        (SequentialModel.ofMallows algorithm human value) k) :
    SequentialModel.HumanUniquelyOptimalAtAllNonterminalHistories
      (SequentialModel.ofMallows algorithm human value) k :=
  paper_theorem4_human_unique_at_each_history_of_strict_stepwise_dominance
    (SequentialModel.ofMallows algorithm human value) hdom

/--
Appendix E (weaker-competition finite inequality): rank factorization plus
`qA < qH` proves the cleared weaker-competition Mallows sum.
-/
theorem paper_appendixE_cross_weight_sum_pos_of_rankFactorization
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy C.human.center value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q)
    (hhuman_q_lt_one : C.human.q < 1) :
    0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c := by
  exact C.cross_weight_sum_pos_of_rankFactorization
    hvalue halg_rank hhuman_rank hq_lt hhuman_q_lt_one

/--
Appendix E (weaker-competition finite inequality, finite Mallows form): the
algorithm and human rank factorizations are constructed from their finite
Kendall fibers.
-/
theorem paper_appendixE_cross_weight_sum_pos
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy C.human.center value)
    (hq_lt : C.algorithm.q < C.human.q)
    (hhuman_q_lt_one : C.human.q < 1) :
    0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c := by
  exact C.cross_weight_sum_pos_of_rankFactorization
    hvalue C.algorithm.rankFactorization C.human.rankFactorization
    hq_lt hhuman_q_lt_one

/--
Theorem 3 / weaker-competition center comparison: when the algorithm Mallows law
has strictly lower inverse-noise parameter than the human law, the rank
factorization formulas imply the strict center first-choice cross-product
comparison used by the paper.
-/
theorem paper_theorem3_centerFirstWeight_cross_lt_of_rankFactorization
    {n : ℕ} (C : MallowsComparison n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
      C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition := by
  exact C.centerFirstWeight_cross_lt_of_rankFactorization
    halg_rank hhuman_rank hq_lt

/--
Theorem 3 / center first-choice probability comparison: under rank
factorization and `qA < qH`, the algorithm law gives the center top candidate
strictly larger first-choice probability than the human law.
-/
theorem paper_theorem3_centerFirstProb_lt_of_rankFactorization
    {n : ℕ} (C : MallowsComparison n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    firstChoiceProb C.human.law C.human.centerFirst <
      firstChoiceProb C.algorithm.law C.human.centerFirst := by
  exact C.centerFirstProb_lt_of_rankFactorization
    halg_rank hhuman_rank hq_lt

/--
Theorem 3 / first-choice prefix dominance: for every proper center-rank prefix,
rank factorization and `qA < qH` imply the algorithm law has strictly more
cross-multiplied first-choice mass on that prefix.
-/
theorem paper_theorem3_firstWeightPrefix_cross_lt_of_rankFactorization
    {n : ℕ} (C : MallowsComparison n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q)
    (k : Fin (n + 1)) :
    C.human.firstWeightPrefix k * C.algorithm.partition <
      C.algorithm.firstWeightPrefix k * C.human.partition := by
  exact C.firstWeightPrefix_cross_lt_of_rankFactorization
    halg_rank hhuman_rank hq_lt k

/--
Theorem 3 / weaker-competition center term: under strict center ordering and
`qA < qH`, rank factorization makes the center candidate's weaker-competition
product strictly positive.
-/
theorem paper_theorem3_weaker_center_cross_product_pos_of_rankFactorization
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    0 < (C.algorithm.firstWeight C.human.centerFirst * C.human.partition -
        C.human.firstWeight C.human.centerFirst * C.algorithm.partition) *
      firstChoiceGapMass C.human.law value C.human.centerFirst := by
  exact C.weaker_center_cross_product_pos_of_rankFactorization
    hstrict halg_rank hhuman_rank hq_lt

/--
Theorem 3 / weaker-competition center summand, denominator-cleared form: under
strict center ordering and `qA < qH`, the center candidate's cleared
weaker-competition summand is strictly positive.
-/
theorem paper_theorem3_weaker_center_cross_weight_summand_pos_of_rankFactorization
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    0 < (C.algorithm.firstWeight C.human.centerFirst * C.human.partition -
        C.human.firstWeight C.human.centerFirst * C.algorithm.partition) *
      C.human.firstChoiceGapWeight value C.human.centerFirst := by
  exact C.weaker_center_cross_weight_summand_pos_of_rankFactorization
    hstrict halg_rank hhuman_rank hq_lt

/--
Theorem 3 (finite-sum Mallows form): from the cleared finite Mallows certificate,
paper hypotheses follow for the induced pointwise model.

Paper assumptions in this entry are explicit as finite Mallows sum inequalities:
1. strict center ordering of the value profile;
2. positive cleared finite Mallows sum for the algorithm;
3. positive cleared finite Mallows sum for the human law;
4. positive cleared cross-weight sum that encodes the weaker-competition term.
-/
theorem paper_theorem3_pointwise_finite_mallows_sum
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (halg : 0 < ∑ c : Candidate n,
      (C.algorithm.partition - C.algorithm.firstWeight c) *
        C.algorithm.firstChoiceGapWeight value c)
    (hhuman : 0 < ∑ c : Candidate n,
      (C.human.partition - C.human.firstWeight c) *
        C.human.firstChoiceGapWeight value c)
    (hweaker : 0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.theorem3_pointwise_of_centerMallowsFiniteSumCertificate
    ⟨hstrict, halg, hhuman, hweaker⟩

/--
Backward-compatible wrapper for callers that already prepared the certificate
structure directly.
-/
theorem paper_theorem3_pointwise_finite_mallows_sum_of_certificate
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (cert : C.CenterMallowsFiniteSumCertificate value) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.theorem3_pointwise_of_centerMallowsFiniteSumCertificate cert

/--
Theorem 3 (rank-factorized independent sums, backward-compatible form): the two
independent-reranking finite inequalities are proved from the Mallows
rank-factorization formulas. The cleared weaker-competition Mallows sum is kept
as an explicit premise for callers that already have it.
-/
theorem paper_theorem3_pointwise_rankFactorization_and_crossWeight
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hn : 0 < n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hweaker : 0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.theorem3_pointwise_of_rankFactorization_and_crossWeight
    hstrict hn halg_rank hhuman_rank halg_q_lt_one hhuman_q_lt_one hweaker

/--
Paper Theorem 3 (Mallows model).

Paper statement: for the Mallows family with common center, if the algorithmic
ranking is more accurate than the human ranking, then for every strictly
center-ordered candidate value profile the induced model satisfies the paper's
independent-reranking and weaker-competition hypotheses.

Lean statement uses the inverse Mallows parameter `q`, so "algorithm more
accurate" is `C.algorithm.q < C.human.q`. The finite Mallows top-one/top-two
fiber formulas used in Appendix E are constructed in Lean by
`MallowsSpec.rankFactorization`, so they are no longer assumptions here.
-/
theorem paper_theorem3_pointwise_rankFactorization
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hn : 0 < n)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hq_lt : C.algorithm.q < C.human.q) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.theorem3_pointwise_of_rankFactorization
    hstrict hn C.algorithm.rankFactorization C.human.rankFactorization
    halg_q_lt_one hhuman_q_lt_one hq_lt

/--
Theorem 3 (reduced product-sign form): from reduced product-sign finite Mallows
certificates, paper hypotheses follow.

Paper assumptions in this entry are explicit as finite non-center sign inequalities:
the algorithm and human non-center summands are nonnegative, non-center cross
product terms are nonnegative, and the center first-choice weights improve
strictly.
-/
theorem paper_theorem3_pointwise_reduced_product_certificate
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (halg_noncenter_nonneg :
      ∀ c : Candidate n, c ≠ C.algorithm.centerFirst →
        0 ≤ firstChoiceMissProb C.algorithm.law c *
          firstChoiceGapMass C.algorithm.law value c)
    (hhum_noncenter_nonneg :
      ∀ c : Candidate n, c ≠ C.human.centerFirst →
        0 ≤ firstChoiceMissProb C.human.law c *
          firstChoiceGapMass C.human.law value c)
    (hweaker_noncenter_cross_product_nonneg :
      ∀ c : Candidate n, c ≠ C.human.centerFirst →
        0 ≤ (C.algorithm.firstWeight c * C.human.partition -
              C.human.firstWeight c * C.algorithm.partition) *
          firstChoiceGapMass C.human.law value c)
    (hcenter : C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
      C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.theorem3_pointwise_of_centerMallowsReducedProductCrossWeightCertificate
    ⟨hstrict, halg_noncenter_nonneg, hhum_noncenter_nonneg,
      hweaker_noncenter_cross_product_nonneg, hcenter⟩

/--
Backward-compatible wrapper for callers that already prepared the reduced
product-sign certificate structure directly.
-/
theorem paper_theorem3_pointwise_reduced_product_certificate_of_certificate
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (cert : C.CenterMallowsReducedProductCrossWeightCertificate value) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.theorem3_pointwise_of_centerMallowsReducedProductCrossWeightCertificate cert

/--
Normalization bridge: strict-center finite-sum certificates are equivalent to
normalized candidate sums under strict center ordering.
-/
theorem paper_theorem3_finite_sum_certificate_from_candidate_sums
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (cert : C.CandidateSumCertificate value) :
    C.CenterMallowsFiniteSumCertificate value := by
  exact C.centerMallowsFiniteSumCertificate_of_candidateSumCertificate hstrict cert

/--
Definition 1 / first-mover monotonicity for Mallows.

Paper statement: when the algorithmic ranking law is more accurate than the
human ranking law, the first mover's expected value is strictly higher under the
algorithmic law.

Lean uses the inverse Mallows parameter `q`, so greater accuracy is
`C.algorithm.q < C.human.q`.
-/
theorem paper_definition1_firstMoverUtility_strict_of_rankFactorization
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hq_lt : C.algorithm.q < C.human.q) :
    expectedFirstMoverUtility C.human.law value <
      expectedFirstMoverUtility C.algorithm.law value := by
  exact C.firstMoverUtility_strict_of_rankFactorization
    hstrict C.algorithm.rankFactorization C.human.rankFactorization hq_lt

/--
Definition 1 / singleton-removal monotonicity for Mallows.

Paper statement: after any candidate `c` is removed, the expected value of the
best remaining candidate is weakly higher under the more accurate algorithmic
Mallows law than under the human law.

Lean uses the inverse Mallows parameter `q`, so greater accuracy is
`C.algorithm.q < C.human.q`.
-/
theorem paper_definition1_expectedBestAfterRemoval_le_of_rankFactorization
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (c : Candidate n)
    (hstrict : C.StrictlyCenterOrdered value)
    (hq_lt : C.algorithm.q < C.human.q)
    (hhuman_q_lt_one : C.human.q < 1) :
    AccuracyFamily.expectedBestAfterRemoval C.human.law value c ≤
      AccuracyFamily.expectedBestAfterRemoval C.algorithm.law value c := by
  exact C.expectedBestAfterRemoval_le_of_rankFactorization
    c C.algorithm.rankFactorization C.human.rankFactorization
    hstrict hq_lt hhuman_q_lt_one

end MallowsComparison

namespace MallowsAccuracyFamilySpec

/--
Mallows family bridge to the paper-level Theorem 1 assumptions.

The fixed-parameter Mallows finite-sum proof supplies Definition 2 for every
positive parameter and Definition 3 for every `θA > θH > 0`.  The first-mover
and singleton-removal parts of Definition 1 monotonicity are proved from
Mallows rank-power MLR theorems. Concrete Mallows instantiates the analytic
fields separately below.
-/
noncomputable def paper_theorem1_paperAssumptions_from_mallows_family
    {n : ℕ} (MF : MallowsAccuracyFamilySpec n)
    (hn : 0 < n) :
    AccuracyFamily.Theorem1PaperAssumptions MF.toAccuracyFamily :=
  MF.theorem1PaperAssumptions hn

/--
Paper Theorem 1 for a parameterized Mallows family.

Definitions 2 and 3 are discharged by the formalized Mallows Theorem 3 route,
and Definition 1 finite monotonicity is discharged by the Mallows MLR route.
-/
theorem paper_theorem1_mallows_family
    {n : ℕ} (MF : MallowsAccuracyFamilySpec n)
    (hn : 0 < n) (θH : ℝ) (hθH : 0 < θH) :
    AccuracyFamily.Theorem1Target MF.toAccuracyFamily θH :=
  MF.theorem1Target hn θH hθH

end MallowsAccuracyFamilySpec

/--
Appendix E / Theorem 9, concrete Mallows satisfies the paper's family
assumptions.

Paper statement: the Mallows family with Kendall tau distance and
`θ = φ - 1` satisfies Definition 1.  Lean exposes the exact package consumed by
Theorem 1; in this concrete Mallows instance the Definition 1 analytic fields,
Definitions 2 and 3, and the finite-removal monotonicity bridge are all filled
by the preceding Mallows formalization.
-/
noncomputable def paper_theorem9_concrete_mallows_family_assumptions
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value)
    (hn : 0 < n) :
    AccuracyFamily.Theorem1PaperAssumptions
      (MallowsAccuracyFamilySpec.toAccuracyFamily
        (concreteMallowsAccuracyFamilySpec center value hvalue)) :=
  (concreteMallowsAccuracyFamilySpec center value hvalue).theorem1PaperAssumptions hn

/--
Paper Theorem 1 for the concrete Mallows family.

Paper statement: under Definition 1's Mallows accuracy family, Definition 2,
Definition 3, and strict center-ordered values, every positive human accuracy
admits a more accurate algorithmic parameter witnessing the monoculture paradox.
-/
theorem paper_theorem1_concrete_mallows_family
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value)
    (hn : 0 < n) (θH : ℝ) (hθH : 0 < θH) :
    AccuracyFamily.Theorem1Target
      (MallowsAccuracyFamilySpec.toAccuracyFamily
        (concreteMallowsAccuracyFamilySpec center value hvalue))
      θH :=
  concreteMallows_theorem1Target center value hvalue hn θH hθH

/--
Theorem 1 proof notation: `h(θA)` is constant in `θA`.
-/
theorem paper_theorem1_h_is_constant
    {n : ℕ} (F : AccuracyFamily n) (θA θA' θH : ℝ) :
    AccuracyFamily.theorem1_h F θA θH =
      AccuracyFamily.theorem1_h F θA' θH :=
  AccuracyFamily.theorem1_h_const F θA θA' θH

/--
Theorem 1 proof notation: `f(θA)` is the all-algorithm welfare expression.
-/
theorem paper_theorem1_f_eq_algorithm_welfare
    {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ) :
    AccuracyFamily.theorem1_f F θA θH =
      Model.welfareRandomOrder (F.modelAt θA θH)
        Strategy.algorithm Strategy.algorithm :=
  AccuracyFamily.theorem1_f_eq_algorithm_welfare F θA θH

/--
Theorem 1 proof notation: `h(θA)` is the all-human welfare expression.
-/
theorem paper_theorem1_h_eq_human_welfare
    {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ) :
    AccuracyFamily.theorem1_h F θA θH =
      Model.welfareRandomOrder (F.modelAt θA θH)
        Strategy.human Strategy.human :=
  AccuracyFamily.theorem1_h_eq_human_welfare F θA θH

/--
Theorem 1 proof notation, finite continuity bridge for `f`.

Paper statement in the proof: the payoff/welfare expressions are continuous in
`θA`. For the all-algorithm expression `f`, Lean proves this from atomwise
epsilon-delta continuity of the finite ranking law `F_θ`.
-/
theorem paper_theorem1_f_continuous_from_atom_continuity
    {n : ℕ} (F : AccuracyFamily n) (θH θstar : ℝ)
    (hdist :
      ∀ π : Ranking n, EconCSLib.EpsilonContinuousAt
        (fun θA => ((F.dist θA) π).toReal) θstar) :
    EconCSLib.EpsilonContinuousAt
      (fun θA => AccuracyFamily.theorem1_f F θA θH) θstar :=
  AccuracyFamily.theorem1_f_epsilonContinuousAt_of_atom_continuity
    F θH θstar hdist

/--
Theorem 1 proof notation, finite continuity bridge for `g`.

The mixed algorithm-human expression `g(θA)` is also continuous in `θA` when the
finite ranking law is atomwise epsilon-delta continuous.
-/
theorem paper_theorem1_g_continuous_from_atom_continuity
    {n : ℕ} (F : AccuracyFamily n) (θH θstar : ℝ)
    (hdist :
      ∀ π : Ranking n, EconCSLib.EpsilonContinuousAt
        (fun θA => ((F.dist θA) π).toReal) θstar) :
    EconCSLib.EpsilonContinuousAt
      (fun θA => AccuracyFamily.theorem1_g F θA θH) θstar :=
  AccuracyFamily.theorem1_g_epsilonContinuousAt_of_atom_continuity
    F θH θstar hdist

/--
Theorem 1 proof notation, interval continuity bridge for `f - g`.

This supplies the `ContinuousOn` field used by the interval sign-change
certificate from atomwise continuity of the finite ranking law on `[lo, hi]`.
-/
theorem paper_theorem1_f_sub_g_continuousOn_from_atom_continuity
    {n : ℕ} (F : AccuracyFamily n) (θH lo hi : ℝ)
    (hdist :
      ∀ θA, θA ∈ Set.Icc lo hi →
        ∀ π : Ranking n, EconCSLib.EpsilonContinuousAt
          (fun θ => ((F.dist θ) π).toReal) θA) :
    ContinuousOn
      (fun θA =>
        AccuracyFamily.theorem1_f F θA θH -
          AccuracyFamily.theorem1_g F θA θH)
      (Set.Icc lo hi) :=
  AccuracyFamily.theorem1_f_sub_g_continuousOn_of_atom_continuity
    F θH lo hi hdist

/--
Theorem 1 proof notation, continuity persistence step.

Paper statement in the proof: after finding a point with `f(θ*) < h(θ*)`,
continuity makes `f(θA) < h(θA)` continue to hold for a sufficiently small
increase of `θA`. Lean proves this finite version from atomwise continuity of
the ranking law.
-/
theorem paper_theorem1_f_lt_h_persists_right_from_atom_continuity
    {n : ℕ} (F : AccuracyFamily n) (θH θstar : ℝ)
    (hdist :
      ∀ π : Ranking n, EconCSLib.EpsilonContinuousAt
        (fun θA => ((F.dist θA) π).toReal) θstar)
    (hgap :
      AccuracyFamily.theorem1_f F θstar θH <
        AccuracyFamily.theorem1_h F θstar θH) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ θA : ℝ, θstar < θA → θA < θstar + δ →
        AccuracyFamily.theorem1_f F θA θH <
          AccuracyFamily.theorem1_h F θA θH :=
  AccuracyFamily.theorem1_f_lt_h_persists_right_of_atom_continuity
    F θH θstar hdist hgap

/--
Theorem 1 proof notation, initial crossing side.

Paper statement in the proof: by Definition 2, at equal accuracies
`f(θH) < g(θH)`, where
`f(θA) = UA(θA, θH) + UAA(θA, θH)` and
`g(θA) = UH(θA, θH) + UAH(θA, θH)`.
-/
theorem paper_theorem1_initial_f_lt_g_from_definition2
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (hpaper : Model.PaperHypotheses (F.modelAt θH θH)) :
    AccuracyFamily.theorem1_f F θH θH <
      AccuracyFamily.theorem1_g F θH θH :=
  AccuracyFamily.theorem1_f_lt_g_of_paperHypotheses_equalAccuracy
    F θH hpaper

/--
Theorem 1 proof notation, left endpoint for the interval sign-change argument.

Paper statement in the proof: by Definition 2, `f(θH) < g(θH)`, and by
continuity this inequality persists for a slightly larger algorithm accuracy.
Lean proves the finite version from atomwise continuity at `θH`.
-/
theorem paper_theorem1_exists_right_initial_f_lt_g_from_definition2_and_continuity
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (hpaper : Model.PaperHypotheses (F.modelAt θH θH))
    (hdist :
      ∀ π : Ranking n, EconCSLib.EpsilonContinuousAt
        (fun θ => ((F.dist θ) π).toReal) θH) :
    ∃ lo : ℝ, θH < lo ∧
      AccuracyFamily.theorem1_f F lo θH <
        AccuracyFamily.theorem1_g F lo θH :=
  AccuracyFamily.theorem1_exists_right_initial_f_lt_g_of_atom_continuity
    F θH hpaper hdist

/--
Theorem 1 proof notation, left endpoint from exactly Definition 2.

This is the paper-faithful version of the previous wrapper: Definition 3 is not
used at equal accuracies, so Lean only assumes independent reranking preference
for `F_θH`.
-/
theorem paper_theorem1_exists_right_initial_f_lt_g_from_independent_reranking_and_continuity
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (hind : Model.PrefersIndependentReranking (F.dist θH) F.value)
    (hdist :
      ∀ π : Ranking n, EconCSLib.EpsilonContinuousAt
        (fun θ => ((F.dist θ) π).toReal) θH) :
    ∃ lo : ℝ, θH < lo ∧
      AccuracyFamily.theorem1_f F lo θH <
        AccuracyFamily.theorem1_g F lo θH :=
  AccuracyFamily.theorem1_exists_right_initial_f_lt_g_of_prefersIndependent_and_atom_continuity
    F θH hind hdist

/--
Theorem 1 proof notation, weaker-competition side.

Paper statement in the proof: by Definition 3, for `θA > θH`,
`g(θA) < h(θA)`, where
`h(θA) = UH(θA, θH) + UHH(θA, θH)`.
-/
theorem paper_theorem1_g_lt_h_from_definition3
    {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ)
    (hpaper : Model.PaperHypotheses (F.modelAt θA θH)) :
    AccuracyFamily.theorem1_g F θA θH <
      AccuracyFamily.theorem1_h F θA θH :=
  AccuracyFamily.theorem1_g_lt_h_of_paperHypotheses F θA θH hpaper

/--
Theorem 1 proof notation, inequality (5).

Paper statement in the proof: Definition 1 monotonicity gives
`UA(θA, θH) + UHA(θA, θH) > UH(θA, θH) + UHH(θA, θH)`.
-/
theorem paper_theorem1_inequality5_from_monotonicity
    {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ)
    (hmono : AccuracyFamily.Theorem1MonotonicityAt F θA θH) :
    AccuracyFamily.theorem1_h F θA θH <
      AccuracyFamily.theorem1_algorithmAgainstHuman F θA θH :=
  AccuracyFamily.theorem1_algorithmAgainstHuman_gt_h_of_monotonicity
    F θA θH hmono

/--
Theorem 1 proof notation, finite-removal monotonicity bridge.

Paper statement in the proof: inequality (5) follows from Definition 1
monotonicity, including weak improvement after removing the first mover's hired
candidate from the pool.
-/
theorem paper_theorem1_inequality5_from_removal_monotonicity
    {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ)
    (hmono : AccuracyFamily.Theorem1RemovalMonotonicityAt F θA θH) :
    AccuracyFamily.theorem1_h F θA θH <
      AccuracyFamily.theorem1_algorithmAgainstHuman F θA θH :=
  AccuracyFamily.theorem1_algorithmAgainstHuman_gt_h_of_monotonicity
    F θA θH
    (AccuracyFamily.theorem1MonotonicityAt_of_removalMonotonicity
      F θA θH hmono)

/--
Paper Theorem 1 from the final crossing certificate.

Paper statement: if a candidate distribution and noisy permutation family satisfy
Definitions 2 and 3, then for every baseline human accuracy `θH` there exists
`θA > θH` such that using the common algorithmic ranking is strictly dominant,
but all-human welfare is higher.

This theorem formalizes the final game-theoretic step: once the paper's
continuity/asymptotic-optimality argument supplies a `θA` with `g < f < h` and
Definition 1 monotonicity supplies inequality (5), the monoculture paradox
follows.
-/
theorem paper_theorem1_from_crossing_certificate
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (cert : AccuracyFamily.Theorem1CrossingCertificate F θH) :
    AccuracyFamily.Theorem1Target F θH :=
  AccuracyFamily.theorem1Target_of_crossingCertificate cert

/--
Paper Theorem 1 from the right-neighborhood nudge certificate.

This exposes the final "slightly increase `θA`" move: if there is a right
neighborhood after the equality point where `g < f < h`, Lean constructs the
witness accuracy at the midpoint of that neighborhood.
-/
theorem paper_theorem1_from_right_nudge_certificate
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (cert : AccuracyFamily.Theorem1RightNudgeCertificate F θH) :
    AccuracyFamily.Theorem1Target F θH :=
  AccuracyFamily.theorem1Target_of_rightNudgeCertificate cert

/--
Paper Theorem 1 from the local analytic nudge certificate.

This version proves the `f < h` part of the right-neighborhood nudge from
epsilon-delta continuity of `f` and the strict inequality `f(θ*) < h(θ*)`.
The remaining analytic crossing obligation is the right-neighborhood `g < f`
field in `AccuracyFamily.Theorem1LocalNudgeCertificate`.
-/
theorem paper_theorem1_from_local_nudge_certificate
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (cert : AccuracyFamily.Theorem1LocalNudgeCertificate F θH) :
    AccuracyFamily.Theorem1Target F θH :=
  AccuracyFamily.theorem1Target_of_localNudgeCertificate cert

/--
Paper Theorem 1 from the atomwise local analytic nudge certificate.

This is the local nudge theorem with the continuity premise stated directly as
atomwise epsilon-delta continuity of the finite ranking family.
-/
theorem paper_theorem1_from_atom_local_nudge_certificate
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (cert : AccuracyFamily.Theorem1AtomLocalNudgeCertificate F θH) :
    AccuracyFamily.Theorem1Target F θH :=
  AccuracyFamily.theorem1Target_of_atomLocalNudgeCertificate cert

/--
Paper Theorem 1 from the interval sign-change nudge certificate.

Paper statement in the proof: after `f` starts below `g` and eventually exceeds
`g`, continuity supplies a crossing, and then a slight increase of `θA` gives
`g < f < h`. Lean uses a last-nonpositive-point version of this argument on a
compact interval, avoiding any hidden assumption that an arbitrary crossing has
the right one-sided sign.
-/
theorem paper_theorem1_from_sign_change_nudge_certificate
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (cert : AccuracyFamily.Theorem1SignChangeNudgeCertificate F θH) :
    AccuracyFamily.Theorem1Target F θH :=
  AccuracyFamily.theorem1Target_of_signChangeNudgeCertificate cert

/--
Paper Theorem 1 from the paper-shaped interval analytic certificate.

This variant states the remaining inputs closer to the paper: Definitions 2/3
as `Model.PaperHypotheses` on the interval, Definition 1 monotonicity as the
finite-removal monotonicity certificate, and the analytic sign-change data for
`f - g`.
-/
theorem paper_theorem1_from_interval_analytic_certificate
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (cert : AccuracyFamily.Theorem1IntervalAnalyticCertificate F θH) :
    AccuracyFamily.Theorem1Target F θH :=
  AccuracyFamily.theorem1Target_of_intervalAnalyticCertificate cert

/--
Paper Theorem 1 from the global analytic certificate.

This is the strongest current Theorem 1 wrapper: it packages the paper's
Definition 2 at equal accuracy, Definition 3 above `θH`, continuity,
asymptotic dominance, and monotonicity inputs at fixed `θH`, then Lean
constructs the witness `θA > θH`.
-/
theorem paper_theorem1_from_global_analytic_certificate
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (cert : AccuracyFamily.Theorem1GlobalAnalyticCertificate F θH) :
    AccuracyFamily.Theorem1Target F θH :=
  AccuracyFamily.theorem1Target_of_globalAnalyticCertificate cert

/--
Paper Theorem 1 from paper-level family assumptions.

Paper statement: suppose the candidate values and noisy permutation family
satisfy Definition 2 and Definition 3, and the family has the Definition 1
analytic properties used in the proof. Then for every positive human accuracy
`θH`, there exists a higher algorithmic accuracy `θA > θH` at which algorithmic
monoculture is strictly dominant but has lower welfare than all-human ranking.

The Lean assumption structure records the finite-discrete version of those
paper hypotheses:
1. independent-reranking preference for every positive accuracy;
2. weaker-competition preference for every `θA > θH > 0`;
3. atomwise continuity of the finite ranking law;
4. the asymptotic dominance consequence used in the crossing argument; and
5. finite-removal monotonicity for the first and second mover inequalities.
-/
theorem paper_theorem1_from_paper_assumptions
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (hθH : 0 < θH)
    (assumptions : AccuracyFamily.Theorem1PaperAssumptions F) :
    AccuracyFamily.Theorem1Target F θH :=
  AccuracyFamily.theorem1Target_of_paperAssumptions hθH assumptions

/--
Paper Theorem 1 from the direct payoff certificate.

This is the same final conclusion stated directly in terms of the two strict
dominance inequalities and the all-human/all-algorithm welfare comparison.
-/
theorem paper_theorem1_from_payoff_certificate
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (cert : AccuracyFamily.Theorem1PayoffCertificate F θH) :
    AccuracyFamily.Theorem1Target F θH :=
  AccuracyFamily.theorem1Target_of_payoffCertificate cert

/--
Paper Theorem 1 (family form).

For a fixed accuracy family `F` and baseline human accuracy `θH`, the theorem
claims there exists `θA > θH` such that the induced monoculture model
`F.modelAt θA θH` exhibits a paradox.

This wrapper is the single-file human-facing checkpoint for the theorem-level
target: `AccuracyFamily.Theorem1Target F θH`.
-/
theorem paper_theorem1_target
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (h : ∃ θA, θH < θA ∧ Model.HasKR21MonocultureParadox (AccuracyFamily.modelAt F θA θH)) :
    AccuracyFamily.Theorem1Target F θH := by
  exact (AccuracyFamily.theorem1Target_iff_exists_paradox (F := F) (θH := θH)).2 h

lemma paper_theorem1_target_iff_exists_paradox
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) :
    AccuracyFamily.Theorem1Target F θH ↔
      ∃ θA, θH < θA ∧ Model.HasKR21MonocultureParadox (AccuracyFamily.modelAt F θA θH) := by
  exact AccuracyFamily.theorem1Target_iff_exists_paradox (F := F) (θH := θH)

end KR21Monoculture
