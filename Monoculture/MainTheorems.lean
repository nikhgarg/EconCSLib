import Monoculture.MallowsFiniteLemmas
import Monoculture.Theorem1
import Monoculture.MallowsPairwise
import Monoculture.MallowsFamily
import Monoculture.RUM

/-!
# Paper-Facing Theorems: Algorithmic Monoculture and Social Welfare

This file is the single, paper-oriented verification surface for the monoculture
formalization.

Declarations are arranged by the paper order so a human can read this file in one
pass, check each statement against the paper wording, and then follow the named
support lemmas below.
-/

namespace Monoculture

/--
Definition 1 / Mallows atomwise continuity.

Paper statement: for the Mallows family with parameter `θ = φ - 1`, the
probability of any fixed permutation varies continuously with positive `θ`.

Lean uses the finite epsilon-delta interface required by the Theorem 1 proof.
-/
theorem paper_definition1_concreteMallowsSpec_atom_continuity
    {n : ℕ} (center : Ranking n) {θ : ℝ} (hθ : 0 < θ)
    (π : Ranking n) :
    DecisionCore.EpsilonContinuousAt
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
        DecisionCore.pmfProb ν (fun ω => (2 : Candidate 1) = firstChoice (better ω)))
    (hworse :
      firstChoiceProb μWorse (2 : Candidate 1) =
        DecisionCore.pmfProb ν (fun ω => (2 : Candidate 1) = firstChoice (worse ω)))
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
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hbottomMiddle_le_bottomTop :
      DecisionCore.pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        DecisionCore.pmfProb ν (fun ω =>
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
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)))
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
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)))
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
      DecisionCore.pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        DecisionCore.pmfProb ν (fun ω =>
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
    DecisionCore.pmfProb ν (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω)) ≤
      DecisionCore.pmfProb ν (fun ω =>
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
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)))
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
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)))
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
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)))
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
      DecisionCore.pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        DecisionCore.pmfProb ν (fun ω =>
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
      (μ π).toReal = DecisionCore.pmfProb ν (fun ω => rank ω = π))
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
      (μ π).toReal = DecisionCore.pmfProb ν (fun ω => rank ω = π))
    (p : Ranking 1 → Prop) [DecidablePred p] :
    DecisionCore.pmfProb μ p =
      DecisionCore.pmfProb ν (fun ω => p (rank ω)) :=
  DecisionCore.pmfProb_eq_pmfProb_preimage_of_atom_eq
    μ ν rank hpreimage p

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
    DecisionCore.pmfProb μ
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
      1 - rum3Lambda1 μ :=
  rum3Lambda1_wrong_eq_one_sub μ

/--
Appendix C / lambda complement identity for the `x₁` vs `x₂` subproblem.
-/
theorem paper_theorem6_lambda3_wrong_eq_one_sub (μ : PMF (Ranking 1)) :
    DecisionCore.pmfProb μ
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
      1 - rum3Lambda3 μ :=
  rum3Lambda3_wrong_eq_one_sub μ

/--
Appendix C / pairwise correctness implies `λ₁ > 1/2`.
-/
theorem paper_theorem6_lambda1_half_of_wrong_lt_correct
    {μ : PMF (Ranking 1)}
    (hwrong :
      DecisionCore.pmfProb μ
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
      DecisionCore.pmfProb μ
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
      DecisionCore.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μWorse)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μWorse π₀).toReal)
    (h12_wrong_lt_correct :
      DecisionCore.pmfProb μWorse
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
      DecisionCore.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μWorse)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (h12_wrong_lt_correct :
      DecisionCore.pmfProb μWorse
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
    DecisionCore.pmfProb μ
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
    DecisionCore.pmfProb μ
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
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μWorse =
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong23μ :
      DecisionCore.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hlambda3μ :
      rum3Lambda3 μWorse =
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong12μ :
      DecisionCore.pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        DecisionCore.pmfProb ν
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
      DecisionCore.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μWorse)
    {π₀ : Ranking 1}
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmassLambda : 0 < (μWorse π₀).toReal)
    (h12_wrong_lt_correct :
      DecisionCore.pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μWorse)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)))
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
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)))
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
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)))
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
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)))
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
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)))
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
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μWorse =
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong23μ :
      DecisionCore.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hlambda3μ :
      rum3Lambda3 μWorse =
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong12μ :
      DecisionCore.pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        DecisionCore.pmfProb ν
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
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)))
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
      (μBetter π).toReal = DecisionCore.pmfProb ν (fun ω => better ω = π))
    (hworsePreimage : ∀ π : Ranking 1,
      (μWorse π).toReal = DecisionCore.pmfProb ν (fun ω => worse ω = π))
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
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (1 : Candidate 1)) := by
    unfold rum3Lambda1
    exact paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
  have hlambda2μ :
      rum3Lambda2 μWorse =
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (1 : Candidate 1) =
            (0 : Candidate 1)) := by
    unfold rum3Lambda2
    exact paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))
  have hwrong23μ :
      DecisionCore.pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (0 : Candidate 1) =
            (2 : Candidate 1)) :=
    paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1))
  have hlambda3μ :
      rum3Lambda3 μWorse =
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (0 : Candidate 1)) := by
    unfold rum3Lambda3
    exact paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))
  have hwrong12μ :
      DecisionCore.pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        DecisionCore.pmfProb ν
          (fun ω => bestRemainingAfter (worse ω) (2 : Candidate 1) =
            (1 : Candidate 1)) :=
    paper_theorem6_eventProb_of_sample_preimages
      μWorse ν worse hworsePreimage
      (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1))
  have hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (better ω)) := by
    intro c
    unfold firstChoiceProb
    exact paper_theorem6_eventProb_of_sample_preimages
      μBetter ν better hbetterPreimage
      (fun π => c = firstChoice π)
  have hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        DecisionCore.pmfProb ν (fun ω => c = firstChoice (worse ω)) := by
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
      ∀ π : Ranking n, DecisionCore.EpsilonContinuousAt
        (fun θA => ((F.dist θA) π).toReal) θstar) :
    DecisionCore.EpsilonContinuousAt
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
      ∀ π : Ranking n, DecisionCore.EpsilonContinuousAt
        (fun θA => ((F.dist θA) π).toReal) θstar) :
    DecisionCore.EpsilonContinuousAt
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
        ∀ π : Ranking n, DecisionCore.EpsilonContinuousAt
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
      ∀ π : Ranking n, DecisionCore.EpsilonContinuousAt
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
      ∀ π : Ranking n, DecisionCore.EpsilonContinuousAt
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
      ∀ π : Ranking n, DecisionCore.EpsilonContinuousAt
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
    (h : ∃ θA, θH < θA ∧ Model.HasMonocultureParadox (AccuracyFamily.modelAt F θA θH)) :
    AccuracyFamily.Theorem1Target F θH := by
  exact (AccuracyFamily.theorem1Target_iff_exists_paradox (F := F) (θH := θH)).2 h

lemma paper_theorem1_target_iff_exists_paradox
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) :
    AccuracyFamily.Theorem1Target F θH ↔
      ∃ θA, θH < θA ∧ Model.HasMonocultureParadox (AccuracyFamily.modelAt F θA θH) := by
  exact AccuracyFamily.theorem1Target_iff_exists_paradox (F := F) (θH := θH)

end Monoculture
