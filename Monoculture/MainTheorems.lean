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
