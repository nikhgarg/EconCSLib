import KR21Monoculture.MainTheorems

/-!
# Paper Interface: Algorithmic Monoculture and Social Welfare

This file is the compact human-facing review surface for the active KR21
formalization. `MainTheorems.lean` remains the full paper-oriented ledger; this
interface starts with the stable Mallows/RUM statements that are ready for
paper-vs-Lean review while other agents continue proof work.
-/

open EconCSLib MeasureTheory
open scoped ENNReal NNReal

namespace KR21Monoculture
namespace PaperInterface

/-! ## Paper Definitions -/

/-- Paper Mallows family parameterization used by the compact review surface. -/
noncomputable abbrev mallowsSpec {n : ℕ} (center : Ranking n) (theta : ℝ) := concreteMallowsSpec center theta

/-- Paper Appendix C strict well-ordered noise predicate. -/
abbrev strictlyWellOrderedNoise (f : ℝ → ℝ) : Prop := StrictlyWellOrderedNoise f

/-! ## Definitions and Appendix C Noise Statements -/

/--
Definition 1 / Mallows atomwise continuity: for the Mallows family with
parameter `theta`, the probability of any fixed permutation varies continuously
with positive `theta`.
-/
theorem definition1_concreteMallowsSpec_atom_continuity
    {n : ℕ} (center : Ranking n) {theta : ℝ} (htheta : 0 < theta)
    (pi : Ranking n) :
    EconCSLib.EpsilonContinuousAt
      (fun theta' => (((concreteMallowsSpec center theta').law) pi).toReal) theta :=
    KR21Monoculture.paper_definition1_concreteMallowsSpec_atom_continuity
      center htheta pi

/--
Definition 1 / Mallows asymptotic first dominance: as algorithmic Mallows
accuracy tends to infinity, the all-algorithm payoff eventually exceeds the
human-against-algorithm payoff used in Theorem 1.
-/
theorem definition1_concreteMallowsSpec_asymptotic_first_dominance
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value) :
    ∀ thetaH lower, 0 < thetaH → thetaH < lower →
      ∃ hi, lower < hi ∧
        AccuracyFamily.theorem1_g
            ({ dist := fun theta => (concreteMallowsSpec center theta).law,
                value := value } : AccuracyFamily n)
            hi thetaH <
          AccuracyFamily.theorem1_f
            ({ dist := fun theta => (concreteMallowsSpec center theta).law,
                value := value } : AccuracyFamily n)
            hi thetaH :=
    KR21Monoculture.paper_definition1_concreteMallowsSpec_asymptotic_first_dominance
      center value hvalue

/-- Appendix C Lemma 1, Gaussian noise is strictly well-ordered. -/
theorem lemma1_gaussian_strictlyWellOrdered
    {kappa : ℝ} (hkappa : 0 < kappa) :
    StrictlyWellOrderedNoise (gaussianNoiseKernel kappa) :=  KR21Monoculture.paper_lemma1_gaussian_strictlyWellOrdered hkappa

/--
Appendix C Lemma 1, Laplacian weak form: the Laplacian density kernel satisfies
the globally valid weak well-ordering inequality.
-/
theorem lemma1_laplacian_weaklyWellOrdered
    {lam : ℝ} (hlam : 0 ≤ lam) :
    WeaklyWellOrderedNoise (laplacianNoiseKernel lam) :=  KR21Monoculture.paper_lemma1_laplacian_weaklyWellOrdered hlam

end PaperInterface
end KR21Monoculture
