import Monoculture.MallowsFiniteLemmas
import Monoculture.Family
import Monoculture.MallowsPairwise

/-!
# Paper-Facing Theorems: Algorithmic Monoculture and Social Welfare

This file is the single, paper-oriented verification surface for the monoculture
formalization.

Declarations are arranged by the paper order so a human can read this file in one
pass, check each statement against the paper wording, and then follow the named
support lemmas below.
-/

namespace Monoculture
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
Theorem 3 (finite-sum Mallows form): from the cleared finite Mallows certificate,
paper hypotheses follow for the induced pointwise model.
-/
theorem paper_theorem3_pointwise_finite_mallows_sum
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (cert : C.CenterMallowsFiniteSumCertificate value) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.theorem3_pointwise_of_centerMallowsFiniteSumCertificate cert

/--
Theorem 3 (reduced product-sign form): from reduced product-sign finite Mallows
certificates, paper hypotheses follow.
-/
theorem paper_theorem3_pointwise_reduced_product_certificate
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

end MallowsComparison

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

end Monoculture
