import Monoculture.MallowsFiniteLemmas

/-!
# Paper-Facing Theorems: Algorithmic Monoculture and Social Welfare

This file is the public theorem interface for the monoculture formalization.
Detailed definitions and proof infrastructure live in the sibling files.
-/

namespace Monoculture
namespace MallowsComparison

/--
Paper Theorem 3, pointwise finite Mallows form.

If the denominator-cleared finite Mallows sum certificate holds for the
algorithm and human Mallows laws, then the induced pointwise model satisfies
the paper's independent-reranking and weaker-competition hypotheses.
-/
theorem paper_theorem3_pointwise_finite_mallows_sum
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (cert : C.CenterMallowsFiniteSumCertificate value) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.theorem3_pointwise_of_centerMallowsFiniteSumCertificate cert

/--
Paper Theorem 3, reduced product-sign finite Mallows form.

This variant isolates the center-candidate positivity facts and leaves only
non-center product-sign finite Mallows inequalities as certificate fields.
-/
theorem paper_theorem3_pointwise_reduced_product_certificate
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (cert : C.CenterMallowsReducedProductCrossWeightCertificate value) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.theorem3_pointwise_of_centerMallowsReducedProductCrossWeightCertificate cert

/--
Normalized candidate-sum obligations are equivalent to the denominator-cleared
finite Mallows certificate once strict center ordering is supplied.
-/
theorem paper_theorem3_finite_sum_certificate_from_candidate_sums
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (cert : C.CandidateSumCertificate value) :
    C.CenterMallowsFiniteSumCertificate value := by
  exact C.centerMallowsFiniteSumCertificate_of_candidateSumCertificate hstrict cert

end MallowsComparison
end Monoculture
