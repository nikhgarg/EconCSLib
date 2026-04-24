import Monoculture.MallowsFiniteLemmas
import Monoculture.Theorem1
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

end MallowsComparison

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
Definition 2, Definition 3, continuity, asymptotic dominance, and monotonicity
inputs at fixed `θH`, then Lean constructs the witness `θA > θH`.
-/
theorem paper_theorem1_from_global_analytic_certificate
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (cert : AccuracyFamily.Theorem1GlobalAnalyticCertificate F θH) :
    AccuracyFamily.Theorem1Target F θH :=
  AccuracyFamily.theorem1Target_of_globalAnalyticCertificate cert

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
