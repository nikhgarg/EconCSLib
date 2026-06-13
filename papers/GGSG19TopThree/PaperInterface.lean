import GGSG19TopThree.ProofInterface
import GGSG19TopThree.Assumptions

/-!
# Human-Facing Interface for GGSG19

This compact interface gives stable paper-label names for the main source
statements in Garg--Gelauff--Sakshuwong--Goel (2019).  The proofs are thin
wrappers around the detailed proof surface in `ProofInterface.lean`.
-/

namespace GGSG19TopThree

open EconCSLib.SocialChoice.Ranking
open EconCSLib.Probability

noncomputable section

/--
Source status: direct source definition.

Paper definition of an exponential large-deviation rate.
-/
abbrev paper_definition_large_deviation_rate (A : ℕ → ℝ) (r : ℝ) : Prop :=
  definition_large_deviation_rate A r

/--
Source Proposition `thm:consistency`, tiered finite-ranking form.  The
no-cross-tier-equality premise is the Lean form of staying in the paper's
strict cross-tier top-prefix regime; within-tier equal expected scores are not
excluded.
-/
theorem source_proposition1_thm_consistency_tiered
    {n Stage : ℕ}
    (law : PMF (Ranking n))
    (targetPrefix : Fin Stage → Finset (Candidate n))
    (hnonempty :
      ∀ stage : Fin Stage, Nonempty (CrossTierPair (targetPrefix stage)))
    (hNoTie :
      ∀ stage : Fin Stage,
        ∀ hi lo : Candidate n,
          hi ∈ targetPrefix stage →
            lo ∉ targetPrefix stage →
              ∀ cut : RankingProperPrefixCut n,
                rankingTopPrefixProb law lo cut ≠
                  rankingTopPrefixProb law hi cut) :
    (∀ stage : Fin Stage,
      ∀ hi lo : Candidate n,
        hi ∈ targetPrefix stage →
          lo ∉ targetPrefix stage →
            ∀ cut : RankingProperPrefixCut n,
              rankingTopPrefixProb law lo cut <
                rankingTopPrefixProb law hi cut) ↔
      (∀ diff : RankingProperPrefixCut n → ℝ,
        ReasonablePrefixWeights diff →
          Filter.Tendsto
            (scoreTopTieredPrefixSelectionErrorProb law
              (rankingPrefixScore diff)
              targetPrefix
              (fun stage voters sample =>
                scoreTopSelectedSetOfCard
                  (iidSampleCandidateScore (rankingPrefixScore diff) sample)
                  (targetPrefix stage)))
            Filter.atTop (nhds 0)) :=
  proposition1_ranking_law_tiered_strict_prefix_dominance_iff_all_reasonable_tiered_prefix_score_consistency_of_no_cross_tier_prefix_ties
    law targetPrefix hnonempty hNoTie

/--
Source Proposition `thm:pairwiselearning`, finite-support form.  The ordinary
two-sided case has the paper's displayed Chernoff exponent; the explicit
one-sided branches record finite-candidate boundary cases where the finite
real rate is a zero-gap rate or the error event is eventually empty.
-/
theorem source_proposition2_thm_pairwiselearning_finite_support
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (hmean :
      0 ≤
        EconCSLib.pmfExp law
          (fun signal => hiScore signal - loScore signal)) :
    ExponentialRateCertificate
        (pairwiseScoringErrorProb law hiScore loScore)
        (pairwiseScoringRate law hiScore loScore) ∨
      (∃ pZero : ℝ,
        EconCSLib.pmfProb law
            (fun signal => hiScore signal - loScore signal = 0) =
          pZero ∧
        0 < pZero ∧
        ExponentialRateCertificate
          (pairwiseScoringErrorProb law hiScore loScore)
          (-Real.log pZero)) ∨
      (∀ᶠ n in Filter.atTop,
        pairwiseScoringErrorProb law hiScore loScore n = 0) :=
  proposition2_pairwise_exact_rate_or_boundary_from_finite_support_mean_nonneg
    law hiScore loScore hmean

/--
Source Proposition `lem:pairwiselearning_approval`, finite ternary form for
K-approval score gaps.  The finite-rate branch is exactly the paper's closed
form `approvalPairwiseRate`; the other branch is the strict boundary where the
mistake event is eventually empty.
-/
theorem source_proposition3_lem_pairwiselearning_approval_finite_ternary
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    {pUp pDown pZero : ℝ}
    (hle : pDown ≤ pUp)
    (hscore :
      ∀ signal,
        hiScore signal - loScore signal = 1 ∨
          hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1)
    (hUpProb :
      EconCSLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 1) =
        pUp)
    (hDownProb :
      EconCSLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = -1) =
        pDown)
    (hZeroProb :
      EconCSLib.pmfProb law
          (fun signal => hiScore signal - loScore signal = 0) =
        pZero) :
    ExponentialRateCertificate
        (pairwiseScoringErrorProb law hiScore loScore)
        (approvalPairwiseRate pUp pDown) ∨
      (∀ᶠ n in Filter.atTop,
        pairwiseScoringErrorProb law hiScore loScore n = 0) :=
  proposition3_approval_pairwise_exact_rate_or_eventually_zero_from_ternary_scores
    law hiScore loScore hle hscore hUpProb hDownProb hZeroProb

/--
Source Proposition `thm:goal_learning`, finite relevant-pair aggregation form.
The finite aggregate has an exact finite exponent unless all relevant
pairwise errors are eventually empty, represented as extended rate `⊤`.
-/
theorem source_proposition4_thm_goal_learning_finite_support
    {Pair Candidate Signal : Type*} [Fintype Pair] [DecidableEq Pair]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (score : Candidate → Signal → ℝ)
    (hi lo : Pair → Candidate)
    (hmean :
      ∀ pair,
        0 ≤ EconCSLib.pmfExp law
          (fun signal =>
            score (hi pair) signal - score (lo pair) signal)) :
    ∃ rate : WithTop ℝ,
      HasExtendedExponentialRate
        (fun sampleSize =>
          ∑ pair : Pair,
            finiteScoreGapPairwiseErrorProb law score
              (hi pair) (lo pair) sampleSize)
        rate := by
  simpa using
    (proposition4_outcome_error_extended_rate_from_relevant_pairs_finite_support_trichotomy
      law score hi lo hmean
      (pairWeight := fun _ => (1 : ℝ))
      (by intro pair; exact zero_le_one)
      (by intro pair; exact zero_lt_one))

/--
Source Theorem `lem:randomizebetterscoring`, finite W-selection form.  The
convex-combination static rule is reasonable, selects the target W-set, and
weakly dominates the randomized scoring rule in extended finite outcome rate.
-/
theorem source_theorem1_lem_randomizebetterscoring
    {Rule Cut Candidate Signal : Type*}
    [Fintype Rule] [DecidableEq Rule] [Fintype Cut] [DecidableEq Cut]
    [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (weight : Rule → ℝ) (diff : Rule → Cut → ℝ)
    (inPrefix : Signal → Candidate → Cut → Prop)
    [∀ signal candidate cut, Decidable (inPrefix signal candidate cut)]
    (winnerSet : Finset Candidate)
    [Nonempty (CrossTierPair winnerSet)]
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hdiff : ∀ rule, ReasonablePrefixWeights (diff rule))
    (hdom :
      StrictTopPrefixDominanceOn (prefixProbFromEvent law inPrefix)
        (fun hi lo => hi ∈ winnerSet ∧ lo ∉ winnerSet)) :
    ReasonablePrefixWeights
        (fun cut => ∑ rule : Rule, weight rule * diff rule cut) ∧
      Filter.Tendsto
        (scoreTopSelectionErrorProb law
          (fun candidate =>
            prefixScoreFromEvent
              (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
              inPrefix candidate)
          winnerSet
          (fun n sample =>
            scoreTopSelectedSetOfCard
              (iidSampleCandidateScore
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                sample)
              winnerSet))
        Filter.atTop (nhds 0) ∧
      ∃ staticRate : WithTop ℝ,
        HasExtendedExponentialRate
          (fun sampleSize =>
            ∑ pair : CrossTierPair winnerSet,
              finiteScoreGapPairwiseErrorProb law
                (fun candidate =>
                  prefixScoreFromEvent
                    (fun cut => ∑ rule : Rule, weight rule * diff rule cut)
                    inPrefix candidate)
                pair.hi pair.lo sampleSize)
          staticRate ∧
          ((finiteOutcomeLearningRate
              (fun pair : CrossTierPair winnerSet =>
                finiteChernoffRate
                  (randomizedScoringSamplingLaw law weight hweight hsum)
                  (fun signal : Rule × Signal =>
                    prefixScoreFromEvent (diff signal.1) inPrefix
                        pair.hi signal.2 -
                      prefixScoreFromEvent (diff signal.1) inPrefix
                        pair.lo signal.2)) : WithTop ℝ) ≤
            staticRate) :=
  randomized_scoring_prefix_actual_cross_tier_static_selection_and_automatic_extended_static_rate_comparison
    law weight diff inPrefix winnerSet hweight hsum hdiff hdom

/--
Source Theorem `lem:randomizenotbetterapproval`, fixed-pair form.  For any
finite randomized K-approval rule, some static component weakly dominates the
randomized pairwise rate; zero-base static boundaries are treated as top
extended rates.
-/
theorem source_theorem2_lem_randomizenotbetterapproval_pairwise
    {n : ℕ} {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (law : PMF (Ranking n))
    (K : Rule → ℕ) (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1)
    (hi lo : Candidate n) :
    ∃ rule : Rule,
      (approvalPairwiseRate
          (∑ rule : Rule,
            weight rule * kApprovalPairUpProb law (K rule) hi lo)
          (∑ rule : Rule,
            weight rule * kApprovalPairDownProb law (K rule) hi lo) :
        WithTop ℝ) ≤
        approvalPairwiseExtendedRate
          (kApprovalPairUpProb law (K rule) hi lo)
          (kApprovalPairDownProb law (K rule) hi lo) :=
  randomized_k_approval_pairwise_extended_rate_le_static
    law K weight hweight hsum hi lo

/--
Source status: direct source theorem.

Source Theorem `lem:randomizebetterapproval_Wselection`, concrete finite
constructed-law endpoint: the six-ranking law is design-invariant for
W-selection and 50/50 randomized approval strictly beats every static
K-approval cutoff in the finite family.
-/
theorem source_theorem_lem_randomizebetterapproval_w_selection_constructed
    : StrictTopPrefixDominanceOn
        constructedWSelectionRanking1TopPrefixProb
        constructedWSelectionCrossTier ∧
      (Finset.univ : Finset (Fin 4)).sup' finiteUnivNonempty
          (fun K =>
            finiteOutcomeLearningRate
              (constructedWSelectionRanking1StaticKRate K)) <
        finiteOutcomeLearningRate
          constructedWSelectionRanking1RandomizedApprovalRate :=
  randomized_approval_w_selection_constructed_ranking_law_design_invariant_and_all_static_k

/--
Source status: direct source corollary, with implicit non-uniform Mallows
domain recorded in `Assumptions.lean`.

Source Corollary `lem:mallowsnorando`: under a finite Mallows model with
`q < 1`, an approval-rate-optimal static K-approval cutoff weakly dominates
any finite randomized family of nontrivial K-approval rules.
-/
theorem source_corollary_lem_mallowsnorando
    {n : ℕ} (M : MallowsSpec n) (W : Candidate n) (hW : 0 < W.val)
    (hq_lt : M.q < 1)
    {Rule : Type*} [Fintype Rule] [Nonempty Rule]
    (K : Rule → ℕ)
    (hK_pos : ∀ rule, 0 < K rule)
    (hK_lt : ∀ rule, K rule < n + 2)
    (weight : Rule → ℝ)
    (hweight : ∀ rule, 0 ≤ weight rule)
    (hsum : (∑ rule : Rule, weight rule) = 1) :
    ∃ cut : RankingProperPrefixCut n,
      (∀ cut' : RankingProperPrefixCut n,
        mallowsTopWKApprovalOutcomeRate M W hW (cut'.val + 1) ≤
          mallowsTopWKApprovalOutcomeRate M W hW (cut.val + 1)) ∧
      mallowsTopWRandomizedKApprovalOutcomeRate M W hW K weight ≤
        mallowsTopWKApprovalOutcomeRate M W hW (cut.val + 1) :=
  mallows_k_approval_no_randomization_to_approval_rate_optimal_from_mallows_model_q_lt_one
    M W hW hq_lt K hK_pos hK_lt weight hweight hsum

/--
Source Theorem `lem:mallowsnotWK`: a four-candidate high-noise Mallows
counterexample where W-approval is not approval-rate optimal.
-/
theorem source_theorem_lem_mallowsnotWK_counterexample :
    ∃ M : MallowsSpec 2,
      M.center = Equiv.refl (Candidate 2) ∧
        M.q = mallowsHighNoisePhi ∧
          ∃ better : Fin 3,
            better ≠ (2 : Fin 3) ∧
              finiteOutcomeLearningRate
                  (mallowsW3StaticKApprovalPairRate M (2 : Fin 3)) <
                finiteOutcomeLearningRate
                  (mallowsW3StaticKApprovalPairRate M better) :=
  mallows_high_noise_w3_w_approval_not_approval_rate_optimal_counterexample

end

end GGSG19TopThree
