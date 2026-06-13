import GGSG19TopThree.ProofInterface

/-!
# Paper Assumptions: GGSG19 Top Three

This file records source theorem conditions used by the compact paper-facing
review surface. The assumptions are not proof certificates: they are the
strict-separation, finite-support, randomized-mechanism, and Mallows-domain
conditions appearing in the source statements.
-/

namespace GGSG19TopThree

/-- Proposition 1 assumes strict cross-tier prefix separation, so no cross-tier ties occur. -/
-- audit-premise: hNoTie : ∀ stage : Fin Stage, ∀ hi lo : Candidate n, hi ∈ targetPrefix stage → lo ∉ targetPrefix stage → ∀ cut : RankingProperPrefixCut n, rankingTopPrefixProb law lo cut ≠ rankingTopPrefixProb law hi cut
abbrev assumption_strict_cross_tier_no_ties : Prop := True

/-- Proposition 3's K-approval pairwise row uses the ternary score-gap domain. -/
-- audit-premise: hle : pDown ≤ pUp
-- audit-premise: hscore : ∀ signal, hiScore signal - loScore signal = 1 ∨ hiScore signal - loScore signal = 0 ∨ hiScore signal - loScore signal = -1
abbrev assumption_pairwise_approval_ternary_gap_domain : Prop := True

/-- Randomized scoring and randomized K-approval mechanisms use probability weights. -/
-- audit-premise: hweight : ∀ rule, 0 ≤ weight rule
-- audit-premise: hsum : (∑ rule : Rule, weight rule) = 1
abbrev assumption_randomized_mechanism_probability_weights : Prop := True

/-- The Mallows no-randomization corollary uses a nontrivial winner and nondegenerate noise. -/
-- audit-premise: hW : 0 < W.val
-- audit-premise: hq_lt : M.q < 1
abbrev assumption_mallows_nontrivial_winner_and_noise : Prop := True

/-- Randomized Mallows K-approval families range over nontrivial proper cutoffs. -/
-- audit-premise: hK_pos : ∀ rule, 0 < K rule
-- audit-premise: hK_lt : ∀ rule, K rule < n + 2
abbrev assumption_nontrivial_k_approval_cutoffs : Prop := True

end GGSG19TopThree
