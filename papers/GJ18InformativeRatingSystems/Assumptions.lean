import GJ18InformativeRatingSystems.MainTheorems

/-!
# Paper Assumptions: GJ18 Informative Rating Systems

This file records source theorem conditions and explicitly documented
large-deviation regularity conditions used by the compact review surface.
The canonical Theorem 1 endpoint uses the source model's positive match rates,
monotone scores, and full finite ordinal rating support.
-/

namespace GJ18InformativeRatingSystems

open EconCSLib.Probability

/-- Sellers receive positive asymptotic match/sample rates. -/
-- audit-premise: hgHi : 0 < sampleRate hi
-- audit-premise: hgLo : 0 < sampleRate lo
-- audit-premise: hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ
abbrev assumption_positive_match_rates {Seller : Type*}
    (sampleRate : Seller → ℝ) : Prop :=
  ∀ θ : Seller, 0 < sampleRate θ

/-- Integer-rate helper rows require positive integer sample rates. -/
-- audit-premise: hgHi : 0 < gHi
-- audit-premise: hgLo : 0 < gLo
abbrev assumption_positive_integer_sample_rates (gHi gLo : ℕ) : Prop :=
  0 < gHi ∧ 0 < gLo

/-- Common-dual large-deviation helper rows use nonpositive dual parameters. -/
-- audit-premise: hz : z ≤ 0
-- audit-premise: hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0
abbrev assumption_nonpositive_common_dual_parameters {Pair : Type*}
    (z : Pair → ℝ) : Prop :=
  ∀ p : Pair, z p ≤ 0

/-- Auxiliary Appendix C route exposes the source threshold minimizer condition. -/
-- audit-premise: hthreshold_min : ∀ b : ℝ, M.pairwiseRateObjective sampleRate hi lo a ≤ M.pairwiseRateObjective sampleRate hi lo b
abbrev assumption_pairwise_threshold_minimizer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (a : ℝ) : Prop :=
  ∀ b : ℝ,
    M.pairwiseRateObjective sampleRate hi lo a ≤
      M.pairwiseRateObjective sampleRate hi lo b

/-- Finite-support lower-bound helper rows use positive and negative score witnesses. -/
-- audit-premise: hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos
-- audit-premise: hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0
abbrev assumption_two_sided_score_witnesses
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (gHi gLo : ℕ) : Prop :=
  ∃ samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating),
    0 < twoSampleRateBlockScore M gHi gLo samplePos ∧
      twoSampleRateBlockScore M gHi gLo sampleNeg < 0

/-- Source rating scores are monotone in the finite ordinal rating level. -/
-- audit-premise: hscore_mono : Monotone M.score
abbrev assumption_monotone_rating_scores {Rating : Type*} [Preorder Rating]
    (score : Rating → ℝ) : Prop :=
  Monotone score

/-- The canonical finite ordinal source endpoint uses full rating-law support. -/
-- audit-premise: hfull_support : M.fullSupport
abbrev assumption_full_finite_ordinal_rating_support
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) : Prop :=
  M.fullSupport

/-- Compatibility real-rate wrappers expose the source score range. -/
-- audit-premise: hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r
-- audit-premise: hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh
-- audit-premise: hscore_lt : M.score rLow < M.score rHigh
abbrev assumption_score_range_and_strict_span {Rating : Type*}
    (score : Rating → ℝ) (rLow rHigh : Rating) : Prop :=
  (∀ r : Rating, score rLow ≤ score r) ∧
    (∀ r : Rating, score r ≤ score rHigh) ∧
      score rLow < score rHigh

end GJ18InformativeRatingSystems
