# Algorithmic Monoculture and Social Welfare

## Source Version

- Paper: *Algorithmic Monoculture and Social Welfare*
- Authors: Jon Kleinberg and Manish Raghavan
- Version formalized: arXiv:2101.05853
- Source URL: https://arxiv.org/abs/2101.05853
- PDF URL: https://arxiv.org/pdf/2101.05853
- Accessed: 2026-04-23

Local cached source artifacts for active formalization:

- `KR21Monoculture/sources/2101.05853.pdf`
- `KR21Monoculture/sources/2101.05853.html`
- `KR21Monoculture/sources/2101.05853.txt`

These source artifacts are intentionally ignored by git. Use the cached local
files first for theorem-number and definition comparisons; use the arXiv URLs
only to refresh or verify the source version.

## Central Theorem File

- `KR21Monoculture/MainTheorems.lean`

That file contains the paper-facing theorem wrappers. Detailed definitions and
proof infrastructure live in the other files in this folder.

## Dependency DAG

- `KR21Monoculture/DependencyDAG.tex`
- `KR21Monoculture/DependencyDAG.pdf`

The DAG tracks the paper-level proof flow and uses the project convention:
green rectangles for fully formalized results, yellow rounded rectangles for
fully formalized lemmas, blue ellipses for model/definition nodes, and dashed
gray rectangles for pending results.  It is intentionally paper-facing: it now
contains every named paper definition, lemma, and theorem, while internal
finite-certificate and continuous-instantiation layers are documented in the
status table below and in the Lean files.

## Theorem Status

Current Theorem 6 concrete continuous-density endpoint:
`paper_theorem6_threeCandidate_prefersWeakerCompetition_of_scoreSpace_density_t_lt_one`.
It proves the three-candidate continuous RUM endpoint on the concrete score
space `ℝ³` for a normalized positive strictly well-ordered score density and
`0 ≤ t < 1`.  The proof now derives the induced ranking laws by ranking raw and
contracted scores, proves event measurability from the rank maps, proves the
Lebesgue-positive lambda source regions and corrected-top region by explicit
open boxes, discharges the finite source-integral side conditions from
normalization, and uses the concrete coordinate swaps.

Concrete three-score-space utilities are exposed as
`paper_theorem6_scoreSpace`, `paper_theorem6_score1`,
`paper_theorem6_score2`, `paper_theorem6_score3`,
`paper_theorem6_scoreSwap12_measurePreserving_volume`,
`paper_theorem6_scoreSwap23_measurePreserving_volume`, and
`paper_theorem6_scoreDensity_isProbabilityMeasure_of_lintegral_eq_one`.  The
normalization bridge also proves the finite source-integral side conditions via
`paper_theorem6_scoreDensity_setLIntegral_ne_top_of_lintegral_eq_one`, and
`paper_theorem6_normalizedScoreRankingPMF` exposes the normalized continuous
ranking law used by the final theorem.

Current RUM status: Appendix C Theorem 8 is now closed; the remaining
RUM-side paper blockers are Theorem 7's probability/Fubini bridge and Appendix
A Theorem 5 before the paper-level Theorem 2 wrapper.  Appendix C Theorem 7 now follows the
paper's three Laplace regions through the C.3 split-integral identities and
derivative signs via
`paper_theorem7_laplacian_conditional_derivative_integral_ratios`.  Theorem 8
now has the paper's C.6 -> C.9 -> C.10/Sampford scalar proof skeleton in
`paper_theorem8_gaussian_c6_formula_positive_of_sampford_mills`, with the C.6
left-hand side, paper `g(t)`, and C.8 positive prefactor exposed explicitly.
For the paper's concrete interval-integral `erf`, Lean now proves the derivative,
left-tail limit, positivity of `1 + erf`, the C.7 rational-term limit, the
paper `J(t)` definition, integrability of its left-half-line integrand, and
the resulting `J(t)` left-tail limit and derivative.  The concrete Mills ratio
`R(t)=exp(t^2/2)∫_t^∞ exp(-x^2/2)dx` is now defined and the paper's
change-of-variables identity `R(-sqrt(2)t)=sqrt(pi/2)g(t)` is proved.  The
C.8 quotient-rule derivative and its factorization into the positive prefactor
times the C.9 bracket are formalized; this exposed a typographical mismatch in
the paper's displayed prefactor, so Lean uses the algebraically correct
positive factor that exactly yields C.9.  The Mills-tail derivative and Mills
ratio derivative are also formalized.  Lean now proves Sampford's cited lower
comparison for the concrete Gaussian Mills ratio by defining
`(sqrt(t^2+4)-t)/2`, proving the associated gap has negative derivative and
vanishes at `+∞`, and deriving the scalar quadratic Mills inequality and
Sampford derivative bound from it.  Consequently, the concrete C.6 scalar
positivity theorem is now unconditional:
`paper_theorem8_gaussian_c6_formula_positive_for_concrete_mills_erf_and_j_unconditional`.
The C.5-to-C.6 quotient-rule bridge is also formalized as
`paper_theorem8_gaussian_conditional_integral_ratio_hasDerivAt_pos`, and the
original-cutoff wrapper
`paper_theorem8_gaussian_conditional_integral_ratio_at_hasDerivAt_pos`, proving
that the Gaussian conditional integral ratio has positive derivative for every
`x_i > x_j` and cutoff `a`.  Lean now also closes the paper's Gaussian
PDF/CDF layer at variance `1/2`: `paper_theorem8_gaussian_pdf_eq_gaussianPDFReal_half`
identifies the density with Mathlib's Gaussian PDF, `paper_theorem8_gaussianReal_Iic_eq_cdf`
identifies the CDF with Mathlib Gaussian left-half-line mass,
`paper_theorem8_gaussian_integral_shift_split` proves the paper's shifted
numerator split into the `erf` tail plus `J`, and
`paper_theorem8_gaussian_pair_numerator_measure_eq_integral` /
`paper_theorem8_gaussian_product_conditional_ratio_at_eq_pdf_cdf` prove the
canonical product-measure Fubini bridge.  Lean now also closes the exact
source-syntax probability wrapper: strict boundary events are related to the
weak integral bridge by Gaussian no-atom lemmas, and the source proof's WLOG
normalization from arbitrary standard deviation `σ > 0` to canonical variance
`1/2` is formalized by `paper_theorem8_gaussianReal_map_canonical_scale`,
`paper_theorem8_gaussian_pair_measure_std_strict_numerator_eq_scaled`,
`paper_theorem8_gaussian_pair_measure_std_strict_denominator_eq_scaled`, and
`paper_theorem8_gaussian_product_strict_conditional_ratio_at_std_eq_scaled`.
The final paper-facing endpoint is
`paper_theorem8_gaussian_product_strict_conditional_ratio_at_std_hasDerivAt_pos`,
which proves the strict conditional probability ratio has positive derivative
for independent Gaussian scores with arbitrary `σ > 0`, `x_i > x_j`, and cutoff
`a`.

Validation note on Appendix C / Lemma 1: the paper's strict pointwise Definition
4 is correct for Gaussian noise but false for Laplacian noise.  Laplacian noise
is globally weakly well-ordered, and it is strictly well-ordered on the
interval-overlap region.  The paper does not state an explicit overlap or
positive-measure repair assumption.  However, the downstream Lemma 3 density
swap argument appears to use only the weak comparison
`f_H(r) <= f_H(swapi(r))`; Theorem 6 gets strictness from the separate
monotonicity/support ingredients.  See the appendix note below for the detailed
audit and the recommended formalization repair.

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Appendix C Definition 4, well-ordered noise | `StrictlyWellOrderedNoise`, `WeaklyWellOrderedNoise` | formalized | `KR21Monoculture/RUM.lean`, `KR21Monoculture/MainTheorems.lean` | None |
| Appendix C Lemma 1, Gaussian well-ordered noise | `paper_lemma1_gaussian_strictlyWellOrdered`, `gaussianNoiseKernel_strictlyWellOrdered` | formalized | `KR21Monoculture/RUM.lean`, `KR21Monoculture/MainTheorems.lean` | None; positive Gaussian scale `0 < κ`; normalizing constants omitted because they cancel in the product inequality |
| Appendix C Lemma 1, Laplacian well-ordered noise | `paper_lemma1_laplacian_weaklyWellOrdered`, `paper_lemma1_laplacian_strictlyWellOrdered_of_overlap`, `paper_lemma1_laplacian_not_strictlyWellOrdered` | partially formalized | `KR21Monoculture/RUM.lean`, `KR21Monoculture/MainTheorems.lean` | Validated with correction; the weak inequality is formalized for `0 ≤ λ`, and strictness is proved on the interval-overlap region.  The paper's global strict pointwise `>` Definition 4 is false for the Laplacian kernel, with counterexample `a=10, b=9, c=1, d=0`.  The paper does not explicitly assume overlap; the downstream Lemma 3 use appears weak, so the natural repair is to weaken the Definition-4 hypothesis needed by Lemma 3/Theorem 6 rather than add an overlap assumption. |
| Appendix C contraction cannot create inversions | `paper_appendixC_contraction_preserves_weak_order`, `paper_appendixC_contraction_preserves_strict_order`, `paper_appendixC_contraction_top_first_of_original_top_first`, `paper_appendixC_contraction_bottom_first_imp_original_bottom_first`, `rum3_contract_bottom_first_imp_original_bottom_first_strict_of_t_lt_one` | formalized | `KR21Monoculture/RUM.lean`, `KR21Monoculture/MainTheorems.lean` | None; status note: deterministic geometry formalized |
| Appendix C monotonicity step for top candidate | `paper_monotonicity_top_of_coupling`, `paper_theorem6_monotonicity_top_of_measure_coupling`, `rum3_monotonicity_top_of_measure_coupling`, `rum3Score_correctedTop_volume_ne_zero_of_t_lt_one` | formalized with caveat | `DecisionCore/FiniteExpectation.lean`, `KR21Monoculture/RUM.lean`, `KR21Monoculture/MainTheorems.lean` | Previous status: finite, continuous, and concrete score-space steps formalized; none beyond the final theorem's normalized positive density and strict-value assumptions |
| Appendix C Lemma 2, bottom-candidate contraction probability inequality | `paper_lemma2_bottom_of_coupling`, `paper_lemma2_bottom_of_measure_coupling`, `rum3_lemma2_bottom_of_measure_coupling`, `rum3DeltaCertificate_of_withDensity_rankByScores_contraction_facts_of_t_lt_one`, `pmfProb_le_of_imp` | formalized with caveat | `DecisionCore/FiniteExpectation.lean`, `KR21Monoculture/RUM.lean`, `KR21Monoculture/MainTheorems.lean` | Previous status: finite, continuous, and concrete rank-by-score coupling steps formalized; none beyond the final theorem's normalized positive density and strict-value assumptions |
| Appendix C Lemma 3, middle-candidate delta comparison | `paper_lemma3_middle_of_measure_transition_mass`, `paper_lemma3_deltaTransition_measureProb_le_of_withDensity_score_facts`, `paper_theorem6_deltaCertificate_of_withDensity_score_contraction_facts`, `rum3_deltaTransition_withDensity_measure_le_of_score_facts`, `paper_lemma3_swapi_middle_transition_geometry`, `paper_lemma3_swapi_density_le_of_weaklyWellOrdered` | formalized with caveat | `KR21Monoculture/RUM.lean`, `KR21Monoculture/MainTheorems.lean`, `EconCSLib/Foundations/Probability/MeasureInequalities.lean` | Previous status: continuous transition algebra, score-level contraction/`swapi` geometry, with-density change-of-variables mass dominance, event measurability, and concrete source-region facts formalized; none beyond the final theorem's normalized positive density and strict-value assumptions |
| Appendix C Theorem 6, three-candidate RUM weaker-competition payoff algebra | `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_scoreSpace_density_t_lt_one`, `paper_theorem6_threeCandidate_prefersWeakerCompetition_of_withDensity_rankByScores_facts_of_t_lt_one`, `paper_theorem6_lambdaCertificate_of_cross_withDensity_score_facts_and_wrong_pos`, `paper_theorem6_deltaCertificate_of_withDensity_score_contraction_facts`, `paper_theorem6_normalizedScoreRankingPMF`, `paper_theorem6_scoreSwap12_measurePreserving_volume`, `paper_theorem6_scoreSwap23_measurePreserving_volume`, `paper_theorem6_scoreDensity_isProbabilityMeasure_of_lintegral_eq_one`, `paper_theorem6_scoreDensity_setLIntegral_ne_top_of_lintegral_eq_one`, `RUM3Theorem6Certificate`, `RUM3DeltaCertificate`, `RUM3LambdaCertificate` | formalized with caveat | `KR21Monoculture/RUM.lean`, `KR21Monoculture/MainTheorems.lean`, `EconCSLib/Foundations/Probability/MeasureInequalities.lean` | Formalized concrete continuous RUM endpoint; currently assumes a measurable positive strictly well-ordered normalized density, `x₃ < x₂ < x₁`, and `0 ≤ t ≤ 1` with `t < 1`.  This is conservative for Gaussian and too strong for direct Laplacian instantiation; the paper proof's Lemma 3 density step only appears to need weak well-ordering, while strict payoff inequality comes from separate support/monotonicity facts. |
| Appendix A Theorem 5, RUMs satisfy Definition 1 | not yet paper-facing | not formalized | pending | differentiability/asymptotic optimality/full-removal monotonicity for continuous RUM families |
| Appendix C Theorem 7, Laplacian conditional derivative | `paper_theorem7_laplacian_conditional_derivative_integral_ratios`, `paper_theorem7_laplacian_integralRatio_derivative_cases`, `paper_theorem7_laplacian_case1_integral_ratio`, `paper_theorem7_laplacian_case2_integral_ratio`, `paper_theorem7_laplacian_case3_integral_ratio`, `paper_theorem7_laplacian_conditional_derivative_closed_forms` | formalized with caveat | `KR21Monoculture/RUM.lean`, `KR21Monoculture/MainTheorems.lean` | Previous status: formalized at C.3 split-integral layer; does not yet build the full random-variable probability space/Fubini bridge from `Pr[Xi > Xj | Xi < a, Xj < a]` to equation (C.3); split-integral derivative cases are stated on region interiors, with the closed-form layer covering the paper's algebraic endpoint formulas |
| Appendix C Theorem 8, Gaussian conditional derivative | `paper_theorem8_gaussian_product_strict_conditional_ratio_at_std_hasDerivAt_pos`, `paper_theorem8_gaussian_product_strict_conditional_ratio_at_std_eq_scaled`, `paper_theorem8_gaussian_pair_measure_std_strict_numerator_eq_scaled`, `paper_theorem8_gaussian_pair_measure_std_strict_denominator_eq_scaled`, `paper_theorem8_gaussian_product_strict_conditional_ratio_at_hasDerivAt_pos`, `paper_theorem8_gaussian_product_strict_conditional_ratio_at_eq_pdf_cdf`, `paper_theorem8_gaussian_pair_strict_numerator_measure_eq_integral`, `paper_theorem8_gaussian_pair_strict_denominator_measure_eq`, `paper_theorem8_gaussianReal_map_canonical_scale`, `paper_theorem8_gaussian_pdf_cdf_ratio_at_hasDerivAt_pos`, `paper_theorem8_gaussian_integral_shift_split`, `paper_theorem8_gaussian_c6_formula_positive_for_concrete_mills_erf_and_j_unconditional`, `paper_theorem8_sampford_mills_bound_concrete`, `paper_theorem8_mills_quadratic_bound_concrete`, `paper_theorem8_mills_ratio_value_relation`, `paper_theorem8_gaussian_j_hasDerivAt_concrete`, `paper_theorem8_erf_hasDerivAt`, `paper_theorem8_gaussian_integral_Iic_eq_erf` | formalized | `KR21Monoculture/RUM.lean`, `KR21Monoculture/MainTheorems.lean` | None; none beyond source hypotheses `0 < σ` and `x_j < x_i`; strict boundary erasure, arbitrary-`σ` scaling, density/Fubini, and Sampford/Mills layers are closed |
| Theorem 2, Gaussian/Laplacian three-candidate RUMs satisfy Theorem 1 conditions | not yet paper-facing | not formalized | pending | depends on Theorems 5, 7, 8 and the Lemma 1 Laplacian strict-well-order caveat |
| Definitions 2 and 3, independent reranking and weaker competition | `Model.PrefersIndependentReranking`, `Model.PrefersWeakerCompetition` | formalized | `KR21Monoculture/PaperDefinitions.lean` | None |
| First-choice probability decomposition of independent reranking | `prefersIndependentReranking_iff_firstChoiceGapMassSum_pos` | formalized | `KR21Monoculture/FirstChoiceDecomposition.lean` | None |
| First-choice probability decomposition of weaker competition | `prefersWeakerCompetition_iff_firstChoiceCollisionDiffSum_pos` | formalized | `KR21Monoculture/FirstChoiceDecomposition.lean` | None |
| Appendix-E top-two expansion and ordered-pair bracket algebra for independent reranking | `MallowsSpec.firstChoiceGapWeight_eq_sum_firstSecondWeight`, `MallowsSpec.independent_weight_sum_eq_pair_sum`, `MallowsSpec.independentPairTerm_add_swap`, `MallowsSpec.independent_weight_sum_pos_of_rankFactorization` | formalized | `KR21Monoculture/MallowsPairwise.lean` | None; finite Mallows fibers are constructed by `MallowsSpec.rankFactorization` |
| Theorem 3, rank-factorized center and prefix first-choice dominance | `MallowsComparison.paper_theorem3_centerFirstProb_lt_of_rankFactorization`, `MallowsComparison.paper_theorem3_firstWeightPrefix_cross_lt_of_rankFactorization`, `MallowsComparison.paper_theorem3_weaker_center_cross_weight_summand_pos_of_rankFactorization` | formalized | `KR21Monoculture/MainTheorems.lean` | None; backward-compatible wrappers take rank-factorization inputs; use `MallowsSpec.rankFactorization` for the assumption-free finite Mallows instance |
| Theorem 3, pointwise Mallows route via cleared finite sums | `MallowsComparison.paper_theorem3_pointwise_finite_mallows_sum` | formalized | `KR21Monoculture/MainTheorems.lean` | None; strict center ordering and the three cleared finite Mallows inequalities |
| Theorem 3, rank-factorized independent-reranking and weaker-competition route | `MallowsComparison.paper_theorem3_pointwise_rankFactorization`, `MallowsComparison.cross_weight_sum_pos_of_rankFactorization`, `candidateRankCrossConditionalGapSum_pos`, `candidateRankWeightedAverage_strictAnti` | formalized | `KR21Monoculture/MainTheorems.lean`, `KR21Monoculture/MallowsPairwise.lean` | None; strict center ordering, `0 < n`, `qA < qH`, and both `q < 1`; the finite Mallows `RankFactorization` is constructed by `MallowsSpec.rankFactorization` |
| Finite Mallows top-one/top-two fiber factorization | `MallowsSpec.rankFactorization`, `reflFirstWeight_eq_rank_mul_zero`, `reflFirstSecondWeight_eq_rank_mul_zero_one_of_lt`, `reflFirstSecondWeight_swap_eq_rank_mul_zero_one_of_lt` | formalized | `KR21Monoculture/Kendall.lean`, `KR21Monoculture/MallowsPairwise.lean` | None |
| Appendix F Lemma 4, MLR weighted-average comparison | `paper_lemma4_weighted_average_lt_of_cross_ratio`, `paper_appendixE_candidateRankWeightedAverage_strictAnti`, `candidateWeightedAverage_cross_pos_of_pairwise` | formalized with caveat | `KR21Monoculture/MainTheorems.lean`, `KR21Monoculture/MallowsPairwise.lean` | Previous status: formalized in denominator-cleared form; Lean states the paper's `pᵢ/qᵢ` monotonicity as cross-products, with one strict pair |
| Appendix F Lemma 5, Mallows top-two order-swap ratio | `reflFirstSecondWeight_eq_rank_mul_zero_one_of_lt`, `reflFirstSecondWeight_swap_eq_rank_mul_zero_one_of_lt`, `MallowsSpec.firstSecondWeight_eq_rank_mul_centerFirstSecond_of_lt`, `MallowsSpec.firstSecondWeight_swap_eq_q_mul_rank_mul_centerFirstSecond_of_lt` | formalized | `KR21Monoculture/MallowsPairwise.lean` | None; Lean uses inverse Mallows parameter `q = φ⁻¹`, so the ratio appears as an extra factor of `q` on the inverted top-two order |
| Appendix F Lemma 6, Mallows first-choice probability formula | `reflFirstWeight_eq_rank_mul_zero`, `MallowsSpec.firstWeight_eq_rank_mul_centerFirst`, `MallowsSpec.partition_eq_rankPowerSum_mul_centerFirstWeight` | formalized | `KR21Monoculture/MallowsPairwise.lean` | None; exposed as unnormalized weights plus the partition formula |
| Appendix F Lemma 7, first human mover beats second human mover under Mallows | `paper_lemma7_mallows_first_mover_gt_second_human`, `MallowsSpec.firstMoverUtility_gt_secondMoverIndependent_same_of_rankFactorization`, `expectedFirstMover_sub_secondMoverIndependent_eq_sum_firstChoiceProb_mul_firstChoiceGapMass` | formalized | `KR21Monoculture/MainTheorems.lean`, `KR21Monoculture/MallowsFamily.lean`, `KR21Monoculture/FirstChoiceDecomposition.lean` | None; Lean proves the fixed-law utility statement with inverse Mallows parameter `q < 1` and strict center-ordered values |
| Appendix F Lemma 8, Mallows pairwise correct-ranking probability increases with accuracy | `paper_lemma8_mallows_pairCorrectProb_lt`, `paper_lemma8_reduced_pairPositionCorrectProb_lt_of_q_lt`, `paper_lemma8_mallows_pairCorrectProb_lt_of_pairPositionReduction`, `MallowsSpec.pairPositionReduction_of_center_lt`, `reflPairPositionReduction_of_lt`, `reflPairPositionReduction_zero_last`, `reflPairPositionReduction_succ_succ`, `reflPairPositionReduction_castSucc_castSucc`, `reflEndpointMiddleCancellation`, `pairCorrectProb_lt_of_pairWeight_cross`, `pairWeight_cross_pos_of_pairPositionReduction` | formalized | `KR21Monoculture/MainTheorems.lean`, `KR21Monoculture/MallowsPairwise.lean`, `KR21Monoculture/Mallows.lean` | None; no cancellation certificate remains; closed wrapper assumes the paper's same center ranking, a center-ordered pair, and inverse Mallows parameters `Mmore.q < Mless.q` |
| Theorem 4, multi-firm Mallows optimal sequence | `paper_theorem4_all_human_sequence_optimal_of_stepwise_dominance`, `paper_theorem4_human_unique_at_each_history_of_strict_stepwise_dominance`, `paper_theorem4_remaining_utility_dominance_of_bestInSetWeight_cross`, `paper_theorem4_remaining_utility_dominance_of_bestInSetWeight_mlr`, `paper_theorem4_remaining_utility_dominance_of_prefix_first_hit`, `paper_theorem4_remaining_utility_dominance_of_firstChoiceBracketSums`, `paper_theorem4_remaining_utility_dominance_of_firstChoiceWeighted`, `paper_theorem4_remaining_utility_dominance_of_firstChoiceAdjacentBoundary`, `paper_theorem4_remaining_utility_dominance_of_prefix_kendall_layer_average`, `paper_theorem4_remaining_utility_dominance_of_adjacent_prefix_kendall_layer_average`, `paper_theorem4_remaining_utility_dominance_of_adjacent_stochastic_dominance`, `paper_theorem4_remaining_utility_dominance_of_weakBruhat_coupling`, `paper_theorem4_remaining_utility_dominance_of_kendall_layer_average`, `paper_theorem4_remaining_utility_dominance_of_adjacent_kendall_layer_average`, `paper_theorem4_bestInSetWeight_univ_sdiff_singleton_eq_bestAfterRemovalWeight`, `paper_theorem4_bestInSetWeight_cross_univ_sdiff_singleton_of_rankFactorization`, `paper_theorem4_mallows_cosingleton_remaining_utility_dominance_of_q_le`, `paper_theorem4_reflMallowsBestInSetWeightMLR_two_of_qLess_lt_one`, `paper_theorem4_mallows_four_candidate_remaining_utility_dominance_of_q_le`, `paper_theorem4_mallows_four_candidate_all_human_sequence_optimal_of_q_le`, `paper_theorem4_mallows_three_candidate_remaining_utility_dominance_of_q_le`, `paper_theorem4_human_weakly_dominates_all_histories_of_remaining_utility_dominance`, `paper_theorem4_mallows_all_human_sequence_optimal_of_adjacent_stochastic_dominance`, `paper_theorem4_mallows_three_candidate_all_human_sequence_optimal_of_q_le`, `paper_theorem4_two_remaining_utility_dominance_of_pairwise`, `paper_theorem4_mallows_two_remaining_utility_dominance_of_q_le`, `paper_theorem4_mallows_two_remaining_strict_utility_dominance_of_q_lt`, `paper_theorem4_mallows_small_remaining_utility_dominance_of_q_le`, `paper_theorem4_mallows_centerConvex_remaining_utility_dominance_of_q_le`, `paper_theorem4_mallows_pairwise_weak_dominance_of_q_le`, `paper_theorem4_mallows_pairwise_strict_dominance_of_q_lt`, `paper_theorem4_mallows_all_human_sequence_optimal_of_remaining_utility_dominance`, `paper_theorem4_mallows_human_unique_at_each_history_of_remaining_utility_dominance` | conditional | `KR21Monoculture/Sequential.lean`, `KR21Monoculture/MainTheorems.lean` | Current status: all histories with at most two remaining candidates, all center-convex remaining intervals, all co-singleton remaining histories with `algorithm.q < 1`, all nonempty histories in the three-candidate Mallows universe, four-candidate identity-center fiber MLR with `qLess < 1`, all nonempty histories in the four-candidate Mallows universe with `algorithm.q < 1`, and the three- and four-candidate all-human weak optimality theorems closed. Lemma 8 supplies weak/strict pairwise Mallows dominance for `q_H ≤ q_A` / `q_H < q_A`, but pairwise correctness is not by itself the arbitrary nonconvex remaining-set lift. The arbitrary-history bridge is reduced to best-in-set fiber MLR (`ReflMallowsBestInSetWeightMLR`) or prefix first-hit dominance; the newest arbitrary route proves first-choice weighted/adjacent-boundary conditional bridges and now deletes absent center extremes through `ReflMallowsBestInSetPrefixCutDominance.succ_of_extremeWeighted` and `ReflMallowsBestInSetPrefixCutDominance.of_extremeWeighted`. The remaining open arbitrary-size step is the narrower endpoint-present target `ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes`, likely via adjacent-hole/block cancellation, or alternatively arbitrary identity-center fiber MLR / prefix-layer / adjacent-stochastic dominance. Strict uniqueness is stated only at nonterminal histories where at least two candidates remain. |
| Appendix D Theorem 9, Mallows satisfies Definition 1 | `paper_theorem9_concrete_mallows_family_assumptions`, `paper_theorem1_paperAssumptions_from_mallows_family`, `MallowsAccuracyFamilySpec.theorem1PaperAssumptions` | formalized | `KR21Monoculture/MallowsFamily.lean`, `KR21Monoculture/MainTheorems.lean` | None; strict center-ordered values and `0 < n` in Lean's `Candidate n` indexing |
| Concrete Mallows family bridge to Theorem 1 | `paper_theorem1_concrete_mallows_family`, `concreteMallowsAccuracyFamilySpec`, `concreteMallowsSpec_asymptotic_first_dominance`, `paper_definition1_concreteMallowsSpec_asymptotic_first_dominance`, `paper_definition1_concreteMallowsSpec_atom_continuity`, `MallowsAccuracyFamilySpec.theorem1PaperAssumptions`, `MallowsAccuracyFamilySpec.prefersIndependentReranking`, `MallowsAccuracyFamilySpec.prefersWeakerCompetition`, `MallowsAccuracyFamilySpec.theorem1RemovalMonotonicityAt`, `MallowsComparison.paper_definition1_firstMoverUtility_strict_of_rankFactorization`, `MallowsComparison.paper_definition1_expectedBestAfterRemoval_le_of_rankFactorization`, `mallowsInverseAccuracyQ_strictAnti` | formalized | `KR21Monoculture/MallowsFamily.lean`, `KR21Monoculture/MainTheorems.lean` | None; fixed-parameter Definitions 2 and 3 are discharged by the rank-factorized Mallows theorem; concrete Mallows atomwise continuity, asymptotic first dominance, and first-mover/singleton-removal monotonicity are proved |
| Theorem 3, reduced product-sign route | `MallowsComparison.paper_theorem3_pointwise_reduced_product_certificate` | formalized | `KR21Monoculture/MainTheorems.lean` | None; strict center ordering and non-center finite Mallows sign inequalities |
| Equivalence of normalized candidate sums and cleared finite sums | `MallowsComparison.paper_theorem3_finite_sum_certificate_from_candidate_sums` | formalized | `KR21Monoculture/MainTheorems.lean` | None; strict center ordering and `CandidateSumCertificate` inputs |
| Theorem 1, shared-algorithm game semantics | `Model.secondMoverEU`, `Model.welfareOrdered`, `Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU` | formalized | `KR21Monoculture/Game.lean`, `KR21Monoculture/WelfareDecomposition.lean` | None |
| Theorem 1, Definition 2 initial crossing side | `paper_theorem1_initial_f_lt_g_from_definition2`, `AccuracyFamily.theorem1_f_lt_g_of_paperHypotheses_equalAccuracy`, `AccuracyFamily.theorem1_f_lt_g_of_prefersIndependent_equalAccuracy` | formalized | `KR21Monoculture/MainTheorems.lean`, `KR21Monoculture/Theorem1.lean` | None; equal algorithm/human accuracy and Definition 2 independent reranking at `θH`; no Definition 3-at-equality premise is needed |
| Theorem 1, left endpoint after Definition 2 | `paper_theorem1_exists_right_initial_f_lt_g_from_independent_reranking_and_continuity`, `paper_theorem1_exists_right_initial_f_lt_g_from_definition2_and_continuity`, `AccuracyFamily.theorem1_exists_right_initial_f_lt_g_of_prefersIndependent_and_atom_continuity`, `AccuracyFamily.theorem1_exists_right_initial_f_lt_g_of_atom_continuity` | conditional | `KR21Monoculture/MainTheorems.lean`, `KR21Monoculture/Theorem1.lean` | Previous status: formalized conditional bridge; Definition 2 at `θH` and atomwise continuity of the finite ranking law at `θH` |
| Theorem 1, Definition 3 weaker-competition side | `paper_theorem1_g_lt_h_from_definition3`, `AccuracyFamily.theorem1_g_lt_h_of_paperHypotheses` | formalized | `KR21Monoculture/MainTheorems.lean`, `KR21Monoculture/Theorem1.lean` | None; `Model.PaperHypotheses (F.modelAt θA θH)` |
| Theorem 1, inequality (5) from finite-removal monotonicity | `paper_theorem1_inequality5_from_removal_monotonicity`, `paper_theorem1_inequality5_from_monotonicity`, `AccuracyFamily.Theorem1RemovalMonotonicityAt`, `AccuracyFamily.Theorem1MonotonicityAt` | conditional | `KR21Monoculture/MainTheorems.lean`, `KR21Monoculture/Theorem1.lean` | Previous status: formalized conditional bridge; finite-removal monotonicity certificate not yet derived from a full formal Definition 1 structure |
| Theorem 1, finite continuity bridges for `f`, `g`, `f - g`, and `f < h` persistence | `paper_theorem1_f_continuous_from_atom_continuity`, `paper_theorem1_g_continuous_from_atom_continuity`, `paper_theorem1_f_sub_g_continuousOn_from_atom_continuity`, `paper_theorem1_f_lt_h_persists_right_from_atom_continuity`, `AccuracyFamily.theorem1_f_sub_g_continuousOn_of_atom_continuity`, `AccuracyFamily.theorem1_f_lt_h_persists_right_of_atom_continuity` | conditional | `DecisionCore/EpsilonContinuity.lean`, `DecisionCore/IntervalCrossing.lean`, `KR21Monoculture/MainTheorems.lean`, `KR21Monoculture/Theorem1.lean` | Previous status: formalized conditional bridge; requires atomwise epsilon-delta continuity of the finite ranking law `fun θ => ((F.dist θ) π).toReal` at the relevant point or throughout `[lo, hi]` |
| Theorem 1, final global/interval-analytic/sign-change/atom-local/local-nudge/right-nudge/payoff bridge to monoculture paradox | `paper_theorem1_from_paper_assumptions`, `paper_theorem1_from_global_analytic_certificate`, `paper_theorem1_from_interval_analytic_certificate`, `paper_theorem1_from_sign_change_nudge_certificate`, `paper_theorem1_from_atom_local_nudge_certificate`, `paper_theorem1_from_local_nudge_certificate`, `paper_theorem1_from_right_nudge_certificate`, `paper_theorem1_from_crossing_certificate`, `AccuracyFamily.theorem1Target_of_paperAssumptions`, `AccuracyFamily.Theorem1PaperAssumptions`, `AccuracyFamily.theorem1Target_of_globalAnalyticCertificate`, `AccuracyFamily.theorem1Target_of_intervalAnalyticCertificate`, `AccuracyFamily.theorem1Target_of_signChangeNudgeCertificate`, `AccuracyFamily.theorem1Target_of_atomLocalNudgeCertificate`, `AccuracyFamily.theorem1Target_of_localNudgeCertificate`, `AccuracyFamily.theorem1Target_of_rightNudgeCertificate`, `AccuracyFamily.theorem1Target_of_crossingCertificate`, `AccuracyFamily.theorem1Target_of_payoffCertificate` | conditional | `DecisionCore/IntervalCrossing.lean`, `KR21Monoculture/MainTheorems.lean`, `KR21Monoculture/Theorem1.lean` | Previous status: formalized conditional bridge; requires `AccuracyFamily.Theorem1PaperAssumptions F` plus `0 < θH`, or one of the narrower certificate structures; the paper-level structure separates Definition 2 at equality, Definition 3 only for `θA > θH`, atomwise continuity, asymptotic dominance, and finite-removal monotonicity |
| Theorem 1, full monoculture paradox existence over Mallows accuracy families | `paper_theorem1_concrete_mallows_family`, `AccuracyFamily.Theorem1Target` | formalized with caveat | `KR21Monoculture/MainTheorems.lean`, `KR21Monoculture/MallowsFamily.lean`, `KR21Monoculture/Family.lean`, `KR21Monoculture/Theorem1.lean` | Previous status: formalized for concrete Mallows; RUM/noisy permutation families beyond Mallows can still instantiate `AccuracyFamily.Theorem1PaperAssumptions F` or `AccuracyFamily.Theorem1GlobalAnalyticCertificate F θH` separately |

## Current Theorem 4 Lift Note

The best-in-set fiber route now includes a verified two-candidate fiber bridge:
`MallowsSpec.bestInSetWeight_pair_eq_pairCorrectWeight`,
`MallowsSpec.bestInSetWeight_pair_eq_pairWrongWeight`,
`MallowsSpec.bestInSetWeight_pair_cross_pos_of_pairPositionReduction`,
`reflMallowsBestInSetWeight_pair_cross_pos`, and
`reflMallowsBestInSetWeight_cross_nonneg_card_le_two`.  This closes the
identity-center best-in-set MLR target for remaining sets of cardinality at most
two using the Appendix F Lemma 8 pair-position machinery.  Combined with the
full-set first-choice cross theorem, this also closes
`reflMallowsBestInSetWeightMLR_one` and the paper-facing
`paper_theorem4_mallows_three_candidate_remaining_utility_dominance_of_bestInSetWeight_mlr`.
The same fiber route now has exact absent-extreme deletion steps:
`reflMallowsBestInSetWeight_eq_tail_of_zero_not_mem`,
`reflMallowsBestInSetWeight_eq_init_of_last_not_mem`,
`reflMallowsBestInSetWeight_cross_nonneg_succ_of_zero_not_mem`,
`reflMallowsBestInSetWeight_cross_nonneg_castSucc_of_last_not_mem`,
`reflMallowsBestInSetWeight_cross_nonneg_of_zero_not_mem`, and
`reflMallowsBestInSetWeight_cross_nonneg_of_last_not_mem`.  These close the
stronger center-convex fiber theorem
`reflMallowsBestInSetWeight_cross_nonneg_centerConvex`.
Co-singleton histories are also closed at the paper-facing expected-utility
level: `paper_theorem4_bestInSetWeight_univ_sdiff_singleton_eq_bestAfterRemovalWeight`
rewrites those best-in-set fibers to `bestAfterRemovalWeight`, and
`paper_theorem4_bestInSetWeight_cross_univ_sdiff_singleton_of_rankFactorization`
/ `paper_theorem4_mallows_cosingleton_remaining_utility_dominance_of_q_le`
apply the existing rank-only best-after-removal MLR theorem.  This route keeps
the geometric side condition `algorithm.q < 1`.  Combining co-singletons with
the existing `card ≤ 2` and center-convex routes closes the four-candidate
remaining-history theorem
`paper_theorem4_mallows_four_candidate_remaining_utility_dominance_of_q_le` and
the corresponding all-human theorem
`paper_theorem4_mallows_four_candidate_all_human_sequence_optimal_of_q_le`.
For the arbitrary-size route, the first-choice decomposition now has a verified
non-monotone branch-bracket algebra layer:
`firstChoiceBranchPayoffSum`, `firstChoiceBranchBracket`,
`candidateRankBranchCross_nonneg_of_diag_pair`, and
`reflMallowsPayoffSum_cross_of_firstChoice_pair_brackets`.  This is intended to
replace the too-strong branch-monotonicity premise in the earlier
first-choice/peel-best steps: arbitrary prefix first-hit branches are not
monotone in the fixed first-choice rank, so the remaining proof should attack
explicit branch brackets instead of adding more finite classifications.  The
individual pair-bracket condition is itself only a sufficient condition and can
be too strong for arbitrary prefix events; the active arbitrary target is now
the weaker aggregate off-diagonal theorem
`candidateRankBranchCross_nonneg_of_diag_pair_sum`, with concrete wrappers
`firstChoiceBranchPayoffSum_prefixCut`,
`firstChoiceBranchPayoffSum_prefixCut_diag_nonneg_of_tail`,
`firstChoiceBranchBracketSum`,
`reflMallowsPayoffSum_cross_of_firstChoice_pair_bracket_sum`, and
`reflMallowsBestInSetPrefixCutSum_cross_of_firstChoice_pair_bracket_sum`.
The tail-packaged prefix step
`reflMallowsBestInSetPrefixCutSum_cross_of_firstChoice_tail_pair_bracket_sum`
reduces the diagonal branch obligations to smaller tail prefix-cut dominance,
leaving the aggregate bracket sum as the main new arbitrary induction target.
The aggregate bracket now has two verified regroupings:
`firstChoiceBranchBracketSum_eq_complementPower` and
`firstChoiceBranchBracketSum_eq_diag_add_weighted`.  The latter proves that
tail diagonal dominance plus the weighted first-choice target
`ReflMallowsBestInSetPrefixCutFirstChoiceWeighted` implies the aggregate
bracket target through
`firstChoiceBranchBracketSum_nonneg_of_diag_weighted` and
`ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum.of_dominance_weighted`.
The full-remaining-set bracket case is closed by
`firstChoiceBranchBracketSum_univ_cut_nonneg`; the analogous weighted target is
closed by `firstChoiceBranchWeighted_univ_cut_nonneg`, with empty/full cut
boundary cases handled by
`firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_lt` and
`firstChoiceBranchWeighted_prefixCut_eq_zero_of_forall_remaining_ge`.  The
weighted target now also has its recursive base case closed by
`ReflMallowsBestInSetPrefixCutFirstChoiceWeighted.zero`, using the concrete
three-candidate pair-pattern lemmas
`firstChoiceBranchWeighted_pair01_cut_one_nonneg`,
`firstChoiceBranchWeighted_pair02_cut_one_nonneg`,
`firstChoiceBranchWeighted_pair02_cut_two_nonneg`, and
`firstChoiceBranchWeighted_pair12_cut_two_nonneg`.  The weighted target also
has the pair-sum identity
`candidateRankWeightedAverage_cross_eq_pair_sum` /
`firstChoiceBranchWeighted_eq_pair_sum`, so the remaining nonconvex successor
case can be attacked as an aggregate cancellation over first-choice pairs.  The
weighted expression is now also packaged as `firstChoiceBranchWeighted`, with
generic antitone and pair-term interfaces
`firstChoiceBranchWeighted_nonneg_of_antitone`,
`firstChoiceBranchWeighted_eq_pair_sum'`, and
`firstChoiceBranchWeighted_nonneg_of_pair_terms`.  A second verified
summation-by-parts view,
`candidateRankWeightedAverage_cross_eq_adjacent_gap_sum` /
`firstChoiceBranchWeighted_eq_adjacent_gap_sum`, rewrites the same target as a
sum of adjacent branch gaps with nonnegative prefix coefficients.  The adjacent
view now has a boundary normal form:
`firstChoiceBranchAdjacentGapCoeff`,
`firstChoiceBranchAdjacentGapCoeff_nonneg`,
`firstChoiceTailRemainingOf_castSucc_eq_succ_of_not_mem`,
`bestInSetPrefixCutIndicator_eq_of_adjacent_cut_not_mem`,
`reflMallowsBestInSetPrefixCutSum_eq_of_adjacent_cut_not_mem`,
`firstChoiceBranchPayoffSum_prefixCut_eq_of_adjacent_not_mem`,
`firstChoiceBranchWeighted_eq_adjacent_gap_sum_boundary`,
`firstChoiceBranchWeighted_adjacentGapTerm_nonneg_of_left_mem_lt`,
`firstChoiceBranchWeighted_adjacentGapTerm_nonneg_of_right_mem_ge`,
`firstChoiceBranchWeighted_adjacentGapTerm_nonneg_of_mem_mem`,
`firstChoiceBranchWeighted_adjacentGapTerm_nonneg`,
`firstChoiceBranchWeighted_prefixCut_nonneg_of_adjacentGapTerms`, and
`firstChoiceBranchWeighted_prefixCut_nonneg_of_no_bad_mixed_adjacent`.  Thus
adjacent outside/outside first-choice gaps are zero, and the easy signed
boundary orientations are nonnegative.  The two hard boundary orientations now
have exact rewrites,
`firstChoiceBranchWeighted_adjacentGapTerm_eq_tail_sub_partition` for
outside-before-good and `firstChoiceBranchWeighted_adjacentGapTerm_eq_neg_tail`
for bad-before-outside; the remaining successor proof is their aggregate
cancellation.  The prefix-cut layer is also tied back to the fiber route by
`reflMallowsBestInSetPrefixCutSum_eq_sum_bestInSetWeight` and
`firstChoiceBranchPayoffSum_prefixCut_eq_sum_bestInSetWeight_of_not_mem`.
The current
pair-sum
workspace has verified prefix-cut bounds
`bestInSetPrefixCutIndicator_nonneg`,
`bestInSetPrefixCutIndicator_le_one`,
`reflMallowsBestInSetPrefixCutSum_nonneg`,
`reflMallowsBestInSetPrefixCutSum_le_partition`,
`firstChoiceBranchPayoffSum_prefixCut_nonneg`,
`firstChoiceBranchPayoffSum_prefixCut_le_partition`, plus direct pair-term
lemmas `firstChoiceBranchWeighted_pairTerm_nonneg_of_remaining_lt_ge`,
`firstChoiceBranchWeighted_pairTerm_eq_zero_of_remaining_lt_lt`,
`firstChoiceBranchWeighted_pairTerm_eq_zero_of_remaining_ge_ge`,
`firstChoiceBranchWeighted_pairTerm_nonneg_of_remaining_lt_notMem`, and
`firstChoiceBranchWeighted_pairTerm_nonneg_of_notMem_remaining_ge`.  The
still-open part is the aggregate cancellation involving outside first-choice
pairs in the weighted successor.
This is now packaged as the recursive interface
`ReflMallowsBestInSetPrefixCutDominance`,
`ReflMallowsBestInSetPrefixCutFirstChoiceBracketSum`,
`ReflMallowsBestInSetPrefixCutFirstChoiceWeighted`,
`ReflMallowsBestInSetPrefixCutFirstChoiceAdjacentBoundary`,
`ReflMallowsBestInSetPrefixCutDominance.succ`,
`ReflMallowsBestInSetPrefixCutDominance.zero`,
`ReflMallowsBestInSetPrefixCutDominance.of_firstChoiceBracketSums`,
`ReflMallowsBestInSetPrefixCutDominance.of_firstChoiceWeighted`,
`ReflMallowsBestInSetPrefixCutFirstChoiceWeighted.of_adjacentBoundary`,
`ReflMallowsBestInSetPrefixCutFirstChoiceAdjacentBoundary.of_weighted`,
`ReflMallowsBestInSetPrefixCutFirstChoiceAdjacentBoundary.zero`,
`reflMallowsBestInSetPrefixSum_cross_of_firstChoiceBracketSums`,
`reflMallowsBestInSetPrefixSum_cross_of_firstChoiceWeighted`,
`expectedBestInSet_le_of_mallows_firstChoiceBracketSums`, and the
weighted bridge `expectedBestInSet_le_of_mallows_firstChoiceWeighted`, with
paper-facing wrappers
`paper_theorem4_remaining_utility_dominance_of_firstChoiceBracketSums` and
`paper_theorem4_remaining_utility_dominance_of_firstChoiceWeighted` plus the
adjacent-boundary wrapper
`paper_theorem4_remaining_utility_dominance_of_firstChoiceAdjacentBoundary`.
This keeps
negative first-choice-pair brackets available for cancellation inside the full
recurrence while narrowing the next open arbitrary-size target to the
adjacent-boundary weighted first-choice successor inequality.
The newest reduction deletes absent center extremes in the prefix-cut induction:
`reflMallowsBestInSetPrefixCutSum_cross_of_extreme_not_mem_from_prev` handles
remaining sets missing either the center-best or center-worst candidate, and
`ReflMallowsBestInSetPrefixCutDominance.succ_of_extremeWeighted` reduces the
same-size successor to the case where both extremes remain and the cut is
nontrivial.  This is now packaged by
`ReflMallowsBestInSetPrefixCutDominance.of_extremeWeighted`; the active open
target is
`ReflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes`, preferably via
adjacent-hole/block cancellation.  Finite counterexample searches through seven
candidates found no counterexample to either the paper-level prefix dominance
or this stronger first-choice weighted target.  If this proof remains open
until a materially stronger model is available, resume from the 2026-05-15
`KR21Monoculture/HANDOFF.md`: it starts with the exact remaining Lean target,
the adjacent-boundary lemmas already available, and the shortcuts that should
not be repeated.  Finish this reduced target first before moving to any other
paper.

## Appendix: Laplacian well-ordering validation note

Appendix C Definition 4 in the source paper defines a noise density `f` to be
well-ordered by the strict pointwise condition
`f(a - c) f(b - d) > f(a - d) f(b - c)` for all `a > b` and `c > d`.
Lemma 1 then claims that both Gaussian and Laplacian noise satisfy this
definition.

The Gaussian claim is valid.  For kernels of the form `exp (-κ x^2)`, the log
product gap reduces to a strictly positive multiple of `(a - b)(c - d)` when
`κ > 0`, so strictness follows from `a > b` and `c > d`.

The Laplacian claim is not valid in this strict global form.  For
`f(x) = exp (-λ |x|)`, strict well-ordering would require
`|a - c| + |b - d| < |a - d| + |b - c|` for every `a > b` and `c > d`.
This inequality can be an equality for separated ordered intervals.  The Lean
counterexample is `a = 10`, `b = 9`, `c = 1`, `d = 0`, where both sides are
`18`, so the two density products are equal.  This is recorded as
`paper_lemma1_laplacian_not_strictlyWellOrdered`.

What Lean proves for Laplacian noise is the strongest globally valid pointwise
statement: weak well-ordering, exposed as
`paper_lemma1_laplacian_weaklyWellOrdered`.  Lean also proves the expected
strict subcase on the interval-overlap region, exposed as
`paper_lemma1_laplacian_strictlyWellOrdered_of_overlap`, under
`b < a`, `d < c`, `b < c`, and `d < a`.

The paper does not appear to state an explicit overlap or positive-measure
repair assumption.  It does assume support `(-∞, ∞)` in Theorem 6 and uses
support everywhere to obtain strict pairwise correctness probabilities, but that
is different from a pointwise overlap condition in Definition 4/Lemma 1.

The downstream proof of Lemma 3 appears to require only the weak density swap
comparison `f_H(r) <= f_H(swapi(r))`, not strict pointwise well-ordering.  The
strict inequality in Theorem 6 is then supplied by separate ingredients:
positive support/monotonicity gives `Δp_1 > 0`, the weak density comparison gives
`Δp_1 >= Δp_2`, and the bottom-candidate contraction comparison gives
`Δp_3 <= 0`.

Recommended formal repair: keep `StrictlyWellOrderedNoise` for Gaussian and
for optional strict overlap lemmas, but route Lemma 3 and the Theorem 6 density
swap through `WeaklyWellOrderedNoise`.  Then Laplacian can instantiate the
Theorem 6 path using the weak global Lemma 1 result plus the paper's separate
support/monotonicity hypotheses, without adding an unstated overlap assumption.
