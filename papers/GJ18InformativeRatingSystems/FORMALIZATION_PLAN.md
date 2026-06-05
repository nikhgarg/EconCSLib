# Formalization Plan: Designing Informative Rating Systems

- Namespace: `GJ18InformativeRatingSystems`
- Publication target: Manufacturing & Service Operations Management 23(3):589-605
  article version, published online 2020 (issue 2021).
- Formalized source target: arXiv 1810.13028 TeX/PDF cache used for
  source-audit text and formalization intake.

## Source Inventory

- Model primitives: seller types `θ`, rating levels `Y`, score function `φ`,
  rating distribution `ρ(θ,y|Y)`, matching rate `g(θ)`, aggregate score
  `x_k(θ)`, pair objective `P_k(θ_1,θ_2)`, and Kendall-style objective `W_k`.
- Theorem `lemhatW` / Theorem 1: large-deviation rate of `1 - W_k` equals a
  minimum over adjacent seller types of
  `inf_a {g(θ_{i+1}) I(a|θ_{i+1}) + g(θ_i) I(a|θ_i)}`.
- Appendix Lemma `lem:problessthan`: pairwise score-comparison error rate from
  a large-deviation/Laplace-principle calculation.
- Appendix Lemma `lem:Pk_LD`: transfers the pairwise score-comparison rate to
  `1 - P_k(θ_1,θ_2)`.
- Final Theorem 1 proof: finite/continuous aggregation from pairwise rates to
  the objective `W_k`, with an adjacent-pair dominance step.

## Initial Proof Strategy

- Use `FiniteRatingLDPModel` for `ρ(θ,y|Y)` and `φ(y)`.
- The current Lean surface closes the source formulas and finite/integer-rate
  Theorem 1 route:
  - `definition_log_mgf_formula`
  - `definition_rate_function_formula`
  - `lemmaC_pairwise_threshold_rate_formula`
  - `lemmaC_equal_sample_pairwise_mgf_product_formula`
  - `lemmaC_equal_sample_pairwise_gap_mean_formula`
  - `lemmaC_two_population_sample_mgf_product_formula`
  - `lemmaC_two_population_sample_chernoff_upper_bound`
  - `lemmaC_two_population_integer_rate_chernoff_upper_certificate`
  - `lemmaC_integer_rate_block_mgf_product_formula`
  - `lemmaC_integer_rate_block_log_mgf_formula`
  - `lemmaC_integer_rate_block_error_rate_from_cramer`
  - `lemmaC_integer_rate_block_error_probability_eq_two_population_probability`
  - `lemmaC_integer_rate_block_source_threshold_rate_from_logMGF_derivatives`
  - `lemmaC_integer_rate_two_population_source_threshold_rate_from_logMGF_derivatives`
  - `lemmaC_pk_complement_error_eq_one_sub_pk_objective`
  - `lemmaC_pk_complement_source_threshold_rate_from_logMGF_derivatives`
  - `source_floor_sample_count_div_tendsto_sampleRate`
  - `source_floor_sample_count_eq_mul_of_nat_sampleRate`
  - `lemmaC_floor_pk_complement_error_rate_from_left_tail`
  - `lemmaC_equal_sample_pairwise_error_rate_from_cramer`
  - `theorem1_finite_ranking_error_upper_bound_from_pair_certificates`
  - `theorem1_finite_ranking_error_exact_rate_from_min_pair_certificate`
  - `theorem1_finite_ranking_error_exact_rate_from_adjacent_pair_min`
  - `theorem1_integer_rate_weighted_objective_oneSub_exact_rate_from_adjacent_logMGF_derivatives`
  - `theorem1_floor_weighted_objective_oneSub_exact_rate_from_nat_sampleRates_adjacent_logMGF_derivatives`
  - `lemmaC_floor_score_gap_rate_from_logMGF_derivative_minimizer`
  - `lemmaC_floor_score_gap_rate_from_logMGF_derivative_threshold_minimizer_of_straddling_support`
  - `theorem1_floor_weighted_objective_oneSub_exact_rate_from_adjacent_logMGF_derivative_minimizers`
  - `theorem1_floor_weighted_objective_oneSub_exact_rate_from_adjacent_logMGF_derivative_threshold_minimizers_of_straddling_support`
  - `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_joint_floor_rating_law`
  - `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_pairwise_threshold_rate_regularity`
  - `lemmaC_pairwise_threshold_rate_top_eq_displayed_objective_of_common_logMGF_derivatives`
  - `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_objective_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds`
  - `theorem1_finite_chain_adjacent_threshold_rate_top_min_eq_displayed_objective_min_of_logMGF_derivatives`
  - `theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_pairwise_threshold_rate_regularity`
  - `theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_expected_score_gap_and_common_extreme_support`
  - `theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_rating_tail_dominance_and_common_extreme_support`
  - `theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_rating_tail_dominance_and_full_support`
  - `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_threshold_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds_of_extended_min_eq`
- The finite/integer-rate route is closed from explicit log-MGF derivative
  witnesses, including finite-type Cramer, the source-threshold equality or
  Fenchel-derived threshold minimizer, the `1 - P_k` algebra, and the finite
  weighted objective `1 - W_n`.
- The source floor-count objective is represented for natural-valued and
  arbitrary real-valued match rates. The strongest arbitrary-real floor-count
  endpoints close the GJ18-specific finite reductions through the support-safe
  extended threshold-rate minimum. The compact pairwise threshold-rate
  regularity package still feeds an auxiliary endpoint, but the main
  source-facing endpoint now derives the common-dual witnesses and pairwise
  support-safe LDP certificates from finite ordinal upper-tail dominance,
  monotone scores, positive match rates, and full finite ordinal rating support.
  The bottom/top atom support used by the lower-bound route is derived from
  that full-support primitive. The
  old derivative/minimizer inputs are retained as reusable helper routes and
  as compatibility bridges to the paper's real-valued `inf_a` notation.

## Shared Library Seams

- Completed broader extraction:
  - `EconCSLib.Foundations.Probability.FiniteRatingComparison` now owns the
    generic finite-rating Lemma C machinery, support-safe pairwise
    threshold-rate APIs, tilted-mean lemmas, two-sample/floor-count comparison
    probabilities, `P_k`/`1 - P_k` algebra, integer-rate block bridges, and
    pairwise LDP certificate constructors.
  - GJ18's `MainTheorems.lean` now starts at the paper-specific finite
    aggregation layer and final Theorem 1 endpoints.
- Already added/used:
  - `FiniteRatingLDPModel`
  - `finiteRateFunction`
  - `FiniteErrorRateCertificate`
  - `ExponentialRateCertificate.of_eventually_const_sandwich`
  - `FiniteErrorRateCertificate.aggregateError_hasExponentialRate_of_dominating_subfamily`
  - `FiniteIidScoreCramerCertificate`
  - `EconCSLib.pmfProd`
  - `EconCSLib.pmfPi`
  - `EconCSLib.pmfExp_pmfProd_eq_pairExp`
  - `EconCSLib.pmfProb_pmfPi_twoCoord_eq_pmfProd_dependent`
  - `EconCSLib.pmfPairExp_mul_separable`
  - `hasExponentialRate_of_event_between_component_and_finite_sum`
  - `exists_component_rate_le_of_eventually_le_finite_sum`
  - `EconCSLib.Foundations.Probability.FiniteRankingEvents`
- Already added during the arbitrary-real floor-count pass:
  - finite-MGF/log-MGF shift algebra for `score - a` and `a - score`.
  - shifted Chernoff/rate-function identities from source log-MGF derivatives.
  - product-event and floor-sample lower-bound composition for independent
    high/low one-population tail certificates.
  - `exists_adjacent_inversion_of_nonadjacent_inversion`, the deterministic
    adjacent-inversion kernel.
  - finite PMF union bounds reducing arbitrary inversion events to sums of
    adjacent inversion events.
  - finite-chain ordered-pair and adjacent-pair threshold-rate predicates, plus
    the concrete joint floor-rating law and marginal bridge used to prove the
    source adjacent-pair reduction.
  - `PairwiseThresholdRateRegularity`, the compact package standing in for the
    source-side common-dual minimizer witnesses on auxiliary routes.
  - `PairwiseThresholdRateTopLdpCertificate.of_expected_score_gap_and_common_extreme_support`,
    deriving the support-safe pairwise LDP certificate from expected-score
    ordering and lower-level common-extreme support witnesses.
  - `FiniteRatingLDPModel.fullSupport`, a shared source-shaped predicate for
    finite rating laws whose every rating atom has positive probability.
  - `EconCSLib.pmfExp_le_pmfExp_of_fin_tail_prob_le`, the reusable finite
    ordinal FOSD bridge from upper-tail dominance to monotone-score expectation
    ordering.
  - `HasExtendedExponentialRate.to_finite`, the general bridge from a finite
    `WithTop` exponential-rate statement to an ordinary real-valued rate.
- Likely next reusable lemmas:
  - packaging of common-dual minimizer data for finite-support rating laws when
    the minimizer lies in the finite score hull.
  - optional compatibility theorem identifying
    `minFiniteChainAdjacentThresholdRateTop` with
    `(minFiniteChainAdjacentThresholdRate : WithTop ℝ)` only under stronger
    all-real boundedness/domain hypotheses.

## Active Scratchpad

- Current Lean endpoint: `lake build GJ18InformativeRatingSystems`.
- Current mathematical gap: the paper-specific GJ18 Theorem 1 spine is closed
  through the support-safe threshold-rate minimum, which is the canonical
  finite-support convention for the paper's finite/bounded rating-scale model.
  The adjacent-pair reduction is proved from the concrete joint floor-rating
  law, dependent finite-product marginals, and finite adjacent-inversion union
  bounds. The strongest finite endpoint proves the exponent at the minimum
  displayed adjacent pairwise-objective rate from common-dual derivative
  witnesses and primitive bottom/top rating support. Lean also identifies that
  value with the support-safe source adjacent threshold-rate minimum, and the
  compact pairwise threshold-rate regularity package feeds the support-safe
  theorem directly. The source-facing ordinal endpoint consumes full finite
  ordinal rating support and derives bottom/top atom support internally. The
  all-real real-rate wrapper is compatibility-only.

## Deviations And Assumptions

- The source paper itself uses finite seller types and finite rating levels, so
  those are not caveats. The support-safe extended-rate route is the canonical
  finite-support convention. The main paper-facing endpoint no longer exposes
  bottom/top atom support separately; it derives those facts from full finite
  ordinal rating support. Auxiliary derivative/minimizer routes may still carry
  lower-level support witnesses because they are reusable bridges, not the
  final source-facing theorem. The old all-real adjacent threshold-rate minimum
  should be treated as a compatibility wrapper, not as the primary paper
  theorem.
- Experimental regressions and empirical plots are out of scope unless the
  project later chooses to formalize the data-analysis workflow.
- The source text writes the match rates as real-valued `g(theta)` with floors;
  the arbitrary-real finite floor endpoint is now discharged by the shifted
  one-population Cramer route.
