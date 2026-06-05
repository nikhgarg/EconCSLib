# Designing Informative Rating Systems: Evidence from an Online Labor Market

## Source Version

- Paper: *Designing Informative Rating Systems: Evidence from an Online Labor Market*
- Authors: Nikhil Garg, Ramesh Johari
- Publication version: Manufacturing & Service Operations Management 23(3):589-605 article version, published online 2020 (issue 2021)
- Formalized source/PDF: arXiv 1810.13028 (`https://arxiv.org/pdf/1810.13028`)
- Official publication URL: https://doi.org/10.1287/msom.2020.0921
- Publisher page: https://pubsonline.informs.org/doi/10.1287/msom.2020.0921
- Public preprint: https://arxiv.org/abs/1810.13028
- Source cache used for intake: arXiv TeX source from `https://arxiv.org/e-print/1810.13028`

The official publisher article may require subscription access. The arXiv TeX
source cache and extracted source text are local/ignored artifacts. Do not
commit them unless redistribution rights are checked separately.

## Current Status

Status: formalized.

The source theorem already uses a finite totally ordered seller-type set,
finite rating levels, and floor-count match rates `n_k(theta) = floor(k
g(theta))`; those are source assumptions, not caveats. Lean represents that
finite ordered model, the source log-MGF and Legendre formulas, the `1 - P_k`
algebra, the floor-count objective, finite aggregation to `1 - W_k`, and the
adjacent-pair reduction from the concrete joint floor-rating law.

Theorem 1 is now closed as a source-facing support-safe finite-rate endpoint.
Lean derives the common-dual witnesses and pairwise support-safe LDP
certificates from positive match rates, the paper's upper-tail rating
dominance, monotone scores, and full finite ordinal rating support. The
bottom/top atom support used by the finite lower-bound route is derived from
that full-support source primitive. The source model uses finite seller types,
finite rating levels, and scores in `[0,1]`, so the support-safe extended-rate
convention is the canonical finite-support statement. The older real-rate
bridge theorem is retained as a compatibility result for users who choose to
supply stronger all-real boundedness/domain conditions. Empirical sections are
source scope but not Lean theorem targets.

## Paper-Facing Ledger

- Implementation theorem file: `GJ18InformativeRatingSystems/MainTheorems.lean`
- Human-facing theorem file: `GJ18InformativeRatingSystems/PaperInterface.lean`
- Shared finite-rating comparison library:
  `EconCSLib.Foundations.Probability.FiniteRatingComparison`
- Machine-readable status source: `GJ18InformativeRatingSystems/status.json`
- Outside-Lean proof plan: `GJ18InformativeRatingSystems/FORMALIZATION_PLAN.md`
- Dependency DAG: `GJ18InformativeRatingSystems/DependencyDAG.tex`

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Definition: log-MGF for a seller type | `definition_log_mgf_formula` | formalized | `PaperInterface.lean` | None; finite-rating formula wrapper. |
| Definition: rate function for a seller type | `definition_rate_function_formula` | formalized | `PaperInterface.lean` | None; Legendre-transform formula wrapper. |
| Appendix pairwise threshold-rate formula | `lemmaC_pairwise_threshold_rate_formula` | formalized | `PaperInterface.lean` | None; source RHS formula. |
| Appendix support-safe threshold-rate attainment | `lemmaC_pairwise_threshold_rate_top_eq_displayed_objective_of_common_logMGF_derivatives` | formalized | `PaperInterface.lean` | None; extended source threshold rate equals the displayed real objective at common-dual derivative thresholds. |
| Appendix equal-sample pairwise MGF product | `lemmaC_equal_sample_pairwise_mgf_product_formula` | formalized | `PaperInterface.lean` | None; paired finite-rating bridge. |
| Appendix equal-sample pairwise mean formula | `lemmaC_equal_sample_pairwise_gap_mean_formula` | formalized | `PaperInterface.lean` | None; paired gap expectation bridge. |
| Appendix two-population sample MGF product | `lemmaC_two_population_sample_mgf_product_formula` | formalized | `PaperInterface.lean` | None; independent high/low sample bridge. |
| Appendix two-population Chernoff upper bound | `lemmaC_two_population_sample_chernoff_upper_bound` | formalized | `PaperInterface.lean` | None; pointwise finite comparison upper bound. |
| Appendix integer-rate Chernoff certificate | `lemmaC_two_population_integer_rate_chernoff_upper_certificate` | formalized | `PaperInterface.lean` | None; sample counts `n * gHi`, `n * gLo`. |
| Appendix integer-rate block MGF product | `lemmaC_integer_rate_block_mgf_product_formula` | formalized | `PaperInterface.lean` | None; one macro-sample with `gHi` and `gLo` draws. |
| Appendix integer-rate block log-MGF | `lemmaC_integer_rate_block_log_mgf_formula` | formalized | `PaperInterface.lean` | None; scaled one-rating log-MGF sum. |
| Appendix integer-rate block Cramer bridge | `lemmaC_integer_rate_block_source_threshold_rate_from_logMGF_derivatives` | formalized | `PaperInterface.lean` | None; finite-type Cramer and source-threshold bridge from derivative witnesses. |
| Appendix block to ungrouped comparison | `lemmaC_integer_rate_block_error_probability_eq_two_population_probability` | formalized | `PaperInterface.lean` | None; exact equality for `n * gHi`, `n * gLo` samples. |
| Appendix `1 - P_k` algebra | `lemmaC_pk_complement_error_eq_one_sub_pk_objective` | formalized | `PaperInterface.lean` | None; matches paper definition of `P_k`. |
| Appendix floor-count sample normalization | `source_floor_sample_count_div_tendsto_sampleRate` | formalized | `PaperInterface.lean` | None; `floor(k g) / k -> g`. |
| Appendix floor-count natural-rate bridge | `source_floor_sample_count_eq_mul_of_nat_sampleRate` | formalized | `PaperInterface.lean` | None; `floor(k g) = k g` for natural-valued rates. |
| Appendix floor-count `P_k` transfer | `lemmaC_floor_pk_complement_error_rate_from_left_tail` | conditional | `PaperInterface.lean` | Reusable bridge from a pairwise floor-count left-tail LDP certificate. |
| Appendix floor-count pairwise score-gap LDP | `lemmaC_floor_score_gap_rate_from_logMGF_derivative_threshold_minimizer_of_straddling_support` | conditional | `PaperInterface.lean` | Takes common-dual log-MGF derivative witnesses, a source-level threshold minimizer, and compact two-sided support as explicit inputs. |
| Appendix equal-sample pairwise Cramer bridge | `lemmaC_equal_sample_pairwise_error_rate_from_cramer` | conditional | `PaperInterface.lean` | From finite iid Cramer certificate. |
| Appendix `P_k` transfer | `lemmaC_pk_complement_source_threshold_rate_from_logMGF_derivatives` | formalized | `PaperInterface.lean` | None; integer-rate source-threshold exact rate for `1 - P_k`. |
| Theorem 1 finite aggregation upper bound | `theorem1_finite_ranking_error_upper_bound_from_pair_certificates` | formalized | `PaperInterface.lean` | None; from pairwise certificates. |
| Theorem 1 finite exact aggregation | `theorem1_finite_ranking_error_exact_rate_from_min_pair_certificate` | formalized | `PaperInterface.lean` | None; minimum component bridge. |
| Theorem 1 finite adjacent-pair reduction | `theorem1_finite_ranking_error_exact_rate_from_adjacent_pair_min` | formalized | `PaperInterface.lean` | None; adjacent dominance bridge. |
| Theorem 1 integer-rate `1 - W_n` endpoint | `theorem1_integer_rate_weighted_objective_oneSub_exact_rate_from_adjacent_logMGF_derivatives` | conditional | `PaperInterface.lean` | Integer-rate reduction is closed once derivative, bounded-rate, support, and adjacent-dominance inputs are supplied. |
| Theorem 1 floor-count natural-rate endpoint | `theorem1_floor_weighted_objective_oneSub_exact_rate_from_nat_sampleRates_adjacent_logMGF_derivatives` | conditional | `PaperInterface.lean` | Source floor objective for natural-valued match rates; still depends on the same explicit pairwise LDP regularity inputs. |
| Theorem 1 finite-chain displayed-objective endpoint | `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_adjacent_objective_rate_from_logMGF_derivatives_and_score_bounds` | conditional | `PaperInterface.lean` | Auxiliary displayed-objective route: finite floor-count LDP, score-bound support witnesses, and aggregation are closed at the displayed adjacent pairwise-objective rate; source threshold-rate identification remains. |
| Theorem 1 finite-chain displayed-objective minimum endpoint | `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_objective_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds` | conditional | `PaperInterface.lean` | Concrete joint floor-rating law, adjacent-pair reduction, and finite aggregation are internal at the minimum displayed adjacent-objective rate; source threshold-rate identification remains. |
| Theorem 1 support-safe adjacent threshold-rate minimum | `theorem1_finite_chain_adjacent_threshold_rate_top_min_eq_displayed_objective_min_of_logMGF_derivatives` | formalized | `PaperInterface.lean` | None; extended source threshold-rate minimum equals the displayed adjacent-objective minimum at common-dual derivative thresholds. |
| Theorem 1 source-facing support-safe endpoint | `theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_rating_tail_dominance_and_full_support` | formalized | `PaperInterface.lean` | None; positive match rates, ordinal upper-tail dominance, monotone scores, and full finite ordinal rating support are theorem hypotheses; bottom/top atom support is derived internally. |
| Theorem 1 real-rate compatibility bridge from support-safe endpoint | `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_threshold_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds_of_extended_min_eq` | conditional | `PaperInterface.lean` | Optional wrapper for stronger all-real domain conventions; not the canonical finite-support statement. |
| Theorem 1 finite-chain real-rate compact regularity endpoint | `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_pairwise_threshold_rate_regularity` | conditional | `PaperInterface.lean` | Concrete joint floor-rating law and adjacent aggregation are internal; this is the real-rate compatibility path from the same named regularity package. |
| Theorem 1 finite-chain real-rate floor endpoint | `theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_joint_floor_rating_law` | partially formalized | `PaperInterface.lean` | Source finite ordered model and adjacent reduction are represented, but positive match-rate, derivative, threshold-minimizer, and support hypotheses remain explicit rather than derived from source primitives. |

## Validation

Last targeted check:

```bash
lake build GJ18InformativeRatingSystems
```
