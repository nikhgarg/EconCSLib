import PRPKG24AccuracyDiversity.ProofInterface

/-!
# Paper Interface: Reconciling the Accuracy-Diversity Trade-off

This file is the compact human-review surface for the PRPKG 2024
accuracy-diversity formalization.  It lists the paper-facing definitions and
named results; the exhaustive endpoint ledger remains in `ProofInterface.lean`.
-/

open scoped BigOperators

namespace PRPKG24AccuracyDiversity
namespace PaperInterface

/-- Definition 1: gamma-homogeneity profile. -/
abbrev definition1_gamma_profile := @gammaProfile

/-- Definition 1: target-share formula. -/
abbrev definition1_gamma_target_share := @definition1_gamma_target_share_eq

/-- Definition 1: exact gamma-homogeneity. -/
abbrev definition1_gamma_homogeneity := @definition1_gamma_homogeneity_exact_iff

/-- Definition 2: asymptotic gamma-homogeneity. -/
abbrev definition2_gamma_homogeneity_sequence := @definition2_gamma_homogeneity_sequence_iff

/-- Example 1: all consumed all romance is optimal. -/
abbrev example1_all_romance := @example1_all_consumed_all_romance_is_optimal

/-- Theorem 1(i): finite discrete logarithmic geometric-tail ratio. -/
abbrev theorem1_i_finite_discrete := @theorem1_i_finite_discrete_log_geometric_tail_ratio

/-- Theorem 1(ii): bounded-support sequence homogeneity. -/
abbrev theorem1_ii_bounded_sequence := @theorem1_ii_bounded_sequence_homogeneity_of_eventual_sublinear_foc_certificate

/-- Theorem 1(ii): bounded loss-to-marginal bridge. -/
abbrev theorem1_ii_bounded_loss_to_marginal := @theorem1_ii_bounded_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop

/-- Theorem 1(ii): bounded source scaled-marginal certificate. -/
abbrev theorem1_ii_bounded_scaled_marginal_from_source := @theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_source

/-- Theorem 1(ii): bounded scaled-marginal certificate from loss plus drop. -/
abbrev theorem1_ii_bounded_scaled_marginal_from_loss_drop := @theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_loss_ae_and_scaled_drop

/-- Theorem 1(ii): bounded iid reflected-CDF scaled-marginal certificate. -/
abbrev theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal := @theorem1_ii_bounded_iid_reflected_cdf_scaled_marginal_certificate_of_base_ae_bounds_and_reflected_cdf_tail_and_scaled_drop

/-- Theorem 1(ii): uniform `[0,1]` order-statistic scaled-marginal certificate. -/
abbrev theorem1_ii_uniform_order_statistic_scaled_marginal := @theorem1_ii_uniform_order_statistic_scaled_marginal_certificate

/-- Theorem 1(ii): uniform `[0,1]` order-statistic source sequence theorem. -/
abbrev theorem1_ii_uniform_order_statistic_sequence := @theorem1_ii_uniform_order_statistic_sequence_homogeneity_of_paper_bound

/-- Theorem 1(ii): uniform `[0,1]` order-statistic source equation (6). -/
abbrev theorem1_ii_uniform_order_statistic_formula := @theorem1_ii_uniform_order_statistic_sequence_formula_of_paper_bound

/-- Theorem 1(iii): exponential sequence formula. -/
abbrev theorem1_iii_exponential_sequence := @theorem1_iii_exponential_sequence_formula_of_eventual_sublinear_foc_certificate

/-- Theorem 1(iv): Pareto sequence formula. -/
abbrev theorem1_iv_pareto_sequence := @theorem1_iv_pareto_sequence_formula_of_eventual_sublinear_foc_certificate

/-- Corollary 1: gamma parameter cases are attainable. -/
abbrev corollary1_gamma_cases := @corollary1_gamma_parameter_cases

/-- Corollary 1: concrete exponential order-statistic realization for `γ = 1`. -/
abbrev corollary1_exponential_gamma_one := @corollary1_exponential_top_k_order_statistic_gamma_one_sequence_formula

/-- Proposition 2: uniform top-k sequence homogeneity. -/
abbrev proposition2_uniform_top_k := @proposition2_uniform_top_k_sequence_homogeneity_of_paper_bound

/-- Corollary 3: iid Bernoulli asymptotic uniform homogeneity. -/
abbrev corollary3_iid_bernoulli := @corollary3_iid_bernoulli_asymptotic_uniform_homogeneity

/-- Theorem 2(i): decaying Bernoulli top-one zero-homogeneity. -/
abbrev theorem2_i_decaying_bernoulli := @PRPKG24AccuracyDiversity.paper_theorem2_i_decaying_bernoulli_top_one_alpha_zero_sequence_uniform_homogeneity

/-- Theorem 2(ii): decaying Bernoulli subunit regime. -/
abbrev theorem2_ii_decaying_bernoulli := @PRPKG24AccuracyDiversity.paper_theorem2_ii_decaying_bernoulli_sequence_homogeneity_of_certificate

/-- Theorem 2(iii): decaying Bernoulli superunit regime. -/
abbrev theorem2_iii_decaying_bernoulli := @PRPKG24AccuracyDiversity.paper_theorem2_iii_decaying_bernoulli_sequence_homogeneity_of_certificate

/-- Theorem 2(iv): all-consumed decaying Bernoulli regime. -/
abbrev theorem2_iv_decaying_bernoulli := @PRPKG24AccuracyDiversity.paper_theorem2_iv_decaying_bernoulli_all_consumed_alpha_one_sequence_homogeneity

/-- Theorem 3: varying success probabilities give log-share homogeneity. -/
abbrev theorem3_varying_success_probability := @theorem3_varying_success_probability_log_share

/-- Lemma D.1: optimizer sequence limit. -/
abbrev lemmaD1_optimizer_sequence_limit := @lemmaD1_optimizer_sequence_limit_of_asymptotic_homogeneity

/-- Lemma D.2: bounded-tail integral asymptotic. -/
abbrev lemmaD2_bounded_integral_asymptotic := @lemmaD2_bounded_integral_top_k_loss_asymptotic_of_split_certificate

/-- Lemma 1: bounded iid loss-to-marginal bridge from reflected-CDF tail. -/
abbrev lemma1_bounded_iid_loss_to_marginal := @lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail_and_scaled_drop

/-- Lemma 1: bounded iid loss-to-marginal bridge from exact reflected-CDF power. -/
abbrev lemma1_bounded_iid_exact_power_loss_to_marginal := @lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power_and_scaled_drop

/-- Lemma 1: concrete continuous uniform `[0,1]` iid bounded source law. -/
abbrev lemma1_uniform01_iid := @lemma1_uniform01_iid_reflected_cdf_count_layer_top_k_loss_asymptotic

/-- Lemma D.3: exponential order-statistic sequence formula. -/
abbrev lemmaD3_exponential_sequence_formula := @theorem1_iii_exponential_sequence_formula_of_eventual_sublinear_foc_certificate

/-- Lemma D.4: Pareto order-statistic sequence formula. -/
abbrev lemmaD4_pareto_sequence_formula := @theorem1_iv_pareto_sequence_formula_of_eventual_sublinear_foc_certificate

/-- Lemma D.4: fixed-rank Pareto finite-difference bridge. -/
abbrev lemmaD4_pareto_rank_finite_difference := @lemmaD4_pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop

/-- Lemma D.4: canonical fixed-rank Pareto finite-difference bridge. -/
abbrev lemmaD4_pareto_rank_canonical_finite_difference := @lemmaD4_pareto_rank_scaled_limit_of_canonical_value_asymptotic_and_scaled_drop

/-- Lemma D.4: exact gamma-ratio fixed-rank Pareto scaled limit. -/
abbrev lemmaD4_pareto_rank_gamma_ratio_scaled_limit := @lemmaD4_pareto_rank_gamma_ratio_mean_scaled_limit

/-- Lemma D.5: real-to-integer rounding seam. -/
abbrev lemmaD5_rounding := @proposition2_uniform_top_k_sharp_finite_of_count_closeness

end PaperInterface
end PRPKG24AccuracyDiversity
