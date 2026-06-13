import PRPKG24AccuracyDiversity.ProofInterface
import PRPKG24AccuracyDiversity.Assumptions

/-!
# Paper Interface: Reconciling the Accuracy-Diversity Trade-off

This is the compact human-review surface for the PRPKG 2024
accuracy-diversity formalization. It exposes one representative declaration for
each paper-named definition, example, theorem part, corollary, proposition, and
appendix lemma. The larger implementation/checkpoint ledger remains in
`ProofInterface.lean`.
-/

open scoped BigOperators

namespace PRPKG24AccuracyDiversity
namespace PaperInterface

/-! ## Definitions and Example -/

/-- Definition 1: exact finite gamma-homogeneity, equation (5). -/
abbrev definition1 :=
  @definition1_gamma_homogeneity_exact_iff

/-- Definition 2: sequence gamma-homogeneity, equation (6). -/
abbrev definition2 :=
  @definition2_gamma_homogeneity_sequence_iff

/-- Definition 3: the top-`k` oracle induced by order-statistic means. -/
noncomputable abbrev definition3 :=
  @definition3_topk_value_oracle_from_order_statistic_mean

/--
Definition 3: the expected top-`k` value from order-statistic means is the sum
of the upper `min k a` order-statistic means.
-/
theorem definition3_expectedTopSum_formula
    (T : ℕ) (mu : ℕ → ℕ → ℝ) (k : ℕ) (t : ItemType T) (a : ℕ) :
    (definition3 T mu).expectedTopSum k t a =
      ∑ i ∈ Finset.range (min k a), mu (a - i) a := by
  rfl

/-- Example 1: exact calibrated top-one exponential sequence. -/
abbrev example1 :=
  @example1_top_one_exponential_harmonic_sequence_formula

/-! ## Main Theorems and Corollaries -/

/-- Theorem 1(i): finite-discrete iid source, equation (6). -/
abbrev theorem1_i :=
  @theorem1_i_finite_discrete_sequence_uniform_formula_of_iid_top_split

/--
Theorem 1(i): finite-discrete iid source, equation (6).
Source status: direct source formula
-/
abbrev theorem1_i_formula :=
  @theorem1_i_finite_discrete_sequence_uniform_formula_of_iid_top_split

/-- Theorem 1(ii): bounded iid upper-endpoint density route, equation (6). -/
abbrev theorem1_ii :=
  @theorem1_ii_bounded_iid_upper_endpoint_density_ratio_sequence_formula_of_nonnegative_support

/--
Theorem 1(ii): bounded iid upper-endpoint density route, equation (6).
Source status: direct source formula
-/
abbrev theorem1_ii_formula :=
  @theorem1_ii_bounded_iid_upper_endpoint_density_ratio_sequence_formula_of_nonnegative_support

/-- Theorem 1(iii): exponential order-statistic source, equation (6). -/
abbrev theorem1_iii :=
  @theorem1_iii_exponential_top_k_order_statistic_sequence_formula

/--
Theorem 1(iii): exponential order-statistic source, equation (6).
Source status: direct source formula
-/
abbrev theorem1_iii_formula :=
  @theorem1_iii_exponential_top_k_order_statistic_sequence_formula

/-- Theorem 1(iv): concrete iid Pareto order-statistic source, equation (6). -/
abbrev theorem1_iv :=
  @theorem1_iv_pareto_iid_order_statistic_sequence_formula

/--
Theorem 1(iv): concrete iid Pareto order-statistic source, equation (6).
Source status: direct source formula
-/
abbrev theorem1_iv_formula :=
  @theorem1_iv_pareto_iid_order_statistic_sequence_formula

/-- Theorem 1(v): all-consumed common-mean argmax optimum. -/
abbrev theorem1_v_common_mean :=
  @theorem1_all_consumed_common_mean_argmax_optimum

/-- Theorem 1(v): unique common-mean argmax converse. -/
abbrev theorem1_v_unique_common_mean :=
  @theorem1_all_consumed_unique_common_mean_only_argmax

/-- Corollary 1: every nonnegative gamma is attainable by a concrete model. -/
abbrev corollary1 :=
  @corollary1_any_nonnegative_gamma_concrete_model_sequence_formula

/-- Theorem 2(i): decaying Bernoulli top-one, `alpha = 0`. -/
abbrev theorem2_i :=
  @theorem2_i_decaying_bernoulli_top_one_uniform_formula

/--
Theorem 2(i): decaying Bernoulli top-one, `alpha = 0`.
Source status: direct source formula
-/
abbrev theorem2_i_formula :=
  @theorem2_i_decaying_bernoulli_top_one_uniform_formula

/-- Theorem 2(ii): decaying Bernoulli top-one, `alpha = 1`. -/
abbrev theorem2_ii :=
  @theorem2_ii_decaying_bernoulli_top_one_formula

/--
Theorem 2(ii): decaying Bernoulli top-one, `alpha = 1`.
Source status: direct source formula
-/
abbrev theorem2_ii_formula :=
  @theorem2_ii_decaying_bernoulli_top_one_formula

/-- Theorem 2(iii): decaying Bernoulli top-one, `alpha > 1`. -/
abbrev theorem2_iii :=
  @theorem2_iii_decaying_bernoulli_top_one_formula

/--
Theorem 2(iii): decaying Bernoulli top-one, `alpha > 1`.
Source status: direct source formula
-/
abbrev theorem2_iii_formula :=
  @theorem2_iii_decaying_bernoulli_top_one_formula

/-- Theorem 2(iv): decaying Bernoulli all-consumed, positive `alpha`. -/
abbrev theorem2_iv_positive_alpha :=
  @theorem2_iv_decaying_bernoulli_all_consumed_positive_alpha_formula

/-- Theorem 2(iv): `alpha = 0` argmax endpoint. -/
abbrev theorem2_iv_alpha_zero :=
  @theorem2_iv_decaying_bernoulli_all_consumed_alpha_zero_argmax

/--
Theorem 2(iv): `alpha = 0` argmax endpoint.
Source status: direct source condition
-/
abbrev theorem2_iv_alpha_zero_condition :=
  @theorem2_iv_decaying_bernoulli_all_consumed_alpha_zero_argmax

/-- Theorem 3: varying success probabilities, log-share formula. -/
abbrev theorem3 :=
  @theorem3_varying_success_probability_log_share_formula

/--
Theorem 3: varying success probabilities, log-share formula.
Source status: direct source formula
-/
abbrev theorem3_formula :=
  @theorem3_varying_success_probability_log_share_formula

/-- Corollary 3: iid Bernoulli gives asymptotic `0`-homogeneity. -/
abbrev corollary3 :=
  @corollary3_iid_bernoulli_asymptotic_uniform_homogeneity

/-! ## Propositions -/

/-- Proposition 2: corrected uniform top-`k` route sufficient for asymptotics. -/
abbrev proposition2 :=
  @proposition2_uniform_top_k_corrected_sequence_homogeneity_of_paper_bound

/-- Proposition 4: full continuous-sphere endpoint, with explicit certificate. -/
abbrev proposition4 :=
  @proposition4_continuous_sphere_uniform_minimizes

/-- Proposition 5: uniform `[0,1]` order-statistic identity. -/
abbrev proposition5 :=
  @proposition5_uniform_order_statistic_topk_sum_eq_value

/--
Proposition 5: uniform `[0,1]` order-statistic identity.
Source status: direct source identity
-/
abbrev proposition5_identity :=
  @proposition5_uniform_order_statistic_topk_sum_eq_value

/-! ## Appendix Lemmas -/

/--
Lemma D.1: optimizer sequence limit from the appendix compactness/unique-limit
objective route.
-/
abbrev lemmaD1 :=
  @lemmaD1_optimizer_sequence_limit_of_unique_simplex_limit_objective

/-- Lemma D.2: bounded-tail integral asymptotic. -/
abbrev lemmaD2 :=
  @lemmaD2_bounded_integral_top_k_loss_asymptotic_of_split_certificate

/--
Lemma D.2: bounded-tail integral asymptotic.
Source status: direct source formula
-/
abbrev lemmaD2_formula :=
  @lemmaD2_bounded_integral_top_k_loss_asymptotic_of_split_certificate

/-- Lemma 1: bounded iid upper-endpoint tail loss-to-marginal bridge. -/
abbrev lemma1 :=
  @lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail

/--
Lemma 1: bounded iid upper-endpoint tail loss-to-marginal bridge.
Source status: direct source tail formula
-/
abbrev lemma1_tail_formula :=
  @lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_upper_endpoint_tail

/-- Lemma D.3: exponential order-statistic sequence formula. -/
abbrev lemmaD3 :=
  @theorem1_iii_exponential_top_k_order_statistic_sequence_formula

/--
Lemma D.3: exponential order-statistic sequence formula.
Source status: direct source formula
-/
abbrev lemmaD3_formula :=
  @theorem1_iii_exponential_top_k_order_statistic_sequence_formula

/-- Lemma D.4: concrete iid Pareto order-statistic sequence formula. -/
abbrev lemmaD4 :=
  @theorem1_iv_pareto_iid_order_statistic_sequence_formula

/--
Lemma D.4: concrete iid Pareto order-statistic sequence formula.
Source status: direct source formula
-/
abbrev lemmaD4_formula :=
  @theorem1_iv_pareto_iid_order_statistic_sequence_formula

/-- Lemma D.5: real-to-integer rounding bridge. -/
abbrev lemmaD5 :=
  @proposition2_uniform_top_k_sharp_finite_of_count_closeness

end PaperInterface
end PRPKG24AccuracyDiversity
