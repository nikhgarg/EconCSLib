# PRPKG24 Formalization Plan

Last updated: 2026-05-23

## Initial Checklist Rerun

- Source cache present: `PRPKG24AccuracyDiversity.pdf` and
  `PRPKG24AccuracyDiversity.txt`.
- Required paper-folder artifacts present: `.gitignore`, `README.md`,
  `DependencyDAG.tex`, `DependencyDAG.pdf`, `MainTheorems.lean`,
  `PaperInterface.lean`, and `review-dashboard.sh`.
- Cached-text named-result search found the expected source inventory:
  Definitions 1-3; Theorems 1-3; Corollaries 1 and 3; Propositions 2, 4, and
  5; Lemma 1; and Appendix Lemmas D.1-D.5.
- Current validation command:
  `lake build PRPKG24AccuracyDiversity`.
- Current build status: passes as of the 2026-05-23 planning refresh.
- Current stopping point:
  `HANDOFF_2026-05-23_PRPKG_STOPPING_POINT.md`.
- Reusable math transfer:
  `EconCSLib.Foundations.Math.GammaAsymptotics` now contains the generic
  Gamma-ratio asymptotic and finite-difference bridge used by the Pareto
  Lemma D.4 checkpoint.

## Source-Level Map

- Complete or effectively closed:
  - Example 1's all-consumed calibration warning and top-one log-relaxation
    calculation. The Lean statements prove the exact all-consumed all-romance
    optimum/unique-argmax consequence and the weighted-log relaxed optimum at
    `(p1*n, p2*n)`.
  - Definitions 1 and 2 at the paper-formula level: `gammaLikelihoodProfile`
    now has a target-share theorem for `p_t^γ / ∑ p_i^γ`, plus finite and
    sequence iff wrappers exposed through `PaperInterface.lean`.
  - Definition 3 / Proposition 5 at the order-statistic-mean interface:
    `orderStatisticTopKSumFromMean` formalizes the paper's bottom-indexed
    `μ_D(i,a)` convention, `TopKValueOracle.ofOrderStatisticMean` builds the
    induced top-`k` oracle, and the paper-facing wrappers expose the exact
    `∑_{i=1}^{min{k,a}} μ_D(a-i+1,a)` shape. The uniform `[0,1]` instance is
    also bridged to the existing closed form by
    `paper_proposition5_uniform_order_statistic_topk_sum_eq_value`, and the
    order-statistic oracle now inherits the uniform Theorem 1(ii) sequence
    theorem through
    `paper_theorem1_ii_uniform_order_statistic_sequence_homogeneity_of_paper_bound`.
  - Theorem 1's paper-facing interface: part (v) has both the argmax optimum
    and strict-argmax converse exposed, and parts (i)-(iv) have direct
    equation (6) formula endpoints in `PaperInterface.lean` in addition to the
    reusable top-`k` certificate wrappers.
  - Theorem 1(i)'s finite-optimization seam below the abstract certificate:
    `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_sublinear_foc_certificate`
    proves that a sublinear unweighted FOC gap certificate is sufficient for
    the finite-discrete `0`-homogeneity conclusion.
  - Theorem 1(i)'s source-shaped top-`k` marginal seam:
    `TopKUniformSublinearFOCCertificate` states the exact backward/forward
    marginal dominance obligation in terms of `expectedTopSum`, and
    `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_topk_sublinear_foc_certificate`
    proves that this obligation implies the Definition 2 uniform limit.
  - Theorem 1(i)'s finite-prefix/floor bridge for the source-shaped top-`k`
    seam: `TopKUniformEventualSublinearFOCCertificate` lets the
    distribution-side proof supply eventual count-floor and large-gap marginal
    estimates only after a finite threshold, and
    `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_eventual_topk_foc_certificate`
    proves that those eventual estimates still imply the Definition 2 uniform
    limit.
  - Theorem 1(i)'s eventual count-floor bridge:
    `TopKUniformCountFloorCertificate` proves that a large-source/small-
    destination marginal dominance estimate forces every sufficiently large
    optimum to put more than a fixed floor in every type.  The paper-facing
    wrapper is
    `paper_theorem1_i_finite_discrete_eventual_count_floor_of_topk_marginal_dominance`.
  - Theorem 1(i)'s combined finite-discrete proof seam:
    `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_count_floor_and_large_gap`
    takes exactly the two remaining distribution estimates (count-floor
    dominance and large-gap dominance above that floor) and returns the source
    `0`-homogeneity conclusion, with a direct equation (6) wrapper in
    `PaperInterface.lean`.
  - Theorem 1(i)'s geometric marginal-bound and tail certificate seams:
    `TopKUniformGeometricMarginalBoundCertificate` packages the source
    polynomial-geometric upper marginal, geometric lower marginal, count-floor,
    and sublinear-gap estimates, while `TopKUniformGeometricTailCertificate`
    derives the count-floor comparison from a positive finite-floor forward
    lower bound and the verified fact that polynomial-geometric tails vanish.
    The paper-facing wrappers are
    `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_geometric_marginal_bounds`
    and
    `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_geometric_tail_certificate`,
    with direct equation (6) wrappers in `PaperInterface.lean`.
  - Theorem 1(i)'s source asymptotic algebra for equations (87)-(90):
    `paper_theorem1_i_finite_discrete_log_geometric_tail_ratio` and
    `paper_theorem1_i_finite_discrete_log_polynomial_geometric_tail_ratio`
    prove that geometric and polynomial-times-geometric tails have the
    logarithmic saturation ratio used in the finite-discrete proof, while
    `paper_theorem1_i_finite_discrete_log_tail_ratio_of_geometric_bounds`
    proves the squeeze step from the paper's lower/upper bounds.
  - Theorem 1(i)'s source binomial estimates for equations (81)-(83) and the
    lower marginal event: `finiteDiscreteTopMassFailureTail` has both the
    shifted paper bound and the certificate-normalized
    `paper_theorem1_i_finite_discrete_top_mass_failure_tail_bound_at_a`, and
    `finiteDiscreteTopMassPromotingEvent` has the matching
    `paper_theorem1_i_finite_discrete_top_mass_promoting_event_lower_bound_at_a`.
    `FiniteDiscreteOrderStats.lean` now proves the deterministic sample-level
    top-`k` upper bound by the failure indicator and the deterministic lower
    bound by the promoting indicator, finite-PMF expectation lifts for both
    event bounds, exact product-PMF/binomial event probabilities, the
    option-sample marginal identity, and the natural scalar `h(a+1)-h(a)`
    upper/lower marginal bounds for `finiteDiscreteIidTopKExpected`.
    `TopKUniformGeometricTailCertificate.of_binomial_event_bounds` now turns
    those event estimates into the geometric-tail certificate once the scalar
    bounds are plugged in with explicit constants and floor hypotheses.
    `TopKUniformGeometricTailCertificate.of_unweighted_binomial_event_bounds`
    and `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_scalar_binomial_event_bounds`
    additionally reduce the i.i.d. source case to scalar marginal inequalities
    for the paper's common `h(a)` function, with type likelihood bounds handled
    separately.
    `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds`
    now instantiates this scalar seam for the actual finite-support i.i.d.
    top-`k` expectation, including the off-by-one upper-tail normalization and
    the constants `backwardLoss = k * xTop * rho⁻¹` and
    `forwardGain = xTop - xSecond`.
    `paper_theorem1_i_finite_discrete_scalar_lower_marginal_top_event_before_k`
    and
    `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor`
    discharge the small-count floor at `floor = k - 1` with
    `smallForward = xTop * q`.
    `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_pred_floor_of_gap_decay`
    verifies the constant algebra for the large-gap comparison, reducing the
    remaining gap obligation to
    `Tendsto (fun N => (N : ℝ)^k * rho^(gap N)) atTop (nhds 0)`.
    `paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_scalar_marginal_bounds_sqrt_gap`
    closes that gap obligation with the concrete schedule `gap N = Nat.sqrt N`.
  - Theorem 1(i)'s fully formalized two-point finite-discrete instance:
    `paper_theorem1_i_two_point_bernoulli_top_one_sequence_uniform_homogeneity`
    proves the Bernoulli `{0,1}` / `k = 1` branch from the existing closed
    Bernoulli log-share machinery and exposes the direct uniform limit formula
    in `PaperInterface.lean`.
  - Theorem 1(iii)'s exact top-one exponential harmonic-oracle instance:
    `EconCSLib.Probability.Exponential.Model` now provides the reusable
    positive-rate exponential distribution wrapper over mathlib's
    `expMeasure`, while `exponentialTopOneHarmonicValue` formalizes the
    `H_q/lambda` value formula as a common top-one oracle, verifies the exact
    forward and backward marginals, and
    `paper_theorem1_iii_exponential_top_one_harmonic_sequence_homogeneity`
    proves the `γ = 1` sequence limit from a concrete `O(1/N)` sublinear FOC
    certificate. The direct equation (6) wrapper is
    `theorem1_iii_exponential_top_one_harmonic_sequence_formula`. The paper's
    log-approximation checkpoint is also verified:
    `paper_theorem1_iii_exponential_top_one_harmonic_log_approximation` proves
    `H_q/lambda - (log q)/lambda` converges to
    `EulerMascheroni/lambda`. The all-`q` binomial survival algebra is now
    exposed as
    `paper_theorem1_iii_exponential_max_survival_binomial_expansion`. The
    termwise integral and all-`q` finite alternating-sum survival-integral
    reduction are exposed as
    `paper_theorem1_iii_exponential_survival_power_integral` and
    `paper_theorem1_iii_exponential_max_survival_integral_finite_sum`. The
    finite alternating-binomial/harmonic identity is now closed by
    `paper_theorem1_iii_exponential_finite_sum_eq_harmonic_value`, and the
    analytic all-`q` survival integral is closed in harmonic form by
    `paper_theorem1_iii_exponential_max_survival_integral_harmonic_value`. The
    first measure-facing checkpoint is also closed:
    `paper_theorem1_iii_exponential_single_draw_survival_integral` derives the
    `q = 1` `H_1/lambda` value from the survival integral of the
    `Exponential.Model.measure` CDF. The all-`q` product-measure bridge is now
    closed by
    `paper_theorem1_iii_exponential_product_max_survival_eq_formula` and
    `paper_theorem1_iii_exponential_product_max_survival_integral_harmonic_value`.
    The layer-cake tail-probability side is closed by
    `paper_theorem1_iii_exponential_product_max_tail_integral_harmonic_value`,
    and the conditional literal expectation bridge is exposed as
    `paper_theorem1_iii_exponential_product_max_integral_harmonic_value_of_integrable`.
    The library also proves finite-maximum integrability under the product
    measure, so the unconditional literal Bochner expectation statement is
    closed by
    `paper_theorem1_iii_exponential_product_max_integral_harmonic_value`. The
    finite top-`k` order-statistic oracle is also closed at the exact
    order-statistic/optimization layer:
    `paper_theorem1_iii_exponential_top_k_order_statistic_forward_marginal`
    proves marginal increment `(1/lambda) * min(k,q+1)/(q+1)`,
    `paper_theorem1_iii_exponential_top_k_order_statistic_sum_Icc` rewrites
    the exact oracle as the threshold-index sum
    `∑_{j=1}^q (1/lambda) * min(k,j)/j`,
    `paper_theorem1_iii_exponential_top_k_order_statistic_marginal_nonnegative`
    and
    `paper_theorem1_iii_exponential_top_k_order_statistic_marginal_antitone`
    prove nonnegative and diminishing one-step marginals,
    `paper_theorem1_iii_exponential_top_k_order_statistic_marginal_strict_antitone`
    proves the eventual strict marginal drop once counts are at least `k`, and
    `paper_theorem1_iii_exponential_top_k_order_statistic_diminishing_returns`
    exposing the consumption-model consequence,
    `paper_theorem1_iii_exponential_top_k_order_statistic_harmonic_closed_form`
    proves `(k/lambda) * (1 + H_q - H_k)` once `q >= k > 0`,
    `paper_theorem1_iii_exponential_top_k_order_statistic_log_asymptotic`
    proves convergence after subtracting `(k/lambda) * log q`, and
    `paper_theorem1_iii_exponential_top_k_scaled_marginal_certificate`
    instantiates the reusable scaled-marginal interface with scale
    `(k/lambda)/(q+1)` and constant type weight. Finally,
    `paper_theorem1_iii_exponential_top_k_order_statistic_sequence_homogeneity`
    plus
    `theorem1_iii_exponential_top_k_order_statistic_sequence_formula` prove
    the `γ = 1` sequence limit from a concrete `O(1/N)` FOC certificate. The
    first measure-facing finite-sample top-`k` layer is also closed:
    `paper_theorem1_iii_exponential_finite_sample_top_k_sum_measurable`
    proves the concrete top-`k` sum random variable is measurable,
    `paper_theorem1_iii_exponential_finite_sample_top_k_sum_le_k_mul_max`
    bounds it by `k` times the finite-sample maximum whenever the maximum is
    nonnegative, and
    `paper_theorem1_iii_exponential_finite_sample_top_k_sum_integrable` proves
    integrability under the iid exponential product measure. The `k = 1`
    specialization is closed all the way back to the sample statistic:
    `paper_theorem1_iii_exponential_finite_sample_top_one_sum_eq_max` proves
    equality with the finite sample maximum on the nonnegative-product-measure
    support, and
    `paper_theorem1_iii_exponential_finite_sample_top_one_integral_harmonic_value`
    proves the exact harmonic iid expectation. The `k = 0` boundary is closed
    by `paper_theorem1_iii_exponential_finite_sample_top_k_zero_sum` and
    `paper_theorem1_iii_exponential_finite_sample_top_k_zero_integral_order_statistic`.
    The `k ≥ q` boundary is also closed:
    `paper_theorem1_iii_exponential_finite_sample_top_k_sum_eq_sum_of_card_le`
    proves equality with the full sample sum under coordinatewise
    nonnegativity, and
      `paper_theorem1_iii_exponential_finite_sample_top_k_card_le_integral_order_statistic`
      proves that the iid expectation matches the exact order-statistic oracle.
      The near-full `k = q - 1` endpoint is now closed by
      `paper_theorem1_iii_exponential_finite_sample_top_pred_card_eq_sum_sub_min`,
      the finite-sample minimum expectation theorem in `EconCSLib`, and
      `paper_theorem1_iii_exponential_finite_sample_top_pred_card_integral_order_statistic`.
      The threshold-count product-measure bridge is also closed:
      `paper_theorem1_iii_exponential_success_index_set_probability` gives the
      exact probability of a prescribed set of coordinates exceeding a
      nonnegative threshold, and
      `paper_theorem1_iii_exponential_success_count_probability` gives the
      binomial count mass, while
      `paper_theorem1_iii_exponential_success_count_tail_probability` gives
      the matching binomial upper-tail formula.
      `paper_theorem1_iii_exponential_success_count_measurable` and
      `paper_theorem1_iii_exponential_success_count_min_real_measurable` give
      the count measurability bridge, and
      `paper_theorem1_iii_exponential_success_count_min_integral_finite_sum`
      integrates the fixed-threshold truncated count into the exact finite
      binomial sum, and
      `paper_theorem1_iii_exponential_success_count_integral_eq_sum` proves
      the deterministic full-count layer-cake identity for nonnegative finite
      samples. The deterministic top-`k` truncated-count layer-cake identity is
      now closed by
      `paper_theorem1_iii_exponential_finite_sample_top_k_layer_cake`, and the
      iid product-measure expectation is reduced to that threshold layer by
      `paper_theorem1_iii_exponential_finite_sample_top_k_integral_layer_cake`.
      The Fubini swap and one-dimensional binomial-tail reduction are now
      closed by
      `paper_theorem1_iii_exponential_threshold_layer_cake_integral_swap` and
      `paper_theorem1_iii_exponential_finite_sample_top_k_tail_binomial_integral`.
      Each positive binomial mass is integrated into a finite alternating
      exponential-tail sum by
      `paper_theorem1_iii_exponential_binomial_mass_integral_alternating_sum`.
      The final mass simplification is now closed by
      `paper_theorem1_iii_exponential_binomial_mass_integral_closed_form`, and
      `paper_theorem1_iii_exponential_finite_sample_top_k_integral_order_statistic`
      proves that the iid top-`k` expectation equals the exact finite
      exponential order-statistic oracle for every nonzero sample size.
  - Theorem 1(iv)'s exact Pareto power-marginal checkpoint:
    `paretoPowerMarginalValue` has exact forward/backward marginal
    `q^-((α-1)/α)`, and
    `paper_theorem1_iv_pareto_power_marginal_scaled_marginal_certificate`
    exposes the corresponding reusable scaled-marginal limit certificate, and
    `paper_theorem1_iv_pareto_power_marginal_sequence_formula` exposes the
    direct equation (6) endpoint at the paper-numbered layer. Finally,
    `paper_theorem1_iv_pareto_power_marginal_sequence_homogeneity` proves the
    paper's `α/(α-1)` sequence-limit profile from a concrete `O(1/N)`
    sublinear FOC certificate. The direct equation (6) wrapper is
    `theorem1_iv_pareto_power_marginal_sequence_formula`.
  - Corollary 1's bounded/Pareto power-marginal realizations:
    `paper_corollary1_bounded_power_marginal_sequence_formula` rewrites an
    arbitrary `0 < γ < 1` into `β = γ/(1-γ)` and proves the exact
    `γ`-homogeneity sequence formula for the bounded power-marginal oracle.
    `paper_corollary1_pareto_power_marginal_sequence_formula` does the same
    for any `γ > 1` with `α = γ/(γ-1)`. These are still optimization-oracle
    realizations; the source-distribution construction remains the bounded
    and Pareto order-statistic derivation of the marginal laws.
  - Proposition 4's final minimization step:
    `Proposition4ContinuousSphereCertificate` captures the exact endpoint
    needed from the source's continuous-sphere proof. Once the analytic
    measure layer supplies the uniform profile's `Γ` value and the universal
    lower bound, `paper_proposition4_continuous_sphere_uniform_minimizes`
    proves that the uniform profile minimizes the relaxed large-`n` objective.
  - Lemma D.2's bounded finite-sum and pointwise-kernel assembly:
    `boundedLemmaD2IntegralTerm` now defines the source integral
    `∫_0^∞ choose(a,j) * G(x)^j * (1-G(x))^(a-j) dx`, and
    `BoundedLemmaD2LimitIntegralAsymptoticCertificate` is the sharpened
    exact-coefficient analytic target: the fixed-`j` source integral is
    asymptotic to
    `boundedLemmaD2LimitCoeff beta c j * a^(-1/β)` under either an explicit
    dominated-kernel certificate or the now-closed local CDF power-bound split
    route. The theorem
    `paper_lemmaD2_bounded_integral_term_sandwich` still turns the more
    general certificate into the uniform finite-index `(1±ε)` bounds needed
    downstream. `BoundedTailCDFPowerSandwich` records the near-zero CDF bound
    derived from the density asymptotic. It now also extracts concrete local
    power bounds (`exists_local_cdf_power_bounds`), and monotonicity plus
    bounded support constructs the finite split certificate through
    `BoundedLemmaD2SplitIntegralFiniteCertificate.ofCDFPowerSandwichMonotoneBoundedSupport`.
    The rescaling layer now proves
    `a*G(y*a^(-1/β)) -> (c/β)y^β`, the fixed-rank exponential kernel limit,
    and the pointwise binomial-kernel limit via
    `paper_lemmaD2_bounded_rescaled_cdf_nat_mul_tendsto`,
    `paper_lemmaD2_bounded_rescaled_cdf_one_sub_pow_sub_tendsto_exp`, and
    `paper_lemmaD2_bounded_rescaled_cdf_binomial_kernel_tendsto`.
    `paper_lemmaD2_bounded_rescaled_kernel_tendsto_limit` rewrites the
    binomial-kernel limit as the exact gamma-kernel integrand.
    `boundedLemmaD2LimitCoeff_eq_gamma` evaluates the limiting kernel integral
    by the gamma integral and `boundedLemmaD2LimitCoeff_pos` proves the fixed
    coefficient is positive. The source-kernel bookkeeping now has direct
    proofs: `boundedLemmaD2IntegralKernel_measurable` derives measurability
    from `Measurable G`,
    `boundedLemmaD2IntegralKernel_norm_le_choose_of_cdf_range` bounds the
    source kernel under `0 ≤ G ≤ 1`,
    `boundedLemmaD2IntegralKernel_eventually_integrableOn_of_bounded_support`
    proves eventual integrability from bounded-support CDF conditions, and
    `boundedLemmaD2IntegralTermAbove_le_geometric_support_bound` proves the
    finite-support geometric envelope for the above-`δ` tail integral under a
    positive lower CDF bound on that tail.
    `boundedTailScale_choose_geometric_tail_ratio_tendsto_zero` proves that
    this binomial/geometric envelope is `o(a^(-1/β))`, and
    `boundedLemmaD2IntegralTermAbove_negligible_of_geometric_support_bound`
    transfers that scalar fact to the actual above-`δ` integral. Finally,
    `boundedLemmaD2IntegralTerm_split` /
    `boundedLemmaD2IntegralTerm_eventually_split` prove the exact near-zero
    plus tail decomposition. The source change of variables
    `x = y*a^(-1/β)` is also proved directly in
    `boundedLemmaD2IntegralTerm_changeOfVariables`, with below-`δ` and
    above-`δ` variants in
    `boundedLemmaD2IntegralTermBelow_changeOfVariables` and
    `boundedLemmaD2IntegralTermAbove_changeOfVariables`. The rescaled integral
    is split at the growing threshold by
    `boundedLemmaD2RescaledIntegral_split`, and
    `boundedLemmaD2GrowingRescaledIntegral_tendsto_of_full_and_source_tail`
    converts full rescaled convergence plus source-tail negligibility into the
    paper's growing near-zero rescaled convergence target.
    `boundedLemmaD2RescaledKernel_aestronglyMeasurable` derives rescaled-kernel
    measurability from `Measurable G`. The explicit
    `BoundedLemmaD2DominatedKernelCertificate` and
    `BoundedLemmaD2DominatedIntegralAsymptoticCertificate` layer now formalizes
    the paper's dominated-convergence step as a precise envelope obligation;
    from those fields Lean proves the fixed-rank integral asymptotic and
    converts it into the exact-gamma finite-index certificate. The paper-style
    near-zero/tail route is also represented by
    `BoundedLemmaD2SplitIntegralAsymptoticCertificate` and
    `BoundedLemmaD2SplitIntegralFiniteCertificate`: a near-zero gamma
    asymptotic plus a tail `o(a^(-1/β))` proof now feeds the same exact-gamma
    source-loss theorem. The constructors
    `BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofAsymptotics` and
    `.ofBoundedSupportAsymptotics` show the source inputs cleanly. The newer
    `.ofBoundedSupportNearZeroAsymptotic` constructor discharges the tail field
    internally from bounded support plus a positive above-`δ` CDF floor, leaving
    only the near-zero gamma asymptotic for the direct split route. The
    `.ofFullAsymptoticAndTail` and `.ofDominatedKernelAndGeometricTail`
    constructors also reconcile the global dominated-convergence route with
    the paper-style split route by proving the near-zero split field from the
    full asymptotic minus the negligible tail.
    `BoundedLemmaD2FiniteSumCertificate` records one positive
    `a^(-1/β)` asymptotic for each fixed source `(i,j)` rank-integral term,
    and `paper_lemmaD2_bounded_top_k_loss_asymptotic_of_rank_terms` proves
    that their finite double sum has the same scale with the summed positive
    coefficient. The nested-display wrapper
    `paper_lemmaD2_bounded_nested_top_k_loss_asymptotic_of_rank_terms` exposes
    the same result in the paper's literal `i`/`j` summation form. This closes
    the finite assembly from equation (96)-style per-term asymptotics to the
    top-`k` bounded loss. The wrapper
    `paper_theorem1_ii_bounded_reflected_source_loss_asymptotic` also verifies
    the reflection algebra in equations (91)-(95): once the original upper
    order-statistic means are `M` minus the reflected nested sums, the source
    loss `M k - h(a)` inherits the same asymptotic. The exact-coefficient
    wrappers
    `paper_lemmaD2_bounded_integral_top_k_loss_asymptotic_of_limit_coeff` and
    `paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_limit_coeff`
    use the gamma coefficients directly. The dominated-certificate wrappers
    `paper_lemmaD2_bounded_integral_term_asymptotic_of_dominated_certificate`,
    `paper_lemmaD2_bounded_integral_top_k_loss_asymptotic_of_dominated_certificate`,
    `paper_lemmaD2_bounded_integral_term_split`,
    `paper_lemmaD2_bounded_integral_kernel_eventually_integrableOn_of_bounded_support`,
    `paper_lemmaD2_bounded_integral_term_above_le_geometric_support_bound`,
    `paper_lemmaD2_bounded_tail_scale_choose_geometric_tail_ratio_tendsto_zero`,
    `paper_lemmaD2_bounded_integral_term_above_negligible_of_geometric_support_bound`,
    `paper_lemmaD2_bounded_integral_term_below_changeOfVariables`,
    `paper_lemmaD2_bounded_integral_term_above_changeOfVariables`,
    `paper_lemmaD2_bounded_rescaled_integral_split`,
    `paper_lemmaD2_bounded_growing_rescaled_integral_tendsto_of_full_and_source_tail`,
    `paper_lemmaD2_bounded_split_certificate_of_full_asymptotic_and_tail`,
    `paper_lemmaD2_bounded_split_certificate_of_bounded_support_asymptotics`,
    `paper_lemmaD2_bounded_split_certificate_of_bounded_support_near_zero_asymptotic`,
    `paper_lemmaD2_bounded_split_certificate_of_dominated_kernel_and_geometric_tail`,
    `paper_lemmaD2_bounded_integral_top_k_loss_asymptotic_of_split_certificate`,
    and
    `paper_theorem1_ii_bounded_reflected_integral_source_loss_asymptotic_of_split_certificate`
    are now public. The direct split route from source-facing bounded-tail CDF
    assumptions is closed. The remaining bounded-family work is the higher
    order-statistic layer: connect actual `μ_D(i,a)` means for a general
    bounded-support distribution to the reflected-CDF integral interface.
  - Corollary 3, i.i.d. Bernoulli asymptotic `0`-homogeneity.
  - Theorem 3 log-share asymptotic and all-consumed argmax endpoint.
  - Theorem 2 top-one and all-consumed decaying-Bernoulli branches, with the
    nondegenerate assumptions documented in the README.
  - Theorem 1(v), all-consumed/no-consumption-constraint common-mean core.
- Partially formalized:
  - Proposition 2: uniform top-`k` source route is closed asymptotically through
    a finite `(2T+2)/N` bound and now feeds Theorem 1(ii)'s `β = 1`,
    `γ = 1/2` bounded-support profile API. The paper's sharper `(T+1)/N`
    finite bound and the printed relaxed-optimizer formula remain caveated.
  - Theorem 1(i)-(iv) and Corollary 1: source-shaped certificate wrappers
    exist, the exact exponential top-one product-measure maximum branch is
    closed, the exact finite top-`k` exponential order-statistic optimization
    branch is closed, the exact bounded power-marginal optimization branch is
    closed and exposes a scaled-marginal certificate, the bounded Lemma D.2
    pointwise-kernel/gamma-coefficient,
    geometric-tail-negligibility, split/dominated bridge, and
    dominated-certificate assembly are closed conditional on the source
    domination fields, and the exact Pareto power-marginal optimization branch
    is closed and exposes a scaled-marginal certificate, but the remaining
    distribution-family order-statistic/probability derivations remain.
  - Lemma D.1: the optimizer-sequence endpoint and reusable scaled-count
    bridges exist, but the four analytic alternatives for `h` are not all
    proved from source distributions.
- Not started or intentionally deferred:
  - Proposition 4's analytic sphere layer: the profile space, uniform sphere
    measure, cosine-distance kernel, full-support user measure, Fubini/symmetry
    constant, and Laplace-principle reduction.
  - Distribution-specific proofs that concrete sampled value laws instantiate
    the Definition 3 `μ_D(i,a)` order-statistic-mean interface beyond the
    uniform instance.

## Active Target

The immediate target is the continuous source-distribution layer for Theorem
1(ii) and Theorem 1(iv), not another optimization wrapper. The current PRPKG
build already closes the finite-discrete branch under explicit source
assumptions, the exponential finite-sample top-`k` order-statistic branch, the
bounded and Pareto exact power-marginal optimization checkpoints, Lemma D.2's
bounded-tail analytic finite-sum assembly, and the conditional Proposition 4
endpoint. The missing proof is the bridge from actual sampled bounded/Pareto
laws to the `μ_D(i,a)` / `TopKValueOracle` objects consumed by those closed
optimization and asymptotic layers.

For the bounded branch, the strongest compiled endpoints are
`paper_lemma1_bounded_support_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support`
and
`paper_lemma1_bounded_support_order_statistic_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support`.
The latter consumes the paper's bottom-indexed `μ_D` interface directly after
the finite-prefix `min k a` bridge. It still needs a source-mean identity of
the form
`sourceMean i a = M - ∑ j, boundedLemmaD2IntegralTerm G j a`. The next proof
should construct this identity from an actual real-valued distribution with
upper endpoint `M`, reflected CDF `G(x) = P[M - X <= x]`, and the paper's
order-statistic means `μ_D(a-i+1,a)`. The `a < k` finite prefix is now handled
by `paper_definition3_order_statistic_topk_loss_eventually_eq_fin_loss`; do not
force small sample sizes into the asymptotic identity. The expectation bridge
from a family of finite sample laws to a global `μ_D(rank,a)` is compiled as
`expectedOrderStatisticMeanSeq` and
`paper_definition3_expected_order_statistic_mean_seq_topk_endpoint_loss_eq_expected_reflected_bottom_sum`;
the Lemma 1 wrapper over those expected order statistics is
`paper_lemma1_bounded_support_expected_order_statistic_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support`.
The aggregate Lemma 1 wrapper
`paper_lemma1_bounded_support_expected_reflected_bottom_top_k_loss_asymptotic_of_cdf_power_sandwich_monotone_bounded_support`
is now the preferred bounded-source boundary: it needs only eventual
integrability/probability facts plus the single distribution-specific CDF
identity for `expectedReflectedBottomKSum`.
Coordinatewise bounded support now discharges the finite sorted-tuple
integrability hypotheses through
`paper_definition3_sample_order_statistic_topk_range_integrable_of_ae_bounds`,
`paper_definition3_sample_topk_sum_integrable_of_ae_bounds`, and the
`_of_ae_bounds` Definition 3 expectation/reflection wrappers.
The pointwise reflected-bottom layer-cake bridge is compiled as
`paper_definition3_reflected_bottom_sum_eq_integral_rank_count_indicator`;
the reusable measure-level bridge is
`EconCSLib.Probability.expectedReflectedBottomKSum_eq_integral_rank_count_layer_of_integrable`,
and the paper-facing bounded endpoint is
`paper_lemma1_bounded_support_expected_reflected_count_layer_top_k_loss_asymptotic_of_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support`.
Coordinatewise bounded support now also discharges the count-layer
product/Fubini integrability through
`EconCSLib.Probability.reflectedBottomKRankCountLayer_integrable_prod_of_ae_bounds`.
The fixed-threshold iid product calculation is compiled as
`paper_definition3_iid_reflected_count_layer_inner_integral_binomial`, and the
version matching the bounded Lemma D.2 source kernel is
`paper_definition3_iid_reflected_count_layer_inner_integral_kernel`. The outer
positive-threshold integral/sum assembly is compiled as
`paper_definition3_iid_reflected_count_layer_integral_kernel_of_integrable_of_le`,
and bounded support for `G` discharges the finite kernel integrability bundle
via
`paper_lemmaD2_bounded_integral_kernel_eventually_fin_integrableOn_of_bounded_support`.
The strongest iid bounded Lemma 1 endpoint is now
`paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_cdf_power_sandwich_monotone_bounded_support`;
the generic library lemma
`EconCSLib.Probability.iidProductMeasure_forall_bounds_ae` lifts
one-dimensional support to product-sample support, and this strongest wrapper
defines `G` as the reflected CDF `x ↦ P[M - X <= x]`. Its remaining
distribution-specific inputs were the Lemma D.2 facts for that reflected CDF.
The newer endpoint
`paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail`
pushes the routine reflected-CDF facts into the reusable probability library:
`EconCSLib.Probability.reflectedCDFMass_measurable`,
`reflectedCDFMass_mono`, `reflectedCDFMass_nonneg`,
`reflectedCDFMass_le_one`, and `reflectedCDFMass_eq_one_of_ae_bounds` now
derive measurability, monotonicity, range, and upper-support saturation from
one-dimensional a.e. bounds. The remaining bounded-family analytic input is a
`BoundedTailCDFPowerSandwich (reflectedCDFMass baseMeasure M) β c`, plus
base-law support and positive support width `0 < M - L`. If the concrete law
has an exact local reflected-CDF power identity, use
`paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power`;
it builds the sandwich through
`BoundedTailCDFPowerSandwich.of_eventually_eq_const_mul_power`. The special
identity-CDF case is recorded as
`BoundedTailCDFPowerSandwich.identity_beta_one`. The continuous uniform
`[0,1]` instance is now compiled: `uniform01Measure`,
`uniform01Measure_ae_bounds`,
`uniform01_reflectedCDFMass_eventually_eq_power`, and
`paper_lemma1_uniform01_iid_reflected_cdf_count_layer_top_k_loss_asymptotic`
prove the concrete iid source-law Lemma 1 endpoint with `β = c = 1`.
The loss-to-forward-marginal step is now compiled, but intentionally requires
an explicit discrete-drop regularity assumption:
`bounded_source_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop`
turns `A - h(q) ~ C*q^(-1/β)` into
`h(q+1)-h(q) ~ (C/β)*(q+1)^(-((β+1)/β))` when
`(q+1)*((A-h(q))-(A-h(q+1)))/(A-h(q)) -> 1/β`.  The scale bridge records the
off-by-one factor
`boundedTailScale_div_succ_ratio_eventually_eq_rpow`, namely
`((q+1)/q)^(1/β) -> 1`; future proofs should not subtract asymptotic
equivalents directly. Source-level wrappers are
`paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_tail_and_scaled_drop`
and
`paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_forward_marginal_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power_and_scaled_drop`.
The marginal result feeds the reusable optimization-facing interface through
`BoundedOrderStatisticScaledMarginalCertificate` and
`BoundedOrderStatisticScaledMarginalCertificate.toTopKScaledMarginalLimitCertificate`;
paper-facing wrappers are
`paper_theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_source`
and
`paper_theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_loss_ae_and_scaled_drop`.
The older per-rank route
`paper_definition3_expected_reflected_bottom_sum_eq_sum_reflected_order_statistic_integrals_of_le`
is still useful after the eventual `k ≤ a` prefix, but the count-layer wrapper
is closer to the CDF/binomial source proof.

For the Pareto branch, the optimizer layer is already represented by
`paretoPowerMarginalScaledMarginalLimitCertificate` and
`paper_theorem1_iv_pareto_power_marginal_sequence_formula`. The remaining
probability proof should derive a `TopKScaledMarginalLimitCertificate` directly
from Pareto order-statistic means, or prove an asymptotically equivalent
source-marginal certificate that feeds the same eventual FOC bridge. The paper
cites external order-statistic facts for Lemma D.4, so the Lean plan can first
expose an auditable source certificate for those gamma-ratio asymptotics, then
replace it with a full integral/gamma proof if needed. This certificate
boundary now exists as `ParetoOrderStatisticScaledMarginalCertificate` and
`paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_source`.
The generic Gamma-ratio and finite-difference pieces have been moved to
`EconCSLib.Foundations.Math.GammaAsymptotics`; PRPKG keeps paper-facing wrappers
for the exact Lemma D.4 constants and sequence.
If the source calculation is more naturally proved as an
`AsymptoticEquivalent`, use
`ParetoOrderStatisticScaledMarginalCertificate.ofConstMulScaleAsymptoticEquivalent`
or
`paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_asymptotic_equivalent`.
If the source proof is naturally rank-by-rank, use
`ParetoOrderStatisticScaledMarginalCertificate.ofFiniteRankScaledLimits` or the
paper-facing
`paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_finite_rank_scaled_limits`:
it only asks for one scaled marginal limit per fixed rank and the finite
coefficient sum. If the paper route first proves the fixed-rank value
asymptotic `μ(q-r,q) ~ C*q^(1/α)` plus the explicit scaled-drop limit, use
`pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop` or the
paper-facing
`paper_lemmaD4_pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop`
to obtain the needed per-rank scaled marginal limit. For the paper's canonical
gamma coefficients, Lean now also proves the exact gamma-ratio sequence route:
`gamma_ratio_nat_add_one_sub_asymptoticEquivalent`,
`paretoRankGammaRatioMean_value_asymptoticEquivalent`,
`paretoRankGammaRatioMean_scaled_drop`, and
`paretoRankGammaRatioMean_scaled_limit`, exposed paper-side as
`paper_lemmaD4_pareto_rank_gamma_ratio_mean_scaled_limit`. Use
`paretoRankMarginalCoeff` and
`paper_theorem1_iv_pareto_order_statistic_scaled_marginal_certificate_of_pareto_rank_scaled_limits`;
positivity and the aggregate coefficient sum are then automatic. The remaining
proof is the measure/order-statistic identification of actual Pareto `μ_D`
with this exact gamma-ratio sequence, plus the strict-concavity claim. Source
note: the PDF's equation (135) appears to print `B log a`, but equations (77),
(131), and Lemma D.4 all point to `B * a^(1/α)`.

Corollary 1 should be closed only after the bounded and Pareto source
distribution certificates exist. The parameter algebra is already verified:
`γ = 0` routes through finite discrete, `0 < γ < 1` through bounded, `γ = 1`
through exponential, and `γ > 1` through Pareto. The final corollary should be
a thin distribution-existence wrapper over those branch certificates.

## Execution Plan To Finish

1. Keep the current build baseline green with `lake build PRPKG24AccuracyDiversity`
   before and after each coherent batch. In the shared worktree, edit only PRPKG
   files and genuinely reusable probability-library files; leave unrelated
   GLM/EOS/LMMS/GN changes and `review_slices.json` deletions untouched.
2. Continue from the reusable real order-statistics source layer in
   `EconCSLib.Foundations.Probability.OrderStatistics`: `ascendingOrderStatistic`,
   `upperOrderStatistic`, `sampleTopKSum`,
   `upperOrderStatistic_eq_endpoint_sub_reflectedAscending`, and
   `sampleTopKEndpointLoss_eq_reflectedBottomKSum` are compiled. The generic
   expectation layer is also compiled:
   `expectedSampleTopKSum_eq_sum_expectedUpperOrderStatistic`,
   `expectedSampleTopKEndpointLoss_eq_expectedReflectedBottomKSum`,
   `expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum`, and
   `expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum`.
   The sorted tuple functions now have reusable measurability and
   bounded-support integrability lemmas (`ascendingOrderStatistic_measurable`,
   `sampleTopKSum_integrable_of_ae_bounds`, and the PRPKG
   `sampleOrderStatisticValue` wrappers). They also have a deterministic
   rank-count layer-cake identity for reflected bottom-`k` sums. The iid
   product/binomial and outer count-layer bridge for bounded reflected samples
   is now compiled. The reflected-CDF routine facts for bounded iid laws are
   also in `EconCSLib.Foundations.Probability.RealDistribution` via
   `reflectedCDFMass`; the next missing bounded law-specific layer is the
   near-zero `BoundedTailCDFPowerSandwich` proof for concrete bounded families.
3. In PRPKG, instantiate the bounded source bridge:
   prove the source-tail sandwich for
   `EconCSLib.Probability.reflectedCDFMass baseMeasure M`, or prove the exact
   local power identity and apply
   `paper_lemma1_bounded_support_iid_reflected_cdf_count_layer_top_k_loss_asymptotic_of_base_ae_bounds_and_reflected_cdf_eventually_eq_power`
   to obtain the `M*k - h(a)` asymptotic as the paper's Lemma 1. The uniform
   `[0,1]` case already follows this route through
   `paper_lemma1_uniform01_iid_reflected_cdf_count_layer_top_k_loss_asymptotic`.
   The exact uniform top-`k` order-statistic closed form is also now compiled
   directly as the bounded `β = 1` scaled-marginal certificate
   `paper_theorem1_ii_uniform_order_statistic_scaled_marginal_certificate`.
   To get the marginal asymptotic, prove the scaled-drop limit above and then
   use the compiled source wrappers ending in `_and_scaled_drop`; this is the
   sanctioned route to the bounded scaled-marginal certificate. The generic
   certificate constructor is
   `paper_theorem1_ii_bounded_order_statistic_scaled_marginal_certificate_of_loss_ae_and_scaled_drop`.
4. Instantiate Pareto from the same probability interface. The current
   certificate boundary is `ParetoOrderStatisticScaledMarginalCertificate`:
   prove its `marginal_ratio_tendsto` field from the paper's cited Lemmas
   D.10/D.11 route, with the maximum asymptotic, fixed-rank gamma-ratio
   multiplier, strict concavity/diminishing marginals, and positive leading
   constant recorded as supporting lemmas. The certificate already constructs
   the actual Pareto `TopKScaledMarginalLimitCertificate`.
5. Close Corollary 1 by assembling the four branch witnesses, then refresh the
   human-facing surface (`PaperInterface.lean`, README status, and DAG wording)
   only after the Lean branch wrappers compile. Do not start the continuous
   sphere Proposition 4 layer until Theorem 1 and Corollary 1 have this
   source-distribution bridge.

## Do Not Work On Next

- Do not touch `GLM20DroppingStandardizedTesting`, `GN21DriverSurgePricing`, or
  `LG21TestOptionalPolicies`; those are active lanes for other agents.
- Do not start the continuous sphere Proposition 4 before Theorem 1 and
  Corollary 1 have the bounded/Pareto source-distribution route.
- Do not replace source-numbered theorem rows with auxiliary heterogeneous or
  mixed Bernoulli certificate endpoints.
