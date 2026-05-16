# Foundations: Probability

Use for `EconCSLib/Foundations/Probability/*`, finite PMFs, expectations,
conditional probability, finite variance, finite Markov kernels/chains/MDPs,
stochastic dominance/couplings, concentration, measure inequalities,
continuous densities, CTMCs, renewal-reward reductions, and RUM/noise models.

## Continuous Reward And CTMC Seams

- For two-state CTMC reward papers, separate primitive accounting from reward
  rates. Prove measured `T`, `Q`, and scaled-earning identities first, then
  derive measured reward-rate statements only when positive mass/time
  denominators are available.
- When a source lemma fixes an arbitrary current policy but the theorem
  constructs prices using accept-all target rates, introduce an effective
  current ratio instead of rewriting the current reward rate to the target
  rate. The reusable pattern is: target accounting `z = ratio*(m-Rtarget)`,
  current reward bound `Rcurrent <= Rtarget`, positivity of `m-Rtarget`, then
  construct `z/(m-Rcurrent)` and prove it is positive and no larger than the
  target ratio.
- Prefer sequential CTMC IC routes when the paper proof is sequential. Move
  the state whose lemma works with the arbitrary current fixed state first;
  after that state is accept-all, discharge the second-state lemma with the
  theorem's target accept-all accounting. This avoids false fixed-state
  reward-rate equalities.
- Audit fixed-state transfer assumptions algebraically. If lower and upper
  bounds demand opposite cross-ratio directions, do not assume equality unless
  the source proves it. Try replacing one direction with a direct endpoint
  sign proof; for GN21 Lemma 9, current lower-endpoint nonpositivity plus only
  the upper fixed-state comparison is enough.
- For CTMC fixed-state complement comparisons, exploit the monotonicity of
  `q(t)/t` before adding certificate fields. A reject-long policy has accepted
  trips shorter than every rejected trip, so strict antitonicity of `q(t)/t`
  gives the lower pointwise side after cross-multiplication and integration.
  In Lean, prove the pointwise cross-product first, rewrite
  `setIntegral_mono_on` with `integral_const_mul`, then scale by the
  nonnegative arrival rate. This often turns a false-looking complement
  equality assumption into a single remaining upper-inequality obligation.
- For renewal-reward papers, do not leave every stochastic step behind an
  opaque "LLN certificate" if the source proof only needs IID cycle averages.
  Mathlib has `ProbabilityTheory.strong_law_ae_real`; wrap it once for
  empirical means and reward/time quotients, then define a paper-local
  IID-cycle model whose fields are the cycle random variables, integrability,
  pairwise independence, identical distribution, and the expected-cycle
  identities from Wald/geometric calculations. This closes sample-path
  ratio/time-fraction theorems with strong-law proof terms and keeps only the
  source's actual cycle-construction assumptions in the theorem signature.
- Keep the paper-facing source boundary honest: denominator-valid reward-rate
  routes should quantify over feasible measurable policies with positive mass,
  while broader measurable wrappers should either keep explicit positive-mass
  obligations or use scaled-earning/accounting forms that avoid division.
- For GN21-style two-state CTMC surge proofs, the useful "support any ratio"
  paragraph is a small-ratio construction, not a claim that the current fixed
  reward equals the target accept-all reward. Prove a scalar lemma of the form:
  for any envelope `Rmax`, if `0 < R2*T2 - Rmax*(T2-1)` and the Lemma 9 upper
  endpoint is positive, choose a sufficiently small positive surge ratio so
  `m2 > Rmax`, accounting holds, and `z2 < U*(m2-Rmax)`. Then wrap it with the
  current lower-endpoint nonpositivity to get a feasible Lemma 9 ratio.
- For signed structured-price envelopes, use two layers. First prove the
  current reward is below `Rmax = m0` when `z0 <= 0`, or below
  `Rmax = m0 + z0*lambda12` when `0 <= z0`. Second prove the small-ratio
  zero-ratio numerator `0 < R2*T2 - Rmax*(T2-1)`. The `Rmax = R2` branch is
  immediate from `R2 > 0`; the positive-`z0` branch should be derived from the
  non-surge ratio formula/feasibility assumptions, or recorded as the exact
  missing source regime condition.
- To avoid token-heavy Lean retries in CTMC algebra, name the denominator and
  numerator identities before using inequalities. Prove `m-r = numerator/den`
  and `z = ratio*B/den`, then transfer slack by
  `div_lt_div_of_pos_right` instead of letting `ring_nf` expand a whole
  reward-rate inequality. For small-ratio existence, choose
  `ratio = min upper (min eps_slack eps_positive) / 2` and derive each
  half-bound with explicit positive-denominator multiplication.
- When the current Lemma 9 upper endpoint varies with the fixed current
  policy, prove a policy-uniform positive lower bound first and transfer slack
  with one monotonic multiplication lemma. This is cheaper and clearer than
  rebuilding the surge construction for every current upper expression.

## Finite PMF and Expectation Seams

- For finite expectation decompositions, prove pointwise identities first, then
  `pmfExp`/`pmfPairExp` sum identities, then the paper-facing equivalence.
  Group by the event or fiber appearing in the paper.
- For sequential weighted without-replacement or "first distinct draw" models,
  audit conditioning/deletion claims before proving them. Conditioning on an
  item being absent from the first `k` distinct draws is generally not the same
  as deleting that item's weight when weights are nonuniform and `k >= 2`. If a
  source proof says conditioning equals deletion, test a small numeric model
  outside Lean, then formalize the inequality actually needed directly. Keep
  false equalities or false deletion upper bounds only as clearly named rejected
  scratch targets, never as theorem assumptions hidden inside green
  paper-facing results. If small audits show the generalized theorem is false,
  record the counterexample and redirect the paper proof to a corrected
  statement instead of continuing proof search.
- For probability-delta comparisons, prove the tiny indicator inequality over
  the finite outcome type, then lift it with a generic PMF lemma comparing
  indicator differences.
- For finite independent-sampling concentration, check Mathlib's
  `Probability.Moments.SubGaussian` before proving Chernoff/Hoeffding from
  scratch. A fast reusable seam is: compose independent variables with a
  centering map, use `hasSubgaussianMGF_of_mem_Icc` for bounded variables, and
  expose a paper-facing wrapper over `measure_sum_ge_le_of_iIndepFun`.
- If a broad shared probability file is dirty or being edited by another
  formalization thread, do not spend proof time repairing unrelated theorem
  experiments. Put the needed stable seam in a focused module with distinct
  names, import that module in the paper-facing file, and leave the shared file
  unstaged unless you intentionally own its changes.
- For strict event monotonicity, split the larger event into the smaller event
  plus a residual event and prove positive residual mass from a finite atom
  witness.
- For two-outcome probabilities, first prove `wrong = 1 - correct`, then turn
  `wrong < correct` into `1 / 2 < correct` when that matches the paper proof.
- For pairwise probability monotonicity, define unnormalized `correctWeight`
  and `wrongWeight`, prove their sum is the partition/mass of the relevant
  sample space, and only then normalize. If the paper proof cancels common
  factors to a reduced finite sum, expose a named reduction bridge from actual
  weights to reduced weights; keep the source theorem conditional until that
  bridge is discharged.
- For finite analytic PMF families, prove continuity at the atom level
  `fun theta => ((mu theta) a).toReal`, then lift through finite expectation
  lemmas such as `epsilonContinuousAt_pmfExp_of_atom`.
- For pure PMFs, use lemmas such as `pmfExp_pure`,
  `pmfPairExp_pure_left`, and `pmfPairExp_pure_right` when available.
- For finite-label papers, start from
  `EconCSLib.Foundations.Probability.FiniteLabel`: use
  `finiteLabelIndicator`, `finiteLabelShare`,
  `finiteLabelAggregateScore`, `FiniteLabelSimplex`,
  `sum_finiteLabelShare_eq_measureReal_univ`,
  `sum_finiteLabelAggregateScore_eq_measureReal_univ_of_measurable_simplex`,
  and the finite-label MAE bounds/integrability lemmas before writing
  paper-local indicator integrals. This is the DSWG-style source interface for
  label shares, aggregate posteriors, posterior-simplex constraints, and
  classifier-error terms.
- For finite Bayesian signal kernels, use
  `EconCSLib.Foundations.Probability.Kernel`:
  `pmfKernelJoint`, `pmfKernelSignalMarginal`,
  `pmfKernelSignalProb`, `pmfKernelPosteriorExpectation`,
  `pmfKernelPosteriorExpectation_mul_signalProb_eq_sum_of_pos`,
  `pmfKernelPosteriorExpectation_const_one_eq_one_of_pos`,
  `pmfKernelPosteriorExpectation_nonneg_of_nonneg`,
  `pmfKernelPosteriorExpectation_le_of_forall_le`,
  `pmfKernelPosteriorExpectation_mem_Icc_of_mem_Icc`, and
  `pmfKernelJointExp`. For admissions/testing papers using
  `AdmissionsModel`, prefer the thin `admissionsPosteriorExpectation_*`
  wrappers.
- For ordinary finite conditional expectations, use
  `pmfConditionalExp_mul_prob_eq_indicatorExp_of_pos`,
  `pmfConditionalExp_const_one_eq_one_of_pos`,
  `pmfIndicatorExp_nonneg_of_nonneg`,
  `pmfIndicatorExp_le_prob_mul_of_forall_le`,
  `pmfConditionalExp_nonneg_of_nonneg`,
  `pmfConditionalExp_le_of_forall_le_of_pos`, and
  `pmfConditionalExp_mem_Icc_of_mem_Icc_of_pos`. These are the right tools for
  bounded posterior estimates, resampling policies, and conditioning-on-event
  arguments before introducing source-specific Gaussian algebra.
- For Gaussian admissions/testing papers, start with
  `EconCSLib.Foundations.Probability.Gaussian` before making paper-local
  definitions. Use `GaussianScaleLaw.standardize`,
  `StandardGaussianCDFAPI.normalCDF_mono`,
  `GaussianPriorSignal.posteriorVariance_eq_mul_div`,
  `GaussianPriorSignal.posteriorMean_eq_weightedAverage`,
  `GaussianPriorSignal.posteriorMean_eq_priorMean_add_signalWeight_mul`,
  `GaussianPriorSignal.posteriorMean_mono`,
  `GaussianPriorSignal.posteriorMeanSignalCutoff`,
  `GaussianPriorSignal.threshold_le_posteriorMean_iff`,
  `GaussianPriorSignal.threshold_le_posteriorMeanOfSignalWithNoiseMean_iff`,
  `GaussianPriorSignal.thresholdPassProb_posteriorMeanRawSignalScaleLaw`,
  `GaussianPriorSignal.posteriorMeanLaw`, and
  `GaussianSignalFamily.posteriorMean_mono_of_pointwise_le` for conjugate
  Gaussian posterior algebra. Use
  `GaussianSignalFamily.posteriorMean_eq_weighted_sum` for finite feature sets,
  `GaussianSignalFamily.posteriorVariance_le_priorVar`, and
  `GaussianSignalFamily.posteriorMeanVariance_nonneg` for finite-feature
  posterior variance comparisons,
  `GaussianSignalFamily.posteriorMeanLaw` and
  `GaussianOffsetSignalFamily.posteriorMeanLaw` when a source lemma states the
  distribution of estimated skill/posterior mean,
  and use `GaussianOffsetSignalFamily` when source features have the form
  `q + noiseMean k + centeredNoise k`. Use
  `GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt`
  when a testing paper compares posterior-score marginal scales across
  different feature sets; this avoids forcing full/test-free features into the
  same finite index type just to reuse same-index precision lemmas.
  Use
  `GaussianOffsetSignalFamily.conditionalPosteriorMeanScaleLaw` and
  `GaussianOffsetSignalFamily.conditionalPosteriorMeanScaleLaw_standardize_threshold`
  when a paper conditions on true skill and writes the posterior-score
  admission probability as `1 - Phi((priorTerm - precision*(q-threshold)) /
  sqrt precision)`.
  Use `StandardGaussianTailLimitAPI` when the paper concludes that a difference
  of high-skill admission probabilities tends to zero because both affine
  upper tails tend to one. Use `StandardGaussianAnalyticAPI` when a paper lemma
  needs the doubled-log density comparison and the high-skill CDF tail limit to
  refer to the same abstract normal CDF/density implementation.
  Use
  `GaussianScaleLaw.affineImage` and
  `StandardGaussianCDFAPI.thresholdPassProb_affineImage_pos` when a paper
  pushes a Gaussian signal through a positive affine posterior-score map. Use
  `StandardGaussianCDFAPI.thresholdPassProb_antitone_threshold` and
  `StandardGaussianCDFAPI.thresholdPassProb_le_of_mean_le_same_scale` for
  cutoff/mean monotonicity. Use
  `StandardGaussianQuantileAPI.lt_standardTail_iff_lt_quantile_one_sub` and
  `StandardGaussianQuantileAPI.standardTail_lt_iff_quantile_one_sub_lt` for
  strict best-response or threshold-uniqueness arguments around an inverse-CDF
  cutoff; prove strict payoff order from these lemmas instead of duplicating
  CDF algebra in a paper file. Use
  high-skill affine-tail delta wrappers only after auditing the exact slope
  order they require. A source phrase like "unequal precision" may give only a
  full-policy ordering, while an eventual comparison of full-minus-sub upper
  tails can require a separate test-free slope ordering; keep that extra
  premise explicit unless it is actually derived from the raw model. Use
  `StandardGaussianCDFAPI.mixtureTailMass_antitone_threshold` and
  `StandardGaussianCDFAPI.MixtureThresholdCertificate` for source equations
  where a common admission cutoff realizes a finite group-mixture capacity.
  When a paper assumes a cutoff family continuously clears fixed capacity, first
  try proving continuity from the capacity equation itself: a finite Gaussian
  mixture mass is continuous in the access parameter and strictly antitone in
  the cutoff, so the level-set squeeze often removes a standalone continuity
  hypothesis from the paper-facing theorem. Use
  `EconCSLib.Foundations.Probability.GaussianDerivatives` for admissions
  lemmas that differentiate affine standardized Gaussian upper tails:
  `StandardGaussianDerivativeAPI.affineUpperTail_hasDerivAt`,
  `StandardGaussianDerivativeAPI.affineUpperTailDifference_hasDerivAt`, and
  the corresponding continuity lemmas discharge raw derivative/continuity
  premises quickly. Use
  `StandardGaussianDerivativeAPI.affineUpperTail_gt_iff_cutoff_lt_of_slope_lt`
  when a paper states that one affine Gaussian admission probability exceeds
  another exactly above a skill cutoff. When a paper compares normal-density terms by taking logs,
  check whether the source silently doubled logs and canceled the shared
  standard-normal normalizing constant; if so, use
  `StandardGaussianDoubledLogDensityAPI` and prove a doubled-log identity
  instead of trying to force an impossible raw `log weighted = -z^2 + log
  precision` equality.
  Mathlib has concrete real Gaussian measures and PDF facts in
  `Mathlib.Probability.Distributions.Gaussian.Real` (`gaussianReal`,
  `gaussianPDFReal`, Gaussian laws, affine transforms, moments). Use those
  before creating any new primitive normal-distribution definitions. For the
  concrete standard-normal CDF/density layer, use
  `EconCSLib.Foundations.Probability.GaussianMathlib`: continuity is fastest
  through `ProbabilityTheory.cdf` as a Stieltjes function plus `NoAtoms`,
  strict monotonicity through positive Gaussian mass on `Ioc` via
  `setLIntegral_pos_iff` and `support_gaussianPDF`, and the median through
  `gaussianReal_map_neg` plus `probReal_compl_eq_one_sub`. For real
  standard-normal quantiles, use `standardGaussianCDFOrderIso` and
  `standardGaussianQuantileAPI`; remember that the true inverse CDF is
  continuous on `(0,1)`, not globally on all real inputs, so paper proofs
  should prove their quantile arguments lie in `(0,1)` from selectivity or
  capacity assumptions. The concrete standard-normal inverse-Mills/hazard
  bridge now lives in `EconCSLib.Foundations.Probability.GaussianMills` and
  `EconCSLib.Foundations.Probability.GaussianMathlib`: use
  `standardGaussianHazardInverseCertificate` when a paper needs the real
  standard-normal hazard, and remember the inverse law is only stated for
  positive right-hand sides (`0 < y`) because the hazard is positive. Keep
  paper-specific or nonstandard hazard/truncated-normal derivations behind
  `GaussianHazardCertificate` or `GaussianHazardInverseCertificate` until their
  concrete bridge is proved. Once a hazard certificate is supplied, use
  `GaussianHazardCertificate.normalTail_pos`,
  `GaussianHazardCertificate.normalDensity_div_normalTail_eq_hazard_div_scale`,
  `GaussianHazardCertificate.normalUpperTailMean_mono_threshold`,
  `GaussianHazardCertificate.mixtureTailMass_pos`, and
  `GaussianHazardCertificate.mixtureUpperTailMean_mul_tailMass_eq_numerator`
  for location-scale tail, academic-merit, and finite-mixture admitted-mean
  comparisons.
  For no-barrier admissions cutoffs, prefer constructing thresholds with
  `StandardGaussianCDFAPI.exists_mixtureTailMass_eq_of_capacity_mem_Ioo` plus
  concrete `standardGaussianCDF_tendsto_atBot`/`standardGaussianCDF_tendsto_atTop`
  instead of leaving separate capacity-equation assumptions for each policy.
  When a paper needs the concrete derivative of the standard-normal CDF, avoid
  leaving a derivative certificate in the paper folder.  In
  `GaussianMathlib`, prove `cdf x = ∫ y in Iic x, density y` with
  `ProbabilityTheory.gaussianReal_apply_eq_integral`, convert `measureReal`
  via `ENNReal.toReal_ofReal` using density nonnegativity, and then apply the
  interval-integral fundamental theorem to `u ↦ ∫ y in Iic u, density y`.
  This gives `standardGaussianCDF_hasDerivAt_density` and the reusable
  `standardGaussianAnalyticAPI`.  For doubled-log density comparisons, prove
  the standard-normal elementary density formula once and set the constant to
  `2 * log ((sqrt (2*pi))⁻¹)`.
  For admissions threshold statements, distinguish the main-body real-threshold
  claim from stronger appendix interior-threshold claims. A continuous strictly
  monotone scalar score on `[0,1]` has a real cutoff for its strict or weak lower
  set without endpoint-crossing assumptions; use
  `exists_threshold_of_continuous_strictMonoOn_Icc` or
  `exists_threshold_le_of_continuous_strictMonoOn_Icc`. Only use endpoint
  crossing lemmas when the paper explicitly needs an interior threshold.
  For access-barrier threshold theorems that use `Φ⁻¹` or `HR⁻¹`, keep the
  analytic inverse facts narrow: use `StandardGaussianQuantileAPI` for
  quantile monotonicity/continuity/positivity above one half, and use
  `GaussianHazardInverseCertificate` only for the order bridge
  `HR(z) <= y ↔ z <= HR⁻¹(y)`. Then prove the paper's algebraic
  monotonicity separately with scalar lemmas such as
  `sqrt_fractionalLinear_const_mul_lt_of_rho_lt_one` and
  `sqrt_fractionalLinear_mul_const_lt_of_one_lt_rho`, instead of assuming the
  whole `β` or `η` characterization.
  For diversity under fixed group-A access barriers, prefer the capacity
  equation route to differentiating the displayed `η` formula: prove the
  admission cutoff is strictly increasing in group-B access from the capacity
  equations and positive tails, then infer diversity monotonicity from the
  falling group-A tail share. If the source defines diversity as the admitted
  group-B share, first use the capacity equation to rewrite that direct share
  as the complement of admitted group-A mass over capacity; do this algebraic
  bridge once instead of carrying both diversity formulas through the proof.
  Prefer one explicit metric-definition endpoint after proving the route:
  define admitted-share diversity and Gaussian upper-tail academic merit in
  Lean, then prove the paper theorem from those definitions. This is more
  audit-friendly than a theorem whose hypotheses are already-expanded hazard
  equations.
  For no-barrier Gaussian admissions comparisons, a fast threshold route is:
  prove the dropped-feature threshold is above the common mean from selective
  capacity, show the full-policy mixture tail at that lower threshold is
  strictly larger because both group scales increased, then use antitonicity of
  the full-policy mixture tail to force `thresholdSub < thresholdFull`. For
  group academic merit, combine the strict same-threshold scale comparison of
  `normalUpperTailMean` with monotonicity in the threshold instead of trying to
  prove a new two-parameter truncated-normal theorem.
- For finite rating-scale large-deviation papers, start with
  `EconCSLib.Foundations.Probability.FiniteSupportMGF`: use `finiteMGF`,
  `finiteLogMGF`, `finiteLegendreValue`, `finiteRateFunction`, and
  `FiniteRatingLDPModel` to state source log-MGF and rate-function formulas
  before adding paper-specific rating designs or ranking rules.
- For exponential-rate aggregation, use
  `EconCSLib.Foundations.Probability.LargeDeviations`: represent the analytic
  distribution-family theorem as an `ExponentialRateCertificate` or
  `LargeDeviationRateCertificate`, convert exact rates to weaker eventual
  upper bounds with
  `ExponentialRateCertificate.hasExpUpperBoundWithConst_of_lt`, convert exact
  rates to weaker eventual lower bounds with
  `ExponentialRateCertificate.hasExpLowerBoundWithConst_of_gt`, and aggregate
  finite unions or weighted sums with
  `finite_weighted_sum_hasExpUpperBoundWithConst`,
  `finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates`,
  `finite_weighted_sum_hasExpLowerBoundWithConst_of_component`,
  `finite_weighted_sum_hasExpLowerBoundWithConst_of_rate_certificate_component`,
  `PairwiseErrorUpperBoundCertificate.aggregateError_hasExpUpperBoundWithConst`,
  or
  `PairwiseErrorRateCertificate.aggregateError_hasExpUpperBoundWithConst_of_lt`.
  Use
  `PairwiseErrorRateCertificate.aggregateError_hasExpLowerBoundWithConst_of_component_gt`
  when a lower-bound or optimality argument needs to show the aggregate cannot
  decay faster than one positive-weight pairwise error.
  Keep Gartner-Ellis, Cramer, and Laplace-principle derivations behind an
  explicit certificate unless the paper needs the analytic proof itself.
- For accuracy-diversity/order-statistic papers, separate the reusable layers:
  finite separable-optimization and FOC bridges belong in optimization or the
  recommender layer; top-`k` expectation oracles and distribution-family
  asymptotic certificates belong in probability. Use
  `EconCSLib.Foundations.Probability.OrderStatistics`:
  `TopKExpectationOracle`, `TopKExpectationOracle.marginalTopK`,
  `TopKExpectationOracle.HasDiminishingReturnsAt`,
  `TopKExpectationOracle.HasNonnegativeMarginalsAt`, and
  `TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_marginal_sandwich`,
  `TopKExpectationOracle.ScaledMarginalLimitCertificate.marginal_lt_of_scaled_gap`,
  and
  `TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_same_count_marginal_lt_of_weight_gap`.
  Concrete bounded, exponential, and Pareto order-statistic integrals should be
  proved once as certificate providers and then fed into the paper's
  homogeneity/FOC certificates.
- For real-valued threshold/tail arguments, use
  `EconCSLib.Foundations.Probability.RealDistribution`: `lowerCDFMass`,
  `upperTailMass`, `lowerCDFMass_mono`, `upperTailMass_antitone`,
  `lowerCDFMass_eq_cdf`, `upperTailMass_eq_one_sub_cdf`, and
  `UpperTailThresholdCertificate`. Put concrete distribution-family tail
  asymptotics on top of these wrappers instead of repeating
  `Measure.real (Iic x)` / `Measure.real (Ioi x)` algebra in paper folders.
- For finite union bounds over paper-indexed bad events, first prove the event
  inclusion or exact event equivalence, then use
  `pmfProb_exists_mem_le_sum` for a finite index set or
  `pmfProb_exists_le_card_mul` when every indexed event has the same upper
  bound `eps`. Keep any paper shorthand such as `choose(k+2,2) <= k^2` as an
  explicit arithmetic side condition if it is not literally true in the stated
  parameter range.
- For expected finite counts, use
  `pmfExp_card_filter_eq_sum_pmfProb` to turn
  `E[#{a | p ω a}]` into `sum_a Pr[p ω a]`. This is the right first move for
  paper lines like `c_k(n) = sum_g Pr[g has property]`; do not hand-expand the
  double sum in the paper folder.
- For lower bounds on expected finite counts, use
  `pmfExp_card_filter_ge_card_mul_of_forall_mem_prob_ge`: it is enough to
  identify a finite subfamily `s` and prove every event in `s` has probability
  at least `rate`. This is the clean wrapper for source arguments that sum
  over a tail block of indices after proving a uniform per-index probability
  lower bound.
- For finite-PMF variance and Chebyshev steps, use `pmfVariance`,
  `pmfProb_abs_sub_mean_gt_le_variance_div_sq`, and
  `pmfProb_lt_half_expectation_le_four_div_expectation_of_variance_le_expectation`.
  This is the right route for arguments like Immorlica-Mahdian Lemma 4.1:
  first prove `Var(Y) <= E[Y]`, then obtain
  `Pr[Y < E[Y]/2] <= 4/E[Y]`, and finally bound reciprocal-successor
  expectations by splitting on the lower-half event.
- For variance of a sum of indicator events under pairwise negative
  correlation, use
  `pmfVariance_card_filter_le_pmfExp_card_filter_of_pairwise_inter_le_mul`.
  It packages the second-moment expansion
  `pmfExp_card_filter_sq_eq_sum_pmfProb_inter` and the
  `E[S^2] - E[S]^2` variance identity, so paper folders only need to prove
  the event-level inequality
  `Pr[E_i ∧ E_j] <= Pr[E_i] * Pr[E_j]` for distinct indices.
- For paper proofs that establish negative correlation through a conditional
  comparison such as `Pr[F_i | F_j] <= Pr[F_i]`, use
  `pmfConditionalProb_eq_inter_div_of_pos` and
  `pmfProb_inter_le_mul_of_conditionalProb_le` from
  `EconCSLib.Foundations.Probability.Conditional`. Then, if the paper has
  independent copies across agents, keep the `n`th-power identities explicit in
  the paper folder and compose them with `pow_le_pow_left₀`; this is the
  Immorlica-Mahdian Lemma 4.4 route from one-man list events to all-men absence
  events. For IM05's omitted multiset/permutation detail, use
  `im05_namesBeforeFirst`, `im05_integerMultisetPermutationSample`,
  `im05_integerMultisetPermutationSample_nonempty`,
  `im05_integerMultisetPermutationList`, `im05_integerMultisetPermutationList_count`,
  `paper_im05_lemma4_4_multiset_event_inclusion_probability`,
  `paper_im05_lemma4_4_integerMultiset_event_inclusion_probability`,
  `paper_im05_lemma4_4_one_man_comparison_from_permutation_limits`,
  `paper_im05_lemma4_4_one_man_comparison_from_integerMultiset_limits`,
  `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_permutation_limits`,
  `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_integerMultiset_limits`,
  and
  `paper_im05_lemma4_4_variance_le_expectation_from_freshList_integerMultiset_limits`:
  the finite event inclusion is now derived internally from the permutation
  events, with a concrete inhabited uniform count-vector word model available,
  and the order-closed limit-passing algebra is closed. If the source approximation is
  already expressed as numeric sequences rather than permutation events, use
  `paper_im05_lemma4_4_one_man_comparison_from_multiset_limits`,
  `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_multiset_limits`,
  and
  `paper_im05_lemma4_4_variance_le_expectation_from_freshList_multiset_limits`.
  If the approximation is represented by pointwise-convergent weight vectors,
  use
  `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_weight_limits`,
  `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_pair_weight_limits`,
  or
  `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_scaled_count_weight_limits`;
  if the finite source-law equalities from uniform count-vector permutations are
  the only remaining obligations, use
  `paper_im05_lemma4_4_freshList_conditional_comparison_family_from_integerMultiset_finite_laws_and_scaled_count_limits`
  and
  `paper_im05_lemma4_4_variance_le_expectation_from_freshList_weight_limits`.
  The remaining source-specific obligation is the finite law bridge from the
  integer-multiset first-distinct-name process to the raw integer-weight
  fresh-list events; the scaled-count bridge then handles normalization and
  limiting.
- For deferred-decision prefix products, avoid reproving the multiplication
  chain in each paper. Use `pmfProb_ge_pow_of_nested_conditionalProb_ge`:
  prove `event 0` is certain, `event (r+1) -> event r`, and a per-step lower
  bound on `Pr[event (r+1) | event r]`. If the source phrases the step as an
  upper bound on the next-hit event, first use
  `one_sub_le_pmfConditionalProb_compl_of_conditionalProb_le`; if the complement
  target is only equivalent under the current prefix, use
  `pmfConditionalProb_congr_of_condition`; if both the conditioning event and
  target need to be replaced, use `pmfConditionalProb_congr`. In IM05 this
  supports the named `im05_listPrefixOmits` route, with the concrete Algorithm
  4.2 filtered without-replacement law now supplied by the fresh-list PMF
  prefix-set theorems.
- For weighted without-replacement deferred-decision steps, state the one-step
  law through `finiteWeightedPMFExcluding_apply_toReal_eq_div_one_sub` rather
  than re-normalizing by hand: after excluding the realized prefix set, the
  available mass is `1 - prevMass` and the next atom is `p_w/(1-prevMass)`.
  If the paper conditions only on a coarse prefix event while the source law is
  statewise for realized prefixes, use
  `pmfConditionalProb_le_of_state_refinement` to average upper bounds and
  `pmfConditionalProb_eq_of_state_refinement` when every refined state has the
  same conditional probability.
  The IM05 wrappers named
  `paper_im05_lemma4_3_*_from_algorithm4_2_prefix_states` are the preferred
  paper-facing interface: the concrete process should prove prefix positivity,
  statewise filtered atom equalities, and then instantiate the product-model
  wrappers, not restate the tail/rank algebra.
- For independent identical finite copies, use `pmfProduct` and
  `pmfProduct_prob_forall` instead of supplying an `n`th-power identity by
  hand. In IM05, `paper_im05_lemma4_3_product_absence_probability`,
  `paper_im05_lemma4_3_absence_probability_ge_rank_power_from_algorithm4_2_prefix_states_product`,
  and
  `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_prefix_states_product`
  are the direct product-model entry points once the one-man list law is
  available. For Lemma 4.4, use
  `paper_im05_lemma4_4_product_event_probability`,
  `paper_im05_lemma4_4_product_joint_event_probability`, and
  `paper_im05_lemma4_4_variance_le_expectation_from_single_man_conditional_product`
  to lift one-man conditional negative dependence to all-men absence events.
  Use `pmfProb_congr` for pointwise-equivalent event shapes before invoking
  the product theorem.
- For IM05-style ranked popularity tails, use the paper wrappers
  `im05_popularityRankTail_card`,
  `im05_popularityRankTail_popular`, and
  `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_ranked_tails_product`.
  They sit on top of `FiniteRanking.lowerRankFinset_mono` and discharge the
  `rank-k` cardinality and pointwise popularity assumptions. The
  ranked-top-prefix mass side is now handled by
  `paper_im05_lemma4_3_previous_mass_le_Q_of_card_le_top_prefix` and
  `paper_im05_lemma4_3_realized_prefixSet_mass_le_Q_of_top_prefix_of_pos_support`,
  using `FiniteSum.finset_sum_le_sum_of_card_le_pairwise_sdiff`.
- For Algorithm 4.2 prefix states, prefer the prefix-set interface when the
  concrete sample is a list: `im05_listPrefixSet`,
  `im05_listPrefixOmits_iff_not_mem_prefixSet`,
  `paper_im05_lemma4_3_one_man_omit_probability_ge_rank_power_from_algorithm4_2_prefix_sets`,
  `paper_im05_lemma4_3_absence_probability_ge_rank_power_from_algorithm4_2_prefix_sets_product`,
  and
  `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_ranked_tails_prefix_sets_product_of_top_prefix_mass`.
  These wrappers derive `w ∉ previous` and available-mass positivity from the
  realized prefix event and `prevMass <= Q`. For the concrete recursive
  fresh-list sampler, use
  `paper_im05_algorithm4_2_freshList_prefixSet_omit_conditional_atom_formula`
  to discharge the statewise filtered-draw equality, or use
  `paper_im05_lemma4_3_expected_absent_count_lower_bound_from_algorithm4_2_freshList_ranked_tails_prefix_sets_product_of_top_prefix_mass`
  for the full ranked-tail product wrapper. Under full support and `k < #W`,
  use `paper_im05_algorithm4_2_freshList_omit_pos_of_full_support` and
  `paper_im05_algorithm4_2_freshList_prefix_omit_pos_of_full_support` to
  discharge the positivity side conditions for Lemma 4.3/Lemma 4.4 wrappers.
- For concrete finite without-replacement laws, use
  `EconCSLib.Foundations.Probability.WithoutReplacement`. The key constructors
  are `finiteWeightedPMFAvailable`, `finiteFreshList`,
  `finiteWithoutReplacementPMF`, `finiteWithoutReplacementPMF_head_prob`,
  `finiteWithoutReplacementPMF_head_tail_prob`,
  `finiteWithoutReplacementPMF_conditional_tail_event_prob`, and
  `finiteWithoutReplacementPMF_prefixSet_conditional_next_prob_excluding`.
  Use `finiteWithoutReplacementPMF_omit_atom_pos` for positive probability of
  avoiding a fixed atom when full support and enough alternatives are available.
  Use `finiteAvailableWeight_const_mul`,
  `finiteFreshListAtomWeight_const_mul`,
  `finiteWithoutReplacementPMF_event_prob_const_mul`, and
  `finiteWithoutReplacementPMF_conditional_prob_const_mul` when a paper scales
  all finite approximation weights by a positive constant; this preserves event
  and conditional event probabilities.
  For convergence of finite weighted samplers, use
  `finiteFreshListAtomWeight`, `finiteWithoutReplacementPMF_atom_toReal`,
  `finiteWithoutReplacementPMF_event_prob_eq_sum_atomWeight`,
  `finiteAvailableWeight_tendsto`, `finiteFreshListAtomWeight_tendsto`, and
  `finiteWithoutReplacementPMF_event_prob_tendsto`; combine event convergence
  with
  `pmfConditionalProb_tendsto_of_inter_tendsto_of_condition_tendsto` when the
  paper needs conditional event convergence. In IM05 the paper-facing wrappers
  are `paper_im05_algorithm4_2_freshList_event_prob_tendsto`,
  `paper_im05_algorithm4_2_freshList_omit_prob_tendsto`, and
  `paper_im05_algorithm4_2_freshList_conditional_omit_tendsto`.
  Full-support availability is supplied by
  `finiteAvailableWeight_pos_of_full_support_of_card_lt`. In IM05, the
  paper-facing aliases are `im05_algorithm42FreshListPMF` and
  `paper_im05_algorithm4_2_freshList_zero_prefix_conditional_atom_formula`;
  the paper-facing positive-prefix atom laws are
  `paper_im05_algorithm4_2_freshList_prefixSet_conditional_atom_formula` and
  `paper_im05_algorithm4_2_freshList_prefixSet_omit_conditional_atom_formula`.
- For negligible-perturbation expectation arguments where two natural-valued
  counts agree on a good event, use
  `pmfExpReciprocalSucc_le_add_prob_of_eq_on_event`. It reduces the proof to
  bounding `Pr[Ebar]`; the pointwise reciprocal loss on the bad event is at
  most `1`.
- For uniform finite experiments, reuse the generic uniform tools before
  expanding sums: `pmfExp_uniformPMF_equiv` for relabeling across equivalent
  finite spaces, `pmfExp_uniformPMF_prod` for product/nested-expectation
  decompositions, `pmfProb_uniformPMF_finset` for converting finite events
  to `card(event) / card(space)`, `pmfProb_uniformPMF_singleton` for atom mass,
  `pmfProb_uniformPMF_equiv` and
  `pmfProb_uniformPMF_eq_of_comp_equiv` for event-probability exchangeability
  under finite sample-space relabelings, and
  `pmfProb_uniformPMF_fun_range_relabel` when the sample space is a uniformly
  drawn finite function and the relabeling is pointwise on the range. For
  ordered without-replacement samples represented as injective finite
  functions, use `injectiveFunRangeRelabelEquiv` and
  `pmfProb_uniformPMF_injective_fun_range_relabel`,
  `pmfProb_uniformPMF_prod_fst_eq` for one coordinate of a product draw,
  `pmfProb_uniformPMF_prod_fst_event` for any event depending only on the left
  coordinate of a uniform product draw,
  `pmfProb_uniformPMF_prod_eq_pair` for a prescribed pair of independent
  product coordinates, and `pmfProb_uniformPMF_fun_eq_pair_of_ne` for two
  distinct prescribed coordinates of a uniformly drawn finite function. Use
  `pmfProb_uniformPMF_prod_eq_diag` and `pmfProb_uniformPMF_fun_eq_of_ne` for
  diagonal/collision events. In
  random-list proofs, keep these distinct from a broader redundancy event; a
  `1/n^2` claim is usually valid only after reducing to two prescribed
  coordinate values, while a plain two-draw collision is `1/n` and is strictly
  larger than `1/n^2` when `n > 1`. A single "redundant slot" event should
  usually be bounded by a union over earlier-slot collisions, giving a
  `#earlier / n` bound unless the source supplies a sharper prescribed-value
  reduction.
- For balls-into-bins arguments, use
  `EconCSLib.Foundations.Probability.Occupancy`: deterministic used/empty-bin
  sets, `occupancyFirstHitBalls` for ordered first appearances, bin/domain
  relabeling for used and empty bins, the uniform `occupancyPMF`, and
  reciprocal empty-bin expectations.
  Immorlica-Mahdian's Lemma 6.3 is closed generically by a one-ball recurrence:
  adding one uniformly chosen ball multiplies `E[1/(Y+1)]` by at most
  `(#bins+1)/#bins`; iterating from zero balls gives the geometric bound, then
  `Real.add_one_le_exp` converts it to `exp(m/n)/n`. Use this recurrence route
  when the source inclusion-exclusion proof is not essential to a downstream
  named dependency.
- When identifying a paper's occupancy experiment with `Fin m`/`Fin n`, prove
  or pass explicit equivalences and then use
  `occupancyReciprocalExpectation_domain_equiv` and
  `occupancyReciprocalExpectation_bin_equiv`. This keeps paper-local labels
  such as men, proposal slots, and women separate from the generic occupancy
  proof over standard finite types.
- For occupancy comparisons such as "experiment 5 names all women experiment 4
  names, and possibly more", reduce the paper statement to
  `occupancyUsedBins assignment₁ ⊆ occupancyUsedBins assignment₂` and apply
  `occupancyEmptyBins_card_le_of_usedBins_subset`. Then lift that deterministic
  count inequality to reciprocal expectations with
  `pmfExpReciprocalSucc_mono_of_forall_ge`.
  If one experiment is a slot restriction of another, use
  `occupancyUsedBins_comp_subset` to get the used-bin inclusion directly.
- For occupancy equalities such as "Experiments 2 and 3 name the same women",
  reduce to equality of used-bin sets and apply
  `occupancyEmptyBins_card_eq_of_usedBins_eq`.
- For ordered draw-prefix arguments, first identify used bins with first
  appearances with `occupancyFirstHitBalls_image_eq_usedBins` and
  `occupancyFirstHitBalls_card_eq_usedBins`. This is the clean route for
  Immorlica-Mahdian-style claims that a `k+2` prefix with at most `k` distinct
  names is equivalent to having two redundant slots, and it lets you state the
  concrete bad-prefix event as exactly an existential union over indexed
  redundant-pair events before applying the finite union bound.

## Finite Markov Chains and Dynamic Models

- For dynamic EC/platform papers with controlled actions, start with
  `EconCSLib.Foundations.Probability.MDP`: `FiniteMDP`, `FiniteMDP.Policy`,
  `controlledKernel`, `actionValue`, `policyValueStep`, `horizonValue`,
  `optimalStep`, `optimalValue`, and occupancy masses.
- For passive dynamics, use the finite kernel interface in
  `EconCSLib.Foundations.Probability.MarkovChain`: `FiniteMarkovKernel`,
  `transitionProb`, `step`, `iterate`, `expectedNext`, `drift`, `Stationary`,
  `Absorbing`, `ExpectedLe`, and `StochasticallyMonotone`.
- Model policy-induced dynamics with `controlledKernel` when actions matter, or
  as separate kernels over the same finite state type when the paper already
  fixes policies. Compare fixed kernels with `ExpectedLe K L V` for the
  observable or Lyapunov/potential function `V`, then lift to
  `drift_le_of_expectedLe`.
- For queueing, surge, and imbalance papers, define the paper's state type
  first, then a potential such as queue length, imbalance, waiting cost, or
  welfare loss. Prove one-step drift bounds before attempting stationary or
  long-run claims.
- Use `Stationary` only for true steady-state claims. If the paper only needs
  one-step improvement, monotonicity, or a Foster-style drift condition, keep
  the theorem at the `expectedNext`/`drift` layer and record the stationary
  bridge as a separate named assumption or future library seam.
- For monotone dynamics, use `StochasticallyMonotone` when the paper compares
  states under every monotone observable. Use `ExpectedLe` when the comparison
  is only for the paper's specific value function or welfare/potential metric.
- For finite first-order stochastic dominance, use
  `EconCSLib.Foundations.Probability.StochasticDominance`.
  `PMF.FirstOrderLe μ ν` is the expectation order against every monotone
  observable, and `PMF.MonotoneCoupling` is the certificate interface for a
  joint distribution supported on ordered pairs. Use this for admissions,
  recommendation, and platform-policy comparisons before introducing
  paper-specific CDF algebra.
- For Gaussian threshold comparisons in testing papers, first reduce the paper
  claim to monotonicity of posterior means or standardized CDF arguments using
  `GaussianPriorSignal`/`GaussianSignalFamily`; only then add the minimal
  analytic CDF or hazard certificate needed for the remaining one-dimensional
  normal-tail comparison.
- Keep finite Markov kernels in the probability foundations layer. Paper
  folders should contain only the concrete state encoding, transition law,
  policy parameters, and paper-facing wrappers.

## Measure Inequalities and Bonferroni

- For textbook probability inequalities that appear in a paper, upstream a
  generic statement in `MeasureInequalities.lean` and leave paper wrappers thin.
  Finite union bounds, complement/intersection bounds, and Bonferroni
  truncations are reusable enough for `EconCSLib`.
- For finite Bonferroni proofs, prove the pointwise counting identity first:
  the sum over `powersetCard k` of event indicators equals
  `(activeEvents.card.choose k : ℝ)`. Then use alternating binomial-sum lemmas
  and integrate the pointwise inequality.
- When converting indicator functions to set integrals, introduce explicit set
  names and local equalities for unions/intersections. Avoid relying on one
  large `simp` after unfolding all set notation; prove membership/indicator
  equivalences with `if_pos`/`if_neg` or explicit `Set.mem_iUnion` /
  `Set.mem_iInter` bridges.
- For probability/complement lower bounds, prove the de Morgan set equality
  explicitly, then use `probReal_compl_eq_one_sub` and the finite union bound.
- Keep real-valued probability goals consistently in either `measureProb` or
  `μ.real`; when crossing between them, unfold `Measure.real` locally rather
  than rewriting through large expressions.
- For continuous finite-mass side conditions, use
  `measure_ne_top_of_subset_of_ne_top`,
  `measureReal_pos_of_measure_ne_zero_ne_top`,
  `measure_pos_of_measureReal_pos`, and
  `withDensity_measureReal_pos_of_pos_on` from `MeasureInequalities`. These
  are the generic GN-style helpers for proving positive real mass from a
  positive finite `ENNReal` mass and a positive density on a measurable set.
- For random-sampling auction proofs where the bad event depends on a
  sample-selected threshold, avoid stopping at a loose union over candidate
  prices if the paper uses a top-prefix argument. Split the proof into:
  deterministic selected-large bridge (often from `alpha * h <= F` plus
  `singlePriceRevenue <= saleCount * h`), selected-bad subset of a fixed
  top-prefix underrepresentation event, finite prefix union bound, and a
  separate geometric-tail lemma. Keep the top-prefix interface explicit until
  its construction is proved, so the remaining paper assumption is auditable.
- When a paper says "top `i` bids" and the rest of the proof only needs that
  threshold winner sets of size at most `i` lie in the prefix, a fast concrete
  model is a sorted `Fin n → ℝ` bid vector with a monotonicity assumption. Define
  the prefix as indices `< i`, prove its cardinality by an equivalence with
  `Fin i`, and prove threshold closure by contradiction using `i + 1` winners.
- For randomized mechanisms whose expectation has a simple finite formula,
  write the expected-payment/revenue double sum directly before introducing
  probability objects. For weighted-pairing-style auctions, the random draw
  "choose `j` with probability proportional to `v_j` and charge `v_j` if
  accepted" becomes a deterministic sum of terms like
  `v_j^2 / (total - v_i)`, which is faster to bound than modeling the sampling
  kernel first.

## Continuous Probability and RUM

- Do not force a finite analogue when the paper theorem is genuinely continuous
  and a direct density/change-of-variables statement is shorter and more
  faithful.
- If the source theorem is measure-theoretic, probabilistic, CTMC-based, or
  long-run average reward based, formalize that layer directly instead of
  parking it behind finite scaffolding. It is fine to state paper-local
  hypotheses for hard analytic facts such as integrability, measurability,
  renewal-reward limits, or almost-sure convergence, but the theorem wrapper
  should expose the source-level measures, integrals, probabilities, and limits
  rather than a finite substitute.
- For continuous reward formulas, first define the exact paper quantities:
  event mass, set integral of payments, set integral of times, reward ratio,
  and accept-all policy. Then prove algebraic dominance lemmas under explicit
  measurability/integrability and positivity hypotheses. Only after that decide
  whether the renewal theorem or LLN bridge needs a reusable library statement
  or a paper-local assumption.
- For CTMC papers, prove the closed-form transition probabilities, ODE/forward
  equation, and probability bounds in `EconCSLib` when reusable. In the paper
  folder, add source-level bridge statements connecting those probabilities to
  the paper's integrals, cycle probabilities, or time fractions; do not mark the
  stochastic theorem green until the process/renewal bridge is discharged or
  explicitly assumed in the theorem signature and status ledger.
- For renewal-cycle CTMC wrappers, keep opaque algebraic side conditions out of
  the main source model when they follow from primitive assumptions. Carry
  arrival/switch positivity, feasible-policy measurability/subset facts, and
  positive accepted mass, then derive denominator nonzero, cross-probability
  nonzero, state-cycle-time nonzero, and total-cycle-time nonzero locally in
  the theorem proof before invoking quotient/strong-law algebra.
- Split continuous RUM proofs into layers: payoff/certificate algebra over
  rankings, continuous density/change-of-variables inequalities over scores,
  and concrete model instantiation proving support, positive source regions,
  normalization, and score-to-ranking interface facts.
- Upstream only paper-neutral RUM infrastructure. Good `EconCSLib` candidates
  include additive noise well-ordering, Gaussian/Laplacian kernels, scalar
  contraction geometry, and density-product swap inequalities; these live in
  `EconCSLib.Foundations.Probability.RandomUtility`. Keep concrete ranking
  encodings, six hard-coded three-candidate rankings, lambda/delta payoff
  certificates, and theorem-number wrappers in the paper folder unless a second
  paper actually needs that same abstraction.
- For continuous distributional inputs that feed a finite theorem over
  rankings, push the measure through the ranking map and convert the finite
  pushforward to a `PMF`. Prove a bridge saying `pmfProb` equals the continuous
  preimage mass.
- For continuous delta inequalities over finite summaries, push the measure
  through the finite summary, apply the finite indicator-difference lemma, and
  pull the result back with a measure-probability bridge.
- For `swapi`/change-of-variables arguments, first prove a reusable
  `withDensity` mass comparison under a measure-preserving measurable
  equivalence and density monotonicity. Then add the paper-local score-geometry
  wrapper proving source regions map into target regions.
- For strict continuous analogues of finite atom witnesses, use a positive
  measure source subset plus a finite source integral. A useful reusable seam is
  a `withDensity` strict comparison lemma with hypotheses like `Measurable D`,
  finite source integral, and positive source measure.
- When a finite certificate seems to require full support of all induced
  rankings, inspect the downstream field actually using it before proving every
  ranking fiber. Often only one strict inequality such as `lambdaOne < 1` is
  needed; for continuous RUMs this can be discharged faster by proving positive
  mass of the exact wrong-choice event and using an identity like
  `wrongProb = 1 - lambdaOne`.
- For concrete continuous support obligations, use explicit open boxes inside
  the target event rather than trying to characterize the whole event. Prove a
  reusable "open box has nonzero volume, and subsets inherit nonzero measure"
  lemma, then instantiate tiny boxes for each lambda source/corrected-top
  region.
- Expose normalized score-law assumptions as the integral equation
  `lintegral D = 1` plus an `IsProbabilityMeasure (mu.withDensity D)` bridge.
  The same equation should discharge finite-source-integral side conditions by
  monotonicity against the full integral.
- Treat ties in real-valued score RUMs explicitly. Either work on no-tie/full
  measure subtypes, prove almost-everywhere ranking-interface lemmas, or state a
  tie-breaking convention and prove score/ranking facts for it.
- After an abstract `withDensity` theorem compiles, add concrete score-space
  utilities for the intended product shape: coordinate projections, measurable
  coordinate swaps, measure-preserving swap lemmas, normalization bridges, and
  finite-source-integral bridges. Align product nesting with Mathlib's product
  measure conventions, for example `(ℝ × ℝ) × ℝ`, so later instantiations do
  not waste time on associativity rewrites.
- When a paper-facing probability theorem is stuck with a premise like
  "source metric field equals the displayed probability formula," close it with
  a canonical source surface when possible. Define the surface so the metric
  field unfolds to the tail probability, expectation, or integral appearing in
  the paper, prove a thin source-surface endpoint, and make the DAG/README point
  to that endpoint rather than to the older abstract formula-premise theorem.

## Lean Patterns

- Prefer `pmfExp`/`pmfProb` abstractions over hand-expanding `PMF` internals.
- For uniform PMFs over finite spaces, use relabeling lemmas such as
  `pmfExp_uniformPMF_comp_equiv`, `pmfExp_uniformPMF_eq_of_comp_equiv`,
  `pmfProb_uniformPMF_equiv`, `pmfProb_uniformPMF_eq_of_comp_equiv`, or
  `pmfProb_uniformPMF_fun_range_relabel`. For injective-function subtypes, use
  `pmfProb_uniformPMF_injective_fun_range_relabel`.
- Open `ENNReal` scope in files that state `ℝ≥0∞` or `∫⁻` expressions.
- When event hypotheses contain abbreviations, normalize each component with
  local equalities before rewriting larger probability goals.
