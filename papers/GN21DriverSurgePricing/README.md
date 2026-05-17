# Driver Surge Pricing

## Source Version

- Paper: *Driver Surge Pricing*
- Authors: Nikhil Garg and Hamid Nazerzadeh
- Version formalized: arXiv v4, dated March 9, 2021; Management Science publication DOI `10.1287/mnsc.2021.4058`
- Official URL: https://pubsonline.informs.org/doi/10.1287/mnsc.2021.4058
- Public PDF: https://arxiv.org/pdf/1905.07544

The PDF is cached locally as `source.pdf` and ignored by Git. The extracted text
cache is `source.txt`.

## Guideline Audit

- Folder follows the one-citation paper contract: local `.gitignore`, README,
  source PDF/text cache, `MainTheorems.lean`, aggregate import, and DAG source.
- `MainTheorems.lean` is source-facing for the continuous trip-length model:
  it uses sets of real trip lengths and abstract lifetime reward functionals.
- Single-state reward quantities are now stated directly as measure/set-integral
  formulas over continuous trip lengths; Proposition 3.1 has a compiled
  source renewal-reward IC proof for measurable feasible continuous policies,
  including the single-state multiplicative-pricing corollary, plus a
  standard-measure constructor that discharges routine nonnegativity and
  monotonicity assumptions and proves the zero-time feasible-set mass bridge
  from positivity of trip lengths, plus a bridge from positive real trip mass
  back to positive underlying measure mass for measured tightening.
- The reusable renewal-reward layer proves the marginal add/remove inequalities
  used in the continuous proof of Theorem 1, plus the same-time replacement
  improvement used in Step 1. It now also exposes strong-law wrappers for IID
  renewal-cycle empirical means and reward/time quotients, used to close the
  stochastic parts of the Section 2.2 formula and Lemmas 1 and 3 from explicit
  cycle variables rather than opaque limit certificates. The Lemma 1/3 IID
  wrappers now carry source primitive positivity and policy-feasibility fields;
  Lean derives the needed cycle-denominator, transition-probability,
  state-cycle-time, and total-cycle-time nonzero facts internally.
- Theorem 1 now has canonical strict, complete, and boundary threshold sets,
  with feasibility, measurability, partial-threshold, boundary-rate facts,
  affine-pricing measurability specializations, a compiled measurable-policy
  Step 1 replacement by the complete threshold at the policy's own reward
  rate, compact upper-semicontinuity Step 3 band/gap reductions, the
  high-reward band/gap split, and the left/right tail compactness reductions;
  one-sided dominated convergence now proves compact upper-semicontinuity even
  with atoms at threshold boundaries, closing the source-facing measurable
  best-response theorem.
- The reusable CTMC layer proves the two-state switch/stay probability closed
  forms, forward equations, row-sum identity, basic probability bounds,
  strict positivity on positive times, the strict linearization bound
  `q(u) < lambda*u`, `q(u)/u` strict decrease on positive times, and the
  zero-time limit `q(u)/u -> lambda`.
- The CTMC monotonicity layer now also exposes
  `gn21SwitchProb_mul_le_mul_of_pos_lt` and
  `gn21FixedState_lower_pointwise_of_rejectsLongTrips`: for reject-long fixed
  states, the lower fixed-state complement comparison is proved directly from
  monotonicity of `q(t)/t`, so that side no longer needs to be supplied as a
  source assumption.
- The reusable real-analysis layer now contains a derivative-proxy criterion
  for strict quasi-convexity on positive reals; GN21 instantiates it for the
  canonical CTMC response shapes in Lemmas 7-8. It also exposes between-endpoint
  consequences for strict quasi-convex/quasi-concave functions, the shape fact
  needed by later Lemma 5 interval arguments.
- Appendix D now exposes the derivative-sign kernel, the polynomial-to-response
  strict-sign transfer, interval-density endpoint primitive derivatives,
  measured upper- and lower-endpoint interval-policy primitive realizations,
  improper-tail FTC and tail primitive derivatives/realizations, bounded
  endpoint-move calculus, positive right-endpoint and left-expansion
  replacement realizations, concrete unbounded-tail left replacements, plus
  finite positive density-mass wrappers for
  interval nondegeneracy and canonical long-/short-trip-rejection primitive
  realizations, feasible shape-to-canonical-policy equalities, and arbitrary
  feasible reject-long/reject-short/accept-middle/reject-middle primitive
  realizations, canonical non-accept-all witnesses for finite interval policy
  shapes, including the two-piece reject-middle endpoint paths and both
  reject-middle cutoff derivative bridges, concrete with-density
  reject-middle cutoff and unbounded-tail replacement policies, and statewise
  wrappers that feed those replacements into the Lemma 9/10 strict-local
  bridges,
  including
  positive-density nondegeneracy constructors for non-surge reject-long
  and accept-middle current/replacement policies and both current/replacement
  surge tail and middle-rejection policies,
  measured monotone-tightening wrappers that derive current-policy Lemma 9/10
  bounds from accept-all bounds, including positive-measure variants that
  discharge `lambda*T-Q` nonnegativity and `lambda<Q`, plus primitive-equality
  variants matching the endpoint bridge signatures and named-primitive Remark
  4 positivity wrappers,
  aggregate quotient-calculus derivative bridge, aggregate quotient
  monotonicity for left/right accepted-trip additions from nonnegative
  integrated Lemma 6 kernels, strict left/right aggregate quotient
  improvement from positive integrated Lemma 6 kernels, measured `Q,T,W`
  union additivity and measured left/right aggregate weak/strict-improvement
  bridges for adding accepted sets, including pointwise-kernel strict
  variants and accept-all-complement strict variants,
  including accept-all-complement specializations for rejected feasible sets,
  plus pointwise-to-integrated kernel bridges that turn nonnegative Lemma 6
  derivative kernels on an added set into the aggregate primitive side
  condition and positive kernel support into a strict primitive side
  condition,
  endpoint-data-to-Lemma-6 derivative certificate bridge,
  structured-kernel-to-Lemma-6 derivative certificate bridge, structured-price
  derivative algebra, small-time switch derivative, the Lemma 7
  canonical derivative-numerator calculation,
  canonical CTMC quasi-convex/quasi-concave response shape, and
  `lambda*t - q(t)` / `lambda T - Q` monotonicity plus nonnegativity and
  strict measured positivity bridges used by Lemmas 6 and 9-10.
  Lemma 9/10 current-bound positivity now also has measured pointwise
  derivative-kernel wrappers and direct accept-all-complement aggregate
  improvement bridges for the surge and non-surge states, including strict
  current-bound variants when the rejected complement has positive
  derivative-kernel support; these are packaged at the raw theorem, full-data,
  primitive-data, and source-data levels.  Lemma 10 additionally
  has a reward-rate-separated endpoint-term layer
  `lemma10StructuredStaticTerm_eq_ratio_reward_split`,
  `lemma10StructuredLinearEndpoint_eq_ratio_reward_split`,
  `lemma10StructuredStaticTerm_pos_of_ratio_reward_slack`,
  `lemma10StructuredLinearEndpoint_pos_of_ratio_reward_slack`,
  `paper_lemma10_structured_derivative_kernel_pos_of_ratio_reward_slack`,
  `paper_lemma10_structured_derivative_kernel_pos_of_endpoint_terms`, and
  `gn21MeasuredAggregateRewardPrimitives_le_acceptAll_left_of_lemma10_endpoint_terms`,
  so non-accept-all fixed-state branches can be closed by proving the actual
  current fixed-reward endpoint inequalities rather than assuming target
  reward-rate identities.  The endpoint-term route is threaded through
  `GN21NonsurgeLemma10EndpointTermsAggregateData`,
  `Theorem4MeasuredAggregateStructuredEndpointTermsCurrentRateWeakCertificate`,
  and
  `theorem3AcceptAllWeakRewardCertificate_of_structured_endpoint_terms_current_rates`
  for the weak Theorem 3 boundary, with the paper-facing source wrapper
  `paper_theorem3_measured_structured_ic_prices_of_structured_endpoint_terms_current_rate_source_assumptions`.
  The source-faithful IC route now also has a compiled sequential accept-all
  interface:
  `Theorem4MeasuredAggregateStructuredSequentialCurrentBoundsWeakCertificate`,
  `Theorem4MeasuredAggregateStructuredFeasibleSequentialCurrentBoundsWeakCertificate`,
  `theorem3AcceptAllSequentialWeakRewardCertificate_of_structured_sequential_current_bounds`,
  `theorem3AcceptAllFeasibleSequentialWeakRewardCertificate_of_structured_feasible_sequential_current_bounds`,
  `paper_theorem3_measured_structured_ic_prices_of_structured_sequential_current_bounds_source_assumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_current_bounds_source_assumptions`.
  The feasible-measurable route has a lighter source-data variant,
  `Theorem4MeasuredAggregateStructuredFeasibleSequentialCurrentBoundsSourceCertificate`
  plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_current_bounds_source_data_assumptions`,
  which derives the packed aggregate data and nondegeneracy fields from
  source-facing Lemma 9/10 data, accept-all mass positivity, and accept-all
  integrability.  The next wrapper,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_surge_source_data_assumptions`,
  discharges the Lemma 10 accept-all fixed-surge branch from Theorem 3
  parameter data, leaving only positive current non-surge mass and Lemma 9
  source data for the surge move.  Two thinner compiled variants,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_surge_accounting_data_assumptions`
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_surge_reward_rate_data_assumptions`,
  let the remaining Lemma 9 fixed-state proof be stated as the paper's
  structured accounting equation or measured reward-rate equality; Lean derives
  the scaled fixed-state earning identity internally.  The broad measurable
  source entry point
  `paper_theorem3_measured_structured_measurable_ic_prices_of_source_assumptions`
  aliases the reduced sequential reward-rate route.
  A denominator-valid variant,
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_source_assumptions`,
  now restricts the source policy domain to feasible measurable policies with
  positive accepted mass in both states, matching the reward-rate denominators
  in Lemma 1 and Lemmas 9--10.  In that route Lean derives the Lemma 10
  accept-all fixed-surge branch and all aggregate nondegeneracy fields; the
  only remaining policy-dependent source field is the Lemma 9 surge
  reward-rate data on this positive-mass domain.  The new fixed-transfer
  adapter
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_fixed_transfer_reward_rate_data_assumptions`
  derives that field from accept-all Lemma 9 bounds, the current fixed
  non-surge reward rate, and the two fixed-state cross-ratio comparisons.
  The target-rate specialization
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_target_fixed_transfer_data_assumptions`
  reuses the constructed Theorem 3 accept-all Lemma 9 bounds when the current
  fixed non-surge policy has target reward rate `R1`.  A reward-bound
  specialization
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_target_reward_bound_fixed_transfer_data_assumptions`
  reuses those target bounds for the policy's effective current ratio when
  the current fixed non-surge reward rate is at most `R1`, the accept-all
  Lemma 9 lower endpoint is nonpositive, and the two fixed-state cross-ratio
  comparisons hold.  The pointwise variant
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_target_pointwise_fixed_transfer_data_assumptions`
  derives both cross-ratio comparisons by integrating a source-style equality
  on the current non-surge rejected complement.  The positive-ratio pointwise
  wrapper
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_target_positive_ratio_pointwise_fixed_transfer_data_assumptions`
  also derives the scalar gap `m_2-R1>0` from positivity of the constructed
  surge ratio.  The positive-mass sequential boundary also has a
  positive-parameter variant,
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_positive_parameter_positive_mass_feasible_sequential_weak_reward`,
  which preserves the constructed positive surge-ratio witness for downstream
  source adapters.  The corresponding reward-bound source wrapper
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_target_reward_bound_fixed_transfer_data_assumptions`
  uses that witness directly, so its policy-dependent field only carries the
  effective-ratio accounting, current reward upper bound, current reward
  nonnegativity, reward-rate identity, and fixed-state cross comparisons.  The
  no-ratio variant
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_target_reward_bound_fixed_transfer_no_ratio_data_assumptions`
  constructs the effective ratio internally, so callers no longer supply the
  quotient/accounting witness.  The final-sign variant
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_final_sign_reward_bound_fixed_transfer_no_ratio_data_assumptions`
  also derives the accept-all lower-endpoint nonpositivity from the paper's
  Lemma 9 final-sign line.  The current-lower/fixed-upper variant
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_current_lower_reward_bound_fixed_upper_no_ratio_data_assumptions`
  was an intermediate reduced boundary: it replaces the lower fixed-state
  cross-ratio comparison by a direct current Lemma 9 lower-endpoint
  nonpositivity proof, keeps only the upper fixed-state comparison, and still
  constructs the effective current ratio internally.
  The newer small-surge-slack wrapper
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_data_assumptions`
  specializes the compiled scalar small-ratio construction to measured
  accept-all primitives.  Its source-data structure
  `Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeSlackDataAssumptions`
  replaces per-candidate positive-parameter obligations with a sign-selected
  `Rmax`, a positive uniform lower bound `U` for current Lemma 9 upper
  endpoints, accept-all Lemma 9 endpoint facts, the zero-ratio numerator
  inequality, and current-policy lower/uniform-upper Lemma 9 facts.
  Two thinner compiled variants,
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_current_lower_data_assumptions`
  and
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_final_sign_data_assumptions`,
  derive the uniform-upper and lower-endpoint denominator work internally, so
  the newest source boundary only asks for the sign-selected `Rmax`, the
  zero-ratio numerator condition, and the current Lemma 9 lower-endpoint sign
  condition.  This lower-endpoint sign condition is stronger than the source
  Lemma 9 interval-feasibility final line, which proves `lower < upper` rather
  than `lower <= 0`; if the sign condition is not implied, the next proof
  route should use a non-small-ratio Lemma 9 construction instead.
  The current preferred interval route avoids that questionable current
  lower-sign step.  The compiled constructors
  `GN21SurgeLemma9AcceptAllAggregateRewardRateData.exists_of_reward_envelope_current_interval_slack`,
  `theorem3SurgeAggregate_ge_of_currentIntervalEnvelopeSlack`, and
  `theorem3SurgeAggregate_ge_of_currentSignedIntervalEnvelopeSlack` build the
  effective Lemma 9 ratio from the exact inequalities
  `current_lower*(m_2-r1_current)<z_2` and
  `z_2<current_upper*(m_2-Rmax)`.  The selected-price wrappers
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_interval_slack_data_assumptions`,
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_current_interval_slack_data_assumptions`,
  and
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_current_interval_slack_final_sign_data_assumptions`
  specialize this to the small-surge construction, derive the current upper
  slack internally from the uniform `U` bound, and leave the selected-price
  lower-slack inequality as the focused remaining policy-dependent Lemma 9
  obligation.
  A sharper mass-affine interval route is also compiled:
  `theorem3StructuredParameters_exist_of_ratio_and_small_surge_mass_affine_slack`,
  `paper_theorem3_measured_ctmc_structured_prices_exist_and_positive_mass_measurable_ic_of_ratio_and_sequential_accept_all_weak_reward_of_small_surge_mass_affine_slack`,
  `theorem3SurgeAggregate_ge_of_currentMassAffineSignedIntervalEnvelopeSlack`,
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_interval_slack_final_sign_data_assumptions`,
  and
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_interval_slack_final_sign_arrival_bound_data_assumptions`.
  This replaces the positive-`z_0` reward envelope `m_0+z_0*switch12` by the
  cycle-normalized envelope `max m_0 (arrival_0*z_0)`, using accept-all mass
  normalization and finite current mass.  The scalar helper
  `theorem3MassAffineRmax_zero_ratio_pos_of_arrival_z_le_R2` discharges the
  zero-ratio condition when `arrival_0*z_0 <= R2`; the newest source wrapper
  uses that bound directly instead of asking for the opaque zero-ratio
  numerator.
  This proves Theorem 3 IC by moving the surge state to accept-all first and
  then applying Lemma 10 only with the surge state already fixed at accept-all,
  avoiding the arbitrary-fixed-surge reward-rate mismatch.
  The derivation and remaining alternatives are
  recorded in `LEMMA9_10_REWARD_RATE_AUDIT.md`.  The current-bound layer also
  includes fixed-state
  cross-ratio union bridges
  `gn21FixedStateCross_le_union_of_increment_ratio_ge` and
  `gn21FixedStateCross_ge_union_of_increment_ratio_le` that reduce the
  remaining non-accept-all fixed-state transfer facts to increment ratio
  inequalities on added trips, with accept-all-complement specializations
  `gn21FixedStateCross_le_acceptAll_of_complement_increment_ratio_ge` and
  `gn21FixedStateCross_ge_acceptAll_of_complement_increment_ratio_le`, plus
  pointwise complement versions and shared-source helpers
  `GN21RegularEndpointSharedSourceData.*_fixed_cross_*_of_complement_pointwise`
  that feed the fixed-transfer endpoint records directly.
- Theorem 3 now has the `C` numerator-bound factorization, a measured
  accept-all `C ∈ [0,1)` theorem with that bound discharged, the non-surge
  `C < R1/R2 < 1` to Lemma 10 bounds bridge, direct Lemma 9 primitive
  feasibility for the surge ratio, and explicit surge/non-surge `m_i,z_i`
  accounting packages for the structured-price construction, plus a
  CTMC IC endpoint that consumes the positive-form Theorem 4 accept-all
  derivation directly.  The integrated endpoint can now also consume the
  global statewise accept-all reward comparisons or the stricter local
  improvement certificates produced by endpoint derivative proofs, including
  measured-reward and measured aggregate versions specialized to the actual
  two-state CTMC reward functional and positive-primitives variants that avoid
  the stronger Lemma 9 final-sign assumptions.  Accept-all-primitive versions
  discharge scalar positivity and, with state-2 accept-all time integrability,
  the direct Lemma 9 feasibility side conditions from measure/CTMC assumptions
  for both the strict-local and packaged statewise-certificate routes.  The
  source-domain strict-local route is now exposed as
  `Theorem3AcceptAllFeasibleStrictLocalSourceAssumptions` plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_feasible_strict_local_source_assumptions`,
  whose final field is the feasible measurable local-improvement certificate
  for constructed prices.  For IC alone, the closest current paper-facing
  endpoint to the Lemma 9/10 derivative proof is the sequential current-bounds
  wrapper above: it asks only for the surge Lemma 9 move at the current policy
  and the non-surge Lemma 10 move after surge is accept-all.  A narrower
  measurable-shape source boundary
  is now exposed as
  `Theorem3AcceptAllMeasurableShapeStatewiseImprovementSourceAssumptions` plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_statewise_improvements_source_assumptions`;
  its final field supplies the measurable Lemma 5 shape derivation together
  with the four feasible endpoint-improvement cases, and Lean converts that
  into the feasible strict-local certificate internally.  The all-measurable
  replacement variant is now exposed as
  `Theorem3AcceptAllMeasurableShapeReplacementStatewiseImprovementSourceAssumptions`
  plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_replacement_statewise_improvements_source_assumptions`;
  it derives the shape derivation internally from Lemma 5-style replacement
  data using
  `Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate.of_all_measurable_shape_replacements`.
  The endpoint current-bounds selection boundary is now exposed as
  `Theorem4MeasurableEndpointCurrentBoundsSelectionCertificate`,
  `Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate.of_endpoint_current_bounds_selection`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_selection`,
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsSelectionSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_selection_source_assumptions`;
  it packages the all-measurable Lemma 5 replacement data together with the
  density endpoint choices and Lemma 9/10 current-bounds data for all four
  shape cases.  A hnot-aware variant,
  `Theorem4MeasurableEndpointCurrentBoundsSelectionUnlessCertificate` plus
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_selection_unless`,
  preserves the `¬ acceptsAllTrips` hypothesis until endpoint witnesses are
  chosen; this is the preferred internal shape-selection interface when cutoff
  nondegeneracy is derived from the actual non-accept-all branch rather than
  assumed for every syntactic shape case.  The accompanying shape-normalization
  lemmas
  `acceptsAllTrips_of_rejectsShortTrips_of_nonpos`,
  `cutoff_pos_of_rejectsShortTrips_of_not_acceptsAll`,
  `acceptsAllTrips_of_rejectsMiddleTrips_of_hi_nonpos`,
  `hi_pos_of_rejectsMiddleTrips_of_not_acceptsAll`, and
  `rejectsShortTrips_of_rejectsMiddleTrips_of_lo_nonpos` formalize the
  degenerate-cutoff reductions needed by this route.  The Theorem 3 source
  boundary for the same route is now exposed as
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsSelectionUnlessSourceAssumptions`
  plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_selection_unless_source_assumptions`.
  The direct hnot-aware statewise route
  `Theorem4MeasurableShapeReplacementStatewiseImprovementUnlessCertificate`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_shape_replacement_statewise_improvements_unless`,
  `Theorem3AcceptAllMeasurableShapeReplacementStatewiseImprovementUnlessSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_shape_replacement_statewise_improvements_unless_positive_source_assumptions`
  lets a proof normalize degenerate syntactic shape cases inside the
  non-accept-all branch and return the final feasible statewise improvement
  directly, rather than forcing every branch through a same-shape endpoint
  data record.  The endpoint-data specialization
  `Theorem4MeasurableEndpointCurrentBoundsSelectionUnlessMiddleRerouteCertificate`
  plus
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_selection_unless_middle_reroute_positive_source_assumptions`
  implements the first such reroute: a surge reject-middle branch with
  `lo <= 0` is discharged by the short-tail endpoint at cutoff `hi`, so source
  proofs only need reject-middle endpoint data for the `0 <= lo` branch.
  The source-facing variant is now exposed as
  `Theorem4NonsurgeMeasurableReplacementData`,
  `Theorem4SurgeMeasurableReplacementData`,
  `Theorem4AllMeasurableOptimalShapeReplacementDerivationCertificate.of_allowed_replacement_data`,
  `Theorem4AllMeasurableAllowedPolicyFormsCertificate.of_shape_replacements`,
  `Theorem4MeasurableEndpointCurrentBoundsAllowedReplacementSelectionCertificate`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_allowed_replacement_selection`,
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsAllowedReplacementSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_allowed_replacement_source_assumptions`;
  it derives feasible measurability of the canonical Lemma 5 replacement
  policies from ordinary allowed replacement cases.  The density-support layer
  `GN21WithDensityAcceptAllSupport` and the five
  `GN21...CurrentBoundsEndpointData.of_acceptAll_support` constructors now
  derive current/replacement finite-mass and positive-density endpoint fields
  from finite positive accept-all density support.  The endpoint calculus
  helpers `continuous_gn21SwitchProb`,
  `continuous_ctmcStructuredSurgePrice`, and
  `intervalIntegrable_mul_density_of_continuous` derive the finite-interval
  continuity, strong-measurability, and integrability fields from continuous
  densities, with `GN21EndpointProductContinuityData` and
  `GN21FiniteEndpointProductCalculusData` bundling those fields for structured
  prices.  The endpoint constructors ending in
  `of_acceptAll_support_and_calculus` or
  `of_acceptAll_support_and_continuity` consume both the density support and
  product-calculus packages.  `GN21PositiveIntervalProductIntegrabilityData`
  derives short accepted-interval integrability from continuous product data,
  while `GN21TailProductIntegrabilityData` bundles improper tail integrability
  and reuses it for narrower tails.  `GN21RegularEndpointSharedSourceData` and
  the five `...RegularEndpointData.of_shared_source` constructors now factor
  shared density support, density continuity, arrival/switch positivity, and
  accept-all integrability out of the regular endpoint cases; the shared
  source package now also discharges routine fixed-state scaled-time and
  exit-weight positivity for the composed accept-all-tightening endpoint
  builders.  Fixed-state current-bound transfer is explicit:
  `lemma10StructuredBounds_of_acceptAll_fixed_state_measured_expansion`
  reduces the Lemma 10 side to a cross-ratio condition, while the Lemma 9
  comparison lemmas show that its lower and upper fixed-state transfers require
  opposite cross-ratio directions.  The two non-surge regular endpoint cases
  now have Theorem 3 parameter-data constructors that consume this Lemma 10
  transfer directly, replacing current-fixed Lemma 10 bounds with the single
  fixed-state cross-ratio condition.  The three surge regular endpoint cases
  have analogous constructors using the Lemma 9 transfer and therefore expose
  both cross-ratio directions explicitly.  The Theorem 3 fixed-transfer regular
  endpoint route is now exposed as
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularAllowedPolicyFormsCertificate`,
  the local source records
  `GN21NonsurgeRejectLongTheorem3FixedTransferLocalData`,
  `GN21NonsurgeAcceptMiddleTheorem3FixedTransferLocalData`,
  `GN21SurgeRejectShortTheorem3FixedTransferLocalData`, and
  `GN21SurgeRejectMiddleTheorem3FixedTransferLocalData`,
  and the paper-facing wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_policy_forms_source_assumptions`.
  A stronger positive-evidence wrapper is exposed as
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_policy_forms_positive_source_assumptions`;
  it preserves the positive surge-ratio witness from the Theorem 3 construction
  through `theorem3AcceptAllStructuredPositiveParameterEvidence`.  The narrower
  shape-replacement boundary
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_shape_replacement_positive_source_assumptions`
  now derives the all-optimal policy-form classification from all-measurable
  Lemma 5 replacement data and asks separately only for the fixed-transfer local
  endpoint facts.  The lighter
  `Theorem4AllMeasurableOptimalAllowedReplacementData` package and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_positive_source_assumptions`
  let the source proof give ordinary allowed Lemma 5 replacement cases instead.
  The support-derived `GN21...Theorem3FixedTransferLocalData.of_positive_cutoff`
  constructors, the positive-cutoff local endpoint certificate, and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_positive_cutoff_source_assumptions`
  remove `hdensity_pos` from the positive-cutoff source boundary: positive
  cutoffs plus accept-all density support now derive density positivity
  internally.  The `...PositiveCutoffLocalData.of_other_acceptAll`
  constructors additionally discharge the fixed-state cross-ratio,
  positive-mass, and accounting fields whenever the fixed other state already
  accepts all trips, using equality, accept-all mass positivity from shared
  support, and `Theorem3AcceptAllStructuredParameterData`.  The
  `...PositiveCutoffLocalData.of_fixed_complement_pointwise` constructors
  discharge the non-accept-all fixed-state cross-ratio fields from pointwise
  complement ratio comparisons plus the existing mass and accounting facts.
  Shared-source accounting helpers
  `GN21RegularEndpointSharedSourceData.nonsurge_fixed_accounting_of_reward_rate`
  and
  `GN21RegularEndpointSharedSourceData.surge_fixed_accounting_of_reward_rate`
  convert measured fixed-state reward-rate equalities into those accounting
  equations, and the corresponding
  `...PositiveCutoffLocalData.of_fixed_complement_pointwise_reward_rate`
  constructors use those helpers directly.  The pointwise/reward-rate local
  endpoint certificate
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularPointwiseRewardRateLocalEndpointCertificate`
  and source wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_pointwise_reward_rate_source_assumptions`
  expose the pointwise fixed-transfer boundary when the source proof supplies
  allowed replacement data.  The mass-separated endpoint certificate
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularPointwiseRewardRateMassSeparatedLocalEndpointCertificate`
  and wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_pointwise_reward_rate_mass_separated_source_assumptions`
  factor fixed-state positive mass once per state and then reuse it across all
  local endpoint cases.  The no-mass endpoint certificate
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularPointwiseRewardRateNoMassLocalEndpointCertificate`
  and wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_pointwise_reward_rate_no_mass_source_assumptions`
  derive the state-level
  mass fields from allowed Lemma 5 forms, accept-all mass positivity, and
  nondegenerate non-surge cutoffs.  The sibling wrappers
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_policy_forms_pointwise_reward_rate_source_assumptions`
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_policy_forms_pointwise_reward_rate_mass_separated_source_assumptions`
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_policy_forms_pointwise_reward_rate_no_mass_source_assumptions`
  accept all-optimal allowed policy forms directly.  Shared-source mass helpers
  `GN21RegularEndpointSharedSourceData.surge_current_mass_pos_of_allowed_policy_form`
  and
  `GN21RegularEndpointSharedSourceData.nonsurge_current_mass_pos_of_allowed_policy_form`
  derive the state-level mass fields from Lemma 5 allowed policy forms and
  cutoff nondegeneracy when those are available.  Equality constructors ending
  in `PointwiseRewardRateNoMassLocalData.of_fixed_complement_pointwise_eq`
  let source proofs provide a single fixed-state pointwise equality instead of
  separate lower/upper complement comparisons in the surge fixed-transfer
  cases.  The no-mass constructors ending in `of_other_acceptAll` discharge
  the fixed-state pointwise and reward-rate fields directly when the fixed
  other state accepts all trips, using Theorem 3 accept-all accounting and
  empty rejected complement.  Reusable fixed-state packages
  `GN21SurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassData` and
  `GN21NonsurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassData`
  now feed the corresponding non-surge and surge moving-state endpoint cases,
  so the source proof can establish fixed-state transfer once per state and
  reuse it across endpoint branches.  The fixed-state-separated endpoint
  certificate
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateSeparatedLocalEndpointCertificate`
  and wrappers
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_separated_source_assumptions`
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_policy_forms_fixed_state_separated_source_assumptions`
  let source proofs supply one fixed-state package for each state plus only
  the remaining surge moving-state cutoff-gap/tail data, and Lean expands that into
  the no-mass, mass-separated, pointwise, positive-cutoff, and regular endpoint
  routes internally.  The non-surge accept-middle branch chooses its local move
  directly from the positive lower cutoff.  The policy-form fixed-state data records
  `GN21SurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassPolicyFormData`
  and
  `GN21NonsurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassPolicyFormData`,
  the endpoint certificate
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateByPolicyFormLocalEndpointCertificate`,
  and wrappers
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_source_assumptions`
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_policy_forms_fixed_state_by_policy_form_source_assumptions`
  let all-optimal Lemma 5 allowed policy forms choose the fixed-state branch
  internally.  The tail-integrability layer now includes
  `integrableOn_Ioi_of_intervalIntegrable_of_integrableOn_Ioi`,
  `GN21TailProductIntegrabilityData.of_interval_and_tail`, and
  `GN21TailProductIntegrabilityData.of_ctmcStructured_positive_tail`, which
  extend positive-tail assumptions to arbitrary lower cutoffs using continuous
  finite-interval product calculus.  The positive-tail package
  `GN21SurgeTheorem3FixedTransferPositiveTailData` derives the older
  uniform-tail package `GN21SurgeTheorem3FixedTransferUniformTailData`, while
  `GN21SurgeTheorem3FixedTransferPositiveTailData.of_shared_acceptAll` derives
  positive surge tails from the shared accept-all time/switch integrability
  fields.  The common fixed-state equality packages
  `GN21SurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassEqData`
  and
  `GN21NonsurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassEqData`
  supply one complement pointwise equality plus one reward-rate identity per
  state and convert to the policy-form records internally.  The cutoff-bounds
  endpoint certificate
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateByPolicyFormDerivedTailCutoffBoundsLocalEndpointCertificate`
  derives the older `GN21SurgeRejectMiddleMovingCutoffChoice` internally.  The
  common fixed-state-equality cutoff-bounds endpoint certificate
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailCutoffBoundsLocalEndpointCertificate`
  converts those common packages to the by-policy-form endpoint, and the new
  direct bridge
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailCutoffBoundsLocalEndpointCertificate.to_fixed_state_separated`
  feeds the fixed-state-separated endpoint route without first selecting a
  Lemma 5 policy-form branch for the fixed state.  The
  derived-tail endpoint certificate
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateByPolicyFormDerivedTailLocalEndpointCertificate`,
  and wrappers
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_cutoff_bounds_source_assumptions`,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_derived_tail_cutoff_bounds_source_assumptions`,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_derived_tail_source_assumptions`,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_positive_tail_source_assumptions`,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_uniform_tail_source_assumptions`
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_policy_forms_fixed_state_by_policy_form_uniform_tail_source_assumptions`
  are compiled fixed-state adapters: the source proof
  supplies ordinary allowed Lemma 5 replacement data, common fixed-state
  complement pointwise equality and reward-rate facts for each state, and
  ordinary surge cutoff bounds; Lean derives the branch-specific policy-form
  packages, surge moving-cutoff choice, and tail-integrability package
  internally.  The corresponding source adapter
  `Theorem3AcceptAllMeasurableEndpointTheorem3FixedTransferRegularAllowedReplacementFixedStateEqDerivedTailCutoffBoundsSourceAssumptions.to_fixed_state_separated_source_assumptions`
  and wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_cutoff_bounds_source_assumptions_via_fixed_state_separated`
  consume the same common fixed-state equality package through the separated
  route directly.  The hnot-aware fixed-transfer adapters
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularAllowedPolicyFormsCertificate.to_endpoint_current_bounds_selection_unless`,
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateByPolicyFormDerivedTailCutoffBoundsLocalEndpointCertificate.to_fixed_transfer_allowed_policy_forms_of_shape_replacements`,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_derived_tail_cutoff_bounds_source_assumptions_via_selection_unless`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_cutoff_bounds_source_assumptions_via_selection_unless`
  thread those existing packages through `SelectionUnless`.  The newer
  adapters
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateByPolicyFormDerivedTailCutoffBoundsLocalEndpointCertificate.to_middle_reroute`,
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailCutoffBoundsLocalEndpointCertificate.to_middle_reroute`,
  `Theorem3AcceptAllMeasurableEndpointTheorem3FixedTransferRegularAllowedReplacementFixedStateByPolicyFormDerivedTailCutoffBoundsSourceAssumptions.to_middle_reroute_source_assumptions`,
  and
  `Theorem3AcceptAllMeasurableEndpointTheorem3FixedTransferRegularAllowedReplacementFixedStateEqDerivedTailCutoffBoundsSourceAssumptions.to_middle_reroute_source_assumptions`
  route those same cutoff-bounds packages through the preferred
  middle-reroute endpoint boundary directly.  The remaining closeout target is
  now to prove or weaken the fixed-state/cutoff-bound source fields from the
  paper's regularity hypotheses, not to maintain a parallel cutoff-only proof
  path.  The reject-long fixed-state
  lower-comparison side is now internal:
  `GN21RegularEndpointSharedSourceData.nonsurge_lower_pointwise_of_rejectsLongTrips`,
  `GN21RegularEndpointSharedSourceData.nonsurge_fixed_cross_ge_acceptAll_of_rejectsLongTrips`,
  `GN21NonsurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassData.of_rejectsLongTrips_and_upper`,
  and
  `GN21NonsurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassPolicyFormData.of_rejectLong_upper`
  reduce the non-surge reject-long fixed-state package from a complement
  equality to the remaining upper inequality plus the fixed reward-rate
  identity.  The lower fixed-transfer
  middle-reroute boundary
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularAllowedPolicyFormsMiddleRerouteCertificate`
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_middle_reroute_source_assumptions`
  now expose exactly that reduced source shape: local endpoint facts receive
  the relevant non-accept-all hypothesis, and reject-middle local data is only
  required when `0 <= lo`.  Lean also now has the nonatomic boundary bridge
  showing that a reject-middle policy with coincident cutoffs (`lo = hi`)
  differs from accept-all only by one trip length and leaves the single-state
  reward and GN21 `Q,T,W` primitives unchanged after removing that
  measure-zero component; left- and right-state aggregate-reward wrappers expose
  this directly for Theorem 4/Theorem 3 weak branches.
  The source with-density support package now also exposes this as
  `GN21WithDensityAcceptAllSupport.lo_lt_hi_of_rejectsMiddleTrips_of_rejected_mass_pos`
  and
  `GN21RegularEndpointSharedSourceData.surge_rejectMiddle_lo_lt_hi_of_rejected_mass_pos`:
  positive rejected mass rules out the collapsed surge middle-rejection gap,
  while the collapsed branch is accepted as almost-everywhere accept-all.
  The reusable AE endpoint layer is now compiled as
  `Theorem4MeasurableShapeReplacementStatewiseRejectedMassImprovementUnlessCertificate`,
  `theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementCertificate_of_shape_replacement_statewise_rejected_mass_improvements_unless`,
  and
  `paper_theorem4_measurable_accept_all_ae_unique_optimal_of_endpoint_current_bounds_selection_unless_middle_reroute`.
  The fixed-transfer local endpoint feed into that AE layer is also compiled as
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateByPolicyFormDerivedTailMiddleRerouteAELocalEndpointCertificate`,
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateByPolicyFormDerivedTailMiddleRerouteAELocalEndpointCertificate.to_shape_replacement_rejected_mass_improvements_of_shape_replacements`,
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteAELocalEndpointCertificate`,
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteAELocalEndpointCertificate.to_by_policy_form_ae_local_endpoint`,
  and
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteLocalEndpointCertificate.to_ae_local_endpoint`;
  this is the Lean bridge corresponding to the paper's equality-up-to-null-sets
  convention for collapsed middle-rejection gaps.
  The Theorem 3 wrappers that consume this AE boundary are now compiled as
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_rejected_mass_strict_local_positive_parameters`,
  `GN21Theorem3MiddleRerouteAEEndpointSourceData`,
  `theorem3AcceptAllFeasibleRejectedMassStrictLocalPositiveParameterCertificate_of_ae_endpoint_middle_reroute`,
  `Theorem3AcceptAllMeasurableAEEndpointMiddleRerouteSourceAssumptions`,
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_ae_endpoint_middle_reroute_source_assumptions`,
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_derived_tail_middle_reroute_ae_source_assumptions`,
  `GN21Theorem3MiddleRerouteLightAEEqSourceData`,
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_middle_reroute_light_ae_source_assumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_middle_reroute_ae_source_assumptions`.
  The first four declarations are the direct measure-theoretic endpoint
  boundary: Theorem 3 can now consume shared regularity plus the AE endpoint
  selection certificate without first packaging exact all-measurable Lemma 5
  replacement data.  The later wrappers use source-data records
  `GN21Theorem3MiddleRerouteAEPolicyFormSourceData` and
  `GN21Theorem3MiddleRerouteLightAEEqSourceData` or
  `GN21Theorem3MiddleRerouteAEEqSourceData` so the proof can separately supply
  Lemma 5 replacement data, accept-all optimality, and the local fixed-state
  endpoint package; prefer the light Eq source data for AE uniqueness because it
  does not ask for the exact-route all-branch surge middle-gap fact.  The stronger exact middle-reroute source boundaries now
  feed this AE route directly through
  `Theorem3AcceptAllMeasurableEndpointTheorem3FixedTransferRegularAllowedReplacementFixedStateByPolicyFormDerivedTailMiddleRerouteSourceAssumptions.to_ae_source_assumptions`,
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_derived_tail_middle_reroute_source_assumptions_via_ae`,
  `Theorem3AcceptAllMeasurableEndpointTheorem3FixedTransferRegularAllowedReplacementFixedStateEqDerivedTailMiddleRerouteSourceAssumptions.to_ae_source_assumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_middle_reroute_source_assumptions_via_ae`.
  The stronger cutoff-bounds source boundaries now feed the same route through
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_derived_tail_cutoff_bounds_source_assumptions_via_middle_reroute`
  and
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_cutoff_bounds_source_assumptions_via_middle_reroute`.
  These adapters derive the separate accept-all optimality field from the
  compiled Theorem 4 middle-reroute endpoint proof, then forget the all-branch
  reject-middle gap assumption to the positive-rejected-mass AE local endpoint.
  These adapters are strongest in accept-all fixed-state branches;
  the source-faithful closure path remains the regular current-bounds route
  until the non-accept-all fixed-state reward-rate issue is discharged.
  Its local records state the fixed-state structured-price accounting
  equations, and Lean expands those equations to the scaled-earning
  reward-rate identities using Remark 2.  It also derives the surge
  `m 1 - R1 > 0` side condition from the shared source, positive surge
  accept-all mass, Theorem 3 ratio positivity, and the constructed parameter
  data.  The current regular allowed-policy-form
  endpoint route is now exposed as
  the five `GN21...RegularEndpointData` packages,
  `Theorem4AllMeasurableAllowedPolicyFormsCertificate`,
  `Theorem4MeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsCertificate`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_allowed_policy_forms`,
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_allowed_policy_forms_source_assumptions`;
  the same regular shape, regular allowed-policy-form, and Theorem 3
  fixed-transfer boundaries now have AE-uniqueness-returning wrappers
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_current_bounds_regular_shape_source_assumptions`,
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_current_bounds_regular_allowed_policy_forms_source_assumptions`,
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_policy_forms_source_assumptions`,
  and the positive-parameter fixed-transfer wrapper
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_policy_forms_positive_source_assumptions`,
  with the fixed-state-equality cutoff-bounds source boundary exposed as
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_cutoff_bounds_source_assumptions`
  and now also routed through the middle-reroute AE endpoint as
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_cutoff_bounds_source_assumptions_via_middle_reroute`;
  the branch-local middle-reroute fixed-transfer source boundary is now exposed
  through the by-policy-form and fixed-state-equality wrappers
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_derived_tail_middle_reroute_source_assumptions`
  and
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_middle_reroute_source_assumptions`;
  it consumes the all-optimal measurable Lemma 5 allowed policy-form
  classification plus continuous-density endpoint data, source Lemma 9/10
  current-bounds data, support, and tail-integrability packages, then chooses a
  representative optimum and derives the feasible strict-local Theorem 4
  certificate internally.  All-measurable Lemma 5 replacement data can now
  provide the policy-form classification directly through
  `Theorem4AllMeasurableAllowedPolicyFormsCertificate.of_shape_replacements`.
  The regular-shape route remains exposed as
  `Theorem4MeasurableEndpointCurrentBoundsRegularShapeDerivationCertificate`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_shape_derivation`,
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularShapeSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_shape_source_assumptions`;
  it is useful when the caller has already packaged the measurable Lemma 5
  shape derivation.  The older regular-selection route remains exposed as
  the five `GN21...RegularEndpointData` packages,
  `Theorem4MeasurableEndpointCurrentBoundsRegularSelectionCertificate`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_selection`,
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_source_assumptions`;
  it additionally asks for ordinary allowed Lemma 5 replacement data and expands
  the regular endpoint packages into the supported endpoint route internally.
  The supported endpoint route remains exposed as
  the five `GN21...SupportedEndpointData` packages,
  `Theorem4MeasurableEndpointCurrentBoundsSupportedSelectionCertificate`,
  `paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_supported_selection`,
  `Theorem3AcceptAllMeasurableEndpointCurrentBoundsSupportedSourceAssumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_supported_source_assumptions`;
  it expands ordinary allowed replacement cases plus density-support,
  calculus-backed endpoint data, and short/tail integrability packages into the
  allowed-replacement current-bounds route internally.  The lightest current
  IC-only source boundary is now exposed as
  `Theorem3AcceptAllWeakRewardSourceAssumptions` plus
  `paper_theorem3_measured_structured_ic_prices_of_weak_reward_source_assumptions`,
  whose final field is just weak statewise accept-all reward improvement for
  the constructed prices and does not require exact-set uniqueness of all
  optima. This can now be supplied from a weak measured aggregate `Q,T,W`
  certificate through
  `theorem3AcceptAllWeakRewardCertificate_of_measured_aggregate_weak_reward`,
  with accept-all-complement bridges reducing each statewise weak improvement
  to pointwise nonnegativity of the Lemma 6 kernel over the rejected feasible
  complement plus the usual denominator and integrability side conditions.
  The direct constructors
  `GN21NonsurgeLemma10AcceptAllAggregateData.of_source` and
  `GN21SurgeLemma9AcceptAllAggregateData.of_source` now compose source Lemma
  9/10 data with the primitive current-bounds route in one step.
  The current-bounds route is now packaged as
  `Theorem4MeasuredAggregateStructuredCurrentBoundsWeakCertificate`, which
  feeds the weak Theorem 3 boundary through
  `theorem3AcceptAllWeakRewardCertificate_of_structured_current_bounds`; the
  direct source wrapper is
  `paper_theorem3_measured_structured_ic_prices_of_structured_current_bounds_source_assumptions`.
  A lighter primitive current-bounds boundary,
  `Theorem4MeasuredAggregateStructuredCurrentBoundsPrimitiveCertificate`, now
  derives aggregate denominator and fixed-state positivity side conditions
  from feasible measurable policies, nonnegative arrivals, and positive switch
  rates, with source wrapper
  `paper_theorem3_measured_structured_ic_prices_of_structured_current_bounds_primitive_source_assumptions`.
  The source-domain variant now exposes
  `dynamicMeasurableIncentiveCompatible` and
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_feasible_primitive_source_assumptions`,
  whose remaining current-bounds proof ranges only over feasible measurable
  dynamic policies.
  The lightest source-data version,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_source_feasible_source_assumptions`,
  derives nondegeneracy, current/rejected-set integrability, and Remark 4
  `Q > lambda` / `lambda*T-Q >= 0` side conditions from global accept-all
  integrability, positive rates, feasible measurability, and positive current
  mass.
  The same source-data route now also exposes the paper's measure-zero policy
  equality convention via
  `theorem3MeasuredStructuredMeasurableICAEUniqueConclusion` and
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_current_bounds_source_feasible_source_assumptions`:
  constructed structured CTMC prices are measurable IC, and every measurable
  optimum rejects only a zero-measure subset of the feasible accept-all trips
  in each state.
  The feasible primitive, accounting-form, and reward-rate current-bounds
  source boundaries expose the same conclusion through
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_current_bounds_feasible_primitive_source_assumptions`,
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_current_bounds_accounting_source_assumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_current_bounds_reward_rate_source_assumptions`.
  The accounting-form wrapper,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_accounting_source_assumptions`,
  further replaces fixed-state reward-rate identities with the structured
  price accounting equations discharged by Remark 2.  The reward-rate wrapper,
  `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_current_bounds_reward_rate_source_assumptions`,
  goes in the other direction: fixed-state source obligations can be stated as
  measured reward-rate equalities, and Lean derives the scaled earning
  identities `W_i = R_i T_i` needed by the current-bounds route.
  The stronger positive-replacement source boundary is exposed as
  `Theorem3AcceptAllPositiveReplacementSourceAssumptions` plus
  `paper_theorem3_measured_structured_ic_prices_of_positive_replacement_source_assumptions`,
  whose final field is exactly the Lemma 9/10 positive-replacement proof for
  the constructed prices. The broader allowed-replacement route is also
  exposed as `Theorem3AcceptAllAllowedReplacementSourceAssumptions` plus
  `paper_theorem3_measured_structured_ic_prices_of_source_assumptions`, whose
  proof boundary is the continuous allowed-replacement Theorem 4 certificate
  for the constructed prices; endpoint-bridge data can now be converted
  directly into that boundary via
  `Theorem4AllowedReplacementEndpointBridgeCertificate` and
  `theorem3AcceptAllAllowedReplacementCertificate_of_endpoint_bridges`, with a
  direct source wrapper
  `paper_theorem3_measured_structured_ic_prices_of_endpoint_bridge_source_assumptions`.
- The finite MDP declarations are marked auxiliary support only. They are not
  used to claim the paper's continuous CTMC theorems.
- The DAG uses the shared TikZ preamble and separates solid verified support
  edges from dashed continuous-source proof debts. Lemma 3 now has outgoing
  verified dependencies into Lemma 1 and the aggregate-reward/Lemma 6 pipeline,
  matching the paper's use of time fractions in the dynamic reward formula.
  Proposition 3.1 now has a solid model-to-result edge rather than a dependency
  on Theorem 1, since the renewal-reward affine IC proof is direct.

## Paper-Facing Ledger

- Human-facing theorem file: `GN21DriverSurgePricing/MainTheorems.lean`
- Dependency DAG: `GN21DriverSurgePricing/DependencyDAG.tex`
- Rendered DAG: `GN21DriverSurgePricing/DependencyDAG.pdf`

Status cells use the controlled vocabulary from `../../docs/STATUS.md`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Section 2.2, driver optimality and IC definitions | `singleStateOptimal`, `singleStateIncentiveCompatible`, `dynamicOptimal`, `dynamicIncentiveCompatible`, `dynamicStateReward`, `dynamicStateReward_optimal_of_dynamicOptimal`, `dynamicOptimal_acceptAll_of_statewise_acceptAll_improvements`, `singleStateTripMass`, `singleStateTripTime`, `singleStateTripPayment`, `singleStateRenewalReward`, `SingleStateRenewalLLNCertificate`, `SingleStateRenewalIIDCycleModel`, `paper_section2_single_state_renewal_reward_stochastic_bridge`, `paper_section2_single_state_renewal_reward_iid_stochastic_bridge` | formalized | `MainTheorems.lean`, `EconCSLib/Foundations/Probability/RenewalReward.lean` | None; continuous source predicates and the single-state renewal-reward formula are represented over real trip-length acceptance sets and set integrals. The single-state stochastic theorem now has both the older LLN-certificate bridge and an explicit IID-cycle model whose sample quotient is closed by mathlib's strong law. |
| Lemma 1, dynamic earnings decomposition | `gn21SubcycleEarning`, `gn21ExpectedStateEarningInRenewalCycle`, `gn21StateRewardRate`, `gn21StateMeanEarning`, `gn21MeasuredStateRewardRate`, `gn21MeasuredDynamicReward`, `GN21DynamicRenewalLLNCertificate`, `paper_lemma1_stochastic_dynamic_reward_decomposition`, `GN21DynamicIIDCycleModel`, `paper_lemma1_stochastic_dynamic_reward_decomposition_of_iid_cycles`, `gn21MeasuredStateRewardRate_eq_scaled_primitives`, `gn21MeasuredTimeFraction_eq_scaled_primitives`, `paper_lemma1_measured_dynamic_reward_eq_aggregate_scaled_primitives`, `gn21MeasuredAggregateRewardPrimitives`, `GN21MeasuredPairNondegenerate`, `gn21MeasuredPairNondegenerate_of_positive_primitives`, `gn21MeasuredPairNondegenerate_of_positive_measure`, `gn21MeasuredPairNondegenerate_of_positive_measure_upperEndpoint_right`, `gn21MeasuredPairNondegenerate_of_positive_measure_upperEndpoint_left`, `singleStateTripMass_pos_of_measure_ne_zero_ne_top`, `singleStateTripMass_withDensity_pos_of_pos_on`, `singleStateTripMass_upperEndpoint_withDensity_pos_of_pos_on`, `singleStateTripMass_upperEndpointReplacement_withDensity_pos_of_pos_on`, `gn21MeasuredPairNondegenerate_of_upperEndpoint_withDensity_right`, `gn21MeasuredPairNondegenerate_of_upperEndpoint_withDensity_left`, `paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives`, `paper_lemma1_measured_dynamic_reward_eq_aggregate_primitives_of_nondegenerate`, `paper_lemma1_measured_dynamic_reward_le_of_aggregate_primitives_le`, `paper_lemma1_measured_dynamic_reward_lt_of_aggregate_primitives_lt`, `paper_lemma1_measured_dynamic_reward_le_of_aggregate_pair_le_of_nondegenerate`, `paper_lemma1_measured_dynamic_reward_lt_of_aggregate_pair_lt_of_nondegenerate`, `gn21MeasuredDynamicRewardFunctional`, `gn21MeasuredDynamicRewardFunctional_apply`, `gn21MeasuredCTMCStructuredDynamicReward`, `gn21AcceptAllScaledStateTime`, `gn21AcceptAllExitWeightIntegral`, `dynamicStateReward_gn21MeasuredDynamicRewardFunctional_zero`, `dynamicStateReward_gn21MeasuredDynamicRewardFunctional_one`, `paper_lemma1_state_reward_rate_algebra`, `paper_lemma1_measured_state_reward_rate_algebra`, `paper_lemma1_measured_dynamic_reward_decomposition` | formalized | `MainTheorems.lean`, `EconCSLib/Foundations/Probability/RenewalReward.lean` | None; Lean proves the displayed reward-rate cancellation, the measured `mu_i R_i + mu_j R_j` decomposition, and an almost-sure IID-cycle theorem for dynamic reward. `GN21DynamicIIDCycleModel` encodes the paper's renewal-cycle variables, source primitive positivity and feasible-policy assumptions, expected cycle-time/earning identities, and IID/integrability hypotheses, while mathlib's strong law proves the sample-path quotient convergence. Lean derives the transition-probability, state-cycle-time, and total-cycle-time nonzero side conditions internally. Lemma 3's time-fraction bridge is used explicitly in the proof path, and the aggregate `Q,T,W` quotient feeds Lemma 6. |
| Theorem 1, single-state threshold best response | `strictThresholdPolicy`, `completeThresholdPolicy`, `thresholdBoundaryPolicy`, `paper_theorem1_policy_le_complete_threshold_at_own_reward`, `paper_theorem1_step2_partial_threshold_dominated_by_strict_or_complete`, `paper_theorem1_high_reward_band_or_gap`, `upperSemicontinuousOn_theorem1_cutoff_objective`, `paper_theorem1_single_state_threshold_best_response_measurable` | formalized | `MainTheorems.lean`, `EconCSLib/Foundations/Probability/RenewalReward.lean` | Lean proves the source measurable single-state threshold best response for nonnegative measurable on-trip rates with finite accept-all mass, accept-all payment/time integrability, positive arrival rate, and positive accept-all payment. Step 1 sends any measurable feasible policy to the complete threshold at its own renewal reward; Step 2 reduces partial thresholds to strict/complete thresholds; Step 3 obtains a compact maximizer using tail bounds, the high-reward band/gap split, and one-sided dominated convergence, so atoms on threshold boundaries are allowed. |
| Proposition 3.1, affine single-state IC | `affinePricing`, `multiplicativePricing`, `singleStateTripPayment_affinePricing`, `affineSingleStateRenewalReward`, `SingleStateTripMeasureAssumptions`, `singleStateTripMeasureAssumptions_of_standard`, `singleStateTripMass_eq_zero_of_time_zero_subset_acceptAll`, `singleStateMeasurableIncentiveCompatible`, `affineSingleStateRenewalReward_acceptAll_diff_eq_complementReward`, `paper_proposition3_1_affine_rejected_set_average_rate_bound`, `paper_proposition3_1_affine_accept_all_ge_rejecting_any_measurable_set`, `paper_proposition3_1_affine_accept_all_ge_measurable_policy`, `paper_proposition3_1_affine_single_state_measurable_ic`, `paper_proposition3_1_affine_single_state_measurable_ic_of_standard_measure`, `paper_proposition3_1_affine_single_state_renewal_reward_measurable_ic`, `paper_proposition3_1_affine_single_state_renewal_reward_measurable_ic_of_standard_measure`, `paper_corollary_single_state_multiplicative_pricing_measurable_ic`, `paper_corollary_single_state_multiplicative_pricing_measurable_ic_of_standard_measure`, `SingleStateAffineICCertificate`, `paper_proposition3_1_affine_single_state_ic_of_certificate` | formalized | `MainTheorems.lean` | None; Lean proves the continuous source endpoint: under `0 <= a <= m/lambda`, accept-all is optimal among all measurable feasible policies for the actual single-state renewal reward `singleStateRenewalReward μ λ (affinePricing m a)`. Setting `a=0` gives the main-text single-state multiplicative-pricing IC corollary for `singleStateRenewalReward μ λ (multiplicativePricing m)`. The standard-measure constructor derives the basic nonnegativity, rejected-set time monotonicity, finite-subset, subset-integrability, and zero-time feasible-set mass facts automatically from the accept-all first moment. |
| Lemma 2 and Remarks 1/3/4, two-state CTMC transition probability | `gn21SwitchProb`, `gn21TransitionProb`, `paper_lemma2_switch_probability_formula`, `paper_lemma2_switch_probability_forward_equation`, `paper_lemma2_switch_probability_pos`, `paper_lemma2_switch_probability_nonneg`, `paper_lemma2_switch_probability_le_one`, `paper_lemma2_transition_probability_zero_time`, `paper_lemma2_transition_probability_row_sum`, `paper_remark1_switch_probability_per_time_deriv_neg`, `paper_remark1_switch_probability_per_time_strictAntiOn`, `paper_remark3_switch_probability_deriv_at_zero`, `paper_remark3_switch_probability_per_time_tendsto_at_zero`, `paper_remark4_switch_probability_lt_rate_mul_time`, `paper_remark4_switch_probability_per_time_lt_rate`, `paper_remark4_switch_time_minus_switch_probability_pos`, `paper_remark4_switch_time_minus_switch_probability_nonneg`, `paper_remark4_switch_time_minus_switch_probability_deriv_nonneg`, `paper_remark4_switch_time_minus_switch_probability_deriv_pos`, `paper_remark4_switch_time_minus_switch_probability_strictMonoOn` | formalized | `MainTheorems.lean`, `EconCSLib/Foundations/Probability/CTMC.lean` | None; the switch/stay closed forms, transition-kernel initial condition, row sums, Kolmogorov forward equation, probability bounds, strict positivity for positive elapsed time, small-time derivative at zero, `q(u)/u -> lambda`, `q(u) < lambda*u`, strict decrease of `q(u)/u` on positive times, `lambda*t - q(t) > 0`, `lambda*t - q(t) >= 0`, and strict monotonicity of `lambda*t - q(t)` on positive times are proved under the paper's rate/time hypotheses. |
| Lemma 3, fraction of time in each state | `gn21StateCycleTime`, `gn21StateCycleTime_pos_of_mass_pos`, `gn21ExitWeightIntegral`, `gn21SubcycleLength`, `gn21SubcycleLength_eq_competing_clocks`, `gn21SubcycleLength_pos_of_pos`, `gn21CrossSubcycleProb`, `gn21CrossSubcycleProb_pos_of_primitives`, `gn21ExpectedStateTimeInRenewalCycle`, `gn21ExpectedStateTimeInRenewalCycle_pos_of_primitives`, `gn21TimeFractionFromCycles`, `gn21TimeFractionFormula`, `gn21MeasuredTimeFraction`, `gn21TimeFractionFromCycleMeans_eq_cycles`, `gn21ExpectedCycleTimeFraction_eq_measuredTimeFraction`, `GN21TimeFractionCycleLLNCertificate`, `paper_lemma3_stochastic_time_fraction_formula`, `GN21TimeFractionIIDCycleModel`, `paper_lemma3_stochastic_time_fraction_formula_of_iid_cycles`, `paper_lemma3_time_fraction_formula_algebra`, `paper_lemma3_measured_time_fraction_formula_algebra`, `paper_lemma3_measured_time_fractions_sum_to_one` | formalized | `MainTheorems.lean`, `EconCSLib/Foundations/Probability/RenewalReward.lean` | None; the displayed time-fraction algebra is proved after substituting the paper's measured `T_i(σ_i)` and `Q_i(σ_i)` set-integral definitions into the subcycle expression, the two measured state fractions are proved to sum to one when the denominator is nonzero, and the IID-cycle theorem proves the almost-sure sample time-fraction limit by mathlib's strong law. `GN21TimeFractionIIDCycleModel` encodes the paper's source primitive positivity, feasible-policy assumptions, IID cycle variables, and expected-geometric-subcycle mean identities; Lean derives all denominator and probability nonzero side conditions internally. |
| Lemma 4, single-state optimal interval form | `paper_lemma4_reward_cutoff_complete_threshold_measurable_optimal`, `paper_lemma4_rejected_strict_threshold_time_zero_of_measurable_optimal_reward`, `paper_lemma4_accepted_below_complete_threshold_time_zero_of_measurable_optimal_reward`, `paper_lemma4_single_state_threshold_time_zero_uniqueness_measurable`, `paper_lemma4_single_state_threshold_mass_zero_uniqueness_measurable` | formalized | `MainTheorems.lean` | Lean proves the source measurable Lemma 4 endpoint from Theorem 1: there exists a measurable optimal complete-threshold policy whose reward equals its cutoff, and every feasible measurable optimal policy differs from it only on zero-mass sets away from the threshold boundary. The older exact-agreement certificate wrappers remain available for stronger hypotheses, but the source mass-zero statement is closed. |
| Lemma 5, derivative-shape optimizer replacement | `Lemma5DerivativeShape`, `lemma5DerivativeShapeWitness`, `lemma5PolicyForm`, `policyAlmostEverywhereEq`, `lemma5PolicyFormAlmostEverywhere`, `lemma5PolicyFormAlmostEverywhere_of_policyForm`, `policyAlmostEverywhereEq_of_diff_null`, `GN21FiniteOpenBallApproximation`, `GN21FiniteOpenIntervalApproximation`, `GN21FiniteIntervalPolicy`, `GN21FiniteIntervalPolicy.policy`, `GN21FiniteIntervalPolicy.measurableSet_policy`, `GN21FiniteIntervalPolicy.policy_subset_acceptAll_of_intervals`, `GN21FiniteIntervalPolicy.complexity`, `GN21GeneralizedIntervalComponent`, `GN21GeneralizedIntervalPolicy`, `GN21GeneralizedIntervalPolicy.policy`, `GN21GeneralizedIntervalPolicy.measurableSet_policy`, `GN21GeneralizedIntervalPolicy.complexity`, `GN21FiniteIntervalPolicy.toGeneralizedIntervalPolicy`, `GN21FiniteIntervalPolicy.toGeneralizedIntervalPolicy_policy`, `exists_gn21GeneralizedIntervalPolicy_reward_close`, `exists_gn21GeneralizedIntervalPolicy_reward_close_below`, `lemma5OptimizerReplacementCertificate_of_generalizedIntervalPolicy_descent_and_maximizer`, `Lemma5GeneralizedIntervalPolicyDescentMaximizerData`, `Lemma5GeneralizedIntervalPolicyDescentMaximizerData.to_optimizer_replacement`, `Lemma5GeneralizedIntervalPolicyDescentMaximizerData.policyForm_of_optimal`, `Lemma5GeneralizedIntervalPolicyDescentMaximizerData.policyForm_of_candidate_le`, `exists_generalizedIntervalPolicy_eq_of_lemma5PolicyForm_of_subset_acceptAll`, `exists_gn21FiniteOpenBallApproximation_of_isOpen`, `GN21FiniteOpenBallApproximation.to_interval`, `exists_gn21FiniteOpenIntervalApproximation_of_isOpen`, `GN21FiniteOpenIntervalApproximation.measure_symmDiff_lt`, `GN21FiniteOpenIntervalApproximation.policy`, `GN21FiniteOpenIntervalApproximation.policy_subset`, `GN21FiniteOpenIntervalApproximation.toFiniteIntervalPolicy`, `GN21FiniteOpenIntervalApproximation.toFiniteIntervalPolicy_policy`, `GN21FiniteOpenIntervalApproximation.toFiniteIntervalPolicy_subset`, `GN21SymmDiffContinuousAt`, `exists_gn21FiniteOpenIntervalApproximation_reward_close`, `exists_gn21FiniteIntervalPolicy_reward_close`, `exists_gn21FiniteIntervalPolicy_reward_close_below`, `endpoint_path_le_of_hasDerivAt_nonneg_on_Icc`, `endpoint_path_lt_of_hasDerivAt_pos_on_Icc`, `endpoint_path_ge_of_hasDerivAt_nonpos_on_Icc`, `endpoint_path_gt_of_hasDerivAt_neg_on_Icc`, `lemma5_strictlyIncreasing_endpoint_sign_dichotomy`, `lemma5_strictlyDecreasing_gap_endpoint_sign_dichotomy`, `lemma5_strictQuasiConvex_middle_endpoint_signs_of_outer_nonpos`, `lemma5_strictQuasiConcave_gap_endpoint_sign_of_lower_nonneg`, `symmDiff_ioo_union_touching_subset_singleton`, `policyAlmostEverywhereEq_ioo_union_touching`, `lemma5_upper_endpoint_merge_reward_ge_of_endpoint_path`, `lemma5_upper_endpoint_merge_reward_gt_of_endpoint_path`, `lemma5_lower_endpoint_collapse_reward_ge_of_endpoint_path`, `lemma5_lower_endpoint_collapse_reward_gt_of_endpoint_path`, `GN21GeneralizedIntervalPolicy.singleBounded`, `GN21GeneralizedIntervalPolicy.twoBounded`, `GN21GeneralizedIntervalPolicy.empty`, `GN21GeneralizedIntervalPolicy.policy_singleBounded`, `GN21GeneralizedIntervalPolicy.policy_twoBounded`, `GN21GeneralizedIntervalPolicy.policy_empty`, `GN21GeneralizedIntervalPolicy.complexity_singleBounded`, `GN21GeneralizedIntervalPolicy.complexity_twoBounded`, `GN21GeneralizedIntervalPolicy.complexity_empty`, `lemma5_twoBounded_upper_merge_step_of_endpoint_path`, `lemma5_twoBounded_upper_merge_strict_step_of_endpoint_path`, `lemma5_singleBounded_lower_collapse_step_of_endpoint_path`, `lemma5_singleBounded_lower_collapse_strict_step_of_endpoint_path`, `lemma5PositiveResponsePolicy`, `lemma5PositiveResponsePolicy_subset_acceptAll`, `measurableSet_lemma5PositiveResponsePolicy`, `lemma5MarginalSetReward`, `ae_eq_set_of_policyAlmostEverywhereEq`, `measure_congr_policy_ae`, `lemma5MarginalSetReward_congr_policy_ae`, `singleStateTripMass_congr_policy_ae`, `singleStateTripTime_congr_policy_ae`, `singleStateTripPayment_congr_policy_ae`, `singleStateRenewalReward_congr_policy_ae`, `gn21ExitWeightIntegral_congr_policy_ae`, `gn21ScaledStateTime_congr_policy_ae`, `gn21ScaledStateEarning_congr_policy_ae`, `gn21MeasuredAggregateRewardPrimitives_congr_left_policy_ae`, `gn21MeasuredAggregateRewardPrimitives_congr_right_policy_ae`, `lemma5MarginalSetReward_le_positiveResponsePolicy`, `lemma5MarginalSetReward_lt_positiveResponsePolicy_of_omits_positive_mass`, `lemma5MarginalSetReward_lt_positiveResponsePolicy_of_accepts_negative_mass`, `lemma5_positiveResponse_omitted_mass_zero_of_candidate_le`, `lemma5_positiveResponse_negative_mass_zero_of_candidate_le`, `lemma5_positiveResponse_strict_masses_zero_of_candidate_le`, `acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le`, `acceptAllAlmostEverywhere_of_lemma5_positiveResponse_feasible_optimal`, `Theorem4MeasurablePositiveResponseAEMarginalCertificate`, `paper_theorem4_measurable_accept_all_ae_unique_optimal_of_positive_response_marginal_optima`, `lemma5MarginalOptimizerReplacementCertificate_positiveResponse`, `paper_lemma5_marginal_optimizer_replacement_of_positiveResponse`, `Lemma5PositiveResponseShapeData`, `Lemma5PositiveResponseShapeData.derivativeShapeWitness`, `Lemma5PositiveResponseShapeData.policyForm`, `Lemma5PositiveResponseShapeData.positive_zero_set_null`, `Lemma5PositiveResponseShapeData.policyAlmostEverywhereEq_positiveResponse_of_candidate_le`, `Lemma5PositiveResponseShapeData.policyFormAlmostEverywhere_of_candidate_le`, `Lemma5PositiveResponseShapeData.policyFormAlmostEverywhere_of_feasible_optimal`, `Lemma5FeasiblePolicyFormAlmostEverywhereData`, `paper_lemma5_fixed_response_policy_form_ae_of_response_shape`, `paper_lemma5_fixed_response_feasible_policy_form_ae_of_response_shape`, `GN21MeasuredPairNondegenerate.congr_left_policy_ae`, `GN21MeasuredPairNondegenerate.congr_right_policy_ae`, `gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement_congr_current_ae`, `gn21SurgeFeasibleStatewiseStrictAggregateImprovement_congr_current_ae`, `Lemma5PositiveResponseShapeData.marginalSetReward_lt_positiveResponsePolicy_of_not_policyFormAE`, `paper_lemma5_marginal_optimizer_replacement_ae_of_response_shape`, `theorem4NonsurgeShapeRepresentative_of_allowed_lemma5_formAE`, `theorem4SurgeShapeRepresentative_of_allowed_lemma5_formAE`, `paper_lemma5_marginal_optimizer_replacement_of_response_shape`, `lemma5PolicyForm_positiveResponse_positive`, `lemma5PolicyForm_positiveResponse_strictlyIncreasing_of_zero`, `lemma5PolicyForm_positiveResponse_strictlyDecreasing_of_zero`, `lemma5PolicyForm_strictlyQuasiConvex_of_boundary_zeros`, `lemma5PolicyForm_strictlyQuasiConcave_of_boundary_zeros`, `rejectLongTripsPolicy`, `rejectShortTripsPolicy`, `acceptMiddleTripsPolicy`, `rejectMiddleTripsPolicy`, `measurableSet_rejectLongTripsPolicy`, `measurableSet_rejectShortTripsPolicy`, `measurableSet_acceptMiddleTripsPolicy`, `measurableSet_rejectMiddleTripsPolicy`, `lemma5PolicyForm_strictlyIncreasing_rejectShortTripsPolicy`, `lemma5PolicyForm_strictlyDecreasing_rejectLongTripsPolicy`, `lemma5DerivativeShapeWitness_strictlyQuasiConvex_of_lemma7_affine_ctmc_response`, `lemma5DerivativeShapeWitness_strictlyQuasiConcave_of_lemma8_affine_ctmc_response`, `paper_lemma5_strictQuasiConvex_response_lt_of_between`, `paper_lemma5_strictQuasiConcave_response_lt_between`, `Lemma5OptimizerReplacementCertificate`, `exists_canonical_ge_of_finite_descent`, `exists_canonical_gt_of_finite_descent`, `exists_canonical_arbitrarily_close_of_seed_finite_descent`, `target_le_canonical_maximizer_of_arbitrarily_close`, `exists_canonical_ge_of_arbitrarily_close_and_maximizer`, `lemma5OptimizerReplacementCertificate_of_finite_descent`, `lemma5OptimizerReplacementCertificate_of_seed_finite_descent`, `lemma5OptimizerReplacementCertificate_of_domain_finite_descent_and_maximizer`, `lemma5OptimizerReplacementCertificate_of_finiteIntervalPolicy_descent_and_maximizer`, `Lemma5FiniteIntervalPolicyDescentMaximizerData`, `Lemma5FiniteIntervalPolicyDescentMaximizerData.to_optimizer_replacement`, `Lemma5FiniteIntervalPolicyDescentMaximizerData.policyForm_of_optimal`, `Lemma5FiniteIntervalPolicyDescentMaximizerData.policyForm_of_candidate_le`, `lemma5PositiveOptimizerReplacementCertificate_acceptAll`, `lemma5StrictlyIncreasingOptimizerReplacementCertificate_rejectShort`, `lemma5StrictlyDecreasingOptimizerReplacementCertificate_rejectLong`, `lemma5StrictlyQuasiConvexOptimizerReplacementCertificate_rejectMiddle`, `lemma5StrictlyQuasiConcaveOptimizerReplacementCertificate_acceptMiddle`, `paper_lemma5_optimizer_replacement_of_certificate`, `lemma5PolicyForm_of_optimizer_replacement_certificate_of_optimal`, `acceptsAllTrips_of_positive_optimizer_replacement_certificate_of_optimal` | partially formalized | `MainTheorems.lean`, `EconCSLib/Foundations/Math/QuasiConvex.lean` | The five derivative-shape cases and resulting policy forms are encoded, canonical measurable interval-policy representatives are provided, and Lean now proves the core sign-to-shape classification for the positive marginal-response policy: positive responses give accept-all, monotone responses with a zero crossing give short/long rejection, and quasi-convex/quasi-concave responses with two boundary zeros give middle rejection/acceptance. `Lemma5PositiveResponseShapeData` is the compiled five-case source table, `paper_lemma5_marginal_optimizer_replacement_of_response_shape` proves the exact-form fixed-response variational optimizer-replacement statement from it under mass-strictness hypotheses, and `paper_lemma5_marginal_optimizer_replacement_ae_of_response_shape` proves the source-faithful a.e.-strict fixed-response variational replacement without a separate strict-mass assumption. Lean now also proves the source-faithful a.e. fixed-response Lemma 5 theorem: under a nonatomic trip-length measure, feasible optimality for the marginal response reward forces the current policy to agree up to null symmetric difference with the canonical five-case policy form, the marginal reward, single-state renewal primitives, Lemma 3 `Q,T,W` primitives, and the Appendix-D aggregate reward primitive are invariant under null symmetric-difference policy changes, and the zero-response boundary set is null in each case. The strengthened feasible a.e. endpoint keeps the exact representative, feasibility, and measurability bundled, and Lean transfers feasible strict aggregate improvements proved on that representative back to the original current policy in either state. The a.e. form also has exact Theorem 4 non-surge/surge shape representatives via `theorem4NonsurgeShapeRepresentative_of_allowed_lemma5_formAE` and `theorem4SurgeShapeRepresentative_of_allowed_lemma5_formAE`, which is the bridge for endpoint arguments that need exact interval syntax while preserving measured rewards. Lean also proves global endpoint-path calculus for Lemma 5 Step 2: nonnegative, positive, nonpositive, or negative derivative on the full interval between two endpoint positions gives the corresponding weak or strict reward ordering between those endpoint policies.  The source Step 2 sign choices are also formalized for the monotone and quasi cases: strict monotonicity gives the upper-vs-lower endpoint dichotomies, strict quasi-convexity turns nonpositive outer responses into inward middle-interval moves, and strict quasi-concavity turns nonnegative lower responses into a gap-closing upper move.  The touching-interval collision step is proved a.e.: `(a,b) ∪ (b,c)` differs from `(a,c)` only at `{b}` under nonatomic trip-length measures.  Basic endpoint-path merge and collapse reward comparisons are now compiled in weak and strict forms, and the two-bounded-interval generalized-policy merge case is threaded to an explicit lower-complexity one-interval seed, and the one-bounded-interval collapse case is threaded to the explicit empty generalized seed. Lean also proves the inner regularity and interval-language part of Lemma 5 Step 1: every open trip-policy set under a finite regular measure has a finite open-interval subpolicy whose omitted mass is arbitrarily small, and the symmetric-difference error is the same omitted mass because the approximation is internal. The approximation is exposed through the concrete bounded `GN21FiniteIntervalPolicy` domain, then embedded into `GN21GeneralizedIntervalPolicy`, a finite interval/ray domain that also represents accept-all and unbounded positive tails. The generalized domain is measurable, has natural endpoint complexity, preserves bounded seeds, includes canonical representatives for all five Lemma 5 policy forms, and has reward-close seed theorems for the descent/maximizer bridge; Lean also proves every feasible policy already classified by Lemma 5 has an exactly equal representative in this generalized domain. The `GN21SymmDiffContinuousAt` bridge composes this with the source continuity assumption to choose a finite generalized interval/ray seed whose reward is arbitrarily close to the original open policy. Lean also proves the finite descent and limit/maximizer bridge used by the source proof: any finite-domain endpoint move that weakly improves reward while lowering a natural-valued complexity reaches a canonical policy, and arbitrary close finite seeds plus a canonical maximizer yield a true replacement certificate for the original policy. The generalized interval/ray specialization now consumes the corrected domain; the older bounded finite-interval specialization remains as the inner-approximation seed boundary. The named `Lemma5GeneralizedIntervalPolicyDescentMaximizerData` target packages the remaining source obligations and already yields both the optimizer-replacement certificate and the policy-form conclusion under unrestricted optimality or a restricted candidate comparison. The fixed-response variational comparison `lemma5MarginalSetReward_le_positiveResponsePolicy` proves that accepting exactly positive-response trips weakly dominates every measurable feasible policy; if a policy is not canonical modulo null sets, Lean proves strict improvement by deriving the positive-response candidate comparison would otherwise force the a.e. policy form. The strict-mass contrapositives still prove that candidate optimality forces both mass obstructions to vanish, and restricted feasible optimality now supplies that candidate comparison automatically, giving the positive-shape accept-all almost-everywhere conclusion without exact set equality. The positive-response marginal route is also packaged as a Theorem 4 measurable AE endpoint for optima in both states. The older exact fixed-response weak/strict results remain packaged as a compiled optimizer-replacement certificate for the positive-response policy. Lemmas 7-8 feed explicit derivative-shape witnesses, all five canonical shape cases have direct optimizer-replacement constructors, and optimality-extraction lemmas convert strict replacement certificates back into policy forms. The remaining conditional step is the paper-specific endpoint-step certificate for each derivative-shape case: instantiate the endpoint path between a noncanonical generalized interval/ray policy and the next collision or canonical boundary, use the global derivative-sign calculus to prove reward improvement, and show that the resulting endpoint move lowers finite complexity. |
| Lemma 6, derivative formula for dynamic reward | `gn21DerivativeSignKernel`, `gn21Lemma6Response`, `gn21AggregateDynamicReward`, `paper_lemma6_aggregate_reward_hasDerivAt`, `paper_lemma6_derivative_formula_of_aggregate_paths`, `paper_lemma6_derivative_formula_of_interval_density_paths`, `paper_lemma6_upper_endpoint_interval_density_response_formula`, `paper_lemma6_lower_derivative_formula_of_interval_density_paths`, `paper_lemma6_tail_derivative_formula_of_interval_density_paths`, `paper_lemma6_reject_middle_lo_derivative_formula_of_interval_density_paths`, `paper_lemma6_reject_middle_hi_derivative_formula_of_interval_density_paths`, `paper_lemma6_derivative_kernel_same_sign_response`, `paper_lemma6_derivative_value_same_sign_response_of_certificate`, `paper_lemma6_derivative_value_pos_of_response_pos_of_certificate`, `paper_lemma6_derivative_value_neg_of_response_neg_of_certificate` | formalized | `MainTheorems.lean` | None for the Lemma 6 derivative formula itself; Lean proves the aggregate reward quotient derivative, the polynomial kernel algebra, and the paper's normalized response sign statement for density-based upper endpoints, with lower, tail, and middle-rejection endpoint variants available for later shape arguments. The remaining arbitrary-open-policy endpoint selection belongs to Lemma 5/Theorem 4, not Lemma 6. |
| Lemmas 7-8, affine pricing quasi-convex/concave response | `strictQuasiConvexOnPositive`, `strictQuasiConcaveOnPositive`, `paper_lemma7_8_affine_response_canonical_form`, `gn21Lemma7CanonicalResponse`, `gn21Lemma7CanonicalDerivativeNumerator`, `paper_lemma7_canonical_response_hasDerivAt`, `paper_lemma7_canonical_derivative_numerator_hasDerivAt`, `paper_lemma7_canonical_derivative_numerator_deriv_pos`, `paper_lemma7_canonical_ctmc_response_quasi_convex`, `paper_lemma8_canonical_ctmc_response_quasi_concave`, `paper_lemma7_affine_ctmc_response_eq_canonical`, `paper_lemma8_affine_ctmc_response_eq_canonical`, `paper_lemma7_affine_ctmc_response_quasi_convex`, `paper_lemma8_affine_ctmc_response_quasi_concave`, `paper_lemma7_affine_positive_additive_response_strict_quasi_convex`, `paper_lemma8_affine_negative_additive_response_strict_quasi_concave`, `Lemma7QuasiConvexCertificate`, `paper_lemma7_affine_ctmc_quasi_convex_certificate`, `paper_lemma7_affine_positive_additive_quasi_convex_of_certificate`, `Lemma8QuasiConcaveCertificate`, `paper_lemma8_affine_ctmc_quasi_concave_certificate`, `paper_lemma8_affine_negative_additive_quasi_concave_of_certificate` | formalized | `MainTheorems.lean`, `EconCSLib/Foundations/Math/QuasiConvex.lean` | None; the affine response algebra is reduced to the source canonical form, the source-series derivative-numerator calculation for Lemma 7 is proved directly from the CTMC closed form, the canonical CTMC response-shape cases are closed under the paper's sign assumptions, and the new source-facing wrappers state exactly the Lemma 7/8 affine-additive sign cases in terms of the paper's `Delta_ji = R_j - R_i` sign. The downstream use of these shapes in Lemma 5/Theorem 4 is tracked in those rows, not as a Lemma 7/8 gap. |
| Lemmas 9-10, IC derivative conditions | `paper_lemma9_surge_derivative_positive_of_acceptAll_bounds`, `paper_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds`, `paper_lemma9_derivative_value_pos_of_current_bounds_certificate`, `paper_lemma10_derivative_value_pos_of_current_bounds_certificate`, `paper_lemma9_structured_bounds_feasible_positive_of_positive_primitives`, `paper_lemma10_structured_bounds_feasible_of_positive_pieces`, `lemma9StructuredBounds_of_acceptAll_tightening`, `lemma10StructuredBounds_of_acceptAll_tightening`, `lemma9SurgeDerivativeCertificate_of_current_bounds`, `lemma10NonsurgeDerivativeCertificate_of_current_bounds`, `lemma5DerivativeShapeWitness_positive_of_lemma9_current_bounds`, `lemma5DerivativeShapeWitness_positive_of_lemma10_current_bounds`, `gn21MeasuredAggregateRewardPrimitives_lt_acceptAll_left_of_lemma10_current_bounds`, `gn21MeasuredAggregateRewardPrimitives_lt_acceptAll_right_of_lemma9_current_bounds`, `GN21NonsurgeLemma10AcceptAllAggregateSourceData.aggregate_lt_acceptAll`, `GN21SurgeLemma9AcceptAllAggregateSourceData.aggregate_lt_acceptAll` | formalized | `MainTheorems.lean` | None for the Lemma 9/10 derivative-sign and ratio-feasibility statements: Lean proves the structured ratio intervals are feasible and that source accept-all bounds, after the formal tightening step to current `Q,T` primitives, imply positive upper-endpoint reward derivatives through the Lemma 6 derivative-value bridge. The current-bound layer now also gives strict accept-all aggregate reward improvements in the surge and non-surge states whenever the rejected complement has positive measure of nonzero Lemma 6 derivative kernel, with full-data, primitive-data, and source-data wrappers. The remaining arbitrary-open-policy endpoint-selection work belongs to Lemma 5/Theorem 4, not to Lemmas 9-10. |
| Theorem 4, appendix structural theorem subsuming Theorem 2 | `theorem4NonsurgeShape`, `theorem4SurgeShape`, `theorem4NonsurgeShape_cases_of_not_acceptsAll`, `theorem4SurgeShape_cases_of_not_acceptsAll`, `theorem4NonsurgeAllowedLemma5Shape`, `theorem4SurgeAllowedLemma5Shape`, `theorem4NonsurgeAllowedLemma5Shape_strictlyDecreasing`, `theorem4SurgeAllowedLemma5Shape_strictlyQuasiConvex`, `theorem4NonsurgeShape_of_lemma5_positive`, `theorem4NonsurgeShape_of_lemma5_strictlyDecreasing`, `theorem4NonsurgeShape_of_lemma5_strictlyQuasiConcave`, `theorem4SurgeShape_of_lemma5_positive`, `theorem4SurgeShape_of_lemma5_strictlyIncreasing`, `theorem4SurgeShape_of_lemma5_strictlyQuasiConvex`, `theorem4NonsurgeShape_rejectLongTripsPolicy`, `theorem4SurgeShape_rejectMiddleTripsPolicy`, `theorem4NonsurgeShape_of_allowed_lemma5_form`, `theorem4SurgeShape_of_allowed_lemma5_form`, `theorem4NonsurgeAllowedReplacement_positive_acceptAll`, `theorem4NonsurgeAllowedReplacement_rejectLong`, `theorem4NonsurgeAllowedReplacement_acceptMiddle`, `theorem4SurgeAllowedReplacement_positive_acceptAll`, `theorem4SurgeAllowedReplacement_rejectShort`, `theorem4SurgeAllowedReplacement_rejectMiddle`, `Theorem4NonsurgeAllowedReplacementData`, `Theorem4SurgeAllowedReplacementData`, `Theorem4AllOptimalShapeReplacementDerivationCertificate.of_allowed_replacement_data`, `Theorem4ShapeDerivationCertificate`, `theorem4StructuralPolicyCertificate_of_shape_derivation`, `paper_theorem4_dynamic_structural_policy_of_shape_derivation`, `Theorem4AllOptimalShapeReplacementDerivationCertificate`, `theorem4ShapeReplacementDerivationCertificate_of_all_shape_replacements`, `theorem4ShapeDerivationCertificate_of_all_shape_replacements`, `paper_theorem4_dynamic_structural_policy_of_all_shape_replacements`, `Theorem4AllowedReplacementStatewiseImprovementCertificate`, `Theorem4ShapeDerivationStatewiseImprovementCertificate.of_allowed_replacement_data`, `paper_theorem4_accept_all_unique_optimal_of_allowed_replacement_data`, `Theorem4AcceptAllDerivationCertificate`, `theorem4ShapeDerivationCertificate_of_accept_all_derivation`, `paper_theorem4_accept_all_unique_optimal_of_positive_lemma5_forms`, `paper_theorem4_dynamic_structural_policy_of_accept_all_derivation`, `Theorem4PositiveReplacementDerivationCertificate`, `theorem4AcceptAllDerivationCertificate_of_positive_replacement`, `paper_theorem4_accept_all_unique_optimal_of_positive_replacement`, `Theorem4StatewiseAcceptAllRewardCertificate`, `theorem4PositiveReplacementDerivationCertificate_of_statewise_accept_all_reward`, `paper_theorem4_accept_all_unique_optimal_of_statewise_accept_all_reward`, `Theorem4GlobalStatewiseAcceptAllRewardCertificate`, `theorem4StatewiseAcceptAllRewardCertificate_of_global_statewise_accept_all_reward`, `paper_theorem4_accept_all_unique_optimal_of_global_statewise_accept_all_reward`, `Theorem4StrictLocalImprovementCertificate`, `acceptAllDynamic_unique_optimal_of_strict_local_improvements`, `paper_theorem4_accept_all_unique_optimal_of_strict_local_improvements`, `Theorem4MeasurableStrictLocalImprovementCertificate`, `acceptAllDynamic_measurable_unique_optimal_of_strict_local_improvements`, `theorem4GlobalStatewiseAcceptAllRewardCertificate_of_measured_reward_improvements`, `Theorem4MeasuredAggregateAcceptAllRewardCertificate`, `theorem4GlobalStatewiseAcceptAllRewardCertificate_of_measured_aggregate_improvements`, `Theorem4MeasuredAggregateStrictLocalImprovementCertificate`, `theorem4StrictLocalImprovementCertificate_of_measured_aggregate_strict_improvements`, `paper_theorem4_accept_all_unique_optimal_of_measured_aggregate_strict_local_improvements`, `Theorem4MeasuredAggregateFeasibleStrictLocalImprovementCertificate`, `theorem4MeasurableStrictLocalImprovementCertificate_of_measured_aggregate_feasible_strict_improvements`, `paper_theorem4_measurable_accept_all_unique_optimal_of_measured_aggregate_feasible_strict_local_improvements`, `replaceDynamicPolicyState`, `gn21MeasuredAggregateDynamicStateReward`, `gn21MeasuredAggregateDynamicStateReward_zero`, `gn21MeasuredAggregateDynamicStateReward_one`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_interval_density`, `paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_interval_density`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_lower_interval_density`, `paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_lower_interval_density`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_tail_interval_density`, `paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_reject_long_withDensity`, `paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_accept_middle_withDensity`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_tail_withDensity`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_interval_density`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_interval_density`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity`, `paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity`, `paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_tail_interval_density`, `GN21SurgeIntervalEndpointBridgeData`, `GN21NonsurgeIntervalEndpointBridgeData`, `GN21SurgeEndpointBridgeData`, `GN21NonsurgeEndpointBridgeData`, `Theorem4Lemma910IntervalBridgeCertificate`, `Theorem4Lemma910EndpointBridgeCertificate`, `Theorem4ShapeDerivationEndpointBridgeCertificate`, `Theorem4ShapeDerivationStatewiseImprovementCertificate`, `Theorem4ShapeDerivationStatewiseImprovementCertificate.of_all_shape_replacements`, `Theorem4ShapeEndpointSelectionCertificate`, `Theorem4ShapeEndpointSelectionCertificate.of_shape_derivation`, `Theorem4ShapeEndpointSelectionCertificate.of_shape_derivation_endpoint_bridges`, `Theorem4ShapeDerivationEndpointBridgeCertificate.of_statewise_improvements`, `Theorem4ShapeDerivationEndpointBridgeCertificate.of_statewise_improvement_certificate`, `Theorem4Lemma910EndpointBridgeCertificate.of_shape_endpoint_selection`, `theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate_of_lemma910_interval_bridges`, `theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_lemma910_interval_bridges`, `theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate_of_lemma910_endpoint_bridges`, `theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_lemma910_endpoint_bridges`, `theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate_of_shape_endpoint_selection`, `theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_shape_endpoint_selection`, `paper_theorem4_accept_all_unique_optimal_of_shape_endpoint_selection`, `paper_theorem4_accept_all_unique_optimal_of_shape_derivation_endpoint_bridges`, `paper_theorem4_accept_all_unique_optimal_of_shape_derivation_endpoint_bridge_certificate`, `paper_theorem4_accept_all_unique_optimal_of_shape_derivation_statewise_improvements`, `paper_theorem4_accept_all_unique_optimal_of_shape_derivation_statewise_improvement_certificate`, `paper_theorem4_accept_all_unique_optimal_of_all_shape_replacements_statewise_improvements`, `Theorem4MeasuredAggregateStatewiseStrictLocalImprovementCertificate`, `theorem4MeasuredAggregateStrictLocalImprovementCertificate_of_statewise_strict_improvements`, `Theorem4StructuralPolicyCertificate`, `paper_theorem4_dynamic_structural_policy_of_certificate` | conditional | `MainTheorems.lean` | The source endpoint is exposed from an explicit structural policy certificate, the pure logic routing from Lemma 5 policy forms to Theorem 4 surge/non-surge shape alternatives is closed, canonical interval policies have direct Theorem 4 shape facts, non-accept-all structural shapes now split into the four endpoint-selection cases used by the source proof, feasible reject-long/reject-short/accept-middle/reject-middle shapes canonicalize to measured endpoint primitives, state-specific allowed-replacement constructors package the canonical Lemma 5 replacement policies into the dependent Theorem 4 shape data, source-facing non-surge/surge replacement data types feed the all-optimal replacement certificate, and a packaged allowed-replacement statewise-improvement certificate combines replacement data, feasibility, and the four endpoint-improvement cases. There is a closer Lemma 5-style shape-derivation certificate that mechanically assembles Theorem 4, constructs the four-case endpoint-selection certificate from feasibility and the four endpoint bridges, and directly produces accept-all unique optimality from raw arguments, the packaged endpoint-bridge certificate, or the source-facing statewise-improvement certificate. All-optimal Lemma 5 replacement data now choose a structural optimum internally and feed the same Theorem 4 routes, so the source proof no longer needs a separate preselected optimum/replacement package. The positive-form special case gives accept-all unique optimality, statewise positive Lemma 5 replacement certificates feed that accept-all derivation through local continuation optimality, statewise accept-all reward comparisons instantiate the replacement interface, global statewise accept-all reward improvements derive accept-all optimality internally, and strict local improvements now also rule out every optimal non-accept-all policy. The feasible-measurable strict-local route restricts both optimality and local replacements to the source policy domain while still deriving accept-all measurable IC. The measured-reward and measured aggregate constructors let Lemma 6-style `Q,T,W` comparisons feed either the global comparison route or the stricter local-improvement route; the uniform statewise aggregate wrapper with state-specific unfolding lemmas removes duplicate state bookkeeping, Lemma 9/10 upper-endpoint, finite lower-endpoint, unbounded-tail, and two-sided middle-rejection endpoint movements now feed the surge and non-surge statewise strict aggregate improvement interfaces under primitive-identification assumptions, with concrete with-density replacement-policy specializations and finite positive-density current/replacement nondegeneracy constructors for all four Theorem 4 shape cases: non-surge reject-long and accept-middle, and surge reject-short and reject-middle. The generalized endpoint bridge plus shape-endpoint-selection certificates package those sides into the measured strict-local interface consumed by Theorem 3 and now directly produce the measured strict-local certificate and accept-all uniqueness endpoint for Theorem 4. The feasible accept-all-bound wrappers for all four shape cases now preserve the measurable feasible-policy domain, and the all-measurable replacement constructor feeds Lemma 5 replacement data into the same statewise-improvement certificate. The interval-density primitives and positive replacements are now realized by actual upper/lower endpoint, tail, and reject-middle policies under `volume.withDensity`; it remains to discharge arbitrary-optimal-policy endpoint selection for the continuous model. |
| Theorem 2, multiplicative pricing not IC and optimal policy shapes | `MultiplicativeNotICCertificate`, `paper_theorem2_multiplicative_not_ic_of_witness`, `MultiplicativePolicyShapeCertificate`, `paper_theorem2_multiplicative_policy_shape_of_certificate` | conditional | `MainTheorems.lean` | The endpoint wrappers are closed from explicit profitable-deviation and policy-shape certificates; constructing those certificates from the continuous model remains open. |
| Theorem 3, structured IC pricing | `structuredSurgePrice`, `ctmcStructuredSurgePrice`, `ctmcDynamicSwitchProb`, `ctmcStructuredDynamicSurgePrice`, `ctmcStructuredDynamicSurgePrice_price_form`, `paper_theorem3_structured_price_uses_lemma2_switch_probability`, `paper_theorem3_structured_price_closed_form`, `theorem3FeasibilityThresholdC`, `paper_theorem3_feasibility_numerator_pos_of_positive_pieces`, `paper_theorem3_feasibility_denominator_pos_of_positive_pieces`, `paper_theorem3_scaled_denominator_pos_of_positive_pieces`, `paper_theorem3_feasibility_numerator_le_scaled_den_of_nonneg_pieces`, `paper_theorem3_feasibility_thresholdC_mem_Ico`, `paper_theorem3_feasibility_thresholdC_mem_Ico_of_positive_pieces`, `paper_theorem3_feasibility_thresholdC_mem_Ico_acceptAll_of_measured_primitives_closed`, `theorem3NonsurgeZRatio`, `theorem3NonsurgeZRatio_accounting`, `lemma10StructuredBounds_of_theorem3_ratio`, `lemma10StructuredBounds_acceptAll_of_theorem3_ratio_measured`, `theorem3NonsurgeParameters_of_theorem3_ratio`, `theorem3SurgeMultiplierFromRatio`, `theorem3SurgeZFromRatio`, `theorem3SurgeRatio_accounting`, `theorem3SurgeRatio_denominator_pos`, `theorem3SurgeMultiplierFromRatio_gt_R1`, `theorem3SurgeZFromRatio_pos`, `paper_lemma9_structured_bounds_feasible_positive_of_positive_primitives`, `theorem3SurgeParameters_exist_of_lemma9_final_signs`, `theorem3SurgeParameters_exist_of_lemma9_positive_primitives`, `theorem3StructuredParameters_exist_of_ratio_and_lemma9_final_signs`, `theorem3StructuredParameters_exist_of_ratio_and_lemma9_positive_primitives`, `theorem3_acceptAll_measured_primitives_scalar_conditions`, `theorem3_acceptAll_measured_primitives_scalar_conditions_positive_primitives`, `StructuredPricingICCertificate`, `structuredPricingICCertificate_of_ctmc_structured_prices`, `paper_theorem3_structured_prices_ic_of_certificate`, `paper_theorem3_ctmc_structured_prices_ic_of_accept_all_unique_optimal`, `paper_theorem3_ctmc_structured_prices_ic_of_statewise_accept_all_optima`, `paper_theorem3_ctmc_structured_prices_ic_of_theorem4_accept_all_derivation`, `paper_theorem3_ctmc_structured_prices_ic_of_positive_replacement_derivation`, `paper_theorem3_ctmc_structured_prices_ic_of_strict_local_improvements`, `paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_positive_replacement`, `paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_strict_local_improvements`, `paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_statewise_accept_all_reward`, `paper_theorem3_ctmc_structured_prices_exist_and_ic_of_ratio_and_global_statewise_accept_all_reward`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_global_statewise_accept_all_reward`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_accept_all_reward`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_strict_local_improvements`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_measured_aggregate_strict_local_improvements_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_lemma910_interval_bridges`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_lemma910_endpoint_bridges`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_endpoint_selection`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_endpoint_bridge_certificate`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_statewise_improvement_certificate`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_statewise_improvement_certificate_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_replacement_statewise_improvements_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_all_shape_replacements_statewise_improvements_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_allowed_replacement_data_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_global_statewise_accept_all_reward`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_measured_aggregate_strict_local_improvements`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_measured_aggregate_strict_local_improvements_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_shape_derivation_statewise_improvement_certificate`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_shape_derivation_statewise_improvement_certificate_of_lemma9_positive_primitives`, `paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_allowed_replacement_data_of_lemma9_positive_primitives` | conditional | `MainTheorems.lean` | The paper price form is tied directly to the Lemma 2 CTMC switch probability and expanded closed form; there is a concrete two-state CTMC dynamic price family; the source `C` threshold has compiled positivity-piece, measured accept-all `[0,1)`, and numerator-bound factorization bridges; the non-surge `C < R1/R2 < 1` to Lemma 10 bounds step is formalized; Lemma 9 surge-ratio feasibility now has a direct primitive-positivity bridge, so the strict-local and packaged statewise measured endpoints can avoid the stronger final-sign assumptions; both surge and non-surge `m_i,z_i` accounting packages are exposed and assembled into two-state parameter arrays with source sign constraints and target scaled-earning identities; and the accept-all IC endpoint can be invoked from unique optimality, statewise accept-all optimality, positive-form Theorem 4 accept-all derivation, statewise positive Lemma 5 replacement derivation, strict local improvement certificates, statewise accept-all reward comparison, global statewise accept-all reward improvements, measured aggregate accept-all improvements, the combined Lemma 9/10 interval bridge certificate, the generalized endpoint bridge certificate, the four-case Theorem 4 shape-endpoint-selection certificate, the paper-ordered shape-derivation endpoint-bridge/statewise-improvement certificates, Lemma 5 shape-replacement data, all-optimal Lemma 5 shape-replacement data, or packaged allowed-replacement source-boundary data. There is now a measured endpoint that constructs `m,z` first and concludes IC for `gn21MeasuredCTMCStructuredDynamicReward` once the measured global reward-improvement proof, the measured aggregate `Q,T,W` improvement proof, the measured aggregate strict-local improvement proof, the combined interval bridge certificate, generalized endpoint bridge certificate, four-shape endpoint-selection certificate, shape-derivation endpoint-bridge/statewise-improvement certificate, shape-replacement statewise-improvement package, all-optimal shape-replacement statewise-improvement package, or allowed-replacement source-boundary package is supplied for those constructed prices; accept-all-primitive endpoints specialize `T_i,Q_i` and share scalar-conditions helpers that derive the needed positivity and direct Lemma 9 feasibility facts from measure/CTMC assumptions for the global, strict-local, packaged statewise-certificate, and packaged allowed-replacement routes. Still needs the continuous proof selecting the realized endpoint policies from arbitrary optimal policies under the Lemma 9-10 derivative signs. |
| Auxiliary finite dynamic policy support | `paper_aux_finite_dynamic_pricing_ic_of_greedy`, `paper_aux_finite_dynamic_pricing_not_ic_of_profitable_deviation` | formalized | `MainTheorems.lean` | None; these are library-level finite MDP support lemmas, not source theorem substitutes. |

The Lemma 5 generalized interval/ray route now also exposes
`GN21GeneralizedIntervalPolicy.lemma5ShapeComplexity` and
`lemma5OptimizerReplacementCertificate_of_generalizedIntervalPolicy_canonical_dominance_and_maximizer`,
with source data packaged as
`Lemma5GeneralizedIntervalPolicyCanonicalDominanceMaximizerData`.  The
endpoint-facing wrapper
`lemma5OptimizerReplacementCertificate_of_generalizedIntervalPolicy_policy_canonical_dominance_and_maximizer`
lets the paper proof supply ordinary feasible canonical `TripPolicy`
replacements; Lean converts those policies to equal generalized interval/ray
representatives.  This route lets the endpoint proof supply a weakly improving
canonical representative directly, while Lean handles the finite-descent
decrease through the shape-specific complexity rather than raw component count.
For Lemma 5 Step 2, the endpoint reductions now work inside an arbitrary fixed
generalized-policy context: bounded-bounded upper/lower merges,
bounded-interval upper/lower collapses, bounded-to-right-ray merge,
left-ray-to-bounded merge, and left/right-ray-to-accept-all merge are all
compiled in weak and strict forms.  An ordered generalized interval/ray list
domain now converts to the existing generalized finite-policy domain and
proves that the first one or two source-ordered components are exactly the
compiled context seeds.  The first ordered-list bounded-bounded merge and
bounded-interval collapse reductions now return shorter ordered lists directly,
and the ordered boundary merges now reach the canonical right-tail, left-tail,
and accept-all families.  The second-component lower-collapse reduction now
removes a middle bounded component while preserving a leading component and
tail, and the symmetric second-component upper-collapse is also compiled.  The
second/third bounded-component upper/lower merges and the second-component
bounded-to-right-ray merge are compiled in weak and strict forms, so ordered
descent can now reduce adjacent middle components after one leading component
has been peeled off.
The quasi-convex three-interval and quasi-concave two-interval source case
splits are now formalized as endpoint-sign trichotomies, matching the paper's
Subcases 1A/1B/1C before the selected move is threaded to an endpoint path.
The ordered source-boundary moves for quasi-convex Subcases 1B/1C are now
covered too: a positive-left-ray component can expand into a following bounded
component, and a bounded component can merge with a following right ray by
moving the right ray's lower endpoint left, including the one-leading-component
right-tail form.
The remaining open part is the stopping argument behind the source's repeated
subcase switches: a current endpoint sign must be converted, using continuity,
into movement until either collision or first sign-change, and those partial
moves must then be iterated until component count falls.
The stopping compactness and stopped reward-move layer is now compiled:
`continuousOn_endpoint_positive_or_first_zero`,
`continuousOn_endpoint_negative_or_first_zero`, and
`continuousOn_endpoint_negative_or_last_zero` choose the first/last sign-change
boundary with sign persistence on the relevant prefix/suffix; the corresponding
endpoint-path lemmas turn those sign intervals into strict reward improvement.
At the Lemma 5 policy level, upper/lower merge and lower/upper collapse moves
now have stopped variants that either reach the collision/deletion boundary or
stop at the sign-change boundary, with strict reward improvement in both
branches.  The stopped layer is now threaded through the four source sign
selectors: the strictly increasing interval, strictly decreasing adjacent-gap,
strictly quasi-convex three-interval, and strictly quasi-concave two-interval
cases each have a compiled
`..._of_stopped_endpoint_paths_with_context` theorem producing an existential
strict local improvement from concrete stopped endpoint paths.  The same four
selectors also have
`..._of_local_endpoint_paths_with_context` variants that require only
one-sided endpoint derivative data and produce a small feasible strict
improvement.  Lean also has
the well-founded replacement constructor
`lemma5OptimizerReplacementCertificate_of_domain_wellFounded_descent_and_maximizer`
and the generalized-policy source data
`Lemma5GeneralizedIntervalPolicyWellFoundedDescentMaximizerData`, so the
remaining iteration no longer has to force every stopped move to lower raw
component count immediately.  The remaining open part is to instantiate the
endpoint-path derivative identities for arbitrary feasible optimal policies and
then either define the paper-specific well-founded progress relation or use the
strict-local route to rule out every noncanonical optimal configuration.
For optimality arguments there is also a shorter strict-local route now
compiled for all nonpositive derivative-shape cases:
`lemma5_strictlyIncreasing_interval_exists_strict_improvement_of_endpoint_moves`,
`lemma5_strictlyDecreasing_gap_exists_strict_improvement_of_endpoint_moves`,
`lemma5_strictQuasiConvex_three_interval_exists_strict_improvement_of_endpoint_moves`
and
`lemma5_strictQuasiConcave_two_interval_exists_strict_improvement_of_endpoint_moves`
combine the source sign dichotomies/trichotomies with stopped endpoint-move
improvement premises to rule out noncanonical interval configurations directly.
Their local endpoint-derivative instantiations are the preferred next
interface for Theorem 4-style optimal-policy exclusion, because a signed
endpoint branch already produces some strictly better nearby policy without
separately proving the full finite path to a canonical Lemma 5 form or a
global stopped path.
The local route now also has source-domain variants that keep the replacement
policy feasible and measurable:
`lemma5_strictlyIncreasing_interval_exists_strict_feasible_measurable_improvement_of_local_endpoint_paths_with_context`,
`lemma5_strictlyDecreasing_gap_exists_strict_feasible_measurable_improvement_of_local_endpoint_paths_with_context`,
`lemma5_strictQuasiConvex_three_interval_exists_strict_feasible_measurable_improvement_of_local_endpoint_paths_with_context`,
and
`lemma5_strictQuasiConcave_two_interval_exists_strict_feasible_measurable_improvement_of_local_endpoint_paths_with_context`.
They are supported by reusable interval-union feasibility/measurability lemmas
and the four feasible-measurable local endpoint primitives, then feed the
compiled optimality bridges
`not_singleStateMeasurableOptimal_of_exists_strict_feasible_improvement` and
`not_dynamicMeasurableOptimal_of_state_exists_strict_feasible_trip_policy_improvement`.
The direct nonoptimality wrappers
`lemma5_strictlyIncreasing_interval_not_singleStateMeasurableOptimal_of_local_endpoint_paths_with_context`,
`lemma5_strictlyDecreasing_gap_not_singleStateMeasurableOptimal_of_local_endpoint_paths_with_context`,
`lemma5_strictQuasiConvex_three_interval_not_singleStateMeasurableOptimal_of_local_endpoint_paths_with_context`,
and
`lemma5_strictQuasiConcave_two_interval_not_singleStateMeasurableOptimal_of_local_endpoint_paths_with_context`
now instantiate those selectors against measurable one-state optimality, and
`not_dynamicMeasurableOptimal_of_state_eq_exists_strict_feasible_trip_policy_improvement`
is the matching dynamic bridge when the current state policy has first been
identified with the concrete endpoint-union policy.
The stronger policy-level constructor
`lemma5OptimizerReplacementCertificate_of_policy_canonical_dominance_and_maximizer`
returns the ordinary canonical source policy as the replacement and exposes its
feasibility/measurability through
`Lemma5PolicyCanonicalDominanceMaximizerData`.  The Theorem 4 bridge
`Theorem4AllMeasurablePolicyCanonicalDominanceData.to_allowed_policy_forms`
now converts per-state policy-level Lemma 5 dominance data into the measurable
all-optimal allowed-policy-form certificate used by the endpoint-selection
wrappers.  When a route needs the concrete allowed replacement cases,
`Theorem4NonsurgeAllowedReplacementData.of_optimizer_replacement_subset`,
`Theorem4SurgeAllowedReplacementData.of_optimizer_replacement_subset`,
`Theorem4NonsurgeAllowedReplacementData.of_policy_canonical_dominance`,
`Theorem4SurgeAllowedReplacementData.of_policy_canonical_dominance`, and
`Theorem4AllMeasurablePolicyCanonicalDominanceData.to_allowed_replacement_data`
recover them noncomputably from the policy-form proofs.  The positive-response
marginal route also has
`Theorem4NonsurgeAllowedReplacementData.of_positiveResponse_marginal` and
`Theorem4SurgeAllowedReplacementData.of_positiveResponse_marginal`, which feed
response-shape/mass-strictness Lemma 5 data into the same replacement
interface.  The regular endpoint package
`Theorem4MeasurableEndpointCurrentBoundsRegularPolicyCanonicalDominanceCertificate`
and theorem
`paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_policy_canonical_dominance`
feed that classification directly into the current-bounds regular Theorem 4
route, and `.to_regular_selection` feeds older concrete-replacement
endpoint-selection routes.  The top-level Theorem 3 wrappers
`paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_policy_canonical_dominance_source_assumptions`
and
`paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_current_bounds_regular_policy_canonical_dominance_source_assumptions`
now expose the same route at the structured-price source boundary; use
`Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularPolicyCanonicalDominanceSourceAssumptions.to_regular_source_assumptions`
to feed the older regular selection boundary.
The source-feasible version is now compiled too:
`Lemma5FeasiblePolicyCanonicalDominanceMaximizerData`,
`Theorem4NonsurgeAllowedReplacementData.of_feasible_policy_canonical_dominance`,
`Theorem4SurgeAllowedReplacementData.of_feasible_policy_canonical_dominance`,
`Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData.to_allowed_policy_forms`,
`Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData.to_allowed_replacement_data`,
`Theorem4MeasurableEndpointCurrentBoundsRegularFeasiblePolicyCanonicalDominanceCertificate`,
`paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_regular_feasible_policy_canonical_dominance`,
`Theorem3AcceptAllMeasurableEndpointCurrentBoundsRegularFeasiblePolicyCanonicalDominanceSourceAssumptions`,
and the paired Theorem 3 IC/AE wrappers.  Prefer this route for final Lemma 5
closeout when the endpoint descent only compares interval/ray seeds contained
in the feasible positive-trip domain.

The measured GN21 reward now has a direct source-faithful bridge from dynamic
local optimality to the fixed-response Lemma 5 marginal objective:
`lemma5MarginalSetReward_optimal_of_gn21MeasuredDynamicRewardFunctional_zero`
and
`lemma5MarginalSetReward_optimal_of_gn21MeasuredDynamicRewardFunctional_one`.
These use the compiled aggregate quotient cross-multiplication lemmas and the
left/right score identities
`gn21MeasuredLeftLinearScore_eq_const_add_marginalSetReward` and
`gn21MeasuredRightLinearScore_eq_const_add_marginalSetReward`, so the remaining
Lemma 5 closeout can target response shape/measurability/integrability and the
standard nondegeneracy/denominator positivity inputs rather than assuming the
dynamic reward is a positive affine transform of the marginal integral.
There is also a weaker fixed-response endpoint,
`paper_lemma5_fixed_response_feasible_policy_form_ae_of_positive_response_policy_form`,
for scaled responses where the positive set has the desired Lemma 5 policy
form and the positive zero set is null, but proving the stronger analytic
`Lemma5PositiveResponseShapeData` for the scaled function would duplicate work.
`Lemma5PositiveResponsePolicyFormData.of_positive_scaling` transfers this
package through positive pointwise scalings on positive trip lengths.
The measured quotient response is now tied to that scaled-response route:
`gn21LeftLinearResponse_eq_scaled_lemma6Response` proves the scalar identity,
`gn21LeftLinearResponse_lemma6_scale_pos` proves the multiplier is positive,
and
`gn21MeasuredLeftMarginalResponse_eq_scaled_lemma6Response` /
`gn21MeasuredRightMarginalResponse_eq_scaled_lemma6Response` rewrite the
left/right measured Lemma 5 marginal responses as positive scalings of the
normalized Lemma 6 response under current reward-rate identities and the usual
nonzero denominator/time inputs.
For the actual structured CTMC price form, the normalized Lemma 6 response now
has a compiled per-time expression:
`paper_lemma6_structured_response_per_time_form`.  Combined with the strict
decrease of `q(u)/u`, this gives direct monotone response-shape bridges
`strictAntiOn_gn21Lemma6Response_structured_ctmc_of_coeff_pos` and
`strictMonoOn_gn21Lemma6Response_structured_ctmc_of_coeff_neg`, plus the
one-threshold policy-form packages
`gn21StructuredLemma6ResponsePolicyFormData_strictlyDecreasing` and
`gn21StructuredLemma6ResponsePolicyFormData_strictlyIncreasing`.
For measured current policies under the actual structured price family, the
state-specialized wrappers
`gn21MeasuredLeftLemma6PolicyFormData_strictlyDecreasing_of_structured` and
`gn21MeasuredRightLemma6PolicyFormData_strictlyIncreasing_of_structured`
build those normalized Lemma 6 policy-form packages directly from the
coefficient sign and zero-cutoff facts, with the moving-state CTMC parameters
substituted.
The cutoff can now be selected internally from a sign bracket:
`continuousOn_gn21Lemma6Response_structured_ctmc`,
`exists_gn21Lemma6Response_structured_ctmc_zero_of_bracket`, and
`exists_gn21Lemma6Response_structured_ctmc_zero_of_reverse_bracket` prove the
IVT step, and the bracket constructors
`gn21StructuredLemma6ResponsePolicyFormData_strictlyDecreasing_of_bracket`,
`gn21StructuredLemma6ResponsePolicyFormData_strictlyIncreasing_of_bracket`,
`gn21MeasuredLeftLemma6PolicyFormData_strictlyDecreasing_of_structured_bracket`,
and
`gn21MeasuredRightLemma6PolicyFormData_strictlyIncreasing_of_structured_bracket`
feed it into the Lemma 5 policy-form package.
The next layer is also packaged:
`gn21MeasuredLeftPositiveResponsePolicyFormData_of_scaled_lemma6Response` and
`gn21MeasuredRightPositiveResponsePolicyFormData_of_scaled_lemma6Response`
transfer normalized Lemma 6 positive-response policy-form data through those
positive scalings to the measured marginal responses.
`Theorem4AllMeasurableFixedResponsePolicyFormData` is the matching all-optima
boundary for this lighter route, with `.to_feasible_ae_policy_forms` feeding
the existing feasible a.e. representative machinery.  The direct paper-facing
consumers are
`paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_improvements`
and
`paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_source_assumptions`.
For endpoint proofs whose middle-reroute branch needs the positive rejected
mass used to select the branch, use the hpos-aware variants instead:
`theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementCertificate_of_feasible_ae_forms_and_representative_rejected_mass_improvements`,
`paper_theorem4_measurable_accept_all_ae_unique_optimal_of_feasible_ae_forms_and_representative_rejected_mass_improvements`,
`theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementCertificate_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements`,
`paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements`,
`GN21Theorem3FixedResponsePolicyFormRejectedMassSourceData`,
`theorem3AcceptAllFeasibleRejectedMassStrictLocalPositiveParameterCertificate_of_fixed_response_policy_form_rejected_mass`, and
`paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_rejected_mass_source_assumptions`.
The older fixed-response source boundary coerces to this one via
`GN21Theorem3FixedResponsePolicyFormRejectedMassSourceData.of_plain` and
`Theorem3AcceptAllMeasurableFixedResponsePolicyFormSourceAssumptions.to_rejected_mass_source_assumptions`.
The source-faithful common-fixed-state middle-reroute AE route is now packaged as
`Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteAELocalEndpointCertificate`,
`Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteLocalEndpointCertificate.to_eq_ae_local_endpoint`,
`GN21Theorem3FixedResponsePolicyFormRejectedMassSourceData.of_fixed_state_eq_middle_reroute`,
`GN21Theorem3FixedResponsePolicyFormEqMiddleRerouteSourceData`, and
`paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_eq_middle_reroute_source_assumptions`.
It derives the untouched-state positive mass from the fixed-response a.e.
Lemma 5 representative and derives the surge middle-gap only from positive
rejected mass, so the source proof does not need exact replacement data or an
all-branch `lo < hi` assumption just to use the middle-reroute branch.
The state-level adapters
`gn21MeasuredLeftFixedResponsePolicyFormFeasibleOptimalData_of_dynamic_optimal`
and
`gn21MeasuredRightFixedResponsePolicyFormFeasibleOptimalData_of_dynamic_optimal`
assemble the required fixed-response Lemma 5 data from dynamic optimality and
scaled Lemma 6 policy-form data.
The generic local-optimality bridge now also has the direct
`singleStateMeasurableOptimal` form:
`dynamicStateReward_singleStateMeasurableOptimal_of_dynamicMeasurableOptimal`,
`not_dynamicMeasurableOptimal_of_state_not_singleStateMeasurableOptimal`, and
`not_dynamicMeasurableOptimal_of_state_eq_not_singleStateMeasurableOptimal`.
Use these when a Lemma 5 endpoint-shape result already proves one-state
measurable nonoptimality; the older strict-improvement bridge remains useful
when the endpoint proof is still phrased as an explicit improved feasible
replacement.
The one-threshold dynamic branch exclusions are exposed as
`lemma5_strictlyIncreasing_interval_not_dynamicMeasurableOptimal_of_local_endpoint_paths_with_context`
and
`lemma5_strictlyDecreasing_gap_not_dynamicMeasurableOptimal_of_local_endpoint_paths_with_context`,
so surge increasing and non-surge decreasing endpoint calculus can now
contradict dynamic measurable optimality without a separate one-state bridge.
The source-data constructors
`GN21MeasuredLeftFixedResponsePolicyFormSourceData.of_regularity` and
`GN21MeasuredRightFixedResponsePolicyFormSourceData.of_regularity` now derive
the measured marginal-response measurability and accept-all integrability from
the primitive payment, switch-probability, and trip-time regularity fields.
For the actual Theorem 3 structured prices, the specialized constructors
`GN21MeasuredLeftFixedResponsePolicyFormSourceData.of_ctmc_structured_price`
and
`GN21MeasuredRightFixedResponsePolicyFormSourceData.of_ctmc_structured_price`
also derive structured-price measurability and integrability internally.
The one-threshold source constructors
`GN21MeasuredLeftFixedResponsePolicyFormSourceData.of_ctmc_structured_price_decreasing`
and
`GN21MeasuredRightFixedResponsePolicyFormSourceData.of_ctmc_structured_price_increasing`
go one layer further: their source-facing inputs are the structured-response
coefficient sign, a positive zero cutoff, denominator/nondegeneracy fields,
and the usual integrability facts, and they return the full state source data
for the non-surge decreasing and surge increasing branches.
Their bracket variants
`GN21MeasuredLeftFixedResponsePolicyFormSourceData.of_ctmc_structured_price_decreasing_of_bracket`
and
`GN21MeasuredRightFixedResponsePolicyFormSourceData.of_ctmc_structured_price_increasing_of_bracket`
replace the explicit zero cutoff by a positive interval and endpoint sign
conditions.
`Theorem4AllMeasurableGN21FixedResponsePolicyFormSourceData` packages these
statewise assumptions for all measurable optima and converts to the
all-optima fixed-response policy-form boundary; the constructor
`Theorem4AllMeasurableGN21FixedResponsePolicyFormSourceData.of_one_threshold_structured_forms`
now discharges the allowed-shape wrappers when all optima supply non-surge
decreasing and surge increasing source data.
`GN21Theorem3FixedResponsePolicyFormSourceData.of_gn21_source_data` turns that
package plus accept-all optimality and the four endpoint-improvement cases into
the fixed-response policy-form Theorem 3 source data.
`GN21Theorem3FixedResponsePolicyFormSourceData.of_one_threshold_structured_forms`
is the matching top-level Theorem 3 source constructor for that one-threshold
route.
The existence-based common-fixed-state middle-reroute route now has the direct
one-threshold source boundary
`GN21Theorem3FixedResponseOneThresholdEqMiddleRerouteSourceExistenceData` and
`paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_one_threshold_eq_middle_reroute_existence_source_assumptions`.
This is the preferred paper-facing target when Lemma 6 supplies non-surge
decreasing and surge increasing fixed-response data and the endpoint proof
supplies the common fixed-state equality middle-reroute certificate; Lean
builds the fixed-response policy-form package and derives accept-all
optimality internally.
Measured marginal response measurability and accept-all integrability now have
direct left/right helper lemmas from payment, trip-time, and switch-probability
regularity.  The state-indexed CTMC price family also has direct continuity,
measurability, and policy-set integrability lemmas:
`continuous_ctmcDynamicSwitchProb`, `measurable_ctmcDynamicSwitchProb`,
`continuous_ctmcStructuredDynamicSurgePrice`,
`measurable_ctmcStructuredDynamicSurgePrice`, and
`integrableOn_ctmcStructuredDynamicSurgePrice`.

Additional bridge-adapter declarations now connect the concrete endpoint
calculus to the top-level routes without extra structure plumbing:
`Theorem4ShapeReplacementDerivationCertificate`,
`theorem4ShapeDerivationCertificate_of_shape_replacement`,
`paper_theorem4_dynamic_structural_policy_of_shape_replacement`,
`theorem4NonsurgeAllowedReplacement_positive_acceptAll`,
`theorem4NonsurgeAllowedReplacement_rejectLong`,
`theorem4NonsurgeAllowedReplacement_acceptMiddle`,
`theorem4SurgeAllowedReplacement_positive_acceptAll`,
`theorem4SurgeAllowedReplacement_rejectShort`,
`theorem4SurgeAllowedReplacement_rejectMiddle`,
`theorem4NonsurgeAEShape`,
`theorem4SurgeAEShape`,
`paper_theorem4_measurable_accept_all_ae_unique_optimal_of_ae_shape_statewise_rejected_mass_improvements_unless`,
`Theorem4MeasurableAEEndpointCurrentBoundsSelectionUnlessMiddleRerouteCertificate`,
`Theorem4MeasurableAEEndpointCurrentBoundsSelectionUnlessMiddleRerouteCertificate.of_exact_endpoint_current_bounds_selection`,
`paper_theorem4_measurable_accept_all_ae_unique_optimal_of_ae_endpoint_current_bounds_selection_unless_middle_reroute`,
`Theorem4AllMeasurableAllowedPolicyFormsCertificate.only_ae_shapes`,
`Theorem4NonsurgeAllowedReplacementData`,
`Theorem4SurgeAllowedReplacementData`,
`Theorem4AllOptimalShapeReplacementDerivationCertificate.of_allowed_replacement_data`,
`Theorem4AllOptimalShapeReplacementDerivationCertificate`,
`theorem4ShapeReplacementDerivationCertificate_of_all_shape_replacements`,
`theorem4ShapeDerivationCertificate_of_all_shape_replacements`,
`paper_theorem4_dynamic_structural_policy_of_all_shape_replacements`,
`Theorem4AllowedReplacementStatewiseImprovementCertificate`,
`Theorem4AllowedReplacementEndpointBridgeCertificate`,
`Theorem4AllowedReplacementStatewiseImprovementCertificate.of_endpoint_bridges`,
`Theorem4ShapeDerivationStatewiseImprovementCertificate.of_allowed_replacement_data`,
`paper_theorem4_accept_all_unique_optimal_of_allowed_replacement_data`,
`paper_theorem4_accept_all_unique_optimal_of_allowed_replacement_endpoint_bridges`,
`Theorem4ShapeDerivationStatewiseImprovementCertificate.of_shape_replacement`,
`Theorem4ShapeDerivationStatewiseImprovementCertificate.of_all_shape_replacements`,
`paper_theorem4_accept_all_unique_optimal_of_shape_replacement_statewise_improvements`,
`paper_theorem4_accept_all_unique_optimal_of_all_shape_replacements_statewise_improvements`,
`Theorem4MeasurableShapeDerivationCertificate`,
`Theorem4AllMeasurableOptimalShapeReplacementDerivationCertificate`,
`theorem4MeasurableShapeDerivationCertificate_of_all_measurable_shape_replacements`,
`paper_theorem4_measurable_dynamic_structural_policy_of_shape_derivation`,
`paper_theorem4_measurable_dynamic_structural_policy_of_all_shape_replacements`,
`gn21SurgeStatewiseStrictAggregateImprovement`,
`gn21NonsurgeStatewiseStrictAggregateImprovement`,
`gn21SurgeFeasibleStatewiseStrictAggregateImprovement`,
`gn21NonsurgeFeasibleStatewiseStrictAggregateImprovement`,
`GN21SurgeEndpointBridgeData.of_statewise_strict_aggregate_improvement`,
`GN21NonsurgeEndpointBridgeData.of_statewise_strict_aggregate_improvement`,
`Theorem4MeasuredAggregateFeasibleStatewiseStrictLocalImprovementCertificate`,
`theorem4MeasuredAggregateFeasibleStatewiseStrictLocalImprovementCertificate_of_measurable_shape_statewise_improvements`,
`theorem4MeasuredAggregateFeasibleStrictLocalImprovementCertificate_of_measurable_shape_statewise_improvements`,
`Theorem4ShapeDerivationStatewiseImprovementCertificate`,
`Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate`,
`Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate.of_all_measurable_shape_replacements`,
`Theorem4ShapeDerivationStatewiseImprovementCertificate.of_statewise_improvements`,
`Theorem4ShapeDerivationEndpointBridgeCertificate.of_statewise_improvements`,
`Theorem4ShapeDerivationEndpointBridgeCertificate.of_statewise_improvement_certificate`,
`paper_theorem4_accept_all_unique_optimal_of_shape_derivation_statewise_improvements`,
`paper_theorem4_accept_all_unique_optimal_of_shape_derivation_statewise_improvement_certificate`,
and
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_statewise_improvement_certificate`,
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_shape_derivation_statewise_improvement_certificate`,
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_statewise_improvement_certificate_of_lemma9_positive_primitives`,
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_shape_derivation_statewise_improvement_certificate_of_lemma9_positive_primitives`,
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_acceptAll_primitives_and_allowed_replacement_data_of_lemma9_positive_primitives`,
`theorem3AcceptAllFeasibleStrictLocalCertificate_of_measurable_shape_statewise_improvements`,
`Theorem3AcceptAllMeasurableShapeStatewiseImprovementSourceAssumptions`,
`paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_statewise_improvements_source_assumptions`,
`Theorem3AcceptAllMeasurableShapeReplacementStatewiseImprovementSourceAssumptions`,
`paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_replacement_statewise_improvements_source_assumptions`,
`Theorem4MeasurableEndpointCurrentBoundsSelectionCertificate`,
`Theorem4MeasurableShapeDerivationStatewiseImprovementCertificate.of_endpoint_current_bounds_selection`,
`theorem4MeasuredAggregateFeasibleStrictLocalImprovementCertificate_of_endpoint_current_bounds_selection`,
`paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_selection`,
`Theorem3AcceptAllMeasurableEndpointCurrentBoundsSelectionSourceAssumptions`,
`paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_selection_source_assumptions`,
`Theorem4NonsurgeMeasurableReplacementData`,
`Theorem4SurgeMeasurableReplacementData`,
`Theorem4AllMeasurableOptimalShapeReplacementDerivationCertificate.of_allowed_replacement_data`,
`Theorem4MeasurableEndpointCurrentBoundsAllowedReplacementSelectionCertificate`,
`Theorem4MeasurableEndpointCurrentBoundsSelectionCertificate.of_allowed_replacement_data`,
`GN21WithDensityAcceptAllSupport`,
`GN21NonsurgeRejectLongCurrentBoundsEndpointData.of_acceptAll_support`,
`GN21NonsurgeAcceptMiddleCurrentBoundsEndpointData.of_acceptAll_support`,
`GN21SurgeRejectShortCurrentBoundsEndpointData.of_acceptAll_support`,
`GN21SurgeRejectMiddleLoCurrentBoundsEndpointData.of_acceptAll_support`,
`GN21SurgeRejectMiddleHiCurrentBoundsEndpointData.of_acceptAll_support`,
`continuous_gn21SwitchProb`,
`continuous_ctmcStructuredSurgePrice`,
`continuousAt_mul_density_of_continuous`,
`stronglyMeasurableAtFilter_mul_density_of_continuous`,
`intervalIntegrable_mul_density_of_continuous`,
`GN21EndpointProductContinuityData`,
`GN21EndpointProductContinuityData.of_ctmcStructured`,
`GN21FiniteEndpointProductCalculusData`,
`GN21FiniteEndpointProductCalculusData.of_ctmcStructured`,
`paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_allowed_replacement_selection`,
`Theorem3AcceptAllMeasurableEndpointCurrentBoundsAllowedReplacementSourceAssumptions`,
`paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_allowed_replacement_source_assumptions`,
`theorem3AcceptAllStructuredParameterEvidence`,
`theorem3MeasuredStructuredICConclusion`,
`Theorem4StatewiseAcceptAllWeakRewardCertificate`,
`theorem4StatewiseAcceptAllWeakRewardCertificate_of_global_statewise_accept_all_reward`,
`paper_theorem4_accept_all_optimal_of_statewise_accept_all_weak_reward`,
`Theorem4MeasuredAggregateWeakAcceptAllRewardCertificate`,
`theorem4StatewiseAcceptAllWeakRewardCertificate_of_measured_aggregate_weak_improvements`,
`theorem4MeasuredAggregateWeakAcceptAllRewardCertificate_of_measured_aggregate_improvements`,
`paper_theorem3_ctmc_structured_prices_ic_of_accept_all_optimal`,
`paper_theorem3_ctmc_structured_prices_ic_of_statewise_accept_all_weak_reward`,
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_statewise_accept_all_weak_reward_of_lemma9_positive_primitives`,
`theorem3AcceptAllWeakRewardCertificate`,
`theorem3AcceptAllWeakRewardCertificate_of_global_statewise_accept_all_reward`,
`theorem3AcceptAllWeakRewardCertificate_of_measured_aggregate_weak_reward`,
`theorem3AcceptAllWeakRewardCertificate_of_measured_aggregate_reward`,
`paper_theorem3_measured_structured_ic_prices_of_weak_reward`,
`Theorem3AcceptAllWeakRewardSourceAssumptions`,
`paper_theorem3_measured_structured_ic_prices_of_weak_reward_source_assumptions`,
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_positive_replacement_of_lemma9_positive_primitives`,
`theorem3AcceptAllPositiveReplacementCertificate`,
`theorem3AcceptAllPositiveReplacementCertificate_of_statewise_accept_all_reward`,
`paper_theorem3_measured_structured_ic_prices_of_positive_replacement`,
`Theorem3AcceptAllPositiveReplacementSourceAssumptions`,
`paper_theorem3_measured_structured_ic_prices_of_positive_replacement_source_assumptions`,
`theorem3AcceptAllAllowedReplacementCertificate`,
`theorem3AcceptAllAllowedReplacementCertificate_of_endpoint_bridges`,
`Theorem3AcceptAllAllowedReplacementSourceAssumptions`,
`paper_theorem3_measured_structured_ic_prices_of_source_assumptions`,
`Theorem3AcceptAllAllowedReplacementEndpointBridgeSourceAssumptions`,
`paper_theorem3_measured_structured_ic_prices_of_endpoint_bridge_source_assumptions`,
with the unbundled raw-argument variant
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_statewise_improvements`
and its positive-primitives counterpart
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_derivation_statewise_improvements_of_lemma9_positive_primitives`;
the Lemma 5 replacement-data version is
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_shape_replacement_statewise_improvements_of_lemma9_positive_primitives`;
the all-optimal replacement-data version is
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_all_shape_replacements_statewise_improvements_of_lemma9_positive_primitives`;
the packaged allowed-replacement source-boundary version is
`paper_theorem3_measured_ctmc_structured_prices_exist_and_ic_of_ratio_and_allowed_replacement_data_of_lemma9_positive_primitives`.
The first concrete shape-level endpoint bridge is also exposed as
`paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_reject_long_withDensity_of_shape`,
with an accept-all-bound variant
`paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_reject_long_withDensity_of_shape_acceptAll_bounds`
that derives the current Lemma 10 bounds and Remark 4 positivity conditions,
with the corresponding accept-middle bridge
`paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_accept_middle_withDensity_of_shape`
and accept-all-bound variant
`paper_theorem4_nonsurge_statewise_strict_aggregate_improvement_of_lemma10_accept_middle_withDensity_of_shape_acceptAll_bounds`;
the surge reject-short bridge
`paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_tail_withDensity_of_shape`
and accept-all-bound variant
`paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_tail_withDensity_of_shape_acceptAll_bounds`
do the same for the tail case, and
`paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity_of_shape`
plus
`paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity_of_shape`
cover the two reject-middle endpoint moves, with accept-all-bound variants
`paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity_of_shape_acceptAll_bounds`
and
`paper_theorem4_surge_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity_of_shape_acceptAll_bounds`.
Their feasible-measurable counterparts are also compiled:
`paper_theorem4_nonsurge_feasible_statewise_strict_aggregate_improvement_of_lemma10_reject_long_withDensity_of_shape_acceptAll_bounds`,
`paper_theorem4_nonsurge_feasible_statewise_strict_aggregate_improvement_of_lemma10_accept_middle_withDensity_of_shape_acceptAll_bounds`,
`paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_tail_withDensity_of_shape_acceptAll_bounds`,
`paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity_of_shape_acceptAll_bounds`,
and
`paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity_of_shape_acceptAll_bounds`;
the current-bounds-data variants
`paper_theorem4_nonsurge_feasible_statewise_strict_aggregate_improvement_of_lemma10_reject_long_withDensity_of_shape_current_bounds_data`,
`paper_theorem4_nonsurge_feasible_statewise_strict_aggregate_improvement_of_lemma10_accept_middle_withDensity_of_shape_current_bounds_data`,
`paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_tail_withDensity_of_shape_current_bounds_data`,
`paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_lo_withDensity_of_shape_current_bounds_data`,
and
`paper_theorem4_surge_feasible_statewise_strict_aggregate_improvement_of_lemma9_reject_middle_hi_withDensity_of_shape_current_bounds_data`
remove duplicated `Q,T,W`, denominator, and Remark 4 plumbing.  The endpoint
data packages
`GN21NonsurgeRejectLongCurrentBoundsEndpointData`,
`GN21NonsurgeAcceptMiddleCurrentBoundsEndpointData`,
`GN21SurgeRejectShortCurrentBoundsEndpointData`,
`GN21SurgeRejectMiddleLoCurrentBoundsEndpointData`,
`GN21SurgeRejectMiddleHiCurrentBoundsEndpointData`, and
`GN21SurgeRejectMiddleCurrentBoundsEndpointData` feed the compiled
`Theorem4MeasurableEndpointCurrentBoundsSelectionCertificate` route to Theorem
4 and Theorem 3.

## Remaining Work

The fastest source-faithful route is continuous, not finite.  The reusable
two-state CTMC transition-kernel closed form is now in place, including strict
switch positivity, `q(u)<lambda*u`, `q(u)/u` monotonicity, and the zero-time
limit needed by Appendix D, plus the `lambda*t - q(t)` strict positivity and
derivative monotonicity used in Remark 4. Theorem 1 has
the Step 1 equal-utilization swap, the stronger measurable replacement by the
complete threshold at the policy reward rate, full Step 2 partial-threshold
dominance, the multiplicative-pricing threshold best-response special case,
compact upper-semicontinuity Step 3 reductions, and canonical measurable
threshold-set infrastructure; its left and right compact-tail reductions and
high-reward band/gap split are now compiled.  The compact
upper-semicontinuity seam is closed by one-sided dominated convergence: from
the left, strict and complete threshold rewards converge to the complete
threshold reward, and from the right they converge to the strict threshold
reward, so the max cutoff objective is upper-semicontinuous even with boundary
atoms.
Lemma 1/Lemma 3 deterministic algebra is
closed at the measured-formula level. Appendix D's derivative kernel, affine
canonical response, Lemma 6 strict-sign transfer, Lemma 7
derivative-numerator calculation, canonical CTMC quasi-convex/quasi-concave
response shapes, Remark 4 maximization, measured current-policy tightening
from accept-all bounds, strict measured-positivity support, structured-price
algebra, structured derivative-kernel positivity from CTMC
linearization, and Lemma 9/10 interval feasibility bridges are represented;
Theorem 1 now has measurable best-response constructors from complete-threshold
or compact-continuity maximizers,
Lemma 5 has canonical measurable interval-policy representatives, policy-form
wrappers, derivative-shape witnesses from Lemmas 7-8, canonical replacement
constructors for all five shape cases, optimality extraction from strict
replacement certificates, reusable quasi-convex/quasi-concave between-endpoint
facts, and the positive-response sign-to-policy-form classification for the
positive, monotone, quasi-convex, and quasi-concave cases. It also has the
  linearized marginal-reward dominance theorem saying the positive-response
  policy weakly dominates every measurable feasible policy for a fixed marginal
  response, plus the zero-mass contrapositive: if the positive-response
  candidate is no worse than the current policy, omitted positive-response
  mass and accepted nonpositive-response support both vanish, yielding
  accept-all almost everywhere in the positive-response case. Theorem 4 now
  has the pure routing from Lemma 5 policy
forms into the source surge/non-surge shape alternatives plus a positive-form
accept-all uniqueness interface, a statewise positive-replacement route into
that interface, a statewise accept-all reward interface, and a global statewise
reward interface that derives accept-all optimality, plus a strict-local
interface that rules out non-accept-all optima, state-specific allowed
replacement constructors for the Theorem 4 shape data, source-facing
replacement-data cases for the all-optimal interface, and measured constructors for
the actual two-state reward formula; the measured aggregate strict-local route
now has a uniform statewise replacement wrapper, measured upper-endpoint
interval-policy, lower-endpoint interval-policy, and unbounded-tail primitive
realization for `Q,T,W`, two-piece middle-rejection realization, positive
endpoint replacement realization, Lemma 9/10 upper/lower/tail endpoint bridges
for both states, Lemma 9 reject-middle lower/upper cutoff bridges for the surge
  state, concrete with-density replacement-policy specializations for both
  surge reject-middle cutoff moves with finite positive-density nondegeneracy
  constructors for both current and replacement middle-rejection policies,
  concrete tail left-replacement realizations and current/replacement
  nondegeneracy constructors for the surge reject-short case, non-surge
  reject-long and accept-middle current/replacement nondegeneracy constructors,
  concrete with-density strict-local bridge wrappers for all four endpoint
  shape cases, and a generalized endpoint bridge certificate feeding the
  measured strict-local interface, with a direct Theorem 4 accept-all
  uniqueness endpoint from the four-case shape-selection certificate and a
  direct Theorem 4 endpoint from the Lemma 5-style shape derivation,
  feasibility, and the four endpoint bridges, plus a source-facing
  statewise-improvement certificate and an all-optimal replacement interface
  that package the remaining analytic selection obligations without requiring
  the caller to preselect a structural optimum, plus a single
  allowed-replacement source-boundary certificate bundling optimum existence,
  feasibility, replacement cases, and endpoint improvements.  The endpoint
  current-bounds selection certificate now packages the feasible endpoint data
  cases and compiles directly to Theorem 4 measurable accept-all uniqueness;
  its source-facing allowed-replacement variant also derives feasible
  measurability of the canonical Lemma 5 replacements internally.
  Theorem 3 now has a
concrete CTMC structured-price endpoint that consumes all of those interfaces,
including integrated ratio-to-parameters-to-IC theorems for the global
statewise reward comparisons, measured aggregate strict-local improvements,
the measured CTMC structured reward, and the measured accept-all primitives
with scalar positivity and direct Lemma 9 primitive-feasibility side
conditions derived for the global, strict-local, and packaged
statewise-certificate routes, plus a
direct weak-reward IC wrapper whose final obligation is only weak statewise
accept-all improvement for the constructed prices, a positive-replacement
source wrapper whose final obligation is the Lemma 9/10 positive Lemma 5
replacement proof for the constructed prices, current-bounds source wrappers
that accept either scaled accounting equations or measured reward-rate
equalities for the fixed state, plus
a direct ratio-to-IC route from the four-case Theorem 4 shape-endpoint-selection
certificate and the paper-ordered shape-derivation endpoint-bridge
certificate, plus a route that accepts the raw statewise improvement
existentials produced by the concrete endpoint lemmas and a packaged
statewise-improvement certificate for the same source boundary, and a route
that consumes all-optimal Lemma 5 replacement data directly or the packaged
allowed-replacement source-boundary certificate, and the current regular
allowed-policy-form route that consumes measurable Lemma 5 policy-form
classification plus regular endpoint packages directly.
Proposition 3.1 is closed for the source renewal reward on measurable
continuous policies. Next: instantiate the regular current-bounds source endpoint for arbitrary feasible measurable
optimal policies by proving the regularity theorem that supplies ordinary Lemma
5 allowed policy-form classification, chooses the relevant upper, lower, tail,
or middle-rejection endpoint move, and discharges the remaining Lemma 9/10
current-bound fields without assuming target reward-rate identities for
arbitrary non-accept-all fixed states.  For Lemma 10, the compiled
endpoint-term route now exposes the exact static and zero-time linearized
endpoint inequalities needed when the current fixed surge reward rate differs
from the Theorem 3 target rate, and this route reaches the weak Theorem 3
accept-all boundary through a current-rate aggregate certificate;
`LEMMA9_10_REWARD_RATE_AUDIT.md` records why a one-sided reward comparison alone
is not enough.
The direct current-bounds strict route is now
`paper_theorem4_measurable_accept_all_unique_optimal_of_structured_current_bounds_source_support`:
it consumes the source current-bound data plus positive Lemma 6 kernel support
on the rejected complement and uses accept-all itself as the strict local
replacement.
The full-data Lemma 9/10 packages also now have rejected-mass variants,
`GN21NonsurgeLemma10AcceptAllAggregateData.aggregate_lt_acceptAll_of_rejected_measure_pos`
and
`GN21SurgeLemma9AcceptAllAggregateData.aggregate_lt_acceptAll_of_rejected_measure_pos`,
which derive positive kernel support from positive rejected-complement measure.
The source-facing endpoint
`paper_theorem4_measurable_accept_all_unique_optimal_of_structured_current_bounds_source_rejected_mass`
uses those wrappers directly, so the remaining exact-uniqueness task can be
phrased as positive rejected-trip mass for every non-accept-all optimum; the
zero-mass alternative points toward an almost-everywhere uniqueness statement.
The measured aggregate positive-rejected-mass route no longer needs
accept-all optimality as a separate source assumption when an optimum exists:
`policyAlmostEverywhereEq_acceptAll_of_acceptAllAlmostEverywhere`,
`dynamicMeasurableOptimal_gn21MeasuredDynamicRewardFunctional_acceptAll_of_exists_optimal_ae_unique`,
and
  `Theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementExistenceCertificate.to_accept_all_certificate`
  upgrade existence plus a.e. uniqueness of optima to exact accept-all
  optimality for the measured GN21 reward.  The feasible a.e. representative
  and fixed-response aggregate constructors now have matching existence
  versions,
  `theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementExistenceCertificate_of_feasible_ae_forms_and_representative_rejected_mass_improvements`
  and
  `theorem4MeasuredAggregateFeasibleRejectedMassStrictLocalImprovementExistenceCertificate_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements`,
  so their compatibility wrappers derive accept-all optimality internally.
  The fixed-response rejected-mass Theorem 3 source boundary also has the
  no-accept-all version
  `GN21Theorem3FixedResponsePolicyFormRejectedMassSourceExistenceData` with
  wrapper
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_rejected_mass_existence_source_assumptions`.
  The common fixed-state equality middle-reroute fixed-response route now has
  the matching source boundary
  `GN21Theorem3FixedResponsePolicyFormEqMiddleRerouteSourceExistenceData` and
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_fixed_response_policy_form_eq_middle_reroute_existence_source_assumptions`.
  The same bridge now powers the by-policy-form and light middle-reroute
  Theorem 3 source boundaries:
  `GN21Theorem3MiddleRerouteAEPolicyFormSourceExistenceData`,
  `GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData`,
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_by_policy_form_derived_tail_middle_reroute_ae_existence_source_assumptions`,
  and
  `paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_middle_reroute_light_ae_existence_source_assumptions`
  consume Lemma 5 replacement data plus the local endpoint package without a
  separate accept-all optimality field.
Lean now derives this rejected mass from the allowed Lemma 5 policy forms under
the shared density-support package via
`GN21WithDensityAcceptAllSupport.rejected_mass_pos_of_rejectsLongTrips`,
`GN21WithDensityAcceptAllSupport.rejected_mass_pos_of_rejectsShortTrips`,
`GN21WithDensityAcceptAllSupport.rejected_mass_pos_of_acceptsMiddleTrips`,
`GN21WithDensityAcceptAllSupport.rejected_mass_pos_of_rejectsMiddleTrips`, and
`paper_theorem4_measurable_accept_all_unique_optimal_of_structured_current_bounds_allowed_policy_forms`;
the residual exact-uniqueness geometry is the nondegenerate surge
middle-rejection gap, because a collapsed one-point gap has zero continuous
mass and belongs in an almost-everywhere uniqueness route.
That paper-faithful route is now compiled as
`paper_theorem4_measurable_accept_all_ae_unique_optimal_of_structured_current_bounds_source`:
from the structured current-bound source data it proves accept-all measurable
optimality and that every measurable optimum agrees with accept-all up to
statewise rejected-trip measure zero.
The Theorem 3 source-current-bounds wrapper now threads this conclusion through
the constructed price parameters as
`paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_structured_current_bounds_source_feasible_source_assumptions`.
The primitive feasible current-bounds package has its own rejected-mass
adapter,
`paper_theorem4_measurable_accept_all_ae_unique_optimal_of_structured_current_bounds_primitive`,
and the feasible-primitive, accounting, and reward-rate Theorem 3 wrappers
reuse it or the source-data adapter to return the same AE uniqueness
conclusion.
Concrete
with-density replacement policies, primitive equalities, finite positive-density
current/replacement nondegeneracy, accept-all density support constructors,
continuous-density endpoint calculus helpers, feasible-domain preservation, and
Lemma 9/10 current-bound data plumbing are now available through regular
endpoint records for all four Theorem 4 shape cases, with reject-middle split
into lower- and upper-cutoff endpoint variants; the older regular-selection
route remains compiled for the variant that proves ordinary allowed Lemma 5
  replacement data explicitly.  Shared source regularity is now factored into
  `GN21RegularEndpointSharedSourceData`, so the final selector can focus on
  positive cutoff geometry and fixed-state transfer
  facts.  The source current-bound records can still be built with
  `GN21NonsurgeLemma10AcceptAllAggregateSourceData.of_acceptAll_tightening` and
  `GN21SurgeLemma9AcceptAllAggregateSourceData.of_acceptAll_tightening`, which
  apply the measured Remark 4 tightening lemmas from accept-all moving-state
  bounds to the current moving-state policy.  The shared-source package also
  has shape-specific current-mass positivity lemmas for reject-long,
  accept-middle, reject-short, and reject-middle policies.  The five
  `...RegularEndpointData.of_shared_source_and_acceptAll_tightening`
  constructors now compose these pieces into the regular endpoint records.
  `Theorem3AcceptAllStructuredParameterData.of_evidence` gives a named view of
  the constructed Theorem 3 ratios, accept-all Lemma 9/10 bounds, and
  accounting identities.
Then continue with the two-state renewal law-of-large-numbers bridge and the
remaining Theorem 3/Theorem 4 endpoint-selection boundary; Theorem 1's compact
upper-semicontinuity proof is closed.
