# GN21 Continuous Proof Plan

This note records the fastest route to closing the remaining GN21 proof, beyond
the already-compiled wrappers.  The most recent compiled adapter is:

```lean
paper_theorem3_measured_structured_measurable_ic_prices_of_source_assumptions
```

This is now the preferred IC closure route.  It proves the surge-state
accept-all move first, using Lemma 9 with the current fixed non-surge reward
rate, and then proves the non-surge accept-all move only after surge is already
fixed at accept-all, where Lemma 10 can use the Theorem 3 target surge reward
rate.  The older fixed-transfer adapter remains useful for branch bookkeeping,
but it should not be treated as the final source-faithful closure route unless
the source proof also establishes the target reward-rate/equality facts for
arbitrary non-accept-all fixed states.  The remaining field for that adapter is
`Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailCutoffBoundsLocalEndpointCertificate`
for the structured prices constructed by Theorem 3, paired with ordinary
all-measurable allowed Lemma 5 replacement data.  This endpoint packages shared
continuous-density regularity, non-surge cutoff nondegeneracy, one fixed-state
pointwise equality/reward-rate package for each state, and ordinary surge cutoff
bounds.  Lean converts those common fixed-state packages into the older
policy-form packages internally.
Lean chooses the upper reject-middle cutoff from `0 ≤ lo < hi`, derives
positive surge-tail product integrability from the shared
accept-all time/switch integrability fields, upgrades those positive tails to
the older uniform-tail package using continuous finite-interval product
calculus, then uses allowed Lemma 5 policy forms to
choose the accept-all or non-accept-all fixed-state branch, derives the
non-surge accept-middle local move from the positive lower cutoff, builds the
surge moving endpoint data from the uniform tail package, then derives current
mass, no-mass pointwise endpoint facts, mass-separated endpoint facts,
positive-cutoff endpoint data, and the regular Theorem 4 certificate
internally.  The older regular
allowed-policy-form route remains compiled and asks for fully built regular
endpoint records; the older regular-shape route remains compiled and asks for
the already-packaged shape derivation; the older regular-selection route remains
compiled and asks for ordinary allowed Lemma 5 replacement data in addition to
the same regular endpoint packages.  The previous broader endpoints remain
compiled:

```lean
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_allowed_policy_forms_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_shape_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_regular_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_supported_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_allowed_replacement_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_selection_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_replacement_statewise_improvements_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_measurable_shape_statewise_improvements_source_assumptions
```

## Current Best Path

1. The feasible endpoint improvement wrappers for the four shape cases are
   compiled, including the accept-all-bound versions:
   non-surge reject-long, non-surge accept-middle, surge reject-short, and
   both surge reject-middle endpoint moves.  The current-bounds-data variants
   are also compiled, so the final theorem no longer has to thread current
   `Q,T,W` paths, denominator positivity, or Remark 4 side conditions by hand.

2. Use the sequential Theorem 3 frontier instead of the stronger simultaneous
   statewise frontier.  The reward-rate audit in
   `LEMMA9_10_REWARD_RATE_AUDIT.md` records the current distinction between
   Theorem 3 target rates and Lemma 9/10 current fixed-state rates.  Lean now
   has a reward-rate-separated Lemma 10 endpoint-term route:
   `lemma10StructuredStaticTerm_eq_ratio_reward_split`,
   `lemma10StructuredLinearEndpoint_eq_ratio_reward_split`,
   `lemma10StructuredStaticTerm_pos_of_ratio_reward_slack`,
   `lemma10StructuredLinearEndpoint_pos_of_ratio_reward_slack`,
   `paper_lemma10_structured_derivative_kernel_pos_of_ratio_reward_slack`,
   `paper_lemma10_structured_derivative_kernel_pos_of_endpoint_terms`, and
   `gn21MeasuredAggregateRewardPrimitives_le_acceptAll_left_of_lemma10_endpoint_terms`.
   This route is threaded up to the weak Theorem 3 boundary through
   `GN21NonsurgeLemma10EndpointTermsAggregateData`,
   `Theorem4MeasuredAggregateStructuredEndpointTermsCurrentRateWeakCertificate`,
   and
   `theorem3AcceptAllWeakRewardCertificate_of_structured_endpoint_terms_current_rates`.
   The paper-facing source wrapper is
   `paper_theorem3_measured_structured_ic_prices_of_structured_endpoint_terms_current_rate_source_assumptions`.
   More importantly, Lean now has the sequential current-bounds route:
   `Theorem4MeasuredAggregateStructuredSequentialCurrentBoundsWeakCertificate`,
   `Theorem4MeasuredAggregateStructuredFeasibleSequentialCurrentBoundsWeakCertificate`,
   `paper_theorem3_measured_structured_ic_prices_of_structured_sequential_current_bounds_source_assumptions`,
   and
   `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_current_bounds_source_assumptions`.
   The lightest feasible-measurable wrapper is
   `paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_current_bounds_source_data_assumptions`,
   exposed canonically as
   `paper_theorem3_measured_structured_measurable_ic_prices_of_source_assumptions`.
   The denominator-valid source theorem is now
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_source_assumptions`.
   Lean now derives the packed aggregate data, nondegeneracy fields, and the
   Lemma 10 accept-all fixed-surge branch from Theorem 3 parameter data.  The
   remaining field on the positive-mass route is just Lemma 9 reward-rate data
   for the surge move, quantified over feasible measurable policies whose
   accepted trip mass is positive in both states.  This field now has a
   compiled fixed-transfer adapter:
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_fixed_transfer_reward_rate_data_assumptions`.
   It asks for accept-all Lemma 9 bounds at the effective current ratio, the
   current fixed non-surge reward rate, and the two fixed-state cross-ratio
   comparisons; Lean transfers the fixed state and then tightens the moving
   surge state.  A target-rate specialization,
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_target_fixed_transfer_data_assumptions`,
   reuses the constructed Theorem 3 accept-all bounds when the current fixed
   non-surge reward rate is `R1` and `m_2-R1>0` is available.  The
   reward-bound specialization
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_target_reward_bound_fixed_transfer_data_assumptions`
   keeps the same target accept-all bounds but lets the current fixed
   non-surge reward rate be below `R1`; Lean converts the target ratio into
   the effective current ratio using the shared `z_2` accounting identity,
   a nonpositive accept-all lower endpoint, and the two fixed-state
   cross-ratio comparisons.  The pointwise
   variant
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_target_pointwise_fixed_transfer_data_assumptions`
   derives both fixed-state cross-ratio comparisons from one equality on the
   current non-surge rejected complement.  The positive-ratio pointwise wrapper
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_target_positive_ratio_pointwise_fixed_transfer_data_assumptions`
   additionally derives `m_2-R1>0` from the existing Theorem 3 multiplier
   lemma.  The positive-parameter sequential boundary
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_positive_parameter_positive_mass_feasible_sequential_weak_reward`
   preserves the constructed positive surge-ratio witness for source adapters
   that should not ask for it again.  The positive-parameter reward-bound
   wrapper
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_target_reward_bound_fixed_transfer_data_assumptions`
   is now the cleanest compiled boundary for the sequential route: the source
   supplies effective-ratio accounting, `r1_current <= R1`, nonnegativity of
   `r1_current`, reward-rate identity, and the fixed-state cross comparisons.
   The no-ratio variant
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_target_reward_bound_fixed_transfer_no_ratio_data_assumptions`
   constructs `z_2/(m_2-r1_current)` internally, leaving only
   `r1_current <= R1`, `0 <= r1_current`, reward-rate identity, and the
   fixed-state cross comparisons as policy-dependent data.  The final-sign
   variant
   `paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_final_sign_reward_bound_fixed_transfer_no_ratio_data_assumptions`
   derives the accept-all lower-endpoint fact from the paper's Lemma 9
   denominator and left-nonpositive final-sign assumptions.
   The older broad
   feasible-measurable wrapper still exposes the explicit positive-current-mass
   obligation, and the accounting-form/raw source-data wrappers remain compiled
   as intermediate adapters.

3. Instantiate the positive-mass feasible sequential source route from source
   regularity: prove either the effective-ratio fixed-transfer data above for
   the surge move at each positive-mass feasible current policy, or prove the
   final-sign reward-bound/no-ratio specialization by showing the current
   non-surge reward rate is at most `R1`, nonnegative, and equal to the
   measured reward-rate expression, plus the fixed-state cross-ratio
   comparisons.  The target-rate positive-ratio pointwise
   specialization remains available when the current non-surge reward rate is
   known to equal `R1`.  The Lemma 10 non-surge move with surge fixed to
   accept-all is now compiled from the constructed Theorem 3 parameter data,
   and positive mass supplies the denominator/nondegeneracy side conditions.
   The older regular
   allowed-policy-form and fixed-transfer routes can remain available for
   stronger uniqueness or statewise statements.

## Key Missing Mathematical Lemma

The hard theorem should have this shape:

```lean
theorem theorem4_measurable_shape_statewise_improvements_of_endpoint_regular
    (...) :
    Theorem4MeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsCertificate
      μ arrival m z switch12 switch21
```

Its hypotheses should be source-level regularity assumptions, not pre-unpacked
endpoint primitives:

- `μ 0` and `μ 1` are Lebesgue measures with nonnegative measurable densities,
  packaged as `GN21WithDensityAcceptAllSupport` when finite/positive support is
  needed.
- The densities are positive and continuous at the relevant finite endpoint.
- Current feasible optimal policies have the interval/tail shapes from Lemma 5.
- The current-policy `Q,T,W` primitives agree with the endpoint path formulas,
  or equivalently produce the compiled current-bounds endpoint data packages.
- The Lemma 9 structured bounds hold for the surge move with the current
  non-surge fixed-state reward rate.
- The Lemma 10 structured bounds hold for the non-surge move after the surge
  state is accept-all, so the fixed-state reward rate is the Theorem 3 target
  accept-all rate.
- The other state's current policy has positive finite mass and the required
  `Q,T,W` accounting identity.

Most of these already have local lemmas.  The missing work is packaging them so
the arbitrary optimum generated by measurable shape derivation can be converted
into the concrete endpoint policy data.

## Reusable Infrastructure To Build

- `dynamicFeasibleMeasurablePolicy_update` is now proved and should be reused
  everywhere a single-state replacement is selected.
- `Theorem4AllMeasurableOptimalShapeReplacementDerivationCertificate.of_allowed_replacement_data`
  now derives feasible measurable replacement data from source-facing allowed
  Lemma 5 cases, so the final source theorem should not provide dependent
  measurable replacement packages by hand.
- `GN21WithDensityAcceptAllSupport` now derives current and replacement
  finite-mass/positive-density support fields for feasible policies and all
  five endpoint movements.  Use
  `GN21NonsurgeRejectLongCurrentBoundsEndpointData.of_acceptAll_support`,
  `GN21NonsurgeAcceptMiddleCurrentBoundsEndpointData.of_acceptAll_support`,
  `GN21SurgeRejectShortCurrentBoundsEndpointData.of_acceptAll_support`,
  `GN21SurgeRejectMiddleLoCurrentBoundsEndpointData.of_acceptAll_support`, and
  `GN21SurgeRejectMiddleHiCurrentBoundsEndpointData.of_acceptAll_support`
  instead of filling those fields manually.
- `continuous_gn21SwitchProb`, `continuous_ctmcStructuredSurgePrice`,
  `continuousAt_mul_density_of_continuous`,
  `stronglyMeasurableAtFilter_mul_density_of_continuous`, and
  `intervalIntegrable_mul_density_of_continuous` derive endpoint continuity,
  strong measurability, and finite-interval integrability fields from a
  continuous real-valued density.
- `GN21EndpointProductContinuityData.of_ctmcStructured` and
  `GN21FiniteEndpointProductCalculusData.of_ctmcStructured` bundle the `q,w,t`
  endpoint calculus fields for structured prices.  Prefer the endpoint
  constructors ending in `of_acceptAll_support_and_calculus` or
  `of_acceptAll_support_and_continuity` when building the final endpoint data.
- `GN21PositiveIntervalProductIntegrabilityData.of_ctmcStructured` derives the
  short accepted-interval integrability fields for all positive finite
  endpoints from continuous density/product data.  `GN21TailProductIntegrabilityData`
  bundles one improper tail assumption and uses `q_mono`, `w_mono`, and
  `t_mono` to supply narrower current and replacement tails.
- The supported endpoint records
  `GN21NonsurgeRejectLongSupportedEndpointData`,
  `GN21NonsurgeAcceptMiddleSupportedEndpointData`,
  `GN21SurgeRejectShortSupportedEndpointData`,
  `GN21SurgeRejectMiddleLoSupportedEndpointData`,
  `GN21SurgeRejectMiddleHiSupportedEndpointData`, and
  `GN21SurgeRejectMiddleSupportedEndpointData` now bridge these support,
  calculus, and short/tail integrability packages into the current-bounds
  endpoint certificate expected by Theorem 4.
- `GN21NonsurgeLemma10AcceptAllAggregateData.of_source` and
  `GN21SurgeLemma9AcceptAllAggregateData.of_source` now turn source Lemma 9/10
  current-bounds data directly into the full current-bounds endpoint packages,
  so endpoint construction should not manually compose the primitive route.
- `GN21NonsurgeLemma10AcceptAllAggregateSourceData.of_acceptAll_tightening`
  and `GN21SurgeLemma9AcceptAllAggregateSourceData.of_acceptAll_tightening`
  build those source current-bound records from accept-all moving-state bounds,
  positive current mass, current integrability, and the fixed-state reward-rate
  identity.  Use these before falling back to hand-proving the source records.
- The regular endpoint records
  `GN21NonsurgeRejectLongRegularEndpointData`,
  `GN21NonsurgeAcceptMiddleRegularEndpointData`,
  `GN21SurgeRejectShortRegularEndpointData`,
  `GN21SurgeRejectMiddleLoRegularEndpointData`,
  `GN21SurgeRejectMiddleHiRegularEndpointData`, and
  `GN21SurgeRejectMiddleRegularEndpointData` now derive the supported endpoint
  records from continuous density, source current-bounds data, support, and
  tail-integrability packages.
- `GN21RegularEndpointSharedSourceData` and the five
  `...RegularEndpointData.of_shared_source` constructors factor out shared
  source regularity.  Use this package before case-splitting on endpoint
  shapes; the shape cases should only provide cutoff-local density positivity,
  small-move/tail data, mass positivity of the other state, and source
  Lemma 9/10 current-bound data.
- The shape-specific `GN21RegularEndpointSharedSourceData.*_current_mass_pos`
  lemmas derive the moving state's positive current mass from shared support
  and the realized Lemma 5 shape, which is exactly the mass input needed by
  the accept-all tightening constructors.
- `GN21RegularEndpointSharedSourceData.nonsurge_scaled_time_pos`,
  `surge_scaled_time_pos`, `nonsurge_exit_weight_pos`,
  `surge_exit_weight_pos`, and
  `surge_fixed_switch_term_pos_for_nonsurge_bounds` discharge routine
  fixed-state time/exit positivity for the shared-source endpoint builders.
- The five `...RegularEndpointData.of_shared_source_and_acceptAll_tightening`
  constructors are the preferred endpoint builders: they compose shared
  source regularity, shape-derived current mass, accept-all moving-state
  tightening, and fixed-state reward-rate data into the regular endpoint
  records consumed by Theorem 4.
- The non-surge endpoint cases now also have
  `GN21NonsurgeRejectLongRegularEndpointData.of_shared_source_and_theorem3_fixed_transfer`
  and
  `GN21NonsurgeAcceptMiddleRegularEndpointData.of_shared_source_and_theorem3_fixed_transfer`.
  These consume `Theorem3AcceptAllStructuredParameterData` directly and use
  the Lemma 10 fixed-state transfer, so the caller supplies a fixed-state
  cross-ratio condition instead of pre-built current-fixed Lemma 10 bounds.
- The surge endpoint cases likewise have
  `GN21SurgeRejectShortRegularEndpointData.of_shared_source_and_theorem3_fixed_transfer`,
  `GN21SurgeRejectMiddleLoRegularEndpointData.of_shared_source_and_theorem3_fixed_transfer`,
  and
  `GN21SurgeRejectMiddleHiRegularEndpointData.of_shared_source_and_theorem3_fixed_transfer`.
  These use the Lemma 9 fixed-state transfer and therefore expose both
  cross-ratio directions, plus the usual surge accept-all positive-measure
  input for `Q_2 > lambda_21`.
- The Theorem 3 fixed-transfer local data records now state the fixed-state
  structured-price accounting equation, not a pre-expanded scaled-earning
  reward-rate identity.  The adapter expands this with
  `paper_remark2_structured_scaled_earning_algebra` and shared accept-all
  integrability restricted to the current feasible policy.
- Fixed-state transfer is now named algebraically.  Lemma 10 has
  `lemma10StructuredBounds_of_fixed_state_expansion` and the measured wrapper
  `lemma10StructuredBounds_of_acceptAll_fixed_state_measured_expansion`,
  which reduce accept-all fixed-state transfer to the cross-ratio condition
  `T_acceptAll * Q_current <= T_current * Q_acceptAll`.  Lemma 9 has
  `lemma9StructuredBounds_of_fixed_state_expansion`; its lower and upper
  comparisons require opposite cross-ratio directions, exposing that this
  side cannot be discharged by one-sided monotonicity alone.
- `Theorem3AcceptAllStructuredParameterData.of_evidence` should be used as
  soon as a constructed-price endpoint receives
  `theorem3AcceptAllStructuredParameterEvidence`; it names the two ratios,
  accept-all Lemma 9/10 bounds, and accounting identities used by the endpoint
  builders.  When a surge endpoint needs the constructed positive-ratio witness,
  use `theorem3AcceptAllStructuredPositiveParameterEvidence` and
  `Theorem3AcceptAllStructuredPositiveParameterData.of_evidence`; the positive
  fixed-transfer wrapper preserves that witness through the Theorem 3
  strict-local route.
- `Theorem4AllMeasurableAllowedPolicyFormsCertificate` and
  `Theorem4MeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsCertificate`
  remain useful older targets because they avoid duplicating Lemma 5 replacement
  measurability work: the continuous proof only needs to classify every
  measurable optimum into the allowed policy forms, and the regular endpoint
  fields supply the realized endpoint moves.  If the source proof instead
  produces all-measurable Lemma 5 replacement data, it feeds this target through
  `Theorem4AllMeasurableAllowedPolicyFormsCertificate.of_shape_replacements`.
- For the fixed-transfer route, the lightest compiled fixed-state adapter is
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_cutoff_bounds_source_assumptions`:
  it derives the constructed parameter data, surge-ratio positivity,
  all-measurable Lemma 5 replacement certificates, allowed policy-form
  classification, density positivity, state-level current mass, fixed-state
  pointwise comparisons, fixed-state reward-rate accounting, and the older
  no-mass endpoint certificate internally.  The source proof now supplies
  ordinary allowed Lemma 5 replacement cases, nondegenerate non-surge cutoffs
  for the reject-long/accept-middle fixed-state forms, common fixed-state
  complement pointwise equality and reward-rate facts for each state, and
  ordinary surge cutoff bounds.  The branch-specific policy-form fixed-state
  packages, moving cutoff choice, and surge tail integrability are derived
  internally.  This is stronger than the paper currently gives for
  non-accept-all fixed-state branches, so it is no longer the primary closure
  target.
- If the fixed other state already accepts all trips, use the
  `...PositiveCutoffLocalData.of_other_acceptAll` constructors.  They derive
  the cross-ratio inequalities by equality, derive positive fixed-state mass
  from shared support and accept-all mass positivity, and use the Theorem 3
  accept-all accounting identities for the fixed-state accounting equation.
- If the fixed other state is non-accept-all, use
  `gn21FixedStateCross_le_union_of_increment_ratio_ge` or
  `gn21FixedStateCross_ge_union_of_increment_ratio_le` to reduce the needed
  cross-ratio direction to an increment ratio inequality on the trips added
  when passing from the current fixed-state policy to accept-all.
- The pointwise versions
  `gn21FixedStateCross_le_acceptAll_of_complement_pointwise_increment_ratio_ge`
  and
  `gn21FixedStateCross_ge_acceptAll_of_complement_pointwise_increment_ratio_le`
  now discharge those increment inequalities from pointwise rejected-complement
  comparisons.  The shared-source helpers
  `GN21RegularEndpointSharedSourceData.*_fixed_cross_*_of_complement_pointwise`
  add the accept-all/current integrability automatically, and the
  `...PositiveCutoffLocalData.of_fixed_complement_pointwise` constructors feed
  the resulting cross-ratio facts straight into the fixed-transfer local
  endpoint records.
- The fixed-state accounting equation in those local records can now be
  supplied as a measured reward-rate identity via
  `GN21RegularEndpointSharedSourceData.nonsurge_fixed_accounting_of_reward_rate`
  or
  `GN21RegularEndpointSharedSourceData.surge_fixed_accounting_of_reward_rate`;
  the helpers expand structured CTMC prices with Remark 2 and shared
  accept-all integrability restricted to the current feasible policy.  The
  `...PositiveCutoffLocalData.of_fixed_complement_pointwise_reward_rate`
  constructors combine the pointwise fixed-complement route with this
  reward-rate accounting route.
- The fixed-state-equality derived-tail cutoff-bounds source theorem asks for
  ordinary all-measurable allowed Lemma 5 replacement data and a
  `Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailCutoffBoundsLocalEndpointCertificate`;
  the adapter chooses the upper reject-middle cutoff from `0 ≤ lo < hi`,
  derives positive tails from shared accept-all integrability,
  derives the uniform-tail package from positive tails plus continuous
  finite-interval product calculus, chooses fixed-state branches from allowed
  policy forms, builds surge moving endpoint data from the uniform tail package
  and cutoff choices,
  and then derives the fixed-state-separated certificate, the no-mass endpoint
  certificate, the mass-separated endpoint certificate, the older pointwise
  certificate, positive-cutoff endpoint data, fixed-state cross-ratios, and
  fixed-state accounting internally.  The
  shared-source helpers
  `GN21RegularEndpointSharedSourceData.surge_current_mass_pos_of_allowed_policy_form`
  and
  `GN21RegularEndpointSharedSourceData.nonsurge_current_mass_pos_of_allowed_policy_form`
  derive the two state-level mass fields from allowed policy forms, accept-all
  mass, and nondegenerate non-surge cutoffs.  The local constructors ending in
  `PointwiseRewardRateNoMassLocalData.of_fixed_complement_pointwise_eq` turn a
  fixed-state pointwise equality into the one-sided non-surge comparison or the
  two-sided surge comparisons.  The no-mass constructors ending in
  `of_other_acceptAll` discharge the fixed-state pointwise and reward-rate
  fields directly in accept-all fixed-state branches.  If the fixed-state
  target reward/equality facts are available, target the reusable common
  packages
  `GN21SurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassEqData` and
  `GN21NonsurgeFixedStateTheorem3FixedTransferPointwiseRewardRateNoMassEqData`
  once per optimal policy; Lean maps them to the branch-specific policy-form
  packages as needed.  If the source proof produces
  all-optimal allowed policy forms directly instead, use the sibling wrapper
  `paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_policy_forms_fixed_state_by_policy_form_uniform_tail_source_assumptions`.
- The feasible endpoint wrappers now mirror the raw endpoint wrappers:
  `...nonsurge_feasible...reject_long...`,
  `...nonsurge_feasible...accept_middle...`,
  `...surge_feasible...tail...`,
  `...surge_feasible...reject_middle_lo...`, and
  `...surge_feasible...reject_middle_hi...`.
- The source certificate should now target
  `Theorem4MeasurableEndpointCurrentBoundsRegularAllowedPolicyFormsCertificate`
  through a repaired current-bounds interface, rather than adding more
  fixed-state target-reward wrappers.

## What Would Fully Close The Paper

The paper is closed once Lean proves a source theorem of this form:

```lean
theorem paper_theorem3_measured_structured_measurable_ic_prices_of_continuous_source_assumptions
    (...) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21
```

where the final assumptions are standard continuous-measure regularity and the
paper's Lemma 9/10 inequalities, not any prepackaged local-improvement or
replacement certificate.
