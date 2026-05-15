# GN21 Next-Agent Handoff

## Scope

Stay on `papers/GN21DriverSurgePricing`.  The current target is to close the
Driver Surge Pricing Theorem 3 IC route, not to audit other papers.

## Build State

As of this handoff, `lake build GN21DriverSurgePricing` passes after the newest
Lemma 9 envelope/slack source-boundary reduction and the current payment
nonnegativity derivation.  Re-run it before and after any edits.

Useful checks:

```bash
lake build GN21DriverSurgePricing
latexmk -pdf DependencyDAG.tex   # from papers/GN21DriverSurgePricing
git diff --check -- papers/GN21DriverSurgePricing skills/econcs-formalizer
```

## Important Conclusion

Do not try to finish Lemma 9 by proving a universal arbitrary-policy bound
`r1_current <= R1`.  That is not the invariant used by the source proof and can
be false for arbitrary current non-surge policies.

The paper's usable argument is the Theorem 3 surge-side slack paragraph:
state 2 can support any admissible payment ratio by choosing the surge
multiplier/intercept with enough slack.  The Lean route is:

```lean
r1_current <= Rmax
z_2 < current_Lemma9_upper * (m_2 - Rmax)
```

together with either current Lemma 9 lower-endpoint nonpositivity or, more
faithfully, exact lower interval slack.  The compiled constructors that package
these routes are:

```lean
GN21SurgeLemma9AcceptAllAggregateRewardRateData.exists_of_reward_envelope_current_lower_upper_slack
GN21SurgeLemma9AcceptAllAggregateRewardRateData.exists_of_reward_envelope_current_interval_slack
```

## Current Best Frontier

The newest source-facing endpoint is:

```lean
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_final_sign_data_assumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_current_interval_slack_final_sign_data_assumptions
```

It proves the positive-mass measurable Theorem 3 IC conclusion by choosing the
small-surge-slack prices directly from measured accept-all primitives, moving
surge to accept-all first, then using Lemma 10 only after surge is fixed at
accept-all.  Compared with the signed-envelope wrapper, callers no longer
provide data for every positive-parameter candidate; they provide the scalar
`Rmax,U` slack package and the current-policy Lemma 9 lower/uniform-upper
facts.  It still does not require either fixed-state cross-ratio comparison for
the surge move and does not ask for `R1_current <= R1`.  The interval variant
is now the preferred frontier when the current lower endpoint may be positive:
it asks for the selected-price inequality
`lower_current * (m_2-r1_current) < z_2` instead of trying to prove
`lower_current <= 0`.

The key new infrastructure is:

```lean
lemma9StructuredBounds_of_target_ratio_effective_ratio_le_current_lower_fixed_upper
GN21SurgeLemma9AcceptAllAggregateRewardRateData.of_target_ratio_reward_le_current_lower_fixed_upper
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentLowerRewardBoundFixedUpperNoRatioDataAssumptions
singleStateTripPayment_nonneg_of_pointwise_nonneg
gn21StateCycleTime_pos_of_mass_pos
gn21MeasuredStateRewardRate_nonneg_of_pointwise_payment_nonneg
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentLowerRewardBoundFixedUpperPaymentNonnegDataAssumptions
theorem3CurrentNonsurgePayment_nonneg_of_acceptAllLemma10
theorem3NonsurgeAfterSurgeAggregate_ge_of_acceptAllLemma10
theorem3SurgeAggregate_ge_of_currentLowerEnvelopeSlack
theorem3SurgeAggregate_ge_of_currentLowerSignedEnvelopeSlack
exists_effectiveRatio_lt_upperRatio_of_reward_le_envelope_interval_slack
theorem3SurgeAggregate_ge_of_currentIntervalEnvelopeSlack
theorem3SurgeAggregate_ge_of_currentSignedIntervalEnvelopeSlack
lemma9StructuredUpper_gt_uniform_of_switch_gap_pos
lemma9StructuredUpperUniformBound_pos
theorem3SurgeSlack_of_uniform_upper_lt_current
theorem3SurgeRatio_exists_small_slack_at_R2
theorem3SurgeRatio_exists_small_slack
theorem3SurgeParameters_exist_small_slack_of_current_lower_nonpos
theorem3StructuredParameters_exist_of_ratio_and_small_surge_slack
theorem3StructuredParameters_exist_of_ratio_and_small_surge_mass_affine_slack
paper_theorem3_measured_ctmc_structured_prices_exist_and_positive_mass_measurable_ic_of_ratio_and_sequential_accept_all_weak_reward_of_small_surge_slack
paper_theorem3_measured_ctmc_structured_prices_exist_and_positive_mass_measurable_ic_of_ratio_and_sequential_accept_all_weak_reward_of_small_surge_mass_affine_slack
theorem3MassAffineRmax_zero_ratio_pos_of_arrival_z_le_R2
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentLowerEnvelopeSlackDataAssumptions
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentLowerSignedEnvelopeSlackDataAssumptions
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentMassAffineIntervalSlackDataAssumptions
Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeSlackDataAssumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_data_assumptions
Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeSlackCurrentLowerDataAssumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_current_lower_data_assumptions
Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeSlackFinalSignDataAssumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_final_sign_data_assumptions
Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeCurrentIntervalSlackFinalSignDataAssumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_current_interval_slack_final_sign_data_assumptions
Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeMassAffineCurrentIntervalSlackFinalSignDataAssumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_interval_slack_final_sign_data_assumptions
```

## Remaining Mathematical Work

The newest source wrapper is:

```lean
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_final_sign_data_assumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_current_interval_slack_final_sign_data_assumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_interval_slack_final_sign_data_assumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_interval_slack_final_sign_arrival_bound_data_assumptions
```

The endpoint/allowed-policy pivot now has a compiled hnot-aware selection
interface:

```lean
Theorem4MeasurableEndpointCurrentBoundsSelectionUnlessCertificate
theorem4MeasuredAggregateFeasibleStrictLocalImprovementCertificate_of_endpoint_current_bounds_selection_unless
paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_selection_unless
Theorem3AcceptAllMeasurableEndpointCurrentBoundsSelectionUnlessSourceAssumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_endpoint_current_bounds_selection_unless_source_assumptions
```

Use it when endpoint witnesses need the actual `¬ acceptsAllTrips (ρ i)`
hypothesis before proving cutoff nondegeneracy.  The supporting
shape-normalization lemmas are:

```lean
acceptsAllTrips_of_rejectsShortTrips_of_nonpos
cutoff_pos_of_rejectsShortTrips_of_not_acceptsAll
acceptsAllTrips_of_rejectsMiddleTrips_of_hi_nonpos
hi_pos_of_rejectsMiddleTrips_of_not_acceptsAll
rejectsShortTrips_of_rejectsMiddleTrips_of_lo_nonpos
```

There is also a direct hnot-aware statewise route for cases where a degenerate
syntactic shape should be rerouted before choosing endpoint data:

```lean
Theorem4MeasurableShapeReplacementStatewiseImprovementUnlessCertificate
paper_theorem4_measurable_accept_all_unique_optimal_of_shape_replacement_statewise_improvements_unless
Theorem3AcceptAllMeasurableShapeReplacementStatewiseImprovementUnlessSourceAssumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_shape_replacement_statewise_improvements_unless_positive_source_assumptions
```

The lower-sign wrapper asks for:

- a signed reward-envelope choice:
  `(z_0 <= 0 and Rmax = R2)` or
  `(0 <= z_0 and Rmax = R2 + z_0 * switch12)`, specialized to the
  accept-all non-surge ratio;
- the zero-ratio numerator condition
  `0 < R2*T2 - Rmax*(T2 - 1)`;
- for every feasible measurable positive-mass policy `rho`, the current
  Lemma 9 lower-endpoint sign condition:
  `lowerNumerator * upperDenominator <= 0`.

The preferred mass-affine interval wrapper asks for a sharper sign-selected
`Rmax`, accept-all mass-one/finite support for state 1, and accept-all
final-sign certificate.  The newest arrival-bound variant asks for
`arrival_0*z_0 <= R2` and derives the old zero-ratio numerator internally.  It
replaces the policy-dependent current lower-sign field by:

```lean
current_lower *
  (m_2 - gn21MeasuredStateRewardRate ... current_non_surge_policy) < z_2
```

for the selected small-surge prices.  It derives the current upper slack
internally from the uniform `U` bound and positive-mass Remark 4 facts.

Do not keep pushing this as an arbitrary-policy sequential obligation without
first adding a policy-shape restriction.  A CTMC-generated two-atom numerical
probe suggests that all-policy selected-price lower slack can fail even with
`C < rho < 1`: with `arrival0=arrival1=5`,
`switch12=switch21=1/2`, state-0 lengths `{1,6}` and state-1 lengths `{1,5}`
with equal masses, and `rho=(C+1)/2≈0.951787`, the accept-all Lemma 9 interval
is approximately `(5.568,12.699)`, but the current state-0 short-trip subset
has lower endpoint about `3.065` while the maximum effective current ratio
over target ratios in that accept-all interval is only about `2.255`.  This is
not a formal Lean counterexample, but it is strong guidance: either use the
endpoint/allowed-policy Theorem 4 route, or prove the lower slack only for the
policy shapes that can actually be optimal.

The wrapper itself derives:

- positivity of `m_2 - Rmax`;
- accept-all and current Lemma 9 lower-endpoint nonpositivity;
- accept-all Lemma 9 upper positivity;
- a positive uniform lower bound `U` for current Lemma 9 upper endpoints;
- `U < current_Lemma9_upper` for every positive-mass current policy;
- surge-side slack
  `z_2 < current_Lemma9_upper * (m_2 - Rmax)`.

`0 <= r1_current`, the reward-rate identity, and `r1_current <= Rmax` are no
longer source fields.  Lean defines the current reward rate internally,
derives current non-surge pointwise payment nonnegativity from Lemma 10, and
derives the reward-rate envelope from the signed structured-price bound.  The
mass-affine branch improves that envelope from `m_0+z_0*switch12` to
`max m_0 (arrival_0*z_0)`.  The main compiled bridges are:

```lean
theorem3CurrentNonsurgePayment_nonneg_of_acceptAllLemma10
theorem3SurgeAggregate_ge_of_currentLowerSignedEnvelopeSlack
theorem3SurgeAggregate_ge_of_currentSignedIntervalEnvelopeSlack
theorem3SurgeAggregate_ge_of_currentMassAffineSignedIntervalEnvelopeSlack
theorem3MassAffineRmax_zero_ratio_pos_of_arrival_z_le_R2
```

The source-facing pointwise-nonnegativity field has already been removed by
the derived-payment wrapper.
Do not treat `r1_current <= R1` as a universal arbitrary-policy fact.  The
source proof's usable argument is the Theorem 3 surge-side slack paragraph:
choose the surge parameters so `z_2/(m_2-r1_current)` remains inside Lemma 9's
current interval for any current reward below a verified envelope.

Lean now has a compiled constructor for this route:

```lean
GN21SurgeLemma9AcceptAllAggregateRewardRateData.exists_of_reward_envelope_current_lower_upper_slack
GN21SurgeLemma9AcceptAllAggregateRewardRateData.exists_of_reward_envelope_current_interval_slack
```

The interval constructor combines `r1_current <= Rmax`,
`lower_current*(m_2-r1_current) < z_2`, and
`z_2 < current_upper*(m_2-Rmax)` to build the effective Lemma 9 ratio and the
full aggregate reward-rate data.

## Why This Route

Lemma 9's lower and upper fixed-state transfers pull in opposite cross-ratio
directions.  Requiring both directions effectively forces equality of the
current fixed non-surge exit-weight/time ratio with accept-all, which is too
strong for arbitrary feasible policies unless a pointwise equality has already
been proved.  The new route uses the source Lemma 9 final-sign logic directly
for the current fixed state to replace the lower cross comparison.

## Next Concrete Step

Start from `CLOSEOUT_PROOF_PLAN.txt`; it records why the all-policy sequential
Lemma 9 lower-slack route is suspect.  The next proof work should use the
endpoint/allowed-policy route, not another attempt to prove the selected lower
slack for arbitrary feasible positive-mass policies.

The fixed-transfer regular endpoint packages are now threaded through
`Theorem4MeasurableEndpointCurrentBoundsSelectionUnlessCertificate`; see
`Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularAllowedPolicyFormsCertificate.to_endpoint_current_bounds_selection_unless`
and the two `..._via_selection_unless` Theorem 3 wrappers.

The next useful Lean target is to weaken the source assumptions using the
direct hnot-aware statewise interface.  In the surge reject-middle branch, split
on `lo <= 0`: use
`rejectsShortTrips_of_rejectsMiddleTrips_of_lo_nonpos` and
`hi_pos_of_rejectsMiddleTrips_of_not_acceptsAll` to route to the short-tail
improvement; otherwise keep the upper-cutoff reject-middle endpoint route.

Keep the mass-affine sequential wrapper as a documented fallback/source
boundary:

```lean
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_interval_slack_final_sign_arrival_bound_data_assumptions
```

Do not try to prove the mass-affine positive-`z0` branch from only loose scalar
feasibility facts; `arrival_0*z_0 <= R2` is the current explicit extra
condition for that wrapper.

## Documentation Map

- `README.md`: theorem inventory and status.
- `CLOSEOUT_PROOF_PLAN.txt`: shortest remaining source proof plan for Theorem 3.
- `CONTINUOUS_PROOF_PLAN.md`: strategic route and reusable infrastructure.
- `LEMMA9_10_REWARD_RATE_AUDIT.md`: why target reward rates cannot be confused
  with current fixed-state rates, and why the sequential route is preferred.
- `DependencyDAG.tex`: graphical paper-stage status.
