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

together with current Lemma 9 lower-endpoint nonpositivity.  The compiled
constructor that packages this is:

```lean
GN21SurgeLemma9AcceptAllAggregateRewardRateData.exists_of_reward_envelope_current_lower_upper_slack
```

## Current Best Frontier

The newest source-facing endpoint is:

```lean
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_current_lower_signed_envelope_slack_data_assumptions
```

It proves the positive-mass measurable Theorem 3 IC conclusion by moving surge
to accept-all first, then using Lemma 10 only after surge is fixed at
accept-all.  Compared with the earlier final-sign/fixed-transfer route, it no
longer requires either fixed-state cross-ratio comparison for the surge move,
and it no longer asks for `R1_current <= R1`.

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
lemma9StructuredUpper_gt_uniform_of_switch_gap_pos
lemma9StructuredUpperUniformBound_pos
theorem3SurgeSlack_of_uniform_upper_lt_current
theorem3SurgeRatio_exists_small_slack_at_R2
theorem3SurgeRatio_exists_small_slack
theorem3SurgeParameters_exist_small_slack_of_current_lower_nonpos
theorem3StructuredParameters_exist_of_ratio_and_small_surge_slack
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentLowerEnvelopeSlackDataAssumptions
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentLowerSignedEnvelopeSlackDataAssumptions
```

## Remaining Mathematical Work

For every feasible measurable positive-mass policy `rho`, the newest Lemma 9
source field asks for:

- a signed reward-envelope choice:
  `(z_0 <= 0 and Rmax = m_0)` or
  `(0 <= z_0 and Rmax = m_0 + z_0 * switch12)`;
- positivity of `m_2 - Rmax`;
- current Lemma 9 lower-endpoint nonpositivity with fixed non-surge `T,Q` and
  moving surge accept-all `Tbar,Qbar`;
- surge-side slack
  `z_2 < current_Lemma9_upper * (m_2 - Rmax)`.

`0 <= r1_current`, the reward-rate identity, and `r1_current <= Rmax` are no
longer source fields.  Lean defines the current reward rate internally,
derives current non-surge pointwise payment nonnegativity from Lemma 10, and
derives the reward-rate envelope from the signed structured-price bound.  The
main compiled bridges are:

```lean
theorem3CurrentNonsurgePayment_nonneg_of_acceptAllLemma10
theorem3SurgeAggregate_ge_of_currentLowerSignedEnvelopeSlack
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
```

It combines `r1_current <= Rmax`, current lower-endpoint nonpositivity, and
`z_2 < current_upper * (m_2 - Rmax)` to build the effective Lemma 9 ratio and
the full aggregate reward-rate data.

## Why This Route

Lemma 9's lower and upper fixed-state transfers pull in opposite cross-ratio
directions.  Requiring both directions effectively forces equality of the
current fixed non-surge exit-weight/time ratio with accept-all, which is too
strong for arbitrary feasible policies unless a pointwise equality has already
been proved.  The new route uses the source Lemma 9 final-sign logic directly
for the current fixed state to replace the lower cross comparison.

## Next Concrete Step

Start from `CLOSEOUT_PROOF_PLAN.txt`; it records the corrected route and the
distinction between the easy `0 <= r1_current` proof, the reward-envelope
bound, and the surge-side slack proof.

The scalar small-ratio surge slack is now compiled.  The most useful packaged
constructor is:

```lean
theorem3StructuredParameters_exist_of_ratio_and_small_surge_slack
```

It returns Theorem 3 structured parameters together with positive parameter
evidence, the sign-selected envelope `Rmax`, `0 < m_2 - Rmax`, and
`z_2 < U * (m_2 - Rmax)`.  The generic scalar side condition still to discharge
in the measured Theorem 3 route is:

```lean
0 < R2 * T2 - Rmax * (T2 - 1)
```

for the chosen sign envelope.  For the `Rmax = R2` branch this is just
`0 < R2`.  For the `Rmax = R2 + z_0 * switch12` branch, prove it from the
Theorem 3 non-surge construction/feasibility assumptions, or record the exact
extra source condition if the paper is implicitly using a regime restriction.

The helper `lemma9StructuredUpper_gt_uniform_of_switch_gap_pos` gives a
policy-uniform positive lower bound on the current Lemma 9 upper endpoint from
`Q_current < switch12 * T_current`; use
`theorem3SurgeSlack_of_uniform_upper_lt_current` to transfer the constructed
uniform slack to the actual current upper endpoint.

Also prove a current-state version of the Lemma 9 final-sign/nonpositive
lower endpoint under the regular source hypotheses.  The useful scalar lemma
already exists:

```lean
lemma9StructuredLower_nonpos_of_final_signs
```

A likely next bridge should specialize it to:

```lean
lemma9StructuredLower
  (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
  (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
  (gn21AcceptAllScaledStateTime (mu 1) (arrival 1))
  (gn21AcceptAllExitWeightIntegral (mu 1) (arrival 1) switch21 switch12)
  switch21 <= 0
```

using current fixed-state denominator positivity and the source final-sign
left-nonpositive inequality.

If that stalls, fall back to the older wrappers documented in
`LEMMA9_10_REWARD_RATE_AUDIT.md`, especially the final-sign/no-ratio route and
the pointwise fixed-transfer route.

## Documentation Map

- `README.md`: theorem inventory and status.
- `CLOSEOUT_PROOF_PLAN.txt`: shortest remaining source proof plan for Theorem 3.
- `CONTINUOUS_PROOF_PLAN.md`: strategic route and reusable infrastructure.
- `LEMMA9_10_REWARD_RATE_AUDIT.md`: why target reward rates cannot be confused
  with current fixed-state rates, and why the sequential route is preferred.
- `DependencyDAG.tex`: graphical paper-stage status.
