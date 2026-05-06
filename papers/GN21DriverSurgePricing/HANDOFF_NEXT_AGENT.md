# GN21 Next-Agent Handoff

## Scope

Stay on `papers/GN21DriverSurgePricing`.  The current target is to close the
Driver Surge Pricing Theorem 3 IC route, not to audit other papers.

## Build State

As of this handoff, `lake build GN21DriverSurgePricing` passes after the newest
Lemma 9 source-boundary reduction and the current reward-rate nonnegativity
wrapper.  Re-run it before and after any edits.

Useful checks:

```bash
lake build GN21DriverSurgePricing
latexmk -pdf DependencyDAG.tex   # from papers/GN21DriverSurgePricing
git diff --check -- papers/GN21DriverSurgePricing skills/econcs-formalizer
```

## Current Best Frontier

The newest source-facing endpoint is:

```lean
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_current_lower_reward_bound_fixed_upper_no_ratio_data_assumptions
```

The newest payment-nonnegative variant replaces the explicit
`0 <= r1_current` source field by pointwise nonnegative current non-surge
payments:

```lean
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_parameter_positive_mass_feasible_sequential_surge_current_lower_reward_bound_fixed_upper_payment_nonneg_data_assumptions
```

It proves the positive-mass measurable Theorem 3 IC conclusion by moving surge
to accept-all first, then using Lemma 10 only after surge is fixed at
accept-all.  Compared with the earlier final-sign/fixed-transfer route, it no
longer requires the lower fixed-state cross-ratio comparison.

The key new infrastructure is:

```lean
lemma9StructuredBounds_of_target_ratio_effective_ratio_le_current_lower_fixed_upper
GN21SurgeLemma9AcceptAllAggregateRewardRateData.of_target_ratio_reward_le_current_lower_fixed_upper
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentLowerRewardBoundFixedUpperNoRatioDataAssumptions
singleStateTripPayment_nonneg_of_pointwise_nonneg
gn21StateCycleTime_pos_of_mass_pos
gn21MeasuredStateRewardRate_nonneg_of_pointwise_payment_nonneg
Theorem3AcceptAllStructuredPositiveParameterPositiveMassFeasibleSequentialSurgeCurrentLowerRewardBoundFixedUpperPaymentNonnegDataAssumptions
```

## Remaining Mathematical Work

For every feasible measurable positive-mass policy `rho`, the remaining Lemma 9
source field at the original current-lower boundary asks for:

- a current non-surge reward rate `r1_current`;
- a verified envelope `r1_current <= Rmax` together with enough surge-ratio
  slack below the current Lemma 9 upper endpoint;
- `0 <= r1_current`;
- the measured reward-rate identity for state 0;
- current Lemma 9 lower-endpoint nonpositivity with fixed non-surge `T,Q` and
  moving surge accept-all `Tbar,Qbar`;
- the upper fixed-state cross comparison
  `T_acceptAll * Q_current <= T_current * Q_acceptAll`.

At the payment-nonnegative boundary, `0 <= r1_current` is no longer a source
field.  Supply pointwise nonnegative current non-surge payments on `rho 0`;
Lean derives the reward-rate nonnegativity from the measured Lemma 1 formula.
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

Then try to prove a current-state version of the Lemma 9 final-sign/nonpositive
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
