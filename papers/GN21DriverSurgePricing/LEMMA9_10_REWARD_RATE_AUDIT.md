# Lemma 9/10 Reward-Rate Audit

This note records the algebraic distinction that matters for closing the GN21
Theorem 3 proof in a source-faithful way.

## Notation Split

The source uses `R1` and `R2` in two different roles.

- In Theorem 3, `R1*` and `R2*` are target accept-all earning rates.
- In Lemma 9, `R1` is the current fixed non-surge state's reward rate under
  the arbitrary fixed policy `sigma1`.
- In Lemma 10, `R2` is the current fixed surge state's reward rate under the
  arbitrary fixed policy `sigma2`.

Those quantities agree automatically only when the fixed state already accepts
all trips, or when a separate reward-rate equality theorem has been proved for
the fixed non-accept-all policy.

## Lemma 9

Lemma 9 fixes the non-surge policy and moves the surge policy.  Its algebraic
kernel is already formalized with the current fixed reward rate separated:

```lean
paper_lemma9_structured_derivative_kernel_pos_of_current_bounds
```

The exact ratio condition is

```text
z2 = ratio9 * (m2 - r1_current)
```

and the bounds are the Lemma 9 bounds for the current fixed-state primitives.
The Theorem 3 construction instead supplies the target accounting identity

```text
z2 = ratio9_target * (m2 - R1*)
```

so a source-faithful non-accept-all fixed-state branch must either prove
`r1_current = R1*` or prove that the effective current ratio
`z2 / (m2 - r1_current)` satisfies the Lemma 9 bounds.

## Lemma 10

Lemma 10 fixes the surge policy and moves the non-surge policy.  In the paper
derivation the moving non-surge slope equals the current fixed surge reward:

```text
m1 = r2_current
z1 = ratio10 * r2_current
```

Theorem 3 constructs instead

```text
m1 = R2*
z1 = ratio10_target * R2*
```

For the actual derivative kernel with moving slope `m` and current fixed reward
`r`, Lean now records the exact split:

```lean
lemma10StructuredStaticTerm_eq_ratio_reward_split
lemma10StructuredLinearEndpoint_eq_ratio_reward_split
```

In paper notation, with `z = ratio * m`,

```text
static =
  Q2*m*(1 - ratio*(Q1 - lambda12)) + Q1*T2*(m - r)

linear_endpoint =
  m*(T2*lambda12 + Q2
    + ratio*(Q2*(lambda12*T1 - Q1)
      + lambda12*(T2*lambda12 + Q2)))
  + (m - r)*T2*(Q1 - lambda12*T1)
```

The source Lemma 10 inequalities prove positivity of the first terms when
`m = r`.  If `m != r`, the two slack terms pull in opposite directions under
the usual `lambda12*T1 - Q1 >= 0` condition.  Thus a simple one-sided reward
comparison is not enough to recover the paper proof for arbitrary non-accept-all
fixed surge policies; the proof needs either equality or explicit endpoint
slack.

## Compiled Lean Frontier

The reward-rate-separated Lemma 10 route is compiled as:

```lean
paper_lemma10_structured_derivative_kernel_pos_of_endpoint_terms
paper_lemma10_derivative_sign_kernel_pos_of_endpoint_terms
paper_lemma10_measured_derivative_sign_kernel_pos_of_endpoint_terms
gn21MeasuredAggregateRewardPrimitives_le_acceptAll_left_of_lemma10_endpoint_terms
lemma10StructuredStaticTerm_pos_of_ratio_reward_slack
lemma10StructuredLinearEndpoint_pos_of_ratio_reward_slack
paper_lemma10_structured_derivative_kernel_pos_of_ratio_reward_slack
GN21NonsurgeLemma10EndpointTermsAggregateData
Theorem4MeasuredAggregateStructuredEndpointTermsCurrentRateWeakCertificate
theorem3AcceptAllWeakRewardCertificate_of_structured_endpoint_terms_current_rates
paper_theorem3_measured_structured_ic_prices_of_structured_endpoint_terms_current_rate_source_assumptions
Theorem4MeasuredAggregateStructuredSequentialCurrentBoundsWeakCertificate
Theorem4MeasuredAggregateStructuredFeasibleSequentialCurrentBoundsWeakCertificate
theorem3AcceptAllSequentialWeakRewardCertificate_of_structured_sequential_current_bounds
theorem3AcceptAllFeasibleSequentialWeakRewardCertificate_of_structured_feasible_sequential_current_bounds
paper_theorem3_measured_structured_ic_prices_of_structured_sequential_current_bounds_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_current_bounds_source_assumptions
Theorem4MeasuredAggregateStructuredFeasibleSequentialCurrentBoundsSourceCertificate
paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_current_bounds_source_data_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_surge_source_data_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_surge_accounting_data_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_structured_feasible_sequential_surge_reward_rate_data_assumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_structured_positive_mass_feasible_sequential_surge_reward_rate_data_assumptions
paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_source_assumptions
paper_theorem3_measured_structured_measurable_ic_prices_of_source_assumptions
```

The endpoint-term theorems do not assume target fixed-state reward-rate
identities.  They ask directly for the two scalar endpoint inequalities that
are mathematically needed by the derivative proof, and the weak Theorem 3
wrapper lets each policy carry its own current fixed-state reward rates.

The sequential current-bounds theorems avoid the arbitrary fixed-surge Lemma 10
problem for the IC conclusion.  They prove the surge move first with Lemma 9
and the current fixed non-surge reward rate; after that, the non-surge move has
surge fixed at accept-all, so Lemma 10 can use the Theorem 3 target surge
accept-all rate.  The source-data wrapper derives the packed aggregate and
nondegeneracy fields from source-facing Lemma 9/10 data, accept-all
integrability, and positive accept-all mass.  The reduced surge-source wrapper
derives the Lemma 10 accept-all fixed-surge branch from Theorem 3 parameter
data, and the accounting/reward-rate wrappers reduce the remaining Lemma 9
fixed-state identity to the source accounting equation or measured reward-rate
statement.  The positive-mass wrapper restricts the policy domain to feasible
measurable policies with positive accepted mass in both states, which is the
domain where the source reward-rate denominators are defined.  On that route
the remaining local proof is only the Lemma 9 surge reward-rate move on the
positive-mass domain; the broad feasible-measurable wrapper keeps the explicit
positive-current-mass obligation for users who want the stronger domain.

## Closure Options

1. Use the sequential Theorem 3 route for IC.  This is the fastest
   source-faithful path: it needs Lemma 9 for the arbitrary current surge move
   on the positive-mass feasible domain, and Lean now discharges Lemma 10 in
   the accept-all fixed-surge branch.

2. Prove fixed-state reward-rate equality for every non-accept-all branch.
   This is the strongest route and is already supported by the fixed-state
   equality adapters, but it is not a consequence of the source text by itself.

3. Prove the Lemma 9 effective-ratio bounds and Lemma 10 endpoint slack
   inequalities for the actual current fixed-state reward rates.  This is the
   most source-faithful local repair.

4. Replace the statewise Lemma 9/10 transfer with a direct two-state aggregate
   comparison that avoids identifying current fixed-state rates with target
   rates.  This may be cleaner if the local slack inequalities are cumbersome.

The current fastest path is option 1.  The endpoint-term interface remains the
right backup for stronger simultaneous statewise statements.
