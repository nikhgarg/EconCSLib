# GN21 Source Audit

This is the tracked source-vs-Lean audit for Garg--Nazerzadeh,
*Driver Surge Pricing*.  It complements the local dashboard trace under
`.review_traces/`, which is intentionally ignored by Git.  The audit was done
against an ignored local source text cache, `PaperInterface.lean`,
`PostPaperAudit.lean`, and the compiled GN21 modules.

This is an agent source audit, not a human signoff. It should not be counted as
dashboard human review.

## Verdict

All 24 `PaperInterface.lean` review rows match the paper-facing source
statements at the Lean formalization surface currently intended for GN21.

Theorem 3's denominator-valid reward domain is now explicit in the
paper-facing row.  The compact endpoint uses the paper's defined reward-rate
semantics, where the accepted-trip mass/time denominators in Appendix D are
defined.  Optional all-feasible totalized zero-mass lifts and obstruction lemmas
are documented separately in `FINAL_VALIDATION_REPORT.md`, `README.md`, and
`PostPaperAudit.lean`; they are not counted as the paper-facing Theorem 3
statement.

## Review Rows

| Paper item | Source lines | Lean review declaration | Audit result |
|---|---:|---|---|
| Section 2.2 single-state IC definition | 264 | `review_definition_single_state_ic` | Matches the paper's accept-all optimality definition for the single-state measurable reward predicate. |
| Section 2.2 dynamic IC definition | 264 | `review_definition_dynamic_ic` | Matches the paper's statewise accept-all dynamic optimality definition. |
| Threshold policy notation | 498 | `review_definition_threshold_policy` | Matches Theorem 1's threshold-rate form: accept trips whose payment-per-time exceeds a nonnegative cutoff. |
| Dynamic defined-reward domain | 324, 3032 | `review_definition_dynamic_defined_reward` | Records the denominator-valid state reward-rate domain needed by the Appendix D reward formulas. |
| Section 2.2 renewal-reward bridge | 271 | `review_section2_single_state_renewal_reward_iid_bridge` | Matches the renewal-reward statement; Lean states the IID almost-sure quotient convergence. |
| Proposition 3.1 affine single-state IC | 2759 | `review_proposition3_1_affine_single_state_ic` | Matches `0 <= a <= m / lambda` plus Lean's explicit measure, integrability, and positivity side conditions. |
| Theorem 1 threshold best response | 498, 2530 | `review_theorem1_single_state_threshold_best_response` | Matches the source threshold best-response theorem, with Lean making measurability/integrability/positive-payment hypotheses explicit. |
| Lemma 4 single-state uniqueness | 2841 | `review_lemma4_single_state_threshold_uniqueness` | Matches uniqueness up to zero-measure sets and threshold-boundary modifications. |
| Lemma 1 dynamic reward decomposition | 324, 3032 | `review_lemma1_measured_dynamic_reward_decomposition` | Matches the decomposition into state time fractions and state reward rates. |
| Lemma 2 CTMC switch probability | 657, 3000 | `review_lemma2_switch_probability_formula` | Matches the two-state CTMC closed form for `q_i->j(s)`. |
| Lemma 3 time fraction | 671, 3054 | `review_lemma3_measured_time_fraction_formula` | Matches the measured time-fraction formula, with Lean exposing nonzero denominator obligations. |
| Remark 1 `q(u)/u` monotonicity | 3747 | `review_remark1_switch_probability_per_time_strictAntiOn` | Matches the strict decrease of switch probability per unit time on positive times. |
| Remark 3 zero-time limit | 3793 | `review_remark3_switch_probability_per_time_tendsto_at_zero` | Matches `q_i->j(u) / u -> lambda_i->j` as `u -> 0`. |
| Remark 4 nonnegativity | 3799 | `review_remark4_switch_time_minus_switch_probability_nonneg` | Matches the nonnegativity behind `lambda_i->j T_i - Q_i >= 0`, stated pointwise for `lambda*t - q(t)`. |
| Lemma 5 fixed-response form | 3343 | `review_lemma5_fixed_response_policy_form` | Matches the a.e. measurable fixed-response optimizer surface used downstream by Theorems 2 and 4. |
| Lemma 6 derivative formula | 3786 | `review_lemma6_upper_endpoint_derivative_formula` | Matches the derivative-sign formula; Lean proves the derivative identity without a positive endpoint-density premise and makes positive density conditional for strict sign transfer. |
| Lemma 7 positive-additive affine response | 3773 | `review_lemma7_affine_positive_additive_response_quasi_convex` | Matches strict quasi-convexity under `m, a > 0` and the paper's sign condition on `R_j - R_i`. |
| Lemma 8 negative-additive affine response | 3775 | `review_lemma8_affine_negative_additive_response_quasi_concave` | Matches strict quasi-concavity under `m > 0`, `a < 0`, and the paper's sign condition on `R_j - R_i`. |
| Lemma 9 surge derivative positivity | 3809 | `review_lemma9_surge_derivative_positive_of_acceptAll_bounds` | Matches derivative positivity under the source accept-all/current-bound inequalities. |
| Lemma 10 non-surge derivative positivity | 3834 | `review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds` | Matches derivative positivity under the source accept-all/current-bound inequalities. |
| Theorem 2 multiplicative policy shape | 560 | `review_theorem2_multiplicative_policy_shape_ae` | Matches the multiplicative optimal-policy shape clause, with Theorem 4/Lemma 5 source assumptions explicit in Lean. |
| Theorem 2 multiplicative non-IC witness | 560 | `review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states` | Matches the existence of positive finite cutoff settings where multiplicative pricing is not IC in either state, via a concrete measured atomic witness. |
| Theorem 4 structural representatives | 3859 | `review_theorem4_structural_policy_representatives` | Matches the Appendix D structural theorem up to null feasible-trip sets. |
| Theorem 3 structured IC pricing | 717 | `review_theorem3_defined_reward_source_statement` | Matches the fully incentive-compatible accept-all clause of Theorem 3; Lean exposes the denominator-valid defined-reward source domain rather than hiding zero-denominator totalization inside a wrapper. |

## Checks

The latest validation pass used:

```bash
lake build GN21DriverSurgePricing.PaperInterface GN21DriverSurgePricing.PostPaperAudit
lake build GN21DriverSurgePricing
python3 scripts/review_dashboard.py --paper GN21DriverSurgePricing --precheck
rg -n --glob "*.lean" "\bsorry\b|\badmit\b|axiom|by\s*omega" papers/GN21DriverSurgePricing
git diff --check -- papers/GN21DriverSurgePricing
```

Dashboard human-review status after clearing agent-generated local trace rows:
`0/24 reviewed`, `24 unreviewed`, `0 stale`, `0 mismatch`. This is expected
until a human reviewer saves dashboard rows.
