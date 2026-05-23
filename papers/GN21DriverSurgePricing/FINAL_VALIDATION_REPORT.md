# Final Validation Report: Driver Surge Pricing

## Verdict

Complete at the paper-facing source surfaces in `GN21DriverSurgePricing`.

The main denominator-valid continuous/CTMC source results are represented by
direct statement endpoints in `PaperInterface.lean`, with source-numbered audit
aliases in `PostPaperAudit.lean` and the theorem ledger in `README.md`.
Theorem 3 has both the denominator-valid positive-mass source endpoint and a
compiled full feasible-measurable endpoint through the source-ordered feasible
sequential Lemma 9/10 current-bounds route.  The separate zero-mass-dominance
lift remains available as an optional stronger bridge, and Lean records a
concrete obstruction showing why that certificate is not automatic for the
current real-valued reward totalization.

## Source checked

- Paper: *Driver Surge Pricing*
- Authors: Nikhil Garg and Hamid Nazerzadeh
- Local source: `source.pdf`
- Local text cache: `source.txt`
- Version note: arXiv v4, dated March 9, 2021; Management Science publication
  DOI `10.1287/mnsc.2021.4058`.

## Paper interface

The compact dashboard-facing `PaperInterface.lean` exposes `review_*` wrappers
for the source definitions and named results.  The larger historical
`PaperInterface.*` alias layer remains importable through `InterfaceAliases.lean`
for compatibility with older notes and `PostPaperAudit.lean`.

- `PaperInterface.review_definition_single_state_ic`
- `PaperInterface.review_definition_dynamic_ic`
- `PaperInterface.review_definition_threshold_policy`
- `PaperInterface.review_section2_single_state_renewal_reward_iid_bridge`
- `PaperInterface.review_definition_dynamic_defined_reward`
- `PaperInterface.review_lemma1_measured_dynamic_reward_decomposition`
- `PaperInterface.review_lemma2_switch_probability_formula`
- `PaperInterface.review_lemma3_measured_time_fraction_formula`
- `PaperInterface.review_lemma4_single_state_threshold_uniqueness`
- `PaperInterface.review_lemma5_fixed_response_policy_form`
- `PaperInterface.review_lemma6_upper_endpoint_derivative_formula`
- `PaperInterface.review_lemma7_affine_positive_additive_response_quasi_convex`
- `PaperInterface.review_lemma8_affine_negative_additive_response_quasi_concave`
- `PaperInterface.review_lemma9_surge_derivative_positive_of_acceptAll_bounds`
- `PaperInterface.review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds`
- `PaperInterface.review_proposition3_1_affine_single_state_ic`
- `PaperInterface.review_theorem1_single_state_threshold_best_response`
- `PaperInterface.review_theorem2_multiplicative_policy_shape_ae`
- `PaperInterface.review_theorem2_multiplicative_measured_not_ic_explicit_atomic`
- `PaperInterface.review_theorem2_multiplicative_profitable_deviations_both_states`
- `PaperInterface.review_theorem2_multiplicative_positive_finite_cutoff_deviations_both_states`
- `PaperInterface.review_theorem2_multiplicative_measured_not_ic_both_states`
- `PaperInterface.review_theorem3_feasibility_threshold`
- `PaperInterface.review_theorem3_positive_mass_source`
- `PaperInterface.review_theorem3_positive_response`
- `PaperInterface.review_theorem3_positive_fixed_response_normalized`
- `PaperInterface.review_theorem3_defined_reward_ic_of_positive_mass`
- `PaperInterface.review_theorem3_defined_reward_source`
- `PaperInterface.review_theorem3_feasible_sequential_current_bounds_source_data`
- `PaperInterface.review_theorem3_feasible_sequential_current_bounds_source_data_statement`
- `PaperInterface.review_theorem3_source_with_zero_mass_dominance`
- `PaperInterface.review_theorem3_zero_mass_totalization_obstruction`
- `PaperInterface.review_theorem3_zero_mass_totalization_obstruction_state_rates`
- `PaperInterface.review_theorem3_zero_mass_dominance_impossible_of_profitable_zero_mass`
- `PaperInterface.review_theorem4_structural_policy_representatives`
- `PaperInterface.review_theorem4_acceptAll_ae_unique_of_current_bounds_source`

## Dashboard source-text overrides

These entries supply paper text for source items whose PDF text extraction is
not caught by the numbered-statement parser because of line breaks, unnumbered
definitions, or appendix remark formatting.

- `PaperInterface.review_definition_single_state_ic`: In the single-state model, a policy is a measurable set of positive trip lengths accepted by the driver. Pricing is incentive compatible when accepting every job request is optimal for lifetime average earnings.
- `PaperInterface.review_definition_dynamic_ic`: In the dynamic model, a policy is a pair of statewise trip-length acceptance sets. Pricing is incentive compatible when the all-trips policy is optimal in both states.
- `PaperInterface.review_definition_threshold_policy`: The paper writes the single-state threshold policy as the set of trips whose payment-per-time is at least a nonnegative constant.
- `PaperInterface.review_definition_dynamic_defined_reward`: Appendix D's state reward rates use accepted-trip probability/time denominators; this Lean interface records the positive-mass domain where those reward rates are defined.
- `PaperInterface.review_section2_single_state_renewal_reward_iid_bridge`: Section 2.2 identifies the single-state model as a renewal-reward process and states that lifetime hourly earnings equal expected renewal-cycle earnings divided by expected renewal-cycle length with probability one.
- `PaperInterface.review_theorem1_single_state_threshold_best_response`: Theorem 1. With a single state, for each payment function there exists a nonnegative threshold constant such that accepting trips with payment-per-time at least that constant is optimal.
- `PaperInterface.review_proposition3_1_affine_single_state_ic`: Proposition 3.1. With a single state, affine pricing of the form w(tau) = m tau + a is incentive compatible if 0 <= a <= m / lambda.
- `PaperInterface.review_remark1_switch_probability_per_time_strictAntiOn`: Remark 1 includes the claim that q_{i->j}(u) / u is strictly decreasing in u, together with continuity and derivative-sign consequences.
- `PaperInterface.review_remark3_switch_probability_per_time_tendsto_at_zero`: Remark 3. The limit of q_{i->j}(u) / u as u tends to zero is lambda_{i->j}.
- `PaperInterface.review_remark4_switch_time_minus_switch_probability_nonneg`: Remark 4. lambda_{i->j} T_i - Q_i is nonnegative and is maximized by the accept-all policy; Q_i is also nonnegative and maximized by accepting all trips.

## Named-result inventory

| Source item | Text-cache line | Audit declaration | Status |
|---|---:|---|---|
| Section 2.2 driver policy and IC definitions | 264 | `audit_section2_single_state_ic`, `audit_section2_dynamic_ic` | complete |
| Section 2.2 renewal-reward bridge | 271 | `audit_section2_single_state_renewal_reward_iid_bridge` | complete |
| Theorem 1 | 498, 2530 | `audit_theorem1_single_state_threshold_best_response` | complete |
| Proposition 3.1 | 2759 | `audit_proposition3_1_affine_single_state_ic` | complete |
| Lemma 1 | 324, 3032 | `audit_lemma1_measured_dynamic_reward_decomposition` | complete |
| Lemma 2 | 657, 3000 | `audit_lemma2_switch_probability_formula` | complete |
| Lemma 3 | 671, 3054 | `audit_lemma3_measured_time_fraction_formula` | complete |
| Lemma 4 | 2841 | `audit_lemma4_single_state_threshold_uniqueness` | complete |
| Lemma 5 | 3343 | `audit_lemma5_fixed_response_policy_form` | complete at the a.e. fixed-response source surface used downstream |
| Lemma 6 | 3724, 4105 | `audit_lemma6_upper_endpoint_derivative_formula` | complete |
| Remarks 1, 3, 4 | 3747, 3793, 3799 | `audit_remark1_switch_probability_per_time_strictAntiOn`, `audit_remark3_switch_probability_per_time_tendsto_at_zero`, `audit_remark4_switch_time_minus_switch_probability_nonneg` | complete |
| Lemmas 7-8 | 3773, 3775 | `audit_lemma7_affine_positive_additive_response_quasi_convex`, `audit_lemma8_affine_negative_additive_response_quasi_concave` | complete |
| Lemmas 9-10 | 3809, 3834 | `audit_lemma9_surge_derivative_positive_of_acceptAll_bounds`, `audit_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds` | complete |
| Theorem 2 | 560 | `audit_theorem2_multiplicative_policy_shape_ae`, `audit_theorem2_multiplicative_measured_not_ic_explicit_atomic`, `audit_theorem2_multiplicative_measured_profitable_deviations_both_states`, `audit_theorem2_multiplicative_measured_profitable_positive_finite_cutoff_deviations_both_states`, `audit_theorem2_multiplicative_measured_not_ic_both_states` | complete for the structural handoff, explicit measured non-IC instance, and a single atomic instance with profitable positive-finite-cutoff deviations in both states |
| Theorem 4 | 3859 | `audit_theorem4_structural_policy_representatives` | complete at the measure-theoretic structural surface |
| Theorem 3 | 704, 3944 | `audit_theorem3_positive_mass_source`, `audit_theorem3_positive_response_source`, `audit_theorem3_positive_fixed_response_source`, `audit_theorem3_feasible_sequential_current_bounds_source_data`, `audit_theorem3_source_with_zero_mass_dominance` | complete through existential structured-price endpoints for the positive-response/fixed-response proof line, the positive-mass source endpoint, and the full feasible sequential current-bounds source-data endpoint; zero-mass dominance remains an optional bridge route |

## Deliberate model conventions and proof deviations

- Trip policies are sets of positive real trip lengths.  Measurability and
  a.e. equality are represented measure-theoretically.
- The stochastic Section 2.2, Lemma 1, and Lemma 3 statements use explicit IID
  cycle models and mathlib strong-law wrappers instead of opaque limit
  certificates.
- The single-state Theorem 1 proof allows atoms at threshold boundaries by
  proving one-sided dominated-convergence limits, rather than assuming boundary
  mass is zero.
- Theorem 3 has source-facing existential structured-price endpoints exposed as
  `PaperInterface.theorem3_positive_response` and
  `PaperInterface.theorem3_positive_fixed_response_normalized`: under the
  paper's normalized-mass ratio assumptions and the Lemma 5 positive-response
  or fixed-response source records, Lean constructs prices of the form
  `m_i tau + z_i q_{i->j}(tau)`, proves measurable IC, and proves accept-all is
  a.e. unique.  It also has a denominator-valid positive-mass source endpoint
  and a full feasible-measurable source-data endpoint exposed as
  `PaperInterface.theorem3_feasible_sequential_current_bounds_source_data`.
  Lean also exposes `PaperInterface.theorem3_defined_reward_ic_of_positive_mass`,
  a partial-reward view where zero-mass denominator failures have no reward
  value rather than a totalized real quotient value.
  A separate all-feasible bridge through
  `DynamicZeroMassStrictDominanceCertificate` is also exposed as
  `PaperInterface.theorem3_source_with_zero_mass_dominance`.
- The current real-valued CTMC reward totalization is intentionally audited by
  `PaperInterface.theorem3_zero_mass_totalization_obstruction_state_rates` and
  `PaperInterface.theorem3_zero_mass_dominance_impossible_of_profitable_zero_mass`,
  which show the overbroad all-feasible zero-mass lift cannot be discharged
  automatically.

## Cross-artifact checks

- `PaperInterface.lean` exposes the named paper definitions and theorem
  statements needed for human review.
- `PostPaperAudit.lean` imports the paper interface and gives source-numbered
  audit aliases for the final endpoints above.
- `README.md` and `DependencyDAG.tex` distinguish the closed positive-mass and
  feasible sequential current-bounds Theorem 3 routes from the optional
  zero-mass-dominance lift.
- The paper root module imports `PostPaperAudit.lean`.

## Verification commands

These checks passed after the latest audit updates:

```bash
lake build GN21DriverSurgePricing.PostPaperAudit
lake build GN21DriverSurgePricing.PaperInterface
lake build GN21DriverSurgePricing
lake build GN21DriverSurgePricing.DomainBridge
latexmk -pdf -halt-on-error DependencyDAG.tex
wc -l papers/GN21DriverSurgePricing/PaperInterface.lean
rg -c '^(noncomputable\s+|private\s+|protected\s+)*(theorem|lemma|def|abbrev) ' papers/GN21DriverSurgePricing/PaperInterface.lean
python3 scripts/review_dashboard.py --paper GN21DriverSurgePricing --precheck
git diff --check -- HumanStartHere.lean papers/GN21DriverSurgePricing
rg -n --glob "*.lean" "\bsorry\b|\badmit\b|axiom|by\s*omega" papers/GN21DriverSurgePricing
```

The dashboard precheck reports `0/39 reviewed` with no stale or mismatch rows;
the remaining action is human review, not Lean formalization work.
