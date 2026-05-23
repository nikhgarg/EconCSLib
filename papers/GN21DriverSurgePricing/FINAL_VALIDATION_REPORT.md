# Final Validation Report: Driver Surge Pricing

## Verdict

Conditionally complete under the paper-facing Lean models in
`GN21DriverSurgePricing`.

The main denominator-valid continuous/CTMC source results are represented by
direct statement endpoints in `PaperInterface.lean`, with source-numbered audit
aliases in `PostPaperAudit.lean` and the theorem ledger in `README.md`.
Theorem 3 has both the positive-mass source endpoint and a compiled full
feasible-measurable endpoint through the source-ordered feasible sequential
Lemma 9/10 current-bounds route.  The separate zero-mass-dominance lift remains
available as an optional bridge, and Lean records a concrete obstruction
showing why that certificate is not automatic for the current real-valued
reward totalization.

## Source checked

- Paper: *Driver Surge Pricing*
- Authors: Nikhil Garg and Hamid Nazerzadeh
- Local source: `source.pdf`
- Local text cache: `source.txt`
- Version note: arXiv v4, dated March 9, 2021; Management Science publication
  DOI `10.1287/mnsc.2021.4058`.

## Paper interface

- `PaperInterface.definition_single_state_ic`
- `PaperInterface.definition_dynamic_ic`
- `PaperInterface.definition_threshold_policy`
- `PaperInterface.section2_single_state_renewal_reward_iid_bridge`
- `PaperInterface.lemma1_measured_dynamic_reward_decomposition`
- `PaperInterface.lemma2_switch_probability_formula`
- `PaperInterface.lemma3_measured_time_fraction_formula`
- `PaperInterface.lemma4_single_state_threshold_uniqueness`
- `PaperInterface.lemma5_fixed_response_policy_form`
- `PaperInterface.lemma6_upper_endpoint_derivative_formula`
- `PaperInterface.lemma7_affine_positive_additive_response_quasi_convex`
- `PaperInterface.lemma8_affine_negative_additive_response_quasi_concave`
- `PaperInterface.lemma9_surge_derivative_positive_of_acceptAll_bounds`
- `PaperInterface.lemma10_nonsurge_derivative_positive_of_acceptAll_bounds`
- `PaperInterface.theorem2_multiplicative_measured_not_ic_explicit_atomic`
- `PaperInterface.theorem3_positive_mass_source`
- `PaperInterface.theorem3_feasible_sequential_current_bounds_source_data`
- `PaperInterface.theorem3_source_with_zero_mass_dominance`
- `PaperInterface.theorem3_zero_mass_totalization_obstruction_state_rates`
- `PaperInterface.theorem3_zero_mass_dominance_impossible_of_profitable_zero_mass`
- `PaperInterface.theorem4_structural_policy_representatives_of_gn21_bracket_source_data`

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
| Theorem 2 | 560 | `audit_theorem2_multiplicative_policy_shape_ae`, `audit_theorem2_multiplicative_measured_not_ic_explicit_atomic` | complete for the structural handoff and explicit measured non-IC instance |
| Theorem 4 | 3859 | `audit_theorem4_structural_policy_representatives` | complete at the measure-theoretic structural surface |
| Theorem 3 | 704, 3944 | `audit_theorem3_positive_mass_source`, `audit_theorem3_feasible_sequential_current_bounds_source_data`, `audit_theorem3_source_with_zero_mass_dominance` | complete through the positive-mass source endpoint and the full feasible sequential current-bounds source-data endpoint; zero-mass dominance remains an optional bridge route |

## Deliberate model conventions and proof deviations

- Trip policies are sets of positive real trip lengths.  Measurability and
  a.e. equality are represented measure-theoretically.
- The stochastic Section 2.2, Lemma 1, and Lemma 3 statements use explicit IID
  cycle models and mathlib strong-law wrappers instead of opaque limit
  certificates.
- The single-state Theorem 1 proof allows atoms at threshold boundaries by
  proving one-sided dominated-convergence limits, rather than assuming boundary
  mass is zero.
- Theorem 3 has a denominator-valid positive-mass source endpoint and a full
  feasible-measurable source-data endpoint exposed as
  `PaperInterface.theorem3_feasible_sequential_current_bounds_source_data`.
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
git diff --check -- papers/GN21DriverSurgePricing skills/econcs-formalizer/references/proof-foundations-probability.md
rg -n "\bsorry\b|\badmit\b|axiom|by\s*omega" papers/GN21DriverSurgePricing
```
