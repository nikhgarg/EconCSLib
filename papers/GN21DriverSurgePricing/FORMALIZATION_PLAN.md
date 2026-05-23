# GN21 Formalization Plan

Last updated: 2026-05-23

## Current State

- `PaperInterface.lean` exposes a compact review surface for central
  single-state source claims, the named CTMC lemmas, Theorems 2--4, and the
  current Theorem 3 source route.
- `PostPaperAudit.lean` is now the importable source-numbered endpoint ledger.
  `FINAL_VALIDATION_REPORT.md` records the named-result inventory, proof-route
  deviations, validation commands, the feasible sequential Theorem 3 endpoint,
  and the optional zero-mass bridge/obstruction boundary.
- `MainTheorems.lean` remains the large proof-facing ledger for the continuous
  and dynamic driver-surge development.  Active Lemma 5 and Theorem 3 route
  adapters now live in `Lemma5Frontier.lean` and `Theorem3Frontier.lean` so
  future proof attempts have narrower build targets.
- `DomainBridge.lean` now contains the source-faithful positive-mass Theorem 3
  a.e.-uniqueness endpoint
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions`,
  exposed as `PaperInterface.theorem3_positive_mass_source`.  It also exposes
  the optional full feasible-measurable bridge
  `PaperInterface.theorem3_source_with_zero_mass_dominance`, which adds exactly
  the explicit zero-mass strict-dominance certificate needed for that route,
  plus the state-rate and certificate-impossibility obstruction theorems that
  show this certificate is not automatic under the current totalized `ℝ`
  reward interface.  `PaperInterface.theorem3_defined_reward_ic_of_positive_mass`
  gives the partial-reward alternative where zero-mass denominator failures are
  left undefined.
- `Theorem3SplitCurrentBounds.lean` now routes the sequential Lemma 9 then
  Lemma 10 a.e.-uniqueness proof through local measured reward-rate records.
  The full feasible sequential current-bounds source-data route is exposed as
  `PaperInterface.theorem3_feasible_sequential_current_bounds_source_data` and
  proves the full `theorem3MeasuredStructuredMeasurableICAEUniqueConclusion`
  without using the zero-mass dominance certificate.
- `Lemma5Frontier.lean` now contains the compact Theorem 4 structural
  endpoints that turn allowed Lemma 5 replacement data, allowed Lemma 5 forms,
  or feasible a.e. representative forms into the paper's measurable-domain
  structural statement.  It also exposes the same a.e. representative
  statement from replacement data, fixed-response shape data, fixed-response
  policy-form data, frozen-state positive-affine policy-form data, GN21
  fixed-response source data, and raw GN21 bracket source data, so the
  source-shaped Theorem 4 route no longer needs a manual reconstruction layer.
  The dynamic-state positive-affine boundary is the preferred paper-proof path
  for the frozen-state Lemma 5 step: it converts dynamic optimality plus a
  positive affine continuation-objective identity directly into a.e. canonical
  representatives, avoiding the older exact strict-mass side condition.
  The raw bracket source data also now prove the Theorem 4-to-Theorem 2 a.e.
  shape handoff for one-threshold CTMC prices.  The remaining Theorem 4 work is
  the analytic construction of those positive-affine fixed-state objective
  identities and policy-form records for arbitrary measurable optima.
- The folder has active proof work; avoid broad rewrites while other agents are
  editing `MainTheorems.lean`.

## Review Plan

- Start human review with `PaperInterface.lean`; do not review the full
  `MainTheorems.lean` ledger directly.
- Treat the current interface as a curated starter surface.  Theorem 3's
  preferred full-measurable review endpoint is
  `PaperInterface.theorem3_feasible_sequential_current_bounds_source_data`;
  `PaperInterface.theorem3_positive_mass_source` and
  `PaperInterface.theorem3_source_with_zero_mass_dominance` are additional
  source-boundary and optional-bridge views.
- Add more paper-facing interface rows only when the corresponding source claim
  has a stable Lean statement.

## Next Work

- Refresh the dashboard/cache around `PaperInterface.lean` and the audit
  endpoints in `PostPaperAudit.lean`, now that the full feasible sequential
  Theorem 3 route is the preferred source-facing endpoint.
- Extend the partial reward interface only if a future paper needs more than
  the current theorem `PaperInterface.theorem3_defined_reward_ic_of_positive_mass`;
  it is no longer required to close the paper-facing Theorem 3 source-data
  endpoint.
- For Theorem 4, target
  `PaperInterface.theorem4_structural_policy_representatives_of_allowed_replacement_data`
  when following the paper's Lemma 5 replacement proof,
  `PaperInterface.theorem4_structural_policy_representatives_of_dynamic_state_positive_affine_policy_forms`
  when proving the paper's frozen-state continuation objective is a positive
  affine transform of a Lemma 5 marginal reward,
  `PaperInterface.theorem4_structural_policy_representatives_of_gn21_bracket_source_data`
  when following the paper proof at the raw Lemma 6 bracket level, or
  `PaperInterface.theorem4_structural_policy_representatives_of_feasible_ae_policy_forms`
  when proving the analytic Lemma 5 a.e.-form data directly.
