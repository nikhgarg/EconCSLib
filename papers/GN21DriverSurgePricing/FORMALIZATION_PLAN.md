# GN21 Formalization Plan

Last updated: 2026-05-23

## Current State

- `PaperInterface.lean` exposes a compact review surface for central
  single-state source claims, the named CTMC lemmas, Theorems 2--4, and the
  current Theorem 3 source route.
- `PostPaperAudit.lean` is now the importable source-numbered endpoint ledger.
  `FINAL_VALIDATION_REPORT.md` records the named-result inventory, proof-route
  deviations, validation commands, and the exact positive-mass/zero-mass
  boundary for Theorem 3.
- `MainTheorems.lean` remains the large proof-facing ledger for the continuous
  and dynamic driver-surge development.  Active Lemma 5 and Theorem 3 route
  adapters now live in `Lemma5Frontier.lean` and `Theorem3Frontier.lean` so
  future proof attempts have narrower build targets.
- `DomainBridge.lean` now contains the source-faithful positive-mass Theorem 3
  a.e.-uniqueness endpoint
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions`,
  exposed as `PaperInterface.theorem3_positive_mass_source`.  It also exposes
  the full feasible-measurable bridge
  `PaperInterface.theorem3_source_with_zero_mass_dominance`, which adds exactly
  the explicit zero-mass strict-dominance certificate needed outside the
  denominator-valid source domain.
- `Theorem3SplitCurrentBounds.lean` now routes the sequential Lemma 9 then
  Lemma 10 a.e.-uniqueness proof through local measured reward-rate records.
  The feasible sequential surge reward-rate wrapper still reuses the existing
  source-data path for weak feasible IC, but its uniqueness half now constructs
  the sequential optimal reward-rate certificate directly rather than
  round-tripping through scaled source data.
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
- Treat the current interface as a curated starter surface; the Theorem 3
  positive-mass source theorem is the current denominator-valid paper endpoint,
  while full feasible-measurable lifting needs an explicit zero-mass dominance
  condition through `PaperInterface.theorem3_source_with_zero_mass_dominance`
  or a revised reward interface.
- Add more paper-facing interface rows only when the corresponding source claim
  has a stable Lean statement.

## Next Work

- Decide whether final status should be positive-mass/nondegenerate source
  closure, or whether to introduce an extended-real/partial reward interface
  for zero-mass policies.
- If staying on the paper's denominator-valid source domain, refresh the
  dashboard/cache around `PaperInterface.theorem3_positive_mass_source` and the
  audit endpoints in `PostPaperAudit.lean`.
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
