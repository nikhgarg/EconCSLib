# GN21 Formalization Plan

Last updated: 2026-05-23

## Current State

- Paper-facing closeout is complete.  The current source of truth is
  `FINAL_VALIDATION_REPORT.md`, then `PaperInterface.lean` and
  `PostPaperAudit.lean`.  Older plan files in this folder record proof-search
  history and optional strengthening paths; they are not required work for the
  named-paper closeout.
- `PaperInterface.lean` exposes a compact review surface for central
  single-state source claims, the named CTMC lemmas, Theorems 2--4, and the
  current Theorem 3 defined-reward source route.
- `PostPaperAudit.lean` is now the importable source-numbered endpoint ledger.
  `FINAL_VALIDATION_REPORT.md` records the named-result inventory, proof-route
  deviations, validation commands, the defined-reward Theorem 3 endpoint, and
  the optional zero-mass totalization bridge/obstruction boundary.
- `MainTheorems.lean` remains the large proof-facing ledger for the continuous
  and dynamic driver-surge development.  Active Lemma 5 and Theorem 3 route
  adapters now live in `Lemma5Frontier.lean` and `Theorem3Frontier.lean` so
  future proof attempts have narrower build targets.
- `DomainBridge.lean` now contains the source-faithful positive-mass Theorem 3
  a.e.-uniqueness endpoint
  `paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions`,
  exposed as `PaperInterface.theorem3_positive_mass_source`.  The compact
  paper-facing endpoint is `PaperInterface.theorem3_defined_reward_source`,
  where Appendix D reward-rate denominators are required to be defined.  The
  file also exposes the optional totalized feasible-measurable bridge
  `PaperInterface.theorem3_source_with_zero_mass_dominance`, which adds exactly
  the explicit zero-mass strict-dominance certificate needed for that route,
  plus the state-rate and certificate-impossibility obstruction theorems that
  show this certificate is not automatic under the current totalized `ℝ`
  reward interface.
- `Theorem3SplitCurrentBounds.lean` now routes the sequential Lemma 9 then
  Lemma 10 a.e.-uniqueness proof through local measured reward-rate records.
  That route feeds the defined-reward source endpoint; optional totalized
  wrappers are retained for audit/strengthening only.
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
  shape handoff for one-threshold CTMC prices.  Further analytic construction
  of positive-affine fixed-state objective identities and policy-form records
  would strengthen optional routes, but is not needed for the closed
  paper-facing endpoints.
- There is no active required proof seam in this folder.  In the shared
  worktree, still stage only GN21-owned files and avoid broad rewrites while
  other agents may be editing unrelated papers.

## Review Plan

- Start human review with `PaperInterface.lean`; do not review the full
  `MainTheorems.lean` ledger directly.
- Treat the current interface as a curated starter surface.  Theorem 3's
  preferred review endpoint is `PaperInterface.theorem3_defined_reward_source`;
  `PaperInterface.theorem3_positive_mass_source` and
  `PaperInterface.theorem3_source_with_zero_mass_dominance` are additional
  source-boundary and optional totalized-bridge views.
- Add more paper-facing interface rows only when the corresponding source claim
  has a stable Lean statement.

## Optional Follow-Up Work

- Refresh the dashboard/cache around `PaperInterface.lean` and the audit
  endpoints in `PostPaperAudit.lean` if the review UI needs regenerated data.
- Extend the defined-reward interface only if a future paper needs more than
  the current theorem `PaperInterface.theorem3_defined_reward_source`.
- For optional Theorem 4 strengthening, target
  `PaperInterface.theorem4_structural_policy_representatives_of_allowed_replacement_data`
  when following the paper's Lemma 5 replacement proof,
  `PaperInterface.theorem4_structural_policy_representatives_of_dynamic_state_positive_affine_policy_forms`
  when proving the paper's frozen-state continuation objective is a positive
  affine transform of a Lemma 5 marginal reward,
  `PaperInterface.theorem4_structural_policy_representatives_of_gn21_bracket_source_data`
  when following the paper proof at the raw Lemma 6 bracket level, or
  `PaperInterface.theorem4_structural_policy_representatives_of_feasible_ae_policy_forms`
  when proving the analytic Lemma 5 a.e.-form data directly.
