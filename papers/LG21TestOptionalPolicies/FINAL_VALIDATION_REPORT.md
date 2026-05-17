# Final Validation Report: Test-optional Policies

## Verdict

Conditionally verified under the paper-facing Lean models in
`LG21TestOptionalPolicies`.

All named definitions and results have compiling Lean endpoints.  The observed
access section is closed: Lemma 4.1, Propositions 4.2--4.3, Definition 6, and
Theorem 4.4 have source-model or source-law wrappers in `PaperInterface.lean`.
Section 3 has paper-facing endpoints for both regimes of Theorem 3.1 and
Theorem 3.2, but they are intentionally marked conditional: the wrappers expose
the concrete Gaussian/affine/event-share source surfaces and equilibrium
shape assumptions used to formalize the paper's proof, rather than an
unconditional theorem over every possible estimation policy.

## Source Checked

- Paper: *Test-optional Policies: Overcoming Strategic Behavior and
  Informational Gaps*
- Authors: Zhi Liu and Nikhil Garg
- Local source text: `source.txt`
- Version note: arXiv:2107.08922 / EAAMO 2021 version.

## Named-Result Inventory

| Source result | Text-cache line | Audit declaration |
|---|---:|---|
| Definition 1, equilibrium | 279 | `audit_definition1_source_equilibrium` |
| Definition 2, latent-skill fairness | 336 | `audit_definition2_latent_skill_fair` |
| Definition 3, observable fairness | 346 | `audit_definition3_observably_fair` |
| Definition 4, demographic fairness | 360 | `audit_definition4_demographically_fair` |
| Definition 5, test-blank policies | 370 | `audit_definition5_test_blank` |
| Theorem 3.1, strategic withholding | 424, 829 | `audit_theorem3_1_section3_optional_reporting`, `audit_theorem3_1_section3_report_required` |
| Theorem 3.2, fairness impossibility | 455, 1614 | `audit_theorem3_2_section3_optional_reporting_fairness_impossibility`, `audit_theorem3_2_section3_report_required_fairness_impossibility` |
| Lemma 4.1, strategy-proofness | 492, 1784 | `audit_lemma4_1_observed_access_strategy_proofness` |
| Proposition 4.2, latent-skill unfairness | 550, 2318 | `audit_proposition4_2_base_indexed_posterior_surface` |
| Proposition 4.3, observable/demographic unfairness | 561, 2417 | `audit_proposition4_3_base_mixed_extra_signal_surface` |
| Definition 6, re-sampling policy | 585 | `audit_definition6_resampling_policy_observable_kernel` |
| Theorem 4.4, re-sampling fairness | 610, 2509 | `audit_theorem4_4_resampling_policy` |

## Cross-Artifact Checks

- Paper-facing Lean: `PaperInterface.lean` exposes the compact statement
  surface. `PostPaperAudit.lean` imports it and gives source-numbered aliases
  for the named definitions and theorem endpoints.
- README: every named paper item has a status row. The Section 3 rows are
  marked `conditional`; Section 4 and resampling rows are marked `formalized`.
- DAG: Theorem 3.1 and Theorem 3.2 are `dag_conditional`; the source-model,
  observed-access, and resampling nodes are closed result/model nodes.
- Build target: `lake build LG21TestOptionalPolicies.PaperInterface` succeeds.

## Proof-Strategy Deviations

- Theorem 3.1 is formalized through explicit optional-reporting and
  report-required source surfaces. The Lean endpoints expose the mixture
  fraction bounds, positive Gaussian/affine slope hypotheses, and concrete
  law surfaces needed by the cutoff and unfairness arguments.
- Theorem 3.2 is formalized through explicit event-or-blank source surfaces.
  The final aliases state the paper's hidden-access implication and no-relevance
  readings, while the concrete routes expose the positive event-share or
  already-test-blank case split used by the unraveling proof.
- The resampling policy is formalized in a finite conditional-kernel form:
  access and no-access estimate laws are both pushforwards of the same
  conditional test-score law, and demographic fairness follows by mixing over
  the shared base-profile law.

## Remaining Assumptions

- Theorem 3.1 is not yet an unconditional theorem over an arbitrary Bayesian
  optimal policy object. The strongest endpoints are the Section 3
  optional/report-required aliases over concrete Gaussian and affine source
  surfaces.
- Theorem 3.2 is not yet an unconditional theorem over an arbitrary estimation
  policy. The strongest endpoints are the Section 3 optional/report-required
  aliases over concrete constant-latent event-share surfaces, plus matching
  no-relevance aliases.
- A stricter skill-dependent conditional-kernel route is optional only if the
  target is broadened beyond the current concrete law surfaces.

## Verification Checks

- `lake build LG21TestOptionalPolicies.PaperInterface` passed.
- `lake build LG21TestOptionalPolicies.PostPaperAudit` passed after rerunning
  past a transient shared-cache missing-`.olean` race.
- `lake build LG21TestOptionalPolicies` passed.
- `latexmk -pdf DependencyDAG.tex` in this folder reported the DAG PDF
  up to date.
- `git diff --check` passed for the status update that introduced the current
  front-door LG21 summary.
