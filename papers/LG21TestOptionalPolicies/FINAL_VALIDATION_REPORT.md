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
| Theorem 3.1, strategic withholding | 424, 829 | `audit_theorem3_1_section3_optional_reporting`, `audit_theorem3_1_section3_report_required`, PMF certificate aliases `audit_theorem3_1_section3_optional_reporting_pmf` and `audit_theorem3_1_section3_report_required_pmf`, finite-event-share source routes `audit_theorem3_1_optional_reporting_event_share_source_route` and `audit_theorem3_1_report_required_event_share_source_route`, finite-event-share continuous-law certificates `audit_theorem3_1_optional_reporting_event_share_law_certificate` and `audit_theorem3_1_report_required_event_share_law_certificate`, plus Section 3 finite-event-share law routes `audit_theorem3_1_section3_optional_reporting_event_share_law_route` and `audit_theorem3_1_section3_report_required_event_share_law_route` |
| Theorem 3.2, fairness impossibility | 455, 1614 | `audit_theorem3_2_positive_event_or_blank_bridge`, share-language bridge `audit_theorem3_2_positive_event_share_or_blank_bridge`, premise conversion `audit_theorem3_2_no_positive_event_blank_of_zero_event_share_blank`, blank-on-zero-share constructor `audit_theorem3_2_blank_on_zero_event_share_constructor`, source event-or-blank certificate aliases `audit_theorem3_2_optional_reporting_source_event_or_blank_fairness_certificate` and `audit_theorem3_2_report_required_source_event_or_blank_fairness_certificate`, source zero-share certificate aliases `audit_theorem3_2_optional_reporting_source_zero_share_fairness_certificate` and `audit_theorem3_2_report_required_source_zero_share_fairness_certificate`, source implication aliases `audit_theorem3_2_optional_reporting_source_event_or_blank_fairness_implies_test_blank`, `audit_theorem3_2_optional_reporting_source_zero_share_fairness_implies_test_blank`, `audit_theorem3_2_report_required_source_event_or_blank_fairness_implies_test_blank`, and `audit_theorem3_2_report_required_source_zero_share_fairness_implies_test_blank`, source no-relevance aliases `audit_theorem3_2_optional_reporting_source_event_or_blank_no_test_relevance`, `audit_theorem3_2_optional_reporting_source_zero_share_no_test_relevance`, `audit_theorem3_2_report_required_source_event_or_blank_no_test_relevance`, and `audit_theorem3_2_report_required_source_zero_share_no_test_relevance`, concrete event-or-blank certificate aliases `audit_theorem3_2_optional_reporting_event_or_blank_fairness_certificate` and `audit_theorem3_2_report_required_event_or_blank_fairness_certificate`, blank-on-zero-share certificate aliases `audit_theorem3_2_optional_reporting_blank_on_zero_share_fairness_certificate` and `audit_theorem3_2_report_required_blank_on_zero_share_fairness_certificate`, `audit_theorem3_2_section3_optional_reporting_fairness_impossibility`, `audit_theorem3_2_section3_report_required_fairness_impossibility`, zero-share Section 3 aliases `audit_theorem3_2_section3_optional_reporting_zero_share_fairness_impossibility`, `audit_theorem3_2_section3_report_required_zero_share_fairness_impossibility`, `audit_theorem3_2_section3_optional_reporting_zero_share_no_test_relevance`, `audit_theorem3_2_section3_report_required_zero_share_no_test_relevance`, plus blank-on-zero-share aliases `audit_theorem3_2_section3_optional_reporting_blank_on_zero_share_fairness_impossibility`, `audit_theorem3_2_section3_report_required_blank_on_zero_share_fairness_impossibility`, `audit_theorem3_2_section3_optional_reporting_blank_on_zero_share_no_test_relevance`, and `audit_theorem3_2_section3_report_required_blank_on_zero_share_no_test_relevance` |
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
  Finite event-share helpers now include strict complement-mass bounds, so a
  positive-mass no-reporter/no-taker atom can discharge the `accessFraction < 1`
  premise when the mixture fraction is instantiated as a finite event share.
  Direct optional/report-required source wrappers now perform that finite
  event-share instantiation and derive `0 ≤ C < 1` internally.
- Theorem 3.2 is formalized through explicit event-or-blank source surfaces.
  The final aliases state the paper's hidden-access implication and no-relevance
  readings, while the concrete routes expose the positive event-share or
  already-test-blank case split used by the unraveling proof.  The bridge
  `paper_interface_theorem3_2_positive_event_or_blank_of_no_positive_event_blank`
  names the convention that a zero-positive-reporter/taker profile is already
  test-blank, so the final aliases no longer take the raw disjunction directly.
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
  implication and no-relevance aliases. The source-level zero-share variants
  state the paper's finite-share branch explicitly: zero reporter/taker event
  share implies the profile is already test-blank. The constructed
  blank-on-zero-share constant-latent surfaces discharge that branch by
  definition.
- A stricter skill-dependent conditional-kernel route is optional only if the
  target is broadened beyond the current concrete law surfaces.

## Verification Checks

- `lake build LG21TestOptionalPolicies.PaperInterface` passed.
- `lake build LG21TestOptionalPolicies.PostPaperAudit` passed after rerunning
  past a transient shared-cache missing-`.olean` race.
- `lake build LG21TestOptionalPolicies` passed.
- `latexmk -pdf DependencyDAG.tex` in this folder reported the DAG PDF
  up to date.
- `python3 scripts/audit_repository.py` was run from the repository root. The
  command still reports unrelated repo-wide cached-PDF/status issues in other
  paper folders, but after restoring this folder's ignored local `source.pdf`,
  it no longer reports LG21-specific errors or warnings.
- `git diff --check` passed.
