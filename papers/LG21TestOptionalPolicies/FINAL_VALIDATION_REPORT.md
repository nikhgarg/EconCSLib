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
| Definition 5, test-blank policies | 370 | `audit_definition5_test_blank`, no-positive/zero-share source-note aliases `audit_definition5_test_blank_of_no_positive_event_blank`, `audit_definition5_test_blank_of_zero_event_share_blank`, blank-on-zero constructor checks `audit_definition5_blank_on_zero_event_share_eq_base_of_zero_share`, `audit_definition5_blank_on_zero_event_share_eq_raw_of_nonzero_share`, and `audit_definition5_blank_on_zero_event_share_eq_raw_of_positive_event`, blank-on-zero raw no-relevance consequences `audit_definition5_blank_on_zero_event_share_no_raw_relevance_of_nonzero_share` and `audit_definition5_blank_on_zero_event_share_no_raw_relevance_of_positive_event`, blank-on-zero normalized-vs-raw no-relevance iff checks `audit_definition5_blank_on_zero_event_share_no_relevance_iff_raw_nonzero_share` and `audit_definition5_blank_on_zero_event_share_no_relevance_iff_raw_positive_event`, named observable-identity certificates `audit_definition5_observable_identity_certificate` and `audit_definition5_law_observable_identity_certificate`, and test-blank-to-observable-fair bridges `audit_definition5_implies_definition3_of_full_feature_base_only`, `audit_definition5_implies_definition3_law_of_full_feature_base_only`, `audit_definition5_implies_definition3_of_observable_identities`, and `audit_definition5_implies_definition3_law_of_observable_identities` |
| Theorem 3.1, strategic withholding | 424, 829 | `audit_theorem3_1_section3_optional_reporting`, `audit_theorem3_1_section3_report_required`, short finite-event-share Section 3 aliases `audit_theorem3_1_section3_optional_reporting_event_share` and `audit_theorem3_1_section3_report_required_event_share`, PMF certificate aliases `audit_theorem3_1_section3_optional_reporting_pmf` and `audit_theorem3_1_section3_report_required_pmf`, finite-event-share PMF routes `audit_theorem3_1_section3_optional_reporting_event_share_pmf_route`, `audit_theorem3_1_section3_report_required_event_share_pmf_route`, `audit_theorem3_1_section3_optional_reporting_event_share_pmf_every_equilibrium_route`, and `audit_theorem3_1_section3_report_required_event_share_pmf_every_equilibrium_route`, finite-event-share source routes `audit_theorem3_1_optional_reporting_event_share_source_route` and `audit_theorem3_1_report_required_event_share_source_route`, finite-event-share continuous-law certificates `audit_theorem3_1_optional_reporting_event_share_law_certificate` and `audit_theorem3_1_report_required_event_share_law_certificate`, long-form Section 3 finite-event-share law routes `audit_theorem3_1_section3_optional_reporting_event_share_law_route` and `audit_theorem3_1_section3_report_required_event_share_law_route`, full-support/not-all-acting Section 3 routes `audit_theorem3_1_section3_optional_reporting_event_share_full_support_not_all` and `audit_theorem3_1_section3_report_required_event_share_full_support_not_all`, plus reusable full-support event-share helpers `audit_event_share_complement_mass_of_full_support_not_all` and `audit_event_share_lt_one_of_full_support_not_all` |
| Theorem 3.2, fairness impossibility | 455, 1614 | `audit_theorem3_2_positive_event_or_blank_bridge`, share-language bridge `audit_theorem3_2_positive_event_share_or_blank_bridge`, premise conversion `audit_theorem3_2_no_positive_event_blank_of_zero_event_share_blank`, blank-on-zero-share constructor `audit_theorem3_2_blank_on_zero_event_share_constructor`, source event-or-blank certificate aliases `audit_theorem3_2_optional_reporting_source_event_or_blank_fairness_certificate` and `audit_theorem3_2_report_required_source_event_or_blank_fairness_certificate`, source zero-share certificate aliases `audit_theorem3_2_optional_reporting_source_zero_share_fairness_certificate` and `audit_theorem3_2_report_required_source_zero_share_fairness_certificate`, source implication aliases `audit_theorem3_2_optional_reporting_source_event_or_blank_fairness_implies_test_blank`, `audit_theorem3_2_optional_reporting_source_zero_share_fairness_implies_test_blank`, `audit_theorem3_2_report_required_source_event_or_blank_fairness_implies_test_blank`, and `audit_theorem3_2_report_required_source_zero_share_fairness_implies_test_blank`, source no-relevance aliases `audit_theorem3_2_optional_reporting_source_event_or_blank_no_test_relevance`, `audit_theorem3_2_optional_reporting_source_zero_share_no_test_relevance`, `audit_theorem3_2_report_required_source_event_or_blank_no_test_relevance`, and `audit_theorem3_2_report_required_source_zero_share_no_test_relevance`, concrete event-or-blank certificate aliases `audit_theorem3_2_optional_reporting_event_or_blank_fairness_certificate` and `audit_theorem3_2_report_required_event_or_blank_fairness_certificate`, blank-on-zero-share certificate aliases `audit_theorem3_2_optional_reporting_blank_on_zero_share_fairness_certificate` and `audit_theorem3_2_report_required_blank_on_zero_share_fairness_certificate`, positive-share no-relevance aliases `audit_theorem3_2_optional_reporting_positive_share_no_relevance` and `audit_theorem3_2_report_required_positive_share_no_relevance`, positive-share fairness/test-blank iff aliases `audit_theorem3_2_optional_reporting_positive_share_fairness_iff_test_blank` and `audit_theorem3_2_report_required_positive_share_fairness_iff_test_blank`, positive-share fairness/no-relevance iff aliases `audit_theorem3_2_optional_reporting_positive_share_fairness_iff_no_relevance` and `audit_theorem3_2_report_required_positive_share_fairness_iff_no_relevance`, `audit_theorem3_2_section3_optional_reporting_fairness_impossibility`, `audit_theorem3_2_section3_report_required_fairness_impossibility`, zero-share Section 3 aliases `audit_theorem3_2_section3_optional_reporting_zero_share_fairness_impossibility`, `audit_theorem3_2_section3_report_required_zero_share_fairness_impossibility`, `audit_theorem3_2_section3_optional_reporting_zero_share_no_test_relevance`, `audit_theorem3_2_section3_report_required_zero_share_no_test_relevance`, blank-on-zero-share aliases `audit_theorem3_2_section3_optional_reporting_blank_on_zero_share_fairness_impossibility`, `audit_theorem3_2_section3_report_required_blank_on_zero_share_fairness_impossibility`, `audit_theorem3_2_section3_optional_reporting_blank_on_zero_share_no_test_relevance`, `audit_theorem3_2_section3_report_required_blank_on_zero_share_no_test_relevance`, `audit_theorem3_2_section3_optional_reporting_blank_on_zero_share_no_raw_relevance`, `audit_theorem3_2_section3_report_required_blank_on_zero_share_no_raw_relevance`, `audit_theorem3_2_section3_optional_reporting_blank_on_zero_share_positive_event_no_raw_relevance`, `audit_theorem3_2_section3_report_required_blank_on_zero_share_positive_event_no_raw_relevance`, blank-on-zero fairness/raw-no-relevance iff aliases `audit_theorem3_2_section3_optional_reporting_blank_on_zero_share_fairness_iff_raw_nonzero_share`, `audit_theorem3_2_section3_optional_reporting_blank_on_zero_share_fairness_iff_raw_positive_event`, `audit_theorem3_2_section3_report_required_blank_on_zero_share_fairness_iff_raw_nonzero_share`, and `audit_theorem3_2_section3_report_required_blank_on_zero_share_fairness_iff_raw_positive_event`, PMF/law fairness-test-blank iff aliases `audit_theorem3_2_fairness_iff_test_blank_of_full_feature_base_only`, `audit_theorem3_2_observable_fair_iff_test_blank_of_full_feature_base_only`, `audit_theorem3_2_section3_fairness_iff_test_blank_of_full_feature_base_only`, `audit_theorem3_2_law_fairness_iff_test_blank_of_full_feature_base_only`, `audit_theorem3_2_law_observable_fair_iff_test_blank_of_full_feature_base_only`, and `audit_theorem3_2_section3_law_fairness_iff_test_blank_of_full_feature_base_only`, named observable-identity iff aliases `audit_theorem3_2_fairness_iff_test_blank_of_observable_identities`, `audit_theorem3_2_observable_fair_iff_test_blank_of_observable_identities`, `audit_theorem3_2_section3_fairness_iff_test_blank_of_observable_identities`, `audit_theorem3_2_law_fairness_iff_test_blank_of_observable_identities`, `audit_theorem3_2_law_observable_fair_iff_test_blank_of_observable_identities`, and `audit_theorem3_2_section3_law_fairness_iff_test_blank_of_observable_identities`, PMF/law fairness-no-relevance iff aliases `audit_theorem3_2_fairness_iff_no_test_relevance_of_full_feature_base_only`, `audit_theorem3_2_observable_fair_iff_no_test_relevance_of_full_feature_base_only`, `audit_theorem3_2_section3_fairness_iff_no_test_relevance_of_full_feature_base_only`, `audit_theorem3_2_law_fairness_iff_no_test_relevance_of_full_feature_base_only`, `audit_theorem3_2_law_observable_fair_iff_no_test_relevance_of_full_feature_base_only`, and `audit_theorem3_2_section3_law_fairness_iff_no_test_relevance_of_full_feature_base_only`, named observable-identity no-relevance aliases `audit_theorem3_2_fairness_iff_no_test_relevance_of_observable_identities`, `audit_theorem3_2_observable_fair_iff_no_test_relevance_of_observable_identities`, `audit_theorem3_2_section3_fairness_iff_no_test_relevance_of_observable_identities`, `audit_theorem3_2_law_fairness_iff_no_test_relevance_of_observable_identities`, `audit_theorem3_2_law_observable_fair_iff_no_test_relevance_of_observable_identities`, and `audit_theorem3_2_section3_law_fairness_iff_no_test_relevance_of_observable_identities`, mapped-actor full-support alias `audit_theorem3_2_report_required_mapped_actor_full_support`, plus contradiction-to-certificate aliases `audit_theorem3_2_fairness_certificate_of_not_latent_or_observable_fair` and `audit_theorem3_2_law_fairness_certificate_of_not_latent_or_observable_fair` |
| Lemma 4.1, strategy-proofness | 492, 1784 | `audit_lemma4_1_observed_access_strategy_proofness` |
| Proposition 4.2, latent-skill unfairness | 550, 2318 | `audit_proposition4_2_base_indexed_posterior_surface` |
| Proposition 4.3, observable/demographic unfairness | 561, 2417 | `audit_proposition4_3_base_mixed_extra_signal_surface` |
| Definition 6, re-sampling policy | 585 | `audit_definition6_resampling_policy_observable_kernel`, `audit_definition6_access_estimate_kernel_eq_map`, `audit_definition6_resampling_estimate_kernel_eq_map`, and `audit_definition6_access_resampling_kernel_eq` |
| Theorem 4.4, re-sampling fairness | 610, 2509 | `audit_theorem4_4_resampling_policy_observably_fair`, `audit_theorem4_4_resampling_policy_demographically_fair`, packaged threshold-equilibrium route `audit_theorem4_4_resampling_policy_strategy_proof_observable_and_demographic_fair`, and source-model route `audit_theorem4_4_resampling_policy` |

Additional Theorem 3.2 audit endpoint:
`audit_theorem3_2_optional_reporting_mapped_actor_finite_test_full_support`
derives the optional-reporting selected-score support facts from full support
of a finite concrete test law before pushing tests forward to reported scores.
The companion aliases
`audit_theorem3_2_optional_reporting_mapped_actor_finite_test_full_support_exists_distinct`
and
`audit_theorem3_2_report_required_mapped_actor_full_support_exists_distinct`
state the strongest mapped-actor routes using existential distinct-test
witnesses rather than explicit selected tests.  The non-certificate
source-witness route is also audited directly by
`audit_theorem3_2_section3_fairness_impossibility_of_mixture_and_source_evidence`,
`audit_theorem3_2_section3_no_test_relevance_of_mixture_and_source_evidence`,
`audit_theorem3_2_section3_law_fairness_impossibility_of_observable_implication_and_source_evidence`,
and
`audit_theorem3_2_section3_law_no_test_relevance_of_observable_implication_and_source_evidence`.

## Cross-Artifact Checks

- Paper-facing Lean: `PaperInterface.lean` exposes the compact statement
  surface. `PostPaperAudit.lean` imports it and gives source-numbered aliases
  for the named definitions and theorem endpoints.
- Pickup note: `START_HERE_NEXT_AGENT.md` records the latest clean boundary,
  validation commands, and next useful proof seams.
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
  The Section 3 PMF hidden-access endpoints now expose that same event-share
  instantiation directly, so the remaining optional PMF work is only a more
  concrete finite surface representation, not the event-share proof route.
  The PMF route now also has every-equilibrium wrappers matching the law route's
  public shape.
- Theorem 3.2 is formalized through explicit event-or-blank source surfaces.
  The final aliases state the paper's hidden-access implication and no-relevance
  readings, while the concrete routes expose the positive event-share or
  already-test-blank case split used by the unraveling proof.  The bridge
  `paper_interface_theorem3_2_positive_event_or_blank_of_no_positive_event_blank`
  names the convention that a zero-positive-reporter/taker profile is already
  test-blank, so the final aliases no longer take the raw disjunction directly.
  Definition 5's source note that an equilibrium with no reporter/taker event is
  test-blank is now exposed explicitly by
  `paper_interface_definition5_test_blank_of_no_positive_event_blank` and its
  finite zero-share variant.  The blank-on-zero-share constructor has a global
  zero-share equality check, so the constructed surfaces discharge the
  no-reporter/no-taker branch by definition.  It also now proves that
  normalized no-relevance is equivalent to raw no-relevance on exactly the
  profiles where the constructor preserves the raw law: nonzero-share profiles
  and, equivalently, positive-mass reporter/taker event profiles.  The other
  source-proof branch, "if the policy ignores the test score, observable
  fairness is immediate", is exposed by the Definition 5-to-Definition 3 bridges
  `paper_interface_definition5_implies_definition3_of_full_feature_base_only`
  and its continuous-law analogue. The named
  `LG21FullFeatureBaseOnlyObservableIdentities` and
  `LG21LawFullFeatureBaseOnlyObservableIdentities` certificates package those
  ordinary observable-surface identities for both Definition 5 and Theorem 3.2
  callers.  The Theorem 3.2 iff wrappers combine that branch with the existing
  source implication, so the audit surface can state that latent-or-observable
  fairness is equivalent to test-blankness under one explicit identity
  certificate. The source-equilibrium event-or-blank and zero-share iff routes
  now have certificate-consuming audit aliases for optional-reporting and
  report-required regimes, so this source-case-split layer no longer exposes
  the raw `testOf`/access/no-access triple.  Binary-mixture and finite
  event-share surfaces now have reusable constructors for that certificate, so
  concrete surface endpoints can assemble the identity witness uniformly. The source-equilibrium
  optional-reporting and report-required event-or-blank/zero-share routes now
  have direct Section 3 iff audit aliases as well, so this "only way" reading
  is exposed at the same source-certification layer as the implication and
  no-relevance endpoints. The fully concrete optional posterior-payoff and
  report-required unit-centered event-or-blank surfaces now expose the same
  iff conclusions, not only the one-way implication/no-relevance forms. The
  blank-on-zero-share concrete surfaces expose direct iff wrappers as well,
  with the zero-share branch discharged by the constructor-backed certificate.
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
  implication, no-relevance, and iff aliases. The strongest direct unfairness
  routes now include optional finite-test and report-required full-support
  mapped-actor endpoints with existential distinct-test witnesses, aligning the
  concrete route with Definition 5's relevance language. The concrete
  event-or-blank iff aliases consume the named ordinary
  full-feature/base-only observable-identity certificate, but not a global
  positive-share premise; the blank-on-zero-share iff aliases additionally
  discharge the zero-share branch by definition. The
  source-level event-or-blank
  and zero-share variants state the paper's finite-share branch explicitly:
  zero reporter/taker event share implies the profile is already test-blank,
  and the ordinary observable-surface identities give the converse fairness
  direction. The constructed
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
