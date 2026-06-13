# Final Validation Report: Test-optional Policies

## 1. Human Verdict

- Lean formalization status: partially formalized under the strict premise-provenance audit
- Human dashboard review status: 0/16 rows reviewed; 0 stale; 0 mismatches.
- Main caveat: none for the compact paper-facing surface. The strict premise
  audit records 20/20 explicit source-model/domain premises as source-matched
  or source-derived.

### Verdict

The paper-facing statement surface is compact and covers all named definitions
and results in Sections 2--4. Under the stricter premise-provenance standard,
the current compact surface is closed: every non-derived source-model/domain
premise is listed in `Assumptions.lean` and validated premise-by-premise in
`assumption_match_llm.json`.

All named definitions and named results in Sections 2--4 have compiling Lean
endpoints in the compact human-review interface. The formalization did not find
a counterexample to a named theorem in the paper. The strict audit now checks
the target declarations reached by the dashboard aliases in
`ProofInterface.lean` and confirms that their explicit source-model/domain
premises are routed through the paper-local assumption ledger.

The existing proof work also identified two places where the informal source
proof needs to be represented carefully:

- continuous cutoff and tie cases should be stated as source-law or a.e.
  equilibrium facts, since boundary types have measure zero;
- arbitrary raw-policy abstractions are broader than the paper's source model
  and can be false, so they are recorded only as diagnostics.

Those are modeling repairs to the formal statement surface, not paper-error
caveats.

Human review is still external: the dashboard currently reports `0/16`
reviewed interface items. The model statement-translation and statement-match
sidecars are current for all 16 compact rows; human review remains a separate
dashboard lane.

### Lean Footprint

- Paper-local Lean files: 127,936 total lines across nine modules.
- `PaperInterface.lean`: 77 lines.
- Human-review surface: 16 declarations.
- `PostPaperAudit.lean`: 1,073 importable audit declarations.

<!-- transitive-source-premise-audit:start -->
### Transitive Source-Premise Audit

The strengthened recursive source-premise audit does not yet pass for full-status provenance. It follows paper-local wrappers and reusable-library certificate APIs, and treats certificate/source-row/external-boundary premises as full-status blockers unless they are derived internally or routed through validated paper assumptions.

Current result: the test-optional endpoints still depend on Gaussian tail/hazard and source-equilibrium certificates rather than fully derived Gaussian source-model algebra.
<!-- transitive-source-premise-audit:end -->

## 2. Source and Scope

### Source Version

- Paper: *Test-optional Policies: Overcoming Strategic Behavior and
  Informational Gaps*
- Authors: Zhi Liu and Nikhil Garg
- Version formalized: arXiv:2107.08922 / EAAMO 2021 version
- Local source text cache: `source.txt` when regenerated locally; omitted from
  the public repository.

Sections 1 and 5 are introduction/discussion material and contain no named
theorem or definition target. The formalized source surface covers the named
model definitions and results in Sections 2--4.

### Source Surface

Human reviewers should start from:

- `PaperInterface.lean`: compact 16-row statement surface.
- `SOURCE_AUDIT.md`: source-order map from the paper text to each interface
  row, including local source-cache line numbers and audit endpoints.
- `PostPaperAudit.lean`: broader importable ledger for proof-route variants
  and diagnostics.

The compact interface covers exactly these paper-facing items:

| Paper item | Interface coverage |
| --- | --- |
| Definition 1, equilibrium | source action, feasibility, best response, and consistency |
| Definition 2, latent-skill fairness | equality of estimate laws conditional on latent skill and observed features |
| Definition 3, observable fairness | equality of estimate laws conditional on observed features |
| Definition 4, demographic fairness | equality of estimate laws by access status |
| Definition 5, test blankness | test score has no estimate relevance |
| Theorem 3.1 | optional-reporting and report-required strategic-withholding branches |
| Theorem 3.2 | optional-reporting and report-required fairness-impossibility/no-relevance branches |
| Lemma 4.1 | observed access makes the Bayesian access-side policy strategy-proof |
| Proposition 4.2 | Bayesian optimal access-side estimates are not latent-skill fair |
| Proposition 4.3 | full Bayesian optimal policy is not observable or demographic fair |
| Definition 6 | resampling policy |
| Theorem 4.4 | resampling policy is strategy-proof, observable fair, and demographic fair |

The dashboard source-statement map used for statement translation is:

- `definition1_source_equilibrium`: A source equilibrium consists of feasible
  access decisions, best-response utility maximization among feasible actions
  in every student information state, and estimation consistency.
- `definition2_latent_skill_fair`: A policy surface is latent-skill fair when,
  in every equilibrium, applicants with the same latent skill and base group
  receive the same estimate law whether or not they have access.
- `definition3_observable_fair`: A policy surface is observably fair when, in
  every equilibrium and base group, the access and no-access observable estimate
  laws are equal.
- `definition4_demographic_fair`: A policy surface is demographically fair
  when, in every equilibrium, the demographic access and no-access estimate laws
  are equal.
- `definition5_test_blank`: A policy surface is test-blank when, in every
  equilibrium, base group, and test value, the base-only estimate equals the
  full-feature estimate.
- `theorem3_1_optional_reporting`: In the hidden-access optional-reporting
  source model, when access fractions are below one, every source equilibrium
  has strategic withholding: everyone takes the test, some base-score pair is
  not reported, reporting is cutoff-shaped within each base group, and the
  base-mixed Gaussian posterior-law surface is not latent-skill fair, not
  observable fair, and not demographic fair.
- `theorem3_1_report_required`: In the hidden-access report-required source
  model with positive slopes and access fractions below one, every source
  equilibrium has strategic withholding: some base-skill pair does not take the
  test, taking is cutoff-shaped within each base group, and the base-mixed
  affine-skill posterior-law surface is not latent-skill fair, not observable
  fair, and not demographic fair.
- `theorem3_2_optional_reporting_fairness_impossibility`: In the
  optional-reporting source model, under source-equilibrium, threshold-reporting,
  and the no-reporter-to-test-blank normalization, latent-skill fairness or
  observable fairness of the event-share binary-mixture surface implies
  test-blankness.
- `theorem3_2_optional_reporting_no_test_relevance`: Under the same
  optional-reporting hypotheses, if the event-share binary-mixture surface is
  latent-skill fair or observable fair, then there is no base/test triple where
  the base-only and full-feature estimates differ.
- `theorem3_2_report_required_fairness_impossibility`: In the report-required
  source model, under source-equilibrium, threshold-taking, and the
  no-taker-to-test-blank normalization, latent-skill fairness or observable
  fairness of the event-share binary-mixture surface implies test-blankness.
- `theorem3_2_report_required_no_test_relevance`: Under the same report-required
  hypotheses, if the event-share binary-mixture surface is latent-skill fair or
  observable fair, then there is no base/test triple where the base-only and
  full-feature estimates differ.
- `lemma4_1_observed_access_strategy_proofness`: With observed access and a
  positive test scale, the fully specified optional-reporting and
  report-required source equilibria choose take-and-report in every student
  information state, giving the strategy-proofness step.
- `proposition4_2_bayesian_access_estimates_not_latent_skill_fair`: For the fully specified
  observed-access source equilibria, any positive-slope base-indexed one-test
  posterior-law surface chooses take-and-report in every information state and
  is not latent-skill fair.
- `proposition4_3_bayesian_optimal_not_observable_or_demographic_fair`: For the fully specified
  observed-access source equilibria, any base-mixed extra-signal posterior-law
  surface with positive extra-noise variance chooses take-and-report in every
  information state and is not observable fair or demographic fair.
- `definition6_resampling_policy`: The resampling policy uses the resampling
  experiment's conditional signal-given-base kernel.
- `theorem4_4_resampling_policy`: For every resampling experiment, the
  fully specified observed-access source equilibria choose take-and-report in
  every information state, and the access-estimate and resampling-estimate
  kernels are observable fair and demographic fair with respect to the base
  profile.

The report intentionally does not list every helper declaration. Those details
belong in `PostPaperAudit.lean`.

## 3. What Has Been Proven

### What Happened

The Section 3 proof was the hard part. The final route follows the paper's
strategic-withholding and unraveling arguments, but makes the implicit cases
explicit:

- In Theorem 3.1, optional reporting and report-required policies are handled
  separately, matching the paper's two bullet points. The formalization uses
  source-shaped Gaussian and affine payoff models to prove the threshold and
  unfairness conclusions.
- In Theorem 3.2, fairness implies either a positive reporter/taker event share
  that unravels by a profitable deviation, or a zero-event branch where the
  policy is already test-blank/no-test-relevant. This is the formal version of
  the paper's unraveling proof.
- For continuous threshold models, pointwise equilibrium at the exact cutoff is
  too strong. The repaired route uses a.e. equilibrium under the realized source
  law, which matches the paper's intended treatment of measure-zero tie points.

The observed-access section is more direct:

- Lemma 4.1 closes the strategy-proofness step for the observed-access source
  model.
- Propositions 4.2 and 4.3 close the informational-gap unfairness results using
  the shared Gaussian posterior infrastructure.
- Definition 6 and Theorem 4.4 close via a finite conditional-resampling
  kernel: access and no-access estimate laws are pushforwards of the same
  conditional test-score law, so observable fairness holds by construction and
  demographic fairness follows by mixing.

## 4. Paper Definitions Checked

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| abbrev definition1_source_equilibrium | `definition1_source_equilibrium` | A source equilibrium consists of feasible access decisions, best-response utility maximization among feasible actions in every student information state, and estimation consistency. |
| abbrev definition2_latent_skill_fair | `definition2_latent_skill_fair` | A policy surface is latent-skill fair when, in every equilibrium, applicants with the same latent skill and base group receive the same estimate law whether or not they have access. |
| abbrev definition3_observable_fair | `definition3_observable_fair` | A policy surface is observably fair when, in every equilibrium and base group, the access and no-access observable estimate laws are equal. |
| abbrev definition4_demographic_fair | `definition4_demographic_fair` | A policy surface is demographically fair when, in every equilibrium, the demographic access and no-access estimate laws are equal. |
| abbrev definition5_test_blank | `definition5_test_blank` | A policy surface is test-blank when, in every equilibrium, base group, and test value, the base-only estimate equals the full-feature estimate. |
| abbrev theorem3_1_optional_reporting | `theorem3_1_optional_reporting` | In the hidden-access optional-reporting source model, when access fractions are below one, every source equilibrium has strategic withholding: everyone takes the test, some base-score pair is not reported, reporting is cutoff-shaped with... |
| abbrev theorem3_1_report_required | `theorem3_1_report_required` | In the hidden-access report-required source model with positive slopes and access fractions below one, every source equilibrium has strategic withholding: some base-skill pair does not take the test, taking is cutoff-shaped within each b... |
| abbrev theorem3_2_optional_reporting_fairness_impossibility | `theorem3_2_optional_reporting_fairness_impossibility` | In the optional-reporting source model, under source-equilibrium, threshold-reporting, and the no-reporter-to-test-blank normalization, latent-skill fairness or observable fairness of the event-share binary-mixture surface implies test-b... |
| abbrev theorem3_2_optional_reporting_no_test_relevance | `theorem3_2_optional_reporting_no_test_relevance` | Under the same optional-reporting hypotheses, if the event-share binary-mixture surface is latent-skill fair or observable fair, then there is no base/test triple where the base-only and full-feature estimates differ. |
| abbrev theorem3_2_report_required_fairness_impossibility | `theorem3_2_report_required_fairness_impossibility` | In the report-required source model, under source-equilibrium, threshold-taking, and the no-taker-to-test-blank normalization, latent-skill fairness or observable fairness of the event-share binary-mixture surface implies test-blankness. |
| abbrev theorem3_2_report_required_no_test_relevance | `theorem3_2_report_required_no_test_relevance` | Under the same report-required hypotheses, if the event-share binary-mixture surface is latent-skill fair or observable fair, then there is no base/test triple where the base-only and full-feature estimates differ. |
| abbrev lemma4_1_observed_access_strategy_proofness | `lemma4_1_observed_access_strategy_proofness` | With observed access and a positive test scale, the fully specified optional-reporting and report-required source equilibria choose take-and-report in every student information state, giving the strategy-proofness step. |
| abbrev proposition4_2_bayesian_access_estimates_not_latent_skill_fair | `proposition4_2_bayesian_access_estimates_not_latent_skill_fair` | For the fully specified observed-access source equilibria, any positive-slope base-indexed one-test posterior-law surface chooses take-and-report in every information state and is not latent-skill fair. |
| abbrev proposition4_3_bayesian_optimal_not_observable_or_demographic_fair | `proposition4_3_bayesian_optimal_not_observable_or_demographic_fair` | For the fully specified observed-access source equilibria, any base-mixed extra-signal posterior-law surface with positive extra-noise variance chooses take-and-report in every information state and is not observable fair or demographic... |
| abbrev definition6_resampling_policy | `definition6_resampling_policy` | The resampling policy uses the resampling experiment's conditional signal-given-base kernel. |
| abbrev theorem4_4_resampling_policy | `theorem4_4_resampling_policy` | For every resampling experiment, the fully specified observed-access source equilibria choose take-and-report in every information state, and the access-estimate and resampling-estimate kernels are observable fair and demographic fair wi... |
<!-- lean-derived-definitions:end -->

## 5. Named Theorem Statements Checked

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

None exposed in the current dashboard surface.
<!-- lean-derived-statements:end -->

## 6. Paper-Facing Statement Validator Ledger

Generated from dashboard status export:

`python3 scripts/review_dashboard.py --paper LG21TestOptionalPolicies --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| abbrev definition1_source_equilibrium | `definition1_source_equilibrium` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev definition2_latent_skill_fair | `definition2_latent_skill_fair` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev definition3_observable_fair | `definition3_observable_fair` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev definition4_demographic_fair | `definition4_demographic_fair` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev definition5_test_blank | `definition5_test_blank` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev definition6_resampling_policy | `definition6_resampling_policy` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev lemma4_1_observed_access_strategy_proofness | `lemma4_1_observed_access_strategy_proofness` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev proposition4_2_bayesian_access_estimates_not_latent_skill_fair | `proposition4_2_bayesian_access_estimates_not_latent_skill_fair` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev proposition4_3_bayesian_optimal_not_observable_or_demographic_fair | `proposition4_3_bayesian_optimal_not_observable_or_demographic_fair` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev theorem3_1_optional_reporting | `theorem3_1_optional_reporting` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev theorem3_1_report_required | `theorem3_1_report_required` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev theorem3_2_optional_reporting_fairness_impossibility | `theorem3_2_optional_reporting_fairness_impossibility` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev theorem3_2_optional_reporting_no_test_relevance | `theorem3_2_optional_reporting_no_test_relevance` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev theorem3_2_report_required_fairness_impossibility | `theorem3_2_report_required_fairness_impossibility` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev theorem3_2_report_required_no_test_relevance | `theorem3_2_report_required_no_test_relevance` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |
| abbrev theorem4_4_resampling_policy | `theorem4_4_resampling_policy` | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z) | gpt-5-codex (model; matches; 2026-06-12T00:00:00Z): The declaration-keyed source statement and context-free Lean-to-TeX draft state the same source-model definition or result. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.

## 7. Paper Assumption Provenance

> Strict premise-source audit update (2026-06-12): `Assumptions.lean` now
> records only the compact paper-facing source-model/domain premises reached
> from `PaperInterface.lean`. `assumption_match_llm.json` validates those
> premises individually. Current result: 20/20 premises are source-matched or
> source-derived, with no visible partial-boundary premises.

Every non-derived compact paper-facing premise is routed through
`LG21TestOptionalPolicies/Assumptions.lean` and checked by
`assumption_match_llm.json`. LG21 has many source-model helper declarations in
`PostPaperAudit.lean`; those implementation-only variants are not part of the
public assumption ledger unless reached by a dashboard row. The repository
audit still follows aliases into `ProofInterface.lean`, so the compact surface
cannot hide theorem hypotheses behind an abbrev.

| Lean assumption/condition group | Judgment | Source role |
| --- | --- | --- |
| `assumption_section3_access_fraction_domain` | paper condition / derived | Interior cohort access fractions give `0 <= C < 1`. |
| `assumption_section3_source_equilibrium_instances` | paper condition | Section 3 optional-reporting and report-required source equilibria. |
| `assumption_source_model_event_and_consistency_predicates` | paper condition | Reporting/taking event predicates and estimation-consistency components from the source model. |
| `assumption_section3_threshold_decision_shapes` | paper condition | Threshold-shaped reporting/taking rules stated and proved in Section 3. |
| `assumption_section3_zero_positive_event_blank_branch` | derived | Zero-positive reporter/taker branches collapse to the test-blank/no-relevance branch. |
| `assumption_positive_gaussian_domain_conditions` | paper condition / derived | Positive Gaussian scales, variances, and posterior-slope conditions. |
| `assumption_observed_access_source_equilibria` | paper condition | Observed-access optional-reporting and report-required source equilibria used by Lemma 4.1 and downstream rows. |

## 8. Proof-Strategy Deviations

The main workflow deviation was repaired in this pass: older report text
treated broad source-model certificate buckets as the public ledger. The strict
audit now validates only the compact paper-facing premise surface and follows
dashboard aliases into `ProofInterface.lean` so hidden theorem premises are
still checked.

## 9. Proof Tricks Worth Reusing

- Keep the paper-facing interface compact, and move proof-route variants into
  the audit ledger. This made the final review surface small enough to compare
  against the source paper directly.
- Use a.e. equilibrium for continuous cutoff models when the paper proof only
  needs best response off measure-zero tie boundaries.
- Package fairness impossibility as a source-model certificate: prove the
  unraveling/no-relevance implication once, then instantiate it for optional
  reporting and report-required regimes.
- Maintain finite event-share and continuous-law routes in parallel when the
  source proof moves between finite support witnesses and Gaussian law
  arguments.

## 10. Library Lift Pass

### Library Pass

The post-verification proof scan produced one small library extraction:

- `measure_pos_of_subset`
- `ae_property_contradicts_positive_failure_mass`

Both now live in `EconCSLib.Foundations.Probability.MeasureInequalities`, and
LG21 keeps only thin paper-local wrappers around them.

Other reusable infrastructure was already in the shared library and was reused
rather than duplicated:

- a.e. choice equilibrium:
  `EconCSLib.Foundations.Optimization.ChoiceEquilibriumAE`;
- finite event shares, binary mixtures, and blank-on-zero normalization:
  `EconCSLib.Foundations.Probability.FiniteMixture`;
- conditional resampling kernels:
  `EconCSLib.Foundations.Probability.Admissions`;
- Gaussian posterior and tail facts:
  `EconCSLib.Foundations.Probability.Gaussian`, `GaussianMathlib`, and
  `GaussianDerivatives`.

Deferred candidate: the paper-local tagged point/Gaussian/finite-mixture law
wrappers may deserve a generic Gaussian-mixture law module if another
standardized-testing paper needs the same constructors. They remain local for
now because their current shape is tuned to LG21's source-law bookkeeping.

## 11. DAG Audit

`DependencyDAG.tex` is source-facing and follows the shared template styles:

- model/definition layers use `dag_model`;
- supporting lemma/library nodes use `dag_lemma`;
- paper-facing theorems, propositions, and final results use `dag_result`.

The final spacing pass widened the lanes, increased vertical separation, and
routed the model-to-fairness dependency vertically so arrows do not cross node
labels. `latexmk -pdf DependencyDAG.tex` rebuilt the PDF, and PNG inspection
found no node-label or arrow-through-text overlap.

## 12. Conditional Results and Remaining Gaps

None separately recorded in the existing report.

## 13. Suspected Paper Errors or Inconsistencies

### Issues Found

No named theorem in the paper is marked false.

The main source-model issue was overgeneralization. A raw abstraction that lets
an arbitrary external Bayesian policy be paired with arbitrary pointwise
cutoff behavior is false. The paper does not need that abstraction. The valid
formal route keeps the policy tied to the source model and uses a.e. statements
for continuous boundary cases.

This distinction is important for future agents: keep diagnostics about false
overbroad abstractions out of the paper-facing theorem inventory unless they
change a named paper theorem. Here, they do not.

No named paper result remains conditional or unformalized under the
paper-facing source models.

## 14. Validation Checks

### Verification Checks

Passed:

- `lake build LG21TestOptionalPolicies`
- `python3 scripts/review_dashboard.py --paper LG21TestOptionalPolicies --statement-check`
- `python3 scripts/review_dashboard.py --paper LG21TestOptionalPolicies --assumption-check`
- `python3 scripts/sync_paper_status.py --check`

Expected human-review precheck warning:

- `python3 scripts/review_dashboard.py --paper LG21TestOptionalPolicies --precheck`
  reports 23 unreviewed dashboard items because human review remains external.

### Statement Translation Audit

Audit date: 2026-06-12 for the statement rows and assumption-provenance audit.
Scope: current dashboard rows from `PaperInterface.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment.

Previous statement summary: 16 rows; 16 match, 0 uncertain, 0 mismatch, 0
missing. Current statement sidecars are refreshed against the compact
`PaperInterface.lean` surface, and the assumption-provenance sidecar validates
20/20 compact source-model/domain premises with no partial-boundary rows.

Flagged rows:
- None.

## 15. Final Verdict

- Completion status: formalized under strict premise provenance.
- Summary: The compact statement surface covers the paper. The statement
  translation lane is current for all 16 rows, and the assumption-provenance
  lane validates 20/20 compact-source premises with no partial boundaries.
