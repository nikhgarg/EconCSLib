# LG21 Source-Surface Audit

This is an agent source audit, not a human dashboard review. It records the
paper-facing source items checked against an ignored local source text cache and the compact Lean
interface item that a human should inspect next. The dashboard state remains
`0/16 reviewed` until a human saves reviews through the review tool.

Source file checked locally: `papers/LG21TestOptionalPolicies/source.txt`
(omitted from the public repository).

## Source-Order Inventory

| Source item | Source lines | Human interface declaration | Audit endpoint | Status |
| --- | ---: | --- | --- | --- |
| Definition 1, equilibrium | 256 | `PaperInterface.definition1_source_equilibrium` | `PostPaperAudit.audit_definition1_source_equilibrium` | Present in compact interface |
| Definition 2, latent skill fairness | 336 | `PaperInterface.definition2_latent_skill_fair` | `PostPaperAudit.audit_definition2_latent_skill_fair` | Present in compact interface |
| Definition 3, observable fairness | 346 | `PaperInterface.definition3_observable_fair` | `PostPaperAudit.audit_definition3_observably_fair` | Present in compact interface |
| Definition 4, demographic fairness | 360 | `PaperInterface.definition4_demographic_fair` | `PostPaperAudit.audit_definition4_demographically_fair` | Present in compact interface |
| Definition 5, test blankness | 370 | `PaperInterface.definition5_test_blank` | `PostPaperAudit.audit_definition5_test_blank` | Present in compact interface |
| Theorem 3.1, strategic withholding, optional reporting branch | 424, 829 | `PaperInterface.theorem3_1_optional_reporting` | `PostPaperAudit.audit_theorem3_1_section3_optional_reporting` | Present in compact interface |
| Theorem 3.1, strategic withholding, report-required branch | 424, 829 | `PaperInterface.theorem3_1_report_required` | `PostPaperAudit.audit_theorem3_1_section3_report_required` | Present in compact interface |
| Theorem 3.2, optional-reporting fairness impossibility | 455, 1614 | `PaperInterface.theorem3_2_optional_reporting_fairness_impossibility` | `PostPaperAudit.audit_theorem3_2_section3_optional_reporting_fairness_impossibility` | Present in compact interface |
| Theorem 3.2, optional-reporting no test relevance | 455, 1614 | `PaperInterface.theorem3_2_optional_reporting_no_test_relevance` | `PostPaperAudit.audit_theorem3_2_section3_optional_reporting_no_test_relevance` | Present in compact interface |
| Theorem 3.2, report-required fairness impossibility | 455, 1614 | `PaperInterface.theorem3_2_report_required_fairness_impossibility` | `PostPaperAudit.audit_theorem3_2_section3_report_required_fairness_impossibility` | Present in compact interface |
| Theorem 3.2, report-required no test relevance | 455, 1614 | `PaperInterface.theorem3_2_report_required_no_test_relevance` | `PostPaperAudit.audit_theorem3_2_section3_report_required_no_test_relevance` | Present in compact interface |
| Lemma 4.1, strategy-proofness with observed access | 492, 1784 | `PaperInterface.lemma4_1_observed_access_strategy_proofness` | `PostPaperAudit.audit_lemma4_1_observed_access_strategy_proofness` | Present in compact interface |
| Proposition 4.2, Bayesian optimal access estimates are not latent-skill fair | 550, 2318 | `PaperInterface.proposition4_2_base_indexed_posterior_surface` | `PostPaperAudit.audit_proposition4_2_base_indexed_posterior_surface` | Present in compact interface |
| Proposition 4.3, full Bayesian optimal policy is not observable or demographic fair | 561, 2417 | `PaperInterface.proposition4_3_base_mixed_extra_signal_surface` | `PostPaperAudit.audit_proposition4_3_base_mixed_extra_signal_surface` | Present in compact interface |
| Definition 6, re-sampling policy | 591 | `PaperInterface.definition6_resampling_policy` | `PostPaperAudit.audit_definition6_resampling_policy_observable_kernel` | Present in compact interface |
| Theorem 4.4, re-sampling policy fairness | 610, 2509 | `PaperInterface.theorem4_4_resampling_policy` | `PostPaperAudit.audit_theorem4_4_resampling_policy` | Present in compact interface |

## Audit Notes

- The compact human-review surface has 16 declarations, matching the source
  definitions and named result branches above.
- The dashboard parser reports 16 interface rows, all unreviewed, with no stale
  or mismatch entries.
- `PostPaperAudit.lean` remains the broad implementation-facing ledger; helper
  aliases and proof-route variants are intentionally not part of the compact
  human interface.
- The remaining non-Lean step is human source review through the dashboard.
