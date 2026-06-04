import LG21TestOptionalPolicies.PostPaperAudit

/-!
# Human Review Interface: LG21 Test-Optional Policies

This is the canonical human-review surface for
*Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps*.
It exposes one compact row per paper-facing definition or named result, with
regime variants only where the paper states the result separately for optional
reporting and report-required policies.

Implementation endpoints, proof-route variants, diagnostics, and reusable
bridge lemmas live in `ProofInterface.lean` and `PostPaperAudit.lean`.
-/

namespace LG21TestOptionalPolicies

namespace PaperInterface

/-! ## Source Definitions -/

/-- Definition 1: source equilibrium for test-taking and reporting decisions. -/
abbrev definition1_source_equilibrium := @PostPaperAudit.audit_definition1_source_equilibrium

/-- Definition 2: latent-skill fairness. -/
abbrev definition2_latent_skill_fair := @PostPaperAudit.audit_definition2_latent_skill_fair

/-- Definition 3: observable fairness. -/
abbrev definition3_observable_fair := @PostPaperAudit.audit_definition3_observably_fair

/-- Definition 4: demographic fairness. -/
abbrev definition4_demographic_fair := @PostPaperAudit.audit_definition4_demographically_fair

/-- Definition 5: test-blank policies. -/
abbrev definition5_test_blank := @PostPaperAudit.audit_definition5_test_blank

/-! ## Section 3: Hidden Access -/

/-- Theorem 3.1: strategic withholding under optional reporting. -/
abbrev theorem3_1_optional_reporting := @PostPaperAudit.audit_theorem3_1_section3_optional_reporting

/-- Theorem 3.1: strategic withholding under report-required policies. -/
abbrev theorem3_1_report_required := @PostPaperAudit.audit_theorem3_1_section3_report_required

/-- Theorem 3.2: optional-reporting fairness impossibility. -/
abbrev theorem3_2_optional_reporting_fairness_impossibility := @PostPaperAudit.audit_theorem3_2_section3_optional_reporting_fairness_impossibility

/-- Theorem 3.2: optional-reporting fairness implies no test relevance. -/
abbrev theorem3_2_optional_reporting_no_test_relevance := @PostPaperAudit.audit_theorem3_2_section3_optional_reporting_no_test_relevance

/-- Theorem 3.2: report-required fairness impossibility. -/
abbrev theorem3_2_report_required_fairness_impossibility := @PostPaperAudit.audit_theorem3_2_section3_report_required_fairness_impossibility

/-- Theorem 3.2: report-required fairness implies no test relevance. -/
abbrev theorem3_2_report_required_no_test_relevance := @PostPaperAudit.audit_theorem3_2_section3_report_required_no_test_relevance

/-! ## Section 4: Observed Access -/

/-- Lemma 4.1: observed access makes the policy strategy-proof. -/
abbrev lemma4_1_observed_access_strategy_proofness := @PostPaperAudit.audit_lemma4_1_observed_access_strategy_proofness

/-- Proposition 4.2: Bayesian optimal estimates are not latent-skill fair. -/
abbrev proposition4_2_base_indexed_posterior_surface := @PostPaperAudit.audit_proposition4_2_base_indexed_posterior_surface

/-- Proposition 4.3: the full Bayesian optimal policy is not observable or demographic fair. -/
abbrev proposition4_3_base_mixed_extra_signal_surface := @PostPaperAudit.audit_proposition4_3_base_mixed_extra_signal_surface

/-- Definition 6: the re-sampling policy kernel. -/
abbrev definition6_resampling_policy := @PostPaperAudit.audit_definition6_resampling_policy_observable_kernel

/-- Theorem 4.4: the re-sampling policy is strategy-proof, observable, and demographic fair. -/
abbrev theorem4_4_resampling_policy := @PostPaperAudit.audit_theorem4_4_resampling_policy

end PaperInterface

end LG21TestOptionalPolicies
