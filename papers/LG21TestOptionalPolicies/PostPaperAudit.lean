import LG21TestOptionalPolicies.PaperInterface

/-!
# Post-paper audit: Test-optional Policies

This file is the importable audit ledger for
*Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps*.

`PaperInterface.lean` is the compact human-facing statement surface.  The
aliases below give source-numbered audit entrypoints for the paper definitions
and named results, while deliberately preserving the current validation caveat:
Theorems 3.1 and 3.2 are closed as conditional Section 3 endpoints over the
concrete Gaussian/affine/event-share source surfaces exposed in
`PaperInterface.lean`.
-/

namespace LG21TestOptionalPolicies

namespace PostPaperAudit

/-- Audit endpoint for the Section 3 hidden-access information-set assumption. -/
abbrev audit_section3_school_information_hides_access :=
  @paper_interface_school_information_hides_access_when_unobserved

/-- Audit endpoint for the Section 4 observed-access information-set assumption. -/
abbrev audit_section4_school_information_records_access :=
  @paper_interface_school_information_records_access_when_observed

/-- Audit endpoint for no-access feasibility in the source requirement policy. -/
abbrev audit_requirement_no_access_feasible_iff :=
  @paper_interface_requirement_no_access_feasible_iff

/-- Audit endpoint for report-required feasibility given access. -/
abbrev audit_requirement_given_access_feasible_iff :=
  @paper_interface_requirement_given_access_feasible_iff

/-- Audit endpoint for Definition 1, source equilibrium. -/
abbrev audit_definition1_source_equilibrium :=
  @paper_interface_definition1_source_equilibrium_iff

/-- Audit endpoint for Definition 2, latent-skill fairness. -/
abbrev audit_definition2_latent_skill_fair :=
  @paper_interface_definition2_latent_skill_fair_iff

/-- Audit endpoint for Definition 2, continuous-law latent-skill fairness. -/
abbrev audit_definition2_law_latent_skill_fair :=
  @paper_interface_definition2_law_latent_skill_fair_iff

/-- Audit endpoint for Definition 3, observable fairness. -/
abbrev audit_definition3_observably_fair :=
  @paper_interface_definition3_observably_fair_iff

/-- Audit endpoint for Definition 3, continuous-law observable fairness. -/
abbrev audit_definition3_law_observably_fair :=
  @paper_interface_definition3_law_observably_fair_iff

/-- Audit endpoint for Definition 4, demographic fairness. -/
abbrev audit_definition4_demographically_fair :=
  @paper_interface_definition4_demographically_fair_iff

/-- Audit endpoint for Definition 4, continuous-law demographic fairness. -/
abbrev audit_definition4_law_demographically_fair :=
  @paper_interface_definition4_law_demographically_fair_iff

/-- Audit endpoint for the finite fairness implication chain. -/
abbrev audit_fairness_implication_chain :=
  @paper_interface_definition2_implies_definition4_of_mixture

/-- Audit endpoint for Definition 5, test-blank policies. -/
abbrev audit_definition5_test_blank :=
  @paper_interface_definition5_test_blank_iff

/-- Audit endpoint for Definition 5, continuous-law test-blank policies. -/
abbrev audit_definition5_law_test_blank :=
  @paper_interface_definition5_law_test_blank_iff

/-- Audit endpoint for the Bayesian optimal Gaussian estimator used by `P_BO`. -/
abbrev audit_bayesian_optimal_estimator_gaussian :=
  @paper_interface_bayesian_optimal_estimator_gaussian

/-- Audit endpoint for Theorem 3.1, optional-reporting Section 3 branch. -/
abbrev audit_theorem3_1_section3_optional_reporting :=
  @paper_interface_theorem3_1_section3_optional_reporting_strategic_withholding

/-- Audit endpoint for Theorem 3.1, report-required Section 3 branch. -/
abbrev audit_theorem3_1_section3_report_required :=
  @paper_interface_theorem3_1_section3_report_required_strategic_withholding

/-- Audit endpoint for Theorem 3.2, optional-reporting fairness-impossibility branch. -/
abbrev audit_theorem3_2_section3_optional_reporting_fairness_impossibility :=
  @paper_interface_theorem3_2_section3_optional_reporting_fairness_impossibility

/-- Audit endpoint for Theorem 3.2, report-required fairness-impossibility branch. -/
abbrev audit_theorem3_2_section3_report_required_fairness_impossibility :=
  @paper_interface_theorem3_2_section3_report_required_fairness_impossibility

/-- Audit endpoint for Theorem 3.2, optional-reporting no-relevance branch. -/
abbrev audit_theorem3_2_section3_optional_reporting_no_test_relevance :=
  @paper_interface_theorem3_2_section3_optional_reporting_no_test_relevance

/-- Audit endpoint for Theorem 3.2, report-required no-relevance branch. -/
abbrev audit_theorem3_2_section3_report_required_no_test_relevance :=
  @paper_interface_theorem3_2_section3_report_required_no_test_relevance

/-- Audit endpoint for Lemma 4.1, observed-access source strategy-proofness. -/
abbrev audit_lemma4_1_observed_access_strategy_proofness :=
  @paper_interface_lemma4_1_observed_access_chosen_actions_of_fully_specified_source_models

/-- Audit endpoint for Proposition 4.2, base-indexed posterior-law surface. -/
abbrev audit_proposition4_2_base_indexed_posterior_surface :=
  @paper_interface_proposition4_2_not_latent_skill_fair_of_fully_specified_source_models_and_base_indexed_one_test_posterior_surface

/-- Audit endpoint for Proposition 4.3, base-mixed extra-signal surface. -/
abbrev audit_proposition4_3_base_mixed_extra_signal_surface :=
  @paper_interface_proposition4_3_not_law_observable_or_demographic_fair_of_fully_specified_source_models_and_base_mixed_extra_signal_surface

/-- Audit endpoint for Definition 6, finite re-sampling policy kernel. -/
abbrev audit_definition6_resampling_policy_observable_kernel :=
  @paper_interface_definition6_resampling_policy_observable_kernel

/-- Audit endpoint for Definition 6, access/resampling kernel equality. -/
abbrev audit_definition6_access_resampling_kernel_eq :=
  @paper_interface_definition6_access_estimate_kernel_eq_resampling_estimate_kernel

/-- Audit endpoint for Theorem 4.4, source strategy-proof fair re-sampling policy. -/
abbrev audit_theorem4_4_resampling_policy :=
  @paper_interface_theorem4_4_resampling_policy_source_strategy_proof_observable_and_demographic_fair

end PostPaperAudit

end LG21TestOptionalPolicies
