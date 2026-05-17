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

/-- Audit endpoint for Theorem 3.1, optional-reporting Section 3 PMF branch. -/
abbrev audit_theorem3_1_section3_optional_reporting_pmf :=
  @paper_interface_theorem3_1_section3_optional_reporting_strategic_withholding_pmf

/-- Audit endpoint for Theorem 3.1, report-required Section 3 PMF branch. -/
abbrev audit_theorem3_1_section3_report_required_pmf :=
  @paper_interface_theorem3_1_section3_report_required_strategic_withholding_pmf

/-- Audit endpoint for Theorem 3.1 optional-reporting finite-event-share source route. -/
abbrev audit_theorem3_1_optional_reporting_event_share_source_route :=
  @paper_interface_theorem3_1_optional_reporting_source_evidence_of_event_share_no_report_mixture

/-- Audit endpoint for Theorem 3.1 report-required finite-event-share source route. -/
abbrev audit_theorem3_1_report_required_event_share_source_route :=
  @paper_interface_theorem3_1_report_required_source_evidence_of_event_share_no_take_mixture

/-- Audit endpoint for Theorem 3.1 optional-reporting finite-event-share law certificate. -/
noncomputable abbrev audit_theorem3_1_optional_reporting_event_share_law_certificate :=
  @paper_interface_theorem3_1_optional_reporting_law_strategic_withholding_certificate_of_event_share_no_report_mixture_and_base_mixed_gaussian_posterior_surface

/-- Audit endpoint for Theorem 3.1 report-required finite-event-share law certificate. -/
noncomputable abbrev audit_theorem3_1_report_required_event_share_law_certificate :=
  @paper_interface_theorem3_1_report_required_law_strategic_withholding_certificate_of_event_share_no_take_mixture_and_base_mixed_affine_skill_posterior_surface

/-- Audit endpoint for Theorem 3.1 optional-reporting finite-event-share every-equilibrium law certificates. -/
noncomputable abbrev audit_theorem3_1_optional_reporting_event_share_every_equilibrium_law_certificate :=
  @paper_interface_theorem3_1_optional_reporting_law_strategic_withholding_certificate_for_every_equilibrium_of_event_share_no_report_mixture_and_base_mixed_gaussian_posterior_surface

/-- Audit endpoint for Theorem 3.1 report-required finite-event-share every-equilibrium law certificates. -/
noncomputable abbrev audit_theorem3_1_report_required_event_share_every_equilibrium_law_certificate :=
  @paper_interface_theorem3_1_report_required_law_strategic_withholding_certificate_for_every_equilibrium_of_event_share_no_take_mixture_and_base_mixed_affine_skill_posterior_surface

/-- Audit endpoint for Theorem 3.1 optional-reporting Section 3 finite-event-share law route. -/
abbrev audit_theorem3_1_section3_optional_reporting_event_share_law_route :=
  @paper_interface_theorem3_1_section3_optional_reporting_strategic_withholding_of_event_share_no_report_mixture_and_base_mixed_gaussian_posterior_surface

/-- Audit endpoint for Theorem 3.1 report-required Section 3 finite-event-share law route. -/
abbrev audit_theorem3_1_section3_report_required_event_share_law_route :=
  @paper_interface_theorem3_1_section3_report_required_strategic_withholding_of_event_share_no_take_mixture_and_base_mixed_affine_skill_posterior_surface

/-- Audit endpoint for Theorem 3.2's positive-event versus already-blank bridge. -/
abbrev audit_theorem3_2_positive_event_or_blank_bridge :=
  @paper_interface_theorem3_2_positive_event_or_blank_of_no_positive_event_blank

/-- Audit endpoint for Theorem 3.2's positive-share versus already-blank bridge. -/
abbrev audit_theorem3_2_positive_event_share_or_blank_bridge :=
  @paper_interface_theorem3_2_positive_event_or_blank_of_zero_event_share_blank

/-- Audit endpoint for the blank-on-zero-share full-feature estimate constructor. -/
noncomputable abbrev audit_theorem3_2_blank_on_zero_event_share_constructor :=
  @paper_interface_theorem3_2_full_feature_estimate_blank_on_zero_event_share

/-- Audit endpoint for the blank-on-zero-share constructor's case split. -/
abbrev audit_theorem3_2_positive_event_or_blank_of_blank_on_zero_event_share :=
  @paper_interface_theorem3_2_positive_event_or_blank_of_blank_on_zero_event_share

/-- Audit endpoint for converting zero-share blankness into no-positive-event blankness. -/
abbrev audit_theorem3_2_no_positive_event_blank_of_zero_event_share_blank :=
  @paper_interface_theorem3_2_no_positive_event_blank_of_zero_event_share_blank

/-- Audit endpoint for positive finite event share iff a positive-mass event atom exists. -/
abbrev audit_event_share_pos_iff_exists_pos_mass :=
  @paper_interface_theorem3_2_pmf_event_share_fn_pos_iff_exists_pos_mass

/-- Audit endpoint for zero finite event share from no positive-mass event atom. -/
abbrev audit_event_share_eq_zero_of_no_positive_mass :=
  @paper_interface_theorem3_2_pmf_event_share_fn_eq_zero_of_no_positive_mass

/-- Audit endpoint for finite event shares being strictly below one. -/
abbrev audit_event_share_lt_one_of_complement_mass :=
  @paper_interface_theorem3_2_pmf_event_share_fn_lt_one_of_mass_not

/-- Audit endpoint for Theorem 3.2, optional-reporting fairness-impossibility branch. -/
abbrev audit_theorem3_2_section3_optional_reporting_fairness_impossibility :=
  @paper_interface_theorem3_2_section3_optional_reporting_fairness_impossibility

/-- Audit endpoint for Theorem 3.2, optional-reporting zero-share fairness-impossibility branch. -/
abbrev audit_theorem3_2_section3_optional_reporting_zero_share_fairness_impossibility :=
  @paper_interface_theorem3_2_section3_optional_reporting_fairness_impossibility_of_zero_event_share_blank

/-- Audit endpoint for Theorem 3.2, report-required fairness-impossibility branch. -/
abbrev audit_theorem3_2_section3_report_required_fairness_impossibility :=
  @paper_interface_theorem3_2_section3_report_required_fairness_impossibility

/-- Audit endpoint for Theorem 3.2, report-required zero-share fairness-impossibility branch. -/
abbrev audit_theorem3_2_section3_report_required_zero_share_fairness_impossibility :=
  @paper_interface_theorem3_2_section3_report_required_fairness_impossibility_of_zero_event_share_blank

/-- Audit endpoint for Theorem 3.2, optional-reporting no-relevance branch. -/
abbrev audit_theorem3_2_section3_optional_reporting_no_test_relevance :=
  @paper_interface_theorem3_2_section3_optional_reporting_no_test_relevance

/-- Audit endpoint for Theorem 3.2, optional-reporting zero-share no-relevance branch. -/
abbrev audit_theorem3_2_section3_optional_reporting_zero_share_no_test_relevance :=
  @paper_interface_theorem3_2_section3_optional_reporting_no_test_relevance_of_zero_event_share_blank

/-- Audit endpoint for Theorem 3.2, report-required no-relevance branch. -/
abbrev audit_theorem3_2_section3_report_required_no_test_relevance :=
  @paper_interface_theorem3_2_section3_report_required_no_test_relevance

/-- Audit endpoint for Theorem 3.2, report-required zero-share no-relevance branch. -/
abbrev audit_theorem3_2_section3_report_required_zero_share_no_test_relevance :=
  @paper_interface_theorem3_2_section3_report_required_no_test_relevance_of_zero_event_share_blank

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
