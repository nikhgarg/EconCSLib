# Test-optional Admissions and Informational Gaps

## Source Version

- Paper: *Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps*
- Authors: Zhi Liu and Nikhil Garg
- Version formalized: arXiv:2107.08922 / EAAMO 2021 version
- Official URL: https://doi.org/10.1145/3465416.3483293
- arXiv URL: https://arxiv.org/abs/2107.08922
- PDF URL: https://arxiv.org/pdf/2107.08922
- Accessed: 2026-05-01

The source PDF is intentionally not committed to git. It is kept locally as
`source.pdf` and ignored by the local `.gitignore`. The extracted source text
cache is kept as `source.txt` for named-statement audits.

## Central Theorem File

- `LG21TestOptionalPolicies/MainTheorems.lean`
- Human-facing theorem ledger: `LG21TestOptionalPolicies/PaperInterface.lean`
- Live proof plan: `LG21TestOptionalPolicies/FORMALIZATION_PLAN.md`

## Dependency DAG

- `LG21TestOptionalPolicies/DependencyDAG.tex`

## Guideline Audit

- Folder contract: satisfied (`.gitignore`, `README.md`, `DependencyDAG.tex`,
  `MainTheorems.lean`, `PaperInterface.lean`, `FORMALIZATION_PLAN.md`, local
  PDF, and `source.txt` are present).
- README status vocabulary: updated to use the controlled statuses from
  `docs/STATUS.md`.
- DAG status vocabulary: updated to use shared `docs/tikz/dag_preamble.tex`
  styles and source-facing node labels.
- Important correction: the earlier README/DAG listed internal finite
  admissions helper identities as the theorem roadmap. Those helper identities
  are real Lean support, but they are not the paper's named theorem structure.
  The table below now separates source items from auxiliary Lean support.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Source model: access status, base/test features, reporting, and estimation policies | `LG21Model`, `LG21AccessStatus`, `LG21SchoolInformationSet`, `LG21RequirementPolicy`, `lg21BaseModel`, `lg21TestModel`, `LG21SourcePolicySurface`, `LG21SourceLawPolicySurface` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | Finite base/test signal kernels, shared quality, access status `Z`, Section 3/4 information-set visibility, the three requirement-policy regimes, the `(Y, X)` access-action feasibility condition, a PMF distributional policy surface, and a continuous-law equality surface are encoded directly. The remaining Gaussian payoff/equilibrium derivations are theorem-level obligations tracked in Theorem 3.1/3.2, not source-model gaps. |
| Bayesian optimal Gaussian estimator used by `P_BO` | `paper_bayesian_optimal_estimator_gaussian`, `paper_bayesian_optimal_estimator_strictMono_feature`, `paper_reporting_gaussian_threshold_iff_cutoff`, `paper_gaussian_posteriorMean_update_exists_below`, `paper_gaussian_posteriorMean_update_exists_above`, `paper_interface_bayesian_optimal_estimator_gaussian` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | The shared Gaussian posterior-mean formula, marginal estimate law, feature monotonicity, reporting-threshold cutoff, and finite low/high comparison scores are proved using `GaussianOffsetSignalFamily`; downstream theorem rows track their own remaining source-equilibrium or mixture obligations. |
| Definition 1, equilibrium | `LG21AccessAction`, `LG21AccessAction.feasible`, `LG21AccessStudentInfo`, `LG21SourceEquilibriumData`, `lg21SourceEquilibrium`, `lg21SourceEquilibrium_iff`, `lg21SourceEquilibrium_feasible`, `lg21SourceEquilibrium_best_response`, `lg21SourceEquilibrium_estimationConsistent`, `LG21EquilibriumData`, `lg21Equilibrium`, `lg21NoProfitableWithholdingDeviation_of_reporting_equilibrium`, `lg21NoProfitableTestTakingDeviation_of_taking_equilibrium`, `lg21NoProfitableBinaryChoiceDeviation`, `lg21NoProfitableBinaryChoiceDeviation_of_reporting_equilibrium`, `lg21NoProfitableBinaryChoiceDeviation_of_taking_equilibrium`, `lg21NoProfitableBinaryChoiceDeviation_of_optional_reporting_source_model`, `lg21NoProfitableBinaryChoiceDeviation_of_base_optional_reporting_source_model`, `lg21NoProfitableBinaryChoiceDeviation_of_report_required_source_model`, `lg21NoProfitableBinaryChoiceDeviation_of_base_report_required_source_model` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | The paper's concrete `(Y,X)` action object, feasibility condition `Y ≥ X`, optional-reporting regime, report-required regime `Y = X`, access-student information `(q, base, test)`, source decision functions `Y(q, base)` and `X(base, test)`, feasibility, best-response, and estimation-consistency projections are encoded directly. Binary reporting and test-taking subgames derive one-sided no-profitable-deviation predicates used in Lemma 4.1 and two-sided best-response predicates used in Theorem 3.1 and Theorem 3.2 from `lg21Equilibrium` or the concrete source payoff model. The optional-reporting and report-required source payoff models also have base-indexed variants, so reported-score, no-report, and taking estimates can depend definitionally on the non-test profile. The full Gaussian payoff/equilibrium instantiation is a later theorem-level obligation, not a remaining Definition 1 gap. |
| Definition 2, latent skill fairness | `lg21SourceLatentSkillFair`, `lg21SourceLawLatentSkillFair`, `paper_interface_definition2_latent_skill_fair_iff`, `paper_interface_definition2_law_latent_skill_fair_iff` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | Source equality of estimate laws conditional on equilibrium, skill, and observed base features is encoded over both PMF and arbitrary continuous-law surfaces, with explicit paper-interface unfold lemmas. |
| Definition 3, observable fairness | `lg21SourceObservablyFair`, `lg21SourceLawObservablyFair`, `lg21ObservableFair`, `paper_interface_definition3_observably_fair_iff`, `paper_interface_definition3_law_observably_fair_iff` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | Source equilibrium-quantified equality is encoded over PMF and arbitrary law surfaces, with explicit paper-interface unfold lemmas; finite kernel equality remains available for resampling. |
| Definition 4, demographic fairness | `lg21SourceDemographicallyFair`, `lg21SourceLawDemographicallyFair`, `paper_interface_definition4_demographically_fair_iff`, `paper_interface_definition4_law_demographically_fair_iff`, `lg21DemographicallyFair`, `lg21DemographicEstimateDistribution`, `lg21_sourceObservablyFair_of_latentSkillFair_of_mixture`, `lg21_sourceDemographicallyFair_of_observablyFair_of_mixture`, `lg21_demographicallyFair_of_observableFair` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | Source equilibrium-quantified equality is encoded over PMF and arbitrary law surfaces, with explicit paper-interface unfold lemmas. The paper's implication chain latent skill fairness implies observable fairness implies demographic fairness is proved for the finite PMF surface under explicit shared skill/base mixture identities. |
| Definition 5, test-blank policies | `lg21SourceTestBlank`, `lg21SourceLawTestBlank`, `paper_interface_definition5_test_blank_iff`, `paper_interface_definition5_law_test_blank_iff`, `lg21_not_testBlank_iff_exists_witness`, `lg21_not_lawTestBlank_iff_exists_witness` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | Source statement that base-only and full-feature estimate laws agree in every equilibrium is encoded over abstract PMF and continuous-law surfaces, with explicit paper-interface unfold lemmas and equivalent witness forms for concrete base/test relevance. |
| Theorem 3.1, strategic withholding | `paper_theorem3_1_reporting_threshold_of_gaussian_best_response`, `LG21OptionalReportingStrategicWithholdingSourceWitness`, `lg21OptionalReportingGaussianStrategicWithholdingSourceWitness`, `paper_theorem3_1_optional_reporting_threshold_conclusions_of_gaussian_best_response`, `paper_interface_theorem3_1_optional_reporting_threshold_conclusions_of_gaussian_best_response`, `paper_theorem3_1_optional_reporting_threshold_equilibrium_exists_of_crossing`, `paper_interface_theorem3_1_optional_reporting_threshold_equilibrium_exists_of_crossing`, `paper_theorem3_1_optional_reporting_source_witness_of_base_crossings`, `paper_interface_theorem3_1_optional_reporting_source_witness_of_base_crossings`, `paper_theorem3_1_optional_reporting_gaussian_source_witness_of_crossings`, `paper_interface_theorem3_1_optional_reporting_gaussian_source_witness_of_crossings`, `paper_theorem3_1_optional_reporting_gaussian_best_response_nontrivial`, `paper_interface_theorem3_1_optional_reporting_gaussian_best_response_nontrivial`, `paper_theorem3_1_optional_reporting_gaussian_threshold_of_best_response_tiebreak`, `paper_interface_theorem3_1_optional_reporting_gaussian_threshold_of_best_response_tiebreak`, `paper_theorem3_1_optional_reporting_gaussian_source_witness_of_best_response_tiebreak`, `paper_interface_theorem3_1_optional_reporting_gaussian_source_witness_of_best_response_tiebreak`, `lg21OptionalNoReportMixtureEstimate`, `standardGaussian_normalCDF_mul_lowerTailMean_sub_tendsto_atBot`, `paper_theorem3_1_affine_lower_tail_mixture_low_endpoint_exists`, `paper_interface_theorem3_1_affine_lower_tail_mixture_low_endpoint_exists`, `paper_theorem3_1_optional_no_report_mixture_standard_lower_tail_continuous`, `paper_theorem3_1_optional_no_report_mixture_low_endpoint_exists`, `paper_interface_theorem3_1_optional_no_report_mixture_low_endpoint_exists`, `paper_theorem3_1_optional_no_report_mixture_high_endpoint_exists`, `paper_theorem3_1_optional_no_report_mixture_high_endpoint_exists_after`, `paper_interface_theorem3_1_optional_no_report_mixture_high_endpoint_exists`, `paper_interface_theorem3_1_optional_no_report_mixture_high_endpoint_exists_after`, `paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture_crossings`, `paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture_low_endpoint`, `paper_theorem3_1_optional_reporting_gaussian_source_witness_of_no_report_mixture`, `paper_interface_theorem3_1_optional_no_report_mixture_standard_lower_tail_continuous`, `LG21ReportRequiredStrategicWithholdingSourceWitness`, `paper_theorem3_1_report_required_threshold_equilibrium_exists_of_crossing`, `paper_interface_theorem3_1_report_required_threshold_equilibrium_exists_of_crossing`, `paper_theorem3_1_report_required_source_witness_of_base_crossings`, `paper_interface_theorem3_1_report_required_source_witness_of_base_crossings`, `paper_theorem3_1_report_required_affine_source_witness_of_crossings`, `paper_interface_theorem3_1_report_required_affine_source_witness_of_crossings`, `paper_theorem3_1_report_required_affine_best_response_nontrivial`, `paper_interface_theorem3_1_report_required_affine_best_response_nontrivial`, `paper_theorem3_1_report_required_affine_threshold_of_best_response_tiebreak`, `paper_interface_theorem3_1_report_required_affine_threshold_of_best_response_tiebreak`, `paper_theorem3_1_report_required_affine_source_witness_of_best_response_tiebreak`, `paper_interface_theorem3_1_report_required_affine_source_witness_of_best_response_tiebreak`, `paper_theorem3_1_report_required_no_take_mixture_standard_lower_tail_continuous`, `paper_theorem3_1_report_required_no_take_mixture_low_endpoint_exists`, `paper_interface_theorem3_1_report_required_no_take_mixture_low_endpoint_exists`, `paper_theorem3_1_report_required_no_take_mixture_high_endpoint_exists`, `paper_theorem3_1_report_required_no_take_mixture_high_endpoint_exists_after`, `paper_interface_theorem3_1_report_required_no_take_mixture_high_endpoint_exists`, `paper_interface_theorem3_1_report_required_no_take_mixture_high_endpoint_exists_after`, `paper_theorem3_1_report_required_affine_source_witness_of_no_take_mixture_crossings`, `paper_theorem3_1_report_required_affine_source_witness_of_no_take_mixture_low_endpoint`, `paper_theorem3_1_report_required_affine_source_witness_of_no_take_mixture`, `lt_lg21OptionalNoReportMixtureEstimate_of_lt_components`, `lg21OptionalNoReportMixtureEstimate_lt_of_components_lt`, `paper_theorem3_1_optional_reporting_strategic_withholding_of_source_witness`, `paper_theorem3_1_optional_reporting_strategic_withholding_of_no_report_mixture`, `paper_theorem3_1_optional_reporting_law_strategic_withholding_of_source_witness`, `paper_theorem3_1_optional_reporting_law_strategic_withholding_of_no_report_mixture`, `paper_interface_theorem3_1_optional_reporting_law_strategic_withholding_of_source_witness`, `paper_base_indexed_one_test_posterior_source_law_not_observably_fair`, `paper_base_indexed_one_test_posterior_source_law_not_demographically_fair`, `paper_theorem3_1_optional_reporting_law_strategic_withholding_of_no_report_mixture_and_base_indexed_one_test_posterior_surface`, `paper_interface_theorem3_1_optional_reporting_law_strategic_withholding_of_no_report_mixture_and_base_indexed_one_test_posterior_surface`, `paper_theorem3_1_report_required_strategic_withholding_of_source_witness`, `paper_theorem3_1_report_required_strategic_withholding_of_no_take_mixture`, `paper_theorem3_1_report_required_law_strategic_withholding_of_source_witness`, `paper_theorem3_1_report_required_law_strategic_withholding_of_no_take_mixture`, `paper_theorem3_1_report_required_law_strategic_withholding_of_no_take_mixture_and_base_indexed_one_test_posterior_surface`, `paper_interface_theorem3_1_report_required_law_strategic_withholding_of_no_take_mixture_and_base_indexed_one_test_posterior_surface`, `LG21SkillBaseMixtureEstimateLaw`, `lg21BaseMixedOneTestPosteriorLawSurface`, `lg21BaseMixedGaussianPosteriorLawSurface`, `lg21BaseMixedAffineSkillPosteriorLawSurface`, `paper_theorem3_1_optional_reporting_law_strategic_withholding_of_no_report_mixture_and_base_mixed_gaussian_posterior_surface`, `paper_interface_theorem3_1_optional_reporting_law_strategic_withholding_of_no_report_mixture_and_base_mixed_gaussian_posterior_surface`, `paper_theorem3_1_report_required_law_strategic_withholding_of_no_take_mixture_and_base_mixed_affine_skill_posterior_surface`, `paper_interface_theorem3_1_report_required_law_strategic_withholding_of_no_take_mixture_and_base_mixed_affine_skill_posterior_surface`, `paper_interface_theorem3_1_report_required_law_strategic_withholding_of_source_witness`, `lg21LowerCutoffStrategy`, `LG21StrategicWithholdingSourceWitness`, `lg21ThresholdStrategicWithholdingSourceWitness`, `paper_theorem3_1_threshold_conclusions_of_cutoff_functions`, `paper_interface_theorem3_1_threshold_conclusions_of_cutoff_functions`, `paper_theorem3_1_threshold_conclusions_of_source_witness`, `paper_theorem3_1_strategic_withholding_of_source_witness`, `paper_theorem3_1_law_strategic_withholding_of_source_witness`, `LG21StrategicWithholdingCertificate`, `paper_theorem3_1_strategic_withholding_of_certificate` | partially formalized | `MainTheorems.lean`, `PaperInterface.lean`, `EconCSLib/Foundations/Probability/GaussianMathlib.lean` | The Gaussian fixed-information reporting decision is proved to be a finite lower-cutoff rule in the reported test score, and all lower-cutoff rules are monotone. The source proof's nontriviality step is formalized: two-sided best response plus positive-slope Gaussian/affine payoffs rules out both everyone acting and no one acting. The tie-breaking threshold step is formalized in both policy regimes. The optional no-report and report-required no-take mixture formulas are encoded, continuous under `0 ≤ C < 1`, and now have automatic low and high endpoints from Gaussian Mills asymptotics and positive-slope affine algebra. The source-mixture crossing wrappers now choose both endpoints automatically, and PMF/law wrappers combine those closed source witnesses with concrete distribution-difference witnesses. The base-indexed one-test posterior law surface discharges the latent-skill, observable, and demographic law differences definitionally by Gaussian-vs-point non-equality for both optional-reporting and report-required Theorem 3.1 law endpoints. The stricter base/skill-mixture law surface now represents observable access laws as mixtures over latent skill and demographic laws as mixtures over base profiles, then packages the optional-reporting and report-required continuous-law endpoints over those source-shaped surfaces. Remaining Theorem 3.1 source work is now limited to an analogous finite PMF endpoint if that representation is desired, plus any later strengthening from the current closed source-mixture endpoint to the exact "every equilibrium" wording. |
| Theorem 3.2, fairness impossibility | `LG21FairnessImpossibilityCertificate`, `LG21LawFairnessImpossibilityCertificate`, `LG21ObservableFairTestBlankSourceWitness`, `LG21LawObservableFairTestBlankSourceWitness`, `paper_theorem3_2_nonblank_off_mean_witness_of_point_estimate_surface`, `paper_interface_theorem3_2_nonblank_off_mean_witness_of_point_estimate_surface`, `paper_theorem3_2_law_nonblank_off_mean_witness_of_point_estimate_surface`, `paper_interface_theorem3_2_law_nonblank_off_mean_witness_of_point_estimate_surface`, `paper_theorem3_2_observable_fair_best_response_implies_test_blank_of_point_estimate_source`, `paper_interface_theorem3_2_observable_fair_best_response_implies_test_blank_of_point_estimate_source`, `paper_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_point_estimate_source`, `paper_interface_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_point_estimate_source`, `paper_theorem3_2_fairness_impossibility_of_certificate`, `paper_theorem3_2_law_fairness_impossibility_of_certificate`, `lg21_pmf_mixture_cancel_right`, `lg21_extensional_law_mixture_cancel_right`, `paper_theorem3_2_observable_fair_resampling_forces_reporter_no_reporter_law_eq`, `paper_interface_theorem3_2_observable_fair_resampling_forces_reporter_no_reporter_law_eq`, `paper_theorem3_2_law_observable_fair_resampling_forces_reporter_no_reporter_law_eq`, `paper_interface_theorem3_2_law_observable_fair_resampling_forces_reporter_no_reporter_law_eq`, `paper_theorem3_2_affine_resampling_mean_payoff_le`, `paper_theorem3_2_affine_resampling_mean_payoff_lt`, `paper_theorem3_2_resampling_law_equality_unstable_of_below_mean_actor`, `paper_theorem3_2_exists_support_actor_le_mean`, `paper_interface_theorem3_2_exists_support_actor_le_mean`, `paper_theorem3_2_exists_support_actor_lt_mean_of_exists_mean_lt_actor`, `paper_interface_theorem3_2_exists_support_actor_lt_mean_of_exists_mean_lt_actor`, `paper_theorem3_2_observable_fair_positive_reporting_resampling_unstable`, `paper_interface_theorem3_2_observable_fair_positive_reporting_resampling_unstable`, `paper_theorem3_2_observable_fair_positive_reporting_below_mean_actor_unstable`, `paper_interface_theorem3_2_observable_fair_positive_reporting_below_mean_actor_unstable`, `paper_theorem3_2_law_observable_fair_positive_reporting_below_mean_actor_unstable`, `paper_interface_theorem3_2_law_observable_fair_positive_reporting_below_mean_actor_unstable`, `paper_theorem3_2_observable_fair_positive_reporting_nondegenerate_actor_distribution_unstable`, `paper_interface_theorem3_2_observable_fair_positive_reporting_nondegenerate_actor_distribution_unstable`, `paper_theorem3_2_law_observable_fair_positive_reporting_nondegenerate_actor_distribution_unstable`, `paper_interface_theorem3_2_law_observable_fair_positive_reporting_nondegenerate_actor_distribution_unstable`, `paper_theorem3_2_observable_fair_best_response_forces_no_above_mean_actor`, `paper_interface_theorem3_2_observable_fair_best_response_forces_no_above_mean_actor`, `paper_theorem3_2_law_observable_fair_best_response_forces_no_above_mean_actor`, `paper_interface_theorem3_2_law_observable_fair_best_response_forces_no_above_mean_actor`, `paper_theorem3_2_exists_support_actor_gt_mean_of_exists_actor_lt_mean`, `paper_interface_theorem3_2_exists_support_actor_gt_mean_of_exists_actor_lt_mean`, `paper_theorem3_2_no_above_mean_actor_forces_support_at_mean`, `paper_interface_theorem3_2_no_above_mean_actor_forces_support_at_mean`, `paper_theorem3_2_observable_fair_best_response_forces_actor_support_at_mean`, `paper_interface_theorem3_2_observable_fair_best_response_forces_actor_support_at_mean`, `paper_theorem3_2_law_observable_fair_best_response_forces_actor_support_at_mean`, `paper_interface_theorem3_2_law_observable_fair_best_response_forces_actor_support_at_mean`, `paper_theorem3_2_support_at_mean_forces_no_distinct_positive_mass_actor_values`, `paper_interface_theorem3_2_support_at_mean_forces_no_distinct_positive_mass_actor_values`, `paper_theorem3_2_observable_fair_best_response_forces_no_distinct_positive_mass_actor_values`, `paper_interface_theorem3_2_observable_fair_best_response_forces_no_distinct_positive_mass_actor_values`, `paper_theorem3_2_law_observable_fair_best_response_forces_no_distinct_positive_mass_actor_values`, `paper_interface_theorem3_2_law_observable_fair_best_response_forces_no_distinct_positive_mass_actor_values`, `paper_theorem3_2_observable_fair_best_response_implies_test_blank_of_distinct_positive_mass_actor_witness`, `paper_interface_theorem3_2_observable_fair_best_response_implies_test_blank_of_distinct_positive_mass_actor_witness`, `paper_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_distinct_positive_mass_actor_witness`, `paper_interface_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_distinct_positive_mass_actor_witness`, `paper_theorem3_2_observable_fair_best_response_implies_test_blank_of_off_mean_positive_mass_actor_witness`, `paper_interface_theorem3_2_observable_fair_best_response_implies_test_blank_of_off_mean_positive_mass_actor_witness`, `paper_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_off_mean_positive_mass_actor_witness`, `paper_interface_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_off_mean_positive_mass_actor_witness`, `paper_theorem3_2_observable_fair_best_response_implies_test_blank_of_source_witness`, `paper_interface_theorem3_2_observable_fair_best_response_implies_test_blank_of_source_witness`, `paper_theorem3_2_fairness_impossibility_of_mixture_and_source_witness`, `paper_interface_theorem3_2_fairness_impossibility_of_mixture_and_source_witness`, `paper_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_source_witness`, `paper_interface_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_source_witness`, `paper_theorem3_2_law_fairness_impossibility_of_observable_implication_and_source_witness`, `paper_interface_theorem3_2_law_fairness_impossibility_of_observable_implication_and_source_witness`, `paper_theorem3_2_fairness_impossibility_of_observable_implication_and_mixture`, `paper_interface_theorem3_2_fairness_impossibility_of_observable_implication_and_mixture`, `paper_theorem3_2_law_fairness_impossibility_of_observable_implication`, `paper_interface_theorem3_2_law_fairness_impossibility_of_observable_implication`, `paper_theorem3_2_no_test_relevance_of_fairness`, `paper_theorem3_2_law_no_test_relevance_of_fairness`, `paper_theorem3_2_not_latent_or_observable_fair_of_test_relevance_witness`, `paper_theorem3_2_not_law_latent_or_observable_fair_of_test_relevance_witness`, `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_optional_base_affine_binary_mixture_point_estimate_distinct_supported_tests_of_event_share_constant_latent`, `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_report_required_base_affine_binary_mixture_point_estimate_distinct_supported_tests_of_event_share_centered_baseTerm_constant_latent` | conditional | `MainTheorems.lean`, `PaperInterface.lean` | Endpoint states latent or observable fairness implies test-blankness over both PMF and arbitrary law surfaces. Test-blankness is equivalent to absence of a concrete base/test relevance witness, so the theorem also has no-relevance and contrapositive forms. The source proof's positive-share resampling algebra is formalized: observable fairness plus `λD1 + (1-λ)D0` with `λ > 0` forces `D1 = D0`; finite acting-distribution support lemmas prove weak below-mean existence and strict below-mean existence under nondegeneracy; the affine posterior-payoff comparison gives a strict best-response contradiction for nondegenerate positive-share acting distributions. Turning this around now proves no positive mass above the acting mean, support-at-mean for every positive-mass actor, and no two positive-mass actors with distinct values under observable fairness plus two-sided best response. PMF/law bridges prove observable fairness implies test-blankness once the source model supplies either a final non-test-blank-to-off-mean positive-mass actor witness or the stronger distinct-positive-mass-actor witness. The source-shaped witness structures now package the mixture, best-response, payoff, and off-mean obligations and feed paper-facing Theorem 3.2 endpoints without the old tautological certificate. The point-estimate constructors close the off-mean witness for deterministic scalar PMF/point-law surfaces, and direct point-estimate source endpoints now combine that with the mixture, best-response, and affine-payoff bridge. The optional-reporting base-affine binary-mixture endpoint makes the paper's reported-score and no-report payoff identities definitional. Constant-latent concrete optional and report-required event-share wrappers now discharge the latent-to-observable mixture identities for skill-independent latent kernels. The older finite point-mass route remains available if one wants that exact finite endpoint; its remaining obligations are the displayed positive-mass/support facts. The active source route is the direct below-mean actor branch: cutoff-midpoint and Gaussian all-acting wrappers now avoid point-mass assumptions, so remaining source work is to connect the paper's final policy assumptions to one of those branches and decide whether a skill-dependent conditional-kernel route is needed for the final source-facing statement. |
| Lemma 4.1, strategy-proofness when access is observed | `GaussianLowerTailMeanCertificate`, `standardGaussianLowerTailMeanCertificate`, `paper_lemma4_1_reporting_cutoff_has_profitable_deviation_core`, `paper_lemma4_1_gaussian_reporting_cutoff_has_profitable_deviation`, `paper_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding`, `paper_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding_from_cutoff`, `paper_lemma4_1_report_cutoff_estimate_lt_of_lower_tail_score`, `paper_lemma4_1_all_report_of_gaussian_lower_tail_certificate_no_profitable_withholding`, `paper_lemma4_1_all_report_of_gaussian_threshold_policy_lower_tail_no_profitable_withholding`, `paper_lemma4_1_take_test_cutoff_has_profitable_deviation`, `paper_lemma4_1_no_nontrivial_take_test_cutoff_of_no_profitable_deviation`, `paper_lemma4_1_all_take_of_gaussian_lower_tail_certificate_no_profitable_test_taking`, `paper_lemma4_1_all_take_of_explicit_lower_tail_threshold_no_profitable_test_taking`, `lg21NoProfitableWithholdingDeviation_of_source_optional_equilibrium`, `lg21OptionalReportingSourceEquilibriumData`, `lg21NoProfitableWithholdingDeviation_of_optional_reporting_source_model`, `lg21ReportRequiredSourceEquilibriumData`, `lg21NoProfitableTestTakingDeviation_of_report_required_source_model`, `lg21NoProfitableTestTakingDeviation_of_source_report_required_equilibrium`, `lg21FullySpecifiedOptionalReportingSourceEquilibriumData`, `lg21FullySpecifiedReportRequiredSourceEquilibriumData`, `paper_lemma4_1_strategy_proofness_of_source_equilibrium_projections`, `paper_lemma4_1_strategy_proofness_of_concrete_source_models`, `paper_lemma4_1_strategy_proofness_of_concrete_threshold_source_models`, `paper_lemma4_1_strategy_proofness_of_fully_specified_threshold_source_models`, `paper_lemma4_1_optional_reporting_chosen_action_take_and_report_of_fully_specified_source_model`, `paper_lemma4_1_report_required_chosen_action_take_and_report_of_fully_specified_source_model`, `paper_lemma4_1_observed_access_chosen_actions_of_fully_specified_source_models`, `paper_interface_lemma4_1_observed_access_chosen_actions_of_fully_specified_source_models`, `paper_lemma4_1_strategy_proofness_of_lower_tail_thresholds`, `paper_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_lower_tail_taking`, `paper_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_explicit_taking_threshold`, `paper_lemma4_1_strategy_proofness_of_explicit_threshold_equilibria`, `LG21GaussianThresholdEquilibriumCertificate`, `paper_lemma4_1_strategy_proofness_of_threshold_equilibrium_certificate`, `LG21ObservedAccessStrategyProofCertificate`, `paper_lemma4_1_strategy_proofness_of_certificate` | formalized | `MainTheorems.lean`, `PaperInterface.lean`, `EconCSLib/Foundations/Probability/Gaussian.lean`, `EconCSLib/Foundations/Probability/GaussianMathlib.lean` | The optional-reporting proof now has the continuous strictly increasing cutoff-deviation core, its Gaussian posterior-score instantiation, and source-shaped lower-tail bridges using the shared lower-tail-mean certificate. Source Definition 1 best-response directly implies the no-profitable-withholding and no-profitable-test-taking predicates; concrete optional-reporting and report-required source payoff models make those payoff identities definitional; concrete threshold source models make reporting/taking threshold shapes definitional; and the fully specified source models build in the lower-tail no-report/no-test estimates. The source-model endpoint now proves the paper's `(Y, X) = (1, 1)` conclusion for every access-student information tuple in both observed-access regimes. Downstream Proposition 4.2/4.3 work should use this as a closed Lemma 4.1 input rather than treating Lemma 4.1 as the blocker. |
| Proposition 4.2, Bayesian optimal on access students is not latent skill fair | `paper_proposition4_2_not_law_latent_skill_fair_of_four_group_core`, `paper_proposition4_2_not_law_latent_skill_fair_of_gaussian_mean_gap`, `paper_proposition4_2_not_law_latent_skill_fair_of_conditional_posterior_mean_gap`, `paper_proposition4_2_not_estimate_law_latent_skill_fair_of_conditional_posterior_mean_gap`, `paper_proposition4_2_not_estimate_law_latent_skill_fair_of_one_test_posterior_law`, `paper_proposition4_2_not_latent_skill_fair_of_lemma4_1_lower_tail_and_one_test_posterior_law`, `paper_proposition4_2_not_latent_skill_fair_of_explicit_thresholds_and_one_test_posterior_law`, `paper_proposition4_2_not_latent_skill_fair_of_threshold_equilibria_and_one_test_posterior_law`, `paper_proposition4_2_not_latent_skill_fair_of_threshold_equilibrium_certificate_and_one_test_posterior_law`, `paper_proposition4_2_not_latent_skill_fair_of_fully_specified_observed_access_source_models_and_one_test_posterior_law`, `paper_interface_proposition4_2_not_latent_skill_fair_of_fully_specified_observed_access_source_models_and_one_test_posterior_law`, `lg21FixedBaseOneTestPosteriorLawSurface`, `paperFixedBaseOneTestPosteriorLawSurface`, `paper_proposition4_2_not_latent_skill_fair_of_fixed_base_one_test_posterior_source_law`, `paper_proposition4_2_not_latent_skill_fair_of_fully_specified_source_models_and_fixed_base_one_test_posterior_surface`, `paper_interface_proposition4_2_not_latent_skill_fair_of_fully_specified_source_models_and_fixed_base_one_test_posterior_surface`, `lg21BaseIndexedOneTestPosteriorLawSurface`, `paperBaseIndexedOneTestPosteriorLawSurface`, `paper_proposition4_2_not_latent_skill_fair_of_base_indexed_one_test_posterior_source_law`, `paper_proposition4_2_not_latent_skill_fair_of_fully_specified_source_models_and_base_indexed_one_test_posterior_surface`, `paper_interface_proposition4_2_not_latent_skill_fair_of_fully_specified_source_models_and_base_indexed_one_test_posterior_surface`, `LG21NotLatentFairCertificate`, `paper_proposition4_2_not_latent_skill_fair_of_certificate` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | The source four-group equality argument is proved over arbitrary law objects. Gaussian mean gaps, concrete conditional posterior-score laws, and base-indexed one-random-test posterior source-law surfaces now supply the access-side law difference when latent skills are strictly ordered, including source-shaped `LG21EstimateLaw` wrappers. Source-route wrappers consume Lemma 4.1's lower-tail, explicit-threshold, binary-equilibrium, packaged threshold-equilibrium-certificate, and fully specified observed-access source-action routes. The base-indexed source-law surface discharges the no-access/access law identities definitionally and proves latent-skill unfairness without law-equality assumptions. |
| Proposition 4.3, full Bayesian optimal policy is not observable or demographic fair | `paper_proposition4_3_not_law_observable_or_demographic_fair_of_witnesses`, `paper_proposition4_3_not_law_observable_fair_of_gaussian_variance_gap`, `paper_proposition4_3_not_law_demographic_fair_of_gaussian_variance_gap`, `paper_proposition4_3_not_estimate_law_observable_fair_of_access_gaussian_no_access_point`, `paper_proposition4_3_not_estimate_law_observable_fair_of_one_test_posterior_law_vs_point`, `paper_proposition4_3_not_law_observable_fair_of_posterior_precision_gap`, `paper_proposition4_3_not_law_demographic_fair_of_posterior_precision_gap`, `paper_proposition4_3_not_law_observable_or_demographic_fair_of_lemma4_1_lower_tail_and_posterior_precision_gap`, `paper_proposition4_3_not_law_observable_or_demographic_fair_of_lemma4_1_lower_tail_and_extra_signal`, `paper_proposition4_3_not_law_observable_or_demographic_fair_of_explicit_thresholds_and_extra_signal`, `paper_proposition4_3_not_law_observable_or_demographic_fair_of_threshold_equilibria_and_extra_signal`, `paper_proposition4_3_not_law_observable_or_demographic_fair_of_threshold_equilibrium_certificate_and_extra_signal`, `paper_proposition4_3_not_law_observable_or_demographic_fair_of_fully_specified_observed_access_source_models_and_extra_signal`, `paper_interface_proposition4_3_not_law_observable_or_demographic_fair_of_fully_specified_observed_access_source_models_and_extra_signal`, `lg21ExtraSignalPosteriorLawSurface`, `paperExtraSignalPosteriorLawSurface`, `paper_proposition4_3_not_law_observable_or_demographic_fair_of_extra_signal_source_law`, `paper_proposition4_3_not_law_observable_or_demographic_fair_of_fully_specified_source_models_and_extra_signal_surface`, `paper_interface_proposition4_3_not_law_observable_or_demographic_fair_of_fully_specified_source_models_and_extra_signal_surface`, `lg21BaseIndexedExtraSignalPosteriorLawSurface`, `paperBaseIndexedExtraSignalPosteriorLawSurface`, `paper_proposition4_3_not_law_observable_fair_of_base_indexed_extra_signal_source_law`, `paper_proposition4_3_not_law_demographic_fair_of_base_indexed_extra_signal_source_law_chosen_base`, `paper_interface_proposition4_3_not_law_observable_fair_of_base_indexed_extra_signal_source_law`, `paper_interface_proposition4_3_not_law_demographic_fair_of_base_indexed_extra_signal_source_law_chosen_base`, `LG21GaussianMixtureLaw`, `lg21BaseMixedExtraSignalPosteriorLawSurface`, `paperBaseMixedExtraSignalPosteriorLawSurface`, `paper_proposition4_3_not_law_observable_or_demographic_fair_of_base_mixed_extra_signal_source_law`, `paper_interface_proposition4_3_not_law_observable_or_demographic_fair_of_base_mixed_extra_signal_source_law`, `paper_proposition4_3_not_law_observable_or_demographic_fair_of_fully_specified_source_models_and_base_mixed_extra_signal_surface`, `paper_interface_proposition4_3_not_law_observable_or_demographic_fair_of_fully_specified_source_models_and_base_mixed_extra_signal_surface`, `LG21NotObservableOrDemographicFairCertificate`, `paper_proposition4_3_not_observable_or_demographic_fair_of_certificate` | formalized | `MainTheorems.lean`, `PaperInterface.lean`, `EconCSLib/Foundations/Probability/Gaussian.lean` | The law-level observable/demographic witness arguments, Gaussian variance/scale-gap contradictions, posterior-score signal-precision instantiations, the source-shaped observable point-vs-Gaussian contradiction, and its fixed-base one-random-test posterior-law form are proved. Source-route wrappers now consume Lemma 4.1's lower-tail, explicit-threshold, binary-equilibrium, packaged threshold-equilibrium-certificate, and fully specified observed-access source-action routes. The common paper case where access observes one extra Gaussian test signal is closed by `GaussianOffsetSignalFamily.withExtraSignal`; concrete one-base, base-indexed, and base-mixture extra-signal source-law surfaces discharge observable and demographic law identities, with demographic laws represented as finite mixtures over the common base-profile distribution. |
| Definition 6, re-sampling policy | `LG21ResamplingExperiment`, `lg21ResamplingPolicyKernel`, `lg21AccessEstimateKernel`, `lg21ResamplingEstimateKernel`, `paper_definition6_resampling_policy_observable_kernel`, `paper_definition6_access_estimate_kernel_eq_map`, `paper_definition6_resampling_estimate_kernel_eq_map`, `paper_definition6_access_estimate_kernel_eq_resampling_estimate_kernel` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | The missing test score is sampled from the conditional test-score law given the non-test profile and then passed through the same estimate map used for access students. The access and re-sampled no-access estimate laws are explicitly unfolded as the same pushforward at each base profile. |
| Theorem 4.4, re-sampling policy is observable and demographic fair | `paper_theorem4_4_resampling_policy_observably_fair`, `paper_theorem4_4_resampling_policy_demographically_fair`, `paper_theorem4_4_resampling_policy_strategy_proof_observable_and_demographic_fair`, `paper_theorem4_4_resampling_policy_source_strategy_proof_observable_and_demographic_fair`, `paper_interface_theorem4_4_resampling_policy_source_strategy_proof_observable_and_demographic_fair` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | Finite distributional core is closed: access and no-access estimate laws are equal because they are pushforwards of the same conditional test-score law, and demographic fairness follows by mixing over the shared base-profile law. The source-model route now combines this resampling fairness core with the closed Lemma 4.1 observed-access action endpoint, yielding `(Y, X) = (1, 1)` plus observable and demographic fairness for the resampling policy. |
| Auxiliary finite admissions accounting support | `lg21_base_exp_decompose`, `lg21_test_exp_decompose`, and the related `lg21_*` mass/selection/monotonicity wrappers | formalized | `MainTheorems.lean` | None; auxiliary finite-kernel support only, not a source theorem wrapper. |

### Recent Theorem 3.1 Progress

- `lg21BaseIndexedGaussianPosteriorLawSurface` and
  `lg21BaseIndexedAffineSkillPosteriorLawSurface` now specialize the
  base-indexed one-test posterior law surface to the concrete Gaussian
  posterior maps used in the optional-reporting and report-required source
  routes.
- `paper_theorem3_1_optional_reporting_law_strategic_withholding_of_no_report_mixture_and_gaussian_posterior_surface`
  and
  `paper_theorem3_1_report_required_law_strategic_withholding_of_no_take_mixture_and_affine_skill_posterior_surface`
  combine the automatic source-mixture threshold witnesses with those concrete
  posterior-law surfaces, so the continuous-law Theorem 3.1 branch no longer
  has an uninstantiated posterior-surface parameter.
- `LG21SkillBaseMixtureEstimateLaw`,
  `lg21BaseMixedGaussianPosteriorLawSurface`, and
  `lg21BaseMixedAffineSkillPosteriorLawSurface` now represent observable laws
  as latent-skill mixtures and demographic laws as base-profile mixtures.  The
  optional-reporting and report-required base-mixed endpoints close the prior
  caveat about needing a stricter conditional-on-skill continuous-law surface.
- `LG21LawStrategicWithholdingCertificate` and
  `paper_theorem3_1_law_strategic_withholding_of_certificate` now mirror the
  compact PMF certificate endpoint for continuous-law surfaces, giving the
  Theorem 3.1 law route the same paper-facing closure pattern as the PMF route.
  The generic PMF and continuous-law source-witness routes now also construct
  those compact strategic-withholding certificates directly, so the top-level
  Theorem 3.1 certificate interface can consume source witnesses plus concrete
  unfairness witnesses without manual certificate assembly.

### Recent Theorem 3.2 Progress

- `paper_theorem3_2_observable_fair_best_response_forces_no_above_mean_actor`
  and
  `paper_theorem3_2_law_observable_fair_best_response_forces_no_above_mean_actor`
  now prove the no-nondegenerate-actor alternative: under observable fairness
  and two-sided best response, a positive-share acting distribution cannot put
  positive mass above its mean.  The finite support bridge
  `paper_theorem3_2_no_above_mean_actor_forces_support_at_mean` and the PMF/law
  wrappers
  `paper_theorem3_2_observable_fair_best_response_forces_actor_support_at_mean`
  and
  `paper_theorem3_2_law_observable_fair_best_response_forces_actor_support_at_mean`
  now strengthen this to support-at-mean: every positive-mass actor must equal
  the acting distribution mean.  The finite bridge
  `paper_theorem3_2_support_at_mean_forces_no_distinct_positive_mass_actor_values`
  and its PMF/law wrappers now also prove that observable fairness plus
  two-sided best response rules out two positive-mass actors with distinct
  values.  The new PMF/law bridges
  `paper_theorem3_2_observable_fair_best_response_implies_test_blank_of_distinct_positive_mass_actor_witness`
  and
  `paper_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_distinct_positive_mass_actor_witness`
  close observable fairness implies test-blankness once the full source model
  supplies the final non-test-blank-to-distinct-positive-mass-actor witness.
  The off-mean variants
  `paper_theorem3_2_observable_fair_best_response_implies_test_blank_of_off_mean_positive_mass_actor_witness`
  and
  `paper_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_off_mean_positive_mass_actor_witness`
  reduce that last witness to one positive-mass acting type whose value differs
  from the acting-distribution mean.  The direct below-mean branch
  `paper_theorem3_2_not_latent_or_observable_fair_of_mixture_and_below_mean_actor`
  and its law analogue
  `paper_theorem3_2_not_law_latent_or_observable_fair_of_observable_implication_and_below_mean_actor`
  now expose the paper proof's profitable-deviation step without any finite
  support or atom assumption: a source model can instead supply one currently
  acting score/skill below the resampling mean.  The optional-reporting and
  report-required source-model wrappers
  `paper_theorem3_2_not_latent_or_observable_fair_of_optional_reporting_base_affine_below_mean_actor`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_report_required_base_affine_below_mean_actor`
  derive the two-sided best-response premise directly from the concrete
  Definition 1 source equilibria.  The cutoff-midpoint wrappers
  `paper_theorem3_2_not_latent_or_observable_fair_of_optional_reporting_base_affine_cutoff_below_mean`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_report_required_base_affine_cutoff_below_mean`
  connect threshold strategies to this branch by choosing the midpoint between
  a below-mean cutoff and the resampling mean.  The contrapositive cutoff
  wrappers
  `paper_theorem3_2_optional_reporting_base_affine_cutoff_ge_mean_of_fair`
  and
  `paper_theorem3_2_report_required_base_affine_cutoff_ge_mean_of_fair`
  package the same argument as a source-facing necessary condition: any fair
  stable threshold policy must have cutoff weakly above the acting mean.  The
  finite actor-support lemma
  `paper_theorem3_2_cutoff_lt_actor_mean_of_support_ge_exists_gt` and the
  optional/report-required wrappers
  `paper_theorem3_2_not_latent_or_observable_fair_of_optional_reporting_base_affine_finite_actor_cutoff_support`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_report_required_base_affine_finite_actor_cutoff_support`
  formalize the finite version of the paper's "such a student always exists by
  the mean" step: a finite acting cohort supported weakly above the cutoff and
  with positive mass strictly above it has mean strictly above the cutoff.  The
  witness-level bridges
  `paper_theorem3_2_optional_reporting_threshold_witness_exists_below_mean_reporter`
  and
  `paper_theorem3_2_report_required_threshold_witness_exists_below_mean_taker`
  make the same midpoint argument directly for the Theorem 3.1 threshold
  source-witness structures.  The witness-level cutoff lower-bound wrappers
  `paper_theorem3_2_optional_reporting_threshold_witness_cutoff_ge_mean_of_fair`
  and
  `paper_theorem3_2_report_required_threshold_witness_cutoff_ge_mean_of_fair`
  now connect those Theorem 3.1 witnesses back to the concrete source decision
  functions and prove the same cutoff-above-mean necessary condition.  The
  Gaussian/all-acting wrappers
  `paper_theorem3_2_gaussianScaleLaw_exists_below_mean`,
  `paper_theorem3_2_not_latent_or_observable_fair_of_optional_reporting_base_affine_gaussian_all_report`,
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_report_required_base_affine_gaussian_all_take`
  instantiate the paper's "such a student always exists" line by choosing
  `mean - scale` from a nondegenerate Gaussian acting cohort, without requiring
  positive point mass.  The standard Gaussian upper-tail bridge
  `paper_theorem3_2_standardGaussian_upper_tail_mean_gt_threshold` and the
  optional/report-required wrappers
  `paper_theorem3_2_not_latent_or_observable_fair_of_optional_reporting_base_affine_gaussian_upper_tail_cutoff`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_report_required_base_affine_gaussian_upper_tail_cutoff`
  now cover thresholded Gaussian acting cohorts by proving that their
  upper-tail conditional mean is strictly above the cutoff.  The witness-level
  bridges
  `paper_theorem3_2_not_latent_or_observable_fair_of_optional_reporting_threshold_witness_gaussian_upper_tail_cutoff`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_report_required_threshold_witness_gaussian_upper_tail_cutoff`
  connect Theorem 3.1 threshold witnesses to those continuous Gaussian
  upper-tail branches.  The source-witness wrappers
  `paper_theorem3_2_not_latent_or_observable_fair_of_optional_reporting_source_witness_gaussian_upper_tail`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_report_required_source_witness_gaussian_upper_tail`
  now extract the finite cutoff directly from the Theorem 3.1 witness and only
  require the policy-specific identification of the witness cutoff with the
  Gaussian upper-tail acting mean.  The best-response wrappers
  `paper_theorem3_2_not_latent_or_observable_fair_of_optional_reporting_gaussian_best_response_source_witness_upper_tail`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_report_required_affine_best_response_source_witness_upper_tail`
  build those source witnesses from the concrete reporting/taking decisions
  using the Theorem 3.1 best-response and tie-breaking constructors, discharging
  the witness-to-decision identification premise.  The threshold-actor-mean
  endpoints
  `paper_theorem3_2_not_latent_or_observable_fair_of_optional_reporting_gaussian_best_response_upper_tail_threshold_actor_mean`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_report_required_affine_best_response_upper_tail_threshold_actor_mean`
  use the reusable uniqueness of real lower cutoffs to close the
  upper-tail-mean identification as well, for source models whose acting mean
  is defined from the concrete reporting/taking threshold.  The
  source-equilibrium wrappers
  `paper_theorem3_2_not_latent_or_observable_fair_of_optional_reporting_gaussian_source_equilibrium_upper_tail_threshold_actor_mean`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_report_required_source_equilibrium_upper_tail_threshold_actor_mean`
  derive the Theorem 3.1 best-response premises directly from the concrete
  base-indexed source equilibria, leaving only the Gaussian payoff identity,
  tie-breaking, threshold shape, and mixture/fairness-surface assumptions
  explicit.  The packaged endpoints
  `paper_theorem3_2_optional_reporting_fairness_impossibility_of_gaussian_upper_tail_source_equilibrium`
  and
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_source_equilibrium`
  now collect the source-equilibrium, Gaussian payoff, tie-breaking,
  threshold-shape, and positive-slope assumptions into auditable certificates,
  leaving only the selected reporter/no-reporter mixture comparison as
  theorem-local data.  The binary-mixture wrappers
  `paper_theorem3_2_optional_reporting_fairness_impossibility_of_gaussian_upper_tail_binary_mixture_source_equilibrium`
  and
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_binary_mixture_source_equilibrium`
  discharge that displayed mixture equality from `lg21BinaryMixturePMF`, so the
  concrete PMF route only needs the share positivity/no-access law and, in the
  report-required case, the outside-payoff equality.  The event-share
  specializations
  `paper_theorem3_2_optional_reporting_fairness_impossibility_of_gaussian_upper_tail_event_share_source_equilibrium`
  and
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_event_share_source_equilibrium`
  derive positive share from a finite positive-mass reporter/taker event.  The
  source-shaped
  structures
  `LG21ObservableFairTestBlankSourceWitness` and
  `LG21LawObservableFairTestBlankSourceWitness` now package these obligations,
  and `paper_theorem3_2_fairness_impossibility_of_mixture_and_source_witness`
  plus the law analogue give paper-facing endpoints without using the old
  tautological fairness-impossibility certificate.  The logical bridge
  `paper_theorem3_2_fairness_implies_test_blank_of_not_latent_or_observable_fair`
  also converts stronger contradiction-style continuous upper-tail branches
  back into the paper's exact "fairness implies test-blankness" conclusion;
  `paper_theorem3_2_law_fairness_implies_test_blank_of_not_latent_or_observable_fair`
  now provides the same conversion for abstract law surfaces.
  The point-estimate
  constructors
  `paper_theorem3_2_nonblank_off_mean_witness_of_point_estimate_surface` and
  `paper_theorem3_2_law_nonblank_off_mean_witness_of_point_estimate_surface`
  discharge the off-mean field for deterministic scalar PMF/point-law surfaces
  where the base-only estimate is the acting mean and the full-feature estimate
  is the selected actor value.  The direct point-estimate endpoints
  `paper_theorem3_2_observable_fair_best_response_implies_test_blank_of_point_estimate_source`
  and
  `paper_theorem3_2_law_observable_fair_best_response_implies_test_blank_of_point_estimate_source`
  combine that constructor with the mixture, best-response, and affine-payoff
  bridge.  The report-required wrappers
  `paper_theorem3_2_observable_fair_report_required_source_equilibrium_implies_test_blank_of_point_estimate_source`
  and
  `paper_theorem3_2_law_observable_fair_report_required_source_equilibrium_implies_test_blank_of_point_estimate_source`
  plus the optional-reporting analogues now derive the two-sided best-response
  field from the concrete source equilibrium models.  The PMF helper
  `lg21BinaryMixturePMF` and wrapper
  `paper_theorem3_2_observable_fair_best_response_implies_test_blank_of_binary_mixture_point_estimate_source`
  now discharge the positive-share mixture identity when the observable-access
  law is built as a Bernoulli reporter/no-reporter mixture.  The report-required
  and optional-reporting endpoints
  `paper_theorem3_2_observable_fair_report_required_source_equilibrium_implies_test_blank_of_binary_mixture_point_estimate_source`
  and
  `paper_theorem3_2_observable_fair_optional_reporting_source_equilibrium_implies_test_blank_of_binary_mixture_point_estimate_source`
  now combine that mixture wrapper with the concrete Definition 1 best-response
  bridges.  The optional-reporting source model now also has a base-indexed
  concrete payoff bridge, and
  `paper_theorem3_2_observable_fair_optional_reporting_source_equilibrium_implies_test_blank_of_base_affine_binary_mixture_point_estimate_source`
  uses it to make the paper's affine reported-score and no-report estimates
  definitional in the optional-reporting binary-mixture endpoint.  The concrete
  surface constructor `lg21BinaryMixturePointEstimateSurface` and endpoint
  `paper_theorem3_2_observable_fair_optional_reporting_source_equilibrium_implies_test_blank_of_concrete_base_affine_binary_mixture_point_estimate_surface`
  now make the observable mixture, no-access, base-only, and full-feature
  point-estimate identities definitional as well.  The concrete fairness
  endpoint
  `paper_theorem3_2_fairness_impossibility_of_concrete_optional_base_affine_binary_mixture_point_estimate_surface`
  adds the paper's latent-to-observable mixture reduction, so latent fairness
  or observable fairness forces test-blankness for this concrete optional
  surface.  The `_self_law` version uses the reporter/no-reporter PMFs
  themselves as the finite law objects, removing the redundant abstract
  PMF-to-law equality bridge from this route.  The report-required endpoint
  `paper_theorem3_2_observable_fair_report_required_source_equilibrium_implies_test_blank_of_base_affine_binary_mixture_point_estimate_source`
  now makes the base-indexed affine taking payoff definitional too, and
  `paper_theorem3_2_fairness_impossibility_of_concrete_report_required_base_affine_binary_mixture_point_estimate_surface_self_law`
  routes this through the same concrete binary-mixture point-estimate surface
  and latent-to-observable mixture reduction.  The centered-outside variant
  `paper_theorem3_2_fairness_impossibility_of_concrete_report_required_base_affine_binary_mixture_point_estimate_surface_self_law_of_centered_outside`
  reduces the report-required outside-payoff identity to the algebraic
  condition that the affine numerator at the resampling mean is half the
  denominator.  The direct contradiction
  `paper_theorem3_2_not_latent_or_observable_fair_of_point_estimate_witness`
  now converts any latent-or-observable-fairness-to-test-blank route into
  explicit unfairness from a point-estimate test witness off the acting mean.
  The optional-reporting concrete endpoint
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_optional_base_affine_binary_mixture_point_estimate_witness`
  applies this directly to the optional binary-mixture surface, and the
  report-required analogue
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_report_required_base_affine_binary_mixture_point_estimate_witness_of_centered_outside`
  applies it under the centered outside-payoff identity.  The remaining source
  gap is discharging the final paper policy assumptions for the concrete
  optional/report-required surfaces.  A distinct-tests bridge
  `paper_theorem3_2_not_latent_or_observable_fair_of_distinct_point_estimate_tests`
  now lets those direct endpoints use two different full-feature point
  estimates as the paper-facing test-relevance witness.  The concrete optional
  and report-required endpoints
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_optional_base_affine_binary_mixture_point_estimate_distinct_tests`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_report_required_base_affine_binary_mixture_point_estimate_distinct_tests_of_centered_outside`
  expose this condition directly on the binary-mixture point-estimate surfaces.
  The localized supported-test variants
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_optional_base_affine_binary_mixture_point_estimate_distinct_supported_tests`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_report_required_base_affine_binary_mixture_point_estimate_distinct_supported_tests_of_centered_outside`
  reduce the support obligation to the two displayed tests rather than all
  tests in the feature space.  The event-share helpers
  `lg21PMFEventShare`, `lg21PMFEventShare_le_one`, and
  `lg21PMFEventShare_pos_of_mass` package finite reporter/taker event
  probabilities as `NNReal` shares, discharging the `positiveShare ≤ 1` and
  `0 < positiveShare` bookkeeping from ordinary positive-mass event witnesses.
  The event-share concrete endpoints
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_optional_base_affine_binary_mixture_point_estimate_distinct_supported_tests_of_event_share`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_report_required_base_affine_binary_mixture_point_estimate_distinct_supported_tests_of_event_share_centered_outside`
  wire those shares directly into the optional-reporting and report-required
  binary-mixture surfaces.  The report-required
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_report_required_base_affine_binary_mixture_point_estimate_distinct_supported_tests_of_event_share_centered_baseTerm`
  endpoint replaces the centered-numerator outside-payoff premise with the
  auditable base-term identity
  `baseTerm = denom / 2 - signalWeight * mean`.
  The constant-latent variants
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_optional_base_affine_binary_mixture_point_estimate_distinct_supported_tests_of_event_share_constant_latent`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_report_required_base_affine_binary_mixture_point_estimate_distinct_supported_tests_of_event_share_centered_baseTerm_constant_latent`
  discharge the latent-to-observable mixture identities for the concrete
  event-share surfaces when the latent estimate kernels are skill-independent
  versions of the observable laws.  For the finite binary-mixture route, the
  remaining concrete assumptions are the two displayed positive-support facts
  and the report-required base-term identity.  The mapped-actor-law
  variants
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_optional_base_affine_binary_mixture_point_estimate_distinct_supported_tests_of_event_share_constant_latent_mapped_actor_law`
  and
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_report_required_base_affine_binary_mixture_point_estimate_distinct_supported_tests_of_event_share_centered_baseTerm_constant_latent_mapped_actor_law`
  further reduce the displayed actor-support assumptions to positive mass for
  the displayed concrete test/skill values under a pushforward acting law.  A
  centered-base-term specialization
  `paper_theorem3_2_not_latent_or_observable_fair_of_concrete_report_required_base_affine_binary_mixture_point_estimate_distinct_supported_tests_of_event_share_centered_baseTerm_constant_latent_mapped_actor_law_by_definition`
  defines the report-required base term as
  `denom / 2 - signalWeight * mean`, closing the remaining outside-payoff
  algebra by construction for that normalized affine source model.  A
  stricter
  skill-dependent latent-kernel instantiation can be added later if the final
  statement insists on conditional-on-skill laws rather than this direct
  constant-kernel specialization.  The continuous upper-tail route now has
  certificate-packaged source-equilibrium endpoints that derive best responses
  from the concrete optional/report-required source games.  For concrete
  binary-mixture observable-access laws, the mixture identity is now
  definitionally discharged; event-share variants also derive share positivity
  from a finite positive-mass reporter/taker event.  Remaining theorem-local
  assumptions are the no-access law and the report-required outside-payoff
  equality, plus any stricter conditional-kernel instantiation wanted for the
  final source statement.
  The concrete event-share surface endpoints
  `paper_theorem3_2_optional_reporting_fairness_impossibility_of_gaussian_upper_tail_event_share_surface`
  and
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_event_share_surface`
  make the no-access and mixture identities definitional for those surfaces,
  leaving only the source certificate, a positive-mass event witness, and the
  report-required outside-payoff equality.  The constant-latent variants
  `paper_theorem3_2_optional_reporting_fairness_impossibility_of_gaussian_upper_tail_event_share_constant_latent_surface`
  and
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_event_share_constant_latent_surface`
  also discharge the latent-to-observable identities by making latent kernels
  skill-independent copies of the observable laws.  The optional-reporting
  posterior-payoff variant
  `paper_theorem3_2_optional_reporting_fairness_impossibility_of_gaussian_upper_tail_event_share_constant_latent_surface_posterior_payoff`
  states the source payoff directly as the Gaussian posterior mean and
  discharges the affine `baseTerm`/`signalWeight`/`denom` bookkeeping from
  `GaussianOffsetSignalFamily.posteriorMean_update_eq_base_add_weight_mul`;
  its indifference/tie step is now derived internally from strict posterior
  monotonicity and the strict Gaussian upper-tail-mean-above-threshold lemma.
  The companion implication wrapper
  `paper_theorem3_2_optional_reporting_fairness_implies_test_blank_of_gaussian_upper_tail_event_share_constant_latent_surface_posterior_payoff`
  states the same continuous route in the paper's exact Theorem 3.2
  fairness-implies-test-blankness form, and the no-relevance wrapper
  `paper_theorem3_2_optional_reporting_no_test_relevance_of_gaussian_upper_tail_event_share_constant_latent_surface_posterior_payoff`
  states the corresponding Definition 5 conclusion that no base/test
  relevance witness exists.  The `_of_nonempty_equilibrium` variants choose
  the reporter witness internally from nonempty equilibrium/base spaces, so
  callers no longer need to supply a distinguished equilibrium and base
  profile for this optional-reporting route.
  The report-required
  centered-base-term endpoint
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_event_share_constant_latent_surface_centered_baseTerm`
  closes the remaining outside-payoff equality when the report-required base
  term is normalized as `denom / 2 - signalWeight * upperTailMean`.  The
  report-required affine-centered-payoff endpoint
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_event_share_constant_latent_surface_affine_centered_payoff`
  further specializes this branch to denominator `1`, with the source payoff
  stated directly as `1 / 2 - slope * upperTailMean + slope * skill`; its
  indifference/tie step is derived internally from the positive slope and the
  strict Gaussian upper-tail-mean-above-threshold lemma.  The unit-centered
  endpoint
  `paper_theorem3_2_report_required_fairness_impossibility_of_upper_tail_event_share_constant_latent_surface_unit_centered_payoff`
  specializes this further to the normalized payoff
  `1 / 2 - upperTailMean + skill`, removing the slope parameter as well.  The
  companion implication wrapper
  `paper_theorem3_2_report_required_fairness_implies_test_blank_of_upper_tail_event_share_constant_latent_surface_unit_centered_payoff`
  states the normalized report-required route directly as fairness implies
  test-blankness; the matching no-relevance wrapper
  `paper_theorem3_2_report_required_no_test_relevance_of_upper_tail_event_share_constant_latent_surface_unit_centered_payoff`
  rules out every base/test relevance witness.  The report-required
  `_of_nonempty_equilibrium` variants now match the optional-reporting cleanup:
  nonempty equilibrium/base spaces are enough to choose the taker-share
  contradiction witness internally.  The compact certificate-level event-share
  endpoints now also have nonempty-equilibrium implication and no-relevance
  variants, so future final statements can route through
  `LG21OptionalReportingGaussianUpperTailSourceEquilibriumCertificate` and
  `LG21ReportRequiredUpperTailSourceEquilibriumCertificate` without carrying an
  explicit selected equilibrium/base pair while still stating Theorem 3.2 as
  fairness implies test-blankness or as absence of any concrete base/test
  relevance witness.  The same source-equilibrium routes now also construct the
  compact `LG21FairnessImpossibilityCertificate`, so the top-level Theorem 3.2
  interface can consume the closed optional-reporting and report-required
  source assumptions directly.

## Source Notes

The current Lean code closes finite admissions accounting identities, the
source-level model primitives for access status, school information sets, and
requirement-policy feasibility, the finite conditional-kernel core of
Definition 6 / Theorem 4.4, the shared Gaussian posterior-mean algebra used by
`P_BO`, generic binary-mixture PMF policy surfaces
`lg21BinaryMixtureEstimateSurface` and
`lg21EventShareBinaryMixtureEstimateSurface`, the two main Lemma 4.1 scalar
no-deviation contradictions, the fully specified observed-access
source-equilibrium endpoint `(Y, X) = (1, 1)`, and the law-level fairness
contradiction cores plus concrete one-base source-law surfaces for Propositions
4.2--4.3, including Proposition 4.3's finite base-profile mixture demographic
law surface. The
Proposition 4.2 and Proposition 4.3 cores now have
concrete Gaussian posterior-score law instantiations from conditional mean gaps
and signal-precision scale gaps. Proposition 4.3's concrete one-extra-test-signal
precision gap is now proved in the shared Gaussian library. Propositions 4.2
and 4.3 now both have named source routes through Lemma 4.1's lower-tail
strategy-proofness bridge and a packaged Gaussian threshold-equilibrium
certificate. Lemma 4.1's own observed-access source endpoint is now closed, and
Propositions 4.2--4.3 both have direct wrappers that consume this source action
endpoint rather than the older packaged certificate. Theorem 3.1/3.2 remain
open only at the level of choosing the final source-facing theorem statement;
their strongest current routes derive source witnesses and upper-tail
impossibility from concrete source equilibria under explicit payoff,
tie-breaking, threshold, and mixture hypotheses.  In the optional-reporting
continuous upper-tail route, the concrete Gaussian posterior-payoff
specialization now removes the separate affine-payoff identity and
tie-at-indifference hypotheses.  In
the report-required continuous upper-tail route, the affine-centered-payoff
specialization now removes the separate denominator/base-term bookkeeping and
the explicit tie-at-indifference hypothesis; its unit-centered specialization
also removes the slope parameter.
