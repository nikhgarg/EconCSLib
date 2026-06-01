# Dropping Standardized Testing for Admissions

## Source Version

- Paper: *Dropping Standardized Testing for Admissions Trades Off Information and Access*
- Authors: Nikhil Garg, Hannah Li, and Faidra Monachou
- Version formalized: arXiv:2010.04396 / Management Science accepted version, 2026
- arXiv URL: https://arxiv.org/abs/2010.04396
- PDF URL: https://arxiv.org/pdf/2010.04396
- Accessed: 2026-05-01

The source PDF is intentionally not committed to git. It is kept locally as
`source.pdf` and ignored by the local `.gitignore`. The extracted source text
cache is kept as `source.txt` for named-statement audits.  The arXiv source
archive is also cached locally as `source_arxiv.tar` and unpacked under
`source_tex/` (ignored by git); use the TeX files, especially
`source_tex/proofs.tex`, when `pdftotext` garbles displayed formulas.

## Central Theorem File

- `GLM20DroppingStandardizedTesting/MainTheorems.lean`
- Human-facing theorem ledger: `GLM20DroppingStandardizedTesting/PaperInterface.lean`
- Live proof plan: `GLM20DroppingStandardizedTesting/FORMALIZATION_PLAN.md`
- One-week restart note:
  `GLM20DroppingStandardizedTesting/START_HERE_NEXT_AGENT.md`
- Latest 2026-05-24 handoff report:
  `GLM20DroppingStandardizedTesting/HANDOFF_2026-05-24.md`
- Prior 2026-05-22 handoff report:
  `GLM20DroppingStandardizedTesting/HANDOFF_2026-05-22.md`
- Detailed 2026-05-17 handoff report:
  `GLM20DroppingStandardizedTesting/HANDOFF_2026-05-17.md`
- Joint standardized-testing plan:
  `../../docs/STANDARDIZED_TESTING_JOINT_FORMALIZATION_PLAN.md`

## Dependency DAG

- `GLM20DroppingStandardizedTesting/DependencyDAG.tex`

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
| Baseline model, group-aware Bayesian estimation, policies `P_S`, `P_full`, `P_sub` | `GLM20Model`, `GLM20SourcePolicySurface`, `glm20PFull`, `glm20PSub`, `glm20WithTestModel`, `glm20WithoutTestModel` | partially formalized | `MainTheorems.lean` | Finite latent-type/signal kernels and a source-facing metric surface are encoded; the concrete Gaussian feature model, precision formulas, access-barrier instantiation, and threshold equations remain open. |
| Source fairness and metric definitions: diversity, individual fairness, group academic merit | `glm20GroupFair`, `glm20IndividualFair`, `glm20DiversityWeaklyImproves`, `glm20GroupAcademicMeritWeaklyImproves` | formalized with caveat | `MainTheorems.lean` | Encodes the source metric comparisons over an abstract policy surface; the Gaussian probability/CDF formulas that instantiate these metrics are not yet formalized. |
| Lemma 1, estimated skill | `paper_lemma1_estimated_skill_source_surface`, `paper_interface_lemma1_estimated_skill_source_surface`, `lemma1GaussianSourceSurface`, `paper_lemma1_estimated_skill_gaussian`, `paper_lemma1_estimated_skill_strictMono_feature`, `paper_fixed_feature_gaussian_threshold_iff_cutoff`, `paper_interface_lemma1_estimated_skill_gaussian` | formalized | `MainTheorems.lean`, `PaperInterface.lean` | The Gaussian posterior-mean formula, marginal estimated-skill law, feature monotonicity, and fixed-feature threshold cutoff are proved using `GaussianOffsetSignalFamily`. The canonical source surface now wires group/policy feature precision, estimated-skill mean, and estimated-skill variance directly to the paper's Lemma 1 quantities; the older `GLM20EstimatedSkillCertificate` remains only as a legacy conditional wrapper. |
| Proposition 1, metrics with a fixed policy | `proposition1FixedPolicySourceSurface`, `paper_proposition1_fixed_policy_static_core_source_surface_standardGaussian`, `paper_interface_proposition1_fixed_policy_static_core_source_surface_standardGaussian`, `paper_proposition1_fixed_policy_static_core_source_surface`, `paper_interface_proposition1_fixed_policy_static_core_source_surface`, `paper_proposition1_fixed_policy_static_core`, `paper_proposition1_not_group_fair_of_precision_gap_capacity_lt_half`, `paper_proposition1_not_individual_fair_of_precision_tail_formulas`, `paper_proposition1_groupB_academic_merit_lt_groupA_of_tail_mean`, `paper_proposition1_diversity_share_decreases_of_precision_gap_lt`, `paper_proposition1_individual_fairness_gap_increases_of_precision_gap_high_skill_formula`, `GLM20FixedPolicyMetricsCertificate`, `paper_proposition1_metrics_fixed_policy_of_certificate` | formalized with caveat | `MainTheorems.lean`, `PaperInterface.lean`, `EconCSLib/Foundations/Probability/GaussianMathlib.lean` | Under the canonical fixed-policy source surface, the static paper conclusions are proved: group fairness fails, individual fairness fails, and admitted group-B academic merit is strictly below group A's. The closed-form threshold/diversity comparative statics and high-skill individual-fairness-gap comparative core are also proved. The preferred wrapper uses the mathlib-backed standard-normal CDF/hazard package. |
| Lemma 2, individual-fairness gap eventually decreases | `paper_lemma2_conditional_posterior_laws_source_surface_standardGaussian`, `paper_interface_lemma2_conditional_posterior_laws_source_surface_standardGaussian`, `paper_lemma2_conditional_posterior_laws_source_surface`, `paper_interface_lemma2_conditional_posterior_laws_source_surface`, `lemma2ConditionalPosteriorSourceSurface`, `paper_lemma2_conditional_posterior_laws`, `paper_lemma2_individual_fairness_gap_strictAntiOn_of_deriv_neg`, `paper_lemma2_individual_fairness_gap_strictAntiOn_of_qe_log_density_data`, `paper_lemma2_individual_fairness_gap_strictAntiOn_of_qe_affine_tail_log_density_data`, `paper_lemma2_individual_fairness_gap_strictAntiOn_of_qe_standard_normal_log_density_data`, `paper_lemma2_individual_fairness_gap_strictAntiOn_of_qe_standard_normal_tail_formulas`, `paper_lemma2_individual_fairness_gap_strictAntiOn_of_qe_threshold_tail_formulas`, `paper_lemma2_individual_fairness_gap_strictAntiOn_of_qe_conditional_posterior_laws`, `paper_lemma2_individual_fairness_gap_tendsto_zero_of_conditional_posterior_laws`, `paper_lemma2_individual_fairness_gap_decreases_on_tail`, `paper_lemma2_log_density_inequality_of_q_gt_threshold`, `GLM20IndividualFairnessTailCertificate`, `paper_lemma2_individual_fairness_gap_decreases_of_certificate` | formalized with caveat | `MainTheorems.lean`, `PaperInterface.lean`, `EconCSLib/Foundations/Probability/GaussianDerivatives.lean`, `EconCSLib/Foundations/Probability/GaussianMathlib.lean` | The calculus step from a negative derivative to strict tail decrease, affine Gaussian upper-tail derivative/continuity bridge, threshold-pass-probability bridge, conditional posterior-score Gaussian law, Gaussian tail-limit proof that `I(q; P_S) → 0`, source doubled-log density threshold algebra for the displayed `q_e`, and combined conditional-posterior-law Lemma 2 theorem are proved. `GaussianMathlib` now instantiates `StandardGaussianAnalyticAPI` by proving the derivative of the mathlib CDF is the standard Gaussian density and the doubled-log density identity, so the preferred wrapper has no abstract Gaussian-analytic API premise. |
| Theorem 1, dropping tests with barriers | `GLM20Theorem1BarrierCanonicalSourceModel`, `GLM20Theorem1BarrierCanonicalSourceModelConclusion`, `paper_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_source_model`, `paper_interface_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_source_model`, `paper_interface_theorem1_low_capacity_domain_nonempty`, `theorem1_low_capacity_domain_nonempty`, `theorem1_capacity_lt_groupA_eligible_of_selectiveB_worst`, `paper_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_of_population_access_bounds`, `paper_interface_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_of_population_access_bounds`, `paper_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_of_worst_case_capacity`, `paper_interface_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_of_worst_case_capacity`, `paper_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_of_capacity_range`, `paper_interface_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_of_capacity_range`, `paper_theorem1_dropping_tests_with_barriers_canonical_of_capacity_range`, `paper_interface_theorem1_dropping_tests_with_barriers_canonical_of_capacity_range`, `theorem1_capacity_mem_on_unit_of_capacity_lt_groupAEligibleMass`, `theorem1_selective_on_unit_of_two_capacity_lt_otherEligibleMass`, `theorem1BarrierMixtureCapacityThreshold_existsUnique`, `theorem1BarrierCapacityThresholdOnUnit_mixtureTailMass_eq`, `paper_theorem1_dropping_tests_with_barriers_canonical_of_mixture_capacity`, `paper_interface_theorem1_dropping_tests_with_barriers_canonical_of_mixture_capacity`, `paper_theorem1_barrier_threshold_continuousOn_of_capacity_equations`, `theorem1BarrierMixtureTailMass_eq`, `paper_theorem1_dropping_tests_with_barriers_canonical_source_surfaces`, `paper_theorem1_dropping_tests_with_barriers_explicit_metrics`, `paper_theorem1_diversity_access_threshold_of_capacity_share_main`, `paper_theorem1_academic_merit_access_threshold_of_groupA_normal_laws_main`, `paper_theorem1_academic_merit_access_threshold_of_groupB_normal_laws_main`, `paper_theorem1_beta_groupA_strictMonoOn`, `paper_theorem1_beta_groupB_strictMonoOn` | formalized with caveat | `MainTheorems.lean`, `PaperInterface.lean`, `EconCSLib/Foundations/Probability/Gaussian.lean`, `EconCSLib/Foundations/Probability/GaussianDerivatives.lean`, `EconCSLib/Foundations/Probability/GaussianMathlib.lean`, `EconCSLib/Foundations/Probability/GaussianMills.lean` | The preferred endpoint now packages the paper parameters in `GLM20Theorem1BarrierCanonicalSourceModel`: group-B population share `pi`, fixed access `gammaA`/`gammaB`, and the corresponding eligible-mass products in the `β_A`/`β_B` expressions. Canonical source surfaces make `diversity`, `academicMerit`, `accessLevel`, and `capacity` unfold to the admitted group-B share and Gaussian upper-tail merit formulas. The common cutoff is constructed from finite Gaussian mixture monotonicity plus CDF limits. The explicit caveat is the source proof's full `[0,1]` access-sweep interior domain: the nonredundant small-capacity assumptions are `2 * capacity < pi * gammaB` and `2 * capacity < (1 - pi) * gammaA` plus positivity; the separate `capacity < (1 - pi) * gammaA` feasibility bound is derived from these, and the low-capacity domain is proved nonempty under positive masses/access levels. |
| Theorem 2, dropping tests without barriers | `GLM20Theorem2NoBarrierCanonicalSourceModel`, `GLM20Theorem2NoBarrierCanonicalSourceModelConclusion`, `paper_theorem2_dropping_tests_without_barriers_standardGaussian_source_model_appendix_direction`, `paper_interface_theorem2_dropping_tests_without_barriers_standardGaussian_source_model`, `paper_theorem2_dropping_tests_without_barriers_standardGaussian_source_families_of_precision_order_population_weights_capacity_thresholds_main_text_direction`, `paper_theorem2_high_skill_individual_fairness_gap_sub_gt_full_source_surface_of_precision_order`, `paper_interface_theorem2_eventual_high_skill_gap_directions_inconsistent`, `paper_theorem2_group_admission_thresholds_standardGaussian_source_families_capacity_thresholds`, `theorem2NoBarrierSourceSurface`, `paper_theorem2_admission_threshold_full_gt_sub_of_scale_increases`, `paper_theorem2_group_academic_merit_full_gt_sub_of_tail_mean` | formalized with caveat | `MainTheorems.lean`, `ProofInterface.lean`, `PaperInterface.lean`, `EconCSLib/Foundations/Probability/Gaussian.lean`, `EconCSLib/Foundations/Probability/GaussianDerivatives.lean` | The source-model wrapper constructs the no-barrier test-free and test-using admission thresholds from the concrete Gaussian mixture-capacity equation and proves the main-text bundle: diversity iff Equation (3), each group's admission-probability threshold crossing, high-skill `I(q; P_sub) > I(q; P_full)`, and admitted academic merit decreases for both groups. The additional formal assumption is the source-model precision order `subB < subA`, alongside `subB + testB < subA + testA`; the cached Appendix D.4 crossed-order derivation is recorded as a source-text issue, not the paper-facing theorem. |
| Strategic one-school/two-school model and equilibrium definition | `GLM20StrategicEquilibriumData`, `glm20StrategicEquilibrium`, `GLM20StrategicPolicySurface`, `glm20TwoSchoolBinaryPolicyEquilibrium`, `paper_interface_two_school_binary_policy_equilibrium_subFull_iff`, `paper_interface_two_school_binary_policy_equilibrium_fullSub_iff`, `paper_interface_two_school_binary_policy_equilibrium_fullFull_iff`, `glm20TwoGroupWeightedAcademicMeritObjective`, `paper_interface_theorem3_school2_keep_test_objective_le_of_single_group_merit_gt` | formalized with caveat | `MainTheorems.lean`, `PaperInterface.lean` | Abstract feasible-action, student best-response, school objective, assignment-consistency, and two-school metric interfaces are encoded. For the binary `{P_sub,P_full}` school-policy game, each of `(P_sub,P_full)`, `(P_full,P_sub)`, and `(P_full,P_full)` is now proved equivalent to its two unilateral school-deviation inequalities. The two-group weighted academic-merit objective `π_A L_i^A(P)+π_B L_i^B(P)` is encoded, and condition (12)'s strict single-surviving-group merit inequality is proved to imply school 2's weak keep-test objective comparison. The paper's concrete costs, valuations, and threshold policies remain open. |
| Lemma 3, unique equilibrium under `P_full` | `paper_interface_lemma3_full_policy_threshold_equilibrium_existsUnique_of_correlatedStandardGaussian_applicant_components`, `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_correlatedStandardGaussian_applicant_components`, `paper_interface_lemma3_strategic_applicant_component_correlatedStandardGaussian_regular`, `glm20Lemma3StrategicApplicantComponent_correlatedStandardGaussian_regular`, `paper_interface_lemma3_full_policy_threshold_equilibrium_existsUnique_of_density_applicant_components`, `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_density_applicant_components`, `paper_interface_lemma3_full_policy_threshold_equilibrium_existsUnique_of_standardBivariate_selection_components_continuous`, `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_standardBivariate_selection_components_continuous`, `paper_interface_lemma3_strategic_applicant_component_standardBivariate_continuous`, `glm20Lemma3StrategicApplicantComponent_standardBivariate_continuous`, `paper_interface_bivariate_apply_admit_mass_standardBivariate_continuous_along`, `glm20BivariateApplyAdmitMass_standardBivariate_continuous_along`, `paper_interface_measure_apply_admit_mass_correlatedStandardGaussian_regular_diagonal`, `glm20MeasureApplyAdmitMass_correlatedStandardGaussian_regular_diagonal`, `paper_interface_standardBivariateGaussianCDF_continuous_of_rho_sq_le_one`, `standardBivariateGaussianCDF_continuous_of_rho_sq_le_one`, `paper_interface_lemma3_full_policy_threshold_equilibrium_existsUnique_of_measure_applicant_components`, `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_measure_applicant_components`, `paper_interface_lemma3_strategic_applicant_component_measure_continuous_of_noAtoms_marginals`, `glm20Lemma3StrategicApplicantComponent_measure_continuous_of_noAtoms_marginals`, `glm20MeasureApplyAdmitMass_continuous_diagonal_of_noAtoms_marginals`, `upperOrthantMass_diagonal_continuous_of_noAtoms_marginals`, `upperOrthantMass_diagonal_continuous_of_boundary_null`, `paper_interface_lemma3_strategic_applicant_component_measure_strictAnti`, `paper_interface_lemma3_strategic_applicant_component_measure_tendsto_atBot`, `paper_interface_lemma3_strategic_applicant_component_measure_tendsto_atTop`, `paperMeasureApplyAdmitMass`, `glm20Lemma3StrategicApplicantComponent_measure_strictAnti`, `glm20Lemma3StrategicApplicantComponent_measure_tendsto_atBot`, `glm20Lemma3StrategicApplicantComponent_measure_tendsto_atTop`, `glm20MeasureApplyAdmitMass`, `upperOrthantMass_strictAnti_of_strictMono_left_monotone_right`, `upperOrthantMass_diagonal_tendsto_atBot_univ`, `upperOrthantMass_diagonal_tendsto_atTop_zero`, `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_strategic_applicant_components`, `paper_interface_lemma3_full_policy_threshold_equilibrium_existsUnique_of_strategic_applicant_components`, `glm20Lemma3StrategicApplicantMass_regular_of_components`, `glm20Lemma3StrategicApplicantComponent`, `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_strategic_applicant_mass`, `paper_interface_lemma3_full_policy_threshold_equilibrium_existsUnique_of_strategic_applicant_mass`, `glm20Lemma3StrategicApplicantMass`, `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_standardGaussian`, `paper_interface_lemma3_full_policy_threshold_equilibrium_existsUnique_standardGaussian`, `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_standardGaussian_mixture`, `paper_interface_lemma3_full_policy_threshold_equilibrium_existsUnique_standardGaussian_mixture`, `glm20Lemma3FullPolicyThresholdEquilibrium`, `paper_lemma3_standardGaussian_applicant_mixture_cutoff_from_offset_families`, `paper_interface_lemma3_standardGaussian_applicant_mixture_cutoff_from_offset_families`, `paper_lemma3_standardGaussian_applicant_mixture_cutoff_existsUnique_and_capacity_region`, `paper_interface_lemma3_standardGaussian_applicant_mixture_cutoff_existsUnique_and_capacity_region`, `paper_lemma3_gaussian_applicant_mixture_cutoff_existsUnique_and_capacity_region`, `existsUnique_mixtureTailMass_eq_and_region_of_capacity_mem_Ioo`, `paper_lemma3_school_cutoff_existsUnique_and_capacity_region_of_strictAnti_applicant_mass`, `paper_interface_lemma3_school_cutoff_existsUnique_and_capacity_region_of_strictAnti_applicant_mass`, `existsUnique_eq_of_continuous_strictAnti_tendsto_atBot_atTop`, `paper_lemma3_precision_cutoff_apply_bestResponse_standardGaussian`, `paper_interface_lemma3_precision_cutoff_apply_bestResponse_standardGaussian`, `paper_lemma3_precision_cutoff_apply_strict_payoff_order_standardGaussian`, `paper_interface_lemma3_precision_cutoff_apply_strict_payoff_order_standardGaussian`, `paper_lemma3_precision_pointwise_bestResponse_threshold_form_standardGaussian`, `paper_interface_lemma3_precision_pointwise_bestResponse_threshold_form_standardGaussian`, `paper_lemma3_precision_unique_threshold_strategy_standardGaussian`, `paper_interface_lemma3_precision_unique_threshold_strategy_standardGaussian`, `paper_lemma3_apply_payoff_positive_iff_above_gaussian_cutoff`, `paper_lemma3_apply_payoff_negative_iff_below_gaussian_cutoff`, `paper_lemma3_full_policy_threshold_form_precision_standardGaussian`, `paper_interface_lemma3_full_policy_threshold_form_precision_standardGaussian`, `glm20StrategicProjectedScale`, `glm20StrategicProjectedScale_pos`, `glm20StrategicApplyPayoff`, `paper_lemma3_full_policy_threshold_form_standardGaussian`, `paper_interface_lemma3_full_policy_threshold_form_standardGaussian`, `glm20StrategicApplyCutoff`, `GLM20UniqueFullPolicyEquilibriumCertificate`, `paper_lemma3_unique_equilibrium_full_policy_of_certificate` | formalized with caveat | `MainTheorems.lean`, `PaperInterface.lean`, `EconCSLib/Foundations/Math/ThresholdCharacterization.lean`, `EconCSLib/Foundations/Probability/MeasureInequalities.lean`, `EconCSLib/Foundations/Probability/BivariateGaussian.lean`, `EconCSLib/Foundations/Probability/GaussianDerivatives.lean`, `EconCSLib/Foundations/Probability/GaussianQuantile.lean` | The displayed one-school Gaussian threshold formula is now proved in precision notation: applying has nonnegative payoff iff projected skill is above `q^*_{full} - scale_g * Phi^{-1}(1 - c_g / v)`, where `scale_g` is the paper's square-root expression in prior, non-test, and test precisions. The binary cutoff application rule is proved to be a best response, strict payoff order is proved on both sides of the cutoff, any pointwise best-response strategy matches the threshold rule away from indifference, and the tie-broken threshold strategy is locally unique for a fixed school cutoff. The scalar school-cutoff capacity step is proved abstractly, for finite standard-Gaussian applicant mixtures, and for group-indexed `GaussianOffsetSignalFamily` posterior-mean laws. These pieces compose into an actual `∃!` equilibrium object `(school cutoff, group cutoffs, group strategy)`, including the self-consistent Equation (35) applicant-mass shape where each group's application cutoff is substituted from Equation (7). The aggregate Eq. (35) continuity, strict-decrease, and endpoint facts are proved from per-group component facts. For the source event `π_g * P(q_sub >= qApply and q_full >= qAdmit)`, Lean proves continuity, strict decrease after Eq. (7), the `-∞` total-mass endpoint, and the `+∞` zero endpoint from normalized positive joint densities over `(q_sub,q_full)`, then composes these into a source-shaped `∃!` equilibrium endpoint. For the concrete nondegenerate correlated standard-Gaussian law, Lean now proves open positivity, packages continuity, strict decrease, and both endpoint limits for the diagonal source-event mass, and composes those facts into the same source-shaped `∃!` equilibrium endpoint. For the displayed bivariate-CDF route, Lean now proves `Phi_2(·,·;rho)` continuity for every valid correlation parameter from nonatomic marginals, proves the second marginal of `correlatedStandardGaussianLaw` is standard normal by Gaussian convolution, and discharges the concrete standard-bivariate continuity premise in the Lemma 3 selection-mass wrapper. The Appendix D.6 Owen/bivariate-CDF identity for the displayed closed form is tracked separately under Proposition 3 / Appendix D support, not as a Lemma 3 equilibrium caveat. |
| Proposition 2, unique two-school equilibrium | `paperProposition2TwoSchoolGroupThresholdEquilibrium`, `paper_interface_proposition2_standardGaussian_mixture_group_threshold_equilibrium_existsUnique_precision_of_high_cost_ratio`, `paper_proposition2_standardGaussian_mixture_group_threshold_equilibrium_existsUnique_precision_of_high_cost_ratio`, `paper_interface_proposition2_two_school_group_threshold_equilibrium_existsUnique_precision_of_high_cost_ratio`, `paper_proposition2_two_school_group_threshold_equilibrium_existsUnique_precision_of_high_cost_ratio`, `glm20Proposition2TwoSchoolGroupThresholdEquilibrium`, `paperProposition2TwoSchoolThresholdEquilibrium`, `paper_interface_proposition2_standardGaussian_mixture_threshold_equilibrium_existsUnique_precision_of_high_cost_ratio`, `paper_proposition2_standardGaussian_mixture_threshold_equilibrium_existsUnique_precision_of_high_cost_ratio`, `paper_interface_proposition2_standardGaussian_mixture_threshold_equilibrium_existsUnique_of_high_cost_ratio`, `paper_proposition2_standardGaussian_mixture_threshold_equilibrium_existsUnique_of_high_cost_ratio`, `paper_interface_proposition2_two_school_threshold_equilibrium_existsUnique_standardGaussian_of_high_cost_ratio`, `paper_proposition2_two_school_threshold_equilibrium_existsUnique_standardGaussian_of_high_cost_ratio`, `paperProposition2TwoSchoolApplicationRegion`, `paper_interface_proposition2_two_school_application_region_nonmonotone_between_cutoffs`, `paper_proposition2_two_school_application_region_nonmonotone_between_cutoffs`, `paper_proposition2_two_school_selection_thresholds_existUnique_and_capacity_regions_of_strictAnti_applicant_masses`, `paper_interface_proposition2_two_school_selection_thresholds_existUnique_and_capacity_regions_of_strictAnti_applicant_masses`, `paper_proposition2_two_school_application_region_unique_strategy_precision_standardGaussian_of_high_cost_ratio`, `paper_interface_proposition2_two_school_application_region_unique_strategy_precision_standardGaussian_of_high_cost_ratio`, `paper_proposition2_two_school_application_region_bestResponse_precision_standardGaussian_of_high_cost_ratio`, `paper_interface_proposition2_two_school_application_region_bestResponse_precision_standardGaussian_of_high_cost_ratio`, `paper_proposition2_two_school_application_region_precision_standardGaussian_of_high_cost_ratio`, `paper_interface_proposition2_two_school_application_region_precision_standardGaussian_of_high_cost_ratio`, `paper_interface_proposition2_cost_ratio_low_of_high`, `paper_proposition2_cost_ratio_low_of_high`, `paper_proposition2_two_school_application_region_unique_strategy_precision_standardGaussian`, `paper_interface_proposition2_two_school_application_region_unique_strategy_precision_standardGaussian`, `paper_proposition2_two_school_application_region_bestResponse_precision_standardGaussian`, `paper_interface_proposition2_two_school_application_region_bestResponse_precision_standardGaussian`, `paper_proposition2_two_school_application_region_precision_standardGaussian`, `paper_interface_proposition2_two_school_application_region_precision_standardGaussian`, `paper_proposition2_two_school_application_region_unique_strategy_standardGaussian`, `paper_proposition2_two_school_application_region_bestResponse_standardGaussian`, `paper_proposition2_two_school_application_region_standardGaussian`, `paper_interface_proposition2_two_school_application_region_standardGaussian`, `paper_proposition2_low_cutoff_lt_high_cutoff_standardGaussian`, `paperProposition2AdmittedMassFormula`, `paper_interface_proposition2_admitted_mass_formula_eq_correlatedStandardGaussian_verticalUpperStripMass`, `paper_interface_proposition2_admitted_mass_formula_eq_owenAffineSelectionMass`, `paperProposition2OwenAffineLowerSelectionMass`, `paper_interface_proposition2_owenAffineLowerSelectionMass_eq_correlatedStandardGaussian_lowerLeftRectangleMass`, `paperProposition2SubEligibleMassFormula`, `paper_interface_proposition2_part_iii_diversity_criterion_above_high_cutoff`, `paper_interface_proposition2_part_iii_diversity_criterion_between_cutoffs`, `paperProposition2OwenProductInterval`, `paper_interface_proposition2_owenProductInterval_eq`, `paperProposition2OwenFirstMomentInterval`, `paper_interface_proposition2_owenFirstMomentInterval_eq`, `paperProposition2OwenProductLowerTail`, `paper_interface_proposition2_owenProductLowerTail_eq`, `paperProposition2OwenSelectionLowerTail`, `paperProposition2OwenFirstMomentLowerTail`, `paper_interface_proposition2_owenFirstMomentLowerTail_eq`, `paperProposition2J2MeritStandardizedLowerTailFormula`, `paper_interface_proposition2_j2MeritStandardizedLowerTailFormula_eq_scaledFirstMoment_of_mass`, `paper_interface_proposition2_j2MeritStandardizedLowerTailFormula_eq_kappaBoundaryDensityFormula`, `paperProposition2KappaFormula`, `paperProposition2KappaBoundaryDensityFormula`, `paper_interface_proposition2_kappaBoundaryDensityFormula_eq_kappaFormula`, `paper_interface_proposition2_kappaFormula_eq_scaled_owenFirstMomentLowerTail_of_boundary_density`, `paper_interface_proposition2_kappaBoundaryDensityFormula_eq_scaled_owenFirstMomentLowerTail`, `paper_interface_proposition2_boundaryDensityScaling_of_normalDensity`, `paper_interface_proposition2_part_iv_lower_academic_merit_iff_lambda_lt_kappa`, `glm20StrategicTwoSchoolApplyPayoff`, `GLM20TwoSchoolEquilibriumCertificate`, `paper_proposition2_unique_two_school_equilibrium_of_certificate` | formalized with caveat | `MainTheorems.lean`, `PaperInterface.lean`, `EconCSLib/Foundations/Probability/Gaussian.lean`, `EconCSLib/Foundations/Probability/GaussianQuantile.lean`, `EconCSLib/Foundations/Probability/BivariateGaussian.lean`, `EconCSLib/Foundations/Probability/GaussianMathlib.lean` | The displayed student application region is proved in precision notation from the Lemma 3 Gaussian cutoff calculation: the low cutoff uses cost ratio `c_g / v1`, the high cutoff uses cost ratio `c_g / (v1 - v2)`, and `q_l^g < q_h^g`. The low-ratio domain is now derived from the high-ratio domain plus `0 < v1 - v2 < v1`, so the preferred paper-facing wrappers no longer assume `c_g / v1 ∈ (0,1)` separately. Lean now also proves the qualitative non-monotonicity implication: when `q^*_{2,sub}` lies strictly between the low and high cutoffs, there are skill values where students apply, then do not apply, then apply again. The two-school selection-threshold existence/uniqueness part is proved at the reusable applicant-mass level for each school. These ingredients now compose into a group-indexed source-shaped unique threshold-equilibrium theorem with common school cutoffs and per-group costs/precision scales, including a finite standard-Gaussian mixture instantiation. Proposition 2(iii)'s `D_g` admitted-mass formula is now instantiated against the concrete correlated standard-Gaussian law, and the lower affine source event for Proposition 2(iv) is proved equal to the correlated-standard-Gaussian lower-left rectangle. The two displayed diversity mass-ratio criteria plus Proposition 2(iv)'s `kappa` academic-merit comparison are proved at the formula-rewrite layer once the model-side diversity and merit values are identified with those displayed masses. The finite-interval and direct lower-tail product-density and first-moment identities behind the `kappa` route are now proved in `GaussianMathlib` and exposed through paper-facing wrappers; the lower-tail first moment is exactly `∫_{-∞}^{q} z φ(z) Φ(A_gD_g+c_gz) dz = c_g φ(A_g)Φ(D_gq+A_gc_g)/D_g - φ(q)Φ(A_gD_g+c_gq)`. Lean also packages the standardized J2 merit expression as `mu` times the lower-tail selection mass plus `sigmaTilde` times the lower-tail first moment, proves it rewrites to the scaled first moment when that mass is `1 - tau`, proves the displayed/source-density `kappa` expression equals that J2 merit expression under the explicit boundary-density scaling premise, and proves the raw normal-density scaling fact `φ(upper) = σtilde * normalDensity(N(mu,σtilde), raw)` when `upper = (raw - mu)/σtilde`. The remaining Proposition 2 caveat is the hard Appendix D.6 model identification: deriving the concrete two-school strategic applicant masses, the integral-to-event lower-tail mass identity, and the exact raw cutoff substitution for the boundary density from the source Gaussian game. |
| Proposition 3, equilibrium under `P_full` | `paperProposition3SelectionCore`, `paperProposition3OwenAffineSelectionMass`, `paperStandardBivariateGaussianCDF`, `paperCorrelatedStandardGaussianLaw`, `paper_interface_proposition3_selection_core_eq_owenAffineSelectionMass`, `paper_proposition3_selection_core_eq_owenAffineSelectionMass`, `paper_interface_proposition3_tau_formula_eq_owenAffineSelectionMass`, `paper_proposition3_tau_formula_eq_owenAffineSelectionMass`, `paper_interface_proposition3_selection_core_standardBivariate_pos`, `glm20Proposition3SelectionCore_standardBivariate_pos`, `paper_interface_proposition3_underrepresented_iff_selection_core_ratio_standardBivariate`, `paper_proposition3_underrepresented_iff_selection_core_ratio_standardBivariate`, `paper_interface_proposition3_full_policy_diversity_ratio_and_academic_merit_formulas_standardBivariate`, `paper_proposition3_full_policy_diversity_ratio_and_academic_merit_formulas_standardBivariate`, `paper_interface_proposition3_full_policy_diversity_ratio_and_academic_merit_owenFirstMoment_formulas_standardBivariate`, `paper_proposition3_full_policy_diversity_ratio_and_academic_merit_owenFirstMoment_formulas_standardBivariate`, `paper_interface_proposition3_rho_sq_lt_one`, `paper_interface_proposition3_selection_core_eq_correlatedStandardGaussian_verticalUpperStripMass`, `paper_interface_bivariate_apply_admit_mass_eq_correlatedStandardGaussian_verticalUpperStripMass`, `paper_interface_proposition3_tau_formula_eq_correlatedStandardGaussian_verticalUpperStripMass`, `paper_interface_proposition3_selection_core_eq_verticalUpperStripMass_of_cdf_identities`, `paper_proposition3_selection_core_eq_verticalUpperStripMass_of_cdf_identities`, `paper_interface_proposition3_selection_core_expr_eq_verticalUpperStripMass_of_cdf_identities`, `paper_proposition3_selection_core_expr_eq_verticalUpperStripMass_of_cdf_identities`, `paperProposition3TauFormula`, `paperProposition3LambdaFormula`, `paperProposition3LambdaOwenFirstMomentFormula`, `paper_interface_proposition3_lambda_owenFirstMomentFormula_eq_lambdaFormula_add_boundaryTerm`, `paper_interface_proposition3_lambda_eq_owenFirstMomentFormula_of_slope_zero`, `paper_interface_proposition3_lambda_ne_owenFirstMomentFormula_of_nonzero_slope`, `paperProposition3OwenFirstMomentProductTailIntegral`, `paper_interface_proposition3_owenFirstMomentProductTailIntegral_eq`, `paperProposition3OwenFirstMomentIntegral`, `paper_interface_proposition3_owenFirstMomentIntegral_eq`, `paper_interface_proposition3_underrepresented_iff_selection_core_ratio`, `paper_proposition3_underrepresented_iff_selection_core_ratio`, `paper_interface_proposition3_full_policy_diversity_ratio_and_academic_merit_formulas`, `paper_proposition3_full_policy_diversity_ratio_and_academic_merit_formulas`, `paper_interface_proposition3_full_policy_diversity_and_academic_merit_formulas`, `glm20Proposition3SelectionCore`, `glm20Proposition3TauFormula`, `glm20Proposition3LambdaFormula`, `glm20Proposition3LambdaOwenFirstMomentFormula`, `glm20Proposition3LambdaFormula_ne_owenFirstMomentFormula_of_nonzero_slope`, `glm20Proposition3OwenFirstMomentIntegral_eq`, `paper_proposition3_full_policy_diversity_and_academic_merit_formulas`, `GLM20FullPolicyEquilibriumConsequencesCertificate`, `paper_proposition3_equilibrium_under_full_policy_of_certificate` | conditional | `MainTheorems.lean`, `PaperInterface.lean`, `EconCSLib/Foundations/Probability/MeasureInequalities.lean`, `EconCSLib/Foundations/Probability/BivariateGaussian.lean`, `EconCSLib/Foundations/Probability/GaussianMathlib.lean` | The paper's displayed `τ_g` and `λ(a_g,b_g,\tilde σ_g,τ_g)` expressions are now encoded explicitly. Lean proves the source-event bookkeeping in the Owen/CDF formula: if the transformed joint law has first marginal CDF `Φ(A_g)`, bivariate lower-left CDF `Φ_2(A_g,B_g;ρ_g)`, and null horizontal boundary, then `Φ(A_g)-Φ_2(A_g,B_g;ρ_g)` is exactly the vertical strip mass `P(Z_1 <= A_g, B_g <= Z_2)`. The abstract `Φ_2` seam is now instantiated by `standardBivariateGaussianCDF`, defined as the lower-left rectangle mass of the correlated standard-Gaussian law `(U, ρU + sqrt(1-ρ^2)V)`; Lean proves the first marginal is standard normal, proves the second marginal is standard normal via Gaussian scaling and convolution, derives nonatomic marginals and `Phi_2` continuity for valid correlations, proves the paper's `ρ_g` satisfies `ρ_g^2 < 1`, proves horizontal boundaries are null, proves every concrete selection core is positive as a nonempty vertical strip under an open-positive correlated law, and rewrites the selection core, bivariate application/admission mass, and `τ_g` formula to that concrete vertical strip mass. Lean also proves the standardized source-affine Owen mass identity: `P(X <= A_g sqrt(1 + (σtilde_g b_g)^2) + σtilde_g b_g Z, B_g <= Z)` equals the same `Φ(A_g)-Φ_2(A_g,B_g;ρ_g)` core by a reusable characteristic-function law-equality proof. Lean also proves the algebraic Step 3 in Proposition 3(i): under the displayed total-capacity identity, group B is under-represented exactly when the Equation (37) selection-core ratio holds, `\tilde σ_B / \tilde σ_A < X_A / X_B`, where `X_g = Φ(A_g)-Φ_2(A_g,B_g;ρ_g)`; the preferred standard-bivariate wrapper discharges the selection-core positivity hypotheses internally. The standardized first-moment analytic layer is now proved without extra integrability assumptions: Lean proves both the product-tail identity and the upper-tail identity `∫_{q_full}^∞ z * φ(z) * Φ(A*sqrt(1+c^2)+c*z) dz = φ(q_full)*Φ(A*sqrt(1+c^2)+c*q_full) + c*φ(A)/sqrt(1+c^2)*(1-Φ(sqrt(1+c^2)*q_full + A*c))`. Lean also encodes the source-style upper-tail first-moment expression and proves it equals the displayed `λ` plus the explicit boundary term `sigmaTilde^2 * b * phi(A) / (tau * sqrt(1+sigmaTilde^2 b^2))`; the two formulas coincide when `b = 0`, and Lean proves they are unequal whenever `sigmaTilde`, `b`, and `tau` are all nonzero. A separate standard-bivariate wrapper composes the diversity ratio with this verified upper-tail merit comparison so downstream model work can target the proved formula without treating it as the source-displayed `λ`. The source-facing comparison theorem still returns the displayed `λ` academic-merit comparison once model-side merit values are identified with that formula. The remaining Proposition 3 caveat is resolving this displayed-`λ` discrepancy and proving the original-source model-to-standardized-affine merit-scaling identification from the full-policy strategic applicant pool. |
| Theorem 3, academic merit and two-school equilibria | `paper_theorem3_source_conditions_of_proposition5_merit_crossings`, `paper_interface_theorem3_source_conditions_of_proposition5_merit_crossings`, `paper_theorem3_source_conditions_of_proposition5_cutoff_objective_bridges`, `paper_interface_theorem3_source_conditions_of_proposition5_cutoff_objective_bridges`, `paper_proposition5_part_i_school1_cutoff_objective_iff_exactly_one_cost_case_of_merit_crossings`, `paper_interface_proposition5_part_i_school1_cutoff_objective_iff_exactly_one_cost_case_of_merit_crossings`, `paper_proposition5_part_i_school1_cutoff_objective_iff_exactly_one_cost_case`, `paper_interface_proposition5_part_i_school1_cutoff_objective_iff_exactly_one_cost_case`, `paper_proposition5_part_i_school1_objective_iff_condition10_of_cutoff_cases`, `paper_interface_proposition5_part_i_school1_objective_iff_condition10_of_cutoff_cases`, `paper_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case_of_low_and_high_merit_formulas`, `paper_interface_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case_of_low_and_high_merit_formulas`, `paper_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case_of_low_merit_crossings`, `paper_interface_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case_of_low_merit_crossings`, `paper_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case`, `paper_interface_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case`, `paper_proposition5_part_ii_school2_objective_iff_condition13_of_cutoff_cases`, `paper_interface_proposition5_part_ii_school2_objective_iff_condition13_of_cutoff_cases`, `paper_proposition5_part_ii_school1_cutoff_objective_iff_no_expand_or_low_cost_of_merit_crossing`, `paper_interface_proposition5_part_ii_school1_cutoff_objective_iff_no_expand_or_low_cost_of_merit_crossing`, `paper_proposition5_part_ii_school1_cutoff_objective_iff_no_expand_or_low_cost`, `paper_interface_proposition5_part_ii_school1_cutoff_objective_iff_no_expand_or_low_cost`, `paper_proposition5_part_ii_school1_objective_iff_condition14_of_cutoff_case`, `paper_interface_proposition5_part_ii_school1_objective_iff_condition14_of_cutoff_case`, `paper_proposition5_condition10_iff_cost_and_fullFull_cutoff_case`, `paper_interface_proposition5_condition10_iff_cost_and_fullFull_cutoff_case`, `paper_proposition5_condition13_iff_cost_and_fullFull_cutoff_case`, `paper_interface_proposition5_condition13_iff_cost_and_fullFull_cutoff_case`, `paper_proposition5_condition14_iff_fullSub_cutoff_case_or_low_cost`, `paper_interface_proposition5_condition14_iff_fullSub_cutoff_case_or_low_cost`, `paper_proposition5_standardGaussian_twoFull_apply_payoff_cutoff_existsUnique`, `paper_interface_proposition5_standardGaussian_twoFull_apply_payoff_cutoff_existsUnique`, `paper_proposition5_twoFull_apply_payoff_cutoff_existsUnique_of_tail_limits`, `paper_interface_proposition5_twoFull_apply_payoff_cutoff_existsUnique_of_tail_limits`, `paper_proposition5_twoFull_apply_payoff_cutoff_existsUnique_of_crossing`, `paper_interface_proposition5_twoFull_apply_payoff_cutoff_existsUnique_of_crossing`, `paper_proposition5_twoFull_apply_payoff_cutoff_strictMono_cost`, `paper_interface_proposition5_twoFull_apply_payoff_cutoff_strictMono_cost`, `paper_proposition5_equation47_cutoff_formula_of_twoFull_payoff_zero`, `paper_interface_proposition5_equation47_cutoff_formula_of_twoFull_payoff_zero`, `paper_proposition5_twoFull_apply_expected_payoff_eq_equation46`, `paper_interface_proposition5_twoFull_apply_expected_payoff_eq_equation46`, `paper_proposition5_twoFull_apply_payoff_strictMono_projectedSkill`, `paper_interface_proposition5_twoFull_apply_payoff_strictMono_projectedSkill`, `paper_proposition5_cost_threshold_of_continuous_strictAntiOn_cost_interval`, `paper_interface_proposition5_cost_threshold_of_continuous_strictAntiOn_cost_interval`, `paper_proposition5_cost_threshold_of_continuous_strictAntiOn_unit_interval`, `paper_interface_proposition5_cost_threshold_of_continuous_strictAntiOn_unit_interval`, `paper_theorem3_source_conditions_of_proposition5_objective_bridges`, `paper_interface_theorem3_source_conditions_of_proposition5_objective_bridges`, `paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition`, `paper_interface_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition`, `paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_source_condition`, `paper_interface_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_source_condition`, `paper_theorem3_source_conditions_of_binary_policy_objective_conditions`, `paper_interface_theorem3_source_conditions_of_binary_policy_objective_conditions`, `paper_theorem3_two_school_academic_merit_source_conditions_of_i_ii_and_positive_costs`, `paper_interface_theorem3_two_school_academic_merit_source_conditions_of_i_ii_and_positive_costs`, `paper_interface_theorem3_exactly_one_group_iff_exists_unique`, `glm20ExactlyOneOfTwo_iff_existsUnique_mem_pair`, `paper_theorem3_fullFull_condition_exists_boundary_functions_of_positive_costs`, `paper_interface_theorem3_fullFull_condition_exists_boundary_functions_of_positive_costs`, `paper_theorem3_two_school_academic_merit_source_conditions`, `paper_interface_theorem3_two_school_academic_merit_source_conditions`, `glm20Theorem3SubFullCondition`, `glm20Theorem3FullSubCondition`, `glm20Theorem3FullFullCondition`, `paper_theorem3_Kg_eq_offset_posterior_mean_tail`, `paper_interface_theorem3_Kg_eq_offset_posterior_mean_tail`, `GLM20Theorem3AcademicMeritSourceCertificate`, `GLM20TwoSchoolAcademicMeritCertificate`, `paper_theorem3_two_school_academic_merit_of_certificate` | conditional | `MainTheorems.lean`, `PaperInterface.lean`, `EconCSLib/Foundations/Math/ThresholdCharacterization.lean` | The paper's `K_g(q)` term is now defined as a Gaussian upper-tail mass and proved equal to the Lemma 1 test-free posterior-mean law formula. Theorem 3(i)--(iii) now have source-shaped condition definitions matching inequalities (10)--(14), the exactly-one-group clause, and the positive cost-boundary functions for `(P_full,P_full)`; the exactly-one helper is proved equivalent to explicit existence and uniqueness over `{A,B}`. Part (iii)'s bare existential boundary-function statement is proved from positive group costs at the abstract source-condition layer. The highest-level current wrapper constructs the condition-(10), condition-(13), and condition-(14) cost thresholds from Proposition 5 merit crossings, proves the lower/high threshold ordering for part (ii), and derives the displayed Theorem 3 policy-pair conditions by composing the binary school-objective bridge, mass/cutoff identities, and weighted-merit bookkeeping. The generic decreasing-cost threshold crossing needed to produce positive `c_hat` values from continuity/monotonicity is now proved and exposed, both on the normalized unit interval and on the paper's non-normalized cost interval `[0,maxCost]`; the Proposition 5(i) `J1` threshold, Proposition 5(ii) `J2` lower threshold, and Proposition 5(ii) `J1` high threshold are now constructed from their monotone merit crossings, and the ordered part-(ii) school-`J2` branch now has a formula-level wrapper that rewrites objective values to the displayed low-merit formulas before constructing both thresholds. The equation (46) two-full-policy test-taking payoff is encoded, algebraically expanded from the expected-value expression, solved into the equation (47) inverse-CDF cutoff formula under the explicit quantile-domain premise, proved strictly increasing in projected skill and increasing in cost, and converted into a unique upper-threshold test-taking cutoff under standard-Gaussian tail limits and the paper's `0 < cost < v1` domain. Conditions (10), (13), and (14)'s mass inequalities are now proved equivalent to the source proof's cutoff cases: `M_g(P_full,P_full) < K_g(q^*_{i,sub})` iff `q^*_{i,sub} < q^g_{full,full}`, and `M_g(P_full,P_sub) > K_g(q^*_{1,sub})` iff `q^g_{full,sub} < q^*_{1,sub}`. The school-`J1` part-(i), school-`J2` part-(ii), and school-`J1` part-(ii) proof case analyses are now packaged into cutoff-form objective bridges. The remaining substantive task is proving the merit-crossing and objective-formula premises from the concrete two-school Gaussian game. |
| Theorem 3 / Proposition 5 weighted objective bridge | `paper_theorem3_source_conditions_of_proposition5_cutoff_and_school2_merit_bridges`, `paper_interface_theorem3_source_conditions_of_proposition5_cutoff_and_school2_merit_bridges`, `paper_theorem3_school2_objective_iff_other_group_keeps_test_of_single_group_no_tie`, `paper_interface_theorem3_school2_objective_iff_other_group_keeps_test_of_single_group_no_tie`, `paper_proposition5_part_i_school2_objective_bridges_of_single_group_no_tie`, `paper_interface_proposition5_part_i_school2_objective_bridges_of_single_group_no_tie` | formalized with caveat | `MainTheorems.lean`, `PaperInterface.lean` | The school-`J2` condition (11)--(12) objective premise is no longer a raw iff: if the `(P_sub,P_full)` objective reduces to the surviving group's weighted merit, the `(P_sub,P_sub)` objective reduces to the two-group weighted merit, the surviving group satisfies the capacity mass condition, and the merit comparison is not tied, Lean proves the objective comparison is equivalent to the paper's keep-test condition. The strengthened Theorem 3 wrapper composes this bridge with the cutoff/mass bridges, so the remaining part-(i) school-`J2` obligations are explicit weighted-merit bookkeeping, mass, and no-tie facts rather than an opaque deviation-equivalence assumption. |
| Proposition 5, strategic students: academic merit | `paperProposition5StrategicAcademicMeritSourceConditions`, `paperProposition5StrategicAcademicMeritSourceConditionsExists`, `paper_interface_proposition5_strategic_academic_merit_source_conditions_of_objective_bridges`, `paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_objective_bridges`, `paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_objective_bridges_and_positive_costs`, `paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_objective_bridges_and_fullFull_cost_family`, `paper_interface_theorem3_source_conditions_exists_of_proposition5_strategic_academic_merit_source_conditions_exists`, `PaperInterface.proposition5_strategic_academic_merit_source_conditions`, `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists`, `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_objective_bridges`, `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_objective_bridges_and_positive_costs`, `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_objective_bridges_and_fullFull_cost_family`, `PaperInterface.theorem3_source_conditions_exists_from_proposition5_strategic_academic_merit_source_conditions_exists`, `GLM20StrategicAcademicMeritCertificate`, `paper_proposition5_strategic_academic_merit_of_certificate` | conditional | `ProofInterface.lean`, `PaperInterface.lean`, `MainTheorems.lean` | Proposition 5 now has typed non-certificate source surfaces, including an existential-threshold version matching the way the paper constructs cost cutoffs. The sub/full and full/sub weighted academic-merit objective comparisons are equivalent to the displayed source conditions, and the full/full pair satisfies the source boundary condition. Positive-cost and full/full cost-family wrappers can fill that third component directly. The legacy certificate endpoint remains only for the still-open concrete Gaussian strategic game instantiation. |
| Proposition 6, strategic students: diversity | `paper_interface_proposition6_full_diversity_formula_eq_correlatedStandardGaussian_verticalUpperStripMass`, `paper_interface_proposition6_sub_diversity_formula_eq_testFreeGroupBTail`, `paper_interface_proposition6_j1_drops_test_iff_full_formula_lt_testFreeGroupBTail`, `paperProposition6FullDiversityFormula`, `paperProposition6SubDiversityFormula`, `paper_interface_proposition6_j1_drops_test_iff_diversity_formulas`, `paper_proposition6_j1_drops_test_iff_diversity_formulas`, `glm20Proposition6FullDiversityFormula`, `glm20Proposition6SubDiversityFormula`, `GLM20StrategicDiversityCertificate`, `paper_proposition6_strategic_diversity_of_certificate` | conditional | `MainTheorems.lean`, `PaperInterface.lean` | The displayed full-policy and test-free diversity formulas for school `J1` are encoded. Lean now rewrites the full-policy left side to the concrete correlated-Gaussian vertical-strip event and proves that the test-free right side is the group-B Gaussian upper tail at the displayed no-test cutoff. The Proposition 6 criterion is proved from either displayed formula identities or the explicit test-free tail identification. The remaining caveat is tying these formula/tail identities to the concrete two-school strategic diversity objective and school-deviation choice. |
| Appendix D.1-D.12, Gaussian, hazard-rate, threshold, and equilibrium support | `GLM20GaussianAnalyticSupportCertificate`, `paper_appendixD_gaussian_support_of_certificate` | conditional | `MainTheorems.lean` | Endpoint groups normal closure, truncated-normal expectation, hazard-rate monotonicity, and threshold comparison support; the analytic proofs remain certificates. |
| Appendix F Definition 1, Blackwell sufficiency | `glm20BlackwellSufficient`, `paper_interface_blackwell_sufficient_bind`, `paper_interface_blackwell_sufficient_map`, `paper_interface_blackwell_sufficient_refl`, `paper_interface_blackwell_sufficient_trans`, `glm20BlackwellSufficient_bind`, `glm20BlackwellSufficient_map`, `glm20BlackwellSufficient_refl`, `glm20BlackwellSufficient_trans` | formalized with caveat | `MainTheorems.lean`, `PaperInterface.lean` | Finite-kernel garbling definition is encoded, with explicit-kernel sufficiency, deterministic post-processing, reflexivity, and transitivity proved by pure/composed garblings; the source's continuous posterior-experiment formulation and sufficiency/SSD bridge remain open. |
| Appendix F Lemmas F.1-F.4, Blackwell/SSD generalization support | `GLM20BlackwellSupportCertificate`, `paper_appendixF_blackwell_ssd_support_of_certificate` | conditional | `MainTheorems.lean` | Endpoint exposes sufficiency-to-SSD equivalence, convex-order mean preservation, and CDF crossing support; finite/continuous second-order stochastic dominance proofs remain certificates. |
| Propositions 7-9, generalized fixed-policy and affirmative-action extensions | `GLM20GeneralizationAndAffirmativeActionCertificate`, `paper_propositions7_9_generalization_affirmative_action_of_certificate` | conditional | `MainTheorems.lean` | Endpoint exposes generalized fixed-policy metrics, affirmative-action fixed-policy comparisons, and dropping-tests-with-barriers under affirmative action; Appendix F/G analytic bridge remains a certificate. |
| Auxiliary finite admissions accounting support | `glm20_with_test_exp_decompose`, `glm20_no_test_exp_decompose`, and the related `glm20_*` mass/selection/monotonicity wrappers | formalized | `MainTheorems.lean` | None; auxiliary finite-kernel support only, not a source theorem wrapper. |

2026-05-24 stopping point: Section 5 is paused at a clean generated
source-family row-package boundary.  The new
`GLM20Proposition5ExactlyOneObjectiveSourceFamilyRows` package is the narrow
Bayesian-game target for the twelve branch-conditioned posterior/admitted-merit
row identifications.  The compiled public bridge is
`PaperInterface.proposition5_exactly_one_weighted_objective_bridge_source_family_policy_state_row_package`.
This closes the table-bookkeeping and weighted-objective algebra around those
rows; it does not yet prove the Bayesian-game row facts themselves.  Start from
`START_HERE_NEXT_AGENT.md` and `HANDOFF_2026-05-24.md`.

Theorem 2 update: the main-text high-skill direction is now proved by
`paper_interface_theorem2_high_skill_individual_fairness_gap_sub_gt_full_source_surface_of_precision_order`
under the extra assumption `subB < subA`, using
`standardGaussianCDF_affine_leftTail_lt_mul_eventually_of_slope_lt`.  The
paper-facing source-model wrapper now uses this main-text direction and the
main-text test-free precision order `subB < subA`; the old
`_appendix_direction` declaration name remains only as a compatibility alias.
The `ProofInterface` theorem-facing Theorem 2 bundle wrappers also now expose
the same main-text assumption/conclusion; the crossed-order opposite-direction
lemmas remain only below that interface as source-audit artifacts.
`FINAL_VALIDATION_REPORT.md` records the cached Appendix D.4 crossed-order
derivation as a source-text issue rather than a separate paper-facing theorem.

2026-05-17 Section 5 checkpoint: Theorem 3 now has concrete
feasibility-aware interval endpoints
`paper_interface_theorem3_policyStateSubFullMassFeasibleSurface_subFull_fullSub_interval`,
`paper_interface_theorem3_policyStateSubFullMassFeasibleSurface_fullFull_condition_of_positive_cost_interval`,
and
`paper_interface_theorem3_policyStateSubFullMassFeasibleSurface_source_conditions_of_i_ii_and_positive_cost_interval`.
Proposition 6 also has fallback-row generated-table endpoints, including
`paper_interface_proposition6_policyState_standardGaussian_source_parameter_diversity_rows_inequality_implies_subFull_equilibrium_of_J2_fallback_eq`,
so future source-model wiring can discharge the `J2` weak no-deviation premise
from a pointwise ordinary-fallback equality under `J1 != J2`. See
`HANDOFF_2026-05-17.md` for the pickup plan.
Compact Section 5 paper-surface adapters that do not belong in the large
theorem ledger now live in `PaperSurfaceWrappers.lean`; the first one is the
bundled binary-policy equilibrium characterization
`PaperInterface.strategic_equilibrium_three_cases`, alongside the
feasibility-aware bundle
`PaperInterface.strategic_feasible_equilibrium_three_cases`.  The LG21-style
continuous-type route is now available as
`PaperInterface.strategic_equilibrium_ae_of_pointwise`, with proof-interface
projections for a.e. student feasibility and best response; use it when
cutoff-tie obligations are null events rather than source-level pointwise
requirements.  The same pattern is used for Proposition 2 by
`PaperInterface.proposition2_application_strategy_ae_unique`, which proves the
application-region strategy is unique a.e. when the low/high cutoff singleton
boundaries have zero mass.  The companion
`PaperInterface.proposition2_application_strategy_ae_unique_binary_choice`
states the same a.e. uniqueness result using the reusable
`EconCSLib.NoProfitableBinaryChoiceDeviationAE` apply/not-apply interface.
The applicant-pool row adapter
`PaperInterface.proposition2_strategic_applicant_pool_masses_to_corrected_source_rows`
identifies Lemma 3's Eq. (35) strategic applicant mass with the finite sum of
corrected Proposition 2 admitted-mass source rows after substituting each
group's Eq. (7) application cutoff.
Proposition 6's
preferred generated-row support bundle is now
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_fallback_eq`,
which returns both `J1`'s strict drop-test iff and the weak `(P_sub,P_full)`
equilibrium iff on the same standard-Gaussian diversity table.  The direct
same-fallback generated-row bundle
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_same_fallback`
is the exact iff version for the common table shape where the ordinary
sub/full fallback row is the sub/sub row; it discharges `J2`'s fallback
equality by construction.  The direct
consequence alias
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium`
now packages the strict displayed inequality into both conclusions through the
preferred same-fallback generated-row route with the paper's concrete
group/school names fixed internally; the
same-fallback variant
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback`
removes the explicit pointwise fallback-equality argument in the common table
shape.  The preferred concrete-source row endpoint is now
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows`,
which gives the exact drop-test iff and equilibrium iff on an actual four-row
diversity table; use the `_paper_groups_schools` variant when the table is
already typed over the paper's concrete group and school names.  The source-row
same-fallback variants
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows_same_fallback`
and
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_same_fallback`
discharge `J2`'s weak no-deviation condition from row equality, and also have
`_paper_groups_schools` variants.  The
generated-sub/full source-row variants
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback`
and
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_generated_subFull_same_fallback`
also discharge the `J1` sub/full source-row identity by construction, leaving
only the `J1` full/full source-row identity visible; the `_paper_schools`
variants specialize these source-row endpoints to `GLM20School` and discharge
`J1 != J2` internally.  When the actual full/full row is also the displayed
generated source-parameter row, prefer
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows_generated_rows_same_fallback`
and
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_generated_rows_same_fallback`;
these discharge both school-`J1` source-row identities and the school-`J2`
same-fallback condition by construction, and their `_paper_groups_schools`
variants fix the paper's concrete names internally.  The direct
consequence form is
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows`:
it gives both conclusions on an actual four-row diversity table from the
`J2` weak no-deviation inequality, the two `J1` source-formula row
identifications, and the strict displayed source-parameter inequality.  The
direct policy-state formula aliases
`PaperInterface.proposition6_policy_state_standardGaussian_drop_iff_source_parameter_formulas`,
`PaperInterface.proposition6_policy_state_standardGaussian_subFull_equilibrium_iff_source_parameter_formulas`,
and
`PaperInterface.proposition6_policy_state_standardGaussian_strict_inequality_implies_subFull_equilibrium`
are the shortest route when the actual diversity table rows are already
identified with the paper's source-parameter formulas.  The compact interface
also exposes the generated source-parameter diversity values/rows and row
identity helpers
`PaperInterface.proposition6_source_parameter_full_diversity_value`,
`PaperInterface.proposition6_source_parameter_sub_diversity_value`,
`PaperInterface.proposition6_source_parameter_fullFull_diversity_row`,
`PaperInterface.proposition6_source_parameter_subFull_diversity_row`,
`PaperInterface.proposition6_source_parameter_fullFull_row_eq_source_value_at_j1`,
`PaperInterface.proposition6_source_parameter_subFull_row_eq_source_value_at_j1`,
`PaperInterface.proposition6_source_parameter_fullFull_row_eq_of_j1_formula`,
and
`PaperInterface.proposition6_source_parameter_subFull_row_eq_of_j1_formula`
for auditing actual four-row table instantiations; the away-from-`J1` helpers
`PaperInterface.proposition6_source_parameter_fullFull_row_eq_fallback_of_ne`
and
`PaperInterface.proposition6_source_parameter_subFull_row_eq_fallback_of_ne`
turn `J1 ≠ J2` into the corresponding `J2` fallback-row identity.

Recent Proposition 2 lower-tail source-model wrappers:
`paper_interface_proposition2_owenSelectionLowerTail_eq_owenAffineLowerSelectionMass`
and
`paper_interface_proposition2_owenSelectionLowerTail_eq_correlatedStandardGaussian_lowerLeftRectangleMass`
prove that the normalized lower-tail affine-CDF integral is both the lower
affine source event and the concrete correlated-Gaussian lower-left rectangle
after the full-test cutoff substitution.
`PaperInterface.proposition2_corrected_subEligible_mass_eq_testFree_tail`
now also identifies the corrected test-free eligible-mass formula with the
unnormalized upper tail of the test-free estimated-skill law. The compact
Proposition 2(iii)
aliases now use corrected-source row wrappers, so the human-facing surface no
longer exposes separate `hmore`/`hj1`/`hj2` diversity-row identification
premises.  The applicant-pool adapter
`PaperInterface.proposition2_strategic_applicant_pool_masses_to_corrected_source_rows`
connects those corrected source rows back to the Lemma 3 strategic mass
fixed point.
`PaperInterface.proposition2_strategic_applicant_pool_masses_to_corrected_source_rows_paper_groups`
specializes the same bridge to the paper's two named groups, expanding the
finite sum as the group-A corrected row plus the group-B corrected row.
The compact Proposition 2(iv) alias now likewise uses a source-row wrapper:
`PaperInterface.proposition2_academic_merit_lambda_kappa` specializes the
lower-academic-merit proposition and both academic-merit rows internally before
returning the displayed `lambda < kappa` comparison.
`paper_interface_proposition2_j2MeritStandardizedLowerTailFormula_eq_kappaBoundaryDensityFormula_of_tau_lowerLeftRectangle`
then packages that lower-left rectangle as the paper's `1 - tau` normalization
inside the J2-to-`kappa` bridge, and
`paper_interface_proposition2_j2MeritStandardizedLowerTailFormula_eq_kappaBoundaryDensityFormula_of_tau_lowerLeftRectangle_normalDensity`
plugs in the raw `N(mu, sigmaTilde^2)` boundary density at `qFull`. The
public support theorem `PaperInterface.proposition2_tau_normalization_lower_tail`
now exposes the source-prime fact that, after substituting the displayed
`a'_g(q)` and `b'_g`, the Owen lower-tail selection mass is `1 - tau_g`.
The stronger
`PaperInterface.proposition2_tau_normalization_source_parameters` also
substitutes the displayed `\tilde\sigma_g` source definition and raw full-test
cutoff.
The
standardized total-mass partition
`paper_interface_proposition2_admittedMass_add_lowerLeftRectangle_eq_affineTotalMass`
also proves `D_g + lowerLeft = pi_g sigma_tilde_g Phi(A_g)`, and
`PaperInterface.proposition2_affine_total_mass_source_parameters` proves the
same statement after substituting the displayed `\tilde\sigma_g`,
`\hat a_g(q)`, and `b_g` source definitions.
`PaperInterface.proposition2_strategic_applicant_pool_mass_add_lowerLeft_eq_affineTotal`
then sums this partition over groups after substituting the Lemma 3 Eq. (7)
application cutoff: strategic applicant-pool mass plus lower-left residuals
equals the sum of affine total masses. The remaining
mass-positivity premise in the first diversity criterion is discharged by
`paper_interface_proposition2_part_iii_diversity_criterion_above_high_cutoff_of_subEligibleMass`.
The complementary diversity criterion has the analogous wrapper
`paper_interface_proposition2_part_iii_diversity_criterion_between_cutoffs_of_subEligibleMass`,
using the lower-left-plus-CDF-gap residual decomposition.
The remaining mass work is the concrete two-school Gaussian game
identification behind these source rows, not the Gaussian partition,
positivity, integral/event, upper-tail eligible-mass, source-parameter `tau`
normalization, affine total-mass substitution, or raw-density identity.
The source-prime wrapper
`paper_interface_proposition2_j2MeritSourcePrimes_eq_kappaBoundaryDensityFormula_of_tau_lowerLeftRectangle_normalDensity`
now substitutes the TeX-source definitions of `a'_g(q)` and `b'_g`, so the next
Proposition 2 work should target the source applicant-pool and concrete-game
identification, not the lower-tail Owen algebra.
The public a.e. strategy aliases
`PaperInterface.proposition2_application_strategy_ae_unique_binary_choice`,
`PaperInterface.proposition2_application_strategy_noProfitableBinaryChoiceDeviationAE`,
`PaperInterface.proposition2_application_strategy_ae_unique_gaussian_student_law`,
`PaperInterface.proposition2_application_strategy_ae_unique_strategic_equilibrium`,
and
`PaperInterface.proposition2_application_strategy_ae_unique_strategic_equilibrium_gaussian_student_law`
now use the paper-readable cost-bound route `0 < c_g < v_1 - v_2`, deriving
both inverse-CDF ratio assumptions internally.

Recent Proposition 3 source-row wrapper:
`PaperInterface.proposition3_full_policy_formulas` now points to
`paper_interface_proposition3_full_policy_diversity_ratio_and_academic_merit_formulas_source_rows`,
which specializes the displayed capacity, admitted-share rows, and displayed
`lambda` academic-merit rows internally.  The resulting compact endpoint
returns Equation (37)'s diversity ratio and the paper's displayed `lambda`
academic-merit comparison without separate capacity/diversity/merit
row-identification premises.  The displayed-`lambda` caveat below still
applies: the verified Owen first-moment formula differs from the displayed
source expression by the documented boundary term.

Recent Theorem 3 formula-rewrite wrappers:
`paper_proposition5_part_i_school1_cutoff_objective_iff_exactly_one_cost_case_of_merit_formulas`,
`paper_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case_of_low_and_high_merit_formulas`,
`paper_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case_of_low_merit_formulas`,
and `paper_proposition5_part_ii_school1_cutoff_objective_iff_no_expand_or_low_cost_of_merit_formulas`
reduce the remaining objective-to-merit comparison premises to equalities for
the two displayed school objective values. The reusable composition lemma
`paper_proposition5_cost_merit_continuous_strictAntiOn_of_cutoff_strictMono`
now derives cost-continuity/strict antitonicity of merit from a continuous
strictly increasing cost-to-cutoff map and a continuous strictly decreasing
cutoff-to-merit map.  The compact Theorem 3 paper-facing alias now uses
`paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_raw_survivor_merits`,
which derives the full-sub high-at-low-root premise and cost-indexed based-row
formulas through fixed-law posterior cost rows, generates the sub-full
equation-(50) cost row internally, specializes the standard-Gaussian API and
hazard certificate internally, and states the final school-`J2` survivor side
as the two displayed condition-(12) merit rows while the feasibility surface
carries condition (11).  The generated-table keep-test route remains available as
`PaperInterface.theorem3_two_school_academic_merit_source_family_j2_keeps_test`;
the previous base component-table route remains available as
`PaperInterface.theorem3_two_school_academic_merit_base_table_j2_keeps_test`.
The older abstract
Gaussian-tail-law keep-test route remains
available as `PaperInterface.theorem3_two_school_academic_merit_gaussian_tail_mean_rows`.  The
support alias
`PaperInterface.proposition5_fullSub_ordered_merits_from_posterior_mean_families`
specializes the full-sub low/high order package to source-family
posterior-mean laws, with
`PaperInterface.proposition5_fullSub_high_at_low_root_from_posterior_mean_families`
providing the corresponding root-side premise.
The source-free variants
`PaperInterface.proposition5_fullSub_ordered_merits_from_posterior_mean_source_free_families`
and
`PaperInterface.proposition5_fullSub_high_at_low_root_from_posterior_mean_source_free_families`
generate the low/high test-free full-sub merit rows directly from posterior
Gaussian upper-tail means, leaving only the cost-indexed test-based row
formulas explicit.
The cost-row variants
`PaperInterface.proposition5_fullSub_ordered_merits_from_posterior_mean_source_free_cost_rows`
and
`PaperInterface.proposition5_fullSub_high_at_low_root_from_posterior_mean_source_free_cost_rows`
also generate the cost-indexed based rows internally and specialize the
standard-Gaussian hazard certificate away from the public surface.
The main Theorem 3 alias
`PaperInterface.theorem3_two_school_academic_merit` now uses the fixed-law
posterior cost-row route with generated source-family school-`J2` keep-test
predicates, bundled cost bounds, bundled sub/full affine tail rows, bundled
full/sub affine threshold rows, and bundled full/full capacity/cutoff rows, so
callers no longer need to supply the low/high test-free full-sub merit-row
formula premises, cost-indexed based-row formula premises, a generic Gaussian
hazard certificate, raw condition-(11)--(12) survivor component rows, separate
endpoint threshold-order rows, separate capacity/fill rows, or separate scalar
cost-interval rows.  The
support alias
`PaperInterface.theorem3_two_school_academic_merit_test_free_formula_rows`
preserves the older formula-row route.
The feasibility-aware support alias
`PaperInterface.theorem3_two_school_academic_merit_feasible_surface` now
exposes the school-`J2` survivor condition as the named keep-test predicate;
`PaperInterface.theorem3_two_school_academic_merit_feasible_surface_raw_survivor_merits`
keeps the raw survivor-merit form.  The strict-merit-only bundle
`GLM20Theorem3J2StrictSurvivorMeritRows` is now available for this route, so
condition-(11)'s survivor mass rows need not be exposed when feasibility
already supplies them.  The compact fixed-law/cost-bound/affine-tail route is
available as `PaperInterface.theorem3_two_school_academic_merit_strict_survivor_merits`
and passed `lake build GLM20DroppingStandardizedTesting.PaperInterface` on
2026-05-23.  The base and generated keep-test pairs feed that
bundle through
`PaperInterface.theorem3_subFull_j2_strict_survivor_merit_rows_of_keep_test_pair`
and
`PaperInterface.theorem3_source_family_j2_strict_survivor_merit_rows_of_keep_test_pair`.
The source-family table rows used by these routes are exposed as
`PaperInterface.theorem3_source_family_policy_state_table_rows`; the bundle
now includes generated mass rows, base admitted-merit rows, and fixed-pool
admitted-merit rows. The two school-`J2` keep-test predicates can be audited
together through
`PaperInterface.theorem3_subFull_j2_keep_test_pair_iff_survivor_components`.
On the generated source-family table,
`PaperInterface.theorem3_source_family_subFull_j2_keep_test_pair_iff_survivor_components`
rewrites that pair directly to the displayed condition-(11)--(12) source rows.
`PaperInterface.theorem3_source_family_subFull_j2_keep_test_pair_iff_base_table_keep_test_pair`
connects the generated table's keep-test pair to the base component table's
keep-test pair used by the strongest Theorem 3 wrapper.
The selected objective alias
`PaperInterface.proposition5_fullSub_posterior_family_selected_objective_bridge`
now feeds posterior-mean source-family rows through the full Proposition
5(ii) weighted-objective iff.  The posterior cost-row alias
`PaperInterface.proposition5_fullSub_posterior_source_free_cost_row_objective_bridge`
now uses the fixed-law variant that derives low/high row regularity from
fixed posterior laws plus threshold maps.  The adapter
`PaperInterface.theorem3_binary_objectives_from_fullSub_bridge` preserves a
packaged Proposition 5(ii) threshold/objective bridge while feeding its
objective iff into the binary-objective Theorem 3 source-condition theorem.
`PaperInterface.theorem3_binary_objectives_from_subFull_and_fullSub_bridges`
is the stronger adapter when both Proposition 5(i) and Proposition 5(ii)
threshold/objective bridges are already packaged.
`PaperInterface.theorem3_weighted_binary_objectives_from_subFull_and_fullSub_bridges`
specializes that adapter to the paper's weighted academic-merit binary-policy
surface, and
`PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_subFull_keep_test_and_fullSub_bridge`
generates the Proposition 5(i) sub-full bridge internally from the
standard-Gaussian keep-test/equation-(50) route while still accepting a
packaged Proposition 5(ii) full-sub bridge.
`PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_prop5_bridges`
also generates the Proposition 5(ii) full-sub bridge from the fixed-law
posterior cost-row route, so both Proposition 5 bridge packages are constructed
before entering the binary-objective Theorem 3 adapter.
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_weighted_surface_theorem3_source_conditions_exists`
is the reverse adapter for the same weighted surface: once a route has already
closed Theorem 3 source conditions, it recovers the existential Proposition 5
weighted-objective source surface without restating the binary-policy
equivalence facts.  Use
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_weighted_surface_rich_theorem3_source_conditions_exists`
when the available Theorem 3 route returns extra threshold/root witness facts
alongside the source-condition triple.  For the current feasible Section 5
surface, use
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_feasible_weighted_surface_theorem3_source_conditions_exists`;
its
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_feasible_weighted_surface_rich_theorem3_source_conditions_exists_inferred_extra`
variant is the direct adapter from the rich compact Theorem 3 packages, with
only the current-pair and unilateral-deviation feasibility facts left visible.
For the concrete policy-state sub/full mass-feasibility surface, use
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_theorem3_source_conditions_exists`
or its rich inferred-extra variant; all definitional feasibility facts are
discharged and only school `J2`'s condition-(11) sub/full mass-fill predicate
remains.  If `GLM20Theorem3J2SurvivorRows` is available, the
`..._of_j2_survivor_rows` variants discharge that final feasibility predicate
from the bundled survivor mass rows.
The direct
ordered-merit route remains available as
`PaperInterface.theorem3_two_school_academic_merit_ordered_fullSub`; the raw
source-row variants remain available as
`PaperInterface.theorem3_two_school_academic_merit_raw_survivor_components`
and
`PaperInterface.theorem3_two_school_academic_merit_gaussian_raw_survivor_components`.
The posterior-family raw survivor route
`PaperInterface.theorem3_two_school_academic_merit_posterior_raw_survivor_components`
instantiates the full-sub merit rows as source-family posterior-mean laws while
leaving condition-(12)'s survivor mass/merit comparisons visible.
`PaperInterface.theorem3_subFull_j2_keeps_test_iff_survivor_components`
exposes the named source-game version of each survivor mass+merit pair:
school `J2` keeps the test for the surviving group under `(P_sub,P_full)`.
The forward helper
`PaperInterface.theorem3_subFull_j2_keeps_test_of_survivor_components`
packages a raw condition-(11)--(12) survivor component pair as that named
keep-test predicate.
cutoff-to-merit map. The selected equation-(46) cutoff function is now proved
strictly increasing on any cost domain by
`paper_proposition5_twoFull_apply_payoff_cutoff_strictMonoOn_cost`, assuming
only that it selects zero-payoff cutoffs. Proposition 5(ii)'s lower-vs-high
threshold ordering now has a constructed wrapper:
`paper_proposition5_low_and_high_cost_thresholds_of_merit_crossings` builds
both `c_hat'_g` and `c_hat''_g` and proves `c_hat'_g < c_hat''_g` from the two
monotone merit crossings plus the high-merit-at-low-root comparison; the
condition-(13) objective wrapper
`paper_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case_of_low_and_high_merit_crossings`
uses that construction directly. The full condition-(13)--(14) source bridge
`paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings`
now composes those thresholds with the `K_g` mass/cutoff identities and the
school-`J1` no-expansion/high-threshold formulas. The part-(i) source bridge
`paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_merit_crossings`
does the analogous condition-(10)--(12) composition from the condition-(10)
merit crossing, `K_g` mass identities, and school-`J2` weighted-merit
bookkeeping.  The new paper-level wrapper
`paper_theorem3_source_conditions_of_proposition5_merit_crossings` packages
both sides together: it existentially constructs all three cost-threshold
functions and derives the displayed Theorem 3 equilibrium conditions from the
binary policy-game bridge.

## Source Notes

The current Lean code closes finite admissions accounting identities, proves
the Gaussian Lemma 1 estimated-skill formula and source-surface wiring, and
now proves the main static Proposition 1 conclusions on a canonical
standard-Gaussian fixed-policy source surface: group-B
under-representation/group-fairness failure, individual-fairness failure, and
lower admitted group-B academic merit. It also proves the threshold/diversity
comparative statics and the high-skill individual-fairness-gap comparative
core. Lemma 2 is now exposed as
`paper_interface_lemma2_conditional_posterior_laws_source_surface_standardGaussian`;
the shared Gaussian library proves the CDF derivative and doubled-log density
facts needed by the paper's `q_e` derivative argument. The Theorem 1
access-barrier main-body threshold theorem now has a canonical paper-facing
endpoint:
`paper_interface_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_of_capacity_range`.
The source policy surfaces are definitional, and the common cutoff is
constructed rather than assumed: the shared Gaussian library proves continuity,
strict antitonicity, and two-sided limits for finite Gaussian mixture
upper-tail mass, and
`theorem1BarrierMixtureCapacityThreshold_existsUnique` gives the unique cutoff
whenever the capacity is strictly between zero and the eligible mass. Cutoff
continuity is still available from capacity realization by
`paper_theorem1_barrier_threshold_continuousOn_of_capacity_equations`. The
concrete mathlib-backed normal CDF/quantile/hazard-inverse layer and reusable
Mills-ratio package close the threshold argument without endpoint-crossing
assumptions for the real-valued thresholds. Theorem 2 now has direct
standard-Gaussian no-barrier source-surface wrappers that close the diversity,
group-threshold, high-skill gap, and academic-merit clauses under explicit
eventual-delta assumptions; the raw `hdelta` and affine-slope wrappers remain
as lower-level adapters. The high-skill individual-fairness direction is now
split because the cached source text is inconsistent: the main statement and
narrative say the gap increases after dropping tests, while the appendix proof
derives `I(Pfull) > I(Psub)` on the high-skill tail. Lean exposes both exact
delta-conditional directions and proves those eventual directions cannot both
hold on the same source surface. Theorem 3 now exposes the paper's displayed
conditions (10)--(14) and the `K_g(q)` Gaussian mass formula in Lean, rather
than only opaque certificate fields; Proposition 5(i)'s school-`J1`
case-analysis step and Proposition 5(ii)'s school-`J2` case-analysis step are
also formalized at the cutoff-objective layer, as is Proposition 5(ii)'s
school-`J1` no-expansion/low-cost split. The corresponding cost thresholds
are now constructed from continuous strictly antitone merit crossings for
Proposition 5(i)'s `J1` branch, Proposition 5(ii)'s `J2` lower-threshold
branch, and Proposition 5(ii)'s `J1` high-threshold branch. Proposition
5(ii)'s lower and high thresholds can now be constructed together, including
the paper's `c_hat''_g > c_hat'_g > 0` ordering, once the two monotone merit
crossings and the high-merit-at-low-root comparison are supplied; the
constructed thresholds now feed a full condition-(13)--(14) objective-pair
bridge for `(P_full,P_sub)`. The school-`J2`
part-(i)
condition (11)--(12) objective bridge now reduces to explicit mass,
objective-reduction, and no-tie assumptions. Proposition 5's remaining
single-school threshold branches also have formula-level wrappers reducing the
objective-to-merit comparison premise to equalities for the two displayed
objective values. Theorem 3 now has a paper-facing merit-crossing endpoint
that composes those Proposition 5 branches into the displayed source
conditions. The top-level `PaperInterface.theorem3_two_school_academic_merit`
alias now uses the cutoff-order, threshold-order, affine-based-threshold
fixed-law posterior cost-row strict-survivor public-row variant; positive affine slopes
discharge the based-threshold continuity/strict-antitonicity inputs, and the
generated-table keep-test predicates are discharged from the displayed
condition-(11)--(12) component rows on audit routes.  The public alias now
consumes one
`GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare`
package: condition-(11)'s survivor mass side is carried by
feasibility/capacity rows, the visible survivor input is the strict
condition-(12) merit bundle, and `0 < pi < 1` is bundled with the public rows.
`PaperInterface.theorem3_two_school_academic_merit_survivor_rows_public_rows`
keeps the older four-row public package route available for audit,
`PaperInterface.theorem3_two_school_academic_merit_strict_survivor_public_rows`
keeps the strict-survivor public-row route with the population-share domain as
a separate premise,
`PaperInterface.theorem3_two_school_academic_merit_strict_survivor_generated_rows`
keeps the strict-survivor full/sub generated-row package route available, and
`PaperInterface.theorem3_two_school_academic_merit_fullSub_generated_rows_scalar_components`
keeps the separate scalar full/sub generated-row component route available.
`PaperInterface.theorem3_two_school_academic_merit_fullSub_prior_precision_rows`
is the direct survivor-row audit route when the full/sub generated rows should
be built from primitive prior mean, prior variance, total precision, affine
threshold, and cost-bound rows inside the theorem wrapper.
`PaperInterface.theorem3_two_school_academic_merit_strict_survivor_prior_precision_rows`
is the corresponding feasibility-aware route when the school-`J2` input is
only the strict condition-(12) merit bundle.
The support bridge
`PaperInterface.theorem3_public_rows_with_population_share_of_source_family_j2_keep_test_pair`
turns a generated source-family school-`J2` keep-test pair plus the named row
bundles into the exact public-row premise used by the compact alias.  The raw
primitive variant
`PaperInterface.theorem3_public_rows_with_population_share_of_source_family_j2_keep_test_pair_and_fullSub_prior_precision_rows`
also constructs the full/sub generated-row bundle from prior
mean/variance/precision equalities, affine threshold rows, and cost bounds.
The full top-level route
`PaperInterface.theorem3_two_school_academic_merit_source_family_keep_test_fullSub_prior_precision_rows`
uses that constructor internally before invoking the compact Theorem 3
endpoint.  If only the source-condition triple is needed from a rich Theorem 3
package, use
`PaperInterface.theorem3_source_conditions_exists_from_rich_theorem3_source_conditions_exists`
to strip the extra threshold/root witnesses.
Direct full-sub merit-order assumptions,
explicit full/full capacity-fill premises, full-sub formula-row premises, named
school-`J2` keep-test predicates, and internal Gaussian API parameters are
removed from the compact review surface. The older raw
survivor-merit fixed-law variant remains available as
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_raw_survivor_merits`;
the raw survivor-row Gaussian variant remains available as
`PaperInterface.theorem3_two_school_academic_merit_gaussian_raw_survivor_components`,
and the direct ordered-merit route remains available as
`PaperInterface.theorem3_two_school_academic_merit_ordered_fullSub`. The
source-family keep-test companion
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test`
is the long-name audit alias for the same endpoint. The companion
`PaperInterface.theorem3_two_school_academic_merit_feasible_surface` alias
keeps condition-(11)'s survivor mass inside the feasibility surface and exposes
only raw survivor-merit comparisons for school `J2`. The compact
`PaperInterface.proposition5_subFull_objective_bridge`
alias now points to the equation-(50), capacity-fill, source-family
fixed-pool/group-merit wrapper with school-`J2`'s survivor requirements bundled
as `GLM20Theorem3J2SurvivorRows` and the standard-Gaussian hazard certificate
specialized internally. The separate-component source-row variant remains
available as
`PaperInterface.proposition5_subFull_objective_bridge_source_family_survivor_components`;
the named keep-test variant remains available as
`PaperInterface.proposition5_subFull_objective_bridge_j2_keeps_test`;
the abstract raw-survivor variant remains available as
`PaperInterface.proposition5_subFull_objective_bridge_raw_survivor_conditions`;
the tail-mean and raw-fixed-pool variants remain available as
`PaperInterface.proposition5_subFull_objective_bridge_tail_mean_fixed_pool`
and `PaperInterface.proposition5_subFull_objective_bridge_raw_fixed_pool`.
`PaperInterface.proposition5_school2_zero_fallback_objective_bridge` packages
the school-`J2` branch-conditioned objective iff from the same bundled
condition-(11)--(12) source rows used by the top Theorem 3 wrapper, with the
standard-Gaussian API and hazard certificate specialized internally.  The
separate-component variant remains available as
`PaperInterface.proposition5_school2_zero_fallback_objective_bridge_base_survivor_components`.
Proposition 5(ii)'s
high-at-low-root premise can now be proved via
`paper_interface_proposition5_high_merit_at_low_root_of_test_free_lt_and_test_based_le`,
which reduces it to direct high-vs-low test-free and test-based merit
inequalities. The Gaussian source bridge
`paper_interface_proposition5_fullSub_ordered_merits_of_gaussian_tail_mean_formulas`
derives those inequalities from concrete Gaussian upper-tail-mean formulas and
scale/threshold comparisons; the selected equation-(46) threshold wrapper
`paper_interface_proposition5_low_and_high_cost_thresholds_of_selected_twoFull_merit_crossings_interval_of_gaussian_tail_mean_formulas`
then constructs the ordered low/high full-sub thresholds from that Gaussian
data.  The selected equation-(46) weighted-objective bridge
`paper_interface_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_gaussian_tail_mean_formulas`
now feeds the same Gaussian tail-mean package directly into the Proposition
5(ii) objective iff, eliminating the standalone high-at-low-root premise at
that surface as well. The newer Theorem 3 cost-row bridge
`PaperInterface.theorem3_two_school_academic_merit_posterior_cost_rows`
pushes this one layer higher for Theorem 3: the full-sub low/high test-free
rows and the cost-indexed based rows are generated directly from posterior
source-family laws, rather than through separate based-formula premises.
The component-table variant
`PaperInterface.theorem3_two_school_academic_merit_posterior_cost_rows_components`
also rewrites condition-(12)'s school-`J2` survivor obligations back to the
source component rows, so use it as the preferred human-facing cost-row
surface when regularity is already available.  The stronger alias
`PaperInterface.theorem3_two_school_academic_merit_fixed_law_posterior_cost_rows_components`
is the preferred surface for the standard-Gaussian fixed-law case: it keeps
the same source component-row survivor obligations and discharges the low/high
cost-row continuity and strict-antitone premises from fixed posterior laws plus
regular threshold maps.  The zero-fallback variant
`PaperInterface.theorem3_two_school_academic_merit_fixed_law_posterior_cost_rows_zero_fallback`
pushes this one step farther by making the school-`J2` expanding-group zero
rows definitional and leaving only the source survivor rows on the base row.
The equation-(50) variant
`PaperInterface.theorem3_two_school_academic_merit_equation50_fixed_law_posterior_cost_rows_zero_fallback`
also generates the sub-full cost row from the displayed equation-(50) formula,
so its continuity and strict-antitone premises are discharged internally.  The
public standard-Gaussian alias
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback`
additionally specializes away the internal CDF API, hazard certificate, and
certificate-equality arguments from that same strongest route.  The raw-row
variant
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_raw_survivor_merits`
weakens the survivor-merit assumptions to unconditional paper rows, and the
generated-table keep-test variant
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test`
converts named source-family keep-test predicates into that base route.  The
threshold-order companion
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_threshold_order_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test`
is the preferred generated-table keep-test route when the full-sub endpoint
crossings are source threshold-order comparisons rather than explicit
upper-tail merit inequalities.  The cutoff-order companion
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_cutoff_order_threshold_order_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test`
also derives the two full/full capacity-fill premises from
`fullFullCutoff g <= q_iSub`.  The affine-threshold companion
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_cutoff_order_threshold_order_affine_thresholds_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test`
further derives the full-sub based-threshold regularity premises from positive
affine slopes, and the compact `PaperInterface.theorem3_two_school_academic_merit`
alias now points to the paper-facing source-row companion whose school-`J2`
condition-(11)--(12) side is bundled as `GLM20Theorem3J2SurvivorRows` and
whose full/sub generated rows are bundled as
`GLM20Theorem3FullSubGeneratedRows`.
The keep-test companion
`PaperInterface.theorem3_two_school_academic_merit_source_family_keep_test_surface`
uses the same compact cost-bound/capacity-row route, but takes the generated
source-family school-`J2` keep-test pair instead.
The
helper
`PaperInterface.theorem3_posterior_cost_row_regularity` discharges the
continuity/strict-antitone row premises in the standard-Gaussian fixed-law
case from a continuous, strictly antitone threshold map; use
`PaperInterface.theorem3_posterior_low_high_cost_row_regularities` when both
full-sub low/high rows should be discharged together.  Use
`PaperInterface.theorem3_keep_signal_rows_components` when the generated
keep-test signal assumptions are bundled as `GLM20Theorem3KeepSignalRows`.
Use
`PaperInterface.theorem3_fullSub_fixed_law_rows_components` to turn the
bundled primitive fixed-law source rows
`GLM20Theorem3FullSubFixedLawRows` into the two posterior-law equalities used
by the same route.  Use
`PaperInterface.theorem3_fullSub_generated_rows_of_prior_precision_rows` when
the source model supplies raw prior mean/variance/precision equalities,
affine threshold rows, and cost bounds, and use
`PaperInterface.theorem3_fullSub_generated_rows` when
the whole generated full/sub source package should travel as one premise:
extra-noise positivity, fixed-law rows, affine threshold rows, and cost bounds.
The compact `PaperInterface.theorem3_two_school_academic_merit` alias now uses
`GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare`;
generated-row and scalar-component aliases remain available for audits that
want the separate rows.
Use
`PaperInterface.theorem3_posterior_low_high_endpoint_crossings` to derive the
four full-sub endpoint merit-crossing inequalities from fixed posterior laws
and endpoint threshold-order comparisons.  The Proposition 5(ii) bridge
`PaperInterface.proposition5_fullSub_posterior_source_free_cost_row_objective_bridge_threshold_order`
now composes that endpoint-crossing step into the fixed-law posterior cost-row
objective route through bundled full/sub affine threshold rows and bundled
full/full capacity/cutoff rows, so callers can state source-shaped threshold
and cutoff facts rather than four Gaussian upper-tail merit inequalities or
separate capacity-fill premises.  The weighted
Theorem 3 adapter
`PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_prop5_threshold_order_bridge`
feeds that same threshold-order Proposition 5(ii) package together with the
standard-Gaussian Proposition 5(i) keep-test bridge into the binary-objective
Theorem 3 source-condition theorem.
The support alias
`PaperInterface.theorem3_source_family_j2_keep_test_pair_of_survivor_rows`
is the direct bridge from the four real condition-(11)--(12) survivor mass and
strict weighted-merit facts to the generated source-family school-`J2`
keep-test pair used by older keep-test surfaces.  The public
`PaperInterface.theorem3_j2_survivor_rows_components` alias unpacks the same
bundled source condition for audit.
Use this route for cost-indexed posterior rows; the selected equation-(46)
wrappers remain the correct surface only when the rows are genuinely
cutoff-indexed. The newer weighted-objective bridge
`paper_interface_proposition5_part_i_school2_objective_bridges_of_weighted_objective_zero_contributions`
removes two objective-equality premises for condition (11)--(12) when the
expanding group has zero weighted contribution and the surviving group has the
displayed nonzero mass/no-tie comparison; the compact `PaperInterface`
aliases `proposition5_school2_objective_bridge_zero_*` expose the
zero-contribution and zero-admitted-merit variants. Theorem 1's full-interval
capacity/selectivity domain is now explicit in a source-model structure rather
than hidden as loose assumptions, and the low-capacity regime is proved
nonempty. Theorem 2's paper-facing source-model wrapper now follows the
main-text high-skill direction under the extra test-free precision assumption
`subB < subA`; the Appendix D.4 crossed-order derivation is documented as a
source-text issue in `FINAL_VALIDATION_REPORT.md`. The paper is not fully
closed: the
Appendix D.6 standardized source-affine mass identity is now exposed not only
for Proposition 3's selection core and `tau_g`, but also for Proposition 2's
`D_g` admitted-mass formula, substituted application/admission masses, and
Proposition 6's full-policy diversity formula. The standardized product-tail
and first-moment Owen identities needed for Proposition 3 academic merit are
now proved in the shared Gaussian library and exposed in the paper interface.
Proposition 6's preferred generated-row surface is now specialized to the
paper's concrete schools by
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_same_fallback_paper_schools`
and
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback_paper_schools`,
so the generated standard-Gaussian diversity-table route has no separate
`J1 != J2` premise and returns the drop-test/equilibrium conclusions directly
from the displayed strict/weak source-parameter comparisons.
Proposition 5's typed source-condition surface now has rich-bridge adapters
that consume the current threshold-construction bridge shape directly, so the
next strategic proof pass should feed the concrete sub/full and full/sub
objective bridge outputs into
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_three_subFull_six_fullSub_side_condition_bridges_and_positive_costs`
or its full/full cost-family variant before handing the result to Theorem 3.
If Theorem 3 source conditions are already available on the weighted
academic-merit surface, use
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_weighted_surface_theorem3_source_conditions_exists`
instead of reconstructing the Proposition 5 bridge inputs; use the
`_rich_theorem3_source_conditions_exists` variant when the theorem also returns
extra threshold/root witnesses.  If the Theorem 3 source conditions are on the
feasible weighted academic-merit surface, use
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_feasible_weighted_surface_theorem3_source_conditions_exists`
or its inferred-extra rich variant; these expose exactly the feasibility facts
needed to erase the feasible-best-response guards.  On the concrete
policy-state sub/full mass-feasibility surface, use the
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_*`
adapters to discharge all definitional feasibility facts, leaving only school
`J2`'s condition-(11) sub/full mass-fill predicate.  The
`..._of_j2_survivor_rows` adapters discharge that predicate from the full
survivor-row source bundle when it is available.  The
`..._of_base_j2_keep_test_pair` and
`..._of_source_family_j2_keep_test_pair` adapters discharge the same predicate
directly from base-table or generated source-family school-`J2` keep-test
pairs when the Theorem 3 route exposes condition (11)--(12) in that form.
These adapters close the feasibility guard only; the generated-table
keep-test Theorem 3 endpoint still depends on the `honlyA`/`honlyB`
objective-row identifications before it can be turned into a closed
Proposition 5 source-condition theorem.
The remaining hard work is
deciding whether the Theorem 1 full-interval domain is an intended paper
assumption or should be
weakened, resolving the displayed-`lambda` merit-scaling discrepancy, and
closing the concrete two-school strategic applicant-pool and objective
instantiations behind Proposition 2 and Theorem 3, plus actual-source-table
row identification for Proposition 6 only if the generated-row table is not
accepted as the final source surface.
