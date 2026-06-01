import GLM20DroppingStandardizedTesting.ProofInterface

/-!
# Paper Interface: GLM20 Dropping Standardized Testing

This file is the compact human-review surface for *Dropping Standardized
Testing for Admissions Trades Off Information and Access*.  It intentionally
lists only the paper-facing definitions and named theorem/proposition endpoints;
the exhaustive proof ledger remains in `ProofInterface.lean`.
-/

namespace GLM20DroppingStandardizedTesting
namespace PaperInterface

/-- Policy notation `P_full`, the test-using admissions policy. -/
abbrev definition_policy_full := GLM20DroppingStandardizedTesting.paperPFull

/-- Policy notation `P_sub`, the test-dropping admissions policy. -/
abbrev definition_policy_sub := GLM20DroppingStandardizedTesting.paperPSub

/-- School notation `J_1`, the first school in Theorem 3. -/
abbrev definition_school_J1 :=
  GLM20DroppingStandardizedTesting.paper_interface_theorem3_schoolJ1

/-- School notation `J_2`, the second school in Theorem 3. -/
abbrev definition_school_J2 :=
  GLM20DroppingStandardizedTesting.paper_interface_theorem3_schoolJ2

/-- Theorem 3 population-share row: group A has share `1 - pi`, group B has share `pi`. -/
abbrev definition_theorem3_populationShare :=
  GLM20DroppingStandardizedTesting.paper_interface_theorem3_populationShare

/-- Appendix F Definition 1: finite-kernel Blackwell sufficiency. -/
abbrev definition_blackwell_sufficient :=
  @GLM20DroppingStandardizedTesting.paperBlackwellSufficient

/--
Proposition 7(i): general-distribution diversity characterization.

Paper statement: with a single posterior-score crossing `q_+`, group `B` is
under-represented iff the school capacity is below the aggregate tail mass
above `q_+`.
-/
abbrev proposition7_diversity_underrepresentation :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition7_diversity_underrepresented_iff_capacity_lt_crossing_tail

/--
Proposition 7(ii): general-distribution academic-merit ordering.

Paper statement: under the same second-order stochastic dominance /
mean-preserving-spread condition, admitted group-`B` academic merit is no
greater than admitted group-`A` academic merit; the strict wrapper exposes the
source's strict linear-utility comparison.
-/
abbrev proposition7_academic_merit_order :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition7_academic_merit_groupB_le_groupA_of_increasingConcaveOrder

/--
Proposition 7(ii), strict support: if the source dominance gives a strict
linear-utility comparison, admitted group-`B` academic merit is strictly below
admitted group-`A` academic merit.
-/
abbrev proposition7_academic_merit_strict_order :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition7_academic_merit_groupB_lt_groupA_of_linearUtility

/--
Proposition 7(iii): general-distribution individual-fairness threshold.

Paper statement: there is a skill threshold above which the individual fairness
gap is positive.
-/
abbrev proposition7_individual_fairness_threshold :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition7_exists_individual_fairness_threshold

/--
Proposition 8: fixed-policy affirmative action.

Paper statement: affirmative action improves the individual-fairness gap,
gives the displayed positive-gap cutoff, keeps group `B` below group `A` in
admitted academic merit, raises group `A` admitted merit, and lowers group `B`
admitted merit.
-/
abbrev proposition8_affirmative_action_fixed_policy :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition8_affirmative_action_fixed_policy_standardGaussian

/--
Proposition 9: dropping tests under affirmative action.

Paper statement: dropping the test under affirmative action improves group
`g`'s admitted academic merit iff the access level satisfies
`gamma_g <= hat_gamma_g`.
-/
abbrev proposition9_affirmative_action_drop_threshold :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition9_dropping_tests_affirmative_action_iff_gamma_le_hatGammaSource

/--
Proposition 9 monotonicity clause: fixing all other parameters, increasing the
test variance weakly increases the displayed access threshold `hat_gamma_g`.
-/
abbrev proposition9_affirmative_action_threshold_monotonicity :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition9_hatGammaSource_mono_of_test_variance_increases

/-- Lemma 1: estimated skill source surface. -/
abbrev lemma1_estimated_skill :=
  @GLM20DroppingStandardizedTesting.paper_interface_lemma1_estimated_skill_source_surface

/-- Proposition 1: fixed-policy group and individual fairness metrics. -/
abbrev proposition1_fixed_policy_metrics :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition1_fixed_policy_static_core_source_surface_standardGaussian

/-- Lemma 2: conditional-posterior law source surface. -/
abbrev lemma2_individual_fairness_gap :=
  @GLM20DroppingStandardizedTesting.paper_interface_lemma2_conditional_posterior_laws_source_surface_standardGaussian

/-- Theorem 1: dropping tests with admissions barriers. -/
abbrev theorem1_dropping_tests_with_barriers :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_source_model

/-- Theorem 2: dropping tests without admissions barriers. -/
abbrev theorem2_dropping_tests_without_barriers :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem2_dropping_tests_without_barriers_standardGaussian_source_model

/--
Theorem 2 audit theorem: the main-text high-skill individual-fairness-gap
direction and the appendix high-skill direction cannot both hold on the same
source surface.
-/
abbrev theorem2_high_skill_direction_inconsistency :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem2_eventual_high_skill_gap_directions_inconsistent

/-- Strategic two-school equilibrium condition, `P_sub`/`P_full` case. -/
abbrev strategic_equilibrium_subFull :=
  @GLM20DroppingStandardizedTesting.paper_interface_two_school_binary_policy_equilibrium_subFull_iff

/-- Strategic two-school equilibrium condition, `P_full`/`P_sub` case. -/
abbrev strategic_equilibrium_fullSub :=
  @GLM20DroppingStandardizedTesting.paper_interface_two_school_binary_policy_equilibrium_fullSub_iff

/-- Strategic two-school equilibrium condition, `P_full`/`P_full` case. -/
abbrev strategic_equilibrium_fullFull :=
  @GLM20DroppingStandardizedTesting.paper_interface_two_school_binary_policy_equilibrium_fullFull_iff

/--
Section 5 strategic equilibrium with student feasibility and best response
required almost everywhere under the realized continuous student law.
-/
abbrev strategic_equilibrium_ae :=
  @GLM20DroppingStandardizedTesting.paperStrategicEquilibriumAE

/--
Section 5 a.e. strategic-equilibrium projection: chosen student actions are
feasible almost everywhere.
-/
abbrev strategic_equilibrium_ae_student_feasible :=
  @GLM20DroppingStandardizedTesting.paper_interface_strategic_equilibrium_ae_student_feasible

/--
Section 5 a.e. strategic-equilibrium projection: chosen student actions are
best responses almost everywhere.
-/
abbrev strategic_equilibrium_ae_student_best_response :=
  @GLM20DroppingStandardizedTesting.paper_interface_strategic_equilibrium_ae_student_best_response

/--
Section 5 a.e. strategic-equilibrium projection: the chosen school policy is
feasible.
-/
abbrev strategic_equilibrium_ae_school_policy_feasible :=
  @GLM20DroppingStandardizedTesting.paper_interface_strategic_equilibrium_ae_school_policy_feasible

/--
Section 5 a.e. strategic-equilibrium projection: the chosen school policy is
a school-side best response.
-/
abbrev strategic_equilibrium_ae_school_policy_best_response :=
  @GLM20DroppingStandardizedTesting.paper_interface_strategic_equilibrium_ae_school_policy_best_response

/-- Section 5 a.e. strategic-equilibrium projection: assignment consistency. -/
abbrev strategic_equilibrium_ae_assignment_consistent :=
  @GLM20DroppingStandardizedTesting.paper_interface_strategic_equilibrium_ae_assignmentConsistent

/--
Section 5 support: pointwise strategic equilibrium implies the corresponding
almost-everywhere student-equilibrium surface for continuous type laws.
-/
abbrev strategic_equilibrium_ae_of_pointwise :=
  @GLM20DroppingStandardizedTesting.paper_interface_strategic_equilibrium_ae_of_strategic_equilibrium

/--
Section 5 a.e. strategic-equilibrium projection: the continuous student side
as a reusable `IsChoiceEquilibriumAE` surface.
-/
abbrev strategic_equilibrium_ae_student_choice_equilibrium :=
  @GLM20DroppingStandardizedTesting.paper_interface_strategic_equilibrium_ae_student_choice_equilibrium

/--
Section 5 a.e. strategic-equilibrium projection: derive a reusable
binary-choice no-profitable-deviation premise for apply/not-apply actions.
-/
abbrev strategic_equilibrium_ae_binary_choice_projection :=
  @GLM20DroppingStandardizedTesting.paper_interface_strategic_equilibrium_ae_binary_choice_projection

/-- Strategic two-school equilibrium conditions for all three Section 5 policy pairs. -/
abbrev strategic_equilibrium_three_cases :=
  @GLM20DroppingStandardizedTesting.paper_interface_two_school_binary_policy_equilibrium_three_cases

/-- Feasibility-aware strategic equilibrium conditions for all three Section 5 policy pairs. -/
abbrev strategic_feasible_equilibrium_three_cases :=
  @GLM20DroppingStandardizedTesting.paper_interface_two_school_binary_policy_feasible_equilibrium_three_cases

/-- Lemma 3: unique equilibrium under `P_full`. -/
abbrev lemma3_unique_full_policy_equilibrium :=
  @GLM20DroppingStandardizedTesting.paper_interface_lemma3_unique_equilibrium_full_policy

/--
Lemma 3 / Proposition 2 source endpoint: unique full-policy threshold
equilibrium for the paper's two named groups, with the corrected
conditional-source bivariate applicant-mass rows substituted.
-/
abbrev lemma3_full_policy_threshold_equilibrium_conditional_source_paper_groups :=
  @GLM20DroppingStandardizedTesting.paper_interface_lemma3_full_policy_threshold_equilibrium_existsUnique_of_standardBivariate_conditional_source_paper_groups

/--
Proposition 2: unique two-school equilibrium, using the paper-readable
group cost-bounds endpoint.
-/
abbrev proposition2_two_school_equilibrium :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_standardGaussian_mixture_group_threshold_equilibrium_existsUnique_precision_of_cost_bounds

/--
Proposition 2 support: the two-school application-region strategy is unique
almost everywhere when the two cutoff boundaries have zero mass, using
paper-readable cost bounds.
-/
abbrev proposition2_application_strategy_ae_unique :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_cost_bounds

/--
Proposition 2 support: a.e. application-region uniqueness with the
apply/not-apply best-response premise stated using the reusable binary-choice
a.e. library predicate and paper-readable cost bounds.
-/
abbrev proposition2_application_strategy_ae_unique_binary_choice :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_binary_choice_of_cost_bounds

/--
Proposition 2 support: the displayed application-region strategy itself
satisfies the reusable a.e. binary no-profitable-deviation predicate under
paper-readable cost bounds.
-/
abbrev proposition2_application_strategy_noProfitableBinaryChoiceDeviationAE :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_two_school_application_region_noProfitableBinaryChoiceDeviationAE_standardGaussian_of_cost_bounds

/--
Proposition 2 support: a.e. application-region uniqueness under a Gaussian
student law, with cutoff-boundary nullness discharged internally and
paper-readable cost bounds.
-/
abbrev proposition2_application_strategy_ae_unique_gaussian_student_law :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_binary_choice_gaussian_student_law_of_cost_bounds

/--
Proposition 2 support: a.e. application-region uniqueness with the
best-response premise supplied by a GLM20 a.e. strategic equilibrium and
paper-readable cost bounds.
-/
abbrev proposition2_application_strategy_ae_unique_strategic_equilibrium :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_strategic_equilibrium_of_cost_bounds

/--
Proposition 2 support: a.e. application-region uniqueness from a GLM20 a.e.
strategic equilibrium under a Gaussian student law and paper-readable cost
bounds.
-/
abbrev proposition2_application_strategy_ae_unique_strategic_equilibrium_gaussian_student_law :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_strategic_equilibrium_gaussian_student_law_of_cost_bounds

/--
Proposition 2 / Lemma 3 applicant-pool support: the Eq. (35) strategic
applicant mass is the finite sum of corrected admitted-mass source rows after
substituting each group's Eq. (7) application cutoff.
-/
abbrev proposition2_strategic_applicant_pool_masses_to_corrected_source_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_strategic_applicant_pool_masses_to_corrected_source_rows

/--
Proposition 2 / Lemma 3 applicant-pool support for the paper's two named
groups: the Eq. (35) strategic applicant mass is the group-A corrected
admitted-mass source row plus the group-B row after substituting Eq. (7).
-/
abbrev proposition2_strategic_applicant_pool_masses_to_corrected_source_rows_paper_groups :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_strategic_applicant_pool_masses_to_corrected_source_rows_paper_groups

/--
Proposition 2(iii) support: the corrected test-free eligible-mass formula is
the unnormalized upper-tail probability for the test-free estimated-skill law.
-/
abbrev proposition2_corrected_subEligible_mass_eq_testFree_tail :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_subEligibleUnnormalizedMassFormula_eq_scaled_testFreeTail

/--
Proposition 2(iii): diversity criterion when `q^*_{2,sub}` is above the high
cutoff, using the corrected conditional-source eligible-mass surface from
Appendix D.6.
-/
abbrev proposition2_diversity_above_high_cutoff :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_part_iii_diversity_criterion_above_high_cutoff_corrected_source_rows

/--
Proposition 2(iii): diversity criterion in the between-cutoffs case, with the
corrected conditional-source eligible-mass surface from Appendix D.6.
-/
abbrev proposition2_diversity_between_cutoffs :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_part_iii_diversity_criterion_between_cutoffs_corrected_source_rows

/--
Proposition 2(iv): when `q^*_{2,sub} > q_h^g`, school `J1` has lower
academic merit for group `g` than school `J2` iff the displayed
`lambda < kappa` comparison holds, with both academic-merit rows and the
source cutoff specialized internally.
-/
abbrev proposition2_academic_merit_lambda_kappa :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_part_iv_lower_academic_merit_iff_lambda_lt_kappaBoundaryDensity_sourceTau_normalDensity_source_rows

/--
Proposition 2(iv) tau-normalization support: after substituting the displayed
`a'_g(q)` and `b'_g`, the Owen lower-tail selection mass is `1 - tau_g`.
-/
abbrev proposition2_tau_normalization_lower_tail :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_owenSelectionLowerTail_eq_one_sub_kappaSourceTau

/--
Proposition 2(iv) source-parameter tau-normalization support: after
substituting the displayed `a'_g(q)`, `b'_g`, and `\tilde\sigma_g` source
definitions, the Owen lower-tail selection mass at the raw full-test cutoff is
`1 - tau_g`.
-/
abbrev proposition2_tau_normalization_source_parameters :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_owenSelectionLowerTail_eq_one_sub_kappaSourceTau_sourceParameters

/--
Proposition 2(iii)/(iv) source-parameter total-mass support: with the
displayed `\tilde\sigma_g`, `\hat a_g(q)`, and `b_g` substituted, `D_g` plus
the lower-left residual mass is `pi_g sigma_tilde_g Phi(A_g)`.
-/
abbrev proposition2_affine_total_mass_source_parameters :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_admittedMass_add_lowerLeftRectangle_eq_affineTotalMass_sourceParameters

/--
Proposition 2(iii)/(iv) conditional-source total-mass support: the same
partition as `proposition2_affine_total_mass_source_parameters`, but with the
conditional `\hat a_g(q)` row used by Lemma 3's applicant-pool substitution.
-/
abbrev proposition2_affine_total_mass_conditional_source_parameters :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_admittedMass_add_lowerLeftRectangle_eq_affineTotalMass_conditionalSourceParameters

/--
Proposition 2 / Lemma 3 applicant-pool support with total-mass substitution:
the strategic applicant-pool mass plus groupwise lower-left residual masses
equals the sum of affine total masses after substituting Eq. (7).
-/
abbrev proposition2_strategic_applicant_pool_mass_add_lowerLeft_eq_affineTotal :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_strategic_applicant_pool_mass_add_lowerLeft_eq_affineTotal

/--
Proposition 3: full-policy diversity and academic-merit source formulas.

The displayed capacity, group admitted-share rows, and `lambda` academic-merit
rows are specialized internally; the resulting diversity condition is the
Equation (37) ratio form.
-/
abbrev proposition3_full_policy_formulas :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition3_full_policy_diversity_ratio_and_academic_merit_formulas_source_rows

/--
Proposition 3 audit theorem: the upper-tail Owen first-moment expression
equals the source-displayed `lambda` formula plus an explicit boundary term.
-/
abbrev proposition3_lambda_boundary_term :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition3_lambda_owenFirstMomentFormula_eq_lambdaFormula_add_boundaryTerm

/--
Proposition 3 audit theorem: with nonzero slope, nonzero scale, and nonzero
normalization, the verified first-moment expression is not literally the
source-displayed `lambda` formula.
-/
abbrev proposition3_lambda_displayed_formula_discrepancy :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition3_lambda_ne_owenFirstMomentFormula_of_nonzero_slope

/--
Proposition 5(i): objective bridge for the Theorem 3 `P_sub`/`P_full`
condition.

This exposes the equation-(50) source-form route with capacity fill,
group-level admitted-merit formulas, and school-`J2` condition-(11)--(12)
survivor requirements as the bundled source-row predicate shared with
Theorem 3.  The paper's named groups, named schools, and population-share row
are fixed internally, and the fixed-pool merit comparisons are generated from
concrete Gaussian source families.
-/
abbrev proposition5_subFull_objective_bridge :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_survivor_rows_paper_groups_schools_with_population_share

/--
Proposition 5(i) audit support: same source-family survivor-row bridge as
`proposition5_subFull_objective_bridge`, but keeping the group, school, and
positive-share premises abstract.
-/
abbrev proposition5_subFull_objective_bridge_generic_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_survivor_rows

/--
Proposition 5(i) audit support: same source-family survivor-row bridge as
`proposition5_subFull_objective_bridge`, but with the Gaussian hazard
certificate left explicit.
-/
abbrev proposition5_subFull_objective_bridge_explicit_hazard_certificate :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_survivor_rows

/--
Proposition 5(i) audit support: the lower-level source-family bridge where the
condition-(11)--(12) survivor facts are supplied as four separate component
rows.
-/
abbrev proposition5_subFull_objective_bridge_source_family_survivor_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_source_family_survivor_components

/--
Proposition 5 / Theorem 3 support: on the generated source-family
policy-state table, the exactly-one weighted-objective comparisons are reduced
to the twelve admitted-merit row identifications that the Bayesian-game layer
must supply.
-/
abbrev proposition5_exactly_one_weighted_objective_bridge_source_family_policy_state_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_exactly_one_weighted_objective_iff_of_source_family_policy_state_table_rows

/--
Proposition 5 / Theorem 3 support: same generated source-family
exactly-one weighted-objective bridge, but taking the twelve Bayesian-game row
identifications as one certificate.
-/
abbrev proposition5_exactly_one_weighted_objective_bridge_source_family_policy_state_row_package :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_exactly_one_weighted_objective_iff_of_source_family_policy_state_table_row_package

/--
Proposition 5(i) support: same objective bridge as
`proposition5_subFull_objective_bridge`, but exposing the fixed-pool
Gaussian upper-tail-mean data instead of the source families.
-/
abbrev proposition5_subFull_objective_bridge_tail_mean_fixed_pool :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_merit_crossings_interval_capacity_tail_mean_fixed_pool_and_group_merit_formulas_of_raw_survivor_conditions

/--
Proposition 5(i) raw-survivor support: same source-family objective bridge as
`proposition5_subFull_objective_bridge`, but keeping the condition-(12)
survivor mass and strict-merit premises on the abstract policy surface.
-/
abbrev proposition5_subFull_objective_bridge_raw_survivor_conditions :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_raw_survivor_conditions

/--
Proposition 5(i) named-keep-test support: same source-family objective bridge as
`proposition5_subFull_objective_bridge`, but stating school-`J2`'s
condition-(11)--(12) survivor requirement as keep-test predicates.
-/
abbrev proposition5_subFull_objective_bridge_j2_keeps_test :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_keeps_test

/--
Proposition 5(i) named-keep-test audit support with the quantile API and
hazard certificate left explicit.
-/
abbrev proposition5_subFull_objective_bridge_j2_keeps_test_explicit_hazard_certificate :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_keeps_test

/--
Proposition 5(i) legacy support: same objective bridge as
`proposition5_subFull_objective_bridge`, but exposing the two fixed-pool merit
comparisons directly.
-/
abbrev proposition5_subFull_objective_bridge_raw_fixed_pool :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_merit_crossings_interval_capacity_fixed_pool_and_group_merit_formulas_of_raw_survivor_conditions

/--
Proposition 5(i) school-`J2` support: the weighted academic-merit objective
comparison is equivalent to the named keep-test condition when the expanding
group's weighted contribution is zero and the survivor mass/no-tie premises
hold.
-/
abbrev proposition5_school2_objective_bridge_zero_contributions :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_i_school2_objective_bridges_of_weighted_objective_zero_contributions

/--
Proposition 5(i) school-`J2` support: same zero-contribution bridge, with the
no-tie premises discharged by the strict surviving-group merit comparisons.
-/
abbrev proposition5_school2_objective_bridge_zero_contributions_and_merit_gt :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_i_school2_objective_bridges_of_weighted_objective_zero_contributions_and_merit_gt

/--
Proposition 5(i) school-`J2` support: the zero-contribution bridge specialized
to the concrete source proof shape where the expanding group has zero admitted
merit at school `J2`.
-/
abbrev proposition5_school2_objective_bridge_zero_merits :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_i_school2_objective_bridges_of_weighted_objective_zero_merits

/--
Proposition 5(i) school-`J2` support: same zero-admitted-merit bridge, with
strict surviving-group merit comparisons instead of no-tie premises.
-/
abbrev proposition5_school2_objective_bridge_zero_merits_and_merit_gt :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_i_school2_objective_bridges_of_weighted_objective_zero_merits_and_merit_gt

/--
Proposition 5(i) school-`J2` zero-fallback support: the bundled
condition-(11)--(12) source rows imply the branch-conditioned
weighted-objective iff statements on the generated source table where the
expanding group has zero admitted merit at school `J2`.  The paper's named
groups, named schools, and population-share row are fixed internally.
-/
abbrev proposition5_school2_zero_fallback_objective_bridge :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_source_family_j2_zero_fallback_school2_objective_bridge_of_j2_survivor_rows_paper_groups_schools_with_population_share

/--
Proposition 5(i) school-`J2` zero-fallback audit support: same bridge as
`proposition5_school2_zero_fallback_objective_bridge`, but keeping the group,
school, and positive-share premises abstract.
-/
abbrev proposition5_school2_zero_fallback_objective_bridge_generic_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_source_family_j2_zero_fallback_school2_objective_bridge_of_j2_survivor_rows

/--
Proposition 5(i) school-`J2` zero-fallback audit support: same bridge as
`proposition5_school2_zero_fallback_objective_bridge`, with the CDF API and
hazard certificate left explicit.
-/
abbrev proposition5_school2_zero_fallback_objective_bridge_explicit_hazard_certificate :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_source_family_j2_zero_fallback_school2_objective_bridge_of_j2_survivor_rows

/--
Proposition 5(i) school-`J2` zero-fallback audit support: the lower-level
variant where the four condition-(11)--(12) survivor facts are supplied as
separate component rows.
-/
abbrev proposition5_school2_zero_fallback_objective_bridge_base_survivor_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_source_family_j2_zero_fallback_school2_objective_bridge_of_base_survivor_components

/--
Proposition 5(ii) support: the high-at-low-root ordering premise follows from
direct high-vs-low test-free and test-based merit inequalities.
-/
abbrev proposition5_fullSub_high_at_low_root_from_merit_order :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_high_merit_at_low_root_of_test_free_lt_and_test_based_le

/--
Proposition 5(ii) Gaussian source bridge: full-sub low/high ordered-merit
premises follow from concrete Gaussian upper-tail-mean formulas plus
scale/threshold comparisons.
-/
abbrev proposition5_fullSub_ordered_merits_from_gaussian_tail_means :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_fullSub_ordered_merits_of_gaussian_tail_mean_formulas

/--
Proposition 5(ii) source-family bridge: same ordered-merit conclusion as
`proposition5_fullSub_ordered_merits_from_gaussian_tail_means`, but the
Gaussian laws are instantiated as posterior-mean laws from source families.
-/
abbrev proposition5_fullSub_ordered_merits_from_posterior_mean_families :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_fullSub_ordered_merits_of_posterior_mean_scale_families

/--
Proposition 5(ii) source-family bridge: same posterior-mean ordered-merit
bridge, but the low/high test-free merit rows are generated internally from
the source families.
-/
abbrev proposition5_fullSub_ordered_merits_from_posterior_mean_source_free_families :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_fullSub_ordered_merits_of_posterior_mean_source_free_families

/--
Proposition 5(ii) source-family bridge: same posterior-mean ordered-merit
bridge, but both the low/high test-free rows and the cost-indexed based rows
are generated internally from source families, with the standard-Gaussian
hazard certificate specialized away from the review surface.
-/
abbrev proposition5_fullSub_ordered_merits_from_posterior_mean_source_free_cost_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_fullSub_ordered_merits_of_posterior_mean_source_free_cost_rows

/--
Proposition 5(ii) audit support: same posterior cost-row ordered-merit bridge
as `proposition5_fullSub_ordered_merits_from_posterior_mean_source_free_cost_rows`,
but with the Gaussian hazard certificate explicit.
-/
abbrev proposition5_fullSub_ordered_merits_from_posterior_mean_source_free_cost_rows_explicit_hazard_certificate :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_fullSub_ordered_merits_of_posterior_mean_source_free_cost_rows

/--
Proposition 5(ii) source-family bridge: the high-at-low-root premise follows
from posterior-mean source-family merit formulas and precision comparisons.
-/
abbrev proposition5_fullSub_high_at_low_root_from_posterior_mean_families :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_high_merit_at_low_root_of_posterior_mean_scale_families

/--
Proposition 5(ii) source-family bridge: same posterior-mean high-at-low-root
bridge, but the low/high test-free merit rows are generated internally from
the source families.
-/
abbrev proposition5_fullSub_high_at_low_root_from_posterior_mean_source_free_families :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_high_merit_at_low_root_of_posterior_mean_source_free_families

/--
Proposition 5(ii) source-family bridge: same posterior-mean high-at-low-root
bridge, but both the low/high test-free rows and the cost-indexed based rows
are generated internally from source families, with the standard-Gaussian
hazard certificate specialized away from the review surface.
-/
abbrev proposition5_fullSub_high_at_low_root_from_posterior_mean_source_free_cost_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_high_merit_at_low_root_of_posterior_mean_source_free_cost_rows

/--
Proposition 5(ii) audit support: same posterior cost-row high-at-low-root
bridge as
`proposition5_fullSub_high_at_low_root_from_posterior_mean_source_free_cost_rows`,
but with the Gaussian hazard certificate explicit.
-/
abbrev proposition5_fullSub_high_at_low_root_from_posterior_mean_source_free_cost_rows_explicit_hazard_certificate :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_high_merit_at_low_root_of_posterior_mean_source_free_cost_rows

/--
Proposition 5(ii) Gaussian source bridge: the high-at-low-root premise follows
directly from concrete Gaussian upper-tail-mean formulas plus scale/threshold
comparisons.
-/
abbrev proposition5_fullSub_high_at_low_root_from_gaussian_tail_means :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_high_merit_at_low_root_of_gaussian_tail_mean_formulas

/--
Proposition 5(ii) support: selected equation-(46) low/high thresholds can be
constructed from ordered high-vs-low merit premises, without a standalone
high-at-low-root assumption.
-/
abbrev proposition5_fullSub_ordered_selected_thresholds :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_low_and_high_cost_thresholds_of_selected_twoFull_merit_crossings_interval_of_ordered_merits

/--
Proposition 5(ii) support: selected equation-(46) low/high thresholds can be
constructed directly from Gaussian upper-tail-mean formulas plus
scale/threshold comparisons.
-/
abbrev proposition5_fullSub_gaussian_selected_thresholds :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_low_and_high_cost_thresholds_of_selected_twoFull_merit_crossings_interval_of_gaussian_tail_mean_formulas

/--
Proposition 5(ii) support: the selected equation-(46) weighted-objective bridge
can derive its high-at-low-root premise directly from Gaussian upper-tail-mean
formulas plus scale/threshold comparisons.
-/
abbrev proposition5_fullSub_gaussian_selected_objective_bridge :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_gaussian_tail_mean_formulas

/--
Proposition 5(ii) support: the selected equation-(46) weighted-objective bridge
with the full-sub Gaussian merit rows instantiated as posterior-mean
source-family laws.
-/
abbrev proposition5_fullSub_posterior_family_selected_objective_bridge :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_scale_families

/--
Proposition 5(ii) support: same selected weighted-objective bridge, but the
low/high test-free full-sub merit rows are generated internally from
posterior-mean source families.
-/
abbrev proposition5_fullSub_posterior_source_free_selected_objective_bridge :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_source_free_families

/--
Proposition 5(ii) support: interval weighted-objective bridge where both the
low/high test-free rows and the cost-indexed based rows are generated directly
from posterior-mean source families, with standard-Gaussian internals
specialized away from the review surface.  In the common fixed-law case, the
low/high row continuity and strict-antitone premises are discharged from the
threshold maps.
-/
abbrev proposition5_fullSub_posterior_source_free_cost_row_objective_bridge :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows

/--
Proposition 5(ii) support: same fixed-law posterior cost-row objective bridge,
but the endpoint merit-crossing assumptions are generated internally from
fixed posterior laws plus endpoint threshold-order comparisons, and the
full/sub threshold side and full/full capacity/fill side are bundled as source
rows.
-/
abbrev proposition5_fullSub_posterior_source_free_cost_row_objective_bridge_threshold_order :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_affine_threshold_rows_interval_capacity_cutoff_rows_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows

/--
Proposition 5(ii) support: same posterior cost-row objective bridge as
`proposition5_fullSub_posterior_source_free_cost_row_objective_bridge`, but
leaving the low/high row continuity and strict-antitone premises explicit.
-/
abbrev proposition5_fullSub_posterior_source_free_cost_row_objective_bridge_explicit_row_regularities :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_source_free_cost_rows

/--
Proposition 5(ii) audit support: same posterior cost-row objective bridge as
`proposition5_fullSub_posterior_source_free_cost_row_objective_bridge`, but
with the Gaussian CDF API and hazard certificate explicit.
-/
abbrev proposition5_fullSub_posterior_source_free_cost_row_objective_bridge_explicit_gaussian_api :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_source_free_cost_rows

/--
Proposition 5: typed strategic academic-merit source-condition predicate.

This is the non-certificate paper-facing surface for the Proposition 5 proof
seams: the sub/full and full/sub weighted-objective comparisons are equivalent
to the displayed source conditions, and the full/full pair satisfies the source
boundary condition.
-/
abbrev proposition5_strategic_academic_merit_source_conditions :=
  @GLM20DroppingStandardizedTesting.paperProposition5StrategicAcademicMeritSourceConditions

/--
Proposition 5: existential-threshold version of the typed strategic
academic-merit source-condition predicate.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists :=
  @GLM20DroppingStandardizedTesting.paperProposition5StrategicAcademicMeritSourceConditionsExists

/--
Proposition 5: package already-proved objective bridges into the typed
strategic academic-merit source-condition predicate.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_from_objective_bridges :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_of_objective_bridges

/--
Proposition 5: package existential threshold-construction objective bridges
into the existential strategic academic-merit source-condition predicate.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_objective_bridges :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_objective_bridges

/--
Proposition 5: existential source-condition package from constructed
sub/full and full/sub objective bridges, using the abstract positive-cost
full/full source condition.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_objective_bridges_and_positive_costs :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_objective_bridges_and_positive_costs

/--
Proposition 5: existential source-condition package from rich threshold
construction bridges with extra side facts, using the abstract positive-cost
full/full source condition.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_rich_objective_bridges_and_positive_costs :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_rich_objective_bridges_and_positive_costs

/--
Proposition 5: existential source-condition package from the standard rich
bridge shape used by the current Proposition 5(i)/(ii) threshold construction
theorems, using the abstract positive-cost full/full source condition.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_three_subFull_six_fullSub_side_condition_bridges_and_positive_costs :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_three_subFull_six_fullSub_side_condition_bridges_and_positive_costs

/--
Proposition 5: existential source-condition package from the standard rich
bridge shape, deriving positive group costs from bundled sub/full source cost
bounds.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_three_subFull_six_fullSub_side_condition_bridges_and_subFull_cost_bounds :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_three_subFull_six_fullSub_side_condition_bridges_and_subFull_cost_bounds

/--
Proposition 5: existential source-condition package from constructed
sub/full and full/sub objective bridges, using the paper's full/full
cost-family boundary condition.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_objective_bridges_and_fullFull_cost_family :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_objective_bridges_and_fullFull_cost_family

/--
Proposition 5: existential source-condition package from rich threshold
construction bridges with extra side facts, using the paper's full/full
cost-family boundary condition.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_rich_objective_bridges_and_fullFull_cost_family :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_rich_objective_bridges_and_fullFull_cost_family

/--
Proposition 5: existential source-condition package from the standard rich
bridge shape used by the current Proposition 5(i)/(ii) threshold construction
theorems, using the paper's full/full cost-family boundary condition.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_three_subFull_six_fullSub_side_condition_bridges_and_fullFull_cost_family :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_three_subFull_six_fullSub_side_condition_bridges_and_fullFull_cost_family

/--
Proposition 5: existential source-condition package from the standard rich
bridge shape and the full/full cost-family route, deriving positive group
costs from bundled sub/full source cost bounds.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_three_subFull_six_fullSub_side_condition_bridges_and_fullFull_cost_family_of_subFull_cost_bounds :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_three_subFull_six_fullSub_side_condition_bridges_and_fullFull_cost_family_of_subFull_cost_bounds

/--
Proposition 5: package objective bridges into the typed source-condition
predicate, using the abstract positive-cost full/full source condition.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_from_objective_bridges_and_positive_costs :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_of_objective_bridges_and_positive_costs

/--
Proposition 5: package objective bridges into the typed source-condition
predicate, using the paper's full/full cost-family boundary condition.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_from_objective_bridges_and_fullFull_cost_family :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_of_objective_bridges_and_fullFull_cost_family

/--
Proposition 5: recover the typed weighted-objective source-condition predicate
from an already-proved Theorem 3 source-condition triple plus binary
policy-equilibrium equivalences.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_from_theorem3_source_conditions :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_of_theorem3_source_conditions

/--
Proposition 5: existential-threshold version of the reverse bridge from
Theorem 3 source conditions back to the Proposition 5 weighted-objective
source-condition predicate.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_theorem3_source_conditions_exists :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_theorem3_source_conditions_exists

/--
Theorem 3 support: strip a rich existential package with extra threshold or
root witnesses down to the source-condition triple expected by simpler
downstream bridges.
-/
abbrev theorem3_source_conditions_exists_from_rich_theorem3_source_conditions_exists :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_exists_of_rich_theorem3_source_conditions_exists

/--
Proposition 5: recover the existential weighted-objective source-condition
predicate from Theorem 3 source conditions on the paper's weighted academic
merit binary surface.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_weighted_surface_theorem3_source_conditions_exists :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_weightedAcademicMeritBinaryPolicySurface_theorem3_source_conditions_exists

/--
Proposition 5: same reverse bridge as above, but for rich Theorem 3
existential packages that include additional threshold/root witness facts.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_weighted_surface_rich_theorem3_source_conditions_exists :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_weightedAcademicMeritBinaryPolicySurface_rich_theorem3_source_conditions_exists

/--
Proposition 5: recover the existential weighted-objective source-condition
predicate from Theorem 3 source conditions on the paper's feasible weighted
academic-merit binary surface, assuming the current and relevant unilateral
deviation pairs are feasible.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_feasible_weighted_surface_theorem3_source_conditions_exists :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_feasibleWeightedAcademicMeritBinaryPolicySurface_theorem3_source_conditions_exists

/--
Proposition 5: same feasible-surface reverse bridge as above, but for rich
Theorem 3 existential packages that include additional threshold/root witness
facts.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_feasible_weighted_surface_rich_theorem3_source_conditions_exists :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_feasibleWeightedAcademicMeritBinaryPolicySurface_rich_theorem3_source_conditions_exists

/--
Proposition 5: ergonomic feasible-surface reverse bridge for rich Theorem 3
packages, with the extra threshold/root witness predicate inferred from the
package itself.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_feasible_weighted_surface_rich_theorem3_source_conditions_exists_inferred_extra :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_feasibleWeightedAcademicMeritBinaryPolicySurface_rich_theorem3_source_conditions_exists_inferred_extra

/--
Proposition 5: feasible-surface reverse bridge specialized to the concrete
policy-state sub/full mass-feasibility surface.  Only school `J2`'s
condition-(11) sub/full mass feasibility remains explicit; all other current
and deviation feasibility facts are definitional.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_theorem3_source_conditions_exists :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_policyStateSubFullMassFeasibleSurface_theorem3_source_conditions_exists

/--
Proposition 5: rich-package version of the policy-state sub/full
mass-feasibility reverse bridge, with the extra witness predicate inferred
from the supplied Theorem 3 package.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_rich_theorem3_source_conditions_exists_inferred_extra :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_policyStateSubFullMassFeasibleSurface_rich_theorem3_source_conditions_exists_inferred_extra

/--
Theorem 3 / Proposition 5 support: the full school-`J2` survivor source-row
bundle supplies the concrete sub/full mass-feasibility predicate used by the
policy-state feasible surface.
-/
abbrev theorem3_policy_state_subFull_j2_mass_feasible_of_survivor_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_policyStateSubFullJ2MassFeasible_of_j2_survivor_rows

/--
Theorem 3 / Proposition 5 support: the base policy-state school-`J2`
keep-test pair supplies the concrete sub/full mass-feasibility predicate used
by the policy-state feasible surface.
-/
abbrev theorem3_policy_state_subFull_j2_mass_feasible_of_base_j2_keep_test_pair :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_policyStateSubFullJ2MassFeasible_of_base_j2_keep_test_pair

/--
Proposition 5: policy-state sub/full mass-feasibility reverse bridge with
school `J2`'s condition-(11)--(12) survivor rows as the visible source premise.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_theorem3_source_conditions_exists_of_j2_survivor_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_policyStateSubFullMassFeasibleSurface_theorem3_source_conditions_exists_of_j2_survivor_rows

/--
Proposition 5: rich-package version of the policy-state survivor-row reverse
bridge, with the extra witness predicate inferred from the supplied Theorem 3
package.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_rich_theorem3_source_conditions_exists_of_j2_survivor_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_policyStateSubFullMassFeasibleSurface_rich_theorem3_source_conditions_exists_of_j2_survivor_rows

/--
Proposition 5: policy-state sub/full mass-feasibility reverse bridge with the
base policy-state school-`J2` keep-test pair as the visible source premise.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_theorem3_source_conditions_exists_of_base_j2_keep_test_pair :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_policyStateSubFullMassFeasibleSurface_theorem3_source_conditions_exists_of_base_j2_keep_test_pair

/--
Proposition 5: rich-package version of the policy-state base keep-test reverse
bridge, with the extra witness predicate inferred from the supplied Theorem 3
package.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_rich_theorem3_source_conditions_exists_of_base_j2_keep_test_pair :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_policyStateSubFullMassFeasibleSurface_rich_theorem3_source_conditions_exists_of_base_j2_keep_test_pair

/--
Theorem 3 / Proposition 5 support: the generated source-family school-`J2`
keep-test pair supplies the concrete sub/full mass-feasibility predicate used
by the policy-state feasible surface.
-/
abbrev theorem3_policy_state_subFull_j2_mass_feasible_of_source_family_j2_keep_test_pair :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_policyStateSubFullJ2MassFeasible_of_source_family_j2_keep_test_pair

/--
Proposition 5: policy-state sub/full mass-feasibility reverse bridge with the
generated source-family school-`J2` keep-test pair as the visible source
premise.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_theorem3_source_conditions_exists_of_source_family_j2_keep_test_pair :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_policyStateSubFullMassFeasibleSurface_theorem3_source_conditions_exists_of_source_family_j2_keep_test_pair

/--
Proposition 5: rich-package version of the policy-state source-family
keep-test reverse bridge, with the extra witness predicate inferred from the
supplied Theorem 3 package.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_rich_theorem3_source_conditions_exists_of_source_family_j2_keep_test_pair :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_policyStateSubFullMassFeasibleSurface_rich_theorem3_source_conditions_exists_of_source_family_j2_keep_test_pair

/--
Theorem 3 support: recover Theorem 3 source conditions from the typed
Proposition 5 strategic academic-merit source-condition predicate plus the
binary policy-equilibrium equivalences.
-/
abbrev theorem3_from_proposition5_strategic_academic_merit_source_conditions :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_proposition5_strategic_academic_merit_source_conditions

/--
Theorem 3 support: existential-threshold version of the bridge from
Proposition 5 strategic academic-merit source conditions.
-/
abbrev theorem3_source_conditions_exists_from_proposition5_strategic_academic_merit_source_conditions_exists :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_exists_of_proposition5_strategic_academic_merit_source_conditions_exists

/--
Theorem 3 support: school `J2`'s condition-(11)--(12) survivor requirement.

On the concrete table surface, the named statement that the other group keeps
the test under `(P_sub,P_full)` is equivalent to the survivor mass lower bound
and strict weighted-merit comparison used by the raw Theorem 3 wrapper.
-/
abbrev theorem3_subFull_j2_keeps_test_iff_survivor_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_otherGroupKeepsTest_iff_components

/--
Theorem 3 support: raw condition-(11)--(12) survivor mass and strict
weighted-merit components imply the named school-`J2` keep-test predicate.
-/
abbrev theorem3_subFull_j2_keeps_test_of_survivor_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_otherGroupKeepsTest_of_components

/--
Theorem 3 support: the named school-`J2` keep-test predicate implies the raw
survivor mass and strict weighted-merit components on the concrete table.
-/
abbrev theorem3_subFull_survivor_components_of_j2_keeps_test :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_components_of_otherGroupKeepsTest

/--
Theorem 3 support: the bundled school-`J2` keep-test predicates for both
possible surviving groups are equivalent to the bundled raw condition-(11)--(12)
survivor mass and strict weighted-merit component rows.
-/
abbrev theorem3_subFull_j2_keep_test_pair_iff_survivor_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_j2_keep_test_pair_iff_components

/--
Theorem 3 support: bundled named school-`J2` keep-test predicates imply the
two raw survivor component rows.
-/
abbrev theorem3_subFull_survivor_components_of_j2_keep_test_pair :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_components_of_j2_keep_test_pair

/--
Theorem 3 support: on the base policy-state table, the named school-`J2`
keep-test pair implies the strict-merit-only survivor row bundle used by
feasibility-aware routes.
-/
abbrev theorem3_subFull_j2_strict_survivor_merit_rows_of_keep_test_pair :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_j2_strict_survivor_merit_rows_of_keep_test_pair

/--
Theorem 3 support: the bundled school-`J2` keep-test predicates on the
generated source-family table are equivalent to the source component rows.
-/
abbrev theorem3_source_family_subFull_j2_keep_test_pair_iff_survivor_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_components

/--
Theorem 3 support: the four substantive survivor mass/merit source-row facts
for condition (11)--(12) imply the generated source-family school-`J2`
keep-test pair used by the compact theorem route.
-/
abbrev theorem3_source_family_j2_keep_test_pair_of_survivor_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_family_j2_keep_test_pair_of_base_survivor_rows

/--
Theorem 3 support: on the generated source-family table, the named school-`J2`
keep-test pair implies the strict-merit-only survivor row bundle used by
feasibility-aware routes.
-/
abbrev theorem3_source_family_j2_strict_survivor_merit_rows_of_keep_test_pair :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_family_j2_strict_survivor_merit_rows_of_keep_test_pair

/--
Theorem 3 support: a generated source-family school-`J2` keep-test pair plus
the named public row bundles packages the compact public-row premise consumed
by `theorem3_two_school_academic_merit`.
-/
abbrev
    theorem3_public_rows_with_population_share_of_source_family_j2_keep_test_pair :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_source_family_j2_keep_test_pair

/--
Theorem 3 support: same public-row package bridge as
`theorem3_public_rows_with_population_share_of_source_family_j2_keep_test_pair`,
but with the full/sub generated rows expanded to primitive Gaussian
prior-precision rows.
-/
abbrev
    theorem3_public_rows_with_population_share_of_source_family_j2_keep_test_pair_and_fullSub_prior_precision_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_source_family_j2_keep_test_pair_and_fullSub_prior_precision_rows

/--
Theorem 3 support: unpack the bundled school-`J2` condition-(11)--(12)
survivor source rows into the two mass lower bounds and two strict weighted
merit comparisons.
-/
abbrev theorem3_j2_survivor_rows_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_j2_survivor_rows_components

/--
Theorem 3 support: unpack the strict-merit-only school-`J2` survivor source
rows used by feasibility-aware routes where capacity is carried by feasibility.
-/
abbrev theorem3_j2_strict_survivor_merit_rows_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_j2_strict_survivor_merit_rows_components

/--
Theorem 3 support: the full condition-(11)--(12) school-`J2` survivor bundle
implies the strict-merit-only bundle used by feasibility-aware routes.
-/
abbrev theorem3_j2_strict_survivor_merit_rows_of_survivor_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_j2_strict_survivor_merit_rows_of_survivor_rows

/--
Theorem 3 support: feed a feasibility-aware endpoint's two strict survivor
merit premises from the bundled strict-merit row predicate.
-/
abbrev theorem3_feasible_endpoint_of_j2_strict_survivor_merit_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_feasible_endpoint_of_j2_strict_survivor_merit_rows

/--
Theorem 3 support: the generated source-family table and the base component
table have equivalent bundled school-`J2` keep-test predicates.
-/
abbrev theorem3_source_family_subFull_j2_keep_test_pair_iff_base_table_keep_test_pair :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_base_table_keep_test_pair

/--
Theorem 3 support: generated source-family policy-state table rows for
mass rows, base admitted-merit rows, and fixed-pool admitted-merit formulas.
-/
abbrev theorem3_source_family_policy_state_table_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_family_policy_state_table_surface_rows

/-- Theorem 3 support: the paper's named groups are distinct. -/
abbrev theorem3_groupA_ne_groupB :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_groupA_ne_groupB

/-- Theorem 3 support: the paper's named groups are distinct. -/
abbrev theorem3_groupB_ne_groupA :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_groupB_ne_groupA

/--
Theorem 3 support: the concrete population-share notation `(1 - pi, pi)`
supplies positive shares for groups A and B from `0 < pi < 1`.
-/
abbrev theorem3_group_populationShare_pos_of_pi_mem_Ioo :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_group_populationShare_pos_of_pi_mem_Ioo
/--
Theorem 3 support: affine-decreasing full-sub based threshold maps are
continuous and strictly antitone on each cost interval.
-/
abbrev theorem3_based_threshold_regularities_of_affine_decreasing :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_based_threshold_regularities_of_affine_decreasing

/--
Theorem 3 support: paired low/high affine-decreasing threshold maps generate
the four regularity premises used by the fixed-law cost-row route.
-/
abbrev theorem3_low_high_based_threshold_regularities_of_affine_decreasing :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_low_high_based_threshold_regularities_of_affine_decreasing

/--
Theorem 3 support: derive the low-based/full-sub fixed posterior-law equality
from prior mean, prior variance, and total centered signal precision rows.
-/
abbrev theorem3_fullSub_low_based_law_of_prior_precision_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_fullSub_low_based_law_of_prior_precision_rows

/--
Theorem 3 support: derive the high-based/full-sub fixed posterior-law equality
from prior mean, prior variance, and total centered signal precision rows.
-/
abbrev theorem3_fullSub_high_based_law_of_prior_precision_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_fullSub_high_based_law_of_prior_precision_rows

/--
Theorem 3 support: derive both low/high full-sub fixed posterior-law
equalities from prior mean, prior variance, and total centered signal
precision rows.
-/
abbrev theorem3_fullSub_based_laws_of_prior_precision_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_fullSub_based_laws_of_prior_precision_rows

/-- Theorem 3 support: bundled primitive full-sub fixed-law source rows. -/
abbrev theorem3_fullSub_fixed_law_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_fullSub_fixed_law_rows

/--
Theorem 3 support: primitive full-sub fixed-law source rows imply both
posterior-law equalities used by the fixed-law cost-row route.
-/
abbrev theorem3_fullSub_fixed_law_rows_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_fullSub_fixed_law_rows_components

/--
Theorem 3 support: bundled generated full/sub source rows, including
extra-noise positivity, fixed posterior-law rows, affine threshold rows, and
full/sub cost bounds.
-/
abbrev theorem3_fullSub_generated_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_fullSub_generated_rows

/--
Theorem 3 support: construct the full/sub generated-row package from primitive
Gaussian prior mean, prior variance, and precision rows, plus affine threshold
rows and cost bounds.
-/
abbrev theorem3_fullSub_generated_rows_of_prior_precision_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_fullSub_generated_rows_of_prior_precision_rows

/--
Theorem 3 support: bundled public source rows for the compact academic-merit
route.
-/
abbrev theorem3_academic_merit_public_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_academic_merit_public_rows

/--
Theorem 3 support: bundled public source rows for the feasibility-aware
academic-merit route with strict school-`J2` survivor merit rows.
-/
abbrev theorem3_academic_merit_strict_survivor_public_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_academic_merit_strict_survivor_public_rows

/--
Theorem 3 support: bundled public source rows plus the population-share domain
for the current compact academic-merit route.
-/
abbrev theorem3_academic_merit_strict_survivor_public_rows_with_population_share :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_academic_merit_strict_survivor_public_rows_with_population_share

/--
Theorem 3 support: package strict-survivor public rows with the
population-share domain.
-/
abbrev theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_rows

/--
Theorem 3 support: package the older four-row public source bundle and the
population-share domain into the current single public-row bundle.
-/
abbrev theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_public_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_public_rows

/--
Theorem 3 support: the older four-row public source bundle implies the
strict-survivor public bundle used by the current main route.
-/
abbrev theorem3_academic_merit_strict_survivor_public_rows_of_public_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_academic_merit_strict_survivor_public_rows_of_public_rows

/-- Theorem 3 support: bundled generated keep-test signal source rows. -/
abbrev theorem3_keep_signal_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_keep_signal_rows

/--
Theorem 3 support: unpack the generated keep-test signal rows into the
positive-variance and threshold-order premises used by lower routes.
-/
abbrev theorem3_keep_signal_rows_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_keep_signal_rows_components

/--
Theorem 3 support: unpack the bundled sub/full affine Gaussian tail-mean row
into the component source assumptions used by lower wrappers.
-/
abbrev theorem3_subFull_affine_tail_rows_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_subFull_affine_tail_rows_components

/--
Theorem 3 support: unpack the bundled full/sub affine threshold row into the
component source assumptions used by lower wrappers.
-/
abbrev theorem3_fullSub_affine_threshold_rows_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_fullSub_affine_threshold_rows_components

/--
Theorem 3 support: unpack the bundled two full/full capacity equations and
four cutoff-order comparisons.
-/
abbrev theorem3_capacity_cutoff_rows_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_capacity_cutoff_rows_components


/--
Theorem 3 support: if each full/full cutoff is weakly below the source cutoff,
then the full/full upper-tail applicant mass weakly fills the capacity.
-/
abbrev theorem3_fullFull_fill_capacity_of_cutoff_le :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_fullFull_fill_capacity_of_cutoff_le

/--
Theorem 3 support: bundled version of the full/full capacity-fill cutoff-order
bridge for the two source cutoffs `q1Sub` and `q2Sub`.
-/
abbrev theorem3_fullFull_fill_capacities_of_cutoff_le :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_fullFull_fill_capacities_of_cutoff_le

/--
Theorem 3 support: apply a theorem endpoint with the two full/full fill
premises by supplying cutoff-order assumptions instead.
-/
abbrev theorem3_apply_fullFull_fill_of_cutoff_order :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_apply_fullFull_fill_of_cutoff_order

/--
Theorem 3 support: positive-share version of the bundled full/full fill
cutoff-order bridge.
-/
abbrev theorem3_fullFull_fill_capacities_of_cutoff_le_of_pos :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_fullFull_fill_capacities_of_cutoff_le_of_pos

/--
Theorem 3 support: positive-share version of the cutoff-order endpoint
adapter.
-/
abbrev theorem3_apply_fullFull_fill_of_cutoff_order_of_pos :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_apply_fullFull_fill_of_cutoff_order_of_pos

/--
Theorem 3 support: a packaged full-sub Proposition 5 objective bridge can be
fed directly into the binary-objective Theorem 3 source-condition bridge.
-/
abbrev theorem3_binary_objectives_from_fullSub_bridge :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_binary_policy_objective_conditions_of_subFull_objective_and_fullSub_objective_bridge

/--
Theorem 3 support: packaged Proposition 5(i) and Proposition 5(ii) objective
bridges can be fed together into the binary-objective Theorem 3
source-condition bridge.
-/
abbrev theorem3_binary_objectives_from_subFull_and_fullSub_bridges :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_binary_policy_objective_conditions_of_subFull_objective_bridge_and_fullSub_objective_bridge

/--
Theorem 3 support: on the paper's weighted academic-merit binary surface,
packaged Proposition 5(i) and Proposition 5(ii) objective bridges imply the
binary-objective Theorem 3 source conditions.
-/
abbrev theorem3_weighted_binary_objectives_from_subFull_and_fullSub_bridges :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_subFull_objective_bridge_and_fullSub_objective_bridge

/--
Theorem 3 support: on the paper's weighted academic-merit binary surface,
Proposition 5(i)'s standard-Gaussian keep-test bridge and a packaged
Proposition 5(ii) full-sub bridge imply the binary-objective Theorem 3 source
conditions.
-/
abbrev theorem3_weighted_binary_objectives_from_standardGaussian_subFull_keep_test_and_fullSub_bridge :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_standardGaussian_subFull_keep_test_bridge_and_fullSub_objective_bridge

/--
Theorem 3 support: on the paper's weighted academic-merit binary surface,
Proposition 5(i)'s standard-Gaussian keep-test bridge and Proposition 5(ii)'s
fixed-law posterior cost-row bridge are both generated internally before
invoking the binary-objective Theorem 3 adapter.
-/
abbrev theorem3_weighted_binary_objectives_from_standardGaussian_prop5_bridges :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_standardGaussian_subFull_keep_test_and_fixed_law_fullSub_cost_rows

/--
Theorem 3 support: same weighted binary-objective adapter as
`theorem3_weighted_binary_objectives_from_standardGaussian_prop5_bridges`, but
the Proposition 5(ii) endpoint crossings are generated from fixed-law
threshold-order comparisons.
-/
abbrev theorem3_weighted_binary_objectives_from_standardGaussian_prop5_threshold_order_bridge :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_standardGaussian_subFull_keep_test_threshold_order_and_fixed_law_fullSub_cost_rows

/--
Theorem 3 strategy support: for continuous student laws, the
application-region uniqueness statement is an a.e. theorem.  The best-response
premise is stated through the reusable binary-choice a.e. predicate, matching
the LG21-style treatment of null indifference boundaries.  Cost assumptions are
the paper-readable bound `0 < c_g < v_1 - v_2`.
-/
abbrev theorem3_application_strategy_ae_unique_binary_choice :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_binary_choice_of_cost_bounds

/--
Theorem 3 strategy support: the displayed application-region strategy satisfies
the reusable a.e. binary no-profitable-deviation predicate under any student
law and paper-readable cost bounds.
-/
abbrev theorem3_application_strategy_noProfitableBinaryChoiceDeviationAE :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_two_school_application_region_noProfitableBinaryChoiceDeviationAE_standardGaussian_of_cost_bounds

/--
Theorem 3 strategy support: a.e. application-region uniqueness under a
Gaussian student law, with cutoff-boundary nullness discharged internally and
paper-readable cost bounds.
-/
abbrev theorem3_application_strategy_ae_unique_gaussian_student_law :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_binary_choice_gaussian_student_law_of_cost_bounds

/--
Theorem 3 strategy support: same a.e. application-region uniqueness result,
but the binary no-deviation premise is projected from a GLM20 a.e. strategic
equilibrium under paper-readable cost bounds.
-/
abbrev theorem3_application_strategy_ae_unique_strategic_equilibrium :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_strategic_equilibrium_of_cost_bounds

/--
Theorem 3 strategy support: a.e. application-region uniqueness from a GLM20
a.e. strategic equilibrium under a Gaussian student law and paper-readable
cost bounds.
-/
abbrev theorem3_application_strategy_ae_unique_strategic_equilibrium_gaussian_student_law :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_strategic_equilibrium_gaussian_student_law_of_cost_bounds

/--
Theorem 3: academic merit and two-school equilibria.

Paper statement: under the displayed source conditions (10)--(14), the policy
pairs `(P_sub,P_full)`, `(P_full,P_sub)`, and `(P_full,P_full)` are equilibria
exactly as stated in Theorem 3.  This interface exposes the strongest
standard-Gaussian source-table route currently verified: fixed-pool merits,
equation (50) supplies the sub/full cost row, and the full-sub fixed-law
posterior cost rows are generated from Gaussian source families; endpoint
crossings come from fixed-law threshold order; based-threshold regularity
comes from positive affine slopes; full/full capacity fill is generated from
cutoff-order facts; the paper's named groups/schools and population-share row
are specialized; the test-keeping source families for `J1` and `J2` are
constructed by adding one positive-variance Gaussian signal to the
test-dropping source families; the full-sub low/high precision comparisons
are generated by adding positive-variance Gaussian signals in the relevant
direction; the fixed posterior-law equalities for the full-sub rows are
generated from primitive source rows bundled as
`GLM20Theorem3FullSubGeneratedRows`; the sub/full admitted-merit row is
generated by a Gaussian upper-tail mean with an affine threshold; and the final
school-`J2` survivor side is stated as the strict condition-(12) merit rows,
with condition-(11)'s capacity-fill side carried by the feasibility/capacity
surface.  The public row requirements and population-share domain are bundled
as `GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare`;
the four-row survivor and component-level generated-row routes remain
available for audits.
-/
abbrev theorem3_two_school_academic_merit :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 source route: same compact endpoint as
`theorem3_two_school_academic_merit`, but constructing the public-row package
internally from a generated source-family school-`J2` keep-test pair and raw
full/sub prior-precision rows.
-/
abbrev
    theorem3_two_school_academic_merit_source_family_keep_test_fullSub_prior_precision_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_j2_keep_test_pair_and_fullSub_prior_precision_rows_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 audit route: same compact public-row theorem as
`theorem3_two_school_academic_merit`, but keeping the population-share domain
as a separate premise.
-/
abbrev theorem3_two_school_academic_merit_strict_survivor_public_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 audit route: same source-family theorem as
`theorem3_two_school_academic_merit`, but using the older four-row school-`J2`
survivor bundle for condition-(11)--(12).
-/
abbrev theorem3_two_school_academic_merit_survivor_rows_public_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_public_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 support: same source-family route as
`theorem3_two_school_academic_merit`, but exposing the full/sub generated-row
components separately for audit.
-/
abbrev theorem3_two_school_academic_merit_fullSub_generated_rows_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_extra_keep_and_fullSub_generated_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 support: same survivor-row source-family route as
`theorem3_two_school_academic_merit_fullSub_generated_rows_components`, but
constructing the full/sub generated-row package from primitive prior-mean,
prior-variance, and precision rows.
-/
abbrev theorem3_two_school_academic_merit_fullSub_prior_precision_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_extra_keep_and_fullSub_prior_precision_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 support: same source-family route as
`theorem3_two_school_academic_merit_fullSub_generated_rows_components`, but
exposing the full/sub generated rows as separate scalar component premises.
-/
abbrev theorem3_two_school_academic_merit_fullSub_generated_rows_scalar_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 feasibility-aware support: same compact source route as
`theorem3_two_school_academic_merit`, but condition-(11)'s survivor mass side
is carried by the feasibility surface, so the visible school-`J2` survivor
input is only the strict condition-(12) merit inequalities bundled as
`GLM20Theorem3J2StrictSurvivorMeritRows`.
-/
abbrev theorem3_two_school_academic_merit_strict_survivor_merits :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 feasibility-aware support: same strict-survivor route as
`theorem3_two_school_academic_merit_strict_survivor_merits`, but with the
full/sub generated-row premises bundled.
-/
abbrev theorem3_two_school_academic_merit_strict_survivor_generated_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_extra_keep_and_fullSub_generated_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 feasibility-aware support: same strict-survivor route as
`theorem3_two_school_academic_merit_strict_survivor_generated_rows`, but
constructing the full/sub generated-row package from primitive prior-mean,
prior-variance, and precision rows.
-/
abbrev theorem3_two_school_academic_merit_strict_survivor_prior_precision_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_extra_keep_and_fullSub_prior_precision_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 support: same compact source route as
`theorem3_two_school_academic_merit`, but condition-(11)--(12) is supplied as
the generated source-family school-`J2` keep-test pair.
-/
abbrev theorem3_two_school_academic_merit_source_family_keep_test_surface :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_j2_keeps_test_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 paper-group support: same named groups/schools/population-share
surface as `theorem3_two_school_academic_merit`, but exposing the sub/full
admitted-merit row as an abstract continuous, strictly antitone cutoff
function with endpoint crossings.
-/
abbrev theorem3_two_school_academic_merit_canonical_laws :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws

/--
Theorem 3 paper-group support: same named groups/schools/population-share
surface as `theorem3_two_school_academic_merit`, but exposing the auxiliary
full-sub fixed-law functions explicitly.
-/
abbrev theorem3_two_school_academic_merit_extra_keep_and_fullSub_signals :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_and_fullSub_signals

/--
Theorem 3 paper-group support: same named groups/schools/population-share
surface as `theorem3_two_school_academic_merit`, but still exposing the
full-sub low/high family precision comparisons explicitly.
-/
abbrev theorem3_two_school_academic_merit_extra_keep_signals :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_signals

/--
Theorem 3 paper-group support: same named groups/schools/population-share
surface as `theorem3_two_school_academic_merit`, but with the `J1` and `J2`
test-keeping source families supplied explicitly.
-/
abbrev theorem3_two_school_academic_merit_explicit_keep_families :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools

/--
Theorem 3 generic source-family support: same verified route as
`theorem3_two_school_academic_merit`, but retaining abstract group/school
parameters for audit and reuse.
-/
abbrev theorem3_two_school_academic_merit_generic_source_surface :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components

/--
Theorem 3 posterior-family audit support: the source-family survivor-row route
with the Gaussian hazard certificate explicit for audit comparisons.
-/
abbrev theorem3_two_school_academic_merit_explicit_hazard_certificate :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_posterior_mean_fullSub_source_free_merits_of_source_family_survivor_components

/--
Theorem 3 posterior-family support: same route as
`theorem3_two_school_academic_merit`, but the final school-`J2` survivor
requirements are stated as named keep-test predicates on the generated
source-family policy-state table.
-/
abbrev theorem3_two_school_academic_merit_source_family_j2_keeps_test :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test

/--
Theorem 3 generated-table keep-test support with the Gaussian hazard certificate
kept explicit for audit comparisons.
-/
abbrev theorem3_two_school_academic_merit_source_family_j2_keeps_test_explicit_hazard_certificate :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_posterior_mean_fullSub_source_free_merits_of_source_family_j2_keeps_test

/--
Theorem 3 posterior-family support: same route as
`theorem3_two_school_academic_merit`, but the final school-`J2` keep-test
predicates are stated on the base component policy-state table.
-/
abbrev theorem3_two_school_academic_merit_base_table_j2_keeps_test :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_posterior_mean_fullSub_source_free_merits_of_j2_keeps_test

/--
Theorem 3 base component-table keep-test support with the Gaussian hazard
certificate kept explicit for audit comparisons.
-/
abbrev theorem3_two_school_academic_merit_base_table_j2_keeps_test_explicit_hazard_certificate :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_posterior_mean_fullSub_source_free_merits_of_j2_keeps_test

/--
Theorem 3 posterior-family support: same route as
`theorem3_two_school_academic_merit`, but exposing the low/high test-free
full-sub merit rows as explicit posterior-mean formula premises.
-/
abbrev theorem3_two_school_academic_merit_test_free_formula_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_posterior_mean_fullSub_merits_of_j2_keeps_test

/--
Theorem 3 Gaussian-tail-law support: same route as
`theorem3_two_school_academic_merit`, but exposing the full-sub merit rows as
abstract Gaussian upper-tail-mean laws instead of posterior-mean source-family
laws.
-/
abbrev theorem3_two_school_academic_merit_gaussian_tail_mean_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_gaussian_fullSub_merits_of_j2_keeps_test

/--
Theorem 3 ordered-merit support: same route as
`theorem3_two_school_academic_merit`, but exposing the direct full-sub merit
ordering assumptions instead of deriving them from Gaussian tail-mean formulas.
-/
abbrev theorem3_two_school_academic_merit_ordered_fullSub :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_ordered_fullSub_merits_of_j2_keeps_test

/--
Theorem 3 raw-survivor support: same route as
`theorem3_two_school_academic_merit`, but exposing condition-(12)'s survivor
mass and survivor-merit comparisons as source-row inequalities.
-/
abbrev theorem3_two_school_academic_merit_raw_survivor_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_raw_survivor_conditions_of_ordered_fullSub_merits

/--
Theorem 3 raw-survivor Gaussian support: same as
`theorem3_two_school_academic_merit_raw_survivor_components`, but the direct
full-sub merit-order premises are derived from Gaussian tail-mean formulas.
-/
abbrev theorem3_two_school_academic_merit_gaussian_raw_survivor_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_raw_survivor_conditions_of_gaussian_fullSub_merits

/--
Theorem 3 raw-survivor posterior-family support: same as
`theorem3_two_school_academic_merit_gaussian_raw_survivor_components`, but the
full-sub Gaussian merit rows are instantiated as posterior-mean source-family
laws.
-/
abbrev theorem3_two_school_academic_merit_posterior_raw_survivor_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_raw_survivor_conditions_of_posterior_mean_fullSub_merits

/--
Theorem 3 posterior cost-row regularity: fixed posterior law plus continuous,
strictly antitone threshold gives continuous and strictly antitone merit rows.
-/
abbrev theorem3_posterior_cost_row_regularity :=
  @GLM20DroppingStandardizedTesting.paper_interface_standardGaussian_posterior_cost_row_regularity_of_fixed_law_threshold_strictAntiOn

/--
Theorem 3 posterior low/high cost-row regularity: the paired version of
`theorem3_posterior_cost_row_regularity` for the two full-sub rows.
-/
abbrev theorem3_posterior_low_high_cost_row_regularities :=
  @GLM20DroppingStandardizedTesting.paper_interface_standardGaussian_posterior_low_high_cost_row_regularities_of_fixed_law_threshold_strictAntiOn

/--
Theorem 3 posterior low/high endpoint crossings: fixed posterior laws plus
endpoint threshold ordering give the four full-sub merit-crossing inequalities.
-/
abbrev theorem3_posterior_low_high_endpoint_crossings :=
  @GLM20DroppingStandardizedTesting.paper_interface_standardGaussian_posterior_low_high_cost_row_endpoint_crossings_of_fixed_law_threshold_order

/--
Theorem 3 posterior-family cost-row support: same two-interval source-family
route, but the full-sub low/high test-free and cost-indexed based rows are
generated directly from posterior-mean source families.
-/
abbrev theorem3_two_school_academic_merit_posterior_cost_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_and_cutoff_fill_subFull_fullSub_interval_of_posterior_mean_fullSub_cost_rows

/--
Theorem 3 posterior-family cost-row support with the school-`J2`
condition-(12) survivor side stated on the source component table.
-/
abbrev theorem3_two_school_academic_merit_posterior_cost_rows_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval_of_posterior_mean_fullSub_cost_rows

/--
Theorem 3 posterior-family cost-row support with source component-row survivor
requirements and low/high cost-row regularity discharged from fixed posterior
laws plus regular threshold maps.
-/
abbrev theorem3_two_school_academic_merit_fixed_law_posterior_cost_rows_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval_of_standardGaussian_fixed_law_posterior_mean_fullSub_cost_rows

/--
Theorem 3 posterior-family cost-row support with fixed-law row regularity and
the school-`J2` zero expanding-group row built into the source table.
-/
abbrev theorem3_two_school_academic_merit_fixed_law_posterior_cost_rows_zero_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_subFull_fullSub_interval_of_standardGaussian_fixed_law_posterior_mean_fullSub_cost_rows

/--
Theorem 3 posterior-family cost-row support with equation-(50) sub-full
regularity, fixed-law full-sub posterior cost rows, and the school-`J2`
zero fallback source table.
-/
abbrev theorem3_two_school_academic_merit_equation50_fixed_law_posterior_cost_rows_zero_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_standardGaussian_fixed_law_posterior_mean_fullSub_cost_rows

/--
Theorem 3 posterior-family cost-row support with the internal standard-Gaussian
API and hazard-certificate parameters specialized away from the public surface.
-/
abbrev theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows

/--
Theorem 3 posterior-family cost-row support with standard-Gaussian internals
specialized and survivor-merit assumptions exposed as unconditional
condition-(12) source rows.
-/
abbrev theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_raw_survivor_merits :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_raw_survivor_merits

/--
Theorem 3 posterior-family cost-row support with the final school-`J2`
survivor side supplied as named keep-test predicates on the base policy-state
table.
-/
abbrev theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_j2_keeps_test :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_j2_keeps_test

/--
Theorem 3 posterior-family cost-row support with the final school-`J2`
survivor side supplied as named keep-test predicates on the generated
source-family policy-state table.
-/
abbrev theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test

/--
Theorem 3 posterior-family cost-row support with source-family school-`J2`
keep-test predicates and full-sub endpoint merit crossings generated from
fixed-law threshold-order comparisons.
-/
abbrev theorem3_two_school_academic_merit_standardGaussian_equation50_threshold_order_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test

/--
Theorem 3 posterior-family cost-row support with source-family school-`J2`
keep-test predicates, full-sub endpoint merit crossings generated from
fixed-law threshold-order comparisons, and full/full capacity fill generated
from cutoff-order facts.
-/
abbrev theorem3_two_school_academic_merit_standardGaussian_equation50_cutoff_order_threshold_order_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test
/--
Theorem 3 posterior-family cost-row support with source-family school-`J2`
keep-test predicates, threshold-order endpoint crossings, cutoff-order
full/full fill, and positive-slope affine based-threshold regularity.
-/
abbrev theorem3_two_school_academic_merit_standardGaussian_equation50_cutoff_order_threshold_order_affine_thresholds_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_j2_keeps_test

/--
Theorem 3 posterior-family cost-row support with threshold-order endpoint
crossings, cutoff-order full/full fill, positive-slope affine based-threshold
regularity, and raw condition-(11)--(12) source rows.
-/
abbrev theorem3_two_school_academic_merit_standardGaussian_equation50_cutoff_order_threshold_order_affine_thresholds_fixed_law_posterior_cost_rows_zero_fallback_source_family_raw_survivor_components :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components


/--
Theorem 3 support, feasibility-aware route: condition-(11)'s survivor-mass
requirements are carried by the explicit feasibility surface, and
condition-(12)'s survivor side is exposed as the named school-`J2` keep-test
predicate.
-/
abbrev theorem3_two_school_academic_merit_feasible_surface :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval_of_j2_keeps_test

/--
Theorem 3 support, feasibility-aware raw-row route: same feasibility-aware
endpoint, but exposing the strict survivor-merit comparisons directly.
-/
abbrev theorem3_two_school_academic_merit_feasible_surface_raw_survivor_merits :=
  @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval_of_raw_survivor_merits

/--
Proposition 6: dropping tests with strategic students, diversity objective.

Paper statement: when both schools initially use `P_full` and schools optimize
for diversity only, school `J1` drops the test iff the displayed Proposition 6
source-parameter inequality holds.
-/
abbrev proposition6_strategic_diversity :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_j1_drops_test_iff_standardGaussian_source_parameter_diversity_rows

/--
Proposition 6 support: the corresponding `(P_sub,P_full)` diversity-only
equilibrium iff under the same-fallback table, reducing exactly to school
`J1`'s weak displayed diversity comparison.
-/
abbrev proposition6_subFull_equilibrium_iff :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_diversity_surface_subFull_equilibrium_iff_standardGaussian_source_parameter_diversity_rows_of_J2_same_fallback

/--
Proposition 6 support: the corresponding `(P_sub,P_full)` diversity-only
equilibrium iff when only school `J2`'s ordinary fallback sub/full entry
matches its sub/sub entry.
-/
abbrev proposition6_subFull_equilibrium_iff_fallback_eq :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_diversity_surface_subFull_equilibrium_iff_standardGaussian_source_parameter_diversity_rows_of_J2_fallback_eq

/--
Proposition 6 support: strict displayed inequality implies the corresponding
`(P_sub,P_full)` diversity-only equilibrium when school `J2`'s ordinary
fallback sub/full diversity row is the same as its sub/sub row.
-/
abbrev proposition6_subFull_equilibrium_from_strict_inequality_same_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_standardGaussian_source_parameter_diversity_rows_inequality_implies_subFull_equilibrium_of_J2_same_fallback

/--
Proposition 6 support: strict displayed inequality implies the corresponding
`(P_sub,P_full)` diversity-only equilibrium when only school `J2`'s ordinary
fallback sub/full entry matches its sub/sub entry.
-/
abbrev proposition6_subFull_equilibrium_from_strict_inequality_fallback_eq :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_standardGaussian_source_parameter_diversity_rows_inequality_implies_subFull_equilibrium_of_J2_fallback_eq

/--
Proposition 6 bundled support: on the generated standard-Gaussian diversity
table, school `J1` drops the test iff the strict displayed inequality holds,
and `(P_sub,P_full)` is an equilibrium iff the weak displayed inequality
holds, assuming only school `J2`'s fallback row matches its sub/sub row.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_fallback_eq :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_drop_iff_and_subFull_equilibrium_of_J2_fallback_eq

/--
Proposition 6 bundled support for the common same-fallback table shape: the
drop-test iff and `(P_sub,P_full)` equilibrium iff both reduce to the displayed
strict/weak source-parameter comparisons, with school `J2`'s fallback equality
discharged by construction.  This is the preferred generated-row surface: the
school-`J1` full/full row and the sub/full row are generated from the displayed
source parameters rather than supplied as source-row identities.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_same_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_generated_rows_drop_iff_and_subFull_equilibrium_same_fallback

/--
Proposition 6 preferred generated-row bundle specialized to the paper's
concrete schools `J1` and `J2`; the distinct-school premise is discharged
internally.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_same_fallback_paper_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_generated_rows_drop_iff_and_subFull_equilibrium_same_fallback_paper_schools

/--
Proposition 6 preferred generated-row bundle specialized to the paper's
concrete groups and schools.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_same_fallback_paper_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_generated_rows_drop_iff_and_subFull_equilibrium_same_fallback_paper_groups_schools

/--
Proposition 6 bundled support with an explicit generated-row name.  This is an
audit alias for `proposition6_drop_iff_and_subFull_equilibrium_same_fallback`.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_generated_rows_same_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_generated_rows_drop_iff_and_subFull_equilibrium_same_fallback

/--
Proposition 6 direct consequence: the strict displayed inequality gives both
school `J1`'s drop-test decision and the `(P_sub,P_full)` diversity-only
equilibrium on the preferred generated standard-Gaussian table with the paper's
concrete groups and schools, in the common same-fallback shape.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_generated_rows_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback_paper_groups_schools

/--
Proposition 6 audit consequence: same generated-row strict-inequality result,
but with school `J2`'s fallback equality exposed explicitly.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_fallback_eq :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_strict_inequality_implies_drop_and_subFull_equilibrium_of_J2_fallback_eq

/--
Proposition 6 direct consequence for the common same-fallback table shape.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_generated_rows_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback

/--
Proposition 6 preferred generated-row strict-inequality consequence
specialized to the paper's concrete schools `J1` and `J2`; the
distinct-school premise is discharged internally.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback_paper_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_generated_rows_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback_paper_schools

/--
Proposition 6 preferred generated-row strict-inequality consequence
specialized to the paper's concrete groups and schools.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback_paper_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_generated_rows_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback_paper_groups_schools

/--
Proposition 6 direct generated-row consequence with an explicit generated-row
name.  This is an audit alias for
`proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback`.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_generated_rows_same_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_generated_rows_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback

/--
Proposition 6 exact bundle on an actual source-game diversity table.

The two school-`J1` source-formula row identifications give the drop-test iff
and the `(P_sub,P_full)` equilibrium iff; the latter keeps school `J2`'s weak
no-deviation condition visible as the ordinary row inequality.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_source_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_iff

/--
Proposition 6 exact bundle on an actual source-game diversity table,
specialized to the paper's concrete groups and schools.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_source_rows_paper_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_iff_paper_groups_schools

/--
Proposition 6 exact bundle on an actual source-game diversity table in the
common same-fallback row shape.

If school `J2`'s `(P_sub,P_full)` diversity row equals its `(P_sub,P_sub)`
row, the exact source-row bundle reduces to the two school-`J1`
source-formula row identifications.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_source_rows_same_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_same_fallback

/--
Proposition 6 exact same-fallback source-row bundle specialized to the paper's
concrete groups and schools.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_source_rows_same_fallback_paper_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_same_fallback_paper_groups_schools

/--
Proposition 6 exact bundle on an actual source-game diversity table whose
`(P_sub,P_full)` row is the generated source-parameter row.

The generated row supplies school `J1`'s sub/full source formula and school
`J2`'s same-fallback condition by construction, leaving only the school-`J1`
full/full source-formula row identity visible.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback

/--
Proposition 6 exact generated-sub/full source-row bundle specialized to the
paper's concrete schools `J1` and `J2`.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback_paper_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback_paper_schools

/--
Proposition 6 exact generated-sub/full source-row bundle specialized to the
paper's concrete groups and schools.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback_paper_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback_paper_groups_schools

/--
Proposition 6 exact bundle on an actual source-game diversity table whose
`(P_sub,P_full)` and `(P_full,P_full)` rows are both generated from the
displayed source-parameter formulas.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_source_rows_generated_rows_same_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_generated_rows_same_fallback

/--
Proposition 6 exact generated-row source bundle specialized to the paper's
concrete schools `J1` and `J2`.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_source_rows_generated_rows_same_fallback_paper_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_generated_rows_same_fallback_paper_schools

/--
Proposition 6 exact generated-row source bundle specialized to the paper's
concrete groups and schools.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_source_rows_generated_rows_same_fallback_paper_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_generated_rows_same_fallback_paper_groups_schools

/--
Proposition 6 direct consequence on an actual source-game diversity table
whose `(P_sub,P_full)` row is the generated source-parameter row.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_generated_subFull_same_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium_generated_subFull_same_fallback

/--
Proposition 6 direct generated-sub/full source-row consequence specialized to
the paper's concrete schools `J1` and `J2`.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_generated_subFull_same_fallback_paper_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium_generated_subFull_same_fallback_paper_schools

/--
Proposition 6 direct generated-sub/full source-row consequence specialized to
the paper's concrete groups and schools.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_generated_subFull_same_fallback_paper_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium_generated_subFull_same_fallback_paper_groups_schools

/--
Proposition 6 direct consequence on an actual source-game diversity table
whose `(P_sub,P_full)` and `(P_full,P_full)` rows are both generated from the
displayed source-parameter formulas.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_generated_rows_same_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium_generated_rows_same_fallback

/--
Proposition 6 direct generated-row source consequence specialized to the
paper's concrete schools `J1` and `J2`.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_generated_rows_same_fallback_paper_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium_generated_rows_same_fallback_paper_schools

/--
Proposition 6 direct generated-row source consequence specialized to the
paper's concrete groups and schools.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_generated_rows_same_fallback_paper_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium_generated_rows_same_fallback_paper_groups_schools

/--
Proposition 6 direct consequence on an actual source-game diversity table.

The strict displayed source-parameter inequality gives both school `J1`'s
drop-test decision and the `(P_sub,P_full)` diversity-only equilibrium, with
school `J2`'s weak no-deviation condition and the two school-`J1` diversity-row
identifications exposed directly.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium

/--
Proposition 6 direct consequence on an actual source-game diversity table,
specialized to the paper's concrete groups and schools.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_paper_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium_paper_groups_schools

/--
Proposition 6 direct consequence on an actual source-game diversity table in
the common same-fallback row shape.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_same_fallback :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback

/--
Proposition 6 direct same-fallback source-row consequence specialized to the
paper's concrete groups and schools.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_same_fallback_paper_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback_paper_groups_schools

/--
Proposition 6 concrete policy-state source-formula drop-test iff.

This is the direct source-parameter formula surface for a policy-state
diversity table, without routing through the generated-row table.
-/
abbrev proposition6_policy_state_drop_iff_source_parameter_formulas :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_j1_strict_diversity_best_response_iff_source_parameter_formulas

/-- Proposition 6 displayed full/full diversity value after source-parameter substitution. -/
noncomputable abbrev proposition6_source_parameter_full_diversity_value :=
  @GLM20DroppingStandardizedTesting.paperProposition6SourceParameterFullDiversityValue

/-- Proposition 6 displayed sub/full diversity value after source-parameter substitution. -/
noncomputable abbrev proposition6_source_parameter_sub_diversity_value :=
  @GLM20DroppingStandardizedTesting.paperProposition6SourceParameterSubDiversityValue

/-- Proposition 6 generated full/full diversity row with school `J1` set to the displayed source value. -/
noncomputable abbrev proposition6_source_parameter_fullFull_diversity_row :=
  @GLM20DroppingStandardizedTesting.paperProposition6SourceParameterFullFullDiversityRow

/-- Proposition 6 generated sub/full diversity row with school `J1` set to the displayed source value. -/
noncomputable abbrev proposition6_source_parameter_subFull_diversity_row :=
  @GLM20DroppingStandardizedTesting.paperProposition6SourceParameterSubFullDiversityRow

/--
Proposition 6 support: the generated sub/full source-parameter row has the
displayed test-free diversity value at school `J1`.
-/
abbrev proposition6_source_parameter_subFull_row_eq_source_value_at_j1 :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_source_parameter_subFullDiversityRow_eq_source_value_at_j1

/--
Proposition 6 support: the generated full/full source-parameter row has the
displayed full-policy diversity value at school `J1`.
-/
abbrev proposition6_source_parameter_fullFull_row_eq_source_value_at_j1 :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_source_parameter_fullFullDiversityRow_eq_source_value_at_j1

/--
Proposition 6 support: if an existing sub/full diversity row already has the
displayed source-parameter value at school `J1`, then generating the
source-parameter row leaves the whole row unchanged.
-/
abbrev proposition6_source_parameter_subFull_row_eq_of_j1_formula :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_source_parameter_subFullDiversityRow_eq_of_j1_formula

/--
Proposition 6 support: if an existing full/full diversity row already has the
displayed source-parameter value at school `J1`, then generating the
source-parameter row leaves the whole row unchanged.
-/
abbrev proposition6_source_parameter_fullFull_row_eq_of_j1_formula :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_source_parameter_fullFullDiversityRow_eq_of_j1_formula

/--
Proposition 6 support: the generated sub/full diversity row equals its
fallback row at every school other than `J1`.
-/
abbrev proposition6_source_parameter_subFull_row_eq_fallback_of_ne :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_source_parameter_subFullDiversityRow_eq_fallback_of_ne

/--
Proposition 6 support: the generated full/full diversity row equals its
fallback row at every school other than `J1`.
-/
abbrev proposition6_source_parameter_fullFull_row_eq_fallback_of_ne :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_source_parameter_fullFullDiversityRow_eq_fallback_of_ne

/--
Proposition 6 generated-row source surface: the full/full and sub/full rows are
constructed from the displayed source-parameter formulas, so no separate
`hfull`/`hsub` row-identification premises are visible.
-/
abbrev proposition6_policy_state_drop_iff_source_parameter_diversity_rows :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_j1_strict_diversity_best_response_iff_source_parameter_diversity_rows

/--
Proposition 6 concrete policy-state source-formula `(P_sub,P_full)`
equilibrium iff.
-/
abbrev proposition6_policy_state_subFull_equilibrium_iff_source_parameter_formulas :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_diversity_surface_subFull_equilibrium_iff_source_parameter_formulas

/--
Proposition 6 concrete policy-state standard-Gaussian source-formula drop-test
iff, specialized to the paper's named groups and schools.
-/
abbrev proposition6_policy_state_standardGaussian_drop_iff_source_parameter_formulas :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_j1_strict_diversity_best_response_iff_standardGaussian_source_parameter_formulas_paper_groups_schools

/--
Proposition 6 audit support: same standard-Gaussian source-formula drop-test
iff, but keeping group and school parameters abstract.
-/
abbrev proposition6_policy_state_standardGaussian_drop_iff_source_parameter_formulas_generic_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_j1_strict_diversity_best_response_iff_standardGaussian_source_parameter_formulas

/--
Proposition 6 concrete policy-state standard-Gaussian source-formula
`(P_sub,P_full)` equilibrium iff, specialized to the paper's named groups and
schools.
-/
abbrev proposition6_policy_state_standardGaussian_subFull_equilibrium_iff_source_parameter_formulas :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_diversity_surface_subFull_equilibrium_iff_standardGaussian_source_parameter_formulas_paper_groups_schools

/--
Proposition 6 audit support: same standard-Gaussian source-formula
`(P_sub,P_full)` equilibrium iff, but keeping group and school parameters
abstract.
-/
abbrev proposition6_policy_state_standardGaussian_subFull_equilibrium_iff_source_parameter_formulas_generic_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_diversity_surface_subFull_equilibrium_iff_standardGaussian_source_parameter_formulas

/--
Proposition 6 concrete policy-state consequence: strict standard-Gaussian
source-parameter inequality plus school-`J2` weak no-deviation implies the
`(P_sub,P_full)` diversity-only equilibrium, specialized to the paper's named
groups and schools.
-/
abbrev proposition6_policy_state_standardGaussian_strict_inequality_implies_subFull_equilibrium :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_standardGaussian_source_parameter_formula_inequality_implies_diversity_surface_subFull_equilibrium_paper_groups_schools

/--
Proposition 6 audit support: same strict-inequality consequence, but keeping
group and school parameters abstract.
-/
abbrev proposition6_policy_state_standardGaussian_strict_inequality_implies_subFull_equilibrium_generic_groups_schools :=
  @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_standardGaussian_source_parameter_formula_inequality_implies_diversity_surface_subFull_equilibrium

/--
Legacy certificate bundle for Propositions 7--9.

The direct paper-facing Proposition 7, 8, and 9 wrappers above are the preferred
audit surface; this older certificate endpoint remains for compatibility with
the exhaustive proof ledger.
-/
abbrev propositions7_9_legacy_certificate_bundle :=
  @GLM20DroppingStandardizedTesting.paper_interface_propositions7_9_generalization_affirmative_action

end PaperInterface
end GLM20DroppingStandardizedTesting
