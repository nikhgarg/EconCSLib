import GLM20DroppingStandardizedTesting.ProofInterface

/-!
# Paper Interface: GLM20 Dropping Standardized Testing

This is the compact human-review surface for *Dropping Standardized Testing for
Admissions Trades Off Information and Access*. It exposes the paper-facing
notation, named statements, and a small number of section-level bridge endpoints.
Detailed route variants and row-identification helpers remain in
`ProofInterface.lean`.
-/

namespace GLM20DroppingStandardizedTesting
namespace PaperInterface
/-- Policy notation `P_full`, the test-using admissions policy. -/
abbrev definition_policy_full := GLM20DroppingStandardizedTesting.paperPFull

/-- Policy notation `P_sub`, the test-dropping admissions policy. -/
abbrev definition_policy_sub := GLM20DroppingStandardizedTesting.paperPSub

/-- School notation `J_1`, the first school in Theorem 3. -/
abbrev definition_school_J1 := GLM20DroppingStandardizedTesting.paper_interface_theorem3_schoolJ1

/-- School notation `J_2`, the second school in Theorem 3. -/
abbrev definition_school_J2 := GLM20DroppingStandardizedTesting.paper_interface_theorem3_schoolJ2

/-- Theorem 3 population-share row: group A has share `1 - pi`, group B has share `pi`. -/
abbrev definition_theorem3_populationShare := GLM20DroppingStandardizedTesting.paper_interface_theorem3_populationShare

/-- Appendix F Definition 1: finite-kernel Blackwell sufficiency. -/
abbrev definition_blackwell_sufficient := @GLM20DroppingStandardizedTesting.paperBlackwellSufficient

/-- Lemma 1: estimated skill source surface. -/
abbrev lemma1_estimated_skill := @GLM20DroppingStandardizedTesting.paper_interface_lemma1_estimated_skill_source_surface

/-- Proposition 1: fixed-policy group and individual fairness metrics. -/
abbrev proposition1_fixed_policy_metrics := @GLM20DroppingStandardizedTesting.paper_interface_proposition1_fixed_policy_static_core_source_surface_standardGaussian

/-- Lemma 2: conditional-posterior law source surface. -/
abbrev lemma2_individual_fairness_gap := @GLM20DroppingStandardizedTesting.paper_interface_lemma2_conditional_posterior_laws_source_surface_standardGaussian

/-- Theorem 1: dropping tests with admissions barriers. -/
abbrev theorem1_dropping_tests_with_barriers := @GLM20DroppingStandardizedTesting.paper_interface_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_source_model

/-- Theorem 2: dropping tests without admissions barriers. -/
abbrev theorem2_dropping_tests_without_barriers := @GLM20DroppingStandardizedTesting.paper_interface_theorem2_dropping_tests_without_barriers_standardGaussian_source_model

/--
Theorem 2 audit theorem: the main-text high-skill individual-fairness-gap
direction and the appendix high-skill direction cannot both hold on the same
source surface.
-/
abbrev theorem2_high_skill_direction_inconsistency := @GLM20DroppingStandardizedTesting.paper_interface_theorem2_eventual_high_skill_gap_directions_inconsistent

/-- Strategic two-school equilibrium condition, `P_sub`/`P_full` case. -/
abbrev strategic_equilibrium_subFull := @GLM20DroppingStandardizedTesting.paper_interface_two_school_binary_policy_equilibrium_subFull_iff

/-- Strategic two-school equilibrium condition, `P_full`/`P_sub` case. -/
abbrev strategic_equilibrium_fullSub := @GLM20DroppingStandardizedTesting.paper_interface_two_school_binary_policy_equilibrium_fullSub_iff

/-- Strategic two-school equilibrium condition, `P_full`/`P_full` case. -/
abbrev strategic_equilibrium_fullFull := @GLM20DroppingStandardizedTesting.paper_interface_two_school_binary_policy_equilibrium_fullFull_iff

/--
Section 5 strategic equilibrium with student feasibility and best response
required almost everywhere under the realized continuous student law.
-/
abbrev strategic_equilibrium_ae := @GLM20DroppingStandardizedTesting.paperStrategicEquilibriumAE

/-- Strategic two-school equilibrium conditions for all three Section 5 policy pairs. -/
abbrev strategic_equilibrium_three_cases := @GLM20DroppingStandardizedTesting.paper_interface_two_school_binary_policy_equilibrium_three_cases

/-- Feasibility-aware strategic equilibrium conditions for all three Section 5 policy pairs. -/
abbrev strategic_feasible_equilibrium_three_cases := @GLM20DroppingStandardizedTesting.paper_interface_two_school_binary_policy_feasible_equilibrium_three_cases

/-- Lemma 3: unique equilibrium under `P_full`. -/
abbrev lemma3_unique_full_policy_equilibrium := @GLM20DroppingStandardizedTesting.paper_interface_lemma3_unique_equilibrium_full_policy

/--
Lemma 3 / Proposition 2 source endpoint: unique full-policy threshold
equilibrium for the paper's two named groups, with the corrected
conditional-source bivariate applicant-mass rows substituted.
-/
abbrev lemma3_full_policy_threshold_equilibrium_conditional_source_paper_groups := @GLM20DroppingStandardizedTesting.paper_interface_lemma3_full_policy_threshold_equilibrium_existsUnique_of_standardBivariate_conditional_source_paper_groups

/--
Proposition 2: unique two-school equilibrium, using the paper-readable
group cost-bounds endpoint.
-/
abbrev proposition2_two_school_equilibrium := @GLM20DroppingStandardizedTesting.paper_interface_proposition2_standardGaussian_mixture_group_threshold_equilibrium_existsUnique_precision_of_cost_bounds

/--
Proposition 2 support: the two-school application-region strategy is unique
almost everywhere when the two cutoff boundaries have zero mass, using
paper-readable cost bounds.
-/
abbrev proposition2_application_strategy_ae_unique := @GLM20DroppingStandardizedTesting.paper_interface_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_cost_bounds

/--
Proposition 2 / Lemma 3 applicant-pool support: the Eq. (35) strategic
applicant mass is the finite sum of corrected admitted-mass source rows after
substituting each group's Eq. (7) application cutoff.
-/
abbrev proposition2_strategic_applicant_pool_masses_to_corrected_source_rows := @GLM20DroppingStandardizedTesting.paper_interface_proposition2_strategic_applicant_pool_masses_to_corrected_source_rows

/--
Proposition 2(iii): diversity criterion when `q^*_{2,sub}` is above the high
cutoff, using the corrected conditional-source eligible-mass surface from
Appendix D.6.
-/
abbrev proposition2_diversity_above_high_cutoff := @GLM20DroppingStandardizedTesting.paper_interface_proposition2_part_iii_diversity_criterion_above_high_cutoff_corrected_source_rows

/--
Proposition 2(iii): diversity criterion in the between-cutoffs case, with the
corrected conditional-source eligible-mass surface from Appendix D.6.
-/
abbrev proposition2_diversity_between_cutoffs := @GLM20DroppingStandardizedTesting.paper_interface_proposition2_part_iii_diversity_criterion_between_cutoffs_corrected_source_rows

/--
Proposition 2(iv): when `q^*_{2,sub} > q_h^g`, school `J1` has lower
academic merit for group `g` than school `J2` iff the displayed
`lambda < kappa` comparison holds, with both academic-merit rows and the
source cutoff specialized internally.
-/
abbrev proposition2_academic_merit_lambda_kappa := @GLM20DroppingStandardizedTesting.paper_interface_proposition2_part_iv_lower_academic_merit_iff_lambda_lt_kappaBoundaryDensity_sourceTau_normalDensity_source_rows

/--
Proposition 3: full-policy diversity and academic-merit source formulas.

The displayed capacity, group admitted-share rows, and `lambda` academic-merit
rows are specialized internally; the resulting diversity condition is the
Equation (37) ratio form.
-/
abbrev proposition3_full_policy_formulas := @GLM20DroppingStandardizedTesting.paper_interface_proposition3_full_policy_diversity_ratio_and_academic_merit_formulas_source_rows

/--
Proposition 3 audit theorem: the upper-tail Owen first-moment expression
equals the source-displayed `lambda` formula plus an explicit boundary term.
-/
abbrev proposition3_lambda_boundary_term := @GLM20DroppingStandardizedTesting.paper_interface_proposition3_lambda_owenFirstMomentFormula_eq_lambdaFormula_add_boundaryTerm

/--
Proposition 3 audit theorem: with nonzero slope, nonzero scale, and nonzero
normalization, the verified first-moment expression is not literally the
source-displayed `lambda` formula.
-/
abbrev proposition3_lambda_displayed_formula_discrepancy := @GLM20DroppingStandardizedTesting.paper_interface_proposition3_lambda_ne_owenFirstMomentFormula_of_nonzero_slope

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
abbrev proposition5_subFull_objective_bridge := @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_survivor_rows_paper_groups_schools_with_population_share

/--
Proposition 5(ii) support: same fixed-law posterior cost-row objective bridge,
but the endpoint merit-crossing assumptions are generated internally from
fixed posterior laws plus endpoint threshold-order comparisons, and the
full/sub threshold side and full/full capacity/fill side are bundled as source
rows.
-/
abbrev proposition5_fullSub_posterior_source_free_cost_row_objective_bridge_threshold_order := @GLM20DroppingStandardizedTesting.paper_interface_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_affine_threshold_rows_interval_capacity_cutoff_rows_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows

/--
Proposition 5: typed strategic academic-merit source-condition predicate.

This is the non-certificate paper-facing surface for the Proposition 5 proof
seams: the sub/full and full/sub weighted-objective comparisons are equivalent
to the displayed source conditions, and the full/full pair satisfies the source
boundary condition.
-/
abbrev proposition5_strategic_academic_merit_source_conditions := @GLM20DroppingStandardizedTesting.paperProposition5StrategicAcademicMeritSourceConditions

/--
Proposition 5: existential-threshold version of the typed strategic
academic-merit source-condition predicate.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists := @GLM20DroppingStandardizedTesting.paperProposition5StrategicAcademicMeritSourceConditionsExists

/--
Proposition 5: existential source-condition package from constructed
sub/full and full/sub objective bridges, using the abstract positive-cost
full/full source condition.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_objective_bridges_and_positive_costs := @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_objective_bridges_and_positive_costs

/--
Proposition 5: rich-package version of the policy-state sub/full
mass-feasibility reverse bridge, with the extra witness predicate inferred
from the supplied Theorem 3 package.
-/
abbrev proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_rich_theorem3_source_conditions_exists_inferred_extra := @GLM20DroppingStandardizedTesting.paper_interface_proposition5_strategic_academic_merit_source_conditions_exists_of_policyStateSubFullMassFeasibleSurface_rich_theorem3_source_conditions_exists_inferred_extra

/--
Theorem 3 support: bundled public source rows plus the population-share domain
for the current compact academic-merit route.
-/
abbrev theorem3_academic_merit_strict_survivor_public_rows_with_population_share := @GLM20DroppingStandardizedTesting.paper_interface_theorem3_academic_merit_strict_survivor_public_rows_with_population_share

/--
Theorem 3 support: same weighted binary-objective adapter as
`theorem3_weighted_binary_objectives_from_standardGaussian_prop5_bridges`, but
the Proposition 5(ii) endpoint crossings are generated from fixed-law
threshold-order comparisons.
-/
abbrev theorem3_weighted_binary_objectives_from_standardGaussian_prop5_threshold_order_bridge := @GLM20DroppingStandardizedTesting.paper_interface_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_standardGaussian_subFull_keep_test_threshold_order_and_fixed_law_fullSub_cost_rows

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
abbrev theorem3_two_school_academic_merit := @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 source route: same compact endpoint as
`theorem3_two_school_academic_merit`, but constructing the public-row package
internally from a generated source-family school-`J2` keep-test pair and raw
full/sub prior-precision rows.
-/
abbrev
    theorem3_two_school_academic_merit_source_family_keep_test_fullSub_prior_precision_rows := @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_j2_keep_test_pair_and_fullSub_prior_precision_rows_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Theorem 3 feasibility-aware support: same strict-survivor route as
`theorem3_two_school_academic_merit_strict_survivor_generated_rows`, but
constructing the full/sub generated-row package from primitive prior-mean,
prior-variance, and precision rows.
-/
abbrev theorem3_two_school_academic_merit_strict_survivor_prior_precision_rows := @GLM20DroppingStandardizedTesting.paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_extra_keep_and_fullSub_prior_precision_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds

/--
Proposition 6: dropping tests with strategic students, diversity objective.

Paper statement: when both schools initially use `P_full` and schools optimize
for diversity only, school `J1` drops the test iff the displayed Proposition 6
source-parameter inequality holds.
-/
abbrev proposition6_strategic_diversity := @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_j1_drops_test_iff_standardGaussian_source_parameter_diversity_rows

/--
Proposition 6 exact bundle on an actual source-game diversity table.

The two school-`J1` source-formula row identifications give the drop-test iff
and the `(P_sub,P_full)` equilibrium iff; the latter keeps school `J2`'s weak
no-deviation condition visible as the ordinary row inequality.
-/
abbrev proposition6_drop_iff_and_subFull_equilibrium_source_rows := @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_iff

/--
Proposition 6 direct consequence on an actual source-game diversity table.

The strict displayed source-parameter inequality gives both school `J1`'s
drop-test decision and the `(P_sub,P_full)` diversity-only equilibrium, with
school `J2`'s weak no-deviation condition and the two school-`J1` diversity-row
identifications exposed directly.
-/
abbrev proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows := @GLM20DroppingStandardizedTesting.paper_interface_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium

/--
Proposition 6 concrete policy-state standard-Gaussian source-formula drop-test
iff, specialized to the paper's named groups and schools.
-/
abbrev proposition6_policy_state_standardGaussian_drop_iff_source_parameter_formulas := @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_j1_strict_diversity_best_response_iff_standardGaussian_source_parameter_formulas_paper_groups_schools

/--
Proposition 6 concrete policy-state consequence: strict standard-Gaussian
source-parameter inequality plus school-`J2` weak no-deviation implies the
`(P_sub,P_full)` diversity-only equilibrium, specialized to the paper's named
groups and schools.
-/
abbrev proposition6_policy_state_standardGaussian_strict_inequality_implies_subFull_equilibrium := @GLM20DroppingStandardizedTesting.paper_interface_proposition6_policyState_standardGaussian_source_parameter_formula_inequality_implies_diversity_surface_subFull_equilibrium_paper_groups_schools

/--
Proposition 7(i): general-distribution diversity characterization.

Paper statement: with a single posterior-score crossing `q_+`, group `B` is
under-represented iff the school capacity is below the aggregate tail mass
above `q_+`.
-/
abbrev proposition7_diversity_underrepresentation := @GLM20DroppingStandardizedTesting.paper_interface_proposition7_diversity_underrepresented_iff_capacity_lt_crossing_tail

/--
Proposition 7(ii): general-distribution academic-merit ordering.

Paper statement: under the same second-order stochastic dominance /
mean-preserving-spread condition, admitted group-`B` academic merit is no
greater than admitted group-`A` academic merit; the strict wrapper exposes the
source's strict linear-utility comparison.
-/
abbrev proposition7_academic_merit_order := @GLM20DroppingStandardizedTesting.paper_interface_proposition7_academic_merit_groupB_le_groupA_of_increasingConcaveOrder

/--
Proposition 7(iii): general-distribution individual-fairness threshold.

Paper statement: there is a skill threshold above which the individual fairness
gap is positive.
-/
abbrev proposition7_individual_fairness_threshold := @GLM20DroppingStandardizedTesting.paper_interface_proposition7_exists_individual_fairness_threshold

/--
Proposition 8: fixed-policy affirmative action.

Paper statement: affirmative action improves the individual-fairness gap,
gives the displayed positive-gap cutoff, keeps group `B` below group `A` in
admitted academic merit, raises group `A` admitted merit, and lowers group `B`
admitted merit.
-/
abbrev proposition8_affirmative_action_fixed_policy := @GLM20DroppingStandardizedTesting.paper_interface_proposition8_affirmative_action_fixed_policy_standardGaussian

/--
Proposition 9: dropping tests under affirmative action.

Paper statement: dropping the test under affirmative action improves group
`g`'s admitted academic merit iff the access level satisfies
`gamma_g <= hat_gamma_g`.
-/
abbrev proposition9_affirmative_action_drop_threshold := @GLM20DroppingStandardizedTesting.paper_interface_proposition9_dropping_tests_affirmative_action_iff_gamma_le_hatGammaSource

/--
Proposition 9 monotonicity clause: fixing all other parameters, increasing the
test variance weakly increases the displayed access threshold `hat_gamma_g`.
-/
abbrev proposition9_affirmative_action_threshold_monotonicity := @GLM20DroppingStandardizedTesting.paper_interface_proposition9_hatGammaSource_mono_of_test_variance_increases

end PaperInterface
end GLM20DroppingStandardizedTesting
