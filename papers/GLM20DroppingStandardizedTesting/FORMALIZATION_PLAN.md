# GLM20 Formalization Plan

Last updated: 2026-05-24

Joint campaign plan:
`../../docs/STANDARDIZED_TESTING_JOINT_FORMALIZATION_PLAN.md`.

## 2026-05-24 Active Stop And Next Step

Current stopping point: the generated source-family exactly-one-objective row
package compiles.  The newest target is
`GLM20Proposition5ExactlyOneObjectiveSourceFamilyRows`, exposed publicly as
`PaperInterface.proposition5_exactly_one_weighted_objective_bridge_source_family_policy_state_row_package`.
This is the precise Bayesian-game obligation for the twelve `honlyA`/`honlyB`
posterior row identifications.  Do not reopen the table algebra or add another
flat theorem over the same twelve premises; prove the row package from the
concrete Gaussian/Bayesian-game model and feed it into the packaged bridge.

Validated commands on 2026-05-24:

```bash
lake build GLM20DroppingStandardizedTesting.Proposition5SourceFamilyRows
lake build GLM20DroppingStandardizedTesting.ProofInterface
lake build GLM20DroppingStandardizedTesting.PaperInterface
```

For restart details, see `START_HERE_NEXT_AGENT.md` and
`HANDOFF_2026-05-24.md`.

## Plan To Finish The Proof

The fastest faithful route is to finish the concrete Bayesian-game
identification layer and feed it into the wrappers that already compile. Do
not add another certificate surface unless one of these targets is
mathematically false.

1. Prove `GLM20Proposition5ExactlyOneObjectiveSourceFamilyRows` from the
   concrete Gaussian two-school game. Treat student application and test-taking
   behavior as a.e. under the relevant projected-skill laws. The row package
   should identify the twelve branch-conditioned `honlyA`/`honlyB`
   posterior/admitted-merit rows: unchanged rows for the non-expanding group,
   test-based rows for the keep-test group, and test-free rows for the
   drop-test group.
2. Feed that package directly to
   `PaperInterface.proposition5_exactly_one_weighted_objective_bridge_source_family_policy_state_row_package`.
   This closes the generated-table weighted-objective algebra without passing
   twelve scalar row facts through every downstream theorem.
3. Use the existing Theorem 3 keep-test/survivor route rather than restating
   Theorem 3. The main entry points are
   `PaperInterface.theorem3_source_family_j2_keep_test_pair_of_survivor_rows`,
   `PaperInterface.theorem3_public_rows_with_population_share_of_source_family_j2_keep_test_pair`,
   and
   `PaperInterface.theorem3_two_school_academic_merit_source_family_keep_test_fullSub_prior_precision_rows`.
   The remaining mathematical obligations here are condition-(11) survivor
   mass lower bounds and condition-(12) strict weighted survivor-merit
   comparisons.
4. Recover Proposition 5 from the rich Theorem 3 package on the concrete
   policy-state sub/full mass-feasibility surface with
   `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_rich_theorem3_source_conditions_exists_of_source_family_j2_keep_test_pair`.
   If the rich theorem package is already in hand, this should only need the
   surface equality and the source-family school-`J2` keep-test pair.
5. Close the remaining Section 5 named results by feeding already-proved
   source rows into their public adapters:
   `PaperInterface.proposition2_application_strategy_ae_unique_binary_choice`
   for a.e. application behavior,
   `PaperInterface.proposition2_strategic_applicant_pool_masses_to_corrected_source_rows`
   for applicant-pool mass rows,
   `PaperInterface.proposition3_full_policy_formulas` for the displayed
   full-policy formula layer, and the generated-row Proposition 6 same-fallback
   wrappers for diversity. Preserve the existing Proposition 3 lambda-scaling
   caveat unless the source formula discrepancy is mathematically resolved.
6. Finalize only after the paper-facing Section 5 chain is closed: run the
   full paper build, rebuild the dependency DAG, then refresh the
   review-dashboard/post-paper audit. Update `README.md`,
   `FINAL_VALIDATION_REPORT.md`, and `docs/ECONCSLEAN_CURRENT_STATUS.md` with
   closed declaration names and keep the Theorem 1, Theorem 2, and Proposition
   3 caveats visible.

## 2026-05-23 Execution Plan

This is the current working plan for fully formalizing GLM20. The proof should
advance in this order, with a targeted
`lake build GLM20DroppingStandardizedTesting.PaperInterface` after each closed
theorem seam.

1. The corrected Theorem 2 main-text source-model bundle is closed. The
   paper-facing wrapper now uses `subB < subA` and concludes the high-skill
   direction `I(q; P_sub) > I(q; P_full)`; the old `_appendix_direction` name
   is only a compatibility alias. Continue from Section 5.
2. Continue the Section 5 concrete strategic Gaussian-game wiring. The closed
   wrappers for Proposition 2, Proposition 5, Theorem 3, and Proposition 6
   should be treated as target adapters; the next work should prove concrete
   Gaussian applicant-pool mass, merit-crossing, objective-value, and
   no-deviation facts that feed those adapters, not restate the strategic game.
   For compact wrapper-only work, use `PaperSurfaceWrappers.lean` instead of
   adding more proof bodies to `MainTheorems.lean`; validate that leaf module
   before rebuilding `PaperInterface`.
   The current `PaperInterface.theorem3_two_school_academic_merit` target is
   the standard-Gaussian fixed-law posterior cost-row wrapper with
   equation-(50) sub-full regularity, threshold-order endpoint crossings,
   positive-slope affine based-threshold regularity, cutoff-order full/full
   fill, zero-fallback school-`J2` rows, and strict condition-(12) survivor
   merit rows on the generated source-family policy-state table.  The public
   alias bundles the visible row premises as
   `GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare`;
   condition-(11)'s survivor mass side is carried by feasibility/capacity rows,
   and `0 < pi < 1` is no longer a separate main-alias premise.  The separated
   population-share audit route is
   `PaperInterface.theorem3_two_school_academic_merit_strict_survivor_public_rows`.
   The older
   four-row survivor public wrapper remains available as
   `PaperInterface.theorem3_two_school_academic_merit_survivor_rows_public_rows`,
   and the strict-survivor full/sub generated-row route remains available
   through
   `PaperInterface.theorem3_two_school_academic_merit_strict_survivor_generated_rows`.
   The
   high-at-low-root proof artifact, cost-indexed full-sub formula rows, and
   named keep-test predicates are discharged inside the posterior cost-row plus
   keep-test conversion route.  The generated-table
   keep-test route is also available explicitly as
   `PaperInterface.theorem3_two_school_academic_merit_source_family_j2_keeps_test`,
   and the base-table keep-test route remains available as
   `PaperInterface.theorem3_two_school_academic_merit_base_table_j2_keeps_test`.
   The direct ordered-merit route remains available as
   `PaperInterface.theorem3_two_school_academic_merit_ordered_fullSub`, and
   the raw-survivor Gaussian route is
   `PaperInterface.theorem3_two_school_academic_merit_gaussian_raw_survivor_components`.
   The reusable Gaussian law lemmas
   `GaussianSignalFamily.posteriorMeanScaleLaw_eq_of_priorMean_eq_priorVar_eq_signalPrecisionSum_eq`
   and
   `GaussianOffsetSignalFamily.posteriorMeanScaleLaw_eq_of_priorMean_eq_priorVar_eq_signalPrecisionSum_eq`
   are now available in `EconCSLib.Foundations.Probability.Gaussian` for
   discharging fixed-law posterior assumptions from prior mean, prior variance,
   and total signal precision rows.
   The public GLM20 helpers
   `PaperInterface.theorem3_fullSub_low_based_law_of_prior_precision_rows` and
   `PaperInterface.theorem3_fullSub_high_based_law_of_prior_precision_rows`
   package those lemmas in the exact low/high full-sub source-family shape used
   by the compact Theorem 3 wrappers; the paired helper
   `PaperInterface.theorem3_fullSub_based_laws_of_prior_precision_rows`
   discharges both fixed-law equalities at once.  The source-row predicate
   `GLM20Theorem3FullSubFixedLawRows`, unpacked by
   `PaperInterface.theorem3_fullSub_fixed_law_rows_components`, is the compact
   way to carry those primitive rows through future wrappers.  The larger
   source package `GLM20Theorem3FullSubGeneratedRows`, exposed as
   `PaperInterface.theorem3_fullSub_generated_rows`, carries the full/sub
   extra-noise positivity rows, fixed-law rows, affine threshold rows, and
   cost bounds together for future Theorem 3 / Proposition 5(ii)
   instantiation work.  If the source model supplies the primitive rows
   separately, use
   `PaperInterface.theorem3_fullSub_generated_rows_of_prior_precision_rows`
   to build that package directly from prior mean, prior variance, total
   precision, affine threshold, and cost-bound rows.
   The generated keep-test signal assumptions can likewise be carried as
   `GLM20Theorem3KeepSignalRows`, unpacked by
   `PaperInterface.theorem3_keep_signal_rows_components`, on the intermediate
   extra-signal source-family routes.
   The compact Proposition 5(i) support alias now exposes the equation-(50),
   capacity-fill, fixed-pool/group-merit wrapper with school-`J2`'s survivor
   requirements bundled as `GLM20Theorem3J2SurvivorRows`, and
   Proposition 2's a.e. application-region uniqueness surface also has a
   reusable binary-choice variant,
   `PaperInterface.proposition2_application_strategy_ae_unique_binary_choice`,
   whose best-response premise is `NoProfitableBinaryChoiceDeviationAE`.
   Proposition 2 also has
   `PaperInterface.proposition2_strategic_applicant_pool_masses_to_corrected_source_rows`,
   which rewrites Lemma 3's Eq. (35) strategic applicant mass as the finite
   sum of corrected admitted-mass source rows after the Eq. (7) application
   cutoff substitution.
   Proposition 6 has a pointwise fallback-equality endpoint for discharging
   the `J2` no-deviation premise.
   The preferred Proposition 6 wrapper is now the generated-row same-fallback
   surface
   `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_same_fallback`,
   with explicit audit alias
   `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_generated_rows_same_fallback`.
   It bundles the strict drop-test iff with the weak sub/full equilibrium iff
   on the generated standard-Gaussian diversity table, generates the school
   `J1` full/full row and the sub/full row from displayed source parameters,
   and discharges school `J2`'s same-fallback no-deviation premise by
   construction.  The direct
   consequence alias
   `PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback`
   packages the strict displayed inequality into both conclusions.  The
   older fallback-equality aliases remain available for auditing when a
   pointwise school-`J2` fallback equality is supplied explicitly.  The stronger
   source-row bundle
   `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows`
   works on an actual four-row diversity table and gives both exact iff
   statements.  The source-row same-fallback aliases
   `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows_same_fallback`
   and
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_same_fallback`
remove school `J2`'s weak no-deviation premise when its sub/full row is
equal to its sub/sub row.  The generated-sub/full source-row aliases
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback`
and
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_generated_subFull_same_fallback`
additionally generate the sub/full row from the sub/sub fallback, so the
`J1` sub/full source-row identity and `J2` same-fallback premise are both
discharged internally; their `_paper_schools` variants also fix the schools to
`GLM20School` and discharge `J1 != J2` internally.  If the full/full row is
also the generated source-parameter row, use
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows_generated_rows_same_fallback`
or
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_generated_rows_same_fallback`;
these remove the remaining `J1` full/full row-identity premise, and their
`_paper_groups_schools` variants fix the paper's concrete group and school
names internally.  The source-row consequence alias
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows`
exposes only school `J2`'s weak no-deviation inequality, the two school-`J1`
source-formula row identifications, and the strict displayed
   source-parameter inequality.  The compact interface also exposes
   `PaperInterface.proposition6_source_parameter_full_diversity_value`,
   `PaperInterface.proposition6_source_parameter_sub_diversity_value`,
   `PaperInterface.proposition6_source_parameter_fullFull_diversity_row`,
   `PaperInterface.proposition6_source_parameter_subFull_diversity_row`,
   `PaperInterface.proposition6_source_parameter_fullFull_row_eq_source_value_at_j1`,
   `PaperInterface.proposition6_source_parameter_subFull_row_eq_source_value_at_j1`,
   `PaperInterface.proposition6_source_parameter_fullFull_row_eq_of_j1_formula`,
   and
   `PaperInterface.proposition6_source_parameter_subFull_row_eq_of_j1_formula`
   for auditing actual four-row source tables; use
   `PaperInterface.proposition6_source_parameter_fullFull_row_eq_fallback_of_ne`
   and
   `PaperInterface.proposition6_source_parameter_subFull_row_eq_fallback_of_ne`
   to turn `J1 ≠ J2` into generated-row fallback identities at school `J2`.
   The preferred Proposition 5(i) support alias
   `PaperInterface.proposition5_subFull_objective_bridge` now uses concrete
   Gaussian source-family fixed-pool data with school-`J2`'s survivor
   requirements bundled as `GLM20Theorem3J2SurvivorRows` and the
   standard-Gaussian hazard certificate specialized internally; use
   `PaperInterface.proposition5_subFull_objective_bridge_source_family_survivor_components`
   to inspect the four scalar source rows,
   `PaperInterface.proposition5_subFull_objective_bridge_j2_keeps_test`
   to view the named school-`J2` keep-test predicate surface, also with the
   standard-Gaussian API/certificate hidden,
   `PaperInterface.proposition5_subFull_objective_bridge_raw_survivor_conditions`
   to inspect the same raw survivor obligations on an abstract policy surface,
   `PaperInterface.proposition5_subFull_objective_bridge_tail_mean_fixed_pool`
   or `PaperInterface.proposition5_subFull_objective_bridge_raw_fixed_pool`
   when auditing the intermediate tail-mean or fixed-pool inequality layers.
   The new
   `PaperInterface.proposition5_school2_zero_fallback_objective_bridge`
   composes the zero-fallback source table with the bundled
   `GLM20Theorem3J2SurvivorRows` premise to recover the branch-conditioned
   school-`J2` objective iff, removing a layer of objective-value and
   zero-contribution bookkeeping from this route; its public alias likewise
   specializes the standard-Gaussian API/certificate internally.  The older
   separate-component surface is retained as
   `PaperInterface.proposition5_school2_zero_fallback_objective_bridge_base_survivor_components`.
   Use
   `PaperInterface.theorem3_source_family_subFull_j2_keep_test_pair_iff_survivor_components`
   to rewrite the generated source-family table's named school-`J2` keep-test
   predicates directly to the displayed condition-(11)--(12) survivor rows, and
   `PaperInterface.theorem3_source_family_subFull_j2_keep_test_pair_iff_base_table_keep_test_pair`
   when a wrapper expects the same keep-test pair on the base component table.
   Proposition 5(ii)'s high-at-low-root premise can now be proved from direct
   high-vs-low test-free and test-based merit inequalities using
   `paper_interface_proposition5_high_merit_at_low_root_of_test_free_lt_and_test_based_le`.
   The next upstream bridge is also proved:
   `paper_interface_proposition5_fullSub_ordered_merits_of_gaussian_tail_mean_formulas`
   derives those direct ordered-merit premises from Gaussian upper-tail-mean
   identifications plus scale/threshold comparisons, and
   `paper_interface_proposition5_low_and_high_cost_thresholds_of_selected_twoFull_merit_crossings_interval_of_gaussian_tail_mean_formulas`
   composes the Gaussian bridge with the selected equation-(46) low/high
   threshold construction.  The selected equation-(46) weighted-objective
   bridge
   `paper_interface_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_gaussian_tail_mean_formulas`
   now uses the same Gaussian tail-mean package to discharge its
   high-at-low-root premise internally.  The posterior-mean source-family
   adapter
   `paper_interface_proposition5_fullSub_ordered_merits_of_posterior_mean_scale_families`
   derives the same order package from `GaussianOffsetSignalFamily`
   posterior-mean laws; its companion
   `paper_interface_proposition5_high_merit_at_low_root_of_posterior_mean_scale_families`
   derives the exact root-side premise from those same source-family facts.
   The source-free variants
   `paper_interface_proposition5_fullSub_ordered_merits_of_posterior_mean_source_free_families`
   and
   `paper_interface_proposition5_high_merit_at_low_root_of_posterior_mean_source_free_families`
   generate the low/high test-free full-sub merit rows directly from posterior
   Gaussian upper-tail means; only the cost-indexed test-based full-sub row
   formulas remain explicit.
   The posterior cost-row variants now also have standard-Gaussian compact
   aliases:
   `paper_interface_proposition5_standardGaussian_fullSub_ordered_merits_of_posterior_mean_source_free_cost_rows`
   and
   `paper_interface_proposition5_standardGaussian_high_merit_at_low_root_of_posterior_mean_source_free_cost_rows`.
   The paper-facing Theorem 3 alias now uses the compact
   cutoff-order/threshold-order/fixed-law cost-row route
   `paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_public_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds`.
   The school-`J2` condition-(11)--(12) side is exposed as the bundled
   `GLM20Theorem3J2SurvivorRows`, with
   `paper_interface_theorem3_j2_survivor_rows_components` available for audit.
   The generated-table keep-test variant remains available through the support
   alias `PaperInterface.theorem3_two_school_academic_merit_source_family_keep_test_surface`.
   The feasibility-aware support route now also has
   `paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval_of_j2_keeps_test`,
   which exposes the school-`J2` survivor condition as the named keep-test
   predicate instead of raw survivor-merit premises.
   The generated source-family policy-state table rows are exposed as
   `paper_interface_theorem3_source_family_policy_state_table_surface_rows`,
   and the two surviving-group keep-test predicates on that generated table are
   bundled by
   `paper_interface_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_components`.
   The selected objective bridge
   `paper_interface_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_scale_families`
   now runs those posterior-mean source-family rows through the full
   Proposition 5(ii) weighted-objective iff.
   The binary-objective adapter
   `paper_interface_theorem3_source_conditions_of_binary_policy_objective_conditions_of_subFull_objective_and_fullSub_objective_bridge`
   now turns any packaged full-sub Proposition 5(ii) threshold/objective
   bridge into the corresponding Theorem 3 source-condition bridge.  The
   stronger
   `PaperInterface.theorem3_binary_objectives_from_subFull_and_fullSub_bridges`
   adapter consumes packaged Proposition 5(i) and Proposition 5(ii) bridges
   together, preserving both sets of threshold/root facts.
   `PaperInterface.theorem3_weighted_binary_objectives_from_subFull_and_fullSub_bridges`
   specializes this adapter to the weighted academic-merit binary-policy
   surface, and
   `PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_subFull_keep_test_and_fullSub_bridge`
   also generates the Proposition 5(i) sub-full bridge from the
   standard-Gaussian keep-test/equation-(50) route.
   `PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_prop5_bridges`
   now composes the fixed-law posterior Proposition 5(ii) full-sub bridge into
   the same weighted adapter, so neither Proposition 5 bridge is supplied as an
   opaque package at this layer.
   `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_weighted_surface_theorem3_source_conditions_exists`
   is the reverse direction for this same weighted surface: use it when a
   route has already closed the Theorem 3 source-condition triple and the
   ledger needs the Proposition 5 existential source surface.  Use the
   `_rich_theorem3_source_conditions_exists` variant when the available theorem
   returns extra threshold/root witness facts along with the triple.  For the
   current feasible weighted surfaces, use
   `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_feasible_weighted_surface_theorem3_source_conditions_exists`;
   its
   `_rich_theorem3_source_conditions_exists_inferred_extra` variant is the
   direct adapter from the rich compact Theorem 3 packages and leaves exactly
   the current-pair and unilateral-deviation feasibility facts as explicit
   obligations.  On the concrete policy-state sub/full mass-feasibility
   surface, prefer
   `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_theorem3_source_conditions_exists`
   or its rich inferred-extra variant; this discharges the definitional
   feasibility facts and leaves only school `J2`'s condition-(11) sub/full
   mass-fill predicate visible.  If the full
   `GLM20Theorem3J2SurvivorRows` source bundle is already available, use the
   `..._of_j2_survivor_rows` policy-state adapters to discharge that remaining
   feasibility predicate from the bundled survivor mass rows.  If the source
   route instead carries school-`J2` keep-test predicates, use the
   `..._of_base_j2_keep_test_pair` adapters for the base policy-state table or
   the `..._of_source_family_j2_keep_test_pair` adapters for the generated
   source-family table; both extract condition-(11)'s mass-fill rows from the
   keep-test pair before composing with Proposition 5.  The remaining
   work is concrete strategic-game
   instantiation of the family, cost-row, cutoff-order, and objective-row
   assumptions feeding this adapter.  A direct Proposition 5 closure from the
   generated-table keep-test Theorem 3 endpoint should wait until the
   `honlyA`/`honlyB` objective-row equalities are proved or bundled; otherwise
   it only produces another large function over those same row-identification
   premises.
   The
   top-level Theorem 3 wrapper
   `paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test`
   now consumes fixed-law posterior-mean full-sub cost rows directly, generates
   the equation-(50) sub-full row internally, and states the final school-`J2`
   condition-(11)--(12) requirements as named keep-test predicates on the
   generated source-family table.  The current compact alias uses the
   strict-survivor public-row companion
   `paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds`,
   which derives the full/full fill premises from `fullFullCutoff g <= q_iSub`,
   derives the full-sub endpoint merit crossings from fixed-law threshold-order
   comparisons, derives based-threshold regularity from positive affine
   slopes, and consumes
   `GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare`.
   Use
   `PaperInterface.theorem3_public_rows_with_population_share_of_source_family_j2_keep_test_pair`
   or its raw full/sub prior-precision variant to build that public-row premise
   from generated source-family keep-test facts.  The direct paper-facing route
   `PaperInterface.theorem3_two_school_academic_merit_source_family_keep_test_fullSub_prior_precision_rows`
   constructs the public-row package internally from those primitive rows
   before invoking the compact Theorem 3 endpoint.  Use
   `PaperInterface.theorem3_two_school_academic_merit_fullSub_prior_precision_rows`
   when condition-(11)--(12) is already available as bundled survivor rows and
   the full/sub generated-row package should be built directly from primitive
   prior mean, prior variance, precision, affine-threshold, and cost-bound
   rows.  Use
   `PaperInterface.theorem3_two_school_academic_merit_strict_survivor_prior_precision_rows`
   for the feasibility-aware version where condition-(11)'s mass side is
   carried by feasibility and the school-`J2` input is only strict
   condition-(12) merit rows.  Use
   `PaperInterface.theorem3_source_conditions_exists_from_rich_theorem3_source_conditions_exists`
   to drop extra threshold/root witnesses from rich Theorem 3 packages before
   feeding simpler downstream bridges.  The older abstract Gaussian-tail-law route
   remains available as
   `paper_interface_theorem3_gaussian_fullSub_merits_of_j2_keeps_test`.
   Future Theorem 3
   work should instantiate these source formulas before treating the merit
   order as a raw assumption.  The raw-survivor theorem also has a
   posterior-family route,
   `paper_interface_theorem3_raw_survivor_conditions_of_posterior_mean_fullSub_merits`,
   for source-family full-sub merit rows while condition-(12)'s survivor
   premises remain explicit.
   The support alias
   `PaperInterface.theorem3_subFull_j2_keeps_test_iff_survivor_components`
   packages each raw condition-(11)--(12) survivor mass+merit pair as the named
   source-game condition that school `J2` keeps the test for the surviving
   group under `(P_sub,P_full)`.
   `PaperInterface.theorem3_subFull_j2_keeps_test_of_survivor_components`
   is the one-way helper for feeding an already proved raw survivor component
   pair into the strongest keep-test route.
   `PaperInterface.theorem3_two_school_academic_merit` now uses the compact
   source-row route: cost bounds, capacity/cutoff rows, affine tail rows, and
   fixed-law posterior cost rows are bundled, while the school-`J2`
   condition-(12) merit side is exposed as
   `GLM20Theorem3J2StrictSurvivorMeritRows` and the population-share domain is
   bundled in the same public package.  The four-row survivor, named keep-test,
   generated-table, and raw-row routes remain available as audit
   aliases.
   The LG21-style a.e. strategic-equilibrium support is available as
   `PaperInterface.strategic_equilibrium_ae_of_pointwise` plus proof-interface
   projections, so future continuous-type strategy work can avoid pointwise
   cutoff-tie obligations when no-atoms/boundary-null lemmas apply.
   Proposition 2 also has
   `PaperInterface.proposition2_application_strategy_ae_unique`, which proves
   the displayed application-region strategy is unique a.e. under singleton-null
   low/high cutoff boundaries.
   The separate `PaperInterface.theorem3_two_school_academic_merit_feasible_surface`
   alias exposes the feasibility-aware route where condition-(11)'s survivor
   mass lives in the feasibility predicate and only raw survivor-merit
   inequalities remain visible for school `J2`.  Use
   `PaperInterface.theorem3_two_school_academic_merit_strict_survivor_merits`
   for the compact fixed-law/cost-bound/affine-tail source-family route with
   those strict survivor-merit inputs; it is validated by
   `lake build GLM20DroppingStandardizedTesting.PaperInterface` on 2026-05-23.
   Use
   `GLM20Theorem3J2StrictSurvivorMeritRows` and
   `PaperInterface.theorem3_feasible_endpoint_of_j2_strict_survivor_merit_rows`
   to bundle those two strict condition-(12) rows without re-exposing the
   capacity rows.  If the strict rows are currently available through named
   keep-test predicates, use
   `PaperInterface.theorem3_subFull_j2_strict_survivor_merit_rows_of_keep_test_pair`
   on the base table or
   `PaperInterface.theorem3_source_family_j2_strict_survivor_merit_rows_of_keep_test_pair`
   on the generated source-family table.
   The compact Proposition 2(iii) aliases now use corrected-source row
   wrappers, so the old `hmore`/`hj1`/`hj2` diversity-row identification
   premises are removed from the human-facing surface.
   `PaperInterface.proposition2_corrected_subEligible_mass_eq_testFree_tail`
   identifies the corrected eligible-mass formula with the unnormalized
   upper-tail probability under the test-free estimated-skill law.  The
   applicant-pool adapter
   `PaperInterface.proposition2_strategic_applicant_pool_masses_to_corrected_source_rows`
   connects the same corrected admitted-mass rows to the Lemma 3 strategic
   applicant mass fixed point, and
   `PaperInterface.proposition2_strategic_applicant_pool_masses_to_corrected_source_rows_paper_groups`
   specializes that bridge to the paper's group-A and group-B rows.  The compact
   Proposition 2(iv) alias now also uses a source-row wrapper, removing the
   lower-academic-merit and academic-merit row-identification premises from
   the public `lambda < kappa` surface.  Proposition 3's compact alias now
   specializes capacity, admitted-share rows, and displayed `lambda` rows
   internally through a source-row wrapper, so the human-facing endpoint is the
   Equation (37) ratio plus the displayed `lambda` merit comparison.
3. Replace remaining strategic certificate endpoints with source-shaped
   theorem wrappers where the paper provides concrete formulas. Proposition 5
   now has the typed source-condition target
   `PaperInterface.proposition5_strategic_academic_merit_source_conditions`,
   plus the existential-threshold target
   `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists`,
   with
   `PaperInterface.proposition5_strategic_academic_merit_source_conditions_from_objective_bridges`
   and
   `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_objective_bridges`
   packaging the two objective bridges and full/full boundary condition.  The
   positive-cost and full/full cost-family variants fill the third component
   internally when those assumptions are the available source route.  For the
   current Proposition 5 bridge theorems, prefer
   `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_three_subFull_six_fullSub_side_condition_bridges_and_positive_costs`
   or its full/full cost-family variant: these forget the threshold
   construction side facts and keep the objective iff statements needed for the
   Proposition 5 source surface.  If Theorem 3 source conditions are already
   available on the weighted academic-merit binary surface, use
   `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_weighted_surface_theorem3_source_conditions_exists`
   instead, or the `_rich_theorem3_source_conditions_exists` variant if the
   route returns extra threshold/root witnesses.  Use
   `PaperInterface.theorem3_from_proposition5_strategic_academic_merit_source_conditions`
   or the existential-threshold
   `PaperInterface.theorem3_source_conditions_exists_from_proposition5_strategic_academic_merit_source_conditions_exists`
   to feed that result into Theorem 3. Prioritize named main-text results over
   appendix generalizations.
4. After the main-text strategic section is closed, return to Appendix F/G:
   Blackwell/SSD support and Propositions 7--9 should either be proved from
   finite/continuous reusable library lemmas or left with explicit documented
   source assumptions if the paper itself only invokes them as extension
   sketches.
5. Finish with the post-paper checklist: rebuild `PaperInterface`,
   `PostPaperAudit`, and the dependency DAG, update the README and final
   validation report with exact closed declaration names, and preserve the
   Theorem 1 and Theorem 2 source caveats rather than smoothing them away.

## Current State

- One-week restart note: `START_HERE_NEXT_AGENT.md`. Future agents should read
  that short file before this longer proof plan.
- Finite admissions accounting is proved in `MainTheorems.lean`.
- Lemma 1's reusable Gaussian algebra is proved:
  `paper_lemma1_estimated_skill_gaussian` gives the precision-weighted
  posterior mean and estimated-skill law variance formula.
- Lemma 1's source-surface wiring is proved:
  `paper_lemma1_estimated_skill_source_surface` and
  `paper_interface_lemma1_estimated_skill_source_surface` use the canonical
  `lemma1GaussianSourceSurface` to connect group/policy feature precision,
  estimated-skill mean, and estimated-skill variance to
  `GaussianOffsetSignalFamily`.
- Fixed-feature Gaussian threshold support is proved:
  `paper_fixed_feature_gaussian_threshold_iff_cutoff` turns posterior-score
  admission into an explicit cutoff inequality in one feature value.
- Proposition 1(i)'s static diversity/group-fairness core is now proved:
  total precision gaps imply posterior-mean scale gaps, selectivity below one
  half pushes the common threshold above the common mean, and the resulting
  strict Gaussian tail comparison implies group-B under-representation and
  group-fairness failure.
- Proposition 1(ii)'s individual-fairness failure/cutoff core is now proved:
  the Gaussian tail gap is positive exactly when the standardized threshold
  comparison holds, and the paper's precision algebra reduces that comparison
  to a skill cutoff.
- Proposition 1(iii)'s admitted-merit core is now proved under the explicit
  scaled-hazard monotonicity certificate: if admitted academic merits are the
  Gaussian upper-tail means, the larger-scale group A has strictly higher
  admitted merit.
- Proposition 1's closed-form threshold/diversity comparative statics are now
  proved: increasing group A's informativeness gap strictly raises the paper's
  displayed common threshold formula and strictly decreases group B's admitted
  share when group B's score law and capacity are fixed.
- Proposition 1's high-skill individual-fairness-gap comparative core is now
  proved: once the group-A standardized cutoff is in the paper's scalar
  square-root form, increasing group A precision raises the individual-fairness
  gap for skills above the perfect-information cutoff.
- Lemma 2's generic calculus shell is now proved: negative derivative on
  `(q_e, ∞)` implies the individual-fairness gap strictly decreases there, and
  vanishing group admission tails imply `I(q; P_S) → 0`.  The source's
  log-density threshold algebra for the displayed `q_e` is also proved.  The
  reusable `StandardGaussianDerivativeAPI` now proves continuity and derivative
  equations for affine Gaussian upper tails, and
  `StandardGaussianDoubledLogDensityAPI` captures the paper's doubled-log
  normal-density comparison. GLM20 bundles those facts in
  `paper_lemma2_individual_fairness_gap_strictAntiOn_of_qe_standard_normal_tail_formulas`,
  which takes the paper's `numerator / sqrt(precision)` standardization form.
  The threshold-probability wrapper
  `paper_lemma2_individual_fairness_gap_strictAntiOn_of_qe_threshold_tail_formulas`
  rewrites source Gaussian pass probabilities into that affine-tail theorem.
  The conditional posterior-score law
  `GaussianOffsetSignalFamily.conditionalPosteriorMeanScaleLaw` is now in the
  shared Gaussian library, and
  `paper_lemma2_individual_fairness_gap_strictAntiOn_of_qe_conditional_posterior_laws`
  instantiates the decreasing-tail part of Lemma 2 for those conditional
  Gaussian laws.  `StandardGaussianTailLimitAPI` and
  `paper_lemma2_individual_fairness_gap_tendsto_zero_of_conditional_posterior_laws`
  prove the source limit `I(q; P_S) → 0` from the same conditional laws.
  `paper_lemma2_conditional_posterior_laws` packages both source conclusions
  of Lemma 2 behind one theorem over `StandardGaussianAnalyticAPI`.
  `lemma2ConditionalPosteriorSourceSurface` and
  `paper_lemma2_conditional_posterior_laws_source_surface` now close the
  remaining field-binding step by making the source surface's
  `individualFairnessGap` unfold directly to the conditional Gaussian
  admission-probability difference.  `GaussianMathlib` now instantiates
  `StandardGaussianAnalyticAPI` from mathlib's standard Gaussian CDF/density:
  `standardGaussianCDF_hasDerivAt_density` proves that the mathlib CDF has
  derivative equal to `standardGaussianDensity`, and
  `standardGaussianDoubledLogDensity_eq` proves the doubled-log density
  identity.  The preferred Lemma 2 endpoint is now
  `paper_lemma2_conditional_posterior_laws_source_surface_standardGaussian`.
- Theorem 1's access-barrier main-body threshold theorem is now proved at the
  canonical source-surface endpoint
  `paper_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_of_population_access_bounds`
  and exposed in the human-facing ledger as
  `paper_interface_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_of_population_access_bounds`.
  The canonical source surfaces make the paper's `diversity`, `academicMerit`,
  `accessLevel`, and `capacity` fields unfold to the admitted group-B share and
  Gaussian upper-tail merit formulas at the standardized `β_A`/`β_B` cutoffs
  and no-test benchmarks.  The cutoff-capacity bridge now has a stronger
  endpoint:
  `paper_theorem1_dropping_tests_with_barriers_canonical_of_capacity_range`.
  The shared Gaussian library proves strict monotonicity, continuity, and
  two-sided limits for finite Gaussian mixture upper-tail mass; GLM20 then
  constructs the unique cutoff for each `γ_B ∈ [0,1]`.  The new worst-case
  wrapper derives the repeated capacity and selectivity hypotheses from scalar
  inequalities using the paper's population/access products
  `(1 - pi) * gammaA`, `pi * gammaB`, and `pi`.  The helper lemmas are
  `theorem1_capacity_mem_on_unit_of_capacity_lt_groupAEligibleMass`
  and `theorem1_selective_on_unit_of_two_capacity_lt_otherEligibleMass`.  The
  paper's displayed weighted upper-tail capacity equation follows from `theorem1BarrierMixtureTailMass_eq`,
  and `paper_theorem1_barrier_threshold_continuousOn_of_capacity_equations`
  derives cutoff continuity from capacity realization.
  `paper_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_of_capacity_range`
  discharges the Gaussian CDF-limit, quantile, hazard-inverse, and derivative
  API fields with the mathlib-backed standard normal.  The remaining Theorem 1
  caveat is now the explicit economic capacity domain, not an assumed
  mixture-capacity equation or an analytic normal API premise.
  The component routes remain available as
  `paper_theorem1_diversity_access_threshold_of_capacity_share_main`,
  `paper_theorem1_academic_merit_access_threshold_of_groupA_normal_laws_main`,
  and `paper_theorem1_academic_merit_access_threshold_of_groupB_normal_laws_main`.
  Endpoint crossing is no longer needed for the main-body real-threshold
  statement; the older `_crossing` wrappers still provide appendix-style
  interior thresholds when endpoint inequalities are supplied.
  `EconCSLib.Foundations.Probability.GaussianMathlib` now instantiates the
  basic standard-normal CDF/density API from mathlib's `gaussianReal`:
  continuity, strict monotonicity, median value, CDF bounds, density
  nonnegativity, and strict upper-tail positivity are proved.  It also provides
  the true standard-normal quantile as the order inverse of this CDF on
  `(0,1)` and a concrete `standardGaussianQuantileAPI`; Theorem 1's beta
  continuity proofs now use the paper's selectivity assumptions to prove the
  quantile arguments lie in `(0,1)`.  `GaussianMills` and `GaussianMathlib`
  also prove the standard-normal hazard positivity, monotonicity,
  scaled-hazard monotonicity, positive-threshold inverse, and concrete
  `standardGaussianHazardInverseCertificate`.  The threshold argument itself is
  no longer only an anonymous explicit-metrics theorem or a named
  cutoff-certificate wrapper.  It also supplies
  `standardGaussianAnalyticAPI`, which is the reusable closure needed by Lemma
  2's derivative argument.
- Source-facing wrappers exist for every named main-body and appendix result.
- `PaperInterface.lean` is the human-facing theorem statement ledger.
- The remaining named results are mostly conditional on Gaussian posterior,
  threshold, hazard-rate, Blackwell/SSD, or strategic equilibrium certificates.
- Theorem 2(ii)'s group-level admission-probability crossing core is now
  proved in `paper_theorem2_group_admission_probability_decreases_iff_above_cutoff`:
  affine standardized Gaussian upper tails cross exactly above the displayed
  skill cutoff.
- Theorem 2 now has direct standard-Gaussian no-barrier source-surface
  endpoints.  The human-facing route is
  `paper_interface_theorem2_dropping_tests_without_barriers_standardGaussian_source_surface`.
  It proves the static bundle for the canonical surface: diversity improves iff
  the displayed Equation (3) test-precision ratio holds, each group's
  full-versus-sub admission probability crosses at an affine Gaussian cutoff,
  admitted academic merit decreases for both groups.  The cached source has a
  high-skill direction mismatch: the Theorem 2 statement and nearby narrative
  say that the individual-fairness gap increases after dropping tests, while
  the appendix proof concludes `I(q; Pfull) > I(q; Psub)` and says the gap
  decreases.  Lean now proves the main-text direction separately via
  `paper_theorem2_high_skill_individual_fairness_gap_sub_gt_full_source_surface_of_precision_order`
  and exposes it in `PaperInterface.lean` as
  `paper_interface_theorem2_high_skill_individual_fairness_gap_sub_gt_full_source_surface_of_precision_order`.
  This proof requires the extra assumption `subB < subA`: after dropping the
  test, the remaining features still give group A higher total precision than
  group B.  It uses the shared Gaussian left-tail dominance lemma
  `standardGaussianCDF_affine_leftTail_lt_mul_eventually_of_slope_lt`.
  The corrected main-text bundle
  `paper_theorem2_dropping_tests_without_barriers_standardGaussian_source_families_of_precision_order_population_weights_capacity_thresholds_main_text_direction`
  constructs the two no-barrier admission thresholds from the concrete
  standard-normal mixture-capacity equation, fixes the paper population weights
  to `1 - pi` and `pi`, and derives the high-skill comparison from
  `subB + testB < subA + testA` plus the main-text assumption `subB < subA`.
  The `ProofInterface` theorem-facing Theorem 2 bundle wrappers now all route
  to this main-text assumption/conclusion.  The older crossed-order
  opposite-direction core remains in `MainTheorems.lean` only as a
  source-audit artifact for Appendix D.4's mismatch.
  The source-model wrapper
  `paper_theorem2_dropping_tests_without_barriers_standardGaussian_source_model_appendix_direction`
  now calls that main-text route; the old suffix is kept only for compatibility.
  The per-group threshold part of
  Theorem 2(ii) is now separated from the high-skill individual-fairness
  bundle:
  `paper_theorem2_group_admission_thresholds_standardGaussian_source_families_capacity_thresholds`
  constructs the two no-barrier capacity cutoffs and proves each group's
  full-versus-sub admission crossing using only positive added test precision,
  without any cross-group test-free precision-order premise.  The remaining
  validation caveat is textual: the source-model theorem uses `subB < subA`,
  which matches the prose/model convention but is not explicit in the theorem
  statement, and Appendix D.4's crossed-order derivation is treated as a
  source-text issue; see `FINAL_VALIDATION_REPORT.md`.

## Fastest Proof Route

1. Use the shared probability library first:
   `EconCSLib.Foundations.Probability.Admissions`,
   `Kernel`, `Conditional`, `Gaussian`, and `RealDistribution`.
2. Treat Proposition 1's static fixed-policy conclusions as closed at the
   canonical standard-Gaussian source-surface endpoint
   `paper_proposition1_fixed_policy_static_core_source_surface_standardGaussian`.
   The threshold/diversity comparative statics are proved through
   `paper_proposition1_diversity_share_decreases_of_precision_gap_lt`, and the
   high-skill individual-fairness-gap comparative core is proved through
   `paper_proposition1_individual_fairness_gap_increases_of_precision_gap_high_skill_formula`.
3. Lemma 1 source-surface wiring is done:
   `paper_lemma1_estimated_skill_source_surface` connects group/policy feature
   precision, estimated-skill mean, and `estimatedSkillVariance` to
   `GaussianOffsetSignalFamily`.  Future Lemma 1 work should only replace the
   legacy certificate wrapper if desired; the paper-facing statement is already
   the canonical direct theorem.
4. Treat Lemma 2 as closed at the canonical conditional-posterior source-surface
   endpoint.  The source-surface `individualFairnessGap` field now unfolds to
   the conditional Gaussian probability formula.  If later work needs a raw
   feature/cutoff instantiation, build it as an adapter to
   `lemma2ConditionalPosteriorSourceSurface` rather than reopening the Lemma 2
   proof tower.
5. Treat Theorem 1's threshold argument as closed at the canonical
   source-surface layer via
   `paper_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_of_capacity_range`,
   with
   `paper_interface_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_of_capacity_range`
   as the human-facing ledger statement.  Do not reintroduce endpoint crossing
   unless proving the stronger appendix claim that the threshold is interior.
   If revisiting Theorem 1, the only honest remaining gap is weakening or
   justifying the low-capacity/interior-selectivity domain
   `2 * capacity < pi * gammaB` and
   `2 * capacity < (1 - pi) * gammaA` from the raw paper model.  The separate
   capacity-feasibility premise is derived from these assumptions, and
   `paper_interface_theorem1_low_capacity_domain_nonempty` proves that the
   domain is feasible under positive masses/access levels.  Cutoff continuity
   and the quantile/Mills/hazard threshold proof are not blockers.
6. Treat Theorem 2's raw-parameter adapter as closed at the corrected
   source-model wrapper. The canonical no-barrier source surface wires
   diversity, affine admission probabilities, and upper-tail academic merit to
   the paper formulas; the high-skill comparison is discharged from
   `subB + testB < subA + testA` and the main-text test-free precision order
   `subB < subA`. Keep the per-group crossing theorem separate from the
   high-skill gap theorem because the group-threshold clause needs only
   positive added test precision.
7. Keep Section 5 strategic proofs separate from static Gaussian algebra.
   The two-school binary policy game now has a clean unilateral-deviation
   bridge:
   `glm20TwoSchoolBinaryPolicyEquilibrium_subFull_iff`,
   `glm20TwoSchoolBinaryPolicyEquilibrium_fullSub_iff`, and
   `glm20TwoSchoolBinaryPolicyEquilibrium_fullFull_iff` reduce each policy-pair
   equilibrium to the two school objective inequalities for deviations within
   `{P_sub, P_full}`.  The two-group weighted academic-merit objective
   `glm20TwoGroupWeightedAcademicMeritObjective` is encoded, and
   `paper_theorem3_school2_keep_test_objective_le_of_single_group_merit_gt`
   proves the condition (12) merit inequality gives school 2's keep-test
   objective comparison when `(P_sub,P_full)` admits only the surviving group.
   The one-school Lemma 3 Gaussian cutoff calculation is now closed through
   `paper_lemma3_full_policy_threshold_form_precision_standardGaussian`, which
   expands the projected admission scale to the paper's square-root precision
   expression.  The binary cutoff application rule is now proved as a student
   best response by
   `paper_lemma3_precision_cutoff_apply_bestResponse_standardGaussian`.  The
   strict payoff order on both sides of the cutoff is proved by
   `paper_lemma3_precision_cutoff_apply_strict_payoff_order_standardGaussian`;
   any pointwise best response is threshold-form away from indifference by
   `paper_lemma3_precision_pointwise_bestResponse_threshold_form_standardGaussian`;
   and, with the paper's tie-breaking convention that the indifferent type
   applies, the local student strategy is unique by
   `paper_lemma3_precision_unique_threshold_strategy_standardGaussian`.  These
   components now compose into the source-shaped Lemma 3 equilibrium endpoint
   `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_standardGaussian`
   and the finite-mixture endpoint
   `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_standardGaussian_mixture`.
   The paper's self-consistent Equation (35) mass shape is also explicit in
   `glm20Lemma3StrategicApplicantMass` and
   `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_strategic_applicant_mass`,
   where each group's Equation (7) application cutoff is substituted into the
   application-gated applicant pool before solving the school capacity fixed
   point.  The aggregate Eq. (35) regularity bridge
   `glm20Lemma3StrategicApplicantMass_regular_of_components` proves that the
   finite group sum inherits continuity, strict decrease, and endpoint limits
   from per-group components.  The measure-backed source event
   `glm20MeasureApplyAdmitMass` now models
   `π_g * P(q_sub >= qApply and q_full >= qAdmit)`, and
   `glm20Lemma3StrategicApplicantComponent_measure_strictAnti`,
   `glm20Lemma3StrategicApplicantComponent_measure_tendsto_atBot`, and
   `glm20Lemma3StrategicApplicantComponent_measure_tendsto_atTop` prove the
   strict-decrease and endpoint obligations after substituting Eq. (7), for
   finite open-positive joint laws.  Continuity is now proved by
   `glm20Lemma3StrategicApplicantComponent_measure_continuous_of_noAtoms_marginals`,
   using the reusable nonatomic-boundary theorem
   `upperOrthantMass_diagonal_continuous_of_noAtoms_marginals`.  These
   component facts compose into
   `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_measure_applicant_components`,
   a source-shaped Lemma 3 `∃!` endpoint for finite open-positive joint laws
   with nonatomic marginals.  The stronger endpoint
   `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_density_applicant_components`
   now derives the same regularity from normalized positive joint densities over
   `(q_sub,q_full)`, using the reusable Lebesgue-density boundary-null and
   open-positive facts in `MeasureInequalities`.  The concrete correlated-law
   endpoint
   `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_correlatedStandardGaussian_applicant_components`
   now derives the same Eq. (35) source-event equilibrium from
   `correlatedStandardGaussianLaw`, using the per-component regularity package
   `glm20Lemma3StrategicApplicantComponent_correlatedStandardGaussian_regular`.
   Treat Lemma 3 itself as closed at these source-event surfaces; the remaining Owen/bivariate
   CDF identity belongs to Proposition 3 / Appendix D support, where the paper
   rewrites this source event into the displayed closed form.  The
   two-school Proposition 2 application-region calculation is closed through
   `paper_proposition2_two_school_application_region_precision_standardGaussian_of_high_cost_ratio`
   with the same precision scale.  The helper
   `paper_proposition2_cost_ratio_low_of_high` derives the low cost-ratio
   domain from the high cost-ratio domain and `0 < v1 - v2 < v1`, so the
   preferred wrappers do not separately assume `c_g / v1 ∈ (0,1)`.
   `paper_proposition2_two_school_application_region_bestResponse_precision_standardGaussian_of_high_cost_ratio`
   proves that the displayed region indicator is a pointwise best response for
   the two-school incremental payoff.  The tie-broken local uniqueness theorem
   `paper_proposition2_two_school_application_region_unique_strategy_precision_standardGaussian_of_high_cost_ratio`
   then proves that every pointwise best-response strategy with the paper's
   cutoff convention equals that low/high region.  The qualitative
   non-monotonicity implication in the text after Proposition 2 is exposed by
   `paper_proposition2_two_school_application_region_nonmonotone_between_cutoffs`.
   The scalar school-cutoff
   capacity fixed-point support for Lemma 3 is now proved by
   `paper_lemma3_school_cutoff_existsUnique_and_capacity_region_of_strictAnti_applicant_mass`,
   and the Proposition 2 two-school selection-threshold part is packaged by
   `paper_proposition2_two_school_selection_thresholds_existUnique_and_capacity_regions_of_strictAnti_applicant_masses`
   by applying that cutoff theorem to each school-specific applicant mass,
   and the source-shaped threshold-equilibrium endpoint
   `paper_proposition2_two_school_threshold_equilibrium_existsUnique_standardGaussian_of_high_cost_ratio`
   now proves uniqueness of the triple `(J1 cutoff, J2 cutoff, student
   strategy)` from those two school cutoffs plus student best-response
   uniqueness.  The finite standard-Gaussian mixture instantiations
   `paper_proposition2_standardGaussian_mixture_threshold_equilibrium_existsUnique_of_high_cost_ratio`
   and
   `paper_proposition2_standardGaussian_mixture_threshold_equilibrium_existsUnique_precision_of_high_cost_ratio`
   discharge the continuity, strict antitonicity, and tail-limit obligations
   for Gaussian-mixture applicant masses, with the latter using the paper's
   projected precision scale.  The group-indexed paper-shaped endpoint
   `paper_proposition2_two_school_group_threshold_equilibrium_existsUnique_precision_of_high_cost_ratio`
   now proves uniqueness with common school cutoffs but per-group costs and
   precision scales, and
   `paper_proposition2_standardGaussian_mixture_group_threshold_equilibrium_existsUnique_precision_of_high_cost_ratio`
   instantiates it for finite standard-Gaussian applicant mixtures,
   using the reusable library theorem
   `existsUnique_eq_of_continuous_strictAnti_tendsto_atBot_atTop`.  The
   standard-Gaussian finite-mixture instantiation is now also proved by
   `paper_lemma3_standardGaussian_applicant_mixture_cutoff_existsUnique_and_capacity_region`,
   using the reusable probability theorem
   `existsUnique_mixtureTailMass_eq_and_region_of_capacity_mem_Ioo`.
   `paper_lemma3_standardGaussian_applicant_mixture_cutoff_from_offset_families`
   specializes this to group-indexed `GaussianOffsetSignalFamily`
   posterior-mean laws.  Proposition 2(iii)--(iv) now has a paper-facing
   formula layer rather than only the application-region theorem:
   `glm20Proposition2AdmittedMassFormula` encodes
   `D_g(a_hat_g(q_a))`, `glm20Proposition2SubEligibleMassFormula` encodes the
   test-free eligible mass above `q^*_{2,sub}`,
   `glm20Proposition2SubEligibleUnnormalizedMassFormula_eq_scaled_testFreeTail`
   identifies the corrected unnormalized eligible-mass formula with the
   test-free estimated-skill upper tail,
   `glm20Proposition2AdmittedMassFormula_eq_correlatedStandardGaussian_verticalUpperStripMass`
   instantiates the `D_g` bivariate CDF expression with the concrete
   correlated standard-Gaussian law,
   `paper_proposition2_part_iii_diversity_criterion_above_high_cutoff` and
   `paper_proposition2_part_iii_diversity_criterion_between_cutoffs` prove the
   two displayed `J1`-more-diverse iff mass-ratio criteria from the school
   diversity-share formulas, and
   `paper_interface_proposition2_admitted_mass_formula_eq_owenAffineSelectionMass`
   exposes the same `D_g` formula as the standardized source-affine Owen event,
   not only as a correlated-Gaussian vertical strip.  Finally,
   `paper_proposition2_part_iv_lower_academic_merit_iff_lambda_lt_kappa`
   rewrites the lower-academic-merit comparison to the displayed
   `lambda < kappa` inequality.  The shared Gaussian library now also proves
   `standardGaussianDensity_mul_affine_integral_interval` and
   `standardGaussian_firstMoment_affineCDF_integral_interval`, and GLM20
   exposes them as `paper_interface_proposition2_owenProductInterval_eq` and
   `paper_interface_proposition2_owenFirstMomentInterval_eq`; this discharges
   the finite-interval product-density and first-moment analytic steps behind
   the `kappa` route by subtracting two upper-tail identities.  The same
   library layer now proves the direct lower-tail versions
   `standardGaussianDensity_mul_affine_integral_Iic` and
   `standardGaussian_firstMoment_affineCDF_integral_Iic`; GLM20 exposes these
   as `paper_interface_proposition2_owenProductLowerTail_eq` and
   `paper_interface_proposition2_owenFirstMomentLowerTail_eq`, giving the
   source-shaped identity
   `∫_{-∞}^{q} z φ(z) Φ(A_g D_g + c_g z) dz =
   c_g φ(A_g)Φ(D_g q + A_g c_g)/D_g - φ(q)Φ(A_g D_g + c_g q)`.
   The wrapper
   `paper_interface_proposition2_kappaFormula_eq_scaled_owenFirstMomentLowerTail_of_boundary_density`
   then proves the displayed `kappa` expression is the scaled lower-tail first
   moment plus `mu * (1 - tau) / tau`, under the explicit source-density
   premise `φ(upper) = σtilde * φ(q)`.  The source-density variant
   `paperProposition2KappaBoundaryDensityFormula` keeps the boundary density
   explicit, `paper_interface_proposition2_kappaBoundaryDensityFormula_eq_scaled_owenFirstMomentLowerTail`
   proves the same lower-tail bridge for that form, and
   `paper_interface_proposition2_boundaryDensityScaling_of_normalDensity`
   proves the reusable raw-density scaling
   `φ(upper) = σtilde * normalDensity(N(mu, sigmaTilde), raw)` whenever
   `upper = (raw - mu) / sigmaTilde`.  Finally,
   `paperProposition2J2MeritStandardizedLowerTailFormula` packages the
   standardized J2 merit expression as `mu` times the lower-tail selection mass
   plus `sigmaTilde` times the lower-tail first moment, and
   `paper_interface_proposition2_j2MeritStandardizedLowerTailFormula_eq_kappaBoundaryDensityFormula`
   rewrites it to the source-density `kappa` formula from the two explicit
   source facts: lower-tail mass `= 1 - tau` and boundary-density scaling.
   The lower affine source event itself is no longer opaque:
   `paper_interface_proposition2_owenAffineLowerSelectionMass_eq_correlatedStandardGaussian_lowerLeftRectangleMass`
   proves it is the corresponding correlated-standard-Gaussian lower-left
   rectangle, the lower-tail counterpart to Proposition 3's vertical-strip
   Owen identity.
   The mass bookkeeping theorem
   `paper_interface_proposition2_j2MassAboveHighCutoff_eq_lowerLeftRectangle_of_subEligibleMass`
   now proves that, once the test-free eligible mass is identified with the
   affine total-selection mass `pi_g sigma_tilde_g Phi(A_g)`, the paper's
   `subEligible - D_g` expression is exactly that lower-left rectangle.
   The standardized total-mass partition
   `paper_interface_proposition2_admittedMass_add_lowerLeftRectangle_eq_affineTotalMass`
   separately proves the Gaussian bookkeeping
   `D_g + lowerLeft = pi_g sigma_tilde_g Phi(A_g)`.
   The residual lower-left mass is also now proved positive by
   `paper_interface_proposition2_j2MassAboveHighCutoff_pos_of_subEligibleMass`,
   using the reusable probability lemma
   `lowerLeftRectangleMass_pos_of_isOpenPosMeasure`; consequently
   `paper_interface_proposition2_part_iii_diversity_criterion_above_high_cutoff_of_subEligibleMass`
   removes the separate `J2` mass-positivity premise from the first diversity
   criterion.  The complementary diversity case now has the analogous
   decomposition
   `paper_interface_proposition2_j2MassBetweenCutoffs_eq_lowerLeftRectangle_add_cdfGap_of_subEligibleMass`
   and positivity wrapper
   `paper_interface_proposition2_j2MassBetweenCutoffs_pos_of_subEligibleMass`,
   which are composed into
   `paper_interface_proposition2_part_iii_diversity_criterion_between_cutoffs_of_subEligibleMass`.
   The lower-tail integral/event bridge itself is also closed:
   `paper_interface_proposition2_owenSelectionLowerTail_eq_correlatedStandardGaussian_lowerLeftRectangleMass`
   proves the normalized lower-tail affine-CDF integral equals that same
   lower-left rectangle after substituting
   `upper = (qFull - mu) / sigmaTilde`.
   The source-normalized kappa wrapper
   `paper_interface_proposition2_j2MeritStandardizedLowerTailFormula_eq_kappaBoundaryDensityFormula_of_tau_lowerLeftRectangle`
   now composes this lower-left rectangle identity with the paper's
   `tau = 1 - lowerLeftRectangleMass` normalization and the explicit
   boundary-density scaling premise.
   The raw-density variant
   `paper_interface_proposition2_j2MeritStandardizedLowerTailFormula_eq_kappaBoundaryDensityFormula_of_tau_lowerLeftRectangle_normalDensity`
   removes that final premise by plugging in the source
   `N(mu, sigmaTilde^2)` density at the raw full-test cutoff.
   The paper's displayed source definitions `a'_g(q)` and `b'_g` are now
   encoded by `paperProposition2KappaAPrime` and
   `paperProposition2KappaBPrime`, and the specialized wrapper
   `paper_interface_proposition2_j2MeritSourcePrimes_eq_kappaBoundaryDensityFormula_of_tau_lowerLeftRectangle_normalDensity`
   proves the same J2-to-`kappa` bridge with those definitions substituted.
   `PaperInterface.proposition2_tau_normalization_lower_tail` now exposes the
   source-prime normalization directly: after substituting those displayed
   `a'_g(q)` and `b'_g` definitions, the Owen lower-tail selection mass is
   `1 - tau_g`.
   `PaperInterface.proposition2_tau_normalization_source_parameters` carries
   the same identity after also substituting the displayed `\tilde\sigma_g`
   source definition and raw full-test cutoff.
   `PaperInterface.proposition2_affine_total_mass_source_parameters` similarly
   proves the source-parameter `D_g + lowerLeft = pi_g sigma_tilde_g Phi(A_g)`
   partition, and
   `PaperInterface.proposition2_strategic_applicant_pool_mass_add_lowerLeft_eq_affineTotal`
   composes it with the Lemma 3 applicant-pool row after Eq. (7)'s cutoff
   substitution.
   The remaining Proposition 2 work is not this Gaussian integration algebra;
   it is the concrete source Gaussian game bookkeeping tying these source rows
   to the two-school strategic model.
   Proposition 3 now has a source-facing formula layer:
   `glm20Proposition3SelectionCore` encodes the common
   `Φ(A_g)-Φ_2(A_g,B_g;ρ_g)` bracket, `glm20Proposition3TauFormula`
   encodes the displayed bivariate-normal `τ_g` expression, and
   `glm20Proposition3LambdaFormula` encodes the displayed academic-merit
   `λ` expression.  The source-event bookkeeping part of the Owen/CDF identity
   is now proved by
   `paper_proposition3_selection_core_eq_verticalUpperStripMass_of_cdf_identities`:
   once the transformed joint law has first marginal CDF `Φ(A_g)`, lower-left
   bivariate CDF `Φ_2(A_g,B_g;ρ_g)`, and null horizontal boundary, the bracket
   `Φ(A_g)-Φ_2(A_g,B_g;ρ_g)` is exactly the vertical strip mass
   `P(Z_1 <= A_g, B_g <= Z_2)`.  The abstract `Φ_2` seam is now also
   instantiated by `standardBivariateGaussianCDF`, defined as the lower-left
   rectangle mass of `correlatedStandardGaussianLaw ρ`, with
   `paper_proposition3_rho_sq_lt_one`,
   `paper_proposition3_selection_core_eq_correlatedStandardGaussian_verticalUpperStripMass`,
   `glm20BivariateApplyAdmitMass_eq_correlatedStandardGaussian_verticalUpperStripMass`,
   and `paper_proposition3_tau_formula_eq_correlatedStandardGaussian_verticalUpperStripMass`
   proving the paper's bracket, application/admission mass, and `τ_g` formula
   against that concrete correlated-Gaussian law.  The source-affine Owen mass
   bridge is now proved by
   `paper_proposition3_selection_core_eq_owenAffineSelectionMass` and
   `paper_proposition3_tau_formula_eq_owenAffineSelectionMass`: the
   standardized event
   `P(X <= A_g sqrt(1 + (sigma_tilde_g b_g)^2) + sigma_tilde_g b_g Z,
   B_g <= Z)` for independent standard normals is identified with the same
   `Phi(A_g)-Phi_2(A_g,B_g;rho_g)` selection core by a reusable
   characteristic-function proof in `BivariateGaussian`.  The same bridge is
   now exposed for substituted Lemma 3/Proposition 3 application masses by
   `paper_interface_bivariate_apply_admit_mass_eq_owenAffineSelectionMass`.
   The correlated-Gaussian
   library now also proves the exact first and second standard-normal marginals:
   the second marginal uses mathlib's Gaussian scaling and convolution theorem.
   The same law is proved open-positive when `ρ^2 < 1`; GLM20 packages this as
   `glm20MeasureApplyAdmitMass_correlatedStandardGaussian_regular_diagonal`,
   giving continuity, strict decrease, and both endpoint limits for the
   nondegenerate correlated-Gaussian source-event mass.  The reusable
   `verticalUpperStripMass_pos_of_isOpenPosMeasure` lemma proves every
   concrete Proposition 3 selection core is positive as a nonempty vertical
   upper strip under this law; GLM20 exposes that as
   `glm20Proposition3SelectionCore_standardBivariate_pos`.
   From those nonatomic marginals, `lowerLeftRectangleMass_continuous_of_noAtoms_marginals`
   proves bivariate CDF continuity, instantiated as
   `standardBivariateGaussianCDF_continuous_of_rho_sq_le_one`.  The concrete
   Lemma 3 bivariate-selection continuity premise is now discharged by
   `paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_standardBivariate_selection_components_continuous`;
   strict antitonicity and endpoint limits for the displayed closed form remain
   the next analytic obligations if pursuing the CDF/Owen route directly.  The algebraic Step 3 diversity comparison is now proved by
   `paper_proposition3_underrepresented_iff_selection_core_ratio`: under the
   total-capacity identity and positive selection cores, `τ_B < π` iff the
   Equation (37) ratio `\tilde σ_B / \tilde σ_A < X_A / X_B` holds.  The
   preferred standard-bivariate wrapper
   `paper_proposition3_underrepresented_iff_selection_core_ratio_standardBivariate`
   discharges those positivity premises from the correlated-Gaussian law.  The
   stronger wrapper
   `paper_proposition3_full_policy_diversity_ratio_and_academic_merit_formulas_standardBivariate`
   returns that ratio criterion and the `λ` academic-merit comparison once the
   remaining original-source model identification and merit-scaling bridge
   identify the admitted academic-merit quantities with the displayed formulas.
   The standardized first-moment/Owen route is now proved directly:
   `paperProposition3OwenFirstMomentProductTailIntegral`,
   `paper_interface_proposition3_owenFirstMomentProductTailIntegral_eq`,
   `paperProposition3OwenFirstMomentIntegral`, and
   `paper_interface_proposition3_owenFirstMomentIntegral_eq` expose the
   product-tail identity and the unconditional upper-tail first-moment identity
   for the source-affine normal integrand.  The remaining issue is not this
   Gaussian integration-by-parts step; it is the source formula/scaling seam.
   `glm20Proposition3LambdaOwenFirstMomentFormula` encodes the upper-tail
   integration-by-parts expression with `1 - Phi(shifted)`, and
   `paper_interface_proposition3_lambda_owenFirstMomentFormula_eq_lambdaFormula_add_boundaryTerm`
   proves that it equals the displayed `lambda` plus the explicit boundary
   term
   `sigmaTilde^2 * b * phi(A) / (tau * sqrt(1+sigmaTilde^2 b^2))`.  Thus the
   displayed `lambda` cannot be treated as the direct upper-tail first-moment
   endpoint unless this boundary term is justified away or the source formula
   is corrected.  The audit theorem
   `paper_interface_proposition3_lambda_ne_owenFirstMomentFormula_of_nonzero_slope`
   proves the two formulas are unequal whenever `sigmaTilde`, `b`, and `tau`
   are all nonzero.  The wrapper
   `paper_interface_proposition3_full_policy_diversity_ratio_and_academic_merit_owenFirstMoment_formulas_standardBivariate`
   composes the verified upper-tail merit formula with the standard-bivariate
   diversity ratio, keeping the corrected formula available without conflating
   it with the displayed `lambda`.  Proposition 6 now has a formula-level diversity endpoint:
   `glm20Proposition6FullDiversityFormula` reuses the Proposition 3
   bivariate-normal admitted-share expression for `J1` under
   `(P_full,P_full)`, `glm20Proposition6SubDiversityFormula` encodes the
   no-test expression, and
   `paper_interface_proposition6_full_diversity_formula_eq_owenAffineSelectionMass`
   rewrites the full-policy expression to the same standardized source-affine
   Owen mass; the stronger wrapper
   `paper_interface_proposition6_full_diversity_formula_eq_correlatedStandardGaussian_verticalUpperStripMass`
   rewrites the same left-hand side to the concrete correlated-Gaussian
   vertical-strip event.  On the no-test side,
   `paper_interface_proposition6_sub_diversity_formula_eq_testFreeGroupBTail`
   proves that the displayed right-hand side is the group-B Gaussian upper tail
   at the displayed no-test cutoff, and
   `paper_interface_proposition6_j1_drops_test_iff_full_formula_lt_testFreeGroupBTail`
   rewrites the source "drop iff diversity improves" condition from that
   explicit tail identification to the paper's formula inequality.  The
   generated-row Proposition 6 route now also has paper-school endpoints
   `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_same_fallback_paper_schools`
   and
   `PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback_paper_schools`.
   These specialize the preferred generated standard-Gaussian diversity table
   to the concrete schools `J1`/`J2`, discharge `J1 != J2`, and return both
   the drop-test iff and the `(P_sub,P_full)` equilibrium iff/consequence.
   The remaining Proposition 6 work is only the actual-source-table
   identification if one insists on using pre-existing concrete diversity rows
   instead of the generated source-parameter rows; it is not bivariate/Owen
   mass algebra, no-test standardization, or school-deviation bookkeeping.  The
   Theorem 3 policy-pair statement is now source-shaped rather than opaque:
   `glm20Theorem3SubFullCondition`, `glm20Theorem3FullSubCondition`, and
   `glm20Theorem3FullFullCondition` encode the displayed inequalities
   (10)--(14), the exactly-one-group clause, and the positive cost-boundary
   functions; `glm20ExactlyOneOfTwo_iff_existsUnique_mem_pair` verifies that
   the exactly-one helper matches explicit uniqueness over `{A,B}`;
   `paper_theorem3_Kg_eq_offset_posterior_mean_tail` connects
   `K_g(q)` to the Lemma 1 test-free posterior-mean Gaussian law.
   `paper_theorem3_fullFull_condition_exists_boundary_functions_of_positive_costs`
   proves Theorem 3(iii)'s bare existential boundary-function statement at the
   abstract source-condition layer from positive group costs; the meaningful
   strategic task is deriving the paper's boundary functions from the model,
   not merely proving the existential.
   `paper_theorem3_two_school_academic_merit_source_conditions_of_i_ii_and_positive_costs`
   leaves only the two policy-pair equivalences in parts (i)--(ii), plus
   positive costs, as hypotheses.  The stronger composition wrapper
   `paper_theorem3_source_conditions_of_binary_policy_objective_conditions`
   starts from binary school objective comparisons and objective-inequality
   equivalences to the paper's conditions.  The preferred current wrapper is
   `paper_theorem3_source_conditions_of_proposition5_objective_bridges`: it
   factors those objective equivalences into the actual Proposition 5 proof
   seams, namely J1's part-(i) condition (10), J2's conditional conditions
   (11)--(12), J2's part-(ii) condition (13), and J1's conditional condition
   (14).  The reusable decreasing-threshold support
   `exists_threshold_of_continuous_strictAntiOn_Icc_crossing` and the GLM
   wrapper
   `paper_proposition5_cost_threshold_of_continuous_strictAntiOn_unit_interval`
   now formalize the source proof step that a continuous strictly decreasing
   merit term with opposite endpoint comparisons induces a positive
   normalized cost threshold `c_hat`.  The non-normalized paper-cost endpoint
   `paper_proposition5_cost_threshold_of_continuous_strictAntiOn_cost_interval`
   now gives the same conclusion directly on `[0,maxCost]`, for source
   intervals such as `[0,v_2]`.  This threshold argument has now been
   composed into the Proposition 5 school-deviation case splits:
   `paper_proposition5_part_i_school1_cutoff_objective_iff_exactly_one_cost_case_of_merit_crossings`
   constructs the part-(i) `J1` threshold from the exactly-one-group merit
   crossing; `paper_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case_of_low_merit_crossings`
   constructs condition (13)'s lower threshold from a supplied high-threshold
   ordering fact.  The helper
   `paper_proposition5_low_root_below_high_threshold_of_high_merit_at_low_root`
   reduces that ordering fact to showing the high-threshold merit comparison is
   still on the test-based side at the lower root.  The stronger wrappers
   `paper_proposition5_low_and_high_cost_thresholds_of_merit_crossings` and
   `paper_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case_of_low_and_high_merit_crossings`
   now construct both `c_hat'_g` and `c_hat''_g`, prove
   `c_hat'_g < c_hat''_g`, and prove the condition-(13) objective iff directly
   from the two monotone merit crossings.  The source-condition wrapper
   `paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings`
   composes that construction with the `K_g` mass/cutoff identities and the
   school-`J1` no-expansion/high-threshold formula, producing the full
   `(P_full,P_sub)` condition (13)--(14) objective pair; and
   `paper_proposition5_part_ii_school1_cutoff_objective_iff_no_expand_or_low_cost_of_merit_crossing`
   constructs condition (14)'s high threshold from the expanding-case merit
   crossing.  The formula-level variants
   `paper_proposition5_part_i_school1_cutoff_objective_iff_exactly_one_cost_case_of_merit_formulas`,
   `paper_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case_of_low_and_high_merit_formulas`,
   `paper_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case_of_low_merit_formulas`,
   and
   `paper_proposition5_part_ii_school1_cutoff_objective_iff_no_expand_or_low_cost_of_merit_formulas`
   further reduce the objective-to-merit comparison premises to equalities for
   the two displayed objective values; the first of these now covers the
   ordered lower/high threshold branch directly.  The part-(i)
   source-condition wrapper
   `paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_merit_crossings`
   now constructs condition (10)'s threshold, translates it through the
   `K_g` mass/cutoff identities, and combines it with the school-`J2`
   weighted-merit/no-tie bridge for conditions (11)--(12).  The new
   paper-level wrapper
   `paper_theorem3_source_conditions_of_proposition5_merit_crossings`
   constructs all three Theorem 3 cost-threshold functions from those
   Proposition 5 merit-crossing premises and derives the displayed
   source-shaped policy-pair conditions from the binary school-objective game.
   The equation (46) full/full
   test-taking payoff expression is encoded as
   `glm20StrategicTwoFullPolicyApplyPayoffValue`, and
   `paper_proposition5_twoFull_apply_expected_payoff_eq_equation46` proves the
   algebraic expansion from the expected-value expression to the displayed
   CDF formula.  The inverse-CDF step displayed as equation (47) is now proved
   by `paper_proposition5_equation47_cutoff_formula_of_twoFull_payoff_zero`,
   conditional only on the quantile argument lying in `(0,1)` and the payoff
   being zero.  The source's post-(47) monotonicity claim is now proved by
   `paper_proposition5_twoFull_apply_payoff_cutoff_strictMono_cost`: increasing
   the test cost strictly raises the full/full indifference cutoff.
   `paper_proposition5_twoFull_apply_payoff_strictMono_projectedSkill` proves
   the source's monotonicity claim directly from strict Gaussian CDF
   monotonicity and `0 < v2 < v1`.  The reusable crossing theorem
   `existsUnique_zero_and_nonneg_iff_of_continuous_strictMono_crossing` and the
   GLM wrapper
   `paper_proposition5_twoFull_apply_payoff_cutoff_existsUnique_of_crossing`
   now turn one negative and one positive value of equation (46) into the
   unique projected-skill cutoff and its upper-threshold application region.
   `paper_proposition5_twoFull_apply_payoff_cutoff_existsUnique_of_tail_limits`
   proves those crossing signs from the Gaussian CDF limits and
   `0 < cost < v1`; the preferred standard-normal endpoint is
   `paper_proposition5_standardGaussian_twoFull_apply_payoff_cutoff_existsUnique`.
   The next Proposition 5 case-analysis bridge is now proved:
   `paper_proposition5_condition10_iff_cost_and_fullFull_cutoff_case`,
   `paper_proposition5_condition13_iff_cost_and_fullFull_cutoff_case`, and
   `paper_proposition5_condition14_iff_fullSub_cutoff_case_or_low_cost`
   convert the displayed Theorem 3 mass inequalities into the cutoff cases
   used in the source proof, using the `K_g(q)` strict upper-tail
   monotonicity.  In paper notation, they prove
   `M_g(P_full,P_full) < K_g(q^*_{i,sub})` iff
   `q^*_{i,sub} < q^g_{full,full}`, and
   `M_g(P_full,P_sub) > K_g(q^*_{1,sub})` iff
   `q^g_{full,sub} < q^*_{1,sub}`.
   The source-shaped Theorem 3 wrapper has also been lifted to this cutoff
   proof language:
   `paper_theorem3_source_conditions_of_proposition5_cutoff_objective_bridges`
   composes the binary policy game, the Proposition 5 cutoff-form
   school-deviation objectives, and the mass/cutoff bridges into the displayed
   Theorem 3 conditions.  The school-`J1` part-(i) case analysis is now
   packaged in cutoff language by
   `paper_proposition5_part_i_school1_cutoff_objective_iff_exactly_one_cost_case`:
   the no-expanding-group case gives no deviation, the both-groups case is
   impossible, and the exactly-one-expanding-group cases reduce the deviation
   objective to the positive cost-threshold comparison.  The part-(ii) school
   `J2` analogue is also packaged by
   `paper_proposition5_part_ii_school2_cutoff_objective_iff_exactly_one_cost_case`,
   with the same no-group/both-groups/unique-group structure and the low/high
   cost-threshold qualifier.  The part-(ii) school `J1` branch is packaged by
   `paper_proposition5_part_ii_school1_cutoff_objective_iff_no_expand_or_low_cost`,
   which splits condition (14) into the no-expansion cutoff case and the high
   cost-threshold comparison.  The newer merit-crossing wrappers listed above
   should be preferred when proving the concrete Gaussian game: they leave
   objective-to-merit rewrites, endpoint crossings, the single
   high-merit-at-low-root comparison, and mass/cutoff identities as explicit
   analytic obligations instead of assuming threshold functions.  When an objective-to-merit rewrite is only a value-formula
   equality, use the newer `_of_merit_formulas` wrappers rather than proving a
   separate iff by hand.  When the paper derives cost-monotonicity through
   equation (47)'s cutoff, use
   `paper_proposition5_cost_merit_continuous_strictAntiOn_of_cutoff_strictMono`
   to compose a continuous/strictly increasing cost-to-cutoff map with a
   continuous/strictly decreasing cutoff-to-merit map.  The selected
   equation-(46) full/full cutoff is now proved strictly increasing on any
   cost domain by
   `paper_proposition5_twoFull_apply_payoff_cutoff_strictMonoOn_cost`, provided
   the selected cutoff satisfies the zero-payoff equation at every cost.  The
   school-`J2`
   part-(i) condition (11)--(12)
   bridge is now reduced by
   `paper_theorem3_source_conditions_of_proposition5_cutoff_and_school2_merit_bridges`:
   the surviving-group objective formula, the two-group `(P_sub,P_sub)` merit
   formula, the surviving-group mass condition, and a no-tie merit comparison
   are enough to recover the objective iff needed by the Theorem 3 wrapper.
   The highest-level paper-facing Theorem 3 alias now uses the generated
   source-family survivor-row wrapper, so condition-(11)--(12)'s survivor
   requirements are displayed source rows.  The named keep-test,
   raw-survivor, and feasibility-aware variants remain available for auditing
   lower layers.  The posterior cost-row route
   `PaperInterface.theorem3_two_school_academic_merit_posterior_cost_rows`
   is now the honest Theorem 3 surface for direct cost-indexed full-sub
   posterior rows: it removes the low/high based-row formula-identification
   premises by defining those rows as posterior upper-tail means, while still
   requiring the direct continuity, strict-antitone, endpoint-crossing,
   feasibility, and capacity premises.  Do not replace it with an `rfl`
   specialization of the selected equation-(46) wrapper unless the rows have
   first been proved to be the selected cutoff-indexed rows.
   The component-table variant
   `PaperInterface.theorem3_two_school_academic_merit_posterior_cost_rows_components`
   is the preferred review surface when using this route, because it states
   condition-(12)'s school-`J2` survivor obligations on the source component
   rows instead of generated feasible-surface rows.  The fixed-law adapter
   `PaperInterface.theorem3_two_school_academic_merit_fixed_law_posterior_cost_rows_components`
   should be used when the low/high posterior laws are fixed and cost only
   moves continuous, strictly antitone threshold maps; it removes the four
   explicit low/high row regularity premises from that component route.  The
   stronger zero-fallback alias
   `PaperInterface.theorem3_two_school_academic_merit_fixed_law_posterior_cost_rows_zero_fallback`
   also derives the school-`J2` expanding-group zero component rows from the
   source table, leaving only the two strict survivor-merit comparisons.
   The equation-(50) variant
   `PaperInterface.theorem3_two_school_academic_merit_equation50_fixed_law_posterior_cost_rows_zero_fallback`
   additionally instantiates the sub-full cost row with the displayed
   equation-(50) cutoff formula and derives its continuity/strict-antitone
   premises from global standard-Gaussian merit regularity.
   `PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback`
   is the cleaned review alias for that same route; it hides the internal CDF
   API, hazard certificate, and certificate-equality arguments.
   `PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_threshold_order_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test`
   is now the generated-table keep-test route for the common fixed-law case
   where endpoint crossings are proved as threshold-order comparisons.
   `PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_raw_survivor_merits`
   is now the public raw-row variant, and the compact
   `PaperInterface.theorem3_two_school_academic_merit` alias points to the
   threshold-order generated-table keep-test route.
   The companion
   `PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_j2_keeps_test`
   feeds the same strongest cost-row route from named school-`J2` keep-test
   predicates, extracting the two condition-(12) merit rows internally.
   Use `PaperInterface.theorem3_posterior_cost_row_regularity` to discharge
   the standard-Gaussian row continuity/strict-antitone assumptions whenever
   the cost-indexed family has a fixed posterior law and only the threshold
   changes continuously and strictly antitone in cost.  The paired alias
   `PaperInterface.theorem3_posterior_low_high_cost_row_regularities`
   packages the low/high full-sub rows together for this route.  The companion
   `PaperInterface.theorem3_posterior_low_high_endpoint_crossings` converts
   fixed posterior laws plus endpoint threshold-order comparisons into the four
   full-sub endpoint merit-crossing inequalities.  The Prop. 5(ii) objective
   bridge
   `PaperInterface.proposition5_fullSub_posterior_source_free_cost_row_objective_bridge_threshold_order`
   now composes this conversion through bundled full/sub affine threshold rows
   and bundled full/full capacity/cutoff rows, so source-shaped threshold and
   capacity facts can feed the fixed-law posterior cost-row objective route
   without restating the four Gaussian upper-tail merit inequalities or
   separate capacity-fill premises.  The weighted adapter
   `PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_prop5_threshold_order_bridge`
   then composes that threshold-order Prop. 5(ii) bridge with the
   standard-Gaussian Prop. 5(i) keep-test bridge.
   The best handoff target is now to prove the remaining concrete Gaussian
   merit-crossing, objective-formula, mass, and no-tie premises feeding those
   paper-level wrappers, not by restating the strategic-game theorem manually.
   The remaining strategic work is connecting the paper's two-school strategic
   applicant-pool expression to source applicant-mass functions for Proposition
   2, resolving the remaining Appendix D.6 source-to-standardized scaling
   bridge for Proposition 3's academic-merit formula and tying Proposition 6's
   verified formula/tail identities to the concrete source objective, plus
   proving those concrete Proposition 5
   school-deviation equivalences from the Gaussian two-school game.
8. Before pushing farther into later Section 5 endpoints, re-audit the earlier
   paper-order results.  Proposition 1 and Lemma 2 are closed at their canonical
   standard-Gaussian source surfaces; Theorem 1 still has the explicit
   low-capacity/interior-selectivity assumptions, now packaged in
   `GLM20Theorem1BarrierCanonicalSourceModel` and proved by
   `paper_theorem1_dropping_tests_with_barriers_canonical_standardGaussian_source_model`.
   The low-capacity domain itself is now proved nonempty by
   `theorem1_low_capacity_domain_nonempty`.
   Theorem 2's raw source model is now packaged in
   `GLM20Theorem2NoBarrierCanonicalSourceModel`; its proved source-model
   wrapper follows the main-text high-skill direction under the extra same-side
   assumption `subB < subA`. Keep that assumption visible in the DAG, README,
   and validation report.
9. Only after a named theorem is source-faithfully closed, update the README row
   from `conditional` to `formalized` or `formalized with caveat`.

## Reusable Library Seams

- Gaussian posterior mean/variance formulas for finite signal families.
- Positive-affine laws of posterior estimates.
- Gaussian CDF derivative wrappers for affine standardized upper tails.
- Doubled-log standard-normal density interfaces for admissions threshold
  comparisons.
- Standard-normal quantile inverse-CDF and tail-cutoff bridges:
  `StandardGaussianQuantileAPI.cdf_quantile` and
  `StandardGaussianQuantileAPI.le_standardTail_iff_le_quantile_one_sub` should
  be used directly for cost/value threshold-strategy proofs.
- Finite-mixture threshold capacity and selected-mean comparisons.
- Hazard-rate/truncated-normal certificates behind `StandardGaussianCDFAPI`,
  `GaussianHazardCertificate`, or `GaussianHazardInverseCertificate`.
- Standard-normal quantile and hazard-inverse interfaces for access-barrier
  threshold theorems.
- Mathlib-backed normal primitives:
  `EconCSLib.Foundations.Probability.GaussianMathlib` now provides
  `standardGaussianCDFAPI`, `standardGaussianQuantileAPI`,
  `standardGaussianTail_pos`, and the concrete `standardGaussianHazard`
  definition from `gaussianReal`/`gaussianPDFReal`.  Together with
  `GaussianMills`, it also provides the concrete
  `standardGaussianHazardInverseCertificate` for positive hazard thresholds.
- Blackwell/SSD finite-kernel bridges shared with later information-policy
  papers.

## Validation

```bash
lake build GLM20DroppingStandardizedTesting
latexmk -pdf -interaction=nonstopmode -halt-on-error DependencyDAG.tex
```

Run the DAG command inside this folder.  The current paper-facing validation
caveats are recorded in `FINAL_VALIDATION_REPORT.md`.  Stage only explicit
GLM20 paths when committing from the shared worktree.
