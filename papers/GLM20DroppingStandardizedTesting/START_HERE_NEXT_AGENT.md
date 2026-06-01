# GLM20 Startup Note for Next Agent

Last updated: 2026-05-24.

This paper is paused mid-Section 5 at a clean Proposition 5 / Theorem 3
row-package boundary. Start here before reading chat history.  For the latest
proof-state ledger, read `HANDOFF_2026-05-24.md` next.  The older
`HANDOFF_2026-05-22.md` and `HANDOFF_2026-05-17.md` remain useful background
for the longer Section 5 push.

## First Commands

```bash
lake build GLM20DroppingStandardizedTesting.PaperInterface
lake build GLM20DroppingStandardizedTesting.PaperSurfaceWrappers
cd papers/GLM20DroppingStandardizedTesting
latexmk -pdf -interaction=nonstopmode -halt-on-error DependencyDAG.tex
```

Most recent proof check before this pause:

```bash
lake build GLM20DroppingStandardizedTesting.Proposition5SourceFamilyRows
lake build GLM20DroppingStandardizedTesting.ProofInterface
lake build GLM20DroppingStandardizedTesting.PaperInterface
```

all passed on 2026-05-24 after adding the packaged generated source-family
exactly-one-objective row bridge.  The latest closed seam is
`PaperInterface.proposition5_exactly_one_weighted_objective_bridge_source_family_policy_state_row_package`,
which consumes the new
`GLM20Proposition5ExactlyOneObjectiveSourceFamilyRows` package.  This is the
right Bayesian-game target, not a closed Bayesian-game proof: the game layer
still has to prove the twelve branch-conditioned posterior/admitted-merit row
identifications.

`PaperSurfaceWrappers.lean` is a small leaf module for compact human-facing
adapters; build it first for wrapper-only edits, then rebuild `PaperInterface`.

The worktree is shared and can be dirty. Stage only explicit GLM20 paths and
skill files you intentionally edit; do not use broad `git add .`.

## Source Files

- `source.pdf` and `source.txt` are the cached paper sources.
- `source_arxiv.tar` and `source_tex/` are local ignored arXiv source caches.
- Prefer `source_tex/proofs.tex` for formulas in Appendix D.6; the PDF text
  extraction is unreliable for several displayed equations.

## Current Closed Surface

- Lemma 1, Proposition 1, Lemma 2, Theorem 1, and Theorem 2 all have
  paper-facing standard-Gaussian source endpoints in `PaperInterface.lean`.
- Theorem 1 is green with an explicit low-capacity/interior-selectivity caveat:
  `2 * capacity < pi * gammaB` and
  `2 * capacity < (1 - pi) * gammaA`.
- Theorem 2's main-text high-skill direction is now proved in
  `paper_interface_theorem2_high_skill_individual_fairness_gap_sub_gt_full_source_surface_of_precision_order`
  under the extra assumption `subB < subA`, i.e. after dropping the test the
  remaining features still give group A higher total precision than group B.
  This matches the prose/model convention but is not explicit in the theorem
  statement.
- The Theorem 2 source-model wrapper now uses the main-text high-skill
  direction and main-text test-free precision order. The paper-facing alias is
  `paper_interface_theorem2_dropping_tests_without_barriers_standardGaussian_source_model`;
  the older `_appendix_direction` declaration name is only a compatibility
  alias. Appendix D.4's crossed-order derivation remains a source-text issue,
  not the paper-facing theorem.
- The theorem-facing Theorem 2 wrappers in `ProofInterface.lean` now also use
  the main-text direction.  Do not treat the crossed-order
  `I(q; P_full) > I(q; P_sub)` lemmas in `MainTheorems.lean` as paper-facing;
  they are retained only to document the Appendix D.4 source mismatch.
- `PaperSurfaceWrappers.lean` now contains the bundled Section 5
  binary-policy equilibrium characterization
  `paper_section5_binary_policy_equilibrium_three_cases`, re-exported in
  `PaperInterface.strategic_equilibrium_three_cases`, and the corresponding
  feasible-equilibrium bundle
  `PaperInterface.strategic_feasible_equilibrium_three_cases`.
- The current paper-facing Theorem 3 alias is
  `PaperInterface.theorem3_two_school_academic_merit`, implemented by
  `paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds`.
  This route generates fixed-pool merit rows from Gaussian source families,
  instantiates the sub-full row with equation (50), uses fixed-law posterior
  cost rows for the full-sub branch, derives the full/full capacity-fill and
  endpoint-crossing premises from cutoff/order rows, specializes the
  standard-Gaussian API and hazard certificate internally, and exposes only
  the strict condition-(12) school-`J2` merit rows through
  `GLM20Theorem3J2StrictSurvivorMeritRows`; condition-(11)'s survivor mass
  side is carried by feasibility/capacity rows.  Its public row premises and
  the source domain `0 < pi < 1` are carried as one
  `GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare`
  package.  The separated-`hpi` audit route is
  `PaperInterface.theorem3_two_school_academic_merit_strict_survivor_public_rows`.
  The older four-row survivor public wrapper remains available as
  `PaperInterface.theorem3_two_school_academic_merit_survivor_rows_public_rows`;
  the generated-row audit route is
  `PaperInterface.theorem3_two_school_academic_merit_strict_survivor_generated_rows`.
  The generated source-family-table keep-test
  variant remains available as
  `PaperInterface.theorem3_two_school_academic_merit_source_family_keep_test_surface`;
  the base component-table variant remains available as
  `PaperInterface.theorem3_two_school_academic_merit_base_table_j2_keeps_test`.
- The feasibility-aware support route
  `PaperInterface.theorem3_two_school_academic_merit_strict_survivor_merits`
  passed `lake build GLM20DroppingStandardizedTesting.PaperInterface` on
  2026-05-23.  It is now the scalar-premise audit route for the main Theorem 3
  alias: condition-(11)'s survivor mass side is carried by feasibility and the
  visible school-`J2` survivor input is only
  `GLM20Theorem3J2StrictSurvivorMeritRows`.  Lower-level feasibility-aware
  aliases remain available as
  `PaperInterface.theorem3_two_school_academic_merit_feasible_surface` and
  `PaperInterface.theorem3_two_school_academic_merit_feasible_surface_raw_survivor_merits`.
- Lemma 3 is closed at source-event applicant-mass surfaces, including
  correlated-standard-Gaussian regularity.
- Proposition 2 has the application-region/threshold-equilibrium layer and
  most lower-tail Owen, bivariate, kappa, mass-partition, and positivity
  algebra proved.
- Proposition 2 now also has the corrected conditional-source algebra needed
  for the Appendix D.6 eligible-mass substitution:
  `glm20Proposition2AHatConditionalSourceDenominator`,
  `glm20Proposition2AHatConditionalSource`,
  `glm20Proposition2SubEligibleUnnormalizedMassFormula`, and
  `glm20Proposition2AHatConditionalSourceDenominator_mul_selectionDenom_eq`.
  It also has
  `PaperInterface.proposition2_corrected_subEligible_mass_eq_testFree_tail`,
  which identifies the corrected eligible-mass formula with the unnormalized
  upper tail of the test-free estimated-skill Gaussian law.
  These are deliberately separate from the literal TeX-display definitions:
  the source display for `\hat a_g(q_a)` omits the
  `(priorPrecision + subPrecisionSum)` factor on `q_a`, while the preceding
  conditional-probability line implies the corrected affine numerator
  `mu * priorPrecision - q_a * (priorPrecision + subPrecisionSum)`.
  The compact Proposition 2(iii) aliases now use source-row wrappers
  (`paper_interface_proposition2_part_iii_diversity_criterion_above_high_cutoff_corrected_source_rows`
  and
  `paper_interface_proposition2_part_iii_diversity_criterion_between_cutoffs_corrected_source_rows`),
  so the old `hmore`/`hj1`/`hj2` diversity-row identification premises are not
  exposed on the human-facing surface.
  `PaperInterface.proposition2_strategic_applicant_pool_masses_to_corrected_source_rows`
  now connects Lemma 3's Eq. (35) strategic applicant mass to the finite sum of
  those corrected source admitted-mass rows after the Eq. (7) application
  cutoff substitution.
- The compact Proposition 2(iv) alias
  `PaperInterface.proposition2_academic_merit_lambda_kappa` now uses
  `paper_interface_proposition2_part_iv_lower_academic_merit_iff_lambda_lt_kappaBoundaryDensity_sourceTau_normalDensity_source_rows`,
  so the lower-academic-merit proposition and both academic-merit row
  identifications are specialized internally.
- The compact Proposition 3 alias `PaperInterface.proposition3_full_policy_formulas`
  now uses
  `paper_interface_proposition3_full_policy_diversity_ratio_and_academic_merit_formulas_source_rows`.
  It specializes the displayed capacity, admitted-share rows, and displayed
  `lambda` rows internally and returns the Equation (37) diversity ratio plus
  the paper's displayed `lambda` academic-merit comparison.
- Theorem 3 has source-shaped condition wrappers for inequalities (10)--(14),
  Proposition 5 merit-crossing/cutoff case-analysis bridges, and concrete
  interval endpoints:
  `paper_interface_theorem3_policyStateSubFullMassFeasibleSurface_subFull_fullSub_interval`,
  `paper_interface_theorem3_policyStateSubFullMassFeasibleSurface_fullFull_condition_of_positive_cost_interval`,
  and
  `paper_interface_theorem3_policyStateSubFullMassFeasibleSurface_source_conditions_of_i_ii_and_positive_cost_interval`.
  The current paper-facing alias
  `PaperInterface.theorem3_two_school_academic_merit` now uses
  `paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds`,
  which no longer exposes direct full-sub merit-order assumptions, low/high
  test-free full-sub merit row premises, cost-indexed based-row formula
  premises, explicit full/full capacity-fill premises, generated school-`J2`
  keep-test predicates, scalar cost-interval rows, separate affine threshold
  endpoint rows, separate capacity/cutoff rows, or internal Gaussian API
  parameters.  The remaining visible Theorem 3 survivor side is the bundled
  `GLM20Theorem3J2StrictSurvivorMeritRows` predicate; the older bundled
  `GLM20Theorem3J2SurvivorRows` public route is retained only as an audit
  variant.  The sub/full and
  full/sub cost domain is bundled as `GLM20CostBoundsBelow` and `GLM20CostBounds`; the
  affine sub/full tail row, affine full/sub threshold row, and full/full
  capacity/cutoff rows are bundled as source predicates.  The honest remaining
  route assumptions are the bundled fixed-law primitive rows
  `GLM20Theorem3FullSubFixedLawRows`, feasibility, and concrete source-family
  precision/threshold checks.  Use
  `PaperInterface.theorem3_subFull_j2_keeps_test_iff_survivor_components`
  to view each survivor mass+merit pair as the named condition that school
  `J2` keeps the test for the surviving group; use
  `PaperInterface.theorem3_subFull_j2_keeps_test_of_survivor_components`
  for the forward direction when the raw component pair is already proved.
  Use
  `PaperInterface.theorem3_subFull_j2_keep_test_pair_iff_survivor_components`
  when auditing both surviving-group keep-test predicates as one bundle.  On
  the generated source-family table, use
  `PaperInterface.theorem3_source_family_subFull_j2_keep_test_pair_iff_survivor_components`
  to rewrite those predicates directly to the displayed condition-(11)--(12)
  source rows.  Use
  `PaperInterface.theorem3_source_family_subFull_j2_keep_test_pair_iff_base_table_keep_test_pair`
  when a wrapper expects the same keep-test pair on the base component table.
  `PaperInterface.theorem3_source_family_policy_state_table_rows` exposes the
  generated mass rows, base admitted-merit rows, and fixed-pool admitted-merit
  rows used by the source-family policy-state table.
  The raw survivor-row variant remains available as
  `PaperInterface.theorem3_two_school_academic_merit_raw_survivor_components`.
  The older abstract Gaussian-tail-law keep-test route remains available as
  `PaperInterface.theorem3_two_school_academic_merit_gaussian_tail_mean_rows`.
  The direct ordered-merit route remains available as
  `PaperInterface.theorem3_two_school_academic_merit_ordered_fullSub`.
  The raw survivor-row Gaussian variant is
  `PaperInterface.theorem3_two_school_academic_merit_gaussian_raw_survivor_components`.
- `PaperInterface.theorem3_two_school_academic_merit_feasible_surface` exposes
  the alternative feasibility-aware route: condition-(11)'s survivor mass is
  carried by the feasibility surface, while the visible school-`J2`
  condition-(12) inputs can be bundled as
  `GLM20Theorem3J2StrictSurvivorMeritRows`.  Use
  `PaperInterface.theorem3_subFull_j2_strict_survivor_merit_rows_of_keep_test_pair`
  or
  `PaperInterface.theorem3_source_family_j2_strict_survivor_merit_rows_of_keep_test_pair`
  when those strict rows are currently packaged as base-table or generated-table
  keep-test predicates.
- `PaperInterface.strategic_equilibrium_ae_of_pointwise` and the
  `paper_interface_strategic_equilibrium_ae_*` projections mirror the LG21
  a.e. equilibrium route. Use them for continuous student-type statements when
  cutoff ties or support-boundary behavior should be discharged by no-atoms /
  measure-zero lemmas instead of pointwise tie assumptions.
- `PaperInterface.proposition2_application_strategy_ae_unique` applies that
  route to the Proposition 2 application-region strategy: a.e. best response
  plus zero mass on the low/high cutoff singletons gives a.e. equality to the
  displayed low/high region indicator, without pointwise tie-breaking premises.
  The companion public aliases
  `PaperInterface.proposition2_application_strategy_ae_unique_binary_choice`,
  `PaperInterface.proposition2_application_strategy_noProfitableBinaryChoiceDeviationAE`,
  `PaperInterface.proposition2_application_strategy_ae_unique_gaussian_student_law`,
  `PaperInterface.proposition2_application_strategy_ae_unique_strategic_equilibrium`,
  and
  `PaperInterface.proposition2_application_strategy_ae_unique_strategic_equilibrium_gaussian_student_law`
  now use the paper-readable cost-bound route `0 < c_g < v_1 - v_2`
  instead of exposing both inverse-CDF ratio assumptions.
- Proposition 5 now has a typed non-certificate source target:
  `PaperInterface.proposition5_strategic_academic_merit_source_conditions`.
  The existential-threshold version is
  `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists`,
  matching the source proof's construction of cost cutoffs.
  Use
  `PaperInterface.proposition5_strategic_academic_merit_source_conditions_from_objective_bridges`
  or
  `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_objective_bridges`
  once the sub/full objective bridge, full/sub objective bridge, and full/full
  boundary condition are available.  If the third component should be derived
  internally, use the positive-cost or full/full cost-family variants with the
  same prefix. If the Proposition 5 bridge theorem returns threshold side
  facts before the final objective iff, use
  `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_rich_objective_bridges_and_positive_costs`
  or the direct current-shape adapter
  `PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_three_subFull_six_fullSub_side_condition_bridges_and_positive_costs`;
  the same two adapters also have full/full cost-family variants. Then use
  `PaperInterface.theorem3_from_proposition5_strategic_academic_merit_source_conditions`
  or
  `PaperInterface.theorem3_source_conditions_exists_from_proposition5_strategic_academic_merit_source_conditions_exists`
  to feed that result into Theorem 3 without going through
  `GLM20StrategicAcademicMeritCertificate`.
- The compact Proposition 5(i) support alias
  `PaperInterface.proposition5_subFull_objective_bridge` now points to the
  equation-(50), capacity-fill, source-family fixed-pool/group-merit wrapper
  with school-`J2`'s survivor requirements bundled as
  `GLM20Theorem3J2SurvivorRows`.  It fixes the paper's named groups, named
  schools, and population-share row internally from `0 < pi < 1`; use
  `PaperInterface.proposition5_subFull_objective_bridge_generic_groups_schools`
  only for abstract audit work.  Use
  `PaperInterface.proposition5_subFull_objective_bridge_source_family_survivor_components`
  to inspect the four scalar source rows,
  `PaperInterface.proposition5_subFull_objective_bridge_j2_keeps_test`
  to view the same bridge through named school-`J2` keep-test predicates,
  `PaperInterface.proposition5_subFull_objective_bridge_raw_survivor_conditions`
  to inspect the same raw survivor obligations on an abstract policy surface,
  `PaperInterface.proposition5_subFull_objective_bridge_tail_mean_fixed_pool`
  to expose the Gaussian upper-tail-mean fixed-pool data, or
  `PaperInterface.proposition5_subFull_objective_bridge_raw_fixed_pool` to
  expose the two fixed-pool merit inequalities directly.
  `PaperInterface.proposition5_school2_zero_fallback_objective_bridge`
  packages the school-`J2` branch-conditioned objective iff from the bundled
  `GLM20Theorem3J2SurvivorRows` source premise when the zero-fallback source
  table makes the expanding group's admitted-merit row zero.  It also fixes
  the paper's named groups, named schools, and population-share row internally;
  use
  `PaperInterface.proposition5_school2_zero_fallback_objective_bridge_generic_groups_schools`
  only for abstract audit work.  Use
  `PaperInterface.proposition5_school2_zero_fallback_objective_bridge_base_survivor_components`
  only when auditing the four scalar survivor rows separately.
  The school-`J2` support aliases
  `PaperInterface.proposition5_school2_objective_bridge_zero_contributions`,
  `PaperInterface.proposition5_school2_objective_bridge_zero_contributions_and_merit_gt`,
  `PaperInterface.proposition5_school2_objective_bridge_zero_merits`, and
  `PaperInterface.proposition5_school2_objective_bridge_zero_merits_and_merit_gt`
  expose the lower-level source-proof route where the expanding group has zero
  weighted or admitted merit and the surviving group satisfies the displayed
  mass/merit condition.
- Proposition 6 has generated-row support endpoints whose `J2` weak
  no-deviation premise is discharged either by whole-row same fallback or by
  the more local pointwise fallback equality at `J2`:
  `paper_interface_proposition6_policyState_standardGaussian_source_parameter_diversity_rows_inequality_implies_subFull_equilibrium_of_J2_fallback_eq`.
  Proposition 2's a.e. application-region uniqueness route is exposed both as
  `PaperInterface.proposition2_application_strategy_ae_unique` and as the
  reusable-library variant
  `PaperInterface.proposition2_application_strategy_ae_unique_binary_choice`,
  which takes a `NoProfitableBinaryChoiceDeviationAE` apply/not-apply premise.
  Prefer the newer bundled public surface
  `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_fallback_eq`
  when checking Proposition 6, because it returns both `J1`'s strict drop-test
  iff and the weak `(P_sub,P_full)` equilibrium iff on the same generated
  standard-Gaussian diversity table.
  `PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium`
  is now the preferred direct consequence from the strict displayed inequality:
  it uses the same-fallback generated-row route and fixes the paper's concrete
  group and school names.  Use
  `PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_fallback_eq`
  only when auditing the looser explicit-fallback-equality surface.
  `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_same_fallback`
  is the exact same-fallback generated-row bundle: it returns both iff
  statements and discharges `J2`'s fallback equality by using the sub/sub row
  as the ordinary sub/full fallback row.  The paper-school specialization
  `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_same_fallback_paper_schools`
  additionally fixes the school type to `GLM20School` and discharges
  `J1 != J2` internally.
  Use
  `PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback`
  when the ordinary fallback sub/full diversity row is literally the sub/sub
  row, or
  `PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback_paper_schools`
  for the same direct consequence with the paper's concrete school names.
  Prefer
  `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows`
  for exact iff checking once the actual source-game diversity rows are
  available.  Use
  `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows_same_fallback`
  when school `J2`'s ordinary sub/full row is literally its sub/sub row; the
  matching direct consequence alias is
  `PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_same_fallback`.
  The `_paper_groups_schools` variants of these source-row aliases specialize
  both `Group` and `School` to the paper's concrete names.
  Prefer
  `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback`
  and its direct consequence
  `PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_generated_subFull_same_fallback`
  when the actual sub/full row is the displayed source-parameter row generated
  from the sub/sub fallback; these leave only the `J1` full/full source-row
  identity visible.  The `_paper_schools` variants specialize this exact route
  to `GLM20School` and discharge `J1 != J2` internally; the
  `_paper_groups_schools` variants also specialize the group type to
  `GLM20Group`.
  If the full/full row is also the displayed generated source-parameter row,
  prefer
  `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows_generated_rows_same_fallback`
  and
  `PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_generated_rows_same_fallback`;
  these remove the last school-`J1` row-identity premise and their
  `_paper_groups_schools` variants fix the paper's concrete group/school names
  internally.
  Its direct consequence alias,
  `PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows`
  uses the `J2` weak no-deviation inequality plus the two `J1` source-formula
  row identifications.  The direct policy-state formula aliases
  `PaperInterface.proposition6_policy_state_standardGaussian_drop_iff_source_parameter_formulas`,
  `PaperInterface.proposition6_policy_state_standardGaussian_subFull_equilibrium_iff_source_parameter_formulas`,
  and
  `PaperInterface.proposition6_policy_state_standardGaussian_strict_inequality_implies_subFull_equilibrium`
  expose the same source-parameter Proposition 6 formulas without routing
  through the generated-row table, specialized to `GLM20Group`, `GLM20School`,
  `glm20SchoolJ1`, and `glm20SchoolJ2`.  The
  `_generic_groups_schools` variants preserve the older abstract audit
  surface.  The value/row helpers
  `PaperInterface.proposition6_source_parameter_full_diversity_value`,
  `PaperInterface.proposition6_source_parameter_sub_diversity_value`,
  `PaperInterface.proposition6_source_parameter_fullFull_diversity_row`,
  `PaperInterface.proposition6_source_parameter_subFull_diversity_row`,
  `PaperInterface.proposition6_source_parameter_fullFull_row_eq_of_j1_formula`,
  and
  `PaperInterface.proposition6_source_parameter_subFull_row_eq_of_j1_formula`
  are exposed for auditing actual four-row source tables.  Use
  `PaperInterface.proposition6_source_parameter_fullFull_row_eq_fallback_of_ne`
  and
  `PaperInterface.proposition6_source_parameter_subFull_row_eq_fallback_of_ne`
  to turn `J1 ≠ J2` into generated-row fallback identities at school `J2`.
- Proposition 5(ii)'s awkward high-at-low-root premise now has a reusable
  support lemma:
  `paper_interface_proposition5_high_merit_at_low_root_of_test_free_lt_and_test_based_le`.
  Use it to prove the root-side ordering from direct high-vs-low test-free and
  test-based merit inequalities.  The stronger Gaussian source bridge
  `paper_interface_proposition5_fullSub_ordered_merits_of_gaussian_tail_mean_formulas`
  proves those ordered-merit premises from concrete Gaussian upper-tail-mean
  formulas plus scale/threshold comparisons, and
  `paper_interface_proposition5_low_and_high_cost_thresholds_of_selected_twoFull_merit_crossings_interval_of_gaussian_tail_mean_formulas`
  feeds that bridge through the selected equation-(46) low/high threshold
  construction.  The selected weighted-objective bridge
  `paper_interface_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_gaussian_tail_mean_formulas`
  now uses the same Gaussian tail-mean package to remove the standalone
  high-at-low-root premise from the Proposition 5(ii) objective iff. The
  source-family adapter
  `paper_interface_proposition5_fullSub_ordered_merits_of_posterior_mean_scale_families`
  specializes the same order package to `GaussianOffsetSignalFamily`
  posterior-mean laws, with
  `paper_interface_proposition5_high_merit_at_low_root_of_posterior_mean_scale_families`
  deriving the corresponding root-side premise. The selected objective bridge
  `paper_interface_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_scale_families`
  now uses posterior-mean source-family rows in the full Proposition 5(ii)
  weighted-objective iff. The adapter
  `paper_interface_theorem3_source_conditions_of_binary_policy_objective_conditions_of_subFull_objective_and_fullSub_objective_bridge`
  feeds packaged full-sub Proposition 5(ii) threshold/objective bridges into
  the binary-objective Theorem 3 source-condition theorem. The newer cost-row
  route
  `PaperInterface.theorem3_two_school_academic_merit_posterior_cost_rows`
  states the full-sub low/high rows directly as posterior source-family
  upper-tail means, removing the `hfullSubLowBasedFormula` /
  `hfullSubHighBasedFormula` identification premises at that two-interval
  route. Its component-table variant
  `PaperInterface.theorem3_two_school_academic_merit_posterior_cost_rows_components`
  is the preferred review surface because condition-(12)'s school-`J2`
  survivor obligations are source component rows. Do not try to force those
  cost rows through the selected
  equation-(46) wrapper with `rfl`; that selected wrapper is cutoff-indexed,
  while this route is cost-indexed.
  `PaperInterface.theorem3_two_school_academic_merit_fixed_law_posterior_cost_rows_components`
  is now the preferred standard-Gaussian fixed-law component route because it
  derives the low/high row regularity premises internally from fixed posterior
  laws and continuous, strictly antitone threshold maps.
  `PaperInterface.theorem3_two_school_academic_merit_fixed_law_posterior_cost_rows_zero_fallback`
  is even tighter when using the zero-fallback source table: it additionally
  derives the school-`J2` expanding-group zero rows, so the remaining survivor
  side is the paper's base source-row inequalities.
  `PaperInterface.theorem3_two_school_academic_merit_equation50_fixed_law_posterior_cost_rows_zero_fallback`
  is the strongest current route in this family: it also derives the sub-full
  cost row regularity from the displayed equation-(50) formula and global
  standard-Gaussian merit regularity.
  `PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback`
  is the cleaner review alias for that route because it specializes away the
  internal CDF API, hazard certificate, and certificate-equality arguments.
  `PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_threshold_order_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test`
  is the threshold-order generated-table keep-test companion; use it when the
  full-sub endpoint facts come as fixed-law threshold-order comparisons rather
  than four explicit Gaussian upper-tail merit inequalities.
  `PaperInterface.theorem3_posterior_cost_row_regularity` is available for
  discharging the standard-Gaussian row continuity/strict-antitone premises
  from fixed posterior laws plus continuous, strictly antitone threshold maps.
  `PaperInterface.theorem3_posterior_low_high_cost_row_regularities` packages
  that step for the two low/high full-sub rows together.  Use
  `PaperInterface.theorem3_posterior_low_high_endpoint_crossings` when the
  endpoint crossings are available as fixed-law threshold-order comparisons
  rather than four explicit Gaussian upper-tail merit inequalities.
  `PaperInterface.proposition5_fullSub_posterior_source_free_cost_row_objective_bridge_threshold_order`
  now consumes bundled full/sub affine threshold rows and bundled full/full
  capacity/cutoff rows in the Proposition 5(ii) objective bridge, so do not
  reintroduce the four endpoint merit inequalities, generic threshold
  regularity rows, or separate capacity-fill premises when the source
  threshold/cutoff facts are available.
  `PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_prop5_threshold_order_bridge`
  then composes that Prop. 5(ii) package with the standard-Gaussian Prop. 5(i)
  keep-test bridge at the weighted binary-objective layer.
  `PaperInterface.theorem3_source_family_j2_keep_test_pair_of_survivor_rows`
  remains the direct support theorem from the four condition-(11)--(12)
  survivor rows to the generated school-`J2` keep-test pair.  The top
  `PaperInterface.theorem3_two_school_academic_merit` surface now exposes the
  stricter public row package
  `GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare`;
  use `PaperInterface.theorem3_j2_survivor_rows_components` only when auditing
  the older four-row survivor package.
  At the lower binary-objective layer,
  `PaperInterface.theorem3_weighted_binary_objectives_from_subFull_and_fullSub_bridges`
  specializes the packaged Proposition 5(i)/(ii) adapter to the weighted
  academic-merit surface, and
  `PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_subFull_keep_test_and_fullSub_bridge`
  generates Proposition 5(i)'s sub-full package internally from the
  standard-Gaussian keep-test/equation-(50) route.
  `PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_prop5_bridges`
  also generates Proposition 5(ii)'s full-sub package internally from the
  fixed-law posterior cost-row route.
  The current top-level Theorem 3 alias points to the cutoff-order,
  threshold-order, affine-based-threshold fixed-law posterior cost-row
  source-row variant
  `paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds`,
  so do not reintroduce raw full-sub merit-order assumptions, standalone
  low/high test-free full-sub rows, explicit full/full fill assumptions,
  internal Gaussian API parameters, or generated keep-test predicates unless
  auditing an older support route explicitly.
  The named keep-test variant
  `PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_j2_keeps_test`
  uses the same cost-row route but extracts the two condition-(12) merit rows
  from semantic school-`J2` keep-test predicates on the base policy-state
  table.
  The generated-table support alias
  `PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test`
  first converts named keep-test predicates on
  `glm20Theorem3SourceFamilyPolicyStateTableSurface` to the base-table pair
  and remains available as the explicit-merit-crossing route. The compact
  top-level alias now points to the cutoff-order threshold-order affine-threshold
  raw-source-row companion named above.
  The raw-survivor route
  `paper_interface_theorem3_raw_survivor_conditions_of_posterior_mean_fullSub_merits`
  also instantiates the full-sub merit rows as source-family posterior-mean
  laws while leaving condition-(12)'s survivor premises explicit.

## Best Next Proof Seam

Continue Section 5 through the concrete strategic Gaussian game. The corrected
Theorem 2 source-model bundle already builds through `PaperInterface`, so do
not reopen it unless a later source audit finds a new mathematical issue.
The previous smallest Proposition 6 seam is now closed.  For an actual
source-game table whose sub/full and full/full rows are both generated from
the displayed source-parameter formulas, use:

- `PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_generated_rows_same_fallback_paper_groups_schools`
- `PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows_generated_rows_same_fallback_paper_groups_schools`

These wrappers fix the paper's concrete group and school names, generate both
school-`J1` diversity rows, and discharge school `J2`'s same-fallback
no-deviation premise internally.  The next useful proof work should feed the
concrete Proposition 5 objective bridges into the Theorem 3 source-condition
surface rather than adding more Proposition 6 row-identification wrappers.

After that, the highest value target is to feed concrete model facts into the
strongest current Theorem 3 wrappers:

- `paper_interface_theorem3_policyStateSubFullMassFeasibleSurface_source_conditions_of_i_ii_and_positive_cost_interval`
- `paper_interface_theorem3_policyStateSubFullMassFeasibleSurface_subFull_fullSub_interval`
- `paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_raw_survivor_merits`
- `paper_interface_standardGaussian_posterior_cost_row_regularity_of_fixed_law_threshold_strictAntiOn`
- `paper_interface_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval_of_posterior_mean_fullSub_cost_rows`
- `paper_interface_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_and_cutoff_fill_subFull_fullSub_interval_of_posterior_mean_fullSub_cost_rows`
- `paper_interface_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_iff`

The remaining premises are concrete Gaussian merit-crossing facts,
objective-value formulas, mass identities, zero-contribution/surviving-group
facts, and no-tie inequalities. Do not restate Theorem 3 from scratch; prove
the concrete inputs to these wrappers. Do not try to close Proposition 5 by
directly applying the generated-table keep-test Theorem 3 endpoint until those
objective-row identifications are supplied: that endpoint is still a curried
function over the same row-equality premises (`honlyA`/`honlyB` full/full vs
sub/full or full/sub admitted-merit rows), not a closed rich source-condition
package.  The keep-test/survivor adapters above only discharge the remaining
feasibility guard. For the full-sub low/high threshold
seam, first try to identify the low/high test-free and cost-indexed merits as
Gaussian upper-tail means and discharge the scale/threshold comparisons needed
by the Gaussian source bridge above.
Use
`PaperInterface.theorem3_fullSub_low_based_law_of_prior_precision_rows` and
`PaperInterface.theorem3_fullSub_high_based_law_of_prior_precision_rows` to
turn primitive prior-mean, prior-variance, and total centered signal-precision
rows into the fixed posterior-law equalities required by the compact
full-sub cost-row wrappers, or use
`PaperInterface.theorem3_fullSub_based_laws_of_prior_precision_rows` to
discharge both low/high equalities together.  If those raw rows are already
bundled, `PaperInterface.theorem3_fullSub_fixed_law_rows_components` unpacks
the source-row predicate `GLM20Theorem3FullSubFixedLawRows` into the two
posterior-law equalities.  If the source model supplies the primitive full/sub
rows separately, use
`PaperInterface.theorem3_fullSub_generated_rows_of_prior_precision_rows` to
construct `GLM20Theorem3FullSubGeneratedRows` directly from positive
extra-noise rows, prior mean/variance/precision equalities, affine threshold
rows, and full/sub cost bounds.  If the source model already presents the
full/sub generated rows as one package, use
`PaperInterface.theorem3_fullSub_generated_rows`; it bundles the full/sub
extra-noise positivity rows, fixed-law rows, affine threshold rows, and cost
bounds for the Theorem 3 / Proposition 5(ii) route.
For generated keep-test source families, use
`PaperInterface.theorem3_keep_signal_rows_components` to unpack
`GLM20Theorem3KeepSignalRows` into the positive extra-signal variance rows and
the school-specific threshold rows.  The support bridge
`PaperInterface.theorem3_public_rows_with_population_share_of_source_family_j2_keep_test_pair`
packages a generated source-family school-`J2` keep-test pair into the compact
public-row premise; use
`PaperInterface.theorem3_public_rows_with_population_share_of_source_family_j2_keep_test_pair_and_fullSub_prior_precision_rows`
when the full/sub generated rows should be built from raw primitive rows at
the same time.  If the goal is the full paper-facing Theorem 3 endpoint rather
than just the public-row package, use
`PaperInterface.theorem3_two_school_academic_merit_source_family_keep_test_fullSub_prior_precision_rows`;
it constructs the public-row package internally and then calls the compact
Theorem 3 alias.  Use
`PaperInterface.theorem3_two_school_academic_merit_fullSub_prior_precision_rows`
when the school-`J2` side is already bundled as survivor rows and the only
remaining packaging task is constructing the full/sub generated rows from raw
prior mean, prior variance, precision, affine-threshold, and cost-bound rows.
Use
`PaperInterface.theorem3_two_school_academic_merit_strict_survivor_prior_precision_rows`
for the feasibility-aware version with only strict school-`J2` survivor merit
rows visible.
If a downstream step needs only the three Theorem 3 source conditions from a
rich package, use
`PaperInterface.theorem3_source_conditions_exists_from_rich_theorem3_source_conditions_exists`
to strip the extra threshold/root/order witnesses.

For the Bayesian-game row-identification seam, target
`GLM20Proposition5ExactlyOneObjectiveSourceFamilyRows`.  It bundles the twelve
`honlyA`/`honlyB` posterior row equalities for the generated source-family
policy-state table.  Once it is proved, call
`PaperInterface.proposition5_exactly_one_weighted_objective_bridge_source_family_policy_state_row_package`
instead of passing twelve separate row facts through the flat source-family
bridge.

For the next Proposition 5 source-condition closure, target
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_feasible_weighted_surface_theorem3_source_conditions_exists`
when the route has already produced Theorem 3 source conditions on the
paper's feasible weighted academic-merit binary surface.  This reverse bridge
supplies the binary-policy objective equivalences from the surface itself, and
the visible extra assumptions are exactly the current-pair and unilateral
deviation feasibility facts needed to remove feasible-best-response guards.
If the available theorem returns extra threshold/root witness facts together
with the Theorem 3 source-condition triple, use
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_feasible_weighted_surface_rich_theorem3_source_conditions_exists_inferred_extra`
to strip those facts first without naming the extra predicate.  Use the older
plain weighted-surface bridge only for non-feasible surfaces.  If the surface
is the concrete policy-state sub/full mass-feasibility surface, use
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_theorem3_source_conditions_exists`
or its rich inferred-extra variant; then the only visible feasibility premise
is school `J2`'s sub/full condition-(11) mass-fill predicate.  If the source
route has the full `GLM20Theorem3J2SurvivorRows` bundle, use
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_theorem3_source_conditions_exists_of_j2_survivor_rows`
or its rich variant; `PaperInterface.theorem3_policy_state_subFull_j2_mass_feasible_of_survivor_rows`
discharges the concrete feasibility predicate from the two bundled mass-fill
rows.  If the source route instead exposes a school-`J2` keep-test pair, use
the `..._of_base_j2_keep_test_pair` adapters for the base policy-state table
or the
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_theorem3_source_conditions_exists_of_source_family_j2_keep_test_pair`
adapter and its rich variant for the generated source-family table;
`PaperInterface.theorem3_policy_state_subFull_j2_mass_feasible_of_base_j2_keep_test_pair`
and `PaperInterface.theorem3_policy_state_subFull_j2_mass_feasible_of_source_family_j2_keep_test_pair`
extract the same concrete feasibility predicate from condition-(11)'s
mass-fill half of the keep-test pair.  Use the rich-bridge/full-full-cost-family adapters only when the proof
is still at the separate Proposition 5(i)/(ii) bridge layer.  Do not use the
legacy
`paper_interface_proposition5_strategic_academic_merit` certificate endpoint
except as historical compatibility.

## Proposition 2 Next Seam

The lower-tail/kappa integration route, corrected-source standardization, and
corrected eligible-mass upper-tail bridge are already proved. Do not reopen
them. The paper-facing aliases in
`PaperInterface.lean` are:

- `PaperInterface.proposition2_diversity_above_high_cutoff`
- `PaperInterface.proposition2_diversity_between_cutoffs`
- `PaperInterface.proposition2_academic_merit_lambda_kappa`
- `PaperInterface.proposition2_corrected_subEligible_mass_eq_testFree_tail`
- `PaperInterface.proposition2_strategic_applicant_pool_masses_to_corrected_source_rows_paper_groups`
- `PaperInterface.proposition2_tau_normalization_lower_tail`
- `PaperInterface.proposition2_tau_normalization_source_parameters`
- `PaperInterface.proposition2_affine_total_mass_source_parameters`
- `PaperInterface.proposition2_strategic_applicant_pool_mass_add_lowerLeft_eq_affineTotal`
- `PaperInterface.proposition3_full_policy_formulas`

The supporting standardization bridges are
`glm20Proposition2AArgument_conditional_source_eq_subEligibleStandardization`
and
`glm20Proposition2SubEligibleUnnormalizedMassFormula_eq_conditional_affineArgument`;
the semantic upper-tail bridge is
`glm20Proposition2SubEligibleUnnormalizedMassFormula_eq_scaled_testFreeTail`.

The broader open work is the Appendix D.6 source-model identification: tying
the source applicant-pool and objective rows to the concrete two-school
Gaussian game.  The source-prime tau normalization
itself is now exposed by `PaperInterface.proposition2_tau_normalization_lower_tail`,
and the paper-parameter version with `\tilde\sigma_g` substituted is
`PaperInterface.proposition2_tau_normalization_source_parameters`; the
source-parameter affine total-mass substitution and its group-summed
applicant-pool composition are also public aliases.

## Do Not Reopen

- Do not reprove standard-normal CDF, derivative, quantile, Mills/hazard,
  mixture-tail cutoff, affine upper-tail derivative, or Owen lower-tail
  identities. They are in `EconCSLib.Foundations.Probability.*`.
- Do not trust `source.txt` for Appendix D.6 formulas when it disagrees with
  `source_tex/proofs.tex`.
- Do not spend time polishing `FINAL_VALIDATION_REPORT.md` again until either a
  named result closes or this paper is being paused again.

## Current Caveats to Preserve

- Theorem 1: low-capacity/interior-selectivity domain caveat.
- Theorem 2: main-text direction needs the extra test-free precision assumption
  `subB < subA`; Appendix D.4 has a crossed-order direction assumption error,
  but the paper-facing wrapper now follows the main-text assumptions.
- Proposition 3: displayed `lambda` formula differs from the verified
  first-moment/Owen expression by a boundary term under ordinary nonzero
  assumptions.
- Section 5: concrete strategic applicant-pool/objective instantiations remain
  conditional even though many formula and case-analysis bridges are proved.
