# GLM20 Final Validation Report

Status: in progress.  This file records paper-facing validation caveats that a
human reviewer should audit before marking the paper complete.

For a cold restart after a long pause, begin with
`START_HERE_NEXT_AGENT.md`; it lists the current validation commands, strongest
Section 5 wrappers, and proof seams that should not be reopened.

Latest handoff: `HANDOFF_2026-05-24.md`.  The current clean stopping point is
the generated source-family exactly-one-objective row package
`GLM20Proposition5ExactlyOneObjectiveSourceFamilyRows`, exposed through
`PaperInterface.proposition5_exactly_one_weighted_objective_bridge_source_family_policy_state_row_package`.
This is a Bayesian-game row-identification target, not a completed
Bayesian-game proof.

Wrapper-only adapters are now split into `PaperSurfaceWrappers.lean` when they
can import the large theorem ledger without needing to live inside it.  The
first such adapter is the bundled Section 5 binary-policy equilibrium
characterization `paper_section5_binary_policy_equilibrium_three_cases`,
plus the feasibility-aware variant
`paper_section5_binary_policy_feasible_equilibrium_three_cases`; these are
re-exported as `PaperInterface.strategic_equilibrium_three_cases` and
`PaperInterface.strategic_feasible_equilibrium_three_cases`.

## Source-TeX Audit

Audited against the cached arXiv TeX source on 2026-05-16.  The caveats below
remain valid.  Prefer these TeX files over `source.txt` for formulas:
`source_tex/model.tex`, `source_tex/theory.tex`,
`source_tex/proofs.tex`, and `source_tex/proofs_twoschools_revision.tex`.

## Theorem 1 Capacity-Domain Caveat

The Theorem 1 source-model endpoint is feasible but restricted to a
low-capacity/interior-selective regime.  The nonredundant capacity assumptions
are `2 * capacity < pi * gammaB` and
`2 * capacity < (1 - pi) * gammaA`, plus positivity.  These imply the separate
capacity-feasibility bound `capacity < (1 - pi) * gammaA`; Lean now records
this as `theorem1_capacity_lt_groupA_eligible_of_selectiveB_worst`.
The domain is nonempty under positive masses/access levels, proved by
`paper_interface_theorem1_low_capacity_domain_nonempty`.  Thus the Lean endpoint
proves the paper's comparative-static conclusion for the full access sweep when
capacity is less than half of each group's relevant eligible mass; it does not
by itself prove the theorem under only generic over-demandedness.

The TeX source still supports this caveat.  The model assumptions state
over-demandedness `C < (1 - pi) * gammaA + pi * gammaB` and selectivity
`C < 1/2` (`source_tex/model.tex:70-72`), while the Theorem 1 statement
requires only unequal precision with barriers (`source_tex/theory.tex:135-149`).
The proof restatement defines the barrier thresholds and monotonicity argument
without explicitly adding the stronger per-group half-mass assumptions
formalized by Lean (`source_tex/proofs.tex:624-665`).

## Theorem 2 High-Skill Direction Caveat

The cached source text appears internally inconsistent for Theorem 2(ii).

- Main statement/narrative: `source.txt` lines 1038-1040 and 4577-4581 say
  that above a high-skill threshold the individual-fairness gap "increases"
  after dropping the test, i.e. the expected reading is
  `I(q; P_sub) > I(q; P_full)`.
- Appendix proof: `source.txt` lines 5151-5156 and 5316-5319 conclude
  `I(q; P_full) > I(q; P_sub)` above the constructed threshold, and explicitly
  say the individual-fairness gap decreases.

Lean treats the main-text direction as the paper-facing theorem.  The
main-text direction is proved in
`paper_interface_theorem2_high_skill_individual_fairness_gap_sub_gt_full_source_surface_of_precision_order`
under the additional assumption `subB < subA`: after dropping the test, the
remaining features still give group A higher total precision than group B.
This assumption matches the model/prose convention that features are less
informative for group B than group A, but it is not explicit in the theorem
statement.  The proof uses the reusable Gaussian left-tail dominance lemma
`standardGaussianCDF_affine_leftTail_lt_mul_eventually_of_slope_lt`.

The source-model theorem
`paper_theorem2_dropping_tests_without_barriers_standardGaussian_source_model_appendix_direction`
now formalizes the corrected main-text direction from the main-text precision
order `subB < subA`; the name is retained only as a compatibility alias for
older ledgers.  The theorem-facing wrappers in `ProofInterface.lean` now follow
the same main-text route.  Thus the appendix proof has a direction assumption
error relative to the prose setting: under the crossed order it derives
`I(q; P_full) > I(q; P_sub)`, which is the opposite of the main-text claim.
Lean also records that the two eventual high-skill directions cannot both hold
for the same source surface:
`paper_interface_theorem2_eventual_high_skill_gap_directions_inconsistent`.

The TeX source still supports this caveat.  The gap is defined as group-A
admission probability minus group-B admission probability
(`source_tex/model.tex:47-50`).  The Theorem 2 statement says the gap
"increases" for sufficiently high skill after dropping the test
(`source_tex/theory.tex:184-186`), but the appendix proof defines the high-skill
threshold and concludes `I(q; P_full) > I(q; P_sub)`, saying the gap decreases
(`source_tex/proofs.tex:559-596`).

## Proposition 3 Lambda-Scaling Caveat

The standardized first-moment/Owen identity needed for the full-policy
strategic academic-merit formula is proved, but the expression it yields is
not literally the displayed `lambda` formula in the source.  The source TeX
display includes the final `+ Phi(...) * sigmaTilde^2 * phi(qFull) / tau`
boundary term (`source_tex/proofs.tex:958-962`).  The mismatch recorded in Lean
is different: the verified upper-tail first-moment calculation uses
`1 - Phi(shifted)` in the first Owen boundary term, while the displayed source
formula uses `- Phi(shifted)`.  Lean records the resulting missing constant
term in
`paper_interface_proposition3_lambda_owenFirstMomentFormula_eq_lambdaFormula_add_boundaryTerm`
and proves non-equality under ordinary nonzero assumptions in
`paper_interface_proposition3_lambda_ne_owenFirstMomentFormula_of_nonzero_slope`.
Before marking Proposition 3/4 academic-merit consequences complete, a human
should decide whether the source formula needs correction or whether an
additional model-side scaling convention eliminates that boundary term.

The TeX source still supports this caveat.  The displayed `lambda` formula is
at `source_tex/proofs.tex:953-964`; the proof appeals to Owen's first-moment
identity and evaluates the upper-tail integral at
`source_tex/proofs.tex:1046-1075`.  The Lean audit is specifically about the
missing top-end contribution in that upper-tail evaluation, not about the
separate second boundary term that is visibly present in the source formula.

## Section 5 Strategic-Model Caveat

The formalization now exposes Section 5 through source-shaped wrappers for
Lemma 3, Proposition 2, Proposition 5, Proposition 6, and Theorem 3.  The
remaining open obligations are not generic Gaussian calculus: they are the
concrete two-school strategic applicant-pool and school-objective
instantiations.  In particular, the next proof should feed concrete
mass/objective/no-tie facts into the existing Proposition 5 and Theorem 3
wrappers rather than introducing a new certificate layer.  Proposition 5 now
has the typed source-condition surface
`PaperInterface.proposition5_strategic_academic_merit_source_conditions`, plus
the existential-threshold surface
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists`,
the packaging bridge
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_from_objective_bridges`
and its existential-threshold analogue, with positive-cost and full/full
cost-family variants,
plus rich-bridge adapters that strip the current Proposition 5 threshold side
facts before packaging the existential source surface,
the weighted-surface reverse adapter
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_weighted_surface_theorem3_source_conditions_exists`
for recovering Proposition 5 directly from already-proved Theorem 3 source
conditions on the paper's weighted academic-merit binary surface,
with
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_weighted_surface_rich_theorem3_source_conditions_exists`
available when that Theorem 3 existential also carries threshold/root witness
facts,
and the feasible-surface reverse adapter
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_feasible_weighted_surface_theorem3_source_conditions_exists`
for the current feasible Section 5 surfaces.  Its rich inferred-extra variant
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_feasible_weighted_surface_rich_theorem3_source_conditions_exists_inferred_extra`
is the preferred route from the compact Theorem 3 packages; it leaves only the
current-pair and unilateral-deviation feasibility facts exposed before
recovering Proposition 5's ordinary objective-comparison source predicate,
and the policy-state sub/full mass-feasibility specialization
`PaperInterface.proposition5_strategic_academic_merit_source_conditions_exists_from_policy_state_subFull_mass_feasible_surface_theorem3_source_conditions_exists`
discharges all definitional feasibility facts, leaving only school `J2`'s
condition-(11) sub/full mass-fill predicate visible.  The rich inferred-extra
variant with the same prefix is the closest adapter from the current rich
Theorem 3 packages on that concrete surface.  When the source route carries the
full `GLM20Theorem3J2SurvivorRows` bundle, the
`..._of_j2_survivor_rows` adapters discharge that remaining feasibility
predicate from the bundled mass-fill rows, while retaining the same ordinary
Proposition 5 objective-comparison target.  When the source route exposes a
school-`J2` keep-test pair instead, the `..._of_base_j2_keep_test_pair` and
`..._of_source_family_j2_keep_test_pair` adapters extract condition-(11)'s two
mass-fill rows directly from base-table or generated-table keep-test pairs
before the same Proposition 5 composition,
and the Theorem 3 handoff bridge
`PaperInterface.theorem3_from_proposition5_strategic_academic_merit_source_conditions`.
The generated-table keep-test Theorem 3 endpoint itself is not yet a closed
Proposition 5 source-condition package: it still awaits the objective-row
identifications for the full/full, sub/full, and full/sub admitted-merit rows.
Those twelve branch-conditioned row facts are now bundled by
`GLM20Proposition5ExactlyOneObjectiveSourceFamilyRows`; once the Bayesian-game
layer proves that package, the generated-table weighted-objective branch
algebra follows from the public packaged bridge named above.
The current
paper-facing Theorem 3 alias uses the standard-Gaussian fixed-law posterior
cost-row route with equation-(50) sub-full regularity, the zero-fallback
school-`J2` source table, strict condition-(12) survivor merit rows,
bundled sub/full affine tail rows, bundled full/sub affine threshold rows,
bundled source cost bounds, and bundled full/full capacity/cutoff rows.  Thus
direct full-sub merit-order assumptions, cost-indexed based-row formula
premises, generated keep-test predicates, separate scalar cost-interval rows,
separate endpoint threshold-order rows, separate full/full capacity/fill
premises, and internal Gaussian API parameters are no longer visible on the
compact theorem surface.
The compact Theorem 3 paper-facing alias now
uses `PaperInterface.theorem3_two_school_academic_merit` through
`paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds`.
This keeps the public row requirements in one
`GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare`
package, including the population-share domain `0 < pi < 1`; the older
four-row public route, separated-`hpi` route, and scalar-component route
remain exposed for audit as
`PaperInterface.theorem3_two_school_academic_merit_survivor_rows_public_rows`,
`PaperInterface.theorem3_two_school_academic_merit_strict_survivor_public_rows`
and
`PaperInterface.theorem3_two_school_academic_merit_fullSub_generated_rows_scalar_components`.
The survivor-row route also has
`PaperInterface.theorem3_two_school_academic_merit_fullSub_prior_precision_rows`,
which constructs the full/sub generated-row package internally from primitive
prior mean, prior variance, total precision, affine-threshold, and cost-bound
rows.
The feasibility-aware strict-survivor counterpart is
`PaperInterface.theorem3_two_school_academic_merit_strict_survivor_prior_precision_rows`.
The generated-table keep-test route remains available as the same compact
support surface
`PaperInterface.theorem3_two_school_academic_merit_source_family_keep_test_surface`;
`PaperInterface.theorem3_source_family_j2_keep_test_pair_of_survivor_rows`
is the direct support bridge from the four substantive condition-(11)--(12)
survivor mass/strict-merit facts to that generated keep-test pair, and
`PaperInterface.theorem3_public_rows_with_population_share_of_source_family_j2_keep_test_pair`
packages that keep-test pair into the compact public-row premise.  When the
full/sub generated-row package is not already available, use
`PaperInterface.theorem3_public_rows_with_population_share_of_source_family_j2_keep_test_pair_and_fullSub_prior_precision_rows`;
it builds the full/sub generated rows from primitive prior mean, prior
variance, total precision, affine threshold, and cost-bound rows before
constructing the same public-row premise.
`PaperInterface.theorem3_two_school_academic_merit_source_family_keep_test_fullSub_prior_precision_rows`
then feeds those primitive rows directly into the full paper-facing Theorem 3
endpoint, so callers no longer need to preconstruct the public-row package
outside the theorem wrapper.
Use
`PaperInterface.theorem3_source_conditions_exists_from_rich_theorem3_source_conditions_exists`
when a downstream bridge only needs the source-condition triple and the
Theorem 3 route also returns threshold/root/order witnesses.
`PaperInterface.theorem3_j2_survivor_rows_components` unpacks the bundled
source-row condition for audit;
the previous base component-table route remains available as
`PaperInterface.theorem3_two_school_academic_merit_base_table_j2_keeps_test`.
The older abstract Gaussian-tail-law route remains available as
`PaperInterface.theorem3_two_school_academic_merit_gaussian_tail_mean_rows`. The
direct ordered-merit route remains available as
`PaperInterface.theorem3_two_school_academic_merit_ordered_fullSub`.  The
compact Proposition 5(i) support alias now
exposes the corresponding equation-(50) source-form wrapper with
school-`J2`'s survivor requirements bundled as
`GLM20Theorem3J2SurvivorRows`, with the paper's named groups, named schools,
and population-share row fixed internally. Proposition 6 can discharge school
`J2`'s weak no-deviation condition from a pointwise fallback equality.
`PaperInterface.theorem3_subFull_j2_keeps_test_iff_survivor_components`
records the exact equivalence between each raw condition-(11)--(12)
survivor mass+merit pair and the named condition that school `J2` keeps the
test for the surviving group; the companion
`PaperInterface.theorem3_subFull_j2_keeps_test_of_survivor_components`
uses the forward direction for callers that already have the raw component
pair.
The full-sub ordered-merit seam has a new Gaussian bridge:
`paper_interface_proposition5_fullSub_ordered_merits_of_gaussian_tail_mean_formulas`
proves the direct ordered-merit assumptions from Gaussian upper-tail-mean
formulas plus scale/threshold comparisons, and
`paper_interface_proposition5_low_and_high_cost_thresholds_of_selected_twoFull_merit_crossings_interval_of_gaussian_tail_mean_formulas`
feeds that bridge into the selected equation-(46) threshold construction.
The posterior-family source-free variants
`paper_interface_proposition5_fullSub_ordered_merits_of_posterior_mean_source_free_families`
and
`paper_interface_proposition5_high_merit_at_low_root_of_posterior_mean_source_free_families`
now generate the low/high test-free full-sub merit rows directly from source
families.
The paper-facing Theorem 3 alias now points at
`paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds`,
which carries the fixed-law posterior cost-row reduction through the current
strongest route with standard-Gaussian internals specialized, school-`J2`
condition-(12) stated as the bundled
`GLM20Theorem3J2StrictSurvivorMeritRows`,
full/sub generated rows stated as `GLM20Theorem3FullSubGeneratedRows`, and
cost-domain and population-share requirements bundled as source rows.
The additional cost-row route
`PaperInterface.theorem3_two_school_academic_merit_posterior_cost_rows`
now lifts posterior source-family full-sub rows into the two-interval Theorem 3
endpoint directly.  It removes the previous `hfullSubLowBasedFormula` /
`hfullSubHighBasedFormula` premises at that route by making the cost-indexed
based rows definitional posterior upper-tail means, while leaving the honest
continuity, strict-antitone, endpoint-crossing, feasibility, and capacity
premises visible.
`PaperInterface.theorem3_two_school_academic_merit_posterior_cost_rows_components`
is the preferred paper-review alias for that route: it keeps the same
posterior cost rows and additionally states condition-(12)'s school-`J2`
survivor obligations as source component rows.
`PaperInterface.theorem3_two_school_academic_merit_fixed_law_posterior_cost_rows_components`
is the stronger standard-Gaussian fixed-law component route: fixed low/high
posterior laws plus regular threshold maps now discharge the four explicit
low/high row regularity premises before invoking the component endpoint.
`PaperInterface.theorem3_two_school_academic_merit_fixed_law_posterior_cost_rows_zero_fallback`
adds the zero-fallback source table on top of that route, so the school-`J2`
expanding-group zero rows are definitional and the visible survivor side is the
paper's base source-row inequalities.
`PaperInterface.theorem3_two_school_academic_merit_equation50_fixed_law_posterior_cost_rows_zero_fallback`
also instantiates the sub-full cost row with the displayed equation-(50)
cutoff formula and derives its continuity/strict-antitone premises from global
standard-Gaussian merit regularity.
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback`
is the same strongest route with the internal CDF API, hazard certificate, and
certificate-equality arguments specialized away for paper review.
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_raw_survivor_merits`
further exposes the survivor-merit assumptions as unconditional paper rows;
the generated-table keep-test variant
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test`
converts named keep-test predicates on the generated source-family table into
the same base-table survivor rows.  The threshold-order companion replaces the
four endpoint merit-crossing assumptions by fixed-law threshold-order
comparisons.  The cutoff-order companion also derives the two full/full
capacity-fill premises from `fullFullCutoff g <= q_iSub`.  The affine-threshold
companion further derives the full-sub based-threshold regularity premises from
positive affine slopes, and the compact
`PaperInterface.theorem3_two_school_academic_merit` alias now points to the
source-row companion, where condition-(11)--(12) is bundled as
`GLM20Theorem3J2SurvivorRows` and converted into the generated-table
keep-test pair internally.
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_fixed_law_posterior_cost_rows_zero_fallback_j2_keeps_test`
is the parallel support alias when those survivor-merit rows are being supplied
through named school-`J2` keep-test predicates.
`PaperInterface.theorem3_posterior_cost_row_regularity` supplies the
standard-Gaussian fixed-law regularity lemma for the remaining row
continuity/strict-antitone premises, and
`PaperInterface.theorem3_posterior_low_high_cost_row_regularities` supplies the
paired low/high version used by the full-sub cost-row route.  The
`PaperInterface.theorem3_posterior_low_high_endpoint_crossings` helper derives
the four full-sub endpoint merit-crossing inequalities from fixed posterior
laws and endpoint threshold-order comparisons.
The feasibility-aware support route also has a named-keep-test endpoint,
`paper_interface_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval_of_j2_keeps_test`,
while the raw survivor-merit endpoint remains available separately.
The raw survivor-row Gaussian variant
`PaperInterface.theorem3_two_school_academic_merit_gaussian_raw_survivor_components`
keeps the same Gaussian merit-order derivation while exposing condition-(12)'s
survivor mass and survivor-merit comparisons as source-row inequalities.
The generated source-family policy-state rows are now exposed in the compact
interface as `PaperInterface.theorem3_source_family_policy_state_table_rows`,
and the two school-`J2` keep-test predicates are bundled by
`PaperInterface.theorem3_subFull_j2_keep_test_pair_iff_survivor_components`.
The compact Proposition 6 paper-surface bundle
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_fallback_eq`
now returns both `J1`'s strict drop-test iff and the weak `(P_sub,P_full)`
equilibrium iff on the same generated standard-Gaussian diversity table; the
direct consequence alias
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium`
now packages the strict displayed inequality into both conclusions through the
preferred same-fallback generated-row route with the paper's concrete
group/school names fixed internally.  The
exact generated-row same-fallback bundle
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_same_fallback`
returns both iff statements while discharging `J2`'s fallback equality by
using the sub/sub row as the ordinary sub/full fallback row.  The source-row
aliases also now have `_paper_groups_schools` variants for exact, same-fallback,
and direct-consequence checking on actual four-row source tables.  The
same-fallback variant
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback`
removes the explicit pointwise fallback-equality argument in the common table
shape.  The paper-school specializations
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_same_fallback_paper_schools`
and
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback_paper_schools`
fix the school type to the paper's `GLM20School` names and discharge
`J1 != J2` internally.  The stronger source-row consequence
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows`
now gives the exact drop-test iff and equilibrium iff on an actual four-row
diversity table.  The source-row same-fallback aliases
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows_same_fallback`
and
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_same_fallback`
discharge school `J2`'s weak no-deviation premise by row equality.  The
generated-sub/full source-row aliases
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback`
and
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_generated_subFull_same_fallback`
also remove the separate school-`J1` sub/full source-row identification by
constructing that row from the source-parameter formula.  The generated-row
source aliases
`PaperInterface.proposition6_drop_iff_and_subFull_equilibrium_source_rows_generated_rows_same_fallback`
and
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_generated_rows_same_fallback`
also generate the full/full row, so there is no remaining school-`J1` row
identity premise when the actual table uses the displayed generated source
rows; the `_paper_groups_schools` variants specialize the paper names
internally.  The direct
consequence alias
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows`
packages school `J2`'s weak no-deviation inequality, the two school-`J1`
source-formula row identifications, and the strict displayed source-parameter
inequality into both conclusions.
The direct policy-state source-formula aliases
`PaperInterface.proposition6_policy_state_standardGaussian_drop_iff_source_parameter_formulas`,
`PaperInterface.proposition6_policy_state_standardGaussian_subFull_equilibrium_iff_source_parameter_formulas`,
and
`PaperInterface.proposition6_policy_state_standardGaussian_strict_inequality_implies_subFull_equilibrium`
now expose the same Proposition 6 source-parameter formulas without the
generated-row detour, specialized to the paper's `GLM20Group`/`GLM20School`
names.  The `_generic_groups_schools` aliases preserve the older abstract
audit surface.  The source-parameter value/row helpers
`PaperInterface.proposition6_source_parameter_full_diversity_value`,
`PaperInterface.proposition6_source_parameter_sub_diversity_value`,
`PaperInterface.proposition6_source_parameter_fullFull_diversity_row`,
`PaperInterface.proposition6_source_parameter_subFull_diversity_row`,
`PaperInterface.proposition6_source_parameter_fullFull_row_eq_source_value_at_j1`,
`PaperInterface.proposition6_source_parameter_subFull_row_eq_source_value_at_j1`,
`PaperInterface.proposition6_source_parameter_fullFull_row_eq_of_j1_formula`,
and
`PaperInterface.proposition6_source_parameter_subFull_row_eq_of_j1_formula`
are exposed for checking actual four-row table instantiations against the
displayed formulas.  The away-from-`J1` row helpers
`PaperInterface.proposition6_source_parameter_fullFull_row_eq_fallback_of_ne`
and
`PaperInterface.proposition6_source_parameter_subFull_row_eq_fallback_of_ne`
turn `J1 ≠ J2` into the generated-row fallback identity needed at school `J2`.
The concrete Proposition 6 generated-row source closure is now available as
`PaperInterface.proposition6_strict_inequality_implies_drop_and_subFull_equilibrium_source_rows_generated_rows_same_fallback_paper_groups_schools`;
it fixes the paper's group/school names, generates both relevant source rows,
and leaves only the displayed source-parameter inequality visible.
The compact Proposition 5(i) alias
`PaperInterface.proposition5_subFull_objective_bridge` now uses the
source-family fixed-pool bridge with school-`J2`'s survivor requirements
bundled as `GLM20Theorem3J2SurvivorRows` and the standard-Gaussian hazard
certificate, paper groups, paper schools, and population-share row specialized
internally.  The separate-component source-row variant
remains available as
`PaperInterface.proposition5_subFull_objective_bridge_source_family_survivor_components`;
the named keep-test variant remains
available as `PaperInterface.proposition5_subFull_objective_bridge_j2_keeps_test`;
the abstract raw-survivor variant remains available as
`PaperInterface.proposition5_subFull_objective_bridge_raw_survivor_conditions`;
the tail-mean and raw-fixed-pool variants remain available under
`PaperInterface.proposition5_subFull_objective_bridge_tail_mean_fixed_pool`
and `PaperInterface.proposition5_subFull_objective_bridge_raw_fixed_pool`.
The school-`J2` zero-fallback objective support endpoint
`PaperInterface.proposition5_school2_zero_fallback_objective_bridge` now
derives the branch-conditioned objective iff statements from the bundled
`GLM20Theorem3J2SurvivorRows` source premise on the generated zero-fallback
source table with the standard-Gaussian API and hazard certificate hidden from
the review surface, and with the paper groups/schools/population-share row
fixed internally.  The lower-level separate-component route remains
available as
`PaperInterface.proposition5_school2_zero_fallback_objective_bridge_base_survivor_components`.
The source-family keep-test adapter
`PaperInterface.theorem3_source_family_subFull_j2_keep_test_pair_iff_survivor_components`
rewrites the two named school-`J2` keep-test predicates on the generated
source table to the displayed condition-(11)--(12) survivor rows; the companion
`PaperInterface.theorem3_source_family_subFull_j2_keep_test_pair_iff_base_table_keep_test_pair`
connects those predicates to the base component table used by the strongest
Theorem 3 wrapper.
Proposition 5(ii)'s high-at-low-root ordering premise also has a direct support
lemma reducing it to high-vs-low test-free and test-based merit inequalities.
The selected equation-(46) weighted-objective bridge
`PaperInterface.proposition5_fullSub_gaussian_selected_objective_bridge`
now discharges that high-at-low-root premise from the Gaussian upper-tail-mean
formula package, so the selected Proposition 5(ii) objective iff no longer
exposes it as a standalone source assumption at the compact paper surface.
The compact interface also exposes
`PaperInterface.proposition5_fullSub_ordered_merits_from_posterior_mean_families`
for source-family posterior-mean laws,
`PaperInterface.proposition5_fullSub_high_at_low_root_from_posterior_mean_families`
for the corresponding root-side premise,
`PaperInterface.proposition5_fullSub_posterior_family_selected_objective_bridge`
for the full selected Proposition 5(ii) weighted-objective bridge,
`PaperInterface.proposition5_fullSub_posterior_source_free_cost_row_objective_bridge`
for the fixed-law posterior cost-row bridge with low/high row regularity
discharged internally,
`PaperInterface.theorem3_fullSub_fixed_law_rows_components` for deriving the
two full-sub posterior-law equality premises from the bundled primitive source
rows `GLM20Theorem3FullSubFixedLawRows`,
`PaperInterface.theorem3_fullSub_generated_rows` for carrying the full/sub
extra-noise positivity rows, fixed-law rows, affine threshold rows, and cost
bounds as one generated source package,
`PaperInterface.theorem3_fullSub_generated_rows_of_prior_precision_rows` for
constructing that generated package directly from primitive prior
mean/variance/precision rows plus affine threshold rows and cost bounds,
`PaperInterface.theorem3_keep_signal_rows_components` for unpacking the
generated keep-test signal bundle `GLM20Theorem3KeepSignalRows`,
`PaperInterface.proposition5_fullSub_posterior_source_free_cost_row_objective_bridge_threshold_order`
for the same bridge with the four endpoint merit inequalities discharged from
fixed posterior laws and endpoint threshold-order comparisons, and
`PaperInterface.theorem3_binary_objectives_from_fullSub_bridge` for feeding a
packaged full-sub Proposition 5(ii) threshold/objective bridge into Theorem 3,
and
`PaperInterface.theorem3_binary_objectives_from_subFull_and_fullSub_bridges`
for feeding packaged Proposition 5(i) and Proposition 5(ii) bridges together
into the binary-objective Theorem 3 source-condition theorem.  The
weighted-surface variants
`PaperInterface.theorem3_weighted_binary_objectives_from_subFull_and_fullSub_bridges`
and
`PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_subFull_keep_test_and_fullSub_bridge`
now apply the same composition on the paper's weighted academic-merit binary
surface; the latter generates the Proposition 5(i) sub-full objective bridge
from the standard-Gaussian keep-test route while accepting a packaged
Proposition 5(ii) bridge.
`PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_prop5_threshold_order_bridge`
uses the threshold-order fixed-law Proposition 5(ii) bridge directly.  The
paper-facing Proposition 5(ii) alias now packages the full/sub affine
threshold rows and full/full capacity/cutoff rows, so the weighted layer no
longer needs four endpoint merit-crossing assumptions, separate threshold
regularity rows, or separate capacity-fill premises when the source data are
threshold/cutoff facts.
`PaperInterface.theorem3_weighted_binary_objectives_from_standardGaussian_prop5_bridges`
goes one step further by generating that full-sub package from the
standard-Gaussian fixed-law posterior cost-row Proposition 5(ii) wrapper.
The top generated-table keep-test route also has
`PaperInterface.theorem3_two_school_academic_merit_standardGaussian_equation50_threshold_order_fixed_law_posterior_cost_rows_zero_fallback_source_family_j2_keeps_test`,
which carries the same threshold-order improvement through the standard-Gaussian
equation-(50) zero-fallback Theorem 3 surface.
The raw-survivor
Theorem 3 route also has
`PaperInterface.theorem3_two_school_academic_merit_posterior_raw_survivor_components`,
which instantiates the full-sub merit rows as source-family posterior-mean
laws while leaving condition-(12)'s survivor premises visible.
The compact Theorem 3 alias now consumes the Gaussian full-sub formula checks,
bundled fixed-law affine threshold rows, bundled cost bounds, bundled
capacity/cutoff rows, and the generated source-family school-`J2` keep-test
pair, with raw component-row routes kept as audit/support variants.
The compact paper interface now exposes the paper-facing Theorem 3 route where
school-`J2` condition (11)--(12) is bundled as
`GLM20Theorem3J2SurvivorRows`; the feasibility-aware variant remains available
as a lower-level audit route where condition-(11)'s survivor mass is carried by
the feasibility surface and the remaining strict survivor-merit comparisons can
be bundled as `GLM20Theorem3J2StrictSurvivorMeritRows`.  The compact
strict-survivor public route
`PaperInterface.theorem3_two_school_academic_merit_strict_survivor_merits`
passed `lake build GLM20DroppingStandardizedTesting.PaperInterface` on
2026-05-23.  The new helpers
`PaperInterface.theorem3_subFull_j2_strict_survivor_merit_rows_of_keep_test_pair`
and
`PaperInterface.theorem3_source_family_j2_strict_survivor_merit_rows_of_keep_test_pair`
extract that strict bundle from base-table or generated-table keep-test pairs.
The GLM20 Section 5 support layer now mirrors LG21's continuous-type
equilibrium pattern with `PaperInterface.strategic_equilibrium_ae_of_pointwise`
and proof-interface projections for a.e. student feasibility and best response.
`PaperInterface.proposition2_application_strategy_ae_unique` applies this
measure-zero boundary route to the two-school application-region strategy, and
`PaperInterface.proposition2_application_strategy_ae_unique_binary_choice`
states the same result with the reusable
`EconCSLib.NoProfitableBinaryChoiceDeviationAE` binary apply/not-apply premise.
`PaperInterface.proposition2_strategic_applicant_pool_masses_to_corrected_source_rows`
connects Lemma 3's Eq. (35) strategic applicant mass to the finite sum of
corrected Proposition 2 admitted-mass rows after Eq. (7)'s application cutoff
substitution.
`PaperInterface.proposition2_strategic_applicant_pool_masses_to_corrected_source_rows_paper_groups`
specializes this row to the paper's two named groups, exposing the group-A row
plus the group-B row directly.
The Proposition 2(iii) compact aliases now use corrected-source row wrappers,
so the formula-level diversity criteria no longer expose separate model-side
`hmore`/`hj1`/`hj2` row-identification assumptions on the human-facing surface.
`PaperInterface.proposition2_corrected_subEligible_mass_eq_testFree_tail`
also verifies that the corrected eligible-mass formula is the unnormalized
upper-tail probability for the test-free estimated-skill Gaussian law.
The Proposition 2(iv) compact alias now similarly specializes the
lower-academic-merit proposition and both academic-merit rows internally before
returning the displayed `lambda < kappa` comparison.  Proposition 3's compact
alias now specializes the displayed capacity, admitted-share rows, and
displayed `lambda` rows internally before returning Equation (37)'s diversity
ratio and the displayed academic-merit comparison.  Proposition 2(iv) also has
the public support alias `PaperInterface.proposition2_tau_normalization_lower_tail`,
which proves the source-prime lower-tail selection mass is `1 - tau_g` after
substituting the displayed `a'_g(q)` and `b'_g`; the source-parameter alias
`PaperInterface.proposition2_tau_normalization_source_parameters` additionally
substitutes the displayed `\tilde\sigma_g` and raw full-test cutoff.
`PaperInterface.proposition2_affine_total_mass_source_parameters` proves the
source-parameter affine total-mass partition, and
`PaperInterface.proposition2_strategic_applicant_pool_mass_add_lowerLeft_eq_affineTotal`
composes that partition with Lemma 3's applicant-pool mass after Eq. (7)'s
cutoff substitution.  These are interface strengthenings; the remaining caveats
are still the concrete strategic source-model identifications and the
displayed-`lambda` discrepancy above.

The TeX source still supports this caveat.  Proposition 2's statement and proof
use the two-school source applicant-pool identities and the `D_g`, `tau`, and
`kappa` formulas directly (`source_tex/proofs.tex:1210-1277`,
`source_tex/proofs.tex:1306-1365`).  Proposition 6 similarly states the
drop-test diversity criterion through the concrete full-policy bivariate
formula and test-free tail formula (`source_tex/proofs_twoschools_revision.tex:147-171`).
Those are the remaining concrete strategic-model identifications to connect to
the already verified formula bridges.
