# Iterative Local Voting for Collective Decision-making in Continuous Spaces

## Source Version

- Paper: *Iterative Local Voting for Collective Decision-making in Continuous Spaces*
- Authors: Nikhil Garg; Vijay Kamble; Ashish Goel; David Marn; Kamesh Munagala
- Version formalized: JAIR 64 (2019), 315-355; published 2019-02-18
- Official URL: https://www.jair.org/index.php/jair/article/view/11358
- Public PDF: https://www.jair.org/index.php/jair/article/download/11358/26474/21047
- DOI: https://doi.org/10.1613/jair.1.11358
- Citation source: `citation.bib` from the Crossref DOI BibTeX endpoint
- Auxiliary source for TeX labels: arXiv:1702.07984v3, last revised
  2018-10-28, https://arxiv.org/abs/1702.07984

The JAIR PDF is cached locally as `source.pdf` and ignored by Git. The extracted
text cache is `source.txt`; it was generated with `mutool` because the local
`pdftotext` binary is the MiKTeX wrapper and refused to run before system setup.

## Paper-Facing Ledger

- Implementation theorem file: `GKGMM19IterativeLocalVoting/MainTheorems.lean`
- Human-facing theorem file: `GKGMM19IterativeLocalVoting/PaperInterface.lean`
- Proof-facing bridge file: `GKGMM19IterativeLocalVoting/ProofInterface.lean`
- Machine-readable status source: `GKGMM19IterativeLocalVoting/status.json`
- Outside-Lean proof plan: `GKGMM19IterativeLocalVoting/FORMALIZATION_PLAN.md`
- Final validation report: `GKGMM19IterativeLocalVoting/FINAL_VALIDATION_REPORT.md`
- Dependency DAG: `GKGMM19IterativeLocalVoting/DependencyDAG.tex`
- Rendered DAG: not generated in this pass; see the final validation report

`PaperInterface.lean` should be readable on its own: expose source formulas and
direct theorem statements there, with short proofs that call into
`MainTheorems.lean`. Do not mark a row `formalized` unless the Lean declaration
is closed and the remaining assumptions cell is `None`.
Keep the dashboard surface small: one row per paper-facing definition or named
result, not every helper theorem, certificate, or proof-route alias.

Use the controlled status vocabulary from `../../docs/STATUS.md`. Public-facing
rows should use `partially formalized` for results that remain conditional on
an external theorem, certificate, or proof boundary, and should name that
boundary in the final column rather than using `conditional` as a separate
status label.
Keep theorem/table content synchronized with `DependencyDAG.tex` node styles and
`MainTheorems.lean` declarations before marking a row `formalized`. Keep
`status.json` as the source of truth for review rows, artifact paths, and the
paper's top-level public status.

At the start of the paper, fill in the `FORMALIZATION_PLAN.md`
`Initial Outside-Lean Paper Audit` section before deep proof work. Read the
source, sanity-check every named result and formula-bearing displayed claim for
signs, constants, normalizations, quantifiers, domains, and dependencies, and
record suspected bugs, missing assumptions, formula ambiguities, and proof
strategy consequences. Alert the user early about any major issue. After that
source inventory and the first compact `PaperInterface.lean` skeleton exist,
run the smaller statement target-setting pass: populate `lean_to_tex_llm.json`,
populate `statement_match_llm.json`, and run
`python3 scripts/review_dashboard.py --paper GKGMM19IterativeLocalVoting --statement-precheck`.
Then run `python3 scripts/review_dashboard.py --paper GKGMM19IterativeLocalVoting
--assumption-precheck`: the statement judge is row-local and does not certify
that theorem premises are source assumptions or derived facts. Use this pass
only to correct theorem targets and premise provenance; do not update the DAG,
final validation report, human-review log, or review-surface audit just because
this early check ran.

At review boundaries, populate `lean_to_tex_llm.json` with context-free
Lean-to-TeX/prose translations generated from `PaperInterface.lean` alone. The
translator must preserve every visible variable, binder, hypothesis, domain
condition, equivalence direction, and conclusion; it must not summarize a theorem
as an endpoint label or omit conditions that appear in the Lean statement. New
tracked entries should use `{ "tex_statement": "...", "lean_statement_sha256":
"..." }`. Then populate `statement_match_llm.json` with an independent
no-context judgment of whether each translation matches the original full paper
statement, including all hypotheses, subparts, quantifiers, domains, constants,
normalizations, signs, inequality directions, and conclusions. A row may be
judged `matches` only if it is equivalent to the full source statement or to a
clearly identified source subpart; if the Lean translation is a conditional
wrapper, source-row package, omitted subclaim, weakened/strengthened statement,
or broad aggregate for several displayed formulas, the judge must mark
`mismatch` or `uncertain`. Include Lean, paper, and TeX statement digests plus
the judge model/agent name, validator type, validation timestamp, and any
validator comment. If the judge flags a mismatch or uncertainty, iterate on the
Lean statement before treating it as the paper theorem target. Run
`python3 scripts/review_dashboard.py --paper GKGMM19IterativeLocalVoting --precheck` before
handoff so missing/stale statement-audit rows are explicit.
If any paper-facing theorem takes a hypothesis that is not proved from prior
Lean declarations, declare that hypothesis in `Assumptions.lean`, list it in
`status.json` `review_surface.assumption_names`, and populate
`assumption_match_llm.json` with an independent judgment that it is a true
paper/source model assumption rather than a proof shortcut.
The repository audit follows paper-local helper chains recursively: a theorem
is not closed if any helper it depends on still consumes an unvalidated
certificate, source-row equation, hidden hypothesis, or proof-boundary premise.
Do not use `axiom`, `constant`, `opaque`, or unsafe declarations to bypass that
provenance boundary.
If the dashboard has more than 30 rows, also populate `review_surface_llm.json`
with a no-paper-context LLM audit that checks whether every dashboard row is a
paper-facing definition, formula, or named statement. At 120 or more rows, treat
the dashboard as oversized and curate `PaperInterface.lean` or
`status.json.review_surface.include_names` before broad human review.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Section 3 assumptions C1-C3 | `conditions_c123_formula` | formalized | `PaperInterface.lean` | None; source model conditions represented as a named assumption predicate; this is a source assumption, not a Lean-derived theorem |
| C1 convexity source | `c1_convex_solution_space_source_formula` | formalized | `PaperInterface.lean` | None; expands the source interpretation that C1 supplies the direct concrete `Convex` fact used by projection residual arguments |
| Theorem 1 norm pair `(2,2)` | `theorem1_norm_pair_l2_l2` | formalized | `PaperInterface.lean` | None; direct constructor for the source disjunction |
| Theorem 1 norm pair `(1,∞)` | `theorem1_norm_pair_l1_linf` | formalized | `PaperInterface.lean` | None; direct constructor for the source disjunction |
| Theorem 1 norm pair `(∞,1)` | `theorem1_norm_pair_linf_l1` | formalized | `PaperInterface.lean` | None; direct constructor for the source disjunction |
| Theorem 1 visible source certificate | `theorem1_visible_hypotheses_case_certificate_formula` | formalized | `PaperInterface.lean` | None; packages C1-C3, Lp utilities, Model A/B response, and a norm-pair case into the structured SSGM case certificate |
| Algorithm 1 radius schedule | `algorithm1_radius_formula` | formalized | `PaperInterface.lean` | None; pure formula row, no proof debt |
| Algorithm 1 radius tends to zero | `algorithm1_radius_tendsto_zero` | formalized | `PaperInterface.lean` | None; direct consequence of `r_t = r_0 / t` and mathlib's natural-at-top limit |
| Algorithm 1 squared radius summability | `algorithm1_radius_sq_summable` | formalized | `PaperInterface.lean` | None; uses mathlib p-series summability for the shifted positive time indices |
| Algorithm 1 radius partial-sum divergence | `algorithm1_radius_sum_tendsto_atTop` | formalized | `PaperInterface.lean` | None; uses mathlib harmonic-series divergence for `r_0 > 0` |
| Algorithm 1 radius non-summability | `algorithm1_radius_not_summable` | formalized | `PaperInterface.lean` | None; derived from positive-radius partial-sum divergence |
| Algorithm 1 radius SSGM step-size package | `algorithm1_radius_ssgm_step_size_conditions` | formalized | `PaperInterface.lean` | None; packages positivity, square summability, and divergent partial sums |
| Algorithm 1 local query set | `algorithm1_local_neighborhood_formula` | formalized | `PaperInterface.lean` | None; local `Lq` ball intersected with feasible solution space |
| Algorithm 1 norm projection | `algorithm1_norm_projection_formula` | formalized | `PaperInterface.lean` | None; projection is a closest feasible point in the selected source norm |
| Algorithm 1 projected update | `algorithm1_projected_update_formula` | formalized | `PaperInterface.lean` | None; next iterate is the projection of the raw local response |
| Algorithm 1 projected trajectory feasibility | `algorithm1_projected_trajectory_feasible_of_normProjection` | formalized | `PaperInterface.lean` | None; projected iterates remain feasible after a feasible initial point |
| Algorithm 1 stopping window | `algorithm1_window_stable_formula` | formalized | `PaperInterface.lean` | None; recent-window stability condition |
| Algorithm 1 stop condition | `algorithm1_stop_condition_formula` | formalized | `PaperInterface.lean` | None; terminal-time-or-stable-window stopping rule |
| Model A response | `modelA_response_formula` | formalized | `PaperInterface.lean` | None; exact local utility maximization formula |
| Model A response as `IsMaxOn` | `modelA_response_isMaxOn_formula` | formalized | `PaperInterface.lean` | None; reuses mathlib extrema predicate |
| Model B finite-coordinate response | `modelB_finite_response_formula` | formalized | `PaperInterface.lean` | None; records the normalized movement formula `x + r * g / |  | g |  | _q` with the subgradient vector supplied explicitly |
| Model B finite-coordinate sign-correct response | `modelB_finite_response_neg_lp_cost_gradient_formula` | formalized | `PaperInterface.lean` | None; lemma 3 removes normalization, giving movement `x - r * ∇cost` |
| Model B finite trace source | `modelB_finite_trace_source_formula` | formalized | `PaperInterface.lean` | None; expands selected-voter trace data; the sampled ideal used by the finite `Lp` cost is explicitly `E.ideal (voter t)` |
| Model B finite trace selected-voter cost | `modelB_finite_trace_selected_voter_cost_formula` | formalized | `PaperInterface.lean` | None; proof-facing trace preserves the identity between the sampled finite `Lp` cost ideal and the selected voter's ideal point |
| Theorem 2 finite SSGM bridge selected-voter cost | `theorem2_finite_ssgm_bridge_selected_voter_cost_formula` | formalized | `PaperInterface.lean` | None; the deterministic SSGM handoff still exposes that the sample cost is the cost to `E.ideal (voter t)` |
| Definition 1, Lp-normed utilities | `definition1_lp_normed_utilities_formula` | formalized | `PaperInterface.lean` | None; direct abstract source formula using `SourceNorm` and `normDistance`; concrete finite-coordinate specializations are exposed separately |
| Finite-coordinate norm-distance source | `finite_coordinate_norm_distance_source_formula` | formalized | `PaperInterface.lean` | None; expands `UsesFiniteCoordinateNormDistance` as exact equality with `finiteCoordinateDistance` |
| Model A cost-minimizer bridge | `modelA_response_lp_normed_cost_minimizer_formula` | formalized | `PaperInterface.lean` | None; derives appendix minimization form from Definition 1 sign convention |
| Definition 1 finite-coordinate L1 | `definition1_finite_coordinate_l1_formula` | formalized | `PaperInterface.lean` | None; concrete finite-sum formula through `FiniteDimensionalNorms.l1` |
| Definition 1 finite-coordinate L2 | `definition1_finite_coordinate_l2_formula` | formalized | `PaperInterface.lean` | None; concrete finite-coordinate Euclidean formula through `FiniteDimensionalNorms.l2` |
| Definition 1 finite-coordinate L∞ | `definition1_finite_coordinate_linf_formula` | formalized | `PaperInterface.lean` | None; concrete finite-coordinate max formula through `FiniteDimensionalNorms.linf` |
| Definition 1 finite-coordinate finite Lp | `definition1_finite_coordinate_lp_formula` | formalized | `PaperInterface.lean` | None; concrete finite-coordinate finite-`Lp` formula through `FiniteDimensionalNorms.lp`; source theorem-level norm assumptions still need audit |
| Appendix C.4 Lemma 3 candidate-gradient formula | `lemma3_gradient_candidate_source_formula` | formalized | `PaperInterface.lean` | None; shows the internal candidate denominator is the paper's displayed ` |  | d |  | _p^(p-1)` denominator |
| Appendix C.4 Lemma 3 candidate-gradient norm | `lemma3_finite_holder_dual_gradient_candidate_norm_formula` | formalized | `PaperInterface.lean` | None; proves the Holder-dual finite-sum algebra for the displayed candidate gradient |
| Appendix C.4 Lemma 3 derivative attachment | `lemma3_gradient_candidate_hasFDerivAt_formula` | formalized | `PaperInterface.lean` | None; shows the displayed candidate gradient is the Frechet derivative of the finite-coordinate `Lp` cost away from coordinate equalities |
| Appendix C.4 coordinate-equality bad event | `lemma3_coordinate_equality_bad_event_null_from_boundedDensity` | formalized | `PaperInterface.lean` | None; formalizes the bounded-density finite-union/null-transfer step, assuming each base coordinate hyperplane is null |
| Appendix C.4 coordinate-equality bad event, product base | `lemma3_coordinate_equality_bad_event_null_from_productMeasure` | formalized | `PaperInterface.lean` | None; specializes the nullness proof to finite products of sigma-finite atomless one-dimensional marginals |
| Appendix C.4 coordinate noncollision a.e. | `lemma3_coordinate_noncollision_ae_from_productMeasure` | formalized | `PaperInterface.lean` | None; converts product-measure bounded-density nullness into the almost-everywhere coordinate noncollision condition needed by Lemma 3 |
| C3 product-density bridge target | `c3_product_density_coordinate_noncollision_ae` | formalized | `PaperInterface.lean` | None; packages the structured finite-coordinate product-density carrier that future work should connect to the paper's abstract C3 condition |
| C3 product-density data | `finite_coordinate_ideal_distribution_data_formula` | formalized | `PaperInterface.lean` | None; expands the finite-coordinate ideal distribution as bounded density over a finite product of atomless one-dimensional marginals |
| C3 finite-coordinate carrier | `finite_coordinate_c3_carrier_formula` | formalized | `PaperInterface.lean` | None; shows that the product-density data plus the abstract C3 source field form the finite C3 carrier |
| Definition 2, weighted-Euclidean utilities | `definition2_weighted_euclidean_utilities_formula` | formalized with caveat | `PaperInterface.lean` | Component formula represented with an explicit `Finset`; Euclidean subspace semantics are carried by the source structure fields |
| Proposition 1 weighted `L2` raw trace source | `weighted_euclidean_l2_ssgm_trace_source_formula` | formalized | `PaperInterface.lean` | None; expands sampled voters, sampled costs as negative voter utilities, projected update equations, and sample-subgradient certificates; Lean preserves the sampled-voter cost formula in the proof-facing projected sample-subgradient recurrence |
| Proposition 1 concrete component trace source | `weighted_euclidean_l2_concrete_component_trace_source_formula` | formalized | `PaperInterface.lean` | None; expands the primitive component-distance source data; Lean derives component subgradients and the old weighted sample-subgradient certificate from finite `L2` component formulas and nonnegative coefficients |
| Proposition 1 weighted source trajectory feasibility | `weighted_euclidean_l2_ssgm_trace_source_trajectory_feasible` | formalized | `PaperInterface.lean` | None; derives feasible weighted `L2` iterates from norm projection, initial feasibility, and the raw projected update equation |
| Proposition 1 source-semantics trajectory feasibility | `proposition1_source_semantics_trajectory_feasible` | formalized | `PaperInterface.lean` | None; shows `Proposition1SourceSemantics` implies projected `L2` trajectory feasibility for the selected Model A/B branch |
| Proposition 1 source-semantics step sizes | `proposition1_source_semantics_step_size_conditions` | formalized | `PaperInterface.lean` | None; shows the positive source radius in `Proposition1SourceSemantics` supplies the SSGM step-size conditions for the selected Model A/B branch |
| Proposition 1 social objective source | `weighted_euclidean_social_objective_formula_source_formula` | formalized | `PaperInterface.lean` | None; expands social optima as feasible maximizers of societal utility; Lean derives the minimization objective `-societalUtility` for the SSGM bridge |
| Proposition 1 source-semantics social objective | `proposition1_source_semantics_social_objective_minimizer_formula` | formalized | `PaperInterface.lean` | None; shows `Proposition1SourceSemantics` derives the feasible minimizer characterization of `E.socialOptimal` used by the SSGM bridge |
| Definition 3, decomposable utilities | `definition3_decomposable_utilities_formula` | formalized with caveat | `PaperInterface.lean` | Coordinate-sum formula represented; coordinate maps and concavity are source structure fields |
| Proposition 2 median-set source | `decomposable_median_set_source_formula` | formalized | `PaperInterface.lean` | None; expands coordinatewise median-set membership source semantics |
| Proposition 2 median carrier | `decomposable_median_carrier_formula` | formalized | `PaperInterface.lean` | None; expands the derived proof-facing median carrier from decomposable utilities and coordinatewise median sets |
| Proposition 2 `L∞` coordinate replacement | `decomposable_linf_coordinate_replacement_formula` | formalized | `PaperInterface.lean` | None; expands the deterministic replacement property used to derive coordinatewise local optimality |
| Proposition 2 local `L∞` response bridge | `decomposable_linf_local_response_bridge_formula` | formalized | `PaperInterface.lean` | None; expands the derived proof-facing bridge from Model A local optimality to coordinatewise maximizers |
| Theorem 3 finite directional-field source model | `theorem3_finite_directional_field_model_formula` | formalized | `PaperInterface.lean` | None; expands the concrete finite voter weights, utility-gradient, expectation, normalized field, zero direction, and finite `L2` norm-distance fields |
| Theorem 3 finite-dot expected raw increment | `theorem3_expected_finiteDot_modelB_response_increment_formula` | formalized | `PaperInterface.lean` | None; shows the weighted expected finite-dot raw Model B increment equals radius times finite-dot directional field |
| Theorem 3 accumulated finite-dot expected increment | `theorem3_expected_finiteDot_modelB_response_increment_sum_formula` | formalized | `PaperInterface.lean` | None; sums the one-step expected increment identity over a finite prefix |
| Theorem 3 projected residual feasible direction | `theorem3_feasible_direction_at_formula` | formalized | `PaperInterface.lean` | None; expands the tangent-style positive-step feasibility predicate used by the projection residual argument |
| Theorem 3 `L2` projection normal cone | `theorem3_l2_projection_normal_cone_formula` | formalized | `PaperInterface.lean` | None; derives the finite normal-cone inequality from finite `L2` norm projection and convexity |
| Theorem 3 projection residual nonpositivity | `theorem3_projection_residual_nonpos_formula` | formalized | `PaperInterface.lean` | None; shows feasible directions have nonpositive finite-dot product with the projection residual |
| Theorem 3 projection progress inequality | `theorem3_projection_step_progress_formula` | formalized | `PaperInterface.lean` | None; gives the finite-dot progress bound for a projected raw step `previous + r * direction` |
| Theorem 3 iid selected-voter concentration | `theorem3_iid_weighted_voter_global_concentration_formula` | formalized | `PaperInterface.lean` | None; exposes the almost-sure finite-dot concentration event for iid weighted-voter draws under corrected global-tail radii |
| Theorem 3 global projected trace skeleton | `theorem3_global_projected_trace_ae_skeleton_formula` | formalized | `PaperInterface.lean` | None; expands the almost-sure global-tail trace data: raw Model B responses, sampled voter stream, finite `L2` projection, projected updates, and positive-step feasible `G(x*)` directions |
| Theorem 3 field continuity source | `theorem3_field_coordinate_continuity_source_formula` | formalized | `PaperInterface.lean` | None; expands the finite-coordinate reading of directional-field uniform continuity as coordinate continuity of the concrete normalized-gradient field |
| Theorem 3 primitive projected Algorithm 1 trace source | `theorem3_global_projected_algorithm1_trace_source_formula` | formalized | `PaperInterface.lean` | None; expands the primitive global projected trace generator: finite `L2` norm semantics, sampled-stream projection, projected-update equations, and positive-step feasible `G(x*)` directions |
| Theorem 3 split Algorithm 1 update source | `theorem3_global_projected_algorithm1_update_source_formula` | formalized | `PaperInterface.lean` | None; separates the global-tail projected Algorithm 1 update equation from the aggregate feasible-direction formula used in the constrained alternative |
| Theorem 3 aggregate feasible-direction formula | `theorem3_aggregate_feasible_direction_formula` | formalized | `PaperInterface.lean` | None; exposes the positive feasible step property as a record-free formula without hiding it as a source-record premise |
| Theorem 3 deterministic projected trace core | `theorem3_global_projected_trace_deterministic_trace_core_formula` | formalized | `PaperInterface.lean` | None; expands the raw pointwise global-tail trace generator with explicit normalized Model B response equations and deterministic sampled-voter alignment, separated from field continuity |
| Theorem 3 deterministic projected trace source | `theorem3_global_projected_trace_deterministic_trace_source_formula` | formalized | `PaperInterface.lean` | None; recombines field continuity with the raw pointwise global-tail trace core |
| Theorem 3 deterministic projected trace skeleton | `theorem3_global_projected_trace_deterministic_skeleton_formula` | formalized | `PaperInterface.lean` | None; expands the proof-facing pointwise trace generator after C1 convexity is supplied separately; deterministic sampled-voter alignment is weakened to the AE skeleton in `ProofInterface.lean` |
| Finite-coordinate convergence source | `finite_coordinate_convergence_source_formula` | formalized | `PaperInterface.lean` | None; expands the source reading that abstract point convergence implies finite coordinatewise convergence |
| Sampled projected full finite-coordinate source semantics | `finite_coordinate_full_sampled_projected_source_semantics_formula` | formalized | `PaperInterface.lean` | None; expands `FiniteCoordinateILVFullSampledProjectedSourceSemantics`, deriving Theorem 2 and Proposition 1 deterministic trace records while keeping Theorem 3 update/convergence/field/continuity/convexity obligations visible and omitting the old aggregate-feasibility source premise |
| Theorem 2 source semantics | `theorem2_source_semantics_formula` | formalized | `PaperInterface.lean` | None; expands the theorem-specific deterministic non-SSGM data: radius, finite norm semantics, C3/product-density carrier, and selected-voter raw Model B Algorithm 1 trace source; Lean derives the proof-facing normalized response predicate |
| Theorem 2 source-semantics selected-voter cost | `theorem2_source_semantics_selected_voter_cost_formula` | formalized | `PaperInterface.lean` | None; shows the finite SSGM bridge constructed from `Theorem2PrimitiveSourceSemantics` preserves selected-voter ideal costs |
| Theorem 2 source-semantics step sizes | `theorem2_source_semantics_step_size_conditions` | formalized | `PaperInterface.lean` | None; shows the positive source radius in `Theorem2PrimitiveSourceSemantics` supplies the SSGM step-size conditions |
| Theorem 2 source-semantics trajectory feasibility | `theorem2_source_semantics_trajectory_feasible` | formalized | `PaperInterface.lean` | None; shows the finite bridge constructed from `Theorem2PrimitiveSourceSemantics` keeps projected Model B iterates feasible |
| Theorem 2 source-semantics finite bridge | `theorem2_source_semantics_finite_bridge_formula` | formalized | `PaperInterface.lean` | None; builds the structured finite SSGM bridge from `Theorem2PrimitiveSourceSemantics` for the selected Holder-dual case |
| Proposition 1 concrete component source semantics | `proposition1_concrete_component_source_semantics_formula` | formalized | `PaperInterface.lean` | None; expands the full primitive source record used by the closeout route; old `Proposition1SourceSemantics.weighted_l2_inputs` is derived from this concrete component source |
| Proposition 1 source semantics | `proposition1_source_semantics_formula` | formalized | `PaperInterface.lean` | None; expands the theorem-specific deterministic weighted-Euclidean recurrence and social-utility maximizer source data; Lean derives trajectory feasibility, the SSGM step-size package, and the proof-facing social-objective bridge |
| Proposition 1 source-semantics finite bridge | `proposition1_source_semantics_finite_bridge_formula` | formalized | `PaperInterface.lean` | None; builds the structured weighted finite SSGM bridge from `Proposition1SourceSemantics` for the selected Model A/B branch |
| Proposition 2 source semantics | `proposition2_source_semantics_formula` | formalized | `PaperInterface.lean` | None; expands the theorem-specific deterministic median-carrier and derived local `L∞` response data; the concrete source model now stores a `DecomposableMedianSetSource` formula plus `DecomposableLinfCoordinateReplacement`, and Lean derives the proof-facing carrier and response bridge |
| Proposition 2 source-semantics case certificate | `proposition2_source_semantics_case_certificate_formula` | formalized | `PaperInterface.lean` | None; builds the structured decomposable/median `L∞` case certificate from `Proposition2SourceSemantics` for a selected decomposition and Model A/B branch |
| Proposition 2 product-box source | `finite_coordinate_product_box_solution_space_source_formula` | formalized | `PaperInterface.lean` | None; expands the finite-coordinate product-box solution-space closure used by the `L∞` coordinate replacement proof |
| Proposition 2 finite-coordinate `L∞` replacement source | `finite_coordinate_linf_coordinate_replacement_source_formula` | formalized | `PaperInterface.lean` | None; expands the finite norm, product-box, and coordinate-projection fields that derive `DecomposableLinfCoordinateReplacement` |
| Proposition 2 finite-coordinate source semantics | `proposition2_finite_coordinate_source_semantics_formula` | formalized | `PaperInterface.lean` | None; expands the paper-faithful finite-coordinate source route from finite norm semantics, product-box closure, and coordinatewise median-set source formulas |
| Proposition 2 finite-coordinate median convergence | `proposition2_finite_coordinate_decomposable_linf_medians` | partially formalized | `PaperInterface.lean` | Proves the finite-coordinate/product-box Proposition 2 endpoint from finite-coordinate source semantics plus the single theorem-shaped SSGM boundary |
| Theorem 1, Lp utilities and dual cases | `theorem1_lp_normed_dual_cases` | partially formalized | `PaperInterface.lean` | Finite-coordinate route; deterministic case certificate is built from visible source hypotheses; consumes only the single theorem-shaped axiom `assumption_ssgm_convergence_theorem` |
| Theorem 2, Model B finite Holder-dual norms | `theorem2_modelB_holder_dual_norms` | partially formalized | `PaperInterface.lean` | Finite-coordinate route; consumes `Theorem2PrimitiveSourceSemantics` plus the single theorem-shaped axiom `assumption_ssgm_convergence_theorem`; Lemma 3 candidate-gradient algebra, derivative attachment, and the Model B-to-projected-SSGM bridge are separated and formalized |
| Proposition 1, weighted-Euclidean L2 convergence | `proposition1_weighted_euclidean_l2` | partially formalized | `PaperInterface.lean` | Finite-coordinate route; consumes `Proposition1SourceSemantics` plus the single theorem-shaped axiom `assumption_ssgm_convergence_theorem` |
| Proposition 2, decomposable Linf median convergence | `proposition2_decomposable_linf_medians` | partially formalized | `PaperInterface.lean` | Finite-coordinate route; consumes `Proposition2FiniteCoordinateSourceSemantics` plus the single theorem-shaped axiom `assumption_ssgm_convergence_theorem`; the old arbitrary-decomposition replacement premise has been replaced by the paper's coordinate/product-box reading |
| Theorem 3, convergent Model B/L2 trajectory implies directional equilibrium | `theorem3_convergent_l2_modelB_is_directional_equilibrium_global_projected_trace` | partially formalized | `PaperInterface.lean` | No SSGM boundary premise; the corrected global-radius route uses `FiniteTheorem3DirectionalFieldModel`, explicit finite-coordinate trajectory convergence, and `FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalPathwiseSemantics` |
| Theorem 3, almost-sure global trace route | `theorem3_convergent_l2_modelB_is_directional_equilibrium_global_ae_trace` | partially formalized | `PaperInterface.lean` | No SSGM boundary premise; uses the global AE trace skeleton and the selected-voter concentration theorem proved in `ProofInterface.lean` |
| Theorem 3 constrained projected alternative | `theorem3_zero_or_no_aggregate_feasible_direction_formula` | formalized | `PaperInterface.lean` | None; proves that projected updates plus convergence give either `G(x*) = 0` or the record-free aggregate feasible-direction formula fails |
| Theorem 3, exact full-space adapter | `theorem3_statement_of_full_sampled_projected_source_semantics_univ` | partially formalized | `PaperInterface.lean` | Proves `theorem3Statement E` from sampled projected source semantics under the explicit condition `E.solutionSpace = Set.univ` |
| SSGM consequence bundle from source semantics | `finite_coordinate_source_semantics_ssgm_consequences` | partially formalized | `PaperInterface.lean` | Proves the four SSGM-backed endpoint consequences from separate theorem source semantics plus an explicit `FiniteCoordinateILVSSGMConvergenceTheorems E` bundle |
| Sampled projected paper closeout from source semantics | `finite_coordinate_full_sampled_projected_paper_consequences_with_ssgm` / `finite_coordinate_full_sampled_projected_paper_consequences` | partially formalized | `PaperInterface.lean` | Proves the represented finite-coordinate consequences from sampled projected source semantics; the second row uses only `assumption_ssgm_convergence_theorem` as the paper-local axiom and records Theorem 3 as constrained alternative plus full-space exact recovery |

## Major Assumption Boundary

The current verification path keeps exactly one paper-local Lean axiom:
`assumption_ssgm_convergence_theorem :
FiniteCoordinateILVSSGMConvergenceTheorems E`.  It is theorem-shaped and
supplies only the reusable stochastic subgradient convergence layer for Theorem
1, Theorem 2, Proposition 1, and Proposition 2.

All other non-SSGM data is explicit source semantics.  The strongest current
closeout route is `FiniteCoordinateILVFullSampledProjectedSourceSemantics`: it
keeps Theorem 2, Proposition 1, Proposition 2, and the Theorem 3 projected
update/convergence/field/continuity/convexity obligations separate, derives the
older deterministic Theorem 2/Proposition 1 records from sampled-process fields,
and intentionally omits the old aggregate-feasibility source premise.  Lean
proves `finite_coordinate_full_sampled_projected_paper_consequences` from this
record and the single SSGM axiom.

The recursive source-record audit is current for digest
`95b8554bfdc06bcb346443e11bdaa7cd49de7da918adedef8339c71b7cda45d9`.
It reports no missing, stale, unresolved, or unapproved source-record judgments.
The only remaining intentional external boundary is SSGM convergence.

Theorem 3 is handled without hiding a non-paper premise.  For general
constrained solution spaces Lean proves the constrained alternative
`proof_theorem3_finite_zero_or_no_aggregateFeasibleDirectionFormula_of_convergent_projectedUpdate`:
from projected updates plus convergence, either `G(x*) = 0` or the record-free
aggregate feasible-direction formula fails.  Lean also proves the exact
paper endpoint as
`proof_theorem3Statement_of_fullSampledProjectedSourceSemantics_univ_solutionSpace`
when `E.solutionSpace = Set.univ`, because every direction is feasible in that
case.  The old general constrained aggregate-feasibility record remains in the
library as a useful sufficient theorem, but it is no longer part of the
paper-closeout source package.

The previous Proposition 2 arbitrary-decomposition replacement issue has been
removed from the public endpoint route.  The current named row uses the
finite-coordinate/product-box source semantics that matches the paper's
coordinate proof, so it no longer asks for replacement semantics for an
arbitrary abstract decomposition.

Theorem 3 is not part of the SSGM boundary.  Lean proves the displayed
directional-field formula from `FiniteTheorem3DirectionalFieldModel`, proves the
fixed-coordinate and finite-dot drift arguments from uniform continuity and
coordinatewise convergence, proves the projection residual geometry, proves the
iid weighted-voter finite-dot concentration route, and uses the corrected
global tail radius `r0 / (N + t + 1)`.  The general constrained exact endpoint
is not claimed without an extra geometric premise: `proof_singleton_solutionSpace_not_force_aggregate_feasible_direction`
and `proof_theorem3_abstract_hypotheses_do_not_imply_statement` show the current
abstract hypotheses cannot imply positive feasible aggregate directions.  The
closed Lean replacement is the constrained alternative plus the full-space exact
recovery theorem described above.

Optlib is not currently pinned in this repo's Lake dependencies. A future
completion route may port the narrow Optlib convex/subgradient and deterministic
first-order-method interfaces, then build the required stochastic convergence
theorem on top of mathlib probability/process infrastructure. Until that exists,
the theorem rows depending on the single SSGM convergence axiom remain
`partially formalized`.

## Intake Checklist

- [x] Confirm the official PDF URL, version, and bibliographic fields.
- [x] Extract/confirm all named definitions, lemmas, and theorems in source order.
- [x] Fill in `FORMALIZATION_PLAN.md` with the initial outside-Lean paper audit,
      formula/result sanity check, proof strategy, and likely hard seams before
      deep Lean work.
- [ ] Run the lightweight statement target-setting pass and fix mismatched
      theorem targets before serious proof work.
- [ ] Run the assumption/hidden-premise precheck after the statement pass; do
      not treat row-local statement matches as globally certified targets until
      premise provenance also clears.
- [ ] Confirm `python3 scripts/audit_repository.py` reports no recursive
      paper-local hidden-premise dependency or axiom-like declaration for this
      paper.
- [x] Populate `DependencyDAG.tex` with the same named-result inventory.
- [x] Replace placeholders in `MainTheorems.lean` and `PaperInterface.lean`
      before updating any status row.
- [x] Keep `PaperInterface.lean` and `status.json` `review_surface` limited to
      source-facing definitions and named statements.
- [ ] Route every non-derived paper-facing theorem premise through
      `Assumptions.lean`, then run the assumption-provenance LLM judge.
- [ ] If the dashboard has more than 30 rows, run the LLM review-surface audit;
      if it has 120 or more rows, curate the interface before broad review.
- [ ] Run the context-free Lean-to-TeX translation and third-LLM match judgment
      workflow before asking for human dashboard review.
- [x] Update `status.json`, then run `python3 scripts/sync_paper_status.py`.
- [ ] Rebuild `DependencyDAG.pdf` and verify visually after the TeX rendering
      environment is available.

## Post-Formalization Checklist

- [ ] Run a library elevation pass over paper-local proof modules and record
      reusable candidates or completed extractions in `FINAL_VALIDATION_REPORT.md`.
- [ ] Run the combined recursive provenance audit and write a closeout report:
      `python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0 --write-report docs/RECURSIVE_PROVENANCE_AUDIT_<date>.md`.
      Resolve all findings for this paper before claiming `formalized`; if a
      finding remains, mark the result partial/conditional in `status.json`,
      `DependencyDAG.tex`, and `FINAL_VALIDATION_REPORT.md`.
