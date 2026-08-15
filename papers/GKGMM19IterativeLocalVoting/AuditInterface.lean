import GKGMM19IterativeLocalVoting.ProofInterface

open MeasureTheory
open scoped BigOperators ENNReal

/-!
# Audited Review Surface: Iterative Local Voting for Collective Decision-making in Continuous Spaces

This file contains the full audited review surface used by the dashboard
and LLM-as-judge checks. The compact human-facing entrypoint is
`PaperInterface.lean`.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- If a named theorem needs a hypothesis that is not derived from earlier Lean
  declarations, declare that hypothesis in `Assumptions.lean` and list it in
  `status.json` `review_surface.assumption_names`.
- Then state the named results directly, with assumptions visible in each
  theorem signature by referencing named paper assumptions imported from
  `Assumptions.lean`.
- Use short proofs that call into `MainTheorems.lean` or lower proof files.
- If implementation endpoints become broad or helper-heavy, move them to
  `ProofInterface.lean`; keep this filename as the single review surface.
- Keep exhaustive endpoint aliases and proof-seam checks in `PostPaperAudit.lean`,
  not here.

## Paper Definitions

- `conditions_c123_formula`: source assumptions C1, C2, C3.
- `c1_convex_solution_space_source_formula`: source interpretation of C1 as
  the direct `Convex` fact used by projection arguments.
- `theorem1_norm_pair_l2_l2`, `theorem1_norm_pair_l1_linf`, and
  `theorem1_norm_pair_linf_l1`: the three source norm pairs for Theorem 1.
- `theorem1_visible_hypotheses_case_certificate_formula`: the visible Theorem 1
  hypotheses form the structured SSGM case certificate.
- `algorithm1_radius_formula`: the ILV radius rule `r_t = r_0 / t`.
- `algorithm1_radius_tendsto_zero`: the ILV radius rule tends to zero.
- `algorithm1_radius_sq_summable`: the shifted squared radii are summable.
- `algorithm1_radius_sum_tendsto_atTop`: for `r_0 > 0`, shifted radius
  partial sums diverge.
- `algorithm1_radius_not_summable`: for `r_0 > 0`, shifted radii are not
  summable.
- `algorithm1_radius_ssgm_step_size_conditions`: the deterministic radius
  schedule satisfies the step-size conditions required by the SSGM layer.
- `algorithm1_local_neighborhood_formula`: local `Lq` ball query set.
- `algorithm1_norm_projection_formula`: the projected point is a closest
  feasible point in the selected source norm.
- `algorithm1_projected_update_formula`: the raw local response is projected
  back to the feasible set.
- `algorithm1_projected_trajectory_feasible_of_normProjection`: projected
  Algorithm 1 trajectories remain feasible.
- `algorithm1_window_stable_formula` and `algorithm1_stop_condition_formula`:
  the stopping-window and terminal-time stopping conditions.
- `modelA_response_formula`: local utility maximization.
- `modelA_response_isMaxOn_formula`: mathlib extrema formulation of Model A.
- `modelA_response_lp_normed_cost_minimizer_formula`: utility maximization as
  distance minimization for Definition 1 utilities.
- `modelB_finite_response_formula`: finite-coordinate normalized movement formula
  for Model B with a supplied subgradient vector.
- `modelB_finite_response_neg_lp_cost_gradient_formula`: sign-correct finite
  Model B movement for the Theorem 2 `Lp` cost-gradient candidate.
- `modelB_finite_algorithm1_trace_source_formula`: primitive raw Model B
  Algorithm 1 trace source with selected voters, sampled ideals, coordinate
  noncollision, coordinate raw-update formula, and projected updates.
- `modelB_finite_trace_source_formula`: proof-facing Model B trace source after
  the Holder-dual sign bridge derives the normalized response predicate.
- `modelB_finite_trace_selected_voter_cost_formula`: proof-facing Model B
  finite `Lp` sample costs remain tied to selected voters' ideal points after
  the raw trace source is converted.
- `theorem2_finite_ssgm_bridge_selected_voter_cost_formula`: Theorem 2's
  deterministic SSGM bridge preserves that selected-voter cost formula.
- `theorem2_source_semantics_selected_voter_cost_formula`: the same selected
  voter cost preservation directly from primitive `Theorem2` source semantics.
- `theorem2_source_semantics_step_size_conditions`: Theorem 2 source semantics
  turns the positive Algorithm 1 radius into the SSGM step-size package.
- `theorem2_source_semantics_trajectory_feasible`: Theorem 2 source semantics
  yields feasible projected Model B iterates for the selected Holder-dual case.
- `theorem2_source_semantics_finite_bridge_formula`: Theorem 2 source semantics
  builds the structured finite SSGM bridge consumed by the convergence theorem.
- `definition1_lp_normed_utilities_formula`: Lp-normed utilities.
- `finite_coordinate_norm_distance_source_formula`: finite-coordinate
  interpretation of the abstract source norm-distance field.
- `definition1_finite_coordinate_l1_formula`, `_l2_formula`,
  `_linf_formula`, and `_lp_formula`: concrete finite-coordinate source
  formulas.
- `lemma3_finite_holder_dual_gradient_candidate_norm_formula`: the algebraic
  core of Appendix C.4 Lemma 3 for the displayed finite Holder-dual gradient
  candidate.
- `lemma3_gradient_candidate_source_formula`: the displayed coordinate formula
  for that candidate gradient.
- `lemma3_gradient_candidate_hasFDerivAt_formula`: the candidate gradient is
  the Frechet derivative of the finite-coordinate `Lp` cost away from coordinate
  equalities.
- `lemma3_coordinate_equality_bad_event_null_from_boundedDensity`: the finite
  coordinate-equality bad event is null under bounded density once each base
  coordinate hyperplane is null.
- `lemma3_coordinate_equality_bad_event_null_from_productMeasure`: a concrete
  product-measure instance using atomless one-dimensional marginals.
- `lemma3_coordinate_noncollision_ae_from_productMeasure`: the corresponding
  almost-everywhere coordinate noncollision condition.
- `c3_product_density_coordinate_noncollision_ae`: a structured finite-coordinate
  C3 density carrier implies that noncollision condition.
- `finite_coordinate_ideal_distribution_data_formula` and
  `finite_coordinate_c3_carrier_formula`: product-density C3 data and its
  source-facing carrier.
- `definition2_weighted_euclidean_utilities_formula`: weighted-Euclidean
  utilities.
- `weighted_euclidean_l2_ssgm_trace_source_formula`: Proposition 1 weighted
  `L2` projected update equation and sample-subgradient source trace.
- `weighted_euclidean_l2_concrete_component_trace_source_formula`: Proposition
  1 concrete component-distance trace source whose finite `L2` component
  formulas derive the sample-subgradient trace.
- `weighted_euclidean_l2_ssgm_source_formula`: proof-facing Proposition 1
  weighted `L2` projected sample-subgradient source recurrence.
- `weighted_euclidean_l2_ssgm_source_trajectory_feasible`: feasibility derived
  from that projected source recurrence.
- `proposition1_source_semantics_trajectory_feasible`: feasibility derived from
  Proposition 1 source semantics and the finite SSGM bridge for the selected
  Model A/B branch.
- `proposition1_source_semantics_step_size_conditions`: the positive source
  radius in Proposition 1 source semantics yields the SSGM step-size package.
- `weighted_euclidean_social_objective_formula_source_formula`: Proposition 1
  social optima as feasible maximizers of societal utility.
- `weighted_euclidean_social_objective_source_formula`: derived minimization
  objective `-societalUtility` used by the SSGM bridge.
- `proposition1_source_semantics_social_objective_minimizer_formula`: full
  Proposition 1 source semantics yields the same social-optimal/minimizer
  bridge.
- `proposition1_concrete_component_source_semantics_formula`: Proposition 1
  concrete component-distance source semantics used by the full primitive
  source closeout route.
- `proposition1_source_semantics_finite_bridge_formula`: Proposition 1 source
  semantics builds the structured weighted finite SSGM bridge.
- `definition3_decomposable_utilities_formula`: decomposable utilities.
- `decomposable_median_set_source_formula` and
  `decomposable_median_carrier_formula`: Proposition 2 median-set source
  formula and derived proof-facing carrier.
- `decomposable_linf_coordinate_replacement_formula` and
  `decomposable_linf_local_response_bridge_formula`: Proposition 2
  coordinate-replacement source semantics and derived local `L∞` response
  bridge.
- `finite_coordinate_product_box_solution_space_source_formula` and
  `finite_coordinate_linf_coordinate_replacement_source_formula`: explicit
  product-box and finite-coordinate `L∞` replacement source formulas used by
  Proposition 2.
- `proposition2_finite_coordinate_source_semantics_formula`: paper-faithful
  finite-coordinate Proposition 2 source semantics derived from finite norm
  semantics, product-box closure, and coordinatewise median-set source formulas.
- `proposition2_source_semantics_case_certificate_formula`: Proposition 2 source
  semantics builds the structured SSGM case certificate.
- `theorem3_finite_directional_field_model_formula`: concrete finite
  normalized-gradient field data used by the Theorem 3 closeout route.
- `theorem3_expected_finiteDot_modelB_response_increment_formula` and
  `theorem3_expected_finiteDot_modelB_response_increment_sum_formula`:
  one-step and accumulated weighted-expectation identities for finite-dot
  Model B increments.
- `theorem3_feasible_direction_at_formula`: the positive-step feasibility
  predicate used by the Theorem 3 projection residual argument.
- `theorem3_l2_projection_normal_cone_formula`,
  `theorem3_projection_residual_nonpos_formula`, and
  `theorem3_projection_step_progress_formula`: deterministic projection
  residual geometry used by the Theorem 3 drift argument.
- `theorem3_iid_weighted_voter_global_concentration_formula`: iid
  selected-voter finite-dot concentration for the corrected global-radius
  projected-trace route.
- `theorem3_global_projected_trace_ae_skeleton_formula`: explicit almost-sure
  global-tail projected Algorithm 1 trace data used by the Theorem 3 route.
- `theorem3_field_coordinate_continuity_source_formula`: source interpretation
  of directional-field uniform continuity as coordinate continuity of the
  concrete finite normalized-gradient field.
- `theorem3_global_projected_trace_deterministic_trace_core_formula`: raw
  pointwise global-tail trace source, separated from field continuity.
- `theorem3_global_projected_algorithm1_trace_source_formula`: primitive
  global projected Algorithm 1 trace generator that derives the old
  deterministic trace core.
- `theorem3_global_projected_algorithm1_update_source_formula`: split
  Algorithm 1 update source for the Theorem 3 global-tail route.
- `theorem3_aggregate_feasible_direction_formula`: record-free statement of
  the aggregate feasible-direction property used to expose the constrained
  Theorem 3 alternative without hiding it in a source record.
- `theorem3_global_projected_trace_deterministic_trace_source_formula`: raw
  pointwise global-tail trace source after recombining field continuity.
- `theorem3_global_projected_trace_deterministic_skeleton_formula`:
  proof-facing pointwise trace skeleton after adding the separate C1 convexity
  interpretation.
- `finite_coordinate_convergence_source_formula`: source reading of abstract
  point convergence as finite coordinatewise convergence.
- `finite_coordinate_full_sampled_projected_source_semantics_formula`: sampled
  projected source semantics deriving Theorem 2 and Proposition 1 deterministic
  trace records while keeping Theorem 3 update, convergence, field, continuity,
  and C1 convexity source fields visible without an aggregate feasibility
  source premise.

## Named Results

- `theorem1_lp_normed_dual_cases`, `theorem2_modelB_holder_dual_norms`,
  `proposition1_weighted_euclidean_l2`, and
  `proposition2_decomposable_linf_medians`: named convergence endpoints
  projected from theorem-specific source semantics and the approved SSGM
  convergence bundle. Proposition 2 uses the finite-coordinate/product-box
  reading exposed by `Proposition2FiniteCoordinateSourceSemantics`.
- `theorem3_convergent_l2_modelB_is_directional_equilibrium_global_projected_trace`:
  paper-faithful projected-trace endpoint using the original global Algorithm 1
  radius schedule along each tail.
- `theorem3_convergent_l2_modelB_is_directional_equilibrium_global_ae_trace`:
  same corrected global route from the almost-sure trace skeleton; the
  selected-voter concentration theorem is proved in `ProofInterface.lean`.
- `theorem3_zero_or_no_aggregate_feasible_direction_formula`: constrained
  projected Theorem 3 alternative proved from the sampled projected source
  package without assuming the missing aggregate feasible-direction property.
- `theorem3_statement_of_full_sampled_projected_source_semantics_univ`: exact
  `theorem3Statement` recovery from the sampled projected source package under
  the explicit full-space condition `E.solutionSpace = Set.univ`.
- `finite_coordinate_source_semantics_ssgm_consequences`: the four
  SSGM-backed endpoint statements from separate theorem source semantics plus
  an explicit SSGM theorem bundle.
- `finite_coordinate_full_sampled_projected_paper_consequences_with_ssgm` and
  `finite_coordinate_full_sampled_projected_paper_consequences`: projected
  finite-coordinate closeout from sampled source semantics; the latter uses
  only the approved theorem-shaped SSGM boundary premise and records the constrained
  Theorem 3 alternative plus the full-space exact recovery theorem.
-/

namespace GKGMM19IterativeLocalVoting

/--
Section 3 assumptions C1, C2, and C3.

Source status: source assumption package.
-/
theorem conditions_c123_formula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) :
    assumption_conditions_c123 E ↔
      E.solutionSpace_nonempty_bounded_closed_convex ∧
        E.uniqueIdealSolutions ∧
          E.idealDistribution_bounded_measurable_density := by
  rfl

/--
C1 convexity source interpretation: the abstract paper C1 clause gives the
`Convex` fact used by the finite-dimensional projection residual proof.
-/
theorem c1_convex_solution_space_source_formula {Voter Point : Type*}
    [AddCommMonoid Point] [Module ℝ Point]
    (E : ILVEnvironment Voter Point) :
    Nonempty (C1ConvexSolutionSpaceSource E) ↔
      Convex ℝ E.solutionSpace := by
  constructor
  · rintro ⟨S⟩
    exact S.convex_solutionSpace
  · intro h
    exact ⟨{ convex_solutionSpace := h }⟩

/-- Theorem 1 source norm pair `(2,2)`. -/
theorem theorem1_norm_pair_l2_l2 :
    Theorem1NormPair SourceNorm.l2 SourceNorm.l2 := by
  exact theorem1NormPair_l2_l2

/-- Theorem 1 source norm pair `(1,∞)`. -/
theorem theorem1_norm_pair_l1_linf :
    Theorem1NormPair SourceNorm.l1 SourceNorm.linfty := by
  exact theorem1NormPair_l1_linf

/-- Theorem 1 source norm pair `(∞,1)`. -/
theorem theorem1_norm_pair_linf_l1 :
    Theorem1NormPair SourceNorm.linfty SourceNorm.l1 := by
  exact theorem1NormPair_linf_l1

/--
Theorem 1 deterministic handoff: C1-C3, the selected `Lp` utility condition,
the Model A/B branch, the response predicate, and one of the three norm-pair
cases are exactly the source certificate consumed by the SSGM convergence
theorem.
-/
theorem theorem1_visible_hypotheses_case_certificate_formula
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    {p q : SourceNorm} {model : VoterResponseModel}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E p)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model)
    (hpq : Theorem1NormPair p q) :
    Theorem1SSGMCaseCertificate E p q model := by
  exact
    proof_theorem1_caseCertificate_of_visible_hypotheses
      hC hUtil hmodel hResponse hpq

/--
Algorithm 1 step-size schedule `r_t = r_0 / t`.

Source status: exact displayed Algorithm 1 formula.
-/
theorem algorithm1_radius_formula (r0 : ℝ) (t : ℕ) :
    ilvRadius r0 t = r0 / (t : ℝ) := by
  rfl

/-- Algorithm 1 radius schedule tends to zero. -/
theorem algorithm1_radius_tendsto_zero (r0 : ℝ) :
    Filter.Tendsto (ilvRadius r0) Filter.atTop (nhds 0) := by
  exact ilvRadius_tendsto_zero r0

/--
Algorithm 1 shifted squared radii are summable, matching the square-step
condition used by stochastic approximation arguments.
-/
theorem algorithm1_radius_sq_summable (r0 : ℝ) :
    Summable (fun t : ℕ => (ilvRadius r0 (t + 1)) ^ 2) := by
  exact ilvRadius_sq_summable r0

/--
Algorithm 1 shifted radius partial sums diverge for positive initial radius,
matching the non-summable step-size condition used by stochastic approximation
arguments.
-/
theorem algorithm1_radius_sum_tendsto_atTop {r0 : ℝ} (hr0 : 0 < r0) :
    Filter.Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, ilvRadius r0 (t + 1))
      Filter.atTop Filter.atTop := by
  exact ilvRadius_sum_tendsto_atTop hr0

/--
Algorithm 1 shifted radii are not summable for positive initial radius.
-/
theorem algorithm1_radius_not_summable {r0 : ℝ} (hr0 : 0 < r0) :
    ¬ Summable (fun t : ℕ => ilvRadius r0 (t + 1)) := by
  exact ilvRadius_not_summable hr0

/--
Algorithm 1 radius schedule satisfies the step-size package used by the
stochastic subgradient layer.
-/
theorem algorithm1_radius_ssgm_step_size_conditions {r0 : ℝ} (hr0 : 0 < r0) :
    SSGMStepSizeConditions (ilvRadius r0) := by
  exact algorithm1_radius_ssgmStepSizeConditions hr0

/--
Algorithm 1 local-neighborhood query set.
Source status: direct source formula
Source note: This is the local `Lq`-ball query intersected with the feasible
solution space `X`.
-/
theorem algorithm1_local_neighborhood_formula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center candidate : Point) (r : ℝ) :
    candidate ∈ LocalNeighborhood E q center r ↔
      candidate ∈ E.solutionSpace ∧
        E.normDistance q candidate center ≤ r := by
  rfl

/--
Algorithm 1 projection operator `[y]_X`: a selected feasible point minimizing
distance to the raw point in the source norm used for projection.

Source status: direct source formula
-/
theorem algorithm1_norm_projection_formula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (project : Point → Point) :
    IsNormProjectionOnto E q project ↔
      ∀ y, project y ∈ E.solutionSpace ∧
        IsMinOn (fun x => E.normDistance q x y) E.solutionSpace (project y) := by
  exact isNormProjectionOnto_formula E q project

/--
Algorithm 1 projected update: the next iterate is the projection of the raw
local response.

Source status: direct source formula
-/
theorem algorithm1_projected_update_formula
    {Point : Type*} (project : Point → Point) (raw next : Point) :
    Algorithm1ProjectedUpdate project raw next ↔ next = project raw := by
  exact algorithm1ProjectedUpdate_formula project raw next

/--
Projected Algorithm 1 trajectories stay in the feasible solution space once
initialized there.

Source status: derived invariant from the projection formula
-/
theorem algorithm1_projected_trajectory_feasible_of_normProjection
    {Voter Point : Type*} {E : ILVEnvironment Voter Point} {q : SourceNorm}
    {project : Point → Point} {raw trajectory : ℕ → Point}
    (hproject : IsNormProjectionOnto E q project)
    (h0 : trajectory 0 ∈ E.solutionSpace)
    (hupdate :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    ∀ t : ℕ, trajectory t ∈ E.solutionSpace := by
  exact algorithm1ProjectedUpdates_mem_solutionSpace_of_normProjection
    hproject h0 hupdate

/--
Algorithm 1 stopping-window condition: all recent iterates in the window are
within `epsilon` of one another.

Source status: direct source formula
-/
theorem algorithm1_window_stable_formula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (t N : ℕ) (epsilon : ℝ) :
    Algorithm1WindowStable E q trajectory t N epsilon ↔
      ∀ l m,
        l ∈ Finset.Icc (t - N) t →
          m ∈ Finset.Icc (t - N) t →
            E.normDistance q (trajectory l) (trajectory m) ≤ epsilon := by
  exact algorithm1WindowStable_formula E q trajectory t N epsilon

/--
Algorithm 1 stopping condition: stop at terminal time `T` or when the recent
window is stable.

Source status: direct source formula
-/
theorem algorithm1_stop_condition_formula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (T N t : ℕ) (epsilon : ℝ) :
    Algorithm1StopCondition E q trajectory T N t epsilon ↔
      t = T ∨ Algorithm1WindowStable E q trajectory t N epsilon := by
  exact algorithm1StopCondition_formula E q trajectory T N t epsilon

/--
Model A response formula: the voter returns a favorite feasible point in the
queried local neighborhood.
Source status: direct source formula
-/
theorem modelA_response_formula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) :
    ModelAResponseAt E q center r voter response ↔
      response ∈ LocalNeighborhood E q center r ∧
        ∀ candidate, candidate ∈ LocalNeighborhood E q center r →
          E.utility voter candidate ≤ E.utility voter response := by
  rfl

/--
Model A response as mathlib `IsMaxOn` over the queried local neighborhood.
Source status: direct source formula
-/
theorem modelA_response_isMaxOn_formula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) :
    ModelAResponseAt E q center r voter response ↔
      response ∈ LocalNeighborhood E q center r ∧
        IsMaxOn (E.utility voter) (LocalNeighborhood E q center r) response := by
  exact modelAResponseAt_iff_isMaxOn E q center r voter response

/--
Model B finite-coordinate response formula:
`x' = x + r * g / ||g||_q`, with the subgradient vector `g` supplied
explicitly.

Source status: direct source formula for the movement rule; the subgradient
membership and stochastic recurrence are separate proof boundaries.
-/
theorem modelB_finite_response_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (q : SourceNorm) (center : Coord → ℝ) (r : ℝ)
    (gradient response : Coord → ℝ) :
    ModelBFiniteResponseAt q center r gradient response ↔
      response =
        fun i => center i + r *
          (gradient i / finiteCoordinateNorm q gradient) := by
  exact modelBFiniteResponseAt_formula q center r gradient response

/--
Finite-coordinate Theorem 2 Model B response formula after Lemma 3 removes the
normalization from the sign-correct utility-gradient direction.

Source status: derived finite-coordinate sign bridge from Lemma 3
-/
theorem modelB_finite_response_neg_lp_cost_gradient_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal : Coord → ℝ} (hcoord : ∀ i, center i ≠ ideal i)
    (r : ℝ) (response : Coord → ℝ) :
    ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response ↔
      response =
        fun i => center i - r *
          lpCostGradientCandidate p (fun j => center j - ideal j) i := by
  exact modelBFiniteResponseAt_neg_lpCostGradientCandidate_formula
    hdual hcoord r response

/--
Raw finite Model B Algorithm 1 trace source: selected voters determine the
sampled ideal points used in the finite `Lp` costs, raw responses follow the
paper's sign-correct coordinate update, and projected updates generate the
environment trajectory.
-/
theorem modelB_finite_algorithm1_trace_source_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (p q r0 : ℝ) :
    Nonempty (FiniteModelBILVAlgorithm1PrimitiveTraceSource E p q r0) ↔
      ∃ project : (Coord → ℝ) → Coord → ℝ,
        ∃ voter : ℕ → Voter,
          ∃ raw : ℕ → Coord → ℝ,
            IsNormProjectionOnto E (SourceNorm.lp q) project ∧
              E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB 0 ∈
                E.solutionSpace ∧
              (∀ t : ℕ,
                ∀ i : Coord,
                  E.trajectory (SourceNorm.lp q)
                      VoterResponseModel.modelB t i ≠
                    E.ideal (voter t) i) ∧
              (∀ t : ℕ,
                raw t =
                  fun i =>
                    E.trajectory (SourceNorm.lp q)
                        VoterResponseModel.modelB t i -
                      ilvRadius r0 (t + 1) *
                        lpCostGradientCandidate p
                          (fun j =>
                            E.trajectory (SourceNorm.lp q)
                                VoterResponseModel.modelB t j -
                              E.ideal (voter t) j) i) ∧
              (∀ t : ℕ,
                Algorithm1ProjectedUpdate project (raw t)
                  (E.trajectory (SourceNorm.lp q)
                    VoterResponseModel.modelB (t + 1))) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.project, S.voter, S.raw, S.project_norm, S.initial_feasible,
      S.coordinate_noncollision, S.raw_update_formula, S.projected_update⟩
  · rintro ⟨project, voter, raw, hProject, hInitial, hAvoids, hRawUpdate,
      hUpdate⟩
    exact
      ⟨{ project := project
         voter := voter
         raw := raw
         project_norm := hProject
         initial_feasible := hInitial
         coordinate_noncollision := hAvoids
         raw_update_formula := hRawUpdate
         projected_update := hUpdate }⟩

/--
Proof-facing finite Model B Algorithm 1 trace source: the raw coordinate update
has been converted to the normalized Model B response predicate by Holder
duality and coordinate noncollision.
-/
theorem modelB_finite_trace_source_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (p q r0 : ℝ) :
    Nonempty (FiniteModelBILVTraceSource E p q r0) ↔
      ∃ project : (Coord → ℝ) → Coord → ℝ,
        ∃ voter : ℕ → Voter,
          ∃ raw : ℕ → Coord → ℝ,
            IsNormProjectionOnto E (SourceNorm.lp q) project ∧
              E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB 0 ∈
                E.solutionSpace ∧
              (∀ t : ℕ,
                E.ideal (voter t) ∉
                  coordinateEqualityBadEvent
                    (E.trajectory (SourceNorm.lp q)
                      VoterResponseModel.modelB t)) ∧
              (∀ t : ℕ,
                ModelBFiniteResponseAt (SourceNorm.lp q)
                  (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
                  (ilvRadius r0 (t + 1))
                  (fun i => -lpCostGradientCandidate p
                    (fun j =>
                      E.trajectory (SourceNorm.lp q)
                          VoterResponseModel.modelB t j -
                        E.ideal (voter t) j) i)
                  (raw t)) ∧
              (∀ t : ℕ,
                Algorithm1ProjectedUpdate project (raw t)
                  (E.trajectory (SourceNorm.lp q)
                    VoterResponseModel.modelB (t + 1))) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.project, S.voter, S.raw, S.project_norm, S.initial_feasible,
      S.avoids_badEvent, S.modelB_response, S.projected_update⟩
  · rintro ⟨project, voter, raw, hProject, hInitial, hAvoids, hResponse,
      hUpdate⟩
    exact
      ⟨{ project := project
         voter := voter
         raw := raw
         project_norm := hProject
         initial_feasible := hInitial
         avoids_badEvent := hAvoids
         modelB_response := hResponse
         projected_update := hUpdate }⟩

/--
Proof-facing Theorem 2 trace sample-cost formula: after the Holder-dual sign
bridge converts the raw selected-voter trace to the normalized Model B response
predicate, the finite `Lp` sample costs still use the ideal point of the same
selected voter.
-/
theorem modelB_finite_trace_selected_voter_cost_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (T : FiniteModelBILVTrace E p q r0) :
    (∀ t : ℕ, T.ideal t = E.ideal (T.voter t)) ∧
      (∀ t : ℕ, ∀ y : Coord → ℝ,
        EconCSLib.FiniteDimensionalNorms.lp p
            (fun i => y i - T.ideal t i) =
          EconCSLib.FiniteDimensionalNorms.lp p
            (fun i => y i - E.ideal (T.voter t) i)) := by
  exact ⟨T.ideal_eq_selectedVoter, T.lpCost_eq_selectedVoter_lpCost⟩

/--
Theorem 2 deterministic SSGM bridge sample-cost formula: the finite `Lp` cost
seen by the SSGM boundary is the cost to the ideal of the selected voter in the
underlying Algorithm 1 trace.
-/
theorem theorem2_finite_ssgm_bridge_selected_voter_cost_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q : ℝ}
    (B : Theorem2FiniteSSGMBridge E p q) :
    ∀ t : ℕ, ∀ y : Coord → ℝ,
      EconCSLib.FiniteDimensionalNorms.lp p
          (fun i => y i - B.trace.ideal t i) =
        EconCSLib.FiniteDimensionalNorms.lp p
          (fun i => y i - E.ideal (B.trace.voter t) i) :=
  B.lpCost_eq_selectedVoter_lpCost

/--
Theorem 2 source-semantics selected-voter cost formula: the finite SSGM bridge
constructed from primitive `Theorem2` source semantics preserves the fact that
every sample cost is measured against the selected voter's ideal point.
-/
theorem theorem2_source_semantics_selected_voter_cost_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2PrimitiveSourceSemantics E)
    {p q : ℝ}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E (SourceNorm.lp p))
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    (hdual : HolderDualFinite p q) :
    let B : Theorem2FiniteSSGMBridge E p q :=
      proof_theorem2SourceSemantics_finite_bridge
        (theorem2SourceSemantics_of_primitive S) hC hUtil hResponse hdual
    ∀ t : ℕ, ∀ y : Coord → ℝ,
      EconCSLib.FiniteDimensionalNorms.lp p
          (fun i => y i - B.trace.ideal t i) =
        EconCSLib.FiniteDimensionalNorms.lp p
          (fun i => y i - E.ideal (B.trace.voter t) i) := by
  exact
    proof_theorem2SourceSemantics_finite_bridge_selected_voter_cost_formula
      (theorem2SourceSemantics_of_primitive S) hC hUtil hResponse hdual

/--
Theorem 2 source-semantics radius consequence: the positive Algorithm 1 radius
in the deterministic source semantics supplies the SSGM step-size hypotheses.
-/
theorem theorem2_source_semantics_step_size_conditions
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2PrimitiveSourceSemantics E) :
    SSGMStepSizeConditions (ilvRadius S.r0) := by
  exact
    proof_theorem2SourceSemantics_stepSizeConditions
      (theorem2SourceSemantics_of_primitive S)

/--
Theorem 2 source-semantics trajectory feasibility: after the raw selected-voter
Model B trace is converted through the Holder-dual finite bridge, every
projected Model B iterate remains in the feasible solution space.
-/
theorem theorem2_source_semantics_trajectory_feasible
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2PrimitiveSourceSemantics E)
    {p q : ℝ}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E (SourceNorm.lp p))
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    (hdual : HolderDualFinite p q) :
    ∀ t : ℕ,
      E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t ∈
        E.solutionSpace := by
  exact
    proof_theorem2SourceSemantics_trajectory_mem_solutionSpace
      (theorem2SourceSemantics_of_primitive S) hC hUtil hResponse hdual

/--
Theorem 2 source-semantics finite bridge: the deterministic source semantics
build the structured finite SSGM input bridge for the selected Holder-dual
case.
-/
def theorem2_source_semantics_finite_bridge_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2PrimitiveSourceSemantics E)
    {p q : ℝ}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E (SourceNorm.lp p))
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    (hdual : HolderDualFinite p q) :
    Theorem2FiniteSSGMBridge E p q :=
  proof_theorem2SourceSemantics_finite_bridge
    (theorem2SourceSemantics_of_primitive S) hC hUtil hResponse hdual

/-- Definition 1: Lp-normed utilities, `f_v(x) = -||x - x_v||_p`. -/
theorem definition1_lp_normed_utilities_formula
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p : SourceNorm) :
    IsLpNormedUtilities E p ↔
      ∀ v x, E.utility v x = -E.normDistance p x (E.ideal v) := by
  rfl

/--
Finite-coordinate source norm-distance formula: the abstract environment
distance field is interpreted as the concrete finite-coordinate source norm.
-/
theorem finite_coordinate_norm_distance_source_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    UsesFiniteCoordinateNormDistance E ↔
      ∀ p x y, E.normDistance p x y = finiteCoordinateDistance p x y := by
  rfl

/--
Model A under Definition 1 is the appendix cost-minimization problem over the
local neighborhood.
Source status: derived sign bridge from Definition 1
-/
theorem modelA_response_lp_normed_cost_minimizer_formula
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point)
    (hUtil : IsLpNormedUtilities E p) :
    ModelAResponseAt E q center r voter response ↔
      response ∈ LocalNeighborhood E q center r ∧
        IsMinOn (fun candidate => E.normDistance p candidate (E.ideal voter))
          (LocalNeighborhood E q center r) response := by
  exact modelAResponseAt_lpNormedUtilities_iff_normDistance_isMinOn
    E p q center r voter response hUtil

/-- Definition 1 specialized to concrete finite-coordinate `L1`. -/
theorem definition1_finite_coordinate_l1_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E) :
    IsLpNormedUtilities E SourceNorm.l1 ↔
      ∀ v x, E.utility v x =
        -EconCSLib.FiniteDimensionalNorms.l1
          (fun m => x m - E.ideal v m) := by
  exact finiteCoordinate_l1NormedUtilities_formula E hNorm

/-- Definition 1 specialized to concrete finite-coordinate `L2`. -/
theorem definition1_finite_coordinate_l2_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E) :
    IsLpNormedUtilities E SourceNorm.l2 ↔
      ∀ v x, E.utility v x =
        -EconCSLib.FiniteDimensionalNorms.l2
          (fun m => x m - E.ideal v m) := by
  exact finiteCoordinate_l2NormedUtilities_formula E hNorm

/-- Definition 1 specialized to concrete finite-coordinate `L∞`. -/
theorem definition1_finite_coordinate_linf_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E) :
    IsLpNormedUtilities E SourceNorm.linfty ↔
      ∀ v x, E.utility v x =
        -EconCSLib.FiniteDimensionalNorms.linf
          (fun m => x m - E.ideal v m) := by
  exact finiteCoordinate_linfNormedUtilities_formula E hNorm

/-- Definition 1 specialized to concrete finite-coordinate finite `Lp`. -/
theorem definition1_finite_coordinate_lp_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E) (p : ℝ) :
    IsLpNormedUtilities E (SourceNorm.lp p) ↔
      ∀ v x, E.utility v x =
        -EconCSLib.FiniteDimensionalNorms.lp p
          (fun m => x m - E.ideal v m) := by
  exact finiteCoordinate_lpRealNormedUtilities_formula E hNorm p

/--
Appendix C.4 Lemma 3 displayed candidate-gradient coordinate formula.

Source status: direct finite-coordinate formula bridge. The denominator is shown
in the paper's `||x - ideal||_p^(p-1)` form.
-/
theorem lemma3_gradient_candidate_source_formula
    {Coord : Type*} [Fintype Coord]
    {p : ℝ} (hp : 0 < p) (d : Coord → ℝ) :
    lpCostGradientCandidate p d =
      fun i => (|d i| ^ (p - 1) * (d i / |d i|)) /
        (EconCSLib.FiniteDimensionalNorms.lp p d) ^ (p - 1) := by
  exact lpCostGradientCandidate_eq_source_formula hp d

/--
Appendix C.4 Lemma 3, algebraic core: the displayed finite Holder-dual
gradient candidate for the `Lp` cost has `Lq` norm equal to `1` away from
coordinate equalities.

Source status: formalized candidate-gradient algebra. The matching
finite-coordinate derivative attachment is exposed in the next row.
-/
theorem lemma3_finite_holder_dual_gradient_candidate_norm_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    finiteCoordinateNorm (SourceNorm.lp q)
      (lpCostGradientCandidate p (fun i => x i - ideal i)) = 1 := by
  exact lemma3_finite_holder_dual_gradient_candidate_norm_formula_impl hdual hcoord

/--
Appendix C.4 Lemma 3 derivative attachment: away from coordinate equalities,
the displayed candidate-gradient vector represents the Frechet derivative of
the finite-coordinate `Lp` cost.

Source status: formalized finite-coordinate differentiability bridge.
-/
theorem lemma3_gradient_candidate_hasFDerivAt_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 1 < p)
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    HasFDerivAt
      (fun y : Coord → ℝ =>
        EconCSLib.FiniteDimensionalNorms.lp p
          (fun i => y i - ideal i))
      (EconCSLib.FiniteDimensionalNorms.coordinateLinearFunctional
        (lpCostGradientCandidate p (fun i => x i - ideal i))) x := by
  have hd : ∀ i, (fun j => x j - ideal j) i ≠ 0 := by
    intro i
    exact sub_ne_zero.mpr (hcoord i)
  have hbase :
      HasFDerivAt
        (fun y : Coord → ℝ => EconCSLib.FiniteDimensionalNorms.lp p y)
        (EconCSLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (lpCostGradientCandidate p (fun i => x i - ideal i)))
        (fun i => x i - ideal i) :=
    hasFDerivAt_lpCostGradientCandidate hp hd
  simpa [Function.comp_def] using
    (hasFDerivAt_comp_sub (𝕜 := ℝ)
      (f := fun y : Coord → ℝ => EconCSLib.FiniteDimensionalNorms.lp p y)
      (f' := EconCSLib.FiniteDimensionalNorms.coordinateLinearFunctional
        (lpCostGradientCandidate p (fun i => x i - ideal i)))
      (x := x) ideal).mpr hbase

/--
Appendix C.4 Lemma 3 bad-event bridge: the finite union of coordinate-equality
hyperplanes is null under a bounded-density ideal distribution, provided each
coordinate hyperplane is null for the base measure.

Source status: formalized finite-union and absolute-continuity reduction.
-/
theorem lemma3_coordinate_equality_bad_event_null_from_boundedDensity
    {Coord : Type*} [Fintype Coord] [MeasurableSpace (Coord → ℝ)]
    {ν μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd : EconCSLib.Probability.HasBoundedDensity ν μ C)
    (x : Coord → ℝ)
    (hcoord : ∀ i, ν (coordinateEqualityHyperplane x i) = 0) :
    μ (coordinateEqualityBadEvent x) = 0 := by
  exact boundedDensity_coordinateEqualityBadEvent_null hbd x hcoord

/--
Appendix C.4 Lemma 3 bad-event bridge, product-measure instance: if the ideal
distribution has bounded density with respect to a finite product of atomless
one-dimensional marginals, then the coordinate-equality bad event is null.

Source status: formalized finite-dimensional product-measure nullness plus
absolute-continuity transfer.
-/
theorem lemma3_coordinate_equality_bad_event_null_from_productMeasure
    {Coord : Type*} [Fintype Coord]
    (ρ : Measure ℝ) [SigmaFinite ρ] [NoAtoms ρ]
    {μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd :
      EconCSLib.Probability.HasBoundedDensity
        (Measure.pi (fun _ : Coord => ρ)) μ C)
    (x : Coord → ℝ) :
    μ (coordinateEqualityBadEvent x) = 0 := by
  exact productMeasure_boundedDensity_coordinateEqualityBadEvent_null ρ hbd x

/--
Appendix C.4 Lemma 3 bad-event bridge, a.e. form: under the same
product-measure bounded-density assumption, almost every ideal point avoids all
coordinate equalities with the current point.

Source status: formalized null-event-to-a.e. bridge for the Lemma 3 hypotheses.
-/
theorem lemma3_coordinate_noncollision_ae_from_productMeasure
    {Coord : Type*} [Fintype Coord]
    (ρ : Measure ℝ) [SigmaFinite ρ] [NoAtoms ρ]
    {μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd :
      EconCSLib.Probability.HasBoundedDensity
        (Measure.pi (fun _ : Coord => ρ)) μ C)
    (x : Coord → ℝ) :
    ∀ᵐ ideal ∂μ, ∀ i, x i ≠ ideal i := by
  exact ae_forall_coordinate_ne_of_productMeasure_boundedDensity ρ hbd x

/--
Structured finite-coordinate C3 bridge: a product bounded-density ideal-point
distribution supplies the almost-everywhere coordinate noncollision condition
used by Appendix C.4 Lemma 3.

Source status: formalized proof-seam target for replacing the abstract C3 field.
-/
theorem c3_product_density_coordinate_noncollision_ae
    {Coord : Type*} [Fintype Coord]
    (D : FiniteCoordinateIdealDistributionData Coord) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂D.idealMeasure, ∀ i, x i ≠ ideal i := by
  exact D.coordinate_noncollision_ae x

/--
Concrete finite-coordinate C3 product-density data formula: the sampled ideal
distribution has bounded density with respect to a finite product of atomless
one-dimensional marginals.
-/
theorem finite_coordinate_ideal_distribution_data_formula
    {Coord : Type*} [Fintype Coord] :
    Nonempty (FiniteCoordinateIdealDistributionData Coord) ↔
      ∃ idealMeasure : Measure (Coord → ℝ),
        ∃ baseMarginal : Measure ℝ,
          ∃ densityBound : ℝ≥0∞,
            SigmaFinite baseMarginal ∧
              NoAtoms baseMarginal ∧
                EconCSLib.Probability.HasBoundedDensity
                  (Measure.pi (fun _ : Coord => baseMarginal))
                  idealMeasure densityBound := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.idealMeasure, D.baseMarginal, D.densityBound,
      D.baseSigmaFinite, D.baseNoAtoms, D.hasBoundedDensity⟩
  · rintro ⟨idealMeasure, baseMarginal, densityBound, hSigmaFinite,
      hNoAtoms, hBoundedDensity⟩
    exact
      ⟨{ idealMeasure := idealMeasure
         baseMarginal := baseMarginal
         densityBound := densityBound
         baseSigmaFinite := hSigmaFinite
         baseNoAtoms := hNoAtoms
         hasBoundedDensity := hBoundedDensity }⟩

/--
Source-facing finite C3 carrier formula: concrete product-density data plus
the abstract C3 field of the environment are exactly the deterministic data
used by the finite-coordinate noncollision bridge.
-/
theorem finite_coordinate_c3_carrier_formula
    {Voter Coord : Type*} [Fintype Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (FiniteCoordinateC3Carrier E) ↔
      Nonempty (FiniteCoordinateIdealDistributionData Coord) ∧
        E.idealDistribution_bounded_measurable_density := by
  constructor
  · rintro ⟨C⟩
    exact ⟨⟨C.data⟩, C.source_c3⟩
  · rintro ⟨⟨data⟩, hC3⟩
    exact
      ⟨{ data := data
         source_c3 := hC3 }⟩

/--
Definition 2: weighted-Euclidean utilities,
`f_v(x) = - sum_k (w_v^k / ||w_v||_2) ||x^k - x_v^k||_2`.
-/
theorem definition2_weighted_euclidean_utilities_formula
    {Voter Point Component : Type*}
    (E : ILVEnvironment Voter Point)
    (W : WeightedEuclideanStructure Voter Point Component) :
    IsWeightedEuclideanUtilitiesWith E W ↔
      W.weightsAndIdealsDistributionCondition ∧
        ∀ v x, E.utility v x = -W.components.sum
          (fun k => (W.weight v k / W.weightNorm2 v) * W.componentDistance k x v) := by
  rfl

/--
Weighted-Euclidean `L2` raw source trace used by Proposition 1 before invoking
the SSGM theorem.  The source supplies the sampled voter stream, the sampled
cost formula, the projected update equation, and sample-subgradient
certificates separately; Lean derives the proof-facing sample-subgradient
recurrence.
-/
theorem weighted_euclidean_l2_ssgm_trace_source_formula
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) :
    Nonempty (WeightedEuclideanL2SSGMTraceSource E W model r0) ↔
      ∃ project : (Coord → ℝ) → Coord → ℝ,
        ∃ selectedVoter : ℕ → Voter,
          ∃ sampleCost : ℕ → (Coord → ℝ) → ℝ,
            ∃ subgradient : ℕ → Coord → ℝ,
              ∃ noise : ℕ → Coord → ℝ,
                ∃ bias : ℕ → Coord → ℝ,
                  0 < r0 ∧
                    IsNormProjectionOnto E SourceNorm.l2 project ∧
                    E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace ∧
                    (∀ t : ℕ, ∀ x : Coord → ℝ,
                      sampleCost t x = -E.utility (selectedVoter t) x) ∧
                    (∀ t : ℕ,
                      E.trajectory SourceNorm.l2 model (t + 1) =
                        project
                          (fun i =>
                            E.trajectory SourceNorm.l2 model t i -
                              ilvRadius r0 (t + 1) *
                                (subgradient t i + noise t i + bias t i))) ∧
                    (∀ t : ℕ,
                      FiniteSubgradientAt (sampleCost t)
                        (E.trajectory SourceNorm.l2 model t) (subgradient t)) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.project, S.selectedVoter, S.sampleCost, S.subgradient, S.noise,
      S.bias, S.r0_pos, S.project_norm, S.initial_feasible,
      S.sampleCost_eq_neg_utility, S.projected_update,
      S.sample_subgradient⟩
  · rintro ⟨project, selectedVoter, sampleCost, subgradient, noise, bias, hr0,
      hProject, hInitial, hSampleCost, hUpdate, hSubgradient⟩
    exact
      ⟨{ project := project
         selectedVoter := selectedVoter
         sampleCost := sampleCost
         subgradient := subgradient
         noise := noise
         bias := bias
         r0_pos := hr0
         project_norm := hProject
         initial_feasible := hInitial
         sampleCost_eq_neg_utility := hSampleCost
         projected_update := hUpdate
         sample_subgradient := hSubgradient }⟩

/--
Concrete component-distance Proposition 1 trace source.  This is the stricter
source layer used by the full closeout path: each component distance is
identified with a finite `L2` distance to an explicit component ideal, and Lean
derives the weighted sample-subgradient certificate from those component
formulas and nonnegative coefficients.
-/
theorem weighted_euclidean_l2_concrete_component_trace_source_formula
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) :
    Nonempty (WeightedEuclideanL2ConcreteComponentTraceSource E W model r0) ↔
      ∃ project : (Coord → ℝ) → Coord → ℝ,
        ∃ selectedVoter : ℕ → Voter,
          ∃ componentIdeal : Component → Voter → Coord → ℝ,
            ∃ noise : ℕ → Coord → ℝ,
              ∃ bias : ℕ → Coord → ℝ,
                0 < r0 ∧
                  IsNormProjectionOnto E SourceNorm.l2 project ∧
                  E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace ∧
                  (∀ t : ℕ, ∀ k, k ∈ W.components →
                    0 ≤
                      W.weight (selectedVoter t) k /
                        W.weightNorm2 (selectedVoter t)) ∧
                  (∀ t : ℕ, ∀ k, k ∈ W.components → ∀ x : Coord → ℝ,
                    W.componentDistance k x (selectedVoter t) =
                      finiteCoordinateDistance SourceNorm.l2 x
                        (componentIdeal k (selectedVoter t))) ∧
                  (∀ t : ℕ, ∀ k, k ∈ W.components → ∀ i : Coord,
                    E.trajectory SourceNorm.l2 model t i ≠
                      componentIdeal k (selectedVoter t) i) ∧
                  (∀ t : ℕ,
                    E.trajectory SourceNorm.l2 model (t + 1) =
                      project
                        (fun i =>
                          E.trajectory SourceNorm.l2 model t i -
                            ilvRadius r0 (t + 1) *
                              (W.components.sum
                                  (fun k =>
                                    (W.weight (selectedVoter t) k /
                                        W.weightNorm2 (selectedVoter t)) *
                                      lpCostGradientCandidate 2
                                        (fun j =>
                                          E.trajectory SourceNorm.l2 model t j -
                                            componentIdeal k
                                              (selectedVoter t) j) i) +
                                noise t i + bias t i))) := by
  constructor
  · rintro ⟨S⟩
    exact
      ⟨S.project, S.selectedVoter, S.componentIdeal, S.noise, S.bias,
        S.r0_pos, S.project_norm, S.initial_feasible,
        S.coefficient_nonneg, S.component_distance_eq_l2,
        S.component_noncollision, S.projected_update⟩
  · rintro
      ⟨project, selectedVoter, componentIdeal, noise, bias, hr0,
        hProject, hInitial, hCoefficient, hDistance, hNoncollision,
        hUpdate⟩
    exact
      ⟨{ project := project
         selectedVoter := selectedVoter
         componentIdeal := componentIdeal
         noise := noise
         bias := bias
         r0_pos := hr0
         project_norm := hProject
         initial_feasible := hInitial
         coefficient_nonneg := hCoefficient
         component_distance_eq_l2 := hDistance
         component_noncollision := hNoncollision
         projected_update := hUpdate }⟩

/--
Weighted-Euclidean `L2` source recurrence used by Proposition 1 before invoking
the SSGM theorem.  The source keeps the sampled voter stream and sampled cost
formula visible while supplying the projected sample-subgradient recurrence and
positive paper radius; Lean derives the SSGM step-size package and trajectory
feasibility from these fields.
-/
theorem weighted_euclidean_l2_ssgm_source_formula
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) :
    Nonempty (WeightedEuclideanL2SSGMSource E W model r0) ↔
      ∃ project : (Coord → ℝ) → Coord → ℝ,
        ∃ selectedVoter : ℕ → Voter,
          ∃ sampleCost : ℕ → (Coord → ℝ) → ℝ,
            ∃ subgradient : ℕ → Coord → ℝ,
              ∃ noise : ℕ → Coord → ℝ,
                ∃ bias : ℕ → Coord → ℝ,
                  0 < r0 ∧
                    IsNormProjectionOnto E SourceNorm.l2 project ∧
                    E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace ∧
                    (∀ t : ℕ, ∀ x : Coord → ℝ,
                      sampleCost t x = -E.utility (selectedVoter t) x) ∧
                    FollowsFiniteProjectedSampleSubgradientMethod sampleCost project
                      (E.trajectory SourceNorm.l2 model) (ilvRadius r0)
                      subgradient noise bias := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.project, S.selectedVoter, S.sampleCost, S.subgradient, S.noise,
      S.bias, S.r0_pos, S.project_norm, S.initial_feasible,
      S.sampleCost_eq_neg_utility, S.follows⟩
  · rintro ⟨project, selectedVoter, sampleCost, subgradient, noise, bias, hr0,
      hProject, hInitial, hSampleCost, hFollows⟩
    exact
      ⟨{ project := project
         selectedVoter := selectedVoter
         sampleCost := sampleCost
         subgradient := subgradient
         noise := noise
         bias := bias
         r0_pos := hr0
         project_norm := hProject
         initial_feasible := hInitial
         sampleCost_eq_neg_utility := hSampleCost
         follows := hFollows }⟩

/--
Weighted-Euclidean Proposition 1 source recurrence keeps all projected iterates
inside the feasible solution space.
-/
theorem weighted_euclidean_l2_ssgm_source_trajectory_feasible
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (S : WeightedEuclideanL2SSGMSource E W model r0) :
    ∀ t : ℕ, E.trajectory SourceNorm.l2 model t ∈ E.solutionSpace :=
  S.trajectory_mem_solutionSpace

theorem weighted_euclidean_l2_ssgm_trace_source_trajectory_feasible
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (S : WeightedEuclideanL2SSGMTraceSource E W model r0) :
    ∀ t : ℕ, E.trajectory SourceNorm.l2 model t ∈ E.solutionSpace :=
  (weightedEuclideanL2SSGMSource_of_traceSource S).trajectory_mem_solutionSpace

/--
Proposition 1 source-semantics trajectory feasibility: the finite bridge
constructed from `Proposition1SourceSemantics` keeps the projected `L2`
trajectory inside the solution space for the selected Model A/B branch.
-/
theorem proposition1_source_semantics_trajectory_feasible
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    {Component : Type}
    (hC : ConditionsC123 E)
    (hWeighted :
      ∃ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
        IsWeightedEuclideanUtilitiesWith E W)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    ∀ t : ℕ, E.trajectory SourceNorm.l2 model t ∈ E.solutionSpace := by
  exact
    proof_proposition1SourceSemantics_trajectory_mem_solutionSpace
      S hC hWeighted model hmodel hResponse

/--
Proposition 1 source-semantics radius consequence: the positive radius bundled
with the weighted `L2` trace source gives the SSGM step-size hypotheses for the
selected Model A/B branch.
-/
theorem proposition1_source_semantics_step_size_conditions
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] {Component : Type}
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    (hC : ConditionsC123 E)
    (hW : IsWeightedEuclideanUtilitiesWith E W)
    {model : VoterResponseModel}
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    ∃ r0 : ℝ, SSGMStepSizeConditions (ilvRadius r0) := by
  exact
    proof_proposition1SourceSemantics_stepSizeConditions
      S hC hW hmodel hResponse

/--
Proposition 1 social-optimum source formula: social optima are exactly the
feasible maximizers of societal utility.
-/
theorem weighted_euclidean_social_objective_formula_source_formula
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component) :
    Nonempty (WeightedEuclideanSocialObjectiveFormulaSource E W) ↔
      ∀ x : Coord → ℝ,
        x ∈ E.socialOptimal ↔
          x ∈ E.solutionSpace ∧
            IsMaxOn E.societalUtility E.solutionSpace x := by
  constructor
  · rintro ⟨S⟩
    exact S.mem_socialOptimal_iff_societalUtility_isMaxOn
  · intro h
    exact
      ⟨{ mem_socialOptimal_iff_societalUtility_isMaxOn := h }⟩

/--
Derived Proposition 1 minimization objective: minimizing `-societalUtility` on
the feasible set is equivalent to maximizing societal utility, so the raw
social-optimality formula yields the proof-facing SSGM objective source.
-/
theorem weighted_euclidean_social_objective_source_formula
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    (S : WeightedEuclideanSocialObjectiveFormulaSource E W) :
    ∀ x : Coord → ℝ,
      x ∈ E.socialOptimal ↔
        x ∈ E.solutionSpace ∧
          IsMinOn (socialCostObjective E) E.solutionSpace x :=
  (weightedEuclideanSocialObjectiveSource_of_formulaSource S).mem_socialOptimal_iff

/--
Proposition 1 source-semantics objective consequence: the full source semantics
derive the proof-facing minimization target `-societalUtility` whose feasible
minimizers are exactly the paper's social optima.
-/
theorem proposition1_source_semantics_social_objective_minimizer_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] {Component : Type}
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    (hC : ConditionsC123 E)
    (hW : IsWeightedEuclideanUtilitiesWith E W)
    {x : Coord → ℝ} :
    x ∈ E.socialOptimal ↔
      x ∈ E.solutionSpace ∧
        IsMinOn (socialCostObjective E) E.solutionSpace x := by
  exact
    proof_proposition1SourceSemantics_socialObjective_mem_socialOptimal_iff
      S hC hW

/--
Proposition 1 source-semantics finite bridge: the deterministic source
semantics build the weighted finite SSGM bridge for the selected Model A/B
branch.
-/
noncomputable def proposition1_source_semantics_finite_bridge_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    {Component : Type}
    (hC : ConditionsC123 E)
    (hWeighted :
      ∃ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
        IsWeightedEuclideanUtilitiesWith E W)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    Σ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
      Σ' _hWeightedW : IsWeightedEuclideanUtilitiesWith E W,
        Proposition1FiniteSSGMBridge E W model :=
  proof_proposition1SourceSemantics_finite_bridge
    S hC hWeighted model hmodel hResponse

/-- Definition 3: decomposable utilities, `f_v(x) = sum_m f_v^m(x^m)`. -/
theorem definition3_decomposable_utilities_formula
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) :
    IsDecomposableUtilitiesWith E D ↔
      D.coordinateUtilitiesConcave ∧
        ∀ v x, E.utility v x =
          D.coords.sum (fun m => D.coordinateUtility m v (D.coordinate m x)) := by
  rfl


/--
Definition 4: DLCD finite-budget utility formula.

Source status: direct paper-facing Definition 4 finite-budget utility formula row.
-/
noncomputable def dlcdBudgetUtility
    {Dim : Type*} [Fintype Dim]
    (isExpense : Dim → Bool) (componentUtility : Dim → ℝ → ℝ)
    (deficitWeight : ℝ) (x : Dim → ℝ) : ℝ :=
  (∑ m : Dim, componentUtility m (x m)) -
    deficitWeight *
      ((∑ m : Dim, if isExpense m then x m else 0) -
        (∑ m : Dim, if isExpense m then 0 else x m))

/--
Source Definition 4 / DLCD: decomposable utility with a linear cost for the
budget deficit.

Source status: direct paper-facing Definition 4 DLCD formula row.
-/
def paper_definition4_dlcd_formula
    {Dim : Type*} [Fintype Dim]
    (utility : (Dim → ℝ) → ℝ)
    (isExpense : Dim → Bool) (componentUtility : Dim → ℝ → ℝ)
    (deficitWeight : ℝ) : Prop :=
  0 ≤ deficitWeight ∧
    (∀ m : Dim, ConcaveOn ℝ Set.univ (componentUtility m)) ∧
      ∀ x : Dim → ℝ,
        utility x =
          dlcdBudgetUtility isExpense componentUtility deficitWeight x

/--
Appendix Theorem 4: expected selected subgradients are subgradients of the
expected objective.

This is now a proved theorem rather than a boundary.  It is stated at the
concrete finite-coordinate instantiation, so "subgradient" is the actual
subgradient inequality and "expected" is the actual Bochner integral.

Source status: covered; the interchange result is proved in the reusable
library module `EconCSLib.Foundations.Optimization.ExpectedSubgradient` and no
external boundary remains for this row.
-/
theorem appendix_theorem4_expected_subgradient
    {Coord Theta : Type*} [Fintype Coord] [MeasurableSpace Theta]
    (μ : MeasureTheory.Measure Theta)
    (cost : Theta → (Coord → ℝ) → ℝ) :
    ExpectedSubgradientTheoremStatement μ cost :=
  expected_subgradient_theorem μ cost

/--
Appendix Theorem 5 boundary: the stochastic subgradient method convergence
bundle quoted by the paper.
-/
theorem appendix_theorem5_ssgm_convergence_boundary
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    FiniteCoordinateILVSSGMConvergenceTheorems E :=
  hSSGM

/--
Proposition 2 median-set source formula: the paper's median target is the set
of points whose decomposed coordinates lie in the corresponding one-dimensional
median sets.
-/
theorem decomposable_median_set_source_formula
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) :
    Nonempty (DecomposableMedianSetSource E D) ↔
      ∃ coordinateMedianSet : Coord → Set ℝ,
        ∀ x : Point,
          x ∈ E.medianSet ↔
            ∀ m, m ∈ D.coords →
              D.coordinate m x ∈ coordinateMedianSet m := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.coordinateMedianSet, S.mem_medianSet_iff⟩
  · rintro ⟨coordinateMedianSet, hMedian⟩
    exact
      ⟨{ coordinateMedianSet := coordinateMedianSet
         mem_medianSet_iff := hMedian }⟩

/--
Proof-facing Proposition 2 median carrier formula derived from the median-set
source and decomposable-utility instance.
-/
theorem decomposable_median_carrier_formula
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) :
    Nonempty (DecomposableMedianCarrier E D) ↔
      IsDecomposableUtilitiesWith E D ∧
        ∃ coordinateMedianSet : Coord → Set ℝ,
          E.medianSet =
            {x | ∀ m, m ∈ D.coords →
              D.coordinate m x ∈ coordinateMedianSet m} := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.decomposable, C.coordinateMedianSet, C.medianSet_formula⟩
  · rintro ⟨hD, coordinateMedianSet, hFormula⟩
    exact
      ⟨{ decomposable := hD
         coordinateMedianSet := coordinateMedianSet
         medianSet_formula := hFormula }⟩

/--
Proposition 2 coordinate-replacement source formula: inside an `L∞` local
query, a feasible one-coordinate value can replace that coordinate of a
response while preserving local feasibility and all other decomposed
coordinates.
-/
theorem decomposable_linf_coordinate_replacement_formula
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) :
    Nonempty (DecomposableLinfCoordinateReplacement E D) ↔
      ∃ replace : Point → Coord → ℝ → Point,
        (∀ {center response : Point} {r : ℝ} {voter : Voter}
          (_hresponse :
            ModelAResponseAt E SourceNorm.linfty center r voter response)
          {m : Coord} {z : ℝ},
          m ∈ D.coords →
            z ∈ {z | ∃ candidate,
              candidate ∈ LocalNeighborhood E SourceNorm.linfty center r ∧
                D.coordinate m candidate = z} →
              replace response m z ∈
                LocalNeighborhood E SourceNorm.linfty center r) ∧
        (∀ (response : Point) {m : Coord} {z : ℝ},
          m ∈ D.coords →
            D.coordinate m (replace response m z) = z) ∧
        (∀ (response : Point) {m : Coord} {z : ℝ} {l : Coord},
          l ∈ D.coords →
            l ≠ m →
              D.coordinate l (replace response m z) =
                D.coordinate l response) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.replace, S.replace_mem_local, S.replace_coordinate_self,
      S.replace_coordinate_other⟩
  · rintro ⟨replace, hMem, hSelf, hOther⟩
    exact
      ⟨{ replace := replace
         replace_mem_local := hMem
         replace_coordinate_self := hSelf
         replace_coordinate_other := hOther }⟩

/--
Proof-facing Proposition 2 local `L∞` response bridge formula: a Model A
maximizer for decomposable utilities is coordinatewise optimal over the
one-dimensional values available in the local query.
-/
theorem decomposable_linf_local_response_bridge_formula
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) :
    Nonempty (DecomposableLinfLocalResponseBridge E D) ↔
      IsDecomposableUtilitiesWith E D ∧
        ∀ {center response : Point} {r : ℝ} {voter : Voter},
          ModelAResponseAt E SourceNorm.linfty center r voter response →
            ∀ m, m ∈ D.coords →
              IsMaxOn
                (fun z : ℝ => D.coordinateUtility m voter z)
                {z | ∃ candidate,
                  candidate ∈ LocalNeighborhood E SourceNorm.linfty center r ∧
                    D.coordinate m candidate = z}
                (D.coordinate m response) := by
  constructor
  · rintro ⟨B⟩
    exact ⟨B.decomposable, B.coordinate_response_optimal⟩
  · rintro ⟨hD, hOptimal⟩
    exact
      ⟨{ decomposable := hD
         coordinate_response_optimal := hOptimal }⟩

/--
Finite-coordinate product-box solution-space source formula: replacing one
coordinate of a feasible point by the same coordinate from another feasible
point remains feasible.
-/
theorem finite_coordinate_product_box_solution_space_source_formula
    {Voter Coord : Type*} [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (FiniteCoordinateProductBoxSolutionSpaceSource E) ↔
      ∀ {x y : Coord → ℝ},
        x ∈ E.solutionSpace →
          y ∈ E.solutionSpace →
            ∀ m : Coord, Function.update x m (y m) ∈ E.solutionSpace := by
  constructor
  · rintro ⟨S⟩
    exact S.coordinate_update_mem_solutionSpace
  · intro h
    exact ⟨{ coordinate_update_mem_solutionSpace := h }⟩

/--
Finite-coordinate `L∞` replacement source formula: finite norm semantics,
product-box solution-space closure, and ambient-coordinate projection formulas
are exactly the data used to derive `DecomposableLinfCoordinateReplacement`.
-/
theorem finite_coordinate_linf_coordinate_replacement_source_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (D : DecomposableStructure Voter (Coord → ℝ) Coord) :
    Nonempty (FiniteCoordinateLinfCoordinateReplacementSource E D) ↔
      ∃ hNorm : UsesFiniteCoordinateNormDistance E,
        ∃ productBox : FiniteCoordinateProductBoxSolutionSpaceSource E,
          ∀ m, m ∈ D.coords → ∀ x : Coord → ℝ, D.coordinate m x = x m := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.normDistance, S.productBox, S.coordinate_eq⟩
  · rintro ⟨hNorm, productBox, hCoordinate⟩
    exact
      ⟨{ normDistance := hNorm
         productBox := productBox
         coordinate_eq := hCoordinate }⟩

/--
Finite-coordinate Proposition 2 source semantics: this is the paper-faithful
ambient-coordinate route.  It supplies finite norm semantics, product-box
solution-space closure, and coordinatewise median-set source formulas; Lean
derives the `L∞` coordinate-replacement bridge from those fields for any
decomposition whose coordinates are the ambient coordinate projections.
-/
theorem proposition2_finite_coordinate_source_semantics_formula
    {Voter Coord : Type} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (Proposition2FiniteCoordinateSourceSemantics E) ↔
      ∃ hNorm : UsesFiniteCoordinateNormDistance E,
        ∃ productBox : FiniteCoordinateProductBoxSolutionSpaceSource E,
          ∃ hMedian :
            (∀ {D : DecomposableStructure Voter (Coord → ℝ) Coord},
              ConditionsC123 E →
                IsDecomposableUtilitiesWith E D →
                  DecomposableMedianSetSource E D),
            True := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.normDistance, S.productBox, S.medianSetSource, trivial⟩
  · rintro ⟨hNorm, productBox, hMedian, _⟩
    exact
      ⟨{ normDistance := hNorm
         productBox := productBox
         medianSetSource := hMedian }⟩

/--
Proposition 2 source-semantics case certificate: the deterministic source
semantics build the structured decomposable/median `L∞` case certificate for
the selected decomposition and Model A/B branch.
-/
noncomputable def proposition2_source_semantics_case_certificate_formula
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (S : Proposition2SourceSemantics E)
    {Coord : Type}
    (hC : ConditionsC123 E)
    (hDecomposable :
      ∃ D : DecomposableStructure Voter Point Coord,
        IsDecomposableUtilitiesWith E D)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    Σ D : DecomposableStructure Voter Point Coord,
      Proposition2SSGMCaseCertificate E D model :=
  proof_proposition2SourceSemantics_case_certificate
    S hC hDecomposable model hmodel hResponse

/--
Concrete finite-coordinate normalized-gradient field model used by Theorem 3.
This expands the source-semantics record so the field formula is not hidden
behind the record name.
-/
theorem theorem3_finite_directional_field_model_formula
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (FiniteTheorem3DirectionalFieldModel E) ↔
      ∃ weight : Voter → ℝ,
        (∀ voter, 0 ≤ weight voter) ∧
          (∑ voter : Voter, weight voter) = 1 ∧
            ∃ utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ,
              E.utilityGradient = utilityGradient ∧
                E.scalarDirection = finiteScalarDirection ∧
                  E.voterExpectation = finiteVoterExpectation weight ∧
                    E.directionalField =
                      finiteTheorem3DirectionalField weight utilityGradient ∧
                      E.zeroDirection = (fun _ : Coord => (0 : ℝ)) ∧
                        (∀ g : Coord → ℝ,
                          E.normDistance SourceNorm.l2 g E.zeroDirection =
                            finiteCoordinateNorm SourceNorm.l2 g) := by
  constructor
  · rintro ⟨M⟩
    exact
      ⟨M.weight, M.weight_nonneg, M.weight_sum, M.utilityGradient,
        M.utilityGradient_eq, M.scalarDirection_eq, M.voterExpectation_eq,
        M.directionalField_eq, M.zeroDirection_eq, M.normDistance_l2_zero_eq⟩
  · rintro
      ⟨weight, hweight_nonneg, hweight_sum, utilityGradient,
        hUtilityGradient, hScalarDirection, hVoterExpectation,
        hDirectionalField, hZeroDirection, hNormDistance⟩
    exact
      ⟨{ weight := weight
         weight_nonneg := hweight_nonneg
         weight_sum := hweight_sum
         utilityGradient := utilityGradient
         utilityGradient_eq := hUtilityGradient
         scalarDirection_eq := hScalarDirection
         voterExpectation_eq := hVoterExpectation
         directionalField_eq := hDirectionalField
         zeroDirection_eq := hZeroDirection
         normDistance_l2_zero_eq := hNormDistance }⟩

/--
Theorem 3 finite-dot expectation identity: averaging raw Model B increments
against finite voter weights gives the radius times the finite-dot product with
the concrete normalized-gradient field.
-/
theorem theorem3_expected_finiteDot_modelB_response_increment_formula
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    {x : Coord → ℝ} {response : Voter → Coord → ℝ}
    (a : Coord → ℝ) (r : ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 x r
          (utilityGradient voter x) (response voter)) :
    (∑ voter : Voter,
      weight voter * finiteDot a (fun i => response voter i - x i)) =
      r * finiteDot a
        (finiteTheorem3DirectionalField weight utilityGradient x) :=
  finiteTheorem3DirectionalField_expected_finiteDot_modelB_response_increment
    weight utilityGradient a r hresponse

/--
Theorem 3 accumulated finite-dot expectation identity over a finite prefix of
the projected-trace tail.
-/
theorem theorem3_expected_finiteDot_modelB_response_increment_sum_formula
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (a : Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t) (radius t)
          (utilityGradient voter (center t)) (response t voter)) :
    ∀ n : ℕ,
      (∑ t ∈ Finset.range n,
        ∑ voter : Voter,
          weight voter *
            finiteDot a (fun i => response t voter i - center t i)) =
        ∑ t ∈ Finset.range n,
          radius t *
            finiteDot a
              (finiteTheorem3DirectionalField weight utilityGradient
                (center t)) :=
  finiteTheorem3DirectionalField_expected_finiteDot_modelB_response_increment_sum
    weight utilityGradient center radius response a hresponse

/--
Projection residual feasibility used by the corrected Theorem 3 route: some
positive step in the fixed direction remains feasible from the projected point.
-/
theorem theorem3_feasible_direction_at_formula
    {Coord : Type*} [Fintype Coord]
    (X : Set (Coord → ℝ)) (point direction : Coord → ℝ) :
    FiniteFeasibleDirectionAt X point direction ↔
      ∃ η : ℝ, 0 < η ∧ (fun i => point i + η * direction i) ∈ X := by
  rfl

/--
Theorem 3 projection geometry: an `L2` nearest-point projection onto a convex
solution set satisfies the finite normal-cone inequality used by the projection
residual argument.
-/
theorem theorem3_l2_projection_normal_cone_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hconv : Convex ℝ E.solutionSpace)
    {project : (Coord → ℝ) → Coord → ℝ} {raw next : Coord → ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next) :
    FiniteProjectionNormalConeAt E.solutionSpace raw next :=
  finiteProjectionNormalConeAt_of_l2_normProjection
    hNorm hconv hproject hupdate

/--
Theorem 3 projection residual geometry: if a direction is feasible from the
projected point, then its finite-dot product with the projection residual is
nonpositive.
-/
theorem theorem3_projection_residual_nonpos_formula
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {raw next direction : Coord → ℝ}
    (hnormal : FiniteProjectionNormalConeAt X raw next)
    (hfeasible : FiniteFeasibleDirectionAt X next direction) :
    finiteDot direction (fun i => raw i - next i) ≤ 0 :=
  finiteDot_projection_residual_nonpos_of_feasibleDirectionAt
    hnormal hfeasible

/--
Theorem 3 projection progress inequality: for a raw step
`previous + r * direction`, the squared projected movement divided by `r` is
bounded by the finite-dot progress in that direction.
-/
theorem theorem3_projection_step_progress_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hconv : Convex ℝ E.solutionSpace)
    {project : (Coord → ℝ) → Coord → ℝ}
    {previous raw next direction : Coord → ℝ} {r : ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next)
    (hr : 0 < r)
    (hraw : raw = fun i => previous i + r * direction i)
    (hprevious : previous ∈ E.solutionSpace) :
    (1 / r) *
        finiteDot (fun i => next i - previous i)
          (fun i => next i - previous i) ≤
      finiteDot direction (fun i => next i - previous i) :=
  finiteDot_step_progress_of_l2_normProjection
    hNorm hconv hproject hupdate hr hraw hprevious

/--
Theorem 3 selected-voter concentration: for iid voters drawn from the finite
weighted voter law, the realized finite-dot raw Model B increments are
eventually within a finite concentration bound of their weighted expectation,
using the corrected global-tail Algorithm 1 radii.
-/
theorem theorem3_iid_weighted_voter_global_concentration_formula
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (hweight_nonneg : ∀ voter, 0 ≤ G.weight voter)
    (hweight_sum : (∑ voter : Voter, G.weight voter) = 1)
    {r0 : ℝ} (hr0 : 0 < r0)
    (xstar : Coord → ℝ) (N : ℕ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N))
          (ilvTailRadius r0 N t)
          (G.utilityGradient voter
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N)))
          (response t voter)) :
    ∀ᵐ sampledVoter
        ∂theorem3FiniteWeightedVoterSequenceMeasure
          G.weight hweight_nonneg hweight_sum,
      ∃ concentrationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        (∑ t ∈ Finset.range n,
            ∑ voter : Voter,
              G.weight voter *
                finiteDot
                  (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar)
                  (fun i =>
                    response t voter i -
                      E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                        (t + N) i)) -
            concentrationBound ≤
          theorem3ConcreteFiniteFieldProjection G xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB N) +
            ∑ t ∈ Finset.range n,
              finiteDot
                (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar)
                (fun i =>
                  response t (sampledVoter t) i -
                    E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                      (t + N) i) :=
  proof_theorem3_finiteDot_projectedTrace_global_concentration_ae_of_iid_weightedVoter
    G hweight_nonneg hweight_sum hr0 xstar N response hresponse

/--
Almost-sure global projected Algorithm 1 trace skeleton used by the corrected
Theorem 3 route.  This spells out the remaining source-semantics data: global
tail radii, concrete Model B responses for all voters, almost-sure selected raw
responses for the sampled voter stream, finite `L2` projection, projected
updates into the environment trajectory, and positive-step feasibility of the
fixed `G(x*)` direction after each projected point.
-/
theorem theorem3_global_projected_trace_ae_skeleton_formula
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty
        (FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalAETraceSkeleton M) ↔
      ∃ r0 : ℝ,
        0 < r0 ∧
          (E.directionalFieldUniformlyContinuous →
            ∀ xstar i ε, 0 < ε →
              ∃ δ, 0 < δ ∧
                ∀ x : Coord → ℝ,
                  finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
                    |finiteTheorem3DirectionalField M.weight
                        M.utilityGradient x i -
                      finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar i| < ε) ∧
          (∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
            ConditionsC123 E →
              E.directionalFieldUniformlyContinuous →
                E.respondsAccordingTo VoterResponseModel.modelB →
                  FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                    VoterResponseModel.modelB xstar →
                    (finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                      0 < c →
                        (∀ n : ℕ,
                          c ≤
                            finiteDot
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar)
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (n + N)))) →
                          ∃ response : ℕ → Voter → Coord → ℝ,
                            (∀ t voter,
                              ModelBFiniteResponseAt SourceNorm.l2
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (t + N))
                                (ilvTailRadius r0 N t)
                                (M.utilityGradient voter
                                  (E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB (t + N)))
                                (response t voter)) ∧
                            ∀ᵐ sampledVoter
                                ∂theorem3FiniteWeightedVoterSequenceMeasure
                                  M.weight M.weight_nonneg M.weight_sum,
                              ∃ raw : ℕ → Coord → ℝ,
                              ∃ project : (Coord → ℝ) → Coord → ℝ,
                                UsesFiniteCoordinateNormDistance E ∧
                                Convex ℝ E.solutionSpace ∧
                                IsNormProjectionOnto E SourceNorm.l2 project ∧
                                (∀ t : ℕ,
                                  raw t = response t (sampledVoter t)) ∧
                                (∀ t : ℕ,
                                  Algorithm1ProjectedUpdate project (raw t)
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))) ∧
                                (∀ t : ℕ,
                                  FiniteFeasibleDirectionAt E.solutionSpace
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar))) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.r0, S.r0_pos, S.coordinate_continuity, S.ae_projected_trace⟩
  · rintro ⟨r0, hr0, hCoordinateContinuity, hAETrace⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         coordinate_continuity := hCoordinateContinuity
         ae_projected_trace := hAETrace }⟩

/--
Theorem 3 concrete field continuity source: the abstract paper continuity
assumption gives coordinatewise continuity of the concrete finite normalized
gradient field.
-/
theorem theorem3_field_coordinate_continuity_source_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty (FiniteTheorem3ConcreteFieldContinuitySource M) ↔
      (E.directionalFieldUniformlyContinuous →
        ∀ xstar i ε, 0 < ε →
          ∃ δ, 0 < δ ∧
            ∀ x : Coord → ℝ,
              finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
                |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                  finiteTheorem3DirectionalField M.weight
                    M.utilityGradient xstar i| < ε) := by
  constructor
  · rintro ⟨S⟩
    exact S.coordinate_continuity
  · intro h
    exact ⟨{ coordinate_continuity := h }⟩

/--
Primitive global projected Algorithm 1 trace generator for the corrected
Theorem 3 route.  This is the granular source record used by the full closeout
path: it exposes finite `L2` norm semantics, a sampled-stream-dependent
projection operator, projected global-tail Algorithm 1 updates, and the
positive-step feasibility of the fixed `G(x*)` direction from each projected
tail iterate.
-/
theorem theorem3_global_projected_algorithm1_trace_source_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty (FiniteTheorem3GlobalProjectedAlgorithm1TraceSource M) ↔
      ∃ r0 : ℝ,
        0 < r0 ∧
          ∃ hNorm : UsesFiniteCoordinateNormDistance E,
            ∃ project : (ℕ → Voter) → (Coord → ℝ) → Coord → ℝ,
              (∀ sampledVoter : ℕ → Voter,
                IsNormProjectionOnto E SourceNorm.l2
                  (project sampledVoter)) ∧
              (∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
                ConditionsC123 E →
                  E.directionalFieldUniformlyContinuous →
                    E.respondsAccordingTo VoterResponseModel.modelB →
                      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                        VoterResponseModel.modelB xstar →
                        (finiteTheorem3DirectionalField M.weight
                            M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                          0 < c →
                            (∀ n : ℕ,
                              c ≤
                                finiteDot
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient xstar)
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB (n + N)))) →
                              ∀ sampledVoter : ℕ → Voter,
                                ∀ t : ℕ,
                                  Algorithm1ProjectedUpdate
                                    (project sampledVoter)
                                    (fun i =>
                                      E.trajectory SourceNorm.l2
                                          VoterResponseModel.modelB
                                          (t + N) i +
                                        ilvTailRadius r0 N t *
                                          (M.utilityGradient (sampledVoter t)
                                            (E.trajectory SourceNorm.l2
                                              VoterResponseModel.modelB
                                              (t + N)) i /
                                            finiteCoordinateNorm SourceNorm.l2
                                              (M.utilityGradient
                                                (sampledVoter t)
                                                (E.trajectory SourceNorm.l2
                                                  VoterResponseModel.modelB
                                                  (t + N)))))
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))) ∧
              (∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
                ConditionsC123 E →
                  E.directionalFieldUniformlyContinuous →
                    E.respondsAccordingTo VoterResponseModel.modelB →
                      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                        VoterResponseModel.modelB xstar →
                        (finiteTheorem3DirectionalField M.weight
                            M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                          0 < c →
                            (∀ n : ℕ,
                              c ≤
                                finiteDot
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient xstar)
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB (n + N)))) →
                              ∀ sampledVoter : ℕ → Voter,
                                ∀ t : ℕ,
                                  FiniteFeasibleDirectionAt E.solutionSpace
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar)) := by
  constructor
  · rintro ⟨S⟩
    exact
      ⟨S.r0, S.r0_pos, S.normDistance, S.project, S.project_norm,
        S.projected_update, S.feasible_direction⟩
  · rintro
      ⟨r0, hr0, hNorm, project, hProjectNorm, hProjectedUpdate,
        hFeasibleDirection⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         normDistance := hNorm
         project := project
         project_norm := hProjectNorm
         projected_update := hProjectedUpdate
         feasible_direction := hFeasibleDirection }⟩

/--
Stricter primitive global projected Algorithm 1 trace generator for Theorem 3:
the aggregate `G(x*)` feasibility field is no longer primitive.  It is derived
from a common positive step that keeps every per-voter normalized-gradient move
inside the solution space, plus convexity of `X`.
-/
theorem theorem3_global_projected_algorithm1_update_source_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty (FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource M) ↔
      ∃ r0 : ℝ,
        0 < r0 ∧
          ∃ hNorm : UsesFiniteCoordinateNormDistance E,
            ∃ project : (ℕ → Voter) → (Coord → ℝ) → Coord → ℝ,
              (∀ sampledVoter : ℕ → Voter,
                IsNormProjectionOnto E SourceNorm.l2
                  (project sampledVoter)) ∧
              (∀ {N : ℕ},
                ∀ sampledVoter : ℕ → Voter,
                  ∀ t : ℕ,
                    Algorithm1ProjectedUpdate
                      (project sampledVoter)
                      (fun i =>
                        E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB
                            (t + N) i +
                          ilvTailRadius r0 N t *
                            (M.utilityGradient (sampledVoter t)
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB
                                (t + N)) i /
                              finiteCoordinateNorm SourceNorm.l2
                                (M.utilityGradient
                                  (sampledVoter t)
                                  (E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB
                                    (t + N)))))
                      (E.trajectory SourceNorm.l2
                        VoterResponseModel.modelB
                        (t + 1 + N))) := by
  constructor
  · rintro ⟨S⟩
    exact
      ⟨S.r0, S.r0_pos, S.normDistance, S.project, S.project_norm,
        S.projected_update⟩
  · rintro ⟨r0, hr0, hNorm, project, hProjectNorm, hProjectedUpdate⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         normDistance := hNorm
         project := project
         project_norm := hProjectNorm
         projected_update := hProjectedUpdate }⟩

/--
Record-free aggregate feasible-direction formula for the projected Theorem 3
residual argument.  The final no-hidden-premise closeout states that, in the
general constrained case, this formula may fail; it is not taken as a source
record premise.
-/
theorem theorem3_aggregate_feasible_direction_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    FiniteTheorem3AggregateFeasibleDirectionFormula M ↔
      ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
        ConditionsC123 E →
          E.directionalFieldUniformlyContinuous →
            E.respondsAccordingTo VoterResponseModel.modelB →
              FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                VoterResponseModel.modelB xstar →
                (finiteTheorem3DirectionalField M.weight
                    M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                  0 < c →
                    (∀ n : ℕ,
                      c ≤
                        finiteDot
                          (finiteTheorem3DirectionalField M.weight
                            M.utilityGradient xstar)
                          (finiteTheorem3DirectionalField M.weight
                            M.utilityGradient
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (n + N)))) →
                      ∀ t : ℕ,
                        FiniteFeasibleDirectionAt E.solutionSpace
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + 1 + N))
                          (finiteTheorem3DirectionalField M.weight
                            M.utilityGradient xstar) := by
  rfl

/--
Trace-only deterministic global projected Algorithm 1 source for the corrected
Theorem 3 route.  Field continuity is deliberately not part of this source; it
is supplied by `FiniteTheorem3ConcreteFieldContinuitySource`.
-/
theorem theorem3_global_projected_trace_deterministic_trace_core_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty
        (FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource
          M) ↔
      ∃ r0 : ℝ,
        0 < r0 ∧
          (∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
            ConditionsC123 E →
              E.directionalFieldUniformlyContinuous →
                E.respondsAccordingTo VoterResponseModel.modelB →
                  FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                    VoterResponseModel.modelB xstar →
                    (finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                      0 < c →
                        (∀ n : ℕ,
                          c ≤
                            finiteDot
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar)
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (n + N)))) →
                          ∃ response : ℕ → Voter → Coord → ℝ,
                            (∀ t voter,
                              response t voter =
                                fun i =>
                                  E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + N) i +
                                    ilvTailRadius r0 N t *
                                      (M.utilityGradient voter
                                        (E.trajectory SourceNorm.l2
                                          VoterResponseModel.modelB
                                          (t + N)) i /
                                        finiteCoordinateNorm SourceNorm.l2
                                          (M.utilityGradient voter
                                            (E.trajectory SourceNorm.l2
                                              VoterResponseModel.modelB
                                              (t + N))))) ∧
                            ∀ sampledVoter : ℕ → Voter,
                              ∃ raw : ℕ → Coord → ℝ,
                              ∃ project : (Coord → ℝ) → Coord → ℝ,
                                UsesFiniteCoordinateNormDistance E ∧
                                IsNormProjectionOnto E SourceNorm.l2 project ∧
                                (∀ t : ℕ,
                                  raw t = response t (sampledVoter t)) ∧
                                (∀ t : ℕ,
                                  Algorithm1ProjectedUpdate project (raw t)
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))) ∧
                                (∀ t : ℕ,
                                  FiniteFeasibleDirectionAt E.solutionSpace
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar))) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.r0, S.r0_pos, S.deterministic_projected_trace⟩
  · rintro ⟨r0, hr0, hTrace⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         deterministic_projected_trace := hTrace }⟩

/--
Raw deterministic global projected Algorithm 1 trace source for the corrected
Theorem 3 route.  This contains the pointwise sampled-voter trace alignment;
the C1 convexity interpretation is supplied separately by the full source model
and then combined into the proof-facing deterministic skeleton.
-/
theorem theorem3_global_projected_trace_deterministic_trace_source_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty
        (FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource
          M) ↔
      ∃ r0 : ℝ,
        0 < r0 ∧
          (E.directionalFieldUniformlyContinuous →
            ∀ xstar i ε, 0 < ε →
              ∃ δ, 0 < δ ∧
                ∀ x : Coord → ℝ,
                  finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
                    |finiteTheorem3DirectionalField M.weight
                        M.utilityGradient x i -
                      finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar i| < ε) ∧
          (∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
            ConditionsC123 E →
              E.directionalFieldUniformlyContinuous →
                E.respondsAccordingTo VoterResponseModel.modelB →
                  FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                    VoterResponseModel.modelB xstar →
                    (finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                      0 < c →
                        (∀ n : ℕ,
                          c ≤
                            finiteDot
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar)
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (n + N)))) →
                          ∃ response : ℕ → Voter → Coord → ℝ,
                            (∀ t voter,
                              response t voter =
                                fun i =>
                                  E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + N) i +
                                    ilvTailRadius r0 N t *
                                      (M.utilityGradient voter
                                        (E.trajectory SourceNorm.l2
                                          VoterResponseModel.modelB
                                          (t + N)) i /
                                        finiteCoordinateNorm SourceNorm.l2
                                          (M.utilityGradient voter
                                            (E.trajectory SourceNorm.l2
                                              VoterResponseModel.modelB
                                              (t + N))))) ∧
                            ∀ sampledVoter : ℕ → Voter,
                              ∃ raw : ℕ → Coord → ℝ,
                              ∃ project : (Coord → ℝ) → Coord → ℝ,
                                UsesFiniteCoordinateNormDistance E ∧
                                IsNormProjectionOnto E SourceNorm.l2 project ∧
                                (∀ t : ℕ,
                                  raw t = response t (sampledVoter t)) ∧
                                (∀ t : ℕ,
                                  Algorithm1ProjectedUpdate project (raw t)
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))) ∧
                                (∀ t : ℕ,
                                  FiniteFeasibleDirectionAt E.solutionSpace
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar))) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.r0, S.r0_pos, S.coordinate_continuity,
      S.deterministic_projected_trace⟩
  · rintro ⟨r0, hr0, hCoordinateContinuity, hTrace⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         coordinate_continuity := hCoordinateContinuity
         deterministic_projected_trace := hTrace }⟩

/--
Proof-facing deterministic global projected Algorithm 1 trace skeleton for the
corrected Theorem 3 route.  It combines the raw pointwise trace source with the
C1 convexity interpretation needed by the projection residual argument.
-/
theorem theorem3_global_projected_trace_deterministic_skeleton_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty
        (FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton
          M) ↔
      ∃ r0 : ℝ,
        0 < r0 ∧
          (E.directionalFieldUniformlyContinuous →
            ∀ xstar i ε, 0 < ε →
              ∃ δ, 0 < δ ∧
                ∀ x : Coord → ℝ,
                  finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
                    |finiteTheorem3DirectionalField M.weight
                        M.utilityGradient x i -
                      finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar i| < ε) ∧
          (ConditionsC123 E → Convex ℝ E.solutionSpace) ∧
          (∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
            ConditionsC123 E →
              E.directionalFieldUniformlyContinuous →
                E.respondsAccordingTo VoterResponseModel.modelB →
                  FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                    VoterResponseModel.modelB xstar →
                    (finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                      0 < c →
                        (∀ n : ℕ,
                          c ≤
                            finiteDot
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar)
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (n + N)))) →
                          ∃ response : ℕ → Voter → Coord → ℝ,
                            (∀ t voter,
                              ModelBFiniteResponseAt SourceNorm.l2
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (t + N))
                                (ilvTailRadius r0 N t)
                                (M.utilityGradient voter
                                  (E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB (t + N)))
                                (response t voter)) ∧
                            ∀ sampledVoter : ℕ → Voter,
                              ∃ raw : ℕ → Coord → ℝ,
                              ∃ project : (Coord → ℝ) → Coord → ℝ,
                                UsesFiniteCoordinateNormDistance E ∧
                                IsNormProjectionOnto E SourceNorm.l2 project ∧
                                (∀ t : ℕ,
                                  raw t = response t (sampledVoter t)) ∧
                                (∀ t : ℕ,
                                  Algorithm1ProjectedUpdate project (raw t)
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))) ∧
                                (∀ t : ℕ,
                                  FiniteFeasibleDirectionAt E.solutionSpace
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar))) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.r0, S.r0_pos, S.coordinate_continuity,
      S.convex_solutionSpace, S.deterministic_projected_trace⟩
  · rintro ⟨r0, hr0, hCoordinateContinuity, hConvex, hTrace⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         coordinate_continuity := hCoordinateContinuity
         convex_solutionSpace := hConvex
         deterministic_projected_trace := hTrace }⟩

/--
Finite-coordinate reading of the abstract trajectory-convergence predicate used
by the exact Theorem 3 statement adapter.
-/
theorem finite_coordinate_convergence_source_formula
    {Voter Coord : Type*}
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (FiniteCoordinateConvergenceSource E) ↔
      ∀ {q : SourceNorm} {model : VoterResponseModel} {xstar : Coord → ℝ},
        ILVTrajectoryConvergesTo E q model xstar →
          FiniteCoordinateILVTrajectoryConvergesTo E q model xstar := by
  constructor
  · rintro ⟨S⟩
    exact S.finite_coordinate_of_ilv_converges
  · intro h
    exact ⟨{ finite_coordinate_of_ilv_converges := h }⟩

/--
Sampled projected full finite-coordinate source semantics used by the
no-hidden-premise closeout route.  Theorem 2 and Proposition 1 enter through
sampled-process records whose marginal-law/bad-event fields derive deterministic
noncollision internally.  Theorem 3 includes projected Algorithm 1 update
semantics but deliberately does not assume aggregate feasibility.
-/
theorem finite_coordinate_full_sampled_projected_source_semantics_formula
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (FiniteCoordinateILVFullSampledProjectedSourceSemantics E) ↔
      ∃ theorem2 : Theorem2SampledSourceSemantics E,
        ∃ proposition1 : Proposition1ConcreteComponentSampledSourceSemantics E,
          ∃ proposition2 : Proposition2SourceSemantics E,
            ∃ field : FiniteTheorem3DirectionalFieldModel E,
              ∃ hConvex : C1ConvexSolutionSpaceSource E,
                ∃ hConvergence : FiniteCoordinateConvergenceSource E,
                  ∃ hContinuity :
                    FiniteTheorem3ConcreteFieldContinuitySource field,
                    Nonempty
                      (FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource
                        field) := by
  constructor
  · rintro ⟨M⟩
    exact
      ⟨M.theorem2_source, M.proposition1_source,
        M.proposition2_source, M.theorem3_field,
        M.theorem3_convex_solutionSpace, M.theorem3_convergence,
        M.theorem3_continuity, ⟨M.theorem3_algorithm1_update⟩⟩
  · rintro
      ⟨theorem2, proposition1, proposition2, field, hConvex,
        hConvergence, hContinuity, ⟨algorithm1Update⟩⟩
    exact
      ⟨{ theorem2_source := theorem2
         proposition1_source := proposition1
         proposition2_source := proposition2
         theorem3_field := field
         theorem3_convex_solutionSpace := hConvex
         theorem3_convergence := hConvergence
         theorem3_continuity := hContinuity
         theorem3_algorithm1_update := algorithm1Update }⟩

/--
Theorem 2 source-semantics interface: exact expansion of the deterministic
non-SSGM data still needed before invoking the SSGM convergence theorem.  The
trace source includes a selected-voter stream, so the sampled ideal used in the
finite `Lp` cost is `E.ideal (voter t)`.
-/
theorem theorem2_source_semantics_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (Theorem2PrimitiveSourceSemantics E) ↔
      ∃ r0 : ℝ,
        ∃ hNorm : UsesFiniteCoordinateNormDistance E,
          ∃ c3Data : FiniteCoordinateIdealDistributionData Coord,
            ∃ hTrace :
              (∀ {p q : ℝ},
                IsLpNormedUtilities E (SourceNorm.lp p) →
                  E.respondsAccordingTo VoterResponseModel.modelB →
                    HolderDualFinite p q →
                      FiniteModelBILVAlgorithm1PrimitiveTraceSource E p q r0),
              0 < r0 := by
  constructor
  · rintro ⟨S⟩
    exact
      ⟨S.r0, S.hNorm, S.c3Data, S.modelB_primitive_trace, S.r0_pos⟩
  · rintro ⟨r0, hNorm, c3Data, hTrace, hr0⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         hNorm := hNorm
         c3Data := c3Data
         modelB_primitive_trace := hTrace }⟩

/--
Proposition 1 concrete component source-semantics interface: exact expansion of
the deterministic weighted-Euclidean component-distance trace data and
social-objective source data.  The older `Proposition1SourceSemantics`
weighted-`L2` input is derived from this row by first deriving component
subgradients and then summing them with the nonnegative source coefficients.
-/
theorem proposition1_concrete_component_source_semantics_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (Proposition1ConcreteComponentSourceSemantics E) ↔
      ∃ hWeightedInputs :
        (∀ {Component : Type}
          {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
          {model : VoterResponseModel},
          ConditionsC123 E →
            IsWeightedEuclideanUtilitiesWith E W →
              (model = VoterResponseModel.modelA ∨
                  model = VoterResponseModel.modelB) →
                  E.respondsAccordingTo model →
                    Σ r0 : ℝ,
                      WeightedEuclideanL2ConcreteComponentTraceSource
                        E W model r0),
        ∃ hWeightedObjective :
          (∀ {Component : Type}
            {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component},
            ConditionsC123 E →
              IsWeightedEuclideanUtilitiesWith E W →
                WeightedEuclideanSocialObjectiveFormulaSource E W),
          True := by
  constructor
  · rintro ⟨S⟩
    exact
      ⟨S.weighted_l2_concrete_component_inputs, S.weighted_objective,
        trivial⟩
  · rintro ⟨hWeightedInputs, hWeightedObjective, _⟩
    exact
      ⟨{ weighted_l2_concrete_component_inputs := hWeightedInputs
         weighted_objective := hWeightedObjective }⟩

/--
Proposition 1 source-semantics interface: exact expansion of the deterministic
weighted-Euclidean SSGM-input and social-objective source data.
-/
theorem proposition1_source_semantics_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (Proposition1SourceSemantics E) ↔
      ∃ hWeightedInputs :
        (∀ {Component : Type}
          {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
          {model : VoterResponseModel},
          ConditionsC123 E →
            IsWeightedEuclideanUtilitiesWith E W →
              (model = VoterResponseModel.modelA ∨
                  model = VoterResponseModel.modelB) →
                  E.respondsAccordingTo model →
                    Σ r0 : ℝ, WeightedEuclideanL2SSGMTraceSource E W model r0),
        ∃ hWeightedObjective :
          (∀ {Component : Type}
            {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component},
            ConditionsC123 E →
              IsWeightedEuclideanUtilitiesWith E W →
                WeightedEuclideanSocialObjectiveFormulaSource E W),
          True := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.weighted_l2_inputs, S.weighted_objective, trivial⟩
  · rintro ⟨hWeightedInputs, hWeightedObjective, _⟩
    exact
      ⟨{ weighted_l2_inputs := hWeightedInputs
         weighted_objective := hWeightedObjective }⟩

/--
Proposition 2 source-semantics interface: exact expansion of the deterministic
median-set and local `L∞` response data.
-/
theorem proposition2_source_semantics_formula
    {Voter Point : Type*} (E : ILVEnvironment Voter Point) :
    Nonempty (Proposition2SourceSemantics E) ↔
      ∃ hMedian :
        (∀ {Axis : Type}
          {D : DecomposableStructure Voter Point Axis},
          ConditionsC123 E →
            IsDecomposableUtilitiesWith E D →
              DecomposableMedianCarrier E D),
        ∃ hLinfResponse :
          (∀ {Axis : Type}
            {D : DecomposableStructure Voter Point Axis},
            ConditionsC123 E →
              IsDecomposableUtilitiesWith E D →
                DecomposableLinfLocalResponseBridge E D),
          True := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.medianCarrier, S.linfResponse, trivial⟩
  · rintro ⟨hMedian, hLinfResponse, _⟩
    exact
      ⟨{ medianCarrier := hMedian
         linfResponse := hLinfResponse }⟩

/--
Separate theorem source semantics plus an explicit SSGM theorem bundle imply
the four SSGM-backed endpoint consequences.  This row exposes the exact
non-SSGM source obligations before the single reusable SSGM boundary is used.
-/
theorem finite_coordinate_source_semantics_ssgm_consequences
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (T2 : Theorem2PrimitiveSourceSemantics E)
    (P1 : Proposition1SourceSemantics E)
    (P2 : Proposition2SourceSemantics E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    ILVSSGMConvergenceConsequences E := by
  exact
    proof_ilvSSGMConvergenceConsequences_of_sourceSemantics_ssgmConvergence
      (theorem2SourceSemantics_of_primitive T2) P1 P2 S

/--
Theorem 1: under C1-C3, Lp-normed utilities, Model A or B response, and
`(p,q) = (2,2), (1,inf), (inf,1)`, ILV with Lq neighborhoods converges w.p. 1
to the societal optimum for finite-coordinate environments.  The visible source
hypotheses themselves construct the deterministic case certificate; the only
remaining input used by this row is the theorem-shaped SSGM convergence bundle
in `Assumptions.lean`.

Source status: conditional boundary; the deterministic source hypotheses are
visible and the remaining convergence input is the approved SSGM theorem.
-/
theorem theorem1_lp_normed_dual_cases
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    theorem1Statement E := by
  exact
    theorem1Statement_of_sourceBridge_ssgmConvergence
      (theorem1SourceToSSGMBridge_of_visible_hypotheses E)
      hSSGM.theorem1_convergence

/--
Theorem 2: under C1-C3, Lp-normed utilities, and Model B response, ILV with Lq
neighborhoods converges w.p. 1 to the societal optimum for finite Holder-dual
`p,q > 0`, for finite-coordinate environments satisfying the concrete
deterministic source model.  The only remaining input used by this row is the
theorem-shaped SSGM convergence bundle in `Assumptions.lean`.

Source status: conditional boundary; the deterministic source semantics are
explicit and the remaining convergence input is the approved SSGM theorem.
-/
theorem theorem2_modelB_holder_dual_norms
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (T2 : Theorem2PrimitiveSourceSemantics E)
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    theorem2Statement E := by
  exact
    theorem2Statement_of_sourceSemantics_ssgmConvergence
      (theorem2SourceSemantics_of_primitive T2)
      hSSGM.theorem2_convergence

/--
Proposition 1: under C1-C3 and weighted-Euclidean utilities, ILV with L2
neighborhoods converges w.p. 1 to the societal optimum for Model A or B
response, for finite-coordinate environments satisfying the concrete
deterministic source model.  The only remaining input used by this row is the
theorem-shaped SSGM convergence bundle in `Assumptions.lean`.
-/
theorem proposition1_weighted_euclidean_l2
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (P1 : Proposition1SourceSemantics E)
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    proposition1Statement E := by
  exact
    proposition1Statement_of_sourceSemantics_ssgmConvergence P1
      hSSGM.proposition1_convergence

/--
Proposition 2: under C1-C3 and decomposable utilities, ILV with Linf
neighborhoods converges w.p. 1 to a point in the coordinate-wise median set for
Model A or B response, for finite-coordinate environments satisfying the
concrete deterministic source model.  The only remaining input used by this row
is the theorem-shaped SSGM convergence bundle in `Assumptions.lean`.
-/
theorem proposition2_decomposable_linf_medians
    {Voter : Type} {Coord : Type} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (S : Proposition2FiniteCoordinateSourceSemantics E)
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    proposition2FiniteCoordinateStatement E := by
  exact
    proof_proposition2FiniteCoordinateStatement_of_finiteCoordinateSourceSemantics_ssgmConvergence
      S
      hSSGM.proposition2_convergence

/--
Proposition 2, finite-coordinate/product-box route: under C1-C3 and
decomposable utilities whose coordinates are the ambient finite coordinates,
ILV with `L∞` neighborhoods converges w.p. 1 to the coordinatewise median set
for Model A or B response.  The `L∞` replacement property is derived from the
finite source semantics; the only remaining input here is the theorem-shaped
SSGM convergence bundle.
-/
theorem proposition2_finite_coordinate_decomposable_linf_medians
    {Voter : Type} {Coord : Type} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (S : Proposition2FiniteCoordinateSourceSemantics E)
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    proposition2FiniteCoordinateStatement E := by
  exact
    proof_proposition2FiniteCoordinateStatement_of_finiteCoordinateSourceSemantics_ssgmConvergence
      S hSSGM.proposition2_convergence

/--
Theorem 3 corrected projected-trace route: this is the paper-faithful version
of the sharper finite trace endpoint.  If the tail beginning at global time `N`
is represented by a pathwise projected Algorithm 1 trace using the original
radius `r0 / (N + t + 1)`, then every coordinatewise-convergent Model B `L2`
trajectory converges to a directional equilibrium.
-/
theorem theorem3_convergent_l2_modelB_is_directional_equilibrium_global_projected_trace
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalPathwiseSemantics G) :
    ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            ∀ xstar,
              FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                VoterResponseModel.modelB xstar →
                IsDirectionalEquilibrium E xstar := by
  intro hC hContinuous hResponse xstar hConverges
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedTraceGlobalPathwise
    G D hC hContinuous hResponse hConverges

/--
Theorem 3 corrected almost-sure trace route: the explicit source trace skeleton
is almost-sure with respect to the iid weighted-voter product law.  The
finite-dot concentration theorem and the extraction of a good pathwise stream
are proved in `ProofInterface.lean`.
-/
theorem theorem3_convergent_l2_modelB_is_directional_equilibrium_global_ae_trace
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (G : FiniteTheorem3DirectionalFieldModel E)
    (S : FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalAETraceSkeleton G) :
    ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            ∀ xstar,
              FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                VoterResponseModel.modelB xstar →
                IsDirectionalEquilibrium E xstar := by
  intro hC hContinuous hResponse xstar hConverges
  exact
    proof_theorem3_finite_projectedTraceGlobalAETraceSkeleton_directionalEquilibrium
      G S hC hContinuous hResponse hConverges

/--
Theorem 3 projected/constrained alternative from sampled projected source
semantics.  Without assuming aggregate feasibility, Lean proves that either the
paper's zero-field conclusion holds or the aggregate feasible-direction formula
fails.
-/
theorem theorem3_zero_or_no_aggregate_feasible_direction_formula
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (M : FiniteCoordinateILVFullSampledProjectedSourceSemantics E) :
    ConditionsC123 E →
      E.directionalFieldUniformlyContinuous →
        E.respondsAccordingTo VoterResponseModel.modelB →
          ∀ xstar,
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.theorem3_field.weight
                  M.theorem3_field.utilityGradient xstar =
                  fun _ => (0 : ℝ)) ∨
                ¬ FiniteTheorem3AggregateFeasibleDirectionFormula
                  M.theorem3_field := by
  intro hC hContinuous hResponse xstar hConverges
  exact
    proof_theorem3_finite_fullSampledProjectedSourceSemantics_zero_or_no_aggregateFeasibleDirectionFormula
      M hC hContinuous hResponse hConverges

/--
Exact original Theorem 3 statement from sampled projected source semantics in
the full finite-coordinate space.  Here aggregate feasibility is derived from
`E.solutionSpace = Set.univ`, so no aggregate-feasibility source record is
assumed.

Source status: conditional boundary; this is the exact paper statement only in
the explicit full-space case `E.solutionSpace = Set.univ`.
-/
theorem theorem3_statement_of_full_sampled_projected_source_semantics_univ
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (M : FiniteCoordinateILVFullSampledProjectedSourceSemantics E)
    (hUniv : E.solutionSpace = (Set.univ : Set (Coord → ℝ))) :
    theorem3Statement E := by
  exact
    proof_theorem3Statement_of_fullSampledProjectedSourceSemantics_univ_solutionSpace
      M hUniv

/--
No-hidden-premise sampled projected finite-coordinate paper closeout with an
explicit SSGM theorem bundle.
-/
theorem finite_coordinate_full_sampled_projected_paper_consequences_with_ssgm
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (M : FiniteCoordinateILVFullSampledProjectedSourceSemantics E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    FiniteCoordinateILVFullProjectedPaperConsequences M := by
  exact
    proof_finiteCoordinateILVFullProjectedPaperConsequences_of_fullSampledProjectedSourceSemantics_ssgmConvergence
      M S

/--
No-hidden-premise sampled projected finite-coordinate paper closeout using the
approved single theorem-shaped SSGM boundary premise and no paper-local Lean
axiom of any kind.
-/
theorem finite_coordinate_full_sampled_projected_paper_consequences
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (M : FiniteCoordinateILVFullSampledProjectedSourceSemantics E)
    (hSSGM : assumption_ssgm_convergence_theorem E) :
    FiniteCoordinateILVFullProjectedPaperConsequences M := by
  exact
    proof_finiteCoordinateILVFullProjectedPaperConsequences_of_fullSampledProjectedSourceSemantics
      M hSSGM

end GKGMM19IterativeLocalVoting
