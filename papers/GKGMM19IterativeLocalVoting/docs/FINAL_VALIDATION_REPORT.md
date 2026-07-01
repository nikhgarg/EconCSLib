# Final Validation Report: Iterative Local Voting for Collective Decision-making in Continuous Spaces

## 1. Human Verdict
Partially formalized. Theorems 1-2 and Propositions 1-2 are formalized except
for a single reusable-library theorem proving stochastic subgradient descent
convergence. Theorem 3 is proved as a constrained alternative in general and
recovers the paper's original statement under the explicit full-space condition.
No human dashboard sign-off has been recorded; detailed validation evidence is
below.

## 2. Closeout Status
- Completion status: partially formalized.
- One-sentence recap: Only SSGM convergence remains as a reusable-library
  boundary; Theorem 3 is handled by the constrained/full-space split above.

## 3. Source and Scope
- Paper: Garg, Kamble, Goel, Marn, and Munagala, "Iterative Local Voting for
  Collective Decision-making in Continuous Spaces".
- Source version: JAIR 64 (2019), 315-355, published 2019-02-18,
  DOI `10.1613/jair.1.11358`.
- Auxiliary source used for labels: arXiv:1702.07984v3.
- Lean folder: `papers/GKGMM19IterativeLocalVoting`.
- Human-facing theorem file:
  `papers/GKGMM19IterativeLocalVoting/PaperInterface.lean`.
- Proof-facing bridge file:
  `papers/GKGMM19IterativeLocalVoting/ProofInterface.lean`.
- Paper assumption file:
  `papers/GKGMM19IterativeLocalVoting/Assumptions.lean`.
- Source/subclaim map:
  `papers/GKGMM19IterativeLocalVoting/paper_statement_map.json`.
- Validator ledger:
  `papers/GKGMM19IterativeLocalVoting/VALIDATOR_LEDGER.md`.
- Machine export:
  `papers/GKGMM19IterativeLocalVoting/review_status_export.json`.

## 4. Researcher Summary of Checked Results
- The paper's ILV definitions and source models are represented at the paper-facing interface.
- Theorems 1-2 and Propositions 1-2 are proved up to the single reusable stochastic-subgradient convergence theorem.
- Theorem 3 is proved as a constrained alternative in general, and the original statement is recovered under the explicit full-space condition.
- No other non-paper mathematical assumption is intended beyond the SSGM convergence boundary.

## 5. Remaining Boundaries and Gaps
The only intended remaining mathematical boundary for Theorems 1-2 and Propositions 1-2 is the reusable stochastic subgradient descent convergence theorem. Theorem 3 has no SSGM boundary; in general constrained spaces Lean proves the constrained alternative, and the original statement is recovered under the explicit full-space condition.

## 6. Additional Assumptions Beyond Paper
- None.

The SSGM convergence theorem is not an additional paper assumption. It is the
remaining reusable-library theorem recorded in Section 5, and the paper remains
partially formalized until that theorem is proved and instantiated for the
finite-coordinate ILV source model.

## 7. Proof-Strategy Deviations
None. The human-facing differences are formalization boundaries, not separate
proof-strategy deviations: Theorems 1-2 and Propositions 1-2 depend on the
single reusable-library stochastic subgradient convergence theorem, and Theorem
3 is reported as a statement/status boundary in the verdict and DAG.

## 8. Proof Tricks Worth Reusing
- None

## 9. Paper Issues or Caveats
Theorem 3 appears to need an explicit feasibility condition for the aggregate direction at a constrained limit point. In full space this condition is automatic, and the formalization recovers the paper's stated conclusion; for general constrained spaces, the formalized result is the weaker alternative that either the aggregate directional field vanishes or the aggregate direction is not feasible. This is recorded as a statement-level caveat, not as a broader objection to the economic model.

## 10. Detailed Formalization Evidence
- The source-facing definition and formula rows compile for C1-C3, the
  Algorithm 1 radius schedule, radius limit-to-zero, squared-radius
  summability, divergent positive-radius partial sums, positive-radius
  non-summability, local neighborhood, norm projection, projected update,
  projected trajectory feasibility, stopping-window condition, stop condition,
  Model A response, Model A `IsMaxOn`, Definition 1 Lp utilities,
  finite-coordinate L1/L2/Linf/Lp utility formulas, Model A cost-minimizer
  bridge, Model B finite-coordinate response, the sign-correct Model B
  Lp-gradient response, Definition 2 weighted-Euclidean utilities, and
  Definition 3 decomposable utilities.
- Appendix C.4 Lemma 3 support rows compile: the displayed candidate-gradient
  formula, the Holder-dual finite-coordinate norm equality, the Frechet
  derivative attachment, bounded-density coordinate-equality null-event
  reductions, product-measure bad-event nullness, and a.e. coordinate
  noncollision.
- The deterministic finite-coordinate source-semantics interface is explicit:
  theorem-specific rows expand Theorem 2 source semantics, Proposition 1 source
  semantics, Proposition 2 finite-coordinate/product-box source semantics, and
  granular full Theorem 3 source semantics.  These rows expose the positive
  Algorithm 1 radius, concrete norm semantics, finite-coordinate
  C3/product-density data, Model B trace source semantics with sampled ideals
  tied to selected voters, weighted-Euclidean raw trace source with sampled
  voters, sampled costs as negative voter utilities, projected updates,
  sample-subgradient certificates, social-utility maximizer source formulas,
  decomposable median-set source formulas, and finite-coordinate `L∞`
  product-box replacement semantics.  Weighted trajectory feasibility, the
  weighted SSGM step-size package, weighted social-objective bridge, median
  carrier, and local response bridge are derived from those fields, while the
  proof-facing Theorem 2 trace/finite-SSGM bridge and weighted SSGM input
  carrier retain their sampled-voter cost identities.
- The interface now also exposes the deterministic provenance rows for the
  finite-coordinate norm-distance interpretation, the concrete C3
  product-density data/carrier, the Proposition 2 median-set source and carrier,
  and the Proposition 2 `L∞` coordinate-replacement/local-response bridge.
- For Proposition 2, the local `L∞` response bridge is no longer only a raw
  source field: `decomposableLinfLocalResponseBridge_of_coordinateReplacement`
  proves it from decomposable additivity plus a product-coordinate replacement
  property for local `L∞` query sets.  For finite coordinate-vector
  environments with identity coordinate projections, Lean also proves
  `decomposableLinfCoordinateReplacement_of_finiteCoordinate`, deriving that
  replacement property from finite `L∞` norm semantics and explicit product-box
  solution-space closure.
- The proof-facing Proposition 2 fixed-decomposition routes
  `proposition2_fixedDecomposition_convergence_of_sourceSemantics_ssgmConvergence`
  and
  `proposition2_fixedDecomposition_convergence_of_finiteCoordinateSourceSemantics_ssgmConvergence`
  avoid the global `Proposition2SourceSemantics` package for a supplied
  decomposition: a median-set membership formula plus coordinate replacement,
  together with the single SSGM theorem, imply the median-set convergence
  conclusion for that decomposition.  The finite-coordinate product-box closure
  and `L∞` coordinate-replacement source records are now expanded in
  `PaperInterface.lean`.
- The four convergence endpoints are not assumed directly. They are projected
  from `ILVSSGMConvergenceConsequences`, which is derived by
  `ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence` from
  the concrete finite-coordinate source model plus the single theorem-shaped
  SSGM axiom.
- Theorem 3 is separated from the SSGM boundary.  The current route uses
  `FiniteTheorem3DirectionalFieldModel` for the displayed field
  `G(x) = E_v[grad f_v(x) / ||grad f_v(x)||_2]`, proves the local drift
  consequence of nonzero `G(x*)`, proves the finite-coordinate convergence
  contradiction, and pushes the stochastic/projection work down to the corrected
  global-radius projected trace.  Lean proves the finite-dot raw-response
  expectation identity, the positive scalar drift from coordinate-continuity and
  convergence, the projection residual identity and nonpositivity geometry, iid
  weighted-voter finite-dot concentration, and the AE-to-pathwise global trace
  bridge.  The active source-side premise visible in the closeout model is the
  split `FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource`, which supplies
  finite `L2` norm semantics, sampled-stream projection operators, and projected
  global-tail updates.  The old aggregate feasible-direction record is no
  longer part of the closeout source package.  Lean instead exposes the
  record-free `FiniteTheorem3AggregateFeasibleDirectionFormula`, proves the
  constrained alternative, and proves exact recovery when
  `E.solutionSpace = Set.univ`.  Lean also proves
  `proof_singleton_solutionSpace_not_force_aggregate_feasible_direction` and
  `proof_theorem3_abstract_hypotheses_do_not_imply_statement`, showing that the
  current C1/projection/convergence/directional-field hypotheses alone do not
  imply the needed feasible-direction premise or the final Theorem 3 statement.
  Theorem 3 also now has two explicit repaired consequences: the closed
  constrained alternative
  `proof_theorem3_finite_zero_or_no_aggregateFeasibleDirectionFormula_of_convergent_projectedUpdate`,
  which says projected updates plus convergence give either `G(x*) = 0` or the
  aggregate feasible-direction formula fails, and the full-space recovery theorem
  `proof_theorem3Statement_of_fullSampledProjectedSourceSemantics_univ_solutionSpace`,
  which recovers the original directional-equilibrium endpoint when
  `E.solutionSpace = Set.univ`.

## 11. Paper Assumption Provenance
| Assumption declaration | Validator judgment | Source / boundary | Premise judgments | Comments |
| --- | --- | --- | --- | --- |
| `assumption_conditions_c123` | source condition | JAIR 2019 Section 3, conditions C1-C3 | `hC : assumption_conditions_c123 E` is source text | Bundles the stated model conditions: nonempty bounded closed convex solution space, unique ideal points, and bounded measurable density for independently drawn ideal points. |
| `assumption_ssgm_convergence_theorem` | formalization boundary | Future SSGM convergence theorem, not a source assumption | `hSSGM : assumption_ssgm_convergence_theorem E` is a formalization boundary | Single approved theorem-shaped library boundary returning `FiniteCoordinateILVSSGMConvergenceTheorems E`; endpoint consequences are derived separately. |

## 12. Statement Validator Findings
The declaration-keyed source/subclaim map and all LLM sidecars are current.
`python3 scripts/review_dashboard.py --paper GKGMM19IterativeLocalVoting --statement-precheck`
reports no missing or stale sidecars.

Rows marked strict `mismatch` with `resolution: "conditional_boundary"`:
- `theorem1_lp_normed_dual_cases`
- `theorem2_modelB_holder_dual_norms`
- `proposition1_weighted_euclidean_l2`
- `proposition2_decomposable_linf_medians`
- `theorem3_statement_of_full_sampled_projected_source_semantics_univ`

Reason: the Lean rows prove finite-coordinate conditional versions with visible
theorem-specific deterministic source-semantics premises. Theorem 2 takes
`Theorem2PrimitiveSourceSemantics E`; Proposition 1 takes
`Proposition1SourceSemantics E`; Proposition 2 takes
`Proposition2FiniteCoordinateSourceSemantics E`; Theorem 3 takes
`FiniteCoordinateILVFullSampledProjectedSourceSemantics E` and the explicit
full-space premise `E.solutionSpace = Set.univ`. The source theorem statements
do not state those extra finite-coordinate data packages or the full-space
restriction. This is the intended current conditional boundary, not a hidden
claim of full theorem equivalence.
Theorem 1-2 and Propositions 1-2 also name
`assumption_ssgm_convergence_theorem` as the external-library SSGM theorem
boundary.

No statement rows are currently marked `uncertain`. Theorem 3 remains a strict
`mismatch` with `resolution: "conditional_boundary"` because the exact adapter
is conditional on granular full finite-coordinate source semantics.  The
concrete `FiniteTheorem3DirectionalFieldModel` supplies the displayed field
formula, so the remaining mismatch is source-semantics/trace alignment with the
abstract paper theorem statement, not an abstract-field representation gap.

## 13. Library Lift Pass
- Reusable modules already introduced or used include:
  `EconCSLib.Foundations.Math.FiniteDimensionalNorms`,
  `EconCSLib.Foundations.Math.FiniteDimensionalNormsDerivative`,
  `EconCSLib.Foundations.Optimization.StochasticSubgradient`, and
  `EconCSLib.Foundations.Probability.BoundedDensity`.
- Future reusable work should prove the SSGM convergence theorem in a shared
  optimization/probability layer and then replace
  `assumption_ssgm_convergence_theorem`.
- The dashboard parser was updated to include `axiom` declarations in
  assumption-source files so proof-boundary axioms appear in the assumption
  provenance surface and cannot be hidden from the closeout metadata.

## 14. DAG Audit
- DAG source: `papers/GKGMM19IterativeLocalVoting/DependencyDAG.tex`.
- Rendered DAG PDF: `papers/GKGMM19IterativeLocalVoting/DependencyDAG.pdf`.
- Visual layout inspection: completed after regenerating the DAG PDF from the
  updated TeX source; the rendered graph has readable paper-result, model,
  partial-boundary, and reusable-library nodes without overlapping labels,
  boxes, or arrows.
- The DAG records the single SSGM theorem-shaped boundary, the Lean-proved
  Theorem 3 constrained alternative, and the exact Theorem 3 full-space
  recovery rather than presenting those as hidden paper assumptions.

## 15. Validation Checks
- `lake build GKGMM19IterativeLocalVoting`: passed.
- `python3 -m py_compile scripts/review_dashboard.py`: passed after the axiom
  parser update.
- Lean footprint: 23,379 lines across paper-local Lean files, including 2,723
  lines in `PaperInterface.lean`; the human review surface exposes 42 dashboard
  rows from 107 paper-interface declarations.
- JSON sidecar validation with `python3 -m json.tool`: passed for
  `lean_to_tex_llm.json`, `statement_match_llm.json`, and
  `assumption_match_llm.json`.
- Statement precheck: current 40-row non-assumption statement surface: 40 drafts
  and 40 judgments, 0 missing, 0 stale, 35 matches, 5 strict mismatches accepted
  as conditional boundaries, 0 unresolved mismatches, 0 uncertain.
- Review-surface audit: current 42-row dashboard surface; the no-paper-context
  surface audit is fresh and passes.
- Assumption precheck/export: current for the configured assumption rows; 2
  configured assumption rows, 0 missing, 0 stale, 1 `paper_condition`, 1
  `partial_boundary`, and 2 premise judgments.  The recursive source-record
  judge sidecar is also current and reports 0 unresolved or unapproved fields.
- Direct targeted `#print axioms` pass over the curated review rows: passed.
  All non-convergence formula/support rows and Theorem 3 depend only on
  standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`),
  except `algorithm1_projected_update_formula`, which reports no axioms. Exactly
  the four SSGM convergence endpoint rows and the boundary axiom itself also
  depend on `assumption_ssgm_convergence_theorem`. A later targeted axiom check
  for the new Theorem 2 selected-voter trace/finite-SSGM bridge cost rows also
  reports only standard Lean foundations; the full closeout theorem still
  reports exactly one paper-local dependency,
  `assumption_ssgm_convergence_theorem`.
- Placeholder/declaration scan: no Lean `sorry` or `admit` in the GKGMM Lean
  files or touched reusable modules. The only actual `axiom` declaration in the
  GKGMM surface is the approved
  `assumption_ssgm_convergence_theorem`.
- Full `--precheck`: current after the sampled projected source split sees
  `source_record_match_llm.json` synced to audit digest
  `95b8554bfdc06bcb346443e11bdaa7cd49de7da918adedef8339c71b7cda45d9`.
  The approved `partial_boundary` premise remains intentional; there is
  no hidden-premise/source-record warning.

## 16. Paper-Facing Statement Validator Ledger
The full generated validator ledger is stored at
`papers/GKGMM19IterativeLocalVoting/VALIDATOR_LEDGER.md`.

Summary:
- 35 statement rows: `matches`.
- 5 statement rows: strict `mismatch` with `resolution:
  "conditional_boundary"` for the conditional finite-coordinate convergence
  endpoints and Theorem 3's visible finite-coordinate/global-trace source
  premise.
- 0 statement rows: `uncertain`.
- 1 assumption row: `paper_condition`.
- 1 proof-boundary row: `partial_boundary`.

This ledger is provenance for statement-target metadata. It does not change the
human-only `human_review.reviewed_rows` counter.

## 17. DAG Audit
- DAG source artifact: `DependencyDAG.tex`.
- Rendered DAG artifact: `DependencyDAG.pdf`.
- Rendered/visual inspection evidence: the `DependencyDAG.pdf` layout was
  regenerated from `DependencyDAG.tex` and visually inspected for readable
  paper-result, model, partial-boundary, and reusable-library nodes without
  overlapping labels, boxes, or arrows.
- The DAG records the single SSGM theorem-shaped boundary, the Lean-proved
  Theorem 3 constrained alternative, and the exact Theorem 3 full-space
  recovery rather than presenting those as hidden paper assumptions.

## 18. Validation Commands
- `lake build GKGMM19IterativeLocalVoting`: passed.
- `python3 scripts/review_dashboard.py --paper GKGMM19IterativeLocalVoting --refresh-cache`: passed.
- `python3 scripts/review_dashboard.py --paper GKGMM19IterativeLocalVoting --precheck`: passed with only documented conditional-boundary status.
- `python3 scripts/audit_repository.py --paper GKGMM19IterativeLocalVoting --paper-closeout --include-active --info-limit 0`: targeted repository audit command for the final closeout.
- `python3 scripts/audit_repository.py --library-only --library-premise-audit --info-limit 0`: reusable-library premise audit passed.
