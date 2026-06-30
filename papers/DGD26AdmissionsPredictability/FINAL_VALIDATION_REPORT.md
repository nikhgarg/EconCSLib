# Final Validation Report: Capacity Constraints Make Admissions Processes Less Predictable

## 1. Human Verdict
This paper's finite choice-function theory is formalized. The Lean development
covers instability, q-representative queues, sequential queue variability,
tight-instability constructions, append/remove variability, and the finite
linear-assignment extension.

No substantive theorem caveat remains in the formalized target. Empirical NYC
performance plots and private-data program instantiations are descriptive
material outside the Lean theorem scope, not unresolved mathematical
assumptions.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: Capacity-constrained admissions predictability results are
  formalized for the finite choice-function and finite assignment models; only
  empirical/private-data instantiations are out of theorem scope.

## 3. Source and Scope
- Paper: *Capacity Constraints Make Admissions Processes Less Predictable*
- Source version: AAAI-26 published version, DOI `10.1609/aaai.v40i45.41179`;
  TeX/formula source from arXiv `2601.11513v1`
- Lean folder: `papers/DGD26AdmissionsPredictability`
- Human-facing theorem file: `papers/DGD26AdmissionsPredictability/PaperInterface.lean`
- Paper assumption file: `papers/DGD26AdmissionsPredictability/Assumptions.lean`
- DAG artifacts: `papers/DGD26AdmissionsPredictability/DependencyDAG.tex` and
  `papers/DGD26AdmissionsPredictability/DependencyDAG.pdf`
- Clean LAP variability proof note:
  `papers/DGD26AdmissionsPredictability/LAP_VARIABILITY_CLEAN_PROOF.tex` and
  `papers/DGD26AdmissionsPredictability/LAP_VARIABILITY_CLEAN_PROOF.pdf`
- Lean build target: `lake build DGD26AdmissionsPredictability`

## 4. Researcher Summary of Checked Results
The formalization proves the core finite choice-function framework:
q-acceptance, choice distance, zero instability, substitutability,
monotonicity, consistency, independence, 1-instability, and the `2q`
instability upper bound.

It proves the even-instability/inconsistency result in both directions: positive
even distance after a single fresh addition yields inconsistency, and every
inconsistent feasible q-acceptant choice function has such a positive even
single-addition witness.

It proves the q-representative characterization: under feasibility,
q-representativeness is equivalent to q-acceptance, 1-instability, and
variability at most one. Exact-one refinements expose the natural nondegenerate
displacement witness rather than hiding it.

It proves the sequential-queue variability results, including additive
variability bounds for feasible q-acceptant 1-unstable stages and the
q-representative queue corollary.

It proves the finite linear-assignment results. Unique global-optimum finite
assignment selectors induce 1-unstable choice rules, and under slotwise no-ties
their variability is bounded by the number of distinct slot-induced applicant
orderings. Lean supplies the detailed alternating-splice proof behind this LAP
variability result; the public folder includes a clean paper-facing proof note
rendered as `LAP_VARIABILITY_CLEAN_PROOF.pdf`.

## 5. Remaining Boundaries and Gaps
No remaining mathematical boundary is used for the finite choice-function and
finite assignment theorem targets.

Empirical NYC performance plots and private-data program instantiations are
outside the Lean theorem scope.

## 6. Additional Assumptions Beyond Paper
No additional assumptions beyond the paper are used, and no paper-local
assumptions are declared in `Assumptions.lean`.

The no-zero-instability result explicitly carries the standard nontrivial
capacity domain from the source model: positive capacity and an applicant set
larger than capacity. Exact variability and tight-instability refinements
expose a concrete displacement witness to exclude degenerate no-change cases.
The LAP distinct-order theorem is exposed with the finite assignment
hypotheses used in the source proof: unique global chosen set, slotwise no ties,
and a classifier that only groups slots with the same induced applicant order.

## 7. Proof-Strategy Deviations
No proof-strategy deviation changes any theorem endpoint.

The appendix removable-set equality uses the mathematically meaningful
corrected form `V_C(X_1) = V_C(X_2)` for what appears to be a source typo.

## 8. Proof Tricks Worth Reusing
- The LAP variability proof uses a directed alternating-splice/proper-suffix
  exchange argument to make same-order-slot reasoning precise when applicants
  can be reassigned along a chain.
- Exact one-for-one changes are handled by proving no incoming edge at the fresh
  root, no outgoing edge at the lost slot, and uniqueness of the relevant
  left/right endpoints.
- Exactness claims are kept conditional on a concrete displacement witness when
  the source statement is about nonzero variability.

## 9. Paper Issues or Caveats
No substantive theorem counterexample was found.

The appendix removable-set equality appears to contain a typo
`V_C(X_1) = V_C(X_1)`. The formalization uses the mathematically meaningful
corrected form `V_C(X_1) = V_C(X_2)`.

## 10. Detailed Formalization Evidence
- `papers/DGD26AdmissionsPredictability/LAP.lean`: finite assignment model,
  objective optimality, alternating-splice exchange, LAP 1-instability, and the
  distinct slot-order variability theorem.
- `papers/DGD26AdmissionsPredictability/LAP_VARIABILITY_CLEAN_PROOF.pdf`: clean
  paper-facing writeup of the detailed LAP variability proof supplied by Lean.
- `papers/DGD26AdmissionsPredictability/MainTheorems.lean`: source-facing
  theorem layer.
- `papers/DGD26AdmissionsPredictability/PaperInterface.lean`: 101 dashboard
  rows for paper-facing definitions and named statements, plus 5 auxiliary
  LAP proof-support rows excluded from the public review surface.
- `EconCSLib/Foundations/Math/FiniteChoice.lean`: reusable finite choice
  function lemmas, including the even-instability inconsistency converse.

## 11. DAG Audit
`DependencyDAG.pdf` is rendered from `DependencyDAG.tex`, uses paper-facing
statement labels rather than Lean declaration names, and was visually inspected
after PNG conversion.

## 12. Validation Checks
- Passed: `lake build DGD26AdmissionsPredictability`
- Passed: `python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --statement-precheck`
  with 101/101 row-local statement translations and semantic matches current.
- Passed: `python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --paper-coverage-precheck`
  with 39/39 source statements covered directly and no conditional-boundary
  source items.
- Passed: `python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --source-to-lean-precheck`
  with 39/39 source statements linked to current Lean rows.
- Passed: recursive source-record audit with four explicit displacement-witness
  exactness conditions and no unresolved record/certificate/process boundary.
- Passed: `python3 scripts/audit_repository.py --paper DGD26AdmissionsPredictability --paper-closeout --info-limit 0`
  with 0 errors and 0 warnings.

## 13. Statement Validator Ledger
The current LLM-as-judge sidecars are:
- `review_surface_llm.json`: current 101-row paper-facing review-surface audit.
- `lean_to_tex_llm.json`: 101 context-free Lean-to-TeX/prose translations.
- `statement_match_llm.json`: 101 semantic source-to-Lean row judgments.
- `paper_coverage_llm.json`: 39 source-inventory coverage judgments, all
  covered directly.
- `source_record_audit.json` and `source_record_match_llm.json`: recursive
  boundary/source-record audit for visible displacement-witness exactness
  premises.
