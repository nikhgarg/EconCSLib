# Post-Formalization Audit

## Scope

This audit records the closeout state for *Capacity Constraints Make Admissions
Processes Less Predictable*. The paper is recorded as formalized for the finite
choice-function and finite assignment theorem target.

The human-facing status entrypoint is `FINAL_VALIDATION_REPORT.md`. The core
theory is closed: instability, q-representative queues, sequential variability,
tight-instability constructions, append/remove variability, and the linear
assignment extension all build. Empirical NYC performance plots and private-data
program instantiations are descriptive material outside the Lean theorem target.

## Source Notes

No substantive theorem counterexample was found.

The no-zero-instability theorem exposes the standard nontrivial capacity
domain: positive capacity and an applicant pool larger than capacity.

The appendix removable-set equality appears to contain a typo
`V_C(X_1) = V_C(X_1)`. Lean uses the corrected form `V_C(X_1) = V_C(X_2)`.

Exact-one variability and tight-one refinements expose a concrete displacement
witness. This is the source-level nondegeneracy condition needed to distinguish
exact variability one from the already-proved at-most-one statements.

## Named Source Inventory

The paper-local review surface covers 101 source-facing rows. Paper-level source
coverage currently records 39/39 source inventory items covered directly and no
conditional-boundary source items.

Important closed items include:

| Source item | Current status | Notes |
|---|---|---|
| Core finite choice-function definitions | formalized | q-acceptance, choice distance, instability, variability, substitutability, monotonicity, consistency, independence, orders, and LAP objects are exposed. |
| Theorem 1 instability package | formalized | No-zero-instability under the nontrivial capacity domain, substitutability iff one-instability, `2q` upper bound, and tight `d` examples for all `1 <= d <= 2q`. |
| Theorem 2 sequential variability | formalized | Sequential q-representative choice properties and variability bound are closed; additive variability is proved for feasible q-acceptant one-unstable stages. |
| Appendix even-instability theorem | formalized | Both directions are exposed, including the converse from inconsistency to a positive even fresh-addition distance witness. |
| q-representative characterization | formalized | q-representativeness iff q-acceptance, one-instability, and variability at most one; exact-one refinements expose a displacement witness. |
| Append/remove variability theorem | formalized | Threshold and exact equivalence between main-text borderline variability and appendix general variability are proved. |
| Linear assignment instability and variability | formalized | Unique global optimum selectors induce feasible q-acceptant one-unstable choice rules; distinct slot-order variability is proved under no ties. |

## DAG Audit

`DependencyDAG.tex` and `DependencyDAG.pdf` have been updated with paper-facing
node names rather than Lean declaration names. The DAG uses only definition,
supporting-result, and main-result node statuses; it no longer presents the
nontrivial capacity domain or exact displacement witnesses as caveats.

The rendered PDF was visually inspected after converting it to
`/tmp/dgd_dependency_dag.png`. Labels are readable and no node text is obscured
by an edge. The diagram includes an explicit even-instability/inconsistency node
for the theorem whose converse was added in the latest proof pass.

## Review Surface and LLM-as-Judge Audit

Current dashboard status:

- 101 source-facing review rows in `PaperInterface.lean`.
- 5 auxiliary LAP proof-support rows are intentionally excluded from the public
  review surface.
- `review_surface_llm.json` is current for the 101-row surface.
- `lean_to_tex_llm.json` has 101 context-free translations.
- `statement_match_llm.json` has 101 semantic match judgments.
- `paper_coverage_llm.json` has 39/39 source statements covered directly.

The human dashboard review count remains 0/101. That is a human sign-off status,
not a Lean proof or LLM audit gap.

## Source-Record and Assumption Audit

`Assumptions.lean` declares no paper-local assumptions.

The generated `source_record_audit.json` reports four visible
displacement-witness exactness inputs and no unresolved record/certificate,
source-row, replay, bridge, or process boundary. `source_record_match_llm.json`
classifies those inputs as source-level nondegeneracy conditions tied to exact
variability/tightness statements.

## Library Extraction Review

Reusable finite choice-function material was moved into
`EconCSLib/Foundations/Math/FiniteChoice.lean`, including the new
inconsistency-to-positive-even-distance converse. The paper-local LAP file
still owns the finite assignment/no-profitable-one-slot-swap model because that
API is not yet needed by another paper.

Future reusable extraction candidate: a general finite assignment/slot-order
exchange API if another OR or matching paper needs the same alternating-splice
argument.

## Validation Commands

The latest closeout pass ran:

```bash
python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --statement-precheck
python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --paper-coverage-precheck
python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --source-to-lean-precheck
python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --assumption-precheck
python3 scripts/review_dashboard.py --paper DGD26AdmissionsPredictability --precheck
python3 scripts/sync_paper_status.py
lake build DGD26AdmissionsPredictability
latexmk -pdf -interaction=nonstopmode -halt-on-error DependencyDAG.tex
pdftoppm -png -singlefile -r 160 DependencyDAG.pdf /tmp/dgd_dependency_dag
```

The closeout gate also ran:

```bash
python3 scripts/audit_repository.py --paper DGD26AdmissionsPredictability --paper-closeout --info-limit 0
```

It completed with 0 errors and 0 warnings.
