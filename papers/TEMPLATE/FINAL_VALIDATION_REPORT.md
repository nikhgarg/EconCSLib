# Final Validation Report: [Paper Short Name]

## 1. Human Verdict
Not started. No formalization or paper-correctness assessment has been
completed yet, and no human dashboard sign-off has been recorded.

## 2. Closeout Status
- Completion status: not formalized
- One-sentence recap: Scaffold only.

## 3. Source and Scope
- Paper: <title>
- Source version: <arXiv/publisher URL + version/date>
- Lean folder: `papers/TEMPLATE`
- Human-facing theorem file: `papers/TEMPLATE/PaperInterface.lean`
- Paper assumption file: `papers/TEMPLATE/Assumptions.lean`
- DAG artifacts: `papers/TEMPLATE/DependencyDAG.tex`, `papers/TEMPLATE/DependencyDAG.pdf`
- Lean footprint: not measured

## 4. Researcher Summary of Checked Results
None yet. Summarize checked paper definitions and named results here in paper language before listing Lean declarations or validator ledgers below.

## 5. Remaining Boundaries and Gaps
All named results remain open. Put partial-formalization, external-library,
analytic, solver, runtime, or source-certificate boundaries here, not in the
additional-assumptions section.

## 6. Additional Assumptions Beyond Paper
- None
Only list hypotheses added by the formalization that are not paper assumptions
or source theorem conditions. If a dependency is open formalization work rather
than a hypothesis, describe it in Section 5.

## 7. Proof-Strategy Deviations
- None

## 8. Proof Tricks Worth Reusing
- None

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.
Use this section for likely mathematical typos, sign errors, missing constants,
source-version corrections, or theorem-statement repairs suggested by the
formalization. Do not use this section for ordinary proof engineering choices
or open Lean/library work.

## 10. Paper Issues or Caveats
None found.

## 11. Detailed Formalization Evidence
None yet.

## 12. Paper Assumption Provenance
Every paper-facing theorem premise that is not derived in Lean should appear as
a named assumption declaration in `Assumptions.lean`, be listed in `status.json`
`review_surface.assumption_names`, and be checked in `assumption_match_llm.json`
as a true paper/source model assumption.
If an assumption declaration has `-- audit-premise:` comments, every exact
premise must have a premise-level source/provenance judgment. Use
`partial_boundary` for any premise that is visible but not yet source-matched or
derived; the paper remains partial until those boundaries are closed. Use
top-level `partial_boundary` for an assumption declaration that is itself a
known external/library/analytic/runtime/solver boundary, not a source caveat.
In human-facing tables, display validator labels as `source condition`,
`derived`, `additional assumption`, `formalization boundary`, `paper caveat`,
or `not paper-facing`; keep raw enum labels only in machine-readable JSON.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No paper assumptions recorded yet. |

## 13. Displayed Formula Provenance
Every displayed or source-defining formula used by a named result should have
an exact paper-facing row or exact subclaim row. Broad aggregate rows are not
enough for full validation. Formula rows are closed only when the formula is
derived in Lean from source primitives or from separately validated paper
assumptions.

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No displayed formulas checked yet. |

## 14. Library Lift Pass
- Reusable library extraction candidates: None
- Library certificate/source-boundary audit: not run. Before a completion
  claim, summarize whether certificate-taking library APIs used by paper
  wrappers are constructed internally, validated as paper assumptions, or listed
  as partial boundaries.
- Paper-local hidden-premise audit: not run. Before a completion claim,
  summarize whether the recursive provenance audit found unresolved broad rows,
  source-row formula boundaries, hidden premises, or transitive library
  certificate findings.

## 15. DAG Audit
- Rendered artifact: not checked
- Topology: not checked
- Layout: not checked

## 16. Validation Checks
- Not run.
- Required closeout checks include targeted Lean build, statement precheck,
  assumption/hidden-premise precheck, repository audit, and library premise
  audit when reusable certificate APIs are used or when preparing a public PR.
  The repository audit must also be clean of axiom-like declarations.
- Machine-required closeout evidence may include the exact targeted repository
  audit command here, but keep commands out of the executive verdict and proof
  narrative.

## 17. Paper Definitions Checked
- None yet.

## 18. Named Theorem Statements Checked
### Theorem <n>
**Paper statement.** <one theorem-box-level statement matching the source>

**Lean interface statement.**
- `<PaperInterface.theoremN_part>`: <which paper clause it states>

**Status.** not formalized.

## 19. Paper-Facing Statement Validator Ledger
This table is one row per dashboard/PaperInterface row. Generate it from the
validator ledger rather than from memory.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| <paper item label> | `<PaperInterface.declaration>` | <human/model/agent validators, judgments, dates, stale flags> | <validator comments or `None`> |

Human dashboard reviews and model/agent statement checks may both appear here.
This table is provenance for the statement targets; it does not change the
human-only `human_review.reviewed_rows` counter.
