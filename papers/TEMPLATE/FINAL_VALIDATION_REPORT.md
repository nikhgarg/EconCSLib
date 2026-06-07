# Final Validation Report: [Paper Short Name]

## 1. Human Verdict
- Lean formalization status: not started
- Human dashboard review status: 0 reviewed, 0 stale, 0 mismatches
- Paper correctness verdict: not assessed
- Qualitative proof verdict: not assessed
- Lean footprint: not measured

## 2. Source and Scope
- Paper: <title>
- Source version: <arXiv/publisher URL + version/date>
- Lean folder: `papers/TEMPLATE`
- Human-facing theorem file: `papers/TEMPLATE/PaperInterface.lean`
- DAG artifacts: `papers/TEMPLATE/DependencyDAG.tex`, `papers/TEMPLATE/DependencyDAG.pdf`

## 3. What Has Been Proven
None yet.

## 4. Additional Assumptions Beyond Paper
- None

## 5. Proof-Strategy Deviations
- None

## 6. Proof Tricks Worth Reusing
- None

## 7. Library Lift Pass
- None

## 8. DAG Audit
- Rendered artifact: not checked
- Topology: not checked
- Layout: not checked

## 9. Conditional Results and Remaining Gaps
- All named results remain open.

## 10. Suspected Paper Errors or Inconsistencies
- None

## 11. Validation Checks
- Not run.

## 12. Final Verdict
- Completion status: not formalized
- Summary: Scaffold only.

## 13. Paper Definitions Checked
- None yet.

## 14. Named Theorem Statements Checked
### Theorem <n>
**Paper statement.** <one theorem-box-level statement matching the source>

**Lean interface statement.**
- `<PaperInterface.theoremN_part>`: <which paper clause it states>

**Status.** not formalized.

## 15. Paper-Facing Statement Validator Ledger
This table is one row per dashboard/PaperInterface row. Regenerate it with:

`python3 scripts/review_dashboard.py --paper TEMPLATE --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| <paper item label> | `<PaperInterface.declaration>` | <human/model/agent validators, judgments, dates, stale flags> | <validator comments or `None`> |

Human dashboard reviews and model/agent statement checks may both appear here.
This table is provenance for the statement targets; it does not change the
human-only `human_review.reviewed_rows` counter.
