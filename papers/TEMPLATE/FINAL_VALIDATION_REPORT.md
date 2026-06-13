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
- Paper assumption file: `papers/TEMPLATE/Assumptions.lean`
- DAG artifacts: `papers/TEMPLATE/DependencyDAG.tex`, `papers/TEMPLATE/DependencyDAG.pdf`

## 3. What Has Been Proven
None yet.

## 4. Paper Assumption Provenance
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

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No paper assumptions recorded yet. |

## 5. Displayed Formula Provenance
Every displayed or source-defining formula used by a named result should have
an exact paper-facing row or exact subclaim row. Broad aggregate rows are not
enough for full validation. Formula rows are closed only when the formula is
derived in Lean from source primitives or from separately validated paper
assumptions.

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No displayed formulas checked yet. |

## 6. Additional Assumptions Beyond Paper
- None

## 7. Proof-Strategy Deviations
- None

## 8. Proof Tricks Worth Reusing
- None

## 9. Library Lift Pass
- Reusable library extraction candidates: None
- Library certificate/source-boundary audit: not run. Before a completion
  claim, run `python3 scripts/audit_repository.py --library-premise-audit` and
  confirm any certificate-taking library APIs used by paper wrappers are
  constructed internally, validated as paper assumptions, or listed as partial
  boundaries. This audit follows transitive helper chains, not only direct
  aliases.
- Paper-local hidden-premise audit: not run. The default repository audit should
  report no reviewed row that recursively depends on a local helper with an
  unvalidated certificate, source-row equation, hidden hypothesis, or other
  proof-boundary premise.
- Recursive provenance closeout report: not run. Before a completion claim,
  run `python3 scripts/audit_repository.py --include-active --library-premise-audit --info-limit 0 --write-report docs/RECURSIVE_PROVENANCE_AUDIT_<date>.md`
  and confirm this paper has no unresolved broad/opaque row, source-row formula
  boundary, paper-local hidden premise, or transitive library certificate
  finding. If a finding remains, record it here and mark the endpoint
  partial/conditional.

## 10. DAG Audit
- Rendered artifact: not checked
- Topology: not checked
- Layout: not checked

## 11. Conditional Results and Remaining Gaps
- All named results remain open.

## 12. Suspected Paper Errors or Inconsistencies
- None

## 13. Validation Checks
- Not run.
- Required closeout checks include targeted Lean build, statement precheck,
  assumption/hidden-premise precheck, repository audit, and library premise
  audit when reusable certificate APIs are used or when preparing a public PR.
  The repository audit must also be clean of axiom-like declarations.

## 14. Final Verdict
- Completion status: not formalized
- Summary: Scaffold only.

## 15. Paper Definitions Checked
- None yet.

## 16. Named Theorem Statements Checked
### Theorem <n>
**Paper statement.** <one theorem-box-level statement matching the source>

**Lean interface statement.**
- `<PaperInterface.theoremN_part>`: <which paper clause it states>

**Status.** not formalized.

## 17. Paper-Facing Statement Validator Ledger
This table is one row per dashboard/PaperInterface row. Regenerate it with:

`python3 scripts/review_dashboard.py --paper TEMPLATE --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| <paper item label> | `<PaperInterface.declaration>` | <human/model/agent validators, judgments, dates, stale flags> | <validator comments or `None`> |

Human dashboard reviews and model/agent statement checks may both appear here.
This table is provenance for the statement targets; it does not change the
human-only `human_review.reviewed_rows` counter.
