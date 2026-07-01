# Final Validation Report: Gale-Shapley 1962

## 1. Human Verdict
Formalized. The Gale-Shapley existence, college-admissions existence, and
applicant-optimality results are checked using the shared matching library. No
paper-correctness caveat is reported. No human dashboard sign-off has been
recorded.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The GS62 paper endpoints are checked using the shared
  matching library.

## 3. Source and Scope
- Paper: *College Admissions and the Stability of Marriage*
- Authors: D. Gale and L. S. Shapley
- Source version: *The American Mathematical Monthly*, Vol. 69, No. 1
  (January 1962), pp. 9--15; DOI
  https://doi.org/10.1080/00029890.1962.11989827; stable JSTOR URL
  http://www.jstor.org/stable/2312726
- Lean folder: `papers/GS62CollegeAdmissions`
- Human-facing theorem file: `papers/GS62CollegeAdmissions/PaperInterface.lean`
- Audit ledger: `papers/GS62CollegeAdmissions/PostPaperAudit.lean`
- DAG artifacts: `papers/GS62CollegeAdmissions/DependencyDAG.tex`,
  `papers/GS62CollegeAdmissions/DependencyDAG.pdf`

## 4. Researcher Summary of Checked Results
- The formalization checks the Gale-Shapley stable-marriage theorem, the college-admissions existence theorem, and applicant-optimality.
- The proof uses the shared matching library while preserving the paper's strict-preference matching domain.
- No source-paper caveat is recorded for the checked results.

## 5. Remaining Boundaries and Gaps
None.

## 6. Additional Assumptions Beyond Paper
- None

## 7. Proof-Strategy Deviations
- Theorem 1 is not re-proved from the printed prose. It is discharged through
  the reusable deferred-acceptance stability theorem plus a finite
  equal-cardinality completeness bridge.
- The college-admissions quota theorem uses the cloned-seat reduction rather
  than a separate many-to-one rejection-process proof.
- Theorem 2 uses the reusable DA proposer-optimality theorem already developed
  for Roth's matching paper.

## 8. Proof Tricks Worth Reusing
None separately recorded in the existing report.

## 9. Paper Issues or Caveats
None found.

## 10. Detailed Formalization Evidence
See the verdict and named-statement sections in this report.

## 11. Paper Definitions Checked
<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def strictMarriageDomain | `strictMarriageDomain` | - Strict marriage domain: both sides have strict preferences and every possible man-woman pair is acceptable. |
| def stableMarriage | `stableMarriage` | - Stable marriage: individual rationality for both sides and no blocking pair. |
| def completeMarriage | `completeMarriage` | - Complete marriage: every participant is matched. |
| def applicantOptimalStableMarriage | `applicantOptimalStableMarriage` | - Applicant/proposer optimal stable marriage: every proposer weakly prefers this stable marriage to any other stable marriage. |
<!-- lean-derived-definitions:end -->

## 12. Named Theorem Statements Checked
### Theorem-by-Theorem Validation

| Paper item | Lean declaration | Status | Statement match | Notes |
|---|---|---|---|---|
| Stable marriage definition | `gs_stable_marriage` | fully formalized | exact up to explicit source-domain assumptions | The Lean model makes the source stability condition explicit over finite sides and outside option value `0`. |
| Complete marriage definition | `gs_complete_marriage` | fully formalized | exact up to explicit source-domain assumptions | Completeness represents the paper's no-unmatched marriage convention. |
| Applicant-optimal stable assignment definition | `gs_applicant_optimal_stable_marriage` | fully formalized | exact up to explicit source-domain assumptions | The definition states applicant-side weak optimality among stable assignments. |
| Strict marriage-domain convention | `gs_strict_marriage_domain` | fully formalized | minor deviation | Lean packages strict rankings and all-pairs acceptability explicitly. |
| Theorem 1: stable marriages exist | `audit_theorem1_stable_marriage_exists` | fully formalized | exact up to explicit source-domain assumptions | The statement is exposed and discharged by the closed reusable deferred-acceptance stability theorem plus finite completeness. |
| College-admissions stable assignment with finite quotas | `audit_college_admissions_stable_assignment_exists` | fully formalized | minor deviation | The cloned-seat route compiles against the closed many-to-one stability endpoint. |
| Theorem 2: applicants are at least as well off under the procedure as under any other stable assignment | `audit_theorem2_deferred_acceptance_applicant_optimal` | fully formalized | exact up to explicit source-domain assumptions | Proposer optimality is discharged through the closed reusable DA optimality theorem. |

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem theorem1_stable_marriage_exists | `theorem1_stable_marriage_exists` | - Theorem 1: on the strict same-index finite marriage domain, a stable complete marriage exists. |
| theorem college_admissions_stable_assignment_exists | `college_admissions_stable_assignment_exists` | - College-admissions theorem: finite applicants and colleges with arbitrary quotas and applicant/college utilities admit a stable many-to-one assignment. |
| theorem theorem2_applicant_optimality | `theorem2_applicant_optimality` | - Theorem 2: on the finite same-index strict marriage domain, the applicant-proposing deferred-acceptance assignment is complete and applicant-optimal among stable assignments. |
<!-- lean-derived-statements:end -->

## 13. Paper-Facing Statement Validator Ledger
Generated from dashboard status export:

`python3 scripts/review_dashboard.py --paper GS62CollegeAdmissions --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| def applicantOptimalStableMarriage | `applicantOptimalStableMarriage` | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z): Translation preserves stability and the universal weak-preference comparison for every proposer against any stable marriage. |
| theorem college_admissions_stable_assignment_exists | `college_admissions_stable_assignment_exists` | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z): Translation preserves finite applicants and colleges, arbitrary quotas and utilities, and existence of a stable many-to-one assignment. |
| def completeMarriage | `completeMarriage` | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z): Translation preserves that every participant on both sides is matched. |
| def stableMarriage | `stableMarriage` | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z): Translation states individual rationality for both sides and excludes blocking pairs with strict mutual preference. |
| def strictMarriageDomain | `strictMarriageDomain` | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z): Translation preserves strict preferences on both sides and universal acceptability of all man-woman pairs. |
| theorem theorem1_stable_marriage_exists | `theorem1_stable_marriage_exists` | gpt-5-codex (model; matches; 2026-06-12T16:19:01Z) | gpt-5-codex (model; matches; 2026-06-12T16:19:01Z): Translation preserves the finite equal-cardinality strict marriage-domain theorem while making the Lean representation explicit: both sides use the same finite index type, so equal cardinality is derived rather than an extra premise. |
| theorem theorem2_applicant_optimality | `theorem2_applicant_optimality` | gpt-5-codex (model; matches; 2026-06-12T16:19:01Z) | gpt-5-codex (model; matches; 2026-06-12T16:19:01Z): Translation preserves the finite equal-cardinality strict-domain applicant-optimality theorem while making the Lean representation explicit: both sides use the same finite index type, so equal cardinality is derived rather than an extra premise. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.

## 14. Paper Assumption Provenance And Modeling Notes
| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No explicit paper-assumption premises remain; equal cardinality is derived from the same-index finite representation. |

### Additional Assumptions Beyond Paper

- `gs_strict_marriage_domain`: packages strict rankings, all-pairs
  acceptability, and outside-option value `0`. These are explicit Lean
  versions of the paper's marriage-market conventions.
- Finite `Fintype`/`DecidableEq` instances: Lean bookkeeping for the finite
  applicant, college, and cloned-seat sets used by the constructive algorithm.
- Responsive cloned-seat college preferences: the many-to-one theorem treats a
  college's quota as identical seats with the same applicant ranking. This is
  the standard cloned-seat formalization of the paper's college quota model.

## 15. Library Lift Pass
None separately recorded in the existing report.

## 16. DAG Audit
No separate DAG audit note is recorded in the existing report.

## 17. Validation Checks
### Cross-Artifact Checks

- Paper text/PDF: local PDF/text caches are ignored by the paper-folder
  `.gitignore`; the attempted text extraction produced only metadata.
- README: every claimed named source endpoint has a controlled-vocabulary status
  row and explicit modeling notes.
- DAG: every closed source-facing endpoint is green, and the general quota node
  depends by a solid verified edge on the reusable deferred-acceptance layer.
  The rendered DAG was visually inspected after regeneration.
- Lean: `PostPaperAudit.lean` is imported by the paper root module and exposes
  one audit theorem for each final endpoint.

### Verification Checks

- The local text extraction had no OCR content, so named-result checking used
  the cached scan and public OCR snippets.
- The paper root module imports `PaperInterface.lean`, `MainTheorems.lean`, and
  `PostPaperAudit.lean`.
- The paper Lean target builds successfully, and the rendered DAG was visually
  inspected after regeneration.

### Statement Translation Audit

Audit date: 2026-06-06.
Scope: current dashboard rows from `PaperInterface.lean`; `lean_to_tex_llm.json` records context-free Lean-to-TeX drafts and `statement_match_llm.json` records the context-free paper-vs-translation judgment.

Summary: 7 rows; 7 match, 0 uncertain, 0 mismatch, 0 missing. Stale sidecar rows: none. Surface audit: not required (30 or fewer rows).

Flagged rows:
- None.
