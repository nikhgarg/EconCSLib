# Final Validation Report: Gale-Shapley 1962

## 1. Human Verdict

- Lean formalization status: formalized
- Human dashboard review status: 0/7 rows reviewed; 0 stale; 0 mismatches.
- Human summary: This only uses a few lines of code as its infrastructure has largely been elevated to the shared matching library.

## 2. Source and Scope

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

## 3. What Has Been Proven

The Gale-Shapley deferred-acceptance model, stability definitions, and the
paper-facing stable-matching existence and optimality endpoints are formalized
for finite strict preference profiles. The named-statement section lists the
exact Lean interface declarations checked against the source theorem
statements.

## 4. Additional Assumptions Beyond Paper

- `gs_strict_marriage_domain`: packages strict rankings, all-pairs
  acceptability, and outside-option value `0`. These are explicit Lean
  versions of the paper's marriage-market conventions.
- `hcard : Fintype.card M = Fintype.card W`: used for complete marriages in
  the one-to-one marriage statement. This matches the source marriage model.
- Finite `Fintype`/`DecidableEq` instances: Lean bookkeeping for the finite
  applicant, college, and cloned-seat sets used by the constructive algorithm.
- Responsive cloned-seat college preferences: the many-to-one theorem treats a
  college's quota as identical seats with the same applicant ranking. This is
  the standard cloned-seat formalization of the paper's college quota model.

## 5. Proof-Strategy Deviations

- Theorem 1 is not re-proved from the printed prose. It is discharged through
  the reusable deferred-acceptance stability theorem plus a finite
  equal-cardinality completeness bridge.
- The college-admissions quota theorem uses the cloned-seat reduction rather
  than a separate many-to-one rejection-process proof.
- Theorem 2 uses the reusable DA proposer-optimality theorem already developed
  for Roth's matching paper.

## 6. Proof Tricks Worth Reusing

None separately recorded in the existing report.

## 7. Library Lift Pass

None separately recorded in the existing report.

## 8. DAG Audit

No separate DAG audit note is recorded in the existing report.

## 9. Conditional Results and Remaining Gaps

- None for the Lean endpoints claimed above.
- No claimed theorem endpoint relies on an extra model certificate; finite
  strict-domain and quota assumptions are the explicit source-domain/modeling
  conventions recorded above.
- Source audit note: the cached PDF is a scan, and the local `pdftotext`
  extraction is only 8 bytes with no theorem-name hits. The named-result
  inventory was therefore cross-checked against the cached scan and public OCR
  snippets rather than local text-cache line numbers.

## 10. Suspected Paper Errors or Inconsistencies

- None found.

## 11. Validation Checks

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

## 12. Final Verdict

- Completion status: formalized.
- Summary: This only uses a few lines of code as its infrastructure has largely been elevated to the shared matching library.

## 13. Paper Definitions Checked

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def strictMarriageDomain | `strictMarriageDomain` | - Strict marriage domain: both sides have strict preferences and every possible man-woman pair is acceptable. |
| def stableMarriage | `stableMarriage` | - Stable marriage: individual rationality for both sides and no blocking pair. |
| def completeMarriage | `completeMarriage` | - Complete marriage: every participant is matched. |
| def applicantOptimalStableMarriage | `applicantOptimalStableMarriage` | - Applicant/proposer optimal stable marriage: every proposer weakly prefers this stable marriage to any other stable marriage. |
<!-- lean-derived-definitions:end -->

## 14. Named Theorem Statements Checked

### Theorem-by-Theorem Validation

| Paper item | Lean declaration | Status | Statement match | Notes |
|---|---|---|---|---|
| Stable marriage definition | `gs_stable_marriage` | fully formalized | exact up to explicit source-domain assumptions | The Lean model makes the source stability condition explicit over finite sides and outside option value `0`. |
| Complete marriage definition | `gs_complete_marriage` | fully formalized | exact up to explicit source-domain assumptions | Completeness represents the paper's no-unmatched marriage convention. |
| Applicant-optimal stable assignment definition | `gs_applicant_optimal_stable_marriage` | fully formalized | exact up to explicit source-domain assumptions | The definition states applicant-side weak optimality among stable assignments. |
| Strict marriage-domain convention | `gs_strict_marriage_domain` | fully formalized | minor deviation | Lean packages strict rankings and all-pairs acceptability explicitly. |
| Theorem 1: stable marriages exist | `audit_theorem1_stable_marriage_exists` | fully formalized | exact up to explicit source-domain assumptions | Closed by `paper_gs62_theorem1_stable_marriage_exists`, using deferred-acceptance stability and equal-cardinality completeness. |
| College-admissions stable assignment with finite quotas | `audit_college_admissions_stable_assignment_exists` | fully formalized | minor deviation | Closed by cloning each college into `quota c` identical one-to-one seats, then collapsing the stable one-to-one assignment into college rosters. This represents the paper's responsive college ranking over individual applicants. |
| Theorem 2: applicants are at least as well off under the procedure as under any other stable assignment | `audit_theorem2_deferred_acceptance_applicant_optimal` | fully formalized | exact up to explicit source-domain assumptions | Closed by the reusable proposer-optimality theorem from the Roth/deferred-acceptance infrastructure. |

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem theorem1_stable_marriage_exists | `theorem1_stable_marriage_exists` | - Theorem 1: on the strict equal-cardinality marriage domain, a stable complete marriage exists. |
| theorem college_admissions_stable_assignment_exists | `college_admissions_stable_assignment_exists` | - College-admissions theorem: finite applicants and colleges with arbitrary quotas and applicant/college utilities admit a stable many-to-one assignment. |
| theorem theorem2_applicant_optimality | `theorem2_applicant_optimality` | - Theorem 2: on the finite equal-cardinality strict marriage domain, the applicant-proposing deferred-acceptance assignment is complete and applicant-optimal among stable assignments. |
<!-- lean-derived-statements:end -->

## 15. Paper-Facing Statement Validator Ledger

Generated from dashboard status export:

`python3 scripts/review_dashboard.py --paper GS62CollegeAdmissions --export-format validators-md`

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| def applicantOptimalStableMarriage | `applicantOptimalStableMarriage` | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z): Translation preserves stability and the universal weak-preference comparison for every proposer against any stable marriage. |
| theorem college_admissions_stable_assignment_exists | `college_admissions_stable_assignment_exists` | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z): Translation preserves finite applicants and colleges, arbitrary quotas and utilities, and existence of a stable many-to-one assignment. |
| def completeMarriage | `completeMarriage` | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z): Translation preserves that every participant on both sides is matched. |
| def stableMarriage | `stableMarriage` | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z): Translation states individual rationality for both sides and excludes blocking pairs with strict mutual preference. |
| def strictMarriageDomain | `strictMarriageDomain` | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z): Translation preserves strict preferences on both sides and universal acceptability of all man-woman pairs. |
| theorem theorem1_stable_marriage_exists | `theorem1_stable_marriage_exists` | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z): Translation preserves finite equal-cardinality strict marriage-domain hypotheses and existence of a stable complete marriage. |
| theorem theorem2_applicant_optimality | `theorem2_applicant_optimality` | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z) | gpt-5-codex (model; matches; 2026-06-06T20:39:36Z): Translation preserves equal-cardinality strict-domain hypotheses and that the deferred-acceptance output is complete and applicant-optimal among stable matchings. |

Human dashboard reviews and model/agent statement checks may both appear here. This table is provenance for the statement targets; it does not change the human-only `human_review.reviewed_rows` counter.
