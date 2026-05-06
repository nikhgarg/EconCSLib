# Final Validation Report: Gale-Shapley 1962

## 1. Source and Scope

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

## 2. Theorem-by-Theorem Validation

| Paper item | Lean declaration | Status | Statement match | Notes |
|---|---|---|---|---|
| Stable marriage / complete marriage / applicant-optimal stable assignment definitions | `gs_stable_marriage`, `gs_complete_marriage`, `gs_applicant_optimal_stable_marriage`, `gs_strict_marriage_domain` | fully formalized | minor deviation | The Lean model makes the source conventions explicit: finite sides, strict rankings for the marriage domain, outside option value `0`, and all potential pairs acceptable when the source forbids unmatched agents. |
| Theorem 1: stable marriages exist | `audit_theorem1_stable_marriage_exists` | fully formalized | exact up to explicit source-domain assumptions | Closed by `paper_gs62_theorem1_stable_marriage_exists`, using deferred-acceptance stability and equal-cardinality completeness. |
| College-admissions stable assignment with finite quotas | `audit_college_admissions_stable_assignment_exists` | fully formalized | minor deviation | Closed by cloning each college into `quota c` identical one-to-one seats, then collapsing the stable one-to-one assignment into college rosters. This represents the paper's responsive college ranking over individual applicants. |
| Theorem 2: applicants are at least as well off under the procedure as under any other stable assignment | `audit_theorem2_deferred_acceptance_applicant_optimal` | fully formalized | exact up to explicit source-domain assumptions | Closed by the reusable proposer-optimality theorem from the Roth/deferred-acceptance infrastructure. |

## 3. Additional Assumptions Beyond Paper

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

## 4. Proof-Strategy Deviations

- Theorem 1 is not re-proved from the printed prose. It is discharged through
  the reusable deferred-acceptance stability theorem plus a finite
  equal-cardinality completeness bridge.
- The college-admissions quota theorem uses the cloned-seat reduction rather
  than a separate many-to-one rejection-process proof.
- Theorem 2 uses the reusable DA proposer-optimality theorem already developed
  for Roth's matching paper.

## 5. Conditional Results and Remaining Gaps

- None for the Lean endpoints claimed above.
- Source audit caveat: the cached PDF is a scan, and the local `pdftotext`
  extraction is only 8 bytes with no theorem-name hits. The named-result
  inventory was therefore cross-checked against the cached scan and public OCR
  snippets rather than local text-cache line numbers.

## 6. Suspected Paper Errors or Inconsistencies

- None found.

## 7. Cross-Artifact Checks

- Paper text/PDF: `GS62CollegeAdmissions.pdf` is cached locally and ignored by
  the paper-folder `.gitignore`; `GS62CollegeAdmissions.txt` records the failed
  metadata-only extraction.
- README: every claimed named source endpoint has a controlled-vocabulary status
  row and explicit modeling notes.
- DAG: every closed source-facing endpoint is green, and the general quota node
  depends by a solid verified edge on the reusable deferred-acceptance layer.
  The rendered DAG was visually inspected after regeneration.
- Lean: `PostPaperAudit.lean` is imported by the paper root module and exposes
  one audit theorem for each final endpoint.

## 8. Verification Checks

- The cached text extraction has no OCR content, so named-result checking used
  the cached scan and public OCR snippets.
- The paper root module imports `PaperInterface.lean`, `MainTheorems.lean`, and
  `PostPaperAudit.lean`.
- The paper Lean target builds successfully, and the rendered DAG was visually
  inspected after regeneration.
