# College Admissions and the Stability of Marriage

Machine-readable status source: [`status.json`](status.json).

## Source Version

- Paper: *College Admissions and the Stability of Marriage*
- Authors: D. Gale and L. S. Shapley
- Version checked locally: *The American Mathematical Monthly*, Vol. 69, No. 1
  (Jan. 1962), pp. 9--15
- DOI: https://doi.org/10.1080/00029890.1962.11989827
- Stable URL: http://www.jstor.org/stable/2312726

The source PDF is cached locally as `GS62CollegeAdmissions.pdf` and ignored by
the paper-folder `.gitignore`. The PDF is a scan; the local text extraction is
currently metadata-only, so source-audit theorem lines are cross-checked against
the cached PDF and public OCR snippets until an OCR cache is available.

## Central Theorem File

- `GS62CollegeAdmissions/PaperInterface.lean`
- `GS62CollegeAdmissions/MainTheorems.lean`
- `GS62CollegeAdmissions/PostPaperAudit.lean`

Detailed reusable matching and deferred-acceptance primitives live in
`EconCSLib/Markets/Matching`.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Definitions: stable marriage, complete marriage, proposer/applicant optimal stable matching, strict marriage domain | `gs_stable_marriage`, `gs_complete_marriage`, `gs_applicant_optimal_stable_marriage`, `gs_strict_marriage_domain` | formalized | `GS62CollegeAdmissions/MainTheorems.lean` | None; the Lean domain records strict rankings, equal-size sides, and positive value for every potential pair to represent the no-unmatched-agent marriage model. |
| Deferred-acceptance stability | `gs_deferredAcceptance_stable` | formalized | `GS62CollegeAdmissions/MainTheorems.lean`; `EconCSLib/Markets/Matching/DeferredAcceptance.lean` | None; the reusable DA invariant and termination facts are proved internally, and `#print axioms` for the paper-facing row uses only standard Lean foundations. |
| Theorem 1, stable marriages exist | `paper_gs62_theorem1_stable_marriage_exists` | formalized | `GS62CollegeAdmissions/MainTheorems.lean` | None; the source statement is exposed and discharged through the closed reusable DA stability theorem plus finite completeness. |
| College-admissions quota-one stable assignment | `paper_gs62_college_admissions_quota_one_stable_assignment_exists`, `paper_gs62_college_admissions_quota_one_manyToOne_stable_assignment_exists` | formalized | `GS62CollegeAdmissions/MainTheorems.lean`; `EconCSLib/Markets/Matching/ManyToOne.lean` | None; quota one is the one-to-one marriage model, and the many-to-one wrapper reuses the closed one-to-one stability result. |
| General college admissions with arbitrary finite quotas | `paper_gs62_college_admissions_stable_assignment_exists` | formalized | `GS62CollegeAdmissions/MainTheorems.lean`; `EconCSLib/Markets/Matching/ManyToOne.lean` | None; the cloned-seat construction compiles against the closed many-to-one stability endpoint. |
| Theorem 2, applicant/proposer optimality | `paper_gs62_theorem2_deferred_acceptance_applicant_optimal` | formalized | `GS62CollegeAdmissions/MainTheorems.lean` | None; proposer optimality is proved through the closed reusable DA optimality theorem. |

## Source-Audit Notes

The source scan and public OCR snippets expose two named theorems: Theorem 1,
the existence of stable marriages, and Theorem 2, applicant optimality of the
deferred-acceptance assignment. The Lean pass closes the one-to-one marriage
statements, the quota-one college-admissions reduction, and the general finite
college-admissions existence statement by cloning each college into its quota of
identical one-to-one seats. The Lean-native axiom-closure audit reports only
standard foundations (`propext`, `Classical.choice`, and `Quot.sound`) for the
paper-facing declarations, and no explicit paper-assumption premises remain.
