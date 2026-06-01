# College Admissions and the Stability of Marriage

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
| Deferred-acceptance stability | `gs_deferredAcceptance_stable` | formalized | `GS62CollegeAdmissions/MainTheorems.lean` | None; thin wrapper around the reusable DA stability theorem in `EconCSLib.Markets.Matching`. |
| Theorem 1, stable marriages exist | `paper_gs62_theorem1_stable_marriage_exists` | formalized | `GS62CollegeAdmissions/MainTheorems.lean` | None; closed for the one-to-one marriage model using DA stability plus equal-cardinality/all-pairs-acceptable completeness. |
| College-admissions quota-one stable assignment | `paper_gs62_college_admissions_quota_one_stable_assignment_exists`, `paper_gs62_college_admissions_quota_one_manyToOne_stable_assignment_exists` | formalized | `GS62CollegeAdmissions/MainTheorems.lean`; `EconCSLib/Markets/Matching/ManyToOne.lean` | None; quota-one college admissions reduces to the marriage theorem and is also embedded into the reusable many-to-one API. |
| General college admissions with arbitrary finite quotas | `paper_gs62_college_admissions_stable_assignment_exists` | formalized | `GS62CollegeAdmissions/MainTheorems.lean`; `EconCSLib/Markets/Matching/ManyToOne.lean` | None; closed by the reusable cloned-seat many-to-one DA construction. The Lean API represents each college's paper ranking over applicants responsively across identical seats. |
| Theorem 2, applicant/proposer optimality | `paper_gs62_theorem2_deferred_acceptance_applicant_optimal` | formalized | `GS62CollegeAdmissions/MainTheorems.lean` | None; closed for quota-one college admissions / one-to-one marriage using the reusable DA men-optimality theorem from the Roth formalization infrastructure. |

## Source-Audit Notes

The source scan and public OCR snippets expose two named theorems: Theorem 1,
the existence of stable marriages, and Theorem 2, applicant optimality of the
deferred-acceptance assignment. The Lean pass closes the one-to-one marriage
statements, the quota-one college-admissions reduction, and the general finite
college-admissions existence statement by cloning each college into its quota of
identical one-to-one seats. No theorem endpoint relies on an extra model
certificate; the scanned PDF/OCR boundary is recorded as a source-audit note,
not a formalization caveat.
