import GS62CollegeAdmissions.MainTheorems

/-!
# Post-paper audit: Gale-Shapley 1962

This file is the Lean-side endpoint ledger for Gale and Shapley's
*College Admissions and the Stability of Marriage*.  For the compact
human-facing statement surface, read `PaperInterface.lean`; each theorem below
is an importable source-facing audit endpoint delegated to
`GS62CollegeAdmissions.MainTheorems`.

Cached source inventory checked by this audit:

- The local publisher PDF is cached as `GS62CollegeAdmissions.pdf`.
- The local `pdftotext` cache is only 8 bytes and contains no usable OCR hits
  for `Theorem`, `Lemma`, `Proposition`, `Corollary`, or `Definition`.
- The source scan and public OCR snippets identify Theorem 1 as existence of
  stable marriages and Theorem 2 as applicant optimality of the deferred
  acceptance procedure.  The college-admissions quota story is formalized as
  the cloned-seat many-to-one wrapper below.

The corresponding README rows and DAG nodes are checked in
`FINAL_VALIDATION_REPORT.md`.
-/

namespace GS62CollegeAdmissions
open EconCSLib.Matching

/-! ## Source-numbered audit endpoints -/

/--
Audit endpoint for Gale-Shapley Theorem 1: on the strict equal-cardinality
marriage domain, a stable complete marriage exists.
-/
theorem audit_theorem1_stable_marriage_exists
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : gs_strict_marriage_domain val_m val_w) :
    ∃ mu : Assignment M W,
      gs_stable_marriage val_m val_w mu ∧ gs_complete_marriage mu := by
  exact paper_gs62_theorem1_stable_marriage_exists
    val_m val_w hcard hdomain

/--
Audit endpoint for the paper's finite college-admissions model: for arbitrary
finite college quotas there is a stable assignment.  The Lean statement uses the
paper's responsive college rankings by replacing each college with identical
cloned seats.
-/
theorem audit_college_admissions_stable_assignment_exists
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ) :
    ∃ mu : ManyToOneAssignment Applicants Colleges,
      ManyToOne.IsStable val_applicant val_college quota mu := by
  exact paper_gs62_college_admissions_stable_assignment_exists
    quota val_applicant val_college

/--
Audit endpoint for Gale-Shapley Theorem 2: the applicant-proposing deferred
acceptance assignment is applicant-optimal among stable assignments.
-/
theorem audit_theorem2_deferred_acceptance_applicant_optimal
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hcard : Fintype.card Applicants = Fintype.card Colleges)
    (hdomain : gs_strict_marriage_domain val_applicant val_college) :
    ∃ mu : Assignment Applicants Colleges,
      gs_complete_marriage mu ∧
        gs_applicant_optimal_stable_marriage val_applicant val_college mu := by
  exact paper_gs62_theorem2_deferred_acceptance_applicant_optimal
    val_applicant val_college hcard hdomain

end GS62CollegeAdmissions
