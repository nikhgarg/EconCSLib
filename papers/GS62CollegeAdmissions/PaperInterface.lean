import GS62CollegeAdmissions.MainTheorems

/-!
# Paper Interface: Gale-Shapley 1962

This is the compact human-facing Lean surface for Gale and Shapley's
*College Admissions and the Stability of Marriage*.  It lists the paper
definitions and direct source theorem statements; implementation details live
in `MainTheorems.lean`.
-/

namespace GS62CollegeAdmissions
namespace PaperInterface

open EconCSLib.Matching

/-! ## Paper Definitions -/

/--
Strict marriage domain: both sides have strict preferences and every possible
man-woman pair is acceptable.
-/
def strictMarriageDomain {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  MenStrictPreferenceProfile val_m ∧
    WomenStrictPreferenceProfile val_w ∧
    AllPairsAcceptable val_m val_w

/-- Stable marriage: individual rationality for both sides and no blocking pair. -/
def stableMarriage {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  (∀ m, 0 ≤ valM val_m m (mu.m_match m)) ∧
    (∀ w, 0 ≤ valW val_w w (mu.w_match w)) ∧
      (∀ m w, valM val_m m (mu.m_match m) < val_m m w →
        valW val_w w (mu.w_match w) < val_w w m → False)

/-- Complete marriage: every participant is matched. -/
def completeMarriage {M W : Type*} (mu : Assignment M W) : Prop :=
  (∀ m, ∃ w, mu.m_match m = some w) ∧
    (∀ w, ∃ m, mu.w_match w = some m)

/--
Applicant/proposer optimal stable marriage: every proposer weakly prefers this
stable marriage to any other stable marriage.
-/
def applicantOptimalStableMarriage {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  stableMarriage val_m val_w mu ∧
    ∀ mu', stableMarriage val_m val_w mu' →
      ∀ m, valM val_m m (mu'.m_match m) ≤ valM val_m m (mu.m_match m)

/-! ## Source Theorems -/

/--
Theorem 1: on the strict equal-cardinality marriage domain, a stable complete
marriage exists.
-/
theorem theorem1_stable_marriage_exists
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w) :
    ∃ mu : Assignment M W,
      stableMarriage val_m val_w mu ∧ completeMarriage mu := by
  simpa [strictMarriageDomain, stableMarriage, completeMarriage, IsStable,
    gs_strict_marriage_domain, gs_stable_marriage, gs_complete_marriage] using
    paper_gs62_theorem1_stable_marriage_exists
      val_m val_w hcard hdomain

/--
College-admissions theorem: finite applicants and colleges with arbitrary
quotas and applicant/college utilities admit a stable many-to-one assignment.
-/
theorem college_admissions_stable_assignment_exists
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
Theorem 2: on the finite equal-cardinality strict marriage domain, the
applicant-proposing deferred-acceptance assignment is complete and
applicant-optimal among stable assignments.
-/
theorem theorem2_applicant_optimality
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hcard : Fintype.card Applicants = Fintype.card Colleges)
    (hdomain : strictMarriageDomain val_applicant val_college) :
    completeMarriage (deferredAcceptance val_applicant val_college) ∧
      applicantOptimalStableMarriage val_applicant val_college
        (deferredAcceptance val_applicant val_college) := by
  constructor
  · simpa [strictMarriageDomain, completeMarriage,
      gs_strict_marriage_domain, gs_complete_marriage] using
      gs_deferredAcceptance_complete_on_strict_marriage_domain
        val_applicant val_college hcard hdomain
  · simpa [strictMarriageDomain, stableMarriage, IsStable,
      applicantOptimalStableMarriage, gs_strict_marriage_domain,
      gs_stable_marriage, gs_applicant_optimal_stable_marriage] using
      gs_deferredAcceptance_applicant_optimal_on_strict_marriage_domain
        val_applicant val_college hdomain

end PaperInterface
end GS62CollegeAdmissions
