import Roth82StableMatching.MainTheorems

/-!
# Paper Interface: Roth 1982 Stable Matching

This is the compact human-facing Lean surface for Roth's
*The Economics of Matching: Stability and Incentives*.  It lists the main
paper definitions and direct named-result statements.  The long DA trace
proofs and counterexample enumerations live in `MainTheorems.lean`.
-/

namespace Roth82StableMatching
namespace PaperInterface

open EconCSLib.Matching

/-! ## Paper Definitions -/

/-- Utility of a possible man-side match, with outside option value `0`. -/
def matchingValM {M W : Type*} (val_m : M → W → ℝ)
    (m : M) (w : Option W) : ℝ :=
  match w with
  | none => 0
  | some w' => val_m m w'

/-- Utility of a possible woman-side match, with outside option value `0`. -/
def matchingValW {M W : Type*} (val_w : W → M → ℝ)
    (w : W) (m : Option M) : ℝ :=
  match m with
  | none => 0
  | some m' => val_w w m'

/--
Stable matching: every assigned partner is acceptable and no man-woman pair
strictly blocks the matching.
-/
def stable {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  (∀ m, 0 ≤ matchingValM val_m m (mu.m_match m)) ∧
    (∀ w, 0 ≤ matchingValW val_w w (mu.w_match w)) ∧
      (∀ m w, matchingValM val_m m (mu.m_match m) < val_m m w →
        matchingValW val_w w (mu.w_match w) < val_w w m → False)

/-- A stable matching is men-optimal if every man weakly prefers it to any stable matching. -/
def menOptimal {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  stable val_m val_w mu ∧
    ∀ mu', stable val_m val_w mu' →
      ∀ m, matchingValM val_m m (mu'.m_match m) ≤
        matchingValM val_m m (mu.m_match m)

/-- Women-optimal stable matching, with the symmetric weak-preference condition. -/
def womenOptimal {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  stable val_m val_w mu ∧
    ∀ mu', stable val_m val_w mu' →
      ∀ w, matchingValW val_w w (mu'.w_match w) ≤
        matchingValW val_w w (mu.w_match w)

/--
Strict marriage domain: each side's utility profile gives strict rankings over
the opposite side, and every potential pair is strictly preferred to being
unmatched.
-/
def strictMarriageDomain {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  (∀ m w w', val_m m w = val_m m w' → w = w') ∧
    (∀ w m m', val_w w m = val_w w m' → m = m') ∧
      (∀ m w, 0 < val_m m w) ∧
        (∀ w m, 0 < val_w w m)

/-- Complete matching: every agent on both sides is matched. -/
def completeMatching {M W : Type*} (mu : Assignment M W) : Prop :=
  (∀ m, ∃ w, mu.m_match m = some w) ∧
    (∀ w, ∃ m, mu.w_match w = some m)

/-- Truthfulness for men in a direct stable matching procedure. -/
def truthfulForMen {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M) (report_m : W → ℝ),
    matchingValM val_m m
        ((mechanism (Function.update val_m m report_m) val_w).m_match m) ≤
      matchingValM val_m m ((mechanism val_m val_w).m_match m)

/-- Truthfulness for women in a direct stable matching procedure. -/
def truthfulForWomen {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ) (w : W) (report_w : M → ℝ),
    matchingValW val_w w
        ((mechanism val_m (Function.update val_w w report_w)).w_match w) ≤
      matchingValW val_w w ((mechanism val_m val_w).w_match w)

/-- Weak Pareto optimality for men: no feasible matching is strictly better for every man. -/
def weaklyParetoOptimalForMen {M W : Type*}
    (val_m : M → W → ℝ) (mu : Assignment M W) : Prop :=
  ¬ ∃ mu' : Assignment M W,
    (∀ m, matchingValM val_m m (mu.m_match m) <
      matchingValM val_m m (mu'.m_match m))

/-! ## Source Theorems -/

/-- Theorem 1: stable outcomes are nonempty. -/
theorem theorem1_stable_outcome_exists
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    ∃ mu : Assignment M W, stable val_m val_w mu := by
  simpa [stable, matchingValM, matchingValW, paper_is_stable,
    paper_matching_valM, paper_matching_valW] using
    paper_roth82_theorem1_stable_outcome_exists val_m val_w

/-- Theorem 2: men-optimal and women-optimal stable outcomes exist. -/
theorem theorem2_optimal_stable_outcomes
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hdomain : strictMarriageDomain val_m val_w) :
    (∃ mu : Assignment M W, menOptimal val_m val_w mu) ∧
      (∃ mu : Assignment M W, womenOptimal val_m val_w mu) := by
  simpa [strictMarriageDomain, menOptimal, womenOptimal, stable,
    matchingValM, matchingValW, paper_strict_marriage_domain,
    paper_is_men_optimal, paper_is_women_optimal, paper_is_stable,
    paper_matching_valM, paper_matching_valW] using
    paper_roth82_theorem2_optimal_stable_outcomes_on_strict_marriage_domain
      val_m val_w hdomain

/-- Theorem 3: no stable matching procedure is truthful for both sides. -/
theorem theorem3_no_stable_truthful_procedure :
    ¬ ∃ mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent,
      paper_stable_matching_procedure mechanism ∧
        paper_truthful_for_men mechanism ∧ paper_truthful_for_women mechanism :=
  paper_roth82_theorem3_no_stable_truthful_procedure

/-- Theorem 4: efficient strategyproof procedures exist. -/
theorem theorem4_serial_dictatorship_constructed {n : ℕ} :
    paper_efficient_matching_procedure_on_strict_men
        (paper_serial_dictatorship_mechanism (n := n)) ∧
      paper_truthful_for_men_on_strict_men
        (paper_serial_dictatorship_mechanism (n := n)) ∧
      paper_truthful_for_women
        (paper_serial_dictatorship_mechanism (n := n)) :=
  paper_roth82_theorem4_serial_dictatorship_constructed

/-- Theorem 5: side-optimal deferred-acceptance procedures are strategyproof. -/
theorem theorem5_optimal_side_truthful
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        strictMarriageDomain val_m val_w →
          (∀ (m : M) (report_m : W → ℝ),
            matchingValM val_m m
                ((deferredAcceptance
                  (Function.update val_m m report_m) val_w).m_match m) ≤
              matchingValM val_m m
                ((deferredAcceptance val_m val_w).m_match m)) ∧
          (∀ (w : W) (report_w : M → ℝ),
            matchingValW val_w w
                ((paper_women_deferredAcceptance val_m
                  (Function.update val_w w report_w)).w_match w) ≤
              matchingValW val_w w
                ((paper_women_deferredAcceptance val_m val_w).w_match w)) := by
  simpa [strictMarriageDomain, matchingValM, matchingValW,
    paper_strict_marriage_domain, paper_matching_valM, paper_matching_valW] using
    (paper_roth82_theorem5_optimal_side_truthful_on_strict_domain_of_card_eq
      (M := M) (W := W))

/-- Corollary 5.1: the opposite side need not misrepresent its first choice. -/
theorem corollary5_1_no_need_to_misrepresent_first_choice
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M] :
    paper_no_need_to_misrepresent_first_choice_for_women_on_strict_domain
      (deferredAcceptance (M := M) (W := W)) :=
  paper_roth82_corollary5_1_no_need_to_misrepresent_first_choice_on_strict_domain

/-- Lemma 1: Roth's strict simple-misrepresentation same-partner route. -/
theorem lemma1_strict_simple_misrepresentation_same_partner
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M)
    (report_m simple_report_m : W → ℝ) (wstar : W)
    (hdomainSimple :
      strictMarriageDomain (Function.update val_m m simple_report_m) val_w)
    (hyPartner :
      (deferredAcceptance (Function.update val_m m report_m) val_w).m_match m =
        some wstar)
    (hfirst : ∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar) :
    (deferredAcceptance (Function.update val_m m simple_report_m) val_w).m_match m =
      (deferredAcceptance (Function.update val_m m report_m) val_w).m_match m := by
  simpa [strictMarriageDomain, paper_strict_marriage_domain] using
    paper_roth82_lemma1_strict_simple_misrepresentation_same_partner
      val_m val_w m report_m simple_report_m wstar hdomainSimple hyPartner hfirst

/-- Lemma 2: a strict simple misrepresentation cannot harm any other man. -/
theorem lemma2_strict_simple_misrepresentation_no_men_harmed
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (simple_report_m : W → ℝ) (ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w)
    (hdomainReport :
      strictMarriageDomain
        (Function.update val_m m simple_report_m) val_w)
    (hy :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hweakM :
      paper_man_weakly_prefers_outcome val_m m
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w))
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar)) :
    ∀ m',
      paper_man_weakly_prefers_outcome val_m m'
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w) := by
  simpa [strictMarriageDomain, paper_strict_marriage_domain] using
    paper_roth82_lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain
      val_m val_w m simple_report_m ystar hcard hdomain hdomainReport hy hweakM hfirst

/-- Theorem 6: the men-optimal stable outcome is weakly Pareto optimal for men. -/
theorem theorem6_weak_pareto_for_men
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w) :
    paper_weakly_pareto_optimal_for_men val_m (deferredAcceptance val_m val_w) := by
  simpa [strictMarriageDomain, paper_strict_marriage_domain] using
    paper_roth82_theorem6_on_strict_marriage_domain
      val_m val_w hcard hdomain

/-- Theorem 7: every stable procedure admits a profitable `k`th-choice manipulation. -/
theorem theorem7_arbitrary_k :
    ∀ k, 1 < k →
      ∃ n : ℕ,
        paper_no_stable_procedure_avoids_kth_choice_manipulation_on
          (Fin n) (Fin n) k :=
  paper_roth82_theorem7_arbitrary_k

end PaperInterface
end Roth82StableMatching
