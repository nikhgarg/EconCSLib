import Roth82StableMatching.MainTheorems

/-!
# Post-Paper Audit: Roth 1982 Stable Matching

This ledger exposes source-numbered final endpoints for the post-verification
audit. For the compact human-facing statement surface, read
`PaperInterface.lean`. Each declaration here is intentionally a thin alias to
the paper-facing theorem proved in `MainTheorems.lean`, so the source inventory
can be checked from one importable file without duplicating proof scripts.
-/

namespace Roth82StableMatching
open EconCSLib.Matching

namespace PostPaperAudit

/-- Audit endpoint for Roth Theorem 1: existence of a stable outcome. -/
theorem audit_roth82_theorem1_stable_outcome_exists
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    ∃ mu : Assignment M W, paper_is_stable val_m val_w mu :=
  paper_roth82_theorem1_stable_outcome_exists val_m val_w

/--
Audit endpoint for Roth Theorem 1 on the equal-size strict marriage domain:
existence of a stable complete matching.
-/
theorem audit_roth82_theorem1_stable_complete_outcome_exists_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    ∃ mu : Assignment M W,
      paper_is_stable val_m val_w mu ∧ paper_is_complete_matching mu :=
  paper_roth82_theorem1_stable_complete_outcome_exists_on_strict_marriage_domain
    val_m val_w hcard hdomain

/--
Audit endpoint for Roth Theorem 2: men-optimal and women-optimal stable
outcomes on the strict marriage domain.
-/
theorem audit_roth82_theorem2_optimal_stable_outcomes_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    (∃ mu : Assignment M W, paper_is_men_optimal val_m val_w mu) ∧
      (∃ mu : Assignment M W, paper_is_women_optimal val_m val_w mu) :=
  paper_roth82_theorem2_optimal_stable_outcomes_on_strict_marriage_domain
    val_m val_w hdomain

/--
Audit endpoint for Roth Theorem 3: no stable matching procedure is truthful for
both sides.
-/
theorem audit_roth82_theorem3_no_stable_truthful_procedure :
    ¬ ∃ mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent,
      paper_stable_matching_procedure mechanism ∧
        paper_truthful_for_men mechanism ∧ paper_truthful_for_women mechanism :=
  paper_roth82_theorem3_no_stable_truthful_procedure

/--
Audit endpoint for Roth Theorem 4: the constructed serial-dictatorship route is
efficient on strict profiles and strategyproof.
-/
theorem audit_roth82_theorem4_serial_dictatorship_constructed {n : ℕ} :
    paper_efficient_matching_procedure_on_strict_men
        (paper_serial_dictatorship_mechanism (n := n)) ∧
      paper_truthful_for_men_on_strict_men
        (paper_serial_dictatorship_mechanism (n := n)) ∧
      paper_truthful_for_women
        (paper_serial_dictatorship_mechanism (n := n)) :=
  paper_roth82_theorem4_serial_dictatorship_constructed

/--
Audit endpoint for Roth Lemma 1: a simple misrepresentation that leaves the
manipulator's partner unchanged preserves stability of that partner.
-/
theorem audit_roth82_lemma1_strict_simple_misrepresentation_same_partner
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M)
    (report_m simple_report_m : W → ℝ) (wstar : W)
    (hdomainSimple :
      paper_strict_marriage_domain (Function.update val_m m simple_report_m) val_w)
    (hyPartner :
      (deferredAcceptance (Function.update val_m m report_m) val_w).m_match m =
        some wstar)
    (hfirst : ∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar) :
    (deferredAcceptance (Function.update val_m m simple_report_m) val_w).m_match m =
      (deferredAcceptance (Function.update val_m m report_m) val_w).m_match m :=
  paper_roth82_lemma1_strict_simple_misrepresentation_same_partner
    val_m val_w m report_m simple_report_m wstar hdomainSimple hyPartner hfirst

/--
Audit endpoint for Roth Lemma 2: a simple misrepresentation by one man cannot
harm any other man on the strict marriage domain.
-/
theorem audit_roth82_lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (simple_report_m : W → ℝ) (ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hdomainReport :
      paper_strict_marriage_domain
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
        (deferredAcceptance val_m val_w) :=
  paper_roth82_lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain
    val_m val_w m simple_report_m ystar hcard hdomain hdomainReport hy hweakM hfirst

/--
Audit endpoint for Roth Theorem 5: the side-optimal deferred-acceptance
procedures are strategyproof for their proposing side on the equal-size strict
marriage domain.
-/
theorem audit_roth82_theorem5_optimal_side_truthful_on_strict_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        paper_strict_marriage_domain val_m val_w →
          (∀ (m : M) (report_m : W → ℝ),
            paper_matching_valM val_m m
                ((deferredAcceptance
                  (Function.update val_m m report_m) val_w).m_match m) ≤
              paper_matching_valM val_m m
                ((deferredAcceptance val_m val_w).m_match m)) ∧
          (∀ (w : W) (report_w : M → ℝ),
            paper_matching_valW val_w w
                ((paper_women_deferredAcceptance val_m
                  (Function.update val_w w report_w)).w_match w) ≤
              paper_matching_valW val_w w
                ((paper_women_deferredAcceptance val_m val_w).w_match w)) :=
  paper_roth82_theorem5_optimal_side_truthful_on_strict_domain_of_card_eq

/--
Audit endpoint for Roth Corollary 5.1: women do not need to misrepresent their
first choices to obtain the best available manipulation outcome.
-/
theorem audit_roth82_corollary5_1_no_need_to_misrepresent_first_choice_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M] :
    paper_no_need_to_misrepresent_first_choice_for_women_on_strict_domain
      (deferredAcceptance (M := M) (W := W)) :=
  paper_roth82_corollary5_1_no_need_to_misrepresent_first_choice_on_strict_domain

/--
Audit endpoint for Roth Theorem 6: no feasible outcome is strictly better for
all men than the men-optimal stable outcome.
-/
theorem audit_roth82_theorem6_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    paper_weakly_pareto_optimal_for_men val_m (deferredAcceptance val_m val_w) :=
  paper_roth82_theorem6_on_strict_marriage_domain
    val_m val_w hcard hdomain

/--
Audit endpoint for Roth Theorem 7: for every `k > 1`, a stable procedure admits
a profitable `k`th-choice misrepresentation on some finite balanced market.
-/
theorem audit_roth82_theorem7_arbitrary_k :
    ∀ k, 1 < k →
      ∃ n : ℕ,
        paper_no_stable_procedure_avoids_kth_choice_manipulation_on
          (Fin n) (Fin n) k :=
  paper_roth82_theorem7_arbitrary_k

end PostPaperAudit

end Roth82StableMatching
