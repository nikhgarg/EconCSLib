import Roth82StableMatching.MainTheorems

/-!
# Paper Interface: Roth 1982 Stable Matching

This is the compact human-facing Lean surface for Roth's
*The Economics of Matching: Stability and Incentives*. It exposes the paper's
core definitions and direct named-result statements. The long deferred-
acceptance trace proofs, counterexample enumerations, compatibility wrappers,
and exhaustive proof-seam aliases live in `MainTheorems.lean` and
`PostPaperAudit.lean`.

Roth discusses quota and many-to-one general matching problems, then uses the
strict-preference marriage problem as the representation for the paper's formal
arguments. This interface follows that source route: it formalizes the
one-to-one marriage-problem representation, while quota expansion is documented
as source scope rather than modeled as a separate Lean API here.
-/

namespace Roth82StableMatching
namespace PaperInterface

open EconCSLib.Matching

universe u v

/-! ## Paper Definitions -/

/-- Roth preference profile `P`: one score table for each side. -/
def preferenceProfile (M : Type u) (W : Type v) : Type (max u v) :=
  (M → W → ℝ) × (W → M → ℝ)

/-- Marriage-problem outcome: a complete one-to-one matching. -/
def completeMarriageOutcome {M W : Type*} (mu : Assignment M W) : Prop :=
  (∀ m, ∃ w, mu.m_match m = some w) ∧
    (∀ w, ∃ m, mu.w_match w = some m)

/--
Stable matching: every assigned partner is acceptable and no man-woman pair
strictly blocks the matching.
-/
def stable {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  (∀ m, 0 ≤ (match mu.m_match m with
    | none => 0
    | some w => val_m m w)) ∧
    (∀ w, 0 ≤ (match mu.w_match w with
      | none => 0
      | some m => val_w w m)) ∧
      (∀ m w,
        (match mu.m_match m with
          | none => 0
          | some w' => val_m m w') < val_m m w →
        val_w w m ≤
          (match mu.w_match w with
            | none => 0
            | some m' => val_w w m'))

/--
Strict marriage domain: each side has strict rankings over the opposite side,
and every potential pair is strictly preferred to being unmatched.
-/
def strictMarriageDomain {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  (∀ m w w', val_m m w = val_m m w' → w = w') ∧
    (∀ w m m', val_w w m = val_w w m' → m = m') ∧
      (∀ m w, 0 < val_m m w) ∧
        (∀ w m, 0 < val_w w m)

/-- The stable-outcome set `C(P)` for a reported preference profile. -/
def stableOutcomes {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Set (Assignment M W) :=
  {mu | stable val_m val_w mu}

/-- A stable matching is men-optimal if every man weakly prefers it to any stable matching. -/
def menOptimal {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  stable val_m val_w mu ∧
    ∀ mu', stable val_m val_w mu' →
      ∀ m, (match mu'.m_match m with
        | none => 0
        | some w => val_m m w) ≤
        (match mu.m_match m with
          | none => 0
          | some w => val_m m w)

/-- Women-optimal stable matching, with the symmetric weak-preference condition. -/
def womenOptimal {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  stable val_m val_w mu ∧
    ∀ mu', stable val_m val_w mu' →
      ∀ w, (match mu'.w_match w with
        | none => 0
        | some m => val_w w m) ≤
        (match mu.w_match w with
          | none => 0
          | some m => val_w w m)

/-- A woman is possible for a man if some stable outcome matches them. -/
def possibleForMan {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M) (w : W) : Prop :=
  ∃ mu, stable val_m val_w mu ∧ mu.m_match m = some w

/-- Stable matching procedure on strict reported preference profiles. -/
def stableMatchingProcedure {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ val_m val_w,
    (∀ m w w', val_m m w = val_m m w' → w = w') →
      (∀ w m m', val_w w m = val_w w m' → m = m') →
        stable val_m val_w (mechanism val_m val_w)

/-- Truthful revelation is dominant for both sides on strict true and reported profiles. -/
def truthfulForAllAgents {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  (∀ val_m val_w,
    (∀ m w w', val_m m w = val_m m w' → w = w') →
      (∀ w m m', val_w w m = val_w w m' → m = m') →
        ∀ m report_m,
          (∀ i w w', ((Function.update val_m m report_m) i) w =
              ((Function.update val_m m report_m) i) w' → w = w') →
            (match (mechanism (Function.update val_m m report_m) val_w).m_match m with
              | none => 0
              | some w => val_m m w) ≤
            (match (mechanism val_m val_w).m_match m with
              | none => 0
              | some w => val_m m w)) ∧
    (∀ val_m val_w,
      (∀ m w w', val_m m w = val_m m w' → w = w') →
        (∀ w m m', val_w w m = val_w w m' → m = m') →
          ∀ w report_w,
            (∀ j m m', ((Function.update val_w w report_w) j) m =
                ((Function.update val_w w report_w) j) m' → m = m') →
              (match (mechanism val_m (Function.update val_w w report_w)).w_match w with
                | none => 0
                | some m => val_w w m) ≤
              (match (mechanism val_m val_w).w_match w with
                | none => 0
                | some m => val_w w m))

/-- Men-proposing deferred acceptance, Roth's procedure/outcome `G(P)`/`g(P)`. -/
noncomputable def menDeferredAcceptance
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W :=
  deferredAcceptance val_m val_w

/--
Women-proposing deferred acceptance, represented on the original `(M, W)`
sides by reversing roles and swapping the resulting assignment back.
-/
noncomputable def womenDeferredAcceptance
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W :=
  (deferredAcceptance (M := W) (W := M) val_w val_m).swap

/-- Pareto-optimal complete matching among complete matchings. -/
def paretoOptimal {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  completeMarriageOutcome mu ∧
    ¬ ∃ nu, completeMarriageOutcome nu ∧
      (∀ m, (match mu.m_match m with
          | none => 0
          | some w => val_m m w) ≤
        (match nu.m_match m with
          | none => 0
          | some w => val_m m w)) ∧
      (∀ w, (match mu.w_match w with
          | none => 0
          | some m => val_w w m) ≤
        (match nu.w_match w with
          | none => 0
          | some m => val_w w m)) ∧
      ((∃ m, (match mu.m_match m with
          | none => 0
          | some w => val_m m w) <
        (match nu.m_match m with
          | none => 0
          | some w => val_m m w)) ∨
      (∃ w, (match mu.w_match w with
          | none => 0
          | some m => val_w w m) <
        (match nu.w_match w with
          | none => 0
          | some m => val_w w m)))

/-- Efficient procedure: every reported preference profile returns a Pareto-optimal matching. -/
def efficientMatchingProcedure {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ val_m val_w, paretoOptimal val_m val_w (mechanism val_m val_w)

/-- The serial-dictatorship mechanism constructed in Roth's Theorem 4 route. -/
noncomputable def serialDictatorshipMechanism {n : ℕ} :
    (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) → Assignment (Fin n) (Fin n) :=
  paper_serial_dictatorship_mechanism (n := n)

/--
The serial-dictatorship mechanism chooses its permutation from the men's
reported preferences and matches each man to `p m` and each woman to `p.symm w`.
-/
theorem serialDictatorshipMechanism_matches {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (val_w : Fin n → Fin n → ℝ)
    (m w : Fin n) :
    (serialDictatorshipMechanism val_m val_w).m_match m =
        some (paper_serial_dictatorship_perm val_m m) ∧
      (serialDictatorshipMechanism val_m val_w).w_match w =
        some ((paper_serial_dictatorship_perm val_m).symm w) := by
  exact ⟨rfl, rfl⟩

/-- A report strictly ranks the optional partner first. -/
def manReportStrictlyRanksPartnerFirst {W : Type*} (report_m : W → ℝ)
    (partner : Option W) : Prop :=
  match partner with
  | none => ∀ w, report_m w < 0
  | some wstar => ∀ w, w ≠ wstar → report_m w < report_m wstar

/-- A report changes the identity of some alternative that was truly ranked `k`. -/
def reportMisrepresentsKthChoice {A : Type*} [Fintype A] [DecidableEq A]
    (true_score report_score : A → ℝ) (k : ℕ) : Prop :=
  ∃ a,
    ((Finset.univ : Finset A).filter fun b => true_score a < true_score b).card + 1 = k ∧
      ((Finset.univ : Finset A).filter fun b => report_score a < report_score b).card + 1 ≠ k

/-! ## Source Theorems -/

/--
Theorem 1: on an equal-size strict marriage domain, a stable complete outcome
exists.
-/
theorem theorem1_stable_complete_outcome_exists_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w) :
    ∃ mu : Assignment M W, stable val_m val_w mu ∧ completeMarriageOutcome mu := by
  simpa [strictMarriageDomain, stable, completeMarriageOutcome,
    paper_strict_marriage_domain, paper_is_stable, paper_is_complete_matching,
    paper_matching_valM, paper_matching_valW] using
    paper_roth82_theorem1_stable_complete_outcome_exists_on_strict_marriage_domain
      val_m val_w hcard hdomain

/-- Theorem 2: men-optimal and women-optimal stable outcomes exist on the strict marriage domain. -/
theorem theorem2_optimal_stable_outcomes_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hdomain : strictMarriageDomain val_m val_w) :
    (∃ mu : Assignment M W, menOptimal val_m val_w mu) ∧
      (∃ nu : Assignment M W, womenOptimal val_m val_w nu) := by
  simpa [menOptimal, womenOptimal, stable, strictMarriageDomain,
    paper_is_men_optimal, paper_is_women_optimal, paper_is_stable,
    paper_matching_valM, paper_matching_valW, paper_strict_marriage_domain] using
    paper_roth82_theorem2_optimal_stable_outcomes_on_strict_marriage_domain
      val_m val_w hdomain

/--
Theorem 3: on Roth's strict 3-by-3 counterexample domain, no procedure stable
on strict profiles is truthful for both sides.
-/
theorem theorem3_no_stable_truthful_procedure_on_strict_profiles :
    ¬ ∃ mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent,
      stableMatchingProcedure mechanism ∧ truthfulForAllAgents mechanism := by
  rintro ⟨mechanism, hstable, hmenTruth, hwomenTruth⟩
  apply paper_roth82_theorem3_no_stable_truthful_procedure_on_strict_profiles
  refine ⟨mechanism, ?_, ?_, ?_⟩
  · intro val_m val_w hstrict
    simpa [stableMatchingProcedure, stable, paper_is_stable, paper_matching_valM,
      paper_matching_valW, paper_strict_preference_profile] using
      hstable val_m val_w hstrict.1 hstrict.2
  · intro val_m val_w hstrict m report_m hreport
    simpa [truthfulForAllAgents, paper_truthful_for_men_on_strict_profiles,
      paper_matching_valM, paper_strict_preference_profile] using
      hmenTruth val_m val_w hstrict.1 hstrict.2 m report_m hreport.1
  · intro val_m val_w hstrict w report_w hreport
    simpa [truthfulForAllAgents, paper_truthful_for_women_on_strict_profiles,
      paper_matching_valW, paper_strict_preference_profile] using
      hwomenTruth val_m val_w hstrict.1 hstrict.2 w report_w hreport.2

/--
Theorem 4: Roth's constructed serial-dictatorship procedure is efficient on
strict men-side profiles, truthful for men on that strict men-side domain, and
truthful for women.
-/
theorem theorem4_serial_dictatorship_constructed {n : ℕ} :
    (∀ val_m val_w,
      (∀ m w w', val_m m w = val_m m w' → w = w') →
        paretoOptimal val_m val_w
          (serialDictatorshipMechanism (n := n) val_m val_w)) ∧
      (∀ val_m val_w,
        (∀ m w w', val_m m w = val_m m w' → w = w') →
          ∀ m report_m,
            (match (serialDictatorshipMechanism (n := n)
                (Function.update val_m m report_m) val_w).m_match m with
              | none => 0
              | some w => val_m m w) ≤
            (match (serialDictatorshipMechanism (n := n) val_m val_w).m_match m with
              | none => 0
              | some w => val_m m w)) ∧
      (∀ val_m val_w w report_w,
        (match (serialDictatorshipMechanism (n := n) val_m
            (Function.update val_w w report_w)).w_match w with
          | none => 0
          | some m => val_w w m) ≤
        (match (serialDictatorshipMechanism (n := n) val_m val_w).w_match w with
          | none => 0
          | some m => val_w w m)) := by
  simpa [serialDictatorshipMechanism, paretoOptimal, completeMarriageOutcome,
    paper_efficient_matching_procedure_on_strict_men,
    paper_truthful_for_men_on_strict_men, paper_truthful_for_women,
    paper_men_strict_preferences, paper_is_pareto_optimal,
    paper_pareto_improves, paper_pareto_dominates, paper_is_complete_matching,
    paper_matching_valM, paper_matching_valW] using
    paper_roth82_theorem4_serial_dictatorship_constructed (n := n)

/-- Theorem 5: side-optimal deferred-acceptance procedures are strategyproof on equal-size strict marriage domains. -/
theorem theorem5_optimal_side_truthful_on_strict_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        strictMarriageDomain val_m val_w →
          (∀ (m : M) (report_m : W → ℝ),
            (match (menDeferredAcceptance
                (Function.update val_m m report_m) val_w).m_match m with
              | none => 0
              | some w => val_m m w) ≤
            (match (menDeferredAcceptance val_m val_w).m_match m with
              | none => 0
              | some w => val_m m w)) ∧
          (∀ (w : W) (report_w : M → ℝ),
            (match (womenDeferredAcceptance val_m
                (Function.update val_w w report_w)).w_match w with
              | none => 0
              | some m => val_w w m) ≤
            (match (womenDeferredAcceptance val_m val_w).w_match w with
              | none => 0
              | some m => val_w w m)) := by
  simpa [strictMarriageDomain, menDeferredAcceptance, womenDeferredAcceptance,
    paper_women_deferredAcceptance, paper_strict_marriage_domain,
    paper_matching_valM, paper_matching_valW] using
    (paper_roth82_theorem5_optimal_side_truthful_on_strict_domain_of_card_eq
      (M := M) (W := W))

/--
Corollary 5.1: under each side-optimal DA procedure, the non-proposing side can
match any report's outcome with a report preserving its true first choice.
-/
theorem corollary5_1_no_need_to_misrepresent_first_choice
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M] [Nonempty W] :
    (∀ val_m val_w, strictMarriageDomain val_m val_w →
      ∀ (w : W) (report_w : M → ℝ), ∃ report_w' : M → ℝ,
        (∀ mstar, (∀ m, m ≠ mstar → val_w w m < val_w w mstar) →
          ∀ m, m ≠ mstar → report_w' m < report_w' mstar) ∧
          (match (menDeferredAcceptance val_m
              (Function.update val_w w report_w)).w_match w with
            | none => 0
            | some m => val_w w m) ≤
          (match (menDeferredAcceptance val_m
              (Function.update val_w w report_w')).w_match w with
            | none => 0
            | some m => val_w w m)) ∧
      (∀ val_m val_w, strictMarriageDomain val_m val_w →
        ∀ (m : M) (report_m : W → ℝ), ∃ report_m' : W → ℝ,
          (∀ wstar, (∀ w, w ≠ wstar → val_m m w < val_m m wstar) →
            ∀ w, w ≠ wstar → report_m' w < report_m' wstar) ∧
            (match (womenDeferredAcceptance
                (Function.update val_m m report_m) val_w).m_match m with
              | none => 0
              | some w => val_m m w) ≤
            (match (womenDeferredAcceptance
                (Function.update val_m m report_m') val_w).m_match m with
              | none => 0
              | some w => val_m m w)) := by
  constructor
  · simpa [menDeferredAcceptance, strictMarriageDomain,
      paper_no_need_to_misrepresent_first_choice_for_women_on_strict_domain,
      paper_woman_report_preserves_first_choice,
      paper_is_strict_top_choice_for_woman, paper_woman_weakly_prefers_outcome,
      paper_strict_marriage_domain, paper_matching_valW] using
      paper_roth82_corollary5_1_no_need_to_misrepresent_first_choice_on_strict_domain
        (M := M) (W := W)
  · simpa [womenDeferredAcceptance, strictMarriageDomain,
      paper_no_need_to_misrepresent_first_choice_for_men_on_strict_domain,
      paper_man_report_preserves_first_choice, paper_is_strict_top_choice_for_man,
      paper_man_weakly_prefers_outcome, paper_strict_marriage_domain,
      paper_matching_valM, paper_women_deferredAcceptance] using
      paper_roth82_corollary5_1_role_reversed_no_need_to_misrepresent_first_choice_on_strict_domain
        (M := M) (W := W)

/-- Lemma 1: Roth's strict simple-misrepresentation same-partner route. -/
theorem lemma1_strict_simple_misrepresentation_same_partner
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M)
    (report_m simple_report_m : W → ℝ) (wstar : W)
    (hdomainSimple :
      strictMarriageDomain (Function.update val_m m simple_report_m) val_w)
    (hyPartner :
      (menDeferredAcceptance (Function.update val_m m report_m) val_w).m_match m =
        some wstar)
    (hfirst : ∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar) :
    (menDeferredAcceptance (Function.update val_m m simple_report_m) val_w).m_match m =
      (menDeferredAcceptance (Function.update val_m m report_m) val_w).m_match m := by
  simpa [menDeferredAcceptance, strictMarriageDomain, paper_strict_marriage_domain] using
    paper_roth82_lemma1_strict_simple_misrepresentation_same_partner
      val_m val_w m report_m simple_report_m wstar hdomainSimple hyPartner hfirst

/-- Lemma 2: a strict simple misrepresentation cannot harm any other man on the strict marriage domain. -/
theorem lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (simple_report_m : W → ℝ) (ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w)
    (hdomainReport :
      strictMarriageDomain
        (Function.update val_m m simple_report_m) val_w)
    (hy :
      (menDeferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hweakM :
      (match (menDeferredAcceptance val_m val_w).m_match m with
        | none => 0
        | some w => val_m m w) ≤
      (match (menDeferredAcceptance
          (Function.update val_m m simple_report_m) val_w).m_match m with
        | none => 0
        | some w => val_m m w))
    (hfirst : manReportStrictlyRanksPartnerFirst simple_report_m (some ystar)) :
    ∀ m',
      (match (menDeferredAcceptance val_m val_w).m_match m' with
        | none => 0
        | some w => val_m m' w) ≤
      (match (menDeferredAcceptance
          (Function.update val_m m simple_report_m) val_w).m_match m' with
        | none => 0
        | some w => val_m m' w) := by
  simpa [menDeferredAcceptance, strictMarriageDomain, paper_strict_marriage_domain,
    paper_man_weakly_prefers_outcome, manReportStrictlyRanksPartnerFirst,
    paper_man_report_strictly_ranks_partner_first, paper_matching_valM] using
    paper_roth82_lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain
      val_m val_w m simple_report_m ystar hcard hdomain hdomainReport hy hweakM hfirst

/-- Theorem 6: the men-optimal stable outcome is weakly Pareto optimal on the strict marriage domain. -/
theorem theorem6_weak_pareto_for_men_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w) :
    ¬ ∃ nu : Assignment M W, completeMarriageOutcome nu ∧
      ∀ m, (match (menDeferredAcceptance val_m val_w).m_match m with
        | none => 0
        | some w => val_m m w) <
        (match nu.m_match m with
          | none => 0
          | some w => val_m m w) := by
  simpa [menDeferredAcceptance, completeMarriageOutcome,
    paper_weakly_pareto_optimal_for_men, paper_strictly_better_for_all_men,
    paper_is_complete_matching, paper_matching_valM, strictMarriageDomain,
    paper_strict_marriage_domain] using
    paper_roth82_theorem6_on_strict_marriage_domain
      val_m val_w hcard hdomain

/--
Theorem 7: for any `k > 1`, some finite balanced strict-profile market admits a
profitable stable-procedure `k`th-choice manipulation.
-/
theorem theorem7_arbitrary_k_on_strict_profiles :
    ∀ k, 1 < k →
      ∃ n : ℕ,
        paper_no_stable_procedure_avoids_strict_kth_choice_manipulation_on
          (Fin n) (Fin n) k :=
  paper_roth82_theorem7_arbitrary_k_on_strict_profiles

end PaperInterface
end Roth82StableMatching
