import IM05MarriageHonestyStability.MainTheorems

/-!
# Paper Interface: Marriage, Honesty, and Stability

This file is the compact human-facing review surface for the IM05
formalization. The paper is not complete: the probabilistic Algorithm 4.1/4.2
route and Section 6 experiment construction are still conditional in the README.
The declarations here expose the closed deterministic source claims that are
ready for paper-vs-Lean review.
-/

namespace IM05MarriageHonestyStability
namespace PaperInterface

open EconCSLib.Matching

/-! ## Paper Definitions -/

/-- Paper stable-matching predicate used by the deterministic IM05 interface. -/
abbrev stableMatching {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (mu : Assignment M W) : Prop :=
  im05_stable_matching val_m val_w mu

/-- Equal-size strict all-acceptable marriage-domain predicate. -/
abbrev strictMarriageDomain {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  im05_strict_marriage_domain val_m val_w

/-! ## Closed Deterministic Statements -/

/-- Theorem A, stability part: men-proposing deferred acceptance finds a stable matching. -/
theorem theoremA_men_proposing_finds_stable
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    im05_stable_matching val_m val_w (deferredAcceptance val_m val_w) := by
  exact
    IM05MarriageHonestyStability.paper_im05_theoremA_men_proposing_finds_stable
      val_m val_w

/--
Theorem B canonical-output core: any stable output satisfying the men-optimality
property is the same matching as the repository's men-proposing deferred
acceptance output.
-/
theorem theoremB_any_men_optimal_output_eq_deferredAcceptance
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hstrictM : MenStrictPreferenceProfile val_m)
    (hstrictW : WomenStrictPreferenceProfile val_w)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    ∀ mu : Assignment M W,
      im05_stable_matching val_m val_w mu →
      (∀ rho, im05_stable_matching val_m val_w rho →
        ∀ m, valM val_m m (rho.m_match m) ≤ valM val_m m (mu.m_match m)) →
      mu = deferredAcceptance val_m val_w := by
  exact
    IM05MarriageHonestyStability.paper_im05_theoremB_any_men_optimal_output_eq_deferredAcceptance
      val_m val_w hcard hstrictM hstrictW hacceptable

/--
Theorem C, complete-domain special case: on equal-size all-acceptable marriage
markets, every stable matching is complete, so the sets of single men and women
are the same across stable matchings.
-/
theorem theoremC_same_singles_on_complete_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    ∀ mu nu : Assignment M W,
      im05_stable_matching val_m val_w mu →
      im05_stable_matching val_m val_w nu →
        im05_singleMen mu = im05_singleMen nu ∧
          im05_singleWomen mu = im05_singleWomen nu := by
  exact
    IM05MarriageHonestyStability.paper_im05_theoremC_same_singles_on_complete_domain
      val_m val_w hcard hacceptable

/--
Theorem D: on the equal-size strict marriage domain, truth-telling is dominant
for the proposing side of the side-optimal deferred-acceptance mechanisms.
-/
theorem theoremD_optimal_side_truthful_on_strict_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        im05_strict_marriage_domain val_m val_w →
          (∀ (m : M) (report_m : W → ℝ),
            valM val_m m
                ((deferredAcceptance
                  (Function.update val_m m report_m) val_w).m_match m) ≤
              valM val_m m
                ((deferredAcceptance val_m val_w).m_match m)) ∧
          (∀ (w : W) (report_w : M → ℝ),
            valW val_w w
                ((im05_women_deferredAcceptance val_m
                  (Function.update val_w w report_w)).w_match w) ≤
              valW val_w w
                ((im05_women_deferredAcceptance val_m val_w).w_match w)) := by
  exact
    IM05MarriageHonestyStability.paper_im05_theoremD_optimal_side_truthful_on_strict_domain_of_card_eq

end PaperInterface
end IM05MarriageHonestyStability
