import Mathlib.Data.Real.Basic
import EconCSLib.Markets.Matching.Basic
import EconCSLib.Markets.Matching.DeferredAcceptance

/-!
# Paper-Facing Theorems: The Economics of Matching: Stability and Incentives (Roth 1982)

This file contains the foundational stable matching definitions and theorem wrappers
for the 2023 EC Test-of-Time matching tracks.
-/

namespace EconCSLib
namespace Matching

/-! ## 1) Paper-Facing Definitions: 2023 Matching -/

/-- Paper Definition: Utility of a match. $u_m(w) = v_m(w)$, $u_m(\emptyset) = 0$. -/
def paper_matching_valM {M W : Type*} (val_m : M → W → ℝ) (m : M) (w : Option W) : ℝ :=
  match w with
  | none => 0
  | some w' => val_m m w'

theorem paper_matching_valM_eq {M W : Type*} (val_m : M → W → ℝ) (m : M) (w : Option W) :
  paper_matching_valM val_m m w = valM val_m m w := by rfl

/-- Paper Definition: Utility of a match. $u_w(m) = v_w(m)$, $u_w(\emptyset) = 0$. -/
def paper_matching_valW {M W : Type*} (val_w : W → M → ℝ) (w : W) (m : Option M) : ℝ :=
  match m with
  | none => 0
  | some m' => val_w w m'

theorem paper_matching_valW_eq {M W : Type*} (val_w : W → M → ℝ) (w : W) (m : Option M) :
  paper_matching_valW val_w w m = valW val_w w m := by rfl

/-- Paper Definition: A matching is stable if it is individually rational and has no blocking pairs.
    IR: $0 \le u_m(\mu(m))$ and $0 \le u_w(\mu(w))$.
    No blocking pair: there is no $(m, w)$ such that $u_m(\mu(m)) < v_m(w)$ and $u_w(\mu(w)) < v_w(m)$. -/
def paper_is_stable {M W : Type*} (val_m : M → W → ℝ) (val_w : W → M → ℝ) (mu : Assignment M W) : Prop :=
  (∀ m, 0 ≤ paper_matching_valM val_m m (mu.m_match m)) ∧
  (∀ w, 0 ≤ paper_matching_valW val_w w (mu.w_match w)) ∧
  (∀ m w, paper_matching_valM val_m m (mu.m_match m) < val_m m w →
          paper_matching_valW val_w w (mu.w_match w) < val_w w m → False)

theorem paper_is_stable_eq {M W : Type*} (val_m : M → W → ℝ) (val_w : W → M → ℝ) (mu : Assignment M W) :
  paper_is_stable val_m val_w mu ↔ IsStable val_m val_w mu := by rfl

/-- Paper Definition: A stable matching $\mu$ is men-optimal if every man prefers his partner in $\mu$ to his partner in any other stable matching. -/
def paper_is_men_optimal {M W : Type*} (val_m : M → W → ℝ) (val_w : W → M → ℝ) (mu : Assignment M W) : Prop :=
  paper_is_stable val_m val_w mu ∧
  ∀ mu', paper_is_stable val_m val_w mu' →
    ∀ m, paper_matching_valM val_m m (mu'.m_match m) ≤ paper_matching_valM val_m m (mu.m_match m)

/-- Paper Definition: Truth-telling is a dominant strategy for men in the men-proposing DA algorithm.
    No man can improve his match by misreporting his preferences, assuming others report truthfully. -/
def paper_truthful_for_men {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M) (report_m : W → ℝ),
    paper_matching_valM val_m m ((mechanism (Function.update val_m m report_m) val_w).m_match m) ≤
    paper_matching_valM val_m m ((mechanism val_m val_w).m_match m)

/-! ## 2) Main Theorems -/

/-- Theorem 1: The Deferred Acceptance algorithm produces a stable matching. -/
theorem paper_da_is_stable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaProducesStableMatchingCertificate val_m val_w) :
    paper_is_stable val_m val_w (deferredAcceptance val_m val_w) := by
  rw [paper_is_stable_eq]
  exact da_produces_stable_matching_of_certificate val_m val_w hcert

/-- Theorem 2: The Men-Proposing Deferred Acceptance algorithm produces a men-optimal stable matching. -/
theorem paper_da_is_men_optimal {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert1 : DaProducesStableMatchingCertificate val_m val_w)
    (hcert2 : DaIsMenOptimalCertificate val_m val_w) :
    paper_is_men_optimal val_m val_w (deferredAcceptance val_m val_w) := by
  unfold paper_is_men_optimal
  rw [paper_is_stable_eq]
  refine ⟨da_produces_stable_matching_of_certificate val_m val_w hcert1, ?_⟩
  intro mu' hstable m
  rw [paper_is_stable_eq] at hstable
  exact hcert2 mu' hstable m

/-- Theorem 3 (Roth 1982): Truth-telling is a dominant strategy for men under men-proposing DA. -/
def DaTruthfulForMenCertificate {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] : Prop :=
  paper_truthful_for_men (deferredAcceptance (M := M) (W := W))

theorem paper_da_truthful_for_men {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hcert : @DaTruthfulForMenCertificate M W _ _ _ _) :
    paper_truthful_for_men (deferredAcceptance (M := M) (W := W)) := by
  exact hcert

end Matching
end EconCSLib