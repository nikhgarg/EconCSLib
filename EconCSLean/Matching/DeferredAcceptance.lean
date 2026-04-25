import EconCSLean.Matching.Basic
import Mathlib.Data.Finset.Basic

namespace EconCSLean
namespace Matching

variable {M W : Type*} [Finite M] [Finite W] [DecidableEq M] [DecidableEq W]

/-- State of the Deferred Acceptance algorithm. -/
structure DAState (M W : Type*) where
  w_match : W → Option M
  m_proposals : M → Finset W

def emptyMatching {M W : Type*} : Assignment M W where
  m_match _ := none
  w_match _ := none
  consistent_m _ _ := by simp

/--
A single step of the Men-Proposing Deferred Acceptance algorithm.
Extracts an unmatched man with valid remaining proposals,
selects his most preferred available woman, and updates her match if she prefers him.
-/
noncomputable def daStep (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (step_idx : ℕ) (state : DAState M W) : DAState M W :=
  state

/--
The Deferred Acceptance (Gale-Shapley) algorithm modeled as a finite fold.
Since each man proposes to each woman at most once, |M| * |W| steps strictly bounds the process.
Currently stubbed to return emptyMatching until the `daStep` loop invariants are proven.
-/
noncomputable def deferredAcceptance (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W :=
  emptyMatching

/-- Certificate that DA terminates in a stable matching. -/
def DaProducesStableMatchingCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  IsStable val_m val_w (deferredAcceptance val_m val_w)

/-- Certificate that DA produces a men-optimal stable matching. -/
def DaIsMenOptimalCertificate (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ∀ mu', IsStable val_m val_w mu' →
    ∀ m, valM val_m m (mu'.m_match m) ≤ valM val_m m ((deferredAcceptance val_m val_w).m_match m)

end Matching
end EconCSLean