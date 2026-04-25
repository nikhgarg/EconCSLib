import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

namespace EconCSLib
namespace Matching

/-- A matching between Men and Women. -/
structure Assignment (M W : Type*) where
  m_match : M → Option W
  w_match : W → Option M
  consistent_m : ∀ m w, m_match m = some w ↔ w_match w = some m

/-- The value of a match for a man. 0 if unmatched. -/
def valM {M W : Type*} (val : M → W → ℝ) (m : M) (w : Option W) : ℝ :=
  match w with
  | none => 0
  | some w' => val m w'

/-- The value of a match for a woman. 0 if unmatched. -/
def valW {M W : Type*} (val : W → M → ℝ) (w : W) (m : Option M) : ℝ :=
  match m with
  | none => 0
  | some m' => val w m'

/-- A matching is stable if it is individually rational and admits no blocking pairs. -/
def IsStable {M W : Type*} (val_m : M → W → ℝ) (val_w : W → M → ℝ) (mu : Assignment M W) : Prop :=
  (∀ m, 0 ≤ valM val_m m (mu.m_match m)) ∧
  (∀ w, 0 ≤ valW val_w w (mu.w_match w)) ∧
  (∀ m w, valM val_m m (mu.m_match m) < val_m m w →
          valW val_w w (mu.w_match w) < val_w w m → False)

end Matching
end EconCSLib