import AccuracyDiversity.Basic
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators
open DecisionCore

namespace AccuracyDiversity

namespace CountAllocation

/-- Representation of a type in a recommendation allocation. -/
noncomputable def representation {T : ℕ} (a : CountAllocation T) (t : ItemType T) : ℝ :=
  DecisionCore.Allocation.share a t

/-- Exact target representation profile. -/
def HasExactRepresentation {T : ℕ}
    (a : CountAllocation T) (target : ItemType T → ℝ) : Prop :=
  ∀ t, representation a t = target t

/-- Approximate target representation profile with uniform error `ε`. -/
def HasApproxRepresentation {T : ℕ}
    (a : CountAllocation T) (target : ItemType T → ℝ) (ε : ℝ) : Prop :=
  ∀ t, |representation a t - target t| ≤ ε

/-- Representation of every type is at least the supplied lower bound. -/
def HasRepresentationAtLeast {T : ℕ}
    (a : CountAllocation T) (lower : ItemType T → ℝ) : Prop :=
  ∀ t, lower t ≤ representation a t

@[simp] theorem representation_eq_share {T : ℕ}
    (a : CountAllocation T) (t : ItemType T) :
    representation a t = DecisionCore.Allocation.share a t := rfl

end CountAllocation

/-- A plain target representation profile. -/
structure HomogeneityProfile (T : ℕ) where
  targetShare : ItemType T → ℝ

namespace HomogeneityProfile

/-- Exact agreement with a target representation profile. -/
def Exact {T : ℕ} (P : HomogeneityProfile T) (a : CountAllocation T) : Prop :=
  CountAllocation.HasExactRepresentation a P.targetShare

/-- Approximate agreement with a target representation profile. -/
def Approx {T : ℕ} (P : HomogeneityProfile T) (a : CountAllocation T) (ε : ℝ) : Prop :=
  CountAllocation.HasApproxRepresentation a P.targetShare ε

end HomogeneityProfile

/--
A γ-homogeneity profile, represented by abstract target weights.

In the paper, the intended target weights are usually proportional to powers of type
likelihoods. We keep the weight function explicit here so the discrete finite layer does
not depend on real-power API details before the asymptotic branch is started.
-/
structure GammaHomogeneityProfile (T : ℕ) where
  gamma : ℝ
  targetWeight : ItemType T → ℝ

namespace GammaHomogeneityProfile

/-- Normalizer for the target weights. -/
noncomputable def normalizer {T : ℕ} (G : GammaHomogeneityProfile T) : ℝ :=
  ∑ t, G.targetWeight t

/-- Target share induced by the γ-profile weights, with zero fallback if the normalizer is zero. -/
noncomputable def targetShare {T : ℕ} (G : GammaHomogeneityProfile T) (t : ItemType T) : ℝ :=
  if h : G.normalizer = 0 then 0 else G.targetWeight t / G.normalizer

/-- Forget the γ-label and keep only the induced target-share profile. -/
noncomputable def toHomogeneityProfile {T : ℕ} (G : GammaHomogeneityProfile T) : HomogeneityProfile T where
  targetShare := G.targetShare

/-- Exact γ-homogeneity for a finite allocation. -/
noncomputable def Exact {T : ℕ} (G : GammaHomogeneityProfile T) (a : CountAllocation T) : Prop :=
  CountAllocation.HasExactRepresentation a G.targetShare

/-- Approximate γ-homogeneity for a finite allocation. -/
noncomputable def Approx {T : ℕ}
    (G : GammaHomogeneityProfile T) (a : CountAllocation T) (ε : ℝ) : Prop :=
  CountAllocation.HasApproxRepresentation a G.targetShare ε

@[simp] theorem targetShare_of_normalizer_zero {T : ℕ}
    (G : GammaHomogeneityProfile T) (t : ItemType T) (h : G.normalizer = 0) :
    G.targetShare t = 0 := by
  simp [targetShare, h]

theorem targetShare_eq_div_of_normalizer_ne_zero {T : ℕ}
    (G : GammaHomogeneityProfile T) (t : ItemType T) (h : G.normalizer ≠ 0) :
    G.targetShare t = G.targetWeight t / G.normalizer := by
  simp [targetShare, h]

end GammaHomogeneityProfile
end AccuracyDiversity

namespace AccuracyDiversity

namespace CountAllocation

/-- Representation shares are nonnegative. -/
theorem representation_nonneg {T : ℕ} (a : CountAllocation T) (t : ItemType T) :
    0 ≤ representation a t := by
  simpa [representation] using DecisionCore.Allocation.share_nonneg (a := a) (k := t)

/-- If the allocation has nonzero total, type representations sum to one. -/
theorem sum_representation_eq_one_of_total_ne_zero {T : ℕ}
    (a : CountAllocation T) (h : DecisionCore.Allocation.total a ≠ 0) :
    ∑ t, representation a t = 1 := by
  simpa [representation] using
    DecisionCore.Allocation.sum_share_eq_one_of_total_ne_zero (a := a) h

/-- Exact representation implies approximate representation for every nonnegative tolerance. -/
theorem exact_implies_approx {T : ℕ}
    (a : CountAllocation T) (target : ItemType T → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    HasExactRepresentation a target → HasApproxRepresentation a target ε := by
  intro hExact t
  rw [hExact t]
  simpa using hε

end CountAllocation

namespace HomogeneityProfile

/-- Exact homogeneity implies approximate homogeneity for every nonnegative tolerance. -/
theorem exact_implies_approx {T : ℕ}
    (P : HomogeneityProfile T) (a : CountAllocation T) {ε : ℝ}
    (hε : 0 ≤ ε) :
    P.Exact a → P.Approx a ε := by
  intro hExact
  exact CountAllocation.exact_implies_approx a P.targetShare hε hExact

end HomogeneityProfile

namespace GammaHomogeneityProfile

/--
If the γ-profile normalizer is nonzero, its induced target shares sum to one.
-/
theorem sum_targetShare_eq_one_of_normalizer_ne_zero {T : ℕ}
    (G : GammaHomogeneityProfile T) (h : G.normalizer ≠ 0) :
    ∑ t, G.targetShare t = 1 := by
  have hreal : G.normalizer ≠ 0 := h
  calc
    ∑ t, G.targetShare t = ∑ t, G.targetWeight t / G.normalizer := by
      refine Finset.sum_congr rfl ?_
      intro t _
      rw [targetShare_eq_div_of_normalizer_ne_zero (G := G) (t := t) h]
    _ = (∑ t, G.targetWeight t) / G.normalizer := by
      rw [Finset.sum_div]
    _ = G.normalizer / G.normalizer := by
      rfl
    _ = 1 := by
      field_simp [hreal]

/-- Exact γ-homogeneity implies approximate γ-homogeneity for every nonnegative tolerance. -/
theorem exact_implies_approx {T : ℕ}
    (G : GammaHomogeneityProfile T) (a : CountAllocation T) {ε : ℝ}
    (hε : 0 ≤ ε) :
    G.Exact a → G.Approx a ε := by
  intro hExact
  exact CountAllocation.exact_implies_approx a G.targetShare hε hExact

end GammaHomogeneityProfile
end AccuracyDiversity
