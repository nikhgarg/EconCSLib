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

/-- The `0`-homogeneity profile: equal target weight on every type. -/
noncomputable def uniformProfile (T : ℕ) : GammaHomogeneityProfile T where
  gamma := 0
  targetWeight := fun _ => 1

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

/--
Coordinate count error implies approximate homogeneity.

This is the finite bridge used by rounding arguments: once each integer count
is within `C` of `N * targetShare`, representation shares are within `C / N`.
-/
theorem approx_of_count_abs_error {T : ℕ}
    (G : GammaHomogeneityProfile T) (a : CountAllocation T) {N : ℕ} {C : ℝ}
    (hN : DecisionCore.Allocation.total a = N) (hNpos : 0 < N)
    (hclose : ∀ t, |(a.count t : ℝ) - (N : ℝ) * G.targetShare t| ≤ C) :
    G.Approx a (C / (N : ℝ)) := by
  intro t
  have htotal_ne : DecisionCore.Allocation.total a ≠ 0 := by
    rw [hN]
    exact Nat.ne_of_gt hNpos
  have hNreal_pos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hNreal_ne : (N : ℝ) ≠ 0 := ne_of_gt hNreal_pos
  have hrep :
      CountAllocation.representation a t = (a.count t : ℝ) / (N : ℝ) := by
    rw [CountAllocation.representation_eq_share]
    rw [DecisionCore.Allocation.share_eq_div_of_total_ne_zero
      (a := a) (k := t) htotal_ne]
    rw [hN]
  calc
    |CountAllocation.representation a t - G.targetShare t|
        = |(a.count t : ℝ) / (N : ℝ) - G.targetShare t| := by
          rw [hrep]
    _ = |((a.count t : ℝ) - (N : ℝ) * G.targetShare t) / (N : ℝ)| := by
          congr 1
          field_simp [hNreal_ne]
    _ = |(a.count t : ℝ) - (N : ℝ) * G.targetShare t| / (N : ℝ) := by
          rw [abs_div]
          rw [abs_of_pos hNreal_pos]
    _ ≤ C / (N : ℝ) :=
          div_le_div_of_nonneg_right (hclose t) hNreal_pos.le

end GammaHomogeneityProfile

@[simp] theorem uniformProfile_targetShare {T : ℕ} [NeZero T]
    (t : ItemType T) :
    (uniformProfile T).targetShare t = 1 / (T : ℝ) := by
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne T)
  have hnorm : (uniformProfile T).normalizer = (T : ℝ) := by
    unfold GammaHomogeneityProfile.normalizer uniformProfile
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have hnorm_ne : (uniformProfile T).normalizer ≠ 0 := by
    rw [hnorm]
    exact hTne
  rw [GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero
    (G := uniformProfile T) (t := t) hnorm_ne]
  rw [hnorm]
  simp [uniformProfile]
/--
If all type counts are pairwise bounded by `C`, then each count is within
`C` of the uniform real average `N / T`.
-/
theorem count_abs_sub_uniform_average_le_C_of_pairwise_bounded
    {T : ℕ} [NeZero T]
    (a : CountAllocation T) {N : ℕ} {C : ℝ}
    (hN : DecisionCore.Allocation.total a = N)
    (hbound : ∀ i j : ItemType T, (a.count i : ℝ) ≤ (a.count j : ℝ) + C)
    (t : ItemType T) :
    |(a.count t : ℝ) - (N : ℝ) / (T : ℝ)| ≤ C := by
  have hTposNat : 0 < T := Nat.pos_of_ne_zero (NeZero.ne T)
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hTposNat
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  have hsum_counts : (∑ j : ItemType T, (a.count j : ℝ)) = (N : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hN
  rw [abs_le]
  constructor
  · -- (a.count t) - N/T >= -C  => T * (a.count t) - N >= -T * C => T * (a.count t) + T * C >= N
    field_simp [hTne]
    have hsum : (∑ j : ItemType T, (a.count j : ℝ)) ≤ ∑ j : ItemType T, ((a.count t : ℝ) + C) := by
      apply Finset.sum_le_sum
      intro j _
      exact hbound j t
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul] at hsum
    linarith
  · -- (a.count t) - N/T <= C => T * (a.count t) - N <= T * C => T * (a.count t) <= N + T * C
    field_simp [hTne]
    have hsum : (∑ j : ItemType T, (a.count t : ℝ)) ≤ ∑ j : ItemType T, ((a.count j : ℝ) + C) := by
      apply Finset.sum_le_sum
      intro j _
      exact hbound t j
    rw [Finset.sum_add_distrib] at hsum
    simp [hsum_counts, Finset.sum_const, Fintype.card_fin, nsmul_eq_mul] at hsum
    linarith

/--
If all type counts differ pairwise by at most one, then each count is within
...
one of the uniform real average `N / T`.
-/
theorem count_abs_sub_uniform_average_le_one_of_pairwise_balanced
    {T : ℕ} [NeZero T]
    (a : CountAllocation T) {N : ℕ}
    (hN : DecisionCore.Allocation.total a = N)
    (hbal : ∀ i j : ItemType T, a.count i ≤ a.count j + 1)
    (t : ItemType T) :
    |(a.count t : ℝ) - (N : ℝ) / (T : ℝ)| ≤ 1 := by
  have hTposNat : 0 < T := Nat.pos_of_ne_zero (NeZero.ne T)
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hTposNat
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  have hsum_counts : (∑ j : ItemType T, (a.count j : ℝ)) = (N : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hN
  have hsum_add_one :
      (∑ j : ItemType T, ((a.count j : ℝ) + 1)) = (N : ℝ) + (T : ℝ) := by
    calc
      (∑ j : ItemType T, ((a.count j : ℝ) + 1))
          = (∑ j : ItemType T, (a.count j : ℝ)) +
              ∑ _j : ItemType T, (1 : ℝ) := by
              simpa using (Finset.sum_add_distrib
                (s := (Finset.univ : Finset (ItemType T)))
                (f := fun j : ItemType T => (a.count j : ℝ))
                (g := fun _j : ItemType T => (1 : ℝ)))
      _ = (N : ℝ) + (T : ℝ) := by
          simp [hsum_counts, Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have hsum_const_count :
      (∑ _j : ItemType T, (a.count t : ℝ)) =
        (T : ℝ) * (a.count t : ℝ) := by
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have hsum_const_count_add_one :
      (∑ _j : ItemType T, ((a.count t : ℝ) + 1)) =
        (T : ℝ) * (a.count t : ℝ) + (T : ℝ) := by
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have hupper_sum :
      ∑ j : ItemType T, (a.count t : ℝ) ≤
        ∑ j : ItemType T, ((a.count j : ℝ) + 1) := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact_mod_cast hbal t j
  have hupper : (T : ℝ) * (a.count t : ℝ) ≤ (N : ℝ) + (T : ℝ) := by
    rw [← hsum_const_count, ← hsum_add_one]
    exact hupper_sum
  have hlower_sum :
      ∑ j : ItemType T, (a.count j : ℝ) ≤
        ∑ j : ItemType T, ((a.count t : ℝ) + 1) := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact_mod_cast hbal j t
  have hlower : (N : ℝ) ≤ (T : ℝ) * (a.count t : ℝ) + (T : ℝ) := by
    rw [← hsum_counts, ← hsum_const_count_add_one]
    exact hlower_sum
  rw [abs_le]
  constructor
  · field_simp [hTne]
    nlinarith
  · field_simp [hTne]
    nlinarith

/--
Pairwise-balanced counts are approximately `0`-homogeneous, with finite
rounding error `1 / N`.
-/
theorem uniformProfile_approx_of_pairwise_balanced_counts
    {T : ℕ} [NeZero T]
    (a : CountAllocation T) {N : ℕ}
    (hN : DecisionCore.Allocation.total a = N) (hNpos : 0 < N)
    (hbal : ∀ i j : ItemType T, a.count i ≤ a.count j + 1) :
    (uniformProfile T).Approx a (1 / (N : ℝ)) := by
  refine GammaHomogeneityProfile.approx_of_count_abs_error
    (uniformProfile T) a hN hNpos ?_
  intro t
  rw [uniformProfile_targetShare]
  have hclose :=
    count_abs_sub_uniform_average_le_one_of_pairwise_balanced a hN hbal t
  simpa [div_eq_mul_inv] using hclose

end AccuracyDiversity
