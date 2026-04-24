import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Card

open scoped BigOperators

namespace EconCSLean
namespace FiniteRounding

/--
No coordinate can be simultaneously too high above an integer anchor while
another coordinate is too low below its anchor.

This is the discrete crossing condition used in rounding arguments for
separable finite optimization problems.
-/
def NoRoundingCrossing {κ : Type*} (a b : κ → ℕ) : Prop :=
  ∀ high low, ¬ (b high + 1 ≤ a high ∧ a low + 1 ≤ b low)

namespace NoRoundingCrossing

theorem exists_low_of_high
    {κ : Type*} [Fintype κ]
    (a b : κ → ℕ) {N B C : ℕ} (high : κ)
    (ha : (∑ i : κ, a i) = N)
    (hb : (∑ i : κ, b i) = B)
    (hNlt : N < B + C)
    (hhigh : b high + C ≤ a high) :
    ∃ low, a low < b low := by
  classical
  by_contra hnone
  have hall : ∀ i, b i ≤ a i := by
    intro i
    exact le_of_not_gt (by
      intro hlt
      exact hnone ⟨i, hlt⟩)
  let raised : κ → ℕ := fun i => if i = high then b high + C else b i
  have hraised_le : ∀ i, raised i ≤ a i := by
    intro i
    by_cases hi : i = high
    · subst hi
      simp [raised, hhigh]
    · simp [raised, hi, hall i]
  have hsum_raised_le : (∑ i : κ, raised i) ≤ ∑ i : κ, a i :=
    Finset.sum_le_sum (by
      intro i _hi
      exact hraised_le i)
  have hsum_raised : (∑ i : κ, raised i) = B + C := by
    have hpoint :
        (fun i : κ => raised i) =
          fun i : κ => b i + if i = high then C else 0 := by
      funext i
      by_cases hi : i = high
      · subst hi
        simp [raised]
      · simp [raised, hi]
    calc
      (∑ i : κ, raised i)
          = ∑ i : κ, (b i + if i = high then C else 0) := by
              rw [hpoint]
      _ = (∑ i : κ, b i) +
            ∑ i : κ, (if i = high then C else 0) := by
              rw [Finset.sum_add_distrib]
      _ = B + C := by
              rw [hb]
              congr 1
              exact Fintype.sum_ite_eq' high (fun _i : κ => C)
  have hB_add_C_le_N : B + C ≤ N := by
    rw [← ha, ← hsum_raised]
    exact hsum_raised_le
  exact (not_lt_of_ge hB_add_C_le_N) hNlt

theorem exists_high_of_low
    {κ : Type*} [Fintype κ]
    (a b : κ → ℕ) {N B C : ℕ} (low : κ)
    (ha : (∑ i : κ, a i) = N)
    (hb : (∑ i : κ, b i) = B)
    (hBle : B ≤ N) (hCpos : 0 < C)
    (hlow : a low + C ≤ b low) :
    ∃ high, b high < a high := by
  classical
  by_contra hnone
  have hall : ∀ i, a i ≤ b i := by
    intro i
    exact le_of_not_gt (by
      intro hlt
      exact hnone ⟨i, hlt⟩)
  let raised : κ → ℕ := fun i => if i = low then a low + C else a i
  have hraised_le : ∀ i, raised i ≤ b i := by
    intro i
    by_cases hi : i = low
    · subst hi
      simp [raised, hlow]
    · simp [raised, hi, hall i]
  have hsum_raised_le : (∑ i : κ, raised i) ≤ ∑ i : κ, b i :=
    Finset.sum_le_sum (by
      intro i _hi
      exact hraised_le i)
  have hsum_raised : (∑ i : κ, raised i) = N + C := by
    have hpoint :
        (fun i : κ => raised i) =
          fun i : κ => a i + if i = low then C else 0 := by
      funext i
      by_cases hi : i = low
      · subst hi
        simp [raised]
      · simp [raised, hi]
    calc
      (∑ i : κ, raised i)
          = ∑ i : κ, (a i + if i = low then C else 0) := by
              rw [hpoint]
      _ = (∑ i : κ, a i) +
            ∑ i : κ, (if i = low then C else 0) := by
              rw [Finset.sum_add_distrib]
      _ = N + C := by
              rw [ha]
              congr 1
              exact Fintype.sum_ite_eq' low (fun _i : κ => C)
  have hN_add_C_le_N : N + C ≤ N := by
    calc
      N + C = ∑ i : κ, raised i := hsum_raised.symm
      _ ≤ ∑ i : κ, b i := hsum_raised_le
      _ = B := hb
      _ ≤ N := hBle
  exact (not_lt_of_ge hN_add_C_le_N) (Nat.lt_add_of_pos_right hCpos)

/--
If the integer allocation has no high/low crossing around anchors `b`, then no
coordinate is above its anchor by as much as the number of coordinates.
-/
theorem count_lt_anchor_add_card
    {κ : Type*} [Fintype κ]
    (a b : κ → ℕ) {N B : ℕ} (t : κ)
    (ha : (∑ i : κ, a i) = N)
    (hb : (∑ i : κ, b i) = B)
    (hNlt : N < B + Fintype.card κ)
    (hno : NoRoundingCrossing a b) :
    a t < b t + Fintype.card κ := by
  by_contra hnot
  have hhigh : b t + Fintype.card κ ≤ a t := le_of_not_gt hnot
  obtain ⟨low, hlow_lt⟩ :=
    exists_low_of_high a b t ha hb hNlt hhigh
  have hcard_pos : 0 < Fintype.card κ :=
    Fintype.card_pos_iff.mpr ⟨t⟩
  have hhigh_one : b t + 1 ≤ a t :=
    le_trans
      (Nat.add_le_add_left (Nat.succ_le_of_lt hcard_pos) (b t))
      hhigh
  have hlow_one : a low + 1 ≤ b low :=
    Nat.succ_le_of_lt hlow_lt
  exact hno t low ⟨hhigh_one, hlow_one⟩

/--
If the integer allocation has no high/low crossing around anchors `b`, then no
coordinate is below its anchor by as much as the number of coordinates.
-/
theorem anchor_lt_count_add_card
    {κ : Type*} [Fintype κ]
    (a b : κ → ℕ) {N B : ℕ} (t : κ)
    (ha : (∑ i : κ, a i) = N)
    (hb : (∑ i : κ, b i) = B)
    (hBle : B ≤ N)
    (hno : NoRoundingCrossing a b) :
    b t < a t + Fintype.card κ := by
  by_contra hnot
  have hlow : a t + Fintype.card κ ≤ b t := le_of_not_gt hnot
  have hcard_pos : 0 < Fintype.card κ :=
    Fintype.card_pos_iff.mpr ⟨t⟩
  obtain ⟨high, hhigh_lt⟩ :=
    exists_high_of_low a b t ha hb hBle hcard_pos hlow
  have hhigh_one : b high + 1 ≤ a high :=
    Nat.succ_le_of_lt hhigh_lt
  have hlow_one : a t + 1 ≤ b t :=
    le_trans
      (Nat.add_le_add_left (Nat.succ_le_of_lt hcard_pos) (a t))
      hlow
  exact hno high t ⟨hhigh_one, hlow_one⟩

end NoRoundingCrossing

end FiniteRounding
end EconCSLean
