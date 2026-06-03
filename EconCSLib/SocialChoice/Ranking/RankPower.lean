import EconCSLib.Foundations.Math.FiniteSigns
import EconCSLib.SocialChoice.Ranking.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# Rank-Power Algebra

Paper-neutral finite geometric sums over ranking positions.  These lemmas are
useful for Mallows-style rank-factorization arguments and for sequential
selection proofs that remove one rank and renormalize the remaining positions.
-/

open scoped BigOperators

namespace EconCSLib
namespace SocialChoice
namespace Ranking

noncomputable section

/-- The geometric rank-power sum over the candidate positions. -/
def candidateRankPowerSum (n : ℕ) (q : ℝ) : ℝ :=
  ∑ i : Candidate n, q ^ (i : ℕ)

/-- The same geometric rank-power sum, indexed from the worst rank downward. -/
def candidateRankReversePowerSum (n : ℕ) (q : ℝ) : ℝ :=
  ∑ i : Candidate n, q ^ (n + 1 - (i : ℕ))

/-- The geometric rank-power sum over the prefix of ranks up to `k`. -/
def candidateRankPrefixPowerSum
    (n : ℕ) (q : ℝ) (k : Fin (n + 1)) : ℝ :=
  ∑ i : Candidate n, if (i : ℕ) ≤ k.val then q ^ (i : ℕ) else 0

/--
Rank-power sum over all candidates except the removed rank, with lower ranks
unchanged and higher ranks shifted down by one.
-/
def candidateRankRemovalPowerSum
    (n : ℕ) (q : ℝ) (k : Candidate n) : ℝ :=
  ∑ r : Candidate n,
    if r < k then q ^ (r : ℕ)
    else if k < r then q ^ ((r : ℕ) - 1)
    else 0

/-- Rank-only numerator weight for the best remaining candidate after center
rank `k` has been removed. -/
def candidateRankBestAfterRemovalWeight
    (n : ℕ) (q : ℝ) (k r : Candidate n) : ℝ :=
  if r < k then
    q ^ (r : ℕ) * candidateRankRemovalPowerSum n q k + q ^ ((r : ℕ) + (k : ℕ))
  else if k < r then
    q ^ (r : ℕ) * candidateRankRemovalPowerSum n q k +
      q ^ ((k : ℕ) + (r : ℕ) - 1)
  else
    0

theorem candidateRankRemovalPowerSum_pos
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (k : Candidate n) :
    0 < candidateRankRemovalPowerSum n q k := by
  classical
  unfold candidateRankRemovalPowerSum
  by_cases hk0 : k = (0 : Candidate n)
  · apply EconCSLib.sum_univ_pos_of_pos_of_nonneg (a₀ := (1 : Candidate n))
    · have hk_lt_one : k < (1 : Candidate n) := by
        rw [hk0]
        change (0 : ℕ) < 1
        omega
      have hnot : ¬(1 : Candidate n) < k := not_lt_of_gt hk_lt_one
      simp [hnot, hk_lt_one]
    · intro r
      by_cases hrk : r < k
      · simp [hrk, pow_nonneg (le_of_lt hq_pos) (r : ℕ)]
      · by_cases hkr : k < r
        · simp [hrk, hkr, pow_nonneg (le_of_lt hq_pos) ((r : ℕ) - 1)]
        · simp [hrk, hkr]
  · apply EconCSLib.sum_univ_pos_of_pos_of_nonneg (a₀ := (0 : Candidate n))
    · have hzero_lt : (0 : Candidate n) < k := by
        change 0 < (k : ℕ)
        by_contra hnot
        have hkval : (k : ℕ) = 0 := by omega
        exact hk0 (Fin.ext hkval)
      simp [hzero_lt]
    · intro r
      by_cases hrk : r < k
      · simp [hrk, pow_nonneg (le_of_lt hq_pos) (r : ℕ)]
      · by_cases hkr : k < r
        · simp [hrk, hkr, pow_nonneg (le_of_lt hq_pos) ((r : ℕ) - 1)]
        · simp [hrk, hkr]

theorem candidateRankRemovalPowerSum_nonneg
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (k : Candidate n) :
    0 ≤ candidateRankRemovalPowerSum n q k :=
  le_of_lt (candidateRankRemovalPowerSum_pos n hq_pos k)

theorem candidateRankBestAfterRemovalWeight_nonneg
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (k r : Candidate n) :
    0 ≤ candidateRankBestAfterRemovalWeight n q k r := by
  unfold candidateRankBestAfterRemovalWeight
  by_cases hrk : r < k
  · rw [if_pos hrk]
    exact add_nonneg
      (mul_nonneg (pow_nonneg (le_of_lt hq_pos) (r : ℕ))
        (candidateRankRemovalPowerSum_nonneg n hq_pos k))
      (pow_nonneg (le_of_lt hq_pos) ((r : ℕ) + (k : ℕ)))
  · rw [if_neg hrk]
    by_cases hkr : k < r
    · rw [if_pos hkr]
      exact add_nonneg
        (mul_nonneg (pow_nonneg (le_of_lt hq_pos) (r : ℕ))
          (candidateRankRemovalPowerSum_nonneg n hq_pos k))
        (pow_nonneg (le_of_lt hq_pos) ((k : ℕ) + (r : ℕ) - 1))
    · rw [if_neg hkr]

theorem candidateRankRemovalPowerSum_eq_range
    (n : ℕ) (q : ℝ) (k : Candidate n) :
    candidateRankRemovalPowerSum n q k =
      ∑ m ∈ Finset.range (n + 1), q ^ m := by
  classical
  unfold candidateRankRemovalPowerSum Candidate
  change
    (∑ x : Fin (n + 2),
      if x.val < k.val then q ^ x.val
      else if k.val < x.val then q ^ (x.val - 1)
      else 0) =
      ∑ m ∈ Finset.range (n + 1), q ^ m
  rw [Fin.sum_univ_eq_sum_range
    (fun x : ℕ =>
      if x < k.val then q ^ x
      else if k.val < x then q ^ (x - 1)
      else 0)
    (n + 2)]
  let a : ℕ := k.val
  have ha_le : a ≤ n + 1 := by
    have ha_lt : a < n + 2 := by
      simp [a]
    omega
  have hfilter_lt :
      (Finset.range (n + 2)).filter (fun i : ℕ => i < a) =
        Finset.range a := by
    ext i
    simp [a]
    omega
  have hfilter_gt :
      (Finset.range (n + 2)).filter (fun i : ℕ => a < i) =
        Finset.Ico (a + 1) (n + 2) := by
    ext i
    simp [Finset.mem_Ico]
    omega
  have hsplit :
      (∑ i ∈ Finset.range (n + 2),
        if i < a then q ^ i else if a < i then q ^ (i - 1) else 0) =
        (∑ i ∈ (Finset.range (n + 2)).filter (fun i : ℕ => i < a),
          q ^ i) +
          (∑ i ∈ (Finset.range (n + 2)).filter (fun i : ℕ => a < i),
            q ^ (i - 1)) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases hia : i < a
    · have hai_not : ¬a < i := not_lt_of_gt hia
      simp [hia, hai_not]
    · by_cases hai : a < i
      · simp [hia, hai]
      · simp [hia, hai]
  have hshift :
      (∑ i ∈ Finset.Ico (a + 1) (n + 2), q ^ (i - 1)) =
        ∑ i ∈ Finset.Ico a (n + 1), q ^ i := by
    have h :=
      (Finset.sum_Ico_add'
        (fun x : ℕ => q ^ (x - 1)) a (n + 1) 1).symm
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  calc
    (∑ i ∈ Finset.range (n + 2),
        if i < ↑k then q ^ i else if ↑k < i then q ^ (i - 1) else 0)
        =
        (∑ i ∈ Finset.range (n + 2),
          if i < a then q ^ i else if a < i then q ^ (i - 1) else 0) := by
          simp [a]
    _ = (∑ i ∈ Finset.range a, q ^ i) +
          (∑ i ∈ Finset.Ico (a + 1) (n + 2), q ^ (i - 1)) := by
          rw [hsplit, hfilter_lt, hfilter_gt]
    _ = (∑ i ∈ Finset.range a, q ^ i) +
          (∑ i ∈ Finset.Ico a (n + 1), q ^ i) := by
          rw [hshift]
    _ = ∑ m ∈ Finset.range (n + 1), q ^ m := by
          exact Finset.sum_range_add_sum_Ico (fun m : ℕ => q ^ m) ha_le

theorem candidateRankRemovalPowerSum_mul_one_sub
    (n : ℕ) (q : ℝ) (k : Candidate n) :
    candidateRankRemovalPowerSum n q k * (1 - q) = 1 - q ^ (n + 1) := by
  rw [candidateRankRemovalPowerSum_eq_range]
  exact geom_sum_mul_neg q (n + 1)

@[simp] theorem candidateRankBestAfterRemovalWeight_self
    (n : ℕ) (q : ℝ) (k : Candidate n) :
    candidateRankBestAfterRemovalWeight n q k k = 0 := by
  unfold candidateRankBestAfterRemovalWeight
  simp

theorem candidateRankBestAfterRemovalWeight_of_lt
    (n : ℕ) (q : ℝ) {k r : Candidate n} (hrk : r < k) :
    candidateRankBestAfterRemovalWeight n q k r =
      q ^ (r : ℕ) *
        (candidateRankRemovalPowerSum n q k + q ^ (k : ℕ)) := by
  unfold candidateRankBestAfterRemovalWeight
  rw [if_pos hrk]
  rw [pow_add]
  ring

theorem candidateRankBestAfterRemovalWeight_of_gt
    (n : ℕ) (q : ℝ) {k r : Candidate n} (hkr : k < r) :
    candidateRankBestAfterRemovalWeight n q k r =
      q ^ ((r : ℕ) - 1) *
        (q * candidateRankRemovalPowerSum n q k + q ^ (k : ℕ)) := by
  unfold candidateRankBestAfterRemovalWeight
  rw [if_neg (not_lt_of_gt hkr), if_pos hkr]
  have hr_pos : 0 < (r : ℕ) :=
    lt_of_le_of_lt (Nat.zero_le (k : ℕ)) hkr
  have hpow_r : q ^ (r : ℕ) = q ^ ((r : ℕ) - 1) * q := by
    calc
      q ^ (r : ℕ) = q ^ (((r : ℕ) - 1) + 1) := by
        congr 1
        omega
      _ = q ^ ((r : ℕ) - 1) * q := by rw [pow_add, pow_one]
  have hpow_kr :
      q ^ ((k : ℕ) + (r : ℕ) - 1) =
        q ^ (((r : ℕ) - 1) + (k : ℕ)) := by
    congr 1
    omega
  rw [hpow_r, hpow_kr, pow_add]
  ring

theorem candidateRankPowerSum_pos (n : ℕ) {q : ℝ} (hq_pos : 0 < q) :
    0 < candidateRankPowerSum n q := by
  classical
  unfold candidateRankPowerSum
  apply EconCSLib.sum_univ_pos_of_pos_of_nonneg (a₀ := (0 : Candidate n))
  · simp
  · intro i
    exact pow_nonneg (le_of_lt hq_pos) (i : ℕ)

theorem candidateRankReversePowerSum_pos (n : ℕ) {q : ℝ} (hq_pos : 0 < q) :
    0 < candidateRankReversePowerSum n q := by
  classical
  unfold candidateRankReversePowerSum
  apply EconCSLib.sum_univ_pos_of_pos_of_nonneg
    (a₀ := (⟨n + 1, by omega⟩ : Candidate n))
  · simp
  · intro i
    exact pow_nonneg (le_of_lt hq_pos) _

theorem candidateRankPowerSum_strict_mono
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_nonneg : 0 ≤ q₁) (hq_lt : q₁ < q₂) :
    candidateRankPowerSum n q₁ < candidateRankPowerSum n q₂ := by
  classical
  unfold candidateRankPowerSum
  refine Finset.sum_lt_sum ?hle ?hstrict
  · intro i _
    exact pow_le_pow_left₀ hq₁_nonneg (le_of_lt hq_lt) (i : ℕ)
  · refine ⟨(1 : Candidate n), Finset.mem_univ _, ?_⟩
    simpa using hq_lt

theorem natPower_mul_lt_mul_natPower
    {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {i j : ℕ} (hij : i < j) :
    q₁ ^ j * q₂ ^ i < q₁ ^ i * q₂ ^ j := by
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  obtain ⟨d, hd_pos, hd_eq⟩ :
      ∃ d : ℕ, 0 < d ∧ j = i + d := by
    refine ⟨j - i, Nat.sub_pos_of_lt hij, ?_⟩
    exact (Nat.add_sub_of_le (le_of_lt hij)).symm
  have hpow : q₁ ^ d < q₂ ^ d := by
    exact pow_lt_pow_left₀ hq_lt (le_of_lt hq₁_pos) (Nat.ne_of_gt hd_pos)
  have hscale : 0 < q₁ ^ i * q₂ ^ i :=
    mul_pos (pow_pos hq₁_pos i) (pow_pos hq₂_pos i)
  have hmul := mul_lt_mul_of_pos_left hpow hscale
  rw [hd_eq, pow_add, pow_add]
  nlinarith

theorem candidateRankPowerSum_mul_one_sub (n : ℕ) (q : ℝ) :
    candidateRankPowerSum n q * (1 - q) = 1 - q ^ (n + 2) := by
  simpa [candidateRankPowerSum, Candidate, Fin.sum_univ_eq_sum_range] using
    (geom_sum_mul_neg q (n + 2))

theorem candidateRankPowerSum_inner_nonneg
    {n : ℕ} {q : ℝ} (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    {r s : Candidate n} (hrs : r < s) :
    0 ≤ (candidateRankPowerSum n q - q ^ (r : ℕ)) -
      q * (candidateRankPowerSum n q - q ^ (s : ℕ)) := by
  have hgeom := candidateRankPowerSum_mul_one_sub n q
  have hs_succ_le : s.val + 1 ≤ n + 2 := s.2
  have hpow_succ_le : q ^ (n + 2) ≤ q ^ (s.val + 1) :=
    pow_le_pow_of_le_one hq_nonneg hq_le_one hs_succ_le
  have hpow_r_le_one : q ^ (r : ℕ) ≤ 1 :=
    pow_le_one₀ hq_nonneg hq_le_one
  have hmain : 0 ≤ (1 - q ^ (r : ℕ)) + (q ^ (s.val + 1) - q ^ (n + 2)) := by
    exact add_nonneg (sub_nonneg.mpr hpow_r_le_one) (sub_nonneg.mpr hpow_succ_le)
  have hpow_succ : q * q ^ (s : ℕ) = q ^ (s.val + 1) := by
    rw [pow_succ']
  nlinarith

theorem candidateRankPowerSum_inner_pos_zero_one
    {n : ℕ} (hn : 0 < n) {q : ℝ} (hq_pos : 0 < q) (hq_lt_one : q < 1) :
    0 < (candidateRankPowerSum n q - q ^ (0 : ℕ)) -
      q * (candidateRankPowerSum n q - q ^ (1 : ℕ)) := by
  have hgeom := candidateRankPowerSum_mul_one_sub n q
  have hpow_lt : q ^ (n + 2) < q ^ (2 : ℕ) := by
    exact pow_lt_pow_right_of_lt_one₀ hq_pos hq_lt_one (by omega)
  nlinarith [hgeom, hpow_lt]

end

end Ranking
end SocialChoice
end EconCSLib
