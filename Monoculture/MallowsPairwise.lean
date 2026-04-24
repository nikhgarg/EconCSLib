import Monoculture.MallowsFiniteLemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Fin.Basic

open scoped BigOperators
open DecisionCore

namespace Monoculture

/-- The geometric rank-power sum over the candidate positions. -/
noncomputable def candidateRankPowerSum (n : ℕ) (q : ℝ) : ℝ :=
  ∑ i : Candidate n, q ^ (i : ℕ)

/-- The geometric rank-power sum over the prefix of ranks up to `k`. -/
noncomputable def candidateRankPrefixPowerSum
    (n : ℕ) (q : ℝ) (k : Fin (n + 1)) : ℝ :=
  ∑ i : Candidate n, if (i : ℕ) ≤ k.val then q ^ (i : ℕ) else 0

noncomputable def candidateRankCrossDelta
    (n : ℕ) (qA qH : ℝ) (r : Candidate n) : ℝ :=
  qA ^ (r : ℕ) * candidateRankPowerSum n qH -
    qH ^ (r : ℕ) * candidateRankPowerSum n qA

noncomputable def candidateRankAdjacentCoeff
    (n : ℕ) (qA qH : ℝ) (k : ℕ) : ℝ :=
  ∑ r : Candidate n, ∑ s : Candidate n,
    if (r : ℕ) ≤ k ∧ k < (s : ℕ) then
      qH ^ ((r : ℕ) + (s : ℕ) - 1) *
        (candidateRankCrossDelta n qA qH r -
          qH * candidateRankCrossDelta n qA qH s)
    else
      0

noncomputable def candidateRankWeightedPrefixCrossDeltaSum
    (n : ℕ) (qA qH : ℝ) (k : ℕ) : ℝ :=
  ∑ r : Candidate n,
    if (r : ℕ) ≤ k then
      qH ^ (r : ℕ) * candidateRankCrossDelta n qA qH r
    else
      0

noncomputable def candidateRankWeightedSuffixCrossDeltaSum
    (n : ℕ) (qA qH : ℝ) (k : ℕ) : ℝ :=
  ∑ s : Candidate n,
    if k < (s : ℕ) then
      qH ^ (s : ℕ) * candidateRankCrossDelta n qA qH s
    else
      0

noncomputable def candidateRankPrefixWeightSum
    (n : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  ∑ r : Candidate n, if (r : ℕ) ≤ k then q ^ (r : ℕ) else 0

noncomputable def candidateRankShiftedSuffixWeightSum
    (n : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  ∑ s : Candidate n, if k < (s : ℕ) then q ^ ((s : ℕ) - 1) else 0

/--
Rank-only conditional top-gap summand.

For a first candidate at center rank `r`, this is the contribution of a possible
second candidate at center rank `s` after dividing out the common first-rank
Mallows factor.  It is the Lean version of the paper's conditional
`x_i - V_{-i}` gap.
-/
noncomputable def candidateRankConditionalGapTerm
    (q : ℝ) (value : Candidate n → ℝ) (r s : Candidate n) : ℝ :=
  if r < s then
    q ^ ((s : ℕ) - 1) * (value r - value s)
  else if s < r then
    q ^ (s : ℕ) * (value r - value s)
  else
    0

/-- Rank-only conditional first-minus-second gap for a fixed first rank. -/
noncomputable def candidateRankConditionalGap
    (n : ℕ) (q : ℝ) (value : Candidate n → ℝ) (r : Candidate n) : ℝ :=
  ∑ s : Candidate n, candidateRankConditionalGapTerm q value r s

theorem candidateRankPowerSum_pos (n : ℕ) {q : ℝ} (hq_pos : 0 < q) :
    0 < candidateRankPowerSum n q := by
  classical
  unfold candidateRankPowerSum
  apply DecisionCore.sum_univ_pos_of_pos_of_nonneg (a₀ := (0 : Candidate n))
  · simp
  · intro i
    exact pow_nonneg (le_of_lt hq_pos) (i : ℕ)

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

theorem rankPower_mul_lt_mul_rankPower
    {n : ℕ} {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {i j : Candidate n} (hij : i < j) :
    q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) <
      q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) := by
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  obtain ⟨d, hd_pos, hd_eq⟩ :
      ∃ d : ℕ, 0 < d ∧ (j : ℕ) = (i : ℕ) + d := by
    refine ⟨(j : ℕ) - (i : ℕ), Nat.sub_pos_of_lt hij, ?_⟩
    exact (Nat.add_sub_of_le (le_of_lt hij)).symm
  have hpow : q₁ ^ d < q₂ ^ d := by
    exact pow_lt_pow_left₀ hq_lt (le_of_lt hq₁_pos) (Nat.ne_of_gt hd_pos)
  have hscale : 0 < q₁ ^ (i : ℕ) * q₂ ^ (i : ℕ) :=
    mul_pos (pow_pos hq₁_pos (i : ℕ)) (pow_pos hq₂_pos (i : ℕ))
  have hmul := mul_lt_mul_of_pos_left hpow hscale
  rw [hd_eq, pow_add, pow_add]
  nlinarith

theorem weightedRankPower_pair_add_pos
    {n : ℕ} {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁)
    (hq_lt : q₁ < q₂) (hq₂_lt_one : q₂ < 1)
    {i j : Candidate n} (hij : i < j) :
    0 <
      q₂ ^ (i : ℕ) *
          (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
            q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ)) +
        q₂ ^ (j : ℕ) *
          (q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) -
            q₂ ^ (j : ℕ) * q₁ ^ (i : ℕ)) := by
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  obtain ⟨d, hd_pos, hd_eq⟩ :
      ∃ d : ℕ, 0 < d ∧ (j : ℕ) = (i : ℕ) + d := by
    refine ⟨(j : ℕ) - (i : ℕ), Nat.sub_pos_of_lt hij, ?_⟩
    exact (Nat.add_sub_of_le (le_of_lt hij)).symm
  have hpow_lt : q₁ ^ d < q₂ ^ d :=
    pow_lt_pow_left₀ hq_lt (le_of_lt hq₁_pos) (Nat.ne_of_gt hd_pos)
  have hpow_one : q₂ ^ d < 1 :=
    pow_lt_one₀ (le_of_lt hq₂_pos) hq₂_lt_one (Nat.ne_of_gt hd_pos)
  have hfactor :
      q₂ ^ (i : ℕ) *
          (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
            q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ)) +
        q₂ ^ (j : ℕ) *
          (q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) -
            q₂ ^ (j : ℕ) * q₁ ^ (i : ℕ)) =
        q₁ ^ (i : ℕ) * q₂ ^ (i : ℕ) * q₂ ^ (i : ℕ) *
          ((q₂ ^ d - q₁ ^ d) * (1 - q₂ ^ d)) := by
    rw [hd_eq, pow_add, pow_add]
    ring
  rw [hfactor]
  exact mul_pos
    (mul_pos (mul_pos (pow_pos hq₁_pos (i : ℕ))
      (pow_pos hq₂_pos (i : ℕ))) (pow_pos hq₂_pos (i : ℕ)))
    (mul_pos (sub_pos.mpr hpow_lt) (sub_pos.mpr hpow_one))

theorem weightedRankPower_pair_add_nonneg
    {n : ℕ} {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁)
    (hq_lt : q₁ < q₂) (hq₂_lt_one : q₂ < 1)
    {i j : Candidate n} (hij : i < j) :
    0 ≤
      q₂ ^ (i : ℕ) *
          (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
            q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ)) +
        q₂ ^ (j : ℕ) *
          (q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) -
            q₂ ^ (j : ℕ) * q₁ ^ (i : ℕ)) :=
  le_of_lt (weightedRankPower_pair_add_pos hq₁_pos hq_lt hq₂_lt_one hij)

/-- Adjacent value gap between center positions `k` and `k+1`. -/
noncomputable def centerAdjacentGapAt {n : ℕ}
    (ρ : Ranking n) (value : Candidate n → ℝ) (k : ℕ) : ℝ :=
  if hk : k + 1 < n + 2 then
    value (ρ ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩) -
      value (ρ ⟨k + 1, hk⟩)
  else
    0

theorem centerAdjacentGapAt_pos_of_strictlyOrderedBy
    {n : ℕ} {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy ρ value) {k : ℕ} (hk : k + 1 < n + 2) :
    0 < centerAdjacentGapAt ρ value k := by
  unfold centerAdjacentGapAt
  simp [hk]
  exact hvalue
    (show rankOf ρ (ρ ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩) <
        rankOf ρ (ρ ⟨k + 1, hk⟩) by
      simp [rankOf])

theorem value_sub_eq_sum_centerAdjacentGapAt
    {n : ℕ} (ρ : Ranking n) (value : Candidate n → ℝ)
    {c d : Candidate n} (hlt : rankOf ρ c < rankOf ρ d) :
    value c - value d =
      ∑ k ∈ Finset.Ico (rankOf ρ c).val (rankOf ρ d).val,
        centerAdjacentGapAt ρ value k := by
  classical
  let f : ℕ → ℝ := fun k =>
    if hk : k < n + 2 then value (ρ ⟨k, hk⟩) else 0
  have hle : (rankOf ρ c).val ≤ (rankOf ρ d).val := le_of_lt hlt
  have htel :
      (∑ k ∈ Finset.Ico (rankOf ρ c).val (rankOf ρ d).val,
        (f k - f (k + 1))) =
        f (rankOf ρ c).val - f (rankOf ρ d).val := by
    let a := (rankOf ρ c).val
    let b := (rankOf ρ d).val
    have hle' : a ≤ b := hle
    have hshift :
        (∑ k ∈ Finset.Ico a b, f (k + 1)) =
          ∑ k ∈ Finset.Ico (a + 1) (b + 1), f k := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Finset.sum_Ico_add' f a b 1)
    have hb :
        (∑ k ∈ Finset.range (b + 1), f k) -
            (∑ k ∈ Finset.range b, f k) = f b :=
      Finset.sum_range_succ_sub_sum f
    have ha :
        (∑ k ∈ Finset.range (a + 1), f k) -
            (∑ k ∈ Finset.range a, f k) = f a :=
      Finset.sum_range_succ_sub_sum f
    calc
      (∑ k ∈ Finset.Ico (rankOf ρ c).val (rankOf ρ d).val,
        (f k - f (k + 1)))
          = (∑ k ∈ Finset.Ico a b, f k) -
              (∑ k ∈ Finset.Ico a b, f (k + 1)) := by
                simp [a, b, Finset.sum_sub_distrib]
      _ = (∑ k ∈ Finset.range b, f k) - (∑ k ∈ Finset.range a, f k) -
              ((∑ k ∈ Finset.range (b + 1), f k) -
                (∑ k ∈ Finset.range (a + 1), f k)) := by
                rw [Finset.sum_Ico_eq_sub f hle', hshift,
                  Finset.sum_Ico_eq_sub f (Nat.succ_le_succ hle')]
      _ = f a - f b := by
                linarith
      _ = f (rankOf ρ c).val - f (rankOf ρ d).val := by
                simp [a, b]
  have hsum :
      (∑ k ∈ Finset.Ico (rankOf ρ c).val (rankOf ρ d).val,
        centerAdjacentGapAt ρ value k) =
      (∑ k ∈ Finset.Ico (rankOf ρ c).val (rankOf ρ d).val,
        (f k - f (k + 1))) := by
    refine Finset.sum_congr rfl ?_
    intro k hk_mem
    have hk_lt_s : k < (rankOf ρ d).val := (Finset.mem_Ico.mp hk_mem).2
    have hk1 : k + 1 < n + 2 := by
      omega
    have hk0 : k < n + 2 := Nat.lt_trans (Nat.lt_succ_self k) hk1
    simp [centerAdjacentGapAt, f, hk1, hk0]
  rw [hsum, htel]
  simp [f, rankOf]

theorem candidateRankConditionalGap_succ_lt
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) {value : Candidate n → ℝ}
    (hvalue : ∀ i j : Candidate n, i < j → value j < value i)
    (k : Fin (n + 1)) :
    candidateRankConditionalGap n q value k.succ <
      candidateRankConditionalGap n q value (Fin.castSucc k) := by
  classical
  let r0 : Candidate n := Fin.castSucc k
  let r1 : Candidate n := k.succ
  have hr01 : r0 < r1 := by
    change k.val < k.val + 1
    omega
  have hgap : 0 < value r0 - value r1 := sub_pos.mpr (hvalue r0 r1 hr01)
  rw [← sub_pos]
  unfold candidateRankConditionalGap
  rw [← Finset.sum_sub_distrib]
  apply DecisionCore.sum_univ_pos_of_pos_of_nonneg (a₀ := r0)
  · have hr1_not_lt_r0 : ¬r1 < r0 := not_lt_of_gt hr01
    have hneg : q ^ (r0 : ℕ) * (value r1 - value r0) < 0 := by
      nlinarith [mul_pos (pow_pos hq_pos (r0 : ℕ)) hgap]
    simpa [candidateRankConditionalGapTerm, r0, r1, hr01, hr1_not_lt_r0] using hneg
  · intro s
    have hcases : s < r0 ∨ s = r0 ∨ s = r1 ∨ r1 < s := by
      by_cases hs_lt : (s : ℕ) < k.val
      · exact Or.inl (by simpa [r0] using hs_lt)
      · by_cases hs_eq0 : (s : ℕ) = k.val
        · exact Or.inr (Or.inl (Fin.ext (by simpa [r0] using hs_eq0)))
        · by_cases hs_eq1 : (s : ℕ) = k.val + 1
          · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa [r1] using hs_eq1))))
          · have hs_gt : k.val + 1 < (s : ℕ) := by omega
            exact Or.inr (Or.inr (Or.inr (by simpa [r1] using hs_gt)))
    rcases hcases with hs_lt | hs_eq0 | hs_eq1 | hr1_lt_s
    · have hr0_not_lt_s : ¬r0 < s := not_lt_of_gt hs_lt
      have hr1_not_lt_s : ¬r1 < s := by
        intro h
        exact not_lt_of_gt (lt_trans hs_lt hr01) h
      have hs_lt_r1 : s < r1 := lt_trans hs_lt hr01
      have hcoeff : 0 ≤ q ^ (s : ℕ) := pow_nonneg (le_of_lt hq_pos) (s : ℕ)
      have hterm :
          candidateRankConditionalGapTerm q value r0 s -
              candidateRankConditionalGapTerm q value r1 s =
            q ^ (s : ℕ) * (value r0 - value r1) := by
        simp [candidateRankConditionalGapTerm, hs_lt, hs_lt_r1,
          hr0_not_lt_s, hr1_not_lt_s]
        ring
      rw [hterm]
      exact mul_nonneg hcoeff (le_of_lt hgap)
    · subst s
      have hr1_not_lt_r0 : ¬r1 < r0 := not_lt_of_gt hr01
      have hcoeff : 0 ≤ q ^ (r0 : ℕ) := pow_nonneg (le_of_lt hq_pos) (r0 : ℕ)
      have hterm :
          candidateRankConditionalGapTerm q value r0 r0 -
              candidateRankConditionalGapTerm q value r1 r0 =
            q ^ (r0 : ℕ) * (value r0 - value r1) := by
        simp [candidateRankConditionalGapTerm, hr01, hr1_not_lt_r0]
        ring
      rw [hterm]
      exact mul_nonneg hcoeff (le_of_lt hgap)
    · subst s
      have hr1_not_lt_r0 : ¬r1 < r0 := not_lt_of_gt hr01
      have hr1_pred : (r1 : ℕ) - 1 = (r0 : ℕ) := by
        simp [r0, r1]
      have hcoeff : 0 ≤ q ^ ((r1 : ℕ) - 1) :=
        pow_nonneg (le_of_lt hq_pos) ((r1 : ℕ) - 1)
      have hterm :
          candidateRankConditionalGapTerm q value r0 r1 -
              candidateRankConditionalGapTerm q value r1 r1 =
            q ^ ((r1 : ℕ) - 1) * (value r0 - value r1) := by
        simp [candidateRankConditionalGapTerm, hr01, hr1_pred]
      rw [hterm]
      exact mul_nonneg hcoeff (le_of_lt hgap)
    · have hr0_lt_s : r0 < s := lt_trans hr01 hr1_lt_s
      have hs_not_lt_r0 : ¬s < r0 := not_lt_of_gt hr0_lt_s
      have hs_not_lt_r1 : ¬s < r1 := not_lt_of_gt hr1_lt_s
      have hcoeff : 0 ≤ q ^ ((s : ℕ) - 1) :=
        pow_nonneg (le_of_lt hq_pos) ((s : ℕ) - 1)
      have hterm :
          candidateRankConditionalGapTerm q value r0 s -
              candidateRankConditionalGapTerm q value r1 s =
            q ^ ((s : ℕ) - 1) * (value r0 - value r1) := by
        simp [candidateRankConditionalGapTerm, hr0_lt_s, hr1_lt_s]
        ring
      rw [hterm]
      exact mul_nonneg hcoeff (le_of_lt hgap)

theorem candidateRankConditionalGap_strictAnti
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) {value : Candidate n → ℝ}
    (hvalue : ∀ i j : Candidate n, i < j → value j < value i) :
    StrictAnti (candidateRankConditionalGap n q value) := by
  exact Fin.strictAnti_iff_succ_lt.mpr
    (candidateRankConditionalGap_succ_lt n hq_pos hvalue)

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

/-- The fiber of rankings whose first center-rank is `r`, for the identity center. -/
noncomputable def reflFirstChoiceFiber (n : ℕ) (r : Candidate n) :
    Finset (Ranking n) := by
  classical
  exact Finset.univ.filter (fun τ => r = firstChoice τ)

/-- Unnormalised identity-center first-choice Mallows mass. -/
noncomputable def reflFirstWeight (n : ℕ) (q : ℝ) (r : Candidate n) : ℝ :=
  ∑ τ ∈ reflFirstChoiceFiber n r,
    q ^ kendallTau (Equiv.refl (Candidate n)) τ

theorem reflFirstWeight_eq_rank_mul_zero
    (n : ℕ) (q : ℝ) (r : Candidate n) :
    reflFirstWeight n q r =
      q ^ (r : ℕ) * reflFirstWeight n q 0 := by
  classical
  let E : Ranking n := Fin.cycleRange r
  unfold reflFirstWeight
  calc
    ∑ τ ∈ reflFirstChoiceFiber n r,
        q ^ kendallTau (Equiv.refl (Candidate n)) τ
        = ∑ σ ∈ reflFirstChoiceFiber n 0,
            q ^ (r : ℕ) *
              q ^ kendallTau (Equiv.refl (Candidate n)) σ := by
          refine Finset.sum_bij
            (i := fun τ _ => τ.trans E) ?hi ?hinj ?hsurj ?hweight
          · intro τ hτ
            have hfirst : firstChoice τ = r := by
              exact (Finset.mem_filter.mp hτ).2.symm
            unfold reflFirstChoiceFiber
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [firstChoice_trans, hfirst]
            simp [E, Fin.cycleRange_self]
          · intro τ₁ _ τ₂ _ h
            apply Equiv.ext
            intro x
            exact E.injective (Equiv.ext_iff.mp h x)
          · intro σ hσ
            refine ⟨σ.trans E.symm, ?_, ?_⟩
            · have hfirst : firstChoice σ = 0 := by
                exact (Finset.mem_filter.mp hσ).2.symm
              have hcycle : E.symm 0 = r := by
                change (Fin.cycleRange r).symm 0 = r
                exact Fin.cycleRange_symm_zero r
              unfold reflFirstChoiceFiber
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              rw [firstChoice_trans, hfirst, hcycle]
            · ext x
              simp [E]
          · intro τ hτ
            have hfirst : firstChoice τ = r := by
              exact (Finset.mem_filter.mp hτ).2.symm
            have hfirst_apply : τ 0 = r := by
              simpa [firstChoice] using hfirst
            have hkend :
                kendallTau (Equiv.refl (Candidate n)) τ =
                  (r : ℕ) +
                    kendallTau (Equiv.refl (Candidate n)) (τ.trans E) := by
              simpa [E, firstChoice, hfirst_apply] using
                kendallTau_eq_firstChoice_add_cycleRange τ
            rw [hkend, pow_add]
    _ = q ^ (r : ℕ) *
        ∑ σ ∈ reflFirstChoiceFiber n 0,
          q ^ kendallTau (Equiv.refl (Candidate n)) σ := by
          rw [Finset.mul_sum]

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

theorem firstWeight_eq_reflFirstWeight (c : Candidate n) :
    M.firstWeight c =
      reflFirstWeight n M.q (rankOf M.center c) := by
  classical
  unfold firstWeight reflFirstWeight reflFirstChoiceFiber mallowsWeight
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (s := Finset.univ.filter (fun π : Ranking n => c = firstChoice π))
    (t := Finset.univ.filter
      (fun τ : Ranking n => rankOf M.center c = firstChoice τ))
    (i := fun π _ => π.trans M.center.symm) ?hi ?hinj ?hsurj ?hweight
  · intro π hπ
    have hc : c = firstChoice π := (Finset.mem_filter.mp hπ).2
    simp [rankOf, firstChoice, hc]
  · intro π₁ _ π₂ _ h
    apply Equiv.ext
    intro x
    exact M.center.symm.injective (Equiv.ext_iff.mp h x)
  · intro τ hτ
    refine ⟨τ.trans M.center, ?_, ?_⟩
    · have hfirst :
          rankOf M.center c = firstChoice τ := (Finset.mem_filter.mp hτ).2
      have hc : c = M.center (firstChoice τ) := by
        rw [← hfirst]
        simp [rankOf]
      simp [firstChoice, hc]
    · ext x
      simp
  · intro π hπ
    have hkend :
        kendallTau M.center π =
          kendallTau (Equiv.refl (Candidate n)) (π.trans M.center.symm) := by
      have hπ : (π.trans M.center.symm).trans M.center = π := by
        ext x
        simp
      simpa [hπ] using
        kendallTau_center_trans M.center (π.trans M.center.symm)
    rw [hkend]

theorem firstWeight_eq_rank_mul_centerFirst (c : Candidate n) :
    M.firstWeight c =
      M.q ^ (rankOf M.center c : ℕ) * M.firstWeight M.centerFirst := by
  rw [M.firstWeight_eq_reflFirstWeight c]
  rw [reflFirstWeight_eq_rank_mul_zero]
  congr 1
  rw [M.firstWeight_eq_reflFirstWeight M.centerFirst]
  simp [centerFirst, firstChoice, rankOf]

theorem partition_eq_rankPowerSum_mul_centerFirstWeight :
    M.partition =
      candidateRankPowerSum n M.q * M.firstWeight M.centerFirst := by
  rw [← M.sum_firstWeight_eq_partition]
  calc
    ∑ c : Candidate n, M.firstWeight c
        = ∑ c : Candidate n,
            M.q ^ (rankOf M.center c : ℕ) * M.firstWeight M.centerFirst := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [M.firstWeight_eq_rank_mul_centerFirst c]
    _ = ∑ r : Candidate n,
          M.q ^ (r : ℕ) * M.firstWeight M.centerFirst := by
          simpa [rankOf] using
            (Equiv.sum_comp M.center.symm
              (fun r : Candidate n =>
                M.q ^ (r : ℕ) * M.firstWeight M.centerFirst))
    _ = candidateRankPowerSum n M.q * M.firstWeight M.centerFirst := by
          unfold candidateRankPowerSum
          rw [Finset.sum_mul]

/--
Closed-form rank factorization for the first and top-two Mallows weights.

For a Mallows law centered at `M.center`, the top-candidate fiber at center rank
`r` has a factor `M.q^r`, and the ordered top-two fiber for center ranks
`r < s` has a factor `M.q^(r+s-1)` while the swapped order has one extra factor
of `M.q`.
-/
structure RankFactorization where
  firstTail : ℝ
  firstSecondTail : ℝ
  firstTail_pos : 0 < firstTail
  firstSecondTail_pos : 0 < firstSecondTail
  partition_eq :
    M.partition = candidateRankPowerSum n M.q * firstTail
  firstWeight_eq :
    ∀ c : Candidate n,
      M.firstWeight c = M.q ^ (rankOf M.center c : ℕ) * firstTail
  firstSecondWeight_eq_of_lt :
    ∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      M.firstSecondWeight c d =
        M.q ^ ((rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1) *
          firstSecondTail
  firstSecondWeight_swap_eq_of_lt :
    ∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      M.firstSecondWeight d c =
        M.q *
          (M.q ^ ((rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1) *
            firstSecondTail)

/-- Unnormalised first-choice mass of a center-rank prefix. -/
noncomputable def firstWeightPrefix (k : Fin (n + 1)) : ℝ :=
  ∑ c : Candidate n,
    if (rankOf M.center c : ℕ) ≤ k.val then M.firstWeight c else 0

theorem firstWeightPrefix_eq_rankPrefixPowerSum_mul
    (fac : M.RankFactorization) (k : Fin (n + 1)) :
    M.firstWeightPrefix k = candidateRankPrefixPowerSum n M.q k * fac.firstTail := by
  classical
  unfold firstWeightPrefix candidateRankPrefixPowerSum
  calc
    (∑ c : Candidate n,
        if (rankOf M.center c : ℕ) ≤ k.val then M.firstWeight c else 0)
        = ∑ c : Candidate n,
            if (rankOf M.center c : ℕ) ≤ k.val then
              M.q ^ (rankOf M.center c : ℕ) * fac.firstTail
            else
              0 := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [fac.firstWeight_eq c]
    _ = ∑ r : Candidate n,
          if (r : ℕ) ≤ k.val then M.q ^ (r : ℕ) * fac.firstTail else 0 := by
          simpa [rankOf] using
            (Equiv.sum_comp M.center.symm
              (fun r : Candidate n =>
                if (r : ℕ) ≤ k.val then M.q ^ (r : ℕ) * fac.firstTail else 0))
    _ = (∑ r : Candidate n,
          if (r : ℕ) ≤ k.val then M.q ^ (r : ℕ) else 0) * fac.firstTail := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro r _
          by_cases hr : (r : ℕ) ≤ k.val <;> simp [hr]

/-- The ordered-pair summand in the cleared independent-reranking numerator. -/
noncomputable def independentPairTerm
    (value : Candidate n → ℝ) (c d : Candidate n) : ℝ :=
  (M.partition - M.firstWeight c) *
    M.firstSecondWeight c d * (value c - value d)

/--
The antisymmetrized top-two bracket for the unordered pair `{c,d}`.

Appendix E compares the `(c,d)` and `(d,c)` top-two fibers through exactly this
quantity after clearing Mallows denominators.
-/
noncomputable def independentPairBracket (c d : Candidate n) : ℝ :=
  (M.partition - M.firstWeight c) * M.firstSecondWeight c d -
    (M.partition - M.firstWeight d) * M.firstSecondWeight d c

@[simp] theorem independentPairTerm_apply
    (value : Candidate n → ℝ) (c d : Candidate n) :
    M.independentPairTerm value c d =
      (M.partition - M.firstWeight c) *
        M.firstSecondWeight c d * (value c - value d) := rfl

@[simp] theorem independentPairBracket_apply (c d : Candidate n) :
    M.independentPairBracket c d =
      (M.partition - M.firstWeight c) * M.firstSecondWeight c d -
        (M.partition - M.firstWeight d) * M.firstSecondWeight d c := rfl

/-- No ranking has the same candidate as both first and second choice. -/
@[simp] theorem firstSecondWeight_self (c : Candidate n) :
    M.firstSecondWeight c c = 0 := by
  classical
  unfold firstSecondWeight
  apply Finset.sum_eq_zero
  intro π _
  have hnot : ¬(c = firstChoice π ∧ c = secondChoice π) := by
    intro h
    have hfs : firstChoice π = secondChoice π := h.1.symm.trans h.2
    exact firstChoice_ne_secondChoice π hfs
  have hraw : ¬(c = π 0 ∧ c = π 1) := by
    intro h
    apply hnot
    exact ⟨by simpa [firstChoice] using h.1,
      by simpa [secondChoice] using h.2⟩
  simp [firstChoice, secondChoice, hraw]

/--
Pairing the ordered top-two events `(c,d)` and `(d,c)` produces a single
bracket times the value difference.
-/
theorem independentPairTerm_add_swap
    (value : Candidate n → ℝ) (c d : Candidate n) :
    M.independentPairTerm value c d + M.independentPairTerm value d c =
      M.independentPairBracket c d * (value c - value d) := by
  unfold independentPairTerm independentPairBracket
  ring

/--
If a pair is ordered by value and its Mallows pair bracket is nonnegative, then
the paired `(c,d)`/`(d,c)` contribution is nonnegative.
-/
theorem independentPairTerm_add_swap_nonneg
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hbracket : 0 ≤ M.independentPairBracket c d)
    (hvalue : value d ≤ value c) :
    0 ≤ M.independentPairTerm value c d + M.independentPairTerm value d c := by
  rw [M.independentPairTerm_add_swap value c d]
  exact mul_nonneg hbracket (sub_nonneg.mpr hvalue)

/--
If a pair is strictly ordered by value and its Mallows pair bracket is positive,
then the paired `(c,d)`/`(d,c)` contribution is positive.
-/
theorem independentPairTerm_add_swap_pos
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hbracket : 0 < M.independentPairBracket c d)
    (hvalue : value d < value c) :
    0 < M.independentPairTerm value c d + M.independentPairTerm value d c := by
  rw [M.independentPairTerm_add_swap value c d]
  exact mul_pos hbracket (sub_pos.mpr hvalue)

/--
The closed-form rank factorization implies the nonnegative Appendix-E
independent-reranking bracket for every center-ordered pair.
-/
theorem independentPairBracket_nonneg_of_rankFactorization
    (fac : M.RankFactorization) (hq_le_one : M.q ≤ 1)
    {c d : Candidate n} (hlt : rankOf M.center c < rankOf M.center d) :
    0 ≤ M.independentPairBracket c d := by
  let k : ℕ := (rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1
  have hinner :
      0 ≤ (candidateRankPowerSum n M.q - M.q ^ (rankOf M.center c : ℕ)) -
        M.q * (candidateRankPowerSum n M.q -
          M.q ^ (rankOf M.center d : ℕ)) := by
    exact candidateRankPowerSum_inner_nonneg
      (le_of_lt M.q_pos) hq_le_one hlt
  have hqk_nonneg : 0 ≤ M.q ^ k := pow_nonneg (le_of_lt M.q_pos) k
  have heq :
      M.independentPairBracket c d =
        fac.firstTail * (M.q ^ k * fac.firstSecondTail) *
          ((candidateRankPowerSum n M.q - M.q ^ (rankOf M.center c : ℕ)) -
            M.q * (candidateRankPowerSum n M.q -
              M.q ^ (rankOf M.center d : ℕ))) := by
    unfold independentPairBracket
    rw [fac.partition_eq, fac.firstWeight_eq c, fac.firstWeight_eq d,
      fac.firstSecondWeight_eq_of_lt c d hlt,
      fac.firstSecondWeight_swap_eq_of_lt c d hlt]
    ring
  rw [heq]
  exact mul_nonneg
    (mul_nonneg (le_of_lt fac.firstTail_pos)
      (mul_nonneg hqk_nonneg (le_of_lt fac.firstSecondTail_pos)))
    hinner

/--
For at least three candidates and `0 < q < 1`, the center top-two pair has a
strictly positive independent-reranking bracket under the rank factorization.
-/
theorem independentPairBracket_centerTopTwo_pos_of_rankFactorization
    (fac : M.RankFactorization) (hn : 0 < n) (hq_lt_one : M.q < 1) :
    0 < M.independentPairBracket M.centerFirst M.centerSecond := by
  let c : Candidate n := M.centerFirst
  let d : Candidate n := M.centerSecond
  have hlt : rankOf M.center c < rankOf M.center d := by
    simp [c, d, MallowsSpec.centerFirst, MallowsSpec.centerSecond, rankOf]
  let k : ℕ := (rankOf M.center c : ℕ) + (rankOf M.center d : ℕ) - 1
  have hk : k = 0 := by
    simp [k, c, d, MallowsSpec.centerFirst, MallowsSpec.centerSecond, rankOf]
  have hinner :
      0 < (candidateRankPowerSum n M.q - M.q ^ (rankOf M.center c : ℕ)) -
        M.q * (candidateRankPowerSum n M.q -
          M.q ^ (rankOf M.center d : ℕ)) := by
    simpa [c, d, MallowsSpec.centerFirst, MallowsSpec.centerSecond, rankOf] using
      candidateRankPowerSum_inner_pos_zero_one hn M.q_pos hq_lt_one
  have hqk_pos : 0 < M.q ^ k := pow_pos M.q_pos k
  have heq :
      M.independentPairBracket c d =
        fac.firstTail * (M.q ^ k * fac.firstSecondTail) *
          ((candidateRankPowerSum n M.q - M.q ^ (rankOf M.center c : ℕ)) -
            M.q * (candidateRankPowerSum n M.q -
              M.q ^ (rankOf M.center d : ℕ))) := by
    unfold independentPairBracket
    rw [fac.partition_eq, fac.firstWeight_eq c, fac.firstWeight_eq d,
      fac.firstSecondWeight_eq_of_lt c d hlt,
      fac.firstSecondWeight_swap_eq_of_lt c d hlt]
    ring
  rw [heq]
  exact mul_pos
    (mul_pos fac.firstTail_pos (mul_pos hqk_pos fac.firstSecondTail_pos))
    hinner

theorem centerFirstGapWeight_pos_of_strictlyOrderedCenter
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy M.center value) :
    0 < M.firstChoiceGapWeight value M.centerFirst := by
  have hmass := M.centerFirstGapMass_pos_of_strictlyOrderedCenter hvalue
  rw [M.firstChoiceGapMass_eq_firstChoiceGapWeight_div_partition] at hmass
  exact (div_pos_iff_of_pos_right M.partition_pos).mp hmass

/--
Top-two expansion of the unnormalised first-choice gap numerator.

This is the paper's Appendix-E decomposition step: a ranking whose first two
candidates are `(c,d)` contributes exactly `value c - value d` to the
first-choice gap attached to `c`.
-/
theorem firstChoiceGapWeight_eq_sum_firstSecondWeight
    (value : Candidate n → ℝ) (c : Candidate n) :
    M.firstChoiceGapWeight value c =
      ∑ d : Candidate n, M.firstSecondWeight c d * (value c - value d) := by
  classical
  unfold firstChoiceGapWeight firstSecondWeight
  calc
    ∑ π : Ranking n,
        (if c = firstChoice π then
          mallowsWeight M.q M.center π * valueGap value π
        else
          0)
        = ∑ π : Ranking n,
            ∑ d : Candidate n,
              (if c = firstChoice π ∧ d = secondChoice π then
                mallowsWeight M.q M.center π * (value c - value d)
              else
                0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases hc : c = firstChoice π
          · have hraw : c = π 0 := by
              simpa [firstChoice] using hc
            have hsum :
                (∑ d : Candidate n,
                  if d = secondChoice π then
                    mallowsWeight M.q M.center π * (value c - value d)
                  else
                    0) =
                  mallowsWeight M.q M.center π *
                    (value c - value (secondChoice π)) := by
              simpa using
                (Finset.sum_ite_eq' Finset.univ (secondChoice π)
                  (fun d : Candidate n =>
                    mallowsWeight M.q M.center π * (value c - value d)))
            calc
              (if c = firstChoice π then
                  mallowsWeight M.q M.center π * valueGap value π
                else
                  0)
                  = mallowsWeight M.q M.center π *
                      (value c - value (secondChoice π)) := by
                    simp [hc, valueGap]
              _ = ∑ d : Candidate n,
                    (if c = firstChoice π ∧ d = secondChoice π then
                      mallowsWeight M.q M.center π * (value c - value d)
                    else
                      0) := by
                    rw [← hsum]
                    refine Finset.sum_congr rfl ?_
                    intro d _
                    by_cases hd : d = secondChoice π <;> simp [hc, hd]
          · have hraw : c ≠ π 0 := by
              simpa [firstChoice] using hc
            simp [hraw]
    _ = ∑ d : Candidate n,
          ∑ π : Ranking n,
            (if c = firstChoice π ∧ d = secondChoice π then
              mallowsWeight M.q M.center π * (value c - value d)
            else
              0) := by
          rw [Finset.sum_comm]
    _ = ∑ d : Candidate n,
          (∑ π : Ranking n,
            (if c = firstChoice π ∧ d = secondChoice π then
              mallowsWeight M.q M.center π
            else
              0)) * (value c - value d) := by
          refine Finset.sum_congr rfl ?_
          intro d _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = firstChoice π ∧ d = secondChoice π
          · simp [h]
          · have h' : ¬(c = π 0 ∧ d = π 1) := by
              intro hraw
              apply h
              exact ⟨by simpa [firstChoice] using hraw.1,
                by simpa [secondChoice] using hraw.2⟩
            simp [h']

/--
Rank-factorized form of the conditional first-choice gap.

After conditioning on a first-choice center rank `r`, the remaining top-two
Mallows fiber contributes the rank-only conditional gap used in Appendix E.
-/
theorem firstChoiceGapWeight_eq_rankConditionalGap
    (fac : M.RankFactorization) (value : Candidate n → ℝ) (c : Candidate n) :
    M.firstChoiceGapWeight value c =
      M.q ^ (rankOf M.center c : ℕ) * fac.firstSecondTail *
        candidateRankConditionalGap n M.q
          (fun r : Candidate n => value (M.center r)) (rankOf M.center c) := by
  classical
  let r : Candidate n := rankOf M.center c
  have hc_center : M.center r = c := by
    simp [r, rankOf]
  rw [M.firstChoiceGapWeight_eq_sum_firstSecondWeight value c]
  calc
    (∑ d : Candidate n, M.firstSecondWeight c d * (value c - value d))
        = ∑ s : Candidate n,
            M.firstSecondWeight c (M.center s) *
              (value c - value (M.center s)) := by
          simpa using
            (Equiv.sum_comp M.center
              (fun d : Candidate n =>
                M.firstSecondWeight c d * (value c - value d))).symm
    _ = ∑ s : Candidate n,
          (M.q ^ (r : ℕ) * fac.firstSecondTail) *
            candidateRankConditionalGapTerm M.q
              (fun x : Candidate n => value (M.center x)) r s := by
          refine Finset.sum_congr rfl ?_
          intro s _
          by_cases hrs : r < s
          · have hlt :
                rankOf M.center c < rankOf M.center (M.center s) := by
              simpa [r, rankOf] using hrs
            have hs_pos : 0 < (s : ℕ) :=
              lt_of_le_of_lt (Nat.zero_le (r : ℕ)) hrs
            have hsplit :
                (r : ℕ) + (s : ℕ) - 1 =
                  (r : ℕ) + ((s : ℕ) - 1) := by
              omega
            rw [fac.firstSecondWeight_eq_of_lt c (M.center s) hlt]
            rw [← hc_center]
            simp [candidateRankConditionalGapTerm, hrs, rankOf]
            rw [hsplit, pow_add]
            ring
          · by_cases hsr : s < r
            · have hlt :
                  rankOf M.center (M.center s) < rankOf M.center c := by
                simpa [r, rankOf] using hsr
              have hnot : ¬r < s := hrs
              have hsucc :
                  ((s : ℕ) + (r : ℕ) - 1) + 1 =
                    (r : ℕ) + (s : ℕ) := by
                have hsr_nat : (s : ℕ) < (r : ℕ) := hsr
                omega
              rw [fac.firstSecondWeight_swap_eq_of_lt (M.center s) c hlt]
              rw [← hc_center]
              simp [candidateRankConditionalGapTerm, hnot, hsr, rankOf]
              rw [← mul_assoc M.q (M.q ^ ((s : ℕ) + (r : ℕ) - 1)) fac.firstSecondTail]
              rw [← pow_succ', hsucc, pow_add]
              ring
            · have hsr_eq : s = r := by
                exact le_antisymm (le_of_not_gt hrs) (le_of_not_gt hsr)
              subst s
              simp [candidateRankConditionalGapTerm, hc_center]
    _ = M.q ^ (rankOf M.center c : ℕ) * fac.firstSecondTail *
          candidateRankConditionalGap n M.q
            (fun r : Candidate n => value (M.center r)) (rankOf M.center c) := by
          unfold candidateRankConditionalGap
          rw [← Finset.mul_sum]

/--
The denominator-cleared independent-reranking sum can be written as a sum over
ordered top-two candidate pairs.
-/
theorem independent_weight_sum_eq_pair_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c) =
      ∑ c : Candidate n, ∑ d : Candidate n,
        M.independentPairTerm value c d := by
  classical
  calc
    ∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c
        = ∑ c : Candidate n,
            (M.partition - M.firstWeight c) *
              (∑ d : Candidate n,
                M.firstSecondWeight c d * (value c - value d)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [M.firstChoiceGapWeight_eq_sum_firstSecondWeight value c]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
        (M.partition - M.firstWeight c) *
          (M.firstSecondWeight c d * (value c - value d)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.mul_sum]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
        M.independentPairTerm value c d := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro d _
          unfold independentPairTerm
          ring

theorem pair_sum_eq_ordered_swap_sum
    {n : ℕ} (ρ : Ranking n) (t : Candidate n → Candidate n → ℝ)
    (hdiag : ∀ c : Candidate n, t c c = 0) :
    (∑ c : Candidate n, ∑ d : Candidate n, t c d) =
      ∑ c : Candidate n, ∑ d : Candidate n,
        if rankOf ρ c < rankOf ρ d then t c d + t d c else 0 := by
  classical
  have hsplit : ∀ c d : Candidate n,
      t c d =
        (if rankOf ρ c < rankOf ρ d then t c d else 0) +
          (if rankOf ρ d < rankOf ρ c then t c d else 0) := by
    intro c d
    by_cases hlt : rankOf ρ c < rankOf ρ d
    · have hnot : ¬ rankOf ρ d < rankOf ρ c := not_lt_of_gt hlt
      simp [hlt, hnot]
    · by_cases hgt : rankOf ρ d < rankOf ρ c
      · simp [hlt, hgt]
      · have heq_rank : rankOf ρ c = rankOf ρ d := le_antisymm
          (le_of_not_gt hgt) (le_of_not_gt hlt)
        have hcd : c = d := by
          exact ρ.symm.injective heq_rank
        subst d
        simp [hdiag]
  calc
    (∑ c : Candidate n, ∑ d : Candidate n, t c d)
        = ∑ c : Candidate n, ∑ d : Candidate n,
            ((if rankOf ρ c < rankOf ρ d then t c d else 0) +
              (if rankOf ρ d < rankOf ρ c then t c d else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro d _
          exact hsplit c d
    _ = (∑ c : Candidate n, ∑ d : Candidate n,
            if rankOf ρ c < rankOf ρ d then t c d else 0) +
          (∑ c : Candidate n, ∑ d : Candidate n,
            if rankOf ρ d < rankOf ρ c then t c d else 0) := by
          simp_rw [Finset.sum_add_distrib]
    _ = (∑ c : Candidate n, ∑ d : Candidate n,
            if rankOf ρ c < rankOf ρ d then t c d else 0) +
          (∑ c : Candidate n, ∑ d : Candidate n,
            if rankOf ρ c < rankOf ρ d then t d c else 0) := by
          have hswap :
              (∑ c : Candidate n, ∑ d : Candidate n,
                if rankOf ρ d < rankOf ρ c then t c d else 0) =
                ∑ c : Candidate n, ∑ d : Candidate n,
                  if rankOf ρ c < rankOf ρ d then t d c else 0 := by
            rw [Finset.sum_comm]
          rw [hswap]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
          if rankOf ρ c < rankOf ρ d then t c d + t d c else 0 := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro d _
          by_cases hlt : rankOf ρ c < rankOf ρ d <;> simp [hlt]

/--
The ordered top-two pair sum can be regrouped over center-ordered unordered
pairs. This is the finite-sum form of the Appendix-E `(c,d)`/`(d,c)` pairing.
-/
theorem independent_pair_sum_eq_ordered_swap_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n, ∑ d : Candidate n,
        M.independentPairTerm value c d) =
      ∑ c : Candidate n, ∑ d : Candidate n,
        if rankOf M.center c < rankOf M.center d then
          M.independentPairTerm value c d + M.independentPairTerm value d c
        else 0 := by
  refine pair_sum_eq_ordered_swap_sum M.center (M.independentPairTerm value) ?_
  intro c
  unfold independentPairTerm
  ring

/--
Appendix-E pair-bracket signs imply positivity of the cleared
independent-reranking numerator.

This reduces the total finite Mallows inequality to the local pairwise bracket
comparisons for center-ordered candidate pairs.
-/
theorem independent_weight_sum_pos_of_pair_brackets
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy M.center value)
    (hbracket_nonneg :
      ∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
        0 ≤ M.independentPairBracket c d)
    (hbracket_pos :
      ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
        0 < M.independentPairBracket c d) :
    0 < ∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c := by
  classical
  rw [M.independent_weight_sum_eq_pair_sum value]
  rw [M.independent_pair_sum_eq_ordered_swap_sum value]
  rcases hbracket_pos with ⟨c₀, d₀, hlt₀, hbracket₀⟩
  apply DecisionCore.sum_univ_pos_of_pos_of_nonneg
    (f := fun c : Candidate n =>
      ∑ d : Candidate n,
        if rankOf M.center c < rankOf M.center d then
          M.independentPairTerm value c d + M.independentPairTerm value d c
        else 0)
    (a₀ := c₀)
  · apply DecisionCore.sum_univ_pos_of_pos_of_nonneg
      (f := fun d : Candidate n =>
        if rankOf M.center c₀ < rankOf M.center d then
          M.independentPairTerm value c₀ d + M.independentPairTerm value d c₀
        else 0)
      (a₀ := d₀)
    · have hpos := M.independentPairTerm_add_swap_pos
          (value := value) hbracket₀ (hvalue hlt₀)
      simpa [hlt₀, independentPairTerm] using hpos
    · intro d
      by_cases hlt : rankOf M.center c₀ < rankOf M.center d
      · exact if_pos hlt ▸
          M.independentPairTerm_add_swap_nonneg
            (value := value) (hbracket_nonneg c₀ d hlt)
            (le_of_lt (hvalue hlt))
      · simp [hlt]
  · intro c
    apply Finset.sum_nonneg
    intro d _
    by_cases hlt : rankOf M.center c < rankOf M.center d
    · exact if_pos hlt ▸
        M.independentPairTerm_add_swap_nonneg
          (value := value) (hbracket_nonneg c d hlt)
          (le_of_lt (hvalue hlt))
    · simp [hlt]

/--
Closed-form Mallows rank factorization proves the cleared
independent-reranking finite-sum inequality for any strictly center-ordered value
profile, provided there are at least three candidates and `0 < q < 1`.
-/
theorem independent_weight_sum_pos_of_rankFactorization
    {value : Candidate n → ℝ}
    (fac : M.RankFactorization) (hn : 0 < n) (hq_lt_one : M.q < 1)
    (hvalue : StrictlyOrderedBy M.center value) :
    0 < ∑ c : Candidate n,
      (M.partition - M.firstWeight c) * M.firstChoiceGapWeight value c := by
  refine M.independent_weight_sum_pos_of_pair_brackets hvalue ?nonneg ?pos
  · intro c d hlt
    exact M.independentPairBracket_nonneg_of_rankFactorization
      fac (le_of_lt hq_lt_one) hlt
  · exact ⟨M.centerFirst, M.centerSecond,
      by
        simp [MallowsSpec.centerFirst, MallowsSpec.centerSecond, rankOf],
      M.independentPairBracket_centerTopTwo_pos_of_rankFactorization
        fac hn hq_lt_one⟩

end MallowsSpec

theorem candidateRankWeightedAverage_strictAnti
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {B : Candidate n → ℝ} (hB : StrictAnti B) :
    0 <
      candidateRankPowerSum n q₂ *
          (∑ i : Candidate n, q₁ ^ (i : ℕ) * B i) -
        candidateRankPowerSum n q₁ *
          (∑ i : Candidate n, q₂ ^ (i : ℕ) * B i) := by
  classical
  let t : Candidate n → Candidate n → ℝ := fun i j =>
    q₁ ^ (i : ℕ) * B i * q₂ ^ (j : ℕ) -
      q₂ ^ (i : ℕ) * B i * q₁ ^ (j : ℕ)
  have hdouble :
      candidateRankPowerSum n q₂ *
          (∑ i : Candidate n, q₁ ^ (i : ℕ) * B i) -
        candidateRankPowerSum n q₁ *
          (∑ i : Candidate n, q₂ ^ (i : ℕ) * B i) =
        ∑ i : Candidate n, ∑ j : Candidate n, t i j := by
    unfold candidateRankPowerSum
    calc
      (∑ j : Candidate n, q₂ ^ (j : ℕ)) *
            (∑ i : Candidate n, q₁ ^ (i : ℕ) * B i) -
          (∑ j : Candidate n, q₁ ^ (j : ℕ)) *
            (∑ i : Candidate n, q₂ ^ (i : ℕ) * B i)
          =
          (∑ i : Candidate n, ∑ j : Candidate n,
              q₁ ^ (i : ℕ) * B i * q₂ ^ (j : ℕ)) -
            (∑ i : Candidate n, ∑ j : Candidate n,
              q₂ ^ (i : ℕ) * B i * q₁ ^ (j : ℕ)) := by
            rw [Finset.sum_mul, Finset.sum_mul]
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
      _ = ∑ i : Candidate n, ∑ j : Candidate n, t i j := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_sub_distrib]
  rw [hdouble]
  rw [MallowsSpec.pair_sum_eq_ordered_swap_sum (Equiv.refl (Candidate n)) t
    (by
      intro i
      simp [t]
      ring)]
  apply DecisionCore.sum_univ_pos_of_pos_of_nonneg
    (f := fun i : Candidate n =>
      ∑ j : Candidate n,
        if rankOf (Equiv.refl (Candidate n)) i <
            rankOf (Equiv.refl (Candidate n)) j then
          t i j + t j i
        else 0)
    (a₀ := (0 : Candidate n))
  · apply DecisionCore.sum_univ_pos_of_pos_of_nonneg
      (f := fun j : Candidate n =>
        if rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
            rankOf (Equiv.refl (Candidate n)) j then
          t (0 : Candidate n) j + t j (0 : Candidate n)
        else 0)
      (a₀ := (1 : Candidate n))
    · have hlt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) (1 : Candidate n) := by
        change (0 : ℕ) < 1
        omega
      have hweight :
          0 < q₁ ^ ((0 : Candidate n) : ℕ) * q₂ ^ ((1 : Candidate n) : ℕ) -
            q₁ ^ ((1 : Candidate n) : ℕ) * q₂ ^ ((0 : Candidate n) : ℕ) := by
        have hpow := rankPower_mul_lt_mul_rankPower
          hq₁_pos hq_lt (show (0 : Candidate n) < (1 : Candidate n) by
            change (0 : ℕ) < 1
            omega)
        exact sub_pos.mpr (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hpow)
      have hgap :
          0 < B (0 : Candidate n) - B (1 : Candidate n) := by
        exact sub_pos.mpr (hB (show (0 : Candidate n) < (1 : Candidate n) by
          change (0 : ℕ) < 1
          omega))
      have hterm :
          0 < t (0 : Candidate n) (1 : Candidate n) +
              t (1 : Candidate n) (0 : Candidate n) := by
        have heq :
            t (0 : Candidate n) (1 : Candidate n) +
                t (1 : Candidate n) (0 : Candidate n) =
              (q₁ ^ ((0 : Candidate n) : ℕ) * q₂ ^ ((1 : Candidate n) : ℕ) -
                q₁ ^ ((1 : Candidate n) : ℕ) * q₂ ^ ((0 : Candidate n) : ℕ)) *
                (B (0 : Candidate n) - B (1 : Candidate n)) := by
          simp [t]
          ring
        rw [heq]
        exact mul_pos hweight hgap
      simpa [hlt] using hterm
    · intro j
      by_cases hlt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) j
      · have hnonneg :
            0 ≤ t (0 : Candidate n) j + t j (0 : Candidate n) := by
          have h0j : (0 : Candidate n) < j := by
            simpa [rankOf] using hlt
          have hweight :
              0 ≤ q₁ ^ ((0 : Candidate n) : ℕ) * q₂ ^ (j : ℕ) -
                q₁ ^ (j : ℕ) * q₂ ^ ((0 : Candidate n) : ℕ) := by
            have hpow := rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt h0j
            exact sub_nonneg.mpr (le_of_lt (by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hpow))
          have hgap : 0 ≤ B (0 : Candidate n) - B j :=
            le_of_lt (sub_pos.mpr (hB h0j))
          have heq :
              t (0 : Candidate n) j + t j (0 : Candidate n) =
                (q₁ ^ ((0 : Candidate n) : ℕ) * q₂ ^ (j : ℕ) -
                  q₁ ^ (j : ℕ) * q₂ ^ ((0 : Candidate n) : ℕ)) *
                  (B (0 : Candidate n) - B j) := by
            simp [t]
            ring
          rw [heq]
          exact mul_nonneg hweight hgap
        exact if_pos hlt ▸ hnonneg
      · simp [hlt]
  · intro i
    apply Finset.sum_nonneg
    intro j _
    by_cases hlt : rankOf (Equiv.refl (Candidate n)) i <
        rankOf (Equiv.refl (Candidate n)) j
    · have hij : i < j := by
        simpa [rankOf] using hlt
      have hweight :
          0 ≤ q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
            q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ) := by
        have hpow := rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hij
        exact sub_nonneg.mpr (le_of_lt (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hpow))
      have hgap : 0 ≤ B i - B j := le_of_lt (sub_pos.mpr (hB hij))
      have heq :
          t i j + t j i =
            (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
              q₁ ^ (j : ℕ) * q₂ ^ (i : ℕ)) * (B i - B j) := by
        simp [t]
        ring
      exact if_pos hlt ▸ by
        rw [heq]
        exact mul_nonneg hweight hgap
    · simp [hlt]

theorem candidateRankCollisionWeight_cross_pos
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    (hq₂_lt_one : q₂ < 1) :
    0 <
      candidateRankPowerSum n q₂ * candidateRankPowerSum n (q₁ * q₂) -
        candidateRankPowerSum n q₁ * candidateRankPowerSum n (q₂ * q₂) := by
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  let B : Candidate n → ℝ := fun i => q₂ ^ (i : ℕ)
  have hB : StrictAnti B := by
    intro i j hij
    exact pow_lt_pow_right_of_lt_one₀ hq₂_pos hq₂_lt_one hij
  have hmain := candidateRankWeightedAverage_strictAnti n hq₁_pos hq_lt hB
  have hleft :
      (∑ i : Candidate n, q₁ ^ (i : ℕ) * B i) =
        candidateRankPowerSum n (q₁ * q₂) := by
    unfold candidateRankPowerSum B
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [mul_pow]
  have hright :
      (∑ i : Candidate n, q₂ ^ (i : ℕ) * B i) =
        candidateRankPowerSum n (q₂ * q₂) := by
    unfold candidateRankPowerSum B
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [mul_pow]
  simpa [hleft, hright] using hmain

theorem candidateRankSquareWeightedConditionalGap_pos
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) (hq_lt_one : q < 1)
    {value : Candidate n → ℝ}
    (hvalue : ∀ i j : Candidate n, i < j → value j < value i) :
    0 < ∑ r : Candidate n,
      (q * q) ^ (r : ℕ) * candidateRankConditionalGap n q value r := by
  classical
  let t : Candidate n → Candidate n → ℝ := fun r s =>
    (q * q) ^ (r : ℕ) * candidateRankConditionalGapTerm q value r s
  have hdouble :
      (∑ r : Candidate n,
        (q * q) ^ (r : ℕ) * candidateRankConditionalGap n q value r) =
        ∑ r : Candidate n, ∑ s : Candidate n, t r s := by
    unfold candidateRankConditionalGap
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [Finset.mul_sum]
  rw [hdouble]
  rw [MallowsSpec.pair_sum_eq_ordered_swap_sum (Equiv.refl (Candidate n)) t
    (by
      intro r
      simp [t, candidateRankConditionalGapTerm])]
  have hq_sq_pos : 0 < q * q := mul_pos hq_pos hq_pos
  have hq_sq_lt_q : q * q < q := by
    nlinarith [mul_lt_mul_of_pos_left hq_lt_one hq_pos]
  apply DecisionCore.sum_univ_pos_of_pos_of_nonneg
    (f := fun r : Candidate n =>
      ∑ s : Candidate n,
        if rankOf (Equiv.refl (Candidate n)) r <
            rankOf (Equiv.refl (Candidate n)) s then
          t r s + t s r
        else 0)
    (a₀ := (0 : Candidate n))
  · apply DecisionCore.sum_univ_pos_of_pos_of_nonneg
      (f := fun s : Candidate n =>
        if rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
            rankOf (Equiv.refl (Candidate n)) s then
          t (0 : Candidate n) s + t s (0 : Candidate n)
        else 0)
      (a₀ := (1 : Candidate n))
    · have hlt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) (1 : Candidate n) := by
        change (0 : ℕ) < 1
        omega
      have hpair : (0 : Candidate n) < (1 : Candidate n) := by
        change (0 : ℕ) < 1
        omega
      have hcoeff :
          0 < (q * q) ^ ((0 : Candidate n) : ℕ) *
                q ^ (((1 : Candidate n) : ℕ) - 1) -
              (q * q) ^ ((1 : Candidate n) : ℕ) *
                q ^ ((0 : Candidate n) : ℕ) := by
        have hpow₁ := rankPower_mul_lt_mul_rankPower
          hq_sq_pos hq_sq_lt_q hpair
        have hpred :
            q ^ (((1 : Candidate n) : ℕ)) <
              q ^ (((1 : Candidate n) : ℕ) - 1) := by
          have hpred_exp :
              (((1 : Candidate n) : ℕ) - 1) < ((1 : Candidate n) : ℕ) := by
            change (1 : ℕ) - 1 < 1
            omega
          exact pow_lt_pow_right_of_lt_one₀ hq_pos hq_lt_one hpred_exp
        have hpow₂ :
            (q * q) ^ ((0 : Candidate n) : ℕ) *
                q ^ (((1 : Candidate n) : ℕ)) <
              (q * q) ^ ((0 : Candidate n) : ℕ) *
                q ^ (((1 : Candidate n) : ℕ) - 1) := by
          exact mul_lt_mul_of_pos_left hpred
            (pow_pos hq_sq_pos ((0 : Candidate n) : ℕ))
        exact sub_pos.mpr (lt_trans (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hpow₁) hpow₂)
      have hgap :
          0 < value (0 : Candidate n) - value (1 : Candidate n) :=
        sub_pos.mpr (hvalue (0 : Candidate n) (1 : Candidate n) hpair)
      have hterm :
          0 < t (0 : Candidate n) (1 : Candidate n) +
              t (1 : Candidate n) (0 : Candidate n) := by
        have hnot : ¬(1 : Candidate n) < (0 : Candidate n) := not_lt_of_gt hpair
        have heq :
            t (0 : Candidate n) (1 : Candidate n) +
                t (1 : Candidate n) (0 : Candidate n) =
              ((q * q) ^ ((0 : Candidate n) : ℕ) *
                  q ^ (((1 : Candidate n) : ℕ) - 1) -
                (q * q) ^ ((1 : Candidate n) : ℕ) *
                  q ^ ((0 : Candidate n) : ℕ)) *
                (value (0 : Candidate n) - value (1 : Candidate n)) := by
          simp [t, candidateRankConditionalGapTerm, hpair, hnot]
          ring
        rw [heq]
        exact mul_pos hcoeff hgap
      simpa [hlt] using hterm
    · intro s
      by_cases hlt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) s
      · have h0s : (0 : Candidate n) < s := by
          simpa [rankOf] using hlt
        have hcoeff :
            0 ≤ (q * q) ^ ((0 : Candidate n) : ℕ) *
                  q ^ ((s : ℕ) - 1) -
                (q * q) ^ (s : ℕ) *
                  q ^ ((0 : Candidate n) : ℕ) := by
          have hpow₁ := rankPower_mul_lt_mul_rankPower
            hq_sq_pos hq_sq_lt_q h0s
          have hpred : q ^ (s : ℕ) < q ^ ((s : ℕ) - 1) := by
            have hs_pos : 0 < (s : ℕ) := by
              simpa using h0s
            have hpred_exp : (s : ℕ) - 1 < (s : ℕ) := by omega
            exact pow_lt_pow_right_of_lt_one₀ hq_pos hq_lt_one hpred_exp
          have hpow₂ :
              (q * q) ^ ((0 : Candidate n) : ℕ) * q ^ (s : ℕ) <
                (q * q) ^ ((0 : Candidate n) : ℕ) *
                  q ^ ((s : ℕ) - 1) := by
            exact mul_lt_mul_of_pos_left hpred
              (pow_pos hq_sq_pos ((0 : Candidate n) : ℕ))
          exact le_of_lt (sub_pos.mpr (lt_trans (by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hpow₁) hpow₂))
        have hgap : 0 ≤ value (0 : Candidate n) - value s :=
          le_of_lt (sub_pos.mpr (hvalue (0 : Candidate n) s h0s))
        have hnot : ¬s < (0 : Candidate n) := not_lt_of_gt h0s
        have heq :
            t (0 : Candidate n) s + t s (0 : Candidate n) =
              ((q * q) ^ ((0 : Candidate n) : ℕ) * q ^ ((s : ℕ) - 1) -
                (q * q) ^ (s : ℕ) * q ^ ((0 : Candidate n) : ℕ)) *
                (value (0 : Candidate n) - value s) := by
          simp [t, candidateRankConditionalGapTerm, h0s, hnot]
          ring
        exact if_pos hlt ▸ by
          rw [heq]
          exact mul_nonneg hcoeff hgap
      · simp [hlt]
  · intro r
    apply Finset.sum_nonneg
    intro s _
    by_cases hlt : rankOf (Equiv.refl (Candidate n)) r <
        rankOf (Equiv.refl (Candidate n)) s
    · have hrs : r < s := by
        simpa [rankOf] using hlt
      have hcoeff :
          0 ≤ (q * q) ^ (r : ℕ) * q ^ ((s : ℕ) - 1) -
            (q * q) ^ (s : ℕ) * q ^ (r : ℕ) := by
        have hpow₁ := rankPower_mul_lt_mul_rankPower
          hq_sq_pos hq_sq_lt_q hrs
        have hpred : q ^ (s : ℕ) < q ^ ((s : ℕ) - 1) := by
          have hs_pos : 0 < (s : ℕ) := by
            exact lt_of_le_of_lt (Nat.zero_le (r : ℕ)) hrs
          have hpred_exp : (s : ℕ) - 1 < (s : ℕ) := by omega
          exact pow_lt_pow_right_of_lt_one₀ hq_pos hq_lt_one hpred_exp
        have hpow₂ :
            (q * q) ^ (r : ℕ) * q ^ (s : ℕ) <
              (q * q) ^ (r : ℕ) * q ^ ((s : ℕ) - 1) := by
          exact mul_lt_mul_of_pos_left hpred (pow_pos hq_sq_pos (r : ℕ))
        exact le_of_lt (sub_pos.mpr (lt_trans (by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hpow₁) hpow₂))
      have hgap : 0 ≤ value r - value s :=
        le_of_lt (sub_pos.mpr (hvalue r s hrs))
      have hnot : ¬s < r := not_lt_of_gt hrs
      have heq :
          t r s + t s r =
            ((q * q) ^ (r : ℕ) * q ^ ((s : ℕ) - 1) -
              (q * q) ^ (s : ℕ) * q ^ (r : ℕ)) *
              (value r - value s) := by
        simp [t, candidateRankConditionalGapTerm, hrs, hnot]
        ring
      exact if_pos hlt ▸ by
        rw [heq]
        exact mul_nonneg hcoeff hgap
    · simp [hlt]

theorem candidateRankCrossConditionalGapSum_pos
    (n : ℕ) {qA qH : ℝ} (hqA_pos : 0 < qA) (hq_lt : qA < qH)
    (hqH_lt_one : qH < 1) {B : Candidate n → ℝ} (hB : StrictAnti B)
    (hH :
      0 < ∑ r : Candidate n, (qH * qH) ^ (r : ℕ) * B r) :
    0 < ∑ r : Candidate n,
      qH ^ (r : ℕ) * candidateRankCrossDelta n qA qH r * B r := by
  classical
  let A : ℝ := ∑ r : Candidate n, (qA * qH) ^ (r : ℕ) * B r
  let H : ℝ := ∑ r : Candidate n, (qH * qH) ^ (r : ℕ) * B r
  let P : ℝ := candidateRankPowerSum n (qA * qH)
  let Q : ℝ := candidateRankPowerSum n (qH * qH)
  let SA : ℝ := candidateRankPowerSum n qA
  let SH : ℝ := candidateRankPowerSum n qH
  have hqH_pos : 0 < qH := lt_trans hqA_pos hq_lt
  have hqAH_pos : 0 < qA * qH := mul_pos hqA_pos hqH_pos
  have hqHH_pos : 0 < qH * qH := mul_pos hqH_pos hqH_pos
  have hqAH_lt_qHH : qA * qH < qH * qH :=
    mul_lt_mul_of_pos_right hq_lt hqH_pos
  have hQ_pos : 0 < Q := by
    exact candidateRankPowerSum_pos n hqHH_pos
  have hSH_pos : 0 < SH := by
    exact candidateRankPowerSum_pos n hqH_pos
  have hE : 0 < Q * A - P * H := by
    simpa [A, H, P, Q] using
      candidateRankWeightedAverage_strictAnti n hqAH_pos hqAH_lt_qHH hB
  have hcoll : 0 < SH * P - SA * Q := by
    simpa [P, Q, SA, SH] using
      candidateRankCollisionWeight_cross_pos n hqA_pos hq_lt hqH_lt_one
  have hH' : 0 < H := by
    simpa [H] using hH
  have htarget : 0 < SH * A - SA * H := by
    have hE_lt : P * H < Q * A := sub_pos.mp hE
    have hcoll_lt : SA * Q < SH * P := sub_pos.mp hcoll
    have h1 : SH * (P * H) < SH * (Q * A) :=
      mul_lt_mul_of_pos_left hE_lt hSH_pos
    have h2 : SA * Q * H < SH * P * H :=
      mul_lt_mul_of_pos_right hcoll_lt hH'
    have h1' : SH * P * H < SH * (Q * A) := by
      nlinarith [h1]
    have hchain : SA * Q * H < SH * (Q * A) := by
      exact lt_trans h2 h1'
    have hQtarget : 0 < Q * (SH * A - SA * H) := by
      have heq : Q * (SH * A - SA * H) = SH * (Q * A) - SA * Q * H := by
        ring
      rw [heq]
      exact sub_pos.mpr hchain
    exact (mul_pos_iff_of_pos_left hQ_pos).mp hQtarget
  have hsum_eq :
      (∑ r : Candidate n,
        qH ^ (r : ℕ) * candidateRankCrossDelta n qA qH r * B r) =
        SH * A - SA * H := by
    unfold A H SA SH
    unfold candidateRankCrossDelta
    calc
      (∑ r : Candidate n,
        qH ^ (r : ℕ) *
            (qA ^ (r : ℕ) * candidateRankPowerSum n qH -
              qH ^ (r : ℕ) * candidateRankPowerSum n qA) * B r)
          =
          ∑ r : Candidate n,
            (candidateRankPowerSum n qH * ((qA * qH) ^ (r : ℕ) * B r) -
              candidateRankPowerSum n qA * ((qH * qH) ^ (r : ℕ) * B r)) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [mul_pow, mul_pow]
            ring
      _ =
          candidateRankPowerSum n qH *
              (∑ r : Candidate n, (qA * qH) ^ (r : ℕ) * B r) -
            candidateRankPowerSum n qA *
              (∑ r : Candidate n, (qH * qH) ^ (r : ℕ) * B r) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hsum_eq]
  exact htarget

theorem candidateRankPrefix_cross_pos
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    (k : Fin (n + 1)) :
    0 < candidateRankPrefixPowerSum n q₁ k * candidateRankPowerSum n q₂ -
      candidateRankPrefixPowerSum n q₂ k * candidateRankPowerSum n q₁ := by
  classical
  let t : Candidate n → Candidate n → ℝ := fun i j =>
    if (i : ℕ) ≤ k.val then
      q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
        q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ)
    else
      0
  have hdouble :
      candidateRankPrefixPowerSum n q₁ k * candidateRankPowerSum n q₂ -
        candidateRankPrefixPowerSum n q₂ k * candidateRankPowerSum n q₁ =
        ∑ i : Candidate n, ∑ j : Candidate n, t i j := by
    unfold candidateRankPrefixPowerSum candidateRankPowerSum
    rw [Finset.sum_mul, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hi : (i : ℕ) ≤ k.val
    · simp [t, hi]
    · simp [t, hi]
  rw [hdouble]
  rw [MallowsSpec.pair_sum_eq_ordered_swap_sum (Equiv.refl (Candidate n)) t
    (by
      intro i
      by_cases hi : (i : ℕ) ≤ k.val
      · simp [t, hi]
        ring
      · simp [t, hi])]
  let j₀ : Candidate n := ⟨k.val + 1, by omega⟩
  apply DecisionCore.sum_univ_pos_of_pos_of_nonneg
    (f := fun i : Candidate n =>
      ∑ j : Candidate n,
        if rankOf (Equiv.refl (Candidate n)) i <
            rankOf (Equiv.refl (Candidate n)) j then
          t i j + t j i
        else 0)
    (a₀ := (0 : Candidate n))
  · apply DecisionCore.sum_univ_pos_of_pos_of_nonneg
      (f := fun j : Candidate n =>
        if rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
            rankOf (Equiv.refl (Candidate n)) j then
          t (0 : Candidate n) j + t j (0 : Candidate n)
        else 0)
      (a₀ := j₀)
    · have hj₀_lt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) j₀ := by
        change (0 : ℕ) < k.val + 1
        omega
      have h0_prefix : ((0 : Candidate n) : ℕ) ≤ k.val := Nat.zero_le k.val
      have hj₀_not_prefix : ¬((j₀ : Candidate n) : ℕ) ≤ k.val := by
        intro h
        exact Nat.not_succ_le_self k.val h
      have hterm :
          0 < t (0 : Candidate n) j₀ + t j₀ (0 : Candidate n) := by
        have hpow : q₁ ^ (j₀ : ℕ) < q₂ ^ (j₀ : ℕ) := by
          exact pow_lt_pow_left₀ hq_lt (le_of_lt hq₁_pos)
            (by simp [j₀])
        simp [t, hj₀_not_prefix]
        exact hpow
      simpa [hj₀_lt] using hterm
    · intro j
      by_cases hlt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) j
      · have hnonneg : 0 ≤ t (0 : Candidate n) j + t j (0 : Candidate n) := by
          by_cases hj : (j : ℕ) ≤ k.val
          · have h0 : ((0 : Candidate n) : ℕ) ≤ k.val := Nat.zero_le k.val
            simp [t, hj]
          · have h0 : ((0 : Candidate n) : ℕ) ≤ k.val := Nat.zero_le k.val
            have hpow : q₁ ^ (j : ℕ) ≤ q₂ ^ (j : ℕ) :=
              pow_le_pow_left₀ (le_of_lt hq₁_pos) (le_of_lt hq_lt) (j : ℕ)
            simp [t, hj]
            exact hpow
        exact if_pos hlt ▸ hnonneg
      · simp [hlt]
  · intro i
    apply Finset.sum_nonneg
    intro j _
    by_cases hlt : rankOf (Equiv.refl (Candidate n)) i <
        rankOf (Equiv.refl (Candidate n)) j
    · have hnonneg : 0 ≤ t i j + t j i := by
        by_cases hi : (i : ℕ) ≤ k.val
        · by_cases hj : (j : ℕ) ≤ k.val
          · simp [t, hi, hj]
            ring_nf
            exact (show (0 : ℝ) ≤ 0 from le_rfl)
          · simp [t, hi, hj]
            have hij : i < j := by
              simpa [rankOf] using hlt
            have hpow := rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hij
            have hpow' :
                q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ) <
                  q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hpow
            exact le_of_lt hpow'
        · have hj : ¬(j : ℕ) ≤ k.val := by
            intro hj
            exact hi (le_trans (le_of_lt hlt) hj)
          simp [t, hi, hj]
      exact if_pos hlt ▸ hnonneg
    · simp [hlt]

theorem candidateRankWeightedPrefix_cross_pos
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁)
    (hq_lt : q₁ < q₂) (hq₂_lt_one : q₂ < 1)
    (k : Fin (n + 1)) :
    0 < ∑ i : Candidate n,
      if (i : ℕ) ≤ k.val then
        q₂ ^ (i : ℕ) * candidateRankCrossDelta n q₁ q₂ i
      else
        0 := by
  classical
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  let t : Candidate n → Candidate n → ℝ := fun i j =>
    if (i : ℕ) ≤ k.val then
      q₂ ^ (i : ℕ) *
        (q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
          q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ))
    else
      0
  have hdouble :
      (∑ i : Candidate n,
        if (i : ℕ) ≤ k.val then
          q₂ ^ (i : ℕ) * candidateRankCrossDelta n q₁ q₂ i
        else
          0) =
        ∑ i : Candidate n, ∑ j : Candidate n, t i j := by
    unfold candidateRankCrossDelta candidateRankPowerSum
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases hi : (i : ℕ) ≤ k.val
    · simp [t, hi]
      rw [mul_sub]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      congr 1
      calc
        q₂ ^ (i : ℕ) * (q₂ ^ (i : ℕ) * ∑ j : Candidate n, q₁ ^ (j : ℕ))
            = q₂ ^ (i : ℕ) *
                (∑ j : Candidate n, q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ)) := by
              rw [Finset.mul_sum]
        _ = ∑ j : Candidate n,
              q₂ ^ (i : ℕ) * (q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ)) := by
              simpa using
                (Finset.mul_sum (s := (Finset.univ : Finset (Candidate n)))
                  (f := fun j : Candidate n => q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ))
                  (a := q₂ ^ (i : ℕ)))
    · simp [t, hi]
  rw [hdouble]
  rw [MallowsSpec.pair_sum_eq_ordered_swap_sum (Equiv.refl (Candidate n)) t
    (by
      intro i
      by_cases hi : (i : ℕ) ≤ k.val
      · have hzero :
            q₁ ^ (i : ℕ) * q₂ ^ (i : ℕ) -
              q₂ ^ (i : ℕ) * q₁ ^ (i : ℕ) = 0 := by
          ring
        simp [t, hi, hzero]
      · simp [t, hi])]
  let j₀ : Candidate n := ⟨k.val + 1, by omega⟩
  apply DecisionCore.sum_univ_pos_of_pos_of_nonneg
    (f := fun i : Candidate n =>
      ∑ j : Candidate n,
        if rankOf (Equiv.refl (Candidate n)) i <
            rankOf (Equiv.refl (Candidate n)) j then
          t i j + t j i
        else 0)
    (a₀ := (0 : Candidate n))
  · apply DecisionCore.sum_univ_pos_of_pos_of_nonneg
      (f := fun j : Candidate n =>
        if rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
            rankOf (Equiv.refl (Candidate n)) j then
          t (0 : Candidate n) j + t j (0 : Candidate n)
        else 0)
      (a₀ := j₀)
    · have hj₀_lt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) j₀ := by
        change (0 : ℕ) < k.val + 1
        omega
      have hj₀_not_prefix : ¬((j₀ : Candidate n) : ℕ) ≤ k.val := by
        intro h
        exact Nat.not_succ_le_self k.val h
      have hpow : q₁ ^ (j₀ : ℕ) < q₂ ^ (j₀ : ℕ) :=
        pow_lt_pow_left₀ hq_lt (le_of_lt hq₁_pos) (by simp [j₀])
      have hterm :
          0 < t (0 : Candidate n) j₀ + t j₀ (0 : Candidate n) := by
        simp [t, hj₀_not_prefix]
        exact hpow
      simpa [hj₀_lt] using hterm
    · intro j
      by_cases hlt : rankOf (Equiv.refl (Candidate n)) (0 : Candidate n) <
          rankOf (Equiv.refl (Candidate n)) j
      · have hnonneg :
            0 ≤ t (0 : Candidate n) j + t j (0 : Candidate n) := by
          by_cases hj : (j : ℕ) ≤ k.val
          · have h0j : (0 : Candidate n) < j := by
              simpa [rankOf] using hlt
            simpa [t, hj] using
              weightedRankPower_pair_add_nonneg
                hq₁_pos hq_lt hq₂_lt_one h0j
          · have hpow : q₁ ^ (j : ℕ) ≤ q₂ ^ (j : ℕ) :=
              pow_le_pow_left₀ (le_of_lt hq₁_pos) (le_of_lt hq_lt) (j : ℕ)
            simp [t, hj]
            exact hpow
        exact if_pos hlt ▸ hnonneg
      · simp [hlt]
  · intro i
    apply Finset.sum_nonneg
    intro j _
    by_cases hlt : rankOf (Equiv.refl (Candidate n)) i <
        rankOf (Equiv.refl (Candidate n)) j
    · have hij : i < j := by
        simpa [rankOf] using hlt
      have hnonneg : 0 ≤ t i j + t j i := by
        by_cases hi : (i : ℕ) ≤ k.val
        · by_cases hj : (j : ℕ) ≤ k.val
          · simpa [t, hi, hj] using
              weightedRankPower_pair_add_nonneg
                hq₁_pos hq_lt hq₂_lt_one hij
          · have hpow :=
              rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hij
            have hinner :
                0 ≤ q₁ ^ (i : ℕ) * q₂ ^ (j : ℕ) -
                    q₂ ^ (i : ℕ) * q₁ ^ (j : ℕ) := by
              exact sub_nonneg.mpr (le_of_lt (by
                simpa [mul_comm, mul_left_comm, mul_assoc] using hpow))
            have hscale : 0 ≤ q₂ ^ (i : ℕ) :=
              pow_nonneg (le_of_lt hq₂_pos) (i : ℕ)
            simp [t, hi, hj]
            exact mul_nonneg hscale hinner
        · have hj : ¬(j : ℕ) ≤ k.val := by
            intro hj
            exact hi (le_trans (le_of_lt hlt) hj)
          simp [t, hi, hj]
      exact if_pos hlt ▸ hnonneg
    · simp [hlt]

theorem candidateRankWeightedPrefixCrossDeltaSum_pos
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁)
    (hq_lt : q₁ < q₂) (hq₂_lt_one : q₂ < 1)
    {k : ℕ} (hk : k < n + 1) :
    0 < candidateRankWeightedPrefixCrossDeltaSum n q₁ q₂ k := by
  simpa [candidateRankWeightedPrefixCrossDeltaSum] using
    candidateRankWeightedPrefix_cross_pos n hq₁_pos hq_lt hq₂_lt_one
      (⟨k, hk⟩ : Fin (n + 1))

theorem candidateRankCrossDelta_scaled_strictAnti
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂)
    {i j : Candidate n} (hij : i < j) :
    q₂ ^ (i : ℕ) * candidateRankCrossDelta n q₁ q₂ j <
      q₂ ^ (j : ℕ) * candidateRankCrossDelta n q₁ q₂ i := by
  have hpow := rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hij
  unfold candidateRankCrossDelta
  have hsum_pos : 0 < candidateRankPowerSum n q₂ :=
    candidateRankPowerSum_pos n (lt_trans hq₁_pos hq_lt)
  have hcore :
      q₂ ^ (i : ℕ) * (q₁ ^ (j : ℕ) * candidateRankPowerSum n q₂) <
        q₂ ^ (j : ℕ) * (q₁ ^ (i : ℕ) * candidateRankPowerSum n q₂) := by
    nlinarith [mul_lt_mul_of_pos_right hpow hsum_pos]
  nlinarith

theorem candidateRankCrossDelta_last_neg
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂) :
    candidateRankCrossDelta n q₁ q₂ (⟨n + 1, by omega⟩ : Candidate n) < 0 := by
  classical
  let last : Candidate n := ⟨n + 1, by omega⟩
  have hpos :
      0 < q₂ ^ (last : ℕ) * candidateRankPowerSum n q₁ -
        q₁ ^ (last : ℕ) * candidateRankPowerSum n q₂ := by
    have hsum :
        q₂ ^ (last : ℕ) * candidateRankPowerSum n q₁ -
          q₁ ^ (last : ℕ) * candidateRankPowerSum n q₂ =
          ∑ j : Candidate n,
            (q₂ ^ (last : ℕ) * q₁ ^ (j : ℕ) -
              q₁ ^ (last : ℕ) * q₂ ^ (j : ℕ)) := by
      unfold candidateRankPowerSum
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [hsum]
    apply DecisionCore.sum_univ_pos_of_pos_of_nonneg (a₀ := (0 : Candidate n))
    · have hlt : (0 : Candidate n) < last := by
        change (0 : ℕ) < n + 1
        omega
      have hpow := rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hlt
      exact sub_pos.mpr (by
        simpa [last, mul_comm, mul_left_comm, mul_assoc] using hpow)
    · intro j
      by_cases hj : j = last
      · subst j
        have hzero :
            q₂ ^ (last : ℕ) * q₁ ^ (last : ℕ) -
              q₁ ^ (last : ℕ) * q₂ ^ (last : ℕ) = 0 := by
          ring
        rw [hzero]
      · have hlt : j < last := by
          change (j : ℕ) < n + 1
          have hj_le : (j : ℕ) ≤ n + 1 := Nat.le_of_lt_succ j.isLt
          have hj_ne : (j : ℕ) ≠ n + 1 := by
            intro h
            exact hj (Fin.ext h)
          omega
        have hpow := rankPower_mul_lt_mul_rankPower hq₁_pos hq_lt hlt
        exact sub_nonneg.mpr (le_of_lt (by
          simpa [last, mul_comm, mul_left_comm, mul_assoc] using hpow))
  unfold candidateRankCrossDelta
  nlinarith

theorem candidateRankWeightedSuffixCrossDeltaSum_last_neg
    (n : ℕ) {q₁ q₂ : ℝ} (hq₁_pos : 0 < q₁) (hq_lt : q₁ < q₂) :
    candidateRankWeightedSuffixCrossDeltaSum n q₁ q₂ n < 0 := by
  classical
  let last : Candidate n := ⟨n + 1, by omega⟩
  have hsum :
      candidateRankWeightedSuffixCrossDeltaSum n q₁ q₂ n =
        q₂ ^ (last : ℕ) * candidateRankCrossDelta n q₁ q₂ last := by
    unfold candidateRankWeightedSuffixCrossDeltaSum
    rw [Finset.sum_eq_single last]
    · simp [last]
    · intro s _ hs_ne
      have hs_not : ¬n < (s : ℕ) := by
        intro hs
        have hs_eq : (s : ℕ) = n + 1 := by
          have hs_le : (s : ℕ) ≤ n + 1 := Nat.le_of_lt_succ s.isLt
          omega
        exact hs_ne (Fin.ext hs_eq)
      simp [hs_not]
    · intro hlast
      exact False.elim (hlast (Finset.mem_univ last))
  have hq₂_pos : 0 < q₂ := lt_trans hq₁_pos hq_lt
  rw [hsum]
  exact mul_neg_of_pos_of_neg (pow_pos hq₂_pos (last : ℕ))
    (candidateRankCrossDelta_last_neg n hq₁_pos hq_lt)

theorem candidateRankPrefixWeightSum_nonneg
    (n : ℕ) {q : ℝ} (hq_nonneg : 0 ≤ q) (k : ℕ) :
    0 ≤ candidateRankPrefixWeightSum n q k := by
  classical
  unfold candidateRankPrefixWeightSum
  apply Finset.sum_nonneg
  intro r _
  by_cases hr : (r : ℕ) ≤ k
  · exact if_pos hr ▸ pow_nonneg hq_nonneg (r : ℕ)
  · simp [hr]

theorem candidateRankShiftedSuffixWeightSum_pos
    (n : ℕ) {q : ℝ} (hq_pos : 0 < q) {k : ℕ} (hk : k < n + 1) :
    0 < candidateRankShiftedSuffixWeightSum n q k := by
  classical
  unfold candidateRankShiftedSuffixWeightSum
  let s₀ : Candidate n := ⟨k + 1, by omega⟩
  apply DecisionCore.sum_univ_pos_of_pos_of_nonneg (a₀ := s₀)
  · have hs₀ : k < (s₀ : ℕ) := by
      simp [s₀]
    have hpow : 0 < q ^ ((s₀ : ℕ) - 1) :=
      pow_pos hq_pos ((s₀ : ℕ) - 1)
    simpa [hs₀] using hpow
  · intro s
    by_cases hs : k < (s : ℕ)
    · exact if_pos hs ▸ le_of_lt (pow_pos hq_pos ((s : ℕ) - 1))
    · simp [hs]

theorem candidateRankAdjacentCoeff_eq_prefix_suffix
    (n : ℕ) (qA qH : ℝ) (k : ℕ) :
    candidateRankAdjacentCoeff n qA qH k =
      candidateRankShiftedSuffixWeightSum n qH k *
          candidateRankWeightedPrefixCrossDeltaSum n qA qH k -
        candidateRankPrefixWeightSum n qH k *
          candidateRankWeightedSuffixCrossDeltaSum n qA qH k := by
  classical
  let Δ : Candidate n → ℝ := fun r =>
    candidateRankCrossDelta n qA qH r
  let U : Candidate n → ℝ := fun s =>
    if k < (s : ℕ) then qH ^ ((s : ℕ) - 1) else 0
  let P : Candidate n → ℝ := fun r =>
    if (r : ℕ) ≤ k then qH ^ (r : ℕ) * Δ r else 0
  let Q : Candidate n → ℝ := fun r =>
    if (r : ℕ) ≤ k then qH ^ (r : ℕ) else 0
  let T : Candidate n → ℝ := fun s =>
    if k < (s : ℕ) then qH ^ (s : ℕ) * Δ s else 0
  unfold candidateRankAdjacentCoeff candidateRankShiftedSuffixWeightSum
    candidateRankWeightedPrefixCrossDeltaSum candidateRankPrefixWeightSum
    candidateRankWeightedSuffixCrossDeltaSum
  change (∑ r : Candidate n, ∑ s : Candidate n,
      if (r : ℕ) ≤ k ∧ k < (s : ℕ) then
        qH ^ ((r : ℕ) + (s : ℕ) - 1) *
          (Δ r - qH * Δ s)
      else
        0) =
    (∑ s : Candidate n, U s) * (∑ r : Candidate n, P r) -
      (∑ r : Candidate n, Q r) * (∑ s : Candidate n, T s)
  symm
  calc
    (∑ s : Candidate n, U s) * (∑ r : Candidate n, P r) -
        (∑ r : Candidate n, Q r) * (∑ s : Candidate n, T s)
        = ∑ r : Candidate n, ∑ s : Candidate n,
            (U s * P r - Q r * T s) := by
          rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
          rw [Finset.sum_comm]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [← Finset.sum_sub_distrib]
    _ = ∑ r : Candidate n, ∑ s : Candidate n,
          if (r : ℕ) ≤ k ∧ k < (s : ℕ) then
            qH ^ ((r : ℕ) + (s : ℕ) - 1) *
              (Δ r - qH * Δ s)
          else
            0 := by
          refine Finset.sum_congr rfl ?_
          intro r _
          refine Finset.sum_congr rfl ?_
          intro s _
          by_cases hr : (r : ℕ) ≤ k
          · by_cases hs : k < (s : ℕ)
            · have hs_pos : 0 < (s : ℕ) := lt_of_le_of_lt (Nat.zero_le k) hs
              have hsplit :
                  (r : ℕ) + (s : ℕ) - 1 =
                    (r : ℕ) + ((s : ℕ) - 1) := by
                omega
              have hs_pred : (s : ℕ) - 1 + 1 = (s : ℕ) := by
                omega
              have hpow_s : qH ^ (s : ℕ) =
                  qH ^ ((s : ℕ) - 1) * qH := by
                rw [← pow_succ, hs_pred]
              simp [U, P, Q, T, hr, hs]
              rw [hsplit, pow_add]
              rw [hpow_s]
              ring
            · have hspan : ¬((r : ℕ) ≤ k ∧ k < (s : ℕ)) := by
                intro h
                exact hs h.2
              simp [U, P, Q, T, hr, hs]
          · simp [U, P, Q, T, hr]

theorem candidateRankAdjacentCoeff_pos_of_suffix_nonpos
    (n : ℕ) {qA qH : ℝ} (hqA_pos : 0 < qA)
    (hq_lt : qA < qH) (hqH_lt_one : qH < 1)
    {k : ℕ} (hk : k < n + 1)
    (hsuffix :
      candidateRankWeightedSuffixCrossDeltaSum n qA qH k ≤ 0) :
    0 < candidateRankAdjacentCoeff n qA qH k := by
  have hqH_pos : 0 < qH := lt_trans hqA_pos hq_lt
  have hprefix :
      0 < candidateRankWeightedPrefixCrossDeltaSum n qA qH k :=
    candidateRankWeightedPrefixCrossDeltaSum_pos n hqA_pos hq_lt hqH_lt_one hk
  have hsuffixWeight :
      0 < candidateRankShiftedSuffixWeightSum n qH k :=
    candidateRankShiftedSuffixWeightSum_pos n hqH_pos hk
  have hprefixWeight :
      0 ≤ candidateRankPrefixWeightSum n qH k :=
    candidateRankPrefixWeightSum_nonneg n (le_of_lt hqH_pos) k
  rw [candidateRankAdjacentCoeff_eq_prefix_suffix]
  nlinarith [mul_pos hsuffixWeight hprefix,
    mul_nonpos_of_nonneg_of_nonpos hprefixWeight hsuffix]

namespace MallowsComparison

variable {n : ℕ} (C : MallowsComparison n)

theorem centerFirstWeight_cross_lt_of_rankFactorization
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
      C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition := by
  have hsum_lt :
      candidateRankPowerSum n C.algorithm.q <
        candidateRankPowerSum n C.human.q :=
    candidateRankPowerSum_strict_mono n
      (le_of_lt C.algorithm.q_pos) hq_lt
  have halg_first :
      C.algorithm.firstWeight C.algorithm.centerFirst = halg_rank.firstTail := by
    rw [halg_rank.firstWeight_eq]
    simp [MallowsSpec.centerFirst, rankOf]
  have hhuman_first :
      C.human.firstWeight C.human.centerFirst = hhuman_rank.firstTail := by
    rw [hhuman_rank.firstWeight_eq]
    simp [MallowsSpec.centerFirst, rankOf]
  rw [halg_rank.partition_eq, hhuman_rank.partition_eq, halg_first, hhuman_first]
  calc
    hhuman_rank.firstTail *
          (candidateRankPowerSum n C.algorithm.q * halg_rank.firstTail)
        = halg_rank.firstTail * hhuman_rank.firstTail *
            candidateRankPowerSum n C.algorithm.q := by ring
    _ < halg_rank.firstTail * hhuman_rank.firstTail *
            candidateRankPowerSum n C.human.q := by
          exact mul_lt_mul_of_pos_left hsum_lt
            (mul_pos halg_rank.firstTail_pos hhuman_rank.firstTail_pos)
    _ = halg_rank.firstTail *
          (candidateRankPowerSum n C.human.q * hhuman_rank.firstTail) := by ring

theorem centerFirstProb_lt_of_rankFactorization
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    firstChoiceProb C.human.law C.human.centerFirst <
      firstChoiceProb C.algorithm.law C.human.centerFirst := by
  exact C.centerFirstProb_lt_of_centerFirstWeight_div_lt
    (C.centerFirstWeight_div_lt_of_cross_mul_lt
      (C.centerFirstWeight_cross_lt_of_rankFactorization
        halg_rank hhuman_rank hq_lt))

theorem firstWeightPrefix_cross_lt_of_rankFactorization
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q)
    (k : Fin (n + 1)) :
    C.human.firstWeightPrefix k * C.algorithm.partition <
      C.algorithm.firstWeightPrefix k * C.human.partition := by
  have hprefix :
      0 < candidateRankPrefixPowerSum n C.algorithm.q k *
            candidateRankPowerSum n C.human.q -
          candidateRankPrefixPowerSum n C.human.q k *
            candidateRankPowerSum n C.algorithm.q :=
    candidateRankPrefix_cross_pos n C.algorithm.q_pos hq_lt k
  have hprefix_lt :
      candidateRankPrefixPowerSum n C.human.q k *
          candidateRankPowerSum n C.algorithm.q <
        candidateRankPrefixPowerSum n C.algorithm.q k *
          candidateRankPowerSum n C.human.q := by
    exact sub_pos.mp hprefix
  rw [C.algorithm.firstWeightPrefix_eq_rankPrefixPowerSum_mul halg_rank k,
    C.human.firstWeightPrefix_eq_rankPrefixPowerSum_mul hhuman_rank k,
    halg_rank.partition_eq, hhuman_rank.partition_eq]
  calc
    (candidateRankPrefixPowerSum n C.human.q k * hhuman_rank.firstTail) *
          (candidateRankPowerSum n C.algorithm.q * halg_rank.firstTail)
        = halg_rank.firstTail * hhuman_rank.firstTail *
            (candidateRankPrefixPowerSum n C.human.q k *
              candidateRankPowerSum n C.algorithm.q) := by ring
    _ < halg_rank.firstTail * hhuman_rank.firstTail *
            (candidateRankPrefixPowerSum n C.algorithm.q k *
              candidateRankPowerSum n C.human.q) := by
          exact mul_lt_mul_of_pos_left hprefix_lt
            (mul_pos halg_rank.firstTail_pos hhuman_rank.firstTail_pos)
    _ = (candidateRankPrefixPowerSum n C.algorithm.q k * halg_rank.firstTail) *
          (candidateRankPowerSum n C.human.q * hhuman_rank.firstTail) := by ring

theorem weaker_center_cross_product_pos_of_rankFactorization
    {value : Candidate n → ℝ}
    (hvalue : C.StrictlyCenterOrdered value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    0 < (C.algorithm.firstWeight C.human.centerFirst * C.human.partition -
        C.human.firstWeight C.human.centerFirst * C.algorithm.partition) *
      firstChoiceGapMass C.human.law value C.human.centerFirst := by
  exact C.weaker_center_cross_product_pos_of_strictlyCenterOrdered hvalue
    (C.centerFirstWeight_cross_lt_of_rankFactorization
      halg_rank hhuman_rank hq_lt)

theorem weaker_center_cross_weight_summand_pos_of_rankFactorization
    {value : Candidate n → ℝ}
    (hvalue : C.StrictlyCenterOrdered value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    0 < (C.algorithm.firstWeight C.human.centerFirst * C.human.partition -
        C.human.firstWeight C.human.centerFirst * C.algorithm.partition) *
      C.human.firstChoiceGapWeight value C.human.centerFirst := by
  have hcross :
      C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
        C.algorithm.firstWeight C.human.centerFirst * C.human.partition := by
    simpa [C.algorithm_centerFirst_eq_human_centerFirst] using
      C.centerFirstWeight_cross_lt_of_rankFactorization
        halg_rank hhuman_rank hq_lt
  have hdiff :
      0 < C.algorithm.firstWeight C.human.centerFirst * C.human.partition -
        C.human.firstWeight C.human.centerFirst * C.algorithm.partition :=
    sub_pos.mpr hcross
  have hhuman_value : StrictlyOrderedBy C.human.center value := by
    rw [← C.same_center]
    exact hvalue
  exact mul_pos hdiff
    (C.human.centerFirstGapWeight_pos_of_strictlyOrderedCenter hhuman_value)

/-- The ordered-pair summand in the cleared weaker-competition numerator. -/
noncomputable def crossPairTerm
    (value : Candidate n → ℝ) (c d : Candidate n) : ℝ :=
  (C.algorithm.firstWeight c * C.human.partition -
      C.human.firstWeight c * C.algorithm.partition) *
    C.human.firstSecondWeight c d * (value c - value d)

/--
The antisymmetrized ordered-pair bracket for the cleared weaker-competition
numerator.
-/
noncomputable def crossPairBracket (c d : Candidate n) : ℝ :=
  (C.algorithm.firstWeight c * C.human.partition -
      C.human.firstWeight c * C.algorithm.partition) *
    C.human.firstSecondWeight c d -
  (C.algorithm.firstWeight d * C.human.partition -
      C.human.firstWeight d * C.algorithm.partition) *
    C.human.firstSecondWeight d c

@[simp] theorem crossPairTerm_apply
    (value : Candidate n → ℝ) (c d : Candidate n) :
    C.crossPairTerm value c d =
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstSecondWeight c d * (value c - value d) := rfl

@[simp] theorem crossPairBracket_apply (c d : Candidate n) :
    C.crossPairBracket c d =
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstSecondWeight c d -
      (C.algorithm.firstWeight d * C.human.partition -
          C.human.firstWeight d * C.algorithm.partition) *
        C.human.firstSecondWeight d c := rfl

/--
Top-two expansion of the cleared weaker-competition numerator.
-/
theorem cross_weight_sum_eq_pair_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c) =
      ∑ c : Candidate n, ∑ d : Candidate n,
        C.crossPairTerm value c d := by
  classical
  calc
    ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c
        = ∑ c : Candidate n,
            (C.algorithm.firstWeight c * C.human.partition -
                C.human.firstWeight c * C.algorithm.partition) *
              (∑ d : Candidate n,
                C.human.firstSecondWeight c d * (value c - value d)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [C.human.firstChoiceGapWeight_eq_sum_firstSecondWeight value c]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
        (C.algorithm.firstWeight c * C.human.partition -
            C.human.firstWeight c * C.algorithm.partition) *
          (C.human.firstSecondWeight c d * (value c - value d)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.mul_sum]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
        C.crossPairTerm value c d := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro d _
          unfold crossPairTerm
          ring

/--
Pairing the ordered weaker-competition top-two events `(c,d)` and `(d,c)`
produces one cross bracket times the value difference.
-/
theorem crossPairTerm_add_swap
    (value : Candidate n → ℝ) (c d : Candidate n) :
    C.crossPairTerm value c d + C.crossPairTerm value d c =
      C.crossPairBracket c d * (value c - value d) := by
  unfold crossPairTerm crossPairBracket
  ring

/-- Coefficient on the adjacent center-rank gap between positions `k` and `k+1`. -/
noncomputable def crossAdjacentCoeff (k : ℕ) : ℝ :=
  ∑ c : Candidate n, ∑ d : Candidate n,
    if (rankOf C.human.center c).val ≤ k ∧
        k < (rankOf C.human.center d).val then
      C.crossPairBracket c d
    else
      0

theorem crossAdjacentCoeff_eq_rankFactorization
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (k : ℕ) :
    C.crossAdjacentCoeff k =
      halg_rank.firstTail * hhuman_rank.firstTail * hhuman_rank.firstSecondTail *
        candidateRankAdjacentCoeff n C.algorithm.q C.human.q k := by
  classical
  unfold crossAdjacentCoeff candidateRankAdjacentCoeff
  let scale : ℝ :=
    halg_rank.firstTail * hhuman_rank.firstTail * hhuman_rank.firstSecondTail
  let R : Candidate n → Candidate n → ℝ := fun r s =>
    C.human.q ^ ((r : ℕ) + (s : ℕ) - 1) *
      (candidateRankCrossDelta n C.algorithm.q C.human.q r -
        C.human.q * candidateRankCrossDelta n C.algorithm.q C.human.q s)
  let G : Candidate n → Candidate n → ℝ := fun c d =>
    if (rankOf C.human.center c).val ≤ k ∧
        k < (rankOf C.human.center d).val then
      C.crossPairBracket c d
    else
      0
  change (∑ c : Candidate n, ∑ d : Candidate n, G c d) =
    scale * (∑ r : Candidate n, ∑ s : Candidate n,
      if (r : ℕ) ≤ k ∧ k < (s : ℕ) then R r s else 0)
  have hreindex :
      (∑ c : Candidate n, ∑ d : Candidate n, G c d) =
        ∑ r : Candidate n, ∑ s : Candidate n,
          G (C.human.center r) (C.human.center s) := by
    calc
      (∑ c : Candidate n, ∑ d : Candidate n, G c d)
          = ∑ r : Candidate n, ∑ d : Candidate n,
              G (C.human.center r) d := by
            simpa using
              (Equiv.sum_comp C.human.center.symm
                (fun r : Candidate n =>
                  ∑ d : Candidate n, G (C.human.center r) d))
      _ = ∑ r : Candidate n, ∑ s : Candidate n,
              G (C.human.center r) (C.human.center s) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            simpa using
              (Equiv.sum_comp C.human.center.symm
                (fun s : Candidate n =>
                  G (C.human.center r) (C.human.center s)))
  calc
    (∑ c : Candidate n, ∑ d : Candidate n, G c d)
        = ∑ r : Candidate n, ∑ s : Candidate n,
            G (C.human.center r) (C.human.center s) := hreindex
    _ = ∑ r : Candidate n, ∑ s : Candidate n,
          if (r : ℕ) ≤ k ∧ k < (s : ℕ) then scale * R r s else 0 := by
        refine Finset.sum_congr rfl ?_
        intro r _
        refine Finset.sum_congr rfl ?_
        intro s _
        by_cases hspan : (r : ℕ) ≤ k ∧ k < (s : ℕ)
        · have hrs : r < s := by
            change (r : ℕ) < (s : ℕ)
            exact lt_of_le_of_lt hspan.1 hspan.2
          have hspan_center :
              (rankOf C.human.center (C.human.center r)).val ≤ k ∧
                k < (rankOf C.human.center (C.human.center s)).val := by
            simpa [rankOf] using hspan
          have halg_first_r :
              C.algorithm.firstWeight (C.human.center r) =
                C.algorithm.q ^ (r : ℕ) * halg_rank.firstTail := by
            rw [halg_rank.firstWeight_eq]
            simp [rankOf, C.same_center]
          have halg_first_s :
              C.algorithm.firstWeight (C.human.center s) =
                C.algorithm.q ^ (s : ℕ) * halg_rank.firstTail := by
            rw [halg_rank.firstWeight_eq]
            simp [rankOf, C.same_center]
          have hhuman_first_r :
              C.human.firstWeight (C.human.center r) =
                C.human.q ^ (r : ℕ) * hhuman_rank.firstTail := by
            rw [hhuman_rank.firstWeight_eq]
            simp [rankOf]
          have hhuman_first_s :
              C.human.firstWeight (C.human.center s) =
                C.human.q ^ (s : ℕ) * hhuman_rank.firstTail := by
            rw [hhuman_rank.firstWeight_eq]
            simp [rankOf]
          have hhuman_second_rs :
              C.human.firstSecondWeight (C.human.center r) (C.human.center s) =
                C.human.q ^ ((r : ℕ) + (s : ℕ) - 1) *
                  hhuman_rank.firstSecondTail := by
            rw [hhuman_rank.firstSecondWeight_eq_of_lt]
            · simp [rankOf]
            · simpa [rankOf] using hrs
          have hhuman_second_sr :
              C.human.firstSecondWeight (C.human.center s) (C.human.center r) =
                C.human.q *
                  (C.human.q ^ ((r : ℕ) + (s : ℕ) - 1) *
                    hhuman_rank.firstSecondTail) := by
            rw [hhuman_rank.firstSecondWeight_swap_eq_of_lt]
            · simp [rankOf]
            · simpa [rankOf] using hrs
          simp [G, hspan_center, hspan]
          rw [halg_first_r, halg_first_s, hhuman_first_r, hhuman_first_s,
            halg_rank.partition_eq, hhuman_rank.partition_eq,
            hhuman_second_rs, hhuman_second_sr]
          dsimp [scale, R, candidateRankCrossDelta]
          ring
        · have hspan_center :
              ¬((rankOf C.human.center (C.human.center r)).val ≤ k ∧
                k < (rankOf C.human.center (C.human.center s)).val) := by
            simpa [rankOf] using hspan
          simp [G, hspan_center, hspan]
    _ = scale * (∑ r : Candidate n, ∑ s : Candidate n,
          if (r : ℕ) ≤ k ∧ k < (s : ℕ) then R r s else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro r _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro s _
        by_cases hspan : (r : ℕ) ≤ k ∧ k < (s : ℕ) <;>
          simp [hspan]

theorem crossAdjacentCoeff_pos_of_rankFactorization_and_suffix_nonpos
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q)
    (hhuman_q_lt_one : C.human.q < 1)
    {k : ℕ} (hk : k ∈ Finset.range (n + 1))
    (hsuffix :
      candidateRankWeightedSuffixCrossDeltaSum n C.algorithm.q C.human.q k ≤ 0) :
    0 < C.crossAdjacentCoeff k := by
  have hcoeff :
      0 < candidateRankAdjacentCoeff n C.algorithm.q C.human.q k :=
    candidateRankAdjacentCoeff_pos_of_suffix_nonpos n
      C.algorithm.q_pos hq_lt hhuman_q_lt_one (Finset.mem_range.mp hk) hsuffix
  rw [C.crossAdjacentCoeff_eq_rankFactorization halg_rank hhuman_rank k]
  exact mul_pos
    (mul_pos (mul_pos halg_rank.firstTail_pos hhuman_rank.firstTail_pos)
      hhuman_rank.firstSecondTail_pos)
    hcoeff

theorem cross_ordered_bracket_sum_eq_adjacent_coeff_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n, ∑ d : Candidate n,
      if rankOf C.human.center c < rankOf C.human.center d then
        C.crossPairBracket c d * (value c - value d)
      else 0) =
      ∑ k ∈ Finset.range (n + 1),
        C.crossAdjacentCoeff k *
          centerAdjacentGapAt C.human.center value k := by
  classical
  calc
    (∑ c : Candidate n, ∑ d : Candidate n,
      if rankOf C.human.center c < rankOf C.human.center d then
        C.crossPairBracket c d * (value c - value d)
      else 0)
        = ∑ c : Candidate n, ∑ d : Candidate n,
            ∑ k ∈ Finset.range (n + 1),
              if (rankOf C.human.center c).val ≤ k ∧
                  k < (rankOf C.human.center d).val then
                C.crossPairBracket c d *
                  centerAdjacentGapAt C.human.center value k
              else
                0 := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro d _
          by_cases hlt : rankOf C.human.center c < rankOf C.human.center d
          · have hgap := value_sub_eq_sum_centerAdjacentGapAt
              C.human.center value hlt
            have hrange :
                (Finset.range (n + 1)).filter
                    (fun k =>
                      (rankOf C.human.center c).val ≤ k ∧
                        k < (rankOf C.human.center d).val) =
                  Finset.Ico (rankOf C.human.center c).val
                    (rankOf C.human.center d).val := by
              ext k
              constructor
              · intro hk
                have hk' := Finset.mem_filter.mp hk
                exact Finset.mem_Ico.mpr hk'.2
              · intro hk
                have hk' := Finset.mem_Ico.mp hk
                have hd_le : (rankOf C.human.center d).val ≤ n + 1 := by
                  omega
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_range.mpr (lt_of_lt_of_le hk'.2 hd_le), hk'⟩
            calc
              (if rankOf C.human.center c < rankOf C.human.center d then
                  C.crossPairBracket c d * (value c - value d)
                else 0)
                  = C.crossPairBracket c d * (value c - value d) := by
                    simp [hlt]
              _ = C.crossPairBracket c d *
                    (∑ k ∈ Finset.Ico (rankOf C.human.center c).val
                      (rankOf C.human.center d).val,
                      centerAdjacentGapAt C.human.center value k) := by
                    rw [hgap]
              _ = ∑ k ∈ Finset.Ico (rankOf C.human.center c).val
                    (rankOf C.human.center d).val,
                    C.crossPairBracket c d *
                      centerAdjacentGapAt C.human.center value k := by
                    rw [Finset.mul_sum]
              _ = ∑ k ∈ Finset.range (n + 1),
                    if (rankOf C.human.center c).val ≤ k ∧
                        k < (rankOf C.human.center d).val then
                      C.crossPairBracket c d *
                        centerAdjacentGapAt C.human.center value k
                    else
                      0 := by
                    rw [← hrange]
                    rw [Finset.sum_filter]
          · have hempty :
                (Finset.range (n + 1)).filter
                    (fun k =>
                      (rankOf C.human.center c).val ≤ k ∧
                        k < (rankOf C.human.center d).val) = ∅ := by
              ext k
              simp only [Finset.mem_filter, Finset.mem_range]
              constructor
              · intro hk
                exfalso
                apply hlt
                change (rankOf C.human.center c).val <
                  (rankOf C.human.center d).val
                exact lt_of_le_of_lt hk.2.1 hk.2.2
              · intro h
                simpa using h
            simp [hlt, ← Finset.sum_filter, hempty]
    _ = ∑ k ∈ Finset.range (n + 1), ∑ c : Candidate n, ∑ d : Candidate n,
          if (rankOf C.human.center c).val ≤ k ∧
              k < (rankOf C.human.center d).val then
            C.crossPairBracket c d *
              centerAdjacentGapAt C.human.center value k
          else
            0 := by
          calc
            (∑ c : Candidate n, ∑ d : Candidate n,
                ∑ k ∈ Finset.range (n + 1),
                  if (rankOf C.human.center c).val ≤ k ∧
                      k < (rankOf C.human.center d).val then
                    C.crossPairBracket c d *
                      centerAdjacentGapAt C.human.center value k
                  else
                    0)
                = ∑ c : Candidate n, ∑ k ∈ Finset.range (n + 1),
                    ∑ d : Candidate n,
                      if (rankOf C.human.center c).val ≤ k ∧
                          k < (rankOf C.human.center d).val then
                        C.crossPairBracket c d *
                          centerAdjacentGapAt C.human.center value k
                      else
                        0 := by
                  refine Finset.sum_congr rfl ?_
                  intro c _
                  rw [Finset.sum_comm]
            _ = ∑ k ∈ Finset.range (n + 1), ∑ c : Candidate n, ∑ d : Candidate n,
                  if (rankOf C.human.center c).val ≤ k ∧
                      k < (rankOf C.human.center d).val then
                    C.crossPairBracket c d *
                      centerAdjacentGapAt C.human.center value k
                  else
                    0 := by
                  rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (n + 1),
          C.crossAdjacentCoeff k *
            centerAdjacentGapAt C.human.center value k := by
          refine Finset.sum_congr rfl ?_
          intro k _
          unfold crossAdjacentCoeff
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro d _
          by_cases hspan :
              (rankOf C.human.center c).val ≤ k ∧
                k < (rankOf C.human.center d).val <;>
            simp [hspan]

theorem crossPairTerm_add_swap_nonneg
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hbracket : 0 ≤ C.crossPairBracket c d)
    (hvalue : value d ≤ value c) :
    0 ≤ C.crossPairTerm value c d + C.crossPairTerm value d c := by
  rw [C.crossPairTerm_add_swap value c d]
  exact mul_nonneg hbracket (sub_nonneg.mpr hvalue)

theorem crossPairTerm_add_swap_pos
    {value : Candidate n → ℝ} {c d : Candidate n}
    (hbracket : 0 < C.crossPairBracket c d)
    (hvalue : value d < value c) :
    0 < C.crossPairTerm value c d + C.crossPairTerm value d c := by
  rw [C.crossPairTerm_add_swap value c d]
  exact mul_pos hbracket (sub_pos.mpr hvalue)

/--
The cleared weaker-competition pair sum regrouped over center-ordered unordered
pairs for the human Mallows center.
-/
theorem cross_pair_sum_eq_ordered_swap_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n, ∑ d : Candidate n,
        C.crossPairTerm value c d) =
      ∑ c : Candidate n, ∑ d : Candidate n,
        if rankOf C.human.center c < rankOf C.human.center d then
          C.crossPairTerm value c d + C.crossPairTerm value d c
        else 0 := by
  refine MallowsSpec.pair_sum_eq_ordered_swap_sum C.human.center (C.crossPairTerm value) ?_
  intro c
  unfold crossPairTerm
  ring

theorem cross_weight_sum_eq_adjacent_coeff_sum
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c) =
      ∑ k ∈ Finset.range (n + 1),
        C.crossAdjacentCoeff k *
          centerAdjacentGapAt C.human.center value k := by
  calc
    (∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c)
        = ∑ c : Candidate n, ∑ d : Candidate n,
            C.crossPairTerm value c d := by
          rw [C.cross_weight_sum_eq_pair_sum value]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
          if rankOf C.human.center c < rankOf C.human.center d then
            C.crossPairTerm value c d + C.crossPairTerm value d c
          else 0 := by
          rw [C.cross_pair_sum_eq_ordered_swap_sum value]
    _ = ∑ c : Candidate n, ∑ d : Candidate n,
          if rankOf C.human.center c < rankOf C.human.center d then
            C.crossPairBracket c d * (value c - value d)
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro c _
          refine Finset.sum_congr rfl ?_
          intro d _
          by_cases hlt : rankOf C.human.center c < rankOf C.human.center d
          · rw [if_pos hlt, if_pos hlt]
            exact C.crossPairTerm_add_swap value c d
          · simp [hlt]
    _ = ∑ k ∈ Finset.range (n + 1),
          C.crossAdjacentCoeff k *
            centerAdjacentGapAt C.human.center value k := by
          rw [C.cross_ordered_bracket_sum_eq_adjacent_coeff_sum value]

theorem cross_weight_sum_pos_of_adjacent_coeff_pos
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy C.human.center value)
    (hcoeff : ∀ k ∈ Finset.range (n + 1), 0 < C.crossAdjacentCoeff k) :
    0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c := by
  rw [C.cross_weight_sum_eq_adjacent_coeff_sum value]
  refine Finset.sum_pos ?hpos ?hne
  · intro k hk
    have hklt : k < n + 1 := Finset.mem_range.mp hk
    have hk1 : k + 1 < n + 2 := by
      omega
    exact mul_pos (hcoeff k hk)
      (centerAdjacentGapAt_pos_of_strictlyOrderedBy hvalue hk1)
  · exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩

theorem cross_weight_sum_pos_of_rankFactorization_and_suffix_nonpos
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy C.human.center value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q)
    (hhuman_q_lt_one : C.human.q < 1)
    (hsuffix :
      ∀ k ∈ Finset.range (n + 1),
        candidateRankWeightedSuffixCrossDeltaSum n C.algorithm.q C.human.q k ≤ 0) :
    0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c := by
  exact C.cross_weight_sum_pos_of_adjacent_coeff_pos hvalue
    (fun k hk =>
      C.crossAdjacentCoeff_pos_of_rankFactorization_and_suffix_nonpos
        halg_rank hhuman_rank hq_lt hhuman_q_lt_one hk (hsuffix k hk))

theorem cross_weight_sum_pos_of_rankFactorization
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy C.human.center value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q)
    (hhuman_q_lt_one : C.human.q < 1) :
    0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c := by
  classical
  let B : Candidate n → ℝ := fun r =>
    candidateRankConditionalGap n C.human.q
      (fun s : Candidate n => value (C.human.center s)) r
  have hvalue_rank :
      ∀ i j : Candidate n, i < j →
        value (C.human.center j) < value (C.human.center i) := by
    intro i j hij
    exact hvalue (by simpa [rankOf] using hij)
  have hB : StrictAnti B := by
    dsimp [B]
    exact candidateRankConditionalGap_strictAnti n C.human.q_pos hvalue_rank
  have hH :
      0 < ∑ r : Candidate n,
        (C.human.q * C.human.q) ^ (r : ℕ) * B r := by
    simpa [B] using
      candidateRankSquareWeightedConditionalGap_pos n
        C.human.q_pos hhuman_q_lt_one hvalue_rank
  have hpure :
      0 < ∑ r : Candidate n,
        C.human.q ^ (r : ℕ) *
          candidateRankCrossDelta n C.algorithm.q C.human.q r * B r := by
    exact candidateRankCrossConditionalGapSum_pos n
      C.algorithm.q_pos hq_lt hhuman_q_lt_one hB hH
  let scale : ℝ :=
    halg_rank.firstTail * hhuman_rank.firstTail * hhuman_rank.firstSecondTail
  have hscale_pos : 0 < scale :=
    mul_pos (mul_pos halg_rank.firstTail_pos hhuman_rank.firstTail_pos)
      hhuman_rank.firstSecondTail_pos
  have hsum_eq :
      (∑ c : Candidate n,
        (C.algorithm.firstWeight c * C.human.partition -
            C.human.firstWeight c * C.algorithm.partition) *
          C.human.firstChoiceGapWeight value c) =
        scale * ∑ r : Candidate n,
          C.human.q ^ (r : ℕ) *
            candidateRankCrossDelta n C.algorithm.q C.human.q r * B r := by
    let F : Candidate n → ℝ := fun c =>
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c
    calc
      (∑ c : Candidate n, F c)
          = ∑ r : Candidate n, F (C.human.center r) := by
            simpa using
              (Equiv.sum_comp C.human.center (fun c : Candidate n => F c)).symm
      _ = ∑ r : Candidate n,
            scale *
              (C.human.q ^ (r : ℕ) *
                candidateRankCrossDelta n C.algorithm.q C.human.q r * B r) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            have halg_first :
                C.algorithm.firstWeight (C.human.center r) =
                  C.algorithm.q ^ (r : ℕ) * halg_rank.firstTail := by
              rw [halg_rank.firstWeight_eq]
              simp [rankOf, C.same_center]
            have hhuman_first :
                C.human.firstWeight (C.human.center r) =
                  C.human.q ^ (r : ℕ) * hhuman_rank.firstTail := by
              rw [hhuman_rank.firstWeight_eq]
              simp [rankOf]
            have hgap :
                C.human.firstChoiceGapWeight value (C.human.center r) =
                  C.human.q ^ (r : ℕ) * hhuman_rank.firstSecondTail * B r := by
              rw [C.human.firstChoiceGapWeight_eq_rankConditionalGap
                hhuman_rank value (C.human.center r)]
              simp [B, rankOf]
            simp [F, scale, candidateRankCrossDelta]
            rw [halg_first, hhuman_first, halg_rank.partition_eq,
              hhuman_rank.partition_eq, hgap]
            ring
      _ = scale * ∑ r : Candidate n,
            C.human.q ^ (r : ℕ) *
              candidateRankCrossDelta n C.algorithm.q C.human.q r * B r := by
            rw [Finset.mul_sum]
  rw [hsum_eq]
  exact mul_pos hscale_pos hpure

/--
Pairwise cross-bracket signs imply positivity of the cleared
weaker-competition numerator.
-/
theorem cross_weight_sum_pos_of_pair_brackets
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy C.human.center value)
    (hbracket_nonneg :
      ∀ c d : Candidate n, rankOf C.human.center c < rankOf C.human.center d →
        0 ≤ C.crossPairBracket c d)
    (hbracket_pos :
      ∃ c d : Candidate n, rankOf C.human.center c < rankOf C.human.center d ∧
        0 < C.crossPairBracket c d) :
    0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c := by
  classical
  rw [C.cross_weight_sum_eq_pair_sum value]
  rw [C.cross_pair_sum_eq_ordered_swap_sum value]
  rcases hbracket_pos with ⟨c₀, d₀, hlt₀, hbracket₀⟩
  apply DecisionCore.sum_univ_pos_of_pos_of_nonneg
    (f := fun c : Candidate n =>
      ∑ d : Candidate n,
        if rankOf C.human.center c < rankOf C.human.center d then
          C.crossPairTerm value c d + C.crossPairTerm value d c
        else 0)
    (a₀ := c₀)
  · apply DecisionCore.sum_univ_pos_of_pos_of_nonneg
      (f := fun d : Candidate n =>
        if rankOf C.human.center c₀ < rankOf C.human.center d then
          C.crossPairTerm value c₀ d + C.crossPairTerm value d c₀
        else 0)
      (a₀ := d₀)
    · have hpos := C.crossPairTerm_add_swap_pos
          (value := value) hbracket₀ (hvalue hlt₀)
      simpa [hlt₀, crossPairTerm] using hpos
    · intro d
      by_cases hlt : rankOf C.human.center c₀ < rankOf C.human.center d
      · exact if_pos hlt ▸
          C.crossPairTerm_add_swap_nonneg
            (value := value) (hbracket_nonneg c₀ d hlt)
            (le_of_lt (hvalue hlt))
      · simp [hlt]
  · intro c
    apply Finset.sum_nonneg
    intro d _
    by_cases hlt : rankOf C.human.center c < rankOf C.human.center d
    · exact if_pos hlt ▸
        C.crossPairTerm_add_swap_nonneg
          (value := value) (hbracket_nonneg c d hlt)
          (le_of_lt (hvalue hlt))
    · simp [hlt]

/--
Appendix-E/F pair-bracket certificate for the finite Mallows sums.

This replaces the three total finite-sum assumptions by local ordered-pair
bracket inequalities.
-/
structure CenterMallowsPairBracketCertificate
    (value : Candidate n → ℝ) : Prop where
  strictly_center_ordered : C.StrictlyCenterOrdered value
  algorithm_bracket_nonneg :
    ∀ c d : Candidate n, rankOf C.algorithm.center c < rankOf C.algorithm.center d →
      0 ≤ C.algorithm.independentPairBracket c d
  algorithm_bracket_pos :
    ∃ c d : Candidate n, rankOf C.algorithm.center c < rankOf C.algorithm.center d ∧
      0 < C.algorithm.independentPairBracket c d
  human_bracket_nonneg :
    ∀ c d : Candidate n, rankOf C.human.center c < rankOf C.human.center d →
      0 ≤ C.human.independentPairBracket c d
  human_bracket_pos :
    ∃ c d : Candidate n, rankOf C.human.center c < rankOf C.human.center d ∧
      0 < C.human.independentPairBracket c d
  cross_bracket_nonneg :
    ∀ c d : Candidate n, rankOf C.human.center c < rankOf C.human.center d →
      0 ≤ C.crossPairBracket c d
  cross_bracket_pos :
    ∃ c d : Candidate n, rankOf C.human.center c < rankOf C.human.center d ∧
      0 < C.crossPairBracket c d

/--
Pair-bracket signs instantiate the existing cleared finite-sum Mallows
certificate.
-/
theorem centerMallowsFiniteSumCertificate_of_pairBracketCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsPairBracketCertificate value) :
    C.CenterMallowsFiniteSumCertificate value := by
  have hhuman_value : StrictlyOrderedBy C.human.center value := by
    rw [← C.same_center]
    exact cert.strictly_center_ordered
  constructor
  · exact cert.strictly_center_ordered
  · exact C.algorithm.independent_weight_sum_pos_of_pair_brackets
      cert.strictly_center_ordered
      cert.algorithm_bracket_nonneg
      cert.algorithm_bracket_pos
  · exact C.human.independent_weight_sum_pos_of_pair_brackets
      hhuman_value
      cert.human_bracket_nonneg
      cert.human_bracket_pos
  · exact C.cross_weight_sum_pos_of_pair_brackets
      hhuman_value
      cert.cross_bracket_nonneg
      cert.cross_bracket_pos

/--
Pair-bracket signs imply the pointwise Mallows paper hypotheses.
-/
theorem theorem3_pointwise_of_centerMallowsPairBracketCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsPairBracketCertificate value) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.theorem3_pointwise_of_centerMallowsFiniteSumCertificate
    (C.centerMallowsFiniteSumCertificate_of_pairBracketCertificate cert)

/--
Rank-factorized Mallows first/top-two formulas discharge the two
independent-reranking finite sums. The weaker-competition cleared finite sum is
kept explicit because its proof needs the separate Mallows majorization
argument.
-/
theorem centerMallowsFiniteSumCertificate_of_rankFactorization_and_crossWeight
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hn : 0 < n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hweaker : 0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c) :
    C.CenterMallowsFiniteSumCertificate value := by
  have hhuman_value : StrictlyOrderedBy C.human.center value := by
    rw [← C.same_center]
    exact hstrict
  constructor
  · exact hstrict
  · exact C.algorithm.independent_weight_sum_pos_of_rankFactorization
      halg_rank hn halg_q_lt_one hstrict
  · exact C.human.independent_weight_sum_pos_of_rankFactorization
      hhuman_rank hn hhuman_q_lt_one hhuman_value
  · exact hweaker

/--
Rank-factorized Mallows first/top-two formulas discharge all three cleared
finite Mallows sums, including the weaker-competition sum via the paper's
conditional-gap/MLR argument.
-/
theorem centerMallowsFiniteSumCertificate_of_rankFactorization
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hn : 0 < n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hq_lt : C.algorithm.q < C.human.q) :
    C.CenterMallowsFiniteSumCertificate value := by
  have hhuman_value : StrictlyOrderedBy C.human.center value := by
    rw [← C.same_center]
    exact hstrict
  exact C.centerMallowsFiniteSumCertificate_of_rankFactorization_and_crossWeight
    hstrict hn halg_rank hhuman_rank halg_q_lt_one hhuman_q_lt_one
    (C.cross_weight_sum_pos_of_rankFactorization
      hhuman_value halg_rank hhuman_rank hq_lt hhuman_q_lt_one)

/--
Paper-hypothesis theorem with independent-reranking finite sums proved from
rank factorization; only the weaker-competition finite Mallows inequality
remains explicit.
-/
theorem theorem3_pointwise_of_rankFactorization_and_crossWeight
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hn : 0 < n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hweaker : 0 < ∑ c : Candidate n,
      (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        C.human.firstChoiceGapWeight value c) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.theorem3_pointwise_of_centerMallowsFiniteSumCertificate
    (C.centerMallowsFiniteSumCertificate_of_rankFactorization_and_crossWeight
      hstrict hn halg_rank hhuman_rank halg_q_lt_one hhuman_q_lt_one hweaker)

/--
Paper-hypothesis theorem with all three finite Mallows inequalities proved from
rank factorization.
-/
theorem theorem3_pointwise_of_rankFactorization
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hn : 0 < n)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hq_lt : C.algorithm.q < C.human.q) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.theorem3_pointwise_of_centerMallowsFiniteSumCertificate
    (C.centerMallowsFiniteSumCertificate_of_rankFactorization
      hstrict hn halg_rank hhuman_rank halg_q_lt_one hhuman_q_lt_one hq_lt)

end MallowsComparison

end Monoculture
