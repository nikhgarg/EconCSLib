import Monoculture.MallowsFiniteLemmas
import Mathlib.Algebra.Ring.GeomSum

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

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

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

end MallowsComparison

end Monoculture
