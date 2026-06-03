import EconCSLib.SocialChoice.Ranking.Mallows
import EconCSLib.SocialChoice.Ranking.RankPower

/-!
# Mallows Rank Factorization

Assumption-driven rank-factorization API for finite Mallows laws.  Concrete
papers may construct this package from source-specific fiber decompositions;
the algebra in this file only consumes the package.
-/

open scoped BigOperators

namespace EconCSLib
namespace SocialChoice
namespace Ranking

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

/--
Under the rank factorization, the first-choice tail is the top-two tail times
the rank-power partition of the remaining candidates after any fixed candidate
is removed from first position.
-/
theorem firstTail_eq_firstSecondTail_mul_removalPowerSum
    (fac : M.RankFactorization) (c : Candidate n) :
    fac.firstTail =
      fac.firstSecondTail *
        candidateRankRemovalPowerSum n M.q (rankOf M.center c) := by
  classical
  let k : Candidate n := rankOf M.center c
  have hc_center : M.center k = c := by
    simp [k, rankOf]
  have hsum_center :
      (∑ r : Candidate n, M.firstSecondWeight c (M.center r)) =
        M.firstWeight c := by
    have hcomp :
        (∑ r : Candidate n, M.firstSecondWeight c (M.center r)) =
          ∑ d : Candidate n, M.firstSecondWeight c d := by
      simpa using
        (Equiv.sum_comp M.center
          (fun d : Candidate n => M.firstSecondWeight c d))
    rw [hcomp, M.sum_firstSecondWeight_right_eq_firstWeight c]
  have hleft :
      (∑ r : Candidate n, M.firstSecondWeight c (M.center r)) =
        M.q ^ (k : ℕ) * fac.firstSecondTail *
          candidateRankRemovalPowerSum n M.q k := by
    unfold candidateRankRemovalPowerSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _
    by_cases hrk : r < k
    · have hlt : rankOf M.center (M.center r) < rankOf M.center c := by
        simpa [k, rankOf] using hrk
      have hpow :
          M.q *
              (M.q ^ ((r : ℕ) + (k : ℕ) - 1) *
                fac.firstSecondTail) =
            M.q ^ (k : ℕ) * fac.firstSecondTail * M.q ^ (r : ℕ) := by
        have hsum :
            ((r : ℕ) + (k : ℕ) - 1) + 1 = (k : ℕ) + (r : ℕ) := by
          have hrk_nat : (r : ℕ) < (k : ℕ) := hrk
          omega
        rw [← mul_assoc M.q (M.q ^ ((r : ℕ) + (k : ℕ) - 1))
          fac.firstSecondTail]
        rw [← pow_succ', hsum, pow_add]
        ring
      rw [fac.firstSecondWeight_swap_eq_of_lt (M.center r) c hlt]
      rw [← hc_center]
      have hrk' : r < rankOf M.center c := by
        simpa [k] using hrk
      rw [if_pos hrk']
      simp [rankOf]
      exact hpow
    · by_cases hkr : k < r
      · have hlt : rankOf M.center c < rankOf M.center (M.center r) := by
          simpa [k, rankOf] using hkr
        have hpow :
            M.q ^ ((k : ℕ) + (r : ℕ) - 1) * fac.firstSecondTail =
              M.q ^ (k : ℕ) * fac.firstSecondTail * M.q ^ ((r : ℕ) - 1) := by
          have hsum :
              (k : ℕ) + (r : ℕ) - 1 = (k : ℕ) + ((r : ℕ) - 1) := by
            have hkr_nat : (k : ℕ) < (r : ℕ) := hkr
            omega
          rw [hsum, pow_add]
          ring
        rw [fac.firstSecondWeight_eq_of_lt c (M.center r) hlt]
        have hkr' : rankOf M.center c < r := by
          simpa [k] using hkr
        have hrk' : ¬r < rankOf M.center c := by
          simpa [k] using hrk
        rw [if_neg hrk', if_pos hkr']
        simp [rankOf]
        exact hpow
      · have hr_eq : r = k := le_antisymm (le_of_not_gt hkr) (le_of_not_gt hrk)
        subst r
        have hself : M.firstSecondWeight c c = 0 := by
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
        simpa [hc_center] using hself
  have hright :
      M.firstWeight c = M.q ^ (k : ℕ) * fac.firstTail := by
    rw [fac.firstWeight_eq c]
  have hqk : M.q ^ (k : ℕ) ≠ 0 := ne_of_gt (pow_pos M.q_pos (k : ℕ))
  have hmain :
      M.q ^ (k : ℕ) *
          (fac.firstSecondTail * candidateRankRemovalPowerSum n M.q k) =
        M.q ^ (k : ℕ) * fac.firstTail := by
    calc
      M.q ^ (k : ℕ) *
          (fac.firstSecondTail * candidateRankRemovalPowerSum n M.q k)
          = M.q ^ (k : ℕ) * fac.firstSecondTail *
              candidateRankRemovalPowerSum n M.q k := by ring
      _ = (∑ r : Candidate n, M.firstSecondWeight c (M.center r)) := by
            rw [hleft]
      _ = M.firstWeight c := hsum_center
      _ = M.q ^ (k : ℕ) * fac.firstTail := hright
  exact (mul_left_cancel₀ hqk hmain).symm

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

end MallowsSpec

end Ranking
end SocialChoice
end EconCSLib
