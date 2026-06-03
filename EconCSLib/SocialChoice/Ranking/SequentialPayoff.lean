import EconCSLib.SocialChoice.Ranking.Payoff
import EconCSLib.SocialChoice.Ranking.Sequential

/-!
# Sequential Payoffs for Ranking Laws

Expected values for the best candidate in a finite feasible set.  This is the
PMF/payoff companion to `Ranking.Sequential`, which keeps the deterministic
best-in-set operations probability-free.
-/

namespace EconCSLib
namespace SocialChoice
namespace Ranking

noncomputable section

/-- Expected value of the best remaining candidate under a ranking law. -/
def expectedBestInSet {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (remaining : Finset (Candidate n)) : ℝ :=
  pmfExp μ (fun π => value (bestInSet π remaining))

/-- Expected value of the best candidate after removing one candidate. -/
def expectedBestAfterRemoval {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (c : Candidate n) : ℝ :=
  pmfExp μ (fun π => value (bestRemainingAfter π c))

@[simp] theorem expectedBestInSet_univ {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedBestInSet μ value Finset.univ =
      expectedFirstMoverUtility μ value := by
  unfold expectedBestInSet expectedFirstMoverUtility
  exact pmfExp_congr μ (fun π => by simp)

theorem expectedBestInSet_univ_sdiff_singleton {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n) :
    expectedBestInSet μ value
        (Finset.univ \ ({c} : Finset (Candidate n))) =
      expectedBestAfterRemoval μ value c := by
  unfold expectedBestInSet expectedBestAfterRemoval
  exact pmfExp_congr μ (fun π => by
    rw [bestInSet_univ_sdiff_singleton])

@[simp] theorem expectedBestInSet_singleton {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (c : Candidate n) :
    expectedBestInSet μ value ({c} : Finset (Candidate n)) =
      value c := by
  unfold expectedBestInSet
  simp [pmfExp_const]

end

end Ranking
end SocialChoice
end EconCSLib
