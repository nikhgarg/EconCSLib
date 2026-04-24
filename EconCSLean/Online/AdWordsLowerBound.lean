import EconCSLean.Online.AdWords
import EconCSLean.Decision.Yao
import Mathlib.Data.Fintype.Perm

/-!
# Lower-Bound Interface for AdWords and b-Matching

Section 7 of the MSVV paper uses Yao's lemma: a hard input distribution for
deterministic algorithms implies a worst-case input for every randomized
algorithm. This file records the finite certificate interface needed for that
argument.
-/

namespace EconCSLean
namespace Online

open DecisionCore

/--
A finite Yao certificate for a randomized lower bound.

`normalizedRevenue algorithm input` should be the algorithm's revenue on the
input divided by the offline benchmark for that input. The certificate says
that the chosen input distribution gives every deterministic algorithm average
normalized revenue at most `ratio`.
-/
structure RandomizedLowerBoundCertificate
    (Algorithm Input : Type*) [Fintype Input] [DecidableEq Input]
    (ratio : ℝ) where
  distribution : PMF Input
  normalizedRevenue : Algorithm → Input → ℝ
  deterministicAverage_le :
    ∀ algorithm,
      pmfExp distribution (fun input => normalizedRevenue algorithm input) ≤
        ratio

namespace RandomizedLowerBoundCertificate

variable {Algorithm Input : Type*} {ratio : ℝ}
variable [Fintype Algorithm] [DecidableEq Algorithm]
variable [Fintype Input] [DecidableEq Input] [Nonempty Input]

/--
Every randomized algorithm has an input where its expected normalized revenue
is at most the certificate ratio.
-/
theorem exists_input_randomized_normalizedRevenue_le
    (C : RandomizedLowerBoundCertificate Algorithm Input ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ∃ input,
      pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm input) ≤
        ratio := by
  exact
    Decision.exists_input_randomized_payoff_le_of_forall_deterministic_average_le
      C.distribution randomizedAlgorithm C.normalizedRevenue ratio
      C.deterministicAverage_le

/--
No randomized algorithm can have normalized revenue strictly above the
certificate ratio on every input.
-/
theorem no_strictly_better_randomized_algorithm
    (C : RandomizedLowerBoundCertificate Algorithm Input ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ input,
      ratio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm input) := by
  exact
    Decision.not_forall_input_bound_lt_randomized_payoff_of_forall_deterministic_average_le
      C.distribution randomizedAlgorithm C.normalizedRevenue ratio
      C.deterministicAverage_le

end RandomizedLowerBoundCertificate

/--
The Section 7 b-matching lower-bound certificate at the MSVV ratio `1 - 1/e`.
The paper's remaining construction work is to instantiate this certificate with
the random permutation distribution over round instances.
-/
abbrev BMatchingYaoLowerBoundCertificate
    (Algorithm Input : Type*) [Fintype Input] [DecidableEq Input] :=
  RandomizedLowerBoundCertificate Algorithm Input AdWordsInstance.msvvRatio

theorem bMatching_no_randomized_algorithm_beats_msvvRatio_of_certificate
    {Algorithm Input : Type*}
    [Fintype Algorithm] [DecidableEq Algorithm]
    [Fintype Input] [DecidableEq Input] [Nonempty Input]
    (C : BMatchingYaoLowerBoundCertificate Algorithm Input)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ input,
      AdWordsInstance.msvvRatio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm input) := by
  exact C.no_strictly_better_randomized_algorithm randomizedAlgorithm

/--
The paper's hard distribution chooses a permutation of the bidders uniformly.
The concrete b-matching instance for a permutation has round `i` adjacent to
permutation positions `i, i+1, ..., N-1`.
-/
noncomputable def uniformPermutationDistribution (N : ℕ) :
    PMF (Equiv.Perm (Fin N)) :=
  DecisionCore.uniformPMF (Equiv.Perm (Fin N))

/--
Section 7 per-bidder upper bound:
`min {1, sum_{i <= j} 1 / (N - i)}` using zero-based `Fin N` indices.
-/
noncomputable def theorem9BidderSpendUpperBound (N : ℕ) (bidder : Fin N) : ℝ :=
  min 1
    (∑ round : Fin N,
      if (round : ℕ) ≤ (bidder : ℕ) then
        1 / ((N - (round : ℕ) : ℕ) : ℝ)
      else
        0)

/--
The finite normalized revenue upper bound obtained by summing the Section 7
per-bidder spend caps and dividing by the offline optimum `N`.
-/
noncomputable def theorem9NormalizedRevenueUpperBound (N : ℕ) : ℝ :=
  (∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder) / (N : ℝ)

/--
Concrete Section 7 certificate specialized to the paper's uniform permutation
distribution. The remaining mathematical field is the paper's deterministic
average normalized-revenue bound for that distribution.
-/
structure BMatchingPermutationLowerBoundCertificate
    (N : ℕ) (Algorithm : Type*) where
  normalizedRevenue : Algorithm → Equiv.Perm (Fin N) → ℝ
  deterministicAverage_le :
    ∀ algorithm,
      pmfExp (uniformPermutationDistribution N)
          (fun permutation => normalizedRevenue algorithm permutation) ≤
        AdWordsInstance.msvvRatio

/--
More explicit Section 7 certificate: deterministic algorithms are first bounded
by the paper's finite harmonic spend-cap expression, and that expression is
then bounded by the MSVV ratio.
-/
structure BMatchingPermutationRevenueBoundCertificate
    (N : ℕ) (Algorithm : Type*) where
  normalizedRevenue : Algorithm → Equiv.Perm (Fin N) → ℝ
  deterministicAverage_le_revenueBound :
    ∀ algorithm,
      pmfExp (uniformPermutationDistribution N)
          (fun permutation => normalizedRevenue algorithm permutation) ≤
        theorem9NormalizedRevenueUpperBound N
  revenueBound_le_msvvRatio :
    theorem9NormalizedRevenueUpperBound N ≤ AdWordsInstance.msvvRatio

namespace BMatchingPermutationLowerBoundCertificate

variable {N : ℕ} {Algorithm : Type*}

/-- Convert the paper-specific permutation certificate into the generic Yao certificate. -/
noncomputable def toYaoCertificate
    (C : BMatchingPermutationLowerBoundCertificate N Algorithm) :
    BMatchingYaoLowerBoundCertificate Algorithm (Equiv.Perm (Fin N)) where
  distribution := uniformPermutationDistribution N
  normalizedRevenue := C.normalizedRevenue
  deterministicAverage_le := C.deterministicAverage_le

theorem no_randomized_algorithm_beats_msvvRatio
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingPermutationLowerBoundCertificate N Algorithm)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      AdWordsInstance.msvvRatio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact
    bMatching_no_randomized_algorithm_beats_msvvRatio_of_certificate
      C.toYaoCertificate randomizedAlgorithm

end BMatchingPermutationLowerBoundCertificate

namespace BMatchingPermutationRevenueBoundCertificate

variable {N : ℕ} {Algorithm : Type*}

/--
Convert the explicit finite revenue-bound certificate into the permutation
lower-bound certificate used by Yao's lemma.
-/
def toPermutationLowerBoundCertificate
    (C : BMatchingPermutationRevenueBoundCertificate N Algorithm) :
    BMatchingPermutationLowerBoundCertificate N Algorithm where
  normalizedRevenue := C.normalizedRevenue
  deterministicAverage_le := by
    intro algorithm
    exact (C.deterministicAverage_le_revenueBound algorithm).trans
      C.revenueBound_le_msvvRatio

theorem no_randomized_algorithm_beats_msvvRatio
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingPermutationRevenueBoundCertificate N Algorithm)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      AdWordsInstance.msvvRatio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact
    C.toPermutationLowerBoundCertificate.no_randomized_algorithm_beats_msvvRatio
      randomizedAlgorithm

end BMatchingPermutationRevenueBoundCertificate

end Online
end EconCSLean
