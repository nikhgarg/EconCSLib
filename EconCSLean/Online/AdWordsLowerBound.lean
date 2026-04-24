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

theorem theorem9BidderSpendUpperBound_nonneg
    (N : ℕ) (bidder : Fin N) :
    0 ≤ theorem9BidderSpendUpperBound N bidder := by
  unfold theorem9BidderSpendUpperBound
  refine le_min zero_le_one ?_
  exact Finset.sum_nonneg fun round _ => by
    by_cases hround : (round : ℕ) ≤ (bidder : ℕ)
    · have hden_nonneg : 0 ≤ ((N - (round : ℕ) : ℕ) : ℝ) := by
        exact_mod_cast (Nat.zero_le (N - (round : ℕ)))
      simpa [hround] using one_div_nonneg.mpr hden_nonneg
    · simp [hround]

theorem theorem9BidderSpendUpperBound_le_one
    (N : ℕ) (bidder : Fin N) :
    theorem9BidderSpendUpperBound N bidder ≤ 1 := by
  unfold theorem9BidderSpendUpperBound
  exact min_le_left 1 _

theorem theorem9NormalizedRevenueUpperBound_nonneg (N : ℕ) :
    0 ≤ theorem9NormalizedRevenueUpperBound N := by
  unfold theorem9NormalizedRevenueUpperBound
  have hsum :
      0 ≤ ∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder :=
    Finset.sum_nonneg fun bidder _ =>
      theorem9BidderSpendUpperBound_nonneg N bidder
  have hden : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  exact div_nonneg hsum hden

theorem theorem9NormalizedRevenueUpperBound_le_one
    {N : ℕ} (hN : 0 < N) :
    theorem9NormalizedRevenueUpperBound N ≤ 1 := by
  unfold theorem9NormalizedRevenueUpperBound
  have hsum_le :
      (∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder) ≤
        ∑ _bidder : Fin N, (1 : ℝ) :=
    Finset.sum_le_sum fun bidder _ =>
      theorem9BidderSpendUpperBound_le_one N bidder
  have hsum_le_card :
      (∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder) ≤
        (N : ℝ) := by
    simpa using hsum_le
  have hN_real : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [div_le_iff₀ hN_real]
  simpa using hsum_le_card

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
then bounded by a requested finite ratio. For the paper theorem this ratio is
used as `msvvRatio + δ` before taking the large-market limit.
-/
structure BMatchingPermutationRevenueBoundCertificate
    (N : ℕ) (Algorithm : Type*) (ratio : ℝ) where
  normalizedRevenue : Algorithm → Equiv.Perm (Fin N) → ℝ
  deterministicAverage_le_revenueBound :
    ∀ algorithm,
      pmfExp (uniformPermutationDistribution N)
          (fun permutation => normalizedRevenue algorithm permutation) ≤
        theorem9NormalizedRevenueUpperBound N
  revenueBound_le_ratio :
    theorem9NormalizedRevenueUpperBound N ≤ ratio

/--
Round-allocation form of the Section 7 deterministic calculation. The field
`expectedRoundBidderAllocation_le` corresponds to the paper's
`E_pi[q_ij] <= 1 / (N - i + 1)` line, in zero-based indices.
-/
structure BMatchingRoundAllocationRevenueCertificate
    (N : ℕ) (Algorithm : Type*) (ratio : ℝ) where
  normalizedRevenue : Algorithm → Equiv.Perm (Fin N) → ℝ
  expectedRoundBidderAllocation : Algorithm → Fin N → Fin N → ℝ
  deterministicAverage_le_cappedExpectedSpend :
    ∀ algorithm,
      pmfExp (uniformPermutationDistribution N)
          (fun permutation => normalizedRevenue algorithm permutation) ≤
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              expectedRoundBidderAllocation algorithm round bidder)) / (N : ℝ)
  expectedRoundBidderAllocation_le :
    ∀ algorithm round bidder,
      expectedRoundBidderAllocation algorithm round bidder ≤
        if (round : ℕ) ≤ (bidder : ℕ) then
          1 / ((N - (round : ℕ) : ℕ) : ℝ)
        else
          0
  revenueBound_le_ratio :
    theorem9NormalizedRevenueUpperBound N ≤ ratio

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

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

/--
Convert the explicit finite revenue-bound certificate into the permutation
lower-bound certificate used by Yao's lemma.
-/
noncomputable def toPermutationLowerBoundCertificate
    (C : BMatchingPermutationRevenueBoundCertificate N Algorithm ratio) :
    RandomizedLowerBoundCertificate Algorithm (Equiv.Perm (Fin N)) ratio where
  normalizedRevenue := C.normalizedRevenue
  distribution := uniformPermutationDistribution N
  deterministicAverage_le := by
    intro algorithm
    exact (C.deterministicAverage_le_revenueBound algorithm).trans
      C.revenueBound_le_ratio

theorem no_randomized_algorithm_beats_ratio
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingPermutationRevenueBoundCertificate N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact
    C.toPermutationLowerBoundCertificate.no_strictly_better_randomized_algorithm
      randomizedAlgorithm

end BMatchingPermutationRevenueBoundCertificate

namespace BMatchingRoundAllocationRevenueCertificate

variable {N : ℕ} {Algorithm : Type*} {ratio : ℝ}

/--
The round-allocation inequalities imply the paper's harmonic revenue-bound
certificate.
-/
noncomputable def toRevenueBoundCertificate
    (C : BMatchingRoundAllocationRevenueCertificate N Algorithm ratio) :
    BMatchingPermutationRevenueBoundCertificate N Algorithm ratio where
  normalizedRevenue := C.normalizedRevenue
  deterministicAverage_le_revenueBound := by
    intro algorithm
    have hbidder :
        ∀ bidder : Fin N,
          min 1
              (∑ round : Fin N,
                C.expectedRoundBidderAllocation algorithm round bidder) ≤
            theorem9BidderSpendUpperBound N bidder := by
      intro bidder
      unfold theorem9BidderSpendUpperBound
      exact min_le_min_left 1
        (Finset.sum_le_sum fun round _ =>
          C.expectedRoundBidderAllocation_le algorithm round bidder)
    have hsum :
        (∑ bidder : Fin N,
          min 1
            (∑ round : Fin N,
              C.expectedRoundBidderAllocation algorithm round bidder)) ≤
        ∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder :=
      Finset.sum_le_sum fun bidder _ => hbidder bidder
    have hden : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
    exact (C.deterministicAverage_le_cappedExpectedSpend algorithm).trans
      (div_le_div_of_nonneg_right hsum hden)
  revenueBound_le_ratio := C.revenueBound_le_ratio

theorem no_randomized_algorithm_beats_ratio
    [Fintype Algorithm] [DecidableEq Algorithm]
    (C : BMatchingRoundAllocationRevenueCertificate N Algorithm ratio)
    (randomizedAlgorithm : PMF Algorithm) :
    ¬ ∀ permutation,
      ratio <
        pmfExp randomizedAlgorithm
          (fun algorithm => C.normalizedRevenue algorithm permutation) := by
  exact
    C.toRevenueBoundCertificate.no_randomized_algorithm_beats_ratio
      randomizedAlgorithm

end BMatchingRoundAllocationRevenueCertificate

end Online
end EconCSLean
