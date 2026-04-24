import Monoculture.MallowsPairwise
import Monoculture.Theorem1

/-!
# Parameterized Mallows Families

This file connects the fixed-parameter Mallows theorem to the family-level
Theorem 1 interface.  It packages the remaining Definition 1 analytic facts
separately from the fixed-parameter Mallows finite-sum proof of Definitions 2
and 3.
-/

namespace Monoculture

/-- Inverse Mallows parameter for the paper convention `θ = φ - 1`. -/
noncomputable def mallowsInverseAccuracyQ (θ : ℝ) : ℝ :=
  (θ + 1)⁻¹

theorem mallowsInverseAccuracyQ_pos {θ : ℝ} (hθ : 0 < θ) :
    0 < mallowsInverseAccuracyQ θ := by
  unfold mallowsInverseAccuracyQ
  exact inv_pos.mpr (by linarith)

theorem mallowsInverseAccuracyQ_lt_one {θ : ℝ} (hθ : 0 < θ) :
    mallowsInverseAccuracyQ θ < 1 := by
  unfold mallowsInverseAccuracyQ
  exact inv_lt_one_of_one_lt₀ (by linarith)

theorem mallowsInverseAccuracyQ_strictAnti {θA θH : ℝ}
    (hθH : 0 < θH) (hθ : θH < θA) :
    mallowsInverseAccuracyQ θA < mallowsInverseAccuracyQ θH := by
  unfold mallowsInverseAccuracyQ
  have hA : 0 < θA + 1 := by linarith
  have hH : 0 < θH + 1 := by linarith
  exact (inv_lt_inv₀ hA hH).2 (by linarith)

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/--
First-mover utility under a Mallows law is the rank-power weighted average of
candidate values in the center order.
-/
theorem expectedFirstMoverUtility_eq_rankAverage
    (fac : M.RankFactorization) (value : Candidate n → ℝ) :
    expectedFirstMoverUtility M.law value =
      (∑ r : Candidate n, M.q ^ (r : ℕ) * value (M.center r)) /
        candidateRankPowerSum n M.q := by
  classical
  rw [expectedFirstMoverUtility_eq_sum_firstChoiceProb]
  have hweight :
      (∑ c : Candidate n, M.firstWeight c * value c) =
        fac.firstTail *
          (∑ r : Candidate n, M.q ^ (r : ℕ) * value (M.center r)) := by
    calc
      ∑ c : Candidate n, M.firstWeight c * value c
          = ∑ c : Candidate n,
              (M.q ^ (rankOf M.center c : ℕ) * fac.firstTail) * value c := by
            refine Finset.sum_congr rfl ?_
            intro c _
            rw [fac.firstWeight_eq c]
      _ = ∑ c : Candidate n,
              fac.firstTail * (M.q ^ (rankOf M.center c : ℕ) * value c) := by
            refine Finset.sum_congr rfl ?_
            intro c _
            ring
      _ = fac.firstTail *
            (∑ c : Candidate n, M.q ^ (rankOf M.center c : ℕ) * value c) := by
            rw [Finset.mul_sum]
      _ = fac.firstTail *
            (∑ r : Candidate n, M.q ^ (r : ℕ) * value (M.center r)) := by
            congr 1
            simpa [rankOf] using
              (Equiv.sum_comp M.center
                (fun c : Candidate n =>
                  M.q ^ (rankOf M.center c : ℕ) * value c)).symm
  calc
    ∑ c : Candidate n, firstChoiceProb M.law c * value c
        = ∑ c : Candidate n, (M.firstWeight c / M.partition) * value c := by
            refine Finset.sum_congr rfl ?_
            intro c _
            rw [M.firstChoiceProb_eq_firstWeight_div_partition c]
    _ = (∑ c : Candidate n, M.firstWeight c * value c) / M.partition := by
            calc
              ∑ c : Candidate n, (M.firstWeight c / M.partition) * value c
                  = ∑ c : Candidate n, (M.firstWeight c * value c) / M.partition := by
                    refine Finset.sum_congr rfl ?_
                    intro c _
                    ring
              _ = (∑ c : Candidate n, M.firstWeight c * value c) / M.partition := by
                    rw [Finset.sum_div]
    _ = (fac.firstTail *
            (∑ r : Candidate n, M.q ^ (r : ℕ) * value (M.center r))) /
          (candidateRankPowerSum n M.q * fac.firstTail) := by
            rw [hweight, fac.partition_eq]
    _ = (∑ r : Candidate n, M.q ^ (r : ℕ) * value (M.center r)) /
          candidateRankPowerSum n M.q := by
            field_simp [ne_of_gt fac.firstTail_pos]

end MallowsSpec

namespace MallowsComparison

variable {n : ℕ} (C : MallowsComparison n)

/--
The Mallows rank-power MLR inequality proves the strict `S = ∅` part of
Definition 1 monotonicity: the more concentrated/lower-`q` law has higher
expected first choice when values strictly decrease down the common center.
-/
theorem firstMoverUtility_strict_of_rankFactorization
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (halg_rank : C.algorithm.RankFactorization)
    (hhuman_rank : C.human.RankFactorization)
    (hq_lt : C.algorithm.q < C.human.q) :
    expectedFirstMoverUtility C.human.law value <
      expectedFirstMoverUtility C.algorithm.law value := by
  classical
  let A : ℝ :=
    ∑ r : Candidate n, C.algorithm.q ^ (r : ℕ) * value (C.human.center r)
  let H : ℝ :=
    ∑ r : Candidate n, C.human.q ^ (r : ℕ) * value (C.human.center r)
  let SA : ℝ := candidateRankPowerSum n C.algorithm.q
  let SH : ℝ := candidateRankPowerSum n C.human.q
  have hB : StrictAnti (fun r : Candidate n => value (C.human.center r)) := by
    intro i j hij
    exact hstrict (by
      simpa [MallowsComparison.StrictlyCenterOrdered, rankOf, C.same_center] using hij)
  have hmain : 0 < SH * A - SA * H := by
    simpa [A, H, SA, SH] using
      candidateRankWeightedAverage_strictAnti
        n C.algorithm.q_pos hq_lt hB
  have hSA_pos : 0 < SA := by
    exact candidateRankPowerSum_pos n C.algorithm.q_pos
  have hSH_pos : 0 < SH := by
    exact candidateRankPowerSum_pos n C.human.q_pos
  have havg : H / SH < A / SA := by
    field_simp [ne_of_gt hSA_pos, ne_of_gt hSH_pos]
    nlinarith [hmain]
  rw [C.algorithm.expectedFirstMoverUtility_eq_rankAverage halg_rank value]
  rw [C.human.expectedFirstMoverUtility_eq_rankAverage hhuman_rank value]
  have halg_sum :
      (∑ r : Candidate n,
        C.algorithm.q ^ (r : ℕ) * value (C.algorithm.center r)) = A := by
    simp [A, C.same_center]
  have hhuman_sum :
      (∑ r : Candidate n,
        C.human.q ^ (r : ℕ) * value (C.human.center r)) = H := by
    simp [H]
  simpa [halg_sum, hhuman_sum, SA, SH] using havg

end MallowsComparison

/--
A one-parameter Mallows accuracy family with a common center ranking and a fixed
value vector.

The finite Mallows algebra in `MallowsPairwise` proves Definitions 2 and 3 from
the common-center ordering and `qA < qH`.  The fields here that remain after
that are the Definition 1 analytic/family facts used by Theorem 1: atomwise
continuity, asymptotic first-dominance in the proof's payoff notation, and the
singleton-removal weak monotonicity needed for the second mover.  The strict
`S = ∅` first-mover monotonicity is proved below from the Mallows rank-power
MLR inequality.
-/
structure MallowsAccuracyFamilySpec (n : ℕ) where
  value : Candidate n → ℝ
  center : Ranking n
  value_strict : StrictlyOrderedBy center value
  spec : ℝ → MallowsSpec n
  same_center : ∀ θ, (spec θ).center = center
  q_lt_one : ∀ θ, 0 < θ → (spec θ).q < 1
  q_strictAnti : ∀ θA θH, 0 < θH → θH < θA → (spec θA).q < (spec θH).q
  dist_atom_continuity :
    ∀ θ, 0 < θ →
      ∀ π : Ranking n, DecisionCore.EpsilonContinuousAt
        (fun θ' => (((spec θ').law) π).toReal) θ
  asymptotic_first_dominance :
    ∀ θH lower, 0 < θH → θH < lower →
      ∃ hi, lower < hi ∧
        AccuracyFamily.theorem1_g
            ({ dist := fun θ => (spec θ).law, value := value } : AccuracyFamily n)
            hi θH <
          AccuracyFamily.theorem1_f
            ({ dist := fun θ => (spec θ).law, value := value } : AccuracyFamily n)
            hi θH
  bestRemaining_weak :
    ∀ θA θH, 0 < θH → θH < θA →
      ∀ c : Candidate n,
        AccuracyFamily.expectedBestAfterRemoval (spec θH).law value c ≤
          AccuracyFamily.expectedBestAfterRemoval (spec θA).law value c

namespace MallowsAccuracyFamilySpec

variable {n : ℕ} (MF : MallowsAccuracyFamilySpec n)

/-- The `AccuracyFamily` induced by a parameterized Mallows family. -/
noncomputable def toAccuracyFamily : AccuracyFamily n where
  dist := fun θ => (MF.spec θ).law
  value := MF.value

/-- The fixed-parameter Mallows comparison induced by two accuracy parameters. -/
noncomputable def comparisonAt (θA θH : ℝ) : MallowsComparison n where
  algorithm := MF.spec θA
  human := MF.spec θH
  same_center := by
    rw [MF.same_center θA, MF.same_center θH]

@[simp] theorem comparisonAt_toModel (θA θH : ℝ) :
    (MF.comparisonAt θA θH).toModel MF.value =
      (MF.toAccuracyFamily).modelAt θA θH := by
  rfl

/-- The common center ordering gives the fixed-parameter Mallows ordering field. -/
theorem comparisonAt_strictlyCenterOrdered (θA θH : ℝ) :
    (MF.comparisonAt θA θH).StrictlyCenterOrdered MF.value := by
  unfold MallowsComparison.StrictlyCenterOrdered StrictlyOrderedBy
  intro a b h
  exact MF.value_strict (by
    simpa [comparisonAt, MF.same_center θA] using h)

/--
Mallows finite-sum algebra proves Definition 2 at every positive parameter.
-/
theorem prefersIndependentReranking
    (hn : 0 < n) (θ : ℝ) (hθ : 0 < θ) :
    Model.PrefersIndependentReranking ((MF.toAccuracyFamily).dist θ) MF.value := by
  let M := MF.spec θ
  have hvalue : StrictlyOrderedBy M.center MF.value := by
    intro a b h
    exact MF.value_strict (by
      simpa [M, MF.same_center θ] using h)
  have hcleared :
      0 < ∑ c : Candidate n,
        (M.partition - M.firstWeight c) *
          M.firstChoiceGapWeight MF.value c :=
    M.independent_weight_sum_pos_of_rankFactorization
      M.rankFactorization hn (MF.q_lt_one θ hθ) hvalue
  have hsum :
      0 < ∑ c : Candidate n,
        firstChoiceMissProb M.law c * firstChoiceGapMass M.law MF.value c :=
    M.firstChoice_miss_gap_sum_pos_of_weight_sum_pos hcleared
  exact (prefersIndependentReranking_iff_firstChoiceGapMassSum_pos
    (μ := M.law) (value := MF.value)).2 hsum

/--
The rank-factorized Mallows theorem proves Definition 3 for every
`θA > θH > 0`.
-/
theorem prefersWeakerCompetition
    (hn : 0 < n) (θA θH : ℝ) (hθH : 0 < θH) (hθ : θH < θA) :
    Model.PrefersWeakerCompetition
      ((MF.toAccuracyFamily).dist θA) ((MF.toAccuracyFamily).dist θH) MF.value := by
  let C := MF.comparisonAt θA θH
  have hstrict : C.StrictlyCenterOrdered MF.value := by
    intro a b h
    exact (MF.comparisonAt_strictlyCenterOrdered θA θH)
      (by simpa [C] using h)
  have hpaper : Model.PaperHypotheses (C.toModel MF.value) := by
    exact C.theorem3_pointwise_of_rankFactorization
      hstrict
      hn
      C.algorithm.rankFactorization
      C.human.rankFactorization
      (MF.q_lt_one θA (lt_trans hθH hθ))
      (MF.q_lt_one θH hθH)
      (MF.q_strictAnti θA θH hθH hθ)
  simpa [C, toAccuracyFamily, comparisonAt] using hpaper.2

/--
Mallows rank-power MLR proves the strict first-mover part of Definition 1
monotonicity for every `θA > θH > 0`.
-/
theorem firstMoverUtility_strict
    (hn : 0 < n) (θA θH : ℝ) (hθH : 0 < θH) (hθ : θH < θA) :
    expectedFirstMoverUtility (MF.spec θH).law MF.value <
      expectedFirstMoverUtility (MF.spec θA).law MF.value := by
  let C := MF.comparisonAt θA θH
  have hstrict : C.StrictlyCenterOrdered MF.value := by
    intro a b h
    exact (MF.comparisonAt_strictlyCenterOrdered θA θH)
      (by simpa [C] using h)
  have hmain := C.firstMoverUtility_strict_of_rankFactorization
    hstrict
    C.algorithm.rankFactorization
    C.human.rankFactorization
    (MF.q_strictAnti θA θH hθH hθ)
  simpa [C, comparisonAt] using hmain

/--
The remaining singleton-removal weak monotonicity field, together with the
proved Mallows first-mover strict monotonicity, gives the Theorem 1 removal
monotonicity certificate.
-/
theorem theorem1RemovalMonotonicityAt
    (hn : 0 < n) (θA θH : ℝ) (hθH : 0 < θH) (hθ : θH < θA) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt MF.toAccuracyFamily θA θH where
  firstMover_strict := by
    simpa [toAccuracyFamily] using
      MF.firstMoverUtility_strict hn θA θH hθH hθ
  bestRemaining_weak := by
    intro c
    simpa [toAccuracyFamily] using
      MF.bestRemaining_weak θA θH hθH hθ c

/--
The parameterized Mallows fields instantiate the paper-level assumptions for
Theorem 1. Definitions 2 and 3 are filled by the proved finite Mallows route;
the remaining fields are exactly the Definition 1 analytic obligations recorded
in `MallowsAccuracyFamilySpec`.
-/
noncomputable def theorem1PaperAssumptions
    (hn : 0 < n) :
    AccuracyFamily.Theorem1PaperAssumptions MF.toAccuracyFamily where
  prefers_independent := fun θ hθ =>
    MF.prefersIndependentReranking hn θ hθ
  prefers_weaker_competition := fun θA θH hθH hθ =>
    MF.prefersWeakerCompetition hn θA θH hθH hθ
  dist_atom_continuity := fun θ hθ π => by
    simpa [toAccuracyFamily] using MF.dist_atom_continuity θ hθ π
  asymptotic_first_dominance := fun θH lower hθH hθ =>
    MF.asymptotic_first_dominance θH lower hθH hθ
  removal_monotonicity := fun θA θH hθH hθ =>
    MF.theorem1RemovalMonotonicityAt hn θA θH hθH hθ

/--
Family-level Mallows Theorem 1 bridge.
-/
theorem theorem1Target
    (hn : 0 < n) (θH : ℝ) (hθH : 0 < θH) :
    AccuracyFamily.Theorem1Target MF.toAccuracyFamily θH :=
  AccuracyFamily.theorem1Target_of_paperAssumptions
    hθH (MF.theorem1PaperAssumptions hn)

end MallowsAccuracyFamilySpec
end Monoculture
