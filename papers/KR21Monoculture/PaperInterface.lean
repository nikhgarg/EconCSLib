import KR21Monoculture.MainTheorems

/-!
# Paper Interface: Algorithmic Monoculture and Social Welfare

This file is the compact human-facing review surface for the active KR21
formalization. `MainTheorems.lean` remains the full paper-oriented ledger; this
interface starts with the stable Mallows/RUM statements that are ready for
paper-vs-Lean review while other agents continue proof work.
-/

open EconCSLib MeasureTheory
open scoped ENNReal NNReal

namespace KR21Monoculture
namespace PaperInterface

/-! ## Paper Definitions -/

/-- Paper Mallows family parameterization used by the compact review surface. -/
noncomputable abbrev mallowsSpec {n : ℕ} (center : Ranking n) (theta : ℝ) := concreteMallowsSpec center theta

/-- Paper Appendix C strict well-ordered noise predicate. -/
abbrev strictlyWellOrderedNoise (f : ℝ → ℝ) : Prop := StrictlyWellOrderedNoise f

/-! ## Definitions and Appendix C Noise Statements -/

/--
Definition 1 / Mallows atomwise continuity: for the Mallows family with
parameter `theta`, the probability of any fixed permutation varies continuously
with positive `theta`.
-/
theorem definition1_concreteMallowsSpec_atom_continuity
    {n : ℕ} (center : Ranking n) {theta : ℝ} (htheta : 0 < theta)
    (pi : Ranking n) :
    EconCSLib.EpsilonContinuousAt
      (fun theta' => (((concreteMallowsSpec center theta').law) pi).toReal) theta :=
    KR21Monoculture.paper_definition1_concreteMallowsSpec_atom_continuity
      center htheta pi

/--
Definition 1 / Mallows asymptotic first dominance: as algorithmic Mallows
accuracy tends to infinity, the all-algorithm payoff eventually exceeds the
human-against-algorithm payoff used in Theorem 1.
-/
theorem definition1_concreteMallowsSpec_asymptotic_first_dominance
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value) :
    ∀ thetaH lower, 0 < thetaH → thetaH < lower →
      ∃ hi, lower < hi ∧
        AccuracyFamily.theorem1_g
            ({ dist := fun theta => (concreteMallowsSpec center theta).law,
                value := value } : AccuracyFamily n)
            hi thetaH <
          AccuracyFamily.theorem1_f
            ({ dist := fun theta => (concreteMallowsSpec center theta).law,
                value := value } : AccuracyFamily n)
            hi thetaH :=
    KR21Monoculture.paper_definition1_concreteMallowsSpec_asymptotic_first_dominance
      center value hvalue

/--
Appendix A / Theorem 5 deterministic finite-source monotonicity: if a finite
source law over RUM score vectors is ranked once by raw scores and once after a
strict contraction toward true values, then every nonempty remaining candidate
set has weakly higher expected top value after contraction.
-/
theorem appendixA_expectedBestInSet_monotonicity_of_finite_rankByScore_contraction
    {n : ℕ} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (value : Candidate n → ℝ)
    (raw : Omega → Candidate n → ℝ)
    {remaining : Finset (Candidate n)}
    {t : ℝ} (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hremaining : remaining.Nonempty) :
    EconCSLib.SocialChoice.Ranking.expectedBestInSet
        (mu.map (fun omega =>
          EconCSLib.SocialChoice.Ranking.rankByScore (raw omega)))
        value remaining ≤
      EconCSLib.SocialChoice.Ranking.expectedBestInSet
        (mu.map (fun omega =>
          EconCSLib.SocialChoice.Ranking.rankByScore
            (fun i => paper_appendixC_contractedScore t (value i) (raw omega i))))
        value remaining :=
  KR21Monoculture.paper_appendixA_expectedBestInSet_monotonicity_of_finite_rankByScore_contraction
    mu value raw ht0 htlt1 hremaining

/--
Appendix A / Theorem 5 continuous-source monotonicity: if a probability source
over RUM score vectors is ranked once by raw scores and once after a strict
contraction toward true values, then every nonempty remaining candidate set has
weakly higher expected top value after contraction.

Source status: derived from source primitives.
-/
theorem appendixA_expectedBestInSet_monotonicity_of_measure_rankByScore_contraction
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (value : Candidate n → ℝ)
    (raw : Omega → Candidate n → ℝ)
    {remaining : Finset (Candidate n)}
    {t : ℝ}
    (hrawRank :
      Measurable (fun omega =>
        EconCSLib.SocialChoice.Ranking.rankByScore (raw omega)))
    (hcontractRank :
      Measurable (fun omega =>
        EconCSLib.SocialChoice.Ranking.rankByScore
          (fun i => paper_appendixC_contractedScore t (value i) (raw omega i))))
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hremaining : remaining.Nonempty) :
    EconCSLib.SocialChoice.Ranking.expectedBestInSet
        (EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega => EconCSLib.SocialChoice.Ranking.rankByScore (raw omega))
          hrawRank)
        value remaining ≤
      EconCSLib.SocialChoice.Ranking.expectedBestInSet
        (EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega =>
            EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => paper_appendixC_contractedScore t (value i) (raw omega i)))
          hcontractRank)
        value remaining :=
  KR21Monoculture.paper_appendixA_expectedBestInSet_monotonicity_of_measure_rankByScore_contraction
    mu value raw hrawRank hcontractRank ht0 htlt1 hremaining

/--
Appendix A / Theorem 5 strict continuous-source monotonicity: the same
source-coupled contraction gives strict expected improvement when the strict
pointwise-improvement region has positive source measure.
-/
theorem appendixA_expectedBestInSet_strict_of_measure_rankByScore_contraction
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (value : Candidate n → ℝ)
    (raw : Omega → Candidate n → ℝ)
    {remaining : Finset (Candidate n)}
    {t : ℝ}
    (hrawRank :
      Measurable (fun omega =>
        EconCSLib.SocialChoice.Ranking.rankByScore (raw omega)))
    (hcontractRank :
      Measurable (fun omega =>
        EconCSLib.SocialChoice.Ranking.rankByScore
          (fun i => paper_appendixC_contractedScore t (value i) (raw omega i))))
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hremaining : remaining.Nonempty)
    (hstrict :
      0 < mu {omega |
        value
          (bestInSet
            (EconCSLib.SocialChoice.Ranking.rankByScore (raw omega))
            remaining) <
        value
          (bestInSet
            (EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => paper_appendixC_contractedScore t (value i) (raw omega i)))
            remaining)}) :
    EconCSLib.SocialChoice.Ranking.expectedBestInSet
        (EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega => EconCSLib.SocialChoice.Ranking.rankByScore (raw omega))
          hrawRank)
        value remaining <
      EconCSLib.SocialChoice.Ranking.expectedBestInSet
        (EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega =>
            EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => paper_appendixC_contractedScore t (value i) (raw omega i)))
          hcontractRank)
        value remaining :=
  KR21Monoculture.paper_appendixA_expectedBestInSet_strict_of_measure_rankByScore_contraction
    mu value raw hrawRank hcontractRank ht0 htlt1 hremaining hstrict

/--
Appendix A / Theorem 5 scaled-noise RUM monotonicity: for `thetaH < thetaA`,
ranking scores `x_i + noise_i / thetaA` is a contraction of
`x_i + noise_i / thetaH`; hence the source model satisfies the finite-removal
monotonicity certificate used by Theorem 1, provided the full-set strict
improvement region has positive source measure.

Source status: derived from source primitives.
-/
theorem appendixA_theorem1RemovalMonotonicityAt_of_scaledNoise_rankByScore_source
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    {F : AccuracyFamily n} {thetaA thetaH : ℝ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (noise : Omega → Candidate n → ℝ)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hrawRank :
      Measurable (fun omega =>
        EconCSLib.SocialChoice.Ranking.rankByScore
          (fun i => F.value i + noise omega i / thetaH)))
    (haccurateRank :
      Measurable (fun omega =>
        EconCSLib.SocialChoice.Ranking.rankByScore
          (fun i => F.value i + noise omega i / thetaA)))
    (hdistH :
      F.dist thetaH =
        EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega =>
            EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise omega i / thetaH))
          hrawRank)
    (hdistA :
      F.dist thetaA =
        EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega =>
            EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise omega i / thetaA))
          haccurateRank)
    (hstrict_univ :
      0 < mu {omega |
        F.value
          (bestInSet
            (EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise omega i / thetaH))
            Finset.univ) <
        F.value
          (bestInSet
            (EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise omega i / thetaA))
            Finset.univ)}) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F thetaA thetaH :=
  KR21Monoculture.paper_appendixA_theorem1RemovalMonotonicityAt_of_scaledNoise_rankByScore_source
    mu noise hthetaH hthetaHA hrawRank haccurateRank hdistH hdistA hstrict_univ

/--
Appendix A / Theorem 5 scaled-noise RUM monotonicity from a concrete top-switch
source region: it is enough to exhibit positive source mass where the
low-accuracy scores uniquely put a lower-valued candidate on top, while the
high-accuracy scores uniquely put a higher-valued candidate on top.

Source status: derived from source primitives.
-/
theorem appendixA_theorem1RemovalMonotonicityAt_of_scaledNoise_top_switch_set
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    {F : AccuracyFamily n} {thetaA thetaH : ℝ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (noise : Omega → Candidate n → ℝ)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hrawRank :
      Measurable (fun omega =>
        EconCSLib.SocialChoice.Ranking.rankByScore
          (fun i => F.value i + noise omega i / thetaH)))
    (haccurateRank :
      Measurable (fun omega =>
        EconCSLib.SocialChoice.Ranking.rankByScore
          (fun i => F.value i + noise omega i / thetaA)))
    (hdistH :
      F.dist thetaH =
        EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega =>
            EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise omega i / thetaH))
          hrawRank)
    (hdistA :
      F.dist thetaA =
        EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega =>
            EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise omega i / thetaA))
          haccurateRank)
    {low high : Candidate n} {S : Set Omega}
    (hSpos : 0 < mu S)
    (hvalue : F.value low < F.value high)
    (hrawTop :
      ∀ omega ∈ S, ∀ d : Candidate n, d ≠ low →
        F.value d + noise omega d / thetaH <
          F.value low + noise omega low / thetaH)
    (haccurateTop :
      ∀ omega ∈ S, ∀ d : Candidate n, d ≠ high →
        F.value d + noise omega d / thetaA <
          F.value high + noise omega high / thetaA) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F thetaA thetaH :=
  KR21Monoculture.paper_appendixA_theorem1RemovalMonotonicityAt_of_scaledNoise_top_switch_set
    mu noise hthetaH hthetaHA hrawRank haccurateRank hdistH hdistA
    hSpos hvalue hrawTop haccurateTop

/--
Appendix A / Theorem 5 scaled-noise strictness from full support: a
positive-everywhere finite noise density gives positive source mass to the
strict full-set improvement event whenever two candidates have a strict value
gap and `thetaA > thetaH > 0`.

Source status: derived from source primitives.
-/
theorem appendixA_scaledNoise_strict_fullset_improvement_pos_of_noise_fullSupport
    {n : ℕ}
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (hDpos : ∀ noise, D noise ≠ 0)
    (value : Candidate n → ℝ)
    {thetaA thetaH : ℝ} {low high : Candidate n}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hvalue : value low < value high) :
    0 < ((volume : Measure (Candidate n → ℝ)).withDensity D)
      {noise |
        value
          (bestInSet
            (EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => value i + noise i / thetaH))
            Finset.univ) <
        value
          (bestInSet
            (EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => value i + noise i / thetaA))
            Finset.univ)} :=
  KR21Monoculture.paper_appendixA_scaledNoise_strict_fullset_improvement_pos_of_noise_fullSupport
    D hD hDpos value hthetaH hthetaHA hvalue

/--
Appendix A / Theorem 5 finite-removal monotonicity from a full-support
scaled-noise density: the positive strict-improvement event is derived from
full support, while the ranking-law equalities identify the paper's family with
the induced scaled-noise laws.

Source status: derived from source primitives.
-/
theorem appendixA_theorem1RemovalMonotonicityAt_of_scaledNoise_fullSupport_density
    {n : ℕ}
    {F : AccuracyFamily n} {thetaA thetaH : ℝ}
    (mu : Measure (Candidate n → ℝ)) [IsProbabilityMeasure mu]
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (hDpos : ∀ noise, D noise ≠ 0)
    (hmu :
      mu = (volume : Measure (Candidate n → ℝ)).withDensity D)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hrawRank :
      Measurable (fun noise : Candidate n → ℝ =>
        EconCSLib.SocialChoice.Ranking.rankByScore
          (fun i => F.value i + noise i / thetaH)))
    (haccurateRank :
      Measurable (fun noise : Candidate n → ℝ =>
        EconCSLib.SocialChoice.Ranking.rankByScore
          (fun i => F.value i + noise i / thetaA)))
    (hdistH :
      F.dist thetaH =
        EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun noise =>
            EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise i / thetaH))
          hrawRank)
    (hdistA :
      F.dist thetaA =
        EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun noise =>
            EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise i / thetaA))
          haccurateRank)
    {low high : Candidate n}
    (hvalue : F.value low < F.value high) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F thetaA thetaH :=
  KR21Monoculture.paper_appendixA_theorem1RemovalMonotonicityAt_of_scaledNoise_fullSupport_density
    mu D hD hDpos hmu hthetaH hthetaHA hrawRank haccurateRank
    hdistH hdistA hvalue

/--
Appendix A / Theorem 5 strictness from a continuous score-space box: for a
positive density on finite score vectors, an explicit open box forcing a raw
low-valued top choice and contracted high-valued top choice has positive source
mass, hence supplies the strict-improvement event used by removal monotonicity.

Source status: derived from source primitives.
-/
theorem appendixA_strict_fullset_improvement_pos_of_scoreSpace_top_switch_openBox
    {n : ℕ}
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (value : Candidate n → ℝ)
    {t : ℝ} {low high : Candidate n}
    {a b : Candidate n → ℝ}
    (hab : ∀ i, a i < b i)
    (hDpos :
      ∀ score,
        score ∈ Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)) →
          D score ≠ 0)
    (hvalue : value low < value high)
    (hrawTop :
      ∀ score ∈ Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)),
        ∀ d : Candidate n, d ≠ low → score d < score low)
    (hcontractTop :
      ∀ score ∈ Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)),
        ∀ d : Candidate n, d ≠ high →
          paper_appendixC_contractedScore t (value d) (score d) <
            paper_appendixC_contractedScore t (value high) (score high)) :
    0 < ((volume : Measure (Candidate n → ℝ)).withDensity D)
      {score |
        value
          (bestInSet
            (EconCSLib.SocialChoice.Ranking.rankByScore score)
            Finset.univ) <
        value
          (bestInSet
            (EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => paper_appendixC_contractedScore t (value i) (score i)))
            Finset.univ)} :=
  KR21Monoculture.paper_appendixA_strict_fullset_improvement_pos_of_scoreSpace_top_switch_openBox
    D hD value hab hDpos hvalue hrawTop hcontractTop

/--
Appendix A / Theorem 5 strictness from explicit numerical margins: with a
positive-everywhere score-space density, endpoint inequalities defining a
raw-low / contracted-high top switch give positive strict-improvement mass.

Source status: derived from source primitives.
-/
theorem appendixA_strict_fullset_improvement_pos_of_scoreSpace_topSwitch_parameters
    {n : ℕ}
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (hDpos : ∀ score, D score ≠ 0)
    (value : Candidate n → ℝ)
    {t eps K : ℝ} {low high : Candidate n}
    (ht0 : 0 ≤ t)
    (heps : 0 < eps) (hKpos : 0 < K)
    (hvalue : value low < value high)
    (hhigh_low :
      paper_appendixC_contractedScore t (value low) eps <
        paper_appendixC_contractedScore t (value high) (-(eps / 8)))
    (hhigh_other :
      ∀ d : Candidate n, d ≠ low → d ≠ high →
        paper_appendixC_contractedScore t (value d) (-K) <
          paper_appendixC_contractedScore t (value high) (-(eps / 8))) :
    0 < ((volume : Measure (Candidate n → ℝ)).withDensity D)
      {score |
        value
          (bestInSet
            (EconCSLib.SocialChoice.Ranking.rankByScore score)
            Finset.univ) <
        value
          (bestInSet
            (EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => paper_appendixC_contractedScore t (value i) (score i)))
            Finset.univ)} :=
  KR21Monoculture.paper_appendixA_strict_fullset_improvement_pos_of_scoreSpace_topSwitch_parameters
    D hD hDpos value ht0 heps hKpos hvalue hhigh_low hhigh_other

/--
Appendix A / Theorem 5 strictness from full-support score density: for a
genuine contraction and two candidates with a strict value gap, any
positive-everywhere continuous score-space density gives positive mass to the
strict full-set improvement event.

Source status: derived from source primitives.
-/
theorem appendixA_strict_fullset_improvement_pos_of_scoreSpace_fullSupport
    {n : ℕ}
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (hDpos : ∀ score, D score ≠ 0)
    (value : Candidate n → ℝ)
    {t : ℝ} {low high : Candidate n}
    (htpos : 0 < t) (htlt1 : t < 1)
    (hvalue : value low < value high) :
    0 < ((volume : Measure (Candidate n → ℝ)).withDensity D)
      {score |
        value
          (bestInSet
            (EconCSLib.SocialChoice.Ranking.rankByScore score)
            Finset.univ) <
        value
          (bestInSet
            (EconCSLib.SocialChoice.Ranking.rankByScore
              (fun i => paper_appendixC_contractedScore t (value i) (score i)))
            Finset.univ)} :=
  KR21Monoculture.paper_appendixA_strict_fullset_improvement_pos_of_scoreSpace_fullSupport
    D hD hDpos value htpos htlt1 hvalue

/--
Appendix A / Theorem 5 asymptotic optimality: if high accuracy makes the total
source probability of pairwise inversions arbitrarily small, then the induced
ranking law converges atomwise to the true ranking.

Source status: derived from source primitives.
-/
theorem appendixA_atomwise_concentration_of_sum_inversion_probs
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℝ → Measure Omega) [∀ theta, IsProbabilityMeasure (mu theta)]
    (rank : ℝ → Omega → Ranking n)
    (hrank : ∀ theta, Measurable (rank theta))
    (center : Ranking n)
    (hinv :
      ∀ lower delta, 0 < delta →
        ∃ hi, lower < hi ∧
          (∑ ab : Candidate n × Candidate n,
            EconCSLib.measureProb (mu hi)
              (fun omega => invertedPair center (rank hi omega) ab)) < delta) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure
                (mu hi) (rank hi) (hrank hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_atomwise_concentration_of_sum_inversion_probs
    mu rank hrank center hinv

/--
Appendix A / Theorem 5 asymptotic optimality: it is enough to make the total
source probability of adjacent inversions in the true ranking order arbitrarily
small.  The finite adjacent-union-bound argument then gives atomwise
convergence to the true ranking.

Source status: derived from source primitives.
-/
theorem appendixA_atomwise_concentration_of_sum_adjacent_inversion_probs
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℝ → Measure Omega) [∀ theta, IsProbabilityMeasure (mu theta)]
    (rank : ℝ → Omega → Ranking n)
    (hrank : ∀ theta, Measurable (rank theta))
    (center : Ranking n)
    (hinv :
      ∀ lower delta, 0 < delta →
        ∃ hi, lower < hi ∧
          (∑ i : Fin (n + 1),
            EconCSLib.measureProb (mu hi)
              (fun omega => invertedPair center (rank hi omega)
                (center i.castSucc, center i.succ))) < delta) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure
                (mu hi) (rank hi) (hrank hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_atomwise_concentration_of_sum_adjacent_inversion_probs
    mu rank hrank center hinv

/--
Appendix A / Theorem 5 asymptotic optimality for score-induced RUM rankings:
it is enough to make the total source probability of adjacent true-neighbor
score misorders arbitrarily small.  This is the coordinate-level tail statement
used in the paper's source argument.

Source status: derived from source primitives.
-/
theorem appendixA_atomwise_concentration_of_sum_adjacent_score_misorder_probs
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℝ → Measure Omega) [∀ theta, IsProbabilityMeasure (mu theta)]
    (score : ℝ → Omega → Candidate n → ℝ)
    (hrank : ∀ theta,
      Measurable (fun omega =>
        EconCSLib.SocialChoice.Ranking.rankByScore (score theta omega)))
    (center : Ranking n)
    (hmisorder :
      ∀ lower delta, 0 < delta →
        ∃ hi, lower < hi ∧
          (∑ i : Fin (n + 1),
            EconCSLib.measureProb (mu hi)
              (fun omega =>
                score hi omega (center i.castSucc) ≤
                  score hi omega (center i.succ))) < delta) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure
                (mu hi)
                (fun omega =>
                  EconCSLib.SocialChoice.Ranking.rankByScore (score hi omega))
                (hrank hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_atomwise_concentration_of_sum_adjacent_score_misorder_probs
    mu score hrank center hmisorder

/--
Appendix A / Theorem 5 asymptotic optimality from a source-tail limit: if the
total source probability of pairwise inversions tends to zero, then the induced
ranking law converges atomwise to the true ranking.

Source status: derived from source primitives.
-/
theorem appendixA_atomwise_concentration_of_sum_inversion_probs_tendsto
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℝ → Measure Omega) [∀ theta, IsProbabilityMeasure (mu theta)]
    (rank : ℝ → Omega → Ranking n)
    (hrank : ∀ theta, Measurable (rank theta))
    (center : Ranking n)
    (hsum :
      Filter.Tendsto
        (fun theta : ℝ =>
          ∑ ab : Candidate n × Candidate n,
            EconCSLib.measureProb (mu theta)
              (fun omega => invertedPair center (rank theta omega) ab))
        Filter.atTop (nhds 0)) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure
                (mu hi) (rank hi) (hrank hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_atomwise_concentration_of_sum_inversion_probs_tendsto
    mu rank hrank center hsum

/--
Appendix A / Theorem 5 asymptotic optimality from an adjacent source-tail limit:
if the total source probability of adjacent inversions in the true ranking order
tends to zero, then the induced ranking law converges atomwise to the true
ranking.

Source status: derived from source primitives.
-/
theorem appendixA_atomwise_concentration_of_sum_adjacent_inversion_probs_tendsto
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℝ → Measure Omega) [∀ theta, IsProbabilityMeasure (mu theta)]
    (rank : ℝ → Omega → Ranking n)
    (hrank : ∀ theta, Measurable (rank theta))
    (center : Ranking n)
    (hsum :
      Filter.Tendsto
        (fun theta : ℝ =>
          ∑ i : Fin (n + 1),
            EconCSLib.measureProb (mu theta)
              (fun omega => invertedPair center (rank theta omega)
                (center i.castSucc, center i.succ)))
        Filter.atTop (nhds 0)) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure
                (mu hi) (rank hi) (hrank hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_atomwise_concentration_of_sum_adjacent_inversion_probs_tendsto
    mu rank hrank center hsum

/--
Appendix A / Theorem 5 asymptotic optimality from a score-tail limit: for
score-induced RUM rankings, it is enough that adjacent true-neighbor score
misorder probabilities have total mass tending to zero.

Source status: derived from source primitives.
-/
theorem appendixA_atomwise_concentration_of_sum_adjacent_score_misorder_probs_tendsto
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℝ → Measure Omega) [∀ theta, IsProbabilityMeasure (mu theta)]
    (score : ℝ → Omega → Candidate n → ℝ)
    (hrank : ∀ theta,
      Measurable (fun omega =>
        EconCSLib.SocialChoice.Ranking.rankByScore (score theta omega)))
    (center : Ranking n)
    (hsum :
      Filter.Tendsto
        (fun theta : ℝ =>
          ∑ i : Fin (n + 1),
            EconCSLib.measureProb (mu theta)
              (fun omega =>
                score theta omega (center i.castSucc) ≤
                  score theta omega (center i.succ)))
        Filter.atTop (nhds 0)) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure
                (mu hi)
                (fun omega =>
                  EconCSLib.SocialChoice.Ranking.rankByScore (score hi omega))
                (hrank hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_atomwise_concentration_of_sum_adjacent_score_misorder_probs_tendsto
    mu score hrank center hsum

/--
Appendix A / Theorem 5 scaled-noise source tail: for fixed finite-dimensional
noise, scores `value_i + noise_i / theta` have vanishing total adjacent
true-neighbor score-misorder probability as accuracy tends to infinity.

Source status: derived from source primitives.
-/
theorem appendixA_scaledNoise_adjacent_score_misorder_sum_tendsto
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (noise : Omega → Candidate n → ℝ)
    (hnoise : ∀ c : Candidate n, Measurable (fun omega => noise omega c))
    (value : Candidate n → ℝ) (center : Ranking n)
    (hcenter :
      ∀ i : Fin (n + 1),
        value (center i.succ) < value (center i.castSucc)) :
    Filter.Tendsto
      (fun theta : ℝ =>
        ∑ i : Fin (n + 1),
          EconCSLib.measureProb mu
            (fun omega =>
              value (center i.castSucc) +
                  noise omega (center i.castSucc) / theta ≤
                value (center i.succ) +
                  noise omega (center i.succ) / theta))
      Filter.atTop (nhds 0) :=
  KR21Monoculture.paper_appendixA_scaledNoise_adjacent_score_misorder_sum_tendsto
    mu noise hnoise value center hcenter

/--
Appendix A / Theorem 5 scaled-noise measurability: if each finite noise
coordinate is measurable, then sorting the scaled-noise scores gives a
measurable ranking-valued random variable.
-/
theorem appendixA_scaledNoise_rankByScore_measurable
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (noise : Omega → Candidate n → ℝ)
    (hnoise : ∀ c : Candidate n, Measurable (fun omega => noise omega c))
    (value : Candidate n → ℝ) (theta : ℝ) :
    Measurable (fun omega =>
      EconCSLib.SocialChoice.Ranking.rankByScore
        (fun c => value c + noise omega c / theta)) :=
  KR21Monoculture.paper_appendixA_scaledNoise_rankByScore_measurable
    noise hnoise value theta

/--
Appendix A / Theorem 5 scaled-noise atom continuity: if scaled scores have no
pairwise ties almost surely at a positive accuracy, then every atom of the
finite induced ranking law is continuous at that accuracy.
-/
theorem appendixA_scaledNoiseRankingPMF_atom_epsilonContinuousAt_of_ae_noTies
    {n : ℕ}
    (mu : Measure (Candidate n → ℝ)) [IsProbabilityMeasure mu]
    (value : Candidate n → ℝ) {theta : ℝ} (htheta : 0 < theta)
    (hnoTie :
      ∀ᵐ noise ∂mu,
        ∀ i j : Candidate n, i ≠ j →
          value i + noise i / theta ≠ value j + noise j / theta)
    (pi : Ranking n) :
    EconCSLib.EpsilonContinuousAt
      (fun theta' =>
        ((KR21Monoculture.paper_appendixA_scaledNoiseRankingPMF
          mu value theta') pi).toReal)
      theta :=
  KR21Monoculture.paper_appendixA_scaledNoiseRankingPMF_atom_epsilonContinuousAt_of_ae_noTies
    mu value htheta hnoTie pi

/--
Appendix A / Theorem 5 scaled-noise no-ties: an absolutely continuous finite
noise-vector law gives probability zero to every pairwise scaled-score tie.

Source status: derived from source primitives.
-/
theorem appendixA_scaledNoise_noTie_ae_of_fullSupport_density
    {n : ℕ}
    (mu : Measure (Candidate n → ℝ)) [IsProbabilityMeasure mu]
    (D : (Candidate n → ℝ) → ENNReal)
    (hmu : mu = (volume : Measure (Candidate n → ℝ)).withDensity D)
    (value : Candidate n → ℝ) {theta : ℝ} (htheta : 0 < theta) :
    ∀ᵐ noise ∂mu,
      ∀ i j : Candidate n, i ≠ j →
        value i + noise i / theta ≠ value j + noise j / theta :=
  KR21Monoculture.paper_appendixA_scaledNoise_noTie_ae_of_fullSupport_density
    mu D hmu value htheta

/--
Appendix A / Theorem 5 scaled-noise asymptotic optimality: fixed noise, a
coordinate-measurable induced ranking, and strict adjacent true-value gaps
imply atomwise convergence of the induced ranking law to the true ranking.
-/
theorem appendixA_scaledNoise_atomwise_concentration
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (noise : Omega → Candidate n → ℝ)
    (hnoise : ∀ c : Candidate n, Measurable (fun omega => noise omega c))
    (value : Candidate n → ℝ)
    (center : Ranking n)
    (hcenter :
      ∀ i : Fin (n + 1),
        value (center i.succ) < value (center i.castSucc)) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure
                mu
                (fun omega =>
                  EconCSLib.SocialChoice.Ranking.rankByScore
                    (fun c => value c + noise omega c / hi))
                (appendixA_scaledNoise_rankByScore_measurable
                  noise hnoise value hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_scaledNoise_atomwise_concentration
    mu noise hnoise value center hcenter

/--
Appendix A / Theorem 5 Definition-1 consequence package for scaled-noise RUMs:
the downstream finite-ranking fields used by Theorem 1.
-/
abbrev AppendixAScaledNoiseDefinition1Consequence
    {n : ℕ} (F : AccuracyFamily n) (center : Ranking n) : Type :=
  KR21Monoculture.PaperAppendixAScaledNoiseDefinition1Consequence F center

/--
Appendix A / Theorem 5 scaled-noise source package: positive full-support noise
density, strict adjacent true-value gaps, and the source no-tie fact imply the
finite-ranking Definition-1 consequences consumed by Theorem 1.

Source status: auxiliary source package, derived from source primitives. This
constructs the Definition-1 consequence package whose fields are exposed by the
reviewed Appendix A rows above: atom continuity, high-accuracy concentration,
and finite-removal monotonicity.
-/
noncomputable def appendixA_scaledNoise_definition1_consequence_of_fullSupport_source
    {n : ℕ}
    {F : AccuracyFamily n} (center : Ranking n)
    (mu : Measure (Candidate n → ℝ)) [IsProbabilityMeasure mu]
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (hDpos : ∀ noise, D noise ≠ 0)
    (hmu :
      mu = (volume : Measure (Candidate n → ℝ)).withDensity D)
    (hcenter :
      ∀ i : Fin (n + 1),
        F.value (center i.succ) < F.value (center i.castSucc))
    (hdist :
      ∀ theta, 0 < theta →
        F.dist theta =
          EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure
            mu
            (fun noise =>
              EconCSLib.SocialChoice.Ranking.rankByScore
                (fun c => F.value c + noise c / theta))
            (appendixA_scaledNoise_rankByScore_measurable
              (Omega := Candidate n → ℝ)
              (fun noise c => noise c)
              (fun c => measurable_pi_apply c)
              F.value theta)) :
    AppendixAScaledNoiseDefinition1Consequence F center :=
  KR21Monoculture.paper_appendixA_scaledNoise_definition1_consequence_of_fullSupport_source
    center mu D hD hDpos hmu hcenter hdist

/--
Definition 1 / Gaussian three-candidate RUM: for the concrete normalized
Gaussian score law, a strict contraction toward ordered values satisfies the
finite-removal monotonicity condition used by Theorem 1.
-/
theorem definition1_threeCandidate_gaussian_removalMonotonicity_of_scoreSpace_t_lt_one
    {F : AccuracyFamily 1} {thetaA thetaH : ℝ}
    (x1 x2 x3 t : ℝ)
    (hdistA :
      F.dist thetaA =
        paper_theorem6_normalizedScoreRankingPMF (theorem8GaussianPDF 0)
          x1 x2 x3
          (paper_theorem6_gaussian_scoreDensity_lintegral_eq_one x1 x2 x3)
          (rum3ContractRankByScoreFns
            t x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
          (rum3ContractRankByScoreFns_measurable
            rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
            t x1 x2 x3))
    (hdistH :
      F.dist thetaH =
        paper_theorem6_normalizedScoreRankingPMF (theorem8GaussianPDF 0)
          x1 x2 x3
          (paper_theorem6_gaussian_scoreDensity_lintegral_eq_one x1 x2 x3)
          (rum3RankByScoreFns
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
          (rum3RankByScoreFns_measurable
            rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F thetaA thetaH :=
  KR21Monoculture.paper_definition1_threeCandidate_removalMonotonicity_of_gaussian_scoreSpace_t_lt_one
    x1 x2 x3 t hdistA hdistH hvalue1 hvalue2 hvalue3
    ht0 ht1 htlt1 hx12 hx23

/--
Definition 1 / Laplace three-candidate RUM: for the concrete normalized
Laplace score law, a strict contraction toward ordered values satisfies the
finite-removal monotonicity condition used by Theorem 1.
-/
theorem definition1_threeCandidate_laplacian_removalMonotonicity_of_scoreSpace_t_lt_one
    {F : AccuracyFamily 1} {thetaA thetaH : ℝ}
    {lam x1 x2 x3 t : ℝ}
    (hlam : 0 < lam)
    (hdistA :
      F.dist thetaA =
        paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
          x1 x2 x3
          (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
            (lam := lam) hlam x1 x2 x3)
          (rum3ContractRankByScoreFns
            t x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
          (rum3ContractRankByScoreFns_measurable
            rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
            t x1 x2 x3))
    (hdistH :
      F.dist thetaH =
        paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
          x1 x2 x3
          (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
            (lam := lam) hlam x1 x2 x3)
          (rum3RankByScoreFns
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
          (rum3RankByScoreFns_measurable
            rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F thetaA thetaH :=
  KR21Monoculture.paper_definition1_threeCandidate_removalMonotonicity_of_laplacian_scoreSpace_t_lt_one
    hlam hdistA hdistH hvalue1 hvalue2 hvalue3 ht0 ht1 htlt1 hx12 hx23

/-- Appendix C Lemma 1, Gaussian noise is strictly well-ordered. -/
theorem lemma1_gaussian_strictlyWellOrdered
    {kappa : ℝ} (hkappa : 0 < kappa) :
    StrictlyWellOrderedNoise (gaussianNoiseKernel kappa) :=  KR21Monoculture.paper_lemma1_gaussian_strictlyWellOrdered hkappa

/--
Appendix C Lemma 1, Laplacian weak form: the Laplacian density kernel satisfies
the globally valid weak well-ordering inequality.

Source status: formalized source note. The paper states global strict
Laplacian well-ordering; Lean proves the globally valid weak form here and
strict overlap/local forms elsewhere. No named theorem or main-text result is
affected.
-/
theorem lemma1_laplacian_weaklyWellOrdered
    {lam : ℝ} (hlam : 0 ≤ lam) :
    WeaklyWellOrderedNoise (laplacianNoiseKernel lam) :=  KR21Monoculture.paper_lemma1_laplacian_weaklyWellOrdered hlam

/--
Appendix C Lemma 1, Laplacian strict local form: for ordered locations
`a > b` and `c > d`, strict Laplacian well-ordering holds under the explicit
overlap condition `b < c` and `d < a`, equivalently overlap of the open
intervals `(b,a)` and `(d,c)`.

Source status: formalized source note. This is the strict local replacement for
the paper's false global strict Laplacian statement; the global theorem above is
weak, and no named theorem or main-text result is affected.
-/
theorem lemma1_laplacian_strictlyWellOrdered_of_overlap
    {lam a b c d : ℝ} (hlam : 0 < lam)
    (hab : b < a) (hcd : d < c) (hbc : b < c) (hda : d < a) :
    laplacianNoiseKernel lam (a - c) * laplacianNoiseKernel lam (b - d) >
      laplacianNoiseKernel lam (a - d) * laplacianNoiseKernel lam (b - c) :=
  KR21Monoculture.laplacianNoiseKernel_strictlyWellOrdered_of_overlap
    hlam hab hcd hbc hda

/-! ## Appendix C, Theorem 6 -/

/--
Appendix C Theorem 6 / Gaussian three-candidate RUM: if algorithmic scores are
a strict contraction of the same independent Gaussian score realization, then
the second mover prefers weaker competition.
-/
theorem theorem6_threeCandidate_gaussian_prefersWeakerCompetition_of_scoreSpace_t_lt_one
    (x1 x2 x3 t : ℝ)
    {value : Candidate 1 → ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_normalizedScoreRankingPMF (theorem8GaussianPDF 0)
        x1 x2 x3
        (paper_theorem6_gaussian_scoreDensity_lintegral_eq_one x1 x2 x3)
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF (theorem8GaussianPDF 0)
        x1 x2 x3
        (paper_theorem6_gaussian_scoreDensity_lintegral_eq_one x1 x2 x3)
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
      value :=
  KR21Monoculture.paper_theorem6_threeCandidate_prefersWeakerCompetition_of_gaussian_scoreSpace_t_lt_one
    x1 x2 x3 t hvalue1 hvalue2 hvalue3 ht0 ht1 htlt1 hx12 hx23

/--
Appendix C Theorem 6 / Laplacian three-candidate RUM: the zero-mean Laplace
score law satisfies the density hypotheses directly; the remaining inputs are
normalization of the concrete score density and the Laplacian lambda
certificate for the human subproblem.
-/
theorem theorem6_threeCandidate_laplacian_prefersWeakerCompetition_of_scoreSpace_lambdaCertificate_t_lt_one
    {lam x1 x2 x3 t : ℝ}
    {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hnorm :
      ∫⁻ ω,
          (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
            ω ∂(volume : Measure paper_theorem6_scoreSpace) = 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda :
      RUM3LambdaCertificate
        (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
          x1 x2 x3 hnorm
          (rum3RankByScoreFns
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
          (rum3RankByScoreFns_measurable
            rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3 hnorm
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3 hnorm
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
      value :=
  KR21Monoculture.paper_theorem6_threeCandidate_prefersWeakerCompetition_of_laplacian_scoreSpace_lambdaCertificate_t_lt_one
    hlam hvalue1 hvalue2 hvalue3 hnorm ht0 ht1 htlt1 hx12 hx23 lambda

/--
Appendix C Theorem 6 / Laplacian three-candidate RUM: the zero-mean Laplace
score density is normalized in Lean; the remaining explicit input is the
Laplacian lambda certificate for the human subproblem.
-/
theorem theorem6_threeCandidate_laplacian_prefersWeakerCompetition_of_scoreSpace_concreteNormalization_lambdaCertificate_t_lt_one
    {lam x1 x2 x3 t : ℝ}
    {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda :
      RUM3LambdaCertificate
        (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
          x1 x2 x3
          (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
            (lam := lam) hlam x1 x2 x3)
          (rum3RankByScoreFns
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
          (rum3RankByScoreFns_measurable
            rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3
        (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
          (lam := lam) hlam x1 x2 x3)
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3
        (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
          (lam := lam) hlam x1 x2 x3)
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
      value :=
  KR21Monoculture.paper_theorem6_threeCandidate_prefersWeakerCompetition_of_laplacian_scoreSpace_concreteNormalization_lambdaCertificate_t_lt_one
    hlam hvalue1 hvalue2 hvalue3 ht0 ht1 htlt1 hx12 hx23 lambda

/--
Appendix C Theorem 6 / Laplacian three-candidate RUM: the concrete Laplace
human-subproblem lambda certificate follows from the pairwise Laplace winner
probabilities when `x₃ < x₂ < x₁`.
-/
theorem theorem6_laplacian_scoreSpace_concreteNormalization_lambdaCertificate
    {lam x1 x2 x3 : ℝ}
    (hlam : 0 < lam) (hx12 : x2 < x1) (hx23 : x3 < x2) :
    RUM3LambdaCertificate
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3
        (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
          (lam := lam) hlam x1 x2 x3)
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable)) :=
  KR21Monoculture.paper_theorem6_laplacian_scoreSpace_concreteNormalization_lambdaCertificate
    hlam hx12 hx23

/--
Appendix C Theorem 6 / Laplacian three-candidate RUM: with normalized concrete
Laplace scores, the second firm prefers weaker competition for `0 ≤ t ≤ 1`,
`t < 1`, and `x₃ < x₂ < x₁`.

Source status: derived from source primitives.
-/
theorem theorem6_threeCandidate_laplacian_prefersWeakerCompetition_of_scoreSpace_t_lt_one
    {lam x1 x2 x3 t : ℝ}
    {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hnorm :
      ∫⁻ ω,
          (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
            ω ∂(volume : Measure paper_theorem6_scoreSpace) = 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3 hnorm
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3 hnorm
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
      value :=
  KR21Monoculture.paper_theorem6_threeCandidate_prefersWeakerCompetition_of_laplacian_scoreSpace_t_lt_one
    hlam hvalue1 hvalue2 hvalue3 hnorm ht0 ht1 htlt1 hx12 hx23

/--
Appendix C Theorem 6 / Laplacian three-candidate RUM: the concrete zero-mean
Laplace score density is normalized in Lean, so the theorem has no remaining
lambda-certificate premise.

Source status: derived from source primitives.
-/
theorem theorem6_threeCandidate_laplacian_prefersWeakerCompetition_of_scoreSpace_concreteNormalization_t_lt_one
    {lam x1 x2 x3 t : ℝ}
    {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3
        (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
          (lam := lam) hlam x1 x2 x3)
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3
        (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
          (lam := lam) hlam x1 x2 x3)
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
      value :=
  KR21Monoculture.paper_theorem6_threeCandidate_prefersWeakerCompetition_of_laplacian_scoreSpace_concreteNormalization_t_lt_one
    hlam hvalue1 hvalue2 hvalue3 ht0 ht1 htlt1 hx12 hx23

/-! ## Appendix C, Theorem 7 -/

/--
Appendix C Theorem 7, Laplacian pairwise conditional derivative: for
independent Laplace scores with `x_j < x_i`, the strict source probability
ratio `Pr[X_i > X_j | X_i < a, X_j < a]` is flat to the left of `x_j`,
strictly increasing between `x_j` and `x_i`, and strictly increasing to the
right of `x_i`.

Source status: derived from source primitives.
-/
theorem theorem7_laplacian_pairwise_conditional_derivative_cases
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (a < xj →
      HasDerivAt
          (fun a =>
            paper_theorem7_laplacian_product_strict_conditional_ratio_at
              lam xi xj a) 0 a ∧
        0 ≤ (0 : ℝ)) ∧
    (xj < a → a < xi →
      ∃ d,
        HasDerivAt
          (fun a =>
            paper_theorem7_laplacian_product_strict_conditional_ratio_at
              lam xi xj a) d a ∧
          0 < d) ∧
    (xi < a →
      ∃ d,
        HasDerivAt
          (fun a =>
            paper_theorem7_laplacian_product_strict_conditional_ratio_at
              lam xi xj a) d a ∧
          0 < d) ∧
    (∃ a d,
      xj < a ∧ a < xi ∧
        HasDerivAt
          (fun a =>
            paper_theorem7_laplacian_product_strict_conditional_ratio_at
              lam xi xj a) d a ∧
        0 < d) :=
    KR21Monoculture.paper_theorem7_laplacian_product_strict_conditional_derivative_cases
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx

/-! ## Definition 2 -/

/--
Definition 2 / three-candidate RUM negative-correlation certificate: if
conditioning on each candidate being first strictly lowers the probability that
the better remaining candidate beats the worse remaining candidate, then the
ranking law prefers independent reranking.
-/
theorem definition2_threeCandidate_prefersIndependentReranking_of_negativeCorrelationCertificate
    {μ : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (cert : RUM3Definition2NegativeCorrelationCertificate μ value) :
    Model.PrefersIndependentReranking μ value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_prefersIndependentReranking_of_negativeCorrelationCertificate
    cert

/--
Definition 2 / three-candidate continuous score bridge: for a ranking law
induced by three measurable score coordinates, the negative-correlation
certificate follows from three strict inequalities stated directly in primitive
score-order events.
-/
theorem definition2_threeCandidate_negativeCorrelationCertificate_of_score_inter_lt_mul
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {r1 r2 r3 : Ω → ℝ}
    (hr1 : Measurable r1) (hr2 : Measurable r2) (hr3 : Measurable r3)
    {value : Candidate 1 → ℝ}
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hfirst0 :
      0 < measureProb ν
        (fun ω => r2 ω ≤ r1 ω ∧ r3 ω ≤ r1 ω))
    (hfirst1 :
      0 < measureProb ν
        (fun ω => r1 ω < r2 ω ∧ r3 ω ≤ r2 ω))
    (hfirst2 :
      0 < measureProb ν
        (fun ω => r1 ω < r3 ω ∧ r2 ω < r3 ω))
    (h0 :
      measureProb ν
          (fun ω => r3 ω ≤ r2 ω ∧ r2 ω ≤ r1 ω) <
        measureProb ν (fun ω => r3 ω ≤ r2 ω) *
          measureProb ν
            (fun ω => r2 ω ≤ r1 ω ∧ r3 ω ≤ r1 ω))
    (h1 :
      measureProb ν
          (fun ω => r3 ω ≤ r1 ω ∧ r1 ω < r2 ω) <
        measureProb ν (fun ω => r3 ω ≤ r1 ω) *
          measureProb ν
            (fun ω => r1 ω < r2 ω ∧ r3 ω ≤ r2 ω))
    (h2 :
      measureProb ν
          (fun ω => r2 ω ≤ r1 ω ∧ r1 ω < r3 ω) <
        measureProb ν (fun ω => r2 ω ≤ r1 ω) *
          measureProb ν
            (fun ω => r1 ω < r3 ω ∧ r2 ω < r3 ω)) :
    RUM3Definition2NegativeCorrelationCertificate
      (rumRankingPMFOfMeasure ν (rum3RankByScoreFns r1 r2 r3)
        (rum3RankByScoreFns_measurable hr1 hr2 hr3)) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_negativeCorrelationCertificate_of_score_inter_lt_mul
    ν hr1 hr2 hr3 hvalue01 hvalue12
    hfirst0 hfirst1 hfirst2 h0 h1 h2

/--
Definition 2 / Gaussian three-candidate RUM: independent Gaussian score signals
with ordered means satisfy the negative-correlation certificate.
-/
theorem definition2_threeCandidate_gaussian_negativeCorrelationCertificate
    {x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    RUM3Definition2NegativeCorrelationCertificate
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_gaussian_negativeCorrelationCertificate
    hvalue01 hvalue12 hx12 hx23

/--
Definition 2 / Gaussian three-candidate RUM: independent Gaussian score signals
with ordered means prefer independent reranking.
-/
theorem definition2_threeCandidate_gaussian_prefersIndependentReranking
    {x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersIndependentReranking
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_gaussian_prefersIndependentReranking
    hvalue01 hvalue12 hx12 hx23

/--
Definition 2 / Laplace three-candidate RUM: independent Laplace score signals
with common positive rate and ordered locations satisfy the negative-correlation
certificate.
-/
theorem definition2_threeCandidate_laplacian_negativeCorrelationCertificate
    {lam x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    RUM3Definition2NegativeCorrelationCertificate
      (theorem7LaplacianDefinition2RankingPMF lam x1 x2 x3 hlam) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_laplacian_negativeCorrelationCertificate
    hlam hvalue01 hvalue12 hx12 hx23

/--
Definition 2 / Laplace three-candidate RUM: independent Laplace score signals
with common positive rate and ordered locations prefer independent reranking.
-/
theorem definition2_threeCandidate_laplacian_prefersIndependentReranking
    {lam x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersIndependentReranking
      (theorem7LaplacianDefinition2RankingPMF lam x1 x2 x3 hlam) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_laplacian_prefersIndependentReranking
    hlam hvalue01 hvalue12 hx12 hx23

/--
Definition 2 / Laplace three-candidate RUM under contraction: contracted
rate-`lam` scores induce the same ranking law as raw rate-`lam / t` scores, so
the contracted source also prefers independent reranking.
-/
theorem definition2_threeCandidate_laplacian_contracted_prefersIndependentReranking
    {lam t x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hlam : 0 < lam) (ht : 0 < t)
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersIndependentReranking
      (theorem7LaplacianDefinition2ContractRankingPMF
        lam t x1 x2 x3 hlam) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_laplacian_contracted_prefersIndependentReranking
    hlam ht hvalue01 hvalue12 hx12 hx23

/--
Definition 2 / Gaussian three-candidate RUM with arbitrary positive standard
deviation: independent Gaussian score signals with ordered means satisfy the
negative-correlation certificate.
-/
theorem definition2_threeCandidate_gaussianStd_negativeCorrelationCertificate
    {σ x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hσ : 0 < σ)
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    RUM3Definition2NegativeCorrelationCertificate
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_gaussianStd_negativeCorrelationCertificate
    hσ hvalue01 hvalue12 hx12 hx23

/--
Definition 2 / Gaussian three-candidate RUM with arbitrary positive standard
deviation: independent Gaussian score signals with ordered means prefer
independent reranking.
-/
theorem definition2_threeCandidate_gaussianStd_prefersIndependentReranking
    {σ x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hσ : 0 < σ)
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersIndependentReranking
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_gaussianStd_prefersIndependentReranking
    hσ hvalue01 hvalue12 hx12 hx23

/-! ## Theorem 2 -/

/--
Preferred source-facing boundary for the three-candidate RUM route to Theorem 2.

It asks for atomwise continuity, positive human mass on the swapped top-two
ranking, and algorithmic atomwise concentration toward the deterministic true
ranking. Lean proves that these finite ranking-law facts imply the payoff-level
asymptotic dominance used by the Theorem 1 crossing proof.
-/
abbrev Theorem2RUMConcentrationBoundary
    (F : AccuracyFamily 1) (center : Ranking 1) : Type :=
  KR21Monoculture.PaperTheorem2RUMConcentrationBoundary F center

/--
The remaining limit/continuity boundary for the three-candidate RUM route to
Theorem 2.  The Gaussian/Laplace source-model proof discharges Definition 2,
Definition 3, and finite-removal monotonicity; this boundary contains only
atomwise continuity of the finite ranking law and asymptotic first dominance.
-/
abbrev Theorem2RUMLimitBoundary (F : AccuracyFamily 1) : Type :=
  KR21Monoculture.PaperTheorem2RUMLimitBoundary F

/--
Theorem 2 / Gaussian RUM route: if `F.dist θ` is the three-candidate Gaussian
RUM law with standard deviation `1 / θ`, then the monoculture-paradox target
follows from the source-facing concentration boundary.
-/
theorem theorem2_gaussianStd_target_from_rum_concentration_boundary
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ, 0 < θ →
        F.dist θ =
          rumRankingPMFOfMeasure
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (rum3RankByScoreFns
              theorem8GaussianDefinition2Score1
              theorem8GaussianDefinition2Score2
              theorem8GaussianDefinition2Score3)
            (rum3RankByScoreFns_measurable
              theorem8GaussianDefinition2Score1_measurable
              theorem8GaussianDefinition2Score2_measurable
              theorem8GaussianDefinition2Score3_measurable))
    (boundary :
      Theorem2RUMConcentrationBoundary F (Equiv.refl (Candidate 1))) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_gaussianStd_target_from_rum_concentration_boundary
    hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist boundary

/--
Theorem 2 / Laplace RUM route: if `F.dist θ` is the three-candidate Laplace
RUM law with positive strictly increasing rate `λ θ`, then the
monoculture-paradox target follows from the source-facing concentration
boundary.
-/
theorem theorem2_laplacianRate_target_from_rum_concentration_boundary
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (lam : ℝ → ℝ)
    (hlam_pos : ∀ θ, 0 < θ → 0 < lam θ)
    (hlam_mono : ∀ θA θH, 0 < θH → θH < θA → lam θH < lam θA)
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ (hθ : 0 < θ),
        F.dist θ =
          theorem7LaplacianDefinition2RankingPMF
            (lam θ) x1 x2 x3 (hlam_pos θ hθ))
    (boundary :
      Theorem2RUMConcentrationBoundary F (Equiv.refl (Candidate 1))) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_laplacianRate_target_from_rum_concentration_boundary
    lam hlam_pos hlam_mono hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist
    boundary

/--
Theorem 2 / Gaussian RUM route from the concrete source model: if `F.dist θ`
is the three-candidate Gaussian RUM law with standard deviation `1 / θ`, then
the monoculture-paradox target follows from the concrete source proof.

The source-model proof supplies the Definition 2, Definition 3,
finite-removal monotonicity, positive swapped-ranking mass, and high-accuracy
concentration ingredients. Atomwise continuity of the finite ranking law is
derived from the continuous Gaussian score source.

Source status: derived from source primitives.
-/
theorem theorem2_gaussianStd_target_from_rum_source
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ, 0 < θ →
        F.dist θ =
          rumRankingPMFOfMeasure
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (rum3RankByScoreFns
              theorem8GaussianDefinition2Score1
              theorem8GaussianDefinition2Score2
              theorem8GaussianDefinition2Score3)
            (rum3RankByScoreFns_measurable
              theorem8GaussianDefinition2Score1_measurable
              theorem8GaussianDefinition2Score2_measurable
              theorem8GaussianDefinition2Score3_measurable)) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_gaussianStd_target_from_rum_source
    hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist

/--
Compatibility alias for the older Gaussian source interface that exposed
atomwise continuity as an explicit argument.
-/
theorem theorem2_gaussianStd_target_from_rum_source_and_atom_continuity
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (_hdist_atom_continuity :
      ∀ θ, 0 < θ →
        ∀ π : Ranking 1, EconCSLib.EpsilonContinuousAt
          (fun θ' => ((F.dist θ') π).toReal) θ)
    (hdist :
      ∀ θ, 0 < θ →
        F.dist θ =
          rumRankingPMFOfMeasure
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (rum3RankByScoreFns
              theorem8GaussianDefinition2Score1
              theorem8GaussianDefinition2Score2
              theorem8GaussianDefinition2Score3)
            (rum3RankByScoreFns_measurable
              theorem8GaussianDefinition2Score1_measurable
              theorem8GaussianDefinition2Score2_measurable
              theorem8GaussianDefinition2Score3_measurable)) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_gaussianStd_target_from_rum_source
    hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist

/--
Theorem 2 / canonical Laplace RUM route from the concrete source model: if
`F.dist θ` is the three-candidate Laplace RUM law with rate `θ`, then the
monoculture-paradox target follows from the concrete source proof.
-/
theorem theorem2_laplacianCanonical_target_from_rum_source
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ (hθ : 0 < θ),
        F.dist θ =
          theorem7LaplacianDefinition2RankingPMF θ x1 x2 x3 hθ) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_laplacianCanonical_target_from_rum_source
    hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist

/--
Theorem 2 / continuous-rate Laplace RUM route from the concrete source model:
if `F.dist θ` is the three-candidate Laplace RUM law with a positive strictly
increasing continuous rate that tends to infinity, then the
monoculture-paradox target follows from the concrete source proof.
-/
theorem theorem2_laplacianRate_target_from_continuous_rum_source
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (lam : ℝ → ℝ)
    (hlam_pos : ∀ θ, 0 < θ → 0 < lam θ)
    (hlam_mono : ∀ θA θH, 0 < θH → θH < θA → lam θH < lam θA)
    (hlam_cont : ∀ θ, 0 < θ → ContinuousAt lam θ)
    (hlam_tendsto : Filter.Tendsto lam Filter.atTop Filter.atTop)
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ (hθ : 0 < θ),
        F.dist θ =
          theorem7LaplacianDefinition2RankingPMF
            (lam θ) x1 x2 x3 (hlam_pos θ hθ)) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_laplacianRate_target_from_continuous_rum_source
    lam hlam_pos hlam_mono hlam_cont hlam_tendsto hθH
    hvalue1 hvalue2 hvalue3 hx12 hx23 hdist

/--
Theorem 2 / Laplace RUM route from the concrete source model: if `F.dist θ`
is the three-candidate Laplace RUM law with a positive strictly increasing
rate that tends to infinity, then the monoculture-paradox target follows from
atomwise continuity of the induced finite ranking law.

The source-model proof supplies the Definition 2, Definition 3,
finite-removal monotonicity, positive swapped-ranking mass, and high-accuracy
concentration ingredients.

Source status: derived from source primitives.
-/
theorem theorem2_laplacianRate_target_from_rum_source_and_atom_continuity
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (lam : ℝ → ℝ)
    (hlam_pos : ∀ θ, 0 < θ → 0 < lam θ)
    (hlam_mono : ∀ θA θH, 0 < θH → θH < θA → lam θH < lam θA)
    (hlam_tendsto : Filter.Tendsto lam Filter.atTop Filter.atTop)
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist_atom_continuity :
      ∀ θ, 0 < θ →
        ∀ π : Ranking 1, EconCSLib.EpsilonContinuousAt
          (fun θ' => ((F.dist θ') π).toReal) θ)
    (hdist :
      ∀ θ (hθ : 0 < θ),
        F.dist θ =
          theorem7LaplacianDefinition2RankingPMF
            (lam θ) x1 x2 x3 (hlam_pos θ hθ)) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_laplacianRate_target_from_rum_source_and_atom_continuity
    lam hlam_pos hlam_mono hlam_tendsto hθH
    hvalue1 hvalue2 hvalue3 hx12 hx23 hdist_atom_continuity hdist

/--
Theorem 2 / Gaussian RUM route: if `F.dist θ` is the three-candidate Gaussian
RUM law with standard deviation `1 / θ`, then the monoculture-paradox target
follows from the remaining limit/continuity boundary.
-/
theorem theorem2_gaussianStd_target_from_rum_limit_boundary
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ, 0 < θ →
        F.dist θ =
          rumRankingPMFOfMeasure
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (rum3RankByScoreFns
              theorem8GaussianDefinition2Score1
              theorem8GaussianDefinition2Score2
              theorem8GaussianDefinition2Score3)
            (rum3RankByScoreFns_measurable
              theorem8GaussianDefinition2Score1_measurable
              theorem8GaussianDefinition2Score2_measurable
              theorem8GaussianDefinition2Score3_measurable))
    (boundary : Theorem2RUMLimitBoundary F) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_gaussianStd_target_from_rum_limit_boundary
    hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist boundary

/--
Theorem 2 / Laplace RUM route: if `F.dist θ` is the three-candidate Laplace
RUM law with positive strictly increasing rate `λ θ`, then the
monoculture-paradox target follows from the remaining limit/continuity boundary.
-/
theorem theorem2_laplacianRate_target_from_rum_limit_boundary
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (lam : ℝ → ℝ)
    (hlam_pos : ∀ θ, 0 < θ → 0 < lam θ)
    (hlam_mono : ∀ θA θH, 0 < θH → θH < θA → lam θH < lam θA)
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ (hθ : 0 < θ),
        F.dist θ =
          theorem7LaplacianDefinition2RankingPMF
            (lam θ) x1 x2 x3 (hlam_pos θ hθ))
    (boundary : Theorem2RUMLimitBoundary F) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_laplacianRate_target_from_rum_limit_boundary
    lam hlam_pos hlam_mono hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist
    boundary

/-! ## Theorems 1, 3, and 9 -/

/--
Paper Theorem 1, conditional family form: if a finite accuracy family satisfies
the paper's Definition 1 analytic conditions, Definition 2 independent
reranking condition, and Definition 3 weaker-competition condition, then every
positive human accuracy admits a more accurate algorithmic accuracy witnessing
the monoculture paradox.

The `assumptions` input is the Lean package of those paper hypotheses. Concrete
Mallows, Gaussian, and Laplace source routes below construct that package rather
than assuming it as an external boundary.

Source status: paper theorem from source conditions.
-/
theorem theorem1_from_paper_assumptions
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (hθH : 0 < θH)
    (assumptions : AccuracyFamily.Theorem1PaperAssumptions F) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem1_from_paper_assumptions F θH hθH assumptions

/--
Paper Theorem 3, Mallows form: for Mallows laws with a common center, if the
algorithmic law is more accurate than the human law, then every strictly
center-ordered value profile satisfies the paper's Definition 2 and Definition
3 hypotheses for the induced two-distribution model.

Lean uses the inverse Mallows parameter `q`, so greater accuracy is
`C.algorithm.q < C.human.q`. The rank-factorization formulas used by the source
proof are proved for `MallowsSpec` and are not exposed as assumptions here.

Source status: derived from source primitives.
-/
theorem theorem3_mallows_satisfies_paper_hypotheses
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hn : 0 < n)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hq_lt : C.algorithm.q < C.human.q) :
    Model.PaperHypotheses (C.toModel value) :=
  KR21Monoculture.MallowsComparison.paper_theorem3_pointwise_rankFactorization
    C hstrict hn halg_q_lt_one hhuman_q_lt_one hq_lt

/--
Appendix E / Theorem 9: concrete Mallows families satisfy the paper-level
assumption package consumed by Theorem 1.
-/
noncomputable def theorem9_concrete_mallows_family_assumptions
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value)
    (hn : 0 < n) :
    AccuracyFamily.Theorem1PaperAssumptions
      (MallowsAccuracyFamilySpec.toAccuracyFamily
        (concreteMallowsAccuracyFamilySpec center value hvalue)) :=
  KR21Monoculture.paper_theorem9_concrete_mallows_family_assumptions
    center value hvalue hn

/--
Paper Theorem 1, concrete Mallows family form: for a strict center-ordered
value profile and positive human accuracy, the concrete Mallows accuracy family
has a more accurate algorithmic parameter witnessing the monoculture paradox.
-/
theorem theorem1_concrete_mallows_family
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value)
    (hn : 0 < n) (θH : ℝ) (hθH : 0 < θH) :
    AccuracyFamily.Theorem1Target
      (MallowsAccuracyFamilySpec.toAccuracyFamily
        (concreteMallowsAccuracyFamilySpec center value hvalue))
      θH :=
  KR21Monoculture.paper_theorem1_concrete_mallows_family
    center value hvalue hn θH hθH

/-! ## Theorem 4 -/

/--
Theorem 4 / Mallows weak optimality: when human and algorithmic Mallows laws
share the same center ranking and the human law is weakly more accurate, the
all-human sequence is a best-response sequence in the multi-firm game.

This route uses the reduced same-size prefix-cut weighted-extremes Mallows
theorem, proved in Lean as
`reflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes_of_q_lt`.
-/
theorem theorem4_mallows_all_human_sequence_optimal_of_q_le
    {n k : ℕ} {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy human.center value) :
    (SequentialModel.ofMallows algorithm human value).IsSequentialBestResponseSequence k
      (SequentialModel.allHumanSequence k) :=
    KR21Monoculture.MallowsComparison.paper_theorem4_mallows_all_human_sequence_optimal_of_q_le
      hcenter hq_le hvalue

/--
Theorem 4 / Mallows strict uniqueness: if the human Mallows law has strictly
lower inverse-noise parameter than the algorithmic law, then at every
nonterminal history the human ranking distribution is the unique best response.
-/
theorem theorem4_mallows_human_unique_at_each_history_of_q_lt
    {n k : ℕ} {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_lt : human.q < algorithm.q)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy human.center value) :
    SequentialModel.HumanUniquelyOptimalAtAllNonterminalHistories
      (SequentialModel.ofMallows algorithm human value) k :=
  KR21Monoculture.MallowsComparison.paper_theorem4_mallows_human_unique_at_each_history_of_q_lt
    hcenter hq_lt hvalue

end PaperInterface
end KR21Monoculture
