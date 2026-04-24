import Monoculture.Family
import Monoculture.Payoff
import DecisionCore.EpsilonContinuity
import DecisionCore.IntervalCrossing

open DecisionCore

namespace Monoculture
namespace AccuracyFamily

/-!
# Theorem 1 Payoff Bridge

This file formalizes the game-theoretic core of paper Theorem 1.  The remaining
analytic task is to instantiate the crossing certificate from Definition 1's
differentiability/asymptotic-optimality/monotonicity assumptions.
-/

/--
Paper proof notation:

`f(θA) = UA(θA, θH) + UAA(θA, θH)`.

This is the random-order payoff numerator for using the algorithm when the
opponent also uses the algorithm.
-/
noncomputable def theorem1_f {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ) : ℝ :=
  let M := F.modelAt θA θH
  Model.firstMoverEU M Strategy.algorithm +
    Model.secondMoverEU M Strategy.algorithm Strategy.algorithm

/--
Paper proof notation:

`g(θA) = UH(θA, θH) + UAH(θA, θH)`.

This is the random-order payoff numerator for using a human evaluator when the
opponent uses the algorithm.
-/
noncomputable def theorem1_g {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ) : ℝ :=
  let M := F.modelAt θA θH
  Model.firstMoverEU M Strategy.human +
    Model.secondMoverEU M Strategy.algorithm Strategy.human

/--
Paper proof notation:

`h(θA) = UH(θA, θH) + UHH(θA, θH)`.

This is both the all-human welfare expression and the payoff numerator for using
a human evaluator when the opponent also uses a human evaluator.
-/
noncomputable def theorem1_h {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ) : ℝ :=
  let M := F.modelAt θA θH
  Model.firstMoverEU M Strategy.human +
    Model.secondMoverEU M Strategy.human Strategy.human

/--
The second strict-dominance numerator in the paper:

`UA(θA, θH) + UHA(θA, θH)`.
-/
noncomputable def theorem1_algorithmAgainstHuman {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ) : ℝ :=
  let M := F.modelAt θA θH
  Model.firstMoverEU M Strategy.algorithm +
    Model.secondMoverEU M Strategy.human Strategy.algorithm

/--
Expected value of the best candidate remaining under `μ` after a fixed candidate
has already been removed.
-/
noncomputable def expectedBestAfterRemoval {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n) : ℝ :=
  pmfExp μ (fun π => value (bestRemainingAfter π c))

/--
Second-mover utility can be read as first averaging, over the first mover's draw,
the second mover's expected best remaining candidate after that first choice is
removed.
-/
theorem expectedSecondMoverIndependent_eq_expect_bestAfterRemoval {n : ℕ}
    (μSecond μFirst : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μSecond μFirst value =
      pmfExp μFirst
        (fun σ => expectedBestAfterRemoval μSecond value (firstChoice σ)) := by
  unfold expectedSecondMoverIndependent expectedBestAfterRemoval
  rw [pmfPairExp_swap]
  rfl

/-- In the paper's notation, `h(θA)` is constant as `θA` varies. -/
theorem theorem1_h_const {n : ℕ} (F : AccuracyFamily n) (θA θA' θH : ℝ) :
    theorem1_h F θA θH = theorem1_h F θA' θH := by
  simp [theorem1_h, modelAt, Model.firstMoverEU, Model.secondMoverEU,
    Model.rankingDist]

/-- `f(θA)` is exactly all-algorithm random-order welfare. -/
theorem theorem1_f_eq_algorithm_welfare {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ) :
    theorem1_f F θA θH =
      Model.welfareRandomOrder (F.modelAt θA θH)
        Strategy.algorithm Strategy.algorithm := by
  rw [Model.welfareRandomOrder_self]
  rw [Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU]
  rfl

/-- `h(θA)` is exactly all-human random-order welfare. -/
theorem theorem1_h_eq_human_welfare {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ) :
    theorem1_h F θA θH =
      Model.welfareRandomOrder (F.modelAt θA θH)
        Strategy.human Strategy.human := by
  rw [Model.welfareRandomOrder_self]
  rw [Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU]
  rfl

/-- Since `h(θA)` is constant in `θA`, it is epsilon-delta continuous. -/
theorem theorem1_h_epsilonContinuousAt {n : ℕ}
    (F : AccuracyFamily n) (θH θstar : ℝ) :
    EpsilonContinuousAt (fun θA => theorem1_h F θA θH) θstar := by
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro θA hdist
  change |theorem1_h F θA θH - theorem1_h F θstar θH| < ε
  rw [theorem1_h_const F θA θstar θH]
  simpa using hε

/--
If every ranking atom of the accuracy family is epsilon-delta continuous at
`θstar`, then the paper's all-algorithm welfare expression `f` is continuous
there. This is the finite-probability bridge needed by the local nudge
certificate.
-/
theorem theorem1_f_epsilonContinuousAt_of_atom_continuity {n : ℕ}
    (F : AccuracyFamily n) (θH θstar : ℝ)
    (hdist :
      ∀ π : Ranking n, EpsilonContinuousAt (fun θA => ((F.dist θA) π).toReal) θstar) :
    EpsilonContinuousAt (fun θA => theorem1_f F θA θH) θstar := by
  dsimp [theorem1_f, modelAt, Model.firstMoverEU, Model.secondMoverEU,
    Model.rankingDist, expectedFirstMoverUtility, expectedSecondMoverShared]
  exact epsilonContinuousAt_add
    (epsilonContinuousAt_pmfExp_of_atom
      (μ := fun θA => F.dist θA)
      (x := θstar)
      hdist
      (fun π => F.value (firstChoice π)))
    (epsilonContinuousAt_pmfExp_of_atom
      (μ := fun θA => F.dist θA)
      (x := θstar)
      hdist
      (fun π => F.value (secondChoice π)))

/--
The paper's `f < h` persistence step follows from finite atomwise continuity of
the ranking law. This isolates the continuity part of the final nudge from the
separate one-sided crossing obligation `g < f`.
-/
theorem theorem1_f_lt_h_persists_right_of_atom_continuity {n : ℕ}
    (F : AccuracyFamily n) (θH θstar : ℝ)
    (hdist :
      ∀ π : Ranking n, EpsilonContinuousAt (fun θA => ((F.dist θA) π).toReal) θstar)
    (hgap : theorem1_f F θstar θH < theorem1_h F θstar θH) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ θA : ℝ, θstar < θA → θA < θstar + δ →
        theorem1_f F θA θH < theorem1_h F θA θH :=
  exists_right_radius_lt_of_epsilonContinuousAt
    (theorem1_f_epsilonContinuousAt_of_atom_continuity F θH θstar hdist)
    (theorem1_h_epsilonContinuousAt F θH θstar)
    hgap

/--
The local monotonicity consequences of Definition 1 used for inequality (5) in
the proof of Theorem 1.
-/
structure Theorem1MonotonicityAt {n : ℕ} (F : AccuracyFamily n) (θA θH : ℝ) :
    Prop where
  firstMover_strict :
    Model.firstMoverEU (F.modelAt θA θH) Strategy.human <
      Model.firstMoverEU (F.modelAt θA θH) Strategy.algorithm
  secondMover_weak :
    Model.secondMoverEU (F.modelAt θA θH) Strategy.human Strategy.human ≤
      Model.secondMoverEU (F.modelAt θA θH) Strategy.human Strategy.algorithm

/--
The finite-removal form of Definition 1 monotonicity needed for inequality (5).
The first field is the strict `S = ∅` case; the second field is the weak
singleton-removal case, pointwise in the removed candidate.
-/
structure Theorem1RemovalMonotonicityAt {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ) : Prop where
  firstMover_strict :
    expectedFirstMoverUtility (F.dist θH) F.value <
      expectedFirstMoverUtility (F.dist θA) F.value
  bestRemaining_weak :
    ∀ c : Candidate n,
      expectedBestAfterRemoval (F.dist θH) F.value c ≤
        expectedBestAfterRemoval (F.dist θA) F.value c

/--
Definition 1's finite-removal monotonicity implies the local monotonicity
certificate used by Theorem 1.
-/
theorem theorem1MonotonicityAt_of_removalMonotonicity {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ)
    (hmono : Theorem1RemovalMonotonicityAt F θA θH) :
    Theorem1MonotonicityAt F θA θH := by
  constructor
  · simpa [modelAt, Model.firstMoverEU, Model.rankingDist] using
      hmono.firstMover_strict
  · simp [modelAt, Model.secondMoverEU, Model.rankingDist]
    rw [expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    rw [expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    exact pmfExp_le_pmfExp_of_forall_le
      (F.dist θH)
      (fun σ => expectedBestAfterRemoval (F.dist θH) F.value (firstChoice σ))
      (fun σ => expectedBestAfterRemoval (F.dist θA) F.value (firstChoice σ))
      (fun σ => hmono.bestRemaining_weak (firstChoice σ))

/--
The paper's final crossing state: after the initial equality point is nudged
upward, `g < f < h`, and monotonicity supplies the second dominance inequality.
-/
structure Theorem1CrossingCertificate {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) :
    Type where
  θA : ℝ
  theta_gt : θH < θA
  first_dominance_crossing : theorem1_g F θA θH < theorem1_f F θA θH
  welfare_gap_persists : theorem1_f F θA θH < theorem1_h F θA θH
  monotonicity : Theorem1MonotonicityAt F θA θH

/--
The paper's final "slightly increase `θA`" step as a right-neighborhood
certificate.  It is designed to be instantiated later from continuity and the
chosen crossing point.
-/
structure Theorem1RightNudgeCertificate {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) :
    Type where
  θstar : ℝ
  radius : ℝ
  thetaH_lt_star : θH < θstar
  radius_pos : 0 < radius
  between_on_right :
    ∀ θA, θstar < θA → θA < θstar + radius →
      theorem1_g F θA θH < theorem1_f F θA θH ∧
        theorem1_f F θA θH < theorem1_h F θA θH
  monotonicity :
    ∀ θA, θH < θA → Theorem1MonotonicityAt F θA θH

/--
A local analytic certificate for the paper's final nudge. The `g < f` side is
given on a right interval after `θstar`; the `f < h` side is obtained from
epsilon-delta continuity of `f` and the strict inequality at `θstar`.
-/
structure Theorem1LocalNudgeCertificate {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) :
    Type where
  θstar : ℝ
  gf_radius : ℝ
  thetaH_lt_star : θH < θstar
  gf_radius_pos : 0 < gf_radius
  f_epsilonContinuousAt :
    EpsilonContinuousAt (fun θA => theorem1_f F θA θH) θstar
  f_lt_h_at_star : theorem1_f F θstar θH < theorem1_h F θstar θH
  first_dominance_on_right :
    ∀ θA, θstar < θA → θA < θstar + gf_radius →
      theorem1_g F θA θH < theorem1_f F θA θH
  monotonicity :
    ∀ θA, θH < θA → Theorem1MonotonicityAt F θA θH

/--
A local nudge certificate whose continuity field is stated at the finite PMF
atom level.  This is closer to Definition 1's family-level continuity premise
than asking directly for continuity of the already-aggregated payoff `f`.
-/
structure Theorem1AtomLocalNudgeCertificate {n : ℕ}
    (F : AccuracyFamily n) (θH : ℝ) : Type where
  θstar : ℝ
  gf_radius : ℝ
  thetaH_lt_star : θH < θstar
  gf_radius_pos : 0 < gf_radius
  dist_atom_continuity :
    ∀ π : Ranking n, EpsilonContinuousAt (fun θA => ((F.dist θA) π).toReal) θstar
  f_lt_h_at_star : theorem1_f F θstar θH < theorem1_h F θstar θH
  first_dominance_on_right :
    ∀ θA, θstar < θA → θA < θstar + gf_radius →
      theorem1_g F θA θH < theorem1_f F θA θH
  monotonicity :
    ∀ θA, θH < θA → Theorem1MonotonicityAt F θA θH

/--
An interval sign-change certificate for the paper's final nudge.  It replaces a
direct right-neighborhood `g < f` assumption with a compact-interval argument:
on `[lo, hi]`, `f - g` is continuous, starts nonpositive, and ends positive.
Lean then chooses the last nonpositive point.
-/
structure Theorem1SignChangeNudgeCertificate {n : ℕ}
    (F : AccuracyFamily n) (θH : ℝ) : Type where
  lo : ℝ
  hi : ℝ
  thetaH_lt_lo : θH < lo
  lo_lt_hi : lo < hi
  diff_continuousOn :
    ContinuousOn (fun θA => theorem1_f F θA θH - theorem1_g F θA θH)
      (Set.Icc lo hi)
  nonpos_at_lo : theorem1_f F lo θH ≤ theorem1_g F lo θH
  positive_at_hi : theorem1_g F hi θH < theorem1_f F hi θH
  dist_atom_continuity :
    ∀ θA, lo ≤ θA → θA < hi →
      ∀ π : Ranking n, EpsilonContinuousAt (fun θ => ((F.dist θ) π).toReal) θA
  weaker_side :
    ∀ θA, θH < θA → θA < hi → theorem1_g F θA θH < theorem1_h F θA θH
  monotonicity :
    ∀ θA, θH < θA → Theorem1MonotonicityAt F θA θH

/--
Paper-shaped interval certificate for the final Theorem 1 nudge.  Compared with
`Theorem1SignChangeNudgeCertificate`, this version asks for Definitions 2/3 as
`Model.PaperHypotheses` and for Definition 1 monotonicity in finite-removal
form; Lean fills the exact payoff fields.
-/
structure Theorem1IntervalAnalyticCertificate {n : ℕ}
    (F : AccuracyFamily n) (θH : ℝ) : Type where
  lo : ℝ
  hi : ℝ
  thetaH_lt_lo : θH < lo
  lo_lt_hi : lo < hi
  diff_continuousOn :
    ContinuousOn (fun θA => theorem1_f F θA θH - theorem1_g F θA θH)
      (Set.Icc lo hi)
  nonpos_at_lo : theorem1_f F lo θH ≤ theorem1_g F lo θH
  positive_at_hi : theorem1_g F hi θH < theorem1_f F hi θH
  dist_atom_continuity :
    ∀ θA, lo ≤ θA → θA < hi →
      ∀ π : Ranking n, EpsilonContinuousAt (fun θ => ((F.dist θ) π).toReal) θA
  paper_hypotheses_on_interval :
    ∀ θA, θH < θA → θA < hi → Model.PaperHypotheses (F.modelAt θA θH)
  removal_monotonicity :
    ∀ θA, θH < θA → Theorem1RemovalMonotonicityAt F θA θH

/--
The direct payoff certificate for Theorem 1's conclusion.
-/
structure Theorem1PayoffCertificate {n : ℕ} (F : AccuracyFamily n) (θH : ℝ) :
    Type where
  θA : ℝ
  theta_gt : θH < θA
  algorithm_beats_human_against_algorithm :
    theorem1_g F θA θH < theorem1_f F θA θH
  algorithm_beats_human_against_human :
    theorem1_h F θA θH < theorem1_algorithmAgainstHuman F θA θH
  human_welfare_beats_algorithm :
    theorem1_f F θA θH < theorem1_h F θA θH

/--
Monotonicity converts the paper's inequality (5) into the second strict
dominance comparison.
-/
theorem theorem1_algorithmAgainstHuman_gt_h_of_monotonicity {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ)
    (hmono : Theorem1MonotonicityAt F θA θH) :
    theorem1_h F θA θH < theorem1_algorithmAgainstHuman F θA θH := by
  unfold theorem1_h theorem1_algorithmAgainstHuman
  linarith [hmono.firstMover_strict, hmono.secondMover_weak]

/--
The crossing certificate is exactly the paper's final `g < f < h` step plus the
monotonicity proof of inequality (5).
-/
def payoffCertificate_of_crossingCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1CrossingCertificate F θH) :
    Theorem1PayoffCertificate F θH where
  θA := cert.θA
  theta_gt := cert.theta_gt
  algorithm_beats_human_against_algorithm := cert.first_dominance_crossing
  algorithm_beats_human_against_human :=
    theorem1_algorithmAgainstHuman_gt_h_of_monotonicity
      F cert.θA θH cert.monotonicity
  human_welfare_beats_algorithm := cert.welfare_gap_persists

/--
The right-neighborhood version of the paper's nudge step supplies a concrete
crossing certificate by choosing the midpoint `θstar + radius / 2`.
-/
noncomputable def crossingCertificate_of_rightNudgeCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1RightNudgeCertificate F θH) :
    Theorem1CrossingCertificate F θH := by
  let θA := cert.θstar + cert.radius / 2
  have hhalf_pos : 0 < cert.radius / 2 := half_pos cert.radius_pos
  have hstar_lt : cert.θstar < θA := by
    dsimp [θA]
    linarith
  have hθ : θH < θA := cert.thetaH_lt_star.trans hstar_lt
  have hwithin : θA < cert.θstar + cert.radius := by
    dsimp [θA]
    linarith
  have hbetween := cert.between_on_right θA hstar_lt hwithin
  exact
    { θA := θA
      theta_gt := hθ
      first_dominance_crossing := hbetween.1
      welfare_gap_persists := hbetween.2
      monotonicity := cert.monotonicity θA hθ }

/--
A payoff certificate yields the fixed-parameter monoculture paradox.
-/
theorem hasMonocultureParadox_of_payoffCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1PayoffCertificate F θH) :
    Model.HasMonocultureParadox (F.modelAt cert.θA θH) := by
  constructor
  · unfold Model.AlgorithmStrictlyDominant
    constructor
    · simpa [theorem1_f, theorem1_g] using
        cert.algorithm_beats_human_against_algorithm
    · simpa [theorem1_h, theorem1_algorithmAgainstHuman] using
        cert.algorithm_beats_human_against_human
  · unfold Model.HumanProfileBeatsAlgorithmProfile
    rw [Model.welfareRandomOrder_self, Model.welfareRandomOrder_self]
    rw [Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU,
      Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU]
    simpa [theorem1_f, theorem1_h] using cert.human_welfare_beats_algorithm

/--
Paper Theorem 1, conditional on the final crossing certificate.
-/
theorem theorem1Target_of_payoffCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1PayoffCertificate F θH) :
    Theorem1Target F θH := by
  exact ⟨cert.θA, cert.theta_gt, hasMonocultureParadox_of_payoffCertificate cert⟩

/--
Paper Theorem 1, conditional on the crossing certificate produced by the paper's
continuity/asymptotic-optimality argument.
-/
theorem theorem1Target_of_crossingCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1CrossingCertificate F θH) :
    Theorem1Target F θH :=
  theorem1Target_of_payoffCertificate
    (payoffCertificate_of_crossingCertificate cert)

/--
Paper Theorem 1 from the right-neighborhood nudge certificate.
-/
theorem theorem1Target_of_rightNudgeCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1RightNudgeCertificate F θH) :
    Theorem1Target F θH :=
  theorem1Target_of_crossingCertificate
    (crossingCertificate_of_rightNudgeCertificate cert)

/--
Paper Theorem 1 from the local analytic nudge certificate.
-/
theorem theorem1Target_of_localNudgeCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1LocalNudgeCertificate F θH) :
    Theorem1Target F θH := by
  rcases exists_right_radius_lt_of_epsilonContinuousAt
      cert.f_epsilonContinuousAt
      (theorem1_h_epsilonContinuousAt F θH cert.θstar)
      cert.f_lt_h_at_star with
    ⟨fh_radius, hfh_radius_pos, hfh⟩
  refine theorem1Target_of_rightNudgeCertificate ?_
  refine
    { θstar := cert.θstar
      radius := min cert.gf_radius fh_radius
      thetaH_lt_star := cert.thetaH_lt_star
      radius_pos := lt_min cert.gf_radius_pos hfh_radius_pos
      between_on_right := ?_
      monotonicity := cert.monotonicity }
  intro θA hstar hwithin
  have hgf_within : θA < cert.θstar + cert.gf_radius := by
    have hmin : min cert.gf_radius fh_radius ≤ cert.gf_radius :=
      min_le_left cert.gf_radius fh_radius
    linarith
  have hfh_within : θA < cert.θstar + fh_radius := by
    have hmin : min cert.gf_radius fh_radius ≤ fh_radius :=
      min_le_right cert.gf_radius fh_radius
    linarith
  exact ⟨cert.first_dominance_on_right θA hstar hgf_within,
    hfh θA hstar hfh_within⟩

/-- Convert atomwise continuity into the aggregated local nudge certificate. -/
def localNudgeCertificate_of_atomLocalNudgeCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1AtomLocalNudgeCertificate F θH) :
    Theorem1LocalNudgeCertificate F θH where
  θstar := cert.θstar
  gf_radius := cert.gf_radius
  thetaH_lt_star := cert.thetaH_lt_star
  gf_radius_pos := cert.gf_radius_pos
  f_epsilonContinuousAt :=
    theorem1_f_epsilonContinuousAt_of_atom_continuity
      F θH cert.θstar cert.dist_atom_continuity
  f_lt_h_at_star := cert.f_lt_h_at_star
  first_dominance_on_right := cert.first_dominance_on_right
  monotonicity := cert.monotonicity

/--
Paper Theorem 1 from the atomwise local analytic nudge certificate.
-/
theorem theorem1Target_of_atomLocalNudgeCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1AtomLocalNudgeCertificate F θH) :
    Theorem1Target F θH :=
  theorem1Target_of_localNudgeCertificate
    (localNudgeCertificate_of_atomLocalNudgeCertificate cert)

/--
Paper Theorem 1 from an interval sign-change nudge certificate.

This formalizes the robust version of the paper's crossing step: choose the last
point in an interval where `f ≤ g`; immediately to its right, `g < f`, while
`f < h` follows from `f ≤ g < h` at that point and finite atomwise continuity.
-/
theorem theorem1Target_of_signChangeNudgeCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1SignChangeNudgeCertificate F θH) :
    Theorem1Target F θH := by
  have hlo_nonpos :
      theorem1_f F cert.lo θH - theorem1_g F cert.lo θH ≤ 0 := by
    linarith [cert.nonpos_at_lo]
  have hhi_pos :
      0 < theorem1_f F cert.hi θH - theorem1_g F cert.hi θH := by
    linarith [cert.positive_at_hi]
  rcases exists_last_nonpos_with_right_pos_on_Icc
      (d := fun θA => theorem1_f F θA θH - theorem1_g F θA θH)
      cert.lo_lt_hi cert.diff_continuousOn hlo_nonpos hhi_pos with
    ⟨θstar, hlo_star, hstar_hi, hdiff_nonpos, hright_pos⟩
  have hthetaH_star : θH < θstar := cert.thetaH_lt_lo.trans_le hlo_star
  have hgap : theorem1_f F θstar θH < theorem1_h F θstar θH := by
    have hfg : theorem1_f F θstar θH ≤ theorem1_g F θstar θH := by
      linarith [hdiff_nonpos]
    have hgh : theorem1_g F θstar θH < theorem1_h F θstar θH :=
      cert.weaker_side θstar hthetaH_star hstar_hi
    exact lt_of_le_of_lt hfg hgh
  refine theorem1Target_of_atomLocalNudgeCertificate ?_
  refine
    { θstar := θstar
      gf_radius := (cert.hi - θstar) / 2
      thetaH_lt_star := hthetaH_star
      gf_radius_pos := by linarith
      dist_atom_continuity := cert.dist_atom_continuity θstar hlo_star hstar_hi
      f_lt_h_at_star := hgap
      first_dominance_on_right := ?_
      monotonicity := cert.monotonicity }
  intro θA hstar_lt hwithin
  have hθA_le_hi : θA ≤ cert.hi := by
    linarith
  have hpos := hright_pos θA hstar_lt hθA_le_hi
  linarith

/--
Definition 3 gives `g(θA) < h(θA)` at any pair `θA > θH` where the induced model
satisfies the paper hypotheses.
-/
theorem theorem1_g_lt_h_of_prefersWeakerCompetition {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ)
    (hweak :
      Model.PrefersWeakerCompetition (F.dist θA) (F.dist θH) F.value) :
    theorem1_g F θA θH < theorem1_h F θA θH := by
  unfold theorem1_g theorem1_h Model.PrefersWeakerCompetition at *
  simp [modelAt, Model.firstMoverEU, Model.secondMoverEU, Model.rankingDist] at *
  linarith

/--
Definition 3, read through `Model.PaperHypotheses`.
-/
theorem theorem1_g_lt_h_of_paperHypotheses {n : ℕ}
    (F : AccuracyFamily n) (θA θH : ℝ)
    (hpaper : Model.PaperHypotheses (F.modelAt θA θH)) :
    theorem1_g F θA θH < theorem1_h F θA θH :=
  theorem1_g_lt_h_of_prefersWeakerCompetition F θA θH hpaper.2

/-- Convert the paper-shaped interval certificate into the direct sign-change certificate. -/
def signChangeNudgeCertificate_of_intervalAnalyticCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1IntervalAnalyticCertificate F θH) :
    Theorem1SignChangeNudgeCertificate F θH where
  lo := cert.lo
  hi := cert.hi
  thetaH_lt_lo := cert.thetaH_lt_lo
  lo_lt_hi := cert.lo_lt_hi
  diff_continuousOn := cert.diff_continuousOn
  nonpos_at_lo := cert.nonpos_at_lo
  positive_at_hi := cert.positive_at_hi
  dist_atom_continuity := cert.dist_atom_continuity
  weaker_side := fun θA hθ hhi =>
    theorem1_g_lt_h_of_paperHypotheses F θA θH
      (cert.paper_hypotheses_on_interval θA hθ hhi)
  monotonicity := fun θA hθ =>
    theorem1MonotonicityAt_of_removalMonotonicity F θA θH
      (cert.removal_monotonicity θA hθ)

/--
Paper Theorem 1 from the interval analytic certificate.
-/
theorem theorem1Target_of_intervalAnalyticCertificate {n : ℕ}
    {F : AccuracyFamily n} {θH : ℝ}
    (cert : Theorem1IntervalAnalyticCertificate F θH) :
    Theorem1Target F θH :=
  theorem1Target_of_signChangeNudgeCertificate
    (signChangeNudgeCertificate_of_intervalAnalyticCertificate cert)

/--
Definition 2 supplies the initial strict inequality `f(θ) < g(θ)` when the
algorithm and human accuracies are equal.
-/
theorem theorem1_f_lt_g_of_prefersIndependent_equalAccuracy {n : ℕ}
    (F : AccuracyFamily n) (θ : ℝ)
    (hind : Model.PrefersIndependentReranking (F.dist θ) F.value) :
    theorem1_f F θ θ < theorem1_g F θ θ := by
  unfold theorem1_f theorem1_g Model.PrefersIndependentReranking at *
  simp [modelAt, Model.firstMoverEU, Model.secondMoverEU, Model.rankingDist] at *
  linarith

/--
Definition 2, read through `Model.PaperHypotheses` at equal accuracies.
-/
theorem theorem1_f_lt_g_of_paperHypotheses_equalAccuracy {n : ℕ}
    (F : AccuracyFamily n) (θ : ℝ)
    (hpaper : Model.PaperHypotheses (F.modelAt θ θ)) :
    theorem1_f F θ θ < theorem1_g F θ θ :=
  theorem1_f_lt_g_of_prefersIndependent_equalAccuracy F θ hpaper.1

end AccuracyFamily
end Monoculture
