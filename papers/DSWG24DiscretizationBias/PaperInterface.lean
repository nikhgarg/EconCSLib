import DSWG24DiscretizationBias.MainTheorems

/-!
# Paper Interface: DSWG24 Discretization Bias

This is the compact, human-facing Lean surface for the paper.  A reader should
be able to inspect this file alone and see the definitions and theorem
statements that correspond to the source paper.

The proofs are intentionally short calls into `MainTheorems.lean`, where the
implementation details and auxiliary lemmas live.
-/

namespace DSWG24DiscretizationBias
namespace PaperInterface

open scoped BigOperators ProbabilityTheory
open MeasureTheory

noncomputable section

/-! ## Paper Definitions -/

/-- Prior class probability `Pr(y)`. -/
def prior [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (y : Y) : ℝ :=
  ((Finite.labelMarginal μ) y).toReal

/-- Marginal label share `\hat p_marg(y) = (1/N) sum_i 1[\hat y_i = y]`. -/
def marginalLabelShare [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (rule : X → Y) (y : Y) : ℝ :=
  EconCSLib.pmfProb (Finite.featureMarginal μ) (fun x => rule x = y)

/-- Aggregate posterior `p_agg^q(y) = (1/N) sum_i q(y,x_i)`. -/
def aggregatePosterior [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (y : Y) : ℝ :=
  EconCSLib.pmfExp (Finite.featureMarginal μ) (fun x => q x y)

/-- Bias `bias(y, \hat y, p_ref) = \hat p_marg(y) - p_ref(y)`. -/
def bias [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (rule : X → Y) (pref : Y → ℝ) (y : Y) : ℝ :=
  marginalLabelShare μ rule y - pref y

/-- Distributional fidelity `fid(p_ref, \hat y) = -sum_y |bias(y,\hat y,p_ref)|`. -/
def fidelity [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (rule : X → Y) (pref : Y → ℝ) : ℝ :=
  -∑ y : Y, |bias μ rule pref y|

/-- Predictive MAE for Bayes posterior scores: `E_X sum_y q(y,x)(1-q(y,x))`. -/
def classifierMAE [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) : ℝ :=
  EconCSLib.pmfExp (Finite.featureMarginal μ)
    (fun x => ∑ y : Y, q x y * (1 - q x y))

/-- Continuous marginal label share: `∫ x, 1[rule x = y] dμ(x)`. -/
def continuousMarginalLabelShare {X Y : Type*} [MeasurableSpace X] [DecidableEq Y]
    (μ : Measure X) (rule : X → Y) (y : Y) : ℝ :=
  ∫ x, (if rule x = y then (1 : ℝ) else 0) ∂μ

/-- Continuous aggregate posterior reference: `∫ x, q x y dμ(x)`. -/
def continuousAggregatePosterior {X Y : Type*} [MeasurableSpace X]
    (μ : Measure X) (q : X → Y → ℝ) (y : Y) : ℝ :=
  ∫ x, q x y ∂μ

/-- Continuous bias relative to a supplied reference distribution. -/
def continuousBias {X Y : Type*} [MeasurableSpace X] [DecidableEq Y]
    (μ : Measure X) (rule : X → Y) (pref : Y → ℝ) (y : Y) : ℝ :=
  continuousMarginalLabelShare μ rule y - pref y

/-- Continuous aggregate-posterior bias. -/
def continuousAggregateBias {X Y : Type*} [MeasurableSpace X] [DecidableEq Y]
    (μ : Measure X) (q : X → Y → ℝ) (rule : X → Y) (y : Y) : ℝ :=
  continuousMarginalLabelShare μ rule y - continuousAggregatePosterior μ q y

/-- Continuous predictive MAE. -/
def continuousClassifierMAE {X Y : Type*} [MeasurableSpace X] [Fintype Y]
    (μ : Measure X) (q : X → Y → ℝ) : ℝ :=
  ∫ x, ∑ y : Y, q x y * (1 - q x y) ∂μ

/-- Joint prior-reference bias for Theorem 1's continuous statement. -/
def continuousJointPriorBias {X Y : Type*} [MeasurableSpace (X × Y)]
    [DecidableEq Y] (μ : Measure (X × Y)) (rule : X → Y) (y : Y) : ℝ :=
  (∫ xy, (if rule xy.1 = y then (1 : ℝ) else 0) ∂μ) -
    ∫ xy, (if xy.2 = y then (1 : ℝ) else 0) ∂μ

/-- Joint predictive MAE for Theorem 1's continuous statement. -/
def continuousJointClassifierMAE {X Y : Type*} [MeasurableSpace (X × Y)]
    [Fintype Y] (μ : Measure (X × Y)) (q : X → Y → ℝ) : ℝ :=
  ∫ xy, ∑ y : Y, q xy.1 y * (1 - q xy.1 y) ∂μ

/-- Posterior-simplex condition: each `q(x)` is a probability vector. -/
def posteriorSimplex {X Y : Type*} [Fintype Y] (q : X → Y → ℝ) : Prop :=
  (∀ x, (∑ y : Y, q x y) = 1) ∧
    (∀ x y, 0 ≤ q x y) ∧
      (∀ x y, q x y ≤ 1)

/-- Tie-broken argmax rule: the selected label has maximal posterior score. -/
def isArgmaxRule {X Y : Type*} (q : X → Y → ℝ) (rule : X → Y) : Prop :=
  ∀ x y, q x y ≤ q x (rule x)

/--
Calibration: for every label and every measurable score event, the true label
mass on that score event equals the aggregate posterior score mass on the same
event.  This is the paper's `Pr(Y=y | q(y,x)=c)=c` condition in
event-preimage form.
-/
def calibrated {X Y : Type*} [MeasurableSpace (X × Y)] [DecidableEq Y]
    (μ : Measure (X × Y)) (q : X → Y → ℝ) : Prop := by
  classical
  exact
    ∀ (y : Y) (s : Set ℝ), MeasurableSet s →
      (∫ xy, (if q xy.1 y ∈ s then
          if xy.2 = y then (1 : ℝ) else 0
        else 0) ∂μ) =
        ∫ xy, (if q xy.1 y ∈ s then q xy.1 y else 0) ∂μ

/--
Paper objective `O_N^gamma` for one observed dataset: `γ` times average
posterior score plus `(1 - γ)` times the fidelity term.
-/
def objective {N K : ℕ} {σ : Type*}
    (γ : ℝ) (posterior : σ → Fin N → Fin K → ℝ)
    (fidelityTerm : σ → (Fin N → Fin K) → ℝ)
    (xs : σ) (decision : Fin N → Fin K) : ℝ :=
  γ * EconCSLib.Decision.averageScore (posterior xs) decision +
    (1 - γ) * fidelityTerm xs decision

/-- Expected paper objective using true-label accuracy plus expected fidelity. -/
def expectedObjective {ω σ : Type*} {N K : ℕ} [NeZero K]
    (expect : (ω → ℝ) → ℝ) (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (γ : ℝ) (fidelityTerm : σ → (Fin N → Fin K) → ℝ)
    (rule : σ → Fin N → Fin K) : ℝ :=
  γ * EconCSLib.Decision.expectedDecisionAccuracy
      expect observedDataset trueLabels rule +
    (1 - γ) * EconCSLib.Decision.expectedObjective
      expect observedDataset fidelityTerm rule

/-- Source proof region `S_a`: focal posterior is `1`. -/
def sourceSa {X Y : Type*} (q : X → Y → ℝ) (z : Y) : Set X :=
  {x | q x z = 1}

/-- Source proof region `S_b`: focal posterior is in `(1/K,1)`. -/
def sourceSb {X Y : Type*} [Fintype Y] (q : X → Y → ℝ) (z : Y) : Set X :=
  {x | (Fintype.card Y : ℝ)⁻¹ < q x z ∧ q x z < 1}

/-- Source proof region `S_c`: focal posterior is exactly `1/K`. -/
def sourceSc {X Y : Type*} [Fintype Y] (q : X → Y → ℝ) (z : Y) : Set X :=
  {x | q x z = (Fintype.card Y : ℝ)⁻¹}

/-- Source proof region `S_d`: focal posterior is in `(0,1/K)`. -/
def sourceSd {X Y : Type*} [Fintype Y] (q : X → Y → ℝ) (z : Y) : Set X :=
  {x | 0 < q x z ∧ q x z < (Fintype.card Y : ℝ)⁻¹}

/-- Source proof region `S_e`: focal posterior is `0`. -/
def sourceSe {X Y : Type*} (q : X → Y → ℝ) (z : Y) : Set X :=
  {x | q x z = 0}

/-! ## Theorem 1 -/

/--
Theorem 1(i): if features provide no information and all rows are assigned to
a plurality class `z`, then plurality-class bias is `1 - Pr(z)` and every other
class has bias `-Pr(y)`.  The same formula holds whether the reference is the
prior or the aggregate posterior.
-/
theorem theorem1i_no_information_bias
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (z y : Y)
    (hnoInformation : ∀ x a, q x a = prior μ a)
    (hplurality : ∀ a, prior μ a ≤ prior μ z) :
    (bias μ (fun _ : X => z) (prior μ) y =
        if z = y then 1 - prior μ y else -prior μ y) ∧
      (bias μ (fun _ : X => z) (aggregatePosterior μ q) y =
        if z = y then 1 - prior μ y else -prior μ y) := by
  classical
  have hprior :
      bias μ (fun _ : X => z) (prior μ) y =
        if z = y then 1 - prior μ y else -prior μ y := by
    simpa [bias, prior, marginalLabelShare, Finite.paperBias,
      Finite.paperPrior, Finite.paperMarginalLabelShare] using
      (Finite.paper_theorem1i_no_information_prior_bias μ z y)
  have hagg : aggregatePosterior μ q y = prior μ y := by
    unfold aggregatePosterior
    have hfun : (fun x : X => q x y) = fun _ : X => prior μ y := by
      funext x
      exact hnoInformation x y
    rw [hfun]
    exact EconCSLib.pmfExp_const (Finite.featureMarginal μ) (prior μ y)
  exact ⟨hprior, by simpa [bias, hagg] using hprior⟩

/--
Theorem 1(ii): if the induced decision rule agrees pointwise with the true
label, then prior-reference amplification bias is zero.
-/
theorem theorem1ii_perfect_classifier_zero_bias
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (rule : X → Y)
    (htruth : ∀ xy : X × Y, rule xy.1 = xy.2) (y : Y) :
    bias μ rule (prior μ) y = 0 := by
  simpa [bias, prior, marginalLabelShare, Finite.paperBias, Finite.paperPrior,
    Finite.paperMarginalLabelShare] using
    (Finite.paper_theorem1ii_perfect_classifier_prior_bias_zero μ rule htruth y)

/--
Theorem 1(iii): for a calibrated posterior classifier and a tie-broken argmax
rule, argmax bias is bounded above by predictive MAE.

The assumptions below are the formal versions of the paper's implicit
measurability, posterior-simplex, and calibration requirements.
-/
theorem theorem1iii_argmax_bias_le_mae
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Fintype Y] [DecidableEq Y]
    (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (q : X → Y → ℝ) (argmaxRule : X → Y) (y : Y)
    (hrule : Measurable argmaxRule)
    (hargmax : isArgmaxRule q argmaxRule)
    (hsimplex : posteriorSimplex q)
    (hscore : ∀ y : Y, Measurable (fun xy : X × Y => q xy.1 y))
    (hcal : calibrated μ q) :
    continuousJointPriorBias μ argmaxRule y ≤
      continuousJointClassifierMAE μ q := by
  have hcal' : ContinuousTheorem1.ContinuousCalibration μ q := by
    simpa [calibrated, ContinuousTheorem1.ContinuousCalibration] using hcal
  simpa [continuousJointPriorBias, continuousJointClassifierMAE,
    isArgmaxRule, posteriorSimplex, calibrated,
    ContinuousTheorem1.ContinuousCalibration,
    ContinuousTheorem1.continuousJointPriorBias,
    ContinuousTheorem1.continuousJointClassifierMAE,
    Finite.paperConditionalMAE] using
    (ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_continuousCalibration_finite_simplex
      μ q argmaxRule y hrule hargmax hsimplex.1 hsimplex.2.1 hscore hcal')

/--
Theorem 1(iii) tightness: there is a binary one-feature instance where
argmax bias equals predictive MAE.
-/
theorem theorem1iii_tight_binary_example :
    bias Finite.paperTheorem1TightMu Finite.paperTheorem1TightArgmax
        (aggregatePosterior Finite.paperTheorem1TightMu Finite.paperTheorem1TightQ) 0 =
      classifierMAE Finite.paperTheorem1TightMu Finite.paperTheorem1TightQ := by
  change
    Finite.paperAggregateBias Finite.paperTheorem1TightMu
      Finite.paperTheorem1TightQ Finite.paperTheorem1TightArgmax 0 =
        Finite.paperClassifierMAE Finite.paperTheorem1TightMu
          Finite.paperTheorem1TightQ
  exact Finite.paper_theorem1iii_tight_binary_uniform_example

/-! ## Theorem 2 -/

/--
Theorem 2(i): for Bayes-optimal scores, every `gamma` and fidelity/reference
term has a joint decision rule maximizing the expected objective `O_N^gamma`.
-/
theorem theorem2i_joint_rule_exists
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hNK : K < N)
    (expect : (ω → ℝ) → ℝ)
    (hlin : EconCSLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (γ : ℝ) (posterior : σ → Fin N → Fin K → ℝ)
    (fidelityTerm : σ → (Fin N → Fin K) → ℝ)
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) :
    ∃ optRule : σ → Fin N → Fin K,
      ∀ rule : σ → Fin N → Fin K,
        expectedObjective expect observedDataset trueLabels γ fidelityTerm rule ≤
          expectedObjective expect observedDataset trueLabels γ fidelityTerm optRule := by
  simpa [expectedObjective, paperExpectedONObjective] using
    (paper_theorem2i_joint_optimization_rule_exists
      hK hNK expect hlin observedDataset trueLabels γ posterior fidelityTerm hbayesRow)

/--
Theorem 2(ii): for Bayes-optimal scores, a pointwise argmax rule maximizes
expected accuracy.
-/
theorem theorem2ii_argmax_accuracy_maximizing
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hNK : K < N)
    (expect : (ω → ℝ) → ℝ)
    (hlin : EconCSLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (posterior : σ → Fin N → Fin K → ℝ)
    {decisionRule argmaxRule : σ → Fin N → Fin K}
    (hargmax :
      ∀ xs, EconCSLib.Decision.IsPointwiseMax (posterior xs) (argmaxRule xs))
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) :
    EconCSLib.Decision.expectedDecisionAccuracy
        expect observedDataset trueLabels decisionRule ≤
      EconCSLib.Decision.expectedDecisionAccuracy
        expect observedDataset trueLabels argmaxRule := by
  exact paper_theorem2ii_argmax_expected_accuracy_maximizing
    hK hNK expect hlin observedDataset trueLabels posterior hargmax hbayesRow

/--
Theorem 2(iii), Pareto part: any independent rule that disagrees with argmax
with positive probability is not Pareto optimal for a non-trivial reference
distribution.
-/
theorem theorem2iii_non_argmax_not_pareto
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ) (pref : Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (hdisagree :
      0 < EconCSLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x))
    (hNpos : 0 < N)
    (hpref_nonneg : ∀ y, 0 ≤ pref y)
    (hpref_sum : (∑ y : Fin K, pref y) = 1)
    (hnontrivial : ∀ y : Fin K, 1 / (N : ℝ) ≤ pref y)
    (hweak_argmax : ∀ x y, posterior x y ≤ posterior x (argmaxRule x)) :
    ¬ Pareto.ParetoOptimal
      (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
        (fun s => Theorem2iii.sampledPosterior posterior s))
      (Theorem2iii.expectedDatasetFidelity (Theorem2iii.iidSamplePMF μ N) pref)
      (fun s => Theorem2iii.sampledDecision rule s) := by
  exact
    Theorem2iii.paper_theorem2iii_not_expected_pareto_of_independent_rule_disagrees_pos
      μ posterior pref rule argmaxRule hdisagree hNpos hpref_nonneg hpref_sum
      hnontrivial hweak_argmax

/--
Theorem 2(iii), objective part for `gamma < 1`: under the usual argmax
maximality certificate, an independent rule maximizes the weighted expected
objective iff it agrees with argmax with probability one.
-/
theorem theorem2iii_weighted_objective_maximizer_iff_agrees_argmax
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ) (pref : Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    {γ : ℝ} (hγnonneg : 0 ≤ γ) (hγlt : γ < 1)
    (hNpos : 0 < N)
    (hpref_nonneg : ∀ y, 0 ≤ pref y)
    (hpref_sum : (∑ y : Fin K, pref y) = 1)
    (hnontrivial : ∀ y : Fin K, 1 / (N : ℝ) ≤ pref y)
    (hweak_argmax : ∀ x y, posterior x y ≤ posterior x (argmaxRule x))
    (hargmaxMax :
      ∀ other : (Fin N → X) → Fin N → Fin K,
        Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun s => Theorem2iii.sampledPosterior posterior s))
            (Theorem2iii.expectedDatasetFidelity (Theorem2iii.iidSamplePMF μ N) pref) other ≤
          Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun s => Theorem2iii.sampledPosterior posterior s))
            (Theorem2iii.expectedDatasetFidelity (Theorem2iii.iidSamplePMF μ N) pref)
            (fun s => Theorem2iii.sampledDecision argmaxRule s)) :
    (∀ other : (Fin N → X) → Fin N → Fin K,
        Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun s => Theorem2iii.sampledPosterior posterior s))
            (Theorem2iii.expectedDatasetFidelity (Theorem2iii.iidSamplePMF μ N) pref) other ≤
          Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun s => Theorem2iii.sampledPosterior posterior s))
            (Theorem2iii.expectedDatasetFidelity (Theorem2iii.iidSamplePMF μ N) pref)
            (fun s => Theorem2iii.sampledDecision rule s)) ↔
      EconCSLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) = 0 := by
  exact
    Theorem2iii.paper_theorem2iii_expected_weightedObjective_maximizer_iff_independent_rule_agrees_ae
      μ posterior pref rule argmaxRule hγnonneg hγlt hNpos hpref_nonneg
      hpref_sum hnontrivial hweak_argmax hargmaxMax

/--
Theorem 2(iii), `gamma = 1` boundary: if every positive-probability
disagreement is posterior-strict, then a disagreeing independent rule is not a
weighted-objective maximizer even at the accuracy-only boundary.
-/
theorem theorem2iii_strict_disagreement_not_weighted_objective_maximizer
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ) (pref : Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    {γ : ℝ} (hγpos : 0 < γ) (hγle : γ ≤ 1)
    (hdisagree :
      0 < EconCSLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x))
    (hNpos : 0 < N)
    (hpref_nonneg : ∀ y, 0 ≤ pref y)
    (hpref_sum : (∑ y : Fin K, pref y) = 1)
    (hnontrivial : ∀ y : Fin K, 1 / (N : ℝ) ≤ pref y)
    (hstrict_argmax :
      ∀ x, rule x ≠ argmaxRule x →
        posterior x (rule x) < posterior x (argmaxRule x)) :
    ¬ ∀ other : (Fin N → X) → Fin N → Fin K,
        Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun s => Theorem2iii.sampledPosterior posterior s))
            (Theorem2iii.expectedDatasetFidelity (Theorem2iii.iidSamplePMF μ N) pref) other ≤
          Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun s => Theorem2iii.sampledPosterior posterior s))
            (Theorem2iii.expectedDatasetFidelity (Theorem2iii.iidSamplePMF μ N) pref)
            (fun s => Theorem2iii.sampledDecision rule s) := by
  exact
    Theorem2iii.paper_theorem2iii_not_expected_weightedObjective_maximizer_of_independent_rule_disagrees_pos_strict_argmax
      μ posterior pref rule argmaxRule hγpos hγle hdisagree hNpos hpref_nonneg
      hpref_sum hnontrivial hstrict_argmax

end

end PaperInterface
end DSWG24DiscretizationBias
