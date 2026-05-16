import EconCSLib.Foundations.Probability.Admissions
import EconCSLib.Foundations.Probability.Gaussian
import EconCSLib.Foundations.Math.AffineThreshold
import EconCSLib.Foundations.Math.ThresholdCharacterization

open EconCSLib
open EconCSLib.Probability

/-!
# Paper-Facing Theorems: Test-optional Policies and Informational Gaps

This file currently exposes the finite admissions-accounting layer used as
support for the future source-faithful formalization of
*Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps*.

## Main declarations

- `LG21Model`: shared finite prior with base and test signal kernels.
- `lg21TwoSignalAdmissionsModel`: adapter to the reusable two-signal
  admissions comparison interface.
- `lg21BaseModel`, `lg21TestModel`: wrappers into the reusable
  `AdmissionsModel`.
- `LG21ResamplingExperiment`: finite conditional-kernel interface for the
  re-sampling policy in Definition 6.
- `LG21EquilibriumData`, `lg21Equilibrium`, `LG21SourcePolicySurface`:
  source-facing equilibrium and fairness surfaces for the strategic parts of
  the paper.
- `LG21GaussianThresholdEquilibriumCertificate`: the current bridge target from
  the source equilibrium to Lemma 4.1's Gaussian threshold subgames.
- `LG21StrategicWithholdingSourceWitness`: the current bridge target for
  Theorem 3.1's threshold and unfairness conclusions.
- `paper_theorem4_4_resampling_policy_observably_fair`,
  `paper_theorem4_4_resampling_policy_demographically_fair`: finite
  distributional core of Theorem 4.4.
- `lg21_base_exp_decompose`, `lg21_test_exp_decompose`: finite expectation
  decompositions for selected and unselected applicants.
-/

namespace LG21TestOptionalPolicies

noncomputable section

/-!
Core abstraction for a test-optional paper-facing model: students have a latent
quality and two signal channels (base profile and optional test outcome).  Both
use the same prior to enable direct comparison.
-/
structure LG21Model (Θ ΩBase ΩTest : Type*) [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest] where
  (prior : PMF Θ)
  (baseKernel : Θ → PMF ΩBase)
  (testKernel : Θ → PMF ΩTest)
  (quality : Θ → ℝ)

def lg21TwoSignalAdmissionsModel
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) :
    TwoSignalAdmissionsModel Θ ΩBase ΩTest :=
  { prior := m.prior
    leftKernel := m.baseKernel
    rightKernel := m.testKernel
    value := m.quality }

/--
Bayesian optimal Gaussian estimator used throughout Sections 3--4.

For any observed feature family, the posterior estimate is the precision-weighted
posterior mean.  The theorem also records the marginal law of that estimate.
This is the shared Gaussian algebra used by Theorem 3.1, Lemma 4.1, and
Propositions 4.2--4.3 before their strategic/threshold comparisons.
-/
theorem paper_bayesian_optimal_estimator_gaussian
    {Feature : Type*} [Fintype Feature] [Nonempty Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) :
    M.posteriorMean theta =
        (M.centeredFamily.priorPrecision * M.priorMean +
          ∑ k : Feature,
            M.centeredFamily.signalPrecision k * (theta k - M.noiseMean k)) /
          M.centeredFamily.posteriorPrecision ∧
      (M.posteriorMeanLaw).mean = M.priorMean ∧
        (M.posteriorMeanLaw).variance =
          M.priorVar *
              (∑ k : Feature, M.centeredFamily.signalPrecision k) /
            M.centeredFamily.posteriorPrecision := by
  refine ⟨?_, ?_, ?_⟩
  · exact M.posteriorMean_eq_precision_weighted_div theta
  · rfl
  · simpa [GaussianOffsetSignalFamily.posteriorMeanLaw] using
      M.posteriorMeanVariance_eq_priorVar_mul_sum_signalPrecision_div_posteriorPrecision

/--
Bayesian optimal estimator support for Lemma 4.1 and Theorem 3.1: holding all
other information fixed, the estimated skill is strictly increasing in any one
reported feature/test score.
-/
theorem paper_bayesian_optimal_estimator_strictMono_feature
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature) :
    StrictMono (fun value : ℝ =>
      M.posteriorMean (Function.update theta k value)) :=
  M.posteriorMean_update_strictMono theta k

/--
Threshold support for reporting/taking decisions: a positive-slope affine
Bayesian estimate clears a reporting threshold exactly above its cutoff.
-/
theorem paper_reporting_affine_estimate_threshold_iff_cutoff
    {intercept slope threshold score : ℝ} (hslope : 0 < slope) :
    threshold ≤ intercept + slope * score ↔
      affineCutoff intercept slope threshold ≤ score :=
  threshold_le_affine_iff_cutoff_le hslope

/--
Gaussian reporting-threshold support: with all other information fixed,
crossing a Bayesian-estimate threshold is equivalent to the selected reported
feature/test score clearing an explicit affine cutoff.
-/
theorem paper_reporting_gaussian_threshold_iff_cutoff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (base threshold value : ℝ) :
    threshold ≤ M.posteriorMean (Function.update theta k value) ↔
      affineCutoff
        (M.posteriorMean (Function.update theta k base) -
          M.centeredFamily.signalWeight k * base)
        (M.centeredFamily.signalWeight k) threshold ≤ value :=
  M.threshold_le_posteriorMean_update_iff_cutoff_le theta k base threshold value

/-- A one-dimensional decision rule is a lower-cutoff rule. -/
def lg21LowerCutoffStrategy (choose : ℝ → Prop) : Prop :=
  ∃ cutoff : ℝ, ∀ value : ℝ, choose value ↔ cutoff ≤ value

/-- Every lower-cutoff rule is monotone in the source paper's direction. -/
theorem lg21_monotone_of_lowerCutoffStrategy
    {choose : ℝ → Prop} (hcutoff : lg21LowerCutoffStrategy choose) :
    ∀ {low high : ℝ}, low ≤ high → choose low → choose high := by
  rcases hcutoff with ⟨cutoff, hchoose⟩
  intro low high hle hlow
  exact (hchoose high).2 ((hchoose low).1 hlow |>.trans hle)

/--
Theorem 3.1 threshold support: any positive-slope affine Bayesian comparison
induces a finite lower-cutoff strategy.
-/
theorem paper_lower_cutoff_strategy_of_affine_threshold
    {intercept slope threshold : ℝ} (hslope : 0 < slope) :
    lg21LowerCutoffStrategy
      (fun value : ℝ => threshold ≤ intercept + slope * value) := by
  refine ⟨affineCutoff intercept slope threshold, ?_⟩
  intro value
  exact paper_reporting_affine_estimate_threshold_iff_cutoff hslope

/--
Theorem 3.1 reporting-threshold support: with all other information fixed, a
Bayesian-optimal report decision based on clearing an estimate threshold is a
finite lower-cutoff rule in the reported test score.
-/
theorem paper_theorem3_1_reporting_threshold_of_gaussian_best_response
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (base threshold : ℝ) :
    lg21LowerCutoffStrategy
      (fun value : ℝ =>
        threshold ≤ M.posteriorMean (Function.update theta k value)) := by
  refine ⟨affineCutoff
    (M.posteriorMean (Function.update theta k base) -
      M.centeredFamily.signalWeight k * base)
    (M.centeredFamily.signalWeight k) threshold, ?_⟩
  intro value
  exact paper_reporting_gaussian_threshold_iff_cutoff
    M theta k base threshold value

/--
Lemma 4.1 scalar core: for a continuous strictly increasing reported-score
estimate, if a non-report estimate lies strictly between the estimate at a
below-cutoff score and the estimate at the cutoff, then some strictly
below-cutoff score is indifferent, and every score from that point up to the
cutoff weakly prefers reporting.  Since the indifference point is strictly
below the cutoff, there is also a strictly below-cutoff score that strictly
prefers reporting.
-/
theorem paper_lemma4_1_reporting_cutoff_has_profitable_deviation_core
    {reportedEstimate : ℝ → ℝ} {scoreLow cutoff noReportEstimate : ℝ}
    (hcont : ContinuousOn reportedEstimate (Set.Icc scoreLow cutoff))
    (hmono : StrictMonoOn reportedEstimate (Set.Icc scoreLow cutoff))
    (hscore_lt : scoreLow < cutoff)
    (hlow : reportedEstimate scoreLow < noReportEstimate)
    (hcutoff : noReportEstimate < reportedEstimate cutoff) :
    ∃ indifferentScore : ℝ,
      indifferentScore ∈ Set.Ioo scoreLow cutoff ∧
        reportedEstimate indifferentScore = noReportEstimate ∧
          (∀ score ∈ Set.Icc indifferentScore cutoff,
            noReportEstimate ≤ reportedEstimate score) ∧
              ∃ profitableScore : ℝ,
                profitableScore ∈ Set.Ioo indifferentScore cutoff ∧
                  noReportEstimate < reportedEstimate profitableScore := by
  have hlevel_mem :
      noReportEstimate ∈
        Set.Icc (reportedEstimate scoreLow) (reportedEstimate cutoff) :=
    ⟨hlow.le, hcutoff.le⟩
  rcases intermediate_value_Icc hscore_lt.le hcont hlevel_mem with
    ⟨indifferentScore, hindiff_mem, hindiff_eq⟩
  have hscoreLow_lt_indiff : scoreLow < indifferentScore := by
    have hne : indifferentScore ≠ scoreLow := by
      intro hEq
      subst indifferentScore
      linarith
    exact lt_of_le_of_ne hindiff_mem.1 (Ne.symm hne)
  have hindiff_lt_cutoff : indifferentScore < cutoff := by
    have hne : indifferentScore ≠ cutoff := by
      intro hEq
      subst indifferentScore
      linarith
    exact lt_of_le_of_ne hindiff_mem.2 hne
  have hweak :
      ∀ score ∈ Set.Icc indifferentScore cutoff,
        noReportEstimate ≤ reportedEstimate score := by
    intro score hscore
    rcases lt_or_eq_of_le hscore.1 with hindiff_lt_score | rfl
    · have hstrict :
          reportedEstimate indifferentScore < reportedEstimate score :=
        hmono hindiff_mem ⟨hindiff_mem.1.trans hscore.1, hscore.2⟩
          hindiff_lt_score
      exact (by simpa [hindiff_eq] using hstrict.le)
    · exact le_of_eq hindiff_eq.symm
  let profitableScore : ℝ := (indifferentScore + cutoff) / 2
  have hprofitable_low : indifferentScore < profitableScore := by
    dsimp [profitableScore]
    linarith
  have hprofitable_high : profitableScore < cutoff := by
    dsimp [profitableScore]
    linarith
  have hprofitable_mem_big : profitableScore ∈ Set.Icc scoreLow cutoff :=
    ⟨le_of_lt (hscoreLow_lt_indiff.trans hprofitable_low),
      le_of_lt hprofitable_high⟩
  have hprofitable_strict :
      reportedEstimate indifferentScore < reportedEstimate profitableScore :=
    hmono hindiff_mem hprofitable_mem_big hprofitable_low
  refine ⟨indifferentScore,
    ⟨hscoreLow_lt_indiff, hindiff_lt_cutoff⟩, hindiff_eq, hweak,
    profitableScore, ⟨hprofitable_low, hprofitable_high⟩, ?_⟩
  simpa [hindiff_eq] using hprofitable_strict

/--
The Gaussian posterior score, as a function of one reported raw score while all
other information is fixed, is continuous.
-/
theorem paper_gaussian_posteriorMean_update_continuous
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature) :
    Continuous (fun value : ℝ =>
      M.posteriorMean (Function.update theta k value)) := by
  have hfun :
      (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value)) =
        fun value : ℝ =>
          M.posteriorMean (Function.update theta k 0) +
            M.centeredFamily.signalWeight k * value := by
    funext value
    exact M.posteriorMean_update_eq_base_add_weight_mul theta k value
  rw [hfun]
  exact continuous_const.add (continuous_const.mul continuous_id)

/--
Gaussian posterior-score support for Lemma 4.1: because the reported score
enters the Bayesian posterior estimate with positive slope, for every cutoff
and no-report estimate there is a sufficiently low reported score whose
posterior estimate is below the no-report estimate.
-/
theorem paper_gaussian_posteriorMean_update_exists_low
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (cutoff noReportEstimate : ℝ) :
    ∃ scoreLow : ℝ,
      scoreLow < cutoff ∧
        M.posteriorMean (Function.update theta k scoreLow) < noReportEstimate := by
  let base0 : ℝ := M.posteriorMean (Function.update theta k 0)
  let weight : ℝ := M.centeredFamily.signalWeight k
  let scoreLow : ℝ := min cutoff ((noReportEstimate - base0) / weight) - 1
  have hweight : 0 < weight := by
    simpa [weight] using M.centeredFamily.signalWeight_pos k
  have hmin_cutoff :
      min cutoff ((noReportEstimate - base0) / weight) ≤ cutoff :=
    min_le_left _ _
  have hscore_lt_cutoff : scoreLow < cutoff := by
    dsimp [scoreLow]
    linarith
  have hmin_level :
      min cutoff ((noReportEstimate - base0) / weight) ≤
        (noReportEstimate - base0) / weight :=
    min_le_right _ _
  have hscore_lt_level :
      scoreLow < (noReportEstimate - base0) / weight := by
    dsimp [scoreLow]
    linarith
  have hmul :
      weight * scoreLow < noReportEstimate - base0 := by
    have hmul' := mul_lt_mul_of_pos_left hscore_lt_level hweight
    have hcancel :
        weight * ((noReportEstimate - base0) / weight) =
          noReportEstimate - base0 :=
      mul_div_cancel₀ _ (ne_of_gt hweight)
    linarith
  refine ⟨scoreLow, hscore_lt_cutoff, ?_⟩
  calc
    M.posteriorMean (Function.update theta k scoreLow) =
        base0 + weight * scoreLow := by
      simpa [base0, weight] using
        M.posteriorMean_update_eq_base_add_weight_mul theta k scoreLow
    _ < noReportEstimate := by
      linarith

/--
Lemma 4.1 Gaussian reporting core: a nontrivial observed-access reporting
cutoff is unstable whenever the no-report posterior estimate is strictly
between the reported-score estimate at a lower score and the estimate at the
cutoff.  The conclusion exhibits the paper's `θ̃_K` and the interval of
withheld scores that weakly benefit from reporting.
-/
theorem paper_lemma4_1_gaussian_reporting_cutoff_has_profitable_deviation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    {scoreLow cutoff noReportEstimate : ℝ}
    (hscore_lt : scoreLow < cutoff)
    (hlow :
      M.posteriorMean (Function.update theta k scoreLow) < noReportEstimate)
    (hcutoff :
      noReportEstimate <
        M.posteriorMean (Function.update theta k cutoff)) :
    ∃ indifferentScore : ℝ,
      indifferentScore ∈ Set.Ioo scoreLow cutoff ∧
        M.posteriorMean (Function.update theta k indifferentScore) =
          noReportEstimate ∧
          (∀ score ∈ Set.Icc indifferentScore cutoff,
            noReportEstimate ≤
              M.posteriorMean (Function.update theta k score)) ∧
            ∃ profitableScore : ℝ,
              profitableScore ∈ Set.Ioo indifferentScore cutoff ∧
                noReportEstimate <
                  M.posteriorMean
                    (Function.update theta k profitableScore) := by
  exact paper_lemma4_1_reporting_cutoff_has_profitable_deviation_core
    (reportedEstimate := fun value : ℝ =>
      M.posteriorMean (Function.update theta k value))
    ((paper_gaussian_posteriorMean_update_continuous M theta k).continuousOn)
    (fun _ hx _ hy hxy =>
      (paper_bayesian_optimal_estimator_strictMono_feature M theta k) hxy)
    hscore_lt hlow hcutoff

/--
No-profitable-withholding condition for the optional-reporting part of Lemma
4.1: any score that is currently withheld must weakly prefer withholding to
reporting.
-/
def lg21NoProfitableWithholdingDeviation
    (reports : ℝ → Prop) (reportedEstimate : ℝ → ℝ)
    (noReportEstimate : ℝ) : Prop :=
  ∀ score, ¬ reports score → reportedEstimate score ≤ noReportEstimate

/--
Lemma 4.1 optional-reporting equilibrium core: a nontrivial lower-cutoff
reporting strategy cannot satisfy no-profitable-withholding-deviation when the
no-report estimate lies strictly inside the cutoff interval.
-/
theorem paper_lemma4_1_no_nontrivial_reporting_cutoff_of_no_profitable_withholding
    {reports : ℝ → Prop} {reportedEstimate : ℝ → ℝ}
    {scoreLow cutoff noReportEstimate : ℝ}
    (hcutoffStrategy : ∀ score : ℝ, reports score ↔ cutoff ≤ score)
    (hnoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports reportedEstimate noReportEstimate)
    (hcont : ContinuousOn reportedEstimate (Set.Icc scoreLow cutoff))
    (hmono : StrictMonoOn reportedEstimate (Set.Icc scoreLow cutoff))
    (hscore_lt : scoreLow < cutoff)
    (hlow : reportedEstimate scoreLow < noReportEstimate)
    (hcutoff : noReportEstimate < reportedEstimate cutoff) :
    False := by
  rcases paper_lemma4_1_reporting_cutoff_has_profitable_deviation_core
      hcont hmono hscore_lt hlow hcutoff with
    ⟨indifferentScore, _hindiff_mem, _hindiff_eq, _hweak,
      profitableScore, hprofitable_mem, hprofitable⟩
  have hnotReport : ¬ reports profitableScore := by
    intro hreport
    have hcutoff_le : cutoff ≤ profitableScore :=
      (hcutoffStrategy profitableScore).1 hreport
    linarith [hprofitable_mem.2]
  have hnoProfit := hnoDeviation profitableScore hnotReport
  linarith

/--
Lemma 4.1 Gaussian optional-reporting equilibrium core: the Bayesian posterior
score supplies the continuous strictly increasing reported estimate, so any
nontrivial lower-cutoff reporting equilibrium with the inside-interval
no-report estimate has a profitable withholding deviation.
-/
theorem paper_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    {reports : ℝ → Prop} {scoreLow cutoff noReportEstimate : ℝ}
    (hcutoffStrategy : ∀ score : ℝ, reports score ↔ cutoff ≤ score)
    (hnoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (hscore_lt : scoreLow < cutoff)
    (hlow :
      M.posteriorMean (Function.update theta k scoreLow) < noReportEstimate)
    (hcutoff :
      noReportEstimate <
        M.posteriorMean (Function.update theta k cutoff)) :
    False :=
  paper_lemma4_1_no_nontrivial_reporting_cutoff_of_no_profitable_withholding
    hcutoffStrategy hnoDeviation
    ((paper_gaussian_posteriorMean_update_continuous M theta k).continuousOn)
    (fun _ hx _ hy hxy =>
    (paper_bayesian_optimal_estimator_strictMono_feature M theta k) hxy)
    hscore_lt hlow hcutoff

/--
Lemma 4.1 Gaussian optional-reporting equilibrium core, source-shaped form:
once the no-report estimate is strictly below the reported estimate at the
reporting cutoff, positive-slope Gaussian posterior algebra supplies the
low-score side of the source proof automatically.
-/
theorem paper_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding_from_cutoff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    {reports : ℝ → Prop} {cutoff noReportEstimate : ℝ}
    (hcutoffStrategy : ∀ score : ℝ, reports score ↔ cutoff ≤ score)
    (hnoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (hcutoff :
      noReportEstimate <
        M.posteriorMean (Function.update theta k cutoff)) :
    False := by
  rcases paper_gaussian_posteriorMean_update_exists_low
      M theta k cutoff noReportEstimate with
    ⟨scoreLow, hscore_lt, hlow⟩
  exact
    paper_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding
      M theta k hcutoffStrategy hnoDeviation hscore_lt hlow hcutoff

/--
Lemma 4.1 optional-reporting endpoint bridge: if every non-all-reporting
candidate equilibrium yields the finite cutoff and cutoff-estimate inequality
used in the source proof, then no-profitable-withholding forces all scores to
be reported.
-/
theorem paper_lemma4_1_all_report_of_gaussian_cutoff_if_not_all_no_profitable_withholding
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    {reports : ℝ → Prop} {noReportEstimate : ℝ}
    (hcutoffIfNotAll :
      ¬ (∀ score : ℝ, reports score) →
        ∃ cutoff : ℝ,
          (∀ score : ℝ, reports score ↔ cutoff ≤ score) ∧
            noReportEstimate <
              M.posteriorMean (Function.update theta k cutoff))
    (hnoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate) :
    ∀ score : ℝ, reports score := by
  by_contra hnotAll
  rcases hcutoffIfNotAll hnotAll with
    ⟨cutoff, hcutoffStrategy, hcutoff⟩
  exact False.elim
    (paper_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding_from_cutoff
      M theta k hcutoffStrategy hnoDeviation hcutoff)

/--
Lemma 4.1 optional-reporting lower-tail support: if the no-report estimate is
the Bayesian posterior estimate evaluated at a lower-tail mean score below the
reporting cutoff, then the no-report estimate is strictly below the reported
estimate at the cutoff.
-/
theorem paper_lemma4_1_report_cutoff_estimate_lt_of_lower_tail_score
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    {lowerTailScore cutoff noReportEstimate : ℝ}
    (hlower : lowerTailScore < cutoff)
    (hnoReport :
      noReportEstimate =
        M.posteriorMean (Function.update theta k lowerTailScore)) :
    noReportEstimate <
      M.posteriorMean (Function.update theta k cutoff) := by
  rw [hnoReport]
  exact paper_bayesian_optimal_estimator_strictMono_feature
    M theta k hlower

/--
Lemma 4.1 optional-reporting endpoint bridge in the paper's lower-tail form:
if every non-all-reporting candidate equilibrium yields a finite reporting
cutoff and identifies the no-report estimate with a lower-tail mean score below
that cutoff, then no-profitable-withholding forces all scores to be reported.
-/
theorem paper_lemma4_1_all_report_of_gaussian_lower_tail_cutoff_no_profitable_withholding
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    {reports : ℝ → Prop} {noReportEstimate : ℝ}
    (hcutoffIfNotAll :
      ¬ (∀ score : ℝ, reports score) →
        ∃ cutoff lowerTailScore : ℝ,
          (∀ score : ℝ, reports score ↔ cutoff ≤ score) ∧
            lowerTailScore < cutoff ∧
              noReportEstimate =
                M.posteriorMean (Function.update theta k lowerTailScore))
    (hnoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate) :
    ∀ score : ℝ, reports score := by
  by_contra hnotAll
  rcases hcutoffIfNotAll hnotAll with
    ⟨cutoff, lowerTailScore, hcutoffStrategy, hlower, hnoReport⟩
  have hcutoff :
      noReportEstimate <
        M.posteriorMean (Function.update theta k cutoff) :=
    paper_lemma4_1_report_cutoff_estimate_lt_of_lower_tail_score
      M theta k hlower hnoReport
  exact False.elim
    (paper_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding_from_cutoff
      M theta k hcutoffStrategy hnoDeviation hcutoff)

/--
Lemma 4.1 optional-reporting endpoint bridge using the shared Gaussian
lower-tail-mean certificate.  This is the source proof's no-report estimate
shape: the school imputes a score equal to the Gaussian mean conditional on
falling below the reporting cutoff.
-/
theorem paper_lemma4_1_all_report_of_gaussian_lower_tail_certificate_no_profitable_withholding
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (C : GaussianLowerTailMeanCertificate)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw : GaussianScaleLaw)
    {reports : ℝ → Prop} {noReportEstimate : ℝ}
    (hcutoffIfNotAll :
      ¬ (∀ score : ℝ, reports score) →
        ∃ cutoff : ℝ,
          (∀ score : ℝ, reports score ↔ cutoff ≤ score) ∧
            noReportEstimate =
              M.posteriorMean
                (Function.update theta k (C.lowerTailMean scoreLaw cutoff)))
    (hnoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate) :
    ∀ score : ℝ, reports score :=
  paper_lemma4_1_all_report_of_gaussian_lower_tail_cutoff_no_profitable_withholding
    M theta k
    (fun hnotAll => by
      rcases hcutoffIfNotAll hnotAll with
        ⟨cutoff, hcutoffStrategy, hnoReport⟩
      exact ⟨cutoff, C.lowerTailMean scoreLaw cutoff,
        hcutoffStrategy, C.lowerTailMean_lt scoreLaw cutoff, hnoReport⟩)
    hnoDeviation

/--
Lemma 4.1 optional-reporting bridge for an explicit Gaussian Bayesian threshold
policy: the paper's threshold-if-not-all premise is discharged by the affine
cutoff generated by the posterior-mean threshold comparison.
-/
theorem paper_lemma4_1_all_report_of_gaussian_threshold_policy_lower_tail_no_profitable_withholding
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (C : GaussianLowerTailMeanCertificate)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw : GaussianScaleLaw)
    {reports : ℝ → Prop} {noReportEstimate base threshold : ℝ}
    (hreports :
      ∀ score : ℝ,
        reports score ↔
          threshold ≤ M.posteriorMean (Function.update theta k score))
    (hnoReport :
      noReportEstimate =
        M.posteriorMean
          (Function.update theta k
            (C.lowerTailMean scoreLaw
              (affineCutoff
                (M.posteriorMean (Function.update theta k base) -
                  M.centeredFamily.signalWeight k * base)
                (M.centeredFamily.signalWeight k) threshold))))
    (hnoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate) :
    ∀ score : ℝ, reports score :=
  paper_lemma4_1_all_report_of_gaussian_lower_tail_certificate_no_profitable_withholding
    C M theta k scoreLaw
    (fun _hnotAll => by
      refine ⟨affineCutoff
        (M.posteriorMean (Function.update theta k base) -
          M.centeredFamily.signalWeight k * base)
        (M.centeredFamily.signalWeight k) threshold, ?_, hnoReport⟩
      intro score
      exact (hreports score).trans
        (paper_reporting_gaussian_threshold_iff_cutoff
          M theta k base threshold score))
    hnoDeviation

/-- Gaussian law of a raw test score conditional on latent skill. -/
def lg21GaussianTestScoreLaw (skill scale : ℝ) (hscale : 0 < scale) :
    GaussianScaleLaw where
  mean := skill
  scale := scale
  scale_pos := hscale

/--
Posterior-score law when all non-test features are fixed and the only random
input is one Gaussian test score.  `intercept + slope * testScore` is the
Bayesian posterior estimate as an affine function of the test score.
-/
def lg21OneTestPosteriorScoreLaw
    (intercept slope : ℝ) (hslope : 0 < slope)
    (skill testScale : ℝ) (htestScale : 0 < testScale) :
    GaussianScaleLaw :=
  (lg21GaussianTestScoreLaw skill testScale htestScale).affineImage
    intercept slope hslope

@[simp] theorem lg21OneTestPosteriorScoreLaw_mean
    (intercept slope : ℝ) (hslope : 0 < slope)
    (skill testScale : ℝ) (htestScale : 0 < testScale) :
    (lg21OneTestPosteriorScoreLaw
      intercept slope hslope skill testScale htestScale).mean =
      intercept + slope * skill := by
  rfl

@[simp] theorem lg21OneTestPosteriorScoreLaw_scale
    (intercept slope : ℝ) (hslope : 0 < slope)
    (skill testScale : ℝ) (htestScale : 0 < testScale) :
    (lg21OneTestPosteriorScoreLaw
      intercept slope hslope skill testScale htestScale).scale =
      slope * testScale := by
  rfl

/--
Proposition 4.2 Gaussian support in the paper's fixed-base form: with fixed
non-test features, the posterior-score law induced by the optional test has
strictly larger mean for strictly larger latent skill.
-/
theorem paper_one_test_posterior_score_law_mean_lt_of_skill_lt
    {intercept slope skillLow skillHigh testScale : ℝ}
    (hslope : 0 < slope) (htestScale : 0 < testScale)
    (hskill : skillLow < skillHigh) :
      (lg21OneTestPosteriorScoreLaw
      intercept slope hslope skillLow testScale htestScale).mean <
      (lg21OneTestPosteriorScoreLaw
        intercept slope hslope skillHigh testScale htestScale).mean := by
  simpa [add_comm] using
    add_lt_add_left (mul_lt_mul_of_pos_left hskill hslope) intercept

/--
Lemma 4.1 test-taking support: a Gaussian test score whose mean is at least a
threshold clears that threshold with probability at least one half.
-/
theorem paper_lemma4_1_test_score_pass_prob_ge_half_of_skill_ge_cutoff
    (api : StandardGaussianCDFAPI) {skill cutoff scale : ℝ} (hscale : 0 < scale)
    (hskill : cutoff ≤ skill) :
    (1 / 2 : ℝ) ≤
      api.thresholdPassProb (lg21GaussianTestScoreLaw skill scale hscale) cutoff :=
  api.thresholdPassProb_ge_half_of_threshold_le_mean
    (L := lg21GaussianTestScoreLaw skill scale hscale)
    (by simpa [lg21GaussianTestScoreLaw] using hskill)

/--
Lemma 4.1 test-taking support, strict form: if the skill/mean is strictly above
the threshold, the probability of clearing the threshold is strictly more than
one half.
-/
theorem paper_lemma4_1_test_score_pass_prob_gt_half_of_skill_gt_cutoff
    (api : StandardGaussianCDFAPI) {skill cutoff scale : ℝ} (hscale : 0 < scale)
    (hskill : cutoff < skill) :
    (1 / 2 : ℝ) <
      api.thresholdPassProb (lg21GaussianTestScoreLaw skill scale hscale) cutoff :=
  api.thresholdPassProb_gt_half_of_threshold_lt_mean
    (L := lg21GaussianTestScoreLaw skill scale hscale)
    (by simpa [lg21GaussianTestScoreLaw] using hskill)

/--
Lemma 4.1 reporting-required core: if the no-test posterior skill estimate
`q̃` is strictly below a proposed taking cutoff `q̄`, then there are skills
strictly between them whose Gaussian test score clears `q̃` with probability
strictly above one half.  These are the source proof's below-cutoff students
who can benefit from taking the test.
-/
theorem paper_lemma4_1_take_test_cutoff_has_profitable_deviation
    (api : StandardGaussianCDFAPI) {qTilde qBar scale : ℝ}
    (hscale : 0 < scale) (hcutoff : qTilde < qBar) :
    ∃ skill : ℝ,
      skill ∈ Set.Ioo qTilde qBar ∧
        (1 / 2 : ℝ) <
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill scale hscale) qTilde := by
  let skill : ℝ := (qTilde + qBar) / 2
  have hlow : qTilde < skill := by
    dsimp [skill]
    linarith
  have hhigh : skill < qBar := by
    dsimp [skill]
    linarith
  exact ⟨skill, ⟨hlow, hhigh⟩,
    paper_lemma4_1_test_score_pass_prob_gt_half_of_skill_gt_cutoff
      api hscale hlow⟩

/--
No-profitable-test-taking condition for the report-required part of Lemma 4.1:
any student who currently does not take the test must have at most one-half
chance of obtaining a score that would improve the school estimate.
-/
def lg21NoProfitableTestTakingDeviation
    (takes : ℝ → Prop) (testBenefitProb : ℝ → ℝ) : Prop :=
  ∀ skill, ¬ takes skill → testBenefitProb skill ≤ (1 / 2 : ℝ)

/--
Lemma 4.1 report-required equilibrium core: a nontrivial lower-cutoff
test-taking strategy cannot satisfy no-profitable-test-taking-deviation when
the no-test posterior skill estimate `q̃` lies strictly below the taking cutoff
`q̄`.
-/
theorem paper_lemma4_1_no_nontrivial_take_test_cutoff_of_no_profitable_deviation
    (api : StandardGaussianCDFAPI) {takes : ℝ → Prop} {qTilde qBar scale : ℝ}
    (hscale : 0 < scale)
    (hcutoffStrategy : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hnoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill scale hscale) qTilde))
    (hcutoff : qTilde < qBar) :
    False := by
  rcases paper_lemma4_1_take_test_cutoff_has_profitable_deviation
      api hscale hcutoff with
    ⟨skill, hskill_mem, hprofitable⟩
  have hnotTake : ¬ takes skill := by
    intro htake
    have hqBar_le_skill : qBar ≤ skill :=
      (hcutoffStrategy skill).1 htake
    linarith [hskill_mem.2]
  have hnoProfit := hnoDeviation skill hnotTake
  linarith

/--
Lemma 4.1 report-required endpoint bridge: if every non-all-taking candidate
equilibrium yields the finite taking cutoff and `q̃ < q̄` inequality used in
the source proof, then no-profitable-test-taking forces all access students to
take the test.
-/
theorem paper_lemma4_1_all_take_of_cutoff_if_not_all_no_profitable_test_taking
    (api : StandardGaussianCDFAPI) {takes : ℝ → Prop} {qTilde scale : ℝ}
    (hscale : 0 < scale)
    (hcutoffIfNotAll :
      ¬ (∀ skill : ℝ, takes skill) →
        ∃ qBar : ℝ,
          (∀ skill : ℝ, takes skill ↔ qBar ≤ skill) ∧ qTilde < qBar)
    (hnoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill scale hscale) qTilde)) :
    ∀ skill : ℝ, takes skill := by
  by_contra hnotAll
  rcases hcutoffIfNotAll hnotAll with
    ⟨qBar, hcutoffStrategy, hcutoff⟩
  exact False.elim
    (paper_lemma4_1_no_nontrivial_take_test_cutoff_of_no_profitable_deviation
      api hscale hcutoffStrategy hnoDeviation hcutoff)

/--
Lemma 4.1 report-required endpoint bridge in the paper's lower-tail form: if
every non-all-taking candidate equilibrium yields a finite taking cutoff and
identifies the no-test estimate `q̃` with a lower-tail skill mean below that
cutoff, then no-profitable-test-taking forces all access students to take the
test.
-/
theorem paper_lemma4_1_all_take_of_lower_tail_cutoff_no_profitable_test_taking
    (api : StandardGaussianCDFAPI) {takes : ℝ → Prop} {qTilde scale : ℝ}
    (hscale : 0 < scale)
    (hcutoffIfNotAll :
      ¬ (∀ skill : ℝ, takes skill) →
        ∃ qBar lowerTailSkill : ℝ,
          (∀ skill : ℝ, takes skill ↔ qBar ≤ skill) ∧
            lowerTailSkill < qBar ∧ qTilde = lowerTailSkill)
    (hnoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill scale hscale) qTilde)) :
    ∀ skill : ℝ, takes skill := by
  by_contra hnotAll
  rcases hcutoffIfNotAll hnotAll with
    ⟨qBar, lowerTailSkill, hcutoffStrategy, hlower, hqTilde⟩
  have hcutoff : qTilde < qBar := by
    rw [hqTilde]
    exact hlower
  exact False.elim
    (paper_lemma4_1_no_nontrivial_take_test_cutoff_of_no_profitable_deviation
      api hscale hcutoffStrategy hnoDeviation hcutoff)

/--
Lemma 4.1 report-required endpoint bridge using the shared Gaussian
lower-tail-mean certificate.  This is the source proof's no-test estimate
shape: the school imputes skill equal to the Gaussian mean conditional on
falling below the taking cutoff.
-/
theorem paper_lemma4_1_all_take_of_gaussian_lower_tail_certificate_no_profitable_test_taking
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI) (skillLaw : GaussianScaleLaw)
    {takes : ℝ → Prop} {qTilde scale : ℝ}
    (hscale : 0 < scale)
    (hcutoffIfNotAll :
      ¬ (∀ skill : ℝ, takes skill) →
        ∃ qBar : ℝ,
          (∀ skill : ℝ, takes skill ↔ qBar ≤ skill) ∧
            qTilde = C.lowerTailMean skillLaw qBar)
    (hnoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill scale hscale) qTilde)) :
    ∀ skill : ℝ, takes skill :=
  paper_lemma4_1_all_take_of_lower_tail_cutoff_no_profitable_test_taking
    api hscale
    (fun hnotAll => by
      rcases hcutoffIfNotAll hnotAll with
        ⟨qBar, hcutoffStrategy, hqTilde⟩
      exact ⟨qBar, C.lowerTailMean skillLaw qBar,
        hcutoffStrategy, C.lowerTailMean_lt skillLaw qBar, hqTilde⟩)
    hnoDeviation

/--
Lemma 4.1 report-required bridge for an explicit lower-threshold taking rule:
if the no-test estimate is the lower-tail skill mean at that threshold, then
no-profitable-test-taking forces every access student to take.
-/
theorem paper_lemma4_1_all_take_of_explicit_lower_tail_threshold_no_profitable_test_taking
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI) (skillLaw : GaussianScaleLaw)
    {takes : ℝ → Prop} {qTilde qBar scale : ℝ}
    (hscale : 0 < scale)
    (htakes : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hqTilde : qTilde = C.lowerTailMean skillLaw qBar)
    (hnoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill scale hscale) qTilde)) :
    ∀ skill : ℝ, takes skill :=
  paper_lemma4_1_all_take_of_gaussian_lower_tail_certificate_no_profitable_test_taking
    C api skillLaw hscale
    (fun _hnotAll => ⟨qBar, htakes, hqTilde⟩)
    hnoDeviation

/--
Lemma 4.1 lower-tail strategy-proofness bridge: combining the optional-reporting
and report-required lower-tail arguments gives the source-shaped conclusion
that the relevant observed-access cohorts all report and all take, conditional
only on the paper's remaining threshold-if-not-all premises.
-/
theorem paper_lemma4_1_strategy_proofness_of_lower_tail_thresholds
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {reports takes : ℝ → Prop} {noReportEstimate qTilde testScale : ℝ}
    (htestScale : 0 < testScale)
    (hreportCutoffIfNotAll :
      ¬ (∀ score : ℝ, reports score) →
        ∃ cutoff : ℝ,
          (∀ score : ℝ, reports score ↔ cutoff ≤ score) ∧
            noReportEstimate =
              M.posteriorMean
                (Function.update theta k (C.lowerTailMean scoreLaw cutoff)))
    (hreportNoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (htakeCutoffIfNotAll :
      ¬ (∀ skill : ℝ, takes skill) →
        ∃ qBar : ℝ,
          (∀ skill : ℝ, takes skill ↔ qBar ≤ skill) ∧
            qTilde = C.lowerTailMean skillLaw qBar)
    (htakeNoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill testScale htestScale) qTilde)) :
    (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
  ⟨paper_lemma4_1_all_report_of_gaussian_lower_tail_certificate_no_profitable_withholding
      C M theta k scoreLaw hreportCutoffIfNotAll hreportNoDeviation,
    paper_lemma4_1_all_take_of_gaussian_lower_tail_certificate_no_profitable_test_taking
      C api skillLaw htestScale htakeCutoffIfNotAll htakeNoDeviation⟩

/--
Lemma 4.1 route with the reporting cutoff discharged by an explicit Gaussian
Bayesian threshold policy, while the taking side remains in the source
lower-tail cutoff form.
-/
theorem paper_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_lower_tail_taking
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {reports takes : ℝ → Prop}
    {noReportEstimate qTilde base threshold testScale : ℝ}
    (htestScale : 0 < testScale)
    (hreports :
      ∀ score : ℝ,
        reports score ↔
          threshold ≤ M.posteriorMean (Function.update theta k score))
    (hnoReport :
      noReportEstimate =
        M.posteriorMean
          (Function.update theta k
            (C.lowerTailMean scoreLaw
              (affineCutoff
                (M.posteriorMean (Function.update theta k base) -
                  M.centeredFamily.signalWeight k * base)
                (M.centeredFamily.signalWeight k) threshold))))
    (hreportNoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (htakeCutoffIfNotAll :
      ¬ (∀ skill : ℝ, takes skill) →
        ∃ qBar : ℝ,
          (∀ skill : ℝ, takes skill ↔ qBar ≤ skill) ∧
            qTilde = C.lowerTailMean skillLaw qBar)
    (htakeNoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill testScale htestScale) qTilde)) :
    (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
  ⟨paper_lemma4_1_all_report_of_gaussian_threshold_policy_lower_tail_no_profitable_withholding
      C M theta k scoreLaw hreports hnoReport hreportNoDeviation,
    paper_lemma4_1_all_take_of_gaussian_lower_tail_certificate_no_profitable_test_taking
      C api skillLaw htestScale htakeCutoffIfNotAll htakeNoDeviation⟩

/--
Lemma 4.1 route with both threshold premises made explicit: Gaussian Bayesian
threshold reporting supplies the reporting cutoff, and an explicit lower-tail
taking threshold supplies the report-required side.
-/
theorem paper_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_explicit_taking_threshold
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {reports takes : ℝ → Prop}
    {noReportEstimate qTilde base threshold qBar testScale : ℝ}
    (htestScale : 0 < testScale)
    (hreports :
      ∀ score : ℝ,
        reports score ↔
          threshold ≤ M.posteriorMean (Function.update theta k score))
    (hnoReport :
      noReportEstimate =
        M.posteriorMean
          (Function.update theta k
            (C.lowerTailMean scoreLaw
              (affineCutoff
                (M.posteriorMean (Function.update theta k base) -
                  M.centeredFamily.signalWeight k * base)
                (M.centeredFamily.signalWeight k) threshold))))
    (hreportNoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (htakes : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hqTilde : qTilde = C.lowerTailMean skillLaw qBar)
    (htakeNoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill testScale htestScale) qTilde)) :
    (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
  ⟨paper_lemma4_1_all_report_of_gaussian_threshold_policy_lower_tail_no_profitable_withholding
      C M theta k scoreLaw hreports hnoReport hreportNoDeviation,
    paper_lemma4_1_all_take_of_explicit_lower_tail_threshold_no_profitable_test_taking
      C api skillLaw htestScale htakes hqTilde htakeNoDeviation⟩

/--
Propositions 4.2--4.3 support: Gaussian estimate laws with strictly different
means are different distributions.
-/
theorem paper_gaussian_estimate_laws_differ_of_mean_lt
    {Llow Lhigh : GaussianVarianceLaw} (hmean : Llow.mean < Lhigh.mean) :
    Llow ≠ Lhigh :=
  GaussianVarianceLaw.ne_of_mean_lt hmean

/--
Proposition 4.3 support: Gaussian estimate laws with strictly different
variances are different distributions.
-/
theorem paper_gaussian_estimate_laws_differ_of_variance_lt
    {Llow Lhigh : GaussianVarianceLaw} (hvar : Llow.variance < Lhigh.variance) :
    Llow ≠ Lhigh :=
  GaussianVarianceLaw.ne_of_variance_lt hvar

/--
Propositions 4.2--4.3 support for the location-scale Gaussian interfaces used
by conditional posterior-score laws: strictly different means are different
laws.
-/
theorem paper_gaussian_scale_laws_differ_of_mean_lt
    {Llow Lhigh : GaussianScaleLaw} (hmean : Llow.mean < Lhigh.mean) :
    Llow ≠ Lhigh :=
  GaussianScaleLaw.ne_of_mean_lt hmean

/--
Proposition 4.3 support for location-scale Gaussian laws: strictly different
scales are different laws.
-/
theorem paper_gaussian_scale_laws_differ_of_scale_lt
    {Llow Lhigh : GaussianScaleLaw} (hscale : Llow.scale < Lhigh.scale) :
    Llow ≠ Lhigh :=
  GaussianScaleLaw.ne_of_scale_lt hscale

/--
Propositions 4.2--4.3 precision support: with the same prior variance, a
strictly larger total signal precision gives a strictly larger marginal
variance of the Bayesian estimated skill.
-/
theorem paper_gaussian_estimate_variance_lt_of_total_precision_lt
    {Feature : Type*} [Fintype Feature]
    {Mlow Mhigh : GaussianOffsetSignalFamily Feature}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      (∑ k : Feature, Mlow.centeredFamily.signalPrecision k) <
        ∑ k : Feature, Mhigh.centeredFamily.signalPrecision k) :
    Mlow.posteriorMeanVariance < Mhigh.posteriorMeanVariance :=
  GaussianOffsetSignalFamily.posteriorMeanVariance_lt_of_priorVar_eq_sum_signalPrecision_lt
    hpriorVar hsum

/--
Propositions 4.2--4.3 precision support: with the same prior variance, a
strictly larger total signal precision gives a strictly larger Gaussian scale
for the Bayesian estimate.
-/
theorem paper_gaussian_estimate_scale_lt_of_total_precision_lt
    {Feature : Type*} [Fintype Feature] [Nonempty Feature]
    {Mlow Mhigh : GaussianOffsetSignalFamily Feature}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      (∑ k : Feature, Mlow.centeredFamily.signalPrecision k) <
        ∑ k : Feature, Mhigh.centeredFamily.signalPrecision k) :
    (Mlow.posteriorMeanScaleLaw).scale <
      (Mhigh.posteriorMeanScaleLaw).scale :=
  GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_sum_signalPrecision_lt
    hpriorVar hsum

/--
Propositions 4.2--4.3 precision support across different observed-feature
sets: with the same prior variance, a strictly larger total signal precision
gives a strictly larger Gaussian scale for the Bayesian estimate.
-/
theorem paper_gaussian_estimate_scale_lt_of_signalPrecisionSum_lt
    {FeatureLow FeatureHigh : Type*}
    [Fintype FeatureLow] [Nonempty FeatureLow]
    [Fintype FeatureHigh] [Nonempty FeatureHigh]
    {Mlow : GaussianOffsetSignalFamily FeatureLow}
    {Mhigh : GaussianOffsetSignalFamily FeatureHigh}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      Mlow.centeredFamily.signalPrecisionSum <
        Mhigh.centeredFamily.signalPrecisionSum) :
    (Mlow.posteriorMeanScaleLaw).scale <
      (Mhigh.posteriorMeanScaleLaw).scale :=
  GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
    hpriorVar hsum

/--
Proposition 4.3 precision support: adding one extra Gaussian signal strictly
increases the scale of the Bayesian posterior-mean law.
-/
theorem paper_gaussian_estimate_scale_lt_of_extra_signal
    {Feature : Type*} [Fintype Feature] [Nonempty Feature]
    (M : GaussianOffsetSignalFamily Feature)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    (M.posteriorMeanScaleLaw).scale <
      ((M.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).posteriorMeanScaleLaw).scale :=
  GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_withExtraSignal
    M extraNoiseMean extraNoiseVar hextraNoiseVar

/--
Propositions 4.2--4.3 precision support: a strict total-precision gap produces
different Bayesian-estimate Gaussian laws.
-/
theorem paper_gaussian_estimate_laws_differ_of_total_precision_lt
    {Feature : Type*} [Fintype Feature] [Nonempty Feature]
    {Mlow Mhigh : GaussianOffsetSignalFamily Feature}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      (∑ k : Feature, Mlow.centeredFamily.signalPrecision k) <
        ∑ k : Feature, Mhigh.centeredFamily.signalPrecision k) :
    Mlow.posteriorMeanLaw ≠ Mhigh.posteriorMeanLaw :=
  GaussianVarianceLaw.ne_of_variance_lt
    (paper_gaussian_estimate_variance_lt_of_total_precision_lt
      hpriorVar hsum)

/--
Proposition 4.3 tail-comparison support: above the common mean, the larger-scale
Gaussian estimate law has weakly larger upper-tail probability.
-/
theorem paper_gaussian_upper_tail_le_of_same_mean_scale_le_above_mean
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale ≤ Llarge.scale)
    {threshold : ℝ} (hthreshold : Lsmall.mean ≤ threshold) :
    api.thresholdPassProb Lsmall threshold ≤
      api.thresholdPassProb Llarge threshold :=
  api.thresholdPassProb_le_of_same_mean_scale_le_of_mean_le
    hmean hscale hthreshold

/--
Proposition 4.3 strict tail-comparison support: strictly above the common mean,
the strictly larger-scale Gaussian estimate law has strictly larger upper-tail
probability.
-/
theorem paper_gaussian_upper_tail_lt_of_same_mean_scale_lt_above_mean
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale < Llarge.scale)
    {threshold : ℝ} (hthreshold : Lsmall.mean < threshold) :
    api.thresholdPassProb Lsmall threshold <
      api.thresholdPassProb Llarge threshold :=
  api.thresholdPassProb_lt_of_same_mean_scale_lt_of_mean_lt
    hmean hscale hthreshold

/--
Proposition 4.2 Gaussian support: conditional on true skill, the posterior-score
law has a strictly larger mean for a strictly larger skill.
-/
theorem paper_conditional_posteriorMeanScaleLaw_mean_lt_of_skill_lt
    {Feature : Type*} [Fintype Feature] [Nonempty Feature]
    (M : GaussianOffsetSignalFamily Feature) {qLow qHigh : ℝ}
    (hq : qLow < qHigh) :
    (M.conditionalPosteriorMeanScaleLaw qLow).mean <
      (M.conditionalPosteriorMeanScaleLaw qHigh).mean := by
  rw [M.conditionalPosteriorMeanScaleLaw_mean_eq_precision_weighted_div qLow,
    M.conditionalPosteriorMeanScaleLaw_mean_eq_precision_weighted_div qHigh]
  have hmul :
      M.centeredFamily.signalPrecisionSum * qLow <
        M.centeredFamily.signalPrecisionSum * qHigh := by
    exact mul_lt_mul_of_pos_left hq M.centeredFamily.signalPrecisionSum_pos
  have hadd :
      M.centeredFamily.priorPrecision * M.priorMean +
          M.centeredFamily.signalPrecisionSum * qLow <
        M.centeredFamily.priorPrecision * M.priorMean +
          M.centeredFamily.signalPrecisionSum * qHigh := by
    simpa [add_comm] using
      add_lt_add_right hmul
        (M.centeredFamily.priorPrecision * M.priorMean)
  exact div_lt_div_of_pos_right hadd M.centeredFamily.posteriorPrecision_pos

/--
Paper-local law type for LG21 statements that compare deterministic
Bayesian estimates with genuinely Gaussian posterior-score laws.
-/
inductive LG21EstimateLaw where
  | point : ℝ → LG21EstimateLaw
  | gaussian : GaussianScaleLaw → LG21EstimateLaw

namespace LG21EstimateLaw

theorem point_ne_gaussian (estimate : ℝ) (law : GaussianScaleLaw) :
    point estimate ≠ gaussian law := by
  intro h
  cases h

theorem gaussian_ne_point (law : GaussianScaleLaw) (estimate : ℝ) :
    gaussian law ≠ point estimate := by
  intro h
  cases h

theorem gaussian_ne_of_ne {L₁ L₂ : GaussianScaleLaw} (hne : L₁ ≠ L₂) :
    gaussian L₁ ≠ gaussian L₂ := by
  intro h
  cases h
  exact hne rfl

theorem gaussian_ne_of_mean_lt {Llow Lhigh : GaussianScaleLaw}
    (hmean : Llow.mean < Lhigh.mean) :
    gaussian Llow ≠ gaussian Lhigh :=
  gaussian_ne_of_ne (GaussianScaleLaw.ne_of_mean_lt hmean)

theorem gaussian_ne_of_scale_lt {Lsmall Llarge : GaussianScaleLaw}
    (hscale : Lsmall.scale < Llarge.scale) :
    gaussian Lsmall ≠ gaussian Llarge :=
  gaussian_ne_of_ne (GaussianScaleLaw.ne_of_scale_lt hscale)

end LG21EstimateLaw

/--
Finite conditional-kernel form of the paper's Section 4.2 re-sampling policy.

The source proof of Theorem 4.4 only needs the distributional fact that, after
conditioning on the observed non-test profile, the imputed test score for a
student without access is sampled from the same conditional test-score law as a
student with access.  This paper-facing abbreviation points to the reusable
finite conditional-resampling interface in `EconCSLib`.
-/
abbrev LG21ResamplingExperiment
    (ΩBase ΩTest Estimate : Type*) [Fintype ΩBase] [DecidableEq ΩBase] :=
  ConditionalResamplingExperiment ΩBase ΩTest Estimate

/-- Estimate distribution for students with test access, conditional on base profile. -/
noncomputable def lg21AccessEstimateKernel
    {ΩBase ΩTest Estimate : Type*} [Fintype ΩBase] [DecidableEq ΩBase]
    (e : LG21ResamplingExperiment ΩBase ΩTest Estimate) (base : ΩBase) :
    PMF Estimate :=
  accessEstimateKernel e base

/-- Test-score kernel used by Definition 6's re-sampling policy. -/
noncomputable def lg21ResamplingPolicyKernel
    {ΩBase ΩTest Estimate : Type*} [Fintype ΩBase] [DecidableEq ΩBase]
    (e : LG21ResamplingExperiment ΩBase ΩTest Estimate) : ΩBase → PMF ΩTest :=
  resamplingSignalKernel e

/--
Estimate distribution for students without test access under the re-sampling
policy, conditional on base profile.
-/
noncomputable def lg21ResamplingEstimateKernel
    {ΩBase ΩTest Estimate : Type*} [Fintype ΩBase] [DecidableEq ΩBase]
    (e : LG21ResamplingExperiment ΩBase ΩTest Estimate) (base : ΩBase) :
    PMF Estimate :=
  resampledEstimateKernel e base

/-- Finite observable fairness: equal estimate laws at each observed base profile. -/
def lg21ObservableFair
    {ΩBase Estimate : Type*} (access noAccess : ΩBase → PMF Estimate) : Prop :=
  ObservableFair access noAccess

/-- Demographic estimate law obtained by mixing base-profile conditional laws. -/
noncomputable def lg21DemographicEstimateDistribution
    {ΩBase Estimate : Type*} (baseProfile : PMF ΩBase)
    (kernel : ΩBase → PMF Estimate) : PMF Estimate :=
  demographicEstimateDistribution baseProfile kernel

/-- Finite demographic fairness: equal estimate laws after mixing over base profiles. -/
def lg21DemographicallyFair
    {ΩBase Estimate : Type*} (baseProfile : PMF ΩBase)
    (access noAccess : ΩBase → PMF Estimate) : Prop :=
  DemographicallyFair baseProfile access noAccess

/-- Definition 1 action object for students with test access: `(Y, X)`. -/
structure LG21AccessAction where
  takesTest : Bool
  reportsScore : Bool
deriving DecidableEq, Repr

namespace LG21AccessAction

/-- Source feasibility condition `Y ≥ X`: reporting requires taking the test. -/
def reportImpliesTake (a : LG21AccessAction) : Prop :=
  a.reportsScore = true → a.takesTest = true

/-- The action `(Y, X) = (0, 0)`. -/
def noTake : LG21AccessAction where
  takesTest := false
  reportsScore := false

/-- The action `(Y, X) = (1, 0)`: take the test and withhold the score. -/
def takeAndWithhold : LG21AccessAction where
  takesTest := true
  reportsScore := false

/-- The action `(Y, X) = (1, 1)`: take the test and report the score. -/
def takeAndReport : LG21AccessAction where
  takesTest := true
  reportsScore := true

/-- Optional reporting imposes no extra feature-requirement constraint. -/
def optionalReportingRequirement (_a : LG21AccessAction) : Prop :=
  True

/-- Reporting is required conditional on taking the test: `Y = X`. -/
def reportRequiredAfterTaking (a : LG21AccessAction) : Prop :=
  a.takesTest = a.reportsScore

/-- Definition 1 feasible action set `T`: `Y ≥ X` plus the requirement policy. -/
def feasible (requirement : LG21AccessAction → Prop)
    (a : LG21AccessAction) : Prop :=
  a.reportImpliesTake ∧ requirement a

theorem noTake_reportImpliesTake : noTake.reportImpliesTake := by
  intro hreport
  cases hreport

theorem takeAndWithhold_reportImpliesTake :
    takeAndWithhold.reportImpliesTake := by
  intro hreport
  rfl

theorem takeAndReport_reportImpliesTake :
    takeAndReport.reportImpliesTake := by
  intro _hreport
  rfl

theorem reportRequiredAfterTaking_reportImpliesTake
    {a : LG21AccessAction} (h : reportRequiredAfterTaking a) :
    a.reportImpliesTake := by
  intro hreport
  rw [h]
  exact hreport

theorem feasible_of_reportRequiredAfterTaking
    {requirement : LG21AccessAction → Prop} {a : LG21AccessAction}
    (hreq : requirement a) (hreportRequired : reportRequiredAfterTaking a) :
    feasible requirement a :=
  ⟨reportRequiredAfterTaking_reportImpliesTake hreportRequired, hreq⟩

end LG21AccessAction

/--
Estimate law conditional on an observed base profile after mixing over the
latent-skill distribution at that base profile.
-/
noncomputable def lg21LatentSkillEstimateDistribution
    {Skill Base Estimate : Type*} (skillGivenBase : Base → PMF Skill)
    (latentEstimate : Skill → Base → PMF Estimate) (base : Base) :
    PMF Estimate :=
  (skillGivenBase base).bind (fun q => latentEstimate q base)

/--
Definition 1 equilibrium data, abstracted from the paper's test-taking and
reporting action space.  `StudentInfo` packages the student's true skill and
observed non-test features, while `Action` packages the `(Y,X)` decision.
-/
structure LG21EquilibriumData (StudentInfo Action : Type*) where
  actionFeasible : StudentInfo → Action → Prop
  chosenAction : StudentInfo → Action
  payoff : StudentInfo → Action → ℝ
  estimationConsistent : Prop

/--
Definition 1 equilibrium predicate: chosen actions are feasible, weakly
maximize estimated payoff among feasible actions, and the estimation rule is
consistent with the induced decisions.
-/
def lg21Equilibrium {StudentInfo Action : Type*}
    (E : LG21EquilibriumData StudentInfo Action) : Prop :=
  (∀ info, E.actionFeasible info (E.chosenAction info)) ∧
    (∀ info action, E.actionFeasible info action →
      E.payoff info action ≤ E.payoff info (E.chosenAction info)) ∧
      E.estimationConsistent

/--
Binary reporting subgame used to connect Definition 1-style best responses to
the no-profitable-withholding predicate in Lemma 4.1.
-/
def lg21ReportingEquilibriumData
    (reports : ℝ → Prop) [DecidablePred reports]
    (reportedEstimate : ℝ → ℝ) (noReportEstimate : ℝ) :
    LG21EquilibriumData ℝ Bool where
  actionFeasible := fun _score _report => True
  chosenAction := fun score => if reports score then true else false
  payoff := fun score report =>
    if report = true then reportedEstimate score else noReportEstimate
  estimationConsistent := True

theorem lg21NoProfitableWithholdingDeviation_of_reporting_equilibrium
    {reports : ℝ → Prop} [DecidablePred reports]
    {reportedEstimate : ℝ → ℝ} {noReportEstimate : ℝ}
    (hEq :
      lg21Equilibrium
        (lg21ReportingEquilibriumData
          reports reportedEstimate noReportEstimate)) :
    lg21NoProfitableWithholdingDeviation
      reports reportedEstimate noReportEstimate := by
  intro score hnreport
  have hbest := hEq.2.1 score true trivial
  dsimp [lg21ReportingEquilibriumData] at hbest
  simpa [hnreport] using hbest

/--
Binary test-taking subgame used to connect Definition 1-style best responses
to the no-profitable-test-taking predicate in Lemma 4.1.
-/
def lg21TestTakingEquilibriumData
    (takes : ℝ → Prop) [DecidablePred takes]
    (testBenefitProb : ℝ → ℝ) :
    LG21EquilibriumData ℝ Bool where
  actionFeasible := fun _skill _take => True
  chosenAction := fun skill => if takes skill then true else false
  payoff := fun skill take =>
    if take = true then testBenefitProb skill else (1 / 2 : ℝ)
  estimationConsistent := True

theorem lg21NoProfitableTestTakingDeviation_of_taking_equilibrium
    {takes : ℝ → Prop} [DecidablePred takes]
    {testBenefitProb : ℝ → ℝ}
    (hEq :
      lg21Equilibrium
        (lg21TestTakingEquilibriumData takes testBenefitProb)) :
    lg21NoProfitableTestTakingDeviation takes testBenefitProb := by
  intro skill hntake
  have hbest := hEq.2.1 skill true trivial
  dsimp [lg21TestTakingEquilibriumData] at hbest
  simpa [hntake] using hbest

/--
Lemma 4.1 route from explicit threshold policies and binary subgame
equilibria: the equilibrium best-response fields supply the no-profitable
reporting and taking deviation predicates.
-/
theorem paper_lemma4_1_strategy_proofness_of_explicit_threshold_equilibria
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {reports takes : ℝ → Prop} [DecidablePred reports] [DecidablePred takes]
    {noReportEstimate qTilde reportingBase threshold qBar testScale : ℝ}
    (htestScale : 0 < testScale)
    (hreports :
      ∀ score : ℝ,
        reports score ↔
          threshold ≤ M.posteriorMean (Function.update theta k score))
    (hnoReport :
      noReportEstimate =
        M.posteriorMean
          (Function.update theta k
            (C.lowerTailMean scoreLaw
              (affineCutoff
                (M.posteriorMean (Function.update theta k reportingBase) -
                  M.centeredFamily.signalWeight k * reportingBase)
                (M.centeredFamily.signalWeight k) threshold))))
    (hreportEq :
      lg21Equilibrium
        (lg21ReportingEquilibriumData
          reports
          (fun value : ℝ => M.posteriorMean (Function.update theta k value))
          noReportEstimate))
    (htakes : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hqTilde : qTilde = C.lowerTailMean skillLaw qBar)
    (htakeEq :
      lg21Equilibrium
        (lg21TestTakingEquilibriumData takes
          (fun skill : ℝ =>
            api.thresholdPassProb
              (lg21GaussianTestScoreLaw skill testScale htestScale) qTilde))) :
    (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
  paper_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_explicit_taking_threshold
    C api M theta k scoreLaw skillLaw htestScale hreports hnoReport
    (lg21NoProfitableWithholdingDeviation_of_reporting_equilibrium hreportEq)
    htakes hqTilde
    (lg21NoProfitableTestTakingDeviation_of_taking_equilibrium htakeEq)

/--
Certificate isolating the remaining source-equilibrium bridge for Lemma 4.1:
the full LG21 equilibrium induces binary Gaussian reporting and test-taking
subgames with the threshold shapes used in the paper proof.
-/
structure LG21GaussianThresholdEquilibriumCertificate
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {testScale : ℝ} (htestScale : 0 < testScale) where
  reports : ℝ → Prop
  reportDecidable : DecidablePred reports
  takes : ℝ → Prop
  takeDecidable : DecidablePred takes
  noReportEstimate : ℝ
  qTilde : ℝ
  reportingBase : ℝ
  threshold : ℝ
  qBar : ℝ
  reporting_threshold :
    ∀ score : ℝ,
      reports score ↔
        threshold ≤ M.posteriorMean (Function.update theta k score)
  no_report_estimate_eq :
    noReportEstimate =
      M.posteriorMean
        (Function.update theta k
          (C.lowerTailMean scoreLaw
            (affineCutoff
              (M.posteriorMean (Function.update theta k reportingBase) -
                M.centeredFamily.signalWeight k * reportingBase)
              (M.centeredFamily.signalWeight k) threshold)))
  reporting_equilibrium :
    @lg21Equilibrium ℝ Bool
      (@lg21ReportingEquilibriumData reports reportDecidable
        (fun value : ℝ => M.posteriorMean (Function.update theta k value))
        noReportEstimate)
  taking_threshold : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill
  qTilde_eq : qTilde = C.lowerTailMean skillLaw qBar
  taking_equilibrium :
    @lg21Equilibrium ℝ Bool
      (@lg21TestTakingEquilibriumData takes takeDecidable
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill testScale htestScale) qTilde))

/--
Lemma 4.1 endpoint from the source-equilibrium threshold certificate.  This is
the one-stop target for the still-open full source-equilibrium instantiation.
-/
theorem paper_lemma4_1_strategy_proofness_of_threshold_equilibrium_certificate
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {testScale : ℝ} (htestScale : 0 < testScale)
    (K :
      LG21GaussianThresholdEquilibriumCertificate
        C api M theta k scoreLaw skillLaw htestScale) :
    (∀ score : ℝ, K.reports score) ∧ (∀ skill : ℝ, K.takes skill) := by
  haveI := K.reportDecidable
  haveI := K.takeDecidable
  exact
    @paper_lemma4_1_strategy_proofness_of_explicit_threshold_equilibria
      Feature _ _ C api M theta k scoreLaw skillLaw
      K.reports K.takes K.reportDecidable K.takeDecidable
      K.noReportEstimate K.qTilde K.reportingBase K.threshold K.qBar testScale
      htestScale
      K.reporting_threshold K.no_report_estimate_eq
      K.reporting_equilibrium K.taking_threshold K.qTilde_eq
      K.taking_equilibrium

/--
Source-facing policy surface for Definitions 2--5.  The fields expose exactly
the estimate distributions whose equality the paper's fairness definitions
compare, quantified over every equilibrium in the surface.
-/
structure LG21SourcePolicySurface
    (Skill Base Test Estimate : Type*) where
  Equilibrium : Type*
  latentAccessEstimate : Equilibrium → Skill → Base → PMF Estimate
  latentNoAccessEstimate : Equilibrium → Skill → Base → PMF Estimate
  observableAccessEstimate : Equilibrium → Base → PMF Estimate
  observableNoAccessEstimate : Equilibrium → Base → PMF Estimate
  demographicAccessEstimate : Equilibrium → PMF Estimate
  demographicNoAccessEstimate : Equilibrium → PMF Estimate
  baseOnlyEstimate : Equilibrium → Base → PMF Estimate
  fullFeatureEstimate : Equilibrium → Base → Test → PMF Estimate

/--
Continuous-law version of the source-facing policy surface.

The finite `LG21SourcePolicySurface` above is used for PMF-based resampling
proofs.  The paper's Gaussian impossibility propositions compare equality of
continuous estimate laws, so this parallel surface abstracts over the law type
directly.
-/
structure LG21SourceLawPolicySurface
    (Skill Base Test Law : Type*) where
  Equilibrium : Type*
  latentAccessLaw : Equilibrium → Skill → Base → Law
  latentNoAccessLaw : Equilibrium → Skill → Base → Law
  observableAccessLaw : Equilibrium → Base → Law
  observableNoAccessLaw : Equilibrium → Base → Law
  demographicAccessLaw : Equilibrium → Law
  demographicNoAccessLaw : Equilibrium → Law
  baseOnlyLaw : Equilibrium → Base → Law
  fullFeatureLaw : Equilibrium → Base → Test → Law

/-- Definition 2: latent-skill fairness in every equilibrium. -/
def lg21SourceLatentSkillFair
    {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) : Prop :=
  ∀ e q base, S.latentAccessEstimate e q base =
    S.latentNoAccessEstimate e q base

/-- Definition 3: observable fairness in every equilibrium. -/
def lg21SourceObservablyFair
    {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) : Prop :=
  ∀ e base, S.observableAccessEstimate e base =
    S.observableNoAccessEstimate e base

/-- Definition 4: demographic fairness in every equilibrium. -/
def lg21SourceDemographicallyFair
    {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) : Prop :=
  ∀ e, S.demographicAccessEstimate e = S.demographicNoAccessEstimate e

/-- Definition 5: test-blankness, i.e. test scores play no role. -/
def lg21SourceTestBlank
    {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) : Prop :=
  ∀ e base test, S.baseOnlyEstimate e base =
    S.fullFeatureEstimate e base test

/-- Definition 2 over arbitrary law objects. -/
def lg21SourceLawLatentSkillFair
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e q base, S.latentAccessLaw e q base =
    S.latentNoAccessLaw e q base

/-- Definition 3 over arbitrary law objects. -/
def lg21SourceLawObservablyFair
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e base, S.observableAccessLaw e base =
    S.observableNoAccessLaw e base

/-- Definition 4 over arbitrary law objects. -/
def lg21SourceLawDemographicallyFair
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e, S.demographicAccessLaw e = S.demographicNoAccessLaw e

/-- Definition 5 over arbitrary law objects. -/
def lg21SourceLawTestBlank
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e base test, S.baseOnlyLaw e base = S.fullFeatureLaw e base test

/--
Definitions 2--3 bridge: if observable estimate laws are obtained by mixing
the latent-skill-conditioned laws over the shared skill law at each base
profile, then latent-skill fairness implies observable fairness.
-/
theorem lg21_sourceObservablyFair_of_latentSkillFair_of_mixture
    {Skill Base Test Estimate : Type*}
    (skillGivenBase : Base → PMF Skill)
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (hAccess :
      ∀ e base, S.observableAccessEstimate e base =
        lg21LatentSkillEstimateDistribution skillGivenBase
          (S.latentAccessEstimate e) base)
    (hNoAccess :
      ∀ e base, S.observableNoAccessEstimate e base =
        lg21LatentSkillEstimateDistribution skillGivenBase
          (S.latentNoAccessEstimate e) base)
    (hlatent : lg21SourceLatentSkillFair S) :
    lg21SourceObservablyFair S := by
  intro e base
  rw [hAccess e base, hNoAccess e base]
  have hkernel :
      (fun q => S.latentAccessEstimate e q base) =
        fun q => S.latentNoAccessEstimate e q base := by
    funext q
    exact hlatent e q base
  simpa [lg21LatentSkillEstimateDistribution, hkernel]

/--
Definitions 3--4 bridge: if demographic estimate laws are obtained by mixing
the observable laws over the shared base-profile distribution, then observable
fairness implies demographic fairness.
-/
theorem lg21_sourceDemographicallyFair_of_observablyFair_of_mixture
    {Skill Base Test Estimate : Type*}
    (baseProfile : PMF Base)
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (hAccess :
      ∀ e, S.demographicAccessEstimate e =
        lg21DemographicEstimateDistribution baseProfile
          (S.observableAccessEstimate e))
    (hNoAccess :
      ∀ e, S.demographicNoAccessEstimate e =
        lg21DemographicEstimateDistribution baseProfile
          (S.observableNoAccessEstimate e))
    (hobs : lg21SourceObservablyFair S) :
    lg21SourceDemographicallyFair S := by
  intro e
  rw [hAccess e, hNoAccess e]
  simpa [lg21DemographicEstimateDistribution, lg21DemographicallyFair] using
    demographicallyFair_of_observableFair baseProfile (hobs e)

/--
Definitions 2--4 bridge: under the paper's shared latent-skill and base-profile
mixture identities, latent-skill fairness implies demographic fairness.
-/
theorem lg21_sourceDemographicallyFair_of_latentSkillFair_of_mixture
    {Skill Base Test Estimate : Type*}
    (skillGivenBase : Base → PMF Skill) (baseProfile : PMF Base)
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (hObsAccess :
      ∀ e base, S.observableAccessEstimate e base =
        lg21LatentSkillEstimateDistribution skillGivenBase
          (S.latentAccessEstimate e) base)
    (hObsNoAccess :
      ∀ e base, S.observableNoAccessEstimate e base =
        lg21LatentSkillEstimateDistribution skillGivenBase
          (S.latentNoAccessEstimate e) base)
    (hDemoAccess :
      ∀ e, S.demographicAccessEstimate e =
        lg21DemographicEstimateDistribution baseProfile
          (S.observableAccessEstimate e))
    (hDemoNoAccess :
      ∀ e, S.demographicNoAccessEstimate e =
        lg21DemographicEstimateDistribution baseProfile
          (S.observableNoAccessEstimate e))
    (hlatent : lg21SourceLatentSkillFair S) :
    lg21SourceDemographicallyFair S :=
  lg21_sourceDemographicallyFair_of_observablyFair_of_mixture
    baseProfile hDemoAccess hDemoNoAccess
    (lg21_sourceObservablyFair_of_latentSkillFair_of_mixture
      skillGivenBase hObsAccess hObsNoAccess hlatent)

theorem lg21_not_latentSkillFair_of_witness
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (e : S.Equilibrium) (q : Skill) (base : Base)
    (hne : S.latentAccessEstimate e q base ≠
      S.latentNoAccessEstimate e q base) :
    ¬ lg21SourceLatentSkillFair S := by
  intro hfair
  exact hne (hfair e q base)

theorem lg21_not_lawLatentSkillFair_of_witness
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (e : S.Equilibrium) (q : Skill) (base : Base)
    (hne : S.latentAccessLaw e q base ≠ S.latentNoAccessLaw e q base) :
    ¬ lg21SourceLawLatentSkillFair S := by
  intro hfair
  exact hne (hfair e q base)

/--
Proposition 4.2 four-group logical core: if no-access estimate laws are the
same for two latent skills at a fixed base profile, but access estimate laws
are different, then latent-skill fairness is impossible.
-/
theorem lg21_not_latentSkillFair_of_noAccess_same_access_ne
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    (hNoAccess :
      S.latentNoAccessEstimate e qHigh base =
        S.latentNoAccessEstimate e qLow base)
    (hAccess :
      S.latentAccessEstimate e qHigh base ≠
        S.latentAccessEstimate e qLow base) :
    ¬ lg21SourceLatentSkillFair S := by
  intro hfair
  have hHigh := hfair e qHigh base
  have hLow := hfair e qLow base
  exact hAccess (by
    rw [hHigh, hLow, hNoAccess])

/--
Proposition 4.2 continuous-law four-group core: if no-access laws are the same
for two latent skills at a fixed base profile, but access laws differ, then
latent-skill fairness is impossible.
-/
theorem lg21_not_lawLatentSkillFair_of_noAccess_same_access_ne
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccess :
      S.latentAccessLaw e qHigh base ≠
        S.latentAccessLaw e qLow base) :
    ¬ lg21SourceLawLatentSkillFair S := by
  intro hfair
  have hHigh := hfair e qHigh base
  have hLow := hfair e qLow base
  exact hAccess (by
    rw [hHigh, hLow, hNoAccess])

theorem lg21_not_observablyFair_of_witness
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (e : S.Equilibrium) (base : Base)
    (hne : S.observableAccessEstimate e base ≠
      S.observableNoAccessEstimate e base) :
    ¬ lg21SourceObservablyFair S := by
  intro hfair
  exact hne (hfair e base)

theorem lg21_not_lawObservablyFair_of_witness
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (e : S.Equilibrium) (base : Base)
    (hne : S.observableAccessLaw e base ≠ S.observableNoAccessLaw e base) :
    ¬ lg21SourceLawObservablyFair S := by
  intro hfair
  exact hne (hfair e base)

theorem lg21_not_demographicallyFair_of_witness
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (e : S.Equilibrium)
    (hne : S.demographicAccessEstimate e ≠ S.demographicNoAccessEstimate e) :
    ¬ lg21SourceDemographicallyFair S := by
  intro hfair
  exact hne (hfair e)

theorem lg21_not_lawDemographicallyFair_of_witness
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (e : S.Equilibrium)
    (hne : S.demographicAccessLaw e ≠ S.demographicNoAccessLaw e) :
    ¬ lg21SourceLawDemographicallyFair S := by
  intro hfair
  exact hne (hfair e)

theorem lg21_not_testBlank_of_witness
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (e : S.Equilibrium) (base : Base) (test : Test)
    (hne : S.baseOnlyEstimate e base ≠ S.fullFeatureEstimate e base test) :
    ¬ lg21SourceTestBlank S := by
  intro hblank
  exact hne (hblank e base test)

theorem lg21_not_lawTestBlank_of_witness
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (e : S.Equilibrium) (base : Base) (test : Test)
    (hne : S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test) :
    ¬ lg21SourceLawTestBlank S := by
  intro hblank
  exact hne (hblank e base test)

/--
Source-shaped witness for Theorem 3.1's strategic-withholding threshold
conclusions.  `Base` represents the paper's non-test feature vector
`{θ_k}_{k=1}^{K-1}`; reports and takes are binary strategy predicates over the
reported test score and latent skill, respectively.
-/
structure LG21StrategicWithholdingSourceWitness (Base : Type*) where
  reports : Base → ℝ → Prop
  takes : Base → ℝ → Prop
  some_access_students_do_not_report : ∃ base score, ¬ reports base score
  reporting_threshold :
    ∀ base, ∃ cutoff : ℝ, ∀ score : ℝ, reports base score ↔ cutoff ≤ score
  taking_threshold :
    ∀ base, ∃ qBar : ℝ, ∀ skill : ℝ, takes base skill ↔ qBar ≤ skill

/--
Theorem 3.1 threshold conclusions from a source-shaped strategic-withholding
witness.
-/
theorem paper_theorem3_1_threshold_conclusions_of_source_witness
    {Base : Type*} (W : LG21StrategicWithholdingSourceWitness Base) :
    (∃ base score, ¬ W.reports base score) ∧
      (∀ base, ∃ cutoff : ℝ,
        ∀ score : ℝ, W.reports base score ↔ cutoff ≤ score) ∧
        (∀ base, ∃ qBar : ℝ,
          ∀ skill : ℝ, W.takes base skill ↔ qBar ≤ skill) :=
  ⟨W.some_access_students_do_not_report,
    W.reporting_threshold, W.taking_threshold⟩

/--
Theorem 3.1 source-facing endpoint over PMF estimate surfaces: strategic
threshold behavior plus concrete fairness-violation witnesses imply the
paper's withholding/threshold conclusions and failure of all three fairness
criteria.
-/
theorem paper_theorem3_1_strategic_withholding_of_source_witness
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (W : LG21StrategicWithholdingSourceWitness Base)
    (eLat : S.Equilibrium) (q : Skill) (baseLat : Base)
    (hLatNe :
      S.latentAccessEstimate eLat q baseLat ≠
        S.latentNoAccessEstimate eLat q baseLat)
    (eObs : S.Equilibrium) (baseObs : Base)
    (hObsNe :
      S.observableAccessEstimate eObs baseObs ≠
        S.observableNoAccessEstimate eObs baseObs)
    (eDemo : S.Equilibrium)
    (hDemoNe :
      S.demographicAccessEstimate eDemo ≠
        S.demographicNoAccessEstimate eDemo) :
    (∃ base score, ¬ W.reports base score) ∧
      (∀ base, ∃ cutoff : ℝ,
        ∀ score : ℝ, W.reports base score ↔ cutoff ≤ score) ∧
        (∀ base, ∃ qBar : ℝ,
          ∀ skill : ℝ, W.takes base skill ↔ qBar ≤ skill) ∧
          ¬ lg21SourceLatentSkillFair S ∧
            ¬ lg21SourceObservablyFair S ∧
              ¬ lg21SourceDemographicallyFair S := by
  refine ⟨W.some_access_students_do_not_report,
    W.reporting_threshold, W.taking_threshold, ?_, ?_, ?_⟩
  · exact lg21_not_latentSkillFair_of_witness eLat q baseLat hLatNe
  · exact lg21_not_observablyFair_of_witness eObs baseObs hObsNe
  · exact lg21_not_demographicallyFair_of_witness eDemo hDemoNe

/--
Theorem 3.1 source-facing endpoint over arbitrary estimate-law objects.  This
is the version used by the Gaussian continuous-law wrappers.
-/
theorem paper_theorem3_1_law_strategic_withholding_of_source_witness
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (W : LG21StrategicWithholdingSourceWitness Base)
    (eLat : S.Equilibrium) (q : Skill) (baseLat : Base)
    (hLatNe :
      S.latentAccessLaw eLat q baseLat ≠ S.latentNoAccessLaw eLat q baseLat)
    (eObs : S.Equilibrium) (baseObs : Base)
    (hObsNe :
      S.observableAccessLaw eObs baseObs ≠ S.observableNoAccessLaw eObs baseObs)
    (eDemo : S.Equilibrium)
    (hDemoNe : S.demographicAccessLaw eDemo ≠ S.demographicNoAccessLaw eDemo) :
    (∃ base score, ¬ W.reports base score) ∧
      (∀ base, ∃ cutoff : ℝ,
        ∀ score : ℝ, W.reports base score ↔ cutoff ≤ score) ∧
        (∀ base, ∃ qBar : ℝ,
          ∀ skill : ℝ, W.takes base skill ↔ qBar ≤ skill) ∧
          ¬ lg21SourceLawLatentSkillFair S ∧
            ¬ lg21SourceLawObservablyFair S ∧
              ¬ lg21SourceLawDemographicallyFair S := by
  refine ⟨W.some_access_students_do_not_report,
    W.reporting_threshold, W.taking_threshold, ?_, ?_, ?_⟩
  · exact lg21_not_lawLatentSkillFair_of_witness eLat q baseLat hLatNe
  · exact lg21_not_lawObservablyFair_of_witness eObs baseObs hObsNe
  · exact lg21_not_lawDemographicallyFair_of_witness eDemo hDemoNe

/-- Certificate for Theorem 3.1's strategic-withholding and unfairness endpoint. -/
structure LG21StrategicWithholdingCertificate
    {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) where
  some_access_students_do_not_report : Prop
  threshold_reporting : Prop
  threshold_taking : Prop
  some_access_students_do_not_report_holds :
    some_access_students_do_not_report
  threshold_reporting_holds : threshold_reporting
  threshold_taking_holds : threshold_taking
  not_latent_skill_fair : ¬ lg21SourceLatentSkillFair S
  not_observably_fair : ¬ lg21SourceObservablyFair S
  not_demographically_fair : ¬ lg21SourceDemographicallyFair S

/-- Theorem 3.1 endpoint, conditional on the strategic-withholding certificate. -/
theorem paper_theorem3_1_strategic_withholding_of_certificate
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (C : LG21StrategicWithholdingCertificate S) :
    C.some_access_students_do_not_report ∧
      C.threshold_reporting ∧ C.threshold_taking ∧
        ¬ lg21SourceLatentSkillFair S ∧
          ¬ lg21SourceObservablyFair S ∧
            ¬ lg21SourceDemographicallyFair S := by
  exact ⟨C.some_access_students_do_not_report_holds,
    C.threshold_reporting_holds, C.threshold_taking_holds,
    C.not_latent_skill_fair, C.not_observably_fair,
    C.not_demographically_fair⟩

/-- Certificate for Theorem 3.2's fairness-impossibility implication. -/
structure LG21FairnessImpossibilityCertificate
    {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) where
  latent_or_observable_implies_test_blank :
    lg21SourceLatentSkillFair S ∨ lg21SourceObservablyFair S →
      lg21SourceTestBlank S

/-- Theorem 3.2 endpoint: latent or observable fairness implies test-blankness. -/
theorem paper_theorem3_2_fairness_impossibility_of_certificate
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (C : LG21FairnessImpossibilityCertificate S) :
    lg21SourceLatentSkillFair S ∨ lg21SourceObservablyFair S →
      lg21SourceTestBlank S := by
  exact C.latent_or_observable_implies_test_blank

/--
Theorem 3.2 contrapositive core: once the source implication from fairness to
test-blankness is available, any concrete test-relevance witness rules out both
latent-skill and observable fairness.
-/
theorem paper_theorem3_2_not_latent_or_observable_fair_of_test_relevance_witness
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (C : LG21FairnessImpossibilityCertificate S)
    (e : S.Equilibrium) (base : Base) (test : Test)
    (hne : S.baseOnlyEstimate e base ≠ S.fullFeatureEstimate e base test) :
    ¬ (lg21SourceLatentSkillFair S ∨ lg21SourceObservablyFair S) := by
  intro hfair
  exact (lg21_not_testBlank_of_witness e base test hne)
    (C.latent_or_observable_implies_test_blank hfair)

/-- Continuous-law certificate for Theorem 3.2's fairness-impossibility implication. -/
structure LG21LawFairnessImpossibilityCertificate
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) where
  latent_or_observable_implies_test_blank :
    lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
      lg21SourceLawTestBlank S

/-- Theorem 3.2 endpoint over arbitrary continuous law objects. -/
theorem paper_theorem3_2_law_fairness_impossibility_of_certificate
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (C : LG21LawFairnessImpossibilityCertificate S) :
    lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
      lg21SourceLawTestBlank S := by
  exact C.latent_or_observable_implies_test_blank

/--
Theorem 3.2 continuous-law contrapositive core: a concrete test-relevance
witness rules out the disjunction of latent-skill and observable fairness.
-/
theorem paper_theorem3_2_not_law_latent_or_observable_fair_of_test_relevance_witness
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (C : LG21LawFairnessImpossibilityCertificate S)
    (e : S.Equilibrium) (base : Base) (test : Test)
    (hne : S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test) :
    ¬ (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) := by
  intro hfair
  exact (lg21_not_lawTestBlank_of_witness e base test hne)
    (C.latent_or_observable_implies_test_blank hfair)

/-- Certificate for Lemma 4.1's strategy-proofness endpoint. -/
structure LG21ObservedAccessStrategyProofCertificate
    {Skill Base Test Estimate : Type*}
    (_S : LG21SourcePolicySurface Skill Base Test Estimate) where
  all_access_take_and_report : Prop
  all_access_take_and_report_holds : all_access_take_and_report

/-- Lemma 4.1 endpoint, conditional on the observed-access strategy-proofness certificate. -/
theorem paper_lemma4_1_strategy_proofness_of_certificate
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (C : LG21ObservedAccessStrategyProofCertificate S) :
    C.all_access_take_and_report := by
  exact C.all_access_take_and_report_holds

/-- Certificate for Proposition 4.2. -/
structure LG21NotLatentFairCertificate
    {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) where
  not_latent_skill_fair : ¬ lg21SourceLatentSkillFair S

/-- Proposition 4.2 endpoint: Bayesian optimality for access students is not latent-skill fair. -/
theorem paper_proposition4_2_not_latent_skill_fair_of_certificate
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (C : LG21NotLatentFairCertificate S) :
    ¬ lg21SourceLatentSkillFair S := by
  exact C.not_latent_skill_fair

/--
Proposition 4.2 logical core: a single latent-skill fairness violation witness
proves the policy is not latent-skill fair.
-/
theorem paper_proposition4_2_not_latent_skill_fair_of_witness
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (e : S.Equilibrium) (q : Skill) (base : Base)
    (hne : S.latentAccessEstimate e q base ≠
      S.latentNoAccessEstimate e q base) :
    ¬ lg21SourceLatentSkillFair S :=
  lg21_not_latentSkillFair_of_witness e q base hne

/--
Proposition 4.2 paper proof core: two no-access groups with the same observed
base profile cannot be distinguished, while two access groups with different
latent skills have different Bayesian-optimal estimate laws.  Those two facts
already contradict latent-skill fairness.
-/
theorem paper_proposition4_2_not_latent_skill_fair_of_four_group_core
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    (hNoAccess :
      S.latentNoAccessEstimate e qHigh base =
        S.latentNoAccessEstimate e qLow base)
    (hAccess :
      S.latentAccessEstimate e qHigh base ≠
        S.latentAccessEstimate e qLow base) :
    ¬ lg21SourceLatentSkillFair S :=
  lg21_not_latentSkillFair_of_noAccess_same_access_ne
    e qHigh qLow base hNoAccess hAccess

/--
Proposition 4.2 continuous-law proof core: two no-access groups with the same
observed base profile cannot be distinguished, while two access groups have
different Bayesian-optimal estimate laws.
-/
theorem paper_proposition4_2_not_law_latent_skill_fair_of_four_group_core
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccess :
      S.latentAccessLaw e qHigh base ≠
        S.latentAccessLaw e qLow base) :
    ¬ lg21SourceLawLatentSkillFair S :=
  lg21_not_lawLatentSkillFair_of_noAccess_same_access_ne
    e qHigh qLow base hNoAccess hAccess

/--
Proposition 4.2 Gaussian-law proof core: if the two access-side estimated-skill
laws have strictly ordered Gaussian means, then the access laws differ, so the
four-group argument rules out latent-skill fairness.
-/
theorem paper_proposition4_2_not_law_latent_skill_fair_of_gaussian_mean_gap
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianVarianceLaw}
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    {Llow Lhigh : GaussianVarianceLaw}
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccessHigh : S.latentAccessLaw e qHigh base = Lhigh)
    (hAccessLow : S.latentAccessLaw e qLow base = Llow)
    (hmean : Llow.mean < Lhigh.mean) :
    ¬ lg21SourceLawLatentSkillFair S := by
  apply paper_proposition4_2_not_law_latent_skill_fair_of_four_group_core
    e qHigh qLow base hNoAccess
  intro hsame
  have hLaw : Lhigh = Llow := by
    rw [← hAccessHigh, ← hAccessLow]
    exact hsame
  exact (GaussianVarianceLaw.ne_of_mean_lt hmean) hLaw.symm

/--
Proposition 4.2 posterior-law instantiation: if the access-side laws are the
conditional Gaussian posterior-score laws for two strictly ordered latent
skills, the source four-group argument rules out latent-skill fairness.
-/
theorem paper_proposition4_2_not_law_latent_skill_fair_of_conditional_posterior_mean_gap
    {Skill Base Test Feature : Type*} [Fintype Feature] [Nonempty Feature]
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianScaleLaw}
    (M : GaussianOffsetSignalFamily Feature)
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    {skillHigh skillLow : ℝ}
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccessHigh :
      S.latentAccessLaw e qHigh base =
        M.conditionalPosteriorMeanScaleLaw skillHigh)
    (hAccessLow :
      S.latentAccessLaw e qLow base =
        M.conditionalPosteriorMeanScaleLaw skillLow)
    (hskill : skillLow < skillHigh) :
    ¬ lg21SourceLawLatentSkillFair S := by
  apply paper_proposition4_2_not_law_latent_skill_fair_of_four_group_core
    e qHigh qLow base hNoAccess
  intro hsame
  have hLaw :
      M.conditionalPosteriorMeanScaleLaw skillHigh =
        M.conditionalPosteriorMeanScaleLaw skillLow := by
    rw [← hAccessHigh, ← hAccessLow]
    exact hsame
  have hmean :
      (M.conditionalPosteriorMeanScaleLaw skillLow).mean <
        (M.conditionalPosteriorMeanScaleLaw skillHigh).mean :=
    paper_conditional_posteriorMeanScaleLaw_mean_lt_of_skill_lt M hskill
  exact (GaussianScaleLaw.ne_of_mean_lt hmean) hLaw.symm

/--
Proposition 4.2 source-shaped law instantiation: no-access groups share the
same observed information, while access groups receive conditional Gaussian
posterior-score laws with different means.
-/
theorem paper_proposition4_2_not_estimate_law_latent_skill_fair_of_conditional_posterior_mean_gap
    {Skill Base Test Feature : Type*} [Fintype Feature] [Nonempty Feature]
    {S : LG21SourceLawPolicySurface Skill Base Test LG21EstimateLaw}
    (M : GaussianOffsetSignalFamily Feature)
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    {skillHigh skillLow : ℝ}
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccessHigh :
      S.latentAccessLaw e qHigh base =
        LG21EstimateLaw.gaussian
          (M.conditionalPosteriorMeanScaleLaw skillHigh))
    (hAccessLow :
      S.latentAccessLaw e qLow base =
        LG21EstimateLaw.gaussian
          (M.conditionalPosteriorMeanScaleLaw skillLow))
    (hskill : skillLow < skillHigh) :
    ¬ lg21SourceLawLatentSkillFair S := by
  apply paper_proposition4_2_not_law_latent_skill_fair_of_four_group_core
    e qHigh qLow base hNoAccess
  intro hsame
  have hLaw :
      LG21EstimateLaw.gaussian
          (M.conditionalPosteriorMeanScaleLaw skillHigh) =
        LG21EstimateLaw.gaussian
          (M.conditionalPosteriorMeanScaleLaw skillLow) := by
    rw [← hAccessHigh, ← hAccessLow]
    exact hsame
  have hmean :
      (M.conditionalPosteriorMeanScaleLaw skillLow).mean <
        (M.conditionalPosteriorMeanScaleLaw skillHigh).mean :=
    paper_conditional_posteriorMeanScaleLaw_mean_lt_of_skill_lt M hskill
  exact (LG21EstimateLaw.gaussian_ne_of_mean_lt hmean) hLaw.symm

/--
Proposition 4.2 source fixed-base instantiation: when non-test features are
fixed, the access-side posterior-score law is the affine image of the one
random optional test score.  Strictly ordered latent skills give different
Gaussian laws, and the four-group proof rules out latent-skill fairness.
-/
theorem paper_proposition4_2_not_estimate_law_latent_skill_fair_of_one_test_posterior_law
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test LG21EstimateLaw}
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    {intercept slope skillHigh skillLow testScale : ℝ}
    (hslope : 0 < slope) (htestScale : 0 < testScale)
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccessHigh :
      S.latentAccessLaw e qHigh base =
        LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope skillHigh testScale htestScale))
    (hAccessLow :
      S.latentAccessLaw e qLow base =
        LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope skillLow testScale htestScale))
    (hskill : skillLow < skillHigh) :
    ¬ lg21SourceLawLatentSkillFair S := by
  apply paper_proposition4_2_not_law_latent_skill_fair_of_four_group_core
    e qHigh qLow base hNoAccess
  intro hsame
  have hLaw :
      LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope skillHigh testScale htestScale) =
        LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope skillLow testScale htestScale) := by
    rw [← hAccessHigh, ← hAccessLow]
    exact hsame
  have hmean :
      (lg21OneTestPosteriorScoreLaw
        intercept slope hslope skillLow testScale htestScale).mean <
      (lg21OneTestPosteriorScoreLaw
        intercept slope hslope skillHigh testScale htestScale).mean :=
    paper_one_test_posterior_score_law_mean_lt_of_skill_lt
      hslope htestScale hskill
  exact (LG21EstimateLaw.gaussian_ne_of_mean_lt hmean) hLaw.symm

/--
Proposition 4.2 source-route wrapper: Lemma 4.1 supplies all-report/all-take
under the observed-access lower-tail threshold premises, and the fixed-base
one-test posterior law then gives the paper's latent-skill fairness
contradiction.
-/
theorem paper_proposition4_2_not_latent_skill_fair_of_lemma4_1_lower_tail_and_one_test_posterior_law
    {Feature Skill Base Test : Type*}
    [Fintype Feature] [DecidableEq Feature]
    {S : LG21SourceLawPolicySurface Skill Base Test LG21EstimateLaw}
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {reports takes : ℝ → Prop} {noReportEstimate qTilde : ℝ}
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    {intercept slope skillHigh skillLow testScale : ℝ}
    (hslope : 0 < slope) (htestScale : 0 < testScale)
    (hreportCutoffIfNotAll :
      ¬ (∀ score : ℝ, reports score) →
        ∃ cutoff : ℝ,
          (∀ score : ℝ, reports score ↔ cutoff ≤ score) ∧
            noReportEstimate =
              M.posteriorMean
                (Function.update theta k (C.lowerTailMean scoreLaw cutoff)))
    (hreportNoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (htakeCutoffIfNotAll :
      ¬ (∀ skill : ℝ, takes skill) →
        ∃ qBar : ℝ,
          (∀ skill : ℝ, takes skill ↔ qBar ≤ skill) ∧
            qTilde = C.lowerTailMean skillLaw qBar)
    (htakeNoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill testScale htestScale) qTilde))
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccessHigh :
      S.latentAccessLaw e qHigh base =
        LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope skillHigh testScale htestScale))
    (hAccessLow :
      S.latentAccessLaw e qLow base =
        LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope skillLow testScale htestScale))
    (hskill : skillLow < skillHigh) :
    (∀ score : ℝ, reports score) ∧
      (∀ skill : ℝ, takes skill) ∧
        ¬ lg21SourceLawLatentSkillFair S := by
  have hstrategy :
      (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
    paper_lemma4_1_strategy_proofness_of_lower_tail_thresholds
      C api M theta k scoreLaw skillLaw htestScale
      hreportCutoffIfNotAll hreportNoDeviation
      htakeCutoffIfNotAll htakeNoDeviation
  refine ⟨hstrategy.1, hstrategy.2, ?_⟩
  exact
    paper_proposition4_2_not_estimate_law_latent_skill_fair_of_one_test_posterior_law
      e qHigh qLow base hslope htestScale hNoAccess
      hAccessHigh hAccessLow hskill

/--
Proposition 4.2 source-route wrapper with explicit Lemma 4.1 threshold
policies: Gaussian Bayesian reporting and lower-tail taking thresholds first
give all-report/all-take, then the fixed-base one-test posterior law gives the
latent-skill fairness contradiction.
-/
theorem paper_proposition4_2_not_latent_skill_fair_of_explicit_thresholds_and_one_test_posterior_law
    {Feature Skill Base Test : Type*}
    [Fintype Feature] [DecidableEq Feature]
    {S : LG21SourceLawPolicySurface Skill Base Test LG21EstimateLaw}
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {reports takes : ℝ → Prop}
    {noReportEstimate qTilde reportingBase threshold qBar : ℝ}
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    {intercept slope skillHigh skillLow testScale : ℝ}
    (hslope : 0 < slope) (htestScale : 0 < testScale)
    (hreports :
      ∀ score : ℝ,
        reports score ↔
          threshold ≤ M.posteriorMean (Function.update theta k score))
    (hnoReport :
      noReportEstimate =
        M.posteriorMean
          (Function.update theta k
            (C.lowerTailMean scoreLaw
              (affineCutoff
                (M.posteriorMean (Function.update theta k reportingBase) -
                  M.centeredFamily.signalWeight k * reportingBase)
                (M.centeredFamily.signalWeight k) threshold))))
    (hreportNoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (htakes : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hqTilde : qTilde = C.lowerTailMean skillLaw qBar)
    (htakeNoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill testScale htestScale) qTilde))
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccessHigh :
      S.latentAccessLaw e qHigh base =
        LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope skillHigh testScale htestScale))
    (hAccessLow :
      S.latentAccessLaw e qLow base =
        LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope skillLow testScale htestScale))
    (hskill : skillLow < skillHigh) :
    (∀ score : ℝ, reports score) ∧
      (∀ skill : ℝ, takes skill) ∧
        ¬ lg21SourceLawLatentSkillFair S := by
  have hstrategy :
      (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
    paper_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_explicit_taking_threshold
      C api M theta k scoreLaw skillLaw htestScale hreports hnoReport
      hreportNoDeviation htakes hqTilde htakeNoDeviation
  refine ⟨hstrategy.1, hstrategy.2, ?_⟩
  exact
    paper_proposition4_2_not_estimate_law_latent_skill_fair_of_one_test_posterior_law
      e qHigh qLow base hslope htestScale hNoAccess
      hAccessHigh hAccessLow hskill

/--
Proposition 4.2 source-route wrapper from binary reporting/taking equilibria:
the equilibrium fields feed Lemma 4.1's explicit-threshold route, then the
fixed-base one-test posterior law gives the latent-skill fairness contradiction.
-/
theorem paper_proposition4_2_not_latent_skill_fair_of_threshold_equilibria_and_one_test_posterior_law
    {Feature Skill Base Test : Type*}
    [Fintype Feature] [DecidableEq Feature]
    {S : LG21SourceLawPolicySurface Skill Base Test LG21EstimateLaw}
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {reports takes : ℝ → Prop} [DecidablePred reports] [DecidablePred takes]
    {noReportEstimate qTilde reportingBase threshold qBar : ℝ}
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    {intercept slope skillHigh skillLow testScale : ℝ}
    (hslope : 0 < slope) (htestScale : 0 < testScale)
    (hreports :
      ∀ score : ℝ,
        reports score ↔
          threshold ≤ M.posteriorMean (Function.update theta k score))
    (hnoReport :
      noReportEstimate =
        M.posteriorMean
          (Function.update theta k
            (C.lowerTailMean scoreLaw
              (affineCutoff
                (M.posteriorMean (Function.update theta k reportingBase) -
                  M.centeredFamily.signalWeight k * reportingBase)
                (M.centeredFamily.signalWeight k) threshold))))
    (hreportEq :
      lg21Equilibrium
        (lg21ReportingEquilibriumData
          reports
          (fun value : ℝ => M.posteriorMean (Function.update theta k value))
          noReportEstimate))
    (htakes : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hqTilde : qTilde = C.lowerTailMean skillLaw qBar)
    (htakeEq :
      lg21Equilibrium
        (lg21TestTakingEquilibriumData takes
          (fun skill : ℝ =>
            api.thresholdPassProb
              (lg21GaussianTestScoreLaw skill testScale htestScale) qTilde)))
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccessHigh :
      S.latentAccessLaw e qHigh base =
        LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope skillHigh testScale htestScale))
    (hAccessLow :
      S.latentAccessLaw e qLow base =
        LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope skillLow testScale htestScale))
    (hskill : skillLow < skillHigh) :
    (∀ score : ℝ, reports score) ∧
      (∀ skill : ℝ, takes skill) ∧
        ¬ lg21SourceLawLatentSkillFair S := by
  have hstrategy :
      (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
    paper_lemma4_1_strategy_proofness_of_explicit_threshold_equilibria
      C api M theta k scoreLaw skillLaw htestScale hreports hnoReport
      hreportEq htakes hqTilde htakeEq
  refine ⟨hstrategy.1, hstrategy.2, ?_⟩
  exact
    paper_proposition4_2_not_estimate_law_latent_skill_fair_of_one_test_posterior_law
      e qHigh qLow base hslope htestScale hNoAccess
      hAccessHigh hAccessLow hskill

/--
Proposition 4.2 source-route wrapper from the packaged threshold-equilibrium
certificate: the certificate supplies Lemma 4.1, and the fixed-base one-test
posterior law gives the latent-skill fairness contradiction.
-/
theorem paper_proposition4_2_not_latent_skill_fair_of_threshold_equilibrium_certificate_and_one_test_posterior_law
    {Feature Skill Base Test : Type*}
    [Fintype Feature] [DecidableEq Feature]
    {S : LG21SourceLawPolicySurface Skill Base Test LG21EstimateLaw}
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    (e : S.Equilibrium) (qHigh qLow : Skill) (base : Base)
    {intercept slope skillHigh skillLow testScale : ℝ}
    (hslope : 0 < slope) (htestScale : 0 < testScale)
    (K :
      LG21GaussianThresholdEquilibriumCertificate
        C api M theta k scoreLaw skillLaw htestScale)
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccessHigh :
      S.latentAccessLaw e qHigh base =
        LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope skillHigh testScale htestScale))
    (hAccessLow :
      S.latentAccessLaw e qLow base =
        LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope skillLow testScale htestScale))
    (hskill : skillLow < skillHigh) :
    (∀ score : ℝ, K.reports score) ∧
      (∀ skill : ℝ, K.takes skill) ∧
        ¬ lg21SourceLawLatentSkillFair S := by
  have hstrategy :
      (∀ score : ℝ, K.reports score) ∧ (∀ skill : ℝ, K.takes skill) :=
    paper_lemma4_1_strategy_proofness_of_threshold_equilibrium_certificate
      C api M theta k scoreLaw skillLaw htestScale K
  refine ⟨hstrategy.1, hstrategy.2, ?_⟩
  exact
    paper_proposition4_2_not_estimate_law_latent_skill_fair_of_one_test_posterior_law
      e qHigh qLow base hslope htestScale hNoAccess
      hAccessHigh hAccessLow hskill

/-- Certificate for Proposition 4.3. -/
structure LG21NotObservableOrDemographicFairCertificate
    {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) where
  not_observably_fair : ¬ lg21SourceObservablyFair S
  not_demographically_fair : ¬ lg21SourceDemographicallyFair S

/--
Proposition 4.3 endpoint: full Bayesian optimality is not observable or
demographic fair.
-/
theorem paper_proposition4_3_not_observable_or_demographic_fair_of_certificate
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (C : LG21NotObservableOrDemographicFairCertificate S) :
    ¬ lg21SourceObservablyFair S ∧ ¬ lg21SourceDemographicallyFair S := by
  exact ⟨C.not_observably_fair, C.not_demographically_fair⟩

/--
Proposition 4.3 logical core: observable and demographic fairness both fail
once concrete law-difference witnesses are supplied.
-/
theorem paper_proposition4_3_not_observable_or_demographic_fair_of_witnesses
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (eObs : S.Equilibrium) (base : Base)
    (hobs : S.observableAccessEstimate eObs base ≠
      S.observableNoAccessEstimate eObs base)
    (eDemo : S.Equilibrium)
    (hdemo : S.demographicAccessEstimate eDemo ≠
      S.demographicNoAccessEstimate eDemo) :
    ¬ lg21SourceObservablyFair S ∧ ¬ lg21SourceDemographicallyFair S := by
  exact ⟨lg21_not_observablyFair_of_witness eObs base hobs,
    lg21_not_demographicallyFair_of_witness eDemo hdemo⟩

/--
Proposition 4.3 continuous-law core: observable and demographic law-difference
witnesses prove both source fairness definitions fail.
-/
theorem paper_proposition4_3_not_law_observable_or_demographic_fair_of_witnesses
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (eObs : S.Equilibrium) (base : Base)
    (hobs : S.observableAccessLaw eObs base ≠ S.observableNoAccessLaw eObs base)
    (eDemo : S.Equilibrium)
    (hdemo : S.demographicAccessLaw eDemo ≠ S.demographicNoAccessLaw eDemo) :
    ¬ lg21SourceLawObservablyFair S ∧ ¬ lg21SourceLawDemographicallyFair S := by
  exact ⟨lg21_not_lawObservablyFair_of_witness eObs base hobs,
    lg21_not_lawDemographicallyFair_of_witness eDemo hdemo⟩

/--
Proposition 4.3 Gaussian observable-law core: a strict variance gap between
the access and no-access Gaussian estimate laws proves observable fairness
fails at the given base profile.
-/
theorem paper_proposition4_3_not_law_observable_fair_of_gaussian_variance_gap
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianVarianceLaw}
    (e : S.Equilibrium) (base : Base)
    {Llow Lhigh : GaussianVarianceLaw}
    (hAccess : S.observableAccessLaw e base = Lhigh)
    (hNoAccess : S.observableNoAccessLaw e base = Llow)
    (hvar : Llow.variance < Lhigh.variance) :
    ¬ lg21SourceLawObservablyFair S := by
  apply lg21_not_lawObservablyFair_of_witness e base
  intro hsame
  have hLaw : Lhigh = Llow := by
    rw [← hAccess, ← hNoAccess]
    exact hsame
  exact (GaussianVarianceLaw.ne_of_variance_lt hvar) hLaw.symm

/--
Proposition 4.3 Gaussian demographic-law core: a strict variance gap between
the demographic Gaussian estimate laws proves demographic fairness fails.
-/
theorem paper_proposition4_3_not_law_demographic_fair_of_gaussian_variance_gap
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianVarianceLaw}
    (e : S.Equilibrium)
    {Llow Lhigh : GaussianVarianceLaw}
    (hAccess : S.demographicAccessLaw e = Lhigh)
    (hNoAccess : S.demographicNoAccessLaw e = Llow)
    (hvar : Llow.variance < Lhigh.variance) :
    ¬ lg21SourceLawDemographicallyFair S := by
  apply lg21_not_lawDemographicallyFair_of_witness e
  intro hsame
  have hLaw : Lhigh = Llow := by
    rw [← hAccess, ← hNoAccess]
    exact hsame
  exact (GaussianVarianceLaw.ne_of_variance_lt hvar) hLaw.symm

/--
Proposition 4.3 Gaussian observable-law core for location-scale laws: a strict
scale gap between the access and no-access posterior-score laws proves
observable fairness fails at the given base profile.
-/
theorem paper_proposition4_3_not_law_observable_fair_of_gaussian_scale_gap
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianScaleLaw}
    (e : S.Equilibrium) (base : Base)
    {Lsmall Llarge : GaussianScaleLaw}
    (hAccess : S.observableAccessLaw e base = Llarge)
    (hNoAccess : S.observableNoAccessLaw e base = Lsmall)
    (hscale : Lsmall.scale < Llarge.scale) :
    ¬ lg21SourceLawObservablyFair S := by
  apply lg21_not_lawObservablyFair_of_witness e base
  intro hsame
  have hLaw : Llarge = Lsmall := by
    rw [← hAccess, ← hNoAccess]
    exact hsame
  exact (GaussianScaleLaw.ne_of_scale_lt hscale) hLaw.symm

/--
Proposition 4.3 Gaussian demographic-law core for location-scale laws: a strict
scale gap between the demographic posterior-score laws proves demographic
fairness fails.
-/
theorem paper_proposition4_3_not_law_demographic_fair_of_gaussian_scale_gap
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianScaleLaw}
    (e : S.Equilibrium)
    {Lsmall Llarge : GaussianScaleLaw}
    (hAccess : S.demographicAccessLaw e = Llarge)
    (hNoAccess : S.demographicNoAccessLaw e = Lsmall)
    (hscale : Lsmall.scale < Llarge.scale) :
    ¬ lg21SourceLawDemographicallyFair S := by
  apply lg21_not_lawDemographicallyFair_of_witness e
  intro hsame
  have hLaw : Llarge = Lsmall := by
    rw [← hAccess, ← hNoAccess]
    exact hsame
  exact (GaussianScaleLaw.ne_of_scale_lt hscale) hLaw.symm

/--
Proposition 4.3 source-shaped observable-law core: conditional on a base
profile, Bayesian optimality gives a genuinely Gaussian access-side posterior
law, while the no-access estimate is fixed by the base profile.  A point law
and a Gaussian law cannot be equal, so observable fairness fails.
-/
theorem paper_proposition4_3_not_estimate_law_observable_fair_of_access_gaussian_no_access_point
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test LG21EstimateLaw}
    (e : S.Equilibrium) (base : Base)
    (estimate : ℝ) (Laccess : GaussianScaleLaw)
    (hAccess :
      S.observableAccessLaw e base = LG21EstimateLaw.gaussian Laccess)
    (hNoAccess :
      S.observableNoAccessLaw e base = LG21EstimateLaw.point estimate) :
    ¬ lg21SourceLawObservablyFair S := by
  apply lg21_not_lawObservablyFair_of_witness e base
  intro hsame
  have hLaw :
      LG21EstimateLaw.gaussian Laccess = LG21EstimateLaw.point estimate := by
    rw [← hAccess, ← hNoAccess]
    exact hsame
  exact (LG21EstimateLaw.gaussian_ne_point Laccess estimate) hLaw

/--
Proposition 4.3 fixed-base instantiation: after Lemma 4.1 makes access
students report, the access-side Bayesian estimate is the one-random-test
posterior-score law, while the no-access estimate is fixed by the base profile.
-/
theorem paper_proposition4_3_not_estimate_law_observable_fair_of_one_test_posterior_law_vs_point
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test LG21EstimateLaw}
    (e : S.Equilibrium) (base : Base)
    {intercept slope conditionalTestMean testScale noAccessEstimate : ℝ}
    (hslope : 0 < slope) (htestScale : 0 < testScale)
    (hAccess :
      S.observableAccessLaw e base =
        LG21EstimateLaw.gaussian
          (lg21OneTestPosteriorScoreLaw
            intercept slope hslope conditionalTestMean testScale htestScale))
    (hNoAccess :
      S.observableNoAccessLaw e base =
        LG21EstimateLaw.point noAccessEstimate) :
    ¬ lg21SourceLawObservablyFair S :=
  paper_proposition4_3_not_estimate_law_observable_fair_of_access_gaussian_no_access_point
    e base noAccessEstimate
    (lg21OneTestPosteriorScoreLaw
      intercept slope hslope conditionalTestMean testScale htestScale)
    hAccess hNoAccess

/--
Proposition 4.3 posterior-law instantiation: if the access policy observes a
feature family with strictly larger total signal precision than the no-access
policy, the induced Gaussian posterior-score laws cannot be observably fair.
-/
theorem paper_proposition4_3_not_law_observable_fair_of_posterior_precision_gap
    {Skill Base Test FeatureLow FeatureHigh : Type*}
    [Fintype FeatureLow] [Nonempty FeatureLow]
    [Fintype FeatureHigh] [Nonempty FeatureHigh]
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianScaleLaw}
    (e : S.Equilibrium) (base : Base)
    {Mlow : GaussianOffsetSignalFamily FeatureLow}
    {Mhigh : GaussianOffsetSignalFamily FeatureHigh}
    (hAccess : S.observableAccessLaw e base = Mhigh.posteriorMeanScaleLaw)
    (hNoAccess : S.observableNoAccessLaw e base = Mlow.posteriorMeanScaleLaw)
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      Mlow.centeredFamily.signalPrecisionSum <
        Mhigh.centeredFamily.signalPrecisionSum) :
    ¬ lg21SourceLawObservablyFair S :=
  paper_proposition4_3_not_law_observable_fair_of_gaussian_scale_gap
    e base hAccess hNoAccess
    (paper_gaussian_estimate_scale_lt_of_signalPrecisionSum_lt hpriorVar hsum)

/--
Proposition 4.3 posterior-law instantiation for demographic fairness: a strict
total-precision gap between no-access and access posterior-score laws rules out
demographic fairness.
-/
theorem paper_proposition4_3_not_law_demographic_fair_of_posterior_precision_gap
    {Skill Base Test FeatureLow FeatureHigh : Type*}
    [Fintype FeatureLow] [Nonempty FeatureLow]
    [Fintype FeatureHigh] [Nonempty FeatureHigh]
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianScaleLaw}
    (e : S.Equilibrium)
    {Mlow : GaussianOffsetSignalFamily FeatureLow}
    {Mhigh : GaussianOffsetSignalFamily FeatureHigh}
    (hAccess : S.demographicAccessLaw e = Mhigh.posteriorMeanScaleLaw)
    (hNoAccess : S.demographicNoAccessLaw e = Mlow.posteriorMeanScaleLaw)
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      Mlow.centeredFamily.signalPrecisionSum <
        Mhigh.centeredFamily.signalPrecisionSum) :
    ¬ lg21SourceLawDemographicallyFair S :=
  paper_proposition4_3_not_law_demographic_fair_of_gaussian_scale_gap
    e hAccess hNoAccess
    (paper_gaussian_estimate_scale_lt_of_signalPrecisionSum_lt hpriorVar hsum)

/--
Proposition 4.3 source-route wrapper: Lemma 4.1 removes the strategic
reporting/taking concern, and the posterior-precision gap then gives both the
observable- and demographic-fairness contradictions.
-/
theorem paper_proposition4_3_not_law_observable_or_demographic_fair_of_lemma4_1_lower_tail_and_posterior_precision_gap
    {Feature Skill Base Test FeatureLow FeatureHigh : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype FeatureLow] [Nonempty FeatureLow]
    [Fintype FeatureHigh] [Nonempty FeatureHigh]
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianScaleLaw}
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {reports takes : ℝ → Prop} {noReportEstimate qTilde testScale : ℝ}
    (htestScale : 0 < testScale)
    (hreportCutoffIfNotAll :
      ¬ (∀ score : ℝ, reports score) →
        ∃ cutoff : ℝ,
          (∀ score : ℝ, reports score ↔ cutoff ≤ score) ∧
            noReportEstimate =
              M.posteriorMean
                (Function.update theta k (C.lowerTailMean scoreLaw cutoff)))
    (hreportNoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (htakeCutoffIfNotAll :
      ¬ (∀ skill : ℝ, takes skill) →
        ∃ qBar : ℝ,
          (∀ skill : ℝ, takes skill ↔ qBar ≤ skill) ∧
            qTilde = C.lowerTailMean skillLaw qBar)
    (htakeNoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill testScale htestScale) qTilde))
    (eObs : S.Equilibrium) (base : Base) (eDemo : S.Equilibrium)
    {Mlow : GaussianOffsetSignalFamily FeatureLow}
    {Mhigh : GaussianOffsetSignalFamily FeatureHigh}
    (hAccessObs : S.observableAccessLaw eObs base = Mhigh.posteriorMeanScaleLaw)
    (hNoAccessObs : S.observableNoAccessLaw eObs base = Mlow.posteriorMeanScaleLaw)
    (hAccessDemo : S.demographicAccessLaw eDemo = Mhigh.posteriorMeanScaleLaw)
    (hNoAccessDemo : S.demographicNoAccessLaw eDemo = Mlow.posteriorMeanScaleLaw)
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      Mlow.centeredFamily.signalPrecisionSum <
        Mhigh.centeredFamily.signalPrecisionSum) :
    (∀ score : ℝ, reports score) ∧
      (∀ skill : ℝ, takes skill) ∧
        ¬ lg21SourceLawObservablyFair S ∧
          ¬ lg21SourceLawDemographicallyFair S := by
  have hstrategy :
      (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
    paper_lemma4_1_strategy_proofness_of_lower_tail_thresholds
      C api M theta k scoreLaw skillLaw htestScale
      hreportCutoffIfNotAll hreportNoDeviation
      htakeCutoffIfNotAll htakeNoDeviation
  refine ⟨hstrategy.1, hstrategy.2, ?_, ?_⟩
  · exact
      paper_proposition4_3_not_law_observable_fair_of_posterior_precision_gap
        eObs base hAccessObs hNoAccessObs hpriorVar hsum
  · exact
      paper_proposition4_3_not_law_demographic_fair_of_posterior_precision_gap
        eDemo hAccessDemo hNoAccessDemo hpriorVar hsum

/--
Proposition 4.3 source-route wrapper for the paper's concrete extra-test-signal
shape: Lemma 4.1 removes strategic concerns, and adding the observed test score
as one extra Gaussian signal gives the posterior-precision gap.
-/
theorem paper_proposition4_3_not_law_observable_or_demographic_fair_of_lemma4_1_lower_tail_and_extra_signal
    {StrategyFeature Skill Base Test Feature : Type*}
    [Fintype StrategyFeature] [DecidableEq StrategyFeature]
    [Fintype Feature] [Nonempty Feature]
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianScaleLaw}
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (Mstrategy : GaussianOffsetSignalFamily StrategyFeature)
    (theta : StrategyFeature → ℝ) (k : StrategyFeature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {reports takes : ℝ → Prop} {noReportEstimate qTilde testScale : ℝ}
    (htestScale : 0 < testScale)
    (hreportCutoffIfNotAll :
      ¬ (∀ score : ℝ, reports score) →
        ∃ cutoff : ℝ,
          (∀ score : ℝ, reports score ↔ cutoff ≤ score) ∧
            noReportEstimate =
              Mstrategy.posteriorMean
                (Function.update theta k (C.lowerTailMean scoreLaw cutoff)))
    (hreportNoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          Mstrategy.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (htakeCutoffIfNotAll :
      ¬ (∀ skill : ℝ, takes skill) →
        ∃ qBar : ℝ,
          (∀ skill : ℝ, takes skill ↔ qBar ≤ skill) ∧
            qTilde = C.lowerTailMean skillLaw qBar)
    (htakeNoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill testScale htestScale) qTilde))
    (eObs : S.Equilibrium) (base : Base) (eDemo : S.Equilibrium)
    (Mbase : GaussianOffsetSignalFamily Feature)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar)
    (hAccessObs :
      S.observableAccessLaw eObs base =
        (Mbase.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).posteriorMeanScaleLaw)
    (hNoAccessObs :
      S.observableNoAccessLaw eObs base = Mbase.posteriorMeanScaleLaw)
    (hAccessDemo :
      S.demographicAccessLaw eDemo =
        (Mbase.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).posteriorMeanScaleLaw)
    (hNoAccessDemo :
      S.demographicNoAccessLaw eDemo = Mbase.posteriorMeanScaleLaw) :
    (∀ score : ℝ, reports score) ∧
      (∀ skill : ℝ, takes skill) ∧
        ¬ lg21SourceLawObservablyFair S ∧
          ¬ lg21SourceLawDemographicallyFair S :=
  paper_proposition4_3_not_law_observable_or_demographic_fair_of_lemma4_1_lower_tail_and_posterior_precision_gap
    C api Mstrategy theta k scoreLaw skillLaw htestScale
    hreportCutoffIfNotAll hreportNoDeviation
    htakeCutoffIfNotAll htakeNoDeviation
    eObs base eDemo
    (Mlow := Mbase)
    (Mhigh := Mbase.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar)
    hAccessObs hNoAccessObs hAccessDemo hNoAccessDemo rfl
    (GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
      Mbase extraNoiseMean extraNoiseVar hextraNoiseVar)

/--
Proposition 4.3 source-route wrapper with explicit Lemma 4.1 thresholds and
the paper's concrete extra-test-signal posterior-precision gap.
-/
theorem paper_proposition4_3_not_law_observable_or_demographic_fair_of_explicit_thresholds_and_extra_signal
    {StrategyFeature Skill Base Test Feature : Type*}
    [Fintype StrategyFeature] [DecidableEq StrategyFeature]
    [Fintype Feature] [Nonempty Feature]
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianScaleLaw}
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (Mstrategy : GaussianOffsetSignalFamily StrategyFeature)
    (theta : StrategyFeature → ℝ) (k : StrategyFeature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {reports takes : ℝ → Prop}
    {noReportEstimate qTilde reportingBase threshold qBar testScale : ℝ}
    (htestScale : 0 < testScale)
    (hreports :
      ∀ score : ℝ,
        reports score ↔
          threshold ≤ Mstrategy.posteriorMean (Function.update theta k score))
    (hnoReport :
      noReportEstimate =
        Mstrategy.posteriorMean
          (Function.update theta k
            (C.lowerTailMean scoreLaw
              (affineCutoff
                (Mstrategy.posteriorMean (Function.update theta k reportingBase) -
                  Mstrategy.centeredFamily.signalWeight k * reportingBase)
                (Mstrategy.centeredFamily.signalWeight k) threshold))))
    (hreportNoDeviation :
      lg21NoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          Mstrategy.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (htakes : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hqTilde : qTilde = C.lowerTailMean skillLaw qBar)
    (htakeNoDeviation :
      lg21NoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (lg21GaussianTestScoreLaw skill testScale htestScale) qTilde))
    (eObs : S.Equilibrium) (base : Base) (eDemo : S.Equilibrium)
    (Mbase : GaussianOffsetSignalFamily Feature)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar)
    (hAccessObs :
      S.observableAccessLaw eObs base =
        (Mbase.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).posteriorMeanScaleLaw)
    (hNoAccessObs :
      S.observableNoAccessLaw eObs base = Mbase.posteriorMeanScaleLaw)
    (hAccessDemo :
      S.demographicAccessLaw eDemo =
        (Mbase.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).posteriorMeanScaleLaw)
    (hNoAccessDemo :
      S.demographicNoAccessLaw eDemo = Mbase.posteriorMeanScaleLaw) :
    (∀ score : ℝ, reports score) ∧
      (∀ skill : ℝ, takes skill) ∧
        ¬ lg21SourceLawObservablyFair S ∧
          ¬ lg21SourceLawDemographicallyFair S := by
  have hstrategy :
      (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
    paper_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_explicit_taking_threshold
      C api Mstrategy theta k scoreLaw skillLaw htestScale hreports hnoReport
      hreportNoDeviation htakes hqTilde htakeNoDeviation
  refine ⟨hstrategy.1, hstrategy.2, ?_, ?_⟩
  · exact
      paper_proposition4_3_not_law_observable_fair_of_posterior_precision_gap
        eObs base hAccessObs hNoAccessObs rfl
        (GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
          Mbase extraNoiseMean extraNoiseVar hextraNoiseVar)
  · exact
      paper_proposition4_3_not_law_demographic_fair_of_posterior_precision_gap
        eDemo hAccessDemo hNoAccessDemo rfl
        (GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
          Mbase extraNoiseMean extraNoiseVar hextraNoiseVar)

/--
Proposition 4.3 source-route wrapper from binary reporting/taking equilibria
and the paper's concrete extra-test-signal posterior-precision gap.
-/
theorem paper_proposition4_3_not_law_observable_or_demographic_fair_of_threshold_equilibria_and_extra_signal
    {StrategyFeature Skill Base Test Feature : Type*}
    [Fintype StrategyFeature] [DecidableEq StrategyFeature]
    [Fintype Feature] [Nonempty Feature]
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianScaleLaw}
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (Mstrategy : GaussianOffsetSignalFamily StrategyFeature)
    (theta : StrategyFeature → ℝ) (k : StrategyFeature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {reports takes : ℝ → Prop} [DecidablePred reports] [DecidablePred takes]
    {noReportEstimate qTilde reportingBase threshold qBar testScale : ℝ}
    (htestScale : 0 < testScale)
    (hreports :
      ∀ score : ℝ,
        reports score ↔
          threshold ≤ Mstrategy.posteriorMean (Function.update theta k score))
    (hnoReport :
      noReportEstimate =
        Mstrategy.posteriorMean
          (Function.update theta k
            (C.lowerTailMean scoreLaw
              (affineCutoff
                (Mstrategy.posteriorMean (Function.update theta k reportingBase) -
                  Mstrategy.centeredFamily.signalWeight k * reportingBase)
                (Mstrategy.centeredFamily.signalWeight k) threshold))))
    (hreportEq :
      lg21Equilibrium
        (lg21ReportingEquilibriumData
          reports
          (fun value : ℝ => Mstrategy.posteriorMean (Function.update theta k value))
          noReportEstimate))
    (htakes : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hqTilde : qTilde = C.lowerTailMean skillLaw qBar)
    (htakeEq :
      lg21Equilibrium
        (lg21TestTakingEquilibriumData takes
          (fun skill : ℝ =>
            api.thresholdPassProb
              (lg21GaussianTestScoreLaw skill testScale htestScale) qTilde)))
    (eObs : S.Equilibrium) (base : Base) (eDemo : S.Equilibrium)
    (Mbase : GaussianOffsetSignalFamily Feature)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar)
    (hAccessObs :
      S.observableAccessLaw eObs base =
        (Mbase.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).posteriorMeanScaleLaw)
    (hNoAccessObs :
      S.observableNoAccessLaw eObs base = Mbase.posteriorMeanScaleLaw)
    (hAccessDemo :
      S.demographicAccessLaw eDemo =
        (Mbase.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).posteriorMeanScaleLaw)
    (hNoAccessDemo :
      S.demographicNoAccessLaw eDemo = Mbase.posteriorMeanScaleLaw) :
    (∀ score : ℝ, reports score) ∧
      (∀ skill : ℝ, takes skill) ∧
        ¬ lg21SourceLawObservablyFair S ∧
          ¬ lg21SourceLawDemographicallyFair S := by
  have hstrategy :
      (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
    paper_lemma4_1_strategy_proofness_of_explicit_threshold_equilibria
      C api Mstrategy theta k scoreLaw skillLaw htestScale hreports hnoReport
      hreportEq htakes hqTilde htakeEq
  refine ⟨hstrategy.1, hstrategy.2, ?_, ?_⟩
  · exact
      paper_proposition4_3_not_law_observable_fair_of_posterior_precision_gap
        eObs base hAccessObs hNoAccessObs rfl
        (GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
          Mbase extraNoiseMean extraNoiseVar hextraNoiseVar)
  · exact
      paper_proposition4_3_not_law_demographic_fair_of_posterior_precision_gap
        eDemo hAccessDemo hNoAccessDemo rfl
        (GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
          Mbase extraNoiseMean extraNoiseVar hextraNoiseVar)

/--
Proposition 4.3 source-route wrapper from the packaged threshold-equilibrium
certificate and the paper's concrete extra-test-signal posterior-precision gap.
-/
theorem paper_proposition4_3_not_law_observable_or_demographic_fair_of_threshold_equilibrium_certificate_and_extra_signal
    {StrategyFeature Skill Base Test Feature : Type*}
    [Fintype StrategyFeature] [DecidableEq StrategyFeature]
    [Fintype Feature] [Nonempty Feature]
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianScaleLaw}
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI)
    (Mstrategy : GaussianOffsetSignalFamily StrategyFeature)
    (theta : StrategyFeature → ℝ) (k : StrategyFeature)
    (scoreLaw skillLaw : GaussianScaleLaw)
    {testScale : ℝ} (htestScale : 0 < testScale)
    (K :
      LG21GaussianThresholdEquilibriumCertificate
        C api Mstrategy theta k scoreLaw skillLaw htestScale)
    (eObs : S.Equilibrium) (base : Base) (eDemo : S.Equilibrium)
    (Mbase : GaussianOffsetSignalFamily Feature)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar)
    (hAccessObs :
      S.observableAccessLaw eObs base =
        (Mbase.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).posteriorMeanScaleLaw)
    (hNoAccessObs :
      S.observableNoAccessLaw eObs base = Mbase.posteriorMeanScaleLaw)
    (hAccessDemo :
      S.demographicAccessLaw eDemo =
        (Mbase.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).posteriorMeanScaleLaw)
    (hNoAccessDemo :
      S.demographicNoAccessLaw eDemo = Mbase.posteriorMeanScaleLaw) :
    (∀ score : ℝ, K.reports score) ∧
      (∀ skill : ℝ, K.takes skill) ∧
        ¬ lg21SourceLawObservablyFair S ∧
          ¬ lg21SourceLawDemographicallyFair S := by
  have hstrategy :
      (∀ score : ℝ, K.reports score) ∧ (∀ skill : ℝ, K.takes skill) :=
    paper_lemma4_1_strategy_proofness_of_threshold_equilibrium_certificate
      C api Mstrategy theta k scoreLaw skillLaw htestScale K
  refine ⟨hstrategy.1, hstrategy.2, ?_, ?_⟩
  · exact
      paper_proposition4_3_not_law_observable_fair_of_posterior_precision_gap
        eObs base hAccessObs hNoAccessObs rfl
        (GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
          Mbase extraNoiseMean extraNoiseVar hextraNoiseVar)
  · exact
      paper_proposition4_3_not_law_demographic_fair_of_posterior_precision_gap
        eDemo hAccessDemo hNoAccessDemo rfl
        (GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
          Mbase extraNoiseMean extraNoiseVar hextraNoiseVar)

/-- Observable fairness implies demographic fairness when the base-profile law is shared. -/
theorem lg21_demographicallyFair_of_observableFair
    {ΩBase Estimate : Type*} (baseProfile : PMF ΩBase)
    {access noAccess : ΩBase → PMF Estimate}
    (hobs : lg21ObservableFair access noAccess) :
    lg21DemographicallyFair baseProfile access noAccess := by
  exact demographicallyFair_of_observableFair baseProfile hobs

/--
Definition 6, finite-kernel form: re-sampling uses the same conditional
test-score law that generated observed test scores for access students.
-/
theorem paper_definition6_resampling_policy_observable_kernel
    {ΩBase ΩTest Estimate : Type*} [Fintype ΩBase] [DecidableEq ΩBase]
    (e : LG21ResamplingExperiment ΩBase ΩTest Estimate) :
    lg21ResamplingPolicyKernel e = e.signalGivenBase := by
  exact resamplingSignalKernel_eq_signalGivenBase e

/--
Theorem 4.4, observable-fairness core.

Conditional on each non-test base profile, the access estimate and the
re-sampled no-access estimate are pushforwards of the same conditional
test-score distribution through the same estimation map.
-/
theorem paper_theorem4_4_resampling_policy_observably_fair
    {ΩBase ΩTest Estimate : Type*} [Fintype ΩBase] [DecidableEq ΩBase]
    (e : LG21ResamplingExperiment ΩBase ΩTest Estimate) :
    lg21ObservableFair (lg21AccessEstimateKernel e) (lg21ResamplingEstimateKernel e) := by
  intro base
  rfl

/--
Theorem 4.4, demographic-fairness core.

Mixing the conditional observable-fairness identity over the shared base-profile
distribution gives equality of the overall access and no-access estimate laws.
-/
theorem paper_theorem4_4_resampling_policy_demographically_fair
    {ΩBase ΩTest Estimate : Type*} [Fintype ΩBase] [DecidableEq ΩBase]
    (e : LG21ResamplingExperiment ΩBase ΩTest Estimate) :
    lg21DemographicallyFair e.baseProfile
      (lg21AccessEstimateKernel e) (lg21ResamplingEstimateKernel e) := by
  exact lg21_demographicallyFair_of_observableFair e.baseProfile
    (paper_theorem4_4_resampling_policy_observably_fair e)

def lg21BaseModel {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) : AdmissionsModel Θ ΩBase :=
  {prior := m.prior, signalKernel := m.baseKernel}

def lg21TestModel {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) : AdmissionsModel Θ ΩTest :=
  {prior := m.prior, signalKernel := m.testKernel}

def lg21BaseMass {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] : ℝ :=
  admissionsSelectedWelfareMass (lg21BaseModel m) p m.quality

def lg21BaseConditionalMass {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] : ℝ :=
  admissionsSelectedWelfareConditionalExp (lg21BaseModel m) p m.quality

def lg21TestMass {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] : ℝ :=
  admissionsSelectedWelfareMass (lg21TestModel m) p m.quality

def lg21TestConditionalMass {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] : ℝ :=
  admissionsSelectedWelfareConditionalExp (lg21TestModel m) p m.quality

def lg21BaseSelectionProb {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] : ℝ :=
  admissionsSelectionProb (lg21BaseModel m) p

def lg21TestSelectionProb {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] : ℝ :=
  admissionsSelectionProb (lg21TestModel m) p

theorem lg21_base_universal_accept
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) :
    lg21BaseMass m (fun _ : ΩBase => True) = pmfExp m.prior m.quality := by
  simpa [lg21BaseMass] using
    (admissionsSelectionMass_of_true (m := lg21BaseModel m) (value := m.quality))

theorem lg21_base_no_accept
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) :
    lg21BaseMass m (fun _ : ΩBase => False) = 0 := by
  simp [lg21BaseMass]

theorem lg21_base_mass_of_compl
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] :
    lg21BaseMass m (fun ω => ¬ p ω) = pmfExp m.prior m.quality - lg21BaseMass m p := by
  simpa [lg21BaseMass] using
    (admissionsSelectedWelfareMass_of_compl (m := lg21BaseModel m) (p := p)
      (value := m.quality))

theorem lg21_base_mass_le_total_of_quality_nonneg
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p]
    (hvalue : ∀ θ, 0 ≤ m.quality θ) :
    lg21BaseMass m p ≤ pmfExp m.prior m.quality := by
  exact admissionsSelectedWelfareMass_le_total_of_value_nonneg (m := lg21BaseModel m)
    (p := p) (value := m.quality) hvalue

theorem lg21_base_conditional_of_zero_selection
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p]
    (hprob : lg21BaseSelectionProb m p = 0) :
    lg21BaseConditionalMass m p = 0 := by
  have hprob' : admissionsSelectionProb (lg21BaseModel m) p = 0 := by
    simpa [lg21BaseSelectionProb] using hprob
  unfold lg21BaseConditionalMass
  exact admissionsSelectedWelfareConditionalExp_of_selectionProb_zero (m := lg21BaseModel m)
    (p := p) (value := m.quality) (hprob := hprob')

theorem lg21_base_mass_of_zero_selection
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p]
    (hprob : lg21BaseSelectionProb m p = 0) :
    lg21BaseMass m p = 0 := by
  have hprob' : admissionsSelectionProb (lg21BaseModel m) p = 0 := by
    simpa [lg21BaseSelectionProb] using hprob
  unfold lg21BaseMass
  exact admissionsSelectedWelfareMass_of_selectionProb_zero (m := lg21BaseModel m)
    (p := p) (value := m.quality) hprob'

theorem lg21_base_mass_eq_selectionProb_mul_conditionalMass
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] :
    lg21BaseMass m p = lg21BaseSelectionProb m p * lg21BaseConditionalMass m p := by
  simpa [lg21BaseMass, lg21BaseConditionalMass, lg21BaseSelectionProb] using
    (admissionsSelectedWelfareMass_eq_selectionProb_mul_conditionalExp (m := lg21BaseModel m)
      (p := p) (value := m.quality))

theorem lg21_base_mass_nonneg_of_quality_nonneg
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p]
    (hvalue : ∀ θ, 0 ≤ m.quality θ) :
    0 ≤ lg21BaseMass m p := by
  unfold lg21BaseMass
  exact admissionsSelectedWelfareMass_nonneg_of_value_nonneg (m := lg21BaseModel m)
    (p := p) (value := m.quality) hvalue

theorem lg21_base_conditional_nonneg_of_quality_nonneg
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p]
    (hvalue : ∀ θ, 0 ≤ m.quality θ) :
    0 ≤ lg21BaseConditionalMass m p := by
  unfold lg21BaseConditionalMass
  exact admissionsSelectedWelfareConditionalExp_nonneg_of_value_nonneg (m := lg21BaseModel m)
    (p := p) (value := m.quality) hvalue

theorem lg21_base_mass_le_of_pred_le
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p q : ΩBase → Prop) [DecidablePred p] [DecidablePred q]
    (hvalue : ∀ θ, 0 ≤ m.quality θ)
    (hsub : ∀ ω, p ω → q ω) :
    lg21BaseMass m p ≤ lg21BaseMass m q := by
  unfold lg21BaseMass
  exact admissionsSelectedWelfareMass_le_of_pred_le (m := lg21BaseModel m) (p := p) (q := q)
    (value := m.quality) hvalue hsub

theorem lg21_test_universal_accept
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) :
    lg21TestMass m (fun _ : ΩTest => True) = pmfExp m.prior m.quality := by
  simpa [lg21TestMass] using
    (admissionsSelectionMass_of_true (m := lg21TestModel m) (value := m.quality))

theorem lg21_test_no_accept
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) :
    lg21TestMass m (fun _ : ΩTest => False) = 0 := by
  simp [lg21TestMass]

theorem lg21_test_mass_of_compl
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] :
    lg21TestMass m (fun ω => ¬ p ω) = pmfExp m.prior m.quality - lg21TestMass m p := by
  simpa [lg21TestMass] using
    (admissionsSelectedWelfareMass_of_compl (m := lg21TestModel m) (p := p)
      (value := m.quality))

theorem lg21_test_mass_le_total_of_quality_nonneg
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p]
    (hvalue : ∀ θ, 0 ≤ m.quality θ) :
    lg21TestMass m p ≤ pmfExp m.prior m.quality := by
  exact admissionsSelectedWelfareMass_le_total_of_value_nonneg (m := lg21TestModel m)
    (p := p) (value := m.quality) hvalue

theorem lg21_test_conditional_of_zero_selection
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p]
    (hprob : lg21TestSelectionProb m p = 0) :
    lg21TestConditionalMass m p = 0 := by
  have hprob' : admissionsSelectionProb (lg21TestModel m) p = 0 := by
    simpa [lg21TestSelectionProb] using hprob
  unfold lg21TestConditionalMass
  exact admissionsSelectedWelfareConditionalExp_of_selectionProb_zero (m := lg21TestModel m)
    (p := p) (value := m.quality) (hprob := hprob')

theorem lg21_test_mass_of_zero_selection
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p]
    (hprob : lg21TestSelectionProb m p = 0) :
    lg21TestMass m p = 0 := by
  have hprob' : admissionsSelectionProb (lg21TestModel m) p = 0 := by
    simpa [lg21TestSelectionProb] using hprob
  unfold lg21TestMass
  exact admissionsSelectedWelfareMass_of_selectionProb_zero (m := lg21TestModel m)
    (p := p) (value := m.quality) hprob'

theorem lg21_test_mass_eq_selectionProb_mul_conditionalMass
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] :
    lg21TestMass m p = lg21TestSelectionProb m p * lg21TestConditionalMass m p := by
  simpa [lg21TestMass, lg21TestConditionalMass, lg21TestSelectionProb] using
    (admissionsSelectedWelfareMass_eq_selectionProb_mul_conditionalExp (m := lg21TestModel m)
      (p := p) (value := m.quality))

theorem lg21_test_mass_nonneg_of_quality_nonneg
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p]
    (hvalue : ∀ θ, 0 ≤ m.quality θ) :
    0 ≤ lg21TestMass m p := by
  unfold lg21TestMass
  exact admissionsSelectedWelfareMass_nonneg_of_value_nonneg (m := lg21TestModel m)
    (p := p) (value := m.quality) hvalue

theorem lg21_test_conditional_nonneg_of_quality_nonneg
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p]
    (hvalue : ∀ θ, 0 ≤ m.quality θ) :
    0 ≤ lg21TestConditionalMass m p := by
  unfold lg21TestConditionalMass
  exact admissionsSelectedWelfareConditionalExp_nonneg_of_value_nonneg (m := lg21TestModel m)
    (p := p) (value := m.quality) hvalue

theorem lg21_test_mass_le_of_pred_le
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p q : ΩTest → Prop) [DecidablePred p] [DecidablePred q]
    (hvalue : ∀ θ, 0 ≤ m.quality θ)
    (hsub : ∀ ω, p ω → q ω) :
    lg21TestMass m p ≤ lg21TestMass m q := by
  unfold lg21TestMass
  exact admissionsSelectedWelfareMass_le_of_pred_le (m := lg21TestModel m) (p := p) (q := q)
    (value := m.quality) hvalue hsub

theorem lg21_base_conditional_universal_accept
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) :
    lg21BaseConditionalMass m (fun _ : ΩBase => True) = pmfExp m.prior m.quality := by
  simpa [lg21BaseConditionalMass] using
    (admissionsSelectedWelfareConditionalExp_of_true (m := lg21BaseModel m) (value := m.quality))

theorem lg21_test_conditional_universal_accept
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) :
  lg21TestConditionalMass m (fun _ : ΩTest => True) = pmfExp m.prior m.quality := by
  simpa [lg21TestConditionalMass] using
    (admissionsSelectedWelfareConditionalExp_of_true (m := lg21TestModel m) (value := m.quality))

theorem lg21_base_conditional_of_compl
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] :
    lg21BaseConditionalMass m (fun ω => ¬ p ω) =
      (pmfExp m.prior m.quality - lg21BaseSelectionProb m p * lg21BaseConditionalMass m p) /
        lg21BaseSelectionProb m (fun ω => ¬ p ω) := by
  simpa [lg21BaseConditionalMass, lg21BaseSelectionProb] using
    (admissionsSelectedWelfareConditionalExp_of_compl (m := lg21BaseModel m) (p := p)
      (value := m.quality))

theorem lg21_base_exp_decompose
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] :
    pmfExp m.prior m.quality =
      lg21BaseSelectionProb m p * lg21BaseConditionalMass m p +
        lg21BaseSelectionProb m (fun ω => ¬ p ω) * lg21BaseConditionalMass m (fun ω => ¬ p ω) := by
  simpa [lg21TwoSignalAdmissionsModel, twoSignalLeftSelectionProb,
    twoSignalLeftConditionalValue, twoSignalLeftModel, lg21BaseSelectionProb,
    lg21BaseConditionalMass, lg21BaseModel] using
    (twoSignalLeftValueExp_decompose (m := lg21TwoSignalAdmissionsModel m) (p := p))

theorem lg21_test_conditional_of_compl
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] :
    lg21TestConditionalMass m (fun ω => ¬ p ω) =
      (pmfExp m.prior m.quality - lg21TestSelectionProb m p * lg21TestConditionalMass m p) /
        lg21TestSelectionProb m (fun ω => ¬ p ω) := by
  simpa [lg21TestConditionalMass, lg21TestSelectionProb] using
    (admissionsSelectedWelfareConditionalExp_of_compl (m := lg21TestModel m) (p := p)
      (value := m.quality))

theorem lg21_test_exp_decompose
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : LG21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] :
    pmfExp m.prior m.quality =
      lg21TestSelectionProb m p * lg21TestConditionalMass m p +
        lg21TestSelectionProb m (fun ω => ¬ p ω) * lg21TestConditionalMass m (fun ω => ¬ p ω) := by
  simpa [lg21TwoSignalAdmissionsModel, twoSignalRightSelectionProb,
    twoSignalRightConditionalValue, twoSignalRightModel, lg21TestSelectionProb,
    lg21TestConditionalMass, lg21TestModel] using
    (twoSignalRightValueExp_decompose (m := lg21TwoSignalAdmissionsModel m) (p := p))

end

end LG21TestOptionalPolicies
