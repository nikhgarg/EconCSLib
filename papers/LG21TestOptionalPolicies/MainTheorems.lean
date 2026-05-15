import EconCSLib.Foundations.Probability.Admissions
import EconCSLib.Foundations.Probability.Gaussian
import EconCSLib.Foundations.Math.AffineThreshold

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
