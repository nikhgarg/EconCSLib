import LG21TestOptionalPolicies.MainTheorems

/-!
# Human-Facing Interface: LG21 Test-Optional Policies

This file is the compact audit surface for
*Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps*.
It lists the source-facing definitions and named theorem endpoints in paper
order.  The re-sampling distributional core is proved; the strategic and
Gaussian posterior endpoints remain certificate-shaped.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open EconCSLib.Probability

/-- Definition 1: equilibrium for the abstract test-taking/reporting game. -/
abbrev paperEquilibrium {StudentInfo Action : Type*}
    (E : LG21EquilibriumData StudentInfo Action) : Prop :=
  lg21Equilibrium E

/--
Definition 1 bridge: in the binary reporting subgame, equilibrium implies the
no-profitable-withholding condition used by Lemma 4.1.
-/
theorem paper_interface_no_profitable_withholding_of_reporting_equilibrium
    {reports : ℝ → Prop} [DecidablePred reports]
    {reportedEstimate : ℝ → ℝ} {noReportEstimate : ℝ}
    (hEq :
      paperEquilibrium
        (lg21ReportingEquilibriumData
          reports reportedEstimate noReportEstimate)) :
    lg21NoProfitableWithholdingDeviation
      reports reportedEstimate noReportEstimate :=
  lg21NoProfitableWithholdingDeviation_of_reporting_equilibrium hEq

/--
Definition 1 bridge: in the binary test-taking subgame, equilibrium implies
the no-profitable-test-taking condition used by Lemma 4.1.
-/
theorem paper_interface_no_profitable_test_taking_of_taking_equilibrium
    {takes : ℝ → Prop} [DecidablePred takes]
    {testBenefitProb : ℝ → ℝ}
    (hEq :
      paperEquilibrium
        (lg21TestTakingEquilibriumData takes testBenefitProb)) :
    lg21NoProfitableTestTakingDeviation takes testBenefitProb :=
  lg21NoProfitableTestTakingDeviation_of_taking_equilibrium hEq

/-- Definition 1 action object for students with test access: `(Y, X)`. -/
abbrev paperAccessAction : Type :=
  LG21AccessAction

/-- Definition 1 feasibility condition: `Y ≥ X` plus the requirement policy. -/
abbrev paperAccessActionFeasible
    (requirement : LG21AccessAction → Prop) (a : LG21AccessAction) : Prop :=
  LG21AccessAction.feasible requirement a

/-- Source regime with optional reporting after taking the test. -/
abbrev paperOptionalReportingRequirement (a : LG21AccessAction) : Prop :=
  LG21AccessAction.optionalReportingRequirement a

/-- Source regime where reporting is required conditional on taking the test. -/
abbrev paperReportRequiredAfterTaking (a : LG21AccessAction) : Prop :=
  LG21AccessAction.reportRequiredAfterTaking a

/-- Under `Y = X`, the source feasibility condition `Y ≥ X` holds. -/
theorem paper_interface_reportRequiredAfterTaking_reportImpliesTake
    {a : LG21AccessAction} (h : paperReportRequiredAfterTaking a) :
    LG21AccessAction.reportImpliesTake a :=
  LG21AccessAction.reportRequiredAfterTaking_reportImpliesTake h

/-- Definition 2: latent-skill fairness in every equilibrium. -/
abbrev paperLatentSkillFair {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) : Prop :=
  lg21SourceLatentSkillFair S

/-- Continuous-law Definition 2: latent-skill fairness by equality of estimate laws. -/
abbrev paperLawLatentSkillFair {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  lg21SourceLawLatentSkillFair S

/-- Definition 3: observable fairness in every equilibrium. -/
abbrev paperObservablyFair {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) : Prop :=
  lg21SourceObservablyFair S

/-- Continuous-law Definition 3: observable fairness by equality of estimate laws. -/
abbrev paperLawObservablyFair {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  lg21SourceLawObservablyFair S

/-- Definition 4: demographic fairness in every equilibrium. -/
abbrev paperDemographicallyFair {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) : Prop :=
  lg21SourceDemographicallyFair S

/-- Continuous-law Definition 4: demographic fairness by equality of estimate laws. -/
abbrev paperLawDemographicallyFair {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  lg21SourceLawDemographicallyFair S

/-- Definition 5: test-blankness, i.e. test scores play no role. -/
abbrev paperTestBlank {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) : Prop :=
  lg21SourceTestBlank S

/-- Continuous-law Definition 5: test scores play no role in estimate laws. -/
abbrev paperLawTestBlank {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) : Prop :=
  lg21SourceLawTestBlank S

/--
Definitions 2--3 implication, with the source's mixture interpretation made
explicit: latent-skill fairness implies observable fairness when observable
laws are the shared-skill-law mixtures of latent-skill-conditioned laws.
-/
theorem paper_interface_definition2_implies_definition3_of_mixture
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
    (hlatent : paperLatentSkillFair S) :
    paperObservablyFair S :=
  lg21_sourceObservablyFair_of_latentSkillFair_of_mixture
    skillGivenBase hAccess hNoAccess hlatent

/--
Definitions 3--4 implication, with the source's mixture interpretation made
explicit: observable fairness implies demographic fairness when demographic
laws are the shared-base-profile mixtures of observable laws.
-/
theorem paper_interface_definition3_implies_definition4_of_mixture
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
    (hobs : paperObservablyFair S) :
    paperDemographicallyFair S :=
  lg21_sourceDemographicallyFair_of_observablyFair_of_mixture
    baseProfile hAccess hNoAccess hobs

/--
Definitions 2--4 implication chain: under the shared latent-skill and
base-profile mixture identities, latent-skill fairness implies demographic
fairness.
-/
theorem paper_interface_definition2_implies_definition4_of_mixture
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
    (hlatent : paperLatentSkillFair S) :
    paperDemographicallyFair S :=
  lg21_sourceDemographicallyFair_of_latentSkillFair_of_mixture
    skillGivenBase baseProfile hObsAccess hObsNoAccess hDemoAccess hDemoNoAccess
    hlatent

/--
Bayesian optimal Gaussian estimator used in Sections 3--4.

Paper statement context: `P_BO` estimates skill by posterior expectation
`E[q | I]`.  For Gaussian prior and noisy features, this is the
precision-weighted posterior mean; its marginal law has mean `μ` and variance
`σ^2 * sum_signal_precision / posterior_precision`.
-/
theorem paper_interface_bayesian_optimal_estimator_gaussian
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
            M.centeredFamily.posteriorPrecision :=
  paper_bayesian_optimal_estimator_gaussian M theta

/--
Bayesian optimal estimator monotonicity support: fixing all other information,
estimated skill is strictly increasing in the selected reported feature/test
score.
-/
theorem paper_interface_bayesian_optimal_estimator_strictMono_feature
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature) :
    StrictMono (fun value : ℝ =>
      M.posteriorMean (Function.update theta k value)) :=
  paper_bayesian_optimal_estimator_strictMono_feature M theta k

/--
Reporting/taking threshold support: a positive-slope affine Bayesian estimate
clears a threshold exactly above the induced cutoff.
-/
theorem paper_interface_reporting_affine_estimate_threshold_iff_cutoff
    {intercept slope threshold score : ℝ} (hslope : 0 < slope) :
    threshold ≤ intercept + slope * score ↔
      EconCSLib.affineCutoff intercept slope threshold ≤ score :=
  paper_reporting_affine_estimate_threshold_iff_cutoff hslope

/--
Gaussian reporting-threshold support: with all other information fixed,
reporting/taking by Bayesian estimate is equivalent to one score clearing the
induced cutoff.
-/
theorem paper_interface_reporting_gaussian_threshold_iff_cutoff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (base threshold value : ℝ) :
    threshold ≤ M.posteriorMean (Function.update theta k value) ↔
      EconCSLib.affineCutoff
        (M.posteriorMean (Function.update theta k base) -
          M.centeredFamily.signalWeight k * base)
        (M.centeredFamily.signalWeight k) threshold ≤ value :=
  paper_reporting_gaussian_threshold_iff_cutoff M theta k base threshold value

/--
Theorem 3.1 cutoff support: a positive-slope affine comparison induces a
finite lower-cutoff strategy.
-/
theorem paper_interface_lower_cutoff_strategy_of_affine_threshold
    {intercept slope threshold : ℝ} (hslope : 0 < slope) :
    lg21LowerCutoffStrategy
      (fun value : ℝ => threshold ≤ intercept + slope * value) :=
  paper_lower_cutoff_strategy_of_affine_threshold hslope

/--
Theorem 3.1 reporting-threshold support: with all other information fixed, a
Bayesian-optimal reporting decision based on an estimate threshold is a finite
lower-cutoff rule in the reported test score.
-/
theorem paper_interface_theorem3_1_reporting_threshold_of_gaussian_best_response
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (base threshold : ℝ) :
    lg21LowerCutoffStrategy
      (fun value : ℝ =>
        threshold ≤ M.posteriorMean (Function.update theta k value)) :=
  paper_theorem3_1_reporting_threshold_of_gaussian_best_response
    M theta k base threshold

/-- Theorem 3.1 cutoff support: lower-cutoff rules are monotone. -/
theorem paper_interface_monotone_of_lowerCutoffStrategy
    {choose : ℝ → Prop} (hcutoff : lg21LowerCutoffStrategy choose) :
    ∀ {low high : ℝ}, low ≤ high → choose low → choose high :=
  lg21_monotone_of_lowerCutoffStrategy hcutoff

/--
Lemma 4.1 optional-reporting core: a continuous strictly increasing reported
estimate with a non-report estimate strictly between a lower score and the
cutoff has a below-cutoff indifference point and a profitable-deviation
interval.
-/
theorem paper_interface_lemma4_1_reporting_cutoff_has_profitable_deviation_core
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
                noReportEstimate < reportedEstimate profitableScore :=
  paper_lemma4_1_reporting_cutoff_has_profitable_deviation_core
    hcont hmono hscore_lt hlow hcutoff

/--
Lemma 4.1 Gaussian optional-reporting core: the reported Bayesian posterior
score supplies the continuous strictly increasing estimate in the cutoff
deviation argument.
-/
theorem paper_interface_lemma4_1_gaussian_reporting_cutoff_has_profitable_deviation
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
                    (Function.update theta k profitableScore) :=
  paper_lemma4_1_gaussian_reporting_cutoff_has_profitable_deviation
    M theta k hscore_lt hlow hcutoff

/-- Lemma 4.1 no-profitable-withholding condition. -/
abbrev paperNoProfitableWithholdingDeviation
    (reports : ℝ → Prop) (reportedEstimate : ℝ → ℝ)
    (noReportEstimate : ℝ) : Prop :=
  lg21NoProfitableWithholdingDeviation
    reports reportedEstimate noReportEstimate

/--
Lemma 4.1 optional-reporting equilibrium core: a nontrivial lower-cutoff
reporting strategy cannot satisfy no-profitable-withholding-deviation.
-/
theorem paper_interface_lemma4_1_no_nontrivial_reporting_cutoff_of_no_profitable_withholding
    {reports : ℝ → Prop} {reportedEstimate : ℝ → ℝ}
    {scoreLow cutoff noReportEstimate : ℝ}
    (hcutoffStrategy : ∀ score : ℝ, reports score ↔ cutoff ≤ score)
    (hnoDeviation :
      paperNoProfitableWithholdingDeviation
        reports reportedEstimate noReportEstimate)
    (hcont : ContinuousOn reportedEstimate (Set.Icc scoreLow cutoff))
    (hmono : StrictMonoOn reportedEstimate (Set.Icc scoreLow cutoff))
    (hscore_lt : scoreLow < cutoff)
    (hlow : reportedEstimate scoreLow < noReportEstimate)
    (hcutoff : noReportEstimate < reportedEstimate cutoff) :
    False :=
  paper_lemma4_1_no_nontrivial_reporting_cutoff_of_no_profitable_withholding
    hcutoffStrategy hnoDeviation hcont hmono hscore_lt hlow hcutoff

/--
Lemma 4.1 Gaussian optional-reporting equilibrium core: a nontrivial
lower-cutoff reporting strategy cannot satisfy no-profitable-withholding when
the reported estimate is the Gaussian posterior score.
-/
theorem paper_interface_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    {reports : ℝ → Prop} {scoreLow cutoff noReportEstimate : ℝ}
    (hcutoffStrategy : ∀ score : ℝ, reports score ↔ cutoff ≤ score)
    (hnoDeviation :
      paperNoProfitableWithholdingDeviation
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
  paper_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding
    M theta k hcutoffStrategy hnoDeviation hscore_lt hlow hcutoff

/--
Lemma 4.1 Gaussian optional-reporting equilibrium core, source-shaped form:
the positive-slope Gaussian posterior estimate supplies the low-score side of
the cutoff argument automatically.
-/
theorem paper_interface_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding_from_cutoff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    {reports : ℝ → Prop} {cutoff noReportEstimate : ℝ}
    (hcutoffStrategy : ∀ score : ℝ, reports score ↔ cutoff ≤ score)
    (hnoDeviation :
      paperNoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (hcutoff :
      noReportEstimate <
        M.posteriorMean (Function.update theta k cutoff)) :
    False :=
  paper_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding_from_cutoff
    M theta k hcutoffStrategy hnoDeviation hcutoff

/--
Lemma 4.1 optional-reporting endpoint bridge: threshold-if-not-all plus
no-profitable-withholding implies all scores are reported.
-/
theorem paper_interface_lemma4_1_all_report_of_gaussian_cutoff_if_not_all_no_profitable_withholding
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
      paperNoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate) :
    ∀ score : ℝ, reports score :=
  paper_lemma4_1_all_report_of_gaussian_cutoff_if_not_all_no_profitable_withholding
    M theta k hcutoffIfNotAll hnoDeviation

/--
Lemma 4.1 optional-reporting lower-tail support: a no-report estimate computed
from a lower-tail mean score below the reporting cutoff is strictly below the
reported estimate at that cutoff.
-/
theorem paper_interface_lemma4_1_report_cutoff_estimate_lt_of_lower_tail_score
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    {lowerTailScore cutoff noReportEstimate : ℝ}
    (hlower : lowerTailScore < cutoff)
    (hnoReport :
      noReportEstimate =
        M.posteriorMean (Function.update theta k lowerTailScore)) :
    noReportEstimate <
      M.posteriorMean (Function.update theta k cutoff) :=
  paper_lemma4_1_report_cutoff_estimate_lt_of_lower_tail_score
    M theta k hlower hnoReport

/--
Lemma 4.1 optional-reporting endpoint bridge in lower-tail form:
threshold-if-not-all plus the paper's lower-tail no-report estimate identity
and no-profitable-withholding imply all scores are reported.
-/
theorem paper_interface_lemma4_1_all_report_of_gaussian_lower_tail_cutoff_no_profitable_withholding
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
      paperNoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate) :
    ∀ score : ℝ, reports score :=
  paper_lemma4_1_all_report_of_gaussian_lower_tail_cutoff_no_profitable_withholding
    M theta k hcutoffIfNotAll hnoDeviation

/--
Lemma 4.1 optional-reporting endpoint bridge with a shared Gaussian
lower-tail-mean certificate: the no-report estimate is the posterior at the
mean score below the reporting cutoff.
-/
theorem paper_interface_lemma4_1_all_report_of_gaussian_lower_tail_certificate_no_profitable_withholding
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
      paperNoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate) :
    ∀ score : ℝ, reports score :=
  paper_lemma4_1_all_report_of_gaussian_lower_tail_certificate_no_profitable_withholding
    C M theta k scoreLaw hcutoffIfNotAll hnoDeviation

/--
Lemma 4.1 optional-reporting bridge for an explicit Gaussian Bayesian threshold
policy: the threshold premise is the affine cutoff generated by posterior
threshold comparison.
-/
theorem paper_interface_lemma4_1_all_report_of_gaussian_threshold_policy_lower_tail_no_profitable_withholding
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
              (EconCSLib.affineCutoff
                (M.posteriorMean (Function.update theta k base) -
                  M.centeredFamily.signalWeight k * base)
                (M.centeredFamily.signalWeight k) threshold))))
    (hnoDeviation :
      paperNoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate) :
    ∀ score : ℝ, reports score :=
  paper_lemma4_1_all_report_of_gaussian_threshold_policy_lower_tail_no_profitable_withholding
    C M theta k scoreLaw hreports hnoReport hnoDeviation

/-- Lemma 4.1 test-taking support: Gaussian score law conditional on skill. -/
abbrev paperGaussianTestScoreLaw (skill scale : ℝ) (hscale : 0 < scale) :
    GaussianScaleLaw :=
  lg21GaussianTestScoreLaw skill scale hscale

/--
Lemma 4.1 test-taking support: if skill is at least a cutoff, a Gaussian test
score with that skill as mean clears the cutoff with probability at least one
half.
-/
theorem paper_interface_lemma4_1_test_score_pass_prob_ge_half_of_skill_ge_cutoff
    (api : StandardGaussianCDFAPI) {skill cutoff scale : ℝ} (hscale : 0 < scale)
    (hskill : cutoff ≤ skill) :
    (1 / 2 : ℝ) ≤
      api.thresholdPassProb (paperGaussianTestScoreLaw skill scale hscale) cutoff :=
  paper_lemma4_1_test_score_pass_prob_ge_half_of_skill_ge_cutoff
    api hscale hskill

/--
Lemma 4.1 test-taking support, strict form: if skill is strictly above a
cutoff, the Gaussian test score clears the cutoff with probability strictly
above one half.
-/
theorem paper_interface_lemma4_1_test_score_pass_prob_gt_half_of_skill_gt_cutoff
    (api : StandardGaussianCDFAPI) {skill cutoff scale : ℝ} (hscale : 0 < scale)
    (hskill : cutoff < skill) :
    (1 / 2 : ℝ) <
      api.thresholdPassProb (paperGaussianTestScoreLaw skill scale hscale) cutoff :=
  paper_lemma4_1_test_score_pass_prob_gt_half_of_skill_gt_cutoff
    api hscale hskill

/--
Lemma 4.1 reporting-required core: if the no-test posterior skill estimate is
strictly below a proposed taking cutoff, some strictly below-cutoff skill has
strictly better-than-half chance to clear that estimate by taking the test.
-/
theorem paper_interface_lemma4_1_take_test_cutoff_has_profitable_deviation
    (api : StandardGaussianCDFAPI) {qTilde qBar scale : ℝ}
    (hscale : 0 < scale) (hcutoff : qTilde < qBar) :
    ∃ skill : ℝ,
      skill ∈ Set.Ioo qTilde qBar ∧
        (1 / 2 : ℝ) <
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill scale hscale) qTilde :=
  paper_lemma4_1_take_test_cutoff_has_profitable_deviation
    api hscale hcutoff

/-- Lemma 4.1 no-profitable-test-taking condition. -/
abbrev paperNoProfitableTestTakingDeviation
    (takes : ℝ → Prop) (testBenefitProb : ℝ → ℝ) : Prop :=
  lg21NoProfitableTestTakingDeviation takes testBenefitProb

/--
Lemma 4.1 reporting-required equilibrium core: a nontrivial lower-cutoff
test-taking strategy cannot satisfy no-profitable-test-taking-deviation when
the no-test estimate is strictly below the taking cutoff.
-/
theorem paper_interface_lemma4_1_no_nontrivial_take_test_cutoff_of_no_profitable_deviation
    (api : StandardGaussianCDFAPI) {takes : ℝ → Prop} {qTilde qBar scale : ℝ}
    (hscale : 0 < scale)
    (hcutoffStrategy : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hnoDeviation :
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill scale hscale) qTilde))
    (hcutoff : qTilde < qBar) :
    False :=
  paper_lemma4_1_no_nontrivial_take_test_cutoff_of_no_profitable_deviation
    api hscale hcutoffStrategy hnoDeviation hcutoff

/--
Lemma 4.1 reporting-required endpoint bridge: threshold-if-not-all plus
no-profitable-test-taking implies all access students take the test.
-/
theorem paper_interface_lemma4_1_all_take_of_cutoff_if_not_all_no_profitable_test_taking
    (api : StandardGaussianCDFAPI) {takes : ℝ → Prop} {qTilde scale : ℝ}
    (hscale : 0 < scale)
    (hcutoffIfNotAll :
      ¬ (∀ skill : ℝ, takes skill) →
        ∃ qBar : ℝ,
          (∀ skill : ℝ, takes skill ↔ qBar ≤ skill) ∧ qTilde < qBar)
    (hnoDeviation :
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill scale hscale) qTilde)) :
    ∀ skill : ℝ, takes skill :=
  paper_lemma4_1_all_take_of_cutoff_if_not_all_no_profitable_test_taking
    api hscale hcutoffIfNotAll hnoDeviation

/--
Lemma 4.1 reporting-required endpoint bridge in lower-tail form:
threshold-if-not-all plus the paper's lower-tail no-test estimate identity and
no-profitable-test-taking imply all access students take the test.
-/
theorem paper_interface_lemma4_1_all_take_of_lower_tail_cutoff_no_profitable_test_taking
    (api : StandardGaussianCDFAPI) {takes : ℝ → Prop} {qTilde scale : ℝ}
    (hscale : 0 < scale)
    (hcutoffIfNotAll :
      ¬ (∀ skill : ℝ, takes skill) →
        ∃ qBar lowerTailSkill : ℝ,
          (∀ skill : ℝ, takes skill ↔ qBar ≤ skill) ∧
            lowerTailSkill < qBar ∧ qTilde = lowerTailSkill)
    (hnoDeviation :
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill scale hscale) qTilde)) :
    ∀ skill : ℝ, takes skill :=
  paper_lemma4_1_all_take_of_lower_tail_cutoff_no_profitable_test_taking
    api hscale hcutoffIfNotAll hnoDeviation

/--
Lemma 4.1 reporting-required endpoint bridge with a shared Gaussian
lower-tail-mean certificate: the no-test estimate is the mean skill below the
taking cutoff.
-/
theorem paper_interface_lemma4_1_all_take_of_gaussian_lower_tail_certificate_no_profitable_test_taking
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
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill scale hscale) qTilde)) :
    ∀ skill : ℝ, takes skill :=
  paper_lemma4_1_all_take_of_gaussian_lower_tail_certificate_no_profitable_test_taking
    C api skillLaw hscale hcutoffIfNotAll hnoDeviation

/--
Lemma 4.1 report-required bridge for an explicit lower-threshold taking rule:
if the no-test estimate is the lower-tail skill mean at that threshold, then
no-profitable-test-taking forces every access student to take.
-/
theorem paper_interface_lemma4_1_all_take_of_explicit_lower_tail_threshold_no_profitable_test_taking
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI) (skillLaw : GaussianScaleLaw)
    {takes : ℝ → Prop} {qTilde qBar scale : ℝ}
    (hscale : 0 < scale)
    (htakes : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hqTilde : qTilde = C.lowerTailMean skillLaw qBar)
    (hnoDeviation :
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill scale hscale) qTilde)) :
    ∀ skill : ℝ, takes skill :=
  paper_lemma4_1_all_take_of_explicit_lower_tail_threshold_no_profitable_test_taking
    C api skillLaw hscale htakes hqTilde hnoDeviation

/--
Lemma 4.1 lower-tail strategy-proofness bridge: the optional-reporting and
report-required lower-tail threshold arguments together imply all relevant
observed-access cohorts report and take.
-/
theorem paper_interface_lemma4_1_strategy_proofness_of_lower_tail_thresholds
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
      paperNoProfitableWithholdingDeviation
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
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill testScale htestScale) qTilde)) :
    (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
  paper_lemma4_1_strategy_proofness_of_lower_tail_thresholds
    C api M theta k scoreLaw skillLaw htestScale
    hreportCutoffIfNotAll hreportNoDeviation
    htakeCutoffIfNotAll htakeNoDeviation

/--
Lemma 4.1 route with the reporting cutoff discharged by an explicit Gaussian
Bayesian threshold policy, while the taking side remains in the lower-tail
cutoff form.
-/
theorem paper_interface_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_lower_tail_taking
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
              (EconCSLib.affineCutoff
                (M.posteriorMean (Function.update theta k base) -
                  M.centeredFamily.signalWeight k * base)
                (M.centeredFamily.signalWeight k) threshold))))
    (hreportNoDeviation :
      paperNoProfitableWithholdingDeviation
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
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill testScale htestScale) qTilde)) :
    (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
  paper_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_lower_tail_taking
    C api M theta k scoreLaw skillLaw htestScale hreports hnoReport
    hreportNoDeviation htakeCutoffIfNotAll htakeNoDeviation

/--
Lemma 4.1 route with both threshold premises explicit: Gaussian Bayesian
threshold reporting supplies the reporting cutoff, and an explicit lower-tail
taking threshold supplies the report-required side.
-/
theorem paper_interface_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_explicit_taking_threshold
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
              (EconCSLib.affineCutoff
                (M.posteriorMean (Function.update theta k base) -
                  M.centeredFamily.signalWeight k * base)
                (M.centeredFamily.signalWeight k) threshold))))
    (hreportNoDeviation :
      paperNoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (htakes : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hqTilde : qTilde = C.lowerTailMean skillLaw qBar)
    (htakeNoDeviation :
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill testScale htestScale) qTilde)) :
    (∀ score : ℝ, reports score) ∧ (∀ skill : ℝ, takes skill) :=
  paper_lemma4_1_strategy_proofness_of_gaussian_reporting_threshold_and_explicit_taking_threshold
    C api M theta k scoreLaw skillLaw htestScale hreports hnoReport
    hreportNoDeviation htakes hqTilde htakeNoDeviation

/--
Fixed-base posterior-score law: all non-test information is fixed and the
Bayesian estimate is a positive-slope affine function of the optional test
score.
-/
abbrev paperOneTestPosteriorScoreLaw
    (intercept slope : ℝ) (hslope : 0 < slope)
    (skill testScale : ℝ) (htestScale : 0 < testScale) :
    GaussianScaleLaw :=
  lg21OneTestPosteriorScoreLaw
    intercept slope hslope skill testScale htestScale

/--
Proposition 4.2 fixed-base Gaussian support: the one-random-test posterior
score law has strictly larger mean for strictly larger latent skill.
-/
theorem paper_interface_one_test_posterior_score_law_mean_lt_of_skill_lt
    {intercept slope skillLow skillHigh testScale : ℝ}
    (hslope : 0 < slope) (htestScale : 0 < testScale)
    (hskill : skillLow < skillHigh) :
    (paperOneTestPosteriorScoreLaw
      intercept slope hslope skillLow testScale htestScale).mean <
      (paperOneTestPosteriorScoreLaw
        intercept slope hslope skillHigh testScale htestScale).mean :=
  paper_one_test_posterior_score_law_mean_lt_of_skill_lt
    hslope htestScale hskill

/--
Propositions 4.2--4.3 Gaussian-law support: distinct means imply distinct
estimate laws.
-/
theorem paper_interface_gaussian_estimate_laws_differ_of_mean_lt
    {Llow Lhigh : GaussianVarianceLaw} (hmean : Llow.mean < Lhigh.mean) :
    Llow ≠ Lhigh :=
  paper_gaussian_estimate_laws_differ_of_mean_lt hmean

/-- Proposition 4.3 Gaussian-law support: distinct variances imply distinct laws. -/
theorem paper_interface_gaussian_estimate_laws_differ_of_variance_lt
    {Llow Lhigh : GaussianVarianceLaw} (hvar : Llow.variance < Lhigh.variance) :
    Llow ≠ Lhigh :=
  paper_gaussian_estimate_laws_differ_of_variance_lt hvar

/--
Propositions 4.2--4.3 Gaussian location-scale support: distinct means imply
distinct estimate laws.
-/
theorem paper_interface_gaussian_scale_laws_differ_of_mean_lt
    {Llow Lhigh : GaussianScaleLaw} (hmean : Llow.mean < Lhigh.mean) :
    Llow ≠ Lhigh :=
  paper_gaussian_scale_laws_differ_of_mean_lt hmean

/--
Proposition 4.3 Gaussian location-scale support: distinct scales imply
distinct estimate laws.
-/
theorem paper_interface_gaussian_scale_laws_differ_of_scale_lt
    {Llow Lhigh : GaussianScaleLaw} (hscale : Llow.scale < Lhigh.scale) :
    Llow ≠ Lhigh :=
  paper_gaussian_scale_laws_differ_of_scale_lt hscale

/-- Paper-local law object for deterministic or Gaussian estimated-skill laws. -/
abbrev paperEstimateLaw : Type :=
  LG21EstimateLaw

/-- Point laws and Gaussian laws are distinct in the paper-local law object. -/
theorem paper_interface_estimate_law_point_ne_gaussian
    (estimate : ℝ) (law : GaussianScaleLaw) :
    LG21EstimateLaw.point estimate ≠ LG21EstimateLaw.gaussian law :=
  LG21EstimateLaw.point_ne_gaussian estimate law

/-- Gaussian laws with strictly ordered means are distinct paper-local laws. -/
theorem paper_interface_estimate_law_gaussian_ne_of_mean_lt
    {Llow Lhigh : GaussianScaleLaw} (hmean : Llow.mean < Lhigh.mean) :
    LG21EstimateLaw.gaussian Llow ≠ LG21EstimateLaw.gaussian Lhigh :=
  LG21EstimateLaw.gaussian_ne_of_mean_lt hmean

/--
Propositions 4.2--4.3 precision support: a strict total-precision gap gives a
strict gap in marginal Bayesian-estimate variance.
-/
theorem paper_interface_gaussian_estimate_variance_lt_of_total_precision_lt
    {Feature : Type*} [Fintype Feature]
    {Mlow Mhigh : GaussianOffsetSignalFamily Feature}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      (∑ k : Feature, Mlow.centeredFamily.signalPrecision k) <
        ∑ k : Feature, Mhigh.centeredFamily.signalPrecision k) :
    Mlow.posteriorMeanVariance < Mhigh.posteriorMeanVariance :=
  paper_gaussian_estimate_variance_lt_of_total_precision_lt hpriorVar hsum

/--
Propositions 4.2--4.3 precision support: a strict total-precision gap gives a
strict gap in Gaussian Bayesian-estimate scale.
-/
theorem paper_interface_gaussian_estimate_scale_lt_of_total_precision_lt
    {Feature : Type*} [Fintype Feature] [Nonempty Feature]
    {Mlow Mhigh : GaussianOffsetSignalFamily Feature}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      (∑ k : Feature, Mlow.centeredFamily.signalPrecision k) <
        ∑ k : Feature, Mhigh.centeredFamily.signalPrecision k) :
    (Mlow.posteriorMeanScaleLaw).scale <
      (Mhigh.posteriorMeanScaleLaw).scale :=
  paper_gaussian_estimate_scale_lt_of_total_precision_lt hpriorVar hsum

/--
Propositions 4.2--4.3 precision support across different observed-feature
sets: a strict signal-precision gap gives a strict posterior-score scale gap.
-/
theorem paper_interface_gaussian_estimate_scale_lt_of_signalPrecisionSum_lt
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
  paper_gaussian_estimate_scale_lt_of_signalPrecisionSum_lt hpriorVar hsum

/--
Propositions 4.2--4.3 precision support: a strict total-precision gap produces
different Bayesian-estimate Gaussian laws.
-/
theorem paper_interface_gaussian_estimate_laws_differ_of_total_precision_lt
    {Feature : Type*} [Fintype Feature] [Nonempty Feature]
    {Mlow Mhigh : GaussianOffsetSignalFamily Feature}
    (hpriorVar : Mlow.priorVar = Mhigh.priorVar)
    (hsum :
      (∑ k : Feature, Mlow.centeredFamily.signalPrecision k) <
        ∑ k : Feature, Mhigh.centeredFamily.signalPrecision k) :
    Mlow.posteriorMeanLaw ≠ Mhigh.posteriorMeanLaw :=
  paper_gaussian_estimate_laws_differ_of_total_precision_lt hpriorVar hsum

/--
Proposition 4.3 tail-comparison support: above the common mean, the larger-scale
Gaussian estimate law has weakly larger upper-tail probability.
-/
theorem paper_interface_gaussian_upper_tail_le_of_same_mean_scale_le_above_mean
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale ≤ Llarge.scale)
    {threshold : ℝ} (hthreshold : Lsmall.mean ≤ threshold) :
    api.thresholdPassProb Lsmall threshold ≤
      api.thresholdPassProb Llarge threshold :=
  paper_gaussian_upper_tail_le_of_same_mean_scale_le_above_mean
    api hmean hscale hthreshold

/--
Proposition 4.3 strict tail-comparison support: strictly above the common mean,
the strictly larger-scale Gaussian estimate law has strictly larger upper-tail
probability.
-/
theorem paper_interface_gaussian_upper_tail_lt_of_same_mean_scale_lt_above_mean
    (api : StandardGaussianCDFAPI)
    {Lsmall Llarge : GaussianScaleLaw}
    (hmean : Lsmall.mean = Llarge.mean)
    (hscale : Lsmall.scale < Llarge.scale)
    {threshold : ℝ} (hthreshold : Lsmall.mean < threshold) :
    api.thresholdPassProb Lsmall threshold <
      api.thresholdPassProb Llarge threshold :=
  paper_gaussian_upper_tail_lt_of_same_mean_scale_lt_above_mean
    api hmean hscale hthreshold

/--
Proposition 4.2 Gaussian support: the conditional posterior-score law has
strictly larger mean for strictly larger latent skill.
-/
theorem paper_interface_conditional_posteriorMeanScaleLaw_mean_lt_of_skill_lt
    {Feature : Type*} [Fintype Feature] [Nonempty Feature]
    (M : GaussianOffsetSignalFamily Feature) {qLow qHigh : ℝ}
    (hq : qLow < qHigh) :
    (M.conditionalPosteriorMeanScaleLaw qLow).mean <
      (M.conditionalPosteriorMeanScaleLaw qHigh).mean :=
  paper_conditional_posteriorMeanScaleLaw_mean_lt_of_skill_lt M hq

/--
Theorem 3.1: strategic withholding and failure of latent-skill, observable,
and demographic fairness.

Current Lean status: conditional on the strategic withholding certificate.
-/
theorem paper_interface_theorem3_1_strategic_withholding
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (C : LG21StrategicWithholdingCertificate S) :
    C.some_access_students_do_not_report ∧
      C.threshold_reporting ∧ C.threshold_taking ∧
        ¬ lg21SourceLatentSkillFair S ∧
          ¬ lg21SourceObservablyFair S ∧
            ¬ lg21SourceDemographicallyFair S :=
  paper_theorem3_1_strategic_withholding_of_certificate C

/--
Theorem 3.2: latent-skill or observable fairness implies test-blankness.

Current Lean status: conditional on the fairness-impossibility certificate.
-/
theorem paper_interface_theorem3_2_fairness_impossibility
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (C : LG21FairnessImpossibilityCertificate S) :
    lg21SourceLatentSkillFair S ∨ lg21SourceObservablyFair S →
      lg21SourceTestBlank S :=
  paper_theorem3_2_fairness_impossibility_of_certificate C

/--
Theorem 3.2 contrapositive core: under the source implication, a concrete
test-relevance witness rules out latent-skill or observable fairness.
-/
theorem paper_interface_theorem3_2_not_latent_or_observable_fair_of_test_relevance_witness
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (C : LG21FairnessImpossibilityCertificate S)
    (e : S.Equilibrium) (base : Base) (test : Test)
    (hne : S.baseOnlyEstimate e base ≠ S.fullFeatureEstimate e base test) :
    ¬ (lg21SourceLatentSkillFair S ∨ lg21SourceObservablyFair S) :=
  paper_theorem3_2_not_latent_or_observable_fair_of_test_relevance_witness
    C e base test hne

/--
Theorem 3.2 continuous-law endpoint: latent-skill or observable fairness
implies test-blankness over arbitrary law objects.
-/
theorem paper_interface_theorem3_2_law_fairness_impossibility
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (C : LG21LawFairnessImpossibilityCertificate S) :
    lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
      lg21SourceLawTestBlank S :=
  paper_theorem3_2_law_fairness_impossibility_of_certificate C

/--
Theorem 3.2 continuous-law contrapositive core: under the source implication, a
test-relevance law witness rules out latent-skill or observable fairness.
-/
theorem paper_interface_theorem3_2_not_law_latent_or_observable_fair_of_test_relevance_witness
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (C : LG21LawFairnessImpossibilityCertificate S)
    (e : S.Equilibrium) (base : Base) (test : Test)
    (hne : S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test) :
    ¬ (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :=
  paper_theorem3_2_not_law_latent_or_observable_fair_of_test_relevance_witness
    C e base test hne

/--
Lemma 4.1: when access is observed, all access students take and report the
test.

Current Lean status: conditional on the observed-access Bayesian threshold
certificate.
-/
theorem paper_interface_lemma4_1_strategy_proofness
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (C : LG21ObservedAccessStrategyProofCertificate S) :
    C.all_access_take_and_report :=
  paper_lemma4_1_strategy_proofness_of_certificate C

/--
Proposition 4.2: Bayesian optimality on access students is not latent-skill
fair.

Current Lean status: conditional on the Gaussian distribution comparison
certificate.
-/
theorem paper_interface_proposition4_2_not_latent_skill_fair
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (C : LG21NotLatentFairCertificate S) :
    ¬ lg21SourceLatentSkillFair S :=
  paper_proposition4_2_not_latent_skill_fair_of_certificate C

/--
Proposition 4.2 logical core: one latent-skill witness with different access
and no-access estimate laws proves latent-skill fairness fails.
-/
theorem paper_interface_proposition4_2_not_latent_skill_fair_of_witness
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (e : S.Equilibrium) (q : Skill) (base : Base)
    (hne : S.latentAccessEstimate e q base ≠
      S.latentNoAccessEstimate e q base) :
    ¬ lg21SourceLatentSkillFair S :=
  paper_proposition4_2_not_latent_skill_fair_of_witness e q base hne

/--
Proposition 4.2 four-group core: if no-access estimate laws agree for two
skills at the same base profile while access estimate laws differ, latent-skill
fairness fails.
-/
theorem paper_interface_proposition4_2_not_latent_skill_fair_of_four_group_core
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
  paper_proposition4_2_not_latent_skill_fair_of_four_group_core
    e qHigh qLow base hNoAccess hAccess

/--
Proposition 4.2 continuous-law four-group core: no-access laws agree for two
skills while access laws differ, so latent-skill fairness fails.
-/
theorem paper_interface_proposition4_2_not_law_latent_skill_fair_of_four_group_core
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
  paper_proposition4_2_not_law_latent_skill_fair_of_four_group_core
    e qHigh qLow base hNoAccess hAccess

/--
Proposition 4.2 Gaussian-law core: a strict access-side Gaussian mean gap
supplies the law difference needed by the four-group proof.
-/
theorem paper_interface_proposition4_2_not_law_latent_skill_fair_of_gaussian_mean_gap
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
    ¬ lg21SourceLawLatentSkillFair S :=
  paper_proposition4_2_not_law_latent_skill_fair_of_gaussian_mean_gap
    e qHigh qLow base hNoAccess hAccessHigh hAccessLow hmean

/--
Proposition 4.2 posterior-law instantiation: conditional Gaussian posterior
laws for two ordered latent skills supply the access-side law difference in
the four-group proof.
-/
theorem paper_interface_proposition4_2_not_law_latent_skill_fair_of_conditional_posterior_mean_gap
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
    ¬ lg21SourceLawLatentSkillFair S :=
  paper_proposition4_2_not_law_latent_skill_fair_of_conditional_posterior_mean_gap
    M e qHigh qLow base hNoAccess hAccessHigh hAccessLow hskill

/--
Proposition 4.2 source-shaped law instantiation: no-access groups share the
same observed information, while access groups receive conditional Gaussian
posterior-score laws with different means.
-/
theorem paper_interface_proposition4_2_not_estimate_law_latent_skill_fair_of_conditional_posterior_mean_gap
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
    ¬ lg21SourceLawLatentSkillFair S :=
  paper_proposition4_2_not_estimate_law_latent_skill_fair_of_conditional_posterior_mean_gap
    M e qHigh qLow base hNoAccess hAccessHigh hAccessLow hskill

/--
Proposition 4.2 fixed-base source instantiation: the access-side law is the
affine image of one random optional test score, so two ordered latent skills
give different Gaussian estimate laws.
-/
theorem paper_interface_proposition4_2_not_estimate_law_latent_skill_fair_of_one_test_posterior_law
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
          (paperOneTestPosteriorScoreLaw
            intercept slope hslope skillHigh testScale htestScale))
    (hAccessLow :
      S.latentAccessLaw e qLow base =
        LG21EstimateLaw.gaussian
          (paperOneTestPosteriorScoreLaw
            intercept slope hslope skillLow testScale htestScale))
    (hskill : skillLow < skillHigh) :
    ¬ lg21SourceLawLatentSkillFair S :=
  paper_proposition4_2_not_estimate_law_latent_skill_fair_of_one_test_posterior_law
    e qHigh qLow base hslope htestScale hNoAccess hAccessHigh hAccessLow
    hskill

/--
Proposition 4.2 source-route wrapper: Lemma 4.1 lower-tail strategy-proofness
first gives all-report/all-take, then the fixed-base one-test posterior law
gives the latent-skill fairness contradiction.
-/
theorem paper_interface_proposition4_2_not_latent_skill_fair_of_lemma4_1_lower_tail_and_one_test_posterior_law
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
      paperNoProfitableWithholdingDeviation
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
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill testScale htestScale) qTilde))
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccessHigh :
      S.latentAccessLaw e qHigh base =
        LG21EstimateLaw.gaussian
          (paperOneTestPosteriorScoreLaw
            intercept slope hslope skillHigh testScale htestScale))
    (hAccessLow :
      S.latentAccessLaw e qLow base =
        LG21EstimateLaw.gaussian
          (paperOneTestPosteriorScoreLaw
            intercept slope hslope skillLow testScale htestScale))
    (hskill : skillLow < skillHigh) :
    (∀ score : ℝ, reports score) ∧
      (∀ skill : ℝ, takes skill) ∧
        ¬ lg21SourceLawLatentSkillFair S :=
  paper_proposition4_2_not_latent_skill_fair_of_lemma4_1_lower_tail_and_one_test_posterior_law
    C api M theta k scoreLaw skillLaw e qHigh qLow base hslope htestScale
    hreportCutoffIfNotAll hreportNoDeviation
    htakeCutoffIfNotAll htakeNoDeviation
    hNoAccess hAccessHigh hAccessLow hskill

/--
Proposition 4.2 source-route wrapper with explicit Lemma 4.1 threshold
policies: Gaussian Bayesian reporting and lower-tail taking thresholds first
give all-report/all-take, then the fixed-base one-test posterior law gives the
latent-skill fairness contradiction.
-/
theorem paper_interface_proposition4_2_not_latent_skill_fair_of_explicit_thresholds_and_one_test_posterior_law
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
              (EconCSLib.affineCutoff
                (M.posteriorMean (Function.update theta k reportingBase) -
                  M.centeredFamily.signalWeight k * reportingBase)
                (M.centeredFamily.signalWeight k) threshold))))
    (hreportNoDeviation :
      paperNoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          M.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (htakes : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hqTilde : qTilde = C.lowerTailMean skillLaw qBar)
    (htakeNoDeviation :
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill testScale htestScale) qTilde))
    (hNoAccess :
      S.latentNoAccessLaw e qHigh base =
        S.latentNoAccessLaw e qLow base)
    (hAccessHigh :
      S.latentAccessLaw e qHigh base =
        LG21EstimateLaw.gaussian
          (paperOneTestPosteriorScoreLaw
            intercept slope hslope skillHigh testScale htestScale))
    (hAccessLow :
      S.latentAccessLaw e qLow base =
        LG21EstimateLaw.gaussian
          (paperOneTestPosteriorScoreLaw
            intercept slope hslope skillLow testScale htestScale))
    (hskill : skillLow < skillHigh) :
    (∀ score : ℝ, reports score) ∧
      (∀ skill : ℝ, takes skill) ∧
        ¬ lg21SourceLawLatentSkillFair S :=
  paper_proposition4_2_not_latent_skill_fair_of_explicit_thresholds_and_one_test_posterior_law
    C api M theta k scoreLaw skillLaw e qHigh qLow base hslope htestScale
    hreports hnoReport hreportNoDeviation htakes hqTilde htakeNoDeviation
    hNoAccess hAccessHigh hAccessLow hskill

/--
Proposition 4.3: the full Bayesian optimal policy is not observable or
demographic fair.

Current Lean status: conditional on the posterior distribution comparison
certificate.
-/
theorem paper_interface_proposition4_3_not_observable_or_demographic_fair
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (C : LG21NotObservableOrDemographicFairCertificate S) :
    ¬ lg21SourceObservablyFair S ∧ ¬ lg21SourceDemographicallyFair S :=
  paper_proposition4_3_not_observable_or_demographic_fair_of_certificate C

/--
Proposition 4.3 logical core: observable and demographic law-difference
witnesses prove both fairness definitions fail.
-/
theorem paper_interface_proposition4_3_not_observable_or_demographic_fair_of_witnesses
    {Skill Base Test Estimate : Type*}
    {S : LG21SourcePolicySurface Skill Base Test Estimate}
    (eObs : S.Equilibrium) (base : Base)
    (hobs : S.observableAccessEstimate eObs base ≠
      S.observableNoAccessEstimate eObs base)
    (eDemo : S.Equilibrium)
    (hdemo : S.demographicAccessEstimate eDemo ≠
      S.demographicNoAccessEstimate eDemo) :
    ¬ lg21SourceObservablyFair S ∧ ¬ lg21SourceDemographicallyFair S :=
  paper_proposition4_3_not_observable_or_demographic_fair_of_witnesses
    eObs base hobs eDemo hdemo

/--
Proposition 4.3 continuous-law core: observable and demographic law-difference
witnesses prove both fairness definitions fail.
-/
theorem paper_interface_proposition4_3_not_law_observable_or_demographic_fair_of_witnesses
    {Skill Base Test Law : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (eObs : S.Equilibrium) (base : Base)
    (hobs : S.observableAccessLaw eObs base ≠ S.observableNoAccessLaw eObs base)
    (eDemo : S.Equilibrium)
    (hdemo : S.demographicAccessLaw eDemo ≠ S.demographicNoAccessLaw eDemo) :
    ¬ lg21SourceLawObservablyFair S ∧ ¬ lg21SourceLawDemographicallyFair S :=
  paper_proposition4_3_not_law_observable_or_demographic_fair_of_witnesses
    eObs base hobs eDemo hdemo

/--
Proposition 4.3 Gaussian observable-law core: a strict variance gap proves
observable fairness fails.
-/
theorem paper_interface_proposition4_3_not_law_observable_fair_of_gaussian_variance_gap
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianVarianceLaw}
    (e : S.Equilibrium) (base : Base)
    {Llow Lhigh : GaussianVarianceLaw}
    (hAccess : S.observableAccessLaw e base = Lhigh)
    (hNoAccess : S.observableNoAccessLaw e base = Llow)
    (hvar : Llow.variance < Lhigh.variance) :
    ¬ lg21SourceLawObservablyFair S :=
  paper_proposition4_3_not_law_observable_fair_of_gaussian_variance_gap
    e base hAccess hNoAccess hvar

/--
Proposition 4.3 Gaussian demographic-law core: a strict variance gap proves
demographic fairness fails.
-/
theorem paper_interface_proposition4_3_not_law_demographic_fair_of_gaussian_variance_gap
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianVarianceLaw}
    (e : S.Equilibrium)
    {Llow Lhigh : GaussianVarianceLaw}
    (hAccess : S.demographicAccessLaw e = Lhigh)
    (hNoAccess : S.demographicNoAccessLaw e = Llow)
    (hvar : Llow.variance < Lhigh.variance) :
    ¬ lg21SourceLawDemographicallyFair S :=
  paper_proposition4_3_not_law_demographic_fair_of_gaussian_variance_gap
    e hAccess hNoAccess hvar

/--
Proposition 4.3 Gaussian observable-law core for location-scale laws: a strict
scale gap proves observable fairness fails.
-/
theorem paper_interface_proposition4_3_not_law_observable_fair_of_gaussian_scale_gap
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianScaleLaw}
    (e : S.Equilibrium) (base : Base)
    {Lsmall Llarge : GaussianScaleLaw}
    (hAccess : S.observableAccessLaw e base = Llarge)
    (hNoAccess : S.observableNoAccessLaw e base = Lsmall)
    (hscale : Lsmall.scale < Llarge.scale) :
    ¬ lg21SourceLawObservablyFair S :=
  paper_proposition4_3_not_law_observable_fair_of_gaussian_scale_gap
    e base hAccess hNoAccess hscale

/--
Proposition 4.3 Gaussian demographic-law core for location-scale laws: a strict
scale gap proves demographic fairness fails.
-/
theorem paper_interface_proposition4_3_not_law_demographic_fair_of_gaussian_scale_gap
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test GaussianScaleLaw}
    (e : S.Equilibrium)
    {Lsmall Llarge : GaussianScaleLaw}
    (hAccess : S.demographicAccessLaw e = Llarge)
    (hNoAccess : S.demographicNoAccessLaw e = Lsmall)
    (hscale : Lsmall.scale < Llarge.scale) :
    ¬ lg21SourceLawDemographicallyFair S :=
  paper_proposition4_3_not_law_demographic_fair_of_gaussian_scale_gap
    e hAccess hNoAccess hscale

/--
Proposition 4.3 source-shaped observable-law core: an access-side Gaussian
posterior-score law cannot equal a no-access point estimate law.
-/
theorem paper_interface_proposition4_3_not_estimate_law_observable_fair_of_access_gaussian_no_access_point
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test LG21EstimateLaw}
    (e : S.Equilibrium) (base : Base)
    (estimate : ℝ) (Laccess : GaussianScaleLaw)
    (hAccess :
      S.observableAccessLaw e base = LG21EstimateLaw.gaussian Laccess)
    (hNoAccess :
      S.observableNoAccessLaw e base = LG21EstimateLaw.point estimate) :
    ¬ lg21SourceLawObservablyFair S :=
  paper_proposition4_3_not_estimate_law_observable_fair_of_access_gaussian_no_access_point
    e base estimate Laccess hAccess hNoAccess

/--
Proposition 4.3 fixed-base source instantiation: the access-side law is the
one-random-test posterior law and the no-access law is a point estimate.
-/
theorem paper_interface_proposition4_3_not_estimate_law_observable_fair_of_one_test_posterior_law_vs_point
    {Skill Base Test : Type*}
    {S : LG21SourceLawPolicySurface Skill Base Test LG21EstimateLaw}
    (e : S.Equilibrium) (base : Base)
    {intercept slope conditionalTestMean testScale noAccessEstimate : ℝ}
    (hslope : 0 < slope) (htestScale : 0 < testScale)
    (hAccess :
      S.observableAccessLaw e base =
        LG21EstimateLaw.gaussian
          (paperOneTestPosteriorScoreLaw
            intercept slope hslope conditionalTestMean testScale htestScale))
    (hNoAccess :
      S.observableNoAccessLaw e base =
        LG21EstimateLaw.point noAccessEstimate) :
    ¬ lg21SourceLawObservablyFair S :=
  paper_proposition4_3_not_estimate_law_observable_fair_of_one_test_posterior_law_vs_point
    e base hslope htestScale hAccess hNoAccess

/--
Proposition 4.3 posterior-law observable-fairness instantiation: a strict
signal-precision gap between no-access and access posterior-score laws rules
out observable fairness.
-/
theorem paper_interface_proposition4_3_not_law_observable_fair_of_posterior_precision_gap
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
  paper_proposition4_3_not_law_observable_fair_of_posterior_precision_gap
    e base hAccess hNoAccess hpriorVar hsum

/--
Proposition 4.3 posterior-law demographic-fairness instantiation: a strict
signal-precision gap between no-access and access posterior-score laws rules
out demographic fairness.
-/
theorem paper_interface_proposition4_3_not_law_demographic_fair_of_posterior_precision_gap
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
  paper_proposition4_3_not_law_demographic_fair_of_posterior_precision_gap
    e hAccess hNoAccess hpriorVar hsum

/--
Proposition 4.3 precision support: adding one extra Gaussian signal strictly
increases the Bayesian posterior-mean law's scale.
-/
theorem paper_interface_gaussian_estimate_scale_lt_of_extra_signal
    {Feature : Type*} [Fintype Feature] [Nonempty Feature]
    (M : GaussianOffsetSignalFamily Feature)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    (M.posteriorMeanScaleLaw).scale <
      ((M.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar).posteriorMeanScaleLaw).scale :=
  paper_gaussian_estimate_scale_lt_of_extra_signal
    M extraNoiseMean extraNoiseVar hextraNoiseVar

/--
Proposition 4.3 source-route wrapper: Lemma 4.1 first supplies
all-report/all-take, and the posterior-precision gap then rules out observable
and demographic fairness.
-/
theorem paper_interface_proposition4_3_not_law_observable_or_demographic_fair_of_lemma4_1_lower_tail_and_posterior_precision_gap
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
      paperNoProfitableWithholdingDeviation
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
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill testScale htestScale) qTilde))
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
          ¬ lg21SourceLawDemographicallyFair S :=
  paper_proposition4_3_not_law_observable_or_demographic_fair_of_lemma4_1_lower_tail_and_posterior_precision_gap
    C api M theta k scoreLaw skillLaw htestScale
    hreportCutoffIfNotAll hreportNoDeviation
    htakeCutoffIfNotAll htakeNoDeviation
    eObs base eDemo hAccessObs hNoAccessObs hAccessDemo hNoAccessDemo
    hpriorVar hsum

/--
Proposition 4.3 source-route wrapper for the paper's extra-test-signal case:
Lemma 4.1 gives all-report/all-take, and the added Gaussian test signal gives
the posterior-precision gap.
-/
theorem paper_interface_proposition4_3_not_law_observable_or_demographic_fair_of_lemma4_1_lower_tail_and_extra_signal
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
      paperNoProfitableWithholdingDeviation
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
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill testScale htestScale) qTilde))
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
  paper_proposition4_3_not_law_observable_or_demographic_fair_of_lemma4_1_lower_tail_and_extra_signal
    C api Mstrategy theta k scoreLaw skillLaw htestScale
    hreportCutoffIfNotAll hreportNoDeviation
    htakeCutoffIfNotAll htakeNoDeviation
    eObs base eDemo Mbase extraNoiseMean extraNoiseVar hextraNoiseVar
    hAccessObs hNoAccessObs hAccessDemo hNoAccessDemo

/--
Proposition 4.3 source-route wrapper with explicit Lemma 4.1 thresholds and
the paper's concrete extra-test-signal posterior-precision gap.
-/
theorem paper_interface_proposition4_3_not_law_observable_or_demographic_fair_of_explicit_thresholds_and_extra_signal
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
              (EconCSLib.affineCutoff
                (Mstrategy.posteriorMean (Function.update theta k reportingBase) -
                  Mstrategy.centeredFamily.signalWeight k * reportingBase)
                (Mstrategy.centeredFamily.signalWeight k) threshold))))
    (hreportNoDeviation :
      paperNoProfitableWithholdingDeviation
        reports
        (fun value : ℝ =>
          Mstrategy.posteriorMean (Function.update theta k value))
        noReportEstimate)
    (htakes : ∀ skill : ℝ, takes skill ↔ qBar ≤ skill)
    (hqTilde : qTilde = C.lowerTailMean skillLaw qBar)
    (htakeNoDeviation :
      paperNoProfitableTestTakingDeviation takes
        (fun skill : ℝ =>
          api.thresholdPassProb
            (paperGaussianTestScoreLaw skill testScale htestScale) qTilde))
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
  paper_proposition4_3_not_law_observable_or_demographic_fair_of_explicit_thresholds_and_extra_signal
    C api Mstrategy theta k scoreLaw skillLaw htestScale
    hreports hnoReport hreportNoDeviation htakes hqTilde htakeNoDeviation
    eObs base eDemo Mbase extraNoiseMean extraNoiseVar hextraNoiseVar
    hAccessObs hNoAccessObs hAccessDemo hNoAccessDemo

/--
Definition 6: the re-sampling policy uses the conditional law of the optional
test score given the non-test profile.
-/
theorem paper_interface_definition6_resampling_policy_observable_kernel
    {ΩBase ΩTest Estimate : Type*} [Fintype ΩBase] [DecidableEq ΩBase]
    (e : LG21ResamplingExperiment ΩBase ΩTest Estimate) :
    lg21ResamplingPolicyKernel e = e.signalGivenBase :=
  paper_definition6_resampling_policy_observable_kernel e

/--
Theorem 4.4, observable-fairness core: access and resampled no-access estimate
laws agree conditional on every base profile.
-/
theorem paper_interface_theorem4_4_resampling_policy_observably_fair
    {ΩBase ΩTest Estimate : Type*} [Fintype ΩBase] [DecidableEq ΩBase]
    (e : LG21ResamplingExperiment ΩBase ΩTest Estimate) :
    lg21ObservableFair (lg21AccessEstimateKernel e) (lg21ResamplingEstimateKernel e) :=
  paper_theorem4_4_resampling_policy_observably_fair e

/--
Theorem 4.4, demographic-fairness core: observable fairness implies equality of
the mixed demographic estimate laws.
-/
theorem paper_interface_theorem4_4_resampling_policy_demographically_fair
    {ΩBase ΩTest Estimate : Type*} [Fintype ΩBase] [DecidableEq ΩBase]
    (e : LG21ResamplingExperiment ΩBase ΩTest Estimate) :
    lg21DemographicallyFair e.baseProfile
      (lg21AccessEstimateKernel e) (lg21ResamplingEstimateKernel e) :=
  paper_theorem4_4_resampling_policy_demographically_fair e

end

end LG21TestOptionalPolicies
