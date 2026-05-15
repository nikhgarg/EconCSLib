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
