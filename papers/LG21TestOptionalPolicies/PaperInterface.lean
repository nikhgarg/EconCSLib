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

/-- Definition 3: observable fairness in every equilibrium. -/
abbrev paperObservablyFair {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) : Prop :=
  lg21SourceObservablyFair S

/-- Definition 4: demographic fairness in every equilibrium. -/
abbrev paperDemographicallyFair {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) : Prop :=
  lg21SourceDemographicallyFair S

/-- Definition 5: test-blankness, i.e. test scores play no role. -/
abbrev paperTestBlank {Skill Base Test Estimate : Type*}
    (S : LG21SourcePolicySurface Skill Base Test Estimate) : Prop :=
  lg21SourceTestBlank S

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
