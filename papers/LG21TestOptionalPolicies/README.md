# Test-optional Admissions and Informational Gaps

## Source Version

- Paper: *Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps*
- Authors: Zhi Liu and Nikhil Garg
- Version formalized: arXiv:2107.08922 / EAAMO 2021 version
- Official URL: https://doi.org/10.1145/3465416.3483293
- arXiv URL: https://arxiv.org/abs/2107.08922
- PDF URL: https://arxiv.org/pdf/2107.08922
- Accessed: 2026-05-01

The source PDF is intentionally not committed to git. It is kept locally as
`source.pdf` and ignored by the local `.gitignore`. The extracted source text
cache is kept as `source.txt` for named-statement audits.

## Central Theorem File

- `LG21TestOptionalPolicies/MainTheorems.lean`
- Human-facing theorem ledger: `LG21TestOptionalPolicies/PaperInterface.lean`
- Live proof plan: `LG21TestOptionalPolicies/FORMALIZATION_PLAN.md`

## Dependency DAG

- `LG21TestOptionalPolicies/DependencyDAG.tex`

## Guideline Audit

- Folder contract: satisfied (`.gitignore`, `README.md`, `DependencyDAG.tex`,
  `MainTheorems.lean`, `PaperInterface.lean`, `FORMALIZATION_PLAN.md`, local
  PDF, and `source.txt` are present).
- README status vocabulary: updated to use the controlled statuses from
  `docs/STATUS.md`.
- DAG status vocabulary: updated to use shared `docs/tikz/dag_preamble.tex`
  styles and source-facing node labels.
- Important correction: the earlier README/DAG listed internal finite
  admissions helper identities as the theorem roadmap. Those helper identities
  are real Lean support, but they are not the paper's named theorem structure.
  The table below now separates source items from auxiliary Lean support.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Source model: access status, base/test features, reporting, and estimation policies | `LG21Model`, `lg21BaseModel`, `lg21TestModel`, `LG21SourcePolicySurface`, `LG21SourceLawPolicySurface` | partially formalized | `MainTheorems.lean` | Finite base/test signal kernels, shared quality, a PMF distributional policy surface, and a continuous-law equality surface are encoded; the concrete access/report/take information sets are not yet source-faithfully instantiated. |
| Bayesian optimal Gaussian estimator used by `P_BO` | `paper_bayesian_optimal_estimator_gaussian`, `paper_bayesian_optimal_estimator_strictMono_feature`, `paper_reporting_gaussian_threshold_iff_cutoff`, `paper_interface_bayesian_optimal_estimator_gaussian` | formalized with caveat | `MainTheorems.lean`, `PaperInterface.lean` | The shared Gaussian posterior-mean formula, marginal estimate law, feature monotonicity, and reporting-threshold cutoff are proved using `GaussianOffsetSignalFamily`; the later strategic/fairness theorems still need concrete equilibrium and distribution-comparison instantiations. |
| Definition 1, equilibrium | `LG21AccessAction`, `LG21AccessAction.feasible`, `LG21EquilibriumData`, `lg21Equilibrium` | formalized with caveat | `MainTheorems.lean`, `PaperInterface.lean` | The paper's concrete `(Y,X)` action object, feasibility condition `Y ≥ X`, optional-reporting regime, and report-required regime `Y = X` are encoded. The equilibrium predicate still abstracts over feasible-action, best-response, and estimation-consistency data and is not yet instantiated with the Gaussian payoff. |
| Definition 2, latent skill fairness | `lg21SourceLatentSkillFair`, `lg21SourceLawLatentSkillFair` | formalized with caveat | `MainTheorems.lean` | Source equality of estimate laws conditional on equilibrium, skill, and observed base features is encoded over both PMF and arbitrary continuous-law surfaces. |
| Definition 3, observable fairness | `lg21SourceObservablyFair`, `lg21SourceLawObservablyFair`, `lg21ObservableFair` | formalized with caveat | `MainTheorems.lean` | Source equilibrium-quantified equality is encoded over PMF and arbitrary law surfaces; finite kernel equality remains available for resampling. |
| Definition 4, demographic fairness | `lg21SourceDemographicallyFair`, `lg21SourceLawDemographicallyFair`, `lg21DemographicallyFair`, `lg21DemographicEstimateDistribution`, `lg21_sourceObservablyFair_of_latentSkillFair_of_mixture`, `lg21_sourceDemographicallyFair_of_observablyFair_of_mixture`, `lg21_demographicallyFair_of_observableFair` | formalized with caveat | `MainTheorems.lean`, `PaperInterface.lean` | Source equilibrium-quantified equality is encoded over PMF and arbitrary law surfaces. The paper's implication chain latent skill fairness implies observable fairness implies demographic fairness is proved for the finite PMF surface under explicit shared skill/base mixture identities. |
| Definition 5, test-blank policies | `lg21SourceTestBlank`, `lg21SourceLawTestBlank` | formalized with caveat | `MainTheorems.lean` | Source statement that base-only and full-feature estimate laws agree in every equilibrium is encoded over abstract PMF and continuous-law surfaces. |
| Theorem 3.1, strategic withholding | `paper_theorem3_1_reporting_threshold_of_gaussian_best_response`, `lg21LowerCutoffStrategy`, `LG21StrategicWithholdingCertificate`, `paper_theorem3_1_strategic_withholding_of_certificate` | partially formalized | `MainTheorems.lean`, `PaperInterface.lean` | The Gaussian fixed-information reporting decision is proved to be a finite lower-cutoff rule in the reported test score, and all lower-cutoff rules are monotone. The endpoint conclusions about existence of withholding, the taking threshold, and failure of fairness remain certificate-shaped pending the full equilibrium/no-profitable-deviation proof. |
| Theorem 3.2, fairness impossibility | `LG21FairnessImpossibilityCertificate`, `LG21LawFairnessImpossibilityCertificate`, `paper_theorem3_2_fairness_impossibility_of_certificate`, `paper_theorem3_2_law_fairness_impossibility_of_certificate`, `paper_theorem3_2_not_latent_or_observable_fair_of_test_relevance_witness`, `paper_theorem3_2_not_law_latent_or_observable_fair_of_test_relevance_witness` | conditional | `MainTheorems.lean`, `PaperInterface.lean` | Endpoint states latent or observable fairness implies test-blankness over both PMF and arbitrary law surfaces. The contrapositive from a concrete test-relevance witness is proved; the source unraveling proof of the implication remains a certificate. |
| Lemma 4.1, strategy-proofness when access is observed | `GaussianLowerTailMeanCertificate`, `standardGaussianLowerTailMeanCertificate`, `paper_lemma4_1_reporting_cutoff_has_profitable_deviation_core`, `paper_lemma4_1_gaussian_reporting_cutoff_has_profitable_deviation`, `paper_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding`, `paper_lemma4_1_no_nontrivial_gaussian_reporting_cutoff_of_no_profitable_withholding_from_cutoff`, `paper_lemma4_1_report_cutoff_estimate_lt_of_lower_tail_score`, `paper_lemma4_1_all_report_of_gaussian_lower_tail_certificate_no_profitable_withholding`, `paper_lemma4_1_take_test_cutoff_has_profitable_deviation`, `paper_lemma4_1_no_nontrivial_take_test_cutoff_of_no_profitable_deviation`, `paper_lemma4_1_all_take_of_gaussian_lower_tail_certificate_no_profitable_test_taking`, `paper_lemma4_1_strategy_proofness_of_lower_tail_thresholds`, `LG21ObservedAccessStrategyProofCertificate`, `paper_lemma4_1_strategy_proofness_of_certificate` | partially formalized | `MainTheorems.lean`, `PaperInterface.lean`, `EconCSLib/Foundations/Probability/Gaussian.lean`, `EconCSLib/Foundations/Probability/GaussianMathlib.lean` | The optional-reporting proof now has the continuous strictly increasing cutoff-deviation core, its Gaussian posterior-score instantiation, and source-shaped lower-tail bridges using the shared lower-tail-mean certificate: if the no-report estimate is the posterior at the Gaussian mean below the cutoff, any nontrivial reporting cutoff contradicts no-profitable-withholding, hence all report under the paper's threshold-if-not-all premise. The report-required proof has the Gaussian half-probability deviation witness and lower-tail all-take bridge. A combined lower-tail bridge now derives all-report and all-take conclusions from the two threshold-if-not-all premises, and `GaussianMathlib` supplies a concrete standard-normal lower-tail certificate; the final endpoint still depends on instantiating the threshold premises from the concrete equilibrium predicate. |
| Proposition 4.2, Bayesian optimal on access students is not latent skill fair | `paper_proposition4_2_not_law_latent_skill_fair_of_four_group_core`, `paper_proposition4_2_not_law_latent_skill_fair_of_gaussian_mean_gap`, `paper_proposition4_2_not_law_latent_skill_fair_of_conditional_posterior_mean_gap`, `paper_proposition4_2_not_estimate_law_latent_skill_fair_of_conditional_posterior_mean_gap`, `paper_proposition4_2_not_estimate_law_latent_skill_fair_of_one_test_posterior_law`, `paper_proposition4_2_not_latent_skill_fair_of_lemma4_1_lower_tail_and_one_test_posterior_law`, `LG21NotLatentFairCertificate`, `paper_proposition4_2_not_latent_skill_fair_of_certificate` | partially formalized | `MainTheorems.lean`, `PaperInterface.lean` | The source four-group equality argument is proved over arbitrary law objects. Gaussian mean gaps, concrete conditional posterior-score laws, and the fixed-base one-random-test posterior law now supply the access-side law difference when latent skills are strictly ordered, including source-shaped `LG21EstimateLaw` wrappers. A source-route wrapper now consumes the Lemma 4.1 lower-tail all-report/all-take bridge and the fixed-base one-test posterior law to derive the Proposition 4.2 latent-skill-fairness contradiction. The final concrete endpoint still depends on deriving Lemma 4.1's threshold and lower-tail premises from the concrete equilibrium/reporting model. |
| Proposition 4.3, full Bayesian optimal policy is not observable or demographic fair | `paper_proposition4_3_not_law_observable_or_demographic_fair_of_witnesses`, `paper_proposition4_3_not_law_observable_fair_of_gaussian_variance_gap`, `paper_proposition4_3_not_law_demographic_fair_of_gaussian_variance_gap`, `paper_proposition4_3_not_estimate_law_observable_fair_of_access_gaussian_no_access_point`, `paper_proposition4_3_not_estimate_law_observable_fair_of_one_test_posterior_law_vs_point`, `paper_proposition4_3_not_law_observable_fair_of_posterior_precision_gap`, `paper_proposition4_3_not_law_demographic_fair_of_posterior_precision_gap`, `paper_proposition4_3_not_law_observable_or_demographic_fair_of_lemma4_1_lower_tail_and_posterior_precision_gap`, `LG21NotObservableOrDemographicFairCertificate`, `paper_proposition4_3_not_observable_or_demographic_fair_of_certificate` | partially formalized | `MainTheorems.lean`, `PaperInterface.lean` | The law-level observable/demographic witness arguments, Gaussian variance/scale-gap contradictions, posterior-score signal-precision instantiations, the source-shaped observable point-vs-Gaussian contradiction, and its fixed-base one-random-test posterior-law form are proved. A source-route wrapper now consumes Lemma 4.1's lower-tail all-report/all-take bridge and the posterior-precision gap to derive both observable- and demographic-fairness contradictions. The final concrete endpoint still depends on deriving Lemma 4.1's threshold/lower-tail premises and the concrete feature-set precision gap from the equilibrium model. |
| Definition 6, re-sampling policy | `LG21ResamplingExperiment`, `lg21ResamplingPolicyKernel`, `paper_definition6_resampling_policy_observable_kernel` | formalized with caveat | `MainTheorems.lean` | Finite conditional-kernel form: the missing test score is sampled from the conditional test-score law given the non-test profile and then passed through the same estimate map; the Gaussian posterior formula and equilibrium interface are not encoded. |
| Theorem 4.4, re-sampling policy is observable and demographic fair | `paper_theorem4_4_resampling_policy_observably_fair`, `paper_theorem4_4_resampling_policy_demographically_fair` | formalized with caveat | `MainTheorems.lean` | Finite distributional core is closed: access and no-access estimate laws are equal because they are pushforwards of the same conditional test-score law, and demographic fairness follows by mixing over the shared base-profile law. This does not yet include Lemma 4.1 strategy-proofness or the paper's Gaussian posterior algebra. |
| Auxiliary finite admissions accounting support | `lg21_base_exp_decompose`, `lg21_test_exp_decompose`, and the related `lg21_*` mass/selection/monotonicity wrappers | formalized | `MainTheorems.lean` | None; auxiliary finite-kernel support only, not a source theorem wrapper. |

## Source Notes

The current Lean code closes finite admissions accounting identities, the
finite conditional-kernel core of Definition 6 / Theorem 4.4, the shared
Gaussian posterior-mean algebra used by `P_BO`, the two main Lemma 4.1 scalar
no-deviation contradictions plus lower-tail conditional all-report/all-take
bridges, and the law-level fairness contradiction cores for Propositions
4.2--4.3. The
Proposition 4.2 and Proposition 4.3 cores now have
concrete Gaussian posterior-score law instantiations from conditional mean gaps
and signal-precision scale gaps. Propositions 4.2 and 4.3 now both have named
source routes through Lemma 4.1's lower-tail strategy-proofness bridge. It does
not yet formalize the paper's concrete strategic equilibrium model, Theorem
3.1/3.2, or the final equilibrium/reporting bridge used in the source proofs.
