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
| Definition 1, equilibrium | `LG21EquilibriumData`, `lg21Equilibrium` | formalized with caveat | `MainTheorems.lean` | Abstract feasible-action, best-response, and estimation-consistency predicate matching the source structure; not yet instantiated with the paper's concrete `(Y,X)` action space and Gaussian payoff. |
| Definition 2, latent skill fairness | `lg21SourceLatentSkillFair`, `lg21SourceLawLatentSkillFair` | formalized with caveat | `MainTheorems.lean` | Source equality of estimate laws conditional on equilibrium, skill, and observed base features is encoded over both PMF and arbitrary continuous-law surfaces. |
| Definition 3, observable fairness | `lg21SourceObservablyFair`, `lg21SourceLawObservablyFair`, `lg21ObservableFair` | formalized with caveat | `MainTheorems.lean` | Source equilibrium-quantified equality is encoded over PMF and arbitrary law surfaces; finite kernel equality remains available for resampling. |
| Definition 4, demographic fairness | `lg21SourceDemographicallyFair`, `lg21SourceLawDemographicallyFair`, `lg21DemographicallyFair`, `lg21DemographicEstimateDistribution`, `lg21_demographicallyFair_of_observableFair` | formalized with caveat | `MainTheorems.lean` | Source equilibrium-quantified equality is encoded over PMF and arbitrary law surfaces; observable fairness implies demographic fairness under a shared base-profile law. |
| Definition 5, test-blank policies | `lg21SourceTestBlank`, `lg21SourceLawTestBlank` | formalized with caveat | `MainTheorems.lean` | Source statement that base-only and full-feature estimate laws agree in every equilibrium is encoded over abstract PMF and continuous-law surfaces. |
| Theorem 3.1, strategic withholding | `LG21StrategicWithholdingCertificate`, `paper_theorem3_1_strategic_withholding_of_certificate` | conditional | `MainTheorems.lean` | Endpoint exposes the source conclusions: some access students do not report, threshold reporting/taking behavior, and failure of all three fairness definitions. The Bayesian threshold/unfairness proof remains a certificate. |
| Theorem 3.2, fairness impossibility | `LG21FairnessImpossibilityCertificate`, `paper_theorem3_2_fairness_impossibility_of_certificate` | conditional | `MainTheorems.lean` | Endpoint states latent or observable fairness implies test-blankness. The unraveling proof remains a certificate. |
| Lemma 4.1, strategy-proofness when access is observed | `LG21ObservedAccessStrategyProofCertificate`, `paper_lemma4_1_strategy_proofness_of_certificate` | conditional | `MainTheorems.lean` | Endpoint states all access students take/report under observed-access Bayesian optimal estimation. The Bayesian threshold proof remains a certificate. |
| Proposition 4.2, Bayesian optimal on access students is not latent skill fair | `paper_proposition4_2_not_law_latent_skill_fair_of_four_group_core`, `paper_proposition4_2_not_law_latent_skill_fair_of_gaussian_mean_gap`, `LG21NotLatentFairCertificate`, `paper_proposition4_2_not_latent_skill_fair_of_certificate` | partially formalized | `MainTheorems.lean`, `PaperInterface.lean` | The source four-group equality argument is proved over arbitrary law objects, and a Gaussian mean gap supplies the access-side law difference. The full endpoint still depends on Lemma 4.1 and concrete equilibrium/reporting instantiation. |
| Proposition 4.3, full Bayesian optimal policy is not observable or demographic fair | `paper_proposition4_3_not_law_observable_or_demographic_fair_of_witnesses`, `paper_proposition4_3_not_law_observable_fair_of_gaussian_variance_gap`, `paper_proposition4_3_not_law_demographic_fair_of_gaussian_variance_gap`, `LG21NotObservableOrDemographicFairCertificate`, `paper_proposition4_3_not_observable_or_demographic_fair_of_certificate` | partially formalized | `MainTheorems.lean`, `PaperInterface.lean` | The law-level observable/demographic witness arguments and Gaussian variance-gap contradictions are proved. The full endpoint still depends on Lemma 4.1 and concrete Bayesian posterior distribution instantiation. |
| Definition 6, re-sampling policy | `LG21ResamplingExperiment`, `lg21ResamplingPolicyKernel`, `paper_definition6_resampling_policy_observable_kernel` | formalized with caveat | `MainTheorems.lean` | Finite conditional-kernel form: the missing test score is sampled from the conditional test-score law given the non-test profile and then passed through the same estimate map; the Gaussian posterior formula and equilibrium interface are not encoded. |
| Theorem 4.4, re-sampling policy is observable and demographic fair | `paper_theorem4_4_resampling_policy_observably_fair`, `paper_theorem4_4_resampling_policy_demographically_fair` | formalized with caveat | `MainTheorems.lean` | Finite distributional core is closed: access and no-access estimate laws are equal because they are pushforwards of the same conditional test-score law, and demographic fairness follows by mixing over the shared base-profile law. This does not yet include Lemma 4.1 strategy-proofness or the paper's Gaussian posterior algebra. |
| Auxiliary finite admissions accounting support | `lg21_base_exp_decompose`, `lg21_test_exp_decompose`, and the related `lg21_*` mass/selection/monotonicity wrappers | formalized | `MainTheorems.lean` | None; auxiliary finite-kernel support only, not a source theorem wrapper. |

## Source Notes

The current Lean code closes finite admissions accounting identities, the
finite conditional-kernel core of Definition 6 / Theorem 4.4, the shared
Gaussian posterior-mean algebra used by `P_BO`, and the law-level fairness
contradiction cores for Propositions 4.2--4.3. It does not yet formalize the
paper's concrete strategic equilibrium model, Lemma 4.1, Theorem 3.1/3.2, or
the full Bayesian posterior distribution instantiations used in the source
proofs.
