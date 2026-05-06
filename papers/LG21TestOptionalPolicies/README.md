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

## Dependency DAG

- `LG21TestOptionalPolicies/DependencyDAG.tex`

## Guideline Audit

- Folder contract: satisfied (`.gitignore`, `README.md`, `DependencyDAG.tex`,
  `MainTheorems.lean`, local PDF, and `source.txt` are present).
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
| Source model: access status, base/test features, reporting, and estimation policies | `LG21Model`, `lg21BaseModel`, `lg21TestModel`, `LG21SourcePolicySurface` | partially formalized | `MainTheorems.lean` | Finite base/test signal kernels, shared quality, and a source-facing distributional policy surface are encoded; the Gaussian posterior formulas and concrete access/report/take information sets are not yet source-faithfully instantiated. |
| Definition 1, equilibrium | `LG21EquilibriumData`, `lg21Equilibrium` | formalized with caveat | `MainTheorems.lean` | Abstract feasible-action, best-response, and estimation-consistency predicate matching the source structure; not yet instantiated with the paper's concrete `(Y,X)` action space and Gaussian payoff. |
| Definition 2, latent skill fairness | `lg21SourceLatentSkillFair` | formalized with caveat | `MainTheorems.lean` | Source equality of estimate laws conditional on equilibrium, skill, and observed base features is encoded over `LG21SourcePolicySurface`; concrete Gaussian estimate distributions remain open. |
| Definition 3, observable fairness | `lg21SourceObservablyFair`, `lg21ObservableFair` | formalized with caveat | `MainTheorems.lean` | Source equilibrium-quantified definition and finite kernel equality are encoded. |
| Definition 4, demographic fairness | `lg21SourceDemographicallyFair`, `lg21DemographicallyFair`, `lg21DemographicEstimateDistribution`, `lg21_demographicallyFair_of_observableFair` | formalized with caveat | `MainTheorems.lean` | Source equilibrium-quantified definition and finite mixed-law equality are encoded; observable fairness implies demographic fairness under a shared base-profile law. |
| Definition 5, test-blank policies | `lg21SourceTestBlank` | formalized with caveat | `MainTheorems.lean` | Source statement that base-only and full-feature estimate distributions agree in every equilibrium is encoded over the abstract policy surface. |
| Theorem 3.1, strategic withholding | `LG21StrategicWithholdingCertificate`, `paper_theorem3_1_strategic_withholding_of_certificate` | conditional | `MainTheorems.lean` | Endpoint exposes the source conclusions: some access students do not report, threshold reporting/taking behavior, and failure of all three fairness definitions. The Bayesian threshold/unfairness proof remains a certificate. |
| Theorem 3.2, fairness impossibility | `LG21FairnessImpossibilityCertificate`, `paper_theorem3_2_fairness_impossibility_of_certificate` | conditional | `MainTheorems.lean` | Endpoint states latent or observable fairness implies test-blankness. The unraveling proof remains a certificate. |
| Lemma 4.1, strategy-proofness when access is observed | `LG21ObservedAccessStrategyProofCertificate`, `paper_lemma4_1_strategy_proofness_of_certificate` | conditional | `MainTheorems.lean` | Endpoint states all access students take/report under observed-access Bayesian optimal estimation. The Bayesian threshold proof remains a certificate. |
| Proposition 4.2, Bayesian optimal on access students is not latent skill fair | `LG21NotLatentFairCertificate`, `paper_proposition4_2_not_latent_skill_fair_of_certificate` | conditional | `MainTheorems.lean` | Endpoint exposes the not-latent-skill-fair conclusion; Gaussian distribution comparison remains a certificate. |
| Proposition 4.3, full Bayesian optimal policy is not observable or demographic fair | `LG21NotObservableOrDemographicFairCertificate`, `paper_proposition4_3_not_observable_or_demographic_fair_of_certificate` | conditional | `MainTheorems.lean` | Endpoint exposes the not-observable and not-demographic conclusions; concrete Bayesian posterior distribution comparison remains a certificate. |
| Definition 6, re-sampling policy | `LG21ResamplingExperiment`, `lg21ResamplingPolicyKernel`, `paper_definition6_resampling_policy_observable_kernel` | formalized with caveat | `MainTheorems.lean` | Finite conditional-kernel form: the missing test score is sampled from the conditional test-score law given the non-test profile and then passed through the same estimate map; the Gaussian posterior formula and equilibrium interface are not encoded. |
| Theorem 4.4, re-sampling policy is observable and demographic fair | `paper_theorem4_4_resampling_policy_observably_fair`, `paper_theorem4_4_resampling_policy_demographically_fair` | formalized with caveat | `MainTheorems.lean` | Finite distributional core is closed: access and no-access estimate laws are equal because they are pushforwards of the same conditional test-score law, and demographic fairness follows by mixing over the shared base-profile law. This does not yet include Lemma 4.1 strategy-proofness or the paper's Gaussian posterior algebra. |
| Auxiliary finite admissions accounting support | `lg21_base_exp_decompose`, `lg21_test_exp_decompose`, and the related `lg21_*` mass/selection/monotonicity wrappers | formalized | `MainTheorems.lean` | None; auxiliary finite-kernel support only, not a source theorem wrapper. |

## Source Notes

The current Lean code closes finite admissions accounting identities and the
finite conditional-kernel core of Definition 6 / Theorem 4.4. It does not yet
formalize the paper's strategic equilibrium model, Lemma 4.1, the negative
unraveling theorems, or the Gaussian posterior formulas used in the source
proofs.
