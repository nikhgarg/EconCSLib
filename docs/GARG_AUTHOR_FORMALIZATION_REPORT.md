# Nikhil Garg Paper Formalization Report

Current as of May 16, 2026 for the dashboard snapshot and inventory rows below.
Some detailed paper notes retain older pass history where useful.

This is the running report for the author-wide formalization campaign requested
for papers at https://gargnikhil.com/Papers/. The screening rule used here is:
papers in an economics-and-computation or machine-learning venue, with Nikhil
Garg as first or last author, and with explicit theorem/proposition-level
mathematical content.

Status vocabulary in this report:

- `Complete`: the selected paper theorem endpoints are closed in Lean and have
  final validation artifacts.
- `Partial`: nontrivial Lean content exists, but source theorem endpoints or
  named sections remain open.
- `Deferred`: not started or paused because the required library infrastructure
  is currently too large for this pass.

## May 16, 2026 Dashboard Snapshot

The review dashboard state records human Lean-vs-paper review progress, not
proof completeness. "Unreviewed" means a human has not yet checked the current
`PaperInterface.lean` statement against the paper statement.

| Paper folder | Formalization status | Human review rows | Current frontier |
|---|---|---:|---|
| `DSWG24DiscretizationBias` | Complete | 1/9 reviewed | Theorems 1 and 2 close in Lean; optional future work is the fully abstract nonatomic source-sweep wrapper. |
| `MBJG25ProducerFairness` | Complete | 0/14 reviewed | Fixed-model rating theorems and responsive-market extensions are closed; the boundary correction for the published strict-variance statement is documented. |
| `GCG24UserItemFairness` | Formalized | 0/6 reviewed | Named main results and supporting propositions/lemmas are formalized in the paper interface; no active proof target is open. |
| `GLM20DroppingStandardizedTesting` | Partial | 0/337 reviewed | Large standard-Gaussian source surface is exposed; Section 5 and later equilibrium/objective bridges remain the main paper-level frontier. |
| `LG21TestOptionalPolicies` | Partial | 0/305 reviewed | Finite decomposition and resampling cores are closed; strategic/Gaussian instantiations remain open. |
| `GN21DriverSurgePricing` | Complete | 0/3 reviewed | CTMC reward/time algebra and Theorems 1-4 are exposed; Theorem 3 has both positive-mass and feasible sequential current-bounds full-measurable endpoints, with zero-mass totalization obstructions documented separately. |
| `PRPKG24AccuracyDiversity` | Partial | 0/8 reviewed | Finite optimization, Bernoulli, and uniform-support layers are in place; asymptotic order-statistic/homogeneity layers remain open. |

## Current Build

Last review-surface verification:

```bash
python3 scripts/audit_repository.py --include-active
python3 -m py_compile scripts/review_dashboard.py scripts/audit_repository.py scripts/bootstrap_review_launchers.py scripts/new_paper.py
lake build GN21DriverSurgePricing.PaperInterface IM05MarriageHonestyStability.PaperInterface KR21Monoculture.PaperInterface LMMS04FairDivision.PaperInterface LOS02CombinatorialAuctions.PaperInterface
lake build PRPKG24AccuracyDiversity.PaperInterface
```

The May 16 audit has zero errors with active paper folders included. Remaining
warnings are ledger-style review prompts: exact-`formalized` rows whose notes
still mention caveats/assumptions and long top-level human summaries.

## Existing Formalization Tracks

| Paper | Venue/source | Status | Current declarations | Blocker before moving further |
|---|---|---|---|---|
| *On Approximately Fair Allocations of Indivisible Goods* | EC 2004 / ACM DOI 10.1145/988772.988792 | Partial | `EconCSLib.FairDivision.paper_lmms_theorem_2_1_max_marginal`, `EconCSLib.FairDivision.paper_lmms_algorithm_isAllocationOf_and_envyBoundedBy` | Later source sections remain open. |
| *Algorithmic Monoculture and Social Welfare* | arXiv:2101.05853 | Partial | `MallowsComparison.paper_theorem3_pointwise_rankFactorization`, `MallowsComparison.cross_weight_sum_pos_of_rankFactorization`, `MallowsComparison.firstMoverUtility_strict_of_rankFactorization`, `MallowsAccuracyFamilySpec.paper_theorem1_mallows_family`, `AccuracyFamily.theorem1Target_of_paperAssumptions`, `AccuracyFamily.theorem1_exists_right_initial_f_lt_g_of_prefersIndependent_and_atom_continuity` | Full concrete-family Theorem 1 remains conditional on instantiating the remaining Definition 1 analytic fields in `MallowsAccuracyFamilySpec` or instantiating `AccuracyFamily.Theorem1GlobalAnalyticCertificate F θH` directly. |
| *User-item fairness tradeoffs in recommendations* | NeurIPS 2024 / arXiv:2412.04466 | Complete | `ReductionWitness.paper_symmetric_item_fairness_value_set_reduction`, `RecommendationModel.paper_lemma3_unconstrained_user_fairness_eq_one`, `TypePolicy.paper_lemma4_problem6_basicFeasibleSupportCertificate_of_thresholdSupport`, `OpposingTypes.paper_problem6_equalizedBasicOptimal_of_equalityFormOptimalBFS`, `OpposingTypes.paper_problem6_equalizedBasicOptimal_of_closed_certificate`, `OpposingTypes.paper_problem6_equalizedBasicOptimal_policy_eq_of_feasibleAtLevel_one_equalized_shared`, `OpposingTypes.paper_problem6_equalizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_equalizedBasicOptimal_isOptimalAtLevel`, `OpposingTypes.paper_lemma6_equalizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_center_of_closed_half`, `OpposingTypes.paper_lemma7_equalizedBasicOptimal_lastActive_mono_of_alpha_le`, `OpposingTypes.paper_problem6_LPOptimalValue_eq_closedValue_of_equalizedBasicOptimal_of_two_lt`, `OpposingTypes.paper_lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center_of_closed_half`, `OpposingTypes.paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_center_chain_of_closed_half`, `OpposingTypes.paper_theorem3_typeFairness_mono_firstHalf_center_chain_of_closed_half`, `OpposingTypes.paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_equalizedBasicOptimal_dominance_closed_half`, `EstimatedRecommendationModel.paper_theorem4_misestimation_large_from_bounds` | Named main results and supporting propositions/lemmas are now formalized in the paper-local interface; remaining dashboard work is human statement validation. |
| *Reconciling the accuracy-diversity trade-off in recommendations* | WWW 2024 / arXiv:2307.15142 | Partial | `ConsumptionModel.paper_finite_optimum_exists`, `BernoulliSatisfactionModel.paper_bernoulli_finite_optimum_exists`, `ConsumptionModel.paper_finite_exchange_improvement`, `BernoulliSatisfactionModel.paper_bernoulli_optimum_first_order_condition`, `BernoulliSatisfactionModel.paper_iid_bernoulli_optimum_uniform_homogeneity`, `paper_uniform_top_one_optimum_first_order_condition`, `paper_uniform_sqrt_homogeneity_of_count_closeness`, `paper_rounding_count_close_of_no_crossing`, `paper_uniform_rounding_count_close_of_strict_exchange_certificate`, `paper_uniform_top_one_sqrt_homogeneity_of_anchor_certificate`, `paper_uniform_rounding_count_close_of_two_anchor_certificate`, `paper_uniform_top_one_sqrt_homogeneity_of_two_anchor_certificate`, `paper_uniform_rounding_count_close_of_shifted_square_anchors`, `paper_uniform_top_one_sqrt_homogeneity_of_shifted_square_anchors` | Proposition 2 still needs the real-relaxation optimizer and construction of square-root lower/upper anchors with one-item target closeness and shifted-target bracketing; full Theorems 1/2/3 still need the asymptotic homogeneity/order-statistic layer for bounded, exponential, Pareto, and varying Bernoulli models. |

## Paper Worked This Pass

### Reconciling the Accuracy-Diversity Trade-off in Recommendations

Source: https://arxiv.org/abs/2307.15142. The paper is Nikhil-last-author and
appeared at TheWebConf/WWW 2024.

Formalized:

- Generic finite count theorem:
  `AccuracyDiversity.count_abs_sub_uniform_average_le_one_of_pairwise_balanced`
- Generic representation theorem:
  `AccuracyDiversity.uniformProfile_approx_of_pairwise_balanced_counts`
- Bernoulli exchange theorem:
  `AccuracyDiversity.BernoulliSatisfactionModel.pairwise_count_le_succ_of_symmetric_optimum`
- Paper-facing theorem:
  `AccuracyDiversity.BernoulliSatisfactionModel.paper_iid_bernoulli_optimum_pairwise_balanced`
- Paper-facing theorem:
  `AccuracyDiversity.BernoulliSatisfactionModel.paper_iid_bernoulli_optimum_uniform_homogeneity`
- Uniform `[0,1]`, `k = 1` order-statistic marginal theorem:
  `AccuracyDiversity.UniformTopOne.forwardMarginal_le_backwardMarginal_of_optimum`
- Paper-facing Proposition 2 marginal theorem:
  `AccuracyDiversity.paper_uniform_top_one_optimum_first_order_condition`
- Paper-facing square-root representation bridge:
  `AccuracyDiversity.paper_uniform_sqrt_homogeneity_of_count_closeness`
- Generic rounding theorem:
  `EconCSLib.FiniteRounding.NoRoundingCrossing.count_lt_anchor_add_card`,
  `EconCSLib.FiniteRounding.NoRoundingCrossing.anchor_lt_count_add_card`
- Paper-facing Appendix D.5 combinatorial wrapper:
  `AccuracyDiversity.paper_rounding_count_close_of_no_crossing`
- Paper-facing strict certificate-to-rounding wrapper:
  `AccuracyDiversity.paper_uniform_rounding_count_close_of_strict_exchange_certificate`
- Paper-facing finite anchor-certificate-to-homogeneity wrapper:
  `AccuracyDiversity.paper_uniform_top_one_sqrt_homogeneity_of_anchor_certificate`
- Two-anchor rounding and homogeneity wrappers:
  `AccuracyDiversity.paper_uniform_rounding_count_close_of_two_anchor_certificate`,
  `AccuracyDiversity.paper_uniform_top_one_sqrt_homogeneity_of_two_anchor_certificate`
- Shifted-square target wrappers:
  `AccuracyDiversity.paper_uniform_rounding_count_close_of_shifted_square_anchors`,
  `AccuracyDiversity.paper_uniform_top_one_sqrt_homogeneity_of_shifted_square_anchors`
- Two-type paper-facing specializations:
  `AccuracyDiversity.paper_symmetric_two_type_bernoulli_optimum_balanced`,
  `AccuracyDiversity.paper_symmetric_two_type_bernoulli_optimum_equal_homogeneity`

Meaning: for a positive finite slate and identical Bernoulli item types with
success probabilities strictly between `0` and `1`, every fixed-total optimum
has type counts differing by at most one, hence each type's recommendation
share is within `1 / N` of the uniform target share. This closes the finite
Bernoulli `0`-homogeneity core. For Proposition 2, the exact uniform top-one
marginal algebra, the bridge from square-root count closeness to
`1/2`-homogeneity, the combinatorial half of Appendix D.5, the strict
exchange-certificate-to-rounding bridge, and the finite
anchor-certificate-to-homogeneity assembly are closed. The rounding layer now
also has a two-anchor lower/upper version that matches floor/ceiling-style
real-relaxation arguments, and the two-anchor strict certificate is discharged
from a squared shifted-target representation of likelihoods.

Not yet formalized:

- The order-statistic and asymptotic machinery for the broader Theorem 1
  distribution families: bounded, exponential, Pareto, and the uniform
  finite-`n` Proposition 2 approximation.
- The Proposition 2 real-relaxation optimizer and proof that square-root floor
  or lower/upper anchors have one-item closeness to the square-root target and
  bracket the shifted square-root real targets.
- Theorems 2 and 3 for non-identical Bernoulli success probabilities and
  decaying probabilities.
- Appendix D-style rounding and limit lemmas connecting discrete optimal count
  allocations to limiting homogeneity constants.

Decision before moving on: continue on this paper only if the next target is the
Proposition 2 relaxation/rounding theorem or the broader
order-statistic/asymptotic layer. The closed finite i.i.d. Bernoulli and uniform
support theorems are unconditional and have no placeholders.

### Addressing Discretization-Induced Bias in Demographic Prediction

Source: https://arxiv.org/abs/2405.16762. The paper is Nikhil-last-author and
appeared at ACM FAccT 2024 before the PNAS Nexus journal version.

Formalized:

- Human-facing Lean interface:
  `DSWG24DiscretizationBias.PaperInterface`.
- Paper-local audit ledger:
  `DSWG24DiscretizationBias.PostPaperAudit`.
- Final validation report:
  `papers/DSWG24DiscretizationBias/FINAL_VALIDATION_REPORT.md`.
- Theorem 1: continuous no-information, perfect-classifier, calibrated MAE
  bound, tightness witness, and the accepted real-coordinate source route are
  formalized.  The source-transformation route includes multiclass-safe
  `S_b/S_d` collapse constructions, aggregate-posterior preservation,
  nonpositive integrated MAE deltas, and coordinate-pullback constructed
  `qNext` endpoints.  The fully abstract arbitrary nonatomic transport version
  is documented as an optional future strengthening.
- Theorem 2(i)--(ii): abstract row-wise Bayes endpoints formalize the paper's
  expected objective and expected-accuracy maximization route; finite Bayes
  dataset wrappers discharge those identities for finite PMF models.
- Theorem 2(iii): finite independent-rule, augmented/randomized-rule, iid
  `Measure.pi`, and Markov-kernel generated wrappers cover the Pareto and
  weighted-objective non-maximality route, plus almost-sure agreement
  equalities and weighted-objective iff packaging under the documented
  argmax-maximality certificate.

Decision before moving on: `Complete`. Optional future work is the fully
abstract nonatomic transport/sweep wrapper and more automatic randomized-rule
measurability wrappers.

### Balancing Producer Fairness and Efficiency via Bayesian Rating System Design

Source: https://arxiv.org/abs/2207.04369. The paper is Nikhil-last-author and
appeared at ICWSM 2025.

**Status: Complete**

The fixed-model theorem pair (Theorems 3.1 and 3.2) is fully formalized.
The responsive market theory and appendices have also been formalized in a secondary pass.
A final validation report and dependency DAG are available in the paper folder.

Bug found and corrected theorem formalized:
- The strict-variance-decrease clause of Theorem 3.1 was found to be false at boundary true
  qualities (`q_v = 0` and `q_v = 1`).
- The corrected strict statement is formalized under the interior-quality
  assumption `0 < q_v < 1`.
- The correct weak statement is formalized on the full closed Bernoulli quality
  interval `0 ≤ q_v ≤ 1`.

Formalized:
- Generic reusable terms and theorems in `EconCSLib.Statistics.BinaryRating`.
- Generic Thompson Sampling and Expected Regret properties in `EconCSLib.Decision` and `EconCSLib.Online`.
- Appendix E Dirichlet-Categorical ordinal rating extension in `EconCSLib.Statistics.OrdinalRating`.
- Section 4 and Appendix C responsive market theory (MSE Decomposition and Individual Producer Unfairness metrics) in `ProducerFairness.ResponsiveMarket`.
- Paper-facing wrappers in `ProducerFairness.MainTheorems` and `ProducerFairness.PaperInterface`.
- Boundary counterexamples justifying the interior assumption.

Final Artifacts:
- Human-facing ledger: `papers/MBJG25ProducerFairness/PaperInterface.lean`
- Validation Report: `papers/MBJG25ProducerFairness/FINAL_VALIDATION_REPORT.md`
- Dependency DAG: `papers/MBJG25ProducerFairness/DependencyDAG.tex`

## Eligible Paper Inventory

These papers passed the first/last-author and venue screen and have explicit
theorem/proposition content. They are candidates for future paper folders.

| Paper | Venue/status on author page | Author position | Theorem content found | Current decision |
|---|---|---:|---|---|
| *How Many Features Can a Language Model Store Under the Linear Representation Hypothesis?* | Working paper, ML theory | first | Theorems 2, 3, 12 and propositions | Deferred: lower bound depends on Alon's rank bound, Turan's theorem, and asymptotic big-O/big-Omega interfaces; upper bound depends on random incoherent matrix existence. |
| *Dropping Standardized Testing for Admissions Trades Off Information and Access* | Management Science; FAccT/EAAMO conference version | first | Strategic withholding, fairness impossibility, strategy-proofness, resampling fairness | Partial: large standard-Gaussian source endpoints for Lemma 1, Proposition 1, Lemma 2, Theorems 1-2, and later bridge surfaces are exposed; Section 5 and later equilibrium/objective bridges remain open and are split into dashboard slices. |
| *Addressing Discretization-Induced Bias in Demographic Prediction* | FAccT 2024 / PNAS Nexus | last | Theorems 1 and 2 | Complete: Theorems 1 and 2 close in Lean; optional future strengthening is the fully abstract nonatomic source sweep. |
| *Driver Surge Pricing* | Management Science; EC 2020 conference version | first | Incentive-compatible pricing mechanism results | Complete: named CTMC lemmas, Theorems 1-4, the positive-mass Theorem 3 endpoint, and the feasible sequential current-bounds full-measurable Theorem 3 endpoint are formalized; `FINAL_VALIDATION_REPORT.md` records the optional zero-mass-dominance lift and the totalized zero-mass obstruction. |
| *Markets for Public Decision-making* | Social Choice and Welfare; WINE 2018 conference version | first | Equilibrium and Nash-welfare results via pairwise issue expansion | Deferred: needs Fisher-market equilibrium, public-decision market equivalence, and Nash-welfare optimality theory. |
| *Designing Informative Rating Systems* | M&SOM; EC 2020 conference version | first | Rating-system design optimization | Deferred: large-deviations performance metric and optimal design algorithm need a statistical asymptotics layer. |
| *Iterative Local Voting for Collective Decision-making in Continuous Spaces* | JAIR; WWW 2017 conference version | first | Convergence and Pareto/fairness properties | Deferred: continuous-space convergence, shrinking neighborhoods, and utility regularity assumptions need analysis infrastructure. |
| *Balancing Producer Fairness and Efficiency via Bayesian Rating System Design* | ICWSM 2025 | last | Theorems 3.1 and 3.2 | Complete: fixed-model theorem pair and dynamic extensions close in Lean; boundary bug logged for the published strict-variance statement at `q_v = 0` and `q_v = 1`. |
| *Monoculture in Matching Markets* | NeurIPS 2024 | last | Theorems 1-3 | Deferred: continuum matching market, market-clearing cutoffs, and asymptotic probability limits. |
| *User-item fairness tradeoffs in recommendations* | NeurIPS 2024 | last | Proposition 1, Proposition 2, Theorems 3-4 | Complete: the named main results and supporting propositions/lemmas are formalized in the paper-local interface; remaining dashboard work is human statement validation. |
| *Wisdom and Foolishness of Noisy Matching Markets* | EC 2024 | last | Theorems 1-4 | Deferred: asymptotic many-to-one matching, max-concentrating/long-tailed probability, and continuum cutoffs. |
| *Redesigning Service Level Agreements: Equity and Efficiency in City Government Operations* | EC 2024 | last | Stylized price-of-equity theorem | Deferred: queueing-network service model and optimization/equity objective layer not present. |
| *Reconciling the accuracy-diversity trade-off in recommendations* | WWW 2024 | last | Theorems 1-3 and corollaries | Partial: full theorem blocked by asymptotic order-statistic layer. |
| *Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps* | EAAMO 2021 | last | Theorems 3.1, 3.2, 4.4 and propositions | Partial: finite decomposition and resampling cores are closed; strategic reporting, Gaussian instantiations, and randomized fairness constraints remain open. |
| *The Stereotyping Problem in Collaboratively Filtered Recommender Systems* | EAAMO 2021 | last | Theorems 2.2, 2.4, 3.1, 3.2 | Deferred: convex hull/separation facts for matrix-factorization accessibility and multi-vector recommender geometry. |
| *Who is in Your Top Three? Optimizing Learning in Elections with Many Candidates* | HCOMP 2019 | first | Learning-rate framework and optimization results | Deferred: asymptotic election-learning rates and large-deviation comparisons. |
| *Designing Optimal Binary Rating Systems* | AISTATS 2019 | first | Optimal binary feedback design | Deferred: large-deviations recovery metric and algorithmic design proof stack. |

## Screened Out

The following papers were not selected in this pass because at least one
required criterion failed.

| Paper | Reason |
|---|---|
| *Correlated Errors in Large Language Models* | Nikhil is last author and ICML, but PDF text search found no theorem/proposition declarations. |
| *Urban Incident Prediction with Graph Neural Networks* | Nikhil is last author and AAAI, but the author-page description is empirical/modeling rather than theorem-driven. |
| *Paper Skygest*, *Optimizing Library Usage and Browser Experience*, *Use Sparse Autoencoders to Discover Unknown Concepts*, *Choosing the Right Weights* | Working paper/other status on the author page, not a published EC/ML venue entry. |
| *Heterogeneous participation and allocation skews* | SIGecom Exchanges essay; no theorem target. |
| *Subjectivity of Monoculture*, *Optimal Strategies in Ranked-Choice Voting*, *Capacity Constraints Make Admissions Processes Less Predictable*, *A No Free Lunch Theorem for Human-AI Collaboration*, *Domain constraints improve risk prediction when outcome data is missing*, *Supply-Side Equilibria in Recommender Systems*, *Strategic Ranking* | Nikhil is not first or last author under the requested screen. |
| Empirical/system papers in CSCW, Nature, NAACL, AAAI public-services tracks, PNAS word embeddings, ML4HC, RecSys short paper, and older wireless/report entries | Either not first/last-author theorem papers in an EC/ML venue, or no theorem-level formal target was identified from the author-page description. |

## Reusable Library Added

Module: `EconCSLib.Decision.Argmax`

- `EconCSLib.Decision.IsPointwiseMax`
- `EconCSLib.Decision.sum_score_le_of_isPointwiseMax`
- `EconCSLib.Decision.averageScore`
- `EconCSLib.Decision.averageScore_le_of_isPointwiseMax`
- `EconCSLib.Decision.exists_maximizingDecisionRule`

This should be reused for admissions, rating-system, recommendation, and
classification papers whenever a Bayes/posterior pointwise argmax rule is the
accuracy-maximizing baseline.

Module: `EconCSLib.Statistics.BinaryRating`

- `EconCSLib.Statistics.JensenConvex`
- `EconCSLib.Statistics.JensenConcave`
- `EconCSLib.Statistics.GlobalMinAt`
- `EconCSLib.Statistics.GlobalMaxAt`
- `EconCSLib.Statistics.priorWeightedVariance`
- `EconCSLib.Statistics.priorWeightedSquaredBias`
- `EconCSLib.Statistics.priorWeightedVariance_quality_zero`
- `EconCSLib.Statistics.priorWeightedVariance_quality_one`
- `EconCSLib.Statistics.priorWeightedVariance_strict_decrease_of_interior_quality`
- `EconCSLib.Statistics.priorWeightedSquaredBias_mono`
- `EconCSLib.Statistics.priorWeightedSquaredBias_jensenConvex_quality`
- `EconCSLib.Statistics.priorWeightedSquaredBias_globalMin_priorMean`
- `EconCSLib.Statistics.priorWeightedVariance_jensenConcave_quality`
- `EconCSLib.Statistics.priorWeightedVariance_globalMax_half`

This should be reused for Bayesian/prior-weighted binary rating papers and for
checking boundary cases in strict monotonicity claims.
