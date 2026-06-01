# Addressing Discretization-Induced Bias in Demographic Prediction

Machine-readable status source: [`status.json`](status.json).

## Source Version

- Paper: *Addressing Discretization-Induced Bias in Demographic Prediction*
- Authors: Evan Dong, Aaron Schein, Yixin Wang, and Nikhil Garg
- Version checked locally: cached arXiv PDF created 2024-05-27; README source label says arXiv:2405.16762 / ACM FAccT 2024 version
- arXiv URL: https://arxiv.org/abs/2405.16762
- PDF URL: https://arxiv.org/pdf/2405.16762
- Official URL: https://doi.org/10.1093/pnasnexus/pgaf027
- Accessed: 2026-04-24

The PDF is cached locally as `DSWG24DiscretizationBias.pdf` and ignored by the
paper-folder `.gitignore`. The extracted text cache
`DSWG24DiscretizationBias.txt` is used for named-statement searches; refresh it
only if the source PDF changes. Use this local PDF for theorem-number and
definition comparisons before refreshing from arXiv.

## Central Theorem And Audit Files

- `DSWG24DiscretizationBias/PaperInterface.lean`
- `DSWG24DiscretizationBias/MainTheorems.lean`
- `DSWG24DiscretizationBias/PostPaperAudit.lean`
- `DSWG24DiscretizationBias/FINAL_VALIDATION_REPORT.md`

`PaperInterface.lean` is the compact human-facing Lean surface: paper
definitions with formulas first, then direct readable theorem statements for
Theorem 1 and Theorem 2. `MainTheorems.lean` contains the full paper-facing
theorem wrappers.
`PostPaperAudit.lean` is the importable audit ledger exposing source-numbered
endpoint aliases and the raw finite/continuous formulas used in the main
paper claims. `FINAL_VALIDATION_REPORT.md` records the source inventory,
paper-definition interface, named theorem statements, documented caveats, and
verification outcomes. Reusable decision-rule lemmas live in
`EconCSLib/Foundations/Optimization/Argmax.lean`.

## Guideline Audit

- Folder contract: satisfied (`.gitignore`, `README.md`, `DependencyDAG.tex`,
  `PaperInterface.lean`, `MainTheorems.lean`, `PostPaperAudit.lean`, local PDF,
  and local extracted text are present).
- README status vocabulary: uses the controlled statuses from
  `docs/STATUS.md`; this refresh adds explicit rows for the source objective
  and Bayes bridge, rather than recording only theorem endpoints.
- DAG status vocabulary: uses shared `docs/tikz/dag_preamble.tex` styles. The
  accepted Theorem 1 coordinate-sweep route is marked closed; dashed edges are
  reserved for conditional auxiliary probability bridges.

## Theorem Status

| Paper item | Lean declaration | Status | File | Remaining assumptions / notes |
|---|---|---|---|---|
| Section 3.1 definitions, continuous classifier, argmax rule, bias, MAE, calibration | `ContinuousTheorem1.continuousMarginalLabelShare`, `continuousAggregatePosterior`, `continuousBias`, `continuousAggregateBias`, `continuousClassifierMAE`, `scoreSigma`, `ConditionalExpectationKernelCalibration`, `ConditionalExpectationCalibration`, `ContinuousCalibration`, `ScoreFiberConditionalCalibration`, `FiniteScoreCalibration`, `PosteriorSimplex`, `IsArgmaxRule`, `BayesianConsistent`, `sourceSaRegion`, `sourceSbRegion`, `sourceScRegion`, `sourceSdRegion`, `sourceSeRegion`, `measurableSet_sourceSaRegion`, `measurableSet_sourceSbRegion`, `measurableSet_sourceScRegion`, `measurableSet_sourceSdRegion`, `measurableSet_sourceSeRegion`, `sourceFocalRegions_exhaustive_of_bounds`, `sourceFocalRegions_cover_of_bounds`, `sourceFocalRegions_exhaustive_of_simplex`, `sourceFocalRegions_cover_of_simplex`, `sourceSaRegion_disjoint_sourceSbRegion`, `sourceSaRegion_disjoint_sourceScRegion`, `sourceSaRegion_disjoint_sourceSdRegion`, `sourceSaRegion_disjoint_sourceSeRegion`, `sourceSbRegion_disjoint_sourceScRegion`, `sourceSbRegion_disjoint_sourceSdRegion`, `sourceSbRegion_disjoint_sourceSeRegion`, `sourceScRegion_disjoint_sourceSdRegion`, `sourceScRegion_disjoint_sourceSeRegion`, `sourceSdRegion_disjoint_sourceSeRegion`, `sourceSbRegion_weights_nonneg`, `sourceSdRegion_weights_nonneg`, `exists_source_balancing_interval_cut`, `integrableOn_of_measurable_norm_le`, `integrableOn_score_of_measurable_unit_interval`, `exists_source_Sb_balancing_interval_cut_of_measurable_bounded`, `exists_source_Sd_balancing_interval_cut_of_measurable_bounded`, `exists_source_Sb_balancing_interval_cut_of_region_subset`, `exists_source_Sb_balancing_interval_cut_of_region_subset_measurable_bounded`, `exists_source_Sd_balancing_interval_cut_of_region_subset`, `exists_source_Sd_balancing_interval_cut_of_region_subset_measurable_bounded` | formalized with caveat | `DSWG24DiscretizationBias/MainTheorems.lean` | Continuous source quantities needed for Theorem 1 are encoded. Calibration is formalized using Mathlib's standard-Borel conditional-expectation kernel, conditional expectation with respect to the score sigma-algebra, event-preimage calibration, positive-mass score-fiber conditional calibration, and finite-score level-set calibration. The source proof's focal regions `S_a` through `S_e`, their measurability, cover including simplex-derived upper-bound variants, pairwise-disjointness, and interval-cut balancing steps are formalized for non-atomic real refinements, with bounded-measurable wrappers discharging interval integrability on finite-measure intervals. |
| Equation (3), expected objective `O_N^gamma` | `paperONObjective`, `paperExpectedONObjective`, `Pareto.weightedObjective` | formalized with caveat | `DSWG24DiscretizationBias/MainTheorems.lean` | None; finite expected-objective formulas are encoded with a supplied fidelity/reference term and an abstract or finite PMF expectation model. |
| Bayes/tower-property bridge for expected true accuracy | `paperExpectedONObjective_eq_expected_paperONObjective`, `expectedDecisionAccuracy_eq_expectedDecisionScore_of_row_bayes`, `Finite.FiniteBayesDatasetModel.row_bayes` | formalized | `DSWG24DiscretizationBias/MainTheorems.lean`, `EconCSLib/Foundations/Optimization/Argmax.lean` | None; the row-wise Bayes identities are the Lean form of the paper's Bayes-optimal score assumption. `FiniteBayesDatasetModel.row_bayes` is only a finite-PMF discharger for those identities, not a restriction on Theorem 2. |
| Theorem 1(i), no-information argmax bias formula | `paper_theorem1i_no_information_prior_bias`, `paper_theorem1i_continuous_no_information_bias`, `paper_theorem1i_continuous_no_information_aggregate_bias` | formalized with caveat | `DSWG24DiscretizationBias/MainTheorems.lean` | None for finite/continuous deterministic all-to-plurality wrappers; plurality/tie-breaking is supplied as the constant selected class. |
| Theorem 1(ii), perfect-classifier zero bias | `paper_theorem1ii_perfect_classifier_prior_bias_zero`, `paper_theorem1ii_continuous_perfect_classifier_prior_bias_zero` | formalized with caveat | `DSWG24DiscretizationBias/MainTheorems.lean` | None for finite/continuous prior-reference wrappers under pointwise truth-equality of the induced rule. |
| Theorem 1(iii), argmax bias bounded by MAE and tight | `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_condExpKernelCalibration`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_condExpKernelCalibration_finite`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_condExpKernelCalibration_finite_scoreBounded`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_condExpKernelCalibration_finite_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_condExpCalibration`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_condExpCalibration_finite`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_condExpCalibration_finite_scoreBounded`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_condExpCalibration_finite_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_continuousCalibration`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_continuousCalibration_finite`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_continuousCalibration_finite_scoreBounded`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_continuousCalibration_finite_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_finiteScoreCalibration`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_finiteScoreCalibration_finite`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_finiteScoreCalibration_finite_scoreBounded`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_finiteScoreCalibration_finite_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sourceTransformation`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_featureMap_worstCaseEquality`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_featureMap_worstCaseEquality_exact`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_featureMap_worstCaseEquality_scoreBounded`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_featureMap_worstCaseEquality_product_scoreBounded`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_featureMap_worstCaseEquality_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_worstCaseEquality_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_featureMap_reducedSourceRegions_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_featureMap_reducedSourceRegions_uniformMiddle_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_featureMap_sourceTransformations_product_scoreBounded`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_featureMap_sourceTransformations_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_featureMap_sourceTransformations_reducedSourceRegions_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_featureMap_sourceTransformations_uniformMiddle_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_featureMap_reducedSourceRegions_continuousCalibration_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_featureMap_reducedSourceRegions_uniformMiddle_continuousCalibration_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_featureMap_sourceTransformations_reducedSourceRegions_continuousCalibration_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_featureMap_sourceTransformations_uniformMiddle_continuousCalibration_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_continuousCalibration_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_continuousCalibration_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_continuousCalibration_aggregate_preserved_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_continuousCalibration_aggregate_preserved_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_worstCaseEquality_integral_delta_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_canonicalRule_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_canonicalRule_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_canonicalRule_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`, `paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_sameLaw_reducedSourceRegions_uniformMiddle_canonicalRule_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`, `paper_theorem1iii_continuous_reference_bias_le_mae`, `paper_theorem1iii_continuous_argmax_bias_le_mae`, `paper_theorem1iii_argmax_bias_le_mae_of_simplex`, `paper_theorem1iii_tight_binary_uniform_example`, `posterior_coord_le_one_of_sum_nonneg`, `PosteriorSimplex.of_sum_nonneg`, `uniform_inverse_card_pos`, `uniform_inverse_card_lt_one_of_one_lt_card`, `norm_paperConditionalMAE_le_one_of_sum_nonneg`, `exists_source_Sb_balancing_interval_cut`, `exists_source_Sd_balancing_interval_cut`, `jointFeatureSetMass_empty`, `jointFeatureSetMass_univ`, `jointFeatureSetMass_univ_of_probability`, `jointFeatureSetMass_eq_featureMarginal_integral`, `jointFeatureSetMass_eq_featureMarginal_real`, `integrable_jointFeatureSetIndicator_of_finite`, `aestronglyMeasurable_jointFeatureSetIndicator_of_measurableSet`, `integrable_jointFeatureSetIndicator_of_measurableSet_finite`, `jointFeatureSetMass_union_of_disjoint`, `jointFeatureSetMass_union_of_disjoint_finite`, `jointFeatureSetMass_five_union_of_pairwise_disjoint`, `jointFeatureSetMass_sourceFocalRegions_sum`, `jointFeatureSetMass_sourceFocalRegions_univ_sum_of_bounds`, `jointFeatureSetMass_sourceFocalRegions_sum_eq_one_of_probability`, `jointFeatureSetMass_sourceFocalRegions_univ_sum_of_bounds_finite`, `jointFeatureSetMass_sourceFocalRegions_univ_sum_of_simplex_finite`, `jointFeatureSetMass_sourceFocalRegions_sum_eq_one_of_probability_finite`, `jointFeatureSetMass_sourceFocalRegions_sum_eq_one_of_probability_simplex_finite`, `integrable_jointLabelIndicator_of_finite`, `integrable_jointScore_of_bounds_finite`, `aestronglyMeasurable_jointLabelIndicator_product`, `integrable_jointLabelIndicator_product_finite`, `integrable_jointDecisionIndicator_of_finite`, `aestronglyMeasurable_jointDecisionIndicator_product`, `integrable_jointDecisionIndicator_product_finite`, `aestronglyMeasurable_finiteScoreMassFiber_product`, `integrable_finiteScoreMassFiber_product_finite`, `aestronglyMeasurable_finiteScoreLabelFiber_product`, `integrable_finiteScoreLabelFiber_product_finite`, `integrable_continuousJointClassifierMAE_of_ae_bound`, `measurable_jointConditionalMAE_of_scores`, `aestronglyMeasurable_jointConditionalMAE_of_scores`, `norm_paperConditionalMAE_le_card_of_bounds`, `eventually_norm_jointConditionalMAE_le_card_of_bounds`, `integrable_jointConditionalMAE_of_scores_finite`, `eventually_norm_jointConditionalMAE_le_one_of_sum_nonneg`, `integrable_jointConditionalMAE_of_scores_simplex_finite`, `sourceTransformationCertificate_trans`, `sourceTransformationCertificate_of_target_bound`, `continuousJointPrior_eq_of_measurePreserving_label`, `continuousJointDecisionShare_eq_of_measurePreserving_rule`, `continuousJointClassifierMAE_eq_of_measurePreserving`, `continuousJointPrior_eq_of_measurePreserving_label_ae`, `continuousJointDecisionShare_le_of_measurePreserving_rule_indicator_ae`, `continuousJointClassifierMAE_le_of_measurePreserving_ae`, `sourceTransformationCertificate_of_measurePreserving_worstCaseEquality`, `sourceTransformationCertificate_of_measurePreserving_worstCaseEquality_product_scoreMeasurable`, `sourceTransformationCertificate_of_measurePreserving_featureMap_worstCaseEquality_product_scoreMeasurable`, `sourceTransformationCertificate_of_measurePreserving_worstCaseEquality_ae_mono`, `sourceTransformationCertificate_of_measurePreserving_targetBound_ae_mono`, `sourceTransformationCertificate_of_measurePreserving_targetBound_ae_mono_product_scoreBounded`, `sourceTransformationCertificate_of_measurePreserving_featureMap_targetBound_ae_mono_product_scoreBounded`, `sourceTransformationCertificate_of_measurePreserving_worstCaseEquality_ae_mono_finite`, `sourceTransformationCertificate_of_measurePreserving_worstCaseEquality_ae_mono_finite_scoreBounded`, `sourceTransformationCertificate_of_measurePreserving_worstCaseEquality_ae_mono_product_scoreBounded`, `sourceTransformationCertificate_of_measurePreserving_featureMap_worstCaseEquality_ae_mono_finite`, `sourceTransformationCertificate_of_measurePreserving_featureMap_worstCaseEquality_ae_mono_finite_scoreBounded`, `sourceTransformationCertificate_of_measurePreserving_featureMap_worstCaseEquality_ae_mono_product_scoreBounded`, `SourceWorstCaseEqualityCertificate`, `SourceTransformationCertificate` | formalized with caveat | `DSWG24DiscretizationBias/MainTheorems.lean` | The continuous MAE bound is proved from posterior-simplex, argmax, integrability, and calibration/consistency assumptions, with finite-simplex algebra deriving coordinate upper bounds, reusable uniform-score positivity/strictness facts, and a sharp `‖MAE‖ ≤ 1` helper, plus finite product-law continuous-calibration, conditional-expectation, conditional-kernel, finite-score, and source-region partition wrappers discharging the standard label/decision/score/MAE integrability and focal-region upper-bound obligations from measurability and simplex assumptions. `ConditionalExpectationKernelCalibration` implies `ConditionalExpectationCalibration` via Mathlib `condExpKernel`; `ConditionalExpectationCalibration` directly implies the prior equals the aggregate posterior and implies event-preimage plus positive-mass score-fiber calibration under label-indicator integrability; `FiniteScoreCalibration` proves the same prior equality by summing finite calibrated score fibers, with product-law fiber-integrability wrappers for measurable bin maps. Tightness has a concrete binary uniform-posterior witness. The source transformation route now has the non-atomic interval-cut balancing lemma for the `S_b`/`S_d` splits, feature-region mass algebra with feature-marginal, finite-law, and measurable-set integrability wrappers, five-region partition mass algebra proving the focal masses sum to the full/probability-one population mass, interval-to-score-mass preservation for real refinements, reduced `S_a/S_c/S_e` aggregate-posterior/decision-share/MAE identities, reduced-region worst-case equality certificates, composable and target-bound transformation certificates proving original bias is bounded by original MAE from the paper's preservation/monotonicity obligations, product-law exact, bounded-measurable, score-bounded, and product-score-bounded source-integrability helpers, and measure-preserving pushforward bridges that derive either exact preservation or a.e. prior-preservation/decision-nondecrease/MAE-nonincrease obligations from a concrete source map, including exact, score-bounded, product-score-bounded, same-law, reduced-target, calibrated reduced-target, original-calibration aggregate-preserved same-law targets, including integrated-MAE-delta variants, and one-step/two-step feature-map specializations and direct paper-facing endpoints that preserve labels by construction. The remaining arbitrary nonatomic map construction is isolated behind explicit map/partition obligations. |
| Theorem 2(i), joint rule maximizes `O_N^γ` | `paper_theorem2i_joint_optimization_rule_exists`, `paper_theorem2i_joint_optimization_rule_exists_finite_bayes`, `audit_theorem2i_joint_optimization_rule_exists`, `audit_theorem2i_joint_optimization_rule_exists_finite_bayes`, `paperExpectedONObjective`, `paperONObjective` | formalized | `DSWG24DiscretizationBias/MainTheorems.lean`, `EconCSLib/Foundations/Optimization/Argmax.lean`, `DSWG24DiscretizationBias/PostPaperAudit.lean` | None. The theorem is proved for the abstract finite-linear expectation interface under row-wise Bayes identities; the finite Bayes wrapper simply proves those identities from atom-level Bayes equations. |
| Theorem 2(ii), argmax is accuracy-maximizing for Bayes-optimal scores | `paper_theorem2ii_argmax_expected_accuracy_maximizing`, `paper_theorem2ii_argmax_expected_accuracy_maximizing_finite_bayes`, `audit_theorem2ii_argmax_expected_accuracy_maximizing`, `audit_theorem2ii_argmax_expected_accuracy_maximizing_finite_bayes` | formalized | `DSWG24DiscretizationBias/MainTheorems.lean`, `EconCSLib/Foundations/Optimization/Argmax.lean`, `DSWG24DiscretizationBias/PostPaperAudit.lean` | None; the expected-accuracy result uses the same row-wise Bayes identity formulation of Bayes optimality, and the finite Bayes wrapper is a discharger rather than an extra theorem-level assumption. |
| Theorem 2(ii), deterministic Bayes-score core | `paper_theorem2ii_argmax_accuracy_maximizing` | formalized | `DSWG24DiscretizationBias/MainTheorems.lean` | None; fixed observed dataset auxiliary support wrapper. |
| Theorem 2(iii), uniqueness/Pareto optimality of argmax among independent rules | `measureExpectedDatasetAccuracy`, `measureExpectedDatasetFidelity`, `integrable_measureDatasetAccuracyScore_of_ae_bound`, `integrable_measureDatasetFidelity_of_ae_bound`, `integrable_iidDatasetAccuracyScore_of_ae_bound`, `integrable_iidDatasetFidelity_of_ae_bound`, `integrable_iidKernelDatasetAccuracyScore_of_ae_bound`, `integrable_iidKernelDatasetFidelity_of_ae_bound`, `integral_lt_integral_of_ae_le_of_measure_setOf_lt_pos`, `iidSampleMeasure`, `allRowsSet`, `allDisagreementSet`, `augmentedAllDisagreementSet`, `randomizedKernelAugmentedLaw`, `randomizedKernelAugmentedLaw_univ_of_markov`, `randomizedKernelAugmentedLaw_univ_of_probability`, `kernelAllDisagreementSet`, `iidSampleMeasure_allRowsSet_pos_of_event_pos`, `iidSampleMeasure_allDisagreement_pos_of_event_pos`, `iidSampleMeasure_augmentedAllDisagreement_pos_of_event_pos`, `iidSampleMeasure_kernelAllDisagreement_pos_of_event_pos`, `not_measureExpectedDataset_pareto_of_positive_measure_event_dominated`, `not_measureExpectedDataset_weightedObjective_maximizer_of_positive_measure_event_dominated`, `not_measureExpectedDataset_weightedObjective_maximizer_of_positive_measure_event_strictly_dominated`, `not_measureExpectedDataset_pareto_of_iid_allRows_event_dominated`, `not_measureExpectedDataset_pareto_of_iid_allDisagreement_event_dominated`, `not_measureExpectedDataset_pareto_of_iid_augmented_allDisagreement_event_dominated`, `not_measureExpectedDataset_pareto_of_iid_kernel_allDisagreement_event_dominated`, `not_measureExpectedDataset_pareto_of_iid_kernel_allDisagreement_event_dominated_of_ae_bound`, `not_measureExpectedDataset_weightedObjective_maximizer_of_iid_augmented_allDisagreement_event_dominated`, `not_measureExpectedDataset_weightedObjective_maximizer_of_iid_augmented_allDisagreement_event_strictly_dominated`, `not_measureExpectedDataset_weightedObjective_maximizer_of_iid_kernel_allDisagreement_event_dominated`, `not_measureExpectedDataset_weightedObjective_maximizer_of_iid_kernel_allDisagreement_event_dominated_of_ae_bound`, `not_measureExpectedDataset_weightedObjective_maximizer_of_iid_kernel_allDisagreement_event_strictly_dominated`, `not_measureExpectedDataset_weightedObjective_maximizer_of_iid_kernel_allDisagreement_event_strictly_dominated_of_ae_bound`, `paper_theorem2iii_not_expected_pareto_of_independent_rule_disagrees_pos`, `paper_theorem2iii_not_expected_weightedObjective_maximizer_of_independent_rule_disagrees_pos`, `paper_theorem2iii_not_expected_weightedObjective_maximizer_of_independent_rule_disagrees_pos_strict_argmax`, `paper_theorem2iii_expected_accuracy_eq_of_independent_rule_agrees_ae`, `paper_theorem2iii_expected_fidelity_eq_of_independent_rule_agrees_ae`, `paper_theorem2iii_expected_weightedObjective_eq_of_independent_rule_agrees_ae`, `paper_theorem2iii_expected_weightedObjective_maximizer_iff_independent_rule_agrees_ae`, `paper_theorem2iii_not_expected_pareto_of_augmented_rule_disagrees_pos`, `paper_theorem2iii_not_expected_weightedObjective_maximizer_of_augmented_rule_disagrees_pos`, `paper_theorem2iii_not_expected_weightedObjective_maximizer_of_augmented_rule_disagrees_pos_strict_argmax` | formalized with caveat | `DSWG24DiscretizationBias/MainTheorems.lean` | Finite deterministic and augmented/randomized independent-rule bridges are formalized from positive disagreement probability. The literal `Measure.pi` iid product on `Fin N -> X` is formalized for measurable samples, including all-rows event mass, all-disagreement event positivity, augmented realized-randomness all-disagreement event positivity, and a Markov-kernel generated augmented law `μ ⊗ₘ κ` for randomized independent rules; the local kernel-law wrapper inherits finite/probability mass instances from Mathlib when the feature law and kernel are finite/Markov. The measure-integral expected-policy layer is also formalized: bounded-measurable integrability helpers discharge the expected accuracy/fidelity integrands under finite laws and finite-kernel generated iid laws; weak a.e. metric improvement plus strict improvement on a positive-measure event lifts to Pareto and weighted-objective non-maximality, with iid all-rows, all-disagreement, augmented all-disagreement, kernel-generated all-disagreement, and finite-kernel bounded-measurable specializations. The finite iid all-disagreement sample, over-allocated-label selection, one-row switch, expected-policy Pareto lift, and weighted-objective lift are discharged. Rules agreeing with argmax almost surely inherit expected accuracy, fidelity, and weighted objective, and a weighted-objective maximizer iff package is formalized under a supplied argmax-maximality certificate. Weighted objective wrappers cover `γ < 1` under weak argmax ties and `0 < γ ≤ 1` when disagreements are posterior-strict. Caveat: finite PMF, augmented-atom, augmented `Measure.pi`, and kernel-generated augmented-law wrappers cover realized randomized rules; more automatic measurability wrappers remain optional. |

Recent Theorem 1 source-route additions include `sourceSaSc_of_no_sourceSbSd_simplex_of_not_sourceSe`, `sourceSaSc_of_no_sourceSbSd_simplex_of_focal_pos`, `not_sourceSeRegion_of_argmax_focal_decision_of_exists_one`, `argmax_focal_decision_subset_sourceSaSc_of_no_sourceSbSd_simplex`, `SourceReducedUniformMiddleShape`, `sourceReducedUniformMiddle_obligations_of_shape_uniform_simplex`, and positive-focal/argmax-dispatched same-law endpoints
`paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_positiveFocal_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`,
`paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_positiveFocal_shape_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`,
`paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_argmaxRule_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`,
`paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_argmaxRule_shape_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`,
`paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_sameLaw_reducedSourceRegions_uniformMiddle_positiveFocal_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`, and
`paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_sameLaw_reducedSourceRegions_uniformMiddle_positiveFocal_shape_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`,
`paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_sameLaw_reducedSourceRegions_uniformMiddle_argmaxRule_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`, and
`paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_sameLaw_reducedSourceRegions_uniformMiddle_argmaxRule_shape_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex`.

## Source-Audit Notes

The cached PDF has two named theorems. The DAG has been checked against those
named source statements:

- `PostPaperAudit.lean` now imports the main theorem layer and exposes
  source-numbered audit endpoints for Theorem 1(i)--(iii), the Theorem 1(iii)
  tightness witness and source-transformation route, including the
  two-coordinate MAE and pointwise feature-map certificate seams, and
  Theorem 2(i)--(iii),
  together with raw finite/continuous formula abbreviations for bias, MAE, and
  the per-dataset objective.
- Theorem 1 now has compiling finite and continuous wrappers for the
  no-information formula, perfect-classifier zero-bias formula, MAE bound, and
  tightness witness. The continuous bound has Mathlib conditional-kernel,
  conditional-expectation, event-preimage, positive-mass score-fiber, and
  finite-score level-set calibration wrappers, including finite product-law
  conditional-expectation, conditional-kernel, and finite-score wrappers that
  discharge standard label/decision/score/MAE integrability obligations from
  measurability and boundedness, in addition to finite feature-space wrappers
  for the reusable `BayesianConsistent` bridge. The source proof route now also
  formalizes the focal-region partition, feature-region mass union algebra including
  feature-marginal and measurable-set integrability wrappers and the
  five-region total-mass/probability-one identity, and non-atomic real-interval
  cut used to balance the `S_b` and `S_d` transformations, weighted score-mass
  algebra, feature-marginal bridges, and finite/simplex wrappers proving those
  balance equations preserve the focal aggregate posterior on the split
  regions, with
  bounded-measurable and simplex finite-interval wrappers discharging cut
  integrability, the worst-case `a+c`, `a+(1/K)c`, `(1-1/K)c` algebra, and
  the transformation certificate that composes prior preservation, argmax-mass
  monotonicity, and MAE nonincrease into the final bound. The source
  interval-cut seam is now connected directly to product-measure balance,
  finite-label nonfocal and measurable feature selectors, interval
  selector/product-balance bridges, interval-cut-to-aggregate-delta endpoints,
  selector-to-aggregate-delta endpoints with finite-law integrability discharged,
  two-region actual-MAE-delta identities/nonpositive bridges,
  multiclass-safe collapse-to-focal MAE bridges, patched `S_b`
  collapse/lower-to-uniform and `S_d` raise-to-uniform/collapse aggregate
  bridges, constructed
  `S_b`/`S_d` interval and subset-sweep `qNext` MAE-delta endpoints,
  measurable simplex-valued `qNext` endpoints including multiclass-safe
  `S_b/S_d` interval and subset-sweep collapse endpoints that also preserve
  focal score mass on the split and the focal aggregate posterior, `qNext`
  shape-preservation bridges and reduced uniform-middle subset-shape
  combiners, coordinate-pushforward nonatomicity lemmas, coordinate-preimage
  integral transfer, coordinate-sweep `S_b/S_d` score-mass preservation, and
  coordinate-pullback constructed `S_b/S_d` `qNext` endpoints preserving focal
  aggregate posterior and nonpositive integrated MAE delta,
  binary `S_b/S_d` interval source-construction endpoints,
  nonnegative region-mass helpers, and feature-marginal score-mass preservation for `S_b` and `S_d` real
  refinements, and the reduced
  `S_a/S_c/S_e` endpoint has compiling aggregate-posterior, decision-share,
	  derived pointwise-MAE, two-coordinate MAE delta/nonincrease, balanced `S_b`
	  and threshold-balanced `S_d` aggregate-delta accounting, uniform-middle, and continuous-calibration
	  worst-case equality certificate wrappers.
  A measure-preserving
  pushforward bridge now turns a concrete source map with label/rule/MAE
  preservation, or the paper's a.e. prior-preservation/decision-nondecrease/
  MAE-nonincrease obligations, into that certificate; product-law exact,
  finite-law, score-bounded, and posterior-simplex wrappers discharge
  decision-indicator and MAE measurability/integrability obligations from
  bounded-measurable or score-coordinate hypotheses. The paper's informal
  continuous expansion is formalized as this explicit real-coordinate sweep;
  a fully abstract nonatomic transport/sweep theorem remains an optional future
  strengthening. The accepted coordinate version now constructs and pulls back
  the transformed posterior, rather than only proving score-mass balance.
  Pointwise feature-map
  wrappers reduce ordinary decision and MAE inequalities to the needed a.e.
  obligations; target-bound constructors and direct one-step/two-step
  score-bounded and simplex feature-map endpoints
  expose the sequential `S_b`/`S_d` reduction route, including product-law
  simplex feature-map endpoints whose target can be supplied by reduced source
  regions or by the paper's uniform-middle reduced shape rather than an
  abstract worst-case certificate. The accepted real-coordinate source route
  now constructs and pulls back the `S_b/S_d` transformed posteriors, preserving
  focal score mass, focal aggregate posterior, and nonpositive integrated MAE
  delta on the original joint law. The reduced-target route now also has
  calibrated one-step, calibrated two-step, same-law identity-map, and
  original-calibration aggregate-preserved same-law variants, including
  integrated-MAE-delta, canonical-rule/auto-fallback, and two-step delta-composition variants, for the concrete worst-case shape.
- Theorem 2(i)-(ii) now use the actual paper objective with expected true
  accuracy plus expected fidelity. The reusable bridge proves that row-wise
  Bayes identities imply the full tower-property equality for every joint rule,
  and `FiniteBayesDatasetModel.row_bayes` discharges those identities for finite
  atom-level Bayes models.
- Theorem 2(iii) now has the finite probabilistic independent-rule route:
  positive disagreement probability gives a target class with positive
  disagreement mass, iid sampling gives a positive-mass all-disagreement
  dataset, non-trivial reference mass forces an over-allocated current label,
  and a one-row switch lifts to expected-policy Pareto and weighted-objective
  non-optimality. The measure-theoretic iid product seam is also formalized:
  positive base-event measure gives positive mass to the `Measure.pi`
  all-disagreement event on `Fin N -> X`, and the measure-integral
  expected-policy lift has bounded-measurable integrability helpers, including
  finite-kernel generated iid wrappers, and turns a.e. weak improvement plus
  positive-measure strict improvement into Pareto and weighted-objective
  non-maximality. The augmented
  atom, measure-product, and Markov-kernel generated wrappers cover randomized
  independent rules by packaging features with realized rule randomness. A strict-argmax
  specialization covers the `γ = 1` accuracy-only boundary whenever every
  positive-probability disagreement is posterior-strict. The finite
  almost-sure agreement side is also packaged: rules agreeing with argmax with
  probability one inherit expected metrics and weighted-objective value, and
  weighted-objective maximality is equivalent to almost-sure argmax agreement
  under a supplied argmax maximality certificate.

## Optional Extensions

1. For Theorem 1, optionally construct the full arbitrary source nonatomic
   transformation map/partition beyond the accepted real-coordinate sweep,
   coordinate-pushforward nonatomicity bridge, real-interval cut,
   interval-to-score-mass bridge, nonfocal and measurable feature selectors,
   interval selector/product-balance bridges, interval-cut-to-aggregate-delta
   endpoints, selector-to-aggregate-delta endpoints, actual two-region MAE-delta
   bridges, constructed `S_b`/`S_d` interval and subset-sweep `qNext`
   endpoints, measurable simplex `qNext` endpoints including multiclass-safe
   `S_b/S_d` interval and subset-sweep collapse endpoints with focal
   score-mass and aggregate-posterior preservation, coordinate-pullback
   constructed `S_b/S_d` `qNext` endpoints, `qNext` shape-preservation
   and reduced uniform-middle subset-shape bridges, and binary `S_b/S_d` interval
   source-construction endpoints,
  reduced-region worst-case certificate, and measure-preserving
  exact/a.e.-monotone, pointwise paper-facing, same-law aggregate-preserved
  reduced-target including original-calibration, integrated-MAE-delta, and
  canonical-rule/auto-fallback variants, balanced `S_b`/`S_d`
   aggregate-delta, and aggregate-delta finite-law pushforward endpoints.
2. For Theorem 2(iii), optionally add more automatic measurability wrappers
   beyond the current finite PMF, augmented-atom, augmented/kernel
   `Measure.pi` iid event-positivity, bounded-integrability, and
   measure-integral expected-policy bridges.
