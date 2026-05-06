import DSWG24DiscretizationBias.MainTheorems

/-!
# Post-Paper Audit: DSWG24 Discretization Bias

This file is the exhaustive importable audit ledger for the paper.  It gives
importable theorem aliases for the main paper claims and their supporting proof
seams.

For the compact human-facing Lean surface, use `PaperInterface.lean`: it lists
the paper definitions with formulas and direct theorem statements for Theorem 1
and Theorem 2's parts.  The aliases here intentionally point back to
`MainTheorems.lean`, where the full proof terms and supporting lemmas live.
-/

namespace DSWG24DiscretizationBias

open MeasureTheory

/-- Audit endpoint for Theorem 1(i), finite no-information bias. -/
abbrev audit_theorem1i_no_information_prior_bias :=
  @Finite.paper_theorem1i_no_information_prior_bias

/-- Audit endpoint for Theorem 1(i), continuous aggregate-bias form. -/
abbrev audit_theorem1i_continuous_no_information_aggregate_bias :=
  @ContinuousTheorem1.paper_theorem1i_continuous_no_information_aggregate_bias

/-- Audit endpoint for Theorem 1(ii), finite perfect-classifier zero bias. -/
abbrev audit_theorem1ii_perfect_classifier_prior_bias_zero :=
  @Finite.paper_theorem1ii_perfect_classifier_prior_bias_zero

/-- Audit endpoint for Theorem 1(ii), continuous perfect-classifier zero bias. -/
abbrev audit_theorem1ii_continuous_perfect_classifier_prior_bias_zero :=
  @ContinuousTheorem1.paper_theorem1ii_continuous_perfect_classifier_prior_bias_zero

/-- Audit endpoint for Theorem 1(iii), finite simplex argmax bias bound. -/
abbrev audit_theorem1iii_argmax_bias_le_mae_of_simplex :=
  @Finite.paper_theorem1iii_argmax_bias_le_mae_of_simplex

/-- Audit endpoint for Theorem 1(iii), continuous-calibration finite simplex bound. -/
abbrev audit_theorem1iii_continuousCalibration_finite_simplex :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_continuousCalibration_finite_simplex

/-- Audit endpoint for Theorem 1(iii), conditional-kernel finite simplex bound. -/
abbrev audit_theorem1iii_condExpKernelCalibration_finite_simplex :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_condExpKernelCalibration_finite_simplex

/--
Audit endpoint for the source-transformation route of Theorem 1(iii), using a
calibrated two-step reduced target.
-/
abbrev audit_theorem1iii_two_step_reduced_continuousCalibration :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_featureMap_sourceTransformations_reducedSourceRegions_continuousCalibration_product_simplex

/--
Audit endpoint for the pointwise source-transformation route of Theorem
1(iii), using a calibrated two-step reduced target.
-/
abbrev audit_theorem1iii_two_step_reduced_continuousCalibration_pointwise :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_featureMap_sourceTransformations_reducedSourceRegions_continuousCalibration_pointwise_product_simplex

/--
Audit endpoint for the aggregate-delta source-transformation route of Theorem
1(iii), using a calibrated two-step reduced target.
-/
abbrev audit_theorem1iii_two_step_reduced_continuousCalibration_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_featureMap_sourceTransformations_reducedSourceRegions_continuousCalibration_integral_delta_product_simplex

/--
Audit endpoint for the source-transformation route of Theorem 1(iii), using a
same-law calibrated reduced target.
-/
abbrev audit_theorem1iii_same_law_reduced_continuousCalibration :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_continuousCalibration_product_simplex

/--
Audit same-law reduced target endpoint where aggregate-posterior preservation
derives the target prior/aggregate identity.
-/
abbrev audit_theorem1iii_same_law_reduced_aggregate_preserved :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_aggregate_preserved_product_simplex

/--
Audit same-law uniform-middle endpoint where aggregate-posterior preservation
derives the target prior/aggregate identity.
-/
abbrev audit_theorem1iii_same_law_uniformMiddle_aggregate_preserved :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_aggregate_preserved_product_simplex

/--
Audit same-law reduced target endpoint using original continuous calibration
plus aggregate-posterior preservation of the transformed target.
-/
abbrev audit_theorem1iii_same_law_reduced_continuousCalibration_aggregate_preserved :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_continuousCalibration_aggregate_preserved_product_simplex

/--
Audit same-law uniform-middle endpoint using original continuous calibration
plus aggregate-posterior preservation of the transformed target.
-/
abbrev audit_theorem1iii_same_law_uniformMiddle_continuousCalibration_aggregate_preserved :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_continuousCalibration_aggregate_preserved_product_simplex

/--
Audit same-law worst-case endpoint using integrated MAE-delta accounting rather
than pointwise MAE monotonicity.
-/
abbrev audit_theorem1iii_same_law_worstCase_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_worstCaseEquality_integral_delta_product_simplex

/-- Audit same-law reduced-target endpoint using integrated MAE-delta accounting. -/
abbrev audit_theorem1iii_same_law_reduced_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_integral_delta_product_simplex

/-- Audit same-law uniform-middle endpoint using integrated MAE-delta accounting. -/
abbrev audit_theorem1iii_same_law_uniformMiddle_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_integral_delta_product_simplex

/--
Audit aggregate-preserved reduced target endpoint using integrated MAE-delta
accounting.
-/
abbrev audit_theorem1iii_same_law_reduced_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_aggregate_preserved_integral_delta_product_simplex

/--
Audit aggregate-preserved uniform-middle endpoint using integrated MAE-delta
accounting.
-/
abbrev audit_theorem1iii_same_law_uniformMiddle_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_aggregate_preserved_integral_delta_product_simplex

/--
Audit original-calibration aggregate-preserved reduced target endpoint using
integrated MAE-delta accounting.
-/
abbrev audit_theorem1iii_same_law_reduced_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/--
Audit original-calibration aggregate-preserved uniform-middle endpoint using
integrated MAE-delta accounting.
-/
abbrev audit_theorem1iii_same_law_uniformMiddle_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/-- Audit generic a.e. decision-indicator monotonicity from pointwise implication. -/
abbrev audit_theorem1iii_focal_decision_indicator_ae_le_of_imp :=
  @ContinuousTheorem1.focalDecisionIndicator_ae_le_of_imp

/-- Audit measurability of the canonical reduced-source decision rule. -/
abbrev audit_theorem1iii_measurable_source_reduced_decision_rule :=
  @ContinuousTheorem1.measurable_sourceReducedDecisionRule

/-- Audit the canonical reduced-source decision rule's focal decision shape. -/
abbrev audit_theorem1iii_source_reduced_decision_rule_eq_z_iff :=
  @ContinuousTheorem1.sourceReducedDecisionRule_eq_z_iff

/--
Audit decision-indicator monotonicity into the canonical reduced-source rule
from a source-region subset obligation.
-/
abbrev audit_theorem1iii_decision_indicator_le_source_reduced_rule_of_subset :=
  @ContinuousTheorem1.focalDecisionIndicator_ae_le_sourceReducedDecisionRule_of_subset

/--
Audit reduced-region bridge: after `S_b/S_d` elimination, non-`S_e` points are
in `S_a ∪ S_c`.
-/
abbrev audit_theorem1iii_sourceSaSc_of_no_sourceSbSd_not_sourceSe :=
  @ContinuousTheorem1.sourceSaSc_of_no_sourceSbSd_simplex_of_not_sourceSe

/--
Audit positive-focal bridge into the reduced decision region after
`S_b/S_d` elimination.
-/
abbrev audit_theorem1iii_sourceSaSc_of_no_sourceSbSd_focal_pos :=
  @ContinuousTheorem1.sourceSaSc_of_no_sourceSbSd_simplex_of_focal_pos

/--
Audit that an argmax rule cannot choose the focal class on an `S_e` point with
a perfect nonfocal class.
-/
abbrev audit_theorem1iii_not_sourceSe_of_argmax_focal_decision_perfect :=
  @ContinuousTheorem1.not_sourceSeRegion_of_argmax_focal_decision_of_exists_one

/--
Audit argmax discharge of the canonical reduced-rule subset obligation.
-/
abbrev audit_theorem1iii_argmax_decision_subset_sourceSaSc_of_no_sourceSbSd :=
  @ContinuousTheorem1.argmax_focal_decision_subset_sourceSaSc_of_no_sourceSbSd_simplex

/-- Audit final reduced uniform-middle pointwise-shape predicate. -/
abbrev audit_theorem1iii_source_reduced_uniformMiddle_shape :=
  @ContinuousTheorem1.SourceReducedUniformMiddleShape

/-- Audit final reduced uniform-middle single-point predicate. -/
abbrev audit_theorem1iii_source_reduced_uniformMiddle_point_shape :=
  @ContinuousTheorem1.SourceReducedUniformMiddlePointShape

/-- Audit the equivalence between global and pointwise reduced shape. -/
abbrev audit_theorem1iii_source_reduced_uniformMiddle_shape_iff_point :=
  @ContinuousTheorem1.sourceReducedUniformMiddleShape_iff_pointShape

/-- Audit focal one-hot points as terminal reduced-shape points. -/
abbrev audit_theorem1iii_source_reduced_uniformMiddle_point_focal_one :=
  @ContinuousTheorem1.sourceReducedUniformMiddlePointShape_of_focal_one_else_zero

/-- Audit nonfocal one-hot points as terminal reduced-shape points. -/
abbrev audit_theorem1iii_source_reduced_uniformMiddle_point_nonfocal_one :=
  @ContinuousTheorem1.sourceReducedUniformMiddlePointShape_of_nonfocal_one_else_zero

/-- Audit all-uniform points as terminal reduced-shape points. -/
abbrev audit_theorem1iii_source_reduced_uniformMiddle_point_all_uniform :=
  @ContinuousTheorem1.sourceReducedUniformMiddlePointShape_of_all_uniform

/-- Audit assembling reduced shape from a pointwise certificate. -/
abbrev audit_theorem1iii_source_reduced_uniformMiddle_shape_of_point :=
  @ContinuousTheorem1.sourceReducedUniformMiddleShape_of_pointShape

/-- Audit pointwise reduced-shape transfer across coordinatewise posterior equality. -/
abbrev audit_theorem1iii_source_reduced_uniformMiddle_point_shape_congr :=
  @ContinuousTheorem1.sourceReducedUniformMiddlePointShape_congr

/-- Audit reduced-shape transfer across coordinatewise posterior equality. -/
abbrev audit_theorem1iii_source_reduced_uniformMiddle_shape_congr :=
  @ContinuousTheorem1.sourceReducedUniformMiddleShape_congr

/-- Audit assembling reduced shape from two transformed pieces and an outside region. -/
abbrev audit_theorem1iii_source_reduced_uniformMiddle_shape_piecewise_two_sets :=
  @ContinuousTheorem1.sourceReducedUniformMiddleShape_of_piecewise_two_sets

/-- Audit assembling reduced shape when one piece is focal one-hot. -/
abbrev audit_theorem1iii_source_reduced_uniformMiddle_shape_focal_one_piecewise :=
  @ContinuousTheorem1.sourceReducedUniformMiddleShape_of_focal_one_piecewise_two_sets

/-- Audit assembling reduced shape when one piece is nonfocal one-hot. -/
abbrev audit_theorem1iii_source_reduced_uniformMiddle_shape_nonfocal_one_piecewise :=
  @ContinuousTheorem1.sourceReducedUniformMiddleShape_of_nonfocal_one_piecewise_two_sets

/--
Audit the `S_b` collapse interval shape combiner: the focal-one upper interval
is terminal, while the lower interval and outside region remain explicit.
-/
abbrev audit_theorem1iii_sourceSb_collapse_interval_uniformMiddle_shape_piecewise :=
  @ContinuousTheorem1.sourceReducedUniformMiddleShape_of_sourceSb_collapse_interval_piecewise

/--
Audit the `S_b` collapse subset-sweep shape combiner: the focal-one upper
swept subset is terminal, while the lower swept subset and outside region
remain explicit.
-/
abbrev audit_theorem1iii_sourceSb_collapse_subset_interval_uniformMiddle_shape_piecewise :=
  @ContinuousTheorem1.sourceReducedUniformMiddleShape_of_sourceSb_collapse_subset_interval_piecewise

/--
Audit the `S_d` collapse interval shape combiner: the nonfocal-one lower
interval is terminal, while the upper interval and outside region remain
explicit.
-/
abbrev audit_theorem1iii_sourceSd_collapse_interval_uniformMiddle_shape_piecewise :=
  @ContinuousTheorem1.sourceReducedUniformMiddleShape_of_sourceSd_collapse_interval_piecewise

/--
Audit the `S_d` collapse subset-sweep shape combiner: the nonfocal-one lower
swept subset is terminal, while the upper swept subset and outside region
remain explicit.
-/
abbrev audit_theorem1iii_sourceSd_collapse_subset_interval_uniformMiddle_shape_piecewise :=
  @ContinuousTheorem1.sourceReducedUniformMiddleShape_of_sourceSd_collapse_subset_interval_piecewise

/-- Audit the terminal point-shape fact for the `S_b` collapse upper interval. -/
abbrev audit_theorem1iii_sourceSb_collapse_upper_interval_point_shape :=
  @ContinuousTheorem1.sourceSb_collapse_upperInterval_reducedUniformMiddlePointShape

/-- Audit the terminal point-shape fact for the `S_b` collapse upper swept subset. -/
abbrev audit_theorem1iii_sourceSb_collapse_upper_subset_interval_point_shape :=
  @ContinuousTheorem1.sourceSb_collapse_upperSubsetInterval_reducedUniformMiddlePointShape

/-- Audit the terminal point-shape fact for the `S_d` collapse lower interval. -/
abbrev audit_theorem1iii_sourceSd_collapse_lower_interval_point_shape :=
  @ContinuousTheorem1.sourceSd_collapse_lowerInterval_reducedUniformMiddlePointShape

/-- Audit the terminal point-shape fact for the `S_d` collapse lower swept subset. -/
abbrev audit_theorem1iii_sourceSd_collapse_lower_subset_interval_point_shape :=
  @ContinuousTheorem1.sourceSd_collapse_lowerSubsetInterval_reducedUniformMiddlePointShape

/-- Audit `S_b` emptiness from the final reduced pointwise shape. -/
abbrev audit_theorem1iii_sourceSb_empty_of_reduced_uniformMiddle_shape :=
  @ContinuousTheorem1.sourceSbRegion_empty_of_reducedUniformMiddleShape

/-- Audit `S_d` emptiness from the final reduced pointwise shape. -/
abbrev audit_theorem1iii_sourceSd_empty_of_reduced_uniformMiddle_shape :=
  @ContinuousTheorem1.sourceSdRegion_empty_of_reducedUniformMiddleShape

/-- Audit uniformity on `S_c` from the final reduced pointwise shape. -/
abbrev audit_theorem1iii_sourceSc_uniform_of_reduced_uniformMiddle_shape :=
  @ContinuousTheorem1.sourceSc_uniform_of_reducedUniformMiddleShape

/-- Audit perfectness on `S_e` from the final reduced pointwise shape. -/
abbrev audit_theorem1iii_sourceSe_perfect_of_reduced_uniformMiddle_shape :=
  @ContinuousTheorem1.sourceSe_perfect_of_reducedUniformMiddleShape

/--
Audit bundled final reduced-shape obligations from the pointwise trichotomy.
-/
abbrev audit_theorem1iii_reduced_uniformMiddle_obligations_of_shape :=
  @ContinuousTheorem1.sourceReducedUniformMiddle_obligations_of_shape

/--
Audit bundled uniform-score final reduced-shape obligations from the pointwise
trichotomy.
-/
abbrev audit_theorem1iii_reduced_uniformMiddle_obligations_of_shape_uniform :=
  @ContinuousTheorem1.sourceReducedUniformMiddle_obligations_of_shape_uniform_simplex

/--
Audit reduced uniform-middle worst-case certificate from the final pointwise
shape.
-/
noncomputable abbrev audit_theorem1iii_source_worst_case_uniformMiddle_shape_certificate :=
  @ContinuousTheorem1.sourceWorstCaseEqualityCertificate_of_reduced_source_regions_uniformMiddle_shape

/--
Audit canonical-rule reduced uniform-middle worst-case certificate from the
final pointwise shape.
-/
noncomputable abbrev audit_theorem1iii_source_worst_case_uniformMiddle_shape_canonical_rule_certificate :=
  @ContinuousTheorem1.sourceWorstCaseEqualityCertificate_of_reduced_source_regions_uniformMiddle_shape_canonicalRule

/--
Audit worst-case bias/MAE equality from the final pointwise shape.
-/
abbrev audit_theorem1iii_source_worst_case_bias_eq_mae_uniformMiddle_shape :=
  @ContinuousTheorem1.sourceWorstCase_bias_eq_mae_of_reduced_source_regions_uniformMiddle_shape

/--
Audit canonical-rule reduced target endpoint: original calibration, aggregate
preservation, and integrated MAE-delta accounting.
-/
abbrev audit_theorem1iii_same_law_reduced_canonical_rule_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_canonicalRule_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/--
Audit canonical-rule uniform-middle endpoint: original calibration, aggregate
preservation, and integrated MAE-delta accounting.
-/
abbrev audit_theorem1iii_same_law_uniformMiddle_canonical_rule_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_canonicalRule_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/--
Audit uniform-middle canonical-rule endpoint where the fallback class is chosen
from `1 < #Y`.
-/
abbrev audit_theorem1iii_same_law_uniformMiddle_canonical_rule_autoFallback_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_canonicalRule_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/--
Audit uniform-middle endpoint where final argmax-ness discharges the canonical
decision-subset obligation.
-/
abbrev audit_theorem1iii_same_law_uniformMiddle_argmax_rule_autoFallback_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_argmaxRule_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/--
Audit uniform-middle endpoint where positive final focal posterior discharges
the canonical decision-subset obligation.
-/
abbrev audit_theorem1iii_same_law_uniformMiddle_positive_focal_autoFallback_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_positiveFocal_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/--
Audit positive-focal endpoint where the final reduced target shape is supplied
as a pointwise trichotomy.
-/
abbrev audit_theorem1iii_same_law_uniformMiddle_positive_focal_shape_autoFallback_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_positiveFocal_shape_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/--
Audit argmax-rule endpoint where the final reduced target shape is supplied as
a pointwise trichotomy.
-/
abbrev audit_theorem1iii_same_law_uniformMiddle_argmax_rule_shape_autoFallback_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_sameLaw_reducedSourceRegions_uniformMiddle_argmaxRule_shape_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/-- Audit composition of focal aggregate-posterior preservation. -/
abbrev audit_theorem1iii_aggregate_posterior_preservation_trans :=
  @ContinuousTheorem1.continuousJointAggregatePosterior_preserved_trans

/-- Audit composition of nonpositive integrated MAE deltas. -/
abbrev audit_theorem1iii_integral_mae_delta_nonpos_trans :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_nonpos_trans

/-- Audit finite-simplex composition of nonpositive integrated MAE deltas. -/
abbrev audit_theorem1iii_integral_mae_delta_nonpos_trans_simplex :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_nonpos_trans_simplex_finite

/--
Audit two-step same-law canonical-rule endpoint for sequential source
reductions.
-/
abbrev audit_theorem1iii_two_same_law_uniformMiddle_canonical_rule_autoFallback_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_sameLaw_reducedSourceRegions_uniformMiddle_canonicalRule_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/--
Audit two-step endpoint where final argmax-ness discharges the canonical
decision-subset obligation.
-/
abbrev audit_theorem1iii_two_same_law_uniformMiddle_argmax_rule_autoFallback_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_sameLaw_reducedSourceRegions_uniformMiddle_argmaxRule_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/--
Audit two-step endpoint where positive final focal posterior discharges the
canonical decision-subset obligation.
-/
abbrev audit_theorem1iii_two_same_law_uniformMiddle_positive_focal_autoFallback_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_sameLaw_reducedSourceRegions_uniformMiddle_positiveFocal_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/--
Audit two-step positive-focal endpoint where the final reduced target shape is
supplied as a pointwise trichotomy.
-/
abbrev audit_theorem1iii_two_same_law_uniformMiddle_positive_focal_shape_autoFallback_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_sameLaw_reducedSourceRegions_uniformMiddle_positiveFocal_shape_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/--
Audit two-step argmax-rule endpoint where the final reduced target shape is
supplied as a pointwise trichotomy.
-/
abbrev audit_theorem1iii_two_same_law_uniformMiddle_argmax_rule_shape_autoFallback_continuousCalibration_aggregate_preserved_integral_delta :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_two_sameLaw_reducedSourceRegions_uniformMiddle_argmaxRule_shape_autoFallback_continuousCalibration_aggregate_preserved_integral_delta_product_simplex

/-- Audit seam for the source proof's `S_b -> S_a` two-coordinate MAE move. -/
abbrev audit_theorem1iii_two_coordinate_raise_focal_to_one_mae_le :=
  @ContinuousTheorem1.paperConditionalMAE_twoCoordinate_raise_focal_to_one_le

/-- Audit multiclass-safe patched `S_b -> S_a` collapse-to-focal MAE move. -/
abbrev audit_theorem1iii_collapse_to_focal_one_mae_le :=
  @ContinuousTheorem1.paperConditionalMAE_collapse_to_focal_one_le

/-- Audit integrated region bridge for the patched collapse-to-focal move. -/
abbrev audit_theorem1iii_integral_collapse_to_focal_one_region_nonpos :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_collapse_to_focal_one_region_nonpos

/--
Audit patched aggregate `S_b` accounting using collapse-to-focal on the upper
piece and lower-to-uniform on the lower piece.
-/
abbrev audit_theorem1iii_sourceSb_collapse_lower_uniform_twoRegion_mae_delta_nonpos :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_sourceSb_collapse_toOne_lower_toUniform_twoRegion_nonpos

/-- Audit exact delta for the source proof's `S_b -> S_a` MAE move. -/
abbrev audit_theorem1iii_two_coordinate_raise_focal_to_one_mae_delta :=
  @ContinuousTheorem1.paperConditionalMAE_twoCoordinate_raise_focal_to_one_delta

/-- Audit integral delta for the source proof's `S_b -> S_a` MAE move. -/
abbrev audit_theorem1iii_integral_two_coordinate_raise_focal_to_one_mae_delta :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_twoCoordinate_raise_focal_to_one

/-- Audit aggregate nonpositive-delta bridge for the `S_b -> S_a` MAE move. -/
abbrev audit_theorem1iii_integral_two_coordinate_raise_focal_to_one_mae_nonpos :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_twoCoordinate_raise_focal_to_one_nonpos

/-- Audit exact delta for the source proof's `S_b -> S_c` MAE move. -/
abbrev audit_theorem1iii_two_coordinate_lower_focal_to_uniform_mae_delta :=
  @ContinuousTheorem1.paperConditionalMAE_twoCoordinate_lower_focal_to_uniform_delta

/-- Audit integral delta for the source proof's `S_b -> S_c` MAE move. -/
abbrev audit_theorem1iii_integral_two_coordinate_lower_focal_to_uniform_mae_delta :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_twoCoordinate_lower_focal_to_uniform

/-- Audit aggregate nonpositive-delta bridge for the `S_b -> S_c` MAE move. -/
abbrev audit_theorem1iii_integral_two_coordinate_lower_focal_to_uniform_mae_nonpos :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_twoCoordinate_lower_focal_to_uniform_nonpos

/--
Audit balanced-split aggregate MAE accounting for the source proof's combined
`S_b -> S_a` and `S_b -> S_c` moves.
-/
abbrev audit_theorem1iii_sourceSb_balanced_split_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_split_twoCoordinate_delta_integral_nonpos_of_balance

/-- Audit uniform-score specialization of balanced `S_b` aggregate MAE accounting. -/
abbrev audit_theorem1iii_sourceSb_balanced_split_uniform_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_split_twoCoordinate_delta_integral_nonpos_of_balance_uniform

/-- Audit region-subset version of balanced `S_b` aggregate MAE accounting. -/
abbrev audit_theorem1iii_sourceSb_balanced_split_region_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_split_twoCoordinate_delta_integral_nonpos_of_balance_region

/-- Audit uniform-score region-subset version of balanced `S_b` aggregate MAE accounting. -/
abbrev audit_theorem1iii_sourceSb_balanced_split_uniform_region_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_split_twoCoordinate_delta_integral_nonpos_of_balance_uniform_region

/--
Audit focal score-mass preservation for a piecewise `S_b` transformed posterior
with focal-one and uniform-score shapes.
-/
abbrev audit_theorem1iii_sourceSb_qNext_preserves_focal_score_mass_of_shapes :=
  @ContinuousTheorem1.sourceSb_qNext_preserves_focal_score_mass_of_shapes

/-- Audit global aggregate-posterior preservation from a preserved split. -/
abbrev audit_theorem1iii_aggregate_posterior_preserved_of_split_scoreMass_preserved :=
  @ContinuousTheorem1.continuousJointAggregatePosterior_eq_of_split_scoreMass_preserved

/-- Audit finite-simplex aggregate-posterior preservation from a preserved split. -/
abbrev audit_theorem1iii_aggregate_posterior_preserved_of_split_scoreMass_preserved_simplex :=
  @ContinuousTheorem1.continuousJointAggregatePosterior_eq_of_split_scoreMass_preserved_simplex_finite

/-- Audit target prior/aggregate identity from original calibration and aggregate preservation. -/
abbrev audit_theorem1iii_priorAggregate_of_aggregate_preserved :=
  @ContinuousTheorem1.continuousJointPrior_eq_jointAggregatePosterior_of_aggregate_preserved

/-- Audit reduced-region worst-case certificate from aggregate preservation. -/
noncomputable abbrev audit_theorem1iii_reduced_source_regions_aggregate_preserved_certificate :=
  @ContinuousTheorem1.sourceWorstCaseEqualityCertificate_of_reduced_source_regions_aggregate_preserved

/-- Audit uniform-middle reduced-region worst-case certificate from aggregate preservation. -/
noncomputable abbrev audit_theorem1iii_reduced_source_regions_uniformMiddle_aggregate_preserved_certificate :=
  @ContinuousTheorem1.sourceWorstCaseEqualityCertificate_of_reduced_source_regions_uniformMiddle_aggregate_preserved

/-- Audit nonfocal below-uniform selector for `S_b` source subregions. -/
abbrev audit_theorem1iii_sourceSb_nonfocal_selector_uniform :=
  @ContinuousTheorem1.exists_sourceSbRegion_nonfocal_selector_uniform_simplex

/-- Audit the generic subset-sweep interval balancing lemma. -/
abbrev audit_theorem1iii_subset_interval_balancing_cut :=
  @ContinuousTheorem1.exists_source_balancing_subset_interval_cut

/-- Audit nonatomicity preservation under injective measurable pushforward. -/
abbrev audit_theorem1iii_noAtoms_map_of_injective :=
  @ContinuousTheorem1.noAtoms_map_of_injective

/-- Audit nonatomicity preservation under measurable embeddings. -/
abbrev audit_theorem1iii_noAtoms_map_of_measurableEmbedding :=
  @ContinuousTheorem1.noAtoms_map_of_measurableEmbedding

/-- Audit coordinate-pushforward nonatomicity for embedded feature coordinates. -/
abbrev audit_theorem1iii_noAtoms_featureCoordinate_map_of_measurableEmbedding :=
  @ContinuousTheorem1.noAtoms_featureCoordinate_map_of_measurableEmbedding

/-- Audit finite coordinate-interval mass for finite product laws. -/
abbrev audit_theorem1iii_featureCoordinate_map_Icc_lt_top :=
  @ContinuousTheorem1.featureCoordinate_map_Icc_lt_top

/-- Audit integral transfer across a measurable real coordinate. -/
abbrev audit_theorem1iii_integral_coordinate_preimage_indicator_eq_map_integral :=
  @ContinuousTheorem1.integral_coordinate_preimage_indicator_eq_map_integral

/-- Audit the coordinate-label joint pushforward map. -/
abbrev audit_theorem1iii_featureCoordinateJointMap :=
  @ContinuousTheorem1.featureCoordinateJointMap

/-- Audit measurability of the coordinate-label joint pushforward map. -/
abbrev audit_theorem1iii_measurable_featureCoordinateJointMap :=
  @ContinuousTheorem1.measurable_featureCoordinateJointMap

/-- Audit the feature marginal identity after coordinate-label pushforward. -/
abbrev audit_theorem1iii_featureCoordinateJointMap_fst_marginal :=
  @ContinuousTheorem1.featureCoordinateJointMap_fst_marginal

/-- Audit paper-MAE factorization through a real feature coordinate. -/
abbrev audit_theorem1iii_paperConditionalMAE_featureCoordinate_factor :=
  @ContinuousTheorem1.paperConditionalMAE_featureCoordinate_factor

/-- Audit aggregate-posterior pullback through a real feature coordinate. -/
abbrev audit_theorem1iii_continuousJointAggregatePosterior_featureCoordinate_pullback :=
  @ContinuousTheorem1.continuousJointAggregatePosterior_featureCoordinate_pullback

/-- Audit weighted feature-mass pullback through a real feature coordinate. -/
abbrev audit_theorem1iii_jointFeatureSetWeightedMass_featureCoordinate_pullback :=
  @ContinuousTheorem1.jointFeatureSetWeightedMass_featureCoordinate_pullback

/-- Audit feature-set mass pullback through a real feature coordinate. -/
abbrev audit_theorem1iii_jointFeatureSetMass_featureCoordinate_pullback :=
  @ContinuousTheorem1.jointFeatureSetMass_featureCoordinate_pullback

/-- Audit focal score-mass pullback through a real feature coordinate. -/
abbrev audit_theorem1iii_jointFeatureSetScoreMass_featureCoordinate_pullback :=
  @ContinuousTheorem1.jointFeatureSetScoreMass_featureCoordinate_pullback

/-- Audit integrated MAE-delta pullback through a real feature coordinate. -/
abbrev audit_theorem1iii_integral_paperConditionalMAE_delta_featureCoordinate_pullback :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_featureCoordinate_pullback

/-- Audit coordinate-sweep `S_b` focal score-mass preservation. -/
abbrev audit_theorem1iii_sourceSb_coordinate_subset_interval_focal_score_mass_preserved :=
  @ContinuousTheorem1.sourceSb_coordinate_subset_interval_split_preserves_focal_score_mass_simplex_finite

/-- Audit coordinate-sweep `S_d` focal score-mass preservation. -/
abbrev audit_theorem1iii_sourceSd_coordinate_subset_interval_focal_score_mass_preserved :=
  @ContinuousTheorem1.sourceSd_coordinate_subset_interval_split_preserves_focal_score_mass_simplex_finite

/-- Audit coordinate-pullback constructive `S_b` source transformation. -/
abbrev audit_theorem1iii_sourceSb_coordinate_constructed_qNext_collapse_simplex_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_coordinate_subset_interval_split_exists_feature_qNext_collapse_simplex_mae_delta_nonpos_uniform_simplex_finite

/-- Audit coordinate-pullback constructive `S_d` source transformation. -/
abbrev audit_theorem1iii_sourceSd_coordinate_constructed_qNext_collapse_simplex_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_coordinate_subset_interval_split_exists_feature_qNext_collapse_simplex_mae_delta_nonpos_uniform_simplex_finite

/-- Audit subset-sweep `S_b` balancing on an arbitrary subregion of an interval. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_balancing_cut :=
  @ContinuousTheorem1.exists_source_Sb_balancing_subset_interval_cut_of_region_subset

/-- Audit bounded-measurable subset-sweep `S_b` balancing. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_balancing_cut_measurable_bounded :=
  @ContinuousTheorem1.exists_source_Sb_balancing_subset_interval_cut_of_region_subset_measurable_bounded

/-- Audit simplex subset-sweep `S_b` balancing. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_balancing_cut_simplex :=
  @ContinuousTheorem1.exists_source_Sb_balancing_subset_interval_cut_of_region_subset_measurable_simplex

/-- Audit uniform-score simplex subset-sweep `S_b` balancing. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_balancing_cut_uniform_simplex :=
  @ContinuousTheorem1.exists_source_Sb_balancing_subset_interval_cut_of_region_subset_uniform_simplex

/-- Audit subset-sweep `S_b` focal score-mass preservation. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_focal_score_mass_preserved :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_preserves_focal_score_mass_simplex_finite

/-- Audit subset-sweep `S_b` focal score-mass preservation for a shaped `qNext`. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_qNext_focal_score_mass_preserved :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_qNext_preserves_focal_score_mass_simplex_finite

/-- Audit subset-sweep `S_b` aggregate preservation for a shaped `qNext`. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_qNext_aggregate_preserved :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_aggregate_preserved_of_shapes_simplex_finite

/-- Audit subset-sweep `S_b` product-measure balance. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_product_balance :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_product_balance_simplex_finite

/-- Audit subset-sweep `S_b` product balance with a nonfocal selector. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_selector_product_balance :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_exists_nonfocal_selector_product_balance_simplex_finite

/-- Audit feature-level measurable selector for subset-sweep `S_b` product balance. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_measurable_feature_selector_product_balance :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_exists_measurable_feature_nonfocal_selector_product_balance_simplex_finite

/-- Audit measurable product-space selector for subset-sweep `S_b` product balance. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_measurable_selector_product_balance :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_exists_measurable_nonfocal_selector_product_balance_simplex_finite

/-- Audit product-measure balance bridge for the source proof's `S_b` interval split. -/
abbrev audit_theorem1iii_sourceSb_interval_product_balance :=
  @ContinuousTheorem1.sourceSb_interval_split_product_balance_simplex_finite

/-- Audit interval split returning both `S_b` product balance and a nonfocal selector. -/
abbrev audit_theorem1iii_sourceSb_interval_selector_product_balance :=
  @ContinuousTheorem1.sourceSb_interval_split_exists_nonfocal_selector_product_balance_simplex_finite

/-- Audit feature-level measurable nonfocal selector for `S_b` interval product balance. -/
abbrev audit_theorem1iii_sourceSb_interval_measurable_feature_selector_product_balance :=
  @ContinuousTheorem1.sourceSb_interval_split_exists_measurable_feature_nonfocal_selector_product_balance_simplex_finite

/-- Audit measurable nonfocal selector for `S_b` interval product balance. -/
abbrev audit_theorem1iii_sourceSb_interval_measurable_selector_product_balance :=
  @ContinuousTheorem1.sourceSb_interval_split_exists_measurable_nonfocal_selector_product_balance_simplex_finite

/--
Audit interval-cut-to-aggregate-delta bridge for the source proof's `S_b`
split.
-/
abbrev audit_theorem1iii_sourceSb_interval_aggregate_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_interval_split_twoCoordinate_delta_integral_nonpos_uniform_simplex_finite

/--
Audit subset-sweep aggregate-delta bridge for the source proof's `S_b` split.
-/
abbrev audit_theorem1iii_sourceSb_subset_interval_aggregate_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_twoCoordinate_delta_integral_nonpos_uniform_simplex_finite

/--
Audit measurable-selector subset-sweep aggregate-delta endpoint for `S_b`.
-/
abbrev audit_theorem1iii_sourceSb_subset_interval_measurable_selector_aggregate_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_exists_measurable_nonfocal_twoCoordinate_delta_integral_nonpos_uniform_simplex_finite

/--
Audit interval split returning an `S_b` nonfocal selector and aggregate
nonpositive MAE delta.
-/
abbrev audit_theorem1iii_sourceSb_interval_selector_aggregate_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_interval_split_exists_nonfocal_twoCoordinate_delta_integral_nonpos_uniform_simplex_finite

/--
Audit measurable-selector `S_b` interval aggregate-delta endpoint with
integrability discharged from finite-law simplex bounds.
-/
abbrev audit_theorem1iii_sourceSb_interval_measurable_selector_aggregate_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_interval_split_exists_measurable_nonfocal_twoCoordinate_delta_integral_nonpos_uniform_simplex_finite

/-- Audit exact actual-MAE delta identity for a two-piece `S_b` transformation. -/
abbrev audit_theorem1iii_sourceSb_twoRegion_actual_mae_delta :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_sourceSb_twoRegion

/-- Audit nonpositive actual-MAE delta bridge for a two-piece `S_b` transformation. -/
abbrev audit_theorem1iii_sourceSb_twoRegion_actual_mae_delta_nonpos :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_sourceSb_twoRegion_nonpos

/-- Audit `S_b` interval endpoint for a supplied piecewise transformed posterior. -/
abbrev audit_theorem1iii_sourceSb_interval_actual_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_interval_split_exists_measurable_nonfocal_twoRegion_mae_delta_nonpos_uniform_simplex_finite

/-- Audit subset-sweep `S_b` endpoint for a supplied piecewise transformed posterior. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_actual_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_exists_measurable_nonfocal_twoRegion_mae_delta_nonpos_uniform_simplex_finite

/-- Audit constructive `S_b` interval endpoint returning a piecewise `qNext`. -/
abbrev audit_theorem1iii_sourceSb_interval_constructed_qNext_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_interval_split_exists_measurable_feature_qNext_mae_delta_nonpos_uniform_simplex_finite

/-- Audit constructive subset-sweep `S_b` endpoint returning a piecewise `qNext`. -/
abbrev audit_theorem1iii_sourceSb_subset_interval_constructed_qNext_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_exists_measurable_feature_qNext_mae_delta_nonpos_uniform_simplex_finite

/--
Audit constructive `S_b` interval endpoint returning a measurable simplex
`qNext`, with the single-coordinate feasibility condition explicit.
-/
abbrev audit_theorem1iii_sourceSb_interval_constructed_qNext_simplex_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_interval_split_exists_measurable_feature_qNext_simplex_mae_delta_nonpos_uniform_simplex_finite

/--
Audit constructive subset-sweep `S_b` endpoint returning a measurable simplex
`qNext`, with the single-coordinate feasibility condition explicit.
-/
abbrev audit_theorem1iii_sourceSb_subset_interval_constructed_qNext_simplex_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_exists_measurable_feature_qNext_simplex_mae_delta_nonpos_uniform_simplex_finite

/--
Audit multiclass-safe constructive `S_b` interval endpoint returning a
measurable simplex `qNext` via collapse-to-focal on the upper interval.
-/
abbrev audit_theorem1iii_sourceSb_interval_constructed_qNext_collapse_simplex_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_interval_split_exists_measurable_feature_qNext_collapse_simplex_mae_delta_nonpos_uniform_simplex_finite

/--
Audit multiclass-safe constructive subset-sweep `S_b` endpoint returning a
measurable simplex `qNext` via collapse-to-focal on the upper swept subset.
-/
abbrev audit_theorem1iii_sourceSb_subset_interval_constructed_qNext_collapse_simplex_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSb_subset_interval_split_exists_measurable_feature_qNext_collapse_simplex_mae_delta_nonpos_uniform_simplex_finite

/-- Audit binary complement identity for the source proof's nonfocal coordinate. -/
abbrev audit_theorem1iii_binary_nonfocal_eq_one_sub_focal :=
  @ContinuousTheorem1.posterior_nonfocal_eq_one_sub_focal_of_card_two

/-- Audit binary `S_b` interval endpoint returning a measurable simplex `qNext`. -/
abbrev audit_theorem1iii_sourceSb_interval_constructed_qNext_simplex_mae_delta_nonpos_binary :=
  @ContinuousTheorem1.sourceSb_interval_split_exists_measurable_feature_qNext_simplex_mae_delta_nonpos_binary_uniform_simplex_finite

/-- Audit product-indicator nonnegative integral helper for source split masses. -/
abbrev audit_theorem1iii_fst_preimage_indicator_integral_nonneg :=
  @ContinuousTheorem1.integral_fst_preimage_indicator_nonneg

/-- Audit nonnegative `1 - q_z` mass on `S_b` subregions. -/
abbrev audit_theorem1iii_sourceSb_deficitToOne_integral_nonneg :=
  @ContinuousTheorem1.sourceSbRegion_deficitToOne_fst_preimage_integral_nonneg

/-- Audit exact delta for the source proof's `S_d -> S_c` MAE move. -/
abbrev audit_theorem1iii_two_coordinate_raise_focal_to_uniform_mae_delta :=
  @ContinuousTheorem1.paperConditionalMAE_twoCoordinate_raise_focal_to_uniform_delta

/-- Audit integral delta for the source proof's `S_d -> S_c` MAE move. -/
abbrev audit_theorem1iii_integral_two_coordinate_raise_focal_to_uniform_mae_delta :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_twoCoordinate_raise_focal_to_uniform

/-- Audit aggregate nonpositive-delta bridge for the `S_d -> S_c` MAE move. -/
abbrev audit_theorem1iii_integral_two_coordinate_raise_focal_to_uniform_mae_nonpos :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_twoCoordinate_raise_focal_to_uniform_nonpos

/-- Audit seam for the source proof's `S_d -> S_e` two-coordinate MAE move. -/
abbrev audit_theorem1iii_two_coordinate_lower_focal_to_zero_mae_le :=
  @ContinuousTheorem1.paperConditionalMAE_twoCoordinate_lower_focal_to_zero_le

/-- Audit exact delta for the source proof's `S_d -> S_e` MAE move. -/
abbrev audit_theorem1iii_two_coordinate_lower_focal_to_zero_mae_delta :=
  @ContinuousTheorem1.paperConditionalMAE_twoCoordinate_lower_focal_to_zero_delta

/-- Audit integral delta for the source proof's `S_d -> S_e` MAE move. -/
abbrev audit_theorem1iii_integral_two_coordinate_lower_focal_to_zero_mae_delta :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_twoCoordinate_lower_focal_to_zero

/-- Audit aggregate nonpositive-delta bridge for the `S_d -> S_e` MAE move. -/
abbrev audit_theorem1iii_integral_two_coordinate_lower_focal_to_zero_mae_nonpos :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_twoCoordinate_lower_focal_to_zero_nonpos

/--
Audit balanced-threshold aggregate MAE accounting for the source proof's combined
`S_d -> S_c` and `S_d -> S_e` moves.
-/
abbrev audit_theorem1iii_sourceSd_balanced_split_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_split_twoCoordinate_delta_integral_nonpos_of_balance

/--
Audit subset-sweep aggregate-delta bridge for the source proof's `S_d` split.
-/
abbrev audit_theorem1iii_sourceSd_subset_interval_aggregate_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_twoCoordinate_delta_integral_nonpos_uniform_simplex_finite

/--
Audit measurable-selector subset-sweep aggregate-delta endpoint for `S_d`.
-/
abbrev audit_theorem1iii_sourceSd_subset_interval_measurable_selector_aggregate_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_exists_measurable_nonfocal_twoCoordinate_delta_integral_nonpos_uniform_simplex_finite

/-- Audit region-subset version of threshold-balanced `S_d` aggregate MAE accounting. -/
abbrev audit_theorem1iii_sourceSd_balanced_split_region_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_split_twoCoordinate_delta_integral_nonpos_of_balance_region

/--
Audit patched aggregate `S_d` accounting using raise-to-uniform on the upper
piece and collapse-to-nonfocal on the lower piece.
-/
abbrev audit_theorem1iii_sourceSd_raise_uniform_collapse_nonfocal_twoRegion_mae_delta_nonpos :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_sourceSd_raise_toUniform_collapseNonfocal_twoRegion_nonpos

/--
Audit focal score-mass preservation for a piecewise `S_d` transformed posterior
with uniform-score and focal-zero shapes.
-/
abbrev audit_theorem1iii_sourceSd_qNext_preserves_focal_score_mass_of_shapes :=
  @ContinuousTheorem1.sourceSd_qNext_preserves_focal_score_mass_of_shapes

/-- Audit nonfocal above-uniform selector for `S_d` source subregions. -/
abbrev audit_theorem1iii_sourceSd_nonfocal_selector_uniform :=
  @ContinuousTheorem1.exists_sourceSdRegion_nonfocal_selector_uniform_simplex

/-- Audit subset-sweep `S_d` balancing on an arbitrary subregion of an interval. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_balancing_cut :=
  @ContinuousTheorem1.exists_source_Sd_balancing_subset_interval_cut_of_region_subset

/-- Audit bounded-measurable subset-sweep `S_d` balancing. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_balancing_cut_measurable_bounded :=
  @ContinuousTheorem1.exists_source_Sd_balancing_subset_interval_cut_of_region_subset_measurable_bounded

/-- Audit simplex subset-sweep `S_d` balancing. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_balancing_cut_simplex :=
  @ContinuousTheorem1.exists_source_Sd_balancing_subset_interval_cut_of_region_subset_measurable_simplex

/-- Audit uniform-score simplex subset-sweep `S_d` balancing. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_balancing_cut_uniform_simplex :=
  @ContinuousTheorem1.exists_source_Sd_balancing_subset_interval_cut_of_region_subset_uniform_simplex

/-- Audit subset-sweep `S_d` focal score-mass preservation. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_focal_score_mass_preserved :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_preserves_focal_score_mass_simplex_finite

/-- Audit subset-sweep `S_d` focal score-mass preservation for a shaped `qNext`. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_qNext_focal_score_mass_preserved :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_qNext_preserves_focal_score_mass_simplex_finite

/-- Audit subset-sweep `S_d` aggregate preservation for a shaped `qNext`. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_qNext_aggregate_preserved :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_aggregate_preserved_of_shapes_simplex_finite

/-- Audit subset-sweep `S_d` product-measure balance. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_product_balance :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_product_balance_simplex_finite

/-- Audit subset-sweep `S_d` product balance with a nonfocal selector. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_selector_product_balance :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_exists_nonfocal_selector_product_balance_simplex_finite

/-- Audit feature-level measurable selector for subset-sweep `S_d` product balance. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_measurable_feature_selector_product_balance :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_exists_measurable_feature_nonfocal_selector_product_balance_simplex_finite

/-- Audit measurable product-space selector for subset-sweep `S_d` product balance. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_measurable_selector_product_balance :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_exists_measurable_nonfocal_selector_product_balance_simplex_finite

/-- Audit product-measure balance bridge for the source proof's `S_d` interval split. -/
abbrev audit_theorem1iii_sourceSd_interval_product_balance :=
  @ContinuousTheorem1.sourceSd_interval_split_product_balance_simplex_finite

/-- Audit interval split returning both `S_d` product balance and a nonfocal selector. -/
abbrev audit_theorem1iii_sourceSd_interval_selector_product_balance :=
  @ContinuousTheorem1.sourceSd_interval_split_exists_nonfocal_selector_product_balance_simplex_finite

/-- Audit feature-level measurable nonfocal selector for `S_d` interval product balance. -/
abbrev audit_theorem1iii_sourceSd_interval_measurable_feature_selector_product_balance :=
  @ContinuousTheorem1.sourceSd_interval_split_exists_measurable_feature_nonfocal_selector_product_balance_simplex_finite

/-- Audit measurable nonfocal selector for `S_d` interval product balance. -/
abbrev audit_theorem1iii_sourceSd_interval_measurable_selector_product_balance :=
  @ContinuousTheorem1.sourceSd_interval_split_exists_measurable_nonfocal_selector_product_balance_simplex_finite

/--
Audit interval-cut-to-aggregate-delta bridge for the source proof's `S_d`
split.
-/
abbrev audit_theorem1iii_sourceSd_interval_aggregate_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_interval_split_twoCoordinate_delta_integral_nonpos_uniform_simplex_finite

/--
Audit interval split returning an `S_d` nonfocal selector and aggregate
nonpositive MAE delta.
-/
abbrev audit_theorem1iii_sourceSd_interval_selector_aggregate_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_interval_split_exists_nonfocal_twoCoordinate_delta_integral_nonpos_uniform_simplex_finite

/--
Audit measurable-selector `S_d` interval aggregate-delta endpoint with
integrability discharged from finite-law simplex bounds and threshold
comparisons left explicit.
-/
abbrev audit_theorem1iii_sourceSd_interval_measurable_selector_aggregate_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_interval_split_exists_measurable_nonfocal_twoCoordinate_delta_integral_nonpos_uniform_simplex_finite

/-- Audit exact actual-MAE delta identity for a two-piece `S_d` transformation. -/
abbrev audit_theorem1iii_sourceSd_twoRegion_actual_mae_delta :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_sourceSd_twoRegion

/-- Audit nonpositive actual-MAE delta bridge for a two-piece `S_d` transformation. -/
abbrev audit_theorem1iii_sourceSd_twoRegion_actual_mae_delta_nonpos :=
  @ContinuousTheorem1.integral_paperConditionalMAE_delta_sourceSd_twoRegion_nonpos

/-- Audit `S_d` interval endpoint for a supplied piecewise transformed posterior. -/
abbrev audit_theorem1iii_sourceSd_interval_actual_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_interval_split_exists_measurable_nonfocal_twoRegion_mae_delta_nonpos_uniform_simplex_finite

/-- Audit subset-sweep `S_d` endpoint for a supplied piecewise transformed posterior. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_actual_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_exists_measurable_nonfocal_twoRegion_mae_delta_nonpos_uniform_simplex_finite

/-- Audit constructive `S_d` interval endpoint returning a piecewise `qNext`. -/
abbrev audit_theorem1iii_sourceSd_interval_constructed_qNext_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_interval_split_exists_measurable_feature_qNext_mae_delta_nonpos_uniform_simplex_finite

/-- Audit constructive subset-sweep `S_d` endpoint returning a piecewise `qNext`. -/
abbrev audit_theorem1iii_sourceSd_subset_interval_constructed_qNext_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_exists_measurable_feature_qNext_mae_delta_nonpos_uniform_simplex_finite

/--
Audit constructive `S_d` interval endpoint returning a measurable simplex
`qNext`, with the aggregate threshold comparisons explicit.
-/
abbrev audit_theorem1iii_sourceSd_interval_constructed_qNext_simplex_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_interval_split_exists_measurable_feature_qNext_simplex_mae_delta_nonpos_uniform_simplex_finite

/--
Audit constructive subset-sweep `S_d` endpoint returning a measurable simplex
`qNext`, with the aggregate threshold comparisons explicit.
-/
abbrev audit_theorem1iii_sourceSd_subset_interval_constructed_qNext_simplex_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_exists_measurable_feature_qNext_simplex_mae_delta_nonpos_uniform_simplex_finite

/--
Audit multiclass-safe constructive `S_d` interval endpoint returning a
measurable simplex `qNext` via collapse-to-nonfocal on the lower interval.
-/
abbrev audit_theorem1iii_sourceSd_interval_constructed_qNext_collapse_simplex_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_interval_split_exists_measurable_feature_qNext_collapse_simplex_mae_delta_nonpos_uniform_simplex_finite

/--
Audit multiclass-safe constructive subset-sweep `S_d` endpoint returning a
measurable simplex `qNext` via collapse-to-nonfocal on the lower swept subset.
-/
abbrev audit_theorem1iii_sourceSd_subset_interval_constructed_qNext_collapse_simplex_mae_delta_nonpos :=
  @ContinuousTheorem1.sourceSd_subset_interval_split_exists_measurable_feature_qNext_collapse_simplex_mae_delta_nonpos_uniform_simplex_finite

/-- Audit binary `S_d` interval endpoint returning a measurable simplex `qNext`. -/
abbrev audit_theorem1iii_sourceSd_interval_constructed_qNext_simplex_mae_delta_nonpos_binary :=
  @ContinuousTheorem1.sourceSd_interval_split_exists_measurable_feature_qNext_simplex_mae_delta_nonpos_binary_uniform_simplex_finite

/-- Audit nonnegative focal score mass on `S_d` subregions. -/
abbrev audit_theorem1iii_sourceSd_score_integral_nonneg :=
  @ContinuousTheorem1.sourceSdRegion_score_fst_preimage_integral_nonneg

/-- Audit nonnegative `u - q_z` mass on `S_d` subregions. -/
abbrev audit_theorem1iii_sourceSd_deficitToUniform_integral_nonneg :=
  @ContinuousTheorem1.sourceSdRegion_deficitToUniform_fst_preimage_integral_nonneg

/-- Audit seam for pointwise feature-map certificates into a worst-case target. -/
abbrev audit_theorem1iii_pointwise_featureMap_worstCase_certificate :=
  @ContinuousTheorem1.sourceTransformationCertificate_of_measurePreserving_featureMap_worstCaseEquality_pointwise_product_simplex

/-- Audit endpoint for pointwise feature-map transformations into a worst-case target. -/
abbrev audit_theorem1iii_pointwise_featureMap_worstCase_endpoint :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_featureMap_worstCaseEquality_pointwise_product_simplex

/--
Audit endpoint for aggregate-delta feature-map transformations into a worst-case
target.
-/
abbrev audit_theorem1iii_integral_delta_featureMap_worstCase_endpoint :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_featureMap_worstCaseEquality_integral_delta_product_simplex

/--
Audit endpoint for pointwise feature-map transformations into a calibrated
reduced target.
-/
abbrev audit_theorem1iii_pointwise_featureMap_reduced_continuousCalibration_endpoint :=
  @ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_featureMap_reducedSourceRegions_continuousCalibration_pointwise_product_simplex

/-- Audit seam for pointwise feature-map certificates with a supplied target bound. -/
abbrev audit_theorem1iii_pointwise_featureMap_targetBound_certificate :=
  @ContinuousTheorem1.sourceTransformationCertificate_of_measurePreserving_featureMap_targetBound_pointwise_product_simplex

/-- Audit seam for aggregate MAE-delta accounting under a measure-preserving map. -/
abbrev audit_theorem1iii_integral_delta_mae_mono :=
  @ContinuousTheorem1.continuousJointClassifierMAE_le_of_measurePreserving_integral_delta

/--
Audit seam for feature-map source certificates whose MAE monotonicity is proved
by a nonpositive integrated delta.
-/
abbrev audit_theorem1iii_integral_delta_featureMap_targetBound_certificate :=
  @ContinuousTheorem1.sourceTransformationCertificate_of_measurePreserving_featureMap_targetBound_integral_delta_product_simplex

/--
Audit seam for feature-map source certificates into a worst-case target whose
MAE monotonicity is proved by a nonpositive integrated delta.
-/
abbrev audit_theorem1iii_integral_delta_featureMap_worstCase_certificate :=
  @ContinuousTheorem1.sourceTransformationCertificate_of_measurePreserving_featureMap_worstCaseEquality_integral_delta_product_simplex

/-- Audit endpoint for the tight binary uniform witness in Theorem 1(iii). -/
abbrev audit_theorem1iii_tight_binary_uniform_example :=
  @Finite.paper_theorem1iii_tight_binary_uniform_example

/-- Audit endpoint for Theorem 2(i), joint-rule existence under Bayes row identities. -/
abbrev audit_theorem2i_joint_optimization_rule_exists :=
  @paper_theorem2i_joint_optimization_rule_exists

/-- Audit endpoint discharging Theorem 2(i)'s Bayes row identities for finite PMFs. -/
abbrev audit_theorem2i_joint_optimization_rule_exists_finite_bayes :=
  @paper_theorem2i_joint_optimization_rule_exists_finite_bayes

/-- Audit endpoint for Theorem 2(ii), argmax accuracy optimality under Bayes row identities. -/
abbrev audit_theorem2ii_argmax_expected_accuracy_maximizing :=
  @paper_theorem2ii_argmax_expected_accuracy_maximizing

/-- Audit endpoint discharging Theorem 2(ii)'s Bayes row identities for finite PMFs. -/
abbrev audit_theorem2ii_argmax_expected_accuracy_maximizing_finite_bayes :=
  @paper_theorem2ii_argmax_expected_accuracy_maximizing_finite_bayes

/--
Audit endpoint for Theorem 2(iii), expected weighted-objective maximality iff
the independent rule agrees with argmax almost surely.
-/
abbrev audit_theorem2iii_expected_weightedObjective_maximizer_iff_independent_rule_agrees_ae :=
  @Theorem2iii.paper_theorem2iii_expected_weightedObjective_maximizer_iff_independent_rule_agrees_ae

/--
Audit endpoint for Theorem 2(iii), non-maximality of any positive-probability
disagreement under `γ < 1`.
-/
abbrev audit_theorem2iii_not_expected_weightedObjective_maximizer_of_independent_rule_disagrees_pos :=
  @Theorem2iii.paper_theorem2iii_not_expected_weightedObjective_maximizer_of_independent_rule_disagrees_pos

/--
Audit endpoint for Theorem 2(iii), non-maximality at the `γ = 1` boundary under
posterior-strict disagreements.
-/
abbrev audit_theorem2iii_not_expected_weightedObjective_maximizer_of_independent_rule_disagrees_pos_strict_argmax :=
  @Theorem2iii.paper_theorem2iii_not_expected_weightedObjective_maximizer_of_independent_rule_disagrees_pos_strict_argmax

/--
Audit endpoint for Theorem 2(iii), augmented/randomized independent-rule
non-Pareto conclusion from positive disagreement probability.
-/
abbrev audit_theorem2iii_not_expected_pareto_of_augmented_rule_disagrees_pos :=
  @Theorem2iii.paper_theorem2iii_not_expected_pareto_of_augmented_rule_disagrees_pos

end DSWG24DiscretizationBias
