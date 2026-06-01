import GLM20DroppingStandardizedTesting.Theorem3SimplePremises
import GLM20DroppingStandardizedTesting.Theorem3SourceFamilyRows

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Theorem 3 source-family keep-test adapter: on the generated source-family
policy-state table, the two school-`J2` `(P_sub,P_full)` keep-test predicates
are exactly the two source component conditions (11)--(12).
-/
theorem
    paper_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_components
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritFallback fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2) {capacity2 : ℝ} :
    (glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB ∧
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA) ↔
      (subFullMass groupB ≥ capacity2 ∧
          populationShare groupB * subFullMeritFallback J2 groupB >
            populationShare groupA * subSubMerit J2 groupA +
              populationShare groupB * subSubMerit J2 groupB) ∧
        (subFullMass groupA ≥ capacity2 ∧
          populationShare groupA * subFullMeritFallback J2 groupA >
            populationShare groupA * subSubMerit J2 groupA +
              populationShare groupB * subSubMerit J2 groupB) := by
  have hJ2_ne_J1 : J2 ≠ J1 := by
    intro h
    exact hJ1_ne_J2 h.symm
  simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
    glm20Theorem3SourceFamilySubFullMeritTable,
    glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
      (paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_j2_keep_test_pair_iff_components
      api subEstimateLaw subSubMass subFullMass fullFullCutoff
      fullSubCutoff subSubMerit
      (glm20Theorem3SourceFamilySubFullMeritTable C J1 J1DropFamily
        J1DropThreshold subFullMeritFallback)
      (glm20Theorem3SourceFamilyFullSubMeritTable C J2 J2DropFamily
        J2DropThreshold fullSubMeritFallback)
      (glm20Theorem3SourceFamilyFullFullMeritTable C J1 J2 J1KeepFamily
        J2KeepFamily J1KeepThreshold J2KeepThreshold fullFullMeritFallback)
      diversity J1 J2 groupA groupB populationShare
      (capacity2 := capacity2))

/--
Theorem 3 source-family keep-test adapter, forward source-row direction.

This names the exact choke point for the remaining substantive condition
(11)--(12) work: once the two survivor mass lower bounds and the two strict
weighted survivor-merit comparisons are proved on the generated source-family
table, they feed the compact Theorem 3 route as the bundled school-`J2`
keep-test pair.
-/
theorem
    paper_theorem3_source_family_j2_keep_test_pair_of_base_survivor_rows
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritFallback fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2) {capacity2 : ℝ}
    (hJ2MassB : subFullMass groupB ≥ capacity2)
    (hJ2MeritGtB :
      populationShare groupB * subFullMeritFallback J2 groupB >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB)
    (hJ2MassA : subFullMass groupA ≥ capacity2)
    (hJ2MeritGtA :
      populationShare groupA * subFullMeritFallback J2 groupA >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB) :
    glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB ∧
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA :=
  (paper_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_components
      api subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
      diversity J1 J2 groupA groupB populationShare fullFullCutoff
      fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
      J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold hJ1_ne_J2 (capacity2 := capacity2)).mpr
    ⟨⟨hJ2MassB, hJ2MeritGtB⟩, ⟨hJ2MassA, hJ2MeritGtA⟩⟩

/--
The generated source-family school-`J2` keep-test pair implies the
strict-merit-only survivor rows used by feasibility-aware Theorem 3 routes.

The keep-test predicates still contain condition-(11)'s survivor capacity
facts, but this helper intentionally forgets them when the downstream theorem
already carries capacity through an explicit feasibility surface.
-/
theorem
    paper_theorem3_source_family_j2_strict_survivor_merit_rows_of_keep_test_pair
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritFallback fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2) {capacity2 : ℝ}
    (hJ2KeepPair :
      glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB ∧
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA) :
    GLM20Theorem3J2StrictSurvivorMeritRows populationShare subSubMerit
      subFullMeritFallback J2 groupA groupB := by
  have hcomponents :=
    (paper_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_components
      api subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
      diversity J1 J2 groupA groupB populationShare fullFullCutoff
      fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
      J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold hJ1_ne_J2 (capacity2 := capacity2)).mp hJ2KeepPair
  exact ⟨hcomponents.1.2, hcomponents.2.2⟩

/--
The generated source-family school-`J2` keep-test pair supplies the
strict-survivor row inside the compact public Theorem 3 row package.

This is the review-facing package bridge: all other public rows are passed in
as their named bundles, while the semantic source-family keep-test pair is
converted to the strict condition-(12) survivor-merit bundle.
-/
theorem
    paper_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_source_family_j2_keep_test_pair
    {FeatureDrop FeatureKeep HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype HighFreeFeature] [Fintype LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subEstimateLaw : GLM20Group → GaussianScaleLaw}
    {subSubMass subFullMass : GLM20Group → ℝ}
    {subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ}
    {diversity : GLM20School → GLM20StrategicPolicyState → ℝ}
    {J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop}
    {J1KeepFamily J2KeepFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureKeep}
    {J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ}
    {J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ}
    {fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature}
    {fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ}
    {fullSubLowFreeThreshold fullSubHighFreeThreshold : GLM20Group → ℝ}
    {fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature}
    {fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ}
    {fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
      fullSubHighBasedThresholdSlope : GLM20Group → ℝ}
    (C : GaussianHazardCertificate)
    (hkeepSignalRows :
      GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold)
    (hsubFullAffineTailRows :
      GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
        subFullLeftCost subFullRightCost subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold)
    (hfullSubGeneratedRows :
      GLM20Theorem3FullSubGeneratedRows testCost fullSubLeftCost
        fullSubRightCost fullSubHighFreeFamily fullSubFreeExtraNoiseMean
        fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
        fullSubHighFreeThreshold fullSubLowBasedFamily
        fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
        fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope)
    (hsubFullCostBounds :
      GLM20CostBoundsBelow testCost subFullLeftCost subFullRightCost
        subFullV2)
    (hcapacityCutoffRows :
      GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
        (glm20Theorem3PopulationShare pi) subEstimateLaw
        GLM20Group.groupA GLM20Group.groupB capacity1 capacity2
        q1Sub q2Sub fullFullCutoff)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hJ2KeepPair :
      glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface
            standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
            subSubMerit subFullMeritBase fullSubMeritFallback
            fullFullMeritFallback diversity glm20SchoolJ1 glm20SchoolJ2
            GLM20Group.groupA GLM20Group.groupB
            (glm20Theorem3PopulationShare pi) fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull glm20SchoolJ2
          GLM20Group.groupA GLM20Group.groupB
          (glm20Theorem3PopulationShare pi) capacity2 GLM20Group.groupB ∧
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface
            standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
            subSubMerit subFullMeritBase fullSubMeritFallback
            fullFullMeritFallback diversity glm20SchoolJ1 glm20SchoolJ2
            GLM20Group.groupA GLM20Group.groupB
            (glm20Theorem3PopulationShare pi) fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull glm20SchoolJ2
          GLM20Group.groupA GLM20Group.groupB
          (glm20Theorem3PopulationShare pi) capacity2 GLM20Group.groupA) :
    GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare
      testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost capacity1 capacity2 q1Sub q2Sub pi fullFullCutoff
      subEstimateLaw subSubMerit subFullMeritBase J1DropFamily J2DropFamily
      J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold subFullQ2Full subFullScale subFullV2
      subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold fullSubHighFreeFamily fullSubFreeExtraNoiseMean
      fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
      fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
      fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope := by
  have hJ2Strict :
      GLM20Theorem3J2StrictSurvivorMeritRows
        (glm20Theorem3PopulationShare pi) subSubMerit subFullMeritBase
        glm20SchoolJ2 GLM20Group.groupA GLM20Group.groupB :=
    paper_theorem3_source_family_j2_strict_survivor_merit_rows_of_keep_test_pair
      standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
      subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback diversity glm20SchoolJ1 glm20SchoolJ2
      GLM20Group.groupA GLM20Group.groupB
      (glm20Theorem3PopulationShare pi) fullFullCutoff fullSubCutoff C
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
      J1KeepThreshold J2DropThreshold J2KeepThreshold glm20SchoolJ1_ne_J2
      (capacity2 := capacity2) hJ2KeepPair
  let hrows :
      GLM20Theorem3AcademicMeritStrictSurvivorPublicRows testCost
        subFullLeftCost subFullRightCost fullSubLeftCost fullSubRightCost
        capacity1 capacity2 q1Sub q2Sub pi fullFullCutoff subEstimateLaw
        subSubMerit subFullMeritBase J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold J1KeepThreshold
        J2DropThreshold J2KeepThreshold subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold
        fullSubHighFreeFamily fullSubFreeExtraNoiseMean
        fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
        fullSubHighFreeThreshold fullSubLowBasedFamily
        fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
        fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope := {
    keepSignalRows := hkeepSignalRows
    subFullAffineTailRows := hsubFullAffineTailRows
    fullSubGeneratedRows := hfullSubGeneratedRows
    subFullCostBounds := hsubFullCostBounds
    capacityCutoffRows := hcapacityCutoffRows
    j2StrictSurvivorMeritRows := hJ2Strict
  }
  exact
    paper_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_rows
      hrows hpi

/--
Raw-source variant of
`paper_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_source_family_j2_keep_test_pair`.

This constructor keeps the source-family `J2` keep-test pair but expands the
full/sub generated-row package into primitive Gaussian prior
mean/variance/precision rows, affine threshold rows, and full/sub cost bounds.
-/
theorem
    paper_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_source_family_j2_keep_test_pair_and_fullSub_prior_precision_rows
    {FeatureDrop FeatureKeep HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype HighFreeFeature] [Fintype LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subEstimateLaw : GLM20Group → GaussianScaleLaw}
    {subSubMass subFullMass : GLM20Group → ℝ}
    {subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ}
    {diversity : GLM20School → GLM20StrategicPolicyState → ℝ}
    {J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop}
    {J1KeepFamily J2KeepFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureKeep}
    {J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ}
    {J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ}
    {fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature}
    {fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ}
    {fullSubLowFreeThreshold fullSubHighFreeThreshold : GLM20Group → ℝ}
    {fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature}
    {fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ}
    {fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
      fullSubHighBasedThresholdSlope : GLM20Group → ℝ}
    (C : GaussianHazardCertificate)
    (hkeepSignalRows :
      GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold)
    (hsubFullAffineTailRows :
      GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
        subFullLeftCost subFullRightCost subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold)
    (hfullSubFreeExtraNoiseVar :
      ∀ g, 0 < fullSubFreeExtraNoiseVar g)
    (hfullSubBasedExtraNoiseVar :
      ∀ g c, 0 < fullSubBasedExtraNoiseVar g c)
    (hfullSubLowPriorMean :
      ∀ g c,
        (fullSubLowBasedFamily g c).priorMean =
          ((fullSubHighFreeFamily g).withExtraSignal
            (fullSubFreeExtraNoiseMean g) (fullSubFreeExtraNoiseVar g)
            (hfullSubFreeExtraNoiseVar g)).priorMean)
    (hfullSubLowPriorVar :
      ∀ g c,
        (fullSubLowBasedFamily g c).priorVar =
          ((fullSubHighFreeFamily g).withExtraSignal
            (fullSubFreeExtraNoiseMean g) (fullSubFreeExtraNoiseVar g)
            (hfullSubFreeExtraNoiseVar g)).priorVar)
    (hfullSubLowPrecision :
      ∀ g c,
        (fullSubLowBasedFamily g c).centeredFamily.signalPrecisionSum =
          ((fullSubHighFreeFamily g).withExtraSignal
            (fullSubFreeExtraNoiseMean g) (fullSubFreeExtraNoiseVar g)
            (hfullSubFreeExtraNoiseVar g)).centeredFamily.signalPrecisionSum)
    (hfullSubHighPriorMean :
      ∀ g c,
        ((fullSubLowBasedFamily g c).withExtraSignal
          (fullSubBasedExtraNoiseMean g c)
          (fullSubBasedExtraNoiseVar g c)
          (hfullSubBasedExtraNoiseVar g c)).priorMean =
          (fullSubHighFreeFamily g).priorMean)
    (hfullSubHighPriorVar :
      ∀ g c,
        ((fullSubLowBasedFamily g c).withExtraSignal
          (fullSubBasedExtraNoiseMean g c)
          (fullSubBasedExtraNoiseVar g c)
          (hfullSubBasedExtraNoiseVar g c)).priorVar =
          (fullSubHighFreeFamily g).priorVar)
    (hfullSubHighPrecision :
      ∀ g c,
        ((fullSubLowBasedFamily g c).withExtraSignal
          (fullSubBasedExtraNoiseMean g c)
          (fullSubBasedExtraNoiseVar g c)
          (hfullSubBasedExtraNoiseVar g c)).centeredFamily.signalPrecisionSum =
          (fullSubHighFreeFamily g).centeredFamily.signalPrecisionSum)
    (hfullSubAffineThresholdRows :
      GLM20Theorem3FullSubAffineThresholdRows fullSubHighFreeFamily
        fullSubLowBasedFamily fullSubLeftCost fullSubRightCost
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope)
    (hfullSubCostBounds :
      GLM20CostBounds testCost fullSubLeftCost fullSubRightCost)
    (hsubFullCostBounds :
      GLM20CostBoundsBelow testCost subFullLeftCost subFullRightCost
        subFullV2)
    (hcapacityCutoffRows :
      GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
        (glm20Theorem3PopulationShare pi) subEstimateLaw
        GLM20Group.groupA GLM20Group.groupB capacity1 capacity2
        q1Sub q2Sub fullFullCutoff)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hJ2KeepPair :
      glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface
            standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
            subSubMerit subFullMeritBase fullSubMeritFallback
            fullFullMeritFallback diversity glm20SchoolJ1 glm20SchoolJ2
            GLM20Group.groupA GLM20Group.groupB
            (glm20Theorem3PopulationShare pi) fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull glm20SchoolJ2
          GLM20Group.groupA GLM20Group.groupB
          (glm20Theorem3PopulationShare pi) capacity2 GLM20Group.groupB ∧
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface
            standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
            subSubMerit subFullMeritBase fullSubMeritFallback
            fullFullMeritFallback diversity glm20SchoolJ1 glm20SchoolJ2
            GLM20Group.groupA GLM20Group.groupB
            (glm20Theorem3PopulationShare pi) fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull glm20SchoolJ2
          GLM20Group.groupA GLM20Group.groupB
          (glm20Theorem3PopulationShare pi) capacity2 GLM20Group.groupA) :
    GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare
      testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost capacity1 capacity2 q1Sub q2Sub pi fullFullCutoff
      subEstimateLaw subSubMerit subFullMeritBase J1DropFamily J2DropFamily
      J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold subFullQ2Full subFullScale subFullV2
      subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold fullSubHighFreeFamily fullSubFreeExtraNoiseMean
      fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
      fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
      fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope := by
  let hfullSubGeneratedRows :
      GLM20Theorem3FullSubGeneratedRows testCost fullSubLeftCost
        fullSubRightCost fullSubHighFreeFamily fullSubFreeExtraNoiseMean
        fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
        fullSubHighFreeThreshold fullSubLowBasedFamily
        fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
        fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope :=
    paper_theorem3_fullSub_generated_rows_of_prior_precision_rows
      hfullSubFreeExtraNoiseVar hfullSubBasedExtraNoiseVar
      hfullSubLowPriorMean hfullSubLowPriorVar hfullSubLowPrecision
      hfullSubHighPriorMean hfullSubHighPriorVar hfullSubHighPrecision
      hfullSubAffineThresholdRows hfullSubCostBounds
  exact
    paper_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_source_family_j2_keep_test_pair
      C hkeepSignalRows hsubFullAffineTailRows hfullSubGeneratedRows
      hsubFullCostBounds hcapacityCutoffRows hpi hJ2KeepPair

/--
The source-family and base component policy-state tables have the same
school-`J2` `(P_sub,P_full)` keep-test pair.  This lets the generated
source-family surface feed wrappers that still state condition-(11)--(12) on
the base table.
-/
theorem
    paper_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_base_table_keep_test_pair
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritFallback fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2) {capacity2 : ℝ} :
    (glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB ∧
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA) ↔
      (glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff subSubMerit subFullMeritFallback
            fullSubMeritFallback fullFullMeritFallback diversity J1 J2
            groupA groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB ∧
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff subSubMerit subFullMeritFallback
            fullSubMeritFallback fullFullMeritFallback diversity J1 J2
            groupA groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA) := by
  constructor
  · intro hsource
    have hcomponents :=
      (paper_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_components
        api subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold hJ1_ne_J2 (capacity2 := capacity2)).mp hsource
    exact
      (paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_j2_keep_test_pair_iff_components
        api subEstimateLaw subSubMass subFullMass fullFullCutoff
        fullSubCutoff subSubMerit subFullMeritFallback fullSubMeritFallback
        fullFullMeritFallback diversity J1 J2 groupA groupB populationShare
        (capacity2 := capacity2)).mpr hcomponents
  · intro hbase
    have hcomponents :=
      (paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_j2_keep_test_pair_iff_components
        api subEstimateLaw subSubMass subFullMass fullFullCutoff
        fullSubCutoff subSubMerit subFullMeritFallback fullSubMeritFallback
        fullFullMeritFallback diversity J1 J2 groupA groupB populationShare
        (capacity2 := capacity2)).mp hbase
    exact
      (paper_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_components
        api subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold hJ1_ne_J2 (capacity2 := capacity2)).mpr hcomponents

end

end GLM20DroppingStandardizedTesting
