import GLM20DroppingStandardizedTesting.Theorem3ConstructedComponents

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Theorem 3 support: the named school-`J2` keep-test predicate on the concrete
policy-state table exposes exactly the raw condition-(11)--(12) survivor
components.

This is the reusable reverse direction of
`paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_otherGroupKeepsTest_of_components`.
-/
theorem
    paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_components_of_otherGroupKeepsTest
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (subSubMerit subFullMerit fullSubMerit fullFullMerit :
      School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB survivingGroup : Group)
    (populationShare : Group → ℝ) {capacity2 : ℝ}
    (hkeep :
      glm20Theorem3SubFullOtherGroupKeepsTest
        (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface api
          subEstimateLaw subSubMass subFullMass fullFullCutoff fullSubCutoff
          subSubMerit subFullMerit fullSubMerit fullFullMerit diversity J1
          J2 groupA groupB populationShare)
        glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull J2 groupA groupB
        populationShare capacity2 survivingGroup) :
    subFullMass survivingGroup ≥ capacity2 ∧
      populationShare survivingGroup * subFullMerit J2 survivingGroup >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB :=
    (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface_subFull_otherGroupKeepsTest_iff_components
      api subEstimateLaw subSubMass subFullMass fullFullCutoff
      fullSubCutoff subSubMerit subFullMerit fullSubMerit fullFullMerit
      diversity J1 J2 groupA groupB survivingGroup populationShare
      (capacity2 := capacity2)).mp hkeep

/--
Standard-Gaussian feasibility-aware Theorem 3 endpoint with school-`J2`
condition-(11)--(12) stated as named keep-test predicates.

The existing feasibility-aware route still consumes only the strict survivor
merit inequalities: the survivor capacity sides are already built into the
feasibility hypothesis.  This bridge extracts the merit inequalities from the
named keep-test predicates and then applies the existing raw-survivor endpoint.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval_of_j2_keeps_test
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost subFullLeftCost subFullRightCost
      fullSubLeftCost fullSubRightCost : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2)
    (hJ1PriorMean :
      ∀ g, (J1DropFamily g).priorMean = (J1KeepFamily g).priorMean)
    (hJ1PriorVar :
      ∀ g, (J1DropFamily g).priorVar = (J1KeepFamily g).priorVar)
    (hJ1Precision :
      ∀ g,
        (J1DropFamily g).centeredFamily.signalPrecisionSum <
          (J1KeepFamily g).centeredFamily.signalPrecisionSum)
    (hJ1ThresholdMean :
      ∀ g, (J1DropFamily g).priorMean < J1DropThreshold g)
    (hJ1Threshold :
      ∀ g, J1DropThreshold g ≤ J1KeepThreshold g)
    (hJ2PriorMean :
      ∀ g, (J2DropFamily g).priorMean = (J2KeepFamily g).priorMean)
    (hJ2PriorVar :
      ∀ g, (J2DropFamily g).priorVar = (J2KeepFamily g).priorVar)
    (hJ2Precision :
      ∀ g,
        (J2DropFamily g).centeredFamily.signalPrecisionSum <
          (J2KeepFamily g).centeredFamily.signalPrecisionSum)
    (hJ2ThresholdMean :
      ∀ g, (J2DropFamily g).priorMean < J2DropThreshold g)
    (hJ2Threshold :
      ∀ g, J2DropThreshold g ≤ J2KeepThreshold g)
    {subFullQ2Full subFullScale subFullV2 : Group → ℝ}
    {fullSubLowQ1Full fullSubLowQ2Full fullSubLowScale fullSubLowV1
      fullSubLowV2 : Group → ℝ}
    {fullSubHighQ1Full fullSubHighQ2Full fullSubHighScale fullSubHighV1
      fullSubHighV2 : Group → ℝ}
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (fullSubLowMeritOfCutoff fullSubHighMeritOfCutoff :
      Group → ℝ → ℝ)
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
    (hsubFullLeftRight :
      ∀ g, subFullLeftCost g < subFullRightCost g)
    (hsubFullLeftPos : ∀ g, 0 < subFullLeftCost g)
    (hsubFullRightLtV2 :
      ∀ g, subFullRightCost g < subFullV2 g)
    (hsubFullCostMem :
      ∀ g, testCost g ∈
        Set.Icc (subFullLeftCost g) (subFullRightCost g))
    (hsubFullScale : ∀ g, 0 < subFullScale g)
    (hsubFullMeritCont :
      ∀ g, Continuous (subFullMeritOfCutoff g))
    (hsubFullMeritAnti :
      ∀ g, StrictAnti (subFullMeritOfCutoff g))
    (hsubFullAtLeft :
      ∀ g, subFullTestFreeMerit g <
        subFullMeritOfCutoff g
          (subFullQ2Full g -
            subFullScale g *
              standardGaussianQuantileAPI.quantile
                (1 - subFullLeftCost g / subFullV2 g)))
    (hsubFullAtRight :
      ∀ g,
        subFullMeritOfCutoff g
            (subFullQ2Full g -
              subFullScale g *
                standardGaussianQuantileAPI.quantile
                  (1 - subFullRightCost g / subFullV2 g)) <
          subFullTestFreeMerit g)
    (hfullSubLeftRight :
      ∀ g, fullSubLeftCost g < fullSubRightCost g)
    (hfullSubLeftPos : ∀ g, 0 < fullSubLeftCost g)
    (hfullSubCostMem :
      ∀ g, testCost g ∈
        Set.Icc (fullSubLeftCost g) (fullSubRightCost g))
    (hfullSubLowScale : ∀ g, 0 < fullSubLowScale g)
    (hfullSubLowV2Pos : ∀ g, 0 < fullSubLowV2 g)
    (hfullSubLowV2LtV1 : ∀ g, fullSubLowV2 g < fullSubLowV1 g)
    (hfullSubLowRightLtV1 :
      ∀ g, fullSubRightCost g < fullSubLowV1 g)
    (hfullSubLowMeritCont :
      ∀ g, Continuous (fullSubLowMeritOfCutoff g))
    (hfullSubLowMeritAnti :
      ∀ g, StrictAnti (fullSubLowMeritOfCutoff g))
    (hfullSubHighScale : ∀ g, 0 < fullSubHighScale g)
    (hfullSubHighV2Pos : ∀ g, 0 < fullSubHighV2 g)
    (hfullSubHighV2LtV1 :
      ∀ g, fullSubHighV2 g < fullSubHighV1 g)
    (hfullSubHighRightLtV1 :
      ∀ g, fullSubRightCost g < fullSubHighV1 g)
    (hfullSubHighMeritCont :
      ∀ g, Continuous (fullSubHighMeritOfCutoff g))
    (hfullSubHighMeritAnti :
      ∀ g, StrictAnti (fullSubHighMeritOfCutoff g))
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
    (hcapacity1 :
      capacity1 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupA) q1Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupB) q1Sub)
    (hfillFullFull1 :
      capacity1 ≤
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupA) (fullFullCutoff groupA) +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupB) (fullFullCutoff groupB))
    (hcapacity2 :
      capacity2 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupA) q2Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupB) q2Sub)
    (hfillFullFull2 :
      capacity2 ≤
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupA) (fullFullCutoff groupA) +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupB) (fullFullCutoff groupB)) :=
  let tableSurface :=
    glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface
      standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
      fullFullCutoff fullSubCutoff subSubMerit subFullMeritBase
      fullSubMeritFallback fullFullMeritFallback diversity J1 J2 groupA
      groupB populationShare
  let endpoint :=
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval_of_raw_survivor_merits
      subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback
      diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost) (capacity1 := capacity1)
      (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
      (feasible1 := feasible1) (feasible2 := feasible2)
      (subFullQ2Full := subFullQ2Full)
      (subFullScale := subFullScale) (subFullV2 := subFullV2)
      (fullSubLowQ1Full := fullSubLowQ1Full)
      (fullSubLowQ2Full := fullSubLowQ2Full)
      (fullSubLowScale := fullSubLowScale)
      (fullSubLowV1 := fullSubLowV1)
      (fullSubLowV2 := fullSubLowV2)
      (fullSubHighQ1Full := fullSubHighQ1Full)
      (fullSubHighQ2Full := fullSubHighQ2Full)
      (fullSubHighScale := fullSubHighScale)
      (fullSubHighV1 := fullSubHighV1)
      (fullSubHighV2 := fullSubHighV2)
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision
      hJ2ThresholdMean hJ2Threshold subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowMeritOfCutoff
      fullSubHighMeritOfCutoff fullSubLowTestFreeMerit
      fullSubHighTestFreeMerit hsubFullLeftRight hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullScale
      hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft
      hsubFullAtRight hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
      hfullSubLowScale hfullSubLowV2Pos hfullSubLowV2LtV1
      hfullSubLowRightLtV1 hfullSubLowMeritCont hfullSubLowMeritAnti
      hfullSubHighScale hfullSubHighV2Pos hfullSubHighV2LtV1
      hfullSubHighRightLtV1 hfullSubHighMeritCont
      hfullSubHighMeritAnti hshareA hshareB hcapacity1 hfillFullFull1
      hcapacity2 hfillFullFull2
  fun hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight hfullSubHighAtLowRoot
      (hJ2KeepsB :
        glm20Theorem3SubFullOtherGroupKeepsTest tableSurface
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB)
      (hJ2KeepsA :
        glm20Theorem3SubFullOtherGroupKeepsTest tableSurface
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA) =>
    let hB :=
      paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_components_of_otherGroupKeepsTest
        standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
        fullFullCutoff fullSubCutoff subSubMerit subFullMeritBase
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2 groupA
        groupB groupB populationShare (capacity2 := capacity2) hJ2KeepsB
    let hA :=
      paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_components_of_otherGroupKeepsTest
        standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
        fullFullCutoff fullSubCutoff subSubMerit subFullMeritBase
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2 groupA
        groupB groupA populationShare (capacity2 := capacity2) hJ2KeepsA
    endpoint hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight hfullSubHighAtLowRoot hB.2 hA.2

end

end GLM20DroppingStandardizedTesting
