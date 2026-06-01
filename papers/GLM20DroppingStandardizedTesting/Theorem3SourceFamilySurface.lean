import GLM20DroppingStandardizedTesting.PaperSurfaceWrappers
import GLM20DroppingStandardizedTesting.Theorem3SourceFamilyKeepTest

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Theorem 3 posterior-family source-free endpoint with school `J2` keep-test
predicates stated on the generated source-family policy-state table.

This has the same mathematical content as
`paper_theorem3_posterior_mean_fullSub_source_free_merits_of_j2_keeps_test`,
but lets callers supply the final condition-(11)--(12) keep-test pair on
`glm20Theorem3SourceFamilyPolicyStateTableSurface`.  The body converts that
pair to the base component table and then calls the existing source-free
wrapper.
-/
abbrev
    paper_theorem3_posterior_mean_fullSub_source_free_merits_of_source_family_j2_keeps_test
    {Group School FeatureDrop FeatureKeep LowFreeFeature HighFreeFeature
      LowBasedFeature HighBasedFeature : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
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
    (C : GaussianHazardCertificate)
    (fullSubLowFreeFamily :
      Group → GaussianOffsetSignalFamily LowFreeFeature)
    (fullSubHighFreeFamily :
      Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold : Group → ℝ)
    (fullSubLowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubHighBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (fullSubLowBasedThreshold fullSubHighBasedThreshold :
      Group → ℝ → ℝ)
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
  let sourceTableSurface :=
    glm20Theorem3SourceFamilyPolicyStateTableSurface
      standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
      subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback diversity J1 J2 groupA groupB
      populationShare fullFullCutoff fullSubCutoff C J1DropFamily
      J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
      J1KeepThreshold J2DropThreshold J2KeepThreshold
  let base :=
    paper_theorem3_posterior_mean_fullSub_source_free_merits_of_j2_keeps_test
      subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
      fullSubMeritFallback fullFullMeritFallback diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (capacity1 := capacity1) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hJ1_ne_J2 hJ1PriorMean hJ1PriorVar
      hJ1Precision hJ1ThresholdMean hJ1Threshold hJ2PriorMean
      hJ2PriorVar hJ2Precision hJ2ThresholdMean hJ2Threshold
      (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
      (subFullV2 := subFullV2) (fullSubLowQ1Full := fullSubLowQ1Full)
      (fullSubLowQ2Full := fullSubLowQ2Full)
      (fullSubLowScale := fullSubLowScale)
      (fullSubLowV1 := fullSubLowV1) (fullSubLowV2 := fullSubLowV2)
      (fullSubHighQ1Full := fullSubHighQ1Full)
      (fullSubHighQ2Full := fullSubHighQ2Full)
      (fullSubHighScale := fullSubHighScale)
      (fullSubHighV1 := fullSubHighV1)
      (fullSubHighV2 := fullSubHighV2) subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowMeritOfCutoff
      fullSubHighMeritOfCutoff C fullSubLowFreeFamily
      fullSubHighFreeFamily fullSubLowFreeThreshold
      fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubHighBasedFamily fullSubLowBasedThreshold
      fullSubHighBasedThreshold hsubFullLeftRight hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullScale
      hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight
      hfullSubLeftRight hfullSubLeftPos hfullSubCostMem hfullSubLowScale
      hfullSubLowV2Pos hfullSubLowV2LtV1 hfullSubLowRightLtV1
      hfullSubLowMeritCont hfullSubLowMeritAnti hfullSubHighScale
      hfullSubHighV2Pos hfullSubHighV2LtV1 hfullSubHighRightLtV1
      hfullSubHighMeritCont hfullSubHighMeritAnti hshareA hshareB
      hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
  fun hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight
      (hfullSubFreePriorMean :
        ∀ g,
          (fullSubHighFreeFamily g).priorMean =
            (fullSubLowFreeFamily g).priorMean)
      (hfullSubFreePriorVar :
        ∀ g,
          (fullSubHighFreeFamily g).priorVar =
            (fullSubLowFreeFamily g).priorVar)
      (hfullSubFreePrecision :
        ∀ g,
          (fullSubHighFreeFamily g).centeredFamily.signalPrecisionSum <
            (fullSubLowFreeFamily g).centeredFamily.signalPrecisionSum)
      (hfullSubFreeThresholdMean :
        ∀ g,
          (fullSubHighFreeFamily g).priorMean <
            fullSubHighFreeThreshold g)
      (hfullSubFreeThreshold :
        ∀ g, fullSubHighFreeThreshold g ≤ fullSubLowFreeThreshold g)
      hfullSubLowBasedFormula hfullSubHighBasedFormula
      (hfullSubBasedPriorMean :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          (fullSubLowBasedFamily g c).priorMean =
            (fullSubHighBasedFamily g c).priorMean)
      (hfullSubBasedPriorVar :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          (fullSubLowBasedFamily g c).priorVar =
            (fullSubHighBasedFamily g c).priorVar)
      (hfullSubBasedPrecision :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          (fullSubLowBasedFamily g c).centeredFamily.signalPrecisionSum <
            (fullSubHighBasedFamily g c).centeredFamily.signalPrecisionSum)
      (hfullSubBasedThresholdMean :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          (fullSubLowBasedFamily g c).priorMean <
            fullSubLowBasedThreshold g c)
      (hfullSubBasedThreshold :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubLowBasedThreshold g c ≤ fullSubHighBasedThreshold g c)
      (hJ2KeepsB :
        glm20Theorem3SubFullOtherGroupKeepsTest sourceTableSurface
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB)
      (hJ2KeepsA :
        glm20Theorem3SubFullOtherGroupKeepsTest sourceTableSurface
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA) =>
    let hbasePair :=
      (paper_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_base_table_keep_test_pair
        standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
        subSubMerit subFullMeritBase fullSubMeritFallback
        fullFullMeritFallback diversity J1 J2 groupA groupB
        populationShare fullFullCutoff fullSubCutoff C J1DropFamily
        J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold hJ1_ne_J2
        (capacity2 := capacity2)).mp ⟨hJ2KeepsB, hJ2KeepsA⟩
    base hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight hfullSubFreePriorMean hfullSubFreePriorVar
      hfullSubFreePrecision hfullSubFreeThresholdMean
      hfullSubFreeThreshold hfullSubLowBasedFormula
      hfullSubHighBasedFormula hfullSubBasedPriorMean
      hfullSubBasedPriorVar hfullSubBasedPrecision
      hfullSubBasedThresholdMean hfullSubBasedThreshold hbasePair.1
      hbasePair.2

/--
Standard-Gaussian specialization of the generated-table keep-test Theorem 3
route.

This is the same surface as
`paper_theorem3_posterior_mean_fullSub_source_free_merits_of_source_family_j2_keeps_test`,
but the Gaussian hazard certificate is fixed internally to the repository's
standard-Gaussian certificate.
-/
abbrev
    paper_theorem3_standardGaussian_posterior_mean_fullSub_source_free_merits_of_source_family_j2_keeps_test
    {Group School FeatureDrop FeatureKeep LowFreeFeature HighFreeFeature
      LowBasedFeature HighBasedFeature : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost subFullLeftCost subFullRightCost
      fullSubLeftCost fullSubRightCost : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : Group → ℝ}
    {fullSubLowQ1Full fullSubLowQ2Full fullSubLowScale fullSubLowV1
      fullSubLowV2 : Group → ℝ}
    {fullSubHighQ1Full fullSubHighQ2Full fullSubHighScale fullSubHighV1
      fullSubHighV2 : Group → ℝ} :=
  paper_theorem3_posterior_mean_fullSub_source_free_merits_of_source_family_j2_keeps_test
    (Group := Group) (School := School) (FeatureDrop := FeatureDrop)
    (FeatureKeep := FeatureKeep) (LowFreeFeature := LowFreeFeature)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (HighBasedFeature := HighBasedFeature)
    (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
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
    (C := standardGaussianHazardInverseCertificate.toGaussianHazardCertificate)

end

end GLM20DroppingStandardizedTesting
