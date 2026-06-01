import GLM20DroppingStandardizedTesting.Theorem3PosteriorCostRows
import GLM20DroppingStandardizedTesting.Theorem3ConstructedComponents
import GLM20DroppingStandardizedTesting.Theorem3FeasibleKeepTest
import GLM20DroppingStandardizedTesting.Theorem3SourceFamilyKeepTest
import GLM20DroppingStandardizedTesting.Theorem3SimplePremises

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Theorem 3 fixed-law posterior cost-row endpoint with the school-`J2`
zero-fallback row built into the source table.

This composes the fixed-law posterior cost-row component route with the
zero-fallback source-table package.  The caller no longer supplies the two
expanding-group zero component assumptions; they are definitional consequences
of `glm20Theorem3SourceFamilySubFullJ2ZeroFallback`.  The visible
school-`J2` condition-(12) premises are only the two strict survivor-merit
comparisons on the paper's base sub/full merit row.
-/
abbrev
    paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_subFull_fullSub_interval_of_standardGaussian_fixed_law_posterior_mean_fullSub_cost_rows
    {Group School FeatureDrop FeatureKeep LowFreeFeature HighFreeFeature
      LowBasedFeature HighBasedFeature : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    (api : StandardGaussianCDFAPI)
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
    (C : GaussianHazardCertificate)
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
    (subFullTestBasedMerit : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
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
    (hsubFullCostMem :
      ∀ g, testCost g ∈
        Set.Icc (subFullLeftCost g) (subFullRightCost g))
    (hsubFullCont :
      ∀ g, ContinuousOn (subFullTestBasedMerit g)
        (Set.Icc (subFullLeftCost g) (subFullRightCost g)))
    (hsubFullAnti :
      ∀ g, StrictAntiOn (subFullTestBasedMerit g)
        (Set.Icc (subFullLeftCost g) (subFullRightCost g)))
    (hsubFullAtLeft :
      ∀ g, subFullTestFreeMerit g <
        subFullTestBasedMerit g (subFullLeftCost g))
    (hsubFullAtRight :
      ∀ g, subFullTestBasedMerit g (subFullRightCost g) <
        subFullTestFreeMerit g)
    (hfullSubLeftRight :
      ∀ g, fullSubLeftCost g < fullSubRightCost g)
    (hfullSubLeftPos : ∀ g, 0 < fullSubLeftCost g)
    (hfullSubCostMem :
      ∀ g, testCost g ∈
        Set.Icc (fullSubLeftCost g) (fullSubRightCost g))
    (hfullSubLowAtLeft :
      ∀ g,
        C.normalUpperTailMean
            (fullSubLowFreeFamily g).posteriorMeanScaleLaw
            (fullSubLowFreeThreshold g) <
          C.normalUpperTailMean
            (fullSubLowBasedFamily g
              (fullSubLeftCost g)).posteriorMeanScaleLaw
            (fullSubLowBasedThreshold g (fullSubLeftCost g)))
    (hfullSubLowAtRight :
      ∀ g,
        C.normalUpperTailMean
            (fullSubLowBasedFamily g
              (fullSubRightCost g)).posteriorMeanScaleLaw
            (fullSubLowBasedThreshold g (fullSubRightCost g)) <
          C.normalUpperTailMean
            (fullSubLowFreeFamily g).posteriorMeanScaleLaw
            (fullSubLowFreeThreshold g))
    (hfullSubHighAtLeft :
      ∀ g,
        C.normalUpperTailMean
            (fullSubHighFreeFamily g).posteriorMeanScaleLaw
            (fullSubHighFreeThreshold g) <
          C.normalUpperTailMean
            (fullSubHighBasedFamily g
              (fullSubLeftCost g)).posteriorMeanScaleLaw
            (fullSubHighBasedThreshold g (fullSubLeftCost g)))
    (hfullSubHighAtRight :
      ∀ g,
        C.normalUpperTailMean
            (fullSubHighBasedFamily g
              (fullSubRightCost g)).posteriorMeanScaleLaw
            (fullSubHighBasedThreshold g (fullSubRightCost g)) <
          C.normalUpperTailMean
            (fullSubHighFreeFamily g).posteriorMeanScaleLaw
            (fullSubHighFreeThreshold g))
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
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
    (hcapacity1 :
      capacity1 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q1Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q1Sub)
    (hfillFullFull1 :
      capacity1 ≤
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              (fullFullCutoff groupA) +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              (fullFullCutoff groupB))
    (hcapacity2 :
      capacity2 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q2Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q2Sub)
    (hfillFullFull2 :
      capacity2 ≤
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              (fullFullCutoff groupA) +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              (fullFullCutoff groupB))
    (hJ2MeritGtB_base :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase)
          fullSubMeritFallback fullFullMeritFallback diversity J1 J2
          groupA groupB populationShare testCost fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold q1Sub costThreshold groupA →
        populationShare groupB * subFullMeritBase J2 groupB >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB)
    (hJ2MeritGtA_base :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase)
          fullSubMeritFallback fullFullMeritFallback diversity J1 J2
          groupA groupB populationShare testCost fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold q1Sub costThreshold groupB →
        populationShare groupA * subFullMeritBase J2 groupA >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB)
    (hC : C = standardGaussianHazardCertificate)
    (fullSubLowBasedLaw fullSubHighBasedLaw : Group → GaussianScaleLaw)
    (hfullSubLowBasedLaw :
      ∀ g c, (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubHighBasedLaw :
      ∀ g c, (fullSubHighBasedFamily g c).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubLowThresholdCont :
      ∀ g, ContinuousOn (fullSubLowBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubLowThresholdAnti :
      ∀ g, StrictAntiOn (fullSubLowBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubHighThresholdCont :
      ∀ g, ContinuousOn (fullSubHighBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubHighThresholdAnti :
      ∀ g, StrictAntiOn (fullSubHighBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g))) :=
  have hcomponents :=
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_feasible_components_of_base_survivor_merits
      api subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback
      diversity J1 J2 groupA groupB populationShare testCost
      fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hshareA hshareB hcapacity1
      hfillFullFull1 hJ2MeritGtB_base hJ2MeritGtA_base
  paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval_of_standardGaussian_fixed_law_posterior_mean_fullSub_cost_rows
    api subEstimateLaw subSubMass subFullMass subSubMerit
    (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
      J2 subFullMeritBase)
    fullSubMeritFallback fullFullMeritFallback diversity
    (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost) (capacity1 := capacity1)
    (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
    (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
    (feasible1 := feasible1) (feasible2 := feasible2) C
    J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
    J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
    hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
    hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision hJ2ThresholdMean
    hJ2Threshold subFullTestBasedMerit subFullTestFreeMerit
    fullSubLowFreeFamily fullSubHighFreeFamily fullSubLowFreeThreshold
    fullSubHighFreeThreshold fullSubLowBasedFamily fullSubHighBasedFamily
    fullSubLowBasedThreshold fullSubHighBasedThreshold hsubFullLeftRight
    hsubFullLeftPos hsubFullCostMem hsubFullCont hsubFullAnti
    hsubFullAtLeft hsubFullAtRight hfullSubLeftRight hfullSubLeftPos
    hfullSubCostMem hfullSubLowAtLeft hfullSubLowAtRight
    hfullSubHighAtLeft hfullSubHighAtRight hfullSubFreePriorMean
    hfullSubFreePriorVar hfullSubFreePrecision hfullSubFreeThresholdMean
    hfullSubFreeThreshold hfullSubBasedPriorMean hfullSubBasedPriorVar
    hfullSubBasedPrecision hfullSubBasedThresholdMean
    hfullSubBasedThreshold hshareA hshareB hcapacity1 hfillFullFull1
    hcapacity2 hfillFullFull2 hcomponents.1 hcomponents.2.1
    hcomponents.2.2.1 hcomponents.2.2.2 hC fullSubLowBasedLaw
    fullSubHighBasedLaw hfullSubLowBasedLaw hfullSubHighBasedLaw
    hfullSubLowThresholdCont hfullSubLowThresholdAnti
    hfullSubHighThresholdCont hfullSubHighThresholdAnti

/--
Theorem 3 fixed-law posterior cost-row endpoint with the school-`J2`
zero-fallback row and equation-(50) sub-full regularity built in.

Compared with
`paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_subFull_fullSub_interval_of_standardGaussian_fixed_law_posterior_mean_fullSub_cost_rows`,
this wrapper no longer asks for the sub-full cost row's continuity or
strict-antitone hypotheses.  It instantiates that row with the paper's
equation-(50) cutoff formula and derives regularity from the global
standard-Gaussian merit assumptions.
-/
abbrev
    paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_standardGaussian_fixed_law_posterior_mean_fullSub_cost_rows
    {Group School FeatureDrop FeatureKeep LowFreeFeature HighFreeFeature
      LowBasedFeature HighBasedFeature : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    (api : StandardGaussianCDFAPI)
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
    {subFullQ2Full subFullScale subFullV2 : Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (C : GaussianHazardCertificate)
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
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
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
    (hfullSubLowAtLeft :
      ∀ g,
        C.normalUpperTailMean
            (fullSubLowFreeFamily g).posteriorMeanScaleLaw
            (fullSubLowFreeThreshold g) <
          C.normalUpperTailMean
            (fullSubLowBasedFamily g
              (fullSubLeftCost g)).posteriorMeanScaleLaw
            (fullSubLowBasedThreshold g (fullSubLeftCost g)))
    (hfullSubLowAtRight :
      ∀ g,
        C.normalUpperTailMean
            (fullSubLowBasedFamily g
              (fullSubRightCost g)).posteriorMeanScaleLaw
            (fullSubLowBasedThreshold g (fullSubRightCost g)) <
          C.normalUpperTailMean
            (fullSubLowFreeFamily g).posteriorMeanScaleLaw
            (fullSubLowFreeThreshold g))
    (hfullSubHighAtLeft :
      ∀ g,
        C.normalUpperTailMean
            (fullSubHighFreeFamily g).posteriorMeanScaleLaw
            (fullSubHighFreeThreshold g) <
          C.normalUpperTailMean
            (fullSubHighBasedFamily g
              (fullSubLeftCost g)).posteriorMeanScaleLaw
            (fullSubHighBasedThreshold g (fullSubLeftCost g)))
    (hfullSubHighAtRight :
      ∀ g,
        C.normalUpperTailMean
            (fullSubHighBasedFamily g
              (fullSubRightCost g)).posteriorMeanScaleLaw
            (fullSubHighBasedThreshold g (fullSubRightCost g)) <
          C.normalUpperTailMean
            (fullSubHighFreeFamily g).posteriorMeanScaleLaw
            (fullSubHighFreeThreshold g))
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
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
    (hcapacity1 :
      capacity1 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q1Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q1Sub)
    (hfillFullFull1 :
      capacity1 ≤
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              (fullFullCutoff groupA) +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              (fullFullCutoff groupB))
    (hcapacity2 :
      capacity2 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              q2Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              q2Sub)
    (hfillFullFull2 :
      capacity2 ≤
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
              (fullFullCutoff groupA) +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
              (fullFullCutoff groupB))
    (hJ2MeritGtB_base :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase)
          fullSubMeritFallback fullFullMeritFallback diversity J1 J2
          groupA groupB populationShare testCost fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold q1Sub costThreshold groupA →
        populationShare groupB * subFullMeritBase J2 groupB >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB)
    (hJ2MeritGtA_base :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase)
          fullSubMeritFallback fullFullMeritFallback diversity J1 J2
          groupA groupB populationShare testCost fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold q1Sub costThreshold groupB →
        populationShare groupA * subFullMeritBase J2 groupA >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB)
    (hC : C = standardGaussianHazardCertificate)
    (fullSubLowBasedLaw fullSubHighBasedLaw : Group → GaussianScaleLaw)
    (hfullSubLowBasedLaw :
      ∀ g c, (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubHighBasedLaw :
      ∀ g c, (fullSubHighBasedFamily g c).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubLowThresholdCont :
      ∀ g, ContinuousOn (fullSubLowBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubLowThresholdAnti :
      ∀ g, StrictAntiOn (fullSubLowBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubHighThresholdCont :
      ∀ g, ContinuousOn (fullSubHighBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubHighThresholdAnti :
      ∀ g, StrictAntiOn (fullSubHighBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g))) :=
  let subFullTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    subFullMeritOfCutoff g
      (subFullQ2Full g -
        subFullScale g *
          standardGaussianQuantileAPI.quantile
            (1 - cost / subFullV2 g))
  have hsubFullRegular :=
    paper_proposition5_equation50_subFull_cost_merit_regular_of_global_regular_cost_bounds
      standardGaussianQuantileAPI
      (q2Full := subFullQ2Full) (scale := subFullScale)
      (v2 := subFullV2) (left := subFullLeftCost)
      (right := subFullRightCost) (meritOfCutoff := subFullMeritOfCutoff)
      hsubFullLeftRight hsubFullScale hsubFullLeftPos hsubFullRightLtV2
      hsubFullMeritCont hsubFullMeritAnti
  paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_subFull_fullSub_interval_of_standardGaussian_fixed_law_posterior_mean_fullSub_cost_rows
    api subEstimateLaw subSubMass subFullMass subSubMerit
    subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
    (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost) (capacity1 := capacity1)
    (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
    (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
    (feasible1 := feasible1) (feasible2 := feasible2) C
    J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
    J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
    hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
    hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision hJ2ThresholdMean
    hJ2Threshold subFullTestBasedMerit subFullTestFreeMerit
    fullSubLowFreeFamily fullSubHighFreeFamily fullSubLowFreeThreshold
    fullSubHighFreeThreshold fullSubLowBasedFamily fullSubHighBasedFamily
    fullSubLowBasedThreshold fullSubHighBasedThreshold hsubFullLeftRight
    hsubFullLeftPos hsubFullCostMem (fun g => hsubFullRegular.1 g)
    (fun g => hsubFullRegular.2 g)
    (by intro g; simpa [subFullTestBasedMerit] using hsubFullAtLeft g)
    (by intro g; simpa [subFullTestBasedMerit] using hsubFullAtRight g)
    hfullSubLeftRight hfullSubLeftPos hfullSubCostMem hfullSubLowAtLeft
    hfullSubLowAtRight hfullSubHighAtLeft hfullSubHighAtRight
    hfullSubFreePriorMean hfullSubFreePriorVar hfullSubFreePrecision
    hfullSubFreeThresholdMean hfullSubFreeThreshold hfullSubBasedPriorMean
    hfullSubBasedPriorVar hfullSubBasedPrecision
    hfullSubBasedThresholdMean hfullSubBasedThreshold hshareA hshareB
    hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
    hJ2MeritGtB_base hJ2MeritGtA_base hC fullSubLowBasedLaw
    fullSubHighBasedLaw hfullSubLowBasedLaw hfullSubHighBasedLaw
    hfullSubLowThresholdCont hfullSubLowThresholdAnti
    hfullSubHighThresholdCont hfullSubHighThresholdAnti

/--
Standard-Gaussian specialization of the strongest fixed-law posterior cost-row
Theorem 3 route.

This hides the internal `StandardGaussianCDFAPI`, `GaussianHazardCertificate`,
and certificate-equality parameters from the review surface.  The remaining
assumptions are the paper-level source-family data, endpoint crossings,
equation-(50) sub-full row facts, fixed-law full-sub posterior rows, capacity
fill, and the two school-`J2` survivor-merit comparisons.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows
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
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop} :=
  paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_standardGaussian_fixed_law_posterior_mean_fullSub_cost_rows
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
    (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
    (subFullV2 := subFullV2) (feasible1 := feasible1)
    (feasible2 := feasible2)
    (api := standardGaussianCDFAPI)
    (C := standardGaussianHazardCertificate)
    (hC := rfl)

/--
Standard-Gaussian fixed-law posterior cost-row endpoint with paper-row
survivor-merit assumptions.

The strongest fixed-law posterior cost-row route asks for the survivor-merit
conditions after conditioning on which group expands.  The paper displays the
corresponding strict inequalities as unconditional source rows; this wrapper
exposes that row shape and weakens it into the branch-conditioned premises.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_raw_survivor_merits
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
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
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
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
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
    (hfullSubLowAtLeft :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubLowFreeFamily g).posteriorMeanScaleLaw
            (fullSubLowFreeThreshold g) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubLowBasedFamily g
              (fullSubLeftCost g)).posteriorMeanScaleLaw
            (fullSubLowBasedThreshold g (fullSubLeftCost g)))
    (hfullSubLowAtRight :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubLowBasedFamily g
              (fullSubRightCost g)).posteriorMeanScaleLaw
            (fullSubLowBasedThreshold g (fullSubRightCost g)) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubLowFreeFamily g).posteriorMeanScaleLaw
            (fullSubLowFreeThreshold g))
    (hfullSubHighAtLeft :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubHighFreeFamily g).posteriorMeanScaleLaw
            (fullSubHighFreeThreshold g) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubHighBasedFamily g
              (fullSubLeftCost g)).posteriorMeanScaleLaw
            (fullSubHighBasedThreshold g (fullSubLeftCost g)))
    (hfullSubHighAtRight :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubHighBasedFamily g
              (fullSubRightCost g)).posteriorMeanScaleLaw
            (fullSubHighBasedThreshold g (fullSubRightCost g)) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubHighFreeFamily g).posteriorMeanScaleLaw
            (fullSubHighFreeThreshold g))
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
              (subEstimateLaw groupB) (fullFullCutoff groupB))
    (hJ2MeritGtB_base :
      populationShare groupB * subFullMeritBase J2 groupB >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB)
    (hJ2MeritGtA_base :
      populationShare groupA * subFullMeritBase J2 groupA >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB)
    (fullSubLowBasedLaw fullSubHighBasedLaw : Group → GaussianScaleLaw)
    (hfullSubLowBasedLaw :
      ∀ g c, (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubHighBasedLaw :
      ∀ g c, (fullSubHighBasedFamily g c).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubLowThresholdCont :
      ∀ g, ContinuousOn (fullSubLowBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubLowThresholdAnti :
      ∀ g, StrictAntiOn (fullSubLowBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubHighThresholdCont :
      ∀ g, ContinuousOn (fullSubHighBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubHighThresholdAnti :
      ∀ g, StrictAntiOn (fullSubHighBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g))) :=
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows
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
    (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
    (subFullV2 := subFullV2) (feasible1 := feasible1)
    (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit
    subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
    J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
    J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
    hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
    hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision hJ2ThresholdMean
    hJ2Threshold subFullMeritOfCutoff subFullTestFreeMerit
    fullSubLowFreeFamily fullSubHighFreeFamily fullSubLowFreeThreshold
    fullSubHighFreeThreshold fullSubLowBasedFamily fullSubHighBasedFamily
    fullSubLowBasedThreshold fullSubHighBasedThreshold hsubFullLeftRight
    hsubFullLeftPos hsubFullRightLtV2 hsubFullCostMem hsubFullScale
    hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight
    hfullSubLeftRight hfullSubLeftPos hfullSubCostMem hfullSubLowAtLeft
    hfullSubLowAtRight hfullSubHighAtLeft hfullSubHighAtRight
    hfullSubFreePriorMean hfullSubFreePriorVar hfullSubFreePrecision
    hfullSubFreeThresholdMean hfullSubFreeThreshold hfullSubBasedPriorMean
    hfullSubBasedPriorVar hfullSubBasedPrecision
    hfullSubBasedThresholdMean hfullSubBasedThreshold hshareA hshareB
    hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
    (fun _ _ => hJ2MeritGtB_base) (fun _ _ => hJ2MeritGtA_base)
    fullSubLowBasedLaw fullSubHighBasedLaw hfullSubLowBasedLaw
    hfullSubHighBasedLaw hfullSubLowThresholdCont
    hfullSubLowThresholdAnti hfullSubHighThresholdCont
    hfullSubHighThresholdAnti

/--
Standard-Gaussian fixed-law posterior cost-row endpoint with the final
school-`J2` survivor side stated as named keep-test predicates.

This keeps the strongest cost-row treatment from the raw-survivor-merit
wrapper, but extracts the two strict condition-(12) merit rows from the named
school-`J2` keep-test predicates on the base policy-state table.  Condition
(11)'s mass side is still supplied by the feasibility surface used by the
underlying theorem.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_j2_keeps_test
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
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
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
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
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
    (hfullSubLowAtLeft :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubLowFreeFamily g).posteriorMeanScaleLaw
            (fullSubLowFreeThreshold g) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubLowBasedFamily g
              (fullSubLeftCost g)).posteriorMeanScaleLaw
            (fullSubLowBasedThreshold g (fullSubLeftCost g)))
    (hfullSubLowAtRight :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubLowBasedFamily g
              (fullSubRightCost g)).posteriorMeanScaleLaw
            (fullSubLowBasedThreshold g (fullSubRightCost g)) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubLowFreeFamily g).posteriorMeanScaleLaw
            (fullSubLowFreeThreshold g))
    (hfullSubHighAtLeft :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubHighFreeFamily g).posteriorMeanScaleLaw
            (fullSubHighFreeThreshold g) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubHighBasedFamily g
              (fullSubLeftCost g)).posteriorMeanScaleLaw
            (fullSubHighBasedThreshold g (fullSubLeftCost g)))
    (hfullSubHighAtRight :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubHighBasedFamily g
              (fullSubRightCost g)).posteriorMeanScaleLaw
            (fullSubHighBasedThreshold g (fullSubRightCost g)) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubHighFreeFamily g).posteriorMeanScaleLaw
            (fullSubHighFreeThreshold g))
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
  fun
      (hJ2KeepsB :
        glm20Theorem3SubFullOtherGroupKeepsTest tableSurface
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB)
      (hJ2KeepsA :
        glm20Theorem3SubFullOtherGroupKeepsTest tableSurface
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA)
      (fullSubLowBasedLaw fullSubHighBasedLaw : Group → GaussianScaleLaw)
      (hfullSubLowBasedLaw :
        ∀ g c, (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
          fullSubLowBasedLaw g)
      (hfullSubHighBasedLaw :
        ∀ g c, (fullSubHighBasedFamily g c).posteriorMeanScaleLaw =
          fullSubHighBasedLaw g)
      (hfullSubLowThresholdCont :
        ∀ g, ContinuousOn (fullSubLowBasedThreshold g)
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
      (hfullSubLowThresholdAnti :
        ∀ g, StrictAntiOn (fullSubLowBasedThreshold g)
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
      (hfullSubHighThresholdCont :
        ∀ g, ContinuousOn (fullSubHighBasedThreshold g)
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
      (hfullSubHighThresholdAnti :
        ∀ g, StrictAntiOn (fullSubHighBasedThreshold g)
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g))) =>
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
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_raw_survivor_merits
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
      (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
      (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
      (subFullV2 := subFullV2) (feasible1 := feasible1)
      (feasible2 := feasible2)
      subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision
      hJ2ThresholdMean hJ2Threshold subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowFreeFamily fullSubHighFreeFamily
      fullSubLowFreeThreshold fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubHighBasedFamily fullSubLowBasedThreshold
      fullSubHighBasedThreshold hsubFullLeftRight hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullScale
      hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight
      hfullSubLeftRight hfullSubLeftPos hfullSubCostMem hfullSubLowAtLeft
      hfullSubLowAtRight hfullSubHighAtLeft hfullSubHighAtRight
      hfullSubFreePriorMean hfullSubFreePriorVar hfullSubFreePrecision
      hfullSubFreeThresholdMean hfullSubFreeThreshold
      hfullSubBasedPriorMean hfullSubBasedPriorVar hfullSubBasedPrecision
      hfullSubBasedThresholdMean hfullSubBasedThreshold hshareA hshareB
      hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2 hB.2 hA.2
      fullSubLowBasedLaw fullSubHighBasedLaw hfullSubLowBasedLaw
      hfullSubHighBasedLaw hfullSubLowThresholdCont
      hfullSubLowThresholdAnti hfullSubHighThresholdCont
      hfullSubHighThresholdAnti

/--
Standard-Gaussian fixed-law posterior cost-row endpoint with the final
school-`J2` survivor side stated on the generated source-family table.

This is the generated-table companion to
`paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_j2_keeps_test`.
The supplied keep-test predicates live on
`glm20Theorem3SourceFamilyPolicyStateTableSurface`; Lean first converts them
to the base weighted-academic-merit table and then uses the already verified
fixed-law posterior cost-row route.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test
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
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
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
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
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
    (hfullSubLowAtLeft :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubLowFreeFamily g).posteriorMeanScaleLaw
            (fullSubLowFreeThreshold g) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubLowBasedFamily g
              (fullSubLeftCost g)).posteriorMeanScaleLaw
            (fullSubLowBasedThreshold g (fullSubLeftCost g)))
    (hfullSubLowAtRight :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubLowBasedFamily g
              (fullSubRightCost g)).posteriorMeanScaleLaw
            (fullSubLowBasedThreshold g (fullSubRightCost g)) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubLowFreeFamily g).posteriorMeanScaleLaw
            (fullSubLowFreeThreshold g))
    (hfullSubHighAtLeft :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubHighFreeFamily g).posteriorMeanScaleLaw
            (fullSubHighFreeThreshold g) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubHighBasedFamily g
              (fullSubLeftCost g)).posteriorMeanScaleLaw
            (fullSubHighBasedThreshold g (fullSubLeftCost g)))
    (hfullSubHighAtRight :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubHighBasedFamily g
              (fullSubRightCost g)).posteriorMeanScaleLaw
            (fullSubHighBasedThreshold g (fullSubRightCost g)) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (fullSubHighFreeFamily g).posteriorMeanScaleLaw
            (fullSubHighFreeThreshold g))
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
      populationShare fullFullCutoff fullSubCutoff
      standardGaussianHazardCertificate J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold
  let baseEndpoint :=
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_j2_keeps_test
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
      (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
      (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
      (subFullV2 := subFullV2) (feasible1 := feasible1)
      (feasible2 := feasible2)
      subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision
      hJ2ThresholdMean hJ2Threshold subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowFreeFamily fullSubHighFreeFamily
      fullSubLowFreeThreshold fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubHighBasedFamily fullSubLowBasedThreshold
      fullSubHighBasedThreshold hsubFullLeftRight hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullScale
      hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight
      hfullSubLeftRight hfullSubLeftPos hfullSubCostMem hfullSubLowAtLeft
      hfullSubLowAtRight hfullSubHighAtLeft hfullSubHighAtRight
      hfullSubFreePriorMean hfullSubFreePriorVar hfullSubFreePrecision
      hfullSubFreeThresholdMean hfullSubFreeThreshold
      hfullSubBasedPriorMean hfullSubBasedPriorVar hfullSubBasedPrecision
      hfullSubBasedThresholdMean hfullSubBasedThreshold hshareA hshareB
      hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
  fun
      (hJ2KeepsB :
        glm20Theorem3SubFullOtherGroupKeepsTest sourceTableSurface
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB)
      (hJ2KeepsA :
        glm20Theorem3SubFullOtherGroupKeepsTest sourceTableSurface
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA)
      (fullSubLowBasedLaw fullSubHighBasedLaw : Group → GaussianScaleLaw)
      (hfullSubLowBasedLaw :
        ∀ g c, (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
          fullSubLowBasedLaw g)
      (hfullSubHighBasedLaw :
        ∀ g c, (fullSubHighBasedFamily g c).posteriorMeanScaleLaw =
          fullSubHighBasedLaw g)
      (hfullSubLowThresholdCont :
        ∀ g, ContinuousOn (fullSubLowBasedThreshold g)
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
      (hfullSubLowThresholdAnti :
        ∀ g, StrictAntiOn (fullSubLowBasedThreshold g)
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
      (hfullSubHighThresholdCont :
        ∀ g, ContinuousOn (fullSubHighBasedThreshold g)
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
      (hfullSubHighThresholdAnti :
        ∀ g, StrictAntiOn (fullSubHighBasedThreshold g)
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g))) =>
    let hbasePair :=
      (paper_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_base_table_keep_test_pair
        standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
        subSubMerit subFullMeritBase fullSubMeritFallback
        fullFullMeritFallback diversity J1 J2 groupA groupB
        populationShare fullFullCutoff fullSubCutoff
        standardGaussianHazardCertificate J1DropFamily J2DropFamily
        J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
        J2DropThreshold J2KeepThreshold hJ1_ne_J2
        (capacity2 := capacity2)).mp ⟨hJ2KeepsB, hJ2KeepsA⟩
    baseEndpoint hbasePair.1 hbasePair.2 fullSubLowBasedLaw
      fullSubHighBasedLaw hfullSubLowBasedLaw hfullSubHighBasedLaw
      hfullSubLowThresholdCont hfullSubLowThresholdAnti
      hfullSubHighThresholdCont hfullSubHighThresholdAnti

/--
Standard-Gaussian fixed-law posterior cost-row endpoint with the full-sub
endpoint crossings generated from threshold order.

This is the threshold-order companion to
`paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test`.
Instead of asking for the four endpoint merit-crossing inequalities directly,
it assumes the free and based rows share fixed posterior mean laws and that the
endpoint thresholds cross in the paper direction.  The four merit inequalities
are then generated by
`paper_standardGaussian_posterior_low_high_cost_row_endpoint_crossings_of_fixed_law_threshold_order`
and passed to the existing source-family school-`J2` keep-test endpoint.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test
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
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
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
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
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
    (fullSubLowBasedLaw fullSubHighBasedLaw : Group → GaussianScaleLaw)
    (hfullSubLowFreeLaw :
      ∀ g, (fullSubLowFreeFamily g).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubLowBasedLaw :
      ∀ g c, (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubHighFreeLaw :
      ∀ g, (fullSubHighFreeFamily g).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubHighBasedLaw :
      ∀ g c, (fullSubHighBasedFamily g c).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubLowAtLeftThreshold :
      ∀ g, fullSubLowFreeThreshold g <
        fullSubLowBasedThreshold g (fullSubLeftCost g))
    (hfullSubLowAtRightThreshold :
      ∀ g, fullSubLowBasedThreshold g (fullSubRightCost g) <
        fullSubLowFreeThreshold g)
    (hfullSubHighAtLeftThreshold :
      ∀ g, fullSubHighFreeThreshold g <
        fullSubHighBasedThreshold g (fullSubLeftCost g))
    (hfullSubHighAtRightThreshold :
      ∀ g, fullSubHighBasedThreshold g (fullSubRightCost g) <
        fullSubHighFreeThreshold g)
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
  let hcross :=
    paper_standardGaussian_posterior_low_high_cost_row_endpoint_crossings_of_fixed_law_threshold_order
      (leftCost := fullSubLeftCost) (rightCost := fullSubRightCost)
      fullSubLowFreeFamily fullSubHighFreeFamily fullSubLowBasedFamily
      fullSubHighBasedFamily fullSubLowFreeThreshold
      fullSubHighFreeThreshold fullSubLowBasedThreshold
      fullSubHighBasedThreshold fullSubLowBasedLaw fullSubHighBasedLaw
      hfullSubLowFreeLaw hfullSubLowBasedLaw hfullSubHighFreeLaw
      hfullSubHighBasedLaw hfullSubLowAtLeftThreshold
      hfullSubLowAtRightThreshold hfullSubHighAtLeftThreshold
      hfullSubHighAtRightThreshold
  let baseEndpoint :=
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test
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
      (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
      (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
      (subFullV2 := subFullV2) (feasible1 := feasible1)
      (feasible2 := feasible2)
      subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision
      hJ2ThresholdMean hJ2Threshold subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowFreeFamily fullSubHighFreeFamily
      fullSubLowFreeThreshold fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubHighBasedFamily fullSubLowBasedThreshold
      fullSubHighBasedThreshold hsubFullLeftRight hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullScale
      hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight
      hfullSubLeftRight hfullSubLeftPos hfullSubCostMem hcross.1
      hcross.2.1 hcross.2.2.1 hcross.2.2.2 hfullSubFreePriorMean
      hfullSubFreePriorVar hfullSubFreePrecision
      hfullSubFreeThresholdMean hfullSubFreeThreshold
      hfullSubBasedPriorMean hfullSubBasedPriorVar hfullSubBasedPrecision
      hfullSubBasedThresholdMean hfullSubBasedThreshold hshareA hshareB
      hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
  fun
      (hJ2KeepsB :
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface
            standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
            subSubMerit subFullMeritBase fullSubMeritFallback
            fullFullMeritFallback diversity J1 J2 groupA groupB
            populationShare fullFullCutoff fullSubCutoff
            standardGaussianHazardCertificate J1DropFamily J2DropFamily
            J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
            J2DropThreshold J2KeepThreshold)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB)
      (hJ2KeepsA :
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface
            standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
            subSubMerit subFullMeritBase fullSubMeritFallback
            fullFullMeritFallback diversity J1 J2 groupA groupB
            populationShare fullFullCutoff fullSubCutoff
            standardGaussianHazardCertificate J1DropFamily J2DropFamily
            J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
            J2DropThreshold J2KeepThreshold)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA)
      (hfullSubLowThresholdCont :
        ∀ g, ContinuousOn (fullSubLowBasedThreshold g)
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
      (hfullSubLowThresholdAnti :
        ∀ g, StrictAntiOn (fullSubLowBasedThreshold g)
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
      (hfullSubHighThresholdCont :
        ∀ g, ContinuousOn (fullSubHighBasedThreshold g)
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
      (hfullSubHighThresholdAnti :
        ∀ g, StrictAntiOn (fullSubHighBasedThreshold g)
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g))) =>
    baseEndpoint hJ2KeepsB hJ2KeepsA fullSubLowBasedLaw
      fullSubHighBasedLaw hfullSubLowBasedLaw hfullSubHighBasedLaw
      hfullSubLowThresholdCont hfullSubLowThresholdAnti
      hfullSubHighThresholdCont hfullSubHighThresholdAnti

/--
Standard-Gaussian threshold-order fixed-law posterior cost-row endpoint with
the full/full capacity-fill premises generated from cutoff order.

This is the preferred companion to
`paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test`.
Instead of asking for the two fill inequalities directly, callers supply the
source-shaped cutoff-order facts
`fullFullCutoff g <= q1Sub` and `fullFullCutoff g <= q2Sub` for both groups.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test
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
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
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
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
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
    (fullSubLowBasedLaw fullSubHighBasedLaw : Group → GaussianScaleLaw)
    (hfullSubLowFreeLaw :
      ∀ g, (fullSubLowFreeFamily g).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubLowBasedLaw :
      ∀ g c, (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubHighFreeLaw :
      ∀ g, (fullSubHighFreeFamily g).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubHighBasedLaw :
      ∀ g c, (fullSubHighBasedFamily g c).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubLowAtLeftThreshold :
      ∀ g, fullSubLowFreeThreshold g <
        fullSubLowBasedThreshold g (fullSubLeftCost g))
    (hfullSubLowAtRightThreshold :
      ∀ g, fullSubLowBasedThreshold g (fullSubRightCost g) <
        fullSubLowFreeThreshold g)
    (hfullSubHighAtLeftThreshold :
      ∀ g, fullSubHighFreeThreshold g <
        fullSubHighBasedThreshold g (fullSubLeftCost g))
    (hfullSubHighAtRightThreshold :
      ∀ g, fullSubHighBasedThreshold g (fullSubRightCost g) <
        fullSubHighFreeThreshold g)
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
    (hcut1A : fullFullCutoff groupA ≤ q1Sub)
    (hcut1B : fullFullCutoff groupB ≤ q1Sub)
    (hcapacity2 :
      capacity2 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupA) q2Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupB) q2Sub)
    (hcut2A : fullFullCutoff groupA ≤ q2Sub)
    (hcut2B : fullFullCutoff groupB ≤ q2Sub) :=
  paper_theorem3_apply_fullFull_fill_of_cutoff_order_of_pos
    standardGaussianCDFAPI subEstimateLaw
    (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (capacity1 := capacity1)
    (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
    (fullFullCutoff := fullFullCutoff) hcapacity1 hcapacity2 hshareA
    hshareB hcut1A hcut1B hcut2A hcut2B
    (fun hfillFullFull1 hfillFullFull2 =>
      paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test
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
        (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
        (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
        (subFullV2 := subFullV2) (feasible1 := feasible1)
        (feasible2 := feasible2)
        subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
        J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
        J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
        hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision
        hJ1ThresholdMean hJ1Threshold hJ2PriorMean hJ2PriorVar
        hJ2Precision hJ2ThresholdMean hJ2Threshold subFullMeritOfCutoff
        subFullTestFreeMerit fullSubLowFreeFamily fullSubHighFreeFamily
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        fullSubLowBasedFamily fullSubHighBasedFamily
        fullSubLowBasedThreshold fullSubHighBasedThreshold
        hsubFullLeftRight hsubFullLeftPos hsubFullRightLtV2
        hsubFullCostMem hsubFullScale hsubFullMeritCont hsubFullMeritAnti
        hsubFullAtLeft hsubFullAtRight hfullSubLeftRight
        hfullSubLeftPos hfullSubCostMem fullSubLowBasedLaw
        fullSubHighBasedLaw hfullSubLowFreeLaw hfullSubLowBasedLaw
        hfullSubHighFreeLaw hfullSubHighBasedLaw
        hfullSubLowAtLeftThreshold hfullSubLowAtRightThreshold
        hfullSubHighAtLeftThreshold hfullSubHighAtRightThreshold
        hfullSubFreePriorMean hfullSubFreePriorVar hfullSubFreePrecision
        hfullSubFreeThresholdMean hfullSubFreeThreshold
        hfullSubBasedPriorMean hfullSubBasedPriorVar
        hfullSubBasedPrecision hfullSubBasedThresholdMean
        hfullSubBasedThreshold hshareA hshareB hcapacity1 hfillFullFull1
        hcapacity2 hfillFullFull2)

/--
Standard-Gaussian cutoff-order and threshold-order Theorem 3 endpoint with
affine-decreasing full-sub based threshold rows.

This specializes the current strongest generated-table keep-test route by
taking the full-sub based thresholds in the source-shaped affine form
`intercept_g - slope_g * c`.  The four continuity/strict-antitonicity inputs
for those threshold maps are generated internally from the two positive-slope
premises.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_j2_keeps_test
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
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
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
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (fullSubLowFreeFamily :
      Group → GaussianOffsetSignalFamily LowFreeFeature)
    (fullSubHighFreeFamily :
      Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold : Group → ℝ)
    (fullSubLowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubHighBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      Group → ℝ)
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
    (fullSubLowBasedLaw fullSubHighBasedLaw : Group → GaussianScaleLaw)
    (hfullSubLowFreeLaw :
      ∀ g, (fullSubLowFreeFamily g).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubLowBasedLaw :
      ∀ g c, (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubHighFreeLaw :
      ∀ g, (fullSubHighFreeFamily g).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubHighBasedLaw :
      ∀ g c, (fullSubHighBasedFamily g c).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubLowAtLeftThreshold :
      ∀ g, fullSubLowFreeThreshold g <
        fullSubLowBasedThresholdIntercept g -
          fullSubLowBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubLowAtRightThreshold :
      ∀ g,
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * fullSubRightCost g <
          fullSubLowFreeThreshold g)
    (hfullSubHighAtLeftThreshold :
      ∀ g, fullSubHighFreeThreshold g <
        fullSubHighBasedThresholdIntercept g -
          fullSubHighBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubHighAtRightThreshold :
      ∀ g,
        fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * fullSubRightCost g <
          fullSubHighFreeThreshold g)
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
          fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c)
    (hfullSubBasedThreshold :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c ≤
          fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * c)
    (hfullSubLowBasedThresholdSlope :
      ∀ g, 0 < fullSubLowBasedThresholdSlope g)
    (hfullSubHighBasedThresholdSlope :
      ∀ g, 0 < fullSubHighBasedThresholdSlope g)
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
    (hcut1A : fullFullCutoff groupA ≤ q1Sub)
    (hcut1B : fullFullCutoff groupB ≤ q1Sub)
    (hcapacity2 :
      capacity2 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupA) q2Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupB) q2Sub)
    (hcut2A : fullFullCutoff groupA ≤ q2Sub)
    (hcut2B : fullFullCutoff groupB ≤ q2Sub) :=
  let hthreshold :=
    paper_theorem3_low_high_based_threshold_regularities_of_affine_decreasing
      (leftCost := fullSubLeftCost) (rightCost := fullSubRightCost)
      fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope
      fullSubHighBasedThresholdSlope
      hfullSubLowBasedThresholdSlope hfullSubHighBasedThresholdSlope
  let base :=
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test
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
      (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
      (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
      (subFullV2 := subFullV2) (feasible1 := feasible1)
      (feasible2 := feasible2)
      subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision
      hJ1ThresholdMean hJ1Threshold hJ2PriorMean hJ2PriorVar
      hJ2Precision hJ2ThresholdMean hJ2Threshold subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowFreeFamily fullSubHighFreeFamily
      fullSubLowFreeThreshold fullSubHighFreeThreshold
      fullSubLowBasedFamily fullSubHighBasedFamily
      (fun g c =>
        fullSubLowBasedThresholdIntercept g -
          fullSubLowBasedThresholdSlope g * c)
      (fun g c =>
        fullSubHighBasedThresholdIntercept g -
          fullSubHighBasedThresholdSlope g * c)
      hsubFullLeftRight hsubFullLeftPos hsubFullRightLtV2
      hsubFullCostMem hsubFullScale hsubFullMeritCont hsubFullMeritAnti
      hsubFullAtLeft hsubFullAtRight hfullSubLeftRight
      hfullSubLeftPos hfullSubCostMem fullSubLowBasedLaw
      fullSubHighBasedLaw hfullSubLowFreeLaw hfullSubLowBasedLaw
      hfullSubHighFreeLaw hfullSubHighBasedLaw
      hfullSubLowAtLeftThreshold hfullSubLowAtRightThreshold
      hfullSubHighAtLeftThreshold hfullSubHighAtRightThreshold
      hfullSubFreePriorMean hfullSubFreePriorVar hfullSubFreePrecision
      hfullSubFreeThresholdMean hfullSubFreeThreshold
      hfullSubBasedPriorMean hfullSubBasedPriorVar
      hfullSubBasedPrecision hfullSubBasedThresholdMean
      hfullSubBasedThreshold hshareA hshareB hcapacity1 hcut1A hcut1B
      hcapacity2 hcut2A hcut2B
  fun hJ2KeepsB hJ2KeepsA =>
    base hJ2KeepsB hJ2KeepsA hthreshold.1 hthreshold.2.1
      hthreshold.2.2.1 hthreshold.2.2.2

/--
Standard-Gaussian cutoff-order and threshold-order Theorem 3 endpoint with
affine-decreasing full-sub based threshold rows and raw survivor source rows.

This is the raw-component companion to
`paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_j2_keeps_test`.
The displayed condition-(11)--(12) source rows are converted into the two
generated-table school-`J2` keep-test predicates before invoking that endpoint.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components
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
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
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
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (fullSubLowFreeFamily :
      Group → GaussianOffsetSignalFamily LowFreeFeature)
    (fullSubHighFreeFamily :
      Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold : Group → ℝ)
    (fullSubLowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubHighBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      Group → ℝ)
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
    (fullSubLowBasedLaw fullSubHighBasedLaw : Group → GaussianScaleLaw)
    (hfullSubLowFreeLaw :
      ∀ g, (fullSubLowFreeFamily g).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubLowBasedLaw :
      ∀ g c, (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubHighFreeLaw :
      ∀ g, (fullSubHighFreeFamily g).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubHighBasedLaw :
      ∀ g c, (fullSubHighBasedFamily g c).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubLowAtLeftThreshold :
      ∀ g, fullSubLowFreeThreshold g <
        fullSubLowBasedThresholdIntercept g -
          fullSubLowBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubLowAtRightThreshold :
      ∀ g,
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * fullSubRightCost g <
          fullSubLowFreeThreshold g)
    (hfullSubHighAtLeftThreshold :
      ∀ g, fullSubHighFreeThreshold g <
        fullSubHighBasedThresholdIntercept g -
          fullSubHighBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubHighAtRightThreshold :
      ∀ g,
        fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * fullSubRightCost g <
          fullSubHighFreeThreshold g)
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
          fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c)
    (hfullSubBasedThreshold :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c ≤
          fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * c)
    (hfullSubLowBasedThresholdSlope :
      ∀ g, 0 < fullSubLowBasedThresholdSlope g)
    (hfullSubHighBasedThresholdSlope :
      ∀ g, 0 < fullSubHighBasedThresholdSlope g)
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
    (hcut1A : fullFullCutoff groupA ≤ q1Sub)
    (hcut1B : fullFullCutoff groupB ≤ q1Sub)
    (hcapacity2 :
      capacity2 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupA) q2Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw groupB) q2Sub)
    (hcut2A : fullFullCutoff groupA ≤ q2Sub)
    (hcut2B : fullFullCutoff groupB ≤ q2Sub)
    (hJ2MassB : subFullMass groupB ≥ capacity2)
    (hJ2MeritGtB :
      populationShare groupB * subFullMeritBase J2 groupB >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB)
    (hJ2MassA : subFullMass groupA ≥ capacity2)
    (hJ2MeritGtA :
      populationShare groupA * subFullMeritBase J2 groupA >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB) :=
  let hthreshold :=
    paper_theorem3_low_high_based_threshold_regularities_of_affine_decreasing
      (leftCost := fullSubLeftCost) (rightCost := fullSubRightCost)
      fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope
      fullSubHighBasedThresholdSlope
      hfullSubLowBasedThresholdSlope hfullSubHighBasedThresholdSlope
  let base :=
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_source_family_j2_keeps_test
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
      (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
      (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
      (subFullV2 := subFullV2) (feasible1 := feasible1)
      (feasible2 := feasible2)
      subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision
      hJ1ThresholdMean hJ1Threshold hJ2PriorMean hJ2PriorVar
      hJ2Precision hJ2ThresholdMean hJ2Threshold subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowFreeFamily fullSubHighFreeFamily
      fullSubLowFreeThreshold fullSubHighFreeThreshold
      fullSubLowBasedFamily fullSubHighBasedFamily
      (fun g c =>
        fullSubLowBasedThresholdIntercept g -
          fullSubLowBasedThresholdSlope g * c)
      (fun g c =>
        fullSubHighBasedThresholdIntercept g -
          fullSubHighBasedThresholdSlope g * c)
      hsubFullLeftRight hsubFullLeftPos hsubFullRightLtV2
      hsubFullCostMem hsubFullScale hsubFullMeritCont hsubFullMeritAnti
      hsubFullAtLeft hsubFullAtRight hfullSubLeftRight
      hfullSubLeftPos hfullSubCostMem fullSubLowBasedLaw
      fullSubHighBasedLaw hfullSubLowFreeLaw hfullSubLowBasedLaw
      hfullSubHighFreeLaw hfullSubHighBasedLaw
      hfullSubLowAtLeftThreshold hfullSubLowAtRightThreshold
      hfullSubHighAtLeftThreshold hfullSubHighAtRightThreshold
      hfullSubFreePriorMean hfullSubFreePriorVar hfullSubFreePrecision
      hfullSubFreeThresholdMean hfullSubFreeThreshold
      hfullSubBasedPriorMean hfullSubBasedPriorVar
      hfullSubBasedPrecision hfullSubBasedThresholdMean
      hfullSubBasedThreshold hshareA hshareB hcapacity1 hcut1A hcut1B
      hcapacity2 hcut2A hcut2B
  let hJ2Pair :=
    (paper_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_components
      standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
      subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback diversity J1 J2 groupA groupB
      populationShare fullFullCutoff fullSubCutoff
      standardGaussianHazardCertificate J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hJ1_ne_J2
      (capacity2 := capacity2)).mpr
      ⟨⟨hJ2MassB, hJ2MeritGtB⟩, ⟨hJ2MassA, hJ2MeritGtA⟩⟩
  base hJ2Pair.1 hJ2Pair.2 hthreshold.1 hthreshold.2.1
    hthreshold.2.2.1 hthreshold.2.2.2

/--
Standard-Gaussian Theorem 3 endpoint specialized to the paper's named groups,
named schools, and population-share row `(1 - pi, pi)`.

This is the concrete-paper companion to
`paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components`.
It discharges the generic school-distinctness and positive-share proof
obligations from the named paper objects and the source assumption
`pi ∈ (0, 1)`.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools
    {FeatureDrop FeatureKeep LowFreeFeature HighFreeFeature LowBasedFeature
      HighBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
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
    (subFullMeritOfCutoff : GLM20Group → ℝ → ℝ)
    (subFullTestFreeMerit : GLM20Group → ℝ)
    (fullSubLowFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily LowFreeFeature)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubHighBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
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
    (fullSubLowBasedLaw fullSubHighBasedLaw :
      GLM20Group → GaussianScaleLaw)
    (hfullSubLowFreeLaw :
      ∀ g, (fullSubLowFreeFamily g).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubLowBasedLaw :
      ∀ g c, (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubHighFreeLaw :
      ∀ g, (fullSubHighFreeFamily g).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubHighBasedLaw :
      ∀ g c, (fullSubHighBasedFamily g c).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubLowAtLeftThreshold :
      ∀ g, fullSubLowFreeThreshold g <
        fullSubLowBasedThresholdIntercept g -
          fullSubLowBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubLowAtRightThreshold :
      ∀ g,
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * fullSubRightCost g <
          fullSubLowFreeThreshold g)
    (hfullSubHighAtLeftThreshold :
      ∀ g, fullSubHighFreeThreshold g <
        fullSubHighBasedThresholdIntercept g -
          fullSubHighBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubHighAtRightThreshold :
      ∀ g,
        fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * fullSubRightCost g <
          fullSubHighFreeThreshold g)
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
          fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c)
    (hfullSubBasedThreshold :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c ≤
          fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * c)
    (hfullSubLowBasedThresholdSlope :
      ∀ g, 0 < fullSubLowBasedThresholdSlope g)
    (hfullSubHighBasedThresholdSlope :
      ∀ g, 0 < fullSubHighBasedThresholdSlope g)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacity1 :
      capacity1 =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupA) q1Sub +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupB) q1Sub)
    (hcut1A : fullFullCutoff GLM20Group.groupA ≤ q1Sub)
    (hcut1B : fullFullCutoff GLM20Group.groupB ≤ q1Sub)
    (hcapacity2 :
      capacity2 =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupA) q2Sub +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupB) q2Sub)
    (hcut2A : fullFullCutoff GLM20Group.groupA ≤ q2Sub)
    (hcut2B : fullFullCutoff GLM20Group.groupB ≤ q2Sub)
    (hJ2MassB : subFullMass GLM20Group.groupB ≥ capacity2)
    (hJ2MeritGtB :
      glm20Theorem3PopulationShare pi GLM20Group.groupB *
          subFullMeritBase glm20SchoolJ2 GLM20Group.groupB >
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            subSubMerit glm20SchoolJ2 GLM20Group.groupA +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            subSubMerit glm20SchoolJ2 GLM20Group.groupB)
    (hJ2MassA : subFullMass GLM20Group.groupA ≥ capacity2)
    (hJ2MeritGtA :
      glm20Theorem3PopulationShare pi GLM20Group.groupA *
          subFullMeritBase glm20SchoolJ2 GLM20Group.groupA >
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            subSubMerit glm20SchoolJ2 GLM20Group.groupA +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            subSubMerit glm20SchoolJ2 GLM20Group.groupB) :=
  let hshares := glm20Theorem3PopulationShare_pos_of_pi_mem_Ioo hpi
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components
    (Group := GLM20Group) (School := GLM20School)
    (FeatureDrop := FeatureDrop) (FeatureKeep := FeatureKeep)
    (LowFreeFeature := LowFreeFeature)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (HighBasedFeature := HighBasedFeature)
    (J1 := glm20SchoolJ1) (J2 := glm20SchoolJ2)
    (groupA := GLM20Group.groupA) (groupB := GLM20Group.groupB)
    (populationShare := glm20Theorem3PopulationShare pi)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
    J1KeepThreshold J2DropThreshold J2KeepThreshold glm20SchoolJ1_ne_J2
    hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
    hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision
    hJ2ThresholdMean hJ2Threshold subFullMeritOfCutoff
    subFullTestFreeMerit fullSubLowFreeFamily fullSubHighFreeFamily
    fullSubLowFreeThreshold fullSubHighFreeThreshold
    fullSubLowBasedFamily fullSubHighBasedFamily
    fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
    fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
    hsubFullLeftRight hsubFullLeftPos hsubFullRightLtV2 hsubFullCostMem
    hsubFullScale hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft
    hsubFullAtRight hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
    fullSubLowBasedLaw fullSubHighBasedLaw hfullSubLowFreeLaw
    hfullSubLowBasedLaw hfullSubHighFreeLaw hfullSubHighBasedLaw
    hfullSubLowAtLeftThreshold hfullSubLowAtRightThreshold
    hfullSubHighAtLeftThreshold hfullSubHighAtRightThreshold
    hfullSubFreePriorMean hfullSubFreePriorVar hfullSubFreePrecision
    hfullSubFreeThresholdMean hfullSubFreeThreshold
    hfullSubBasedPriorMean hfullSubBasedPriorVar
    hfullSubBasedPrecision hfullSubBasedThresholdMean
    hfullSubBasedThreshold hfullSubLowBasedThresholdSlope
    hfullSubHighBasedThresholdSlope hshares.1 hshares.2 hcapacity1 hcut1A
  hcut1B hcapacity2 hcut2A hcut2B hJ2MassB hJ2MeritGtB hJ2MassA
    hJ2MeritGtA

/--
Paper-group Theorem 3 endpoint where the test-keeping source families are
constructed by adding one extra Gaussian signal to the corresponding
test-dropping source families.

This discharges the common-prior and strict precision-increase premises for
the `J1` and `J2` fixed-pool Theorem 2 comparisons from the paper-native fact
that `P_full` observes one additional positive-variance signal.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_signals
    {FeatureDrop LowFreeFeature HighFreeFeature LowBasedFeature
      HighBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hkeepSignalRows :
      GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold)
    (subFullMeritOfCutoff : GLM20Group → ℝ → ℝ)
    (subFullTestFreeMerit : GLM20Group → ℝ)
    (fullSubLowFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily LowFreeFeature)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubHighBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
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
    (fullSubLowBasedLaw fullSubHighBasedLaw :
      GLM20Group → GaussianScaleLaw)
    (hfullSubLowFreeLaw :
      ∀ g, (fullSubLowFreeFamily g).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubLowBasedLaw :
      ∀ g c, (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubHighFreeLaw :
      ∀ g, (fullSubHighFreeFamily g).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubHighBasedLaw :
      ∀ g c, (fullSubHighBasedFamily g c).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubLowAtLeftThreshold :
      ∀ g, fullSubLowFreeThreshold g <
        fullSubLowBasedThresholdIntercept g -
          fullSubLowBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubLowAtRightThreshold :
      ∀ g,
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * fullSubRightCost g <
          fullSubLowFreeThreshold g)
    (hfullSubHighAtLeftThreshold :
      ∀ g, fullSubHighFreeThreshold g <
        fullSubHighBasedThresholdIntercept g -
          fullSubHighBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubHighAtRightThreshold :
      ∀ g,
        fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * fullSubRightCost g <
          fullSubHighFreeThreshold g)
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
          fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c)
    (hfullSubBasedThreshold :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c ≤
          fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * c)
    (hfullSubLowBasedThresholdSlope :
      ∀ g, 0 < fullSubLowBasedThresholdSlope g)
    (hfullSubHighBasedThresholdSlope :
      ∀ g, 0 < fullSubHighBasedThresholdSlope g)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacity1 :
      capacity1 =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupA) q1Sub +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupB) q1Sub)
    (hcut1A : fullFullCutoff GLM20Group.groupA ≤ q1Sub)
    (hcut1B : fullFullCutoff GLM20Group.groupB ≤ q1Sub)
    (hcapacity2 :
      capacity2 =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupA) q2Sub +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupB) q2Sub)
    (hcut2A : fullFullCutoff GLM20Group.groupA ≤ q2Sub)
    (hcut2B : fullFullCutoff GLM20Group.groupB ≤ q2Sub)
    (hJ2MassB : subFullMass GLM20Group.groupB ≥ capacity2)
    (hJ2MeritGtB :
      glm20Theorem3PopulationShare pi GLM20Group.groupB *
          subFullMeritBase glm20SchoolJ2 GLM20Group.groupB >
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            subSubMerit glm20SchoolJ2 GLM20Group.groupA +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            subSubMerit glm20SchoolJ2 GLM20Group.groupB)
    (hJ2MassA : subFullMass GLM20Group.groupA ≥ capacity2)
    (hJ2MeritGtA :
      glm20Theorem3PopulationShare pi GLM20Group.groupA *
          subFullMeritBase glm20SchoolJ2 GLM20Group.groupA >
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            subSubMerit glm20SchoolJ2 GLM20Group.groupA +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            subSubMerit glm20SchoolJ2 GLM20Group.groupB) :=
  let hkeepRows := paper_theorem3_keep_signal_rows_components
    hkeepSignalRows
  let hJ1ExtraNoiseVar := hkeepRows.1
  let hJ2ExtraNoiseVar := hkeepRows.2.1
  let hJ1ThresholdMean := hkeepRows.2.2.1
  let hJ1Threshold := hkeepRows.2.2.2.1
  let hJ2ThresholdMean := hkeepRows.2.2.2.2.1
  let hJ2Threshold := hkeepRows.2.2.2.2.2
  let J1KeepFamily : GLM20Group → GaussianOffsetSignalFamily (Option FeatureDrop) :=
    fun g =>
      (J1DropFamily g).withExtraSignal (J1ExtraNoiseMean g)
        (J1ExtraNoiseVar g) (hJ1ExtraNoiseVar g)
  let J2KeepFamily : GLM20Group → GaussianOffsetSignalFamily (Option FeatureDrop) :=
    fun g =>
      (J2DropFamily g).withExtraSignal (J2ExtraNoiseMean g)
        (J2ExtraNoiseVar g) (hJ2ExtraNoiseVar g)
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools
    (FeatureDrop := FeatureDrop) (FeatureKeep := Option FeatureDrop)
    (LowFreeFeature := LowFreeFeature)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (HighBasedFeature := HighBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
    J1KeepThreshold J2DropThreshold J2KeepThreshold
    (by intro g; rfl) (by intro g; rfl)
    (by
      intro g
      exact
        GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
          (J1DropFamily g) (J1ExtraNoiseMean g) (J1ExtraNoiseVar g)
          (hJ1ExtraNoiseVar g))
    hJ1ThresholdMean hJ1Threshold
    (by intro g; rfl) (by intro g; rfl)
    (by
      intro g
      exact
        GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
          (J2DropFamily g) (J2ExtraNoiseMean g) (J2ExtraNoiseVar g)
          (hJ2ExtraNoiseVar g))
    hJ2ThresholdMean hJ2Threshold subFullMeritOfCutoff
    subFullTestFreeMerit fullSubLowFreeFamily fullSubHighFreeFamily
    fullSubLowFreeThreshold fullSubHighFreeThreshold
    fullSubLowBasedFamily fullSubHighBasedFamily
    fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
    fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
    hsubFullLeftRight hsubFullLeftPos hsubFullRightLtV2 hsubFullCostMem
    hsubFullScale hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft
    hsubFullAtRight hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
    fullSubLowBasedLaw fullSubHighBasedLaw hfullSubLowFreeLaw
    hfullSubLowBasedLaw hfullSubHighFreeLaw hfullSubHighBasedLaw
    hfullSubLowAtLeftThreshold hfullSubLowAtRightThreshold
    hfullSubHighAtLeftThreshold hfullSubHighAtRightThreshold
    hfullSubFreePriorMean hfullSubFreePriorVar hfullSubFreePrecision
    hfullSubFreeThresholdMean hfullSubFreeThreshold
    hfullSubBasedPriorMean hfullSubBasedPriorVar
    hfullSubBasedPrecision hfullSubBasedThresholdMean
    hfullSubBasedThreshold hfullSubLowBasedThresholdSlope
    hfullSubHighBasedThresholdSlope hpi hcapacity1 hcut1A hcut1B
    hcapacity2 hcut2A hcut2B hJ2MassB hJ2MeritGtB hJ2MassA
    hJ2MeritGtA

/--
Paper-group Theorem 3 endpoint where both the fixed-pool keep-test families
and the full-sub low/high comparison families are generated by adding one
extra Gaussian signal in the paper-directed precision order.

The test-free full-sub row constructs the more precise low family from the
high family.  The cost-indexed based row constructs the more precise high
family from the low family.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_and_fullSub_signals
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hkeepSignalRows :
      GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold)
    (subFullMeritOfCutoff : GLM20Group → ℝ → ℝ)
    (subFullTestFreeMerit : GLM20Group → ℝ)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (hfullSubFreeExtraNoiseVar :
      ∀ g, 0 < fullSubFreeExtraNoiseVar g)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (hfullSubBasedExtraNoiseVar :
      ∀ g c, 0 < fullSubBasedExtraNoiseVar g c)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
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
    (fullSubLowBasedLaw fullSubHighBasedLaw :
      GLM20Group → GaussianScaleLaw)
    (hfullSubLowFreeLaw :
      ∀ g,
        ((fullSubHighFreeFamily g).withExtraSignal
            (fullSubFreeExtraNoiseMean g) (fullSubFreeExtraNoiseVar g)
            (hfullSubFreeExtraNoiseVar g)).posteriorMeanScaleLaw =
          fullSubLowBasedLaw g)
    (hfullSubLowBasedLaw :
      ∀ g c, (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
        fullSubLowBasedLaw g)
    (hfullSubHighFreeLaw :
      ∀ g, (fullSubHighFreeFamily g).posteriorMeanScaleLaw =
        fullSubHighBasedLaw g)
    (hfullSubHighBasedLaw :
      ∀ g c,
        ((fullSubLowBasedFamily g c).withExtraSignal
            (fullSubBasedExtraNoiseMean g c)
            (fullSubBasedExtraNoiseVar g c)
            (hfullSubBasedExtraNoiseVar g c)).posteriorMeanScaleLaw =
          fullSubHighBasedLaw g)
    (hfullSubLowAtLeftThreshold :
      ∀ g, fullSubLowFreeThreshold g <
        fullSubLowBasedThresholdIntercept g -
          fullSubLowBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubLowAtRightThreshold :
      ∀ g,
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * fullSubRightCost g <
          fullSubLowFreeThreshold g)
    (hfullSubHighAtLeftThreshold :
      ∀ g, fullSubHighFreeThreshold g <
        fullSubHighBasedThresholdIntercept g -
          fullSubHighBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubHighAtRightThreshold :
      ∀ g,
        fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * fullSubRightCost g <
          fullSubHighFreeThreshold g)
    (hfullSubFreeThresholdMean :
      ∀ g,
        (fullSubHighFreeFamily g).priorMean <
          fullSubHighFreeThreshold g)
    (hfullSubFreeThreshold :
      ∀ g, fullSubHighFreeThreshold g ≤ fullSubLowFreeThreshold g)
    (hfullSubBasedThresholdMean :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        (fullSubLowBasedFamily g c).priorMean <
          fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c)
    (hfullSubBasedThreshold :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c ≤
          fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * c)
    (hfullSubLowBasedThresholdSlope :
      ∀ g, 0 < fullSubLowBasedThresholdSlope g)
    (hfullSubHighBasedThresholdSlope :
      ∀ g, 0 < fullSubHighBasedThresholdSlope g)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacity1 :
      capacity1 =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupA) q1Sub +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupB) q1Sub)
    (hcut1A : fullFullCutoff GLM20Group.groupA ≤ q1Sub)
    (hcut1B : fullFullCutoff GLM20Group.groupB ≤ q1Sub)
    (hcapacity2 :
      capacity2 =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupA) q2Sub +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupB) q2Sub)
    (hcut2A : fullFullCutoff GLM20Group.groupA ≤ q2Sub)
    (hcut2B : fullFullCutoff GLM20Group.groupB ≤ q2Sub)
    (hJ2MassB : subFullMass GLM20Group.groupB ≥ capacity2)
    (hJ2MeritGtB :
      glm20Theorem3PopulationShare pi GLM20Group.groupB *
          subFullMeritBase glm20SchoolJ2 GLM20Group.groupB >
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            subSubMerit glm20SchoolJ2 GLM20Group.groupA +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            subSubMerit glm20SchoolJ2 GLM20Group.groupB)
    (hJ2MassA : subFullMass GLM20Group.groupA ≥ capacity2)
    (hJ2MeritGtA :
      glm20Theorem3PopulationShare pi GLM20Group.groupA *
          subFullMeritBase glm20SchoolJ2 GLM20Group.groupA >
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            subSubMerit glm20SchoolJ2 GLM20Group.groupA +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            subSubMerit glm20SchoolJ2 GLM20Group.groupB) :=
  let fullSubLowFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily (Option HighFreeFeature) :=
    fun g =>
      (fullSubHighFreeFamily g).withExtraSignal
        (fullSubFreeExtraNoiseMean g) (fullSubFreeExtraNoiseVar g)
        (hfullSubFreeExtraNoiseVar g)
  let fullSubHighBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily (Option LowBasedFeature) :=
    fun g c =>
      (fullSubLowBasedFamily g c).withExtraSignal
        (fullSubBasedExtraNoiseMean g c)
        (fullSubBasedExtraNoiseVar g c)
        (hfullSubBasedExtraNoiseVar g c)
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_signals
    (FeatureDrop := FeatureDrop)
    (LowFreeFeature := Option HighFreeFeature)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (HighBasedFeature := Option LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar J1DropThreshold J1KeepThreshold J2DropThreshold
    J2KeepThreshold hkeepSignalRows
    subFullMeritOfCutoff
    subFullTestFreeMerit fullSubLowFreeFamily fullSubHighFreeFamily
    fullSubLowFreeThreshold fullSubHighFreeThreshold
    fullSubLowBasedFamily fullSubHighBasedFamily
    fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
    fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
    hsubFullLeftRight hsubFullLeftPos hsubFullRightLtV2 hsubFullCostMem
    hsubFullScale hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft
    hsubFullAtRight hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
    fullSubLowBasedLaw fullSubHighBasedLaw
    (by
      intro g
      simpa [fullSubLowFreeFamily] using hfullSubLowFreeLaw g)
    hfullSubLowBasedLaw hfullSubHighFreeLaw
    (by
      intro g c
      simpa [fullSubHighBasedFamily] using hfullSubHighBasedLaw g c)
    hfullSubLowAtLeftThreshold hfullSubLowAtRightThreshold
    hfullSubHighAtLeftThreshold hfullSubHighAtRightThreshold
    (by intro g; rfl) (by intro g; rfl)
    (by
      intro g
      exact
        GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
          (fullSubHighFreeFamily g) (fullSubFreeExtraNoiseMean g)
          (fullSubFreeExtraNoiseVar g) (hfullSubFreeExtraNoiseVar g))
    hfullSubFreeThresholdMean hfullSubFreeThreshold
    (by intro g c hc; rfl) (by intro g c hc; rfl)
    (by
      intro g c hc
      exact
        GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
          (fullSubLowBasedFamily g c) (fullSubBasedExtraNoiseMean g c)
          (fullSubBasedExtraNoiseVar g c)
          (hfullSubBasedExtraNoiseVar g c))
    hfullSubBasedThresholdMean hfullSubBasedThreshold
    hfullSubLowBasedThresholdSlope hfullSubHighBasedThresholdSlope hpi
    hcapacity1 hcut1A hcut1B hcapacity2 hcut2A hcut2B hJ2MassB
    hJ2MeritGtB hJ2MassA hJ2MeritGtA

/--
Paper-group Theorem 3 endpoint with canonical fixed posterior laws for the
full-sub low/high rows.

This is the same extra-signal surface as
`paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_and_fullSub_signals`,
but the auxiliary fixed-law functions are chosen definitionally from the free
families, leaving only the based-family law-identification rows exposed.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hkeepSignalRows :
      GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold)
    (subFullMeritOfCutoff : GLM20Group → ℝ → ℝ)
    (subFullTestFreeMerit : GLM20Group → ℝ)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (hfullSubFreeExtraNoiseVar :
      ∀ g, 0 < fullSubFreeExtraNoiseVar g)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (hfullSubBasedExtraNoiseVar :
      ∀ g c, 0 < fullSubBasedExtraNoiseVar g c)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
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
    (hfullSubLowBasedLaw :
      ∀ g c,
        (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
          ((fullSubHighFreeFamily g).withExtraSignal
            (fullSubFreeExtraNoiseMean g) (fullSubFreeExtraNoiseVar g)
            (hfullSubFreeExtraNoiseVar g)).posteriorMeanScaleLaw)
    (hfullSubHighBasedLaw :
      ∀ g c,
        ((fullSubLowBasedFamily g c).withExtraSignal
            (fullSubBasedExtraNoiseMean g c)
            (fullSubBasedExtraNoiseVar g c)
            (hfullSubBasedExtraNoiseVar g c)).posteriorMeanScaleLaw =
          (fullSubHighFreeFamily g).posteriorMeanScaleLaw)
    (hfullSubLowAtLeftThreshold :
      ∀ g, fullSubLowFreeThreshold g <
        fullSubLowBasedThresholdIntercept g -
          fullSubLowBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubLowAtRightThreshold :
      ∀ g,
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * fullSubRightCost g <
          fullSubLowFreeThreshold g)
    (hfullSubHighAtLeftThreshold :
      ∀ g, fullSubHighFreeThreshold g <
        fullSubHighBasedThresholdIntercept g -
          fullSubHighBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubHighAtRightThreshold :
      ∀ g,
        fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * fullSubRightCost g <
          fullSubHighFreeThreshold g)
    (hfullSubFreeThresholdMean :
      ∀ g,
        (fullSubHighFreeFamily g).priorMean <
          fullSubHighFreeThreshold g)
    (hfullSubFreeThreshold :
      ∀ g, fullSubHighFreeThreshold g ≤ fullSubLowFreeThreshold g)
    (hfullSubBasedThresholdMean :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        (fullSubLowBasedFamily g c).priorMean <
          fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c)
    (hfullSubBasedThreshold :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c ≤
          fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * c)
    (hfullSubLowBasedThresholdSlope :
      ∀ g, 0 < fullSubLowBasedThresholdSlope g)
    (hfullSubHighBasedThresholdSlope :
      ∀ g, 0 < fullSubHighBasedThresholdSlope g)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacity1 :
      capacity1 =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupA) q1Sub +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupB) q1Sub)
    (hcut1A : fullFullCutoff GLM20Group.groupA ≤ q1Sub)
    (hcut1B : fullFullCutoff GLM20Group.groupB ≤ q1Sub)
    (hcapacity2 :
      capacity2 =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupA) q2Sub +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupB) q2Sub)
    (hcut2A : fullFullCutoff GLM20Group.groupA ≤ q2Sub)
    (hcut2B : fullFullCutoff GLM20Group.groupB ≤ q2Sub)
    (hJ2MassB : subFullMass GLM20Group.groupB ≥ capacity2)
    (hJ2MeritGtB :
      glm20Theorem3PopulationShare pi GLM20Group.groupB *
          subFullMeritBase glm20SchoolJ2 GLM20Group.groupB >
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            subSubMerit glm20SchoolJ2 GLM20Group.groupA +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            subSubMerit glm20SchoolJ2 GLM20Group.groupB)
    (hJ2MassA : subFullMass GLM20Group.groupA ≥ capacity2)
    (hJ2MeritGtA :
      glm20Theorem3PopulationShare pi GLM20Group.groupA *
          subFullMeritBase glm20SchoolJ2 GLM20Group.groupA >
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            subSubMerit glm20SchoolJ2 GLM20Group.groupA +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            subSubMerit glm20SchoolJ2 GLM20Group.groupB) :=
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_and_fullSub_signals
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar J1DropThreshold J1KeepThreshold J2DropThreshold
    J2KeepThreshold hkeepSignalRows
    subFullMeritOfCutoff
    subFullTestFreeMerit fullSubHighFreeFamily fullSubFreeExtraNoiseMean
    fullSubFreeExtraNoiseVar hfullSubFreeExtraNoiseVar
    fullSubLowFreeThreshold fullSubHighFreeThreshold fullSubLowBasedFamily
    fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
    hfullSubBasedExtraNoiseVar fullSubLowBasedThresholdIntercept
    fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
    fullSubHighBasedThresholdSlope hsubFullLeftRight hsubFullLeftPos
    hsubFullRightLtV2 hsubFullCostMem hsubFullScale hsubFullMeritCont
    hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight hfullSubLeftRight
    hfullSubLeftPos hfullSubCostMem
    (fun g =>
      ((fullSubHighFreeFamily g).withExtraSignal
        (fullSubFreeExtraNoiseMean g) (fullSubFreeExtraNoiseVar g)
        (hfullSubFreeExtraNoiseVar g)).posteriorMeanScaleLaw)
    (fun g => (fullSubHighFreeFamily g).posteriorMeanScaleLaw)
    (by intro g; rfl)
    (by
      intro g c
      exact hfullSubLowBasedLaw g c)
    (by intro g; rfl)
    (by
      intro g c
      exact hfullSubHighBasedLaw g c)
    hfullSubLowAtLeftThreshold hfullSubLowAtRightThreshold
    hfullSubHighAtLeftThreshold hfullSubHighAtRightThreshold
    hfullSubFreeThresholdMean hfullSubFreeThreshold
    hfullSubBasedThresholdMean hfullSubBasedThreshold
    hfullSubLowBasedThresholdSlope hfullSubHighBasedThresholdSlope hpi
    hcapacity1 hcut1A hcut1B hcapacity2 hcut2A hcut2B hJ2MassB
    hJ2MeritGtB hJ2MassA hJ2MeritGtA

/--
Paper-group Theorem 3 endpoint with the sub/full admitted-merit row generated
from a fixed Gaussian posterior law and an affine decreasing threshold.

This discharges the abstract `subFullMeritOfCutoff` continuity,
strict-antitonicity, and endpoint-crossing premises from the standard-Gaussian
upper-tail-mean formula plus two displayed threshold-order assumptions.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hkeepSignalRows :
      GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (hsubFullAffineTailRows :
      GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
        subFullLeftCost subFullRightCost subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (hfullSubFreeExtraNoiseVar :
      ∀ g, 0 < fullSubFreeExtraNoiseVar g)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (hfullSubBasedExtraNoiseVar :
      ∀ g c, 0 < fullSubBasedExtraNoiseVar g c)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
    (hsubFullLeftRight :
      ∀ g, subFullLeftCost g < subFullRightCost g)
    (hsubFullLeftPos : ∀ g, 0 < subFullLeftCost g)
    (hsubFullRightLtV2 :
      ∀ g, subFullRightCost g < subFullV2 g)
    (hsubFullCostMem :
      ∀ g, testCost g ∈
        Set.Icc (subFullLeftCost g) (subFullRightCost g))
    (hfullSubLeftRight :
      ∀ g, fullSubLeftCost g < fullSubRightCost g)
    (hfullSubLeftPos : ∀ g, 0 < fullSubLeftCost g)
    (hfullSubCostMem :
      ∀ g, testCost g ∈
        Set.Icc (fullSubLeftCost g) (fullSubRightCost g))
    (hfullSubLowBasedLaw :
      ∀ g c,
        (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
          ((fullSubHighFreeFamily g).withExtraSignal
            (fullSubFreeExtraNoiseMean g) (fullSubFreeExtraNoiseVar g)
            (hfullSubFreeExtraNoiseVar g)).posteriorMeanScaleLaw)
    (hfullSubHighBasedLaw :
      ∀ g c,
        ((fullSubLowBasedFamily g c).withExtraSignal
            (fullSubBasedExtraNoiseMean g c)
            (fullSubBasedExtraNoiseVar g c)
            (hfullSubBasedExtraNoiseVar g c)).posteriorMeanScaleLaw =
          (fullSubHighFreeFamily g).posteriorMeanScaleLaw)
    (hfullSubLowAtLeftThreshold :
      ∀ g, fullSubLowFreeThreshold g <
        fullSubLowBasedThresholdIntercept g -
          fullSubLowBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubLowAtRightThreshold :
      ∀ g,
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * fullSubRightCost g <
          fullSubLowFreeThreshold g)
    (hfullSubHighAtLeftThreshold :
      ∀ g, fullSubHighFreeThreshold g <
        fullSubHighBasedThresholdIntercept g -
          fullSubHighBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubHighAtRightThreshold :
      ∀ g,
        fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * fullSubRightCost g <
          fullSubHighFreeThreshold g)
    (hfullSubFreeThresholdMean :
      ∀ g,
        (fullSubHighFreeFamily g).priorMean <
          fullSubHighFreeThreshold g)
    (hfullSubFreeThreshold :
      ∀ g, fullSubHighFreeThreshold g ≤ fullSubLowFreeThreshold g)
    (hfullSubBasedThresholdMean :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        (fullSubLowBasedFamily g c).priorMean <
          fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c)
    (hfullSubBasedThreshold :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c ≤
          fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * c)
    (hfullSubLowBasedThresholdSlope :
      ∀ g, 0 < fullSubLowBasedThresholdSlope g)
    (hfullSubHighBasedThresholdSlope :
      ∀ g, 0 < fullSubHighBasedThresholdSlope g)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacity1 :
      capacity1 =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupA) q1Sub +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupB) q1Sub)
    (hcut1A : fullFullCutoff GLM20Group.groupA ≤ q1Sub)
    (hcut1B : fullFullCutoff GLM20Group.groupB ≤ q1Sub)
    (hcapacity2 :
      capacity2 =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupA) q2Sub +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupB) q2Sub)
    (hcut2A : fullFullCutoff GLM20Group.groupA ≤ q2Sub)
    (hcut2B : fullFullCutoff GLM20Group.groupB ≤ q2Sub)
    (hJ2MassB : subFullMass GLM20Group.groupB ≥ capacity2)
    (hJ2MeritGtB :
      glm20Theorem3PopulationShare pi GLM20Group.groupB *
          subFullMeritBase glm20SchoolJ2 GLM20Group.groupB >
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            subSubMerit glm20SchoolJ2 GLM20Group.groupA +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            subSubMerit glm20SchoolJ2 GLM20Group.groupB)
    (hJ2MassA : subFullMass GLM20Group.groupA ≥ capacity2)
    (hJ2MeritGtA :
      glm20Theorem3PopulationShare pi GLM20Group.groupA *
          subFullMeritBase glm20SchoolJ2 GLM20Group.groupA >
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            subSubMerit glm20SchoolJ2 GLM20Group.groupA +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            subSubMerit glm20SchoolJ2 GLM20Group.groupB) :=
  let hkeepRows := paper_theorem3_keep_signal_rows_components
    hkeepSignalRows
  let hJ1ExtraNoiseVar := hkeepRows.1
  let hJ2ExtraNoiseVar := hkeepRows.2.1
  let hJ1ThresholdMean := hkeepRows.2.2.1
  let hJ1Threshold := hkeepRows.2.2.2.1
  let hJ2ThresholdMean := hkeepRows.2.2.2.2.1
  let hJ2Threshold := hkeepRows.2.2.2.2.2
  let hsubFullRows :=
    paper_theorem3_subFull_affine_tail_rows_components
      hsubFullAffineTailRows
  let hsubFullScale := hsubFullRows.1
  let hsubFullBasedThresholdSlope := hsubFullRows.2.1
  let hsubFullAtLeftThreshold := hsubFullRows.2.2.1
  let hsubFullAtRightThreshold := hsubFullRows.2.2.2
  let subFullMeritOfCutoff : GLM20Group → ℝ → ℝ := fun g q =>
    standardGaussianHazardCertificate.normalUpperTailMean
      (subFullLaw g)
      (subFullBasedThresholdIntercept g -
        subFullBasedThresholdSlope g * q)
  let subFullTestFreeMerit : GLM20Group → ℝ := fun g =>
    standardGaussianHazardCertificate.normalUpperTailMean
      (subFullLaw g) (subFullFreeThreshold g)
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar J1DropThreshold J1KeepThreshold J2DropThreshold
    J2KeepThreshold hkeepSignalRows subFullMeritOfCutoff
    subFullTestFreeMerit fullSubHighFreeFamily fullSubFreeExtraNoiseMean
    fullSubFreeExtraNoiseVar hfullSubFreeExtraNoiseVar
    fullSubLowFreeThreshold fullSubHighFreeThreshold fullSubLowBasedFamily
    fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
    hfullSubBasedExtraNoiseVar fullSubLowBasedThresholdIntercept
    fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
    fullSubHighBasedThresholdSlope hsubFullLeftRight hsubFullLeftPos
    hsubFullRightLtV2 hsubFullCostMem hsubFullScale
    (by
      intro g
      dsimp [subFullMeritOfCutoff]
      exact
        (paper_standardGaussian_normalUpperTailMean_continuous_threshold
          (subFullLaw g)).comp
          (by
            fun_prop))
    (by
      intro g x y hxy
      dsimp [subFullMeritOfCutoff]
      have hmul :
          subFullBasedThresholdSlope g * x <
            subFullBasedThresholdSlope g * y :=
        mul_lt_mul_of_pos_left hxy (hsubFullBasedThresholdSlope g)
      have hthreshold :
          subFullBasedThresholdIntercept g -
              subFullBasedThresholdSlope g * y <
            subFullBasedThresholdIntercept g -
              subFullBasedThresholdSlope g * x := by
        nlinarith
      exact
        (paper_proposition8_standardGaussian_normalUpperTailMean_strictMono_threshold
          (subFullLaw g)) hthreshold)
    (by
      intro g
      dsimp [subFullMeritOfCutoff, subFullTestFreeMerit]
      exact
        (paper_proposition8_standardGaussian_normalUpperTailMean_strictMono_threshold
          (subFullLaw g)) (hsubFullAtLeftThreshold g))
    (by
      intro g
      dsimp [subFullMeritOfCutoff, subFullTestFreeMerit]
      exact
        (paper_proposition8_standardGaussian_normalUpperTailMean_strictMono_threshold
          (subFullLaw g)) (hsubFullAtRightThreshold g))
    hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
    hfullSubLowBasedLaw hfullSubHighBasedLaw
    hfullSubLowAtLeftThreshold hfullSubLowAtRightThreshold
    hfullSubHighAtLeftThreshold hfullSubHighAtRightThreshold
    hfullSubFreeThresholdMean hfullSubFreeThreshold
    hfullSubBasedThresholdMean hfullSubBasedThreshold
    hfullSubLowBasedThresholdSlope hfullSubHighBasedThresholdSlope hpi
    hcapacity1 hcut1A hcut1B hcapacity2 hcut2A hcut2B hJ2MassB
    hJ2MeritGtB hJ2MassA hJ2MeritGtA

/--
Paper-group Theorem 3 endpoint with the same strongest fixed-law and
sub/full tail-mean surface as
`paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean`,
but exposing condition-(11)--(12) through the generated source-family
school-`J2` keep-test pair rather than the four raw survivor component rows.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_j2_keeps_test_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (hJ1ExtraNoiseVar : ∀ g, 0 < J1ExtraNoiseVar g)
    (hJ2ExtraNoiseVar : ∀ g, 0 < J2ExtraNoiseVar g)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hJ1ThresholdMean :
      ∀ g, (J1DropFamily g).priorMean < J1DropThreshold g)
    (hJ1Threshold :
      ∀ g, J1DropThreshold g ≤ J1KeepThreshold g)
    (hJ2ThresholdMean :
      ∀ g, (J2DropFamily g).priorMean < J2DropThreshold g)
    (hJ2Threshold :
      ∀ g, J2DropThreshold g ≤ J2KeepThreshold g)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (hsubFullAffineTailRows :
      GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
        subFullLeftCost subFullRightCost subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (hfullSubFreeExtraNoiseVar :
      ∀ g, 0 < fullSubFreeExtraNoiseVar g)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (hfullSubBasedExtraNoiseVar :
      ∀ g c, 0 < fullSubBasedExtraNoiseVar g c)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
    (hsubFullLeftRight :
      ∀ g, subFullLeftCost g < subFullRightCost g)
    (hsubFullLeftPos : ∀ g, 0 < subFullLeftCost g)
    (hsubFullRightLtV2 :
      ∀ g, subFullRightCost g < subFullV2 g)
    (hsubFullCostMem :
      ∀ g, testCost g ∈
        Set.Icc (subFullLeftCost g) (subFullRightCost g))
    (hfullSubLeftRight :
      ∀ g, fullSubLeftCost g < fullSubRightCost g)
    (hfullSubLeftPos : ∀ g, 0 < fullSubLeftCost g)
    (hfullSubCostMem :
      ∀ g, testCost g ∈
        Set.Icc (fullSubLeftCost g) (fullSubRightCost g))
    (hfullSubLowBasedLaw :
      ∀ g c,
        (fullSubLowBasedFamily g c).posteriorMeanScaleLaw =
          ((fullSubHighFreeFamily g).withExtraSignal
            (fullSubFreeExtraNoiseMean g) (fullSubFreeExtraNoiseVar g)
            (hfullSubFreeExtraNoiseVar g)).posteriorMeanScaleLaw)
    (hfullSubHighBasedLaw :
      ∀ g c,
        ((fullSubLowBasedFamily g c).withExtraSignal
            (fullSubBasedExtraNoiseMean g c)
            (fullSubBasedExtraNoiseVar g c)
            (hfullSubBasedExtraNoiseVar g c)).posteriorMeanScaleLaw =
          (fullSubHighFreeFamily g).posteriorMeanScaleLaw)
    (hfullSubLowAtLeftThreshold :
      ∀ g, fullSubLowFreeThreshold g <
        fullSubLowBasedThresholdIntercept g -
          fullSubLowBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubLowAtRightThreshold :
      ∀ g,
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * fullSubRightCost g <
          fullSubLowFreeThreshold g)
    (hfullSubHighAtLeftThreshold :
      ∀ g, fullSubHighFreeThreshold g <
        fullSubHighBasedThresholdIntercept g -
          fullSubHighBasedThresholdSlope g * fullSubLeftCost g)
    (hfullSubHighAtRightThreshold :
      ∀ g,
        fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * fullSubRightCost g <
          fullSubHighFreeThreshold g)
    (hfullSubFreeThresholdMean :
      ∀ g,
        (fullSubHighFreeFamily g).priorMean <
          fullSubHighFreeThreshold g)
    (hfullSubFreeThreshold :
      ∀ g, fullSubHighFreeThreshold g ≤ fullSubLowFreeThreshold g)
    (hfullSubBasedThresholdMean :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        (fullSubLowBasedFamily g c).priorMean <
          fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c)
    (hfullSubBasedThreshold :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowBasedThresholdIntercept g -
            fullSubLowBasedThresholdSlope g * c ≤
          fullSubHighBasedThresholdIntercept g -
            fullSubHighBasedThresholdSlope g * c)
    (hfullSubLowBasedThresholdSlope :
      ∀ g, 0 < fullSubLowBasedThresholdSlope g)
    (hfullSubHighBasedThresholdSlope :
      ∀ g, 0 < fullSubHighBasedThresholdSlope g)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacityCutoffRows :
      GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
        (glm20Theorem3PopulationShare pi) subEstimateLaw
        GLM20Group.groupA GLM20Group.groupB capacity1 capacity2
        q1Sub q2Sub fullFullCutoff)
    (hJ2KeepPair :
      let J1KeepFamily : GLM20Group →
          GaussianOffsetSignalFamily (Option FeatureDrop) := fun g =>
        (J1DropFamily g).withExtraSignal (J1ExtraNoiseMean g)
          (J1ExtraNoiseVar g) (hJ1ExtraNoiseVar g)
      let J2KeepFamily : GLM20Group →
          GaussianOffsetSignalFamily (Option FeatureDrop) := fun g =>
        (J2DropFamily g).withExtraSignal (J2ExtraNoiseMean g)
          (J2ExtraNoiseVar g) (hJ2ExtraNoiseVar g)
      glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface
            standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
            subSubMerit subFullMeritBase fullSubMeritFallback
            fullFullMeritFallback diversity glm20SchoolJ1 glm20SchoolJ2
            GLM20Group.groupA GLM20Group.groupB
            (glm20Theorem3PopulationShare pi) fullFullCutoff fullSubCutoff
            standardGaussianHazardCertificate J1DropFamily J2DropFamily
            J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
            J2DropThreshold J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull glm20SchoolJ2
          GLM20Group.groupA GLM20Group.groupB
          (glm20Theorem3PopulationShare pi) capacity2
          GLM20Group.groupB ∧
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface
            standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
            subSubMerit subFullMeritBase fullSubMeritFallback
            fullFullMeritFallback diversity glm20SchoolJ1 glm20SchoolJ2
            GLM20Group.groupA GLM20Group.groupB
            (glm20Theorem3PopulationShare pi) fullFullCutoff fullSubCutoff
            standardGaussianHazardCertificate J1DropFamily J2DropFamily
            J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
            J2DropThreshold J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull glm20SchoolJ2
          GLM20Group.groupA GLM20Group.groupB
          (glm20Theorem3PopulationShare pi) capacity2
          GLM20Group.groupA) :=
  let J1KeepFamily : GLM20Group →
      GaussianOffsetSignalFamily (Option FeatureDrop) := fun g =>
    (J1DropFamily g).withExtraSignal (J1ExtraNoiseMean g)
      (J1ExtraNoiseVar g) (hJ1ExtraNoiseVar g)
  let J2KeepFamily : GLM20Group →
      GaussianOffsetSignalFamily (Option FeatureDrop) := fun g =>
    (J2DropFamily g).withExtraSignal (J2ExtraNoiseMean g)
      (J2ExtraNoiseVar g) (hJ2ExtraNoiseVar g)
  let hcomponents :=
    (paper_theorem3_source_family_policy_state_table_subFull_j2_keep_test_pair_iff_components
      standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
      subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback diversity glm20SchoolJ1 glm20SchoolJ2
      GLM20Group.groupA GLM20Group.groupB
      (glm20Theorem3PopulationShare pi) fullFullCutoff fullSubCutoff
      standardGaussianHazardCertificate J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold glm20SchoolJ1_ne_J2
      (capacity2 := capacity2)).mp hJ2KeepPair
  let hcapacityRows :=
    paper_theorem3_capacity_cutoff_rows_components hcapacityCutoffRows
  let hcapacity1 := hcapacityRows.1
  let hcut1A := hcapacityRows.2.1
  let hcut1B := hcapacityRows.2.2.1
  let hcapacity2 := hcapacityRows.2.2.2.1
  let hcut2A := hcapacityRows.2.2.2.2.1
  let hcut2B := hcapacityRows.2.2.2.2.2
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_raw_survivor_components_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar J1DropThreshold J1KeepThreshold J2DropThreshold
    J2KeepThreshold
    ⟨hJ1ExtraNoiseVar, hJ2ExtraNoiseVar, hJ1ThresholdMean,
      hJ1Threshold, hJ2ThresholdMean, hJ2Threshold⟩
    subFullLaw
    subFullBasedThresholdIntercept subFullBasedThresholdSlope
    subFullFreeThreshold hsubFullAffineTailRows
    fullSubHighFreeFamily fullSubFreeExtraNoiseMean
    fullSubFreeExtraNoiseVar hfullSubFreeExtraNoiseVar
    fullSubLowFreeThreshold fullSubHighFreeThreshold fullSubLowBasedFamily
    fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
    hfullSubBasedExtraNoiseVar fullSubLowBasedThresholdIntercept
    fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
    fullSubHighBasedThresholdSlope hsubFullLeftRight hsubFullLeftPos
    hsubFullRightLtV2 hsubFullCostMem hfullSubLeftRight hfullSubLeftPos
    hfullSubCostMem hfullSubLowBasedLaw
    hfullSubHighBasedLaw hfullSubLowAtLeftThreshold
    hfullSubLowAtRightThreshold hfullSubHighAtLeftThreshold
    hfullSubHighAtRightThreshold hfullSubFreeThresholdMean
    hfullSubFreeThreshold hfullSubBasedThresholdMean
    hfullSubBasedThreshold hfullSubLowBasedThresholdSlope
    hfullSubHighBasedThresholdSlope hpi hcapacity1 hcut1A hcut1B
    hcapacity2 hcut2A hcut2B hcomponents.1.1 hcomponents.1.2
    hcomponents.2.1 hcomponents.2.2

/--
Paper-group Theorem 3 endpoint with generated source-family school-`J2`
keep-test premises, bundled source cost bounds, and bundled full/full
capacity/cutoff rows.

This is the preferred compact surface for the current top route: it keeps the
named condition-(11)--(12) `J2` keep-test pair and replaces the seven scalar
sub/full and full/sub cost-domain assumptions by the two bundled cost-bound
predicates used elsewhere in the Theorem 3 support layer.  It also packages
the two full/full capacity equations and four cutoff-order comparisons into a
single source-row predicate.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_j2_keeps_test_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (hJ1ExtraNoiseVar : ∀ g, 0 < J1ExtraNoiseVar g)
    (hJ2ExtraNoiseVar : ∀ g, 0 < J2ExtraNoiseVar g)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hJ1ThresholdMean :
      ∀ g, (J1DropFamily g).priorMean < J1DropThreshold g)
    (hJ1Threshold :
      ∀ g, J1DropThreshold g ≤ J1KeepThreshold g)
    (hJ2ThresholdMean :
      ∀ g, (J2DropFamily g).priorMean < J2DropThreshold g)
    (hJ2Threshold :
      ∀ g, J2DropThreshold g ≤ J2KeepThreshold g)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (hsubFullAffineTailRows :
      GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
        subFullLeftCost subFullRightCost subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (hfullSubFreeExtraNoiseVar :
      ∀ g, 0 < fullSubFreeExtraNoiseVar g)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (hfullSubBasedExtraNoiseVar :
      ∀ g c, 0 < fullSubBasedExtraNoiseVar g c)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
    (hfullSubAffineThresholdRows :
      GLM20Theorem3FullSubAffineThresholdRows fullSubHighFreeFamily
        fullSubLowBasedFamily fullSubLeftCost fullSubRightCost
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope)
    (hsubFullCostBounds :
      GLM20CostBoundsBelow testCost subFullLeftCost subFullRightCost
        subFullV2)
    (hfullSubCostBounds :
      GLM20CostBounds testCost fullSubLeftCost fullSubRightCost)
    (hfullSubFixedLawRows :
      GLM20Theorem3FullSubFixedLawRows fullSubHighFreeFamily
        fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar
        hfullSubFreeExtraNoiseVar fullSubLowBasedFamily
        fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
        hfullSubBasedExtraNoiseVar)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacityCutoffRows :
      GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
        (glm20Theorem3PopulationShare pi) subEstimateLaw
        GLM20Group.groupA GLM20Group.groupB capacity1 capacity2
        q1Sub q2Sub fullFullCutoff)
    (hJ2KeepPair :
      let J1KeepFamily : GLM20Group →
          GaussianOffsetSignalFamily (Option FeatureDrop) := fun g =>
        (J1DropFamily g).withExtraSignal (J1ExtraNoiseMean g)
          (J1ExtraNoiseVar g) (hJ1ExtraNoiseVar g)
      let J2KeepFamily : GLM20Group →
          GaussianOffsetSignalFamily (Option FeatureDrop) := fun g =>
        (J2DropFamily g).withExtraSignal (J2ExtraNoiseMean g)
          (J2ExtraNoiseVar g) (hJ2ExtraNoiseVar g)
      glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface
            standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
            subSubMerit subFullMeritBase fullSubMeritFallback
            fullFullMeritFallback diversity glm20SchoolJ1 glm20SchoolJ2
            GLM20Group.groupA GLM20Group.groupB
            (glm20Theorem3PopulationShare pi) fullFullCutoff fullSubCutoff
            standardGaussianHazardCertificate J1DropFamily J2DropFamily
            J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
            J2DropThreshold J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull glm20SchoolJ2
          GLM20Group.groupA GLM20Group.groupB
          (glm20Theorem3PopulationShare pi) capacity2
          GLM20Group.groupB ∧
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3SourceFamilyPolicyStateTableSurface
            standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
            subSubMerit subFullMeritBase fullSubMeritFallback
            fullFullMeritFallback diversity glm20SchoolJ1 glm20SchoolJ2
            GLM20Group.groupA GLM20Group.groupB
            (glm20Theorem3PopulationShare pi) fullFullCutoff fullSubCutoff
            standardGaussianHazardCertificate J1DropFamily J2DropFamily
            J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
            J2DropThreshold J2KeepThreshold)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull glm20SchoolJ2
          GLM20Group.groupA GLM20Group.groupB
          (glm20Theorem3PopulationShare pi) capacity2
          GLM20Group.groupA) :=
  let hsub :=
    paper_theorem3_subFull_cost_premises_of_bounds hsubFullCostBounds
  let hfull :=
    paper_theorem3_fullSub_cost_premises_of_bounds hfullSubCostBounds
  let hfullSubFixedLaws :=
    paper_theorem3_fullSub_fixed_law_rows_components
      hfullSubFixedLawRows
  let hfullSubLowBasedLaw := hfullSubFixedLaws.1
  let hfullSubHighBasedLaw := hfullSubFixedLaws.2
  let hfullSubThresholdRows :=
    paper_theorem3_fullSub_affine_threshold_rows_components
      hfullSubAffineThresholdRows
  let hfullSubLowAtLeftThreshold := hfullSubThresholdRows.1
  let hfullSubLowAtRightThreshold := hfullSubThresholdRows.2.1
  let hfullSubHighAtLeftThreshold := hfullSubThresholdRows.2.2.1
  let hfullSubHighAtRightThreshold := hfullSubThresholdRows.2.2.2.1
  let hfullSubFreeThresholdMean := hfullSubThresholdRows.2.2.2.2.1
  let hfullSubFreeThreshold := hfullSubThresholdRows.2.2.2.2.2.1
  let hfullSubBasedThresholdMean := hfullSubThresholdRows.2.2.2.2.2.2.1
  let hfullSubBasedThreshold := hfullSubThresholdRows.2.2.2.2.2.2.2.1
  let hfullSubLowBasedThresholdSlope :=
    hfullSubThresholdRows.2.2.2.2.2.2.2.2.1
  let hfullSubHighBasedThresholdSlope :=
    hfullSubThresholdRows.2.2.2.2.2.2.2.2.2
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_j2_keeps_test_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar hJ1ExtraNoiseVar hJ2ExtraNoiseVar J1DropThreshold
    J1KeepThreshold J2DropThreshold J2KeepThreshold hJ1ThresholdMean
    hJ1Threshold hJ2ThresholdMean hJ2Threshold subFullLaw
    subFullBasedThresholdIntercept subFullBasedThresholdSlope
    subFullFreeThreshold hsubFullAffineTailRows
    fullSubHighFreeFamily fullSubFreeExtraNoiseMean
    fullSubFreeExtraNoiseVar hfullSubFreeExtraNoiseVar
    fullSubLowFreeThreshold fullSubHighFreeThreshold fullSubLowBasedFamily
    fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
    hfullSubBasedExtraNoiseVar fullSubLowBasedThresholdIntercept
    fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
    fullSubHighBasedThresholdSlope hsub.1 hsub.2.1 hsub.2.2.1
    hsub.2.2.2 hfull.1 hfull.2.1 hfull.2.2
    hfullSubLowBasedLaw hfullSubHighBasedLaw
    hfullSubLowAtLeftThreshold hfullSubLowAtRightThreshold
    hfullSubHighAtLeftThreshold hfullSubHighAtRightThreshold
    hfullSubFreeThresholdMean hfullSubFreeThreshold
    hfullSubBasedThresholdMean hfullSubBasedThreshold
    hfullSubLowBasedThresholdSlope hfullSubHighBasedThresholdSlope hpi
    hcapacityCutoffRows hJ2KeepPair

/--
Preferred feasibility-aware Theorem 3 endpoint with the school-`J2` survivor
side stated as the strict condition-(12) merit rows.

This is the compact cost-bound/capacity-row route used by the current
paper-facing theorem, but it bypasses the keep-test conversion that also
contains condition-(11)'s survivor-mass rows.  On this feasibility-aware
surface condition (11) is carried by the feasibility predicates, so the visible
school-`J2` survivor input is the smaller
`GLM20Theorem3J2StrictSurvivorMeritRows` bundle.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (hJ1ExtraNoiseVar : ∀ g, 0 < J1ExtraNoiseVar g)
    (hJ2ExtraNoiseVar : ∀ g, 0 < J2ExtraNoiseVar g)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hJ1ThresholdMean :
      ∀ g, (J1DropFamily g).priorMean < J1DropThreshold g)
    (hJ1Threshold :
      ∀ g, J1DropThreshold g ≤ J1KeepThreshold g)
    (hJ2ThresholdMean :
      ∀ g, (J2DropFamily g).priorMean < J2DropThreshold g)
    (hJ2Threshold :
      ∀ g, J2DropThreshold g ≤ J2KeepThreshold g)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (hsubFullAffineTailRows :
      GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
        subFullLeftCost subFullRightCost subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (hfullSubFreeExtraNoiseVar :
      ∀ g, 0 < fullSubFreeExtraNoiseVar g)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (hfullSubBasedExtraNoiseVar :
      ∀ g c, 0 < fullSubBasedExtraNoiseVar g c)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
    (hfullSubAffineThresholdRows :
      GLM20Theorem3FullSubAffineThresholdRows fullSubHighFreeFamily
        fullSubLowBasedFamily fullSubLeftCost fullSubRightCost
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope)
    (hsubFullCostBounds :
      GLM20CostBoundsBelow testCost subFullLeftCost subFullRightCost
        subFullV2)
    (hfullSubCostBounds :
      GLM20CostBounds testCost fullSubLeftCost fullSubRightCost)
    (hfullSubFixedLawRows :
      GLM20Theorem3FullSubFixedLawRows fullSubHighFreeFamily
        fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar
        hfullSubFreeExtraNoiseVar fullSubLowBasedFamily
        fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
        hfullSubBasedExtraNoiseVar)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacityCutoffRows :
      GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
        (glm20Theorem3PopulationShare pi) subEstimateLaw
        GLM20Group.groupA GLM20Group.groupB capacity1 capacity2
        q1Sub q2Sub fullFullCutoff)
    (hJ2StrictSurvivorMeritRows :
      GLM20Theorem3J2StrictSurvivorMeritRows
        (glm20Theorem3PopulationShare pi) subSubMerit subFullMeritBase
        glm20SchoolJ2 GLM20Group.groupA GLM20Group.groupB) :=
  let J1KeepFamily : GLM20Group →
      GaussianOffsetSignalFamily (Option FeatureDrop) := fun g =>
    (J1DropFamily g).withExtraSignal (J1ExtraNoiseMean g)
      (J1ExtraNoiseVar g) (hJ1ExtraNoiseVar g)
  let J2KeepFamily : GLM20Group →
      GaussianOffsetSignalFamily (Option FeatureDrop) := fun g =>
    (J2DropFamily g).withExtraSignal (J2ExtraNoiseMean g)
      (J2ExtraNoiseVar g) (hJ2ExtraNoiseVar g)
  let fullSubLowFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily (Option HighFreeFeature) :=
    fun g =>
      (fullSubHighFreeFamily g).withExtraSignal
        (fullSubFreeExtraNoiseMean g) (fullSubFreeExtraNoiseVar g)
        (hfullSubFreeExtraNoiseVar g)
  let fullSubHighBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily (Option LowBasedFeature) :=
    fun g c =>
      (fullSubLowBasedFamily g c).withExtraSignal
        (fullSubBasedExtraNoiseMean g c)
        (fullSubBasedExtraNoiseVar g c)
        (hfullSubBasedExtraNoiseVar g c)
  let fullSubLowBasedThreshold : GLM20Group → ℝ → ℝ := fun g c =>
    fullSubLowBasedThresholdIntercept g -
      fullSubLowBasedThresholdSlope g * c
  let fullSubHighBasedThreshold : GLM20Group → ℝ → ℝ := fun g c =>
    fullSubHighBasedThresholdIntercept g -
      fullSubHighBasedThresholdSlope g * c
  let fullSubLowBasedLaw : GLM20Group → GaussianScaleLaw := fun g =>
    (fullSubLowFreeFamily g).posteriorMeanScaleLaw
  let fullSubHighBasedLaw : GLM20Group → GaussianScaleLaw := fun g =>
    (fullSubHighFreeFamily g).posteriorMeanScaleLaw
  let hsub := paper_theorem3_subFull_cost_premises_of_bounds
    hsubFullCostBounds
  let hfull := paper_theorem3_fullSub_cost_premises_of_bounds
    hfullSubCostBounds
  let hfullSubFixedLaws :=
    paper_theorem3_fullSub_fixed_law_rows_components
      hfullSubFixedLawRows
  let hfullSubLowBasedLaw := hfullSubFixedLaws.1
  let hfullSubHighBasedLaw := hfullSubFixedLaws.2
  let hsubFullRows :=
    paper_theorem3_subFull_affine_tail_rows_components
      hsubFullAffineTailRows
  let hsubFullScale := hsubFullRows.1
  let hsubFullBasedThresholdSlope := hsubFullRows.2.1
  let hsubFullAtLeftThreshold := hsubFullRows.2.2.1
  let hsubFullAtRightThreshold := hsubFullRows.2.2.2
  let hfullSubThresholdRows :=
    paper_theorem3_fullSub_affine_threshold_rows_components
      hfullSubAffineThresholdRows
  let hfullSubLowAtLeftThreshold := hfullSubThresholdRows.1
  let hfullSubLowAtRightThreshold := hfullSubThresholdRows.2.1
  let hfullSubHighAtLeftThreshold := hfullSubThresholdRows.2.2.1
  let hfullSubHighAtRightThreshold := hfullSubThresholdRows.2.2.2.1
  let hfullSubFreeThresholdMean := hfullSubThresholdRows.2.2.2.2.1
  let hfullSubFreeThreshold := hfullSubThresholdRows.2.2.2.2.2.1
  let hfullSubBasedThresholdMean := hfullSubThresholdRows.2.2.2.2.2.2.1
  let hfullSubBasedThreshold := hfullSubThresholdRows.2.2.2.2.2.2.2.1
  let hfullSubLowBasedThresholdSlope :=
    hfullSubThresholdRows.2.2.2.2.2.2.2.2.1
  let hfullSubHighBasedThresholdSlope :=
    hfullSubThresholdRows.2.2.2.2.2.2.2.2.2
  let hthreshold :=
    paper_theorem3_low_high_based_threshold_regularities_of_affine_decreasing
      (leftCost := fullSubLeftCost) (rightCost := fullSubRightCost)
      fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
      hfullSubLowBasedThresholdSlope hfullSubHighBasedThresholdSlope
  let hcapacityRows :=
    paper_theorem3_capacity_cutoff_rows_components hcapacityCutoffRows
  let hcapacity1 := hcapacityRows.1
  let hcut1A := hcapacityRows.2.1
  let hcut1B := hcapacityRows.2.2.1
  let hcapacity2 := hcapacityRows.2.2.2.1
  let hcut2A := hcapacityRows.2.2.2.2.1
  let hcut2B := hcapacityRows.2.2.2.2.2
  let hshares := glm20Theorem3PopulationShare_pos_of_pi_mem_Ioo hpi
  let hstrict :=
    paper_theorem3_j2_strict_survivor_merit_rows_components
      hJ2StrictSurvivorMeritRows
  let subFullMeritOfCutoff : GLM20Group → ℝ → ℝ := fun g q =>
    standardGaussianHazardCertificate.normalUpperTailMean
      (subFullLaw g)
      (subFullBasedThresholdIntercept g -
        subFullBasedThresholdSlope g * q)
  let subFullTestFreeMerit : GLM20Group → ℝ := fun g =>
    standardGaussianHazardCertificate.normalUpperTailMean
      (subFullLaw g) (subFullFreeThreshold g)
  let hcross :=
    paper_standardGaussian_posterior_low_high_cost_row_endpoint_crossings_of_fixed_law_threshold_order
      (leftCost := fullSubLeftCost) (rightCost := fullSubRightCost)
      fullSubLowFreeFamily fullSubHighFreeFamily fullSubLowBasedFamily
      fullSubHighBasedFamily fullSubLowFreeThreshold
      fullSubHighFreeThreshold fullSubLowBasedThreshold
      fullSubHighBasedThreshold fullSubLowBasedLaw fullSubHighBasedLaw
      (by intro g; rfl)
      (by
        intro g c
        simpa [fullSubLowBasedLaw, fullSubLowFreeFamily] using
          hfullSubLowBasedLaw g c)
      (by intro g; rfl)
      (by
        intro g c
        simpa [fullSubHighBasedLaw, fullSubHighBasedFamily] using
          hfullSubHighBasedLaw g c)
      hfullSubLowAtLeftThreshold hfullSubLowAtRightThreshold
      hfullSubHighAtLeftThreshold hfullSubHighAtRightThreshold
  paper_theorem3_apply_fullFull_fill_of_cutoff_order_of_pos
    standardGaussianCDFAPI subEstimateLaw
    (groupA := GLM20Group.groupA) (groupB := GLM20Group.groupB)
    (populationShare := glm20Theorem3PopulationShare pi)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub)
    (fullFullCutoff := fullFullCutoff) hcapacity1 hcapacity2
    hshares.1 hshares.2 hcut1A hcut1B hcut2A hcut2B
    (fun hfillFullFull1 hfillFullFull2 =>
      paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_fill_subFull_fullSub_interval_of_fixed_law_posterior_mean_fullSub_cost_rows_of_raw_survivor_merits
        (Group := GLM20Group) (School := GLM20School)
        (FeatureDrop := FeatureDrop) (FeatureKeep := Option FeatureDrop)
        (LowFreeFeature := Option HighFreeFeature)
        (HighFreeFeature := HighFreeFeature)
        (LowBasedFeature := LowBasedFeature)
        (HighBasedFeature := Option LowBasedFeature)
        (J1 := glm20SchoolJ1) (J2 := glm20SchoolJ2)
        (groupA := GLM20Group.groupA) (groupB := GLM20Group.groupB)
        (populationShare := glm20Theorem3PopulationShare pi)
        (testCost := testCost) (subFullLeftCost := subFullLeftCost)
        (subFullRightCost := subFullRightCost)
        (fullSubLeftCost := fullSubLeftCost)
        (fullSubRightCost := fullSubRightCost)
        (capacity1 := capacity1) (capacity2 := capacity2)
        (q1Sub := q1Sub) (q2Sub := q2Sub)
        (fullFullCutoff := fullFullCutoff)
        (fullSubCutoff := fullSubCutoff)
        (subFullQ2Full := subFullQ2Full)
        (subFullScale := subFullScale) (subFullV2 := subFullV2)
        (feasible1 := feasible1) (feasible2 := feasible2)
        subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritBase fullSubMeritFallback fullFullMeritFallback
        diversity J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
        J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
        glm20SchoolJ1_ne_J2 (by intro g; rfl) (by intro g; rfl)
        (by
          intro g
          exact
            GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
              (J1DropFamily g) (J1ExtraNoiseMean g)
              (J1ExtraNoiseVar g) (hJ1ExtraNoiseVar g))
        hJ1ThresholdMean hJ1Threshold (by intro g; rfl)
        (by intro g; rfl)
        (by
          intro g
          exact
            GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
              (J2DropFamily g) (J2ExtraNoiseMean g)
              (J2ExtraNoiseVar g) (hJ2ExtraNoiseVar g))
        hJ2ThresholdMean hJ2Threshold subFullMeritOfCutoff
        subFullTestFreeMerit fullSubLowFreeFamily fullSubHighFreeFamily
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        fullSubLowBasedFamily fullSubHighBasedFamily
        fullSubLowBasedThreshold fullSubHighBasedThreshold hsub.1
        hsub.2.1 hsub.2.2.1 hsub.2.2.2 hsubFullScale
        (by
          intro g
          dsimp [subFullMeritOfCutoff]
          exact
            (paper_standardGaussian_normalUpperTailMean_continuous_threshold
              (subFullLaw g)).comp
              (by
                fun_prop))
        (by
          intro g x y hxy
          dsimp [subFullMeritOfCutoff]
          have hmul :
              subFullBasedThresholdSlope g * x <
                subFullBasedThresholdSlope g * y :=
            mul_lt_mul_of_pos_left hxy (hsubFullBasedThresholdSlope g)
          have hthreshold' :
              subFullBasedThresholdIntercept g -
                  subFullBasedThresholdSlope g * y <
                subFullBasedThresholdIntercept g -
                  subFullBasedThresholdSlope g * x := by
            nlinarith
          exact
            (paper_proposition8_standardGaussian_normalUpperTailMean_strictMono_threshold
              (subFullLaw g)) hthreshold')
        (by
          intro g
          dsimp [subFullMeritOfCutoff, subFullTestFreeMerit]
          exact
            (paper_proposition8_standardGaussian_normalUpperTailMean_strictMono_threshold
              (subFullLaw g)) (hsubFullAtLeftThreshold g))
        (by
          intro g
          dsimp [subFullMeritOfCutoff, subFullTestFreeMerit]
          exact
            (paper_proposition8_standardGaussian_normalUpperTailMean_strictMono_threshold
              (subFullLaw g)) (hsubFullAtRightThreshold g))
        hfull.1 hfull.2.1 hfull.2.2 hcross.1 hcross.2.1
        hcross.2.2.1 hcross.2.2.2 (by intro g; rfl)
        (by intro g; rfl)
        (by
          intro g
          exact
            GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
              (fullSubHighFreeFamily g) (fullSubFreeExtraNoiseMean g)
              (fullSubFreeExtraNoiseVar g)
              (hfullSubFreeExtraNoiseVar g))
        hfullSubFreeThresholdMean hfullSubFreeThreshold
        (by intro g c hc; rfl) (by intro g c hc; rfl)
        (by
          intro g c hc
          exact
            GaussianOffsetSignalFamily.signalPrecisionSum_lt_withExtraSignal
              (fullSubLowBasedFamily g c)
              (fullSubBasedExtraNoiseMean g c)
              (fullSubBasedExtraNoiseVar g c)
              (hfullSubBasedExtraNoiseVar g c))
        hfullSubBasedThresholdMean hfullSubBasedThreshold hshares.1
        hshares.2 hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
        hstrict.1 hstrict.2 fullSubLowBasedLaw fullSubHighBasedLaw
        (by
          intro g c
          simpa [fullSubLowBasedLaw, fullSubLowFreeFamily] using
            hfullSubLowBasedLaw g c)
        (by
          intro g c
          simpa [fullSubHighBasedLaw, fullSubHighBasedFamily] using
            hfullSubHighBasedLaw g c)
        hthreshold.1 hthreshold.2.1 hthreshold.2.2.1
        hthreshold.2.2.2)

/--
Preferred paper-facing Theorem 3 endpoint with condition-(11)--(12) stated as
the four displayed survivor source rows.

This is the same compact cost-bound/capacity-row route as
`paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_j2_keeps_test_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean_of_cost_bounds`,
but it exposes the school-`J2` survivor side through
`GLM20Theorem3J2SurvivorRows` instead of an internal generated-table keep-test
predicate.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hkeepSignalRows :
      GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (hsubFullAffineTailRows :
      GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
        subFullLeftCost subFullRightCost subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (hfullSubFreeExtraNoiseVar :
      ∀ g, 0 < fullSubFreeExtraNoiseVar g)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (hfullSubBasedExtraNoiseVar :
      ∀ g c, 0 < fullSubBasedExtraNoiseVar g c)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
    (hfullSubAffineThresholdRows :
      GLM20Theorem3FullSubAffineThresholdRows fullSubHighFreeFamily
        fullSubLowBasedFamily fullSubLeftCost fullSubRightCost
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope)
    (hsubFullCostBounds :
      GLM20CostBoundsBelow testCost subFullLeftCost subFullRightCost
        subFullV2)
    (hfullSubCostBounds :
      GLM20CostBounds testCost fullSubLeftCost fullSubRightCost)
    (hfullSubFixedLawRows :
      GLM20Theorem3FullSubFixedLawRows fullSubHighFreeFamily
        fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar
        hfullSubFreeExtraNoiseVar fullSubLowBasedFamily
        fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
        hfullSubBasedExtraNoiseVar)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacityCutoffRows :
      GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
        (glm20Theorem3PopulationShare pi) subEstimateLaw
        GLM20Group.groupA GLM20Group.groupB capacity1 capacity2
        q1Sub q2Sub fullFullCutoff)
    (hJ2SurvivorRows :
      GLM20Theorem3J2SurvivorRows (glm20Theorem3PopulationShare pi)
        subFullMass subSubMerit subFullMeritBase glm20SchoolJ2
        GLM20Group.groupA GLM20Group.groupB capacity2) :=
  let hkeepRows := paper_theorem3_keep_signal_rows_components
    hkeepSignalRows
  let hJ1ExtraNoiseVar := hkeepRows.1
  let hJ2ExtraNoiseVar := hkeepRows.2.1
  let hJ1ThresholdMean := hkeepRows.2.2.1
  let hJ1Threshold := hkeepRows.2.2.2.1
  let hJ2ThresholdMean := hkeepRows.2.2.2.2.1
  let hJ2Threshold := hkeepRows.2.2.2.2.2
  let J1KeepFamily : GLM20Group →
      GaussianOffsetSignalFamily (Option FeatureDrop) := fun g =>
    (J1DropFamily g).withExtraSignal (J1ExtraNoiseMean g)
      (J1ExtraNoiseVar g) (hJ1ExtraNoiseVar g)
  let J2KeepFamily : GLM20Group →
      GaussianOffsetSignalFamily (Option FeatureDrop) := fun g =>
    (J2DropFamily g).withExtraSignal (J2ExtraNoiseMean g)
      (J2ExtraNoiseVar g) (hJ2ExtraNoiseVar g)
  let hsurvivor := paper_theorem3_j2_survivor_rows_components hJ2SurvivorRows
  let hJ2KeepPair :=
    paper_theorem3_source_family_j2_keep_test_pair_of_base_survivor_rows
      standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
      subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback diversity glm20SchoolJ1 glm20SchoolJ2
      GLM20Group.groupA GLM20Group.groupB
      (glm20Theorem3PopulationShare pi) fullFullCutoff fullSubCutoff
      standardGaussianHazardCertificate J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold glm20SchoolJ1_ne_J2
      hsurvivor.1 hsurvivor.2.1 hsurvivor.2.2.1
      hsurvivor.2.2.2
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_j2_keeps_test_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar hJ1ExtraNoiseVar hJ2ExtraNoiseVar J1DropThreshold
    J1KeepThreshold J2DropThreshold J2KeepThreshold hJ1ThresholdMean
    hJ1Threshold hJ2ThresholdMean hJ2Threshold subFullLaw
    subFullBasedThresholdIntercept subFullBasedThresholdSlope
    subFullFreeThreshold hsubFullAffineTailRows fullSubHighFreeFamily
    fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar
    hfullSubFreeExtraNoiseVar fullSubLowFreeThreshold
    fullSubHighFreeThreshold fullSubLowBasedFamily
    fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
    hfullSubBasedExtraNoiseVar fullSubLowBasedThresholdIntercept
    fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
    fullSubHighBasedThresholdSlope hfullSubAffineThresholdRows
    hsubFullCostBounds hfullSubCostBounds hfullSubFixedLawRows hpi
    hcapacityCutoffRows hJ2KeepPair

/--
Theorem 3 paper-groups/schools source-family route, with the full/sub
generated-row premises bundled.

This is an additive human-facing wrapper around the current survivor-row
endpoint.  It replaces the separate full/sub positive-noise, fixed-law,
affine-threshold, and cost-bound premises by one
`GLM20Theorem3FullSubGeneratedRows` package.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_extra_keep_and_fullSub_generated_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hkeepSignalRows :
      GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (hsubFullAffineTailRows :
      GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
        subFullLeftCost subFullRightCost subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
    (hfullSubGeneratedRows :
      GLM20Theorem3FullSubGeneratedRows testCost fullSubLeftCost
        fullSubRightCost fullSubHighFreeFamily
        fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        fullSubLowBasedFamily fullSubBasedExtraNoiseMean
        fullSubBasedExtraNoiseVar fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope)
    (hsubFullCostBounds :
      GLM20CostBoundsBelow testCost subFullLeftCost subFullRightCost
        subFullV2)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacityCutoffRows :
      GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
        (glm20Theorem3PopulationShare pi) subEstimateLaw
        GLM20Group.groupA GLM20Group.groupB capacity1 capacity2
        q1Sub q2Sub fullFullCutoff)
    (hJ2SurvivorRows :
      GLM20Theorem3J2SurvivorRows (glm20Theorem3PopulationShare pi)
        subFullMass subSubMerit subFullMeritBase glm20SchoolJ2
        GLM20Group.groupA GLM20Group.groupB capacity2) :=
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar J1DropThreshold J1KeepThreshold J2DropThreshold
    J2KeepThreshold hkeepSignalRows subFullLaw
    subFullBasedThresholdIntercept subFullBasedThresholdSlope
    subFullFreeThreshold hsubFullAffineTailRows fullSubHighFreeFamily
    fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar
    hfullSubGeneratedRows.freeExtraNoiseVar_pos
    fullSubLowFreeThreshold fullSubHighFreeThreshold
    fullSubLowBasedFamily fullSubBasedExtraNoiseMean
    fullSubBasedExtraNoiseVar hfullSubGeneratedRows.basedExtraNoiseVar_pos
    fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
    fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
    hfullSubGeneratedRows.affineThresholdRows hsubFullCostBounds
    hfullSubGeneratedRows.costBounds hfullSubGeneratedRows.fixedLawRows hpi
    hcapacityCutoffRows hJ2SurvivorRows

/--
Theorem 3 paper-groups/schools source-family route from primitive full/sub
prior-precision rows.

This is the raw-source companion to
`..._survivor_rows_paper_groups_schools_extra_keep_and_fullSub_generated_rows_...`:
instead of requiring callers to prepackage `GLM20Theorem3FullSubGeneratedRows`,
it builds that package from the positive-noise rows, the six fixed-law
prior/variance/precision equalities, the affine threshold rows, and the
full/sub cost bounds.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_extra_keep_and_fullSub_prior_precision_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hkeepSignalRows :
      GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (hsubFullAffineTailRows :
      GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
        subFullLeftCost subFullRightCost subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
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
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacityCutoffRows :
      GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
        (glm20Theorem3PopulationShare pi) subEstimateLaw
        GLM20Group.groupA GLM20Group.groupB capacity1 capacity2
        q1Sub q2Sub fullFullCutoff)
    (hJ2SurvivorRows :
      GLM20Theorem3J2SurvivorRows (glm20Theorem3PopulationShare pi)
        subFullMass subSubMerit subFullMeritBase glm20SchoolJ2
        GLM20Group.groupA GLM20Group.groupB capacity2) :=
  let hfullSubGeneratedRows :=
    paper_theorem3_fullSub_generated_rows_of_prior_precision_rows
      (testCost := testCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (highFreeFamily := fullSubHighFreeFamily)
      (freeExtraNoiseMean := fullSubFreeExtraNoiseMean)
      (freeExtraNoiseVar := fullSubFreeExtraNoiseVar)
      (fullSubLowFreeThreshold := fullSubLowFreeThreshold)
      (fullSubHighFreeThreshold := fullSubHighFreeThreshold)
      (lowBasedFamily := fullSubLowBasedFamily)
      (basedExtraNoiseMean := fullSubBasedExtraNoiseMean)
      (basedExtraNoiseVar := fullSubBasedExtraNoiseVar)
      (lowBasedThresholdIntercept := fullSubLowBasedThresholdIntercept)
      (highBasedThresholdIntercept := fullSubHighBasedThresholdIntercept)
      (lowBasedThresholdSlope := fullSubLowBasedThresholdSlope)
      (highBasedThresholdSlope := fullSubHighBasedThresholdSlope)
      hfullSubFreeExtraNoiseVar hfullSubBasedExtraNoiseVar
      hfullSubLowPriorMean hfullSubLowPriorVar hfullSubLowPrecision
      hfullSubHighPriorMean hfullSubHighPriorVar hfullSubHighPrecision
      hfullSubAffineThresholdRows hfullSubCostBounds
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_extra_keep_and_fullSub_generated_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar J1DropThreshold J1KeepThreshold J2DropThreshold
    J2KeepThreshold hkeepSignalRows subFullLaw
    subFullBasedThresholdIntercept subFullBasedThresholdSlope
    subFullFreeThreshold hsubFullAffineTailRows fullSubHighFreeFamily
    fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar
    fullSubLowFreeThreshold fullSubHighFreeThreshold
    fullSubLowBasedFamily fullSubBasedExtraNoiseMean
    fullSubBasedExtraNoiseVar fullSubLowBasedThresholdIntercept
    fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
    fullSubHighBasedThresholdSlope hfullSubGeneratedRows
    hsubFullCostBounds hpi hcapacityCutoffRows hJ2SurvivorRows

/--
Theorem 3 paper-groups/schools source-family route, with the full/sub
generated-row premises bundled and the school-`J2` survivor side stated only
as strict condition-(12) merit rows.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_extra_keep_and_fullSub_generated_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hkeepSignalRows :
      GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (hsubFullAffineTailRows :
      GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
        subFullLeftCost subFullRightCost subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
    (hfullSubGeneratedRows :
      GLM20Theorem3FullSubGeneratedRows testCost fullSubLeftCost
        fullSubRightCost fullSubHighFreeFamily
        fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        fullSubLowBasedFamily fullSubBasedExtraNoiseMean
        fullSubBasedExtraNoiseVar fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope)
    (hsubFullCostBounds :
      GLM20CostBoundsBelow testCost subFullLeftCost subFullRightCost
        subFullV2)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacityCutoffRows :
      GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
        (glm20Theorem3PopulationShare pi) subEstimateLaw
        GLM20Group.groupA GLM20Group.groupB capacity1 capacity2
        q1Sub q2Sub fullFullCutoff)
    (hJ2StrictSurvivorMeritRows :
      GLM20Theorem3J2StrictSurvivorMeritRows
        (glm20Theorem3PopulationShare pi) subSubMerit subFullMeritBase
        glm20SchoolJ2 GLM20Group.groupA GLM20Group.groupB) :=
  let hkeepRows := paper_theorem3_keep_signal_rows_components
    hkeepSignalRows
  let hJ1ExtraNoiseVar := hkeepRows.1
  let hJ2ExtraNoiseVar := hkeepRows.2.1
  let hJ1ThresholdMean := hkeepRows.2.2.1
  let hJ1Threshold := hkeepRows.2.2.2.1
  let hJ2ThresholdMean := hkeepRows.2.2.2.2.1
  let hJ2Threshold := hkeepRows.2.2.2.2.2
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_extra_keep_and_fullSub_signals_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar hJ1ExtraNoiseVar hJ2ExtraNoiseVar J1DropThreshold
    J1KeepThreshold J2DropThreshold J2KeepThreshold hJ1ThresholdMean
    hJ1Threshold hJ2ThresholdMean hJ2Threshold subFullLaw
    subFullBasedThresholdIntercept subFullBasedThresholdSlope
    subFullFreeThreshold hsubFullAffineTailRows fullSubHighFreeFamily
    fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar
    hfullSubGeneratedRows.freeExtraNoiseVar_pos
    fullSubLowFreeThreshold fullSubHighFreeThreshold
    fullSubLowBasedFamily fullSubBasedExtraNoiseMean
    fullSubBasedExtraNoiseVar hfullSubGeneratedRows.basedExtraNoiseVar_pos
    fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
    fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
    hfullSubGeneratedRows.affineThresholdRows hsubFullCostBounds
    hfullSubGeneratedRows.costBounds hfullSubGeneratedRows.fixedLawRows hpi
    hcapacityCutoffRows hJ2StrictSurvivorMeritRows

/--
Theorem 3 paper-groups/schools source-family route from primitive full/sub
prior-precision rows, with the school-`J2` survivor side stated only as
strict condition-(12) merit rows.

This is the raw-source companion to the strict-survivor generated-row endpoint:
it constructs `GLM20Theorem3FullSubGeneratedRows` internally from the
positive-noise rows, fixed-law prior/variance/precision equalities, affine
threshold rows, and full/sub cost bounds.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_extra_keep_and_fullSub_prior_precision_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hkeepSignalRows :
      GLM20Theorem3KeepSignalRows J1DropFamily J2DropFamily
        J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (hsubFullAffineTailRows :
      GLM20Theorem3SubFullAffineTailRows standardGaussianQuantileAPI
        subFullLeftCost subFullRightCost subFullQ2Full subFullScale
        subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
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
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hcapacityCutoffRows :
      GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
        (glm20Theorem3PopulationShare pi) subEstimateLaw
        GLM20Group.groupA GLM20Group.groupB capacity1 capacity2
        q1Sub q2Sub fullFullCutoff)
    (hJ2StrictSurvivorMeritRows :
      GLM20Theorem3J2StrictSurvivorMeritRows
        (glm20Theorem3PopulationShare pi) subSubMerit subFullMeritBase
        glm20SchoolJ2 GLM20Group.groupA GLM20Group.groupB) :=
  let hfullSubGeneratedRows :=
    paper_theorem3_fullSub_generated_rows_of_prior_precision_rows
      (testCost := testCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (highFreeFamily := fullSubHighFreeFamily)
      (freeExtraNoiseMean := fullSubFreeExtraNoiseMean)
      (freeExtraNoiseVar := fullSubFreeExtraNoiseVar)
      (fullSubLowFreeThreshold := fullSubLowFreeThreshold)
      (fullSubHighFreeThreshold := fullSubHighFreeThreshold)
      (lowBasedFamily := fullSubLowBasedFamily)
      (basedExtraNoiseMean := fullSubBasedExtraNoiseMean)
      (basedExtraNoiseVar := fullSubBasedExtraNoiseVar)
      (lowBasedThresholdIntercept := fullSubLowBasedThresholdIntercept)
      (highBasedThresholdIntercept := fullSubHighBasedThresholdIntercept)
      (lowBasedThresholdSlope := fullSubLowBasedThresholdSlope)
      (highBasedThresholdSlope := fullSubHighBasedThresholdSlope)
      hfullSubFreeExtraNoiseVar hfullSubBasedExtraNoiseVar
      hfullSubLowPriorMean hfullSubLowPriorVar hfullSubLowPrecision
      hfullSubHighPriorMean hfullSubHighPriorVar hfullSubHighPrecision
      hfullSubAffineThresholdRows hfullSubCostBounds
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_extra_keep_and_fullSub_generated_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar J1DropThreshold J1KeepThreshold J2DropThreshold
    J2KeepThreshold hkeepSignalRows subFullLaw
    subFullBasedThresholdIntercept subFullBasedThresholdSlope
    subFullFreeThreshold hsubFullAffineTailRows fullSubHighFreeFamily
    fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar
    fullSubLowFreeThreshold fullSubHighFreeThreshold
    fullSubLowBasedFamily fullSubBasedExtraNoiseMean
    fullSubBasedExtraNoiseVar fullSubLowBasedThresholdIntercept
    fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
    fullSubHighBasedThresholdSlope hfullSubGeneratedRows
    hsubFullCostBounds hpi hcapacityCutoffRows hJ2StrictSurvivorMeritRows

/--
Theorem 3 paper-groups/schools source-family route, with all public source-row
premises bundled.

This wraps the current public route in one auditable
`GLM20Theorem3AcademicMeritPublicRows` package for the generated keep-signal,
sub/full affine-tail, full/sub generated-row, cost-bound, capacity/cutoff, and
school-`J2` survivor premises.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_public_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
    (hpublicRows :
      GLM20Theorem3AcademicMeritPublicRows testCost subFullLeftCost
        subFullRightCost fullSubLeftCost fullSubRightCost capacity1
        capacity2 q1Sub q2Sub pi fullFullCutoff subEstimateLaw
        subFullMass subSubMerit subFullMeritBase J1DropFamily J2DropFamily
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
        fullSubHighBasedThresholdSlope)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1) :=
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_extra_keep_and_fullSub_generated_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar J1DropThreshold J1KeepThreshold J2DropThreshold
    J2KeepThreshold hpublicRows.keepSignalRows subFullLaw
    subFullBasedThresholdIntercept subFullBasedThresholdSlope
    subFullFreeThreshold hpublicRows.subFullAffineTailRows
    fullSubHighFreeFamily fullSubFreeExtraNoiseMean
    fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
    fullSubHighFreeThreshold fullSubLowBasedFamily
    fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
    fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
    fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
    hpublicRows.fullSubGeneratedRows hpublicRows.subFullCostBounds hpi
    hpublicRows.capacityCutoffRows hpublicRows.j2SurvivorRows

/--
Theorem 3 paper-groups/schools source-family route, with all public source-row
premises bundled and the school-`J2` survivor side reduced to strict merit
rows.

Compared with
`paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_survivor_rows_paper_groups_schools_public_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds`,
this endpoint no longer asks the public row package for the two raw survivor
capacity-fill inequalities.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
    (hpublicRows :
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
        fullSubHighBasedThresholdSlope)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1) :=
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_extra_keep_and_fullSub_generated_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar J1DropThreshold J1KeepThreshold J2DropThreshold
    J2KeepThreshold hpublicRows.keepSignalRows subFullLaw
    subFullBasedThresholdIntercept subFullBasedThresholdSlope
    subFullFreeThreshold hpublicRows.subFullAffineTailRows
    fullSubHighFreeFamily fullSubFreeExtraNoiseMean
    fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
    fullSubHighFreeThreshold fullSubLowBasedFamily
    fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
    fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
    fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
    hpublicRows.fullSubGeneratedRows hpublicRows.subFullCostBounds hpi
    hpublicRows.capacityCutoffRows hpublicRows.j2StrictSurvivorMeritRows

/--
Preferred Theorem 3 paper-groups/schools source-family route, with all public
source-row premises and the population-share domain bundled together.

This is the same theorem as
`paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds`,
but the visible public input is a single
`GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare`
package.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    {FeatureDrop HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
    (hpublicRows :
      GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare
        testCost subFullLeftCost subFullRightCost fullSubLeftCost
        fullSubRightCost capacity1 capacity2 q1Sub q2Sub pi fullFullCutoff
        subEstimateLaw subSubMerit subFullMeritBase J1DropFamily
        J2DropFamily J1ExtraNoiseVar J2ExtraNoiseVar J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold subFullQ2Full
        subFullScale subFullV2 subFullBasedThresholdIntercept
        subFullBasedThresholdSlope subFullFreeThreshold
        fullSubHighFreeFamily fullSubFreeExtraNoiseMean
        fullSubFreeExtraNoiseVar fullSubLowFreeThreshold
        fullSubHighFreeThreshold fullSubLowBasedFamily
        fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
        fullSubLowBasedThresholdIntercept
        fullSubHighBasedThresholdIntercept fullSubLowBasedThresholdSlope
        fullSubHighBasedThresholdSlope) :=
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar J1DropThreshold J1KeepThreshold J2DropThreshold
    J2KeepThreshold subFullLaw subFullBasedThresholdIntercept
    subFullBasedThresholdSlope subFullFreeThreshold fullSubHighFreeFamily
    fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar
    fullSubLowFreeThreshold fullSubHighFreeThreshold fullSubLowBasedFamily
    fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
    fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
    fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
    hpublicRows.rows hpublicRows.populationShare_mem

/--
Raw-source paper-facing Theorem 3 route with the compact public-row package
constructed internally.

Callers supply the generated source-family school-`J2` keep-test pair and the
primitive full/sub prior mean, prior variance, and total precision rows.  This
wrapper constructs
`GLM20Theorem3AcademicMeritStrictSurvivorPublicRowsWithPopulationShare` and
then invokes the compact public-row endpoint.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_j2_keep_test_pair_and_fullSub_prior_precision_rows_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    {FeatureDrop FeatureKeep HighFreeFeature LowBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    {testCost subFullLeftCost subFullRightCost fullSubLeftCost
      fullSubRightCost : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub pi : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1ExtraNoiseMean J2ExtraNoiseMean
      J1ExtraNoiseVar J2ExtraNoiseVar : GLM20Group → ℝ)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (subFullLaw : GLM20Group → GaussianScaleLaw)
    (subFullBasedThresholdIntercept subFullBasedThresholdSlope
      subFullFreeThreshold : GLM20Group → ℝ)
    (fullSubHighFreeFamily :
      GLM20Group → GaussianOffsetSignalFamily HighFreeFeature)
    (fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar :
      GLM20Group → ℝ)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold :
      GLM20Group → ℝ)
    (fullSubLowBasedFamily :
      GLM20Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar :
      GLM20Group → ℝ → ℝ)
    (fullSubLowBasedThresholdIntercept
      fullSubHighBasedThresholdIntercept
      fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope :
      GLM20Group → ℝ)
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
          (glm20Theorem3PopulationShare pi) capacity2 GLM20Group.groupA) :=
  let hpublicRows :=
    paper_theorem3_academic_merit_strict_survivor_public_rows_with_population_share_of_source_family_j2_keep_test_pair_and_fullSub_prior_precision_rows
      C hkeepSignalRows hsubFullAffineTailRows hfullSubFreeExtraNoiseVar
      hfullSubBasedExtraNoiseVar hfullSubLowPriorMean
      hfullSubLowPriorVar hfullSubLowPrecision hfullSubHighPriorMean
      hfullSubHighPriorVar hfullSubHighPrecision
      hfullSubAffineThresholdRows hfullSubCostBounds hsubFullCostBounds
      hcapacityCutoffRows hpi hJ2KeepPair
  paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_equation50_subFull_cutoff_order_subFull_fullSub_interval_of_threshold_order_fixed_law_posterior_mean_fullSub_cost_rows_of_affine_based_thresholds_source_family_strict_survivor_merits_paper_groups_schools_public_rows_with_population_share_canonical_laws_subFull_affine_tail_mean_of_cost_bounds
    (FeatureDrop := FeatureDrop)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) (pi := pi)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (feasible1 := feasible1) (feasible2 := feasible2)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity J1DropFamily
    J2DropFamily J1ExtraNoiseMean J2ExtraNoiseMean J1ExtraNoiseVar
    J2ExtraNoiseVar J1DropThreshold J1KeepThreshold J2DropThreshold
    J2KeepThreshold subFullLaw subFullBasedThresholdIntercept
    subFullBasedThresholdSlope subFullFreeThreshold fullSubHighFreeFamily
    fullSubFreeExtraNoiseMean fullSubFreeExtraNoiseVar
    fullSubLowFreeThreshold fullSubHighFreeThreshold fullSubLowBasedFamily
    fullSubBasedExtraNoiseMean fullSubBasedExtraNoiseVar
    fullSubLowBasedThresholdIntercept fullSubHighBasedThresholdIntercept
    fullSubLowBasedThresholdSlope fullSubHighBasedThresholdSlope
    hpublicRows

end

end GLM20DroppingStandardizedTesting
