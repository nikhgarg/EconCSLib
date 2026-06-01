import GLM20DroppingStandardizedTesting.Proposition5KeepTestObjective
import GLM20DroppingStandardizedTesting.Theorem3PosteriorCostRows

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Theorem 3 weighted binary-policy endpoint with the Proposition 5(i) sub-full
bridge generated internally.

This composes the standard-Gaussian Proposition 5(i) keep-test bridge with the
weighted binary-policy Theorem 3 adapter.  Callers still supply a packaged
Proposition 5(ii) full-sub bridge, but the sub-full threshold, root equation,
threshold monotonicity, and objective iff are now generated directly from the
equation-(50) source-family keep-test route.
-/
theorem
    paper_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_standardGaussian_subFull_keep_test_bridge_and_fullSub_objective_bridge
    {Group Policy School FeatureDrop FeatureKeep : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    {S : GLM20StrategicPolicySurface Group Policy School (Policy × Policy)}
    {massTestTaking : Group → Policy → ℝ}
    {admittedAcademicMerit : School → Group → Policy → ℝ}
    {diversity : School → Policy → ℝ}
    {policyPair : Policy → Policy → Policy}
    {Psub Pfull : Policy} {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost subFullLeftCost subFullRightCost
      subFullQ2Full subFullScale subFullV2 fullSubLeftCost
      fullSubRightCost : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff : Group → ℝ}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (J1DropFamily : Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily : Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold : Group → ℝ)
    (fullSubLowTestBasedMerit : Group → ℝ → ℝ)
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestBasedMerit : Group → ℝ → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
    (hS :
      S =
        glm20WeightedAcademicMeritBinaryPolicySurface massTestTaking
          admittedAcademicMerit diversity policyPair Psub Pfull J1 J2
          groupA groupB populationShare)
    (hsubFullLeftRight :
      ∀ g, subFullLeftCost g < subFullRightCost g)
    (hsubFullScale : ∀ g, 0 < subFullScale g)
    (hsubFullLeftPos : ∀ g, 0 < subFullLeftCost g)
    (hsubFullRightLtV2 :
      ∀ g, subFullRightCost g < subFullV2 g)
    (hsubFullCostMem :
      ∀ g, testCost g ∈
        Set.Icc (subFullLeftCost g) (subFullRightCost g))
    (hsubFullMeritCont :
      ∀ g, Continuous (subFullMeritOfCutoff g))
    (hsubFullMeritAnti :
      ∀ g, StrictAnti (subFullMeritOfCutoff g))
    (hsubFullAtLeft :
      ∀ g,
        subFullTestFreeMerit g <
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
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
    (hmassFullFullA :
      S.massTestTaking groupA (policyPair Pfull Pfull) =
        glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
          (subEstimateLaw groupA) (fullFullCutoff groupA))
    (hmassFullFullB :
      S.massTestTaking groupB (policyPair Pfull Pfull) =
        glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
          (subEstimateLaw groupB) (fullFullCutoff groupB))
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
            S.massTestTaking groupA (policyPair Pfull Pfull) +
          populationShare groupB *
            S.massTestTaking groupB (policyPair Pfull Pfull))
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
    (hJ1DropMerit :
      ∀ g,
        ¬ q1Sub < fullFullCutoff groupA →
          ¬ q1Sub < fullFullCutoff groupB →
            S.admittedAcademicMerit J1 g (policyPair Psub Pfull) =
              (standardGaussianHazardInverseCertificate.toGaussianHazardCertificate).normalUpperTailMean
                    (J1DropFamily g).posteriorMeanScaleLaw
                    (J1DropThreshold g))
    (hJ1KeepMerit :
      ∀ g,
        ¬ q1Sub < fullFullCutoff groupA →
          ¬ q1Sub < fullFullCutoff groupB →
            S.admittedAcademicMerit J1 g (policyPair Pfull Pfull) =
              (standardGaussianHazardInverseCertificate.toGaussianHazardCertificate).normalUpperTailMean
                    (J1KeepFamily g).posteriorMeanScaleLaw
                    (J1KeepThreshold g))
    (honlyA_J1_groupB_eq :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J1 groupB (policyPair Pfull Pfull) =
            S.admittedAcademicMerit J1 groupB (policyPair Psub Pfull))
    (honlyA_J1_groupA_testBased :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J1 groupA (policyPair Pfull Pfull) =
            subFullMeritOfCutoff groupA
              (subFullQ2Full groupA -
                subFullScale groupA *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost groupA / subFullV2 groupA)))
    (honlyA_J1_groupA_testFree :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J1 groupA (policyPair Psub Pfull) =
            subFullTestFreeMerit groupA)
    (honlyB_J1_groupA_eq :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J1 groupA (policyPair Pfull Pfull) =
            S.admittedAcademicMerit J1 groupA (policyPair Psub Pfull))
    (honlyB_J1_groupB_testBased :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J1 groupB (policyPair Pfull Pfull) =
            subFullMeritOfCutoff groupB
              (subFullQ2Full groupB -
                subFullScale groupB *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost groupB / subFullV2 groupB)))
    (honlyB_J1_groupB_testFree :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J1 groupB (policyPair Psub Pfull) =
            subFullTestFreeMerit groupB)
    (hJ2ObjectiveSubSub :
      glm20TwoGroupWeightedAcademicMeritObjective S policyPair J2
          groupA groupB populationShare Psub Psub =
        populationShare groupA *
            S.admittedAcademicMerit J2 groupA (policyPair Psub Psub) +
          populationShare groupB *
            S.admittedAcademicMerit J2 groupB (policyPair Psub Psub))
    (hJ2ObjectiveSubFullB :
      glm20TwoGroupWeightedAcademicMeritObjective S policyPair J2
          groupA groupB populationShare Psub Pfull =
        populationShare groupB *
          S.admittedAcademicMerit J2 groupB (policyPair Psub Pfull))
    (hJ2KeepsB :
      glm20Theorem3SubFullOtherGroupKeepsTest S policyPair Psub Pfull J2
        groupA groupB populationShare capacity2 groupB)
    (hJ2ObjectiveSubFullA :
      glm20TwoGroupWeightedAcademicMeritObjective S policyPair J2
          groupA groupB populationShare Psub Pfull =
        populationShare groupA *
          S.admittedAcademicMerit J2 groupA (policyPair Psub Pfull))
    (hJ2KeepsA :
      glm20Theorem3SubFullOtherGroupKeepsTest S policyPair Psub Pfull J2
        groupA groupB populationShare capacity2 groupA)
    (hfullSubBridge :
      ∃ fullSubLowCostThreshold fullSubHighCostThreshold : Group → ℝ,
        (∀ g, fullSubLowCostThreshold g ∈
          Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
          (∀ g, fullSubHighCostThreshold g ∈
            Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
            (∀ g,
              fullSubLowTestBasedMerit g (fullSubLowCostThreshold g) =
                fullSubLowTestFreeMerit g) ∧
              (∀ g,
                fullSubHighTestBasedMerit g
                    (fullSubHighCostThreshold g) =
                  fullSubHighTestFreeMerit g) ∧
                (∀ g, 0 < fullSubLowCostThreshold g) ∧
                  (∀ g,
                    fullSubLowCostThreshold g <
                      fullSubHighCostThreshold g) ∧
                    ((glm20TwoGroupWeightedAcademicMeritObjective S
                          policyPair J1 groupA groupB populationShare Psub
                          Psub ≤
                        glm20TwoGroupWeightedAcademicMeritObjective S
                          policyPair J1 groupA groupB populationShare Pfull
                          Psub ∧
                      glm20TwoGroupWeightedAcademicMeritObjective S
                          policyPair J2 groupA groupB populationShare Pfull
                          Pfull ≤
                        glm20TwoGroupWeightedAcademicMeritObjective S
                          policyPair J2 groupA groupB populationShare Pfull
                          Psub) ↔
                      glm20Theorem3FullSubCondition S policyPair Psub Pfull
                        groupA groupB testCost fullSubLowCostThreshold
                        fullSubHighCostThreshold q1Sub q2Sub
                        (fun g q =>
                          glm20StrategicSubEstimateMassAbove
                            standardGaussianCDFAPI (subEstimateLaw g) q)))
    (hcostA : 0 < testCost groupA) (hcostB : 0 < testCost groupB) :
    ∃ subFullCostThreshold fullSubLowCostThreshold
        fullSubHighCostThreshold : Group → ℝ,
      (∀ g, subFullCostThreshold g ∈
        Set.Ioo (subFullLeftCost g) (subFullRightCost g)) ∧
        (∀ g,
          subFullMeritOfCutoff g
              (subFullQ2Full g -
                subFullScale g *
                  standardGaussianQuantileAPI.quantile
                    (1 - subFullCostThreshold g / subFullV2 g)) =
            subFullTestFreeMerit g) ∧
          (∀ g c, c ∈ Set.Icc (subFullLeftCost g) (subFullRightCost g) →
            (subFullMeritOfCutoff g
                (subFullQ2Full g -
                  subFullScale g *
                    standardGaussianQuantileAPI.quantile
                      (1 - c / subFullV2 g)) ≤
                subFullTestFreeMerit g ↔
              subFullCostThreshold g ≤ c)) ∧
            (∀ g, fullSubLowCostThreshold g ∈
              Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
              (∀ g, fullSubHighCostThreshold g ∈
                Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
                (∀ g,
                  fullSubLowTestBasedMerit g
                      (fullSubLowCostThreshold g) =
                    fullSubLowTestFreeMerit g) ∧
                  (∀ g,
                    fullSubHighTestBasedMerit g
                        (fullSubHighCostThreshold g) =
                      fullSubHighTestFreeMerit g) ∧
                    (∀ g, 0 < fullSubLowCostThreshold g) ∧
                      (∀ g,
                        fullSubLowCostThreshold g <
                          fullSubHighCostThreshold g) ∧
                        ((S.policyPairIsEquilibrium Psub Pfull ↔
                            glm20Theorem3SubFullCondition S policyPair Psub
                              Pfull J2 groupA groupB populationShare
                              testCost subFullCostThreshold capacity2 q1Sub
                              (fun g q =>
                                glm20StrategicSubEstimateMassAbove
                                  standardGaussianCDFAPI
                                  (subEstimateLaw g) q)) ∧
                          (S.policyPairIsEquilibrium Pfull Psub ↔
                            glm20Theorem3FullSubCondition S policyPair Psub
                              Pfull groupA groupB testCost
                              fullSubLowCostThreshold
                              fullSubHighCostThreshold q1Sub q2Sub
                              (fun g q =>
                                glm20StrategicSubEstimateMassAbove
                                  standardGaussianCDFAPI
                                  (subEstimateLaw g) q)) ∧
                            glm20Theorem3FullFullCondition S Pfull groupA
                              groupB testCost) := by
  let subFullTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    subFullMeritOfCutoff g
      (subFullQ2Full g -
        subFullScale g *
          standardGaussianQuantileAPI.quantile
            (1 - cost / subFullV2 g))
  have hsubFullBridge :
      ∃ subFullCostThreshold : Group → ℝ,
        (∀ g, subFullCostThreshold g ∈
          Set.Ioo (subFullLeftCost g) (subFullRightCost g)) ∧
          (∀ g,
            subFullTestBasedMerit g (subFullCostThreshold g) =
              subFullTestFreeMerit g) ∧
            (∀ g c, c ∈
              Set.Icc (subFullLeftCost g) (subFullRightCost g) →
              (subFullTestBasedMerit g c ≤ subFullTestFreeMerit g ↔
                subFullCostThreshold g ≤ c)) ∧
              ((glm20TwoGroupWeightedAcademicMeritObjective S policyPair J1
                    groupA groupB populationShare Pfull Pfull ≤
                  glm20TwoGroupWeightedAcademicMeritObjective S policyPair J1
                    groupA groupB populationShare Psub Pfull ∧
                glm20TwoGroupWeightedAcademicMeritObjective S policyPair J2
                    groupA groupB populationShare Psub Psub ≤
                  glm20TwoGroupWeightedAcademicMeritObjective S policyPair J2
                    groupA groupB populationShare Psub Pfull) ↔
                glm20Theorem3SubFullCondition S policyPair Psub Pfull J2
                  groupA groupB populationShare testCost
                  subFullCostThreshold capacity2 q1Sub
                  (fun g q =>
                    glm20StrategicSubEstimateMassAbove
                      standardGaussianCDFAPI (subEstimateLaw g) q)) := by
    simpa [subFullTestBasedMerit] using
      (paper_proposition5_standardGaussian_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_keeps_test
        (S := S) (policyPair := policyPair) (Psub := Psub)
        (Pfull := Pfull) (J1 := J1) (J2 := J2) (groupA := groupA)
        (groupB := groupB) (populationShare := populationShare)
        (testCost := testCost) (leftCost := subFullLeftCost)
        (rightCost := subFullRightCost) (q2Full := subFullQ2Full)
        (scale := subFullScale) (v2 := subFullV2)
        (capacity1 := capacity1) (capacity2 := capacity2)
        (q1Sub := q1Sub) subEstimateLaw
        (fullFullCutoff := fullFullCutoff)
        (glm20TwoGroupWeightedAcademicMeritObjective S policyPair J2
          groupA groupB populationShare)
        subFullMeritOfCutoff subFullTestFreeMerit J1DropFamily
        J1KeepFamily J1DropThreshold J1KeepThreshold hsubFullLeftRight
        hsubFullScale hsubFullLeftPos hsubFullRightLtV2 hsubFullCostMem
        hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft
        hsubFullAtRight hshareA hshareB hmassFullFullA hmassFullFullB
        hcapacity1 hfillFullFull1 hJ1PriorMean hJ1PriorVar
        hJ1Precision hJ1ThresholdMean hJ1Threshold hJ1DropMerit
        hJ1KeepMerit honlyA_J1_groupB_eq
        honlyA_J1_groupA_testBased honlyA_J1_groupA_testFree
        honlyB_J1_groupA_eq honlyB_J1_groupB_testBased
        honlyB_J1_groupB_testFree hJ2ObjectiveSubSub
        hJ2ObjectiveSubFullB hJ2KeepsB hJ2ObjectiveSubFullA hJ2KeepsA)
  simpa [subFullTestBasedMerit] using
    (paper_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_subFull_objective_bridge_and_fullSub_objective_bridge
      (S := S) (massTestTaking := massTestTaking)
      (admittedAcademicMerit := admittedAcademicMerit)
      (diversity := diversity) (policyPair := policyPair)
      (Psub := Psub) (Pfull := Pfull) (J1 := J1) (J2 := J2)
      (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub)
      (K := fun g q =>
        glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
          (subEstimateLaw g) q)
      subFullTestBasedMerit subFullTestFreeMerit fullSubLowTestBasedMerit
      fullSubLowTestFreeMerit fullSubHighTestBasedMerit
      fullSubHighTestFreeMerit hS hsubFullBridge hfullSubBridge hcostA
      hcostB)

/--
Theorem 3 weighted binary-policy endpoint with both Proposition 5 bridges
generated internally for the standard-Gaussian fixed-law posterior-row route.

This composes the Proposition 5(i) keep-test bridge and the Proposition 5(ii)
fixed-law posterior cost-row bridge before invoking the weighted Theorem 3
adapter.  It is the local binary-objective composition layer for the common
paper case where the full-sub low/high based rows are posterior upper-tail means
with fixed posterior laws and cost-dependent thresholds.
-/
theorem
    paper_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_standardGaussian_subFull_keep_test_and_fixed_law_fullSub_cost_rows
    {Group Policy School FeatureDrop FeatureKeep LowFreeFeature
      HighFreeFeature LowBasedFeature HighBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {S : GLM20StrategicPolicySurface Group Policy School (Policy × Policy)}
    {massTestTaking : Group → Policy → ℝ}
    {admittedAcademicMerit : School → Group → Policy → ℝ}
    {diversity : School → Policy → ℝ}
    {policyPair : Policy → Policy → Policy}
    {Psub Pfull : Policy} {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost subFullLeftCost subFullRightCost
      subFullQ2Full subFullScale subFullV2 fullSubLeftCost
      fullSubRightCost : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (J1DropFamily : Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily : Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold : Group → ℝ)
    (lowFreeFamily : Group → GaussianOffsetSignalFamily LowFreeFeature)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (lowBasedThreshold highBasedThreshold : Group → ℝ → ℝ)
    (lowBasedLaw highBasedLaw : Group → GaussianScaleLaw)
    (hS :
      S =
        glm20WeightedAcademicMeritBinaryPolicySurface massTestTaking
          admittedAcademicMerit diversity policyPair Psub Pfull J1 J2
          groupA groupB populationShare)
    (hsubFullLeftRight :
      ∀ g, subFullLeftCost g < subFullRightCost g)
    (hsubFullScale : ∀ g, 0 < subFullScale g)
    (hsubFullLeftPos : ∀ g, 0 < subFullLeftCost g)
    (hsubFullRightLtV2 :
      ∀ g, subFullRightCost g < subFullV2 g)
    (hsubFullCostMem :
      ∀ g, testCost g ∈
        Set.Icc (subFullLeftCost g) (subFullRightCost g))
    (hsubFullMeritCont :
      ∀ g, Continuous (subFullMeritOfCutoff g))
    (hsubFullMeritAnti :
      ∀ g, StrictAnti (subFullMeritOfCutoff g))
    (hsubFullAtLeft :
      ∀ g,
        subFullTestFreeMerit g <
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
    (hlowBasedLaw :
      ∀ g c, (lowBasedFamily g c).posteriorMeanScaleLaw =
        lowBasedLaw g)
    (hhighBasedLaw :
      ∀ g c, (highBasedFamily g c).posteriorMeanScaleLaw =
        highBasedLaw g)
    (hlowThresholdCont :
      ∀ g, ContinuousOn (lowBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hlowThresholdAnti :
      ∀ g, StrictAntiOn (lowBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hhighThresholdCont :
      ∀ g, ContinuousOn (highBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hhighThresholdAnti :
      ∀ g, StrictAntiOn (highBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubLeftRight :
      ∀ g, fullSubLeftCost g < fullSubRightCost g)
    (hfullSubLeftPos : ∀ g, 0 < fullSubLeftCost g)
    (hfullSubCostMem :
      ∀ g, testCost g ∈
        Set.Icc (fullSubLeftCost g) (fullSubRightCost g))
    (hlowAtLeft :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (lowFreeFamily g).posteriorMeanScaleLaw
            (lowFreeThreshold g) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (lowBasedFamily g (fullSubLeftCost g)).posteriorMeanScaleLaw
            (lowBasedThreshold g (fullSubLeftCost g)))
    (hlowAtRight :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (lowBasedFamily g (fullSubRightCost g)).posteriorMeanScaleLaw
            (lowBasedThreshold g (fullSubRightCost g)) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (lowFreeFamily g).posteriorMeanScaleLaw
            (lowFreeThreshold g))
    (hhighAtLeft :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (highFreeFamily g).posteriorMeanScaleLaw
            (highFreeThreshold g) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (highBasedFamily g (fullSubLeftCost g)).posteriorMeanScaleLaw
            (highBasedThreshold g (fullSubLeftCost g)))
    (hhighAtRight :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (highBasedFamily g (fullSubRightCost g)).posteriorMeanScaleLaw
            (highBasedThreshold g (fullSubRightCost g)) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (highFreeFamily g).posteriorMeanScaleLaw
            (highFreeThreshold g))
    (hfreePriorMean :
      ∀ g, (highFreeFamily g).priorMean = (lowFreeFamily g).priorMean)
    (hfreePriorVar :
      ∀ g, (highFreeFamily g).priorVar = (lowFreeFamily g).priorVar)
    (hfreePrecision :
      ∀ g,
        (highFreeFamily g).centeredFamily.signalPrecisionSum <
          (lowFreeFamily g).centeredFamily.signalPrecisionSum)
    (hfreeThresholdMean :
      ∀ g, (highFreeFamily g).priorMean < highFreeThreshold g)
    (hfreeThreshold :
      ∀ g, highFreeThreshold g ≤ lowFreeThreshold g)
    (hbasedPriorMean :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        (lowBasedFamily g c).priorMean = (highBasedFamily g c).priorMean)
    (hbasedPriorVar :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        (lowBasedFamily g c).priorVar = (highBasedFamily g c).priorVar)
    (hbasedPrecision :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        (lowBasedFamily g c).centeredFamily.signalPrecisionSum <
          (highBasedFamily g c).centeredFamily.signalPrecisionSum)
    (hbasedThresholdMean :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        (lowBasedFamily g c).priorMean < lowBasedThreshold g c)
    (hbasedThreshold :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        lowBasedThreshold g c ≤ highBasedThreshold g c)
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
    (hmassFullFullA :
      S.massTestTaking groupA (policyPair Pfull Pfull) =
        glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
          (subEstimateLaw groupA) (fullFullCutoff groupA))
    (hmassFullFullB :
      S.massTestTaking groupB (policyPair Pfull Pfull) =
        glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
          (subEstimateLaw groupB) (fullFullCutoff groupB))
    (hmassFullSubA :
      S.massTestTaking groupA (policyPair Pfull Psub) =
        glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
          (subEstimateLaw groupA) (fullSubCutoff groupA))
    (hmassFullSubB :
      S.massTestTaking groupB (policyPair Pfull Psub) =
        glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
          (subEstimateLaw groupB) (fullSubCutoff groupB))
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
            S.massTestTaking groupA (policyPair Pfull Pfull) +
          populationShare groupB *
            S.massTestTaking groupB (policyPair Pfull Pfull))
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
            S.massTestTaking groupA (policyPair Pfull Pfull) +
          populationShare groupB *
            S.massTestTaking groupB (policyPair Pfull Pfull))
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
    (hJ1DropMerit :
      ∀ g,
        ¬ q1Sub < fullFullCutoff groupA →
          ¬ q1Sub < fullFullCutoff groupB →
            S.admittedAcademicMerit J1 g (policyPair Psub Pfull) =
              (standardGaussianHazardInverseCertificate.toGaussianHazardCertificate).normalUpperTailMean
                    (J1DropFamily g).posteriorMeanScaleLaw
                    (J1DropThreshold g))
    (hJ1KeepMerit :
      ∀ g,
        ¬ q1Sub < fullFullCutoff groupA →
          ¬ q1Sub < fullFullCutoff groupB →
            S.admittedAcademicMerit J1 g (policyPair Pfull Pfull) =
              (standardGaussianHazardInverseCertificate.toGaussianHazardCertificate).normalUpperTailMean
                    (J1KeepFamily g).posteriorMeanScaleLaw
                    (J1KeepThreshold g))
    (honlyA_J1_groupB_eq :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J1 groupB (policyPair Pfull Pfull) =
            S.admittedAcademicMerit J1 groupB (policyPair Psub Pfull))
    (honlyA_J1_groupA_testBased :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J1 groupA (policyPair Pfull Pfull) =
            subFullMeritOfCutoff groupA
              (subFullQ2Full groupA -
                subFullScale groupA *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost groupA / subFullV2 groupA)))
    (honlyA_J1_groupA_testFree :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J1 groupA (policyPair Psub Pfull) =
            subFullTestFreeMerit groupA)
    (honlyB_J1_groupA_eq :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J1 groupA (policyPair Pfull Pfull) =
            S.admittedAcademicMerit J1 groupA (policyPair Psub Pfull))
    (honlyB_J1_groupB_testBased :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J1 groupB (policyPair Pfull Pfull) =
            subFullMeritOfCutoff groupB
              (subFullQ2Full groupB -
                subFullScale groupB *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost groupB / subFullV2 groupB)))
    (honlyB_J1_groupB_testFree :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J1 groupB (policyPair Psub Pfull) =
            subFullTestFreeMerit groupB)
    (hfixedPoolMeritA :
      ¬ q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J2 groupA (policyPair Pfull Psub) <
            S.admittedAcademicMerit J2 groupA (policyPair Pfull Pfull))
    (hfixedPoolMeritB :
      ¬ q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J2 groupB (policyPair Pfull Psub) <
            S.admittedAcademicMerit J2 groupB (policyPair Pfull Pfull))
    (honlyA_J2_groupB_eq :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J2 groupB (policyPair Pfull Pfull) =
            S.admittedAcademicMerit J2 groupB (policyPair Pfull Psub))
    (honlyA_J2_groupA_testBased :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J2 groupA (policyPair Pfull Pfull) =
            standardGaussianHazardCertificate.normalUpperTailMean
              (lowBasedFamily groupA
                (testCost groupA)).posteriorMeanScaleLaw
              (lowBasedThreshold groupA (testCost groupA)))
    (honlyA_J2_groupA_testFree :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J2 groupA (policyPair Pfull Psub) =
            standardGaussianHazardCertificate.normalUpperTailMean
              (lowFreeFamily groupA).posteriorMeanScaleLaw
              (lowFreeThreshold groupA))
    (honlyB_J2_groupA_eq :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J2 groupA (policyPair Pfull Pfull) =
            S.admittedAcademicMerit J2 groupA (policyPair Pfull Psub))
    (honlyB_J2_groupB_testBased :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J2 groupB (policyPair Pfull Pfull) =
            standardGaussianHazardCertificate.normalUpperTailMean
              (lowBasedFamily groupB
                (testCost groupB)).posteriorMeanScaleLaw
              (lowBasedThreshold groupB (testCost groupB)))
    (honlyB_J2_groupB_testFree :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J2 groupB (policyPair Pfull Psub) =
            standardGaussianHazardCertificate.normalUpperTailMean
              (lowFreeFamily groupB).posteriorMeanScaleLaw
              (lowFreeThreshold groupB))
    (hnoExpandA :
      fullSubCutoff groupA < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S policyPair J1
          groupA groupB populationShare Psub Psub ≤
        glm20TwoGroupWeightedAcademicMeritObjective S policyPair J1
          groupA groupB populationShare Pfull Psub)
    (hexpandA_J1_groupB_eq :
      ¬ fullSubCutoff groupA < q1Sub →
        S.admittedAcademicMerit J1 groupB (policyPair Psub Psub) =
          S.admittedAcademicMerit J1 groupB (policyPair Pfull Psub))
    (hexpandA_J1_groupA_testFree :
      ¬ fullSubCutoff groupA < q1Sub →
        S.admittedAcademicMerit J1 groupA (policyPair Psub Psub) =
          standardGaussianHazardCertificate.normalUpperTailMean
            (highFreeFamily groupA).posteriorMeanScaleLaw
            (highFreeThreshold groupA))
    (hexpandA_J1_groupA_testBased :
      ¬ fullSubCutoff groupA < q1Sub →
        S.admittedAcademicMerit J1 groupA (policyPair Pfull Psub) =
          standardGaussianHazardCertificate.normalUpperTailMean
            (highBasedFamily groupA
              (testCost groupA)).posteriorMeanScaleLaw
            (highBasedThreshold groupA (testCost groupA)))
    (hnoExpandB :
      fullSubCutoff groupB < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S policyPair J1
          groupA groupB populationShare Psub Psub ≤
        glm20TwoGroupWeightedAcademicMeritObjective S policyPair J1
          groupA groupB populationShare Pfull Psub)
    (hexpandB_J1_groupA_eq :
      ¬ fullSubCutoff groupB < q1Sub →
        S.admittedAcademicMerit J1 groupA (policyPair Psub Psub) =
          S.admittedAcademicMerit J1 groupA (policyPair Pfull Psub))
    (hexpandB_J1_groupB_testFree :
      ¬ fullSubCutoff groupB < q1Sub →
        S.admittedAcademicMerit J1 groupB (policyPair Psub Psub) =
          standardGaussianHazardCertificate.normalUpperTailMean
            (highFreeFamily groupB).posteriorMeanScaleLaw
            (highFreeThreshold groupB))
    (hexpandB_J1_groupB_testBased :
      ¬ fullSubCutoff groupB < q1Sub →
        S.admittedAcademicMerit J1 groupB (policyPair Pfull Psub) =
          standardGaussianHazardCertificate.normalUpperTailMean
            (highBasedFamily groupB
              (testCost groupB)).posteriorMeanScaleLaw
            (highBasedThreshold groupB (testCost groupB)))
    (hJ2ObjectiveSubSub :
      glm20TwoGroupWeightedAcademicMeritObjective S policyPair J2
          groupA groupB populationShare Psub Psub =
        populationShare groupA *
            S.admittedAcademicMerit J2 groupA (policyPair Psub Psub) +
          populationShare groupB *
            S.admittedAcademicMerit J2 groupB (policyPair Psub Psub))
    (hJ2ObjectiveSubFullB :
      glm20TwoGroupWeightedAcademicMeritObjective S policyPair J2
          groupA groupB populationShare Psub Pfull =
        populationShare groupB *
          S.admittedAcademicMerit J2 groupB (policyPair Psub Pfull))
    (hJ2KeepsB :
      glm20Theorem3SubFullOtherGroupKeepsTest S policyPair Psub Pfull J2
        groupA groupB populationShare capacity2 groupB)
    (hJ2ObjectiveSubFullA :
      glm20TwoGroupWeightedAcademicMeritObjective S policyPair J2
          groupA groupB populationShare Psub Pfull =
        populationShare groupA *
          S.admittedAcademicMerit J2 groupA (policyPair Psub Pfull))
    (hJ2KeepsA :
      glm20Theorem3SubFullOtherGroupKeepsTest S policyPair Psub Pfull J2
        groupA groupB populationShare capacity2 groupA)
    (hcostA : 0 < testCost groupA) (hcostB : 0 < testCost groupB) :
    let fullSubLowTestBasedMerit : Group → ℝ → ℝ := fun g c =>
      standardGaussianHazardCertificate.normalUpperTailMean
        (lowBasedFamily g c).posteriorMeanScaleLaw
        (lowBasedThreshold g c)
    let fullSubLowTestFreeMerit : Group → ℝ := fun g =>
      standardGaussianHazardCertificate.normalUpperTailMean
        (lowFreeFamily g).posteriorMeanScaleLaw
        (lowFreeThreshold g)
    let fullSubHighTestBasedMerit : Group → ℝ → ℝ := fun g c =>
      standardGaussianHazardCertificate.normalUpperTailMean
        (highBasedFamily g c).posteriorMeanScaleLaw
        (highBasedThreshold g c)
    let fullSubHighTestFreeMerit : Group → ℝ := fun g =>
      standardGaussianHazardCertificate.normalUpperTailMean
        (highFreeFamily g).posteriorMeanScaleLaw
        (highFreeThreshold g)
    ∃ subFullCostThreshold fullSubLowCostThreshold
        fullSubHighCostThreshold : Group → ℝ,
      (∀ g, subFullCostThreshold g ∈
        Set.Ioo (subFullLeftCost g) (subFullRightCost g)) ∧
        (∀ g,
          subFullMeritOfCutoff g
              (subFullQ2Full g -
                subFullScale g *
                  standardGaussianQuantileAPI.quantile
                    (1 - subFullCostThreshold g / subFullV2 g)) =
            subFullTestFreeMerit g) ∧
          (∀ g c, c ∈ Set.Icc (subFullLeftCost g) (subFullRightCost g) →
            (subFullMeritOfCutoff g
                (subFullQ2Full g -
                  subFullScale g *
                    standardGaussianQuantileAPI.quantile
                      (1 - c / subFullV2 g)) ≤
                subFullTestFreeMerit g ↔
              subFullCostThreshold g ≤ c)) ∧
            (∀ g, fullSubLowCostThreshold g ∈
              Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
              (∀ g, fullSubHighCostThreshold g ∈
                Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
                (∀ g,
                  fullSubLowTestBasedMerit g
                      (fullSubLowCostThreshold g) =
                    fullSubLowTestFreeMerit g) ∧
                  (∀ g,
                    fullSubHighTestBasedMerit g
                        (fullSubHighCostThreshold g) =
                      fullSubHighTestFreeMerit g) ∧
                    (∀ g, 0 < fullSubLowCostThreshold g) ∧
                      (∀ g,
                        fullSubLowCostThreshold g <
                          fullSubHighCostThreshold g) ∧
                        ((S.policyPairIsEquilibrium Psub Pfull ↔
                            glm20Theorem3SubFullCondition S policyPair Psub
                              Pfull J2 groupA groupB populationShare
                              testCost subFullCostThreshold capacity2 q1Sub
                              (fun g q =>
                                glm20StrategicSubEstimateMassAbove
                                  standardGaussianCDFAPI
                                  (subEstimateLaw g) q)) ∧
                          (S.policyPairIsEquilibrium Pfull Psub ↔
                            glm20Theorem3FullSubCondition S policyPair Psub
                              Pfull groupA groupB testCost
                              fullSubLowCostThreshold
                              fullSubHighCostThreshold q1Sub q2Sub
                              (fun g q =>
                                glm20StrategicSubEstimateMassAbove
                                  standardGaussianCDFAPI
                                  (subEstimateLaw g) q)) ∧
                            glm20Theorem3FullFullCondition S Pfull groupA
                              groupB testCost) := by
  let fullSubLowTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    standardGaussianHazardCertificate.normalUpperTailMean
      (lowBasedFamily g c).posteriorMeanScaleLaw
      (lowBasedThreshold g c)
  let fullSubLowTestFreeMerit : Group → ℝ := fun g =>
    standardGaussianHazardCertificate.normalUpperTailMean
      (lowFreeFamily g).posteriorMeanScaleLaw
      (lowFreeThreshold g)
  let fullSubHighTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    standardGaussianHazardCertificate.normalUpperTailMean
      (highBasedFamily g c).posteriorMeanScaleLaw
      (highBasedThreshold g c)
  let fullSubHighTestFreeMerit : Group → ℝ := fun g =>
    standardGaussianHazardCertificate.normalUpperTailMean
      (highFreeFamily g).posteriorMeanScaleLaw
      (highFreeThreshold g)
  have hfullSubBridge :
      ∃ fullSubLowCostThreshold fullSubHighCostThreshold : Group → ℝ,
        (∀ g, fullSubLowCostThreshold g ∈
          Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
          (∀ g, fullSubHighCostThreshold g ∈
            Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
            (∀ g,
              fullSubLowTestBasedMerit g (fullSubLowCostThreshold g) =
                fullSubLowTestFreeMerit g) ∧
              (∀ g,
                fullSubHighTestBasedMerit g
                    (fullSubHighCostThreshold g) =
                  fullSubHighTestFreeMerit g) ∧
                (∀ g, 0 < fullSubLowCostThreshold g) ∧
                  (∀ g,
                    fullSubLowCostThreshold g <
                      fullSubHighCostThreshold g) ∧
                    ((glm20TwoGroupWeightedAcademicMeritObjective S
                          policyPair J1 groupA groupB populationShare Psub
                          Psub ≤
                        glm20TwoGroupWeightedAcademicMeritObjective S
                          policyPair J1 groupA groupB populationShare Pfull
                          Psub ∧
                      glm20TwoGroupWeightedAcademicMeritObjective S
                          policyPair J2 groupA groupB populationShare Pfull
                          Pfull ≤
                        glm20TwoGroupWeightedAcademicMeritObjective S
                          policyPair J2 groupA groupB populationShare Pfull
                          Psub) ↔
                      glm20Theorem3FullSubCondition S policyPair Psub Pfull
                        groupA groupB testCost fullSubLowCostThreshold
                        fullSubHighCostThreshold q1Sub q2Sub
                        (fun g q =>
                          glm20StrategicSubEstimateMassAbove
                            standardGaussianCDFAPI (subEstimateLaw g) q)) := by
    simpa [fullSubLowTestBasedMerit, fullSubLowTestFreeMerit,
      fullSubHighTestBasedMerit, fullSubHighTestFreeMerit] using
      (paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows
        (S := S) (policyPair := policyPair) (Psub := Psub)
        (Pfull := Pfull) (J1 := J1) (J2 := J2) (groupA := groupA)
        (groupB := groupB) (populationShare := populationShare)
        (testCost := testCost) (leftCost := fullSubLeftCost)
        (rightCost := fullSubRightCost) (capacity2 := capacity2)
        (q1Sub := q1Sub) (q2Sub := q2Sub) subEstimateLaw
        (fullFullCutoff := fullFullCutoff)
        (fullSubCutoff := fullSubCutoff) lowFreeFamily highFreeFamily
        lowFreeThreshold highFreeThreshold lowBasedFamily highBasedFamily
        lowBasedThreshold highBasedThreshold lowBasedLaw highBasedLaw
        hlowBasedLaw hhighBasedLaw hlowThresholdCont hlowThresholdAnti
        hhighThresholdCont hhighThresholdAnti hfullSubLeftRight
        hfullSubLeftPos hfullSubCostMem hlowAtLeft hlowAtRight
        hhighAtLeft hhighAtRight hfreePriorMean hfreePriorVar
        hfreePrecision hfreeThresholdMean hfreeThreshold hbasedPriorMean
        hbasedPriorVar hbasedPrecision hbasedThresholdMean hbasedThreshold
        hshareA hshareB hmassFullFullA hmassFullFullB hmassFullSubA
        hmassFullSubB hcapacity2 hfillFullFull2 hfixedPoolMeritA
        hfixedPoolMeritB honlyA_J2_groupB_eq honlyA_J2_groupA_testBased
        honlyA_J2_groupA_testFree honlyB_J2_groupA_eq
        honlyB_J2_groupB_testBased honlyB_J2_groupB_testFree hnoExpandA
        hexpandA_J1_groupB_eq hexpandA_J1_groupA_testFree
        hexpandA_J1_groupA_testBased hnoExpandB hexpandB_J1_groupA_eq
        hexpandB_J1_groupB_testFree hexpandB_J1_groupB_testBased)
  simpa [fullSubLowTestBasedMerit, fullSubLowTestFreeMerit,
    fullSubHighTestBasedMerit, fullSubHighTestFreeMerit] using
    (paper_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_standardGaussian_subFull_keep_test_bridge_and_fullSub_objective_bridge
      (S := S) (massTestTaking := massTestTaking)
      (admittedAcademicMerit := admittedAcademicMerit)
      (diversity := diversity) (policyPair := policyPair)
      (Psub := Psub) (Pfull := Pfull) (J1 := J1) (J2 := J2)
      (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (subFullQ2Full := subFullQ2Full)
      (subFullScale := subFullScale) (subFullV2 := subFullV2)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost) (capacity1 := capacity1)
      (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff) subEstimateLaw
      subFullMeritOfCutoff subFullTestFreeMerit J1DropFamily
      J1KeepFamily J1DropThreshold J1KeepThreshold
      fullSubLowTestBasedMerit fullSubLowTestFreeMerit
      fullSubHighTestBasedMerit fullSubHighTestFreeMerit hS
      hsubFullLeftRight hsubFullScale hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullMeritCont
      hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight hshareA
      hshareB hmassFullFullA hmassFullFullB hcapacity1 hfillFullFull1
      hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ1DropMerit hJ1KeepMerit honlyA_J1_groupB_eq
      honlyA_J1_groupA_testBased honlyA_J1_groupA_testFree
      honlyB_J1_groupA_eq honlyB_J1_groupB_testBased
      honlyB_J1_groupB_testFree hJ2ObjectiveSubSub
      hJ2ObjectiveSubFullB hJ2KeepsB hJ2ObjectiveSubFullA hJ2KeepsA
      hfullSubBridge hcostA hcostB)

/--
Theorem 3 weighted binary-policy endpoint with the Proposition 5(ii)
threshold-order full-sub cost-row bridge generated internally.

This is the threshold-order analogue of
`paper_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_standardGaussian_subFull_keep_test_and_fixed_law_fullSub_cost_rows`:
the full-sub branch supplies fixed-law free-family equations and endpoint
threshold-order comparisons instead of endpoint merit-crossing inequalities.
-/
theorem
    paper_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_standardGaussian_subFull_keep_test_threshold_order_and_fixed_law_fullSub_cost_rows
    {Group Policy School FeatureDrop FeatureKeep LowFreeFeature
      HighFreeFeature LowBasedFeature HighBasedFeature : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {S : GLM20StrategicPolicySurface Group Policy School (Policy × Policy)}
    {massTestTaking : Group → Policy → ℝ}
    {admittedAcademicMerit : School → Group → Policy → ℝ}
    {diversity : School → Policy → ℝ}
    {policyPair : Policy → Policy → Policy}
    {Psub Pfull : Policy} {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost subFullLeftCost subFullRightCost
      subFullQ2Full subFullScale subFullV2 fullSubLeftCost
      fullSubRightCost : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (J1DropFamily : Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily : Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold : Group → ℝ)
    (lowFreeFamily : Group → GaussianOffsetSignalFamily LowFreeFeature)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (lowBasedThreshold highBasedThreshold : Group → ℝ → ℝ)
    (lowBasedLaw highBasedLaw : Group → GaussianScaleLaw)
    (hS :
      S =
        glm20WeightedAcademicMeritBinaryPolicySurface massTestTaking
          admittedAcademicMerit diversity policyPair Psub Pfull J1 J2
          groupA groupB populationShare)
    (hsubFullLeftRight :
      ∀ g, subFullLeftCost g < subFullRightCost g)
    (hsubFullScale : ∀ g, 0 < subFullScale g)
    (hsubFullLeftPos : ∀ g, 0 < subFullLeftCost g)
    (hsubFullRightLtV2 :
      ∀ g, subFullRightCost g < subFullV2 g)
    (hsubFullCostMem :
      ∀ g, testCost g ∈
        Set.Icc (subFullLeftCost g) (subFullRightCost g))
    (hsubFullMeritCont :
      ∀ g, Continuous (subFullMeritOfCutoff g))
    (hsubFullMeritAnti :
      ∀ g, StrictAnti (subFullMeritOfCutoff g))
    (hsubFullAtLeft :
      ∀ g,
        subFullTestFreeMerit g <
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
    (hlowFreeLaw :
      ∀ g, (lowFreeFamily g).posteriorMeanScaleLaw = lowBasedLaw g)
    (hlowBasedLaw :
      ∀ g c, (lowBasedFamily g c).posteriorMeanScaleLaw =
        lowBasedLaw g)
    (hhighFreeLaw :
      ∀ g, (highFreeFamily g).posteriorMeanScaleLaw = highBasedLaw g)
    (hhighBasedLaw :
      ∀ g c, (highBasedFamily g c).posteriorMeanScaleLaw =
        highBasedLaw g)
    (hlowThresholdCont :
      ∀ g, ContinuousOn (lowBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hlowThresholdAnti :
      ∀ g, StrictAntiOn (lowBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hhighThresholdCont :
      ∀ g, ContinuousOn (highBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hhighThresholdAnti :
      ∀ g, StrictAntiOn (highBasedThreshold g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubLeftRight :
      ∀ g, fullSubLeftCost g < fullSubRightCost g)
    (hfullSubLeftPos : ∀ g, 0 < fullSubLeftCost g)
    (hfullSubCostMem :
      ∀ g, testCost g ∈
        Set.Icc (fullSubLeftCost g) (fullSubRightCost g))
    (hlowAtLeftThreshold :
      ∀ g, lowFreeThreshold g < lowBasedThreshold g (fullSubLeftCost g))
    (hlowAtRightThreshold :
      ∀ g, lowBasedThreshold g (fullSubRightCost g) < lowFreeThreshold g)
    (hhighAtLeftThreshold :
      ∀ g, highFreeThreshold g < highBasedThreshold g (fullSubLeftCost g))
    (hhighAtRightThreshold :
      ∀ g, highBasedThreshold g (fullSubRightCost g) < highFreeThreshold g)
    (hfreePriorMean :
      ∀ g, (highFreeFamily g).priorMean = (lowFreeFamily g).priorMean)
    (hfreePriorVar :
      ∀ g, (highFreeFamily g).priorVar = (lowFreeFamily g).priorVar)
    (hfreePrecision :
      ∀ g,
        (highFreeFamily g).centeredFamily.signalPrecisionSum <
          (lowFreeFamily g).centeredFamily.signalPrecisionSum)
    (hfreeThresholdMean :
      ∀ g, (highFreeFamily g).priorMean < highFreeThreshold g)
    (hfreeThreshold :
      ∀ g, highFreeThreshold g ≤ lowFreeThreshold g)
    (hbasedPriorMean :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        (lowBasedFamily g c).priorMean = (highBasedFamily g c).priorMean)
    (hbasedPriorVar :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        (lowBasedFamily g c).priorVar = (highBasedFamily g c).priorVar)
    (hbasedPrecision :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        (lowBasedFamily g c).centeredFamily.signalPrecisionSum <
          (highBasedFamily g c).centeredFamily.signalPrecisionSum)
    (hbasedThresholdMean :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        (lowBasedFamily g c).priorMean < lowBasedThreshold g c)
    (hbasedThreshold :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        lowBasedThreshold g c ≤ highBasedThreshold g c)
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
    (hmassFullFullA :
      S.massTestTaking groupA (policyPair Pfull Pfull) =
        glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
          (subEstimateLaw groupA) (fullFullCutoff groupA))
    (hmassFullFullB :
      S.massTestTaking groupB (policyPair Pfull Pfull) =
        glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
          (subEstimateLaw groupB) (fullFullCutoff groupB))
    (hmassFullSubA :
      S.massTestTaking groupA (policyPair Pfull Psub) =
        glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
          (subEstimateLaw groupA) (fullSubCutoff groupA))
    (hmassFullSubB :
      S.massTestTaking groupB (policyPair Pfull Psub) =
        glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
          (subEstimateLaw groupB) (fullSubCutoff groupB))
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
            S.massTestTaking groupA (policyPair Pfull Pfull) +
          populationShare groupB *
            S.massTestTaking groupB (policyPair Pfull Pfull))
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
            S.massTestTaking groupA (policyPair Pfull Pfull) +
          populationShare groupB *
            S.massTestTaking groupB (policyPair Pfull Pfull))
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
    (hJ1DropMerit :
      ∀ g,
        ¬ q1Sub < fullFullCutoff groupA →
          ¬ q1Sub < fullFullCutoff groupB →
            S.admittedAcademicMerit J1 g (policyPair Psub Pfull) =
              (standardGaussianHazardInverseCertificate.toGaussianHazardCertificate).normalUpperTailMean
                    (J1DropFamily g).posteriorMeanScaleLaw
                    (J1DropThreshold g))
    (hJ1KeepMerit :
      ∀ g,
        ¬ q1Sub < fullFullCutoff groupA →
          ¬ q1Sub < fullFullCutoff groupB →
            S.admittedAcademicMerit J1 g (policyPair Pfull Pfull) =
              (standardGaussianHazardInverseCertificate.toGaussianHazardCertificate).normalUpperTailMean
                    (J1KeepFamily g).posteriorMeanScaleLaw
                    (J1KeepThreshold g))
    (honlyA_J1_groupB_eq :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J1 groupB (policyPair Pfull Pfull) =
            S.admittedAcademicMerit J1 groupB (policyPair Psub Pfull))
    (honlyA_J1_groupA_testBased :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J1 groupA (policyPair Pfull Pfull) =
            subFullMeritOfCutoff groupA
              (subFullQ2Full groupA -
                subFullScale groupA *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost groupA / subFullV2 groupA)))
    (honlyA_J1_groupA_testFree :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J1 groupA (policyPair Psub Pfull) =
            subFullTestFreeMerit groupA)
    (honlyB_J1_groupA_eq :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J1 groupA (policyPair Pfull Pfull) =
            S.admittedAcademicMerit J1 groupA (policyPair Psub Pfull))
    (honlyB_J1_groupB_testBased :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J1 groupB (policyPair Pfull Pfull) =
            subFullMeritOfCutoff groupB
              (subFullQ2Full groupB -
                subFullScale groupB *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost groupB / subFullV2 groupB)))
    (honlyB_J1_groupB_testFree :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J1 groupB (policyPair Psub Pfull) =
            subFullTestFreeMerit groupB)
    (hfixedPoolMeritA :
      ¬ q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J2 groupA (policyPair Pfull Psub) <
            S.admittedAcademicMerit J2 groupA (policyPair Pfull Pfull))
    (hfixedPoolMeritB :
      ¬ q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J2 groupB (policyPair Pfull Psub) <
            S.admittedAcademicMerit J2 groupB (policyPair Pfull Pfull))
    (honlyA_J2_groupB_eq :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J2 groupB (policyPair Pfull Pfull) =
            S.admittedAcademicMerit J2 groupB (policyPair Pfull Psub))
    (honlyA_J2_groupA_testBased :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J2 groupA (policyPair Pfull Pfull) =
            standardGaussianHazardCertificate.normalUpperTailMean
              (lowBasedFamily groupA
                (testCost groupA)).posteriorMeanScaleLaw
              (lowBasedThreshold groupA (testCost groupA)))
    (honlyA_J2_groupA_testFree :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J2 groupA (policyPair Pfull Psub) =
            standardGaussianHazardCertificate.normalUpperTailMean
              (lowFreeFamily groupA).posteriorMeanScaleLaw
              (lowFreeThreshold groupA))
    (honlyB_J2_groupA_eq :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J2 groupA (policyPair Pfull Pfull) =
            S.admittedAcademicMerit J2 groupA (policyPair Pfull Psub))
    (honlyB_J2_groupB_testBased :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J2 groupB (policyPair Pfull Pfull) =
            standardGaussianHazardCertificate.normalUpperTailMean
              (lowBasedFamily groupB
                (testCost groupB)).posteriorMeanScaleLaw
              (lowBasedThreshold groupB (testCost groupB)))
    (honlyB_J2_groupB_testFree :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J2 groupB (policyPair Pfull Psub) =
            standardGaussianHazardCertificate.normalUpperTailMean
              (lowFreeFamily groupB).posteriorMeanScaleLaw
              (lowFreeThreshold groupB))
    (hnoExpandA :
      fullSubCutoff groupA < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S policyPair J1
          groupA groupB populationShare Psub Psub ≤
        glm20TwoGroupWeightedAcademicMeritObjective S policyPair J1
          groupA groupB populationShare Pfull Psub)
    (hexpandA_J1_groupB_eq :
      ¬ fullSubCutoff groupA < q1Sub →
        S.admittedAcademicMerit J1 groupB (policyPair Psub Psub) =
          S.admittedAcademicMerit J1 groupB (policyPair Pfull Psub))
    (hexpandA_J1_groupA_testFree :
      ¬ fullSubCutoff groupA < q1Sub →
        S.admittedAcademicMerit J1 groupA (policyPair Psub Psub) =
          standardGaussianHazardCertificate.normalUpperTailMean
            (highFreeFamily groupA).posteriorMeanScaleLaw
            (highFreeThreshold groupA))
    (hexpandA_J1_groupA_testBased :
      ¬ fullSubCutoff groupA < q1Sub →
        S.admittedAcademicMerit J1 groupA (policyPair Pfull Psub) =
          standardGaussianHazardCertificate.normalUpperTailMean
            (highBasedFamily groupA
              (testCost groupA)).posteriorMeanScaleLaw
            (highBasedThreshold groupA (testCost groupA)))
    (hnoExpandB :
      fullSubCutoff groupB < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S policyPair J1
          groupA groupB populationShare Psub Psub ≤
        glm20TwoGroupWeightedAcademicMeritObjective S policyPair J1
          groupA groupB populationShare Pfull Psub)
    (hexpandB_J1_groupA_eq :
      ¬ fullSubCutoff groupB < q1Sub →
        S.admittedAcademicMerit J1 groupA (policyPair Psub Psub) =
          S.admittedAcademicMerit J1 groupA (policyPair Pfull Psub))
    (hexpandB_J1_groupB_testFree :
      ¬ fullSubCutoff groupB < q1Sub →
        S.admittedAcademicMerit J1 groupB (policyPair Psub Psub) =
          standardGaussianHazardCertificate.normalUpperTailMean
            (highFreeFamily groupB).posteriorMeanScaleLaw
            (highFreeThreshold groupB))
    (hexpandB_J1_groupB_testBased :
      ¬ fullSubCutoff groupB < q1Sub →
        S.admittedAcademicMerit J1 groupB (policyPair Pfull Psub) =
          standardGaussianHazardCertificate.normalUpperTailMean
            (highBasedFamily groupB
              (testCost groupB)).posteriorMeanScaleLaw
            (highBasedThreshold groupB (testCost groupB)))
    (hJ2ObjectiveSubSub :
      glm20TwoGroupWeightedAcademicMeritObjective S policyPair J2
          groupA groupB populationShare Psub Psub =
        populationShare groupA *
            S.admittedAcademicMerit J2 groupA (policyPair Psub Psub) +
          populationShare groupB *
            S.admittedAcademicMerit J2 groupB (policyPair Psub Psub))
    (hJ2ObjectiveSubFullB :
      glm20TwoGroupWeightedAcademicMeritObjective S policyPair J2
          groupA groupB populationShare Psub Pfull =
        populationShare groupB *
          S.admittedAcademicMerit J2 groupB (policyPair Psub Pfull))
    (hJ2KeepsB :
      glm20Theorem3SubFullOtherGroupKeepsTest S policyPair Psub Pfull J2
        groupA groupB populationShare capacity2 groupB)
    (hJ2ObjectiveSubFullA :
      glm20TwoGroupWeightedAcademicMeritObjective S policyPair J2
          groupA groupB populationShare Psub Pfull =
        populationShare groupA *
          S.admittedAcademicMerit J2 groupA (policyPair Psub Pfull))
    (hJ2KeepsA :
      glm20Theorem3SubFullOtherGroupKeepsTest S policyPair Psub Pfull J2
        groupA groupB populationShare capacity2 groupA)
    (hcostA : 0 < testCost groupA) (hcostB : 0 < testCost groupB) :
    let fullSubLowTestBasedMerit : Group → ℝ → ℝ := fun g c =>
      standardGaussianHazardCertificate.normalUpperTailMean
        (lowBasedFamily g c).posteriorMeanScaleLaw
        (lowBasedThreshold g c)
    let fullSubLowTestFreeMerit : Group → ℝ := fun g =>
      standardGaussianHazardCertificate.normalUpperTailMean
        (lowFreeFamily g).posteriorMeanScaleLaw
        (lowFreeThreshold g)
    let fullSubHighTestBasedMerit : Group → ℝ → ℝ := fun g c =>
      standardGaussianHazardCertificate.normalUpperTailMean
        (highBasedFamily g c).posteriorMeanScaleLaw
        (highBasedThreshold g c)
    let fullSubHighTestFreeMerit : Group → ℝ := fun g =>
      standardGaussianHazardCertificate.normalUpperTailMean
        (highFreeFamily g).posteriorMeanScaleLaw
        (highFreeThreshold g)
    ∃ subFullCostThreshold fullSubLowCostThreshold
        fullSubHighCostThreshold : Group → ℝ,
      (∀ g, subFullCostThreshold g ∈
        Set.Ioo (subFullLeftCost g) (subFullRightCost g)) ∧
        (∀ g,
          subFullMeritOfCutoff g
              (subFullQ2Full g -
                subFullScale g *
                  standardGaussianQuantileAPI.quantile
                    (1 - subFullCostThreshold g / subFullV2 g)) =
            subFullTestFreeMerit g) ∧
          (∀ g c, c ∈ Set.Icc (subFullLeftCost g) (subFullRightCost g) →
            (subFullMeritOfCutoff g
                (subFullQ2Full g -
                  subFullScale g *
                    standardGaussianQuantileAPI.quantile
                      (1 - c / subFullV2 g)) ≤
                subFullTestFreeMerit g ↔
              subFullCostThreshold g ≤ c)) ∧
            (∀ g, fullSubLowCostThreshold g ∈
              Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
              (∀ g, fullSubHighCostThreshold g ∈
                Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
                (∀ g,
                  fullSubLowTestBasedMerit g
                      (fullSubLowCostThreshold g) =
                    fullSubLowTestFreeMerit g) ∧
                  (∀ g,
                    fullSubHighTestBasedMerit g
                        (fullSubHighCostThreshold g) =
                      fullSubHighTestFreeMerit g) ∧
                    (∀ g, 0 < fullSubLowCostThreshold g) ∧
                      (∀ g,
                        fullSubLowCostThreshold g <
                          fullSubHighCostThreshold g) ∧
                        ((S.policyPairIsEquilibrium Psub Pfull ↔
                            glm20Theorem3SubFullCondition S policyPair Psub
                              Pfull J2 groupA groupB populationShare
                              testCost subFullCostThreshold capacity2 q1Sub
                              (fun g q =>
                                glm20StrategicSubEstimateMassAbove
                                  standardGaussianCDFAPI
                                  (subEstimateLaw g) q)) ∧
                          (S.policyPairIsEquilibrium Pfull Psub ↔
                            glm20Theorem3FullSubCondition S policyPair Psub
                              Pfull groupA groupB testCost
                              fullSubLowCostThreshold
                              fullSubHighCostThreshold q1Sub q2Sub
                              (fun g q =>
                                glm20StrategicSubEstimateMassAbove
                                  standardGaussianCDFAPI
                                  (subEstimateLaw g) q)) ∧
                            glm20Theorem3FullFullCondition S Pfull groupA
                              groupB testCost) := by
  let fullSubLowTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    standardGaussianHazardCertificate.normalUpperTailMean
      (lowBasedFamily g c).posteriorMeanScaleLaw
      (lowBasedThreshold g c)
  let fullSubLowTestFreeMerit : Group → ℝ := fun g =>
    standardGaussianHazardCertificate.normalUpperTailMean
      (lowFreeFamily g).posteriorMeanScaleLaw
      (lowFreeThreshold g)
  let fullSubHighTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    standardGaussianHazardCertificate.normalUpperTailMean
      (highBasedFamily g c).posteriorMeanScaleLaw
      (highBasedThreshold g c)
  let fullSubHighTestFreeMerit : Group → ℝ := fun g =>
    standardGaussianHazardCertificate.normalUpperTailMean
      (highFreeFamily g).posteriorMeanScaleLaw
      (highFreeThreshold g)
  have hfullSubBridge :
      ∃ fullSubLowCostThreshold fullSubHighCostThreshold : Group → ℝ,
        (∀ g, fullSubLowCostThreshold g ∈
          Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
          (∀ g, fullSubHighCostThreshold g ∈
            Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
            (∀ g,
              fullSubLowTestBasedMerit g (fullSubLowCostThreshold g) =
                fullSubLowTestFreeMerit g) ∧
              (∀ g,
                fullSubHighTestBasedMerit g
                    (fullSubHighCostThreshold g) =
                  fullSubHighTestFreeMerit g) ∧
                (∀ g, 0 < fullSubLowCostThreshold g) ∧
                  (∀ g,
                    fullSubLowCostThreshold g <
                      fullSubHighCostThreshold g) ∧
                    ((glm20TwoGroupWeightedAcademicMeritObjective S
                          policyPair J1 groupA groupB populationShare Psub
                          Psub ≤
                        glm20TwoGroupWeightedAcademicMeritObjective S
                          policyPair J1 groupA groupB populationShare Pfull
                          Psub ∧
                      glm20TwoGroupWeightedAcademicMeritObjective S
                          policyPair J2 groupA groupB populationShare Pfull
                          Pfull ≤
                        glm20TwoGroupWeightedAcademicMeritObjective S
                          policyPair J2 groupA groupB populationShare Pfull
                          Psub) ↔
                      glm20Theorem3FullSubCondition S policyPair Psub Pfull
                        groupA groupB testCost fullSubLowCostThreshold
                        fullSubHighCostThreshold q1Sub q2Sub
                        (fun g q =>
                          glm20StrategicSubEstimateMassAbove
                            standardGaussianCDFAPI (subEstimateLaw g) q)) := by
    simpa [fullSubLowTestBasedMerit, fullSubLowTestFreeMerit,
      fullSubHighTestBasedMerit, fullSubHighTestFreeMerit] using
      (paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_threshold_order_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows
        (S := S) (policyPair := policyPair) (Psub := Psub)
        (Pfull := Pfull) (J1 := J1) (J2 := J2) (groupA := groupA)
        (groupB := groupB) (populationShare := populationShare)
        (testCost := testCost) (leftCost := fullSubLeftCost)
        (rightCost := fullSubRightCost) (capacity2 := capacity2)
        (q1Sub := q1Sub) (q2Sub := q2Sub) subEstimateLaw
        (fullFullCutoff := fullFullCutoff)
        (fullSubCutoff := fullSubCutoff) lowFreeFamily highFreeFamily
        lowFreeThreshold highFreeThreshold lowBasedFamily highBasedFamily
        lowBasedThreshold highBasedThreshold lowBasedLaw highBasedLaw
        hlowFreeLaw hlowBasedLaw hhighFreeLaw hhighBasedLaw
        hlowThresholdCont hlowThresholdAnti hhighThresholdCont
        hhighThresholdAnti hfullSubLeftRight hfullSubLeftPos
        hfullSubCostMem hlowAtLeftThreshold hlowAtRightThreshold
        hhighAtLeftThreshold hhighAtRightThreshold hfreePriorMean
        hfreePriorVar
        hfreePrecision hfreeThresholdMean hfreeThreshold hbasedPriorMean
        hbasedPriorVar hbasedPrecision hbasedThresholdMean hbasedThreshold
        hshareA hshareB hmassFullFullA hmassFullFullB hmassFullSubA
        hmassFullSubB hcapacity2 hfillFullFull2 hfixedPoolMeritA
        hfixedPoolMeritB honlyA_J2_groupB_eq honlyA_J2_groupA_testBased
        honlyA_J2_groupA_testFree honlyB_J2_groupA_eq
        honlyB_J2_groupB_testBased honlyB_J2_groupB_testFree hnoExpandA
        hexpandA_J1_groupB_eq hexpandA_J1_groupA_testFree
        hexpandA_J1_groupA_testBased hnoExpandB hexpandB_J1_groupA_eq
        hexpandB_J1_groupB_testFree hexpandB_J1_groupB_testBased)
  simpa [fullSubLowTestBasedMerit, fullSubLowTestFreeMerit,
    fullSubHighTestBasedMerit, fullSubHighTestFreeMerit] using
    (paper_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_standardGaussian_subFull_keep_test_bridge_and_fullSub_objective_bridge
      (S := S) (massTestTaking := massTestTaking)
      (admittedAcademicMerit := admittedAcademicMerit)
      (diversity := diversity) (policyPair := policyPair)
      (Psub := Psub) (Pfull := Pfull) (J1 := J1) (J2 := J2)
      (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (subFullQ2Full := subFullQ2Full)
      (subFullScale := subFullScale) (subFullV2 := subFullV2)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost) (capacity1 := capacity1)
      (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff) subEstimateLaw
      subFullMeritOfCutoff subFullTestFreeMerit J1DropFamily
      J1KeepFamily J1DropThreshold J1KeepThreshold
      fullSubLowTestBasedMerit fullSubLowTestFreeMerit
      fullSubHighTestBasedMerit fullSubHighTestFreeMerit hS
      hsubFullLeftRight hsubFullScale hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullMeritCont
      hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight hshareA
      hshareB hmassFullFullA hmassFullFullB hcapacity1 hfillFullFull1
      hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ1DropMerit hJ1KeepMerit honlyA_J1_groupB_eq
      honlyA_J1_groupA_testBased honlyA_J1_groupA_testFree
      honlyB_J1_groupA_eq honlyB_J1_groupB_testBased
      honlyB_J1_groupB_testFree hJ2ObjectiveSubSub
      hJ2ObjectiveSubFullB hJ2KeepsB hJ2ObjectiveSubFullA hJ2KeepsA
      hfullSubBridge hcostA hcostB)

end

end GLM20DroppingStandardizedTesting
