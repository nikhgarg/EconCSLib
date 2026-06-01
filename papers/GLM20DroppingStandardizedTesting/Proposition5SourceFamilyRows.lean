import GLM20DroppingStandardizedTesting.PaperSurfaceWrappers
import GLM20DroppingStandardizedTesting.Theorem3SimplePremises

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Proposition 5(i) school-`J2` objective rows on the concrete policy-state
table.

The two-group weighted academic-merit objective has the paper's displayed
`(P_sub,P_sub)` row definitionally.  Under `(P_sub,P_full)`, it reduces to the
surviving group's weighted merit as soon as the expanding group's admitted
merit row is zero.
-/
theorem
    paper_proposition5_policyStateTable_j2_weighted_objective_rows_of_subFull_zero_components
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (subSubMerit subFullMerit fullSubMerit fullFullMerit :
      School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare : Group → ℝ) :
    let S :=
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface api
        subEstimateLaw subSubMass subFullMass fullFullCutoff fullSubCutoff
        subSubMerit subFullMerit fullSubMerit fullFullMerit diversity J1 J2
        groupA groupB populationShare
    let objective2 :=
      glm20TwoGroupWeightedAcademicMeritObjective S
        glm20StrategicPolicyStatePair J2 groupA groupB populationShare
    objective2 GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleSub =
      populationShare groupA * subSubMerit J2 groupA +
        populationShare groupB * subSubMerit J2 groupB ∧
    (subFullMerit J2 groupA = 0 →
      objective2 GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull =
        populationShare groupB * subFullMerit J2 groupB) ∧
    (subFullMerit J2 groupB = 0 →
      objective2 GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull =
        populationShare groupA * subFullMerit J2 groupA) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [glm20TwoGroupWeightedAcademicMeritObjective,
      glm20TwoGroupWeightedAcademicMerit,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit]
  · intro hzeroA
    simp [glm20TwoGroupWeightedAcademicMeritObjective,
      glm20TwoGroupWeightedAcademicMerit,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit, hzeroA]
  · intro hzeroB
    simp [glm20TwoGroupWeightedAcademicMeritObjective,
      glm20TwoGroupWeightedAcademicMerit,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit, hzeroB]

/--
Proposition 5(i) source-family row wrapper.

This specializes the raw source-family Proposition 5 bridge to the generated
Theorem 3 source-family policy-state table and exposes the school-`J2`
survivor requirements as the displayed `subFullMass`/`subFullMeritBase` rows.
-/
abbrev
    paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_source_family_survivor_components
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
      subFullQ2Full subFullScale subFullV2 : Group → ℝ}
    {capacity1 capacity2 q1Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    (objective2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → ℝ)
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2)
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
    (honlyA_J1_groupB_eq :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          C.normalUpperTailMean
              (J1KeepFamily groupB).posteriorMeanScaleLaw
              (J1KeepThreshold groupB) =
            C.normalUpperTailMean
              (J1DropFamily groupB).posteriorMeanScaleLaw
              (J1DropThreshold groupB))
    (honlyA_J1_groupA_testBased :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          C.normalUpperTailMean
              (J1KeepFamily groupA).posteriorMeanScaleLaw
              (J1KeepThreshold groupA) =
            subFullMeritOfCutoff groupA
              (subFullQ2Full groupA -
                subFullScale groupA *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost groupA / subFullV2 groupA)))
    (honlyA_J1_groupA_testFree :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          C.normalUpperTailMean
              (J1DropFamily groupA).posteriorMeanScaleLaw
              (J1DropThreshold groupA) =
            subFullTestFreeMerit groupA)
    (honlyB_J1_groupA_eq :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          C.normalUpperTailMean
              (J1KeepFamily groupA).posteriorMeanScaleLaw
              (J1KeepThreshold groupA) =
            C.normalUpperTailMean
              (J1DropFamily groupA).posteriorMeanScaleLaw
              (J1DropThreshold groupA))
    (honlyB_J1_groupB_testBased :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          C.normalUpperTailMean
              (J1KeepFamily groupB).posteriorMeanScaleLaw
              (J1KeepThreshold groupB) =
            subFullMeritOfCutoff groupB
              (subFullQ2Full groupB -
                subFullScale groupB *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost groupB / subFullV2 groupB)))
    (honlyB_J1_groupB_testFree :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          C.normalUpperTailMean
              (J1DropFamily groupB).posteriorMeanScaleLaw
              (J1DropThreshold groupB) =
            subFullTestFreeMerit groupB)
    (hJ2ObjectiveSubSub :
      objective2 GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleSub =
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB)
    (hJ2ObjectiveSubFullB :
      objective2 GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull =
        populationShare groupB * subFullMeritBase J2 groupB)
    (hJ2MassB : subFullMass groupB ≥ capacity2)
    (hJ2MeritGtB :
      populationShare groupB * subFullMeritBase J2 groupB >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB)
    (hJ2ObjectiveSubFullA :
      objective2 GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull =
        populationShare groupA * subFullMeritBase J2 groupA)
    (hJ2MassA : subFullMass groupA ≥ capacity2)
    (hJ2MeritGtA :
      populationShare groupA * subFullMeritBase J2 groupA >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB) :=
  have hJ2_ne_J1 : J2 ≠ J1 := by
    intro h
    exact hJ1_ne_J2 h.symm
  paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_raw_survivor_conditions
    (Q := standardGaussianQuantileAPI) (C := C)
    (S :=
      glm20Theorem3SourceFamilyPolicyStateTableSurface
        standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
        subSubMerit subFullMeritBase fullSubMeritFallback
        fullFullMeritFallback diversity J1 J2 groupA groupB
        populationShare fullFullCutoff fullSubCutoff C J1DropFamily
        J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold)
    (policyPair := glm20StrategicPolicyStatePair)
    (Psub := GLM20StrategicPolicyState.singleSub)
    (Pfull := GLM20StrategicPolicyState.singleFull)
    (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (leftCost := subFullLeftCost) (rightCost := subFullRightCost)
    (q2Full := subFullQ2Full) (scale := subFullScale)
    (v2 := subFullV2) (capacity1 := capacity1)
    (capacity2 := capacity2) (q1Sub := q1Sub) subEstimateLaw
    (fullFullCutoff := fullFullCutoff) objective2 subFullMeritOfCutoff
    subFullTestFreeMerit J1DropFamily J1KeepFamily J1DropThreshold
    J1KeepThreshold hsubFullLeftRight hsubFullScale hsubFullLeftPos
    hsubFullRightLtV2 hsubFullCostMem hsubFullMeritCont
    hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight hshareA hshareB
    (by
      simp [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass,
        glm20StrategicSubEstimateMassAbove, standardGaussianQuantileAPI])
    (by
      simp [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass,
        glm20StrategicSubEstimateMassAbove, standardGaussianQuantileAPI])
    (by
      simpa [standardGaussianQuantileAPI] using hcapacity1)
    (by
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass,
        glm20StrategicSubEstimateMassAbove, standardGaussianQuantileAPI] using
        hfillFullFull1)
    hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean hJ1Threshold
    (by
      intro g _ _
      change
        glm20Theorem3SourceFamilySubFullMeritTable C J1 J1DropFamily
            J1DropThreshold subFullMeritBase J1 g =
          C.normalUpperTailMean
            (J1DropFamily g).posteriorMeanScaleLaw
            (J1DropThreshold g)
      simp [glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow])
    (by
      intro g _ _
      change
        glm20Theorem3SourceFamilyFullFullMeritTable C J1 J2 J1KeepFamily
            J2KeepFamily J1KeepThreshold J2KeepThreshold
            fullFullMeritFallback J1 g =
          C.normalUpperTailMean
            (J1KeepFamily g).posteriorMeanScaleLaw
            (J1KeepThreshold g)
      simp [glm20Theorem3SourceFamilyFullFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ1_ne_J2])
    (by
      intro hA hB
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20Theorem3SourceFamilyFullFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ1_ne_J2] using
        honlyA_J1_groupB_eq hA hB)
    (by
      intro hA hB
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilyFullFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ1_ne_J2] using
        honlyA_J1_groupA_testBased hA hB)
    (by
      intro hA hB
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow] using
        honlyA_J1_groupA_testFree hA hB)
    (by
      intro hB hA
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20Theorem3SourceFamilyFullFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ1_ne_J2] using
        honlyB_J1_groupA_eq hB hA)
    (by
      intro hB hA
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilyFullFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ1_ne_J2] using
        honlyB_J1_groupB_testBased hB hA)
    (by
      intro hB hA
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow] using
        honlyB_J1_groupB_testFree hB hA)
    (by
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit] using hJ2ObjectiveSubSub)
    (by
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
        hJ2ObjectiveSubFullB)
    (by
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface] using
        hJ2MassB)
    (by
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
        hJ2MeritGtB)
    (by
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
        hJ2ObjectiveSubFullA)
    (by
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface] using
        hJ2MassA)
    (by
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
        hJ2MeritGtA)

/--
Proposition 5(i) source-family row wrapper with condition (11)--(12) supplied
as the same bundled source-row predicate used by the strongest Theorem 3
surface.

The only difference from
`paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_source_family_survivor_components`
is that the four school-`J2` survivor mass/merit assumptions are packaged as
`GLM20Theorem3J2SurvivorRows`.
-/
abbrev
    paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_survivor_rows
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
      subFullQ2Full subFullScale subFullV2 : Group → ℝ}
    {capacity1 capacity2 q1Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    (objective2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → ℝ)
    (subFullMeritOfCutoff : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2)
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
    (honlyA_J1_groupB_eq :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          C.normalUpperTailMean
              (J1KeepFamily groupB).posteriorMeanScaleLaw
              (J1KeepThreshold groupB) =
            C.normalUpperTailMean
              (J1DropFamily groupB).posteriorMeanScaleLaw
              (J1DropThreshold groupB))
    (honlyA_J1_groupA_testBased :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          C.normalUpperTailMean
              (J1KeepFamily groupA).posteriorMeanScaleLaw
              (J1KeepThreshold groupA) =
            subFullMeritOfCutoff groupA
              (subFullQ2Full groupA -
                subFullScale groupA *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost groupA / subFullV2 groupA)))
    (honlyA_J1_groupA_testFree :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          C.normalUpperTailMean
              (J1DropFamily groupA).posteriorMeanScaleLaw
              (J1DropThreshold groupA) =
            subFullTestFreeMerit groupA)
    (honlyB_J1_groupA_eq :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          C.normalUpperTailMean
              (J1KeepFamily groupA).posteriorMeanScaleLaw
              (J1KeepThreshold groupA) =
            C.normalUpperTailMean
              (J1DropFamily groupA).posteriorMeanScaleLaw
              (J1DropThreshold groupA))
    (honlyB_J1_groupB_testBased :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          C.normalUpperTailMean
              (J1KeepFamily groupB).posteriorMeanScaleLaw
              (J1KeepThreshold groupB) =
            subFullMeritOfCutoff groupB
              (subFullQ2Full groupB -
                subFullScale groupB *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost groupB / subFullV2 groupB)))
    (honlyB_J1_groupB_testFree :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          C.normalUpperTailMean
              (J1DropFamily groupB).posteriorMeanScaleLaw
              (J1DropThreshold groupB) =
            subFullTestFreeMerit groupB)
    (hJ2ObjectiveSubSub :
      objective2 GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleSub =
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB)
    (hJ2ObjectiveSubFullB :
      objective2 GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull =
        populationShare groupB * subFullMeritBase J2 groupB)
    (hJ2ObjectiveSubFullA :
      objective2 GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull =
        populationShare groupA * subFullMeritBase J2 groupA)
    (hJ2SurvivorRows :
      GLM20Theorem3J2SurvivorRows populationShare subFullMass
        subSubMerit subFullMeritBase J2 groupA groupB capacity2) :=
  have hrows :=
    paper_theorem3_j2_survivor_rows_components hJ2SurvivorRows
  paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_source_family_survivor_components
    (subEstimateLaw := subEstimateLaw) (subSubMass := subSubMass)
    (subFullMass := subFullMass) (subSubMerit := subSubMerit)
    (subFullMeritBase := subFullMeritBase)
    (fullSubMeritFallback := fullSubMeritFallback)
    (fullFullMeritFallback := fullFullMeritFallback)
    (diversity := diversity) (J1 := J1) (J2 := J2)
    (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff) objective2 subFullMeritOfCutoff
    subFullTestFreeMerit C J1DropFamily J2DropFamily J1KeepFamily
    J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
    J2KeepThreshold hJ1_ne_J2 hsubFullLeftRight hsubFullScale
    hsubFullLeftPos hsubFullRightLtV2 hsubFullCostMem hsubFullMeritCont
    hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight hshareA hshareB
    hcapacity1 hfillFullFull1 hJ1PriorMean hJ1PriorVar hJ1Precision
    hJ1ThresholdMean hJ1Threshold honlyA_J1_groupB_eq
    honlyA_J1_groupA_testBased honlyA_J1_groupA_testFree
    honlyB_J1_groupA_eq honlyB_J1_groupB_testBased
    honlyB_J1_groupB_testFree hJ2ObjectiveSubSub hJ2ObjectiveSubFullB
    hrows.1 hrows.2.1 hJ2ObjectiveSubFullA hrows.2.2.1 hrows.2.2.2

/--
Standard-Gaussian Proposition 5(i) source-family bridge with survivor source
rows bundled as `GLM20Theorem3J2SurvivorRows`.
-/
abbrev
    paper_proposition5_standardGaussian_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_survivor_rows
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost subFullLeftCost subFullRightCost
      subFullQ2Full subFullScale subFullV2 : Group → ℝ}
    {capacity1 capacity2 q1Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ} :=
  paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_survivor_rows
    (Group := Group) (School := School) (FeatureDrop := FeatureDrop)
    (FeatureKeep := FeatureKeep) (J1 := J1) (J2 := J2)
    (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (C := standardGaussianHazardInverseCertificate.toGaussianHazardCertificate)

/--
Standard-Gaussian Proposition 5(i) source-family bridge, specialized to the
paper's named groups, named schools, and population-share row `(1 - pi, pi)`.

Compared with
`paper_proposition5_standardGaussian_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_survivor_rows`,
this paper-facing wrapper discharges the `J1 ≠ J2` and positive-share
side-conditions from `0 < pi < 1`.
-/
abbrev
    paper_proposition5_standardGaussian_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_survivor_rows_paper_groups_schools_with_population_share
    {FeatureDrop FeatureKeep : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    {pi : ℝ}
    {testCost subFullLeftCost subFullRightCost
      subFullQ2Full subFullScale subFullV2 : GLM20Group → ℝ}
    {capacity1 capacity2 q1Sub : ℝ}
    {fullFullCutoff fullSubCutoff : GLM20Group → ℝ}
    (objective2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → ℝ)
    (subFullMeritOfCutoff : GLM20Group → ℝ → ℝ)
    (subFullTestFreeMerit : GLM20Group → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
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
    (hcapacity1 :
      capacity1 =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupA) q1Sub +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupB) q1Sub)
    (hfillFullFull1 :
      capacity1 ≤
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupA)
              (fullFullCutoff GLM20Group.groupA) +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            glm20StrategicSubEstimateMassAbove standardGaussianCDFAPI
              (subEstimateLaw GLM20Group.groupB)
              (fullFullCutoff GLM20Group.groupB))
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
    (honlyA_J1_groupB_eq :
      q1Sub < fullFullCutoff GLM20Group.groupA →
        ¬ q1Sub < fullFullCutoff GLM20Group.groupB →
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate.normalUpperTailMean
              (J1KeepFamily GLM20Group.groupB).posteriorMeanScaleLaw
              (J1KeepThreshold GLM20Group.groupB) =
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate.normalUpperTailMean
              (J1DropFamily GLM20Group.groupB).posteriorMeanScaleLaw
              (J1DropThreshold GLM20Group.groupB))
    (honlyA_J1_groupA_testBased :
      q1Sub < fullFullCutoff GLM20Group.groupA →
        ¬ q1Sub < fullFullCutoff GLM20Group.groupB →
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate.normalUpperTailMean
              (J1KeepFamily GLM20Group.groupA).posteriorMeanScaleLaw
              (J1KeepThreshold GLM20Group.groupA) =
            subFullMeritOfCutoff GLM20Group.groupA
              (subFullQ2Full GLM20Group.groupA -
                subFullScale GLM20Group.groupA *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost GLM20Group.groupA /
                      subFullV2 GLM20Group.groupA)))
    (honlyA_J1_groupA_testFree :
      q1Sub < fullFullCutoff GLM20Group.groupA →
        ¬ q1Sub < fullFullCutoff GLM20Group.groupB →
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate.normalUpperTailMean
              (J1DropFamily GLM20Group.groupA).posteriorMeanScaleLaw
              (J1DropThreshold GLM20Group.groupA) =
            subFullTestFreeMerit GLM20Group.groupA)
    (honlyB_J1_groupA_eq :
      q1Sub < fullFullCutoff GLM20Group.groupB →
        ¬ q1Sub < fullFullCutoff GLM20Group.groupA →
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate.normalUpperTailMean
              (J1KeepFamily GLM20Group.groupA).posteriorMeanScaleLaw
              (J1KeepThreshold GLM20Group.groupA) =
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate.normalUpperTailMean
              (J1DropFamily GLM20Group.groupA).posteriorMeanScaleLaw
              (J1DropThreshold GLM20Group.groupA))
    (honlyB_J1_groupB_testBased :
      q1Sub < fullFullCutoff GLM20Group.groupB →
        ¬ q1Sub < fullFullCutoff GLM20Group.groupA →
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate.normalUpperTailMean
              (J1KeepFamily GLM20Group.groupB).posteriorMeanScaleLaw
              (J1KeepThreshold GLM20Group.groupB) =
            subFullMeritOfCutoff GLM20Group.groupB
              (subFullQ2Full GLM20Group.groupB -
                subFullScale GLM20Group.groupB *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost GLM20Group.groupB /
                      subFullV2 GLM20Group.groupB)))
    (honlyB_J1_groupB_testFree :
      q1Sub < fullFullCutoff GLM20Group.groupB →
        ¬ q1Sub < fullFullCutoff GLM20Group.groupA →
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate.normalUpperTailMean
              (J1DropFamily GLM20Group.groupB).posteriorMeanScaleLaw
              (J1DropThreshold GLM20Group.groupB) =
            subFullTestFreeMerit GLM20Group.groupB)
    (hJ2ObjectiveSubSub :
      objective2 GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleSub =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
            subSubMerit glm20SchoolJ2 GLM20Group.groupA +
          glm20Theorem3PopulationShare pi GLM20Group.groupB *
            subSubMerit glm20SchoolJ2 GLM20Group.groupB)
    (hJ2ObjectiveSubFullB :
      objective2 GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull =
        glm20Theorem3PopulationShare pi GLM20Group.groupB *
          subFullMeritBase glm20SchoolJ2 GLM20Group.groupB)
    (hJ2ObjectiveSubFullA :
      objective2 GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull =
        glm20Theorem3PopulationShare pi GLM20Group.groupA *
          subFullMeritBase glm20SchoolJ2 GLM20Group.groupA)
    (hJ2SurvivorRows :
      GLM20Theorem3J2SurvivorRows (glm20Theorem3PopulationShare pi)
        subFullMass subSubMerit subFullMeritBase glm20SchoolJ2
        GLM20Group.groupA GLM20Group.groupB capacity2) :=
  let hshares := glm20Theorem3PopulationShare_pos_of_pi_mem_Ioo hpi
  paper_proposition5_standardGaussian_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_survivor_rows
    (Group := GLM20Group) (School := GLM20School)
    (FeatureDrop := FeatureDrop) (FeatureKeep := FeatureKeep)
    (J1 := glm20SchoolJ1) (J2 := glm20SchoolJ2)
    (groupA := GLM20Group.groupA) (groupB := GLM20Group.groupB)
    (populationShare := glm20Theorem3PopulationShare pi)
    (testCost := testCost) (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
    fullSubMeritFallback fullFullMeritFallback diversity objective2
    subFullMeritOfCutoff subFullTestFreeMerit J1DropFamily J2DropFamily
    J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
    J2DropThreshold J2KeepThreshold glm20SchoolJ1_ne_J2
    hsubFullLeftRight hsubFullScale hsubFullLeftPos hsubFullRightLtV2
    hsubFullCostMem hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft
    hsubFullAtRight hshares.1 hshares.2 hcapacity1 hfillFullFull1
    hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean hJ1Threshold
    honlyA_J1_groupB_eq honlyA_J1_groupA_testBased
    honlyA_J1_groupA_testFree honlyB_J1_groupA_eq
    honlyB_J1_groupB_testBased honlyB_J1_groupB_testFree
    hJ2ObjectiveSubSub hJ2ObjectiveSubFullB hJ2ObjectiveSubFullA
    hJ2SurvivorRows

/--
Standard-Gaussian Proposition 5(i) source-family bridge with survivor source
rows.

This is the paper-facing specialization of
`paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_source_family_survivor_components`:
the Gaussian hazard certificate is fixed internally to the repository's
standard-Gaussian certificate.
-/
abbrev
    paper_proposition5_standardGaussian_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_source_family_survivor_components
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost subFullLeftCost subFullRightCost
      subFullQ2Full subFullScale subFullV2 : Group → ℝ}
    {capacity1 capacity2 q1Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ} :=
  paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_source_family_survivor_components
    (Group := Group) (School := School) (FeatureDrop := FeatureDrop)
    (FeatureKeep := FeatureKeep) (J1 := J1) (J2 := J2)
    (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (subFullQ2Full := subFullQ2Full)
    (subFullScale := subFullScale) (subFullV2 := subFullV2)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (C := standardGaussianHazardInverseCertificate.toGaussianHazardCertificate)

/--
The Bayesian-game row package needed by the generated source-family
exactly-one objective bridge.

These are the twelve admitted-merit identifications left after the table
bookkeeping is unfolded: on each one-expanding-group branch, the non-expanding
group's posterior row is unchanged and the expanding group's row is identified
with the paper's test-based or test-free merit formula.
-/
structure GLM20Proposition5ExactlyOneObjectiveSourceFamilyRows
    {Group FeatureDrop FeatureKeep : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    (testCost : Group → ℝ) (q1Sub q2Sub : ℝ)
    (fullFullCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (subFullTestBasedMerit : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (fullSubLowTestBasedMerit : Group → ℝ → ℝ)
    (fullSubLowTestFreeMerit : Group → ℝ)
    (groupA groupB : Group) : Prop where
  honlyA_J1_groupB_eq :
    q1Sub < fullFullCutoff groupA →
      ¬ q1Sub < fullFullCutoff groupB →
        C.normalUpperTailMean
            (J1KeepFamily groupB).posteriorMeanScaleLaw
            (J1KeepThreshold groupB) =
          C.normalUpperTailMean
            (J1DropFamily groupB).posteriorMeanScaleLaw
            (J1DropThreshold groupB)
  honlyA_J1_groupA_testBased :
    q1Sub < fullFullCutoff groupA →
      ¬ q1Sub < fullFullCutoff groupB →
        C.normalUpperTailMean
            (J1KeepFamily groupA).posteriorMeanScaleLaw
            (J1KeepThreshold groupA) =
          subFullTestBasedMerit groupA (testCost groupA)
  honlyA_J1_groupA_testFree :
    q1Sub < fullFullCutoff groupA →
      ¬ q1Sub < fullFullCutoff groupB →
        C.normalUpperTailMean
            (J1DropFamily groupA).posteriorMeanScaleLaw
            (J1DropThreshold groupA) =
          subFullTestFreeMerit groupA
  honlyB_J1_groupA_eq :
    q1Sub < fullFullCutoff groupB →
      ¬ q1Sub < fullFullCutoff groupA →
        C.normalUpperTailMean
            (J1KeepFamily groupA).posteriorMeanScaleLaw
            (J1KeepThreshold groupA) =
          C.normalUpperTailMean
            (J1DropFamily groupA).posteriorMeanScaleLaw
            (J1DropThreshold groupA)
  honlyB_J1_groupB_testBased :
    q1Sub < fullFullCutoff groupB →
      ¬ q1Sub < fullFullCutoff groupA →
        C.normalUpperTailMean
            (J1KeepFamily groupB).posteriorMeanScaleLaw
            (J1KeepThreshold groupB) =
          subFullTestBasedMerit groupB (testCost groupB)
  honlyB_J1_groupB_testFree :
    q1Sub < fullFullCutoff groupB →
      ¬ q1Sub < fullFullCutoff groupA →
        C.normalUpperTailMean
            (J1DropFamily groupB).posteriorMeanScaleLaw
            (J1DropThreshold groupB) =
          subFullTestFreeMerit groupB
  honlyA_J2_groupB_eq :
    q2Sub < fullFullCutoff groupA →
      ¬ q2Sub < fullFullCutoff groupB →
        C.normalUpperTailMean
            (J2KeepFamily groupB).posteriorMeanScaleLaw
            (J2KeepThreshold groupB) =
          C.normalUpperTailMean
            (J2DropFamily groupB).posteriorMeanScaleLaw
            (J2DropThreshold groupB)
  honlyA_J2_groupA_testBased :
    q2Sub < fullFullCutoff groupA →
      ¬ q2Sub < fullFullCutoff groupB →
        C.normalUpperTailMean
            (J2KeepFamily groupA).posteriorMeanScaleLaw
            (J2KeepThreshold groupA) =
          fullSubLowTestBasedMerit groupA (testCost groupA)
  honlyA_J2_groupA_testFree :
    q2Sub < fullFullCutoff groupA →
      ¬ q2Sub < fullFullCutoff groupB →
        C.normalUpperTailMean
            (J2DropFamily groupA).posteriorMeanScaleLaw
            (J2DropThreshold groupA) =
          fullSubLowTestFreeMerit groupA
  honlyB_J2_groupA_eq :
    q2Sub < fullFullCutoff groupB →
      ¬ q2Sub < fullFullCutoff groupA →
        C.normalUpperTailMean
            (J2KeepFamily groupA).posteriorMeanScaleLaw
            (J2KeepThreshold groupA) =
          C.normalUpperTailMean
            (J2DropFamily groupA).posteriorMeanScaleLaw
            (J2DropThreshold groupA)
  honlyB_J2_groupB_testBased :
    q2Sub < fullFullCutoff groupB →
      ¬ q2Sub < fullFullCutoff groupA →
        C.normalUpperTailMean
            (J2KeepFamily groupB).posteriorMeanScaleLaw
            (J2KeepThreshold groupB) =
          fullSubLowTestBasedMerit groupB (testCost groupB)
  honlyB_J2_groupB_testFree :
    q2Sub < fullFullCutoff groupB →
      ¬ q2Sub < fullFullCutoff groupA →
        C.normalUpperTailMean
            (J2DropFamily groupB).posteriorMeanScaleLaw
            (J2DropThreshold groupB) =
          fullSubLowTestFreeMerit groupB

/--
The generated source-family policy-state table reduces the exactly-one
weighted-objective branches to twelve visible admitted-merit row facts.

This is the bookkeeping bridge needed before the Bayesian-game layer: the
table itself supplies the four policy rows as Gaussian upper-tail means, while
the caller still proves the substantive row identifications saying that the
non-expanding group's row is unchanged and the expanding group's row matches
the paper's test-based or test-free merit formula.
-/
theorem
    paper_proposition5_exactly_one_weighted_objective_iff_of_source_family_policy_state_table_rows
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
    {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost : Group → ℝ}
    {q1Sub q2Sub : ℝ} {fullFullCutoff fullSubCutoff : Group → ℝ}
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2)
    (subFullTestBasedMerit : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (fullSubLowTestBasedMerit : Group → ℝ → ℝ)
    (fullSubLowTestFreeMerit : Group → ℝ)
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
    (honlyA_J1_groupB_eq :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          C.normalUpperTailMean
              (J1KeepFamily groupB).posteriorMeanScaleLaw
              (J1KeepThreshold groupB) =
            C.normalUpperTailMean
              (J1DropFamily groupB).posteriorMeanScaleLaw
              (J1DropThreshold groupB))
    (honlyA_J1_groupA_testBased :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          C.normalUpperTailMean
              (J1KeepFamily groupA).posteriorMeanScaleLaw
              (J1KeepThreshold groupA) =
            subFullTestBasedMerit groupA (testCost groupA))
    (honlyA_J1_groupA_testFree :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          C.normalUpperTailMean
              (J1DropFamily groupA).posteriorMeanScaleLaw
              (J1DropThreshold groupA) =
            subFullTestFreeMerit groupA)
    (honlyB_J1_groupA_eq :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          C.normalUpperTailMean
              (J1KeepFamily groupA).posteriorMeanScaleLaw
              (J1KeepThreshold groupA) =
            C.normalUpperTailMean
              (J1DropFamily groupA).posteriorMeanScaleLaw
              (J1DropThreshold groupA))
    (honlyB_J1_groupB_testBased :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          C.normalUpperTailMean
              (J1KeepFamily groupB).posteriorMeanScaleLaw
              (J1KeepThreshold groupB) =
            subFullTestBasedMerit groupB (testCost groupB))
    (honlyB_J1_groupB_testFree :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          C.normalUpperTailMean
              (J1DropFamily groupB).posteriorMeanScaleLaw
              (J1DropThreshold groupB) =
            subFullTestFreeMerit groupB)
    (honlyA_J2_groupB_eq :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          C.normalUpperTailMean
              (J2KeepFamily groupB).posteriorMeanScaleLaw
              (J2KeepThreshold groupB) =
            C.normalUpperTailMean
              (J2DropFamily groupB).posteriorMeanScaleLaw
              (J2DropThreshold groupB))
    (honlyA_J2_groupA_testBased :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          C.normalUpperTailMean
              (J2KeepFamily groupA).posteriorMeanScaleLaw
              (J2KeepThreshold groupA) =
            fullSubLowTestBasedMerit groupA (testCost groupA))
    (honlyA_J2_groupA_testFree :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          C.normalUpperTailMean
              (J2DropFamily groupA).posteriorMeanScaleLaw
              (J2DropThreshold groupA) =
            fullSubLowTestFreeMerit groupA)
    (honlyB_J2_groupA_eq :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          C.normalUpperTailMean
              (J2KeepFamily groupA).posteriorMeanScaleLaw
              (J2KeepThreshold groupA) =
            C.normalUpperTailMean
              (J2DropFamily groupA).posteriorMeanScaleLaw
              (J2DropThreshold groupA))
    (honlyB_J2_groupB_testBased :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          C.normalUpperTailMean
              (J2KeepFamily groupB).posteriorMeanScaleLaw
              (J2KeepThreshold groupB) =
            fullSubLowTestBasedMerit groupB (testCost groupB))
    (honlyB_J2_groupB_testFree :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          C.normalUpperTailMean
              (J2DropFamily groupB).posteriorMeanScaleLaw
              (J2DropThreshold groupB) =
            fullSubLowTestFreeMerit groupB) :
    let S :=
      glm20Theorem3SourceFamilyPolicyStateTableSurface api
        subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold
    (q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          ((glm20TwoGroupWeightedAcademicMeritObjective S
              glm20StrategicPolicyStatePair J1 groupA groupB
              populationShare GLM20StrategicPolicyState.singleFull
              GLM20StrategicPolicyState.singleFull ≤
            glm20TwoGroupWeightedAcademicMeritObjective S
              glm20StrategicPolicyStatePair J1 groupA groupB
              populationShare GLM20StrategicPolicyState.singleSub
              GLM20StrategicPolicyState.singleFull) ↔
            subFullTestBasedMerit groupA (testCost groupA) ≤
              subFullTestFreeMerit groupA)) ∧
      (q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          ((glm20TwoGroupWeightedAcademicMeritObjective S
              glm20StrategicPolicyStatePair J1 groupA groupB
              populationShare GLM20StrategicPolicyState.singleFull
              GLM20StrategicPolicyState.singleFull ≤
            glm20TwoGroupWeightedAcademicMeritObjective S
              glm20StrategicPolicyStatePair J1 groupA groupB
              populationShare GLM20StrategicPolicyState.singleSub
              GLM20StrategicPolicyState.singleFull) ↔
            subFullTestBasedMerit groupB (testCost groupB) ≤
              subFullTestFreeMerit groupB)) ∧
      (q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          ((glm20TwoGroupWeightedAcademicMeritObjective S
              glm20StrategicPolicyStatePair J2 groupA groupB
              populationShare GLM20StrategicPolicyState.singleFull
              GLM20StrategicPolicyState.singleFull ≤
            glm20TwoGroupWeightedAcademicMeritObjective S
              glm20StrategicPolicyStatePair J2 groupA groupB
              populationShare GLM20StrategicPolicyState.singleFull
              GLM20StrategicPolicyState.singleSub) ↔
            fullSubLowTestBasedMerit groupA (testCost groupA) ≤
              fullSubLowTestFreeMerit groupA)) ∧
        (q2Sub < fullFullCutoff groupB →
          ¬ q2Sub < fullFullCutoff groupA →
            ((glm20TwoGroupWeightedAcademicMeritObjective S
                glm20StrategicPolicyStatePair J2 groupA groupB
                populationShare GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull ≤
              glm20TwoGroupWeightedAcademicMeritObjective S
                glm20StrategicPolicyStatePair J2 groupA groupB
                populationShare GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub) ↔
              fullSubLowTestBasedMerit groupB (testCost groupB) ≤
                fullSubLowTestFreeMerit groupB)) := by
  dsimp only
  refine
    paper_proposition5_exactly_one_weighted_objective_iff_of_group_merit_formulas
      (S :=
        glm20Theorem3SourceFamilyPolicyStateTableSurface api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold)
      (policyPair := glm20StrategicPolicyStatePair)
      (Psub := GLM20StrategicPolicyState.singleSub)
      (Pfull := GLM20StrategicPolicyState.singleFull)
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff) subFullTestBasedMerit
      subFullTestFreeMerit fullSubLowTestBasedMerit
      fullSubLowTestFreeMerit hshareA hshareB ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_
  · intro hA hB
    simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit,
      glm20Theorem3SourceFamilySubFullMeritTable,
      glm20Theorem3SourceFamilyFullFullMeritTable,
      glm20OverrideSchoolMeritRow, hJ1_ne_J2] using
      honlyA_J1_groupB_eq hA hB
  · intro hA hB
    simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit,
      glm20Theorem3SourceFamilyFullFullMeritTable,
      glm20OverrideSchoolMeritRow, hJ1_ne_J2] using
      honlyA_J1_groupA_testBased hA hB
  · intro hA hB
    simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit,
      glm20Theorem3SourceFamilySubFullMeritTable,
      glm20OverrideSchoolMeritRow] using
      honlyA_J1_groupA_testFree hA hB
  · intro hB hA
    simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit,
      glm20Theorem3SourceFamilySubFullMeritTable,
      glm20Theorem3SourceFamilyFullFullMeritTable,
      glm20OverrideSchoolMeritRow, hJ1_ne_J2] using
      honlyB_J1_groupA_eq hB hA
  · intro hB hA
    simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit,
      glm20Theorem3SourceFamilyFullFullMeritTable,
      glm20OverrideSchoolMeritRow, hJ1_ne_J2] using
      honlyB_J1_groupB_testBased hB hA
  · intro hB hA
    simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit,
      glm20Theorem3SourceFamilySubFullMeritTable,
      glm20OverrideSchoolMeritRow] using
      honlyB_J1_groupB_testFree hB hA
  · intro hA hB
    simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit,
      glm20Theorem3SourceFamilyFullSubMeritTable,
      glm20Theorem3SourceFamilyFullFullMeritTable,
      glm20OverrideSchoolMeritRow] using
      honlyA_J2_groupB_eq hA hB
  · intro hA hB
    simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit,
      glm20Theorem3SourceFamilyFullFullMeritTable,
      glm20OverrideSchoolMeritRow] using
      honlyA_J2_groupA_testBased hA hB
  · intro hA hB
    simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit,
      glm20Theorem3SourceFamilyFullSubMeritTable,
      glm20OverrideSchoolMeritRow] using
      honlyA_J2_groupA_testFree hA hB
  · intro hB hA
    simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit,
      glm20Theorem3SourceFamilyFullSubMeritTable,
      glm20Theorem3SourceFamilyFullFullMeritTable,
      glm20OverrideSchoolMeritRow] using
      honlyB_J2_groupA_eq hB hA
  · intro hB hA
    simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit,
      glm20Theorem3SourceFamilyFullFullMeritTable,
      glm20OverrideSchoolMeritRow] using
      honlyB_J2_groupB_testBased hB hA
  · intro hB hA
    simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20StrategicPolicyStateAdmittedMerit,
      glm20Theorem3SourceFamilyFullSubMeritTable,
      glm20OverrideSchoolMeritRow] using
      honlyB_J2_groupB_testFree hB hA

/--
Packaged version of
`paper_proposition5_exactly_one_weighted_objective_iff_of_source_family_policy_state_table_rows`.

Use this when the Bayesian-game layer has produced the twelve source-family
row identifications as a single certificate.
-/
abbrev
    paper_proposition5_exactly_one_weighted_objective_iff_of_source_family_policy_state_table_row_package
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
    {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost : Group → ℝ}
    {q1Sub q2Sub : ℝ} {fullFullCutoff fullSubCutoff : Group → ℝ}
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2)
    (subFullTestBasedMerit : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (fullSubLowTestBasedMerit : Group → ℝ → ℝ)
    (fullSubLowTestFreeMerit : Group → ℝ)
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
    (hrows :
      GLM20Proposition5ExactlyOneObjectiveSourceFamilyRows testCost
        q1Sub q2Sub fullFullCutoff C J1DropFamily J2DropFamily
        J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
        J2DropThreshold J2KeepThreshold subFullTestBasedMerit
        subFullTestFreeMerit fullSubLowTestBasedMerit
        fullSubLowTestFreeMerit groupA groupB) :=
  paper_proposition5_exactly_one_weighted_objective_iff_of_source_family_policy_state_table_rows
    (api := api) (subEstimateLaw := subEstimateLaw)
    (subSubMass := subSubMass) (subFullMass := subFullMass)
    (subSubMerit := subSubMerit)
    (subFullMeritFallback := subFullMeritFallback)
    (fullSubMeritFallback := fullSubMeritFallback)
    (fullFullMeritFallback := fullFullMeritFallback)
    (diversity := diversity) (J1 := J1) (J2 := J2)
    (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (q1Sub := q1Sub) (q2Sub := q2Sub)
    (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
    (C := C) (J1DropFamily := J1DropFamily)
    (J2DropFamily := J2DropFamily) (J1KeepFamily := J1KeepFamily)
    (J2KeepFamily := J2KeepFamily)
    (J1DropThreshold := J1DropThreshold)
    (J1KeepThreshold := J1KeepThreshold)
    (J2DropThreshold := J2DropThreshold)
    (J2KeepThreshold := J2KeepThreshold)
    (hJ1_ne_J2 := hJ1_ne_J2)
    (subFullTestBasedMerit := subFullTestBasedMerit)
    (subFullTestFreeMerit := subFullTestFreeMerit)
    (fullSubLowTestBasedMerit := fullSubLowTestBasedMerit)
    (fullSubLowTestFreeMerit := fullSubLowTestFreeMerit)
    (hshareA := hshareA) (hshareB := hshareB)
    (honlyA_J1_groupB_eq := hrows.honlyA_J1_groupB_eq)
    (honlyA_J1_groupA_testBased := hrows.honlyA_J1_groupA_testBased)
    (honlyA_J1_groupA_testFree := hrows.honlyA_J1_groupA_testFree)
    (honlyB_J1_groupA_eq := hrows.honlyB_J1_groupA_eq)
    (honlyB_J1_groupB_testBased := hrows.honlyB_J1_groupB_testBased)
    (honlyB_J1_groupB_testFree := hrows.honlyB_J1_groupB_testFree)
    (honlyA_J2_groupB_eq := hrows.honlyA_J2_groupB_eq)
    (honlyA_J2_groupA_testBased := hrows.honlyA_J2_groupA_testBased)
    (honlyA_J2_groupA_testFree := hrows.honlyA_J2_groupA_testFree)
    (honlyB_J2_groupA_eq := hrows.honlyB_J2_groupA_eq)
    (honlyB_J2_groupB_testBased := hrows.honlyB_J2_groupB_testBased)
    (honlyB_J2_groupB_testFree := hrows.honlyB_J2_groupB_testFree)

end

end GLM20DroppingStandardizedTesting
