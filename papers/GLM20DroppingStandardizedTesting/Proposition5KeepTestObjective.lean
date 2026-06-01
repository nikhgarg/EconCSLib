import GLM20DroppingStandardizedTesting.PaperSurfaceWrappers

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Proposition 5(i) / Theorem 3(i) source-family bridge with school-`J2`
condition-(11)--(12) exposed as named keep-test predicates.

This is the keep-test-predicate version of
`paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_raw_survivor_conditions`.
-/
abbrev
    paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_keeps_test
    (Q : StandardGaussianQuantileAPI) (C : GaussianHazardCertificate)
    {Group Policy School Equilibrium FeatureDrop FeatureKeep : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    {S : GLM20StrategicPolicySurface Group Policy School Equilibrium}
    {policyPair : Policy → Policy → Policy}
    {Psub Pfull : Policy} {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost leftCost rightCost q2Full scale v2 :
      Group → ℝ}
    {capacity1 capacity2 q1Sub : ℝ}
    (subEstimateLaw : Group → GaussianScaleLaw)
    {fullFullCutoff : Group → ℝ}
    (objective2 : Policy → Policy → ℝ)
    (meritOfCutoff : Group → ℝ → ℝ) (testFreeMerit : Group → ℝ)
    (J1DropFamily : Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily : Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold : Group → ℝ)
    (hleftRight : ∀ g, leftCost g < rightCost g)
    (hscale : ∀ g, 0 < scale g)
    (hleftPos : ∀ g, 0 < leftCost g)
    (hrightLtV2 : ∀ g, rightCost g < v2 g)
    (hcostMem :
      ∀ g, testCost g ∈ Set.Icc (leftCost g) (rightCost g))
    (hmerit_cont : ∀ g, Continuous (meritOfCutoff g))
    (hmerit_anti : ∀ g, StrictAnti (meritOfCutoff g))
    (hlowCost :
      ∀ g,
        testFreeMerit g <
          meritOfCutoff g
            (q2Full g - scale g * Q.quantile (1 - leftCost g / v2 g)))
    (hhighCost :
      ∀ g,
        meritOfCutoff g
            (q2Full g -
              scale g * Q.quantile (1 - rightCost g / v2 g)) <
          testFreeMerit g)
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
    (hmassFullFullA :
      S.massTestTaking groupA (policyPair Pfull Pfull) =
        glm20StrategicSubEstimateMassAbove Q.cdfAPI
          (subEstimateLaw groupA) (fullFullCutoff groupA))
    (hmassFullFullB :
      S.massTestTaking groupB (policyPair Pfull Pfull) =
        glm20StrategicSubEstimateMassAbove Q.cdfAPI
          (subEstimateLaw groupB) (fullFullCutoff groupB))
    (hcapacity1 :
      capacity1 =
        populationShare groupA *
            glm20StrategicSubEstimateMassAbove Q.cdfAPI
              (subEstimateLaw groupA) q1Sub +
          populationShare groupB *
            glm20StrategicSubEstimateMassAbove Q.cdfAPI
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
              C.normalUpperTailMean
                (J1DropFamily g).posteriorMeanScaleLaw
                (J1DropThreshold g))
    (hJ1KeepMerit :
      ∀ g,
        ¬ q1Sub < fullFullCutoff groupA →
          ¬ q1Sub < fullFullCutoff groupB →
            S.admittedAcademicMerit J1 g (policyPair Pfull Pfull) =
              C.normalUpperTailMean
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
            meritOfCutoff groupA
              (q2Full groupA -
                scale groupA *
                  Q.quantile (1 - testCost groupA / v2 groupA)))
    (honlyA_J1_groupA_testFree :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J1 groupA (policyPair Psub Pfull) =
            testFreeMerit groupA)
    (honlyB_J1_groupA_eq :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J1 groupA (policyPair Pfull Pfull) =
            S.admittedAcademicMerit J1 groupA (policyPair Psub Pfull))
    (honlyB_J1_groupB_testBased :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J1 groupB (policyPair Pfull Pfull) =
            meritOfCutoff groupB
              (q2Full groupB -
                scale groupB *
                  Q.quantile (1 - testCost groupB / v2 groupB)))
    (honlyB_J1_groupB_testFree :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J1 groupB (policyPair Psub Pfull) =
            testFreeMerit groupB)
    (hJ2ObjectiveSubSub :
      objective2 Psub Psub =
        populationShare groupA *
            S.admittedAcademicMerit J2 groupA (policyPair Psub Psub) +
          populationShare groupB *
            S.admittedAcademicMerit J2 groupB (policyPair Psub Psub))
    (hJ2ObjectiveSubFullB :
      objective2 Psub Pfull =
        populationShare groupB *
          S.admittedAcademicMerit J2 groupB (policyPair Psub Pfull))
    (hJ2KeepsB :
      glm20Theorem3SubFullOtherGroupKeepsTest S policyPair Psub Pfull J2
        groupA groupB populationShare capacity2 groupB)
    (hJ2ObjectiveSubFullA :
      objective2 Psub Pfull =
        populationShare groupA *
          S.admittedAcademicMerit J2 groupA (policyPair Psub Pfull))
    (hJ2KeepsA :
      glm20Theorem3SubFullOtherGroupKeepsTest S policyPair Psub Pfull J2
        groupA groupB populationShare capacity2 groupA) :=
  paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_raw_survivor_conditions
    (Q := Q) (C := C) (S := S) (policyPair := policyPair)
    (Psub := Psub) (Pfull := Pfull) (J1 := J1) (J2 := J2)
    (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (leftCost := leftCost) (rightCost := rightCost) (q2Full := q2Full)
    (scale := scale) (v2 := v2) (capacity1 := capacity1)
    (capacity2 := capacity2) (q1Sub := q1Sub) subEstimateLaw
    (fullFullCutoff := fullFullCutoff) objective2 meritOfCutoff
    testFreeMerit J1DropFamily J1KeepFamily J1DropThreshold
    J1KeepThreshold hleftRight hscale hleftPos hrightLtV2 hcostMem
    hmerit_cont hmerit_anti hlowCost hhighCost hshareA hshareB
    hmassFullFullA hmassFullFullB hcapacity1 hfillFullFull1
    hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean hJ1Threshold
    hJ1DropMerit hJ1KeepMerit honlyA_J1_groupB_eq
    honlyA_J1_groupA_testBased honlyA_J1_groupA_testFree
    honlyB_J1_groupA_eq honlyB_J1_groupB_testBased
    honlyB_J1_groupB_testFree hJ2ObjectiveSubSub hJ2ObjectiveSubFullB
    hJ2KeepsB.1 hJ2KeepsB.2 hJ2ObjectiveSubFullA hJ2KeepsA.1
    hJ2KeepsA.2

/--
Standard-Gaussian Proposition 5(i) keep-test bridge.

This fixes the quantile API and Gaussian hazard certificate in
`paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_keeps_test`,
leaving the visible surface as the policy/objective data plus the named
school-`J2` keep-test predicates.
-/
abbrev
    paper_proposition5_standardGaussian_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_keeps_test
    {Group Policy School Equilibrium FeatureDrop FeatureKeep : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    {S : GLM20StrategicPolicySurface Group Policy School Equilibrium}
    {policyPair : Policy → Policy → Policy}
    {Psub Pfull : Policy} {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost leftCost rightCost q2Full scale v2 :
      Group → ℝ}
    {capacity1 capacity2 q1Sub : ℝ}
    {fullFullCutoff : Group → ℝ} :=
  paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_j2_keeps_test
    standardGaussianQuantileAPI
    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
    (Group := Group) (Policy := Policy) (School := School)
    (Equilibrium := Equilibrium) (FeatureDrop := FeatureDrop)
    (FeatureKeep := FeatureKeep) (S := S) (policyPair := policyPair)
    (Psub := Psub) (Pfull := Pfull) (J1 := J1) (J2 := J2)
    (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (leftCost := leftCost) (rightCost := rightCost)
    (q2Full := q2Full) (scale := scale) (v2 := v2)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (fullFullCutoff := fullFullCutoff)

end

end GLM20DroppingStandardizedTesting
