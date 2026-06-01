import GLM20DroppingStandardizedTesting.PaperSurfaceWrappers

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Proposition 5(ii) / Theorem 3(ii) selected equation-(46) objective bridge
with the full-sub test-free merit rows generated directly from posterior-mean
source families.

This is the source-free version of
`paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_scale_families`:
callers no longer pass the `lowTestFreeMerit` and `highTestFreeMerit`
functions or their formula proofs.  The cost-indexed test-based formulas and
all objective, mass, capacity, and no-expansion premises remain explicit.
-/
abbrev
    paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_source_free_families
    {Group Policy School Equilibrium LowFreeFeature HighFreeFeature
      LowBasedFeature HighBasedFeature : Type*}
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {S : GLM20StrategicPolicySurface Group Policy School Equilibrium}
    {policyPair : Policy → Policy → Policy}
    {Psub Pfull : Policy} {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost leftCost rightCost : Group → ℝ}
    {capacity2 q1Sub q2Sub : ℝ}
    (subEstimateLaw : Group → GaussianScaleLaw)
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    {lowQ1Full lowQ2Full lowScale lowV1 lowV2 : Group → ℝ}
    {highQ1Full highQ2Full highScale highV1 highV2 : Group → ℝ}
    (lowCutoffOfCost highCutoffOfCost : Group → ℝ → ℝ)
    (lowMeritOfCutoff highMeritOfCutoff : Group → ℝ → ℝ)
    (C : GaussianHazardCertificate)
    (lowFreeFamily : Group → GaussianOffsetSignalFamily LowFreeFeature)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (lowBasedThreshold highBasedThreshold : Group → ℝ → ℝ)
    (hleft_right : ∀ g, leftCost g < rightCost g)
    (hleft_pos : ∀ g, 0 < leftCost g)
    (hcostMem :
      ∀ g, testCost g ∈ Set.Icc (leftCost g) (rightCost g))
    (hlowScale : ∀ g, 0 < lowScale g)
    (hlowV2Pos : ∀ g, 0 < lowV2 g)
    (hlowV2LtV1 : ∀ g, lowV2 g < lowV1 g)
    (hlowZero :
      ∀ g cost, cost ∈ Set.Icc (leftCost g) (rightCost g) →
        glm20StrategicTwoFullPolicyApplyPayoffValue standardGaussianCDFAPI
          (lowQ1Full g) (lowQ2Full g) (lowScale g) (lowV1 g)
          (lowV2 g) cost (lowCutoffOfCost g cost) = 0)
    (hlowMeritCont : ∀ g, Continuous (lowMeritOfCutoff g))
    (hlowMeritAnti : ∀ g, StrictAnti (lowMeritOfCutoff g))
    (hhighScale : ∀ g, 0 < highScale g)
    (hhighV2Pos : ∀ g, 0 < highV2 g)
    (hhighV2LtV1 : ∀ g, highV2 g < highV1 g)
    (hhighZero :
      ∀ g cost, cost ∈ Set.Icc (leftCost g) (rightCost g) →
        glm20StrategicTwoFullPolicyApplyPayoffValue standardGaussianCDFAPI
          (highQ1Full g) (highQ2Full g) (highScale g) (highV1 g)
          (highV2 g) cost (highCutoffOfCost g cost) = 0)
    (hhighMeritCont : ∀ g, Continuous (highMeritOfCutoff g))
    (hhighMeritAnti : ∀ g, StrictAnti (highMeritOfCutoff g))
    (hlowAtLeft :
      ∀ g,
        C.normalUpperTailMean
            (lowFreeFamily g).posteriorMeanScaleLaw
            (lowFreeThreshold g) <
          lowMeritOfCutoff g (lowCutoffOfCost g (leftCost g)))
    (hlowAtRight :
      ∀ g,
        lowMeritOfCutoff g (lowCutoffOfCost g (rightCost g)) <
          C.normalUpperTailMean
            (lowFreeFamily g).posteriorMeanScaleLaw
            (lowFreeThreshold g))
    (hhighAtLeft :
      ∀ g,
        C.normalUpperTailMean
            (highFreeFamily g).posteriorMeanScaleLaw
            (highFreeThreshold g) <
          highMeritOfCutoff g (highCutoffOfCost g (leftCost g)))
    (hhighAtRight :
      ∀ g,
        highMeritOfCutoff g (highCutoffOfCost g (rightCost g)) <
          C.normalUpperTailMean
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
    (hlowBasedFormula :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        lowMeritOfCutoff g (lowCutoffOfCost g c) =
          C.normalUpperTailMean
            (lowBasedFamily g c).posteriorMeanScaleLaw
            (lowBasedThreshold g c))
    (hhighBasedFormula :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        highMeritOfCutoff g (highCutoffOfCost g c) =
          C.normalUpperTailMean
            (highBasedFamily g c).posteriorMeanScaleLaw
            (highBasedThreshold g c))
    (hbasedPriorMean :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        (lowBasedFamily g c).priorMean = (highBasedFamily g c).priorMean)
    (hbasedPriorVar :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        (lowBasedFamily g c).priorVar = (highBasedFamily g c).priorVar)
    (hbasedPrecision :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        (lowBasedFamily g c).centeredFamily.signalPrecisionSum <
          (highBasedFamily g c).centeredFamily.signalPrecisionSum)
    (hbasedThresholdMean :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        (lowBasedFamily g c).priorMean < lowBasedThreshold g c)
    (hbasedThreshold :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
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
            lowMeritOfCutoff groupA
              (lowCutoffOfCost groupA (testCost groupA)))
    (honlyA_J2_groupA_testFree :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J2 groupA (policyPair Pfull Psub) =
            C.normalUpperTailMean
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
            lowMeritOfCutoff groupB
              (lowCutoffOfCost groupB (testCost groupB)))
    (honlyB_J2_groupB_testFree :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          S.admittedAcademicMerit J2 groupB (policyPair Pfull Psub) =
            C.normalUpperTailMean
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
          C.normalUpperTailMean
            (highFreeFamily groupA).posteriorMeanScaleLaw
            (highFreeThreshold groupA))
    (hexpandA_J1_groupA_testBased :
      ¬ fullSubCutoff groupA < q1Sub →
        S.admittedAcademicMerit J1 groupA (policyPair Pfull Psub) =
          highMeritOfCutoff groupA
            (highCutoffOfCost groupA (testCost groupA)))
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
          C.normalUpperTailMean
            (highFreeFamily groupB).posteriorMeanScaleLaw
            (highFreeThreshold groupB))
    (hexpandB_J1_groupB_testBased :
      ¬ fullSubCutoff groupB < q1Sub →
        S.admittedAcademicMerit J1 groupB (policyPair Pfull Psub) =
          highMeritOfCutoff groupB
            (highCutoffOfCost groupB (testCost groupB))) :=
  let lowTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean (lowFreeFamily g).posteriorMeanScaleLaw
      (lowFreeThreshold g)
  let highTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean (highFreeFamily g).posteriorMeanScaleLaw
      (highFreeThreshold g)
  paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_scale_families
    (S := S) (policyPair := policyPair) (Psub := Psub)
    (Pfull := Pfull) (J1 := J1) (J2 := J2) (groupA := groupA)
    (groupB := groupB) (populationShare := populationShare)
    (testCost := testCost) (leftCost := leftCost) (rightCost := rightCost)
    (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
    subEstimateLaw (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff) (lowQ1Full := lowQ1Full)
    (lowQ2Full := lowQ2Full) (lowScale := lowScale) (lowV1 := lowV1)
    (lowV2 := lowV2) (highQ1Full := highQ1Full)
    (highQ2Full := highQ2Full) (highScale := highScale)
    (highV1 := highV1) (highV2 := highV2) lowCutoffOfCost
    highCutoffOfCost lowMeritOfCutoff lowTestFreeMerit
    highMeritOfCutoff highTestFreeMerit C lowFreeFamily highFreeFamily
    lowFreeThreshold highFreeThreshold lowBasedFamily highBasedFamily
    lowBasedThreshold highBasedThreshold hleft_right hleft_pos hcostMem
    hlowScale hlowV2Pos hlowV2LtV1 hlowZero hlowMeritCont
    hlowMeritAnti hhighScale hhighV2Pos hhighV2LtV1 hhighZero
    hhighMeritCont hhighMeritAnti hlowAtLeft hlowAtRight hhighAtLeft
    hhighAtRight (by intro g; rfl) (by intro g; rfl)
    hfreePriorMean hfreePriorVar hfreePrecision hfreeThresholdMean
    hfreeThreshold hlowBasedFormula hhighBasedFormula hbasedPriorMean
    hbasedPriorVar hbasedPrecision hbasedThresholdMean hbasedThreshold
    hshareA hshareB hmassFullFullA hmassFullFullB hmassFullSubA
    hmassFullSubB hcapacity2 hfillFullFull2 hfixedPoolMeritA
    hfixedPoolMeritB honlyA_J2_groupB_eq honlyA_J2_groupA_testBased
    honlyA_J2_groupA_testFree honlyB_J2_groupA_eq
    honlyB_J2_groupB_testBased honlyB_J2_groupB_testFree hnoExpandA
    hexpandA_J1_groupB_eq hexpandA_J1_groupA_testFree
    hexpandA_J1_groupA_testBased hnoExpandB hexpandB_J1_groupA_eq
    hexpandB_J1_groupB_testFree hexpandB_J1_groupB_testBased

end

end GLM20DroppingStandardizedTesting
