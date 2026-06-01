import GLM20DroppingStandardizedTesting.Proposition5SourceFreeObjective

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Proposition 5(ii) source-family ordered-merit bridge with both the test-free
and cost-indexed test-based full-sub rows generated directly from posterior
mean source families.

Compared with
`paper_proposition5_fullSub_ordered_merits_of_posterior_mean_source_free_families`,
callers no longer pass the cost-indexed low/high test-based merit functions or
their formula rows.  The low/high based rows are definitional Gaussian
upper-tail means from the source families.
-/
abbrev
    paper_proposition5_fullSub_ordered_merits_of_posterior_mean_source_free_cost_rows
    (C : GaussianHazardCertificate)
    {Group LowFreeFeature HighFreeFeature LowBasedFeature
      HighBasedFeature : Type*}
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {leftCost rightCost : Group → ℝ}
    (lowFreeFamily : Group → GaussianOffsetSignalFamily LowFreeFeature)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (lowBasedThreshold highBasedThreshold : Group → ℝ → ℝ)
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
        lowBasedThreshold g c ≤ highBasedThreshold g c) :=
  let lowTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    C.normalUpperTailMean (lowBasedFamily g c).posteriorMeanScaleLaw
      (lowBasedThreshold g c)
  let highTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    C.normalUpperTailMean (highBasedFamily g c).posteriorMeanScaleLaw
      (highBasedThreshold g c)
  paper_proposition5_fullSub_ordered_merits_of_posterior_mean_source_free_families
    C (leftCost := leftCost) (rightCost := rightCost)
    lowTestBasedMerit highTestBasedMerit lowFreeFamily highFreeFamily
    lowFreeThreshold highFreeThreshold lowBasedFamily highBasedFamily
    lowBasedThreshold highBasedThreshold hfreePriorMean hfreePriorVar
    hfreePrecision hfreeThresholdMean hfreeThreshold
    (by intro g c hc; rfl) (by intro g c hc; rfl)
    hbasedPriorMean hbasedPriorVar hbasedPrecision hbasedThresholdMean
    hbasedThreshold

/--
Standard-Gaussian specialization of the Proposition 5(ii) posterior cost-row
ordered-merit bridge.
-/
abbrev
    paper_proposition5_standardGaussian_fullSub_ordered_merits_of_posterior_mean_source_free_cost_rows
    {Group LowFreeFeature HighFreeFeature LowBasedFeature
      HighBasedFeature : Type*}
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {leftCost rightCost : Group → ℝ} :=
  paper_proposition5_fullSub_ordered_merits_of_posterior_mean_source_free_cost_rows
    (Group := Group) (LowFreeFeature := LowFreeFeature)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (HighBasedFeature := HighBasedFeature)
    (leftCost := leftCost) (rightCost := rightCost)
    (C := standardGaussianHazardInverseCertificate.toGaussianHazardCertificate)

/--
Proposition 5(ii) source-family high-at-low-root support with all full-sub
posterior rows generated directly from source families.

The returned root-side premise is the same one used by the selected
equation-(46) full-sub objective bridge, but the low/high test-free and
cost-indexed based merit rows are all definitional posterior upper-tail means.
-/
abbrev
    paper_proposition5_high_merit_at_low_root_of_posterior_mean_source_free_cost_rows
    (C : GaussianHazardCertificate)
    {Group LowFreeFeature HighFreeFeature LowBasedFeature
      HighBasedFeature : Type*}
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {leftCost rightCost : Group → ℝ}
    (lowFreeFamily : Group → GaussianOffsetSignalFamily LowFreeFeature)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (lowBasedThreshold highBasedThreshold : Group → ℝ → ℝ)
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
        lowBasedThreshold g c ≤ highBasedThreshold g c) :=
  let lowTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    C.normalUpperTailMean (lowBasedFamily g c).posteriorMeanScaleLaw
      (lowBasedThreshold g c)
  let highTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    C.normalUpperTailMean (highBasedFamily g c).posteriorMeanScaleLaw
      (highBasedThreshold g c)
  paper_proposition5_high_merit_at_low_root_of_posterior_mean_source_free_families
    C (leftCost := leftCost) (rightCost := rightCost)
    lowTestBasedMerit highTestBasedMerit lowFreeFamily highFreeFamily
    lowFreeThreshold highFreeThreshold lowBasedFamily highBasedFamily
    lowBasedThreshold highBasedThreshold hfreePriorMean hfreePriorVar
    hfreePrecision hfreeThresholdMean hfreeThreshold
    (by intro g c hc; rfl) (by intro g c hc; rfl)
    hbasedPriorMean hbasedPriorVar hbasedPrecision hbasedThresholdMean
    hbasedThreshold

/--
Standard-Gaussian specialization of the Proposition 5(ii) posterior cost-row
high-at-low-root bridge.
-/
abbrev
    paper_proposition5_standardGaussian_high_merit_at_low_root_of_posterior_mean_source_free_cost_rows
    {Group LowFreeFeature HighFreeFeature LowBasedFeature
      HighBasedFeature : Type*}
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {leftCost rightCost : Group → ℝ} :=
  paper_proposition5_high_merit_at_low_root_of_posterior_mean_source_free_cost_rows
    (Group := Group) (LowFreeFeature := LowFreeFeature)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (HighBasedFeature := HighBasedFeature)
    (leftCost := leftCost) (rightCost := rightCost)
    (C := standardGaussianHazardInverseCertificate.toGaussianHazardCertificate)

/--
Proposition 5(ii) / Theorem 3(ii) interval objective bridge with the full-sub
low/high posterior rows generated directly from source families.

This is the posterior-row analogue of
`paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas`.
It keeps the interval continuity/crossing and strategic branch assumptions,
but states them against the source-family posterior upper-tail rows rather
than against caller-supplied merit functions plus separate formula
identifications.
-/
theorem
    paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_source_free_cost_rows
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
    (api : StandardGaussianCDFAPI) (subEstimateLaw : Group → GaussianScaleLaw)
    {fullFullCutoff fullSubCutoff : Group → ℝ}
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
    (hlowCont :
      ∀ g,
        ContinuousOn
          (fun c =>
            C.normalUpperTailMean (lowBasedFamily g c).posteriorMeanScaleLaw
              (lowBasedThreshold g c))
          (Set.Icc (leftCost g) (rightCost g)))
    (hlowAnti :
      ∀ g,
        StrictAntiOn
          (fun c =>
            C.normalUpperTailMean (lowBasedFamily g c).posteriorMeanScaleLaw
              (lowBasedThreshold g c))
          (Set.Icc (leftCost g) (rightCost g)))
    (hlowAtLeft :
      ∀ g,
        C.normalUpperTailMean (lowFreeFamily g).posteriorMeanScaleLaw
            (lowFreeThreshold g) <
          C.normalUpperTailMean
            (lowBasedFamily g (leftCost g)).posteriorMeanScaleLaw
            (lowBasedThreshold g (leftCost g)))
    (hlowAtRight :
      ∀ g,
        C.normalUpperTailMean
            (lowBasedFamily g (rightCost g)).posteriorMeanScaleLaw
            (lowBasedThreshold g (rightCost g)) <
          C.normalUpperTailMean (lowFreeFamily g).posteriorMeanScaleLaw
            (lowFreeThreshold g))
    (hhighCont :
      ∀ g,
        ContinuousOn
          (fun c =>
            C.normalUpperTailMean
              (highBasedFamily g c).posteriorMeanScaleLaw
              (highBasedThreshold g c))
          (Set.Icc (leftCost g) (rightCost g)))
    (hhighAnti :
      ∀ g,
        StrictAntiOn
          (fun c =>
            C.normalUpperTailMean
              (highBasedFamily g c).posteriorMeanScaleLaw
              (highBasedThreshold g c))
          (Set.Icc (leftCost g) (rightCost g)))
    (hhighAtLeft :
      ∀ g,
        C.normalUpperTailMean (highFreeFamily g).posteriorMeanScaleLaw
            (highFreeThreshold g) <
          C.normalUpperTailMean
            (highBasedFamily g (leftCost g)).posteriorMeanScaleLaw
            (highBasedThreshold g (leftCost g)))
    (hhighAtRight :
      ∀ g,
        C.normalUpperTailMean
            (highBasedFamily g (rightCost g)).posteriorMeanScaleLaw
            (highBasedThreshold g (rightCost g)) <
          C.normalUpperTailMean (highFreeFamily g).posteriorMeanScaleLaw
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
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
          (fullFullCutoff groupA))
    (hmassFullFullB :
      S.massTestTaking groupB (policyPair Pfull Pfull) =
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
          (fullFullCutoff groupB))
    (hmassFullSubA :
      S.massTestTaking groupA (policyPair Pfull Psub) =
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
          (fullSubCutoff groupA))
    (hmassFullSubB :
      S.massTestTaking groupB (policyPair Pfull Psub) =
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
          (fullSubCutoff groupB))
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
            C.normalUpperTailMean
              (lowBasedFamily groupA (testCost groupA)).posteriorMeanScaleLaw
              (lowBasedThreshold groupA (testCost groupA)))
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
            C.normalUpperTailMean
              (lowBasedFamily groupB (testCost groupB)).posteriorMeanScaleLaw
              (lowBasedThreshold groupB (testCost groupB)))
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
          C.normalUpperTailMean
            (highBasedFamily groupA (testCost groupA)).posteriorMeanScaleLaw
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
          C.normalUpperTailMean
            (highFreeFamily groupB).posteriorMeanScaleLaw
            (highFreeThreshold groupB))
    (hexpandB_J1_groupB_testBased :
      ¬ fullSubCutoff groupB < q1Sub →
        S.admittedAcademicMerit J1 groupB (policyPair Pfull Psub) =
          C.normalUpperTailMean
            (highBasedFamily groupB (testCost groupB)).posteriorMeanScaleLaw
            (highBasedThreshold groupB (testCost groupB))) :
    ∃ lowCostThreshold highCostThreshold : Group → ℝ,
      (∀ g, lowCostThreshold g ∈
        Set.Ioo (leftCost g) (rightCost g)) ∧
        (∀ g, highCostThreshold g ∈
          Set.Ioo (leftCost g) (rightCost g)) ∧
          (∀ g,
            C.normalUpperTailMean
                (lowBasedFamily g (lowCostThreshold g)).posteriorMeanScaleLaw
                (lowBasedThreshold g (lowCostThreshold g)) =
              C.normalUpperTailMean
                (lowFreeFamily g).posteriorMeanScaleLaw
                (lowFreeThreshold g)) ∧
            (∀ g,
              C.normalUpperTailMean
                  (highBasedFamily g
                    (highCostThreshold g)).posteriorMeanScaleLaw
                  (highBasedThreshold g (highCostThreshold g)) =
                C.normalUpperTailMean
                  (highFreeFamily g).posteriorMeanScaleLaw
                  (highFreeThreshold g)) ∧
              (∀ g, 0 < lowCostThreshold g) ∧
                (∀ g, lowCostThreshold g < highCostThreshold g) ∧
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
                    groupA groupB testCost lowCostThreshold highCostThreshold
                    q1Sub q2Sub
                    (fun g q =>
                      glm20StrategicSubEstimateMassAbove api
                        (subEstimateLaw g) q)) := by
  let lowTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    C.normalUpperTailMean (lowBasedFamily g c).posteriorMeanScaleLaw
      (lowBasedThreshold g c)
  let lowTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean (lowFreeFamily g).posteriorMeanScaleLaw
      (lowFreeThreshold g)
  let highTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    C.normalUpperTailMean (highBasedFamily g c).posteriorMeanScaleLaw
      (highBasedThreshold g c)
  let highTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean (highFreeFamily g).posteriorMeanScaleLaw
      (highFreeThreshold g)
  have hhighAtLowRoot :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        lowTestBasedMerit g c = lowTestFreeMerit g →
          highTestFreeMerit g < highTestBasedMerit g c :=
    paper_proposition5_high_merit_at_low_root_of_posterior_mean_source_free_cost_rows
      C (leftCost := leftCost) (rightCost := rightCost) lowFreeFamily
      highFreeFamily lowFreeThreshold highFreeThreshold lowBasedFamily
      highBasedFamily lowBasedThreshold highBasedThreshold hfreePriorMean
      hfreePriorVar hfreePrecision hfreeThresholdMean hfreeThreshold
      hbasedPriorMean hbasedPriorVar hbasedPrecision hbasedThresholdMean
      hbasedThreshold
  simpa [lowTestBasedMerit, lowTestFreeMerit, highTestBasedMerit,
    highTestFreeMerit] using
    (paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas
      (S := S) (policyPair := policyPair) (Psub := Psub)
      (Pfull := Pfull) (J1 := J1) (J2 := J2) (groupA := groupA)
      (groupB := groupB) (populationShare := populationShare)
      (testCost := testCost) (leftCost := leftCost)
      (rightCost := rightCost) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub) api subEstimateLaw
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) lowTestBasedMerit
      lowTestFreeMerit highTestBasedMerit highTestFreeMerit hleft_right
      hleft_pos hcostMem hlowCont hlowAnti hlowAtLeft hlowAtRight
      hhighCont hhighAnti hhighAtLeft hhighAtRight hhighAtLowRoot
      hshareA hshareB hmassFullFullA hmassFullFullB hmassFullSubA
      hmassFullSubB hcapacity2 hfillFullFull2 hfixedPoolMeritA
      hfixedPoolMeritB honlyA_J2_groupB_eq
      honlyA_J2_groupA_testBased honlyA_J2_groupA_testFree
      honlyB_J2_groupA_eq honlyB_J2_groupB_testBased
      honlyB_J2_groupB_testFree hnoExpandA hexpandA_J1_groupB_eq
      hexpandA_J1_groupA_testFree hexpandA_J1_groupA_testBased hnoExpandB
      hexpandB_J1_groupA_eq hexpandB_J1_groupB_testFree
      hexpandB_J1_groupB_testBased)

/--
Standard-Gaussian specialization of the posterior cost-row Proposition 5(ii)
objective bridge.

This is the same source-family cost-row route as
`paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_source_free_cost_rows`,
but the internal standard-Gaussian CDF API and hazard certificate are fixed
for the paper-facing surface.
-/
abbrev
    paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_source_free_cost_rows
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
    {fullFullCutoff fullSubCutoff : Group → ℝ} :=
  paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_source_free_cost_rows
    (Group := Group) (Policy := Policy) (School := School)
    (Equilibrium := Equilibrium) (LowFreeFeature := LowFreeFeature)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (HighBasedFeature := HighBasedFeature) (S := S)
    (policyPair := policyPair) (Psub := Psub) (Pfull := Pfull)
    (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (leftCost := leftCost) (rightCost := rightCost)
    (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
    (api := standardGaussianCDFAPI)
    (C := standardGaussianHazardInverseCertificate.toGaussianHazardCertificate)

end

end GLM20DroppingStandardizedTesting
