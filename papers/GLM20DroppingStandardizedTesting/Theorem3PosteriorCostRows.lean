import GLM20DroppingStandardizedTesting.Proposition5PosteriorCostRows
import GLM20DroppingStandardizedTesting.Theorem3SimplePremises

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/-- The concrete Gaussian hazard certificate used by the standard-Gaussian wrappers. -/
abbrev standardGaussianHazardCertificate : GaussianHazardCertificate :=
  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate

/--
Standard-Gaussian posterior cost-row regularity for the common fixed-law case.

If the cost-indexed source family has a fixed posterior-mean law and cost only
moves a continuous, strictly antitone admission threshold, then the generated
posterior upper-tail merit row is continuous and strictly antitone in cost.
This is the reusable regularity lemma for the `hfullSubLowCont` /
`hfullSubLowAnti` and high-row analogues in the posterior cost-row Theorem 3
route.
-/
theorem
    paper_standardGaussian_posterior_cost_row_regularity_of_fixed_law_threshold_strictAntiOn
    {Group Feature : Type*}
    [Fintype Feature] [Nonempty Feature]
    {leftCost rightCost : Group → ℝ}
    (basedFamily : Group → ℝ → GaussianOffsetSignalFamily Feature)
    (basedThreshold : Group → ℝ → ℝ)
    (basedLaw : Group → GaussianScaleLaw)
    (hbasedLaw :
      ∀ g c, (basedFamily g c).posteriorMeanScaleLaw = basedLaw g)
    (hthresholdCont :
      ∀ g, ContinuousOn (basedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hthresholdAnti :
      ∀ g, StrictAntiOn (basedThreshold g)
        (Set.Icc (leftCost g) (rightCost g))) :
    (∀ g,
      ContinuousOn
        (fun c =>
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            |>.normalUpperTailMean (basedFamily g c).posteriorMeanScaleLaw
              (basedThreshold g c))
        (Set.Icc (leftCost g) (rightCost g))) ∧
      (∀ g,
        StrictAntiOn
          (fun c =>
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              |>.normalUpperTailMean (basedFamily g c).posteriorMeanScaleLaw
                (basedThreshold g c))
          (Set.Icc (leftCost g) (rightCost g))) := by
  constructor
  · intro g
    let C := standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
    let s := Set.Icc (leftCost g) (rightCost g)
    have hmeanCont :
        ContinuousOn (fun z => C.normalUpperTailMean (basedLaw g) z)
          Set.univ :=
      (paper_standardGaussian_normalUpperTailMean_continuous_threshold
        (basedLaw g)).continuousOn
    have hmap : Set.MapsTo (basedThreshold g) s Set.univ := by
      intro z hz
      trivial
    have hbase :
        ContinuousOn (fun c => C.normalUpperTailMean (basedLaw g)
          (basedThreshold g c)) s :=
      hmeanCont.comp (hthresholdCont g) hmap
    exact hbase.congr (by
      intro c hc
      simp [C, hbasedLaw g c])
  · intro g x hx y hy hxy
    let C := standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
    have hthreshold_lt : basedThreshold g y < basedThreshold g x :=
      hthresholdAnti g hx hy hxy
    simpa [C, hbasedLaw g x, hbasedLaw g y] using
        (paper_proposition8_standardGaussian_normalUpperTailMean_strictMono_threshold
        (basedLaw g) hthreshold_lt)

/--
Paired standard-Gaussian posterior cost-row regularity for the low/high
full-sub rows.

This is the two-row version used by Theorem 3 wrappers: if both cost-indexed
source families keep a fixed posterior-mean law and cost only moves a
continuous, strictly antitone threshold, then both generated posterior
upper-tail merit rows are continuous and strictly antitone in cost.
-/
theorem
    paper_standardGaussian_posterior_low_high_cost_row_regularities_of_fixed_law_threshold_strictAntiOn
    {Group LowFeature HighFeature : Type*}
    [Fintype LowFeature] [Nonempty LowFeature]
    [Fintype HighFeature] [Nonempty HighFeature]
    {leftCost rightCost : Group → ℝ}
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighFeature)
    (lowBasedThreshold highBasedThreshold : Group → ℝ → ℝ)
    (lowBasedLaw highBasedLaw : Group → GaussianScaleLaw)
    (hlowBasedLaw :
      ∀ g c, (lowBasedFamily g c).posteriorMeanScaleLaw =
        lowBasedLaw g)
    (hhighBasedLaw :
      ∀ g c, (highBasedFamily g c).posteriorMeanScaleLaw =
        highBasedLaw g)
    (hlowThresholdCont :
      ∀ g, ContinuousOn (lowBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hlowThresholdAnti :
      ∀ g, StrictAntiOn (lowBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hhighThresholdCont :
      ∀ g, ContinuousOn (highBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hhighThresholdAnti :
      ∀ g, StrictAntiOn (highBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g))) :
    (∀ g,
      ContinuousOn
        (fun c =>
          standardGaussianHazardCertificate.normalUpperTailMean
            (lowBasedFamily g c).posteriorMeanScaleLaw
            (lowBasedThreshold g c))
        (Set.Icc (leftCost g) (rightCost g))) ∧
      (∀ g,
        StrictAntiOn
          (fun c =>
            standardGaussianHazardCertificate.normalUpperTailMean
              (lowBasedFamily g c).posteriorMeanScaleLaw
              (lowBasedThreshold g c))
          (Set.Icc (leftCost g) (rightCost g))) ∧
        (∀ g,
          ContinuousOn
            (fun c =>
              standardGaussianHazardCertificate.normalUpperTailMean
                (highBasedFamily g c).posteriorMeanScaleLaw
                (highBasedThreshold g c))
            (Set.Icc (leftCost g) (rightCost g))) ∧
          (∀ g,
            StrictAntiOn
              (fun c =>
                standardGaussianHazardCertificate.normalUpperTailMean
                  (highBasedFamily g c).posteriorMeanScaleLaw
                  (highBasedThreshold g c))
              (Set.Icc (leftCost g) (rightCost g))) := by
  have hlow :=
    paper_standardGaussian_posterior_cost_row_regularity_of_fixed_law_threshold_strictAntiOn
      lowBasedFamily lowBasedThreshold lowBasedLaw hlowBasedLaw
      hlowThresholdCont hlowThresholdAnti
  have hhigh :=
    paper_standardGaussian_posterior_cost_row_regularity_of_fixed_law_threshold_strictAntiOn
      highBasedFamily highBasedThreshold highBasedLaw hhighBasedLaw
      hhighThresholdCont hhighThresholdAnti
  exact ⟨hlow.1, hlow.2, hhigh.1, hhigh.2⟩

/--
Endpoint crossings for fixed-law full-sub posterior cost rows.

When the free row and its cost-indexed based row share a fixed posterior law,
the four endpoint merit inequalities used by the full-sub cost-row bridge
follow from the corresponding threshold-order comparisons.
-/
theorem
    paper_standardGaussian_posterior_low_high_cost_row_endpoint_crossings_of_fixed_law_threshold_order
    {Group LowFreeFeature HighFreeFeature LowBasedFeature
      HighBasedFeature : Type*}
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {leftCost rightCost : Group → ℝ}
    (lowFreeFamily : Group → GaussianOffsetSignalFamily LowFreeFeature)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedThreshold highBasedThreshold : Group → ℝ → ℝ)
    (lowBasedLaw highBasedLaw : Group → GaussianScaleLaw)
    (hlowFreeLaw :
      ∀ g, (lowFreeFamily g).posteriorMeanScaleLaw = lowBasedLaw g)
    (hlowBasedLaw :
      ∀ g c, (lowBasedFamily g c).posteriorMeanScaleLaw = lowBasedLaw g)
    (hhighFreeLaw :
      ∀ g, (highFreeFamily g).posteriorMeanScaleLaw = highBasedLaw g)
    (hhighBasedLaw :
      ∀ g c, (highBasedFamily g c).posteriorMeanScaleLaw = highBasedLaw g)
    (hlowAtLeftThreshold :
      ∀ g, lowFreeThreshold g < lowBasedThreshold g (leftCost g))
    (hlowAtRightThreshold :
      ∀ g, lowBasedThreshold g (rightCost g) < lowFreeThreshold g)
    (hhighAtLeftThreshold :
      ∀ g, highFreeThreshold g < highBasedThreshold g (leftCost g))
    (hhighAtRightThreshold :
      ∀ g, highBasedThreshold g (rightCost g) < highFreeThreshold g) :
    (∀ g,
      standardGaussianHazardCertificate.normalUpperTailMean
          (lowFreeFamily g).posteriorMeanScaleLaw
          (lowFreeThreshold g) <
        standardGaussianHazardCertificate.normalUpperTailMean
          (lowBasedFamily g (leftCost g)).posteriorMeanScaleLaw
          (lowBasedThreshold g (leftCost g))) ∧
      (∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (lowBasedFamily g (rightCost g)).posteriorMeanScaleLaw
            (lowBasedThreshold g (rightCost g)) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (lowFreeFamily g).posteriorMeanScaleLaw
            (lowFreeThreshold g)) ∧
        (∀ g,
          standardGaussianHazardCertificate.normalUpperTailMean
              (highFreeFamily g).posteriorMeanScaleLaw
              (highFreeThreshold g) <
            standardGaussianHazardCertificate.normalUpperTailMean
              (highBasedFamily g (leftCost g)).posteriorMeanScaleLaw
              (highBasedThreshold g (leftCost g))) ∧
          (∀ g,
            standardGaussianHazardCertificate.normalUpperTailMean
                (highBasedFamily g (rightCost g)).posteriorMeanScaleLaw
                (highBasedThreshold g (rightCost g)) <
              standardGaussianHazardCertificate.normalUpperTailMean
                (highFreeFamily g).posteriorMeanScaleLaw
                (highFreeThreshold g)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    simpa [standardGaussianHazardCertificate, hlowFreeLaw g,
      hlowBasedLaw g (leftCost g)] using
      (paper_proposition8_standardGaussian_normalUpperTailMean_strictMono_threshold
        (lowBasedLaw g) (hlowAtLeftThreshold g))
  · intro g
    simpa [standardGaussianHazardCertificate, hlowBasedLaw g (rightCost g),
      hlowFreeLaw g] using
      (paper_proposition8_standardGaussian_normalUpperTailMean_strictMono_threshold
        (lowBasedLaw g) (hlowAtRightThreshold g))
  · intro g
    simpa [standardGaussianHazardCertificate, hhighFreeLaw g,
      hhighBasedLaw g (leftCost g)] using
      (paper_proposition8_standardGaussian_normalUpperTailMean_strictMono_threshold
        (highBasedLaw g) (hhighAtLeftThreshold g))
  · intro g
    simpa [standardGaussianHazardCertificate, hhighBasedLaw g (rightCost g),
      hhighFreeLaw g] using
      (paper_proposition8_standardGaussian_normalUpperTailMean_strictMono_threshold
        (highBasedLaw g) (hhighAtRightThreshold g))

/--
Standard-Gaussian Proposition 5(ii) objective bridge with full-sub posterior
cost-row regularity generated from fixed posterior laws and threshold
regularity.

Compared with
`paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_source_free_cost_rows`,
this wrapper removes the four visible low/high cost-row continuity and
strict-antitone assumptions.
-/
theorem
    paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows
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
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (lowFreeFamily : Group → GaussianOffsetSignalFamily LowFreeFeature)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (lowBasedThreshold highBasedThreshold : Group → ℝ → ℝ)
    (lowBasedLaw highBasedLaw : Group → GaussianScaleLaw)
    (hlowBasedLaw :
      ∀ g c, (lowBasedFamily g c).posteriorMeanScaleLaw =
        lowBasedLaw g)
    (hhighBasedLaw :
      ∀ g c, (highBasedFamily g c).posteriorMeanScaleLaw =
        highBasedLaw g)
    (hlowThresholdCont :
      ∀ g, ContinuousOn (lowBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hlowThresholdAnti :
      ∀ g, StrictAntiOn (lowBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hhighThresholdCont :
      ∀ g, ContinuousOn (highBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hhighThresholdAnti :
      ∀ g, StrictAntiOn (highBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hleft_right : ∀ g, leftCost g < rightCost g)
    (hleft_pos : ∀ g, 0 < leftCost g)
    (hcostMem :
      ∀ g, testCost g ∈ Set.Icc (leftCost g) (rightCost g))
    (hlowAtLeft :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (lowFreeFamily g).posteriorMeanScaleLaw
            (lowFreeThreshold g) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (lowBasedFamily g (leftCost g)).posteriorMeanScaleLaw
            (lowBasedThreshold g (leftCost g)))
    (hlowAtRight :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (lowBasedFamily g (rightCost g)).posteriorMeanScaleLaw
            (lowBasedThreshold g (rightCost g)) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (lowFreeFamily g).posteriorMeanScaleLaw
            (lowFreeThreshold g))
    (hhighAtLeft :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (highFreeFamily g).posteriorMeanScaleLaw
            (highFreeThreshold g) <
          standardGaussianHazardCertificate.normalUpperTailMean
            (highBasedFamily g (leftCost g)).posteriorMeanScaleLaw
            (highBasedThreshold g (leftCost g)))
    (hhighAtRight :
      ∀ g,
        standardGaussianHazardCertificate.normalUpperTailMean
            (highBasedFamily g (rightCost g)).posteriorMeanScaleLaw
            (highBasedThreshold g (rightCost g)) <
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
            (highBasedThreshold groupB (testCost groupB))) :
    ∃ lowCostThreshold highCostThreshold : Group → ℝ,
      (∀ g, lowCostThreshold g ∈
        Set.Ioo (leftCost g) (rightCost g)) ∧
        (∀ g, highCostThreshold g ∈
          Set.Ioo (leftCost g) (rightCost g)) ∧
          (∀ g,
            standardGaussianHazardCertificate.normalUpperTailMean
                (lowBasedFamily g
                  (lowCostThreshold g)).posteriorMeanScaleLaw
                (lowBasedThreshold g (lowCostThreshold g)) =
              standardGaussianHazardCertificate.normalUpperTailMean
                (lowFreeFamily g).posteriorMeanScaleLaw
                (lowFreeThreshold g)) ∧
            (∀ g,
              standardGaussianHazardCertificate.normalUpperTailMean
                  (highBasedFamily g
                    (highCostThreshold g)).posteriorMeanScaleLaw
                  (highBasedThreshold g (highCostThreshold g)) =
                standardGaussianHazardCertificate.normalUpperTailMean
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
                      glm20StrategicSubEstimateMassAbove
                        standardGaussianCDFAPI (subEstimateLaw g) q)) := by
  have hregular :=
    paper_standardGaussian_posterior_low_high_cost_row_regularities_of_fixed_law_threshold_strictAntiOn
      (leftCost := leftCost) (rightCost := rightCost)
      lowBasedFamily highBasedFamily lowBasedThreshold highBasedThreshold
      lowBasedLaw highBasedLaw hlowBasedLaw hhighBasedLaw
      hlowThresholdCont hlowThresholdAnti hhighThresholdCont
      hhighThresholdAnti
  exact
    paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_source_free_cost_rows
      (S := S) (policyPair := policyPair) (Psub := Psub)
      (Pfull := Pfull) (J1 := J1) (J2 := J2) (groupA := groupA)
      (groupB := groupB) (populationShare := populationShare)
      (testCost := testCost) (leftCost := leftCost)
      (rightCost := rightCost) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub) subEstimateLaw
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) lowFreeFamily highFreeFamily
      lowFreeThreshold highFreeThreshold lowBasedFamily highBasedFamily
      lowBasedThreshold highBasedThreshold hleft_right hleft_pos hcostMem
      hregular.1 hregular.2.1 hlowAtLeft hlowAtRight hregular.2.2.1
      hregular.2.2.2 hhighAtLeft hhighAtRight hfreePriorMean
      hfreePriorVar hfreePrecision hfreeThresholdMean hfreeThreshold
      hbasedPriorMean hbasedPriorVar hbasedPrecision hbasedThresholdMean
      hbasedThreshold hshareA hshareB hmassFullFullA hmassFullFullB
      hmassFullSubA hmassFullSubB hcapacity2 hfillFullFull2
      hfixedPoolMeritA hfixedPoolMeritB honlyA_J2_groupB_eq
      honlyA_J2_groupA_testBased honlyA_J2_groupA_testFree
      honlyB_J2_groupA_eq honlyB_J2_groupB_testBased
      honlyB_J2_groupB_testFree hnoExpandA hexpandA_J1_groupB_eq
      hexpandA_J1_groupA_testFree hexpandA_J1_groupA_testBased hnoExpandB
      hexpandB_J1_groupA_eq hexpandB_J1_groupB_testFree
      hexpandB_J1_groupB_testBased

/--
Standard-Gaussian Proposition 5(ii) objective bridge with full-sub posterior
cost-row regularity and endpoint merit crossings both generated from fixed
posterior laws.

Compared with
`paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows`,
this wrapper replaces the four endpoint merit-crossing inequalities by the
corresponding endpoint threshold-order comparisons.
-/
theorem
    paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_threshold_order_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows
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
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (lowFreeFamily : Group → GaussianOffsetSignalFamily LowFreeFeature)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (lowBasedThreshold highBasedThreshold : Group → ℝ → ℝ)
    (lowBasedLaw highBasedLaw : Group → GaussianScaleLaw)
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
        (Set.Icc (leftCost g) (rightCost g)))
    (hlowThresholdAnti :
      ∀ g, StrictAntiOn (lowBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hhighThresholdCont :
      ∀ g, ContinuousOn (highBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hhighThresholdAnti :
      ∀ g, StrictAntiOn (highBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hleft_right : ∀ g, leftCost g < rightCost g)
    (hleft_pos : ∀ g, 0 < leftCost g)
    (hcostMem :
      ∀ g, testCost g ∈ Set.Icc (leftCost g) (rightCost g))
    (hlowAtLeftThreshold :
      ∀ g, lowFreeThreshold g < lowBasedThreshold g (leftCost g))
    (hlowAtRightThreshold :
      ∀ g, lowBasedThreshold g (rightCost g) < lowFreeThreshold g)
    (hhighAtLeftThreshold :
      ∀ g, highFreeThreshold g < highBasedThreshold g (leftCost g))
    (hhighAtRightThreshold :
      ∀ g, highBasedThreshold g (rightCost g) < highFreeThreshold g)
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
            (highBasedThreshold groupB (testCost groupB))) :
    ∃ lowCostThreshold highCostThreshold : Group → ℝ,
      (∀ g, lowCostThreshold g ∈
        Set.Ioo (leftCost g) (rightCost g)) ∧
        (∀ g, highCostThreshold g ∈
          Set.Ioo (leftCost g) (rightCost g)) ∧
          (∀ g,
            standardGaussianHazardCertificate.normalUpperTailMean
                (lowBasedFamily g
                  (lowCostThreshold g)).posteriorMeanScaleLaw
                (lowBasedThreshold g (lowCostThreshold g)) =
              standardGaussianHazardCertificate.normalUpperTailMean
                (lowFreeFamily g).posteriorMeanScaleLaw
                (lowFreeThreshold g)) ∧
            (∀ g,
              standardGaussianHazardCertificate.normalUpperTailMean
                  (highBasedFamily g
                    (highCostThreshold g)).posteriorMeanScaleLaw
                  (highBasedThreshold g (highCostThreshold g)) =
                standardGaussianHazardCertificate.normalUpperTailMean
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
                      glm20StrategicSubEstimateMassAbove
                        standardGaussianCDFAPI (subEstimateLaw g) q)) := by
  have hcross :=
    paper_standardGaussian_posterior_low_high_cost_row_endpoint_crossings_of_fixed_law_threshold_order
      (leftCost := leftCost) (rightCost := rightCost)
      lowFreeFamily highFreeFamily lowBasedFamily highBasedFamily
      lowFreeThreshold highFreeThreshold lowBasedThreshold
      highBasedThreshold lowBasedLaw highBasedLaw hlowFreeLaw
      hlowBasedLaw hhighFreeLaw hhighBasedLaw hlowAtLeftThreshold
      hlowAtRightThreshold hhighAtLeftThreshold hhighAtRightThreshold
  exact
    paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows
      (S := S) (policyPair := policyPair) (Psub := Psub)
      (Pfull := Pfull) (J1 := J1) (J2 := J2) (groupA := groupA)
      (groupB := groupB) (populationShare := populationShare)
      (testCost := testCost) (leftCost := leftCost)
      (rightCost := rightCost) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub) subEstimateLaw
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) lowFreeFamily highFreeFamily
      lowFreeThreshold highFreeThreshold lowBasedFamily highBasedFamily
      lowBasedThreshold highBasedThreshold lowBasedLaw highBasedLaw
      hlowBasedLaw hhighBasedLaw hlowThresholdCont hlowThresholdAnti
      hhighThresholdCont hhighThresholdAnti hleft_right hleft_pos
      hcostMem hcross.1 hcross.2.1 hcross.2.2.1 hcross.2.2.2
      hfreePriorMean hfreePriorVar hfreePrecision hfreeThresholdMean
      hfreeThreshold hbasedPriorMean hbasedPriorVar hbasedPrecision
      hbasedThresholdMean hbasedThreshold hshareA hshareB hmassFullFullA
      hmassFullFullB hmassFullSubA hmassFullSubB hcapacity2
      hfillFullFull2 hfixedPoolMeritA hfixedPoolMeritB
      honlyA_J2_groupB_eq honlyA_J2_groupA_testBased
      honlyA_J2_groupA_testFree honlyB_J2_groupA_eq
      honlyB_J2_groupB_testBased honlyB_J2_groupB_testFree hnoExpandA
      hexpandA_J1_groupB_eq hexpandA_J1_groupA_testFree
      hexpandA_J1_groupA_testBased hnoExpandB hexpandB_J1_groupA_eq
      hexpandB_J1_groupB_testFree hexpandB_J1_groupB_testBased

/--
Standard-Gaussian Proposition 5(ii) objective bridge with the same fixed-law
posterior cost-row and threshold-order surface, but with the capacity equation
and full/full fill premise derived from the bundled full/full capacity/cutoff
source rows.
-/
abbrev
    paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_threshold_order_interval_capacity_cutoff_rows_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows
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
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (lowFreeFamily : Group → GaussianOffsetSignalFamily LowFreeFeature)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (lowBasedThreshold highBasedThreshold : Group → ℝ → ℝ)
    (lowBasedLaw highBasedLaw : Group → GaussianScaleLaw)
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
        (Set.Icc (leftCost g) (rightCost g)))
    (hlowThresholdAnti :
      ∀ g, StrictAntiOn (lowBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hhighThresholdCont :
      ∀ g, ContinuousOn (highBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hhighThresholdAnti :
      ∀ g, StrictAntiOn (highBasedThreshold g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hleft_right : ∀ g, leftCost g < rightCost g)
    (hleft_pos : ∀ g, 0 < leftCost g)
    (hcostMem :
      ∀ g, testCost g ∈ Set.Icc (leftCost g) (rightCost g))
    (hlowAtLeftThreshold :
      ∀ g, lowFreeThreshold g < lowBasedThreshold g (leftCost g))
    (hlowAtRightThreshold :
      ∀ g, lowBasedThreshold g (rightCost g) < lowFreeThreshold g)
    (hhighAtLeftThreshold :
      ∀ g, highFreeThreshold g < highBasedThreshold g (leftCost g))
    (hhighAtRightThreshold :
      ∀ g, highBasedThreshold g (rightCost g) < highFreeThreshold g)
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
    (hcapacityCutoffRows :
      GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
        populationShare subEstimateLaw groupA groupB capacity1 capacity2
        q1Sub q2Sub fullFullCutoff)
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
            (highBasedThreshold groupB (testCost groupB))) :=
  let hcapacityRows :=
    paper_theorem3_capacity_cutoff_rows_components hcapacityCutoffRows
  let hcapacity2 := hcapacityRows.2.2.2.1
  let hcut2A := hcapacityRows.2.2.2.2.1
  let hcut2B := hcapacityRows.2.2.2.2.2
  let hfillFullFull2 :
      capacity2 ≤
        populationShare groupA *
            S.massTestTaking groupA (policyPair Pfull Pfull) +
          populationShare groupB *
            S.massTestTaking groupB (policyPair Pfull Pfull) := by
    have hfill :=
      paper_theorem3_fullFull_fill_capacity_of_cutoff_le
        standardGaussianCDFAPI subEstimateLaw hcapacity2 (le_of_lt hshareA)
        (le_of_lt hshareB) hcut2A hcut2B
    simpa [hmassFullFullA, hmassFullFullB] using hfill
  paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_threshold_order_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows
    (S := S) (policyPair := policyPair) (Psub := Psub) (Pfull := Pfull)
    (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (leftCost := leftCost) (rightCost := rightCost)
    (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
    subEstimateLaw (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff) lowFreeFamily highFreeFamily
    lowFreeThreshold highFreeThreshold lowBasedFamily highBasedFamily
    lowBasedThreshold highBasedThreshold lowBasedLaw highBasedLaw
    hlowFreeLaw hlowBasedLaw hhighFreeLaw hhighBasedLaw
    hlowThresholdCont hlowThresholdAnti hhighThresholdCont
    hhighThresholdAnti hleft_right hleft_pos hcostMem hlowAtLeftThreshold
    hlowAtRightThreshold hhighAtLeftThreshold hhighAtRightThreshold
    hfreePriorMean hfreePriorVar hfreePrecision hfreeThresholdMean
    hfreeThreshold hbasedPriorMean hbasedPriorVar hbasedPrecision
    hbasedThresholdMean hbasedThreshold hshareA hshareB hmassFullFullA
    hmassFullFullB hmassFullSubA hmassFullSubB hcapacity2 hfillFullFull2
    hfixedPoolMeritA hfixedPoolMeritB honlyA_J2_groupB_eq
    honlyA_J2_groupA_testBased honlyA_J2_groupA_testFree
    honlyB_J2_groupA_eq honlyB_J2_groupB_testBased
    honlyB_J2_groupB_testFree hnoExpandA hexpandA_J1_groupB_eq
    hexpandA_J1_groupA_testFree hexpandA_J1_groupA_testBased hnoExpandB
    hexpandB_J1_groupA_eq hexpandB_J1_groupB_testFree
    hexpandB_J1_groupB_testBased

/--
Standard-Gaussian Proposition 5(ii) objective bridge with fixed-law posterior
cost rows, affine full-sub threshold rows, and bundled full/full
capacity/cutoff source rows.

This is the compact paper-facing version of the threshold-order bridge: the
four low/high threshold regularity premises are generated from positive affine
slopes, the endpoint/threshold-order rows are unpacked from
`GLM20Theorem3FullSubAffineThresholdRows`, and the full/full capacity/fill
side is generated from `GLM20Theorem3CapacityCutoffRows`.
-/
abbrev
    paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_affine_threshold_rows_interval_capacity_cutoff_rows_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows
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
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    (subEstimateLaw : Group → GaussianScaleLaw)
    (lowFreeFamily : Group → GaussianOffsetSignalFamily LowFreeFeature)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (lowBasedLaw highBasedLaw : Group → GaussianScaleLaw)
    (lowBasedThresholdIntercept highBasedThresholdIntercept
      lowBasedThresholdSlope highBasedThresholdSlope : Group → ℝ)
    (hfullSubAffineThresholdRows :
      GLM20Theorem3FullSubAffineThresholdRows highFreeFamily lowBasedFamily
        leftCost rightCost lowFreeThreshold highFreeThreshold
        lowBasedThresholdIntercept highBasedThresholdIntercept
        lowBasedThresholdSlope highBasedThresholdSlope)
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
    (hleft_right : ∀ g, leftCost g < rightCost g)
    (hleft_pos : ∀ g, 0 < leftCost g)
    (hcostMem :
      ∀ g, testCost g ∈ Set.Icc (leftCost g) (rightCost g))
    (hfreePriorMean :
      ∀ g, (highFreeFamily g).priorMean = (lowFreeFamily g).priorMean)
    (hfreePriorVar :
      ∀ g, (highFreeFamily g).priorVar = (lowFreeFamily g).priorVar)
    (hfreePrecision :
      ∀ g,
        (highFreeFamily g).centeredFamily.signalPrecisionSum <
          (lowFreeFamily g).centeredFamily.signalPrecisionSum)
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
    (hcapacityCutoffRows :
      GLM20Theorem3CapacityCutoffRows standardGaussianCDFAPI
        populationShare subEstimateLaw groupA groupB capacity1 capacity2
        q1Sub q2Sub fullFullCutoff)
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
              (lowBasedThresholdIntercept groupA -
                lowBasedThresholdSlope groupA * testCost groupA))
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
              (lowBasedThresholdIntercept groupB -
                lowBasedThresholdSlope groupB * testCost groupB))
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
            (highBasedThresholdIntercept groupA -
              highBasedThresholdSlope groupA * testCost groupA))
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
            (highBasedThresholdIntercept groupB -
              highBasedThresholdSlope groupB * testCost groupB)) :=
  let hthresholdRows :=
    paper_theorem3_fullSub_affine_threshold_rows_components
      hfullSubAffineThresholdRows
  let hregularity :=
    paper_theorem3_low_high_based_threshold_regularities_of_affine_decreasing
      (leftCost := leftCost) (rightCost := rightCost)
      lowBasedThresholdIntercept highBasedThresholdIntercept
      lowBasedThresholdSlope highBasedThresholdSlope
      hthresholdRows.2.2.2.2.2.2.2.2.1
      hthresholdRows.2.2.2.2.2.2.2.2.2
  paper_proposition5_standardGaussian_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_threshold_order_interval_capacity_cutoff_rows_fixed_pool_and_weighted_group_merit_formulas_of_fixed_law_posterior_mean_source_free_cost_rows
    (S := S) (policyPair := policyPair) (Psub := Psub) (Pfull := Pfull)
    (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (leftCost := leftCost) (rightCost := rightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub) subEstimateLaw
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff) lowFreeFamily highFreeFamily
    lowFreeThreshold highFreeThreshold lowBasedFamily highBasedFamily
    (fun g c => lowBasedThresholdIntercept g - lowBasedThresholdSlope g * c)
    (fun g c =>
      highBasedThresholdIntercept g - highBasedThresholdSlope g * c)
    lowBasedLaw highBasedLaw hlowFreeLaw hlowBasedLaw hhighFreeLaw
    hhighBasedLaw hregularity.1 hregularity.2.1 hregularity.2.2.1
    hregularity.2.2.2 hleft_right hleft_pos hcostMem hthresholdRows.1
    hthresholdRows.2.1 hthresholdRows.2.2.1
    hthresholdRows.2.2.2.1 hfreePriorMean hfreePriorVar
    hfreePrecision hthresholdRows.2.2.2.2.1
    hthresholdRows.2.2.2.2.2.1 hbasedPriorMean hbasedPriorVar
    hbasedPrecision hthresholdRows.2.2.2.2.2.2.1
    hthresholdRows.2.2.2.2.2.2.2.1 hshareA hshareB
    hmassFullFullA hmassFullFullB hmassFullSubA hmassFullSubB
    hcapacityCutoffRows hfixedPoolMeritA hfixedPoolMeritB
    honlyA_J2_groupB_eq honlyA_J2_groupA_testBased
    honlyA_J2_groupA_testFree honlyB_J2_groupA_eq
    honlyB_J2_groupB_testBased honlyB_J2_groupB_testFree hnoExpandA
    hexpandA_J1_groupB_eq hexpandA_J1_groupA_testFree
    hexpandA_J1_groupA_testBased hnoExpandB hexpandB_J1_groupA_eq
    hexpandB_J1_groupB_testFree hexpandB_J1_groupB_testBased

/--
Theorem 3 source-family endpoint with the full-sub low/high cost rows
generated directly from posterior-mean source families.

This is the cost-row analogue of the source-family full-sub wrappers that
route through selected equation-(46) cutoffs.  The full-sub branch is stated
against the cost-indexed posterior upper-tail rows themselves, so callers do
not need separate formula-identification assumptions for
`fullSubLowMeritOfCutoff` or `fullSubHighMeritOfCutoff`.
-/
abbrev
    paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_and_cutoff_fill_subFull_fullSub_interval_of_posterior_mean_fullSub_cost_rows
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
    (subSubMerit subFullMeritFallback fullSubMeritFallback
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
    (hfullSubLowCont :
      ∀ g,
        ContinuousOn
          (fun c =>
            C.normalUpperTailMean
              (fullSubLowBasedFamily g c).posteriorMeanScaleLaw
              (fullSubLowBasedThreshold g c))
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubLowAnti :
      ∀ g,
        StrictAntiOn
          (fun c =>
            C.normalUpperTailMean
              (fullSubLowBasedFamily g c).posteriorMeanScaleLaw
              (fullSubLowBasedThreshold g c))
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
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
    (hfullSubHighCont :
      ∀ g,
        ContinuousOn
          (fun c =>
            C.normalUpperTailMean
              (fullSubHighBasedFamily g c).posteriorMeanScaleLaw
              (fullSubHighBasedThreshold g c))
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubHighAnti :
      ∀ g,
        StrictAntiOn
          (fun c =>
            C.normalUpperTailMean
              (fullSubHighBasedFamily g c).posteriorMeanScaleLaw
              (fullSubHighBasedThreshold g c))
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
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
              (fullFullCutoff groupB)) :=
  let fullSubLowTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    C.normalUpperTailMean
      (fullSubLowBasedFamily g c).posteriorMeanScaleLaw
      (fullSubLowBasedThreshold g c)
  let fullSubLowTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean
      (fullSubLowFreeFamily g).posteriorMeanScaleLaw
      (fullSubLowFreeThreshold g)
  let fullSubHighTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    C.normalUpperTailMean
      (fullSubHighBasedFamily g c).posteriorMeanScaleLaw
      (fullSubHighBasedThreshold g c)
  let fullSubHighTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean
      (fullSubHighFreeFamily g).posteriorMeanScaleLaw
      (fullSubHighFreeThreshold g)
  have hfullSubHighAtLowRoot :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowTestBasedMerit g c = fullSubLowTestFreeMerit g →
          fullSubHighTestFreeMerit g < fullSubHighTestBasedMerit g c := by
    simpa [fullSubLowTestBasedMerit, fullSubLowTestFreeMerit,
      fullSubHighTestBasedMerit, fullSubHighTestFreeMerit] using
      (paper_proposition5_high_merit_at_low_root_of_posterior_mean_source_free_cost_rows
        C (leftCost := fullSubLeftCost) (rightCost := fullSubRightCost)
        fullSubLowFreeFamily fullSubHighFreeFamily
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        fullSubLowBasedFamily fullSubHighBasedFamily
        fullSubLowBasedThreshold fullSubHighBasedThreshold
        hfullSubFreePriorMean hfullSubFreePriorVar
        hfullSubFreePrecision hfullSubFreeThresholdMean
        hfullSubFreeThreshold hfullSubBasedPriorMean
        hfullSubBasedPriorVar hfullSubBasedPrecision
        hfullSubBasedThresholdMean hfullSubBasedThreshold)
  paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_and_cutoff_fill_subFull_fullSub_interval
    api subEstimateLaw subSubMass subFullMass subSubMerit
    subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
    diversity
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
    fullSubLowTestBasedMerit fullSubLowTestFreeMerit
    fullSubHighTestBasedMerit fullSubHighTestFreeMerit
    hsubFullLeftRight hsubFullLeftPos hsubFullCostMem hsubFullCont
    hsubFullAnti hsubFullAtLeft hsubFullAtRight hfullSubLeftRight
    hfullSubLeftPos hfullSubCostMem hfullSubLowCont hfullSubLowAnti
    hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighCont
    hfullSubHighAnti hfullSubHighAtLeft hfullSubHighAtRight
    hfullSubHighAtLowRoot hshareA hshareB hcapacity1 hfillFullFull1
    hcapacity2 hfillFullFull2

/--
Theorem 3 source-family endpoint with full-sub posterior cost rows and
school-`J2` condition-(12) obligations stated on the paper's component table.

This is the component-table analogue of
`paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_and_cutoff_fill_subFull_fullSub_interval_of_posterior_mean_fullSub_cost_rows`.
It keeps the new posterior cost-row treatment of the full-sub low/high
thresholds, while rewriting the final school-`J2` survivor assumptions from
generated feasible-surface rows back to the source component rows.
-/
abbrev
    paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval_of_posterior_mean_fullSub_cost_rows
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
    (subSubMerit subFullMeritFallback fullSubMeritFallback
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
    (hfullSubLowCont :
      ∀ g,
        ContinuousOn
          (fun c =>
            C.normalUpperTailMean
              (fullSubLowBasedFamily g c).posteriorMeanScaleLaw
              (fullSubLowBasedThreshold g c))
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubLowAnti :
      ∀ g,
        StrictAntiOn
          (fun c =>
            C.normalUpperTailMean
              (fullSubLowBasedFamily g c).posteriorMeanScaleLaw
              (fullSubLowBasedThreshold g c))
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
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
    (hfullSubHighCont :
      ∀ g,
        ContinuousOn
          (fun c =>
            C.normalUpperTailMean
              (fullSubHighBasedFamily g c).posteriorMeanScaleLaw
              (fullSubHighBasedThreshold g c))
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hfullSubHighAnti :
      ∀ g,
        StrictAntiOn
          (fun c =>
            C.normalUpperTailMean
              (fullSubHighBasedFamily g c).posteriorMeanScaleLaw
              (fullSubHighBasedThreshold g c))
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
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
    (hJ2ZeroA_component :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback
          fullFullMeritFallback diversity J1 J2 groupA groupB
          populationShare testCost fullFullCutoff fullSubCutoff C
          J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
          J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
          q1Sub costThreshold groupA →
        subFullMeritFallback J2 groupA = 0)
    (hJ2MeritGtB_component :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback
          fullFullMeritFallback diversity J1 J2 groupA groupB
          populationShare testCost fullFullCutoff fullSubCutoff C
          J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
          J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
          q1Sub costThreshold groupA →
        populationShare groupB * subFullMeritFallback J2 groupB >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB)
    (hJ2ZeroB_component :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback
          fullFullMeritFallback diversity J1 J2 groupA groupB
          populationShare testCost fullFullCutoff fullSubCutoff C
          J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
          J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
          q1Sub costThreshold groupB →
        subFullMeritFallback J2 groupB = 0)
    (hJ2MeritGtA_component :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback
          fullFullMeritFallback diversity J1 J2 groupA groupB
          populationShare testCost fullFullCutoff fullSubCutoff C
          J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
          J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
          q1Sub costThreshold groupB →
        populationShare groupA * subFullMeritFallback J2 groupA >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB) :=
  let fullSubLowTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    C.normalUpperTailMean
      (fullSubLowBasedFamily g c).posteriorMeanScaleLaw
      (fullSubLowBasedThreshold g c)
  let fullSubLowTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean
      (fullSubLowFreeFamily g).posteriorMeanScaleLaw
      (fullSubLowFreeThreshold g)
  let fullSubHighTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    C.normalUpperTailMean
      (fullSubHighBasedFamily g c).posteriorMeanScaleLaw
      (fullSubHighBasedThreshold g c)
  let fullSubHighTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean
      (fullSubHighFreeFamily g).posteriorMeanScaleLaw
      (fullSubHighFreeThreshold g)
  have hfullSubHighAtLowRoot :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowTestBasedMerit g c = fullSubLowTestFreeMerit g →
          fullSubHighTestFreeMerit g < fullSubHighTestBasedMerit g c := by
    simpa [fullSubLowTestBasedMerit, fullSubLowTestFreeMerit,
      fullSubHighTestBasedMerit, fullSubHighTestFreeMerit] using
      (paper_proposition5_high_merit_at_low_root_of_posterior_mean_source_free_cost_rows
        C (leftCost := fullSubLeftCost) (rightCost := fullSubRightCost)
        fullSubLowFreeFamily fullSubHighFreeFamily
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        fullSubLowBasedFamily fullSubHighBasedFamily
        fullSubLowBasedThreshold fullSubHighBasedThreshold
        hfullSubFreePriorMean hfullSubFreePriorVar
        hfullSubFreePrecision hfullSubFreeThresholdMean
        hfullSubFreeThreshold hfullSubBasedPriorMean
        hfullSubBasedPriorVar hfullSubBasedPrecision
        hfullSubBasedThresholdMean hfullSubBasedThreshold)
  paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval
    api subEstimateLaw subSubMass subFullMass subSubMerit
    subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
    diversity
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
    fullSubLowTestBasedMerit fullSubLowTestFreeMerit
    fullSubHighTestBasedMerit fullSubHighTestFreeMerit
    hsubFullLeftRight hsubFullLeftPos hsubFullCostMem hsubFullCont
    hsubFullAnti hsubFullAtLeft hsubFullAtRight hfullSubLeftRight
    hfullSubLeftPos hfullSubCostMem hfullSubLowCont hfullSubLowAnti
    hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighCont
    hfullSubHighAnti hfullSubHighAtLeft hfullSubHighAtRight
    hfullSubHighAtLowRoot hshareA hshareB hcapacity1 hfillFullFull1
    hcapacity2 hfillFullFull2 hJ2ZeroA_component hJ2MeritGtB_component
    hJ2ZeroB_component hJ2MeritGtA_component

section FixedLawComponentCostRows

variable {Group School FeatureDrop FeatureKeep LowFreeFeature HighFreeFeature
  LowBasedFeature HighBasedFeature : Type*}
variable [DecidableEq School]
variable [Fintype FeatureDrop] [Nonempty FeatureDrop]
variable [Fintype FeatureKeep] [Nonempty FeatureKeep]
variable [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
variable [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
variable [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
variable [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
variable (api : StandardGaussianCDFAPI)
variable (subEstimateLaw : Group → GaussianScaleLaw)
variable (subSubMass subFullMass : Group → ℝ)
variable (subSubMerit subFullMeritFallback fullSubMeritFallback
  fullFullMeritFallback : School → Group → ℝ)
variable (diversity : School → GLM20StrategicPolicyState → ℝ)
variable {J1 J2 : School} {groupA groupB : Group}
variable {populationShare testCost subFullLeftCost subFullRightCost
  fullSubLeftCost fullSubRightCost : Group → ℝ}
variable {capacity1 capacity2 q1Sub q2Sub : ℝ}
variable {fullFullCutoff fullSubCutoff : Group → ℝ}
variable {feasible1 feasible2 :
  GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
variable (C : GaussianHazardCertificate)
variable (J1DropFamily J2DropFamily :
  Group → GaussianOffsetSignalFamily FeatureDrop)
variable (J1KeepFamily J2KeepFamily :
  Group → GaussianOffsetSignalFamily FeatureKeep)
variable (J1DropThreshold J1KeepThreshold J2DropThreshold
  J2KeepThreshold : Group → ℝ)
variable (hJ1_ne_J2 : J1 ≠ J2)
variable (hJ1PriorMean :
  ∀ g, (J1DropFamily g).priorMean = (J1KeepFamily g).priorMean)
variable (hJ1PriorVar :
  ∀ g, (J1DropFamily g).priorVar = (J1KeepFamily g).priorVar)
variable (hJ1Precision :
  ∀ g,
    (J1DropFamily g).centeredFamily.signalPrecisionSum <
      (J1KeepFamily g).centeredFamily.signalPrecisionSum)
variable (hJ1ThresholdMean :
  ∀ g, (J1DropFamily g).priorMean < J1DropThreshold g)
variable (hJ1Threshold :
  ∀ g, J1DropThreshold g ≤ J1KeepThreshold g)
variable (hJ2PriorMean :
  ∀ g, (J2DropFamily g).priorMean = (J2KeepFamily g).priorMean)
variable (hJ2PriorVar :
  ∀ g, (J2DropFamily g).priorVar = (J2KeepFamily g).priorVar)
variable (hJ2Precision :
  ∀ g,
    (J2DropFamily g).centeredFamily.signalPrecisionSum <
      (J2KeepFamily g).centeredFamily.signalPrecisionSum)
variable (hJ2ThresholdMean :
  ∀ g, (J2DropFamily g).priorMean < J2DropThreshold g)
variable (hJ2Threshold :
  ∀ g, J2DropThreshold g ≤ J2KeepThreshold g)
variable (subFullTestBasedMerit : Group → ℝ → ℝ)
variable (subFullTestFreeMerit : Group → ℝ)
variable (fullSubLowFreeFamily :
  Group → GaussianOffsetSignalFamily LowFreeFeature)
variable (fullSubHighFreeFamily :
  Group → GaussianOffsetSignalFamily HighFreeFeature)
variable (fullSubLowFreeThreshold fullSubHighFreeThreshold : Group → ℝ)
variable (fullSubLowBasedFamily :
  Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
variable (fullSubHighBasedFamily :
  Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
variable (fullSubLowBasedThreshold fullSubHighBasedThreshold :
  Group → ℝ → ℝ)
variable (hsubFullLeftRight :
  ∀ g, subFullLeftCost g < subFullRightCost g)
variable (hsubFullLeftPos : ∀ g, 0 < subFullLeftCost g)
variable (hsubFullCostMem :
  ∀ g, testCost g ∈ Set.Icc (subFullLeftCost g) (subFullRightCost g))
variable (hsubFullCont :
  ∀ g, ContinuousOn (subFullTestBasedMerit g)
    (Set.Icc (subFullLeftCost g) (subFullRightCost g)))
variable (hsubFullAnti :
  ∀ g, StrictAntiOn (subFullTestBasedMerit g)
    (Set.Icc (subFullLeftCost g) (subFullRightCost g)))
variable (hsubFullAtLeft :
  ∀ g, subFullTestFreeMerit g <
    subFullTestBasedMerit g (subFullLeftCost g))
variable (hsubFullAtRight :
  ∀ g, subFullTestBasedMerit g (subFullRightCost g) <
    subFullTestFreeMerit g)
variable (hfullSubLeftRight :
  ∀ g, fullSubLeftCost g < fullSubRightCost g)
variable (hfullSubLeftPos : ∀ g, 0 < fullSubLeftCost g)
variable (hfullSubCostMem :
  ∀ g, testCost g ∈ Set.Icc (fullSubLeftCost g) (fullSubRightCost g))
variable (hfullSubLowAtLeft :
  ∀ g,
    C.normalUpperTailMean
        (fullSubLowFreeFamily g).posteriorMeanScaleLaw
        (fullSubLowFreeThreshold g) <
      C.normalUpperTailMean
        (fullSubLowBasedFamily g (fullSubLeftCost g)).posteriorMeanScaleLaw
        (fullSubLowBasedThreshold g (fullSubLeftCost g)))
variable (hfullSubLowAtRight :
  ∀ g,
    C.normalUpperTailMean
        (fullSubLowBasedFamily g (fullSubRightCost g)).posteriorMeanScaleLaw
        (fullSubLowBasedThreshold g (fullSubRightCost g)) <
      C.normalUpperTailMean
        (fullSubLowFreeFamily g).posteriorMeanScaleLaw
        (fullSubLowFreeThreshold g))
variable (hfullSubHighAtLeft :
  ∀ g,
    C.normalUpperTailMean
        (fullSubHighFreeFamily g).posteriorMeanScaleLaw
        (fullSubHighFreeThreshold g) <
      C.normalUpperTailMean
        (fullSubHighBasedFamily g (fullSubLeftCost g)).posteriorMeanScaleLaw
        (fullSubHighBasedThreshold g (fullSubLeftCost g)))
variable (hfullSubHighAtRight :
  ∀ g,
    C.normalUpperTailMean
        (fullSubHighBasedFamily g (fullSubRightCost g)).posteriorMeanScaleLaw
        (fullSubHighBasedThreshold g (fullSubRightCost g)) <
      C.normalUpperTailMean
        (fullSubHighFreeFamily g).posteriorMeanScaleLaw
        (fullSubHighFreeThreshold g))
variable (hfullSubFreePriorMean :
  ∀ g,
    (fullSubHighFreeFamily g).priorMean =
      (fullSubLowFreeFamily g).priorMean)
variable (hfullSubFreePriorVar :
  ∀ g,
    (fullSubHighFreeFamily g).priorVar =
      (fullSubLowFreeFamily g).priorVar)
variable (hfullSubFreePrecision :
  ∀ g,
    (fullSubHighFreeFamily g).centeredFamily.signalPrecisionSum <
      (fullSubLowFreeFamily g).centeredFamily.signalPrecisionSum)
variable (hfullSubFreeThresholdMean :
  ∀ g,
    (fullSubHighFreeFamily g).priorMean <
      fullSubHighFreeThreshold g)
variable (hfullSubFreeThreshold :
  ∀ g, fullSubHighFreeThreshold g ≤ fullSubLowFreeThreshold g)
variable (hfullSubBasedPriorMean :
  ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
    (fullSubLowBasedFamily g c).priorMean =
      (fullSubHighBasedFamily g c).priorMean)
variable (hfullSubBasedPriorVar :
  ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
    (fullSubLowBasedFamily g c).priorVar =
      (fullSubHighBasedFamily g c).priorVar)
variable (hfullSubBasedPrecision :
  ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
    (fullSubLowBasedFamily g c).centeredFamily.signalPrecisionSum <
      (fullSubHighBasedFamily g c).centeredFamily.signalPrecisionSum)
variable (hfullSubBasedThresholdMean :
  ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
    (fullSubLowBasedFamily g c).priorMean <
      fullSubLowBasedThreshold g c)
variable (hfullSubBasedThreshold :
  ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
    fullSubLowBasedThreshold g c ≤ fullSubHighBasedThreshold g c)
variable (hshareA : 0 < populationShare groupA)
variable (hshareB : 0 < populationShare groupB)
variable (hcapacity1 :
  capacity1 =
    populationShare groupA *
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
          q1Sub +
      populationShare groupB *
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
          q1Sub)
variable (hfillFullFull1 :
  capacity1 ≤
    populationShare groupA *
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
          (fullFullCutoff groupA) +
      populationShare groupB *
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
          (fullFullCutoff groupB))
variable (hcapacity2 :
  capacity2 =
    populationShare groupA *
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
          q2Sub +
      populationShare groupB *
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
          q2Sub)
variable (hfillFullFull2 :
  capacity2 ≤
    populationShare groupA *
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
          (fullFullCutoff groupA) +
      populationShare groupB *
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
          (fullFullCutoff groupB))
variable (hJ2ZeroA_component :
  ∀ costThreshold : Group → ℝ,
    glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
      subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
      diversity J1 J2 groupA groupB populationShare testCost
      fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold q1Sub costThreshold groupA →
    subFullMeritFallback J2 groupA = 0)
variable (hJ2MeritGtB_component :
  ∀ costThreshold : Group → ℝ,
    glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
      subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
      diversity J1 J2 groupA groupB populationShare testCost
      fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold q1Sub costThreshold groupA →
    populationShare groupB * subFullMeritFallback J2 groupB >
      populationShare groupA * subSubMerit J2 groupA +
        populationShare groupB * subSubMerit J2 groupB)
variable (hJ2ZeroB_component :
  ∀ costThreshold : Group → ℝ,
    glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
      subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
      diversity J1 J2 groupA groupB populationShare testCost
      fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold q1Sub costThreshold groupB →
    subFullMeritFallback J2 groupB = 0)
variable (hJ2MeritGtA_component :
  ∀ costThreshold : Group → ℝ,
    glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
      subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
      diversity J1 J2 groupA groupB populationShare testCost
      fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold q1Sub costThreshold groupB →
    populationShare groupA * subFullMeritFallback J2 groupA >
      populationShare groupA * subSubMerit J2 groupA +
        populationShare groupB * subSubMerit J2 groupB)

/--
Theorem 3 component-table posterior cost-row endpoint with the full-sub
low/high continuity and strict-antitone premises discharged from fixed
posterior laws and regular threshold maps.

The remaining endpoint-crossing, source-family ordering, capacity/fill, and
school-`J2` survivor premises are the same as the component-table posterior
cost-row route.  This is the strongest current cost-row surface for the common
standard-Gaussian case where cost changes only the low/high admission
thresholds.
-/
abbrev
    paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval_of_standardGaussian_fixed_law_posterior_mean_fullSub_cost_rows
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
  have hregular :=
    paper_standardGaussian_posterior_low_high_cost_row_regularities_of_fixed_law_threshold_strictAntiOn
      (leftCost := fullSubLeftCost) (rightCost := fullSubRightCost)
      fullSubLowBasedFamily fullSubHighBasedFamily
      fullSubLowBasedThreshold fullSubHighBasedThreshold
      fullSubLowBasedLaw fullSubHighBasedLaw
      hfullSubLowBasedLaw hfullSubHighBasedLaw
      hfullSubLowThresholdCont hfullSubLowThresholdAnti
      hfullSubHighThresholdCont hfullSubHighThresholdAnti
  have hfullSubLowCont :
      ∀ g,
        ContinuousOn
          (fun c =>
            C.normalUpperTailMean
              (fullSubLowBasedFamily g c).posteriorMeanScaleLaw
              (fullSubLowBasedThreshold g c))
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)) := by
    intro g
    simpa [hC, standardGaussianHazardCertificate] using hregular.1 g
  have hfullSubLowAnti :
      ∀ g,
        StrictAntiOn
          (fun c =>
            C.normalUpperTailMean
              (fullSubLowBasedFamily g c).posteriorMeanScaleLaw
              (fullSubLowBasedThreshold g c))
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)) := by
    intro g
    simpa [hC, standardGaussianHazardCertificate] using hregular.2.1 g
  have hfullSubHighCont :
      ∀ g,
        ContinuousOn
          (fun c =>
            C.normalUpperTailMean
              (fullSubHighBasedFamily g c).posteriorMeanScaleLaw
              (fullSubHighBasedThreshold g c))
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)) := by
    intro g
    simpa [hC, standardGaussianHazardCertificate] using hregular.2.2.1 g
  have hfullSubHighAnti :
      ∀ g,
        StrictAntiOn
          (fun c =>
            C.normalUpperTailMean
              (fullSubHighBasedFamily g c).posteriorMeanScaleLaw
              (fullSubHighBasedThreshold g c))
          (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)) := by
    intro g
    simpa [hC, standardGaussianHazardCertificate] using hregular.2.2.2 g
  paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval_of_posterior_mean_fullSub_cost_rows
    api subEstimateLaw subSubMass subFullMass subSubMerit
    subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
    diversity
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
    hfullSubCostMem hfullSubLowCont hfullSubLowAnti hfullSubLowAtLeft
    hfullSubLowAtRight hfullSubHighCont hfullSubHighAnti
    hfullSubHighAtLeft hfullSubHighAtRight hfullSubFreePriorMean
    hfullSubFreePriorVar hfullSubFreePrecision hfullSubFreeThresholdMean
    hfullSubFreeThreshold hfullSubBasedPriorMean hfullSubBasedPriorVar
    hfullSubBasedPrecision hfullSubBasedThresholdMean
    hfullSubBasedThreshold hshareA hshareB hcapacity1 hfillFullFull1
    hcapacity2 hfillFullFull2 hJ2ZeroA_component hJ2MeritGtB_component
    hJ2ZeroB_component hJ2MeritGtA_component

end FixedLawComponentCostRows

end

end GLM20DroppingStandardizedTesting
