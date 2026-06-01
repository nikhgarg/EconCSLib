import GLM20DroppingStandardizedTesting.Theorem3ConstructedComponents
import GLM20DroppingStandardizedTesting.Theorem3SimplePremises

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Proposition 5(i) school-`J2` objective bridge for the zero-fallback source
table.

The zero-fallback table makes the expanding group's school-`J2` admitted merit
zero on the relevant cutoff branch.  Combined with the base survivor mass and
strict-merit source rows, this gives the two branch-conditioned objective
iff statements needed by the Proposition 5 / Theorem 3 route.
-/
theorem
    paper_proposition5_source_family_j2_zero_fallback_school2_objective_bridge_of_base_survivor_components
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost : Group → ℝ)
    {capacity1 capacity2 q1Sub : ℝ}
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2)
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
    (hJ2MassB_base :
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
        subFullMass groupB ≥ capacity2)
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
    (hJ2MassA_base :
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
        subFullMass groupA ≥ capacity2)
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
            populationShare groupB * subSubMerit J2 groupB) :
    let S :=
      glm20Theorem3SourceFamilyPolicyStateTableSurface api subEstimateLaw
        subSubMass subFullMass subSubMerit
        (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
          fullFullCutoff J2 subFullMeritBase)
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2 groupA
        groupB populationShare fullFullCutoff fullSubCutoff C
        J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
        J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
    let obj :=
      glm20TwoGroupWeightedAcademicMeritObjective S
        glm20StrategicPolicyStatePair J2 groupA groupB populationShare
    (∀ costThreshold : Group → ℝ,
      glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
        subEstimateLaw subSubMass subFullMass subSubMerit
        (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
          fullFullCutoff J2 subFullMeritBase)
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2
        groupA groupB populationShare testCost fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold q1Sub costThreshold groupA →
      ((obj GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub ≤
          obj GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) ↔
        glm20Theorem3SubFullOtherGroupKeepsTest S
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB)) ∧
    (∀ costThreshold : Group → ℝ,
      glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
        subEstimateLaw subSubMass subFullMass subSubMerit
        (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
          fullFullCutoff J2 subFullMeritBase)
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2
        groupA groupB populationShare testCost fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold q1Sub costThreshold groupB →
      ((obj GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub ≤
          obj GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) ↔
        glm20Theorem3SubFullOtherGroupKeepsTest S
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA)) := by
  let S :=
    glm20Theorem3SourceFamilyPolicyStateTableSurface api subEstimateLaw
      subSubMass subFullMass subSubMerit
      (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
        fullFullCutoff J2 subFullMeritBase)
      fullSubMeritFallback fullFullMeritFallback diversity J1 J2 groupA
      groupB populationShare fullFullCutoff fullSubCutoff C
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
  let K : Group → ℝ → ℝ :=
    fun g q => glm20StrategicSubEstimateMassAbove api (subEstimateLaw g) q
  have hJ2_ne_J1 : J2 ≠ J1 := by
    intro h
    exact hJ1_ne_J2 h.symm
  have hcomponents :=
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_components_of_base_survivor_components
      api subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback
      diversity J1 J2 groupA groupB populationShare testCost
      fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hshareA hshareB hcapacity1
      hfillFullFull1 hJ2MassB_base hJ2MeritGtB_base hJ2MassA_base
      hJ2MeritGtA_base
  constructor
  · intro costThreshold hdropA
    have hbridge :=
      paper_proposition5_part_i_school2_objective_bridges_of_weighted_objective_zero_merits_and_merit_gt
        (S := S) (policyPair := glm20StrategicPolicyStatePair)
        (Psub := GLM20StrategicPolicyState.singleSub)
        (Pfull := GLM20StrategicPolicyState.singleFull)
        (J2 := J2) (groupA := groupA) (groupB := groupB)
        (populationShare := populationShare) (testCost := testCost)
        (costThreshold := costThreshold) (capacity2 := capacity2)
        (q1Sub := q1Sub) (K := K)
        (by
          intro hdrop
          simpa [S, glm20Theorem3SourceFamilyPolicyStateTableSurface,
            glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
            glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface,
            glm20StrategicPolicyStateAdmittedMerit,
            glm20Theorem3SourceFamilySubFullMeritTable,
            glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
              hcomponents.1 costThreshold
                (by
                  simpa [S, K,
                    glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
                    using hdrop))
        (by
          intro hdrop
          exact hcomponents.2.1 costThreshold
            (by
              simpa [S, K,
                glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
                using hdrop))
        (by
          intro hdrop
          simpa [S, glm20Theorem3SourceFamilyPolicyStateTableSurface,
            glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
            glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface,
            glm20StrategicPolicyStateAdmittedMerit,
            glm20Theorem3SourceFamilySubFullMeritTable,
            glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
              hcomponents.2.2.1 costThreshold
                (by
                  simpa [S, K,
                    glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
                    using hdrop))
        (by
          intro hdrop
          simpa [S, glm20Theorem3SourceFamilyPolicyStateTableSurface,
            glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
            glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface,
            glm20StrategicPolicyStateAdmittedMerit,
            glm20Theorem3SourceFamilySubFullMeritTable,
            glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
              hcomponents.2.2.2.1 costThreshold
                (by
                  simpa [S, K,
                    glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
                    using hdrop))
        (by
          intro hdrop
          exact hcomponents.2.2.2.2.1 costThreshold
            (by
              simpa [S, K,
                glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
                using hdrop))
        (by
          intro hdrop
          simpa [S, glm20Theorem3SourceFamilyPolicyStateTableSurface,
            glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
            glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface,
            glm20StrategicPolicyStateAdmittedMerit,
            glm20Theorem3SourceFamilySubFullMeritTable,
            glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
              hcomponents.2.2.2.2.2 costThreshold
                (by
                  simpa [S, K,
                    glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
                    using hdrop))
    exact hbridge.1
      (by
        simpa [S, K, glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
          using hdropA)
  · intro costThreshold hdropB
    have hbridge :=
      paper_proposition5_part_i_school2_objective_bridges_of_weighted_objective_zero_merits_and_merit_gt
        (S := S) (policyPair := glm20StrategicPolicyStatePair)
        (Psub := GLM20StrategicPolicyState.singleSub)
        (Pfull := GLM20StrategicPolicyState.singleFull)
        (J2 := J2) (groupA := groupA) (groupB := groupB)
        (populationShare := populationShare) (testCost := testCost)
        (costThreshold := costThreshold) (capacity2 := capacity2)
        (q1Sub := q1Sub) (K := K)
        (by
          intro hdrop
          simpa [S, glm20Theorem3SourceFamilyPolicyStateTableSurface,
            glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
            glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface,
            glm20StrategicPolicyStateAdmittedMerit,
            glm20Theorem3SourceFamilySubFullMeritTable,
            glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
              hcomponents.1 costThreshold
                (by
                  simpa [S, K,
                    glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
                    using hdrop))
        (by
          intro hdrop
          exact hcomponents.2.1 costThreshold
            (by
              simpa [S, K,
                glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
                using hdrop))
        (by
          intro hdrop
          simpa [S, glm20Theorem3SourceFamilyPolicyStateTableSurface,
            glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
            glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface,
            glm20StrategicPolicyStateAdmittedMerit,
            glm20Theorem3SourceFamilySubFullMeritTable,
            glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
              hcomponents.2.2.1 costThreshold
                (by
                  simpa [S, K,
                    glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
                    using hdrop))
        (by
          intro hdrop
          simpa [S, glm20Theorem3SourceFamilyPolicyStateTableSurface,
            glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
            glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface,
            glm20StrategicPolicyStateAdmittedMerit,
            glm20Theorem3SourceFamilySubFullMeritTable,
            glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
              hcomponents.2.2.2.1 costThreshold
                (by
                  simpa [S, K,
                    glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
                    using hdrop))
        (by
          intro hdrop
          exact hcomponents.2.2.2.2.1 costThreshold
            (by
              simpa [S, K,
                glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
                using hdrop))
        (by
          intro hdrop
          simpa [S, glm20Theorem3SourceFamilyPolicyStateTableSurface,
            glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
            glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface,
            glm20StrategicPolicyStateAdmittedMerit,
            glm20Theorem3SourceFamilySubFullMeritTable,
            glm20OverrideSchoolMeritRow, hJ2_ne_J1] using
              hcomponents.2.2.2.2.2 costThreshold
                (by
                  simpa [S, K,
                    glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
                    using hdrop))
    exact hbridge.2
      (by
        simpa [S, K, glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands]
          using hdropB)

/--
Proposition 5(i) school-`J2` objective bridge for the zero-fallback source
table, with condition (11)--(12) supplied as the same bundled paper source rows
used by the top Theorem 3 wrapper.

This is a paper-facing convenience layer over
`paper_proposition5_source_family_j2_zero_fallback_school2_objective_bridge_of_base_survivor_components`.
-/
abbrev
    paper_proposition5_source_family_j2_zero_fallback_school2_objective_bridge_of_j2_survivor_rows
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost : Group → ℝ)
    {capacity1 capacity2 q1Sub : ℝ}
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2)
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
    (hJ2SurvivorRows :
      GLM20Theorem3J2SurvivorRows populationShare subFullMass
        subSubMerit subFullMeritBase J2 groupA groupB capacity2) :=
  have hrows :=
    paper_theorem3_j2_survivor_rows_components hJ2SurvivorRows
  paper_proposition5_source_family_j2_zero_fallback_school2_objective_bridge_of_base_survivor_components
    (api := api) (subEstimateLaw := subEstimateLaw)
    (subSubMass := subSubMass) (subFullMass := subFullMass)
    (subSubMerit := subSubMerit)
    (subFullMeritBase := subFullMeritBase)
    (fullSubMeritFallback := fullSubMeritFallback)
    (fullFullMeritFallback := fullFullMeritFallback)
    (diversity := diversity) (J1 := J1) (J2 := J2)
    (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (capacity1 := capacity1) (capacity2 := capacity2) (q1Sub := q1Sub)
    (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
    (C := C) (J1DropFamily := J1DropFamily)
    (J2DropFamily := J2DropFamily) (J1KeepFamily := J1KeepFamily)
    (J2KeepFamily := J2KeepFamily)
    (J1DropThreshold := J1DropThreshold)
    (J1KeepThreshold := J1KeepThreshold)
    (J2DropThreshold := J2DropThreshold)
    (J2KeepThreshold := J2KeepThreshold)
    (hJ1_ne_J2 := hJ1_ne_J2) (hshareA := hshareA)
    (hshareB := hshareB) (hcapacity1 := hcapacity1)
    (hfillFullFull1 := hfillFullFull1)
    (hJ2MassB_base := by
      intro _ _
      exact hrows.1)
    (hJ2MeritGtB_base := by
      intro _ _
      exact hrows.2.1)
    (hJ2MassA_base := by
      intro _ _
      exact hrows.2.2.1)
    (hJ2MeritGtA_base := by
      intro _ _
      exact hrows.2.2.2)

/--
Standard-Gaussian version of
`paper_proposition5_source_family_j2_zero_fallback_school2_objective_bridge_of_j2_survivor_rows`.
-/
abbrev
    paper_proposition5_standardGaussian_source_family_j2_zero_fallback_school2_objective_bridge_of_j2_survivor_rows
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    {capacity1 capacity2 q1Sub : ℝ} :=
  paper_proposition5_source_family_j2_zero_fallback_school2_objective_bridge_of_j2_survivor_rows
    (Group := Group) (School := School) (FeatureDrop := FeatureDrop)
    (FeatureKeep := FeatureKeep) (capacity1 := capacity1)
    (capacity2 := capacity2) (q1Sub := q1Sub)
    (api := standardGaussianCDFAPI)
    (C := standardGaussianHazardInverseCertificate.toGaussianHazardCertificate)

/--
Standard-Gaussian zero-fallback school-`J2` objective bridge specialized to
the paper's named groups, named schools, and population-share row.

This discharges the school distinctness and positive-share side-conditions from
`0 < pi < 1`, leaving only the source rows needed by Proposition 5.
-/
abbrev
    paper_proposition5_standardGaussian_source_family_j2_zero_fallback_school2_objective_bridge_of_j2_survivor_rows_paper_groups_schools_with_population_share
    {FeatureDrop FeatureKeep : Type*}
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    (subEstimateLaw : GLM20Group → GaussianScaleLaw)
    (subSubMass subFullMass : GLM20Group → ℝ)
    (subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback : GLM20School → GLM20Group → ℝ)
    (diversity : GLM20School → GLM20StrategicPolicyState → ℝ)
    {pi : ℝ}
    (testCost : GLM20Group → ℝ)
    {capacity1 capacity2 q1Sub : ℝ}
    (fullFullCutoff fullSubCutoff : GLM20Group → ℝ)
    (J1DropFamily J2DropFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      GLM20Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : GLM20Group → ℝ)
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
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
    (hJ2SurvivorRows :
      GLM20Theorem3J2SurvivorRows (glm20Theorem3PopulationShare pi)
        subFullMass subSubMerit subFullMeritBase glm20SchoolJ2
        GLM20Group.groupA GLM20Group.groupB capacity2) :=
  let hshares := glm20Theorem3PopulationShare_pos_of_pi_mem_Ioo hpi
  paper_proposition5_standardGaussian_source_family_j2_zero_fallback_school2_objective_bridge_of_j2_survivor_rows
    (Group := GLM20Group) (School := GLM20School)
    (FeatureDrop := FeatureDrop) (FeatureKeep := FeatureKeep)
    (capacity1 := capacity1) (capacity2 := capacity2) (q1Sub := q1Sub)
    (subEstimateLaw := subEstimateLaw) (subSubMass := subSubMass)
    (subFullMass := subFullMass) (subSubMerit := subSubMerit)
    (subFullMeritBase := subFullMeritBase)
    (fullSubMeritFallback := fullSubMeritFallback)
    (fullFullMeritFallback := fullFullMeritFallback)
    (diversity := diversity) (J1 := glm20SchoolJ1) (J2 := glm20SchoolJ2)
    (groupA := GLM20Group.groupA) (groupB := GLM20Group.groupB)
    (populationShare := glm20Theorem3PopulationShare pi)
    (testCost := testCost) (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff) (J1DropFamily := J1DropFamily)
    (J2DropFamily := J2DropFamily) (J1KeepFamily := J1KeepFamily)
    (J2KeepFamily := J2KeepFamily)
    (J1DropThreshold := J1DropThreshold)
    (J1KeepThreshold := J1KeepThreshold)
    (J2DropThreshold := J2DropThreshold)
    (J2KeepThreshold := J2KeepThreshold)
    (hJ1_ne_J2 := glm20SchoolJ1_ne_J2) (hshareA := hshares.1)
    (hshareB := hshares.2) (hcapacity1 := hcapacity1)
    (hfillFullFull1 := hfillFullFull1)
    (hJ2SurvivorRows := hJ2SurvivorRows)

/--
Standard-Gaussian zero-fallback school-`J2` objective bridge.

This specializes
`paper_proposition5_source_family_j2_zero_fallback_school2_objective_bridge_of_base_survivor_components`
to the standard-Gaussian CDF API and hazard certificate, so paper-review
callers only see the source-family data and survivor component rows.
-/
abbrev
    paper_proposition5_standardGaussian_source_family_j2_zero_fallback_school2_objective_bridge_of_base_survivor_components
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    {capacity1 capacity2 q1Sub : ℝ} :=
  paper_proposition5_source_family_j2_zero_fallback_school2_objective_bridge_of_base_survivor_components
    (Group := Group) (School := School) (FeatureDrop := FeatureDrop)
    (FeatureKeep := FeatureKeep) (capacity1 := capacity1)
    (capacity2 := capacity2) (q1Sub := q1Sub)
    (api := standardGaussianCDFAPI)
    (C := standardGaussianHazardInverseCertificate.toGaussianHazardCertificate)

end

end GLM20DroppingStandardizedTesting
