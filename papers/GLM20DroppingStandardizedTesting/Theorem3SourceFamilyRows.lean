import GLM20DroppingStandardizedTesting.Theorem3KeepTestBundle

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Theorem 3 source-family table rows.

The generated policy-state table used by the compact Theorem 3 and
Proposition 5 routes has the paper's mass rows, base admitted-merit rows, and
the fixed-pool admitted-merit rows by definition.  This theorem exposes those
source rows as one auditable bundle for human-facing interfaces.
-/
theorem paper_theorem3_source_family_policy_state_table_surface_rows
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
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2) :
    (∀ J g,
      (glm20Theorem3SourceFamilyPolicyStateTableSurface api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold).admittedAcademicMerit J g
        (glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleSub) =
        subSubMerit J g) ∧
    (∀ g,
      (glm20Theorem3SourceFamilyPolicyStateTableSurface api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold).massTestTaking g
        (glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleSub) = subSubMass g) ∧
    (∀ g,
      (glm20Theorem3SourceFamilyPolicyStateTableSurface api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold).massTestTaking g
        (glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull) = subFullMass g) ∧
    (∀ g,
      (glm20Theorem3SourceFamilyPolicyStateTableSurface api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold).massTestTaking g
        (glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleFull
          GLM20StrategicPolicyState.singleSub) =
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw g)
          (fullSubCutoff g)) ∧
    (∀ g,
      (glm20Theorem3SourceFamilyPolicyStateTableSurface api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold).massTestTaking g
        (glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleFull
          GLM20StrategicPolicyState.singleFull) =
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw g)
          (fullFullCutoff g)) ∧
    (∀ g,
      (glm20Theorem3SourceFamilyPolicyStateTableSurface api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold).admittedAcademicMerit J1 g
        (glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull) =
        C.normalUpperTailMean (J1DropFamily g).posteriorMeanScaleLaw
          (J1DropThreshold g)) ∧
    (∀ g,
      (glm20Theorem3SourceFamilyPolicyStateTableSurface api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold).admittedAcademicMerit J2 g
        (glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull) =
        subFullMeritFallback J2 g) ∧
    (∀ g,
      (glm20Theorem3SourceFamilyPolicyStateTableSurface api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold).admittedAcademicMerit J2 g
        (glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleFull
          GLM20StrategicPolicyState.singleSub) =
        C.normalUpperTailMean (J2DropFamily g).posteriorMeanScaleLaw
          (J2DropThreshold g)) ∧
    (∀ g,
      (glm20Theorem3SourceFamilyPolicyStateTableSurface api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold).admittedAcademicMerit J1 g
        (glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleFull
          GLM20StrategicPolicyState.singleSub) =
        fullSubMeritFallback J1 g) ∧
    (∀ g,
      (glm20Theorem3SourceFamilyPolicyStateTableSurface api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold).admittedAcademicMerit J1 g
        (glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleFull
          GLM20StrategicPolicyState.singleFull) =
        C.normalUpperTailMean (J1KeepFamily g).posteriorMeanScaleLaw
          (J1KeepThreshold g)) ∧
    (∀ g,
      (glm20Theorem3SourceFamilyPolicyStateTableSurface api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold).admittedAcademicMerit J2 g
        (glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleFull
          GLM20StrategicPolicyState.singleFull) =
        C.normalUpperTailMean (J2KeepFamily g).posteriorMeanScaleLaw
          (J2KeepThreshold g)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro J g
    rfl
  · intro g
    rfl
  · intro g
    rfl
  · intro g
    rfl
  · intro g
    simp [glm20Theorem3SourceFamilyPolicyStateTableSurface,
      glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass,
      glm20StrategicSubEstimateMassAbove]
  · intro g
    change
      glm20Theorem3SourceFamilySubFullMeritTable C J1 J1DropFamily
          J1DropThreshold subFullMeritFallback J1 g =
        C.normalUpperTailMean (J1DropFamily g).posteriorMeanScaleLaw
          (J1DropThreshold g)
    simp [glm20Theorem3SourceFamilySubFullMeritTable,
      glm20OverrideSchoolMeritRow]
  · intro g
    change
      glm20Theorem3SourceFamilySubFullMeritTable C J1 J1DropFamily
          J1DropThreshold subFullMeritFallback J2 g =
        subFullMeritFallback J2 g
    simp [glm20Theorem3SourceFamilySubFullMeritTable,
      glm20OverrideSchoolMeritRow, hJ1_ne_J2.symm]
  · intro g
    change
      glm20Theorem3SourceFamilyFullSubMeritTable C J2 J2DropFamily
          J2DropThreshold fullSubMeritFallback J2 g =
        C.normalUpperTailMean (J2DropFamily g).posteriorMeanScaleLaw
          (J2DropThreshold g)
    simp [glm20Theorem3SourceFamilyFullSubMeritTable,
      glm20OverrideSchoolMeritRow]
  · intro g
    change
      glm20Theorem3SourceFamilyFullSubMeritTable C J2 J2DropFamily
          J2DropThreshold fullSubMeritFallback J1 g =
        fullSubMeritFallback J1 g
    simp [glm20Theorem3SourceFamilyFullSubMeritTable,
      glm20OverrideSchoolMeritRow, hJ1_ne_J2]
  · intro g
    change
      glm20Theorem3SourceFamilyFullFullMeritTable C J1 J2 J1KeepFamily
          J2KeepFamily J1KeepThreshold J2KeepThreshold
          fullFullMeritFallback J1 g =
        C.normalUpperTailMean (J1KeepFamily g).posteriorMeanScaleLaw
          (J1KeepThreshold g)
    simp [glm20Theorem3SourceFamilyFullFullMeritTable,
      glm20OverrideSchoolMeritRow, hJ1_ne_J2]
  · intro g
    change
      glm20Theorem3SourceFamilyFullFullMeritTable C J1 J2 J1KeepFamily
          J2KeepFamily J1KeepThreshold J2KeepThreshold
          fullFullMeritFallback J2 g =
        C.normalUpperTailMean (J2KeepFamily g).posteriorMeanScaleLaw
          (J2KeepThreshold g)
    simp [glm20Theorem3SourceFamilyFullFullMeritTable,
      glm20OverrideSchoolMeritRow]

end

end GLM20DroppingStandardizedTesting
