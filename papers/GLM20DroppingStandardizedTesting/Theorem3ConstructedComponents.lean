import GLM20DroppingStandardizedTesting.MainTheorems

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Theorem 3 source table adapter for the school-`J2` row of
`(P_sub,P_full)`.

Paper proof line for Proposition 5(i): when group `g` is the one whose pool
expands after school `J1` drops the test, no students from group `g` remain
for school `J2`.  The cutoff component of condition (10) is
`q^*_{1,sub} < q^g_{full,full}`; this adapter makes the corresponding
`J2` admitted-merit entry zero and leaves all other entries in the fallback
table.
-/
def glm20Theorem3SourceFamilySubFullJ2ZeroFallback
    {Group School : Type*} [DecidableEq School]
    (q1Sub : ℝ) (fullFullCutoff : Group → ℝ) (J2 : School)
    (fallback : School → Group → ℝ) : School → Group → ℝ := by
  classical
  exact fun J g =>
    if J = J2 then
      if q1Sub < fullFullCutoff g then 0 else fallback J g
    else
      fallback J g

@[simp] theorem
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_self_of_cutoff
    {Group School : Type*} [DecidableEq School]
    {q1Sub : ℝ} {fullFullCutoff : Group → ℝ} {J2 : School}
    {fallback : School → Group → ℝ} {g : Group}
    (hcutoff : q1Sub < fullFullCutoff g) :
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
        J2 fallback J2 g = 0 := by
  classical
  simp [glm20Theorem3SourceFamilySubFullJ2ZeroFallback, hcutoff]

@[simp] theorem
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_self_of_not_cutoff
    {Group School : Type*} [DecidableEq School]
    {q1Sub : ℝ} {fullFullCutoff : Group → ℝ} {J2 : School}
    {fallback : School → Group → ℝ} {g : Group}
    (hcutoff : ¬ q1Sub < fullFullCutoff g) :
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
        J2 fallback J2 g = fallback J2 g := by
  classical
  simp [glm20Theorem3SourceFamilySubFullJ2ZeroFallback, hcutoff]

theorem
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_cutoff_of_subFullExpands
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
    (populationShare testCost costThreshold : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    {q1Sub : ℝ} {g : Group}
    (hdrop :
      glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
        subEstimateLaw subSubMass subFullMass subSubMerit
        (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
          fullFullCutoff J2 subFullMeritBase)
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2
        groupA groupB populationShare testCost fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold q1Sub costThreshold g) :
    q1Sub < fullFullCutoff g := by
  have hcond :=
    (paper_proposition5_sourceFamilyPolicyStateTable_condition10_iff_cost_and_fullFull_cutoff_case
      api subEstimateLaw subSubMass subFullMass subSubMerit
      (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
        fullFullCutoff J2 subFullMeritBase)
      fullSubMeritFallback fullFullMeritFallback diversity J1 J2 groupA
      groupB populationShare testCost costThreshold fullFullCutoff
      fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
      J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold (q1Sub := q1Sub) (g := g)).mp hdrop
  exact hcond.2.2

theorem
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_zero_of_subFullExpands
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
    (populationShare testCost costThreshold : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    {q1Sub : ℝ} {g : Group}
    (hdrop :
      glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
        subEstimateLaw subSubMass subFullMass subSubMerit
        (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
          fullFullCutoff J2 subFullMeritBase)
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2
        groupA groupB populationShare testCost fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold q1Sub costThreshold g) :
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
        J2 subFullMeritBase J2 g = 0 := by
  classical
  have hcutoff :
      q1Sub < fullFullCutoff g :=
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_cutoff_of_subFullExpands
      api subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
      J1 J2 groupA groupB populationShare testCost costThreshold
      fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hdrop
  exact
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_self_of_cutoff
      (fallback := subFullMeritBase) hcutoff

theorem
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupB_not_cutoff_of_groupA_expands
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
    (populationShare testCost costThreshold : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    {capacity1 q1Sub : ℝ}
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
    (hdropA :
      glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
        subEstimateLaw subSubMass subFullMass subSubMerit
        (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
          fullFullCutoff J2 subFullMeritBase)
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2
        groupA groupB populationShare testCost fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold q1Sub costThreshold groupA) :
    ¬ q1Sub < fullFullCutoff groupB := by
  intro hcutB
  have hcutA :
      q1Sub < fullFullCutoff groupA :=
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_cutoff_of_subFullExpands
      api subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
      J1 J2 groupA groupB populationShare testCost costThreshold
      fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hdropA
  exact
    paper_proposition5_both_fullFull_cutoff_cases_impossible_of_weighted_capacity
      (populationShare := populationShare) (capacity := capacity1)
      (qSub := q1Sub)
      (K := fun g q =>
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw g) q)
      (massFullFull := fun g =>
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw g)
          (fullFullCutoff g))
      hshareA hshareB
      (glm20StrategicSubEstimateMassAbove_strictAnti api
        (subEstimateLaw groupA))
      (glm20StrategicSubEstimateMassAbove_strictAnti api
        (subEstimateLaw groupB))
      rfl rfl hcapacity1 hfillFullFull1 hcutA hcutB

theorem
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupA_not_cutoff_of_groupB_expands
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
    (populationShare testCost costThreshold : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    {capacity1 q1Sub : ℝ}
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
    (hdropB :
      glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
        subEstimateLaw subSubMass subFullMass subSubMerit
        (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
          fullFullCutoff J2 subFullMeritBase)
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2
        groupA groupB populationShare testCost fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold q1Sub costThreshold groupB) :
    ¬ q1Sub < fullFullCutoff groupA := by
  intro hcutA
  have hcutB :
      q1Sub < fullFullCutoff groupB :=
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_cutoff_of_subFullExpands
      api subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
      J1 J2 groupA groupB populationShare testCost costThreshold
      fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hdropB
  exact
    paper_proposition5_both_fullFull_cutoff_cases_impossible_of_weighted_capacity
      (populationShare := populationShare) (capacity := capacity1)
      (qSub := q1Sub)
      (K := fun g q =>
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw g) q)
      (massFullFull := fun g =>
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw g)
          (fullFullCutoff g))
      hshareA hshareB
      (glm20StrategicSubEstimateMassAbove_strictAnti api
        (subEstimateLaw groupA))
      (glm20StrategicSubEstimateMassAbove_strictAnti api
        (subEstimateLaw groupB))
      rfl rfl hcapacity1 hfillFullFull1 hcutA hcutB

theorem
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupB_eq_base_of_groupA_expands
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
    (populationShare testCost costThreshold : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    {capacity1 q1Sub : ℝ}
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
    (hdropA :
      glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
        subEstimateLaw subSubMass subFullMass subSubMerit
        (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
          fullFullCutoff J2 subFullMeritBase)
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2
        groupA groupB populationShare testCost fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold q1Sub costThreshold groupA) :
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
        J2 subFullMeritBase J2 groupB =
      subFullMeritBase J2 groupB := by
  classical
  exact
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_self_of_not_cutoff
      (fallback := subFullMeritBase)
      (glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupB_not_cutoff_of_groupA_expands
        api subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritBase fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare testCost
        costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
        J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold hshareA hshareB
        hcapacity1 hfillFullFull1 hdropA)

theorem
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupA_eq_base_of_groupB_expands
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
    (populationShare testCost costThreshold : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    {capacity1 q1Sub : ℝ}
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
    (hdropB :
      glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
        subEstimateLaw subSubMass subFullMass subSubMerit
        (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
          fullFullCutoff J2 subFullMeritBase)
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2
        groupA groupB populationShare testCost fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold q1Sub costThreshold groupB) :
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
        J2 subFullMeritBase J2 groupA =
      subFullMeritBase J2 groupA := by
  classical
  exact
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_self_of_not_cutoff
      (fallback := subFullMeritBase)
      (glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupA_not_cutoff_of_groupB_expands
        api subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritBase fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare testCost
        costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
        J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold hshareA hshareB
        hcapacity1 hfillFullFull1 hdropB)

theorem
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupB_merit_gt_of_base_merit_gt
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
    (populationShare testCost costThreshold : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    {capacity1 q1Sub : ℝ}
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
    (hdropA :
      glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
        subEstimateLaw subSubMass subFullMass subSubMerit
        (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
          fullFullCutoff J2 subFullMeritBase)
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2
        groupA groupB populationShare testCost fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold q1Sub costThreshold groupA)
    (hbase :
      populationShare groupB * subFullMeritBase J2 groupB >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB) :
    populationShare groupB *
        glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
          J2 subFullMeritBase J2 groupB >
      populationShare groupA * subSubMerit J2 groupA +
        populationShare groupB * subSubMerit J2 groupB := by
  rw [
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupB_eq_base_of_groupA_expands
      api subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
      J1 J2 groupA groupB populationShare testCost costThreshold
      fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hshareA hshareB hcapacity1
      hfillFullFull1 hdropA]
  exact hbase

theorem
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupA_merit_gt_of_base_merit_gt
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
    (populationShare testCost costThreshold : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    {capacity1 q1Sub : ℝ}
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
    (hdropB :
      glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
        subEstimateLaw subSubMass subFullMass subSubMerit
        (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
          fullFullCutoff J2 subFullMeritBase)
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2
        groupA groupB populationShare testCost fullFullCutoff
        fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
        J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
        J2KeepThreshold q1Sub costThreshold groupB)
    (hbase :
      populationShare groupA * subFullMeritBase J2 groupA >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB) :
    populationShare groupA *
        glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
          J2 subFullMeritBase J2 groupA >
      populationShare groupA * subSubMerit J2 groupA +
        populationShare groupB * subSubMerit J2 groupB := by
  rw [
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupA_eq_base_of_groupB_expands
      api subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
      J1 J2 groupA groupB populationShare testCost costThreshold
      fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hshareA hshareB hcapacity1
      hfillFullFull1 hdropB]
  exact hbase

/--
Proposition 5(i) source-component package for the zero-fallback `J2` row.

The current strongest Theorem 3 endpoint needs six school-`J2` component
obligations under the two possible condition-(10) branches.  With
`glm20Theorem3SourceFamilySubFullJ2ZeroFallback`, the two expanding-group zero
facts are theorem consequences of the cutoff branch.  The two surviving-group
strict-merit facts can therefore be stated on the paper's base component row,
and this package rewrites them to the actual zero-fallback source table.
-/
theorem
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_components_of_base_survivor_components
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
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    {capacity1 capacity2 q1Sub : ℝ}
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
      glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
        J2 subFullMeritBase J2 groupA = 0) ∧
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
      subFullMass groupB ≥ capacity2) ∧
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
      populationShare groupB *
          glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase J2 groupB >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB) ∧
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
      glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
        J2 subFullMeritBase J2 groupB = 0) ∧
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
      subFullMass groupA ≥ capacity2) ∧
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
      populationShare groupA *
          glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase J2 groupA >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB) := by
  constructor
  · intro costThreshold hdropA
    exact
      glm20Theorem3SourceFamilySubFullJ2ZeroFallback_zero_of_subFullExpands
        api subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritBase fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare testCost
        costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
        J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold hdropA
  constructor
  · intro costThreshold hdropA
    exact hJ2MassB_base costThreshold hdropA
  constructor
  · intro costThreshold hdropA
    exact
      glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupB_merit_gt_of_base_merit_gt
        api subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritBase fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare testCost
        costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
        J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold hshareA hshareB
        hcapacity1 hfillFullFull1 hdropA
        (hJ2MeritGtB_base costThreshold hdropA)
  constructor
  · intro costThreshold hdropB
    exact
      glm20Theorem3SourceFamilySubFullJ2ZeroFallback_zero_of_subFullExpands
        api subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritBase fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare testCost
        costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
        J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold hdropB
  constructor
  · intro costThreshold hdropB
    exact hJ2MassA_base costThreshold hdropB
  · intro costThreshold hdropB
    exact
      glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupA_merit_gt_of_base_merit_gt
        api subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritBase fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare testCost
        costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
        J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold hshareA hshareB
        hcapacity1 hfillFullFull1 hdropB
        (hJ2MeritGtA_base costThreshold hdropB)

/--
Feasibility-aware source-component package for the zero-fallback `J2` row.

The feasibility-aware Theorem 3 route keeps the surviving-group mass-fill
side inside its explicit feasibility hypothesis, so it only needs the two
expanding-group zero facts and the two strict surviving-group merit facts.
This package derives those four obligations from the source-table
zero-fallback construction and survivor merit inequalities stated on the
paper's base sub/full row.
-/
theorem
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_feasible_components_of_base_survivor_merits
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
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    {capacity1 q1Sub : ℝ}
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
            populationShare groupB * subSubMerit J2 groupB) :
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
      glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
        J2 subFullMeritBase J2 groupA = 0) ∧
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
      populationShare groupB *
          glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase J2 groupB >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB) ∧
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
      glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
        J2 subFullMeritBase J2 groupB = 0) ∧
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
      populationShare groupA *
          glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase J2 groupA >
        populationShare groupA * subSubMerit J2 groupA +
          populationShare groupB * subSubMerit J2 groupB) := by
  constructor
  · intro costThreshold hdropA
    exact
      glm20Theorem3SourceFamilySubFullJ2ZeroFallback_zero_of_subFullExpands
        api subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritBase fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare testCost
        costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
        J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold hdropA
  constructor
  · intro costThreshold hdropA
    exact
      glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupB_merit_gt_of_base_merit_gt
        api subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritBase fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare testCost
        costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
        J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold hshareA hshareB
        hcapacity1 hfillFullFull1 hdropA
        (hJ2MeritGtB_base costThreshold hdropA)
  constructor
  · intro costThreshold hdropB
    exact
      glm20Theorem3SourceFamilySubFullJ2ZeroFallback_zero_of_subFullExpands
        api subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritBase fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare testCost
        costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
        J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold hdropB
  · intro costThreshold hdropB
    exact
      glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupA_merit_gt_of_base_merit_gt
        api subEstimateLaw subSubMass subFullMass subSubMerit
        subFullMeritBase fullSubMeritFallback fullFullMeritFallback
        diversity J1 J2 groupA groupB populationShare testCost
        costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
        J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
        J1KeepThreshold J2DropThreshold J2KeepThreshold hshareA hshareB
        hcapacity1 hfillFullFull1 hdropB
        (hJ2MeritGtA_base costThreshold hdropB)

/--
School-`J2` feasibility predicate for Theorem 3(i) on the concrete
policy-state surface.

At `(P_sub,P_full)`, feasibility is exactly the paper's condition (11):
if group `A` is the condition-(10) expanding group, then group `B`'s
`(P_sub,P_full)` applicant mass can fill school `J2`, and symmetrically for
group `B`.  Other policy pairs are marked feasible here because this local
predicate is only intended to discharge the current-pair feasibility side of
the `(P_sub,P_full)` proof route.
-/
def glm20Theorem3PolicyStateSubFullJ2MassFeasible
    {Group : Type*}
    (subFullMass : Group → ℝ)
    (groupA groupB : Group)
    (testCost costThreshold fullFullCutoff : Group → ℝ)
    (capacity2 q1Sub : ℝ) :
    GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop
  | .singleSub, .singleFull =>
      (testCost groupA ≥ costThreshold groupA ∧
          0 < costThreshold groupA ∧ q1Sub < fullFullCutoff groupA →
        subFullMass groupB ≥ capacity2) ∧
      (testCost groupB ≥ costThreshold groupB ∧
          0 < costThreshold groupB ∧ q1Sub < fullFullCutoff groupB →
        subFullMass groupA ≥ capacity2)
  | _, _ => True

@[simp] theorem
    glm20Theorem3PolicyStateSubFullJ2MassFeasible_subFull
    {Group : Type*}
    (subFullMass : Group → ℝ)
    (groupA groupB : Group)
    (testCost costThreshold fullFullCutoff : Group → ℝ)
    (capacity2 q1Sub : ℝ) :
    glm20Theorem3PolicyStateSubFullJ2MassFeasible subFullMass groupA groupB
        testCost costThreshold fullFullCutoff capacity2 q1Sub
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull =
      ((testCost groupA ≥ costThreshold groupA ∧
          0 < costThreshold groupA ∧ q1Sub < fullFullCutoff groupA →
        subFullMass groupB ≥ capacity2) ∧
      (testCost groupB ≥ costThreshold groupB ∧
          0 < costThreshold groupB ∧ q1Sub < fullFullCutoff groupB →
        subFullMass groupA ≥ capacity2)) := rfl

@[simp] theorem
    glm20Theorem3PolicyStateSubFullJ2MassFeasible_subSub
    {Group : Type*}
    (subFullMass : Group → ℝ)
    (groupA groupB : Group)
    (testCost costThreshold fullFullCutoff : Group → ℝ)
    (capacity2 q1Sub : ℝ) :
    glm20Theorem3PolicyStateSubFullJ2MassFeasible subFullMass groupA groupB
        testCost costThreshold fullFullCutoff capacity2 q1Sub
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleSub = True := rfl

@[simp] theorem
    glm20Theorem3PolicyStateSubFullJ2MassFeasible_fullSub
    {Group : Type*}
    (subFullMass : Group → ℝ)
    (groupA groupB : Group)
    (testCost costThreshold fullFullCutoff : Group → ℝ)
    (capacity2 q1Sub : ℝ) :
    glm20Theorem3PolicyStateSubFullJ2MassFeasible subFullMass groupA groupB
        testCost costThreshold fullFullCutoff capacity2 q1Sub
        GLM20StrategicPolicyState.singleFull
        GLM20StrategicPolicyState.singleSub = True := rfl

@[simp] theorem
    glm20Theorem3PolicyStateSubFullJ2MassFeasible_fullFull
    {Group : Type*}
    (subFullMass : Group → ℝ)
    (groupA groupB : Group)
    (testCost costThreshold fullFullCutoff : Group → ℝ)
    (capacity2 q1Sub : ℝ) :
    glm20Theorem3PolicyStateSubFullJ2MassFeasible subFullMass groupA groupB
        testCost costThreshold fullFullCutoff capacity2 q1Sub
        GLM20StrategicPolicyState.singleFull
        GLM20StrategicPolicyState.singleFull = True := rfl

/--
The concrete school-`J2` feasibility predicate is equivalent to the
condition-(11) mass implications used by the feasibility-aware Theorem 3
wrapper.
-/
theorem
    glm20Theorem3PolicyStateSubFullJ2MassFeasible_iff_sourceFamilySubFullExpands
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
    (populationShare testCost costThreshold : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    {capacity2 q1Sub : ℝ} :
    glm20Theorem3PolicyStateSubFullJ2MassFeasible subFullMass groupA groupB
        testCost costThreshold fullFullCutoff capacity2 q1Sub
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      (glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase)
          fullSubMeritFallback fullFullMeritFallback diversity J1 J2
          groupA groupB populationShare testCost fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold q1Sub costThreshold groupA →
        subFullMass groupB ≥ capacity2) ∧
      (glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase)
          fullSubMeritFallback fullFullMeritFallback diversity J1 J2
          groupA groupB populationShare testCost fullFullCutoff
          fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
          J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
          J2KeepThreshold q1Sub costThreshold groupB →
        subFullMass groupA ≥ capacity2) := by
  constructor
  · rintro ⟨hA, hB⟩
    constructor
    · intro hdropA
      have hcut :
          testCost groupA ≥ costThreshold groupA ∧
            0 < costThreshold groupA ∧ q1Sub < fullFullCutoff groupA :=
        (paper_proposition5_sourceFamilyPolicyStateTable_condition10_iff_cost_and_fullFull_cutoff_case
          api subEstimateLaw subSubMass subFullMass subSubMerit
          (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase)
          fullSubMeritFallback fullFullMeritFallback diversity J1 J2
          groupA groupB populationShare testCost costThreshold
          fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
          J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
          J2DropThreshold J2KeepThreshold
          (q1Sub := q1Sub) (g := groupA)).mp hdropA
      exact hA hcut
    · intro hdropB
      have hcut :
          testCost groupB ≥ costThreshold groupB ∧
            0 < costThreshold groupB ∧ q1Sub < fullFullCutoff groupB :=
        (paper_proposition5_sourceFamilyPolicyStateTable_condition10_iff_cost_and_fullFull_cutoff_case
          api subEstimateLaw subSubMass subFullMass subSubMerit
          (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase)
          fullSubMeritFallback fullFullMeritFallback diversity J1 J2
          groupA groupB populationShare testCost costThreshold
          fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
          J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
          J2DropThreshold J2KeepThreshold
          (q1Sub := q1Sub) (g := groupB)).mp hdropB
      exact hB hcut
  · rintro ⟨hA, hB⟩
    constructor
    · intro hcutA
      exact hA
        ((paper_proposition5_sourceFamilyPolicyStateTable_condition10_iff_cost_and_fullFull_cutoff_case
          api subEstimateLaw subSubMass subFullMass subSubMerit
          (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase)
          fullSubMeritFallback fullFullMeritFallback diversity J1 J2
          groupA groupB populationShare testCost costThreshold
          fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
          J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
          J2DropThreshold J2KeepThreshold
          (q1Sub := q1Sub) (g := groupA)).mpr hcutA)
    · intro hcutB
      exact hB
        ((paper_proposition5_sourceFamilyPolicyStateTable_condition10_iff_cost_and_fullFull_cutoff_case
          api subEstimateLaw subSubMass subFullMass subSubMerit
          (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase)
          fullSubMeritFallback fullFullMeritFallback diversity J1 J2
          groupA groupB populationShare testCost costThreshold
          fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
          J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
          J2DropThreshold J2KeepThreshold
          (q1Sub := q1Sub) (g := groupB)).mpr hcutB)

/--
Policy-state version of
`glm20Theorem3PolicyStateSubFullJ2MassFeasible_iff_sourceFamilySubFullExpands`.

This is the exact bridge needed by the feasibility-aware binary game: once the
policy-state mass table is the paper's `K_g` cutoff table, the concrete
school-`J2` feasibility predicate at `(P_sub,P_full)` is equivalent to the
two condition-(11) mass implications.
-/
theorem
    glm20Theorem3PolicyStateSubFullJ2MassFeasible_iff_policyStateExpands
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost costThreshold : Group → ℝ)
    {capacity2 q1Sub : ℝ} :
    glm20Theorem3PolicyStateSubFullJ2MassFeasible subFullMass groupA groupB
        testCost costThreshold fullFullCutoff capacity2 q1Sub
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      (glm20Theorem3SubFullGroupExpandsByDropping
          (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
            groupB populationShare)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)
          groupA →
        (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
          subEstimateLaw subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare).massTestTaking groupB
          (glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) ≥ capacity2) ∧
      (glm20Theorem3SubFullGroupExpandsByDropping
          (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
            groupB populationShare)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)
          groupB →
        (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
          subEstimateLaw subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare).massTestTaking groupA
          (glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) ≥ capacity2) := by
  constructor
  · rintro ⟨hA, hB⟩
    constructor
    · intro hdropA
      have hcut :
          testCost groupA ≥ costThreshold groupA ∧
            0 < costThreshold groupA ∧ q1Sub < fullFullCutoff groupA :=
        (paper_proposition5_policyState_condition10_iff_cost_and_fullFull_cutoff_case
          api subEstimateLaw subSubMass subFullMass admittedAcademicMerit
          diversity J1 J2 groupA groupB populationShare
          (testCost := testCost) (costThreshold := costThreshold)
          (q1Sub := q1Sub) (fullFullCutoff := fullFullCutoff)
          (fullSubCutoff := fullSubCutoff) (g := groupA)).mp hdropA
      simpa [glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass]
        using hA hcut
    · intro hdropB
      have hcut :
          testCost groupB ≥ costThreshold groupB ∧
            0 < costThreshold groupB ∧ q1Sub < fullFullCutoff groupB :=
        (paper_proposition5_policyState_condition10_iff_cost_and_fullFull_cutoff_case
          api subEstimateLaw subSubMass subFullMass admittedAcademicMerit
          diversity J1 J2 groupA groupB populationShare
          (testCost := testCost) (costThreshold := costThreshold)
          (q1Sub := q1Sub) (fullFullCutoff := fullFullCutoff)
          (fullSubCutoff := fullSubCutoff) (g := groupB)).mp hdropB
      simpa [glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass]
        using hB hcut
  · rintro ⟨hA, hB⟩
    constructor
    · intro hcutA
      have hdropA :
          glm20Theorem3SubFullGroupExpandsByDropping
            (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
              subEstimateLaw subSubMass subFullMass fullFullCutoff
              fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
              groupB populationShare)
            glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull testCost costThreshold q1Sub
            (fun g q => glm20StrategicSubEstimateMassAbove api
              (subEstimateLaw g) q)
            groupA :=
        (paper_proposition5_policyState_condition10_iff_cost_and_fullFull_cutoff_case
          api subEstimateLaw subSubMass subFullMass admittedAcademicMerit
          diversity J1 J2 groupA groupB populationShare
          (testCost := testCost) (costThreshold := costThreshold)
          (q1Sub := q1Sub) (fullFullCutoff := fullFullCutoff)
          (fullSubCutoff := fullSubCutoff) (g := groupA)).mpr hcutA
      simpa [glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass]
        using hA hdropA
    · intro hcutB
      have hdropB :
          glm20Theorem3SubFullGroupExpandsByDropping
            (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
              subEstimateLaw subSubMass subFullMass fullFullCutoff
              fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
              groupB populationShare)
            glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull testCost costThreshold q1Sub
            (fun g q => glm20StrategicSubEstimateMassAbove api
              (subEstimateLaw g) q)
            groupB :=
        (paper_proposition5_policyState_condition10_iff_cost_and_fullFull_cutoff_case
          api subEstimateLaw subSubMass subFullMass admittedAcademicMerit
          diversity J1 J2 groupA groupB populationShare
          (testCost := testCost) (costThreshold := costThreshold)
          (q1Sub := q1Sub) (fullFullCutoff := fullFullCutoff)
          (fullSubCutoff := fullSubCutoff) (g := groupB)).mpr hcutB
      simpa [glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass]
        using hB hdropB

/--
Concrete feasible policy-state surface for Theorem 3(i).

School `J1` is feasible at every binary policy pair.  School `J2` uses the
paper's condition-(11) survivor-mass feasibility predicate at
`(P_sub,P_full)` and is otherwise locally feasible.  This surface is useful
when the cost threshold in condition (10) is already fixed.
-/
def glm20Theorem3PolicyStateSubFullMassFeasibleSurface
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost costThreshold : Group → ℝ)
    (capacity2 q1Sub : ℝ) :
    GLM20StrategicPolicySurface Group GLM20StrategicPolicyState School
      (GLM20StrategicPolicyState × GLM20StrategicPolicyState) :=
  glm20FeasibleWeightedAcademicMeritBinaryPolicySurface
    (glm20Theorem3PolicyStateCutoffMass api subEstimateLaw subSubMass
      subFullMass fullFullCutoff fullSubCutoff)
    admittedAcademicMerit diversity glm20StrategicPolicyStatePair
    GLM20StrategicPolicyState.singleSub
    GLM20StrategicPolicyState.singleFull J1 J2 groupA groupB
    populationShare
    (fun _ _ => True)
    (glm20Theorem3PolicyStateSubFullJ2MassFeasible subFullMass groupA groupB
      testCost costThreshold fullFullCutoff capacity2 q1Sub)

/--
The concrete Theorem 3(i) feasible policy-state surface unfolds to exactly the
school-`J2` condition-(11) mass implications plus the two weighted
academic-merit best-response comparisons.
-/
theorem
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface_subFull_iff_components
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost costThreshold : Group → ℝ)
    {capacity2 q1Sub : ℝ} :
    let S :=
      glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
        subSubMass subFullMass fullFullCutoff fullSubCutoff
        admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
        testCost costThreshold capacity2 q1Sub
    S.policyPairIsEquilibrium GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      ((testCost groupA ≥ costThreshold groupA ∧
            0 < costThreshold groupA ∧ q1Sub < fullFullCutoff groupA →
          subFullMass groupB ≥ capacity2) ∧
        (testCost groupB ≥ costThreshold groupB ∧
            0 < costThreshold groupB ∧ q1Sub < fullFullCutoff groupB →
          subFullMass groupA ≥ capacity2)) ∧
      glm20TwoGroupWeightedAcademicMeritObjective S
          glm20StrategicPolicyStatePair J1 groupA groupB populationShare
          GLM20StrategicPolicyState.singleFull
          GLM20StrategicPolicyState.singleFull ≤
        glm20TwoGroupWeightedAcademicMeritObjective S
          glm20StrategicPolicyStatePair J1 groupA groupB populationShare
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull ∧
      glm20TwoGroupWeightedAcademicMeritObjective S
          glm20StrategicPolicyStatePair J2 groupA groupB populationShare
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleSub ≤
        glm20TwoGroupWeightedAcademicMeritObjective S
          glm20StrategicPolicyStatePair J2 groupA groupB populationShare
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull := by
  simp [glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
    glm20FeasibleWeightedAcademicMeritBinaryPolicySurface_subFull_iff,
    glm20Theorem3PolicyStateSubFullJ2MassFeasible]

/--
Concrete Theorem 3(i) feasible-surface bridge for a fixed condition-(10)
threshold.

Once the Proposition 5 objective work has shown that the two unilateral
weighted-academic-merit comparisons are equivalent to the paper's
condition-(10)--(12) predicate, the concrete condition-(11) feasibility
surface has `(P_sub,P_full)` as an equilibrium exactly when Theorem 3(i)'s
sub/full condition holds.  This removes the generic `feasible1`/`feasible2`
bookkeeping from the paper-facing sub/full proof seam.
-/
theorem
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface_subFull_iff_theorem3Condition
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost costThreshold : Group → ℝ)
    {capacity2 q1Sub : ℝ}
    (hobjective :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost costThreshold capacity2 q1Sub
      ((glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB
            populationShare GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleFull ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB
            populationShare GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) ∧
        (glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J2 groupA groupB
            populationShare GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J2 groupA groupB
            populationShare GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull)) ↔
        glm20Theorem3SubFullCondition S glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare testCost costThreshold capacity2 q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)) :
    let S :=
      glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
        subSubMass subFullMass fullFullCutoff fullSubCutoff
        admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
        testCost costThreshold capacity2 q1Sub
    S.policyPairIsEquilibrium GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      glm20Theorem3SubFullCondition S glm20StrategicPolicyStatePair
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull J2 groupA groupB
        populationShare testCost costThreshold capacity2 q1Sub
        (fun g q => glm20StrategicSubEstimateMassAbove api
          (subEstimateLaw g) q) := by
  let feasible2 :=
    glm20Theorem3PolicyStateSubFullJ2MassFeasible subFullMass groupA groupB
      testCost costThreshold fullFullCutoff capacity2 q1Sub
  exact
    paper_theorem3_subFull_condition_of_feasible_weighted_surface_objective_pair_bridge
      (S := glm20Theorem3PolicyStateSubFullMassFeasibleSurface api
        subEstimateLaw subSubMass subFullMass fullFullCutoff fullSubCutoff
        admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
        testCost costThreshold capacity2 q1Sub)
      (massTestTaking :=
        glm20Theorem3PolicyStateCutoffMass api subEstimateLaw subSubMass
          subFullMass fullFullCutoff fullSubCutoff)
      (admittedAcademicMerit := admittedAcademicMerit)
      (diversity := diversity)
      (policyPair := glm20StrategicPolicyStatePair)
      (Psub := GLM20StrategicPolicyState.singleSub)
      (Pfull := GLM20StrategicPolicyState.singleFull)
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (costThreshold := costThreshold) (capacity2 := capacity2)
      (q1Sub := q1Sub)
      (K := fun g q => glm20StrategicSubEstimateMassAbove api
        (subEstimateLaw g) q)
      (feasible1 := fun _ _ => True) (feasible2 := feasible2)
      (hS := by rfl)
      (hfeasible1SubFull := trivial)
      (hfeasible1FullFull := trivial)
      (hfeasible2SubSub := by
        simp [feasible2])
      (hfeasible2SubFull := by
        simpa [feasible2, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
          glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
          glm20WeightedAcademicMeritBinaryPolicySurface,
          glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
          using
            (glm20Theorem3PolicyStateSubFullJ2MassFeasible_iff_policyStateExpands
              api subEstimateLaw subSubMass subFullMass fullFullCutoff
              fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
              groupB populationShare testCost costThreshold
              (capacity2 := capacity2) (q1Sub := q1Sub)))
      hobjective

/--
Concrete Theorem 3(i) feasible-surface bridge with condition (11) supplied by
the surface itself.

This is the preferred fixed-threshold endpoint for the paper proof.  The
school-`J1` objective comparison supplies condition (10), the two school-`J2`
objective bridges supply condition (12), and the concrete feasibility predicate
on school `J2` supplies condition (11).
-/
theorem
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface_subFull_iff_theorem3Condition_of_objective_bridges
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost costThreshold : Group → ℝ)
    {capacity2 q1Sub : ℝ}
    (hJ1 :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost costThreshold capacity2 q1Sub
      (glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB
            populationShare GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleFull ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB
            populationShare GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) ↔
        glm20ExactlyOneOfTwo groupA groupB
          (glm20Theorem3SubFullGroupExpandsByDropping S
            glm20StrategicPolicyStatePair
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull testCost costThreshold
            q1Sub
            (fun g q => glm20StrategicSubEstimateMassAbove api
              (subEstimateLaw g) q)))
    (hJ2A_merit :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost costThreshold capacity2 q1Sub
      glm20Theorem3SubFullGroupExpandsByDropping S
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)
          groupA →
        ((glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J2 groupA groupB
            populationShare GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J2 groupA groupB
            populationShare GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) ↔
          populationShare groupB *
              S.admittedAcademicMerit J2 groupB
                (glm20StrategicPolicyStatePair
                  GLM20StrategicPolicyState.singleSub
                  GLM20StrategicPolicyState.singleFull) >
            populationShare groupA *
                S.admittedAcademicMerit J2 groupA
                  (glm20StrategicPolicyStatePair
                    GLM20StrategicPolicyState.singleSub
                    GLM20StrategicPolicyState.singleSub) +
              populationShare groupB *
                S.admittedAcademicMerit J2 groupB
                  (glm20StrategicPolicyStatePair
                    GLM20StrategicPolicyState.singleSub
                    GLM20StrategicPolicyState.singleSub)))
    (hJ2B_merit :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost costThreshold capacity2 q1Sub
      glm20Theorem3SubFullGroupExpandsByDropping S
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)
          groupB →
        ((glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J2 groupA groupB
            populationShare GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J2 groupA groupB
            populationShare GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) ↔
          populationShare groupA *
              S.admittedAcademicMerit J2 groupA
                (glm20StrategicPolicyStatePair
                  GLM20StrategicPolicyState.singleSub
                  GLM20StrategicPolicyState.singleFull) >
            populationShare groupA *
                S.admittedAcademicMerit J2 groupA
                  (glm20StrategicPolicyStatePair
                    GLM20StrategicPolicyState.singleSub
                    GLM20StrategicPolicyState.singleSub) +
              populationShare groupB *
                S.admittedAcademicMerit J2 groupB
                  (glm20StrategicPolicyStatePair
                    GLM20StrategicPolicyState.singleSub
                    GLM20StrategicPolicyState.singleSub))) :
    let S :=
      glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
        subSubMass subFullMass fullFullCutoff fullSubCutoff
        admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
        testCost costThreshold capacity2 q1Sub
    S.policyPairIsEquilibrium GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      glm20Theorem3SubFullCondition S glm20StrategicPolicyStatePair
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull J2 groupA groupB
        populationShare testCost costThreshold capacity2 q1Sub
        (fun g q => glm20StrategicSubEstimateMassAbove api
          (subEstimateLaw g) q) := by
  let feasible2 :=
    glm20Theorem3PolicyStateSubFullJ2MassFeasible subFullMass groupA groupB
      testCost costThreshold fullFullCutoff capacity2 q1Sub
  exact
    paper_theorem3_subFull_condition_of_feasible_weighted_surface_objective_mass_bridges
      (S := glm20Theorem3PolicyStateSubFullMassFeasibleSurface api
        subEstimateLaw subSubMass subFullMass fullFullCutoff fullSubCutoff
        admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
        testCost costThreshold capacity2 q1Sub)
      (massTestTaking :=
        glm20Theorem3PolicyStateCutoffMass api subEstimateLaw subSubMass
          subFullMass fullFullCutoff fullSubCutoff)
      (admittedAcademicMerit := admittedAcademicMerit)
      (diversity := diversity)
      (policyPair := glm20StrategicPolicyStatePair)
      (Psub := GLM20StrategicPolicyState.singleSub)
      (Pfull := GLM20StrategicPolicyState.singleFull)
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (costThreshold := costThreshold) (capacity2 := capacity2)
      (q1Sub := q1Sub)
      (K := fun g q => glm20StrategicSubEstimateMassAbove api
        (subEstimateLaw g) q)
      (feasible1 := fun _ _ => True) (feasible2 := feasible2)
      (hS := by rfl)
      (hfeasible1SubFull := trivial)
      (hfeasible1FullFull := trivial)
      (hfeasible2SubSub := by simp [feasible2])
      (hfeasible2SubFull := by
        simpa [feasible2, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
          glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
          glm20WeightedAcademicMeritBinaryPolicySurface,
          glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
          using
            (glm20Theorem3PolicyStateSubFullJ2MassFeasible_iff_policyStateExpands
              api subEstimateLaw subSubMass subFullMass fullFullCutoff
              fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
              groupB populationShare testCost costThreshold
              (capacity2 := capacity2) (q1Sub := q1Sub)))
      hJ1 hJ2A_merit hJ2B_merit

/--
Concrete Theorem 3(i) positive-interval endpoint for the policy-state
condition-(11) feasible surface.

This constructs the paper's cost threshold from the Proposition 5(i) monotone
merit crossing on a positive interval, proves the school-`J1` objective
case split, and then applies the concrete feasibility surface so condition
(11)'s survivor-mass requirements are part of the equilibrium predicate rather
than external feasibility assumptions.
-/
theorem
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface_subFull_interval
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost leftCost rightCost : Group → ℝ)
    {capacity1 capacity2 q1Sub : ℝ}
    (testBasedMerit : Group → ℝ → ℝ)
    (testFreeMerit : Group → ℝ)
    (hleftRight : ∀ g, leftCost g < rightCost g)
    (hleftPos : ∀ g, 0 < leftCost g)
    (hcostMem :
      ∀ g, testCost g ∈ Set.Icc (leftCost g) (rightCost g))
    (hcont :
      ∀ g, ContinuousOn (testBasedMerit g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hanti :
      ∀ g, StrictAntiOn (testBasedMerit g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hlowCost :
      ∀ g, testFreeMerit g < testBasedMerit g (leftCost g))
    (hhighCost :
      ∀ g, testBasedMerit g (rightCost g) < testFreeMerit g)
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
    (hfixedPoolMeritA :
      ¬ q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          admittedAcademicMerit J1 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) <
            admittedAcademicMerit J1 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull))
    (hfixedPoolMeritB :
      ¬ q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          admittedAcademicMerit J1 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) <
            admittedAcademicMerit J1 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull))
    (honlyA_J1_groupB_eq :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          admittedAcademicMerit J1 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            admittedAcademicMerit J1 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull))
    (honlyA_J1_groupA_testBased :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          admittedAcademicMerit J1 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            testBasedMerit groupA (testCost groupA))
    (honlyA_J1_groupA_testFree :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          admittedAcademicMerit J1 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) =
            testFreeMerit groupA)
    (honlyB_J1_groupA_eq :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          admittedAcademicMerit J1 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            admittedAcademicMerit J1 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull))
    (honlyB_J1_groupB_testBased :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          admittedAcademicMerit J1 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            testBasedMerit groupB (testCost groupB))
    (honlyB_J1_groupB_testFree :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          admittedAcademicMerit J1 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) =
            testFreeMerit groupB)
    (hJ2ZeroA :
      ∀ costThreshold : Group → ℝ,
      glm20Theorem3SubFullGroupExpandsByDropping
          (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
            groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)
          groupA →
        admittedAcademicMerit J2 groupA
          (glm20StrategicPolicyStatePair
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) = 0)
    (hJ2NotTieB :
      ∀ costThreshold : Group → ℝ,
      glm20Theorem3SubFullGroupExpandsByDropping
          (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
            groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)
          groupA →
        populationShare groupB *
            admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) ≠
          populationShare groupA *
              admittedAcademicMerit J2 groupA
                (glm20StrategicPolicyStatePair
                  GLM20StrategicPolicyState.singleSub
                  GLM20StrategicPolicyState.singleSub) +
            populationShare groupB *
              admittedAcademicMerit J2 groupB
                (glm20StrategicPolicyStatePair
                  GLM20StrategicPolicyState.singleSub
                  GLM20StrategicPolicyState.singleSub))
    (hJ2ZeroB :
      ∀ costThreshold : Group → ℝ,
      glm20Theorem3SubFullGroupExpandsByDropping
          (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
            groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)
          groupB →
        admittedAcademicMerit J2 groupB
          (glm20StrategicPolicyStatePair
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) = 0)
    (hJ2NotTieA :
      ∀ costThreshold : Group → ℝ,
      glm20Theorem3SubFullGroupExpandsByDropping
          (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
            groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)
          groupB →
        populationShare groupA *
            admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) ≠
          populationShare groupA *
              admittedAcademicMerit J2 groupA
                (glm20StrategicPolicyStatePair
                  GLM20StrategicPolicyState.singleSub
                  GLM20StrategicPolicyState.singleSub) +
            populationShare groupB *
              admittedAcademicMerit J2 groupB
                (glm20StrategicPolicyStatePair
                  GLM20StrategicPolicyState.singleSub
                  GLM20StrategicPolicyState.singleSub)) :
    ∃ costThreshold : Group → ℝ,
      (∀ g, costThreshold g ∈ Set.Ioo (leftCost g) (rightCost g)) ∧
        (∀ g, testBasedMerit g (costThreshold g) = testFreeMerit g) ∧
          (∀ g c, c ∈ Set.Icc (leftCost g) (rightCost g) →
            (testBasedMerit g c ≤ testFreeMerit g ↔
              costThreshold g ≤ c)) ∧
            let S :=
              glm20Theorem3PolicyStateSubFullMassFeasibleSurface api
                subEstimateLaw subSubMass subFullMass fullFullCutoff
                fullSubCutoff admittedAcademicMerit diversity J1 J2
                groupA groupB populationShare testCost costThreshold
                capacity2 q1Sub
            S.policyPairIsEquilibrium GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull ↔
              glm20Theorem3SubFullCondition S glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull J2 groupA groupB
                populationShare testCost costThreshold capacity2 q1Sub
                (fun g q => glm20StrategicSubEstimateMassAbove api
                  (subEstimateLaw g) q) := by
  let BaseS :=
    glm20Theorem3PolicyStateWeightedAcademicMeritSurface api subEstimateLaw
      subSubMass subFullMass fullFullCutoff fullSubCutoff
      admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
  let K := fun g q =>
    glm20StrategicSubEstimateMassAbove api (subEstimateLaw g) q
  let objective1 : GLM20StrategicPolicyState → GLM20StrategicPolicyState → ℝ :=
    glm20TwoGroupWeightedAcademicMeritObjective BaseS
      glm20StrategicPolicyStatePair J1 groupA groupB populationShare
  let objective2 : GLM20StrategicPolicyState → GLM20StrategicPolicyState → ℝ :=
    glm20TwoGroupWeightedAcademicMeritObjective BaseS
      glm20StrategicPolicyStatePair J2 groupA groupB populationShare
  have hmassFullFullA :
      BaseS.massTestTaking groupA
          (glm20StrategicPolicyStatePair
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleFull) =
        K groupA (fullFullCutoff groupA) := by
    simp [BaseS, K, glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass,
      glm20StrategicSubEstimateMassAbove]
  have hmassFullFullB :
      BaseS.massTestTaking groupB
          (glm20StrategicPolicyStatePair
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleFull) =
        K groupB (fullFullCutoff groupB) := by
    simp [BaseS, K, glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass,
      glm20StrategicSubEstimateMassAbove]
  have hfillFullFull1Base :
      capacity1 ≤
        populationShare groupA *
            BaseS.massTestTaking groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) +
          populationShare groupB *
            BaseS.massTestTaking groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) := by
    simpa [BaseS, K, glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass,
      glm20StrategicSubEstimateMassAbove]
      using hfillFullFull1
  have hbothJ1_impossible :
      q1Sub < fullFullCutoff groupA →
        q1Sub < fullFullCutoff groupB → False :=
    paper_proposition5_part_i_both_fullFull_cutoff_cases_impossible_of_capacity
      (S := BaseS) (policyPair := glm20StrategicPolicyStatePair)
      (Pfull := GLM20StrategicPolicyState.singleFull)
      (populationShare := populationShare) (capacity1 := capacity1)
      (q1Sub := q1Sub) api subEstimateLaw hshareA hshareB
      hmassFullFullA hmassFullFullB hcapacity1 hfillFullFull1Base
  have hnoneJ1 :
      ¬ q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          ¬ objective1 GLM20StrategicPolicyState.singleFull
              GLM20StrategicPolicyState.singleFull ≤
            objective1 GLM20StrategicPolicyState.singleSub
              GLM20StrategicPolicyState.singleFull :=
    paper_proposition5_no_group_expands_no_drop_of_weighted_groupwise_merit_lt
      (S := BaseS) (policyPair := glm20StrategicPolicyStatePair) (J := J1)
      (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare)
      (Pdrop1 := GLM20StrategicPolicyState.singleSub)
      (Pdrop2 := GLM20StrategicPolicyState.singleFull)
      (Pkeep1 := GLM20StrategicPolicyState.singleFull)
      (Pkeep2 := GLM20StrategicPolicyState.singleFull) (q := q1Sub)
      (cutoff := fullFullCutoff) hshareA hshareB
      (by
        intro hA hB
        simpa [BaseS, glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
          glm20WeightedAcademicMeritBinaryPolicySurface]
          using hfixedPoolMeritA hA hB)
      (by
        intro hA hB
        simpa [BaseS, glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
          glm20WeightedAcademicMeritBinaryPolicySurface]
          using hfixedPoolMeritB hA hB)
  have honlyA_J1_merit :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          ((objective1 GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull ≤
              objective1 GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) ↔
            testBasedMerit groupA (testCost groupA) ≤
              testFreeMerit groupA) := by
    intro hcut hnot
    exact
      glm20TwoGroupWeightedAcademicMeritObjective_le_iff_groupA_formula_of_groupB_eq
        BaseS glm20StrategicPolicyStatePair J1 groupA groupB
        populationShare GLM20StrategicPolicyState.singleFull
        GLM20StrategicPolicyState.singleFull
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull hshareA
        (by
          simpa [BaseS, glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface]
            using honlyA_J1_groupB_eq hcut hnot)
        (by
          simpa [BaseS, glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface]
            using honlyA_J1_groupA_testBased hcut hnot)
        (by
          simpa [BaseS, glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface]
            using honlyA_J1_groupA_testFree hcut hnot)
  have honlyB_J1_merit :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          ((objective1 GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull ≤
              objective1 GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) ↔
            testBasedMerit groupB (testCost groupB) ≤
              testFreeMerit groupB) := by
    intro hcut hnot
    exact
      glm20TwoGroupWeightedAcademicMeritObjective_le_iff_groupB_formula_of_groupA_eq
        BaseS glm20StrategicPolicyStatePair J1 groupA groupB
        populationShare GLM20StrategicPolicyState.singleFull
        GLM20StrategicPolicyState.singleFull
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull hshareB
        (by
          simpa [BaseS, glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface]
            using honlyB_J1_groupA_eq hcut hnot)
        (by
          simpa [BaseS, glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface]
            using honlyB_J1_groupB_testBased hcut hnot)
        (by
          simpa [BaseS, glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface]
            using honlyB_J1_groupB_testFree hcut hnot)
  rcases
    paper_proposition5_part_i_school1_cutoff_objective_iff_exactly_one_cost_case_of_merit_crossings_interval
      objective1 testBasedMerit testFreeMerit hleftRight hleftPos hcostMem
      hcont hanti hlowCost hhighCost
      hnoneJ1 hbothJ1_impossible honlyA_J1_merit honlyB_J1_merit with
    ⟨costThreshold, hmem, heq, hle, hJ1Cutoff⟩
  let S :=
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
      subSubMass subFullMass fullFullCutoff fullSubCutoff
      admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
      testCost costThreshold capacity2 q1Sub
  have hJ1 :
      (glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleFull ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) ↔
        glm20ExactlyOneOfTwo groupA groupB
          (glm20Theorem3SubFullGroupExpandsByDropping S
            glm20StrategicPolicyStatePair
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull testCost costThreshold
            q1Sub K) := by
    have hbase :
        (objective1 GLM20StrategicPolicyState.singleFull
              GLM20StrategicPolicyState.singleFull ≤
            objective1 GLM20StrategicPolicyState.singleSub
              GLM20StrategicPolicyState.singleFull) ↔
          glm20ExactlyOneOfTwo groupA groupB
            (glm20Theorem3SubFullGroupExpandsByDropping BaseS
              glm20StrategicPolicyStatePair
              GLM20StrategicPolicyState.singleSub
              GLM20StrategicPolicyState.singleFull testCost costThreshold
              q1Sub K) :=
      paper_proposition5_part_i_school1_objective_iff_condition10_of_cutoff_cases
        BaseS glm20StrategicPolicyStatePair
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull api subEstimateLaw objective1
        hmassFullFullA hmassFullFullB hJ1Cutoff
    simpa [S, BaseS, K, objective1,
      glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
      glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
      glm20WeightedAcademicMeritBinaryPolicySurface,
      glm20FeasibleWeightedAcademicMeritBinaryPolicySurface,
      glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass]
      using hbase
  have hJ2A_merit :
      glm20Theorem3SubFullGroupExpandsByDropping S
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub K groupA →
        ((glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J2 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J2 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) ↔
          populationShare groupB *
              S.admittedAcademicMerit J2 groupB
                (glm20StrategicPolicyStatePair
                  GLM20StrategicPolicyState.singleSub
                  GLM20StrategicPolicyState.singleFull) >
            populationShare groupA *
                S.admittedAcademicMerit J2 groupA
                  (glm20StrategicPolicyStatePair
                    GLM20StrategicPolicyState.singleSub
                    GLM20StrategicPolicyState.singleSub) +
              populationShare groupB *
                S.admittedAcademicMerit J2 groupB
                  (glm20StrategicPolicyStatePair
                    GLM20StrategicPolicyState.singleSub
                    GLM20StrategicPolicyState.singleSub)) := by
    intro hdropA
    have hdropA_base :
        glm20Theorem3SubFullGroupExpandsByDropping BaseS
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub K groupA := by
      simpa [S, BaseS, K, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20FeasibleWeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass]
        using hdropA
    exact
      paper_theorem3_school2_objective_iff_single_group_merit_gt_of_no_tie
        S glm20StrategicPolicyStatePair
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull J2 groupA groupB groupB
        populationShare
        (glm20TwoGroupWeightedAcademicMeritObjective S
          glm20StrategicPolicyStatePair J2 groupA groupB populationShare)
        (glm20TwoGroupWeightedAcademicMeritObjective_eq_groupB_of_groupA_zero
          S glm20StrategicPolicyStatePair J2 groupA groupB populationShare
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull
          (by
            simpa [S, BaseS,
              glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
              glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
              glm20WeightedAcademicMeritBinaryPolicySurface,
              glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
              using Or.inr (hJ2ZeroA costThreshold hdropA_base)))
        (by rfl)
        (by
          simpa [S, BaseS,
            glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
            glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface,
            glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
            using hJ2NotTieB costThreshold hdropA_base)
  have hJ2B_merit :
      glm20Theorem3SubFullGroupExpandsByDropping S
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub K groupB →
        ((glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J2 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J2 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) ↔
          populationShare groupA *
              S.admittedAcademicMerit J2 groupA
                (glm20StrategicPolicyStatePair
                  GLM20StrategicPolicyState.singleSub
                  GLM20StrategicPolicyState.singleFull) >
            populationShare groupA *
                S.admittedAcademicMerit J2 groupA
                  (glm20StrategicPolicyStatePair
                    GLM20StrategicPolicyState.singleSub
                    GLM20StrategicPolicyState.singleSub) +
              populationShare groupB *
                S.admittedAcademicMerit J2 groupB
                  (glm20StrategicPolicyStatePair
                    GLM20StrategicPolicyState.singleSub
                    GLM20StrategicPolicyState.singleSub)) := by
    intro hdropB
    have hdropB_base :
        glm20Theorem3SubFullGroupExpandsByDropping BaseS
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub K groupB := by
      simpa [S, BaseS, K, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20FeasibleWeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass]
        using hdropB
    exact
      paper_theorem3_school2_objective_iff_single_group_merit_gt_of_no_tie
        S glm20StrategicPolicyStatePair
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull J2 groupA groupB groupA
        populationShare
        (glm20TwoGroupWeightedAcademicMeritObjective S
          glm20StrategicPolicyStatePair J2 groupA groupB populationShare)
        (glm20TwoGroupWeightedAcademicMeritObjective_eq_groupA_of_groupB_zero
          S glm20StrategicPolicyStatePair J2 groupA groupB populationShare
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull
          (by
            simpa [S, BaseS,
              glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
              glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
              glm20WeightedAcademicMeritBinaryPolicySurface,
              glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
              using Or.inr (hJ2ZeroB costThreshold hdropB_base)))
        (by rfl)
        (by
          simpa [S, BaseS,
            glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
            glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
            glm20WeightedAcademicMeritBinaryPolicySurface,
            glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
            using hJ2NotTieA costThreshold hdropB_base)
  refine ⟨costThreshold, hmem, heq, hle, ?_⟩
  simpa [S] using
    (glm20Theorem3PolicyStateSubFullMassFeasibleSurface_subFull_iff_theorem3Condition_of_objective_bridges
      api subEstimateLaw subSubMass subFullMass fullFullCutoff
      fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA groupB
      populationShare testCost costThreshold (capacity2 := capacity2)
      (q1Sub := q1Sub) hJ1 hJ2A_merit hJ2B_merit)

/--
Source-family Theorem 3(i) positive-interval endpoint with school `J2`'s
zero fallback and concrete condition-(11) feasibility.

The admitted-merit table is the paper's four policy-state rows, with the
`(P_sub,P_full)` row generated by the school-`J1` Gaussian source family and
school `J2`'s expanding-group entry set to zero.  The conclusion uses the
concrete condition-(11) feasible surface, so no generic feasibility predicate
or separate condition-(11) hypothesis remains.
-/
abbrev
    paper_theorem3_source_conditions_of_policy_state_table_j2_zero_fallback_subFull_interval
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
    {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost leftCost rightCost : Group → ℝ}
    {capacity1 capacity2 q1Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    (C : GaussianHazardCertificate)
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2)
    (testBasedMerit : Group → ℝ → ℝ)
    (testFreeMerit : Group → ℝ)
    (hleftRight : ∀ g, leftCost g < rightCost g)
    (hleftPos : ∀ g, 0 < leftCost g)
    (hcostMem :
      ∀ g, testCost g ∈ Set.Icc (leftCost g) (rightCost g))
    (hcont :
      ∀ g, ContinuousOn (testBasedMerit g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hanti :
      ∀ g, StrictAntiOn (testBasedMerit g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hlowCost :
      ∀ g, testFreeMerit g < testBasedMerit g (leftCost g))
    (hhighCost :
      ∀ g, testBasedMerit g (rightCost g) < testFreeMerit g)
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
    (hfixedPoolMeritA :
      ¬ q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          glm20Theorem3SourceFamilySubFullMeritTable C J1 J1DropFamily
              J1DropThreshold
              (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
                fullFullCutoff J2 subFullMeritBase) J1 groupA <
            glm20Theorem3SourceFamilyFullFullMeritTable C J1 J2
              J1KeepFamily J2KeepFamily J1KeepThreshold J2KeepThreshold
              fullFullMeritFallback J1 groupA)
    (hfixedPoolMeritB :
      ¬ q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          glm20Theorem3SourceFamilySubFullMeritTable C J1 J1DropFamily
              J1DropThreshold
              (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
                fullFullCutoff J2 subFullMeritBase) J1 groupB <
            glm20Theorem3SourceFamilyFullFullMeritTable C J1 J2
              J1KeepFamily J2KeepFamily J1KeepThreshold J2KeepThreshold
              fullFullMeritFallback J1 groupB)
    (honlyA_J1_groupB_eq :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          glm20Theorem3SourceFamilyFullFullMeritTable C J1 J2
              J1KeepFamily J2KeepFamily J1KeepThreshold J2KeepThreshold
              fullFullMeritFallback J1 groupB =
            glm20Theorem3SourceFamilySubFullMeritTable C J1 J1DropFamily
              J1DropThreshold
              (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
                fullFullCutoff J2 subFullMeritBase) J1 groupB)
    (honlyA_J1_groupA_testBased :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          glm20Theorem3SourceFamilyFullFullMeritTable C J1 J2
              J1KeepFamily J2KeepFamily J1KeepThreshold J2KeepThreshold
              fullFullMeritFallback J1 groupA =
            testBasedMerit groupA (testCost groupA))
    (honlyA_J1_groupA_testFree :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          glm20Theorem3SourceFamilySubFullMeritTable C J1 J1DropFamily
              J1DropThreshold
              (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
                fullFullCutoff J2 subFullMeritBase) J1 groupA =
            testFreeMerit groupA)
    (honlyB_J1_groupA_eq :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          glm20Theorem3SourceFamilyFullFullMeritTable C J1 J2
              J1KeepFamily J2KeepFamily J1KeepThreshold J2KeepThreshold
              fullFullMeritFallback J1 groupA =
            glm20Theorem3SourceFamilySubFullMeritTable C J1 J1DropFamily
              J1DropThreshold
              (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
                fullFullCutoff J2 subFullMeritBase) J1 groupA)
    (honlyB_J1_groupB_testBased :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          glm20Theorem3SourceFamilyFullFullMeritTable C J1 J2
              J1KeepFamily J2KeepFamily J1KeepThreshold J2KeepThreshold
              fullFullMeritFallback J1 groupB =
            testBasedMerit groupB (testCost groupB))
    (honlyB_J1_groupB_testFree :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          glm20Theorem3SourceFamilySubFullMeritTable C J1 J1DropFamily
              J1DropThreshold
              (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
                fullFullCutoff J2 subFullMeritBase) J1 groupB =
            testFreeMerit groupB)
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
            populationShare groupB * subSubMerit J2 groupB) :=
  let subFullMerit :=
    glm20Theorem3SourceFamilySubFullMeritTable C J1 J1DropFamily
      J1DropThreshold
      (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff
        J2 subFullMeritBase)
  let fullSubMerit :=
    glm20Theorem3SourceFamilyFullSubMeritTable C J2 J2DropFamily
      J2DropThreshold fullSubMeritFallback
  let fullFullMerit :=
    glm20Theorem3SourceFamilyFullFullMeritTable C J1 J2 J1KeepFamily
      J2KeepFamily J1KeepThreshold J2KeepThreshold fullFullMeritFallback
  let admittedAcademicMerit :=
    glm20StrategicPolicyStateAdmittedMerit subSubMerit subFullMerit
      fullSubMerit fullFullMerit
  glm20Theorem3PolicyStateSubFullMassFeasibleSurface_subFull_interval
    api subEstimateLaw subSubMass subFullMass fullFullCutoff fullSubCutoff
    admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
    testCost leftCost rightCost (capacity1 := capacity1)
    (capacity2 := capacity2) (q1Sub := q1Sub) testBasedMerit testFreeMerit
    hleftRight hleftPos hcostMem hcont hanti hlowCost hhighCost
    hshareA hshareB hcapacity1 hfillFullFull1
    (by
      intro hA hB
      simpa [admittedAcademicMerit, subFullMerit, fullFullMerit,
        glm20StrategicPolicyStateAdmittedMerit] using
          hfixedPoolMeritA hA hB)
    (by
      intro hA hB
      simpa [admittedAcademicMerit, subFullMerit, fullFullMerit,
        glm20StrategicPolicyStateAdmittedMerit] using
          hfixedPoolMeritB hA hB)
    (by
      intro hA hB
      simpa [admittedAcademicMerit, subFullMerit, fullFullMerit,
        glm20StrategicPolicyStateAdmittedMerit] using
          honlyA_J1_groupB_eq hA hB)
    (by
      intro hA hB
      simpa [admittedAcademicMerit, fullFullMerit,
        glm20StrategicPolicyStateAdmittedMerit] using
          honlyA_J1_groupA_testBased hA hB)
    (by
      intro hA hB
      simpa [admittedAcademicMerit, subFullMerit,
        glm20StrategicPolicyStateAdmittedMerit] using
          honlyA_J1_groupA_testFree hA hB)
    (by
      intro hB hA
      simpa [admittedAcademicMerit, subFullMerit, fullFullMerit,
        glm20StrategicPolicyStateAdmittedMerit] using
          honlyB_J1_groupA_eq hB hA)
    (by
      intro hB hA
      simpa [admittedAcademicMerit, fullFullMerit,
        glm20StrategicPolicyStateAdmittedMerit] using
          honlyB_J1_groupB_testBased hB hA)
    (by
      intro hB hA
      simpa [admittedAcademicMerit, subFullMerit,
        glm20StrategicPolicyStateAdmittedMerit] using
          honlyB_J1_groupB_testFree hB hA)
    (by
      intro costThreshold hdropA
      have hdropA' :
          glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
            subEstimateLaw subSubMass subFullMass subSubMerit
            (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
              fullFullCutoff J2 subFullMeritBase)
            fullSubMeritFallback fullFullMeritFallback diversity J1 J2
            groupA groupB populationShare testCost fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold q1Sub costThreshold groupA := by
        simpa [admittedAcademicMerit, subFullMerit, fullSubMerit,
          fullFullMerit, glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands,
          glm20Theorem3SourceFamilyPolicyStateTableSurface,
          glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
          glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
          glm20WeightedAcademicMeritBinaryPolicySurface] using hdropA
      have hzero :=
        glm20Theorem3SourceFamilySubFullJ2ZeroFallback_zero_of_subFullExpands
          api subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritBase fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare testCost
          costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
          J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
          J1KeepThreshold J2DropThreshold J2KeepThreshold hdropA'
      have hJ2_ne_J1 : J2 ≠ J1 := by
        intro h
        exact hJ1_ne_J2 h.symm
      simpa [admittedAcademicMerit, subFullMerit,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ2_ne_J1] using hzero)
    (by
      intro costThreshold hdropA
      have hdropA' :
          glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
            subEstimateLaw subSubMass subFullMass subSubMerit
            (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
              fullFullCutoff J2 subFullMeritBase)
            fullSubMeritFallback fullFullMeritFallback diversity J1 J2
            groupA groupB populationShare testCost fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold q1Sub costThreshold groupA := by
        simpa [admittedAcademicMerit, subFullMerit, fullSubMerit,
          fullFullMerit, glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands,
          glm20Theorem3SourceFamilyPolicyStateTableSurface,
          glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
          glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
          glm20WeightedAcademicMeritBinaryPolicySurface] using hdropA
      have hgt :=
        glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupB_merit_gt_of_base_merit_gt
          api subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritBase fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare testCost
          costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
          J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
          J1KeepThreshold J2DropThreshold J2KeepThreshold hshareA hshareB
          hcapacity1 hfillFullFull1 hdropA'
          (hJ2MeritGtB_base costThreshold hdropA')
      have hJ2_ne_J1 : J2 ≠ J1 := by
        intro h
        exact hJ1_ne_J2 h.symm
      exact ne_of_gt
        (by
          simpa [admittedAcademicMerit, subFullMerit,
            glm20StrategicPolicyStateAdmittedMerit,
            glm20Theorem3SourceFamilySubFullMeritTable,
            glm20OverrideSchoolMeritRow, hJ2_ne_J1] using hgt))
    (by
      intro costThreshold hdropB
      have hdropB' :
          glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
            subEstimateLaw subSubMass subFullMass subSubMerit
            (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
              fullFullCutoff J2 subFullMeritBase)
            fullSubMeritFallback fullFullMeritFallback diversity J1 J2
            groupA groupB populationShare testCost fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold q1Sub costThreshold groupB := by
        simpa [admittedAcademicMerit, subFullMerit, fullSubMerit,
          fullFullMerit, glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands,
          glm20Theorem3SourceFamilyPolicyStateTableSurface,
          glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
          glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
          glm20WeightedAcademicMeritBinaryPolicySurface] using hdropB
      have hzero :=
        glm20Theorem3SourceFamilySubFullJ2ZeroFallback_zero_of_subFullExpands
          api subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritBase fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare testCost
          costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
          J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
          J1KeepThreshold J2DropThreshold J2KeepThreshold hdropB'
      have hJ2_ne_J1 : J2 ≠ J1 := by
        intro h
        exact hJ1_ne_J2 h.symm
      simpa [admittedAcademicMerit, subFullMerit,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ2_ne_J1] using hzero)
    (by
      intro costThreshold hdropB
      have hdropB' :
          glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
            subEstimateLaw subSubMass subFullMass subSubMerit
            (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
              fullFullCutoff J2 subFullMeritBase)
            fullSubMeritFallback fullFullMeritFallback diversity J1 J2
            groupA groupB populationShare testCost fullFullCutoff
            fullSubCutoff C J1DropFamily J2DropFamily J1KeepFamily
            J2KeepFamily J1DropThreshold J1KeepThreshold J2DropThreshold
            J2KeepThreshold q1Sub costThreshold groupB := by
        simpa [admittedAcademicMerit, subFullMerit, fullSubMerit,
          fullFullMerit, glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands,
          glm20Theorem3SourceFamilyPolicyStateTableSurface,
          glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
          glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
          glm20WeightedAcademicMeritBinaryPolicySurface] using hdropB
      have hgt :=
        glm20Theorem3SourceFamilySubFullJ2ZeroFallback_groupA_merit_gt_of_base_merit_gt
          api subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritBase fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare testCost
          costThreshold fullFullCutoff fullSubCutoff C J1DropFamily
          J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
          J1KeepThreshold J2DropThreshold J2KeepThreshold hshareA hshareB
          hcapacity1 hfillFullFull1 hdropB'
          (hJ2MeritGtA_base costThreshold hdropB')
      have hJ2_ne_J1 : J2 ≠ J1 := by
        intro h
        exact hJ1_ne_J2 h.symm
      exact ne_of_gt
        (by
          simpa [admittedAcademicMerit, subFullMerit,
            glm20StrategicPolicyStateAdmittedMerit,
            glm20Theorem3SourceFamilySubFullMeritTable,
            glm20OverrideSchoolMeritRow, hJ2_ne_J1] using hgt))

/--
Standard-Gaussian source-family Theorem 3(i) endpoint with school `J2`'s
zero fallback and concrete condition-(11) feasibility.

This is the equation-(50) specialization of
`paper_theorem3_source_conditions_of_policy_state_table_j2_zero_fallback_subFull_interval`:
the sub/full test-based merit as a function of cost is
`L(c) = merit(q_{2,full} - scale * Phi^{-1}(1 - c / v_2))`, and its
continuity/strict antitonicity on the positive interval are proved from the
standard-Gaussian quantile API.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_policy_state_table_j2_zero_fallback_subFull_interval_of_equation50
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
    {populationShare testCost leftCost rightCost : Group → ℝ}
    {capacity1 capacity2 q1Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    (J1DropFamily J2DropFamily :
      Group → GaussianOffsetSignalFamily FeatureDrop)
    (J1KeepFamily J2KeepFamily :
      Group → GaussianOffsetSignalFamily FeatureKeep)
    (J1DropThreshold J1KeepThreshold J2DropThreshold
      J2KeepThreshold : Group → ℝ)
    (hJ1_ne_J2 : J1 ≠ J2)
    {q2Full scale v2 : Group → ℝ}
    (meritOfCutoff : Group → ℝ → ℝ)
    (testFreeMerit : Group → ℝ)
    (hleftRight : ∀ g, leftCost g < rightCost g)
    (hleftPos : ∀ g, 0 < leftCost g)
    (hrightLtV2 : ∀ g, rightCost g < v2 g)
    (hcostMem :
      ∀ g, testCost g ∈ Set.Icc (leftCost g) (rightCost g))
    (hscale : ∀ g, 0 < scale g)
    (hmeritCont : ∀ g, Continuous (meritOfCutoff g))
    (hmeritAnti : ∀ g, StrictAnti (meritOfCutoff g))
    (hleft :
      ∀ g, testFreeMerit g <
        meritOfCutoff g
          (q2Full g -
            scale g *
              standardGaussianQuantileAPI.quantile
                (1 - leftCost g / v2 g)))
    (hright :
      ∀ g,
        meritOfCutoff g
            (q2Full g -
              scale g *
                standardGaussianQuantileAPI.quantile
                  (1 - rightCost g / v2 g)) <
          testFreeMerit g)
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
    (hfixedPoolMeritA :
      ¬ q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          glm20Theorem3SourceFamilySubFullMeritTable
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              J1 J1DropFamily J1DropThreshold
              (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
                fullFullCutoff J2 subFullMeritBase) J1 groupA <
            glm20Theorem3SourceFamilyFullFullMeritTable
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              J1 J2 J1KeepFamily J2KeepFamily J1KeepThreshold
              J2KeepThreshold fullFullMeritFallback J1 groupA)
    (hfixedPoolMeritB :
      ¬ q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          glm20Theorem3SourceFamilySubFullMeritTable
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              J1 J1DropFamily J1DropThreshold
              (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
                fullFullCutoff J2 subFullMeritBase) J1 groupB <
            glm20Theorem3SourceFamilyFullFullMeritTable
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              J1 J2 J1KeepFamily J2KeepFamily J1KeepThreshold
              J2KeepThreshold fullFullMeritFallback J1 groupB)
    (honlyA_J1_groupB_eq :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          glm20Theorem3SourceFamilyFullFullMeritTable
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              J1 J2 J1KeepFamily J2KeepFamily J1KeepThreshold
              J2KeepThreshold fullFullMeritFallback J1 groupB =
            glm20Theorem3SourceFamilySubFullMeritTable
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              J1 J1DropFamily J1DropThreshold
              (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
                fullFullCutoff J2 subFullMeritBase) J1 groupB)
    (honlyA_J1_groupA_testBased :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          glm20Theorem3SourceFamilyFullFullMeritTable
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              J1 J2 J1KeepFamily J2KeepFamily J1KeepThreshold
              J2KeepThreshold fullFullMeritFallback J1 groupA =
            meritOfCutoff groupA
              (q2Full groupA -
                scale groupA *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost groupA / v2 groupA)))
    (honlyA_J1_groupA_testFree :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          glm20Theorem3SourceFamilySubFullMeritTable
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              J1 J1DropFamily J1DropThreshold
              (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
                fullFullCutoff J2 subFullMeritBase) J1 groupA =
            testFreeMerit groupA)
    (honlyB_J1_groupA_eq :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          glm20Theorem3SourceFamilyFullFullMeritTable
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              J1 J2 J1KeepFamily J2KeepFamily J1KeepThreshold
              J2KeepThreshold fullFullMeritFallback J1 groupA =
            glm20Theorem3SourceFamilySubFullMeritTable
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              J1 J1DropFamily J1DropThreshold
              (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
                fullFullCutoff J2 subFullMeritBase) J1 groupA)
    (honlyB_J1_groupB_testBased :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          glm20Theorem3SourceFamilyFullFullMeritTable
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              J1 J2 J1KeepFamily J2KeepFamily J1KeepThreshold
              J2KeepThreshold fullFullMeritFallback J1 groupB =
            meritOfCutoff groupB
              (q2Full groupB -
                scale groupB *
                  standardGaussianQuantileAPI.quantile
                    (1 - testCost groupB / v2 groupB)))
    (honlyB_J1_groupB_testFree :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          glm20Theorem3SourceFamilySubFullMeritTable
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              J1 J1DropFamily J1DropThreshold
              (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
                fullFullCutoff J2 subFullMeritBase) J1 groupB =
            testFreeMerit groupB)
    (hJ2MeritGtB_base :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands
          standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
          subSubMerit
          (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase)
          fullSubMeritFallback fullFullMeritFallback diversity J1 J2
          groupA groupB populationShare testCost fullFullCutoff
          fullSubCutoff
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
          J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
          J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
          q1Sub costThreshold groupA →
        populationShare groupB * subFullMeritBase J2 groupB >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB)
    (hJ2MeritGtA_base :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands
          standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
          subSubMerit
          (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub
            fullFullCutoff J2 subFullMeritBase)
          fullSubMeritFallback fullFullMeritFallback diversity J1 J2
          groupA groupB populationShare testCost fullFullCutoff
          fullSubCutoff
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
          J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
          J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
          q1Sub costThreshold groupB →
        populationShare groupA * subFullMeritBase J2 groupA >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB) :=
  let testBasedMerit : Group → ℝ → ℝ :=
    fun g cost =>
      meritOfCutoff g
        (q2Full g -
          scale g *
            standardGaussianQuantileAPI.quantile (1 - cost / v2 g))
  let hregular :=
    paper_proposition5_equation50_subFull_cost_merit_regular_of_global_regular_cost_bounds
      standardGaussianQuantileAPI hleftRight hscale hleftPos hrightLtV2
      hmeritCont hmeritAnti
  paper_theorem3_source_conditions_of_policy_state_table_j2_zero_fallback_subFull_interval
    standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
    subSubMerit subFullMeritBase fullSubMeritFallback
    fullFullMeritFallback diversity
    (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (leftCost := leftCost) (rightCost := rightCost)
    (capacity1 := capacity1) (capacity2 := capacity2) (q1Sub := q1Sub)
    (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
    J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily J1DropThreshold
    J1KeepThreshold J2DropThreshold J2KeepThreshold hJ1_ne_J2
    testBasedMerit testFreeMerit hleftRight hleftPos hcostMem
    (fun g => hregular.1 g) (fun g => hregular.2 g)
    (by
      intro g
      simpa [testBasedMerit] using hleft g)
    (by
      intro g
      simpa [testBasedMerit] using hright g)
    hshareA hshareB hcapacity1 hfillFullFull1 hfixedPoolMeritA
    hfixedPoolMeritB honlyA_J1_groupB_eq
    (by
      intro hA hB
      simpa [testBasedMerit] using honlyA_J1_groupA_testBased hA hB)
    honlyA_J1_groupA_testFree honlyB_J1_groupA_eq
    (by
      intro hB hA
      simpa [testBasedMerit] using honlyB_J1_groupB_testBased hB hA)
    honlyB_J1_groupB_testFree hJ2MeritGtB_base hJ2MeritGtA_base

/--
Concrete Theorem 3(ii) feasible-surface bridge for the full/sub branch.

The condition-(11) feasibility surface only constrains the school-`J2`
`(P_sub,P_full)` branch.  Therefore the current `(P_full,P_sub)` pair and its
binary deviations are feasible by definition, and the full/sub branch reduces
to the ordinary Theorem 3(ii) objective-pair condition.
-/
theorem
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface_fullSub_iff_theorem3Condition
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost subFullCostThreshold
      lowCostThreshold highCostThreshold : Group → ℝ)
    {capacity2 q1Sub q2Sub : ℝ}
    (hfullSubObjective :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      (glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleSub ∧
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J2 groupA groupB populationShare
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleFull ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J2 groupA groupB populationShare
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleSub) ↔
        glm20Theorem3FullSubCondition S glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull groupA groupB testCost
          lowCostThreshold highCostThreshold q1Sub q2Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)) :
    let S :=
      glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
        subSubMass subFullMass fullFullCutoff fullSubCutoff
        admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
        testCost subFullCostThreshold capacity2 q1Sub
    S.policyPairIsEquilibrium GLM20StrategicPolicyState.singleFull
        GLM20StrategicPolicyState.singleSub ↔
      glm20Theorem3FullSubCondition S glm20StrategicPolicyStatePair
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull groupA groupB testCost
        lowCostThreshold highCostThreshold q1Sub q2Sub
        (fun g q => glm20StrategicSubEstimateMassAbove api
          (subEstimateLaw g) q) := by
  let feasible2 :=
    glm20Theorem3PolicyStateSubFullJ2MassFeasible subFullMass groupA groupB
      testCost subFullCostThreshold fullFullCutoff capacity2 q1Sub
  exact
    paper_theorem3_fullSub_condition_of_feasible_weighted_surface_objective_bridge
      (S := glm20Theorem3PolicyStateSubFullMassFeasibleSurface api
        subEstimateLaw subSubMass subFullMass fullFullCutoff fullSubCutoff
        admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
        testCost subFullCostThreshold capacity2 q1Sub)
      (massTestTaking :=
        glm20Theorem3PolicyStateCutoffMass api subEstimateLaw subSubMass
          subFullMass fullFullCutoff fullSubCutoff)
      (admittedAcademicMerit := admittedAcademicMerit)
      (diversity := diversity)
      (policyPair := glm20StrategicPolicyStatePair)
      (Psub := GLM20StrategicPolicyState.singleSub)
      (Pfull := GLM20StrategicPolicyState.singleFull)
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (lowCostThreshold := lowCostThreshold)
      (highCostThreshold := highCostThreshold) (q1Sub := q1Sub)
      (q2Sub := q2Sub)
      (K := fun g q => glm20StrategicSubEstimateMassAbove api
        (subEstimateLaw g) q)
      (feasible1 := fun _ _ => True) (feasible2 := feasible2)
      (hS := by rfl)
      (hfeasible1FullSub := trivial)
      (hfeasible2FullSub := by simp [feasible2])
      (hfeasible1SubSub := trivial)
      (hfeasible2FullFull := by simp [feasible2])
      hfullSubObjective

/--
Concrete Theorem 3(ii) positive-interval endpoint for the policy-state
condition-(11) feasible surface.

The sub/full feasibility threshold is a parameter of the surface, but the
full/sub branch is definitionally feasible for that surface.  The theorem
constructs the low/high condition-(13)--(14) thresholds from the Proposition
5(ii) interval crossings and returns the paper-facing full/sub equilibrium
equivalence on the same concrete surface.
-/
theorem
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface_fullSub_interval
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost subFullCostThreshold leftCost rightCost :
      Group → ℝ)
    {capacity2 q1Sub q2Sub : ℝ}
    (lowTestBasedMerit : Group → ℝ → ℝ)
    (lowTestFreeMerit : Group → ℝ)
    (highTestBasedMerit : Group → ℝ → ℝ)
    (highTestFreeMerit : Group → ℝ)
    (hleftRight : ∀ g, leftCost g < rightCost g)
    (hleftPos : ∀ g, 0 < leftCost g)
    (hcostMem :
      ∀ g, testCost g ∈ Set.Icc (leftCost g) (rightCost g))
    (hlowCont :
      ∀ g, ContinuousOn (lowTestBasedMerit g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hlowAnti :
      ∀ g, StrictAntiOn (lowTestBasedMerit g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hlowAtLeft :
      ∀ g, lowTestFreeMerit g < lowTestBasedMerit g (leftCost g))
    (hlowAtRight :
      ∀ g, lowTestBasedMerit g (rightCost g) < lowTestFreeMerit g)
    (hhighCont :
      ∀ g, ContinuousOn (highTestBasedMerit g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hhighAnti :
      ∀ g, StrictAntiOn (highTestBasedMerit g)
        (Set.Icc (leftCost g) (rightCost g)))
    (hhighAtLeft :
      ∀ g, highTestFreeMerit g < highTestBasedMerit g (leftCost g))
    (hhighAtRight :
      ∀ g, highTestBasedMerit g (rightCost g) < highTestFreeMerit g)
    (hhighAtLowRoot :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        lowTestBasedMerit g c = lowTestFreeMerit g →
          highTestFreeMerit g < highTestBasedMerit g c)
    (hshareA : 0 < populationShare groupA)
    (hshareB : 0 < populationShare groupB)
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
    (hfixedPoolMeritA :
      ¬ q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub) <
            admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull))
    (hfixedPoolMeritB :
      ¬ q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub) <
            admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull))
    (honlyA_J2_groupB_eq :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub))
    (honlyA_J2_groupA_testBased :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            lowTestBasedMerit groupA (testCost groupA))
    (honlyA_J2_groupA_testFree :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub) =
            lowTestFreeMerit groupA)
    (honlyB_J2_groupA_eq :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub))
    (honlyB_J2_groupB_testBased :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            lowTestBasedMerit groupB (testCost groupB))
    (honlyB_J2_groupB_testFree :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub) =
            lowTestFreeMerit groupB)
    (hnoExpandA :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      fullSubCutoff groupA < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleSub)
    (hexpandA_testFree :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      ¬ fullSubCutoff groupA < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub =
          highTestFreeMerit groupA)
    (hexpandA_testBased :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      ¬ fullSubCutoff groupA < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleSub =
          highTestBasedMerit groupA (testCost groupA))
    (hnoExpandB :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      fullSubCutoff groupB < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleSub)
    (hexpandB_testFree :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      ¬ fullSubCutoff groupB < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub =
          highTestFreeMerit groupB)
    (hexpandB_testBased :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      ¬ fullSubCutoff groupB < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleSub =
          highTestBasedMerit groupB (testCost groupB)) :
    ∃ lowCostThreshold highCostThreshold : Group → ℝ,
      (∀ g, lowCostThreshold g ∈ Set.Ioo (leftCost g) (rightCost g)) ∧
        (∀ g, highCostThreshold g ∈
          Set.Ioo (leftCost g) (rightCost g)) ∧
          (∀ g, lowTestBasedMerit g (lowCostThreshold g) =
            lowTestFreeMerit g) ∧
            (∀ g, highTestBasedMerit g (highCostThreshold g) =
              highTestFreeMerit g) ∧
              (∀ g, 0 < lowCostThreshold g) ∧
                (∀ g, lowCostThreshold g < highCostThreshold g) ∧
                  let S :=
                    glm20Theorem3PolicyStateSubFullMassFeasibleSurface api
                      subEstimateLaw subSubMass subFullMass fullFullCutoff
                      fullSubCutoff admittedAcademicMerit diversity J1 J2
                      groupA groupB populationShare testCost
                      subFullCostThreshold capacity2 q1Sub
                  S.policyPairIsEquilibrium
                      GLM20StrategicPolicyState.singleFull
                      GLM20StrategicPolicyState.singleSub ↔
                    glm20Theorem3FullSubCondition S
                      glm20StrategicPolicyStatePair
                      GLM20StrategicPolicyState.singleSub
                      GLM20StrategicPolicyState.singleFull groupA groupB
                      testCost lowCostThreshold highCostThreshold q1Sub
                      q2Sub
                      (fun g q => glm20StrategicSubEstimateMassAbove api
                        (subEstimateLaw g) q) := by
  let S :=
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
      subSubMass subFullMass fullFullCutoff fullSubCutoff
      admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
      testCost subFullCostThreshold capacity2 q1Sub
  let objective1 : GLM20StrategicPolicyState → GLM20StrategicPolicyState → ℝ :=
    glm20TwoGroupWeightedAcademicMeritObjective S
      glm20StrategicPolicyStatePair J1 groupA groupB populationShare
  let objective2 : GLM20StrategicPolicyState → GLM20StrategicPolicyState → ℝ :=
    glm20TwoGroupWeightedAcademicMeritObjective S
      glm20StrategicPolicyStatePair J2 groupA groupB populationShare
  have hmassFullFullA :
      S.massTestTaking groupA
          (glm20StrategicPolicyStatePair
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleFull) =
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
          (fullFullCutoff groupA) := by
    simp [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
      glm20FeasibleWeightedAcademicMeritBinaryPolicySurface,
      glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass,
      glm20StrategicSubEstimateMassAbove]
  have hmassFullFullB :
      S.massTestTaking groupB
          (glm20StrategicPolicyStatePair
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleFull) =
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
          (fullFullCutoff groupB) := by
    simp [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
      glm20FeasibleWeightedAcademicMeritBinaryPolicySurface,
      glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass,
      glm20StrategicSubEstimateMassAbove]
  have hmassFullSubA :
      S.massTestTaking groupA
          (glm20StrategicPolicyStatePair
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleSub) =
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupA)
          (fullSubCutoff groupA) := by
    simp [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
      glm20FeasibleWeightedAcademicMeritBinaryPolicySurface,
      glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass,
      glm20StrategicSubEstimateMassAbove]
  have hmassFullSubB :
      S.massTestTaking groupB
          (glm20StrategicPolicyStatePair
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleSub) =
        glm20StrategicSubEstimateMassAbove api (subEstimateLaw groupB)
          (fullSubCutoff groupB) := by
    simp [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
      glm20FeasibleWeightedAcademicMeritBinaryPolicySurface,
      glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass,
      glm20StrategicSubEstimateMassAbove]
  have hfillFullFull2S :
      capacity2 ≤
        populationShare groupA *
            S.massTestTaking groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) +
          populationShare groupB *
            S.massTestTaking groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) := by
    simpa [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
      glm20FeasibleWeightedAcademicMeritBinaryPolicySurface,
      glm20Theorem3PolicyStateCutoffMass, glm20StrategicPolicyStateMass,
      glm20StrategicSubEstimateMassAbove] using hfillFullFull2
  rcases
    paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_merit_crossings_interval_capacity_fixed_pool_and_group_merit_formulas
      (S := S) (policyPair := glm20StrategicPolicyStatePair)
      (Psub := GLM20StrategicPolicyState.singleSub)
      (Pfull := GLM20StrategicPolicyState.singleFull)
      (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (leftCost := leftCost) (rightCost := rightCost)
      (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
      api subEstimateLaw (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) objective1 lowTestBasedMerit
      lowTestFreeMerit highTestBasedMerit highTestFreeMerit
      hleftRight hleftPos hcostMem hlowCont hlowAnti hlowAtLeft
      hlowAtRight hhighCont hhighAnti hhighAtLeft hhighAtRight
      hhighAtLowRoot hshareA hshareB hmassFullFullA hmassFullFullB
      hmassFullSubA hmassFullSubB hcapacity2 hfillFullFull2S
      (by
        intro hA hB
        simpa [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
          glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
          using hfixedPoolMeritA hA hB)
      (by
        intro hA hB
        simpa [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
          glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
          using hfixedPoolMeritB hA hB)
      (by
        intro hA hB
        simpa [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
          glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
          using honlyA_J2_groupB_eq hA hB)
      (by
        intro hA hB
        simpa [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
          glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
          using honlyA_J2_groupA_testBased hA hB)
      (by
        intro hA hB
        simpa [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
          glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
          using honlyA_J2_groupA_testFree hA hB)
      (by
        intro hB hA
        simpa [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
          glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
          using honlyB_J2_groupA_eq hB hA)
      (by
        intro hB hA
        simpa [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
          glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
          using honlyB_J2_groupB_testBased hB hA)
      (by
        intro hB hA
        simpa [S, glm20Theorem3PolicyStateSubFullMassFeasibleSurface,
          glm20FeasibleWeightedAcademicMeritBinaryPolicySurface]
          using honlyB_J2_groupB_testFree hB hA)
      (by simpa [S, objective1] using hnoExpandA)
      (by simpa [S, objective1] using hexpandA_testFree)
      (by simpa [S, objective1] using hexpandA_testBased)
      (by simpa [S, objective1] using hnoExpandB)
      (by simpa [S, objective1] using hexpandB_testFree)
      (by simpa [S, objective1] using hexpandB_testBased) with
    ⟨lowCostThreshold, highCostThreshold, hlowMem, hhighMem, hlowEq,
      hhighEq, hlowPos, hlowHigh, hobjective⟩
  refine ⟨lowCostThreshold, highCostThreshold, hlowMem, hhighMem, hlowEq,
    hhighEq, hlowPos, hlowHigh, ?_⟩
  simpa [S] using
    (glm20Theorem3PolicyStateSubFullMassFeasibleSurface_fullSub_iff_theorem3Condition
      api subEstimateLaw subSubMass subFullMass fullFullCutoff
      fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA groupB
      populationShare testCost subFullCostThreshold lowCostThreshold
      highCostThreshold (capacity2 := capacity2) (q1Sub := q1Sub)
      (q2Sub := q2Sub) hobjective)

/--
Concrete Theorem 3(iii) full/full endpoint for the condition-(11) feasible
surface.

The paper's part (iii) boundary-function conclusion follows from positive
realized group test costs.  In the interval versions of parts (i)--(ii), those
positive costs are already available because each realized cost lies in a
positive interval.
-/
theorem
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface_fullFull_condition_of_positive_cost_interval
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost subFullCostThreshold leftCost rightCost :
      Group → ℝ)
    {capacity2 q1Sub : ℝ}
    (hleftPos : ∀ g, 0 < leftCost g)
    (hcostMem :
      ∀ g, testCost g ∈ Set.Icc (leftCost g) (rightCost g)) :
    let S :=
      glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
        subSubMass subFullMass fullFullCutoff fullSubCutoff
        admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
        testCost subFullCostThreshold capacity2 q1Sub
    glm20Theorem3FullFullCondition S GLM20StrategicPolicyState.singleFull
      groupA groupB testCost := by
  intro S
  have hcostA : 0 < testCost groupA :=
    lt_of_lt_of_le (hleftPos groupA) (hcostMem groupA).1
  have hcostB : 0 < testCost groupB :=
    lt_of_lt_of_le (hleftPos groupB) (hcostMem groupB).1
  exact
    paper_theorem3_fullFull_condition_exists_boundary_functions_of_positive_costs
      S GLM20StrategicPolicyState.singleFull groupA groupB testCost hcostA
      hcostB

/--
Concrete Theorem 3 source-shaped endpoint on the condition-(11) feasible
surface, with part (iii) discharged from the same positive cost interval used
to construct the part (i)--(ii) thresholds.

This is the paper-facing composition layer: callers provide the already proved
part (i) and part (ii) equilibrium equivalences, and Lean returns the three
Theorem 3 conclusions in the paper order.
-/
theorem
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface_source_conditions_of_i_ii_and_positive_cost_interval
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost subFullCostThreshold
      fullSubLowCostThreshold fullSubHighCostThreshold leftCost rightCost :
        Group → ℝ)
    {capacity2 q1Sub q2Sub : ℝ}
    (hleftPos : ∀ g, 0 < leftCost g)
    (hcostMem :
      ∀ g, testCost g ∈ Set.Icc (leftCost g) (rightCost g))
    (hsubFull :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      S.policyPairIsEquilibrium GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull ↔
        glm20Theorem3SubFullCondition S glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q))
    (hfullSub :
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      S.policyPairIsEquilibrium GLM20StrategicPolicyState.singleFull
          GLM20StrategicPolicyState.singleSub ↔
        glm20Theorem3FullSubCondition S glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull groupA groupB testCost
          fullSubLowCostThreshold fullSubHighCostThreshold q1Sub q2Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)) :
    let S :=
      glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
        subSubMass subFullMass fullFullCutoff fullSubCutoff
        admittedAcademicMerit diversity J1 J2 groupA groupB populationShare
        testCost subFullCostThreshold capacity2 q1Sub
    (S.policyPairIsEquilibrium GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      glm20Theorem3SubFullCondition S glm20StrategicPolicyStatePair
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull J2 groupA groupB
        populationShare testCost subFullCostThreshold capacity2 q1Sub
        (fun g q => glm20StrategicSubEstimateMassAbove api
          (subEstimateLaw g) q)) ∧
      (S.policyPairIsEquilibrium GLM20StrategicPolicyState.singleFull
          GLM20StrategicPolicyState.singleSub ↔
        glm20Theorem3FullSubCondition S glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull groupA groupB testCost
          fullSubLowCostThreshold fullSubHighCostThreshold q1Sub q2Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)) ∧
        glm20Theorem3FullFullCondition S
          GLM20StrategicPolicyState.singleFull groupA groupB testCost := by
  intro S
  have hcostA : 0 < testCost groupA :=
    lt_of_lt_of_le (hleftPos groupA) (hcostMem groupA).1
  have hcostB : 0 < testCost groupB :=
    lt_of_lt_of_le (hleftPos groupB) (hcostMem groupB).1
  exact
    paper_theorem3_two_school_academic_merit_source_conditions_of_i_ii_and_positive_costs
      (S := S) (policyPair := glm20StrategicPolicyStatePair)
      (Psub := GLM20StrategicPolicyState.singleSub)
      (Pfull := GLM20StrategicPolicyState.singleFull)
      (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullCostThreshold := subFullCostThreshold)
      (fullSubLowCostThreshold := fullSubLowCostThreshold)
      (fullSubHighCostThreshold := fullSubHighCostThreshold)
      (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
      (K := fun g q => glm20StrategicSubEstimateMassAbove api
        (subEstimateLaw g) q)
      hsubFull hfullSub hcostA hcostB

/--
Concrete Theorem 3(i)--(ii) positive-interval endpoint for the
condition-(11) feasible surface.

This composes the sub/full interval theorem, which constructs the paper's
condition-(10) threshold, with the full/sub interval theorem on the same
surface.  The full/sub objective-row assumptions are quantified over the
constructed sub/full threshold because that threshold is not available before
part (i) is applied.
-/
theorem
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface_subFull_fullSub_interval
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare testCost subFullLeftCost subFullRightCost
      fullSubLeftCost fullSubRightCost : Group → ℝ)
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    (subFullTestBasedMerit : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (lowTestBasedMerit : Group → ℝ → ℝ)
    (lowTestFreeMerit : Group → ℝ)
    (highTestBasedMerit : Group → ℝ → ℝ)
    (highTestFreeMerit : Group → ℝ)
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
    (hsubFullLowCost :
      ∀ g, subFullTestFreeMerit g <
        subFullTestBasedMerit g (subFullLeftCost g))
    (hsubFullHighCost :
      ∀ g, subFullTestBasedMerit g (subFullRightCost g) <
        subFullTestFreeMerit g)
    (hfullSubLeftRight :
      ∀ g, fullSubLeftCost g < fullSubRightCost g)
    (hfullSubLeftPos : ∀ g, 0 < fullSubLeftCost g)
    (hfullSubCostMem :
      ∀ g, testCost g ∈
        Set.Icc (fullSubLeftCost g) (fullSubRightCost g))
    (hlowCont :
      ∀ g, ContinuousOn (lowTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hlowAnti :
      ∀ g, StrictAntiOn (lowTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hlowAtLeft :
      ∀ g, lowTestFreeMerit g <
        lowTestBasedMerit g (fullSubLeftCost g))
    (hlowAtRight :
      ∀ g, lowTestBasedMerit g (fullSubRightCost g) <
        lowTestFreeMerit g)
    (hhighCont :
      ∀ g, ContinuousOn (highTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hhighAnti :
      ∀ g, StrictAntiOn (highTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hhighAtLeft :
      ∀ g, highTestFreeMerit g <
        highTestBasedMerit g (fullSubLeftCost g))
    (hhighAtRight :
      ∀ g, highTestBasedMerit g (fullSubRightCost g) <
        highTestFreeMerit g)
    (hhighAtLowRoot :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        lowTestBasedMerit g c = lowTestFreeMerit g →
          highTestFreeMerit g < highTestBasedMerit g c)
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
    (hsubFullFixedPoolMeritA :
      ¬ q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          admittedAcademicMerit J1 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) <
            admittedAcademicMerit J1 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull))
    (hsubFullFixedPoolMeritB :
      ¬ q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          admittedAcademicMerit J1 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) <
            admittedAcademicMerit J1 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull))
    (hsubFullOnlyA_J1_groupB_eq :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          admittedAcademicMerit J1 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            admittedAcademicMerit J1 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull))
    (hsubFullOnlyA_J1_groupA_testBased :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          admittedAcademicMerit J1 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            subFullTestBasedMerit groupA (testCost groupA))
    (hsubFullOnlyA_J1_groupA_testFree :
      q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          admittedAcademicMerit J1 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) =
            subFullTestFreeMerit groupA)
    (hsubFullOnlyB_J1_groupA_eq :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          admittedAcademicMerit J1 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            admittedAcademicMerit J1 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull))
    (hsubFullOnlyB_J1_groupB_testBased :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          admittedAcademicMerit J1 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            subFullTestBasedMerit groupB (testCost groupB))
    (hsubFullOnlyB_J1_groupB_testFree :
      q1Sub < fullFullCutoff groupB →
        ¬ q1Sub < fullFullCutoff groupA →
          admittedAcademicMerit J1 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) =
            subFullTestFreeMerit groupB)
    (hJ2ZeroA :
      ∀ costThreshold : Group → ℝ,
      glm20Theorem3SubFullGroupExpandsByDropping
          (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
            groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)
          groupA →
        admittedAcademicMerit J2 groupA
          (glm20StrategicPolicyStatePair
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) = 0)
    (hJ2NotTieB :
      ∀ costThreshold : Group → ℝ,
      glm20Theorem3SubFullGroupExpandsByDropping
          (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
            groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)
          groupA →
        populationShare groupB *
            admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) ≠
          populationShare groupA *
              admittedAcademicMerit J2 groupA
                (glm20StrategicPolicyStatePair
                  GLM20StrategicPolicyState.singleSub
                  GLM20StrategicPolicyState.singleSub) +
            populationShare groupB *
              admittedAcademicMerit J2 groupB
                (glm20StrategicPolicyStatePair
                  GLM20StrategicPolicyState.singleSub
                  GLM20StrategicPolicyState.singleSub))
    (hJ2ZeroB :
      ∀ costThreshold : Group → ℝ,
      glm20Theorem3SubFullGroupExpandsByDropping
          (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
            groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)
          groupB →
        admittedAcademicMerit J2 groupB
          (glm20StrategicPolicyStatePair
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull) = 0)
    (hJ2NotTieA :
      ∀ costThreshold : Group → ℝ,
      glm20Theorem3SubFullGroupExpandsByDropping
          (glm20Theorem3PolicyStateWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA
            groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull testCost costThreshold
          q1Sub
          (fun g q => glm20StrategicSubEstimateMassAbove api
            (subEstimateLaw g) q)
          groupB →
        populationShare groupA *
            admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleSub
                GLM20StrategicPolicyState.singleFull) ≠
          populationShare groupA *
              admittedAcademicMerit J2 groupA
                (glm20StrategicPolicyStatePair
                  GLM20StrategicPolicyState.singleSub
                  GLM20StrategicPolicyState.singleSub) +
            populationShare groupB *
              admittedAcademicMerit J2 groupB
                (glm20StrategicPolicyStatePair
                  GLM20StrategicPolicyState.singleSub
                  GLM20StrategicPolicyState.singleSub))
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
    (hfullSubFixedPoolMeritA :
      ¬ q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub) <
            admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull))
    (hfullSubFixedPoolMeritB :
      ¬ q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub) <
            admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull))
    (hfullSubOnlyA_J2_groupB_eq :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub))
    (hfullSubOnlyA_J2_groupA_testBased :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            lowTestBasedMerit groupA (testCost groupA))
    (hfullSubOnlyA_J2_groupA_testFree :
      q2Sub < fullFullCutoff groupA →
        ¬ q2Sub < fullFullCutoff groupB →
          admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub) =
            lowTestFreeMerit groupA)
    (hfullSubOnlyB_J2_groupA_eq :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            admittedAcademicMerit J2 groupA
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub))
    (hfullSubOnlyB_J2_groupB_testBased :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleFull) =
            lowTestBasedMerit groupB (testCost groupB))
    (hfullSubOnlyB_J2_groupB_testFree :
      q2Sub < fullFullCutoff groupB →
        ¬ q2Sub < fullFullCutoff groupA →
          admittedAcademicMerit J2 groupB
              (glm20StrategicPolicyStatePair
                GLM20StrategicPolicyState.singleFull
                GLM20StrategicPolicyState.singleSub) =
            lowTestFreeMerit groupB)
    (hnoExpandA :
      ∀ subFullCostThreshold : Group → ℝ,
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      fullSubCutoff groupA < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleSub)
    (hexpandA_testFree :
      ∀ subFullCostThreshold : Group → ℝ,
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      ¬ fullSubCutoff groupA < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub =
          highTestFreeMerit groupA)
    (hexpandA_testBased :
      ∀ subFullCostThreshold : Group → ℝ,
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      ¬ fullSubCutoff groupA < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleSub =
          highTestBasedMerit groupA (testCost groupA))
    (hnoExpandB :
      ∀ subFullCostThreshold : Group → ℝ,
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      fullSubCutoff groupB < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub ≤
          glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleSub)
    (hexpandB_testFree :
      ∀ subFullCostThreshold : Group → ℝ,
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      ¬ fullSubCutoff groupB < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleSub =
          highTestFreeMerit groupB)
    (hexpandB_testBased :
      ∀ subFullCostThreshold : Group → ℝ,
      let S :=
        glm20Theorem3PolicyStateSubFullMassFeasibleSurface api subEstimateLaw
          subSubMass subFullMass fullFullCutoff fullSubCutoff
          admittedAcademicMerit diversity J1 J2 groupA groupB
          populationShare testCost subFullCostThreshold capacity2 q1Sub
      ¬ fullSubCutoff groupB < q1Sub →
        glm20TwoGroupWeightedAcademicMeritObjective S
            glm20StrategicPolicyStatePair J1 groupA groupB populationShare
            GLM20StrategicPolicyState.singleFull
            GLM20StrategicPolicyState.singleSub =
          highTestBasedMerit groupB (testCost groupB)) :
    ∃ subFullCostThreshold lowCostThreshold highCostThreshold : Group → ℝ,
      (∀ g, subFullCostThreshold g ∈
        Set.Ioo (subFullLeftCost g) (subFullRightCost g)) ∧
        (∀ g, subFullTestBasedMerit g (subFullCostThreshold g) =
          subFullTestFreeMerit g) ∧
          (∀ g c, c ∈
            Set.Icc (subFullLeftCost g) (subFullRightCost g) →
              (subFullTestBasedMerit g c ≤ subFullTestFreeMerit g ↔
                subFullCostThreshold g ≤ c)) ∧
            (∀ g, lowCostThreshold g ∈
              Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
              (∀ g, highCostThreshold g ∈
                Set.Ioo (fullSubLeftCost g) (fullSubRightCost g)) ∧
                (∀ g, lowTestBasedMerit g (lowCostThreshold g) =
                  lowTestFreeMerit g) ∧
                  (∀ g, highTestBasedMerit g (highCostThreshold g) =
                    highTestFreeMerit g) ∧
                    (∀ g, 0 < lowCostThreshold g) ∧
                      (∀ g, lowCostThreshold g < highCostThreshold g) ∧
                        let S :=
                          glm20Theorem3PolicyStateSubFullMassFeasibleSurface
                            api subEstimateLaw subSubMass subFullMass
                            fullFullCutoff fullSubCutoff admittedAcademicMerit
                            diversity J1 J2 groupA groupB populationShare
                            testCost subFullCostThreshold capacity2 q1Sub
                        (S.policyPairIsEquilibrium
                            GLM20StrategicPolicyState.singleSub
                            GLM20StrategicPolicyState.singleFull ↔
                          glm20Theorem3SubFullCondition S
                            glm20StrategicPolicyStatePair
                            GLM20StrategicPolicyState.singleSub
                            GLM20StrategicPolicyState.singleFull J2 groupA
                            groupB populationShare testCost
                            subFullCostThreshold capacity2 q1Sub
                            (fun g q =>
                              glm20StrategicSubEstimateMassAbove api
                                (subEstimateLaw g) q)) ∧
                          (S.policyPairIsEquilibrium
                              GLM20StrategicPolicyState.singleFull
                              GLM20StrategicPolicyState.singleSub ↔
                            glm20Theorem3FullSubCondition S
                              glm20StrategicPolicyStatePair
                              GLM20StrategicPolicyState.singleSub
                              GLM20StrategicPolicyState.singleFull groupA
                              groupB testCost lowCostThreshold
                              highCostThreshold q1Sub q2Sub
                              (fun g q =>
                                glm20StrategicSubEstimateMassAbove api
                                  (subEstimateLaw g) q)) := by
  rcases
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface_subFull_interval
      api subEstimateLaw subSubMass subFullMass fullFullCutoff
      fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA groupB
      populationShare testCost subFullLeftCost subFullRightCost
      (capacity1 := capacity1) (capacity2 := capacity2) (q1Sub := q1Sub)
      subFullTestBasedMerit subFullTestFreeMerit hsubFullLeftRight
      hsubFullLeftPos hsubFullCostMem hsubFullCont hsubFullAnti
      hsubFullLowCost hsubFullHighCost hshareA hshareB hcapacity1
      hfillFullFull1 hsubFullFixedPoolMeritA hsubFullFixedPoolMeritB
      hsubFullOnlyA_J1_groupB_eq hsubFullOnlyA_J1_groupA_testBased
      hsubFullOnlyA_J1_groupA_testFree hsubFullOnlyB_J1_groupA_eq
      hsubFullOnlyB_J1_groupB_testBased hsubFullOnlyB_J1_groupB_testFree
      hJ2ZeroA hJ2NotTieB hJ2ZeroB hJ2NotTieA with
    ⟨subFullCostThreshold, hsubFullMem, hsubFullEq, hsubFullIffCost,
      hsubFullEquilibrium⟩
  rcases
    glm20Theorem3PolicyStateSubFullMassFeasibleSurface_fullSub_interval
      api subEstimateLaw subSubMass subFullMass fullFullCutoff
      fullSubCutoff admittedAcademicMerit diversity J1 J2 groupA groupB
      populationShare testCost subFullCostThreshold fullSubLeftCost
      fullSubRightCost (capacity2 := capacity2) (q1Sub := q1Sub)
      (q2Sub := q2Sub) lowTestBasedMerit lowTestFreeMerit
      highTestBasedMerit highTestFreeMerit hfullSubLeftRight
      hfullSubLeftPos hfullSubCostMem hlowCont hlowAnti hlowAtLeft
      hlowAtRight hhighCont hhighAnti hhighAtLeft hhighAtRight
      hhighAtLowRoot hshareA hshareB hcapacity2 hfillFullFull2
      hfullSubFixedPoolMeritA hfullSubFixedPoolMeritB
      hfullSubOnlyA_J2_groupB_eq hfullSubOnlyA_J2_groupA_testBased
      hfullSubOnlyA_J2_groupA_testFree hfullSubOnlyB_J2_groupA_eq
      hfullSubOnlyB_J2_groupB_testBased hfullSubOnlyB_J2_groupB_testFree
      (hnoExpandA subFullCostThreshold)
      (hexpandA_testFree subFullCostThreshold)
      (hexpandA_testBased subFullCostThreshold)
      (hnoExpandB subFullCostThreshold)
      (hexpandB_testFree subFullCostThreshold)
      (hexpandB_testBased subFullCostThreshold) with
    ⟨lowCostThreshold, highCostThreshold, hlowMem, hhighMem, hlowEq,
      hhighEq, hlowPos, hlowHigh, hfullSubEquilibrium⟩
  refine
    ⟨subFullCostThreshold, lowCostThreshold, highCostThreshold,
      hsubFullMem, hsubFullEq, hsubFullIffCost, hlowMem, hhighMem, hlowEq,
      hhighEq, hlowPos, hlowHigh, ?_⟩
  exact ⟨hsubFullEquilibrium, hfullSubEquilibrium⟩

/--
Feasibility-aware policy-state-table interval endpoint with the school-`J2`
zero expanding-group row built into the source model.

This is the feasibility-aware analogue of
`paper_theorem3_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_subFull_fullSub_interval`.
The mass-fill side of condition (12) remains in the explicit feasibility
hypothesis, while the expanding-group zero facts are definitional and the
visible school-`J2` premises are just the two strict survivor-merit comparisons
on the paper's base sub/full merit row.
-/
abbrev
    paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_subFull_fullSub_interval
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
    (fullSubLowTestBasedMerit : Group → ℝ → ℝ)
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestBasedMerit : Group → ℝ → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
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
    (hlowCont :
      ∀ g, ContinuousOn (fullSubLowTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hlowAnti :
      ∀ g, StrictAntiOn (fullSubLowTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hlowAtLeft :
      ∀ g,
        fullSubLowTestFreeMerit g <
          fullSubLowTestBasedMerit g (fullSubLeftCost g))
    (hlowAtRight :
      ∀ g,
        fullSubLowTestBasedMerit g (fullSubRightCost g) <
          fullSubLowTestFreeMerit g)
    (hhighCont :
      ∀ g, ContinuousOn (fullSubHighTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hhighAnti :
      ∀ g, StrictAntiOn (fullSubHighTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hhighAtLeft :
      ∀ g,
        fullSubHighTestFreeMerit g <
          fullSubHighTestBasedMerit g (fullSubLeftCost g))
    (hhighAtRight :
      ∀ g,
        fullSubHighTestBasedMerit g (fullSubRightCost g) <
          fullSubHighTestFreeMerit g)
    (hhighAtLowRoot :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowTestBasedMerit g c = fullSubLowTestFreeMerit g →
          fullSubHighTestFreeMerit g <
            fullSubHighTestBasedMerit g c)
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
            populationShare groupB * subSubMerit J2 groupB) :=
  let hcomponents :=
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_feasible_components_of_base_survivor_merits
      (api := api) (subEstimateLaw := subEstimateLaw)
      (subSubMass := subSubMass) (subFullMass := subFullMass)
      (subSubMerit := subSubMerit) (subFullMeritBase := subFullMeritBase)
      (fullSubMeritFallback := fullSubMeritFallback)
      (fullFullMeritFallback := fullFullMeritFallback)
      (diversity := diversity) (J1 := J1) (J2 := J2)
      (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold (capacity1 := capacity1)
      (q1Sub := q1Sub) hshareA hshareB hcapacity1 hfillFullFull1
      hJ2MeritGtB_base hJ2MeritGtA_base
  paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval
    api subEstimateLaw subSubMass subFullMass subSubMerit
    (glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff J2
      subFullMeritBase)
    fullSubMeritFallback fullFullMeritFallback diversity
    (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost) (capacity1 := capacity1)
    (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
    (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
    (feasible1 := feasible1) (feasible2 := feasible2)
    C J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
    J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
    hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
    hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision hJ2ThresholdMean
    hJ2Threshold subFullTestBasedMerit subFullTestFreeMerit
    fullSubLowTestBasedMerit fullSubLowTestFreeMerit
    fullSubHighTestBasedMerit fullSubHighTestFreeMerit
    hsubFullLeftRight hsubFullLeftPos hsubFullCostMem hsubFullCont
    hsubFullAnti hsubFullAtLeft hsubFullAtRight hfullSubLeftRight
    hfullSubLeftPos hfullSubCostMem hlowCont hlowAnti hlowAtLeft
    hlowAtRight hhighCont hhighAnti hhighAtLeft hhighAtRight
    hhighAtLowRoot hshareA hshareB hcapacity1 hfillFullFull1 hcapacity2
    hfillFullFull2 hcomponents.1 hcomponents.2.1 hcomponents.2.2.1
    hcomponents.2.2.2

/--
Proposition-5 policy-state-table interval endpoint with school-`J2`
condition (12) stated on the paper source component tables.

This is the two-interior-interval analogue of
`paper_theorem3_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill`.
It also rewrites the full/full fill assumptions into the displayed
`K_g(q_i^*)` notation, so callers do not need to mention the generated surface
mass terms.
-/
abbrev
    paper_theorem3_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval
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
    {populationShare testCost subFullLeftCost subFullRightCost
      fullSubLeftCost fullSubRightCost : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
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
    (fullSubLowTestBasedMerit : Group → ℝ → ℝ)
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestBasedMerit : Group → ℝ → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
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
    (hlowCont :
      ∀ g, ContinuousOn (fullSubLowTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hlowAnti :
      ∀ g, StrictAntiOn (fullSubLowTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hlowAtLeft :
      ∀ g,
        fullSubLowTestFreeMerit g <
          fullSubLowTestBasedMerit g (fullSubLeftCost g))
    (hlowAtRight :
      ∀ g,
        fullSubLowTestBasedMerit g (fullSubRightCost g) <
          fullSubLowTestFreeMerit g)
    (hhighCont :
      ∀ g, ContinuousOn (fullSubHighTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hhighAnti :
      ∀ g, StrictAntiOn (fullSubHighTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hhighAtLeft :
      ∀ g,
        fullSubHighTestFreeMerit g <
          fullSubHighTestBasedMerit g (fullSubLeftCost g))
    (hhighAtRight :
      ∀ g,
        fullSubHighTestBasedMerit g (fullSubRightCost g) <
          fullSubHighTestFreeMerit g)
    (hhighAtLowRoot :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowTestBasedMerit g c = fullSubLowTestFreeMerit g →
          fullSubHighTestFreeMerit g <
            fullSubHighTestBasedMerit g c)
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
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare testCost
          fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
          J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
          J2DropThreshold J2KeepThreshold q1Sub costThreshold groupA →
        subFullMeritFallback J2 groupA = 0)
    (hJ2MassB_component :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare testCost
          fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
          J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
          J2DropThreshold J2KeepThreshold q1Sub costThreshold groupA →
        subFullMass groupB ≥ capacity2)
    (hJ2MeritGtB_component :
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
    (hJ2ZeroB_component :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare testCost
          fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
          J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
          J2DropThreshold J2KeepThreshold q1Sub costThreshold groupB →
        subFullMeritFallback J2 groupB = 0)
    (hJ2MassA_component :
      ∀ costThreshold : Group → ℝ,
        glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
          subEstimateLaw subSubMass subFullMass subSubMerit
          subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
          diversity J1 J2 groupA groupB populationShare testCost
          fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
          J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
          J2DropThreshold J2KeepThreshold q1Sub costThreshold groupB →
        subFullMass groupA ≥ capacity2)
    (hJ2MeritGtA_component :
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
            populationShare groupB * subSubMerit J2 groupB) :=
  fun honlyA_J1_groupB_eq honlyA_J1_groupA_testBased
      honlyA_J1_groupA_testFree honlyB_J1_groupA_eq
      honlyB_J1_groupB_testBased honlyB_J1_groupB_testFree =>
  paper_theorem3_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_subFull_fullSub_interval
    api subEstimateLaw subSubMass subFullMass subSubMerit
    subFullMeritFallback fullSubMeritFallback fullFullMeritFallback diversity
    (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost) (capacity1 := capacity1)
    (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
    (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
    C J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
    J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
    hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
    hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision hJ2ThresholdMean
    hJ2Threshold subFullTestBasedMerit subFullTestFreeMerit
    fullSubLowTestBasedMerit fullSubLowTestFreeMerit
    fullSubHighTestBasedMerit fullSubHighTestFreeMerit
    hsubFullLeftRight hsubFullLeftPos hsubFullCostMem hsubFullCont
    hsubFullAnti hsubFullAtLeft hsubFullAtRight hfullSubLeftRight
    hfullSubLeftPos hfullSubCostMem hlowCont hlowAnti hlowAtLeft
    hlowAtRight hhighCont hhighAnti hhighAtLeft hhighAtRight
    hhighAtLowRoot hshareA hshareB hcapacity1
    (by
      simpa [glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass,
        glm20StrategicPolicyStateMass,
        glm20StrategicSubEstimateMassAbove] using hfillFullFull1)
    hcapacity2
    (by
      simpa [glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass,
        glm20StrategicPolicyStateMass,
        glm20StrategicSubEstimateMassAbove] using hfillFullFull2)
    honlyA_J1_groupB_eq honlyA_J1_groupA_testBased
    honlyA_J1_groupA_testFree honlyB_J1_groupA_eq
    honlyB_J1_groupB_testBased honlyB_J1_groupB_testFree
    (by
      intro costThreshold hdropA
      have hdropA' :
          glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare testCost
            fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
            J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
            J2DropThreshold J2KeepThreshold q1Sub costThreshold groupA := by
        simpa [glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands,
          glm20Theorem3SourceFamilyPolicyStateTableSurface] using hdropA
      have hzero := hJ2ZeroA_component costThreshold hdropA'
      have hJ2_ne_J1 : J2 ≠ J1 := by
        intro h
        exact hJ1_ne_J2 h.symm
      simp [glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ2_ne_J1, hzero])
    (by
      intro costThreshold hdropA
      have hdropA' :
          glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare testCost
            fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
            J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
            J2DropThreshold J2KeepThreshold q1Sub costThreshold groupA := by
        simpa [glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands,
          glm20Theorem3SourceFamilyPolicyStateTableSurface] using hdropA
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass,
        glm20StrategicPolicyStateMass] using
          hJ2MassB_component costThreshold hdropA')
    (by
      intro costThreshold hdropA
      have hdropA' :
          glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare testCost
            fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
            J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
            J2DropThreshold J2KeepThreshold q1Sub costThreshold groupA := by
        simpa [glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands,
          glm20Theorem3SourceFamilyPolicyStateTableSurface] using hdropA
      have hgt := hJ2MeritGtB_component costThreshold hdropA'
      have hJ2_ne_J1 : J2 ≠ J1 := by
        intro h
        exact hJ1_ne_J2 h.symm
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ2_ne_J1] using hgt)
    (by
      intro costThreshold hdropB
      have hdropB' :
          glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare testCost
            fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
            J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
            J2DropThreshold J2KeepThreshold q1Sub costThreshold groupB := by
        simpa [glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands,
          glm20Theorem3SourceFamilyPolicyStateTableSurface] using hdropB
      have hzero := hJ2ZeroB_component costThreshold hdropB'
      have hJ2_ne_J1 : J2 ≠ J1 := by
        intro h
        exact hJ1_ne_J2 h.symm
      simp [glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ2_ne_J1, hzero])
    (by
      intro costThreshold hdropB
      have hdropB' :
          glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare testCost
            fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
            J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
            J2DropThreshold J2KeepThreshold q1Sub costThreshold groupB := by
        simpa [glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands,
          glm20Theorem3SourceFamilyPolicyStateTableSurface] using hdropB
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20Theorem3PolicyStateCutoffMass,
        glm20StrategicPolicyStateMass] using
          hJ2MassA_component costThreshold hdropB')
    (by
      intro costThreshold hdropB
      have hdropB' :
          glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands api
            subEstimateLaw subSubMass subFullMass subSubMerit
            subFullMeritFallback fullSubMeritFallback fullFullMeritFallback
            diversity J1 J2 groupA groupB populationShare testCost
            fullFullCutoff fullSubCutoff C J1DropFamily J2DropFamily
            J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
            J2DropThreshold J2KeepThreshold q1Sub costThreshold groupB := by
        simpa [glm20Theorem3SourceFamilyPolicyStateTableSubFullExpands,
          glm20Theorem3SourceFamilyPolicyStateTableSurface] using hdropB
      have hgt := hJ2MeritGtA_component costThreshold hdropB'
      have hJ2_ne_J1 : J2 ≠ J1 := by
        intro h
        exact hJ1_ne_J2 h.symm
      simpa [glm20Theorem3SourceFamilyPolicyStateTableSurface,
        glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface,
        glm20Theorem3PolicyStateWeightedAcademicMeritSurface,
        glm20WeightedAcademicMeritBinaryPolicySurface,
        glm20StrategicPolicyStateAdmittedMerit,
        glm20Theorem3SourceFamilySubFullMeritTable,
        glm20OverrideSchoolMeritRow, hJ2_ne_J1] using hgt)

/--
Proposition-5 policy-state-table interval endpoint with the school-`J2`
zero expanding-group row built into the source model.

This is the same theorem as
`paper_theorem3_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval`,
but `L_2^g(P_sub,P_full)=0` for the condition-(10) expanding group is no
longer a caller assumption.  The source table
`glm20Theorem3SourceFamilySubFullJ2ZeroFallback` makes it definitional from
the cutoff case.  The remaining school-`J2` premises are exactly the paper's
surviving-group capacity and strict weighted-merit comparisons, stated on the
base survivor row.
-/
abbrev
    paper_theorem3_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_subFull_fullSub_interval
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
    {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost subFullLeftCost subFullRightCost
      fullSubLeftCost fullSubRightCost : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
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
    (fullSubLowTestBasedMerit : Group → ℝ → ℝ)
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestBasedMerit : Group → ℝ → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
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
    (hlowCont :
      ∀ g, ContinuousOn (fullSubLowTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hlowAnti :
      ∀ g, StrictAntiOn (fullSubLowTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hlowAtLeft :
      ∀ g,
        fullSubLowTestFreeMerit g <
          fullSubLowTestBasedMerit g (fullSubLeftCost g))
    (hlowAtRight :
      ∀ g,
        fullSubLowTestBasedMerit g (fullSubRightCost g) <
          fullSubLowTestFreeMerit g)
    (hhighCont :
      ∀ g, ContinuousOn (fullSubHighTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hhighAnti :
      ∀ g, StrictAntiOn (fullSubHighTestBasedMerit g)
        (Set.Icc (fullSubLeftCost g) (fullSubRightCost g)))
    (hhighAtLeft :
      ∀ g,
        fullSubHighTestFreeMerit g <
          fullSubHighTestBasedMerit g (fullSubLeftCost g))
    (hhighAtRight :
      ∀ g,
        fullSubHighTestBasedMerit g (fullSubRightCost g) <
          fullSubHighTestFreeMerit g)
    (hhighAtLowRoot :
      ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
        fullSubLowTestBasedMerit g c = fullSubLowTestFreeMerit g →
          fullSubHighTestFreeMerit g <
            fullSubHighTestBasedMerit g c)
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
            populationShare groupB * subSubMerit J2 groupB) := by
  let subFullMeritFallback :=
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback q1Sub fullFullCutoff J2
      subFullMeritBase
  let hcomponents :=
    glm20Theorem3SourceFamilySubFullJ2ZeroFallback_components_of_base_survivor_components
      (api := api) (subEstimateLaw := subEstimateLaw)
      (subSubMass := subSubMass) (subFullMass := subFullMass)
      (subSubMerit := subSubMerit) (subFullMeritBase := subFullMeritBase)
      (fullSubMeritFallback := fullSubMeritFallback)
      (fullFullMeritFallback := fullFullMeritFallback)
      (diversity := diversity) (J1 := J1) (J2 := J2)
      (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) C J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold (capacity1 := capacity1)
      (capacity2 := capacity2) (q1Sub := q1Sub) hshareA hshareB
      hcapacity1 hfillFullFull1 hJ2MassB_base hJ2MeritGtB_base
      hJ2MassA_base hJ2MeritGtA_base
  exact
    paper_theorem3_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval
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
      C J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision hJ2ThresholdMean
      hJ2Threshold subFullTestBasedMerit subFullTestFreeMerit
      fullSubLowTestBasedMerit fullSubLowTestFreeMerit
      fullSubHighTestBasedMerit fullSubHighTestFreeMerit
      hsubFullLeftRight hsubFullLeftPos hsubFullCostMem hsubFullCont
      hsubFullAnti hsubFullAtLeft hsubFullAtRight hfullSubLeftRight
      hfullSubLeftPos hfullSubCostMem hlowCont hlowAnti hlowAtLeft
      hlowAtRight hhighCont hhighAnti hhighAtLeft hhighAtRight
      hhighAtLowRoot hshareA hshareB hcapacity1 hfillFullFull1
      hcapacity2 hfillFullFull2 hcomponents.1 hcomponents.2.1
      hcomponents.2.2.1 hcomponents.2.2.2.1 hcomponents.2.2.2.2.1
      hcomponents.2.2.2.2.2

/--
Standard-Gaussian feasibility-aware Theorem 3 component-table endpoint with
equation-(50) sub-full regularity and equation-(46) low/high full/full cutoffs
constructed internally.

This is the component-table analogue of
`paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval`.
The remaining arguments are the paper's endpoint-crossing, strategic branch,
feasibility, and source component-table condition-(12) premises, stated against
the equation-(46) cutoffs Lean constructs from the standard Gaussian API.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
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
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
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
  let hregular :=
    paper_theorem3_source_cost_merit_regularities_of_equation50_and_standardGaussian_twoFull
      standardGaussianQuantileAPI
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (subFullQ2Full := subFullQ2Full)
      (subFullScale := subFullScale) (subFullV2 := subFullV2)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (lowQ1Full := fullSubLowQ1Full)
      (lowQ2Full := fullSubLowQ2Full)
      (lowScale := fullSubLowScale) (lowV1 := fullSubLowV1)
      (lowV2 := fullSubLowV2)
      (highQ1Full := fullSubHighQ1Full)
      (highQ2Full := fullSubHighQ2Full)
      (highScale := fullSubHighScale) (highV1 := fullSubHighV1)
      (highV2 := fullSubHighV2) subFullMeritOfCutoff
      fullSubLowMeritOfCutoff fullSubHighMeritOfCutoff
      hsubFullLeftRight hsubFullScale hsubFullLeftPos
      hsubFullRightLtV2 hsubFullMeritCont hsubFullMeritAnti
      hfullSubLeftRight hfullSubLeftPos hfullSubLowScale
      hfullSubLowV2Pos hfullSubLowV2LtV1 hfullSubLowRightLtV1
      hfullSubLowMeritCont hfullSubLowMeritAnti hfullSubHighScale
      hfullSubHighV2Pos hfullSubHighV2LtV1 hfullSubHighRightLtV1
      hfullSubHighMeritCont hfullSubHighMeritAnti
  let fullSubLowCutoffOfCost : Group → ℝ → ℝ :=
    Classical.choose hregular
  let hregular' := Classical.choose_spec hregular
  let fullSubHighCutoffOfCost : Group → ℝ → ℝ :=
    Classical.choose hregular'
  let hspec := Classical.choose_spec hregular'
  let subFullRegular := hspec.2.2.1
  let lowRegular := hspec.2.2.2.1
  let highRegular := hspec.2.2.2.2
  let subFullTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    subFullMeritOfCutoff g
      (subFullQ2Full g -
        subFullScale g *
          standardGaussianQuantileAPI.quantile
            (1 - cost / subFullV2 g))
  let fullSubLowTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g cost)
  let fullSubHighTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g cost)
  fun
      (hfullSubLowAtLeft :
        ∀ g,
          fullSubLowTestFreeMerit g <
            fullSubLowMeritOfCutoff g
              (fullSubLowCutoffOfCost g (fullSubLeftCost g)))
      (hfullSubLowAtRight :
        ∀ g,
          fullSubLowMeritOfCutoff g
              (fullSubLowCutoffOfCost g (fullSubRightCost g)) <
            fullSubLowTestFreeMerit g)
      (hfullSubHighAtLeft :
        ∀ g,
          fullSubHighTestFreeMerit g <
            fullSubHighMeritOfCutoff g
              (fullSubHighCutoffOfCost g (fullSubLeftCost g)))
      (hfullSubHighAtRight :
        ∀ g,
          fullSubHighMeritOfCutoff g
              (fullSubHighCutoffOfCost g (fullSubRightCost g)) <
            fullSubHighTestFreeMerit g)
      (hfullSubHighAtLowRoot :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g c) =
              fullSubLowTestFreeMerit g →
            fullSubHighTestFreeMerit g <
              fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g c))
      hJ2ZeroA_component hJ2MeritGtB_component hJ2ZeroB_component
      hJ2MeritGtA_component =>
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval
      subEstimateLaw subSubMass subFullMass subSubMerit
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
      (feasible1 := feasible1) (feasible2 := feasible2)
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision
      hJ2ThresholdMean hJ2Threshold subFullTestBasedMerit
      subFullTestFreeMerit fullSubLowTestBasedMerit
      fullSubLowTestFreeMerit fullSubHighTestBasedMerit
      fullSubHighTestFreeMerit hsubFullLeftRight hsubFullLeftPos
      hsubFullCostMem (fun g => (subFullRegular g).1)
      (fun g => (subFullRegular g).2)
      (by
        intro g
        simpa [subFullTestBasedMerit] using hsubFullAtLeft g)
      (by
        intro g
        simpa [subFullTestBasedMerit] using hsubFullAtRight g)
      hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
      (fun g => (lowRegular g).1) (fun g => (lowRegular g).2)
      (by
        intro g
        simpa [fullSubLowTestBasedMerit] using hfullSubLowAtLeft g)
      (by
        intro g
        simpa [fullSubLowTestBasedMerit] using hfullSubLowAtRight g)
      (fun g => (highRegular g).1) (fun g => (highRegular g).2)
      (by
        intro g
        simpa [fullSubHighTestBasedMerit] using hfullSubHighAtLeft g)
      (by
        intro g
        simpa [fullSubHighTestBasedMerit] using hfullSubHighAtRight g)
      (by
        intro g c hc hlow
        simpa [fullSubLowTestBasedMerit, fullSubHighTestBasedMerit] using
          hfullSubHighAtLowRoot g c hc hlow)
      hshareA hshareB hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
      hJ2ZeroA_component hJ2MeritGtB_component hJ2ZeroB_component
      hJ2MeritGtA_component

/--
Standard-Gaussian feasibility-aware Theorem 3 endpoint with the school-`J2`
zero expanding-group row built into the source model.

Equation-(50) sub-full regularity and equation-(46) low/high full/full cutoffs
are constructed internally.  Compared with the component-table endpoint above,
the caller no longer supplies the expanding-group zero component assumptions;
the visible school-`J2` premises are the two strict survivor-merit comparisons
on the paper's base sub/full merit row.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval
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
      fullSubLeftCost fullSubRightCost : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
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
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
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
  let hregular :=
    paper_theorem3_source_cost_merit_regularities_of_equation50_and_standardGaussian_twoFull
      standardGaussianQuantileAPI
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (subFullQ2Full := subFullQ2Full)
      (subFullScale := subFullScale) (subFullV2 := subFullV2)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (lowQ1Full := fullSubLowQ1Full)
      (lowQ2Full := fullSubLowQ2Full)
      (lowScale := fullSubLowScale) (lowV1 := fullSubLowV1)
      (lowV2 := fullSubLowV2)
      (highQ1Full := fullSubHighQ1Full)
      (highQ2Full := fullSubHighQ2Full)
      (highScale := fullSubHighScale) (highV1 := fullSubHighV1)
      (highV2 := fullSubHighV2) subFullMeritOfCutoff
      fullSubLowMeritOfCutoff fullSubHighMeritOfCutoff
      hsubFullLeftRight hsubFullScale hsubFullLeftPos
      hsubFullRightLtV2 hsubFullMeritCont hsubFullMeritAnti
      hfullSubLeftRight hfullSubLeftPos hfullSubLowScale
      hfullSubLowV2Pos hfullSubLowV2LtV1 hfullSubLowRightLtV1
      hfullSubLowMeritCont hfullSubLowMeritAnti hfullSubHighScale
      hfullSubHighV2Pos hfullSubHighV2LtV1 hfullSubHighRightLtV1
      hfullSubHighMeritCont hfullSubHighMeritAnti
  let fullSubLowCutoffOfCost : Group → ℝ → ℝ :=
    Classical.choose hregular
  let hregular' := Classical.choose_spec hregular
  let fullSubHighCutoffOfCost : Group → ℝ → ℝ :=
    Classical.choose hregular'
  let hspec := Classical.choose_spec hregular'
  let subFullRegular := hspec.2.2.1
  let lowRegular := hspec.2.2.2.1
  let highRegular := hspec.2.2.2.2
  let subFullTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    subFullMeritOfCutoff g
      (subFullQ2Full g -
        subFullScale g *
          standardGaussianQuantileAPI.quantile
            (1 - cost / subFullV2 g))
  let fullSubLowTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g cost)
  let fullSubHighTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g cost)
  fun
      (hfullSubLowAtLeft :
        ∀ g,
          fullSubLowTestFreeMerit g <
            fullSubLowMeritOfCutoff g
              (fullSubLowCutoffOfCost g (fullSubLeftCost g)))
      (hfullSubLowAtRight :
        ∀ g,
          fullSubLowMeritOfCutoff g
              (fullSubLowCutoffOfCost g (fullSubRightCost g)) <
            fullSubLowTestFreeMerit g)
      (hfullSubHighAtLeft :
        ∀ g,
          fullSubHighTestFreeMerit g <
            fullSubHighMeritOfCutoff g
              (fullSubHighCutoffOfCost g (fullSubLeftCost g)))
      (hfullSubHighAtRight :
        ∀ g,
          fullSubHighMeritOfCutoff g
              (fullSubHighCutoffOfCost g (fullSubRightCost g)) <
            fullSubHighTestFreeMerit g)
      (hfullSubHighAtLowRoot :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g c) =
              fullSubLowTestFreeMerit g →
            fullSubHighTestFreeMerit g <
              fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g c))
      hJ2MeritGtB_base hJ2MeritGtA_base =>
    paper_theorem3_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_subFull_fullSub_interval
      standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
      subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost) (capacity1 := capacity1)
      (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
      (feasible1 := feasible1) (feasible2 := feasible2)
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision
      hJ2ThresholdMean hJ2Threshold subFullTestBasedMerit
      subFullTestFreeMerit fullSubLowTestBasedMerit
      fullSubLowTestFreeMerit fullSubHighTestBasedMerit
      fullSubHighTestFreeMerit hsubFullLeftRight hsubFullLeftPos
      hsubFullCostMem (fun g => (subFullRegular g).1)
      (fun g => (subFullRegular g).2)
      (by
        intro g
        simpa [subFullTestBasedMerit] using hsubFullAtLeft g)
      (by
        intro g
        simpa [subFullTestBasedMerit] using hsubFullAtRight g)
      hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
      (fun g => (lowRegular g).1) (fun g => (lowRegular g).2)
      (by
        intro g
        simpa [fullSubLowTestBasedMerit] using hfullSubLowAtLeft g)
      (by
        intro g
        simpa [fullSubLowTestBasedMerit] using hfullSubLowAtRight g)
      (fun g => (highRegular g).1) (fun g => (highRegular g).2)
      (by
        intro g
        simpa [fullSubHighTestBasedMerit] using hfullSubHighAtLeft g)
      (by
        intro g
        simpa [fullSubHighTestBasedMerit] using hfullSubHighAtRight g)
      (by
        intro g c hc hlow
        simpa [fullSubLowTestBasedMerit, fullSubHighTestBasedMerit] using
          hfullSubHighAtLowRoot g c hc hlow)
      hshareA hshareB hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
      hJ2MeritGtB_base hJ2MeritGtA_base

/--
Standard-Gaussian feasibility-aware Theorem 3 endpoint with raw survivor-merit
condition-(12) inequalities.

The constructed endpoint above asks for the survivor-merit inequalities after
conditioning on which group expands.  The displayed inequalities themselves do
not mention the branch witness; this wrapper exposes them in that paper-shaped
unconditional form and supplies the branch-conditioned premises by weakening.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval_of_raw_survivor_merits
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
      fullSubLeftCost fullSubRightCost : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    {feasible1 feasible2 :
      GLM20StrategicPolicyState → GLM20StrategicPolicyState → Prop}
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
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
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
  let endpoint :=
    paper_theorem3_standardGaussian_source_conditions_of_feasible_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval
      subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback
      diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost) (capacity1 := capacity1)
      (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
      (feasible1 := feasible1) (feasible2 := feasible2)
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
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision
      hJ2ThresholdMean hJ2Threshold subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowMeritOfCutoff
      fullSubHighMeritOfCutoff fullSubLowTestFreeMerit
      fullSubHighTestFreeMerit hsubFullLeftRight hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullScale
      hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft
      hsubFullAtRight hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
      hfullSubLowScale hfullSubLowV2Pos hfullSubLowV2LtV1
      hfullSubLowRightLtV1 hfullSubLowMeritCont hfullSubLowMeritAnti
      hfullSubHighScale hfullSubHighV2Pos hfullSubHighV2LtV1
      hfullSubHighRightLtV1 hfullSubHighMeritCont
      hfullSubHighMeritAnti hshareA hshareB hcapacity1 hfillFullFull1
      hcapacity2 hfillFullFull2
  fun hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight hfullSubHighAtLowRoot hJ2MeritGtB hJ2MeritGtA =>
    endpoint hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight hfullSubHighAtLowRoot
      (fun _ _ => hJ2MeritGtB)
      (fun _ _ => hJ2MeritGtA)

/--
Standard-Gaussian Proposition-5 Theorem 3 component-table endpoint with
equation-(50) sub-full regularity and equation-(46) low/high full/full cutoffs
constructed internally.

Compared with the feasibility-aware constructed endpoint, this lands on the
paper's strategic Proposition 5 policy-state-table route.  The remaining
condition-(12) assumptions are exactly the source component-table zero, mass,
and strict-surviving-merit premises for the expanding group branch.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval
    {Group School FeatureDrop FeatureKeep : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
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
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
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
  let hregular :=
    paper_theorem3_source_cost_merit_regularities_of_equation50_and_standardGaussian_twoFull
      standardGaussianQuantileAPI
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (subFullQ2Full := subFullQ2Full)
      (subFullScale := subFullScale) (subFullV2 := subFullV2)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (lowQ1Full := fullSubLowQ1Full)
      (lowQ2Full := fullSubLowQ2Full)
      (lowScale := fullSubLowScale) (lowV1 := fullSubLowV1)
      (lowV2 := fullSubLowV2)
      (highQ1Full := fullSubHighQ1Full)
      (highQ2Full := fullSubHighQ2Full)
      (highScale := fullSubHighScale) (highV1 := fullSubHighV1)
      (highV2 := fullSubHighV2) subFullMeritOfCutoff
      fullSubLowMeritOfCutoff fullSubHighMeritOfCutoff
      hsubFullLeftRight hsubFullScale hsubFullLeftPos
      hsubFullRightLtV2 hsubFullMeritCont hsubFullMeritAnti
      hfullSubLeftRight hfullSubLeftPos hfullSubLowScale
      hfullSubLowV2Pos hfullSubLowV2LtV1 hfullSubLowRightLtV1
      hfullSubLowMeritCont hfullSubLowMeritAnti hfullSubHighScale
      hfullSubHighV2Pos hfullSubHighV2LtV1 hfullSubHighRightLtV1
      hfullSubHighMeritCont hfullSubHighMeritAnti
  let fullSubLowCutoffOfCost : Group → ℝ → ℝ :=
    Classical.choose hregular
  let hregular' := Classical.choose_spec hregular
  let fullSubHighCutoffOfCost : Group → ℝ → ℝ :=
    Classical.choose hregular'
  let hspec := Classical.choose_spec hregular'
  let subFullRegular := hspec.2.2.1
  let lowRegular := hspec.2.2.2.1
  let highRegular := hspec.2.2.2.2
  let subFullTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    subFullMeritOfCutoff g
      (subFullQ2Full g -
        subFullScale g *
          standardGaussianQuantileAPI.quantile
            (1 - cost / subFullV2 g))
  let fullSubLowTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g cost)
  let fullSubHighTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g cost)
  fun
      (hfullSubLowAtLeft :
        ∀ g,
          fullSubLowTestFreeMerit g <
            fullSubLowMeritOfCutoff g
              (fullSubLowCutoffOfCost g (fullSubLeftCost g)))
      (hfullSubLowAtRight :
        ∀ g,
          fullSubLowMeritOfCutoff g
              (fullSubLowCutoffOfCost g (fullSubRightCost g)) <
            fullSubLowTestFreeMerit g)
      (hfullSubHighAtLeft :
        ∀ g,
          fullSubHighTestFreeMerit g <
            fullSubHighMeritOfCutoff g
              (fullSubHighCutoffOfCost g (fullSubLeftCost g)))
      (hfullSubHighAtRight :
        ∀ g,
          fullSubHighMeritOfCutoff g
              (fullSubHighCutoffOfCost g (fullSubRightCost g)) <
            fullSubHighTestFreeMerit g)
      (hfullSubHighAtLowRoot :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g c) =
              fullSubLowTestFreeMerit g →
            fullSubHighTestFreeMerit g <
              fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g c))
      hJ2ZeroA_component hJ2MassB_component hJ2MeritGtB_component
      hJ2ZeroB_component hJ2MassA_component hJ2MeritGtA_component =>
    paper_theorem3_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_subFull_fullSub_interval
      standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
      subSubMerit subFullMeritFallback fullSubMeritFallback
      fullFullMeritFallback diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost) (capacity1 := capacity1)
      (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision
      hJ2ThresholdMean hJ2Threshold subFullTestBasedMerit
      subFullTestFreeMerit fullSubLowTestBasedMerit
      fullSubLowTestFreeMerit fullSubHighTestBasedMerit
      fullSubHighTestFreeMerit hsubFullLeftRight hsubFullLeftPos
      hsubFullCostMem (fun g => (subFullRegular g).1)
      (fun g => (subFullRegular g).2)
      (by
        intro g
        simpa [subFullTestBasedMerit] using hsubFullAtLeft g)
      (by
        intro g
        simpa [subFullTestBasedMerit] using hsubFullAtRight g)
      hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
      (fun g => (lowRegular g).1) (fun g => (lowRegular g).2)
      (by
        intro g
        simpa [fullSubLowTestBasedMerit] using hfullSubLowAtLeft g)
      (by
        intro g
        simpa [fullSubLowTestBasedMerit] using hfullSubLowAtRight g)
      (fun g => (highRegular g).1) (fun g => (highRegular g).2)
      (by
        intro g
        simpa [fullSubHighTestBasedMerit] using hfullSubHighAtLeft g)
      (by
        intro g
        simpa [fullSubHighTestBasedMerit] using hfullSubHighAtRight g)
      (by
        intro g c hc hlow
        simpa [fullSubLowTestBasedMerit, fullSubHighTestBasedMerit] using
          hfullSubHighAtLowRoot g c hc hlow)
      hshareA hshareB hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
      hJ2ZeroA_component hJ2MassB_component hJ2MeritGtB_component
      hJ2ZeroB_component hJ2MassA_component hJ2MeritGtA_component

/--
Standard-Gaussian Proposition-5 Theorem 3 endpoint with the school-`J2`
zero expanding-group row built into the source model.

This strengthens
`paper_theorem3_standardGaussian_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_subfull_components_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval`:
equation-(50) sub-full regularity and equation-(46) low/high full/full cutoffs
are still constructed internally, but the caller no longer supplies the
expanding-group zero component assumptions.  The remaining school-`J2`
premises are the survivor capacity and strict survivor-merit comparisons on
the paper's base sub/full merit row.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval
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
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
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
  let hregular :=
    paper_theorem3_source_cost_merit_regularities_of_equation50_and_standardGaussian_twoFull
      standardGaussianQuantileAPI
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (subFullQ2Full := subFullQ2Full)
      (subFullScale := subFullScale) (subFullV2 := subFullV2)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (lowQ1Full := fullSubLowQ1Full)
      (lowQ2Full := fullSubLowQ2Full)
      (lowScale := fullSubLowScale) (lowV1 := fullSubLowV1)
      (lowV2 := fullSubLowV2)
      (highQ1Full := fullSubHighQ1Full)
      (highQ2Full := fullSubHighQ2Full)
      (highScale := fullSubHighScale) (highV1 := fullSubHighV1)
      (highV2 := fullSubHighV2) subFullMeritOfCutoff
      fullSubLowMeritOfCutoff fullSubHighMeritOfCutoff
      hsubFullLeftRight hsubFullScale hsubFullLeftPos
      hsubFullRightLtV2 hsubFullMeritCont hsubFullMeritAnti
      hfullSubLeftRight hfullSubLeftPos hfullSubLowScale
      hfullSubLowV2Pos hfullSubLowV2LtV1 hfullSubLowRightLtV1
      hfullSubLowMeritCont hfullSubLowMeritAnti hfullSubHighScale
      hfullSubHighV2Pos hfullSubHighV2LtV1 hfullSubHighRightLtV1
      hfullSubHighMeritCont hfullSubHighMeritAnti
  let fullSubLowCutoffOfCost : Group → ℝ → ℝ :=
    Classical.choose hregular
  let hregular' := Classical.choose_spec hregular
  let fullSubHighCutoffOfCost : Group → ℝ → ℝ :=
    Classical.choose hregular'
  let hspec := Classical.choose_spec hregular'
  let subFullRegular := hspec.2.2.1
  let lowRegular := hspec.2.2.2.1
  let highRegular := hspec.2.2.2.2
  let subFullTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    subFullMeritOfCutoff g
      (subFullQ2Full g -
        subFullScale g *
          standardGaussianQuantileAPI.quantile
            (1 - cost / subFullV2 g))
  let fullSubLowTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g cost)
  let fullSubHighTestBasedMerit : Group → ℝ → ℝ := fun g cost =>
    fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g cost)
  fun
      (hfullSubLowAtLeft :
        ∀ g,
          fullSubLowTestFreeMerit g <
            fullSubLowMeritOfCutoff g
              (fullSubLowCutoffOfCost g (fullSubLeftCost g)))
      (hfullSubLowAtRight :
        ∀ g,
          fullSubLowMeritOfCutoff g
              (fullSubLowCutoffOfCost g (fullSubRightCost g)) <
            fullSubLowTestFreeMerit g)
      (hfullSubHighAtLeft :
        ∀ g,
          fullSubHighTestFreeMerit g <
            fullSubHighMeritOfCutoff g
              (fullSubHighCutoffOfCost g (fullSubLeftCost g)))
      (hfullSubHighAtRight :
        ∀ g,
          fullSubHighMeritOfCutoff g
              (fullSubHighCutoffOfCost g (fullSubRightCost g)) <
            fullSubHighTestFreeMerit g)
      (hfullSubHighAtLowRoot :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g c) =
              fullSubLowTestFreeMerit g →
            fullSubHighTestFreeMerit g <
              fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g c))
      hJ2MassB_base hJ2MeritGtB_base hJ2MassA_base hJ2MeritGtA_base =>
    paper_theorem3_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_subFull_fullSub_interval
      standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
      subSubMerit subFullMeritBase fullSubMeritFallback
      fullFullMeritFallback diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost) (capacity1 := capacity1)
      (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision
      hJ2ThresholdMean hJ2Threshold subFullTestBasedMerit
      subFullTestFreeMerit fullSubLowTestBasedMerit
      fullSubLowTestFreeMerit fullSubHighTestBasedMerit
      fullSubHighTestFreeMerit hsubFullLeftRight hsubFullLeftPos
      hsubFullCostMem (fun g => (subFullRegular g).1)
      (fun g => (subFullRegular g).2)
      (by
        intro g
        simpa [subFullTestBasedMerit] using hsubFullAtLeft g)
      (by
        intro g
        simpa [subFullTestBasedMerit] using hsubFullAtRight g)
      hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
      (fun g => (lowRegular g).1) (fun g => (lowRegular g).2)
      (by
        intro g
        simpa [fullSubLowTestBasedMerit] using hfullSubLowAtLeft g)
      (by
        intro g
        simpa [fullSubLowTestBasedMerit] using hfullSubLowAtRight g)
      (fun g => (highRegular g).1) (fun g => (highRegular g).2)
      (by
        intro g
        simpa [fullSubHighTestBasedMerit] using hfullSubHighAtLeft g)
      (by
        intro g
        simpa [fullSubHighTestBasedMerit] using hfullSubHighAtRight g)
      (by
        intro g c hc hlow
        simpa [fullSubLowTestBasedMerit, fullSubHighTestBasedMerit] using
          hfullSubHighAtLowRoot g c hc hlow)
      hshareA hshareB hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
      hJ2MassB_base (fun _ _ => hJ2MeritGtB_base)
      hJ2MassA_base (fun _ _ => hJ2MeritGtA_base)

/--
Standard-Gaussian Proposition-5 Theorem 3 endpoint with raw survivor
condition-(12) premises.

This is the paper-facing form of
`paper_theorem3_standardGaussian_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval`.
The constructed endpoint still proves the branch-conditioned obligations, but
this wrapper exposes the survivor mass and survivor-merit premises as the four
unconditional source-row inequalities displayed in the paper.
-/
abbrev
    paper_theorem3_standardGaussian_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval_of_raw_survivor_conditions
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
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
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
  let endpoint :=
    paper_theorem3_standardGaussian_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval
      subEstimateLaw subSubMass subFullMass subSubMerit
      subFullMeritBase fullSubMeritFallback fullFullMeritFallback diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost) (capacity1 := capacity1)
      (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff) (fullSubCutoff := fullSubCutoff)
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
      J1DropFamily J2DropFamily J1KeepFamily J2KeepFamily
      J1DropThreshold J1KeepThreshold J2DropThreshold J2KeepThreshold
      hJ1_ne_J2 hJ1PriorMean hJ1PriorVar hJ1Precision hJ1ThresholdMean
      hJ1Threshold hJ2PriorMean hJ2PriorVar hJ2Precision
      hJ2ThresholdMean hJ2Threshold subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowMeritOfCutoff
      fullSubHighMeritOfCutoff fullSubLowTestFreeMerit
      fullSubHighTestFreeMerit hsubFullLeftRight hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullScale
      hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft
      hsubFullAtRight hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
      hfullSubLowScale hfullSubLowV2Pos hfullSubLowV2LtV1
      hfullSubLowRightLtV1 hfullSubLowMeritCont hfullSubLowMeritAnti
      hfullSubHighScale hfullSubHighV2Pos hfullSubHighV2LtV1
      hfullSubHighRightLtV1 hfullSubHighMeritCont
      hfullSubHighMeritAnti hshareA hshareB hcapacity1 hfillFullFull1
      hcapacity2 hfillFullFull2
  fun hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight hfullSubHighAtLowRoot hJ2MassB hJ2MeritGtB
      hJ2MassA hJ2MeritGtA =>
    endpoint hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight hfullSubHighAtLowRoot
      (fun _ _ => hJ2MassB) hJ2MeritGtB (fun _ _ => hJ2MassA)
      hJ2MeritGtA

end

end GLM20DroppingStandardizedTesting
