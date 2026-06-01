import GLM20DroppingStandardizedTesting.Theorem3FeasibleKeepTest
import GLM20DroppingStandardizedTesting.Theorem3SimplePremises

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

/--
Theorem 3 support: the two school-`J2` keep-test predicates needed for the
`(P_sub,P_full)` policy-state table are exactly the two raw survivor
condition-(11)--(12) component pairs.
-/
theorem
    paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_j2_keep_test_pair_iff_components
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (subSubMerit subFullMerit fullSubMerit fullFullMerit :
      School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare : Group → ℝ) {capacity2 : ℝ} :
    (glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff subSubMerit subFullMerit fullSubMerit
            fullFullMerit diversity J1 J2 groupA groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB ∧
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff subSubMerit subFullMerit fullSubMerit
            fullFullMerit diversity J1 J2 groupA groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA) ↔
      (subFullMass groupB ≥ capacity2 ∧
          populationShare groupB * subFullMerit J2 groupB >
            populationShare groupA * subSubMerit J2 groupA +
              populationShare groupB * subSubMerit J2 groupB) ∧
        (subFullMass groupA ≥ capacity2 ∧
          populationShare groupA * subFullMerit J2 groupA >
            populationShare groupA * subSubMerit J2 groupA +
              populationShare groupB * subSubMerit J2 groupB) := by
  constructor
  · intro hkeep
    exact
      ⟨(glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface_subFull_otherGroupKeepsTest_iff_components
          api subEstimateLaw subSubMass subFullMass fullFullCutoff
          fullSubCutoff subSubMerit subFullMerit fullSubMerit
          fullFullMerit diversity J1 J2 groupA groupB groupB
          populationShare (capacity2 := capacity2)).mp hkeep.1,
        (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface_subFull_otherGroupKeepsTest_iff_components
          api subEstimateLaw subSubMass subFullMass fullFullCutoff
          fullSubCutoff subSubMerit subFullMerit fullSubMerit
          fullFullMerit diversity J1 J2 groupA groupB groupA
          populationShare (capacity2 := capacity2)).mp hkeep.2⟩
  · intro hcomponents
    exact
      ⟨(glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface_subFull_otherGroupKeepsTest_iff_components
          api subEstimateLaw subSubMass subFullMass fullFullCutoff
          fullSubCutoff subSubMerit subFullMerit fullSubMerit
          fullFullMerit diversity J1 J2 groupA groupB groupB
          populationShare (capacity2 := capacity2)).mpr hcomponents.1,
        (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface_subFull_otherGroupKeepsTest_iff_components
          api subEstimateLaw subSubMass subFullMass fullFullCutoff
          fullSubCutoff subSubMerit subFullMerit fullSubMerit
          fullFullMerit diversity J1 J2 groupA groupB groupA
          populationShare (capacity2 := capacity2)).mpr hcomponents.2⟩

/--
Convenience forward direction for callers that already have the named
school-`J2` keep-test predicates bundled.
-/
theorem
    paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_components_of_j2_keep_test_pair
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (subSubMerit subFullMerit fullSubMerit fullFullMerit :
      School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare : Group → ℝ) {capacity2 : ℝ}
    (hkeep :
      glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff subSubMerit subFullMerit fullSubMerit
            fullFullMerit diversity J1 J2 groupA groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB ∧
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff subSubMerit subFullMerit fullSubMerit
            fullFullMerit diversity J1 J2 groupA groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA) :
    (subFullMass groupB ≥ capacity2 ∧
        populationShare groupB * subFullMerit J2 groupB >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB) ∧
      (subFullMass groupA ≥ capacity2 ∧
        populationShare groupA * subFullMerit J2 groupA >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB) := by
  exact
    (paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_j2_keep_test_pair_iff_components
      api subEstimateLaw subSubMass subFullMass fullFullCutoff fullSubCutoff
      subSubMerit subFullMerit fullSubMerit fullFullMerit diversity J1 J2
      groupA groupB populationShare (capacity2 := capacity2)).mp hkeep

/--
The base policy-state table's bundled school-`J2` keep-test predicates imply
the strict-merit-only survivor row bundle used by feasibility-aware Theorem 3
routes.
-/
theorem
    paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_j2_strict_survivor_merit_rows_of_keep_test_pair
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (subSubMerit subFullMerit fullSubMerit fullFullMerit :
      School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB : Group)
    (populationShare : Group → ℝ) {capacity2 : ℝ}
    (hkeep :
      glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff subSubMerit subFullMerit fullSubMerit
            fullFullMerit diversity J1 J2 groupA groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB ∧
        glm20Theorem3SubFullOtherGroupKeepsTest
          (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface api
            subEstimateLaw subSubMass subFullMass fullFullCutoff
            fullSubCutoff subSubMerit subFullMerit fullSubMerit
            fullFullMerit diversity J1 J2 groupA groupB populationShare)
          glm20StrategicPolicyStatePair
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA) :
    GLM20Theorem3J2StrictSurvivorMeritRows populationShare subSubMerit
      subFullMerit J2 groupA groupB := by
  have hcomponents :=
    paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_components_of_j2_keep_test_pair
      api subEstimateLaw subSubMass subFullMass fullFullCutoff
      fullSubCutoff subSubMerit subFullMerit fullSubMerit fullFullMerit
      diversity J1 J2 groupA groupB populationShare
      (capacity2 := capacity2) hkeep
  exact ⟨hcomponents.1.2, hcomponents.2.2⟩

end

end GLM20DroppingStandardizedTesting
