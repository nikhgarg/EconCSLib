import GLM20DroppingStandardizedTesting.Theorem3ConstructedComponents
import EconCSLib.Foundations.Optimization.BinaryChoiceAE

open EconCSLib
open EconCSLib.Probability
open MeasureTheory
open scoped ENNReal NNReal

namespace GLM20DroppingStandardizedTesting

noncomputable section

instance glm20GroupFintype : Fintype GLM20Group where
  elems := {GLM20Group.groupA, GLM20Group.groupB}
  complete := by
    intro g
    cases g <;> simp

/-- Finite sums over the paper's named groups expand to the group-A row plus the group-B row. -/
theorem glm20Group_sum_eq (f : GLM20Group → ℝ) :
    (∑ g : GLM20Group, f g) =
      f GLM20Group.groupA + f GLM20Group.groupB := by
  change ({GLM20Group.groupA, GLM20Group.groupB} : Finset GLM20Group).sum f =
    f GLM20Group.groupA + f GLM20Group.groupB
  simp

/--
Section 5 binary-policy equilibrium characterization, bundled across the three
policy pairs used by the GLM20 strategic section.

This leaf module is intentionally for compact paper-surface adapters.  Keeping
such wrappers out of `MainTheorems.lean` avoids recompiling the large theorem
ledger when only the human-facing interface changes.
-/
theorem paper_section5_binary_policy_equilibrium_three_cases
    {Policy : Type*} (objective1 objective2 : Policy → Policy → ℝ)
    (Psub Pfull : Policy) :
    (glm20TwoSchoolBinaryPolicyEquilibrium objective1 objective2
          Psub Pfull Psub Pfull ↔
        objective1 Pfull Pfull ≤ objective1 Psub Pfull ∧
          objective2 Psub Psub ≤ objective2 Psub Pfull) ∧
      (glm20TwoSchoolBinaryPolicyEquilibrium objective1 objective2
          Psub Pfull Pfull Psub ↔
        objective1 Psub Psub ≤ objective1 Pfull Psub ∧
          objective2 Pfull Pfull ≤ objective2 Pfull Psub) ∧
      (glm20TwoSchoolBinaryPolicyEquilibrium objective1 objective2
          Psub Pfull Pfull Pfull ↔
        objective1 Psub Pfull ≤ objective1 Pfull Pfull ∧
          objective2 Pfull Psub ≤ objective2 Pfull Pfull) := by
  constructor
  · exact
      glm20TwoSchoolBinaryPolicyEquilibrium_subFull_iff
        objective1 objective2 Psub Pfull
  constructor
  · exact
      glm20TwoSchoolBinaryPolicyEquilibrium_fullSub_iff
        objective1 objective2 Psub Pfull
  · exact
      glm20TwoSchoolBinaryPolicyEquilibrium_fullFull_iff
        objective1 objective2 Psub Pfull

/--
Section 5 feasibility-aware binary-policy equilibrium characterization, bundled
across the three policy pairs used by Theorem 3.
-/
theorem paper_section5_binary_policy_feasible_equilibrium_three_cases
    {Policy : Type*} (objective1 objective2 : Policy → Policy → ℝ)
    (feasible1 feasible2 : Policy → Policy → Prop)
    (Psub Pfull : Policy) :
    (glm20TwoSchoolBinaryPolicyFeasibleEquilibrium objective1 objective2
          feasible1 feasible2 Psub Pfull Psub Pfull ↔
        feasible1 Psub Pfull ∧ feasible2 Psub Pfull ∧
          (feasible1 Pfull Pfull →
            objective1 Pfull Pfull ≤ objective1 Psub Pfull) ∧
            (feasible2 Psub Psub →
              objective2 Psub Psub ≤ objective2 Psub Pfull)) ∧
      (glm20TwoSchoolBinaryPolicyFeasibleEquilibrium objective1 objective2
          feasible1 feasible2 Psub Pfull Pfull Psub ↔
        feasible1 Pfull Psub ∧ feasible2 Pfull Psub ∧
          (feasible1 Psub Psub →
            objective1 Psub Psub ≤ objective1 Pfull Psub) ∧
            (feasible2 Pfull Pfull →
              objective2 Pfull Pfull ≤ objective2 Pfull Psub)) ∧
      (glm20TwoSchoolBinaryPolicyFeasibleEquilibrium objective1 objective2
          feasible1 feasible2 Psub Pfull Pfull Pfull ↔
        feasible1 Pfull Pfull ∧ feasible2 Pfull Pfull ∧
          (feasible1 Psub Pfull →
            objective1 Psub Pfull ≤ objective1 Pfull Pfull) ∧
            (feasible2 Pfull Psub →
              objective2 Pfull Psub ≤ objective2 Pfull Pfull)) := by
  constructor
  · exact
      glm20TwoSchoolBinaryPolicyFeasibleEquilibrium_subFull_iff
        objective1 objective2 feasible1 feasible2 Psub Pfull
  constructor
  · exact
      glm20TwoSchoolBinaryPolicyFeasibleEquilibrium_fullSub_iff
        objective1 objective2 feasible1 feasible2 Psub Pfull
  · exact
      glm20TwoSchoolBinaryPolicyFeasibleEquilibrium_fullFull_iff
        objective1 objective2 feasible1 feasible2 Psub Pfull

/--
Section 5 student-side choice-equilibrium data extracted from a GLM20
strategic equilibrium surface.

This is the GLM20 analogue of the LG21 a.e. source-equilibrium wrapper: the
continuous student component is sent through the reusable `IsChoiceEquilibriumAE`
API, while school policy and assignment consistency remain on the surrounding
strategic-equilibrium record.
-/
def paper_section5_student_choice_equilibrium_data
    {Student Action SchoolPolicy : Type*}
    (E : GLM20StrategicEquilibriumData Student Action SchoolPolicy) :
    EconCSLib.ChoiceEquilibriumData Student Action where
  actionFeasible := E.studentActionFeasible
  chosenAction := E.chosenStudentAction
  payoff := E.studentPayoff
  consistency := True

/--
Section 5 a.e. strategic-equilibrium projection: the continuous student side is
an `IsChoiceEquilibriumAE`, ready for reusable binary-choice projections.
-/
theorem paper_section5_student_choice_equilibriumAE_of_strategic_equilibriumAE
    {Student Action SchoolPolicy : Type*} [MeasurableSpace Student]
    {μ : Measure Student}
    {E : GLM20StrategicEquilibriumData Student Action SchoolPolicy}
    (hEq : glm20StrategicEquilibriumAE μ E) :
    EconCSLib.IsChoiceEquilibriumAE μ
      (paper_section5_student_choice_equilibrium_data E) := by
  refine ⟨?_, ?_, trivial⟩
  · exact glm20StrategicEquilibriumAE_student_feasible_ae hEq
  · exact glm20StrategicEquilibriumAE_student_best_response_ae hEq

/--
Section 5 binary-deviation projection from an a.e. strategic equilibrium.

Use this to discharge a `NoProfitableBinaryChoiceDeviationAE` premise from the
student best-response clause of `glm20StrategicEquilibriumAE` by naming the
apply/not-apply deviation actions and their payoff rewrites.
-/
theorem
    paper_section5_noProfitableBinaryChoiceDeviationAE_of_strategic_equilibriumAE
    {Student Action SchoolPolicy : Type*} [MeasurableSpace Student]
    {μ : Measure Student}
    {E : GLM20StrategicEquilibriumData Student Action SchoolPolicy}
    {chooses : Student → Prop} {choosePayoff otherPayoff : Student → ℝ}
    (hEq : glm20StrategicEquilibriumAE μ E)
    (chooseAction otherAction : Student → Action)
    (hchooseFeasible :
      ∀ s, E.studentActionFeasible s (chooseAction s))
    (hotherFeasible :
      ∀ s, E.studentActionFeasible s (otherAction s))
    (hchoosePayoff :
      ∀ s, E.studentPayoff s (chooseAction s) = choosePayoff s)
    (hotherPayoff :
      ∀ s, E.studentPayoff s (otherAction s) = otherPayoff s)
    (hchosenChoosePayoff :
      ∀ s, chooses s →
        E.studentPayoff s (E.chosenStudentAction s) = choosePayoff s)
    (hchosenOtherPayoff :
      ∀ s, ¬ chooses s →
        E.studentPayoff s (E.chosenStudentAction s) = otherPayoff s) :
    EconCSLib.NoProfitableBinaryChoiceDeviationAE μ chooses
      choosePayoff otherPayoff :=
  EconCSLib.noProfitableBinaryChoiceDeviationAE_of_choiceEquilibriumAE_payoff_projection
    (paper_section5_student_choice_equilibriumAE_of_strategic_equilibriumAE hEq)
    chooseAction otherAction hchooseFeasible hotherFeasible hchoosePayoff
    hotherPayoff hchosenChoosePayoff hchosenOtherPayoff

/--
Proposition 2 a.e. uniqueness support with the student best-response premise
stated through the reusable `NoProfitableBinaryChoiceDeviationAE` interface.

This is the LG21-style cutoff-boundary surface: continuous laws can discharge
cutoff ties by singleton-null assumptions, while the binary apply/not-apply
best-response condition is reusable library vocabulary.
-/
theorem
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_binary_choiceAE
    (Q : StandardGaussianQuantileAPI)
    {admissionThreshold school2SubThreshold scale cost v1 v2 : ℝ}
    (hscale : 0 < scale) (hcost : 0 < cost)
    (hv1 : 0 < v1) (hdiff_pos : 0 < v1 - v2)
    (hdiff_lt_v1 : v1 - v2 < v1)
    (hcostRatioLow : cost / v1 ∈ Set.Ioo (0 : ℝ) 1)
    (hcostRatioHigh : cost / (v1 - v2) ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ lowCutoff highCutoff : ℝ,
      lowCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / v1) ∧
      highCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / (v1 - v2)) ∧
      lowCutoff < highCutoff ∧
      ∀ (μ : Measure ℝ) (strategy : ℝ → Bool),
        μ {lowCutoff} = 0 →
        μ {highCutoff} = 0 →
        EconCSLib.NoProfitableBinaryChoiceDeviationAE μ
          (fun q => strategy q = true)
          (fun q =>
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q true)
          (fun q =>
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q false) →
        ∀ᵐ q ∂μ,
          strategy q =
            decide
              ((q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
                (school2SubThreshold ≤ q ∧ highCutoff ≤ q)) := by
  rcases
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian
      Q (admissionThreshold := admissionThreshold)
      (school2SubThreshold := school2SubThreshold) (scale := scale)
      (cost := cost) (v1 := v1) (v2 := v2)
      hscale hcost hv1 hdiff_pos hdiff_lt_v1
      hcostRatioLow hcostRatioHigh with
    ⟨lowCutoff, highCutoff, hlow_eq, hhigh_eq, hlt, hunique⟩
  refine ⟨lowCutoff, highCutoff, hlow_eq, hhigh_eq, hlt, ?_⟩
  intro μ strategy hnullLow hnullHigh hbinary
  refine hunique μ strategy hnullLow hnullHigh ?_
  filter_upwards [hbinary.1, hbinary.2] with q hchosen hunchosen
  intro apply
  by_cases hstrategy : strategy q = true
  · cases apply
    · simpa [hstrategy] using hchosen hstrategy
    · simp [hstrategy]
  · cases apply
    · simp [hstrategy]
    · simpa [hstrategy] using hunchosen hstrategy

/--
Proposition 2 canonical application-region strategy satisfies the reusable
a.e. binary no-profitable-deviation predicate under any student law.

This packages the pointwise best-response theorem into the a.e. vocabulary used
by the continuous-type strategy surface.
-/
theorem
    paper_proposition2_two_school_application_region_noProfitableBinaryChoiceDeviationAE_standardGaussian
    (Q : StandardGaussianQuantileAPI)
    {admissionThreshold school2SubThreshold scale cost v1 v2 : ℝ}
    (hscale : 0 < scale) (hcost : 0 < cost)
    (hv1 : 0 < v1) (hdiff_pos : 0 < v1 - v2)
    (hdiff_lt_v1 : v1 - v2 < v1)
    (hcostRatioLow : cost / v1 ∈ Set.Ioo (0 : ℝ) 1)
    (hcostRatioHigh : cost / (v1 - v2) ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ lowCutoff highCutoff : ℝ,
      lowCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / v1) ∧
      highCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / (v1 - v2)) ∧
      lowCutoff < highCutoff ∧
      ∀ μ : Measure ℝ,
        EconCSLib.NoProfitableBinaryChoiceDeviationAE μ
          (fun q =>
            decide
              ((q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
                (school2SubThreshold ≤ q ∧ highCutoff ≤ q)) = true)
          (fun q =>
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q true)
          (fun q =>
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q false) := by
  rcases
    paper_proposition2_two_school_application_region_bestResponse_standardGaussian
      Q (admissionThreshold := admissionThreshold)
      (school2SubThreshold := school2SubThreshold) (scale := scale)
      (cost := cost) (v1 := v1) (v2 := v2)
      hscale hcost hv1 hdiff_pos hdiff_lt_v1
      hcostRatioLow hcostRatioHigh with
    ⟨lowCutoff, highCutoff, hlow_eq, hhigh_eq, hlt, hbest⟩
  refine ⟨lowCutoff, highCutoff, hlow_eq, hhigh_eq, hlt, ?_⟩
  intro μ
  exact
    EconCSLib.noProfitableBinaryChoiceDeviationAE_of_bool_best_response_ae
      (μ := μ)
      (chooses := fun q : ℝ =>
        decide
          ((q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
            (school2SubThreshold ≤ q ∧ highCutoff ≤ q)))
      (Filter.Eventually.of_forall hbest)

/--
Proposition 2 a.e. uniqueness under a Gaussian student law.

For Gaussian projected-skill laws, the two cutoff singleton-null hypotheses in
the general a.e. uniqueness theorem are automatic.
-/
theorem
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_binary_choiceAE_gaussian_student_law
    (Q : StandardGaussianQuantileAPI)
    {admissionThreshold school2SubThreshold scale cost v1 v2 : ℝ}
    (hscale : 0 < scale) (hcost : 0 < cost)
    (hv1 : 0 < v1) (hdiff_pos : 0 < v1 - v2)
    (hdiff_lt_v1 : v1 - v2 < v1)
    (hcostRatioLow : cost / v1 ∈ Set.Ioo (0 : ℝ) 1)
    (hcostRatioHigh : cost / (v1 - v2) ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ lowCutoff highCutoff : ℝ,
      lowCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / v1) ∧
      highCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / (v1 - v2)) ∧
      lowCutoff < highCutoff ∧
      ∀ (studentLaw : GaussianScaleLaw) (strategy : ℝ → Bool),
        EconCSLib.NoProfitableBinaryChoiceDeviationAE studentLaw.toMeasure
          (fun q => strategy q = true)
          (fun q =>
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q true)
          (fun q =>
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q false) →
        ∀ᵐ q ∂studentLaw.toMeasure,
          strategy q =
            decide
              ((q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
                (school2SubThreshold ≤ q ∧ highCutoff ≤ q)) := by
  rcases
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_binary_choiceAE
      Q (admissionThreshold := admissionThreshold)
      (school2SubThreshold := school2SubThreshold) (scale := scale)
      (cost := cost) (v1 := v1) (v2 := v2)
      hscale hcost hv1 hdiff_pos hdiff_lt_v1
      hcostRatioLow hcostRatioHigh with
    ⟨lowCutoff, highCutoff, hlow_eq, hhigh_eq, hlt, huniq⟩
  refine ⟨lowCutoff, highCutoff, hlow_eq, hhigh_eq, hlt, ?_⟩
  intro studentLaw strategy hbest
  exact
    huniq studentLaw.toMeasure strategy
      (GaussianScaleLaw.toMeasure_singleton_eq_zero studentLaw lowCutoff)
      (GaussianScaleLaw.toMeasure_singleton_eq_zero studentLaw highCutoff)
      hbest

/--
Proposition 2 a.e. uniqueness support with the student best-response premise
supplied by a GLM20 a.e. strategic equilibrium.

This is the GLM20 analogue of the LG21 source-equilibrium-to-binary-deviation
route: callers name the apply/not-apply actions and payoff rewrites, and the
student side of `glm20StrategicEquilibriumAE` supplies the reusable
`NoProfitableBinaryChoiceDeviationAE` premise.
-/
theorem
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_strategic_equilibriumAE
    {Action SchoolPolicy : Type*}
    (Q : StandardGaussianQuantileAPI)
    {admissionThreshold school2SubThreshold scale cost v1 v2 : ℝ}
    (hscale : 0 < scale) (hcost : 0 < cost)
    (hv1 : 0 < v1) (hdiff_pos : 0 < v1 - v2)
    (hdiff_lt_v1 : v1 - v2 < v1)
    (hcostRatioLow : cost / v1 ∈ Set.Ioo (0 : ℝ) 1)
    (hcostRatioHigh : cost / (v1 - v2) ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ lowCutoff highCutoff : ℝ,
      lowCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / v1) ∧
      highCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / (v1 - v2)) ∧
      lowCutoff < highCutoff ∧
      ∀ (μ : Measure ℝ)
        (E : GLM20StrategicEquilibriumData ℝ Action SchoolPolicy)
        (strategy : ℝ → Bool),
        μ {lowCutoff} = 0 →
        μ {highCutoff} = 0 →
        glm20StrategicEquilibriumAE μ E →
        ∀ (chooseAction otherAction : ℝ → Action),
          (∀ q, E.studentActionFeasible q (chooseAction q)) →
          (∀ q, E.studentActionFeasible q (otherAction q)) →
          (∀ q,
            E.studentPayoff q (chooseAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q true) →
          (∀ q,
            E.studentPayoff q (otherAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q false) →
          (∀ q, strategy q = true →
            E.studentPayoff q (E.chosenStudentAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q true) →
          (∀ q, ¬ strategy q = true →
            E.studentPayoff q (E.chosenStudentAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q false) →
          ∀ᵐ q ∂μ,
            strategy q =
              decide
                ((q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
                  (school2SubThreshold ≤ q ∧ highCutoff ≤ q)) := by
  rcases
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_binary_choiceAE
      Q (admissionThreshold := admissionThreshold)
      (school2SubThreshold := school2SubThreshold) (scale := scale)
      (cost := cost) (v1 := v1) (v2 := v2)
      hscale hcost hv1 hdiff_pos hdiff_lt_v1
      hcostRatioLow hcostRatioHigh with
    ⟨lowCutoff, highCutoff, hlow_eq, hhigh_eq, hlt, huniq⟩
  refine ⟨lowCutoff, highCutoff, hlow_eq, hhigh_eq, hlt, ?_⟩
  intro μ E strategy hμLow hμHigh hEq chooseAction otherAction
    hchooseFeasible hotherFeasible hchoosePayoff hotherPayoff
    hchosenChoosePayoff hchosenOtherPayoff
  exact
    huniq μ strategy hμLow hμHigh
      (paper_section5_noProfitableBinaryChoiceDeviationAE_of_strategic_equilibriumAE
        (E := E) hEq chooseAction otherAction hchooseFeasible hotherFeasible
        hchoosePayoff hotherPayoff hchosenChoosePayoff hchosenOtherPayoff)

/--
Proposition 2 a.e. uniqueness under a Gaussian student law, with the
best-response premise supplied by a GLM20 a.e. strategic equilibrium.

This is the most direct continuous-type strategy surface: Gaussian laws
discharge cutoff-boundary nullness, and the student side of
`glm20StrategicEquilibriumAE` discharges the binary no-deviation premise.
-/
theorem
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_strategic_equilibriumAE_gaussian_student_law
    {Action SchoolPolicy : Type*}
    (Q : StandardGaussianQuantileAPI)
    {admissionThreshold school2SubThreshold scale cost v1 v2 : ℝ}
    (hscale : 0 < scale) (hcost : 0 < cost)
    (hv1 : 0 < v1) (hdiff_pos : 0 < v1 - v2)
    (hdiff_lt_v1 : v1 - v2 < v1)
    (hcostRatioLow : cost / v1 ∈ Set.Ioo (0 : ℝ) 1)
    (hcostRatioHigh : cost / (v1 - v2) ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ lowCutoff highCutoff : ℝ,
      lowCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / v1) ∧
      highCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / (v1 - v2)) ∧
      lowCutoff < highCutoff ∧
      ∀ (studentLaw : GaussianScaleLaw)
        (E : GLM20StrategicEquilibriumData ℝ Action SchoolPolicy)
        (strategy : ℝ → Bool),
        glm20StrategicEquilibriumAE studentLaw.toMeasure E →
        ∀ (chooseAction otherAction : ℝ → Action),
          (∀ q, E.studentActionFeasible q (chooseAction q)) →
          (∀ q, E.studentActionFeasible q (otherAction q)) →
          (∀ q,
            E.studentPayoff q (chooseAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q true) →
          (∀ q,
            E.studentPayoff q (otherAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q false) →
          (∀ q, strategy q = true →
            E.studentPayoff q (E.chosenStudentAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q true) →
          (∀ q, ¬ strategy q = true →
            E.studentPayoff q (E.chosenStudentAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q false) →
          ∀ᵐ q ∂studentLaw.toMeasure,
            strategy q =
              decide
                ((q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
                  (school2SubThreshold ≤ q ∧ highCutoff ≤ q)) := by
  rcases
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_binary_choiceAE_gaussian_student_law
      Q (admissionThreshold := admissionThreshold)
      (school2SubThreshold := school2SubThreshold) (scale := scale)
      (cost := cost) (v1 := v1) (v2 := v2)
      hscale hcost hv1 hdiff_pos hdiff_lt_v1
      hcostRatioLow hcostRatioHigh with
    ⟨lowCutoff, highCutoff, hlow_eq, hhigh_eq, hlt, huniq⟩
  refine ⟨lowCutoff, highCutoff, hlow_eq, hhigh_eq, hlt, ?_⟩
  intro studentLaw E strategy hEq chooseAction otherAction hchooseFeasible
    hotherFeasible hchoosePayoff hotherPayoff hchosenChoosePayoff
    hchosenOtherPayoff
  exact
    huniq studentLaw strategy
      (paper_section5_noProfitableBinaryChoiceDeviationAE_of_strategic_equilibriumAE
        (E := E) hEq chooseAction otherAction hchooseFeasible hotherFeasible
        hchoosePayoff hotherPayoff hchosenChoosePayoff hchosenOtherPayoff)

/--
Proposition 2 base a.e. uniqueness theorem with paper-readable cost bounds.
-/
theorem
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_cost_bounds
    (Q : StandardGaussianQuantileAPI)
    {admissionThreshold school2SubThreshold scale cost v1 v2 : ℝ}
    (hscale : 0 < scale) (hcost : 0 < cost)
    (hv1 : 0 < v1) (hdiff_pos : 0 < v1 - v2)
    (hdiff_lt_v1 : v1 - v2 < v1)
    (hcost_lt_diff : cost < v1 - v2) :
    ∃ lowCutoff highCutoff : ℝ,
      lowCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / v1) ∧
      highCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / (v1 - v2)) ∧
      lowCutoff < highCutoff ∧
      ∀ (μ : Measure ℝ) (strategy : ℝ → Bool),
        μ {lowCutoff} = 0 →
        μ {highCutoff} = 0 →
        (∀ᵐ q ∂μ, ∀ apply : Bool,
          glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q apply ≤
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q (strategy q)) →
        ∀ᵐ q ∂μ,
          strategy q =
            decide
              ((q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
                (school2SubThreshold ≤ q ∧ highCutoff ≤ q)) :=
  let hhigh := paper_proposition2_cost_ratio_high_of_cost_bounds hcost hcost_lt_diff
  let hlow :=
    paper_proposition2_cost_ratio_low_of_high hcost hv1 hdiff_pos
      hdiff_lt_v1 hhigh
  paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian
    Q (admissionThreshold := admissionThreshold)
    (school2SubThreshold := school2SubThreshold) (scale := scale)
    (cost := cost) (v1 := v1) (v2 := v2)
    hscale hcost hv1 hdiff_pos hdiff_lt_v1 hlow hhigh

/--
Proposition 2 a.e. uniqueness support with paper-readable cost bounds.

The source condition `0 < cost < v1 - v2` implies both inverse-CDF ratio
premises used by the two-cutoff application-region theorem.
-/
theorem
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_binary_choiceAE_of_cost_bounds
    (Q : StandardGaussianQuantileAPI)
    {admissionThreshold school2SubThreshold scale cost v1 v2 : ℝ}
    (hscale : 0 < scale) (hcost : 0 < cost)
    (hv1 : 0 < v1) (hdiff_pos : 0 < v1 - v2)
    (hdiff_lt_v1 : v1 - v2 < v1)
    (hcost_lt_diff : cost < v1 - v2) :
    ∃ lowCutoff highCutoff : ℝ,
      lowCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / v1) ∧
      highCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / (v1 - v2)) ∧
      lowCutoff < highCutoff ∧
      ∀ (μ : Measure ℝ) (strategy : ℝ → Bool),
        μ {lowCutoff} = 0 →
        μ {highCutoff} = 0 →
        EconCSLib.NoProfitableBinaryChoiceDeviationAE μ
          (fun q => strategy q = true)
          (fun q =>
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q true)
          (fun q =>
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q false) →
        ∀ᵐ q ∂μ,
          strategy q =
            decide
              ((q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
                (school2SubThreshold ≤ q ∧ highCutoff ≤ q)) :=
  let hhigh := paper_proposition2_cost_ratio_high_of_cost_bounds hcost hcost_lt_diff
  let hlow :=
    paper_proposition2_cost_ratio_low_of_high hcost hv1 hdiff_pos
      hdiff_lt_v1 hhigh
  paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_binary_choiceAE
    Q (admissionThreshold := admissionThreshold)
    (school2SubThreshold := school2SubThreshold) (scale := scale)
    (cost := cost) (v1 := v1) (v2 := v2)
    hscale hcost hv1 hdiff_pos hdiff_lt_v1 hlow hhigh

/--
Proposition 2 canonical application-region strategy satisfies the reusable
a.e. binary no-profitable-deviation predicate under paper-readable cost bounds.
-/
theorem
    paper_proposition2_two_school_application_region_noProfitableBinaryChoiceDeviationAE_standardGaussian_of_cost_bounds
    (Q : StandardGaussianQuantileAPI)
    {admissionThreshold school2SubThreshold scale cost v1 v2 : ℝ}
    (hscale : 0 < scale) (hcost : 0 < cost)
    (hv1 : 0 < v1) (hdiff_pos : 0 < v1 - v2)
    (hdiff_lt_v1 : v1 - v2 < v1)
    (hcost_lt_diff : cost < v1 - v2) :
    ∃ lowCutoff highCutoff : ℝ,
      lowCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / v1) ∧
      highCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / (v1 - v2)) ∧
      lowCutoff < highCutoff ∧
      ∀ μ : Measure ℝ,
        EconCSLib.NoProfitableBinaryChoiceDeviationAE μ
          (fun q =>
            decide
              ((q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
                (school2SubThreshold ≤ q ∧ highCutoff ≤ q)) = true)
          (fun q =>
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q true)
          (fun q =>
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q false) :=
  let hhigh := paper_proposition2_cost_ratio_high_of_cost_bounds hcost hcost_lt_diff
  let hlow :=
    paper_proposition2_cost_ratio_low_of_high hcost hv1 hdiff_pos
      hdiff_lt_v1 hhigh
  paper_proposition2_two_school_application_region_noProfitableBinaryChoiceDeviationAE_standardGaussian
    Q (admissionThreshold := admissionThreshold)
    (school2SubThreshold := school2SubThreshold) (scale := scale)
    (cost := cost) (v1 := v1) (v2 := v2)
    hscale hcost hv1 hdiff_pos hdiff_lt_v1 hlow hhigh

/--
Proposition 2 a.e. uniqueness under a Gaussian student law and paper-readable
cost bounds.
-/
theorem
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_binary_choiceAE_gaussian_student_law_of_cost_bounds
    (Q : StandardGaussianQuantileAPI)
    {admissionThreshold school2SubThreshold scale cost v1 v2 : ℝ}
    (hscale : 0 < scale) (hcost : 0 < cost)
    (hv1 : 0 < v1) (hdiff_pos : 0 < v1 - v2)
    (hdiff_lt_v1 : v1 - v2 < v1)
    (hcost_lt_diff : cost < v1 - v2) :
    ∃ lowCutoff highCutoff : ℝ,
      lowCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / v1) ∧
      highCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / (v1 - v2)) ∧
      lowCutoff < highCutoff ∧
      ∀ (studentLaw : GaussianScaleLaw) (strategy : ℝ → Bool),
        EconCSLib.NoProfitableBinaryChoiceDeviationAE studentLaw.toMeasure
          (fun q => strategy q = true)
          (fun q =>
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q true)
          (fun q =>
            glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
              (Q.cdfAPI.thresholdPassProb
                { mean := q, scale := scale, scale_pos := hscale }
                admissionThreshold)
              q false) →
        ∀ᵐ q ∂studentLaw.toMeasure,
          strategy q =
            decide
              ((q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
                (school2SubThreshold ≤ q ∧ highCutoff ≤ q)) :=
  let hhigh := paper_proposition2_cost_ratio_high_of_cost_bounds hcost hcost_lt_diff
  let hlow :=
    paper_proposition2_cost_ratio_low_of_high hcost hv1 hdiff_pos
      hdiff_lt_v1 hhigh
  paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_binary_choiceAE_gaussian_student_law
    Q (admissionThreshold := admissionThreshold)
    (school2SubThreshold := school2SubThreshold) (scale := scale)
    (cost := cost) (v1 := v1) (v2 := v2)
    hscale hcost hv1 hdiff_pos hdiff_lt_v1 hlow hhigh

/--
Proposition 2 a.e. uniqueness from a GLM20 a.e. strategic equilibrium under
paper-readable cost bounds.
-/
theorem
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_strategic_equilibriumAE_of_cost_bounds
    {Action SchoolPolicy : Type*}
    (Q : StandardGaussianQuantileAPI)
    {admissionThreshold school2SubThreshold scale cost v1 v2 : ℝ}
    (hscale : 0 < scale) (hcost : 0 < cost)
    (hv1 : 0 < v1) (hdiff_pos : 0 < v1 - v2)
    (hdiff_lt_v1 : v1 - v2 < v1)
    (hcost_lt_diff : cost < v1 - v2) :
    ∃ lowCutoff highCutoff : ℝ,
      lowCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / v1) ∧
      highCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / (v1 - v2)) ∧
      lowCutoff < highCutoff ∧
      ∀ (μ : Measure ℝ)
        (E : GLM20StrategicEquilibriumData ℝ Action SchoolPolicy)
        (strategy : ℝ → Bool),
        μ {lowCutoff} = 0 →
        μ {highCutoff} = 0 →
        glm20StrategicEquilibriumAE μ E →
        ∀ (chooseAction otherAction : ℝ → Action),
          (∀ q, E.studentActionFeasible q (chooseAction q)) →
          (∀ q, E.studentActionFeasible q (otherAction q)) →
          (∀ q,
            E.studentPayoff q (chooseAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q true) →
          (∀ q,
            E.studentPayoff q (otherAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q false) →
          (∀ q, strategy q = true →
            E.studentPayoff q (E.chosenStudentAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q true) →
          (∀ q, ¬ strategy q = true →
            E.studentPayoff q (E.chosenStudentAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q false) →
          ∀ᵐ q ∂μ,
            strategy q =
              decide
                ((q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
                  (school2SubThreshold ≤ q ∧ highCutoff ≤ q)) :=
  let hhigh := paper_proposition2_cost_ratio_high_of_cost_bounds hcost hcost_lt_diff
  let hlow :=
    paper_proposition2_cost_ratio_low_of_high hcost hv1 hdiff_pos
      hdiff_lt_v1 hhigh
  paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_strategic_equilibriumAE
    (Action := Action) (SchoolPolicy := SchoolPolicy)
    Q (admissionThreshold := admissionThreshold)
    (school2SubThreshold := school2SubThreshold) (scale := scale)
    (cost := cost) (v1 := v1) (v2 := v2)
    hscale hcost hv1 hdiff_pos hdiff_lt_v1 hlow hhigh

/--
Proposition 2 a.e. uniqueness from a GLM20 a.e. strategic equilibrium under a
Gaussian student law and paper-readable cost bounds.
-/
theorem
    paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_strategic_equilibriumAE_gaussian_student_law_of_cost_bounds
    {Action SchoolPolicy : Type*}
    (Q : StandardGaussianQuantileAPI)
    {admissionThreshold school2SubThreshold scale cost v1 v2 : ℝ}
    (hscale : 0 < scale) (hcost : 0 < cost)
    (hv1 : 0 < v1) (hdiff_pos : 0 < v1 - v2)
    (hdiff_lt_v1 : v1 - v2 < v1)
    (hcost_lt_diff : cost < v1 - v2) :
    ∃ lowCutoff highCutoff : ℝ,
      lowCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / v1) ∧
      highCutoff =
        glm20StrategicApplyCutoff Q admissionThreshold scale (cost / (v1 - v2)) ∧
      lowCutoff < highCutoff ∧
      ∀ (studentLaw : GaussianScaleLaw)
        (E : GLM20StrategicEquilibriumData ℝ Action SchoolPolicy)
        (strategy : ℝ → Bool),
        glm20StrategicEquilibriumAE studentLaw.toMeasure E →
        ∀ (chooseAction otherAction : ℝ → Action),
          (∀ q, E.studentActionFeasible q (chooseAction q)) →
          (∀ q, E.studentActionFeasible q (otherAction q)) →
          (∀ q,
            E.studentPayoff q (chooseAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q true) →
          (∀ q,
            E.studentPayoff q (otherAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q false) →
          (∀ q, strategy q = true →
            E.studentPayoff q (E.chosenStudentAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q true) →
          (∀ q, ¬ strategy q = true →
            E.studentPayoff q (E.chosenStudentAction q) =
              glm20StrategicTwoSchoolApplyPayoff school2SubThreshold v1 v2 cost
                (Q.cdfAPI.thresholdPassProb
                  { mean := q, scale := scale, scale_pos := hscale }
                  admissionThreshold)
                q false) →
          ∀ᵐ q ∂studentLaw.toMeasure,
            strategy q =
              decide
                ((q < school2SubThreshold ∧ lowCutoff ≤ q) ∨
                  (school2SubThreshold ≤ q ∧ highCutoff ≤ q)) :=
  let hhigh := paper_proposition2_cost_ratio_high_of_cost_bounds hcost hcost_lt_diff
  let hlow :=
    paper_proposition2_cost_ratio_low_of_high hcost hv1 hdiff_pos
      hdiff_lt_v1 hhigh
  paper_proposition2_two_school_application_region_unique_strategy_ae_standardGaussian_of_strategic_equilibriumAE_gaussian_student_law
    (Action := Action) (SchoolPolicy := SchoolPolicy)
    Q (admissionThreshold := admissionThreshold)
    (school2SubThreshold := school2SubThreshold) (scale := scale)
    (cost := cost) (v1 := v1) (v2 := v2)
    hscale hcost hv1 hdiff_pos hdiff_lt_v1 hlow hhigh

/--
Proposition 2 / Lemma 3 applicant-pool component row.

After substituting the Eq. (7) application cutoff into Lemma 3's strategic
applicant component, the source-row mass is exactly the corrected
Proposition 2 admitted-mass formula evaluated at that induced application
cutoff.
-/
theorem paper_proposition2_strategic_applicant_component_eq_corrected_source_row
    {Group : Type*}
    (populationShare priorSigma priorPrecision subPrecisionSum
      fullPrecisionSum cost mu : Group → ℝ)
    (value : ℝ) (g : Group) (qAdmit : ℝ) :
    let sigmaTilde : Group → ℝ :=
      fun g =>
        glm20Proposition3SigmaTildeSource
          (priorSigma g) (priorPrecision g) (fullPrecisionSum g)
    let b : Group → ℝ :=
      fun g =>
        glm20Proposition3BSource
          (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g)
    let aOfApply : Group → ℝ → ℝ :=
      fun g qApply =>
        glm20Proposition2AHatConditionalSource
          (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g)
          (mu g) qApply
    let jointApplyAdmitMass : Group → ℝ → ℝ → ℝ :=
      fun g qApply qAdmit =>
        glm20BivariateApplyAdmitMass standardGaussianCDFAPI
          standardBivariateGaussianCDF
          (populationShare g) (sigmaTilde g) (aOfApply g) (b g)
          (mu g) qApply qAdmit
    glm20Lemma3StrategicApplicantComponent standardGaussianQuantileAPI
        jointApplyAdmitMass priorPrecision subPrecisionSum fullPrecisionSum
        cost value g qAdmit =
      glm20Proposition2AdmittedMassFormula standardGaussianCDFAPI
        standardBivariateGaussianCDF (populationShare g) (sigmaTilde g)
        (aOfApply g
          (qAdmit -
            glm20StrategicProjectedScale
              (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g) *
              standardGaussianQuantileAPI.quantile (1 - cost g / value)))
        (b g) (mu g) qAdmit := by
  rfl

/--
Proposition 2 / Lemma 3 applicant-pool mass rows.

The aggregate Eq. (35) strategic applicant-pool mass is the finite sum of the
corrected Proposition 2 admitted-mass source rows evaluated at each group's
Eq. (7) induced application cutoff.
-/
theorem paper_proposition2_strategic_applicant_pool_masses_to_corrected_source_rows
    {Group : Type*} [Fintype Group]
    (populationShare priorSigma priorPrecision subPrecisionSum
      fullPrecisionSum cost mu : Group → ℝ)
    (value qAdmit : ℝ) :
    let sigmaTilde : Group → ℝ :=
      fun g =>
        glm20Proposition3SigmaTildeSource
          (priorSigma g) (priorPrecision g) (fullPrecisionSum g)
    let b : Group → ℝ :=
      fun g =>
        glm20Proposition3BSource
          (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g)
    let aOfApply : Group → ℝ → ℝ :=
      fun g qApply =>
        glm20Proposition2AHatConditionalSource
          (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g)
          (mu g) qApply
    let jointApplyAdmitMass : Group → ℝ → ℝ → ℝ :=
      fun g qApply qAdmit =>
        glm20BivariateApplyAdmitMass standardGaussianCDFAPI
          standardBivariateGaussianCDF
          (populationShare g) (sigmaTilde g) (aOfApply g) (b g)
          (mu g) qApply qAdmit
    glm20Lemma3StrategicApplicantMass standardGaussianQuantileAPI
        jointApplyAdmitMass priorPrecision subPrecisionSum fullPrecisionSum
        cost value qAdmit =
      ∑ g : Group,
        glm20Proposition2AdmittedMassFormula standardGaussianCDFAPI
          standardBivariateGaussianCDF (populationShare g) (sigmaTilde g)
          (aOfApply g
            (qAdmit -
              glm20StrategicProjectedScale
                (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g) *
                standardGaussianQuantileAPI.quantile (1 - cost g / value)))
          (b g) (mu g) qAdmit := by
  rfl

/--
Proposition 2 / Lemma 3 applicant-pool mass rows for the paper's two named
groups.

This is the aggregate row above specialized to `GLM20Group`, with the finite
sum expanded as the group-A corrected source row plus the group-B corrected
source row.
-/
theorem paper_proposition2_strategic_applicant_pool_masses_to_corrected_source_rows_paper_groups
    (populationShare priorSigma priorPrecision subPrecisionSum
      fullPrecisionSum cost mu : GLM20Group → ℝ)
    (value qAdmit : ℝ) :
    let sigmaTilde : GLM20Group → ℝ :=
      fun g =>
        glm20Proposition3SigmaTildeSource
          (priorSigma g) (priorPrecision g) (fullPrecisionSum g)
    let b : GLM20Group → ℝ :=
      fun g =>
        glm20Proposition3BSource
          (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g)
    let aOfApply : GLM20Group → ℝ → ℝ :=
      fun g qApply =>
        glm20Proposition2AHatConditionalSource
          (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g)
          (mu g) qApply
    let jointApplyAdmitMass : GLM20Group → ℝ → ℝ → ℝ :=
      fun g qApply qAdmit =>
        glm20BivariateApplyAdmitMass standardGaussianCDFAPI
          standardBivariateGaussianCDF
          (populationShare g) (sigmaTilde g) (aOfApply g) (b g)
          (mu g) qApply qAdmit
    glm20Lemma3StrategicApplicantMass standardGaussianQuantileAPI
        jointApplyAdmitMass priorPrecision subPrecisionSum fullPrecisionSum
        cost value qAdmit =
      glm20Proposition2AdmittedMassFormula standardGaussianCDFAPI
        standardBivariateGaussianCDF
        (populationShare GLM20Group.groupA) (sigmaTilde GLM20Group.groupA)
        (aOfApply GLM20Group.groupA
          (qAdmit -
            glm20StrategicProjectedScale
              (priorPrecision GLM20Group.groupA) (subPrecisionSum GLM20Group.groupA)
              (fullPrecisionSum GLM20Group.groupA) *
              standardGaussianQuantileAPI.quantile
                (1 - cost GLM20Group.groupA / value)))
        (b GLM20Group.groupA) (mu GLM20Group.groupA) qAdmit +
      glm20Proposition2AdmittedMassFormula standardGaussianCDFAPI
        standardBivariateGaussianCDF
        (populationShare GLM20Group.groupB) (sigmaTilde GLM20Group.groupB)
        (aOfApply GLM20Group.groupB
          (qAdmit -
            glm20StrategicProjectedScale
              (priorPrecision GLM20Group.groupB) (subPrecisionSum GLM20Group.groupB)
              (fullPrecisionSum GLM20Group.groupB) *
              standardGaussianQuantileAPI.quantile
                (1 - cost GLM20Group.groupB / value)))
        (b GLM20Group.groupB) (mu GLM20Group.groupB) qAdmit := by
  simpa [glm20Group_sum_eq] using
    (paper_proposition2_strategic_applicant_pool_masses_to_corrected_source_rows
      (Group := GLM20Group) populationShare priorSigma priorPrecision
      subPrecisionSum fullPrecisionSum cost mu value qAdmit)

/--
Proposition 2 / Lemma 3 applicant-pool mass with the affine total-mass
substitution.

After substituting each group's Eq. (7) application cutoff, the strategic
applicant-pool mass plus the groupwise lower-left residuals equals the finite
sum of the affine total masses `pi_g sigma_tilde_g Phi(A_g)`.
-/
theorem paper_proposition2_strategic_applicant_pool_mass_add_lowerLeft_eq_affineTotal
    {Group : Type*} [Fintype Group]
    (populationShare priorSigma priorPrecision subPrecisionSum
      fullPrecisionSum cost mu : Group → ℝ)
    (value qAdmit : ℝ) :
    let sigmaTilde : Group → ℝ :=
      fun g =>
        glm20Proposition3SigmaTildeSource
          (priorSigma g) (priorPrecision g) (fullPrecisionSum g)
    let b : Group → ℝ :=
      fun g =>
        glm20Proposition3BSource
          (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g)
    let aOfApply : Group → ℝ → ℝ :=
      fun g qApply =>
        glm20Proposition2AHatConditionalSource
          (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g)
          (mu g) qApply
    let aRow : Group → ℝ :=
      fun g =>
        aOfApply g
          (qAdmit -
            glm20StrategicProjectedScale
              (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g) *
              standardGaussianQuantileAPI.quantile (1 - cost g / value))
    let lowerLeft : Group → ℝ :=
      fun g =>
        populationShare g * sigmaTilde g *
          lowerLeftRectangleMass
            (correlatedStandardGaussianLaw
              (-(sigmaTilde g * b g) /
                Real.sqrt (1 + sigmaTilde g ^ 2 * b g ^ 2)))
            ((aRow g + b g * mu g) /
              Real.sqrt (1 + sigmaTilde g ^ 2 * b g ^ 2))
            ((qAdmit - mu g) / sigmaTilde g)
    let affineTotal : Group → ℝ :=
      fun g =>
        populationShare g * sigmaTilde g *
          standardGaussianCDF
            ((aRow g + b g * mu g) /
              Real.sqrt (1 + sigmaTilde g ^ 2 * b g ^ 2))
    let jointApplyAdmitMass : Group → ℝ → ℝ → ℝ :=
      fun g qApply qAdmit =>
        glm20BivariateApplyAdmitMass standardGaussianCDFAPI
          standardBivariateGaussianCDF
          (populationShare g) (sigmaTilde g) (aOfApply g) (b g)
          (mu g) qApply qAdmit
    glm20Lemma3StrategicApplicantMass standardGaussianQuantileAPI
        jointApplyAdmitMass priorPrecision subPrecisionSum fullPrecisionSum
        cost value qAdmit +
      ∑ g : Group, lowerLeft g =
        ∑ g : Group, affineTotal g := by
  classical
  let sigmaTilde : Group → ℝ := fun g =>
    glm20Proposition3SigmaTildeSource
      (priorSigma g) (priorPrecision g) (fullPrecisionSum g)
  let b : Group → ℝ := fun g =>
    glm20Proposition3BSource
      (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g)
  let aOfApply : Group → ℝ → ℝ := fun g qApply =>
    glm20Proposition2AHatConditionalSource
      (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g)
      (mu g) qApply
  let aRow : Group → ℝ := fun g =>
    aOfApply g
      (qAdmit -
        glm20StrategicProjectedScale
          (priorPrecision g) (subPrecisionSum g) (fullPrecisionSum g) *
          standardGaussianQuantileAPI.quantile (1 - cost g / value))
  let lowerLeft : Group → ℝ := fun g =>
    populationShare g * sigmaTilde g *
      lowerLeftRectangleMass
        (correlatedStandardGaussianLaw
          (-(sigmaTilde g * b g) /
            Real.sqrt (1 + sigmaTilde g ^ 2 * b g ^ 2)))
        ((aRow g + b g * mu g) /
          Real.sqrt (1 + sigmaTilde g ^ 2 * b g ^ 2))
        ((qAdmit - mu g) / sigmaTilde g)
  let affineTotal : Group → ℝ := fun g =>
    populationShare g * sigmaTilde g *
      standardGaussianCDF
        ((aRow g + b g * mu g) /
          Real.sqrt (1 + sigmaTilde g ^ 2 * b g ^ 2))
  let jointApplyAdmitMass : Group → ℝ → ℝ → ℝ := fun g qApply qAdmit =>
    glm20BivariateApplyAdmitMass standardGaussianCDFAPI
      standardBivariateGaussianCDF
      (populationShare g) (sigmaTilde g) (aOfApply g) (b g)
      (mu g) qApply qAdmit
  change
    glm20Lemma3StrategicApplicantMass standardGaussianQuantileAPI
        jointApplyAdmitMass priorPrecision subPrecisionSum fullPrecisionSum
        cost value qAdmit +
      ∑ g : Group, lowerLeft g =
        ∑ g : Group, affineTotal g
  calc
    glm20Lemma3StrategicApplicantMass standardGaussianQuantileAPI
        jointApplyAdmitMass priorPrecision subPrecisionSum fullPrecisionSum
        cost value qAdmit +
      ∑ g : Group, lowerLeft g
        =
          (∑ g : Group,
            glm20Proposition2AdmittedMassFormula standardGaussianCDFAPI
              standardBivariateGaussianCDF (populationShare g) (sigmaTilde g)
              (aRow g) (b g) (mu g) qAdmit) +
            ∑ g : Group, lowerLeft g := by
          rw [paper_proposition2_strategic_applicant_pool_masses_to_corrected_source_rows
            (populationShare := populationShare) (priorSigma := priorSigma)
            (priorPrecision := priorPrecision)
            (subPrecisionSum := subPrecisionSum)
            (fullPrecisionSum := fullPrecisionSum) (cost := cost)
            (mu := mu) (value := value) (qAdmit := qAdmit)]
    _ =
          ∑ g : Group,
            (glm20Proposition2AdmittedMassFormula standardGaussianCDFAPI
                standardBivariateGaussianCDF (populationShare g) (sigmaTilde g)
                (aRow g) (b g) (mu g) qAdmit +
              lowerLeft g) := by
          rw [Finset.sum_add_distrib]
    _ =
          ∑ g : Group, affineTotal g := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          exact
            glm20Proposition2AdmittedMassFormula_add_lowerLeftRectangle_eq_affineTotalMass
              (populationShare g) (sigmaTilde g) (aRow g) (b g) (mu g)
              qAdmit

/--
Paper Lemma 3 / Proposition 2 source endpoint for the paper's two named
groups and population-share row.

This specializes the standard-bivariate conditional-source equilibrium theorem
to `GLM20Group` and discharges population-share positivity from `0 < pi < 1`.
-/
theorem
    paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_standardBivariate_conditional_source_paper_groups
    {capacity value pi : ℝ}
    {priorSigma priorPrecision subPrecision testPrecision cost
      mu : GLM20Group → ℝ}
    (hpi : pi ∈ Set.Ioo (0 : ℝ) 1)
    (hsigma : ∀ g : GLM20Group, 0 < priorSigma g)
    (hsigma_sq : ∀ g : GLM20Group, priorSigma g ^ 2 = 1 / priorPrecision g)
    (hcapacity :
      capacity ∈ Set.Ioo (0 : ℝ)
        (∑ g : GLM20Group,
          (match g with
            | GLM20Group.groupA => 1 - pi
            | GLM20Group.groupB => pi) *
            glm20Proposition3SigmaTildeSource
              (priorSigma g) (priorPrecision g) (testPrecision g)))
    (hprior_pos : ∀ g : GLM20Group, 0 < priorPrecision g)
    (hsub_pos : ∀ g : GLM20Group, 0 < subPrecision g)
    (htest_pos : ∀ g : GLM20Group, 0 < testPrecision g)
    (hvalue : 0 < value)
    (hcostRatio :
      ∀ g : GLM20Group, cost g / value ∈ Set.Ioo (0 : ℝ) 1) :
    let sigmaTilde : GLM20Group → ℝ :=
      fun g =>
        glm20Proposition3SigmaTildeSource
          (priorSigma g) (priorPrecision g) (testPrecision g)
    let b : GLM20Group → ℝ :=
      fun g =>
        glm20Proposition3BSource
          (priorPrecision g) (subPrecision g) (testPrecision g)
    let aOfApply : GLM20Group → ℝ → ℝ :=
      fun g qApply =>
        glm20Proposition2AHatConditionalSource
          (priorPrecision g) (subPrecision g) (testPrecision g) (mu g)
          qApply
    let populationShare : GLM20Group → ℝ :=
      fun
        | GLM20Group.groupA => 1 - pi
        | GLM20Group.groupB => pi
    let jointApplyAdmitMass : GLM20Group → ℝ → ℝ → ℝ :=
      fun g qApply qAdmit =>
        glm20BivariateApplyAdmitMass standardGaussianCDFAPI
          standardBivariateGaussianCDF
          (populationShare g) (sigmaTilde g)
          (aOfApply g) (b g) (mu g) qApply qAdmit
    let hscale :
      ∀ g : GLM20Group,
        0 < glm20StrategicProjectedScale
          (priorPrecision g) (subPrecision g) (testPrecision g) :=
      fun g => glm20StrategicProjectedScale_pos
        (hprior_pos g) (hsub_pos g) (htest_pos g)
    ∃! equilibrium : ℝ × (GLM20Group → ℝ) × (GLM20Group → ℝ → Bool),
      glm20Lemma3FullPolicyThresholdEquilibrium standardGaussianQuantileAPI
        (glm20Lemma3StrategicApplicantMass standardGaussianQuantileAPI
          jointApplyAdmitMass priorPrecision subPrecision testPrecision cost
          value)
        capacity value priorPrecision subPrecision testPrecision cost hscale
        equilibrium := by
  let populationShare : GLM20Group → ℝ := fun
    | GLM20Group.groupA => 1 - pi
    | GLM20Group.groupB => pi
  have hpopulation :
      ∀ g : GLM20Group, 0 < populationShare g := by
    intro g
    cases g
    · simpa [populationShare] using sub_pos.mpr hpi.2
    · simpa [populationShare] using hpi.1
  haveI : Nonempty GLM20Group := ⟨GLM20Group.groupA⟩
  exact
    paper_lemma3_full_policy_threshold_equilibrium_existsUnique_of_standardBivariate_conditional_source_components
      (Group := GLM20Group)
      (populationShare := populationShare)
      (priorSigma := priorSigma) (priorPrecision := priorPrecision)
      (subPrecision := subPrecision) (testPrecision := testPrecision)
      (cost := cost) (mu := mu) (capacity := capacity) (value := value)
      hpopulation hsigma hsigma_sq (by simpa [populationShare] using hcapacity)
      hprior_pos hsub_pos htest_pos
      hvalue hcostRatio

/--
Proposition 6 standard-Gaussian generated-row bundle.

On the same source-parameter diversity table, this records both paper-facing
facts a human checker wants at once: school `J1` drops the test iff the
displayed strict diversity inequality holds, and `(P_sub,P_full)` is the weak
diversity-only equilibrium iff the corresponding weak inequality holds.  The
only extra strategic-side premise is that school `J2`'s fallback sub/full entry
matches its sub/sub entry.
-/
theorem
    paper_proposition6_standardGaussian_drop_iff_and_subFull_equilibrium_of_J2_fallback_eq
    {Group School : Type*} [DecidableEq School]
    {massTestTaking : Group → GLM20StrategicPolicyState → ℝ}
    {admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ}
    (subSubDiversity subFullDiversityFallback fullSubDiversity
      fullFullDiversityFallback : School → ℝ)
    (J1 J2 : School)
    {groupBPopulationShare capacity1 priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB
      fullPrecisionSumB aB mu q1Full : ℝ}
    (hJ1_ne_J2 : J1 ≠ J2)
    (hJ2_fallback_eq :
      subFullDiversityFallback J2 = subSubDiversity J2) :
    (glm20Proposition6J1DropsTestForDiversity
        (glm20DiversityBinaryPolicySurface massTestTaking
          admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subFullDiversityFallback
              capacity1 groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity
            (glm20Proposition6SourceParameterFullFullDiversityRow
              standardGaussianCDFAPI standardBivariateGaussianCDF J1
              fullFullDiversityFallback groupBPopulationShare capacity1
              priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB
              aB mu q1Full))
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2)
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) ∧
      ((glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subFullDiversityFallback
              capacity1 groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity
            (glm20Proposition6SourceParameterFullFullDiversityRow
              standardGaussianCDFAPI standardBivariateGaussianCDF J1
              fullFullDiversityFallback groupBPopulationShare capacity1
              priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB
              aB mu q1Full))
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2).policyPairIsEquilibrium
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull ↔
        glm20Proposition6SourceParameterFullDiversityValue
            standardGaussianCDFAPI standardBivariateGaussianCDF
            groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
            subPrecisionSumB fullPrecisionSumB aB mu q1Full ≤
          glm20Proposition6SourceParameterSubDiversityValue
            standardGaussianQuantileAPI capacity1 groupBPopulationShare
            priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
            priorPrecisionB subPrecisionSumB) := by
  constructor
  · exact
      paper_proposition6_policyState_j1_drops_test_iff_standardGaussian_source_parameter_diversity_rows
        (massTestTaking := massTestTaking)
        (admittedAcademicMerit := admittedAcademicMerit)
        subSubDiversity subFullDiversityFallback fullSubDiversity
        fullFullDiversityFallback J1 J2
        (groupBPopulationShare := groupBPopulationShare)
        (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
        (priorPrecisionA := priorPrecisionA)
        (subPrecisionSumA := subPrecisionSumA)
        (priorSigmaB := priorSigmaB)
        (priorPrecisionB := priorPrecisionB)
        (subPrecisionSumB := subPrecisionSumB)
        (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
        (mu := mu) (q1Full := q1Full)
  · exact
      paper_proposition6_policyState_diversity_surface_subFull_equilibrium_iff_standardGaussian_source_parameter_diversity_rows_of_J2_fallback_eq
        (massTestTaking := massTestTaking)
        (admittedAcademicMerit := admittedAcademicMerit)
        subSubDiversity subFullDiversityFallback fullSubDiversity
        fullFullDiversityFallback J1 J2
        (groupBPopulationShare := groupBPopulationShare)
        (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
        (priorPrecisionA := priorPrecisionA)
        (subPrecisionSumA := subPrecisionSumA)
        (priorSigmaB := priorSigmaB)
        (priorPrecisionB := priorPrecisionB)
        (subPrecisionSumB := subPrecisionSumB)
        (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
        (mu := mu) (q1Full := q1Full) hJ1_ne_J2 hJ2_fallback_eq

/--
Proposition 6 standard-Gaussian generated-row bundle in the common
same-fallback table shape.

This is the exact drop-test/equilibrium iff bundle, not just the strict
consequence.  The ordinary sub/full fallback row is literally the sub/sub
diversity row, so school `J2`'s no-deviation equality is discharged by
construction.
-/
theorem
    paper_proposition6_standardGaussian_drop_iff_and_subFull_equilibrium_of_J2_same_fallback
    {Group School : Type*} [DecidableEq School]
    {massTestTaking : Group → GLM20StrategicPolicyState → ℝ}
    {admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ}
    (subSubDiversity fullSubDiversity fullFullDiversityFallback :
      School → ℝ)
    (J1 J2 : School)
    {groupBPopulationShare capacity1 priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB
      fullPrecisionSumB aB mu q1Full : ℝ}
    (hJ1_ne_J2 : J1 ≠ J2) :
    (glm20Proposition6J1DropsTestForDiversity
        (glm20DiversityBinaryPolicySurface massTestTaking
          admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subSubDiversity capacity1
              groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity
            (glm20Proposition6SourceParameterFullFullDiversityRow
              standardGaussianCDFAPI standardBivariateGaussianCDF J1
              fullFullDiversityFallback groupBPopulationShare capacity1
              priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB
              aB mu q1Full))
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2)
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) ∧
      ((glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subSubDiversity capacity1
              groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity
            (glm20Proposition6SourceParameterFullFullDiversityRow
              standardGaussianCDFAPI standardBivariateGaussianCDF J1
              fullFullDiversityFallback groupBPopulationShare capacity1
              priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB
              aB mu q1Full))
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2).policyPairIsEquilibrium
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull ↔
        glm20Proposition6SourceParameterFullDiversityValue
            standardGaussianCDFAPI standardBivariateGaussianCDF
            groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
            subPrecisionSumB fullPrecisionSumB aB mu q1Full ≤
          glm20Proposition6SourceParameterSubDiversityValue
            standardGaussianQuantileAPI capacity1 groupBPopulationShare
            priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
            priorPrecisionB subPrecisionSumB) :=
  paper_proposition6_standardGaussian_drop_iff_and_subFull_equilibrium_of_J2_fallback_eq
    (massTestTaking := massTestTaking)
    (admittedAcademicMerit := admittedAcademicMerit)
    subSubDiversity subSubDiversity fullSubDiversity fullFullDiversityFallback
    J1 J2
    (groupBPopulationShare := groupBPopulationShare)
    (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
    (priorPrecisionA := priorPrecisionA)
    (subPrecisionSumA := subPrecisionSumA)
    (priorSigmaB := priorSigmaB)
    (priorPrecisionB := priorPrecisionB)
    (subPrecisionSumB := subPrecisionSumB)
    (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
    (mu := mu) (q1Full := q1Full) hJ1_ne_J2 rfl

/--
Proposition 6 row support: the generated sub/full source-parameter diversity
row agrees with its fallback row at every school other than `J1`.
-/
theorem paper_proposition6_source_parameter_subFullDiversityRow_eq_fallback_of_ne
    (Q : StandardGaussianQuantileAPI)
    {School : Type*} [DecidableEq School]
    (fallback : School → ℝ) {J1 J : School}
    {capacity1 groupBPopulationShare priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB : ℝ}
    (hJ : J ≠ J1) :
    glm20Proposition6SourceParameterSubFullDiversityRow Q J1 fallback
        capacity1 groupBPopulationShare priorSigmaA priorPrecisionA
        subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB J =
      fallback J := by
  simpa [glm20Proposition6SourceParameterSubFullDiversityRow] using
    (glm20OverrideSchoolValue_of_ne
      (target := J1) (J := J) hJ
      (value :=
        glm20Proposition6SourceParameterSubDiversityValue Q capacity1
          groupBPopulationShare priorSigmaA priorPrecisionA subPrecisionSumA
          priorSigmaB priorPrecisionB subPrecisionSumB)
      fallback)

/--
Proposition 6 row support: the generated full/full source-parameter diversity
row agrees with its fallback row at every school other than `J1`.
-/
theorem paper_proposition6_source_parameter_fullFullDiversityRow_eq_fallback_of_ne
    (api : StandardGaussianCDFAPI) (bivariateCDF : ℝ → ℝ → ℝ → ℝ)
    {School : Type*} [DecidableEq School]
    (fallback : School → ℝ) {J1 J : School}
    {groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
      subPrecisionSumB fullPrecisionSumB aB mu q1Full : ℝ}
    (hJ : J ≠ J1) :
    glm20Proposition6SourceParameterFullFullDiversityRow api bivariateCDF
        J1 fallback groupBPopulationShare capacity1 priorSigmaB
        priorPrecisionB subPrecisionSumB fullPrecisionSumB aB mu q1Full J =
      fallback J := by
  simpa [glm20Proposition6SourceParameterFullFullDiversityRow] using
    (glm20OverrideSchoolValue_of_ne
      (target := J1) (J := J) hJ
      (value :=
        glm20Proposition6SourceParameterFullDiversityValue api bivariateCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full)
      fallback)

/--
Proposition 6 standard-Gaussian generated-row consequence.

The strict displayed Proposition 6 inequality is enough to get both pieces of
the Section 5 narrative on the generated diversity table: school `J1` drops
the test, and `(P_sub,P_full)` is a diversity-only equilibrium.
-/
theorem
    paper_proposition6_standardGaussian_strict_inequality_implies_drop_and_subFull_equilibrium_of_J2_fallback_eq
    {Group School : Type*} [DecidableEq School]
    {massTestTaking : Group → GLM20StrategicPolicyState → ℝ}
    {admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ}
    (subSubDiversity subFullDiversityFallback fullSubDiversity
      fullFullDiversityFallback : School → ℝ)
    (J1 J2 : School)
    {groupBPopulationShare capacity1 priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB
      fullPrecisionSumB aB mu q1Full : ℝ}
    (hJ1_ne_J2 : J1 ≠ J2)
    (hJ2_fallback_eq :
      subFullDiversityFallback J2 = subSubDiversity J2)
    (hineq :
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) :
    glm20Proposition6J1DropsTestForDiversity
        (glm20DiversityBinaryPolicySurface massTestTaking
          admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subFullDiversityFallback
              capacity1 groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity
            (glm20Proposition6SourceParameterFullFullDiversityRow
              standardGaussianCDFAPI standardBivariateGaussianCDF J1
              fullFullDiversityFallback groupBPopulationShare capacity1
              priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB
              aB mu q1Full))
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2)
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ∧
      (glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subFullDiversityFallback
              capacity1 groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity
            (glm20Proposition6SourceParameterFullFullDiversityRow
              standardGaussianCDFAPI standardBivariateGaussianCDF J1
              fullFullDiversityFallback groupBPopulationShare capacity1
              priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB
              aB mu q1Full))
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2).policyPairIsEquilibrium
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull := by
  have hbundle :=
    paper_proposition6_standardGaussian_drop_iff_and_subFull_equilibrium_of_J2_fallback_eq
      (massTestTaking := massTestTaking)
      (admittedAcademicMerit := admittedAcademicMerit)
      subSubDiversity subFullDiversityFallback fullSubDiversity
      fullFullDiversityFallback J1 J2
      (groupBPopulationShare := groupBPopulationShare)
      (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
      (priorPrecisionA := priorPrecisionA)
      (subPrecisionSumA := subPrecisionSumA)
      (priorSigmaB := priorSigmaB)
      (priorPrecisionB := priorPrecisionB)
      (subPrecisionSumB := subPrecisionSumB)
      (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
      (mu := mu) (q1Full := q1Full) hJ1_ne_J2 hJ2_fallback_eq
  exact ⟨hbundle.1.mpr hineq, hbundle.2.mpr (le_of_lt hineq)⟩

/--
Proposition 6 standard-Gaussian generated-row consequence in the common
same-fallback table shape.

Here the ordinary fallback sub/full row is literally the sub/sub diversity row,
so the school-`J2` no-deviation premise is discharged without an explicit
pointwise equality argument.
-/
theorem
    paper_proposition6_standardGaussian_strict_inequality_implies_drop_and_subFull_equilibrium_of_J2_same_fallback
    {Group School : Type*} [DecidableEq School]
    {massTestTaking : Group → GLM20StrategicPolicyState → ℝ}
    {admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ}
    (subSubDiversity fullSubDiversity fullFullDiversityFallback :
      School → ℝ)
    (J1 J2 : School)
    {groupBPopulationShare capacity1 priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB
      fullPrecisionSumB aB mu q1Full : ℝ}
    (hJ1_ne_J2 : J1 ≠ J2)
    (hineq :
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) :
    glm20Proposition6J1DropsTestForDiversity
        (glm20DiversityBinaryPolicySurface massTestTaking
          admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subSubDiversity capacity1
              groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity
            (glm20Proposition6SourceParameterFullFullDiversityRow
              standardGaussianCDFAPI standardBivariateGaussianCDF J1
              fullFullDiversityFallback groupBPopulationShare capacity1
              priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB
              aB mu q1Full))
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2)
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ∧
      (glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subSubDiversity capacity1
              groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity
            (glm20Proposition6SourceParameterFullFullDiversityRow
              standardGaussianCDFAPI standardBivariateGaussianCDF J1
              fullFullDiversityFallback groupBPopulationShare capacity1
              priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB
              aB mu q1Full))
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2).policyPairIsEquilibrium
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull :=
  paper_proposition6_standardGaussian_strict_inequality_implies_drop_and_subFull_equilibrium_of_J2_fallback_eq
    (massTestTaking := massTestTaking)
    (admittedAcademicMerit := admittedAcademicMerit)
    subSubDiversity subSubDiversity fullSubDiversity fullFullDiversityFallback
    J1 J2
    (groupBPopulationShare := groupBPopulationShare)
    (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
    (priorPrecisionA := priorPrecisionA)
    (subPrecisionSumA := subPrecisionSumA)
    (priorSigmaB := priorSigmaB)
    (priorPrecisionB := priorPrecisionB)
    (subPrecisionSumB := subPrecisionSumB)
    (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
    (mu := mu) (q1Full := q1Full) hJ1_ne_J2 rfl hineq

/--
Proposition 6 standard-Gaussian concrete-row bundle.

On an actual four-row diversity table, the two school-`J1` source-formula row
identifications are enough to recover the paper's exact strict drop-test iff
and the weak `(P_sub,P_full)` equilibrium iff.  Unlike the generated-row
bundle, the school-`J2` no-deviation condition remains visible as the ordinary
row inequality `D_2(P_sub,P_sub) ≤ D_2(P_sub,P_full)`.
-/
theorem
    paper_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_iff
    {Group School : Type*}
    {massTestTaking : Group → GLM20StrategicPolicyState → ℝ}
    {admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ}
    (subSubDiversity subFullDiversity fullSubDiversity fullFullDiversity :
      School → ℝ)
    (J1 J2 : School)
    {groupBPopulationShare capacity1 priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB
      fullPrecisionSumB aB mu q1Full : ℝ}
    (hfull :
      fullFullDiversity J1 =
        glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full)
    (hsub :
      subFullDiversity J1 =
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) :
    (glm20Proposition6J1DropsTestForDiversity
        (glm20DiversityBinaryPolicySurface massTestTaking
          admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            subFullDiversity fullSubDiversity fullFullDiversity)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2)
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) ∧
      ((glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            subFullDiversity fullSubDiversity fullFullDiversity)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2).policyPairIsEquilibrium
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull ↔
        glm20Proposition6SourceParameterFullDiversityValue
            standardGaussianCDFAPI standardBivariateGaussianCDF
            groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
            subPrecisionSumB fullPrecisionSumB aB mu q1Full ≤
          glm20Proposition6SourceParameterSubDiversityValue
            standardGaussianQuantileAPI capacity1 groupBPopulationShare
            priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
            priorPrecisionB subPrecisionSumB ∧
        subSubDiversity J2 ≤ subFullDiversity J2) := by
  let S :=
    glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
      (glm20StrategicPolicyStateDiversity subSubDiversity
        subFullDiversity fullSubDiversity fullFullDiversity)
      glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
      GLM20StrategicPolicyState.singleFull J1 J2
  change
    (glm20Proposition6J1DropsTestForDiversity S
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) ∧
      (S.policyPairIsEquilibrium GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull ↔
        glm20Proposition6SourceParameterFullDiversityValue
            standardGaussianCDFAPI standardBivariateGaussianCDF
            groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
            subPrecisionSumB fullPrecisionSumB aB mu q1Full ≤
          glm20Proposition6SourceParameterSubDiversityValue
            standardGaussianQuantileAPI capacity1 groupBPopulationShare
            priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
            priorPrecisionB subPrecisionSumB ∧
        subSubDiversity J2 ≤ subFullDiversity J2)
  have hfullFormula :
      fullFullDiversity J1 =
        glm20Proposition6FullDiversityFormula standardGaussianCDFAPI
          standardBivariateGaussianCDF groupBPopulationShare capacity1
          (glm20Proposition3SigmaTildeSource
            priorSigmaB priorPrecisionB fullPrecisionSumB)
          aB
          (glm20Proposition3BSource
            priorPrecisionB subPrecisionSumB fullPrecisionSumB)
          mu q1Full := by
    simpa [glm20Proposition6SourceParameterFullDiversityValue] using hfull
  have hsubFormula :
      subFullDiversity J1 =
        glm20Proposition6PaperSubDiversityFormula
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          (glm20Proposition6SubSigmaTildeSourceRatio
            priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
            priorPrecisionB subPrecisionSumB) := by
    simpa [glm20Proposition6SourceParameterSubDiversityValue] using hsub
  constructor
  · have hstrictIff :=
      paper_proposition6_policyState_j1_strict_diversity_best_response_iff_standardGaussian_source_parameter_formulas
        (massTestTaking := massTestTaking)
        (admittedAcademicMerit := admittedAcademicMerit)
        subSubDiversity subFullDiversity fullSubDiversity fullFullDiversity
        J1 J2
        (groupBPopulationShare := groupBPopulationShare)
        (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
        (priorPrecisionA := priorPrecisionA)
        (subPrecisionSumA := subPrecisionSumA)
        (priorSigmaB := priorSigmaB)
        (priorPrecisionB := priorPrecisionB)
        (subPrecisionSumB := subPrecisionSumB)
        (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
        (mu := mu) (q1Full := q1Full) hfullFormula hsubFormula
    have hstrictDrop :
        glm20Proposition6J1StrictDiversityBestResponseDropsTest S
            glm20StrategicPolicyStatePair J1
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull ↔
          glm20Proposition6J1DropsTestForDiversity S
            glm20StrategicPolicyStatePair J1
            GLM20StrategicPolicyState.singleSub
            GLM20StrategicPolicyState.singleFull :=
      glm20Proposition6J1StrictDiversityBestResponseDropsTest_iff S
        glm20StrategicPolicyStatePair J1
    simpa [glm20Proposition6SourceParameterFullDiversityValue,
      glm20Proposition6SourceParameterSubDiversityValue] using
      hstrictDrop.symm.trans hstrictIff
  · simpa [S, glm20Proposition6SourceParameterFullDiversityValue,
      glm20Proposition6SourceParameterSubDiversityValue] using
      (paper_proposition6_policyState_diversity_surface_subFull_equilibrium_iff_standardGaussian_source_parameter_formulas
        (massTestTaking := massTestTaking)
        (admittedAcademicMerit := admittedAcademicMerit)
        subSubDiversity subFullDiversity fullSubDiversity fullFullDiversity
        J1 J2
        (groupBPopulationShare := groupBPopulationShare)
        (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
        (priorPrecisionA := priorPrecisionA)
        (subPrecisionSumA := subPrecisionSumA)
        (priorSigmaB := priorSigmaB)
        (priorPrecisionB := priorPrecisionB)
        (subPrecisionSumB := subPrecisionSumB)
        (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
        (mu := mu) (q1Full := q1Full) hfullFormula hsubFormula)

/--
Proposition 6 standard-Gaussian concrete-row bundle in the common
same-fallback shape.

On an actual four-row diversity table, if school `J2`'s ordinary
`(P_sub,P_full)` diversity row equals its `(P_sub,P_sub)` row, the weak
`J2` no-deviation condition is automatic.  The source-row bundle then reduces
to the two school-`J1` source-formula row identifications.
-/
theorem
    paper_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_same_fallback
    {Group School : Type*}
    {massTestTaking : Group → GLM20StrategicPolicyState → ℝ}
    {admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ}
    (subSubDiversity subFullDiversity fullSubDiversity fullFullDiversity :
      School → ℝ)
    (J1 J2 : School)
    {groupBPopulationShare capacity1 priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB
      fullPrecisionSumB aB mu q1Full : ℝ}
    (hJ2_same : subSubDiversity J2 = subFullDiversity J2)
    (hfull :
      fullFullDiversity J1 =
        glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full)
    (hsub :
      subFullDiversity J1 =
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) :
    (glm20Proposition6J1DropsTestForDiversity
        (glm20DiversityBinaryPolicySurface massTestTaking
          admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            subFullDiversity fullSubDiversity fullFullDiversity)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2)
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) ∧
      ((glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            subFullDiversity fullSubDiversity fullFullDiversity)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2).policyPairIsEquilibrium
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull ↔
        glm20Proposition6SourceParameterFullDiversityValue
            standardGaussianCDFAPI standardBivariateGaussianCDF
            groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
            subPrecisionSumB fullPrecisionSumB aB mu q1Full ≤
          glm20Proposition6SourceParameterSubDiversityValue
            standardGaussianQuantileAPI capacity1 groupBPopulationShare
            priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
            priorPrecisionB subPrecisionSumB) := by
  have hbundle :=
    paper_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_iff
      (massTestTaking := massTestTaking)
      (admittedAcademicMerit := admittedAcademicMerit)
      subSubDiversity subFullDiversity fullSubDiversity fullFullDiversity
      J1 J2
      (groupBPopulationShare := groupBPopulationShare)
      (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
      (priorPrecisionA := priorPrecisionA)
      (subPrecisionSumA := subPrecisionSumA)
      (priorSigmaB := priorSigmaB)
      (priorPrecisionB := priorPrecisionB)
      (subPrecisionSumB := subPrecisionSumB)
      (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
      (mu := mu) (q1Full := q1Full) hfull hsub
  constructor
  · exact hbundle.1
  · constructor
    · intro hEq
      exact (hbundle.2.mp hEq).1
    · intro hineq
      exact hbundle.2.mpr ⟨hineq, le_of_eq hJ2_same⟩

/--
Proposition 6 exact source-row bundle with the generated sub/full row.

On an actual source-game diversity table whose `(P_sub,P_full)` row is the
displayed source-parameter row generated from the `(P_sub,P_sub)` fallback,
the `J1` sub-row formula and school-`J2` same-fallback condition are supplied
by construction.  The only visible source-row premise is the school-`J1`
full/full row identity.
-/
theorem
    paper_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback
    {Group School : Type*} [DecidableEq School]
    {massTestTaking : Group → GLM20StrategicPolicyState → ℝ}
    {admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ}
    (subSubDiversity fullSubDiversity fullFullDiversity : School → ℝ)
    (J1 J2 : School)
    {groupBPopulationShare capacity1 priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB
      fullPrecisionSumB aB mu q1Full : ℝ}
    (hJ1_ne_J2 : J1 ≠ J2)
    (hfull :
      fullFullDiversity J1 =
        glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full) :
    (glm20Proposition6J1DropsTestForDiversity
        (glm20DiversityBinaryPolicySurface massTestTaking
          admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subSubDiversity capacity1
              groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity fullFullDiversity)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2)
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) ∧
      ((glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subSubDiversity capacity1
              groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity fullFullDiversity)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2).policyPairIsEquilibrium
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull ↔
        glm20Proposition6SourceParameterFullDiversityValue
            standardGaussianCDFAPI standardBivariateGaussianCDF
            groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
            subPrecisionSumB fullPrecisionSumB aB mu q1Full ≤
          glm20Proposition6SourceParameterSubDiversityValue
            standardGaussianQuantileAPI capacity1 groupBPopulationShare
            priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
            priorPrecisionB subPrecisionSumB) := by
  let subFullDiversity :=
    glm20Proposition6SourceParameterSubFullDiversityRow
      standardGaussianQuantileAPI J1 subSubDiversity capacity1
      groupBPopulationShare priorSigmaA priorPrecisionA subPrecisionSumA
      priorSigmaB priorPrecisionB subPrecisionSumB
  have hJ2_ne_J1 : J2 ≠ J1 := by
    intro h
    exact hJ1_ne_J2 h.symm
  have hJ2_same : subSubDiversity J2 = subFullDiversity J2 := by
    dsimp [subFullDiversity]
    symm
    exact
      paper_proposition6_source_parameter_subFullDiversityRow_eq_fallback_of_ne
        standardGaussianQuantileAPI subSubDiversity hJ2_ne_J1
  have hsub :
      subFullDiversity J1 =
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB := by
    simp [subFullDiversity,
      glm20Proposition6SourceParameterSubFullDiversityRow]
  simpa [subFullDiversity] using
    (paper_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_same_fallback
      (massTestTaking := massTestTaking)
      (admittedAcademicMerit := admittedAcademicMerit)
      subSubDiversity subFullDiversity fullSubDiversity fullFullDiversity
      J1 J2
      (groupBPopulationShare := groupBPopulationShare)
      (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
      (priorPrecisionA := priorPrecisionA)
      (subPrecisionSumA := subPrecisionSumA)
      (priorSigmaB := priorSigmaB)
      (priorPrecisionB := priorPrecisionB)
      (subPrecisionSumB := subPrecisionSumB)
      (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
      (mu := mu) (q1Full := q1Full) hJ2_same hfull hsub)

/--
Proposition 6 exact source-row bundle with both generated diversity rows.

On an actual source-game diversity table whose `(P_sub,P_full)` and
`(P_full,P_full)` rows are generated from the displayed source-parameter
formulas, the two school-`J1` row identities and the school-`J2`
same-fallback condition are supplied by construction.
-/
theorem
    paper_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_generated_rows_same_fallback
    {Group School : Type*} [DecidableEq School]
    {massTestTaking : Group → GLM20StrategicPolicyState → ℝ}
    {admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ}
    (subSubDiversity fullSubDiversity fullFullDiversityFallback :
      School → ℝ)
    (J1 J2 : School)
    {groupBPopulationShare capacity1 priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB
      fullPrecisionSumB aB mu q1Full : ℝ}
    (hJ1_ne_J2 : J1 ≠ J2) :
    (glm20Proposition6J1DropsTestForDiversity
        (glm20DiversityBinaryPolicySurface massTestTaking
          admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subSubDiversity capacity1
              groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity
            (glm20Proposition6SourceParameterFullFullDiversityRow
              standardGaussianCDFAPI standardBivariateGaussianCDF J1
              fullFullDiversityFallback groupBPopulationShare capacity1
              priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB
              aB mu q1Full))
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2)
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ↔
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) ∧
      ((glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subSubDiversity capacity1
              groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity
            (glm20Proposition6SourceParameterFullFullDiversityRow
              standardGaussianCDFAPI standardBivariateGaussianCDF J1
              fullFullDiversityFallback groupBPopulationShare capacity1
              priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB
              aB mu q1Full))
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2).policyPairIsEquilibrium
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull ↔
        glm20Proposition6SourceParameterFullDiversityValue
            standardGaussianCDFAPI standardBivariateGaussianCDF
            groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
            subPrecisionSumB fullPrecisionSumB aB mu q1Full ≤
          glm20Proposition6SourceParameterSubDiversityValue
            standardGaussianQuantileAPI capacity1 groupBPopulationShare
            priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
            priorPrecisionB subPrecisionSumB) := by
  let fullFullDiversity :=
    glm20Proposition6SourceParameterFullFullDiversityRow
      standardGaussianCDFAPI standardBivariateGaussianCDF J1
      fullFullDiversityFallback groupBPopulationShare capacity1
      priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB aB
      mu q1Full
  have hfull :
      fullFullDiversity J1 =
        glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full := by
    simpa [fullFullDiversity] using
      (paper_proposition6_source_parameter_fullFullDiversityRow_eq_source_value_at_j1
        standardGaussianCDFAPI standardBivariateGaussianCDF
        fullFullDiversityFallback J1
        (groupBPopulationShare := groupBPopulationShare)
        (capacity1 := capacity1) (priorSigmaB := priorSigmaB)
        (priorPrecisionB := priorPrecisionB)
        (subPrecisionSumB := subPrecisionSumB)
        (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
        (mu := mu) (q1Full := q1Full))
  simpa [fullFullDiversity] using
    (paper_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback
      (massTestTaking := massTestTaking)
      (admittedAcademicMerit := admittedAcademicMerit)
      subSubDiversity fullSubDiversity fullFullDiversity J1 J2
      (groupBPopulationShare := groupBPopulationShare)
      (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
      (priorPrecisionA := priorPrecisionA)
      (subPrecisionSumA := subPrecisionSumA)
      (priorSigmaB := priorSigmaB)
      (priorPrecisionB := priorPrecisionB)
      (subPrecisionSumB := subPrecisionSumB)
      (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
      (mu := mu) (q1Full := q1Full) hJ1_ne_J2 hfull)

/--
Proposition 6 concrete-row consequence with the generated sub/full row.

The displayed strict source-parameter inequality gives both school `J1`'s
drop-test decision and the `(P_sub,P_full)` diversity-only equilibrium.  The
generated sub/full row supplies the school-`J1` sub-row formula and the
school-`J2` same-fallback premise internally.
-/
theorem
    paper_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium_generated_subFull_same_fallback
    {Group School : Type*} [DecidableEq School]
    {massTestTaking : Group → GLM20StrategicPolicyState → ℝ}
    {admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ}
    (subSubDiversity fullSubDiversity fullFullDiversity : School → ℝ)
    (J1 J2 : School)
    {groupBPopulationShare capacity1 priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB
      fullPrecisionSumB aB mu q1Full : ℝ}
    (hJ1_ne_J2 : J1 ≠ J2)
    (hfull :
      fullFullDiversity J1 =
        glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full)
    (hineq :
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) :
    glm20Proposition6J1DropsTestForDiversity
        (glm20DiversityBinaryPolicySurface massTestTaking
          admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subSubDiversity capacity1
              groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity fullFullDiversity)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2)
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ∧
      (glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subSubDiversity capacity1
              groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity fullFullDiversity)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2).policyPairIsEquilibrium
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull := by
  have hbundle :=
    paper_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_generated_subFull_same_fallback
      (massTestTaking := massTestTaking)
      (admittedAcademicMerit := admittedAcademicMerit)
      subSubDiversity fullSubDiversity fullFullDiversity J1 J2
      (groupBPopulationShare := groupBPopulationShare)
      (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
      (priorPrecisionA := priorPrecisionA)
      (subPrecisionSumA := subPrecisionSumA)
      (priorSigmaB := priorSigmaB)
      (priorPrecisionB := priorPrecisionB)
      (subPrecisionSumB := subPrecisionSumB)
      (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
      (mu := mu) (q1Full := q1Full) hJ1_ne_J2 hfull
  exact ⟨hbundle.1.mpr hineq, hbundle.2.mpr (le_of_lt hineq)⟩

/--
Proposition 6 concrete-row consequence with both generated diversity rows.

The displayed strict source-parameter inequality gives both school `J1`'s
drop-test decision and the `(P_sub,P_full)` diversity-only equilibrium on the
actual source-row table whose sub/full and full/full school-`J1` rows are
generated from the displayed formulas.
-/
theorem
    paper_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium_generated_rows_same_fallback
    {Group School : Type*} [DecidableEq School]
    {massTestTaking : Group → GLM20StrategicPolicyState → ℝ}
    {admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ}
    (subSubDiversity fullSubDiversity fullFullDiversityFallback :
      School → ℝ)
    (J1 J2 : School)
    {groupBPopulationShare capacity1 priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB
      fullPrecisionSumB aB mu q1Full : ℝ}
    (hJ1_ne_J2 : J1 ≠ J2)
    (hineq :
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) :
    glm20Proposition6J1DropsTestForDiversity
        (glm20DiversityBinaryPolicySurface massTestTaking
          admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subSubDiversity capacity1
              groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity
            (glm20Proposition6SourceParameterFullFullDiversityRow
              standardGaussianCDFAPI standardBivariateGaussianCDF J1
              fullFullDiversityFallback groupBPopulationShare capacity1
              priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB
              aB mu q1Full))
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2)
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ∧
      (glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            (glm20Proposition6SourceParameterSubFullDiversityRow
              standardGaussianQuantileAPI J1 subSubDiversity capacity1
              groupBPopulationShare priorSigmaA priorPrecisionA
              subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB)
            fullSubDiversity
            (glm20Proposition6SourceParameterFullFullDiversityRow
              standardGaussianCDFAPI standardBivariateGaussianCDF J1
              fullFullDiversityFallback groupBPopulationShare capacity1
              priorSigmaB priorPrecisionB subPrecisionSumB fullPrecisionSumB
              aB mu q1Full))
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2).policyPairIsEquilibrium
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull := by
  have hbundle :=
    paper_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_generated_rows_same_fallback
      (massTestTaking := massTestTaking)
      (admittedAcademicMerit := admittedAcademicMerit)
      subSubDiversity fullSubDiversity fullFullDiversityFallback J1 J2
      (groupBPopulationShare := groupBPopulationShare)
      (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
      (priorPrecisionA := priorPrecisionA)
      (subPrecisionSumA := subPrecisionSumA)
      (priorSigmaB := priorSigmaB)
      (priorPrecisionB := priorPrecisionB)
      (subPrecisionSumB := subPrecisionSumB)
      (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
      (mu := mu) (q1Full := q1Full) hJ1_ne_J2
  exact ⟨hbundle.1.mpr hineq, hbundle.2.mpr (le_of_lt hineq)⟩

/--
Proposition 6 standard-Gaussian concrete-row consequence.

This is the source-game version of the generated-row wrappers above: it works
on the actual four-row diversity table.  The visible premises are exactly the
school `J2` weak no-deviation inequality, the two school-`J1` source-formula
row identifications, and the displayed strict diversity inequality.
-/
theorem
    paper_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium
    {Group School : Type*}
    {massTestTaking : Group → GLM20StrategicPolicyState → ℝ}
    {admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ}
    (subSubDiversity subFullDiversity fullSubDiversity fullFullDiversity :
      School → ℝ)
    (J1 J2 : School)
    {groupBPopulationShare capacity1 priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB
      fullPrecisionSumB aB mu q1Full : ℝ}
    (hJ2 : subSubDiversity J2 ≤ subFullDiversity J2)
    (hfull :
      fullFullDiversity J1 =
        glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full)
    (hsub :
      subFullDiversity J1 =
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB)
    (hineq :
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) :
    glm20Proposition6J1DropsTestForDiversity
        (glm20DiversityBinaryPolicySurface massTestTaking
          admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            subFullDiversity fullSubDiversity fullFullDiversity)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2)
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ∧
      (glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            subFullDiversity fullSubDiversity fullFullDiversity)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2).policyPairIsEquilibrium
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull := by
  have hbundle :=
    paper_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_iff
      (massTestTaking := massTestTaking)
      (admittedAcademicMerit := admittedAcademicMerit)
      subSubDiversity subFullDiversity fullSubDiversity fullFullDiversity
      J1 J2
      (groupBPopulationShare := groupBPopulationShare)
      (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
      (priorPrecisionA := priorPrecisionA)
      (subPrecisionSumA := subPrecisionSumA)
      (priorSigmaB := priorSigmaB)
      (priorPrecisionB := priorPrecisionB)
      (subPrecisionSumB := subPrecisionSumB)
      (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
      (mu := mu) (q1Full := q1Full) hfull hsub
  exact ⟨hbundle.1.mpr hineq, hbundle.2.mpr ⟨le_of_lt hineq, hJ2⟩⟩

/--
Proposition 6 standard-Gaussian concrete-row consequence in the common
same-fallback shape.

This is the source-game analogue of the generated-table same-fallback
consequence: the displayed strict source-parameter inequality gives both
school `J1`'s drop-test decision and the weak `(P_sub,P_full)` equilibrium,
with school `J2`'s weak no-deviation condition discharged by row equality.
-/
theorem
    paper_proposition6_standardGaussian_source_rows_strict_inequality_implies_drop_and_subFull_equilibrium_same_fallback
    {Group School : Type*}
    {massTestTaking : Group → GLM20StrategicPolicyState → ℝ}
    {admittedAcademicMerit :
      School → Group → GLM20StrategicPolicyState → ℝ}
    (subSubDiversity subFullDiversity fullSubDiversity fullFullDiversity :
      School → ℝ)
    (J1 J2 : School)
    {groupBPopulationShare capacity1 priorSigmaA priorPrecisionA
      subPrecisionSumA priorSigmaB priorPrecisionB subPrecisionSumB
      fullPrecisionSumB aB mu q1Full : ℝ}
    (hJ2_same : subSubDiversity J2 = subFullDiversity J2)
    (hfull :
      fullFullDiversity J1 =
        glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full)
    (hsub :
      subFullDiversity J1 =
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB)
    (hineq :
      glm20Proposition6SourceParameterFullDiversityValue
          standardGaussianCDFAPI standardBivariateGaussianCDF
          groupBPopulationShare capacity1 priorSigmaB priorPrecisionB
          subPrecisionSumB fullPrecisionSumB aB mu q1Full <
        glm20Proposition6SourceParameterSubDiversityValue
          standardGaussianQuantileAPI capacity1 groupBPopulationShare
          priorSigmaA priorPrecisionA subPrecisionSumA priorSigmaB
          priorPrecisionB subPrecisionSumB) :
    glm20Proposition6J1DropsTestForDiversity
        (glm20DiversityBinaryPolicySurface massTestTaking
          admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            subFullDiversity fullSubDiversity fullFullDiversity)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2)
        glm20StrategicPolicyStatePair J1
        GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull ∧
      (glm20DiversityBinaryPolicySurface massTestTaking admittedAcademicMerit
          (glm20StrategicPolicyStateDiversity subSubDiversity
            subFullDiversity fullSubDiversity fullFullDiversity)
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J1 J2).policyPairIsEquilibrium
          GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull := by
  have hbundle :=
    paper_proposition6_standardGaussian_source_rows_drop_iff_and_subFull_equilibrium_same_fallback
      (massTestTaking := massTestTaking)
      (admittedAcademicMerit := admittedAcademicMerit)
      subSubDiversity subFullDiversity fullSubDiversity fullFullDiversity
      J1 J2
      (groupBPopulationShare := groupBPopulationShare)
      (capacity1 := capacity1) (priorSigmaA := priorSigmaA)
      (priorPrecisionA := priorPrecisionA)
      (subPrecisionSumA := subPrecisionSumA)
      (priorSigmaB := priorSigmaB)
      (priorPrecisionB := priorPrecisionB)
      (subPrecisionSumB := subPrecisionSumB)
      (fullPrecisionSumB := fullPrecisionSumB) (aB := aB)
      (mu := mu) (q1Full := q1Full) hJ2_same hfull hsub
  exact ⟨hbundle.1.mpr hineq, hbundle.2.mpr (le_of_lt hineq)⟩

/--
Proposition 5(i) / Theorem 3(i) interval bridge with fixed-pool merit
comparisons derived from Theorem 2 tail-mean data.

This is the raw-survivor Proposition 5(i) bridge, but the two fixed-pool
merit assumptions for school `J1` are discharged internally from Gaussian
upper-tail-mean identities, equal means, larger full-policy scale, and ordered
thresholds.
-/
abbrev
    paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_merit_crossings_interval_capacity_tail_mean_fixed_pool_and_group_merit_formulas_of_raw_survivor_conditions
    (Q : StandardGaussianQuantileAPI) (C : GaussianHazardCertificate)
    {Group Policy School Equilibrium : Type*}
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
    (J1DropLaw J1KeepLaw : Group → GaussianScaleLaw)
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
    (hJ1Mean : ∀ g, (J1DropLaw g).mean = (J1KeepLaw g).mean)
    (hJ1Scale : ∀ g, (J1DropLaw g).scale < (J1KeepLaw g).scale)
    (hJ1ThresholdMean :
      ∀ g, (J1DropLaw g).mean < J1DropThreshold g)
    (hJ1Threshold :
      ∀ g, J1DropThreshold g ≤ J1KeepThreshold g)
    (hJ1DropMerit :
      ∀ g,
        ¬ q1Sub < fullFullCutoff groupA →
          ¬ q1Sub < fullFullCutoff groupB →
            S.admittedAcademicMerit J1 g (policyPair Psub Pfull) =
              C.normalUpperTailMean (J1DropLaw g) (J1DropThreshold g))
    (hJ1KeepMerit :
      ∀ g,
        ¬ q1Sub < fullFullCutoff groupA →
          ¬ q1Sub < fullFullCutoff groupB →
            S.admittedAcademicMerit J1 g (policyPair Pfull Pfull) =
              C.normalUpperTailMean (J1KeepLaw g) (J1KeepThreshold g))
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
    (hJ2MassB :
      S.massTestTaking groupB (policyPair Psub Pfull) ≥ capacity2)
    (hJ2MeritGtB :
      populationShare groupB *
          S.admittedAcademicMerit J2 groupB (policyPair Psub Pfull) >
        populationShare groupA *
            S.admittedAcademicMerit J2 groupA (policyPair Psub Psub) +
          populationShare groupB *
            S.admittedAcademicMerit J2 groupB (policyPair Psub Psub))
    (hJ2ObjectiveSubFullA :
      objective2 Psub Pfull =
        populationShare groupA *
          S.admittedAcademicMerit J2 groupA (policyPair Psub Pfull))
    (hJ2MassA :
      S.massTestTaking groupA (policyPair Psub Pfull) ≥ capacity2)
    (hJ2MeritGtA :
      populationShare groupA *
          S.admittedAcademicMerit J2 groupA (policyPair Psub Pfull) >
        populationShare groupA *
            S.admittedAcademicMerit J2 groupA (policyPair Psub Psub) +
          populationShare groupB *
            S.admittedAcademicMerit J2 groupB (policyPair Psub Psub)) :=
  let hfixedPoolMeritA :
      ¬ q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J1 groupA (policyPair Psub Pfull) <
            S.admittedAcademicMerit J1 groupA (policyPair Pfull Pfull) :=
    paper_proposition5_fixed_pool_group_merit_lt_of_theorem2_tail_mean_branch
      C S policyPair J1 groupA groupB groupA
      (Pdrop1 := Psub) (Pdrop2 := Pfull) (Pkeep1 := Pfull)
      (Pkeep2 := Pfull) (q := q1Sub) (cutoff := fullFullCutoff)
      (Ldrop := J1DropLaw groupA) (Lkeep := J1KeepLaw groupA)
      (thresholdDrop := J1DropThreshold groupA)
      (thresholdKeep := J1KeepThreshold groupA)
      (hJ1Mean groupA) (hJ1Scale groupA) (hJ1ThresholdMean groupA)
      (hJ1Threshold groupA) (hJ1DropMerit groupA) (hJ1KeepMerit groupA)
  let hfixedPoolMeritB :
      ¬ q1Sub < fullFullCutoff groupA →
        ¬ q1Sub < fullFullCutoff groupB →
          S.admittedAcademicMerit J1 groupB (policyPair Psub Pfull) <
            S.admittedAcademicMerit J1 groupB (policyPair Pfull Pfull) :=
    paper_proposition5_fixed_pool_group_merit_lt_of_theorem2_tail_mean_branch
      C S policyPair J1 groupA groupB groupB
      (Pdrop1 := Psub) (Pdrop2 := Pfull) (Pkeep1 := Pfull)
      (Pkeep2 := Pfull) (q := q1Sub) (cutoff := fullFullCutoff)
      (Ldrop := J1DropLaw groupB) (Lkeep := J1KeepLaw groupB)
      (thresholdDrop := J1DropThreshold groupB)
      (thresholdKeep := J1KeepThreshold groupB)
      (hJ1Mean groupB) (hJ1Scale groupB) (hJ1ThresholdMean groupB)
      (hJ1Threshold groupB) (hJ1DropMerit groupB) (hJ1KeepMerit groupB)
  paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_merit_crossings_interval_capacity_fixed_pool_and_group_merit_formulas_of_raw_survivor_conditions
    (Q := Q) (S := S) (policyPair := policyPair) (Psub := Psub)
    (Pfull := Pfull) (J1 := J1) (J2 := J2) (groupA := groupA)
    (groupB := groupB) (populationShare := populationShare)
    (testCost := testCost) (leftCost := leftCost)
    (rightCost := rightCost) (q2Full := q2Full) (scale := scale)
    (v2 := v2) (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) subEstimateLaw
    (fullFullCutoff := fullFullCutoff) objective2 meritOfCutoff
    testFreeMerit hleftRight hscale hleftPos hrightLtV2 hcostMem
    hmerit_cont hmerit_anti hlowCost hhighCost hshareA hshareB
    hmassFullFullA hmassFullFullB hcapacity1 hfillFullFull1
    hfixedPoolMeritA hfixedPoolMeritB honlyA_J1_groupB_eq
    honlyA_J1_groupA_testBased honlyA_J1_groupA_testFree
    honlyB_J1_groupA_eq honlyB_J1_groupB_testBased
    honlyB_J1_groupB_testFree hJ2ObjectiveSubSub hJ2ObjectiveSubFullB
    hJ2MassB hJ2MeritGtB hJ2ObjectiveSubFullA hJ2MassA hJ2MeritGtA

/--
Proposition 5(i) / Theorem 3(i) source-family bridge.

This strengthens
`paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_merit_crossings_interval_capacity_tail_mean_fixed_pool_and_group_merit_formulas_of_raw_survivor_conditions`:
the fixed-pool tail-mean data is generated from concrete Gaussian source
families, common prior means/variances, and the strict precision increase from
the drop-test family to the keep-test family for school `J1`.
-/
abbrev
    paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_source_family_fixed_pool_and_group_merit_formulas_of_raw_survivor_conditions
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
    (hJ2MassB :
      S.massTestTaking groupB (policyPair Psub Pfull) ≥ capacity2)
    (hJ2MeritGtB :
      populationShare groupB *
          S.admittedAcademicMerit J2 groupB (policyPair Psub Pfull) >
        populationShare groupA *
            S.admittedAcademicMerit J2 groupA (policyPair Psub Psub) +
          populationShare groupB *
            S.admittedAcademicMerit J2 groupB (policyPair Psub Psub))
    (hJ2ObjectiveSubFullA :
      objective2 Psub Pfull =
        populationShare groupA *
          S.admittedAcademicMerit J2 groupA (policyPair Psub Pfull))
    (hJ2MassA :
      S.massTestTaking groupA (policyPair Psub Pfull) ≥ capacity2)
    (hJ2MeritGtA :
      populationShare groupA *
          S.admittedAcademicMerit J2 groupA (policyPair Psub Pfull) >
        populationShare groupA *
            S.admittedAcademicMerit J2 groupA (policyPair Psub Psub) +
          populationShare groupB *
            S.admittedAcademicMerit J2 groupB (policyPair Psub Psub)) :=
  paper_proposition5_part_i_objective_pair_iff_theorem3_subFull_condition_of_equation50_merit_crossings_interval_capacity_tail_mean_fixed_pool_and_group_merit_formulas_of_raw_survivor_conditions
    (Q := Q) (C := C) (S := S) (policyPair := policyPair)
    (Psub := Psub) (Pfull := Pfull) (J1 := J1) (J2 := J2)
    (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (leftCost := leftCost) (rightCost := rightCost) (q2Full := q2Full)
    (scale := scale) (v2 := v2) (capacity1 := capacity1)
    (capacity2 := capacity2) (q1Sub := q1Sub) subEstimateLaw
    (fullFullCutoff := fullFullCutoff) objective2 meritOfCutoff
    testFreeMerit
    (J1DropLaw := fun g => (J1DropFamily g).posteriorMeanScaleLaw)
    (J1KeepLaw := fun g => (J1KeepFamily g).posteriorMeanScaleLaw)
    J1DropThreshold J1KeepThreshold hleftRight hscale hleftPos
    hrightLtV2 hcostMem hmerit_cont hmerit_anti hlowCost hhighCost
    hshareA hshareB hmassFullFullA hmassFullFullB hcapacity1
    hfillFullFull1
    (by
      intro g
      simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
        using hJ1PriorMean g)
    (by
      intro g
      exact
        GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
          (Mlow := J1DropFamily g) (Mhigh := J1KeepFamily g)
          (hJ1PriorVar g) (hJ1Precision g))
    (by
      intro g
      simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
        using hJ1ThresholdMean g)
    hJ1Threshold hJ1DropMerit hJ1KeepMerit honlyA_J1_groupB_eq
    honlyA_J1_groupA_testBased honlyA_J1_groupA_testFree
    honlyB_J1_groupA_eq honlyB_J1_groupB_testBased
    honlyB_J1_groupB_testFree hJ2ObjectiveSubSub hJ2ObjectiveSubFullB
    hJ2MassB hJ2MeritGtB hJ2ObjectiveSubFullA hJ2MassA hJ2MeritGtA

/--
Proposition 5(ii) / Theorem 3(ii) selected equation-(46) objective bridge
with the full-sub high-at-low-root premise derived from Gaussian tail-mean
formulas.

This is a leaf adapter around
`paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas`.
It keeps the selected low/high full/full zero-payoff cutoff functions visible,
but replaces the standalone high-at-low-root proof artifact by concrete
Gaussian upper-tail-mean identifications and scale/threshold comparisons.
-/
theorem
    paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_gaussian_tail_mean_formulas
    {Group Policy School Equilibrium : Type*}
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
    (lowMeritOfCutoff : Group → ℝ → ℝ)
    (lowTestFreeMerit : Group → ℝ)
    (highMeritOfCutoff : Group → ℝ → ℝ)
    (highTestFreeMerit : Group → ℝ)
    (C : GaussianHazardCertificate)
    (lowFreeLaw highFreeLaw : Group → GaussianScaleLaw)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedLaw highBasedLaw : Group → ℝ → GaussianScaleLaw)
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
        lowTestFreeMerit g <
          lowMeritOfCutoff g (lowCutoffOfCost g (leftCost g)))
    (hlowAtRight :
      ∀ g,
        lowMeritOfCutoff g (lowCutoffOfCost g (rightCost g)) <
          lowTestFreeMerit g)
    (hhighAtLeft :
      ∀ g,
        highTestFreeMerit g <
          highMeritOfCutoff g (highCutoffOfCost g (leftCost g)))
    (hhighAtRight :
      ∀ g,
        highMeritOfCutoff g (highCutoffOfCost g (rightCost g)) <
          highTestFreeMerit g)
    (hlowFreeFormula :
      ∀ g,
        lowTestFreeMerit g =
          C.normalUpperTailMean (lowFreeLaw g) (lowFreeThreshold g))
    (hhighFreeFormula :
      ∀ g,
        highTestFreeMerit g =
          C.normalUpperTailMean (highFreeLaw g) (highFreeThreshold g))
    (hfreeMean :
      ∀ g, (highFreeLaw g).mean = (lowFreeLaw g).mean)
    (hfreeScale :
      ∀ g, (highFreeLaw g).scale < (lowFreeLaw g).scale)
    (hfreeThresholdMean :
      ∀ g, (highFreeLaw g).mean < highFreeThreshold g)
    (hfreeThreshold :
      ∀ g, highFreeThreshold g ≤ lowFreeThreshold g)
    (hlowBasedFormula :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        lowMeritOfCutoff g (lowCutoffOfCost g c) =
          C.normalUpperTailMean (lowBasedLaw g c)
            (lowBasedThreshold g c))
    (hhighBasedFormula :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        highMeritOfCutoff g (highCutoffOfCost g c) =
          C.normalUpperTailMean (highBasedLaw g c)
            (highBasedThreshold g c))
    (hbasedMean :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        (lowBasedLaw g c).mean = (highBasedLaw g c).mean)
    (hbasedScale :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        (lowBasedLaw g c).scale ≤ (highBasedLaw g c).scale)
    (hbasedThresholdMean :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        (lowBasedLaw g c).mean < lowBasedThreshold g c)
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
            lowTestFreeMerit groupA)
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
            lowTestFreeMerit groupB)
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
          highTestFreeMerit groupA)
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
          highTestFreeMerit groupB)
    (hexpandB_J1_groupB_testBased :
      ¬ fullSubCutoff groupB < q1Sub →
        S.admittedAcademicMerit J1 groupB (policyPair Pfull Psub) =
          highMeritOfCutoff groupB
            (highCutoffOfCost groupB (testCost groupB))) :
    ∃ lowCostThreshold highCostThreshold : Group → ℝ,
      (∀ g, lowCostThreshold g ∈
        Set.Ioo (leftCost g) (rightCost g)) ∧
        (∀ g, highCostThreshold g ∈
          Set.Ioo (leftCost g) (rightCost g)) ∧
          (∀ g,
            lowMeritOfCutoff g
                (lowCutoffOfCost g (lowCostThreshold g)) =
              lowTestFreeMerit g) ∧
            (∀ g,
              highMeritOfCutoff g
                  (highCutoffOfCost g (highCostThreshold g)) =
                highTestFreeMerit g) ∧
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
  let lowTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    lowMeritOfCutoff g (lowCutoffOfCost g c)
  let highTestBasedMerit : Group → ℝ → ℝ := fun g c =>
    highMeritOfCutoff g (highCutoffOfCost g c)
  have hhighAtLowRoot :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        lowMeritOfCutoff g (lowCutoffOfCost g c) = lowTestFreeMerit g →
          highTestFreeMerit g <
            highMeritOfCutoff g (highCutoffOfCost g c) := by
    simpa [lowTestBasedMerit, highTestBasedMerit] using
      (paper_proposition5_high_merit_at_low_root_of_gaussian_tail_mean_formulas
        (C := C) (leftCost := leftCost) (rightCost := rightCost)
        lowTestBasedMerit lowTestFreeMerit highTestBasedMerit
        highTestFreeMerit lowFreeLaw highFreeLaw lowFreeThreshold
        highFreeThreshold lowBasedLaw highBasedLaw lowBasedThreshold
        highBasedThreshold hlowFreeFormula hhighFreeFormula hfreeMean
        hfreeScale hfreeThresholdMean hfreeThreshold
        (by
          intro g c hc
          simpa [lowTestBasedMerit] using hlowBasedFormula g c hc)
        (by
          intro g c hc
          simpa [highTestBasedMerit] using hhighBasedFormula g c hc)
        hbasedMean hbasedScale hbasedThresholdMean hbasedThreshold)
  exact
    paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas
      (S := S) (policyPair := policyPair) (Psub := Psub)
      (Pfull := Pfull) (J1 := J1) (J2 := J2) (groupA := groupA)
      (groupB := groupB) (populationShare := populationShare)
      (testCost := testCost) (leftCost := leftCost)
      (rightCost := rightCost) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub) subEstimateLaw
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff)
      (lowQ1Full := lowQ1Full) (lowQ2Full := lowQ2Full)
      (lowScale := lowScale) (lowV1 := lowV1) (lowV2 := lowV2)
      (highQ1Full := highQ1Full) (highQ2Full := highQ2Full)
      (highScale := highScale) (highV1 := highV1)
      (highV2 := highV2) lowCutoffOfCost highCutoffOfCost
      lowMeritOfCutoff lowTestFreeMerit highMeritOfCutoff
      highTestFreeMerit hleft_right hleft_pos hcostMem hlowScale
      hlowV2Pos hlowV2LtV1 hlowZero hlowMeritCont hlowMeritAnti
      hhighScale hhighV2Pos hhighV2LtV1 hhighZero hhighMeritCont
      hhighMeritAnti hlowAtLeft hlowAtRight hhighAtLeft hhighAtRight
      hhighAtLowRoot hshareA hshareB hmassFullFullA hmassFullFullB
      hmassFullSubA hmassFullSubB hcapacity2 hfillFullFull2
      hfixedPoolMeritA hfixedPoolMeritB honlyA_J2_groupB_eq
      honlyA_J2_groupA_testBased honlyA_J2_groupA_testFree
      honlyB_J2_groupA_eq honlyB_J2_groupB_testBased
      honlyB_J2_groupB_testFree hnoExpandA hexpandA_J1_groupB_eq
      hexpandA_J1_groupA_testFree hexpandA_J1_groupA_testBased
      hnoExpandB hexpandB_J1_groupA_eq hexpandB_J1_groupB_testFree
      hexpandB_J1_groupB_testBased

/--
Proposition 5(ii) / Theorem 3(ii) selected equation-(46) objective bridge
with full-sub Gaussian merit laws instantiated as source-family posterior-mean
laws.

This is the source-family version of
`paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_gaussian_tail_mean_formulas`.
It replaces the visible `GaussianScaleLaw` rows by
`GaussianOffsetSignalFamily.posteriorMeanScaleLaw` rows and derives the needed
mean/scale comparisons from prior-mean, prior-variance, and signal-precision
facts.
-/
abbrev
    paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_posterior_mean_scale_families
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
    (lowMeritOfCutoff : Group → ℝ → ℝ)
    (lowTestFreeMerit : Group → ℝ)
    (highMeritOfCutoff : Group → ℝ → ℝ)
    (highTestFreeMerit : Group → ℝ)
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
        lowTestFreeMerit g <
          lowMeritOfCutoff g (lowCutoffOfCost g (leftCost g)))
    (hlowAtRight :
      ∀ g,
        lowMeritOfCutoff g (lowCutoffOfCost g (rightCost g)) <
          lowTestFreeMerit g)
    (hhighAtLeft :
      ∀ g,
        highTestFreeMerit g <
          highMeritOfCutoff g (highCutoffOfCost g (leftCost g)))
    (hhighAtRight :
      ∀ g,
        highMeritOfCutoff g (highCutoffOfCost g (rightCost g)) <
          highTestFreeMerit g)
    (hlowFreeFormula :
      ∀ g,
        lowTestFreeMerit g =
          C.normalUpperTailMean
            (lowFreeFamily g).posteriorMeanScaleLaw
            (lowFreeThreshold g))
    (hhighFreeFormula :
      ∀ g,
        highTestFreeMerit g =
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
            lowTestFreeMerit groupA)
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
            lowTestFreeMerit groupB)
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
          highTestFreeMerit groupA)
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
          highTestFreeMerit groupB)
    (hexpandB_J1_groupB_testBased :
      ¬ fullSubCutoff groupB < q1Sub →
        S.admittedAcademicMerit J1 groupB (policyPair Pfull Psub) =
          highMeritOfCutoff groupB
            (highCutoffOfCost groupB (testCost groupB))) :=
  paper_proposition5_part_ii_objective_pair_iff_theorem3_fullSub_condition_of_selected_twoFull_merit_crossings_interval_capacity_fixed_pool_and_weighted_group_merit_formulas_of_gaussian_tail_mean_formulas
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
    highMeritOfCutoff highTestFreeMerit C
    (fun g => (lowFreeFamily g).posteriorMeanScaleLaw)
    (fun g => (highFreeFamily g).posteriorMeanScaleLaw)
    lowFreeThreshold highFreeThreshold
    (fun g c => (lowBasedFamily g c).posteriorMeanScaleLaw)
    (fun g c => (highBasedFamily g c).posteriorMeanScaleLaw)
    lowBasedThreshold highBasedThreshold hleft_right hleft_pos hcostMem
    hlowScale hlowV2Pos hlowV2LtV1 hlowZero hlowMeritCont
    hlowMeritAnti hhighScale hhighV2Pos hhighV2LtV1 hhighZero
    hhighMeritCont hhighMeritAnti hlowAtLeft hlowAtRight hhighAtLeft
    hhighAtRight hlowFreeFormula hhighFreeFormula
    (by
      intro g
      simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
        using hfreePriorMean g)
    (by
      intro g
      exact
        GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
          (hfreePriorVar g) (hfreePrecision g))
    (by
      intro g
      simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
        using hfreeThresholdMean g)
    hfreeThreshold hlowBasedFormula hhighBasedFormula
    (by
      intro g c hc
      simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
        using hbasedPriorMean g c hc)
    (by
      intro g c hc
      exact le_of_lt
        (GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
          (hbasedPriorVar g c hc) (hbasedPrecision g c hc)))
    (by
      intro g c hc
      simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
        using hbasedThresholdMean g c hc)
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
Proposition 5(ii) source-family support for direct full-sub merit ordering.

This specializes the abstract Gaussian tail-mean order package to
`GaussianOffsetSignalFamily.posteriorMeanScaleLaw`, deriving the mean and scale
rows from source-family prior means, prior variances, and signal-precision
comparisons.  The visible formula premises are exactly the admitted upper-tail
mean identities for the source families.
-/
theorem
    paper_proposition5_fullSub_ordered_merits_of_posterior_mean_scale_families
    (C : GaussianHazardCertificate)
    {Group LowFreeFeature HighFreeFeature LowBasedFeature
      HighBasedFeature : Type*}
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {leftCost rightCost : Group → ℝ}
    (lowTestBasedMerit : Group → ℝ → ℝ)
    (lowTestFreeMerit : Group → ℝ)
    (highTestBasedMerit : Group → ℝ → ℝ)
    (highTestFreeMerit : Group → ℝ)
    (lowFreeFamily : Group → GaussianOffsetSignalFamily LowFreeFeature)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (lowBasedThreshold highBasedThreshold : Group → ℝ → ℝ)
    (hlowFreeFormula :
      ∀ g,
        lowTestFreeMerit g =
          C.normalUpperTailMean
            (lowFreeFamily g).posteriorMeanScaleLaw
            (lowFreeThreshold g))
    (hhighFreeFormula :
      ∀ g,
        highTestFreeMerit g =
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
        lowTestBasedMerit g c =
          C.normalUpperTailMean
            (lowBasedFamily g c).posteriorMeanScaleLaw
            (lowBasedThreshold g c))
    (hhighBasedFormula :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        highTestBasedMerit g c =
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
        lowBasedThreshold g c ≤ highBasedThreshold g c) :
    (∀ g, highTestFreeMerit g < lowTestFreeMerit g) ∧
      (∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        lowTestBasedMerit g c ≤ highTestBasedMerit g c) := by
  exact
    paper_proposition5_fullSub_ordered_merits_of_gaussian_tail_mean_formulas
      C lowTestBasedMerit lowTestFreeMerit highTestBasedMerit
      highTestFreeMerit
      (fun g => (lowFreeFamily g).posteriorMeanScaleLaw)
      (fun g => (highFreeFamily g).posteriorMeanScaleLaw)
      lowFreeThreshold highFreeThreshold
      (fun g c => (lowBasedFamily g c).posteriorMeanScaleLaw)
      (fun g c => (highBasedFamily g c).posteriorMeanScaleLaw)
      lowBasedThreshold highBasedThreshold hlowFreeFormula hhighFreeFormula
      (by
        intro g
        simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
          using hfreePriorMean g)
      (by
        intro g
        exact
          GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
            (hfreePriorVar g) (hfreePrecision g))
      (by
        intro g
        simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
          using hfreeThresholdMean g)
      hfreeThreshold hlowBasedFormula hhighBasedFormula
      (by
        intro g c hc
        simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
          using hbasedPriorMean g c hc)
      (by
        intro g c hc
        exact le_of_lt
          (GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
            (hbasedPriorVar g c hc) (hbasedPrecision g c hc)))
      (by
        intro g c hc
        simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
          using hbasedThresholdMean g c hc)
      hbasedThreshold

/--
Proposition 5(ii) source-family support for the full-sub high-at-low-root
premise.

This composes the posterior-mean source-family ordered-merit adapter with the
generic high-at-low-root lemma, producing the exact root-side premise needed by
the selected full-sub objective and threshold bridges.
-/
theorem
    paper_proposition5_high_merit_at_low_root_of_posterior_mean_scale_families
    (C : GaussianHazardCertificate)
    {Group LowFreeFeature HighFreeFeature LowBasedFeature
      HighBasedFeature : Type*}
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {leftCost rightCost : Group → ℝ}
    (lowTestBasedMerit : Group → ℝ → ℝ)
    (lowTestFreeMerit : Group → ℝ)
    (highTestBasedMerit : Group → ℝ → ℝ)
    (highTestFreeMerit : Group → ℝ)
    (lowFreeFamily : Group → GaussianOffsetSignalFamily LowFreeFeature)
    (highFreeFamily : Group → GaussianOffsetSignalFamily HighFreeFeature)
    (lowFreeThreshold highFreeThreshold : Group → ℝ)
    (lowBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily LowBasedFeature)
    (highBasedFamily :
      Group → ℝ → GaussianOffsetSignalFamily HighBasedFeature)
    (lowBasedThreshold highBasedThreshold : Group → ℝ → ℝ)
    (hlowFreeFormula :
      ∀ g,
        lowTestFreeMerit g =
          C.normalUpperTailMean
            (lowFreeFamily g).posteriorMeanScaleLaw
            (lowFreeThreshold g))
    (hhighFreeFormula :
      ∀ g,
        highTestFreeMerit g =
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
        lowTestBasedMerit g c =
          C.normalUpperTailMean
            (lowBasedFamily g c).posteriorMeanScaleLaw
            (lowBasedThreshold g c))
    (hhighBasedFormula :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        highTestBasedMerit g c =
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
        lowBasedThreshold g c ≤ highBasedThreshold g c) :
    ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
      lowTestBasedMerit g c = lowTestFreeMerit g →
        highTestFreeMerit g < highTestBasedMerit g c := by
  let horders :=
    paper_proposition5_fullSub_ordered_merits_of_posterior_mean_scale_families
      C lowTestBasedMerit lowTestFreeMerit highTestBasedMerit
      highTestFreeMerit lowFreeFamily highFreeFamily lowFreeThreshold
      highFreeThreshold lowBasedFamily highBasedFamily lowBasedThreshold
      highBasedThreshold hlowFreeFormula hhighFreeFormula hfreePriorMean
      hfreePriorVar hfreePrecision hfreeThresholdMean hfreeThreshold
      hlowBasedFormula hhighBasedFormula hbasedPriorMean hbasedPriorVar
      hbasedPrecision hbasedThresholdMean hbasedThreshold
  exact
    paper_proposition5_high_merit_at_low_root_of_test_free_lt_and_test_based_le
      lowTestBasedMerit lowTestFreeMerit highTestBasedMerit
      highTestFreeMerit horders.1 horders.2

/--
Proposition 5(ii) source-family support with the full-sub test-free merit rows
generated directly from posterior-mean source families.

This is the same ordered-merit conclusion as
`paper_proposition5_fullSub_ordered_merits_of_posterior_mean_scale_families`,
but it removes the two test-free formula hypotheses by defining the low/high
test-free rows to be the corresponding posterior Gaussian upper-tail means.
The cost-indexed test-based rows remain explicit because they depend on the
constructed cost-to-cutoff maps.
-/
abbrev
    paper_proposition5_fullSub_ordered_merits_of_posterior_mean_source_free_families
    (C : GaussianHazardCertificate)
    {Group LowFreeFeature HighFreeFeature LowBasedFeature
      HighBasedFeature : Type*}
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {leftCost rightCost : Group → ℝ}
    (lowTestBasedMerit highTestBasedMerit : Group → ℝ → ℝ)
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
    (hlowBasedFormula :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        lowTestBasedMerit g c =
          C.normalUpperTailMean
            (lowBasedFamily g c).posteriorMeanScaleLaw
            (lowBasedThreshold g c))
    (hhighBasedFormula :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        highTestBasedMerit g c =
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
        lowBasedThreshold g c ≤ highBasedThreshold g c) :=
  let lowTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean (lowFreeFamily g).posteriorMeanScaleLaw
      (lowFreeThreshold g)
  let highTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean (highFreeFamily g).posteriorMeanScaleLaw
      (highFreeThreshold g)
  paper_proposition5_fullSub_ordered_merits_of_posterior_mean_scale_families
    C lowTestBasedMerit lowTestFreeMerit highTestBasedMerit
    highTestFreeMerit lowFreeFamily highFreeFamily lowFreeThreshold
    highFreeThreshold lowBasedFamily highBasedFamily lowBasedThreshold
    highBasedThreshold (by intro g; rfl) (by intro g; rfl)
    hfreePriorMean hfreePriorVar hfreePrecision hfreeThresholdMean
    hfreeThreshold hlowBasedFormula hhighBasedFormula hbasedPriorMean
    hbasedPriorVar hbasedPrecision hbasedThresholdMean hbasedThreshold

/--
Proposition 5(ii) source-family high-at-low-root support with the full-sub
test-free merit rows generated directly from posterior-mean source families.
-/
abbrev
    paper_proposition5_high_merit_at_low_root_of_posterior_mean_source_free_families
    (C : GaussianHazardCertificate)
    {Group LowFreeFeature HighFreeFeature LowBasedFeature
      HighBasedFeature : Type*}
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {leftCost rightCost : Group → ℝ}
    (lowTestBasedMerit highTestBasedMerit : Group → ℝ → ℝ)
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
    (hlowBasedFormula :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        lowTestBasedMerit g c =
          C.normalUpperTailMean
            (lowBasedFamily g c).posteriorMeanScaleLaw
            (lowBasedThreshold g c))
    (hhighBasedFormula :
      ∀ g c, c ∈ Set.Ioo (leftCost g) (rightCost g) →
        highTestBasedMerit g c =
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
        lowBasedThreshold g c ≤ highBasedThreshold g c) :=
  let lowTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean (lowFreeFamily g).posteriorMeanScaleLaw
      (lowFreeThreshold g)
  let highTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean (highFreeFamily g).posteriorMeanScaleLaw
      (highFreeThreshold g)
  paper_proposition5_high_merit_at_low_root_of_posterior_mean_scale_families
    C lowTestBasedMerit lowTestFreeMerit highTestBasedMerit
    highTestFreeMerit lowFreeFamily highFreeFamily lowFreeThreshold
    highFreeThreshold lowBasedFamily highBasedFamily lowBasedThreshold
    highBasedThreshold (by intro g; rfl) (by intro g; rfl)
    hfreePriorMean hfreePriorVar hfreePrecision hfreeThresholdMean
    hfreeThreshold hlowBasedFormula hhighBasedFormula hbasedPriorMean
    hbasedPriorVar hbasedPrecision hbasedThresholdMean hbasedThreshold

/--
Theorem 3 binary-objective adapter for a packaged full-sub Proposition 5
bridge.

The binary Theorem 3 source-condition bridge needs the full-sub objective iff
for a fixed pair of low/high cost thresholds.  Proposition 5(ii) wrappers
naturally return those thresholds together with their interval/root/order
facts.  This adapter preserves the threshold facts and feeds the packaged
objective iff into the Theorem 3 binary-objective endpoint.
-/
theorem
    paper_theorem3_source_conditions_of_binary_policy_objective_conditions_of_subFull_objective_and_fullSub_objective_bridge
    {Group Policy School Equilibrium : Type*}
    {S : GLM20StrategicPolicySurface Group Policy School Equilibrium}
    {policyPair : Policy → Policy → Policy}
    {Psub Pfull : Policy} {J2 : School} {groupA groupB : Group}
    {populationShare testCost subFullCostThreshold leftCost rightCost :
      Group → ℝ}
    {capacity2 q1Sub q2Sub : ℝ} {K : Group → ℝ → ℝ}
    (objective1 objective2 : Policy → Policy → ℝ)
    (lowTestBasedMerit : Group → ℝ → ℝ)
    (lowTestFreeMerit : Group → ℝ)
    (highTestBasedMerit : Group → ℝ → ℝ)
    (highTestFreeMerit : Group → ℝ)
    (hpolicySubFull :
      S.policyPairIsEquilibrium Psub Pfull ↔
        glm20TwoSchoolBinaryPolicyEquilibrium objective1 objective2
          Psub Pfull Psub Pfull)
    (hpolicyFullSub :
      S.policyPairIsEquilibrium Pfull Psub ↔
        glm20TwoSchoolBinaryPolicyEquilibrium objective1 objective2
          Psub Pfull Pfull Psub)
    (hsubFullObjective :
      (objective1 Pfull Pfull ≤ objective1 Psub Pfull ∧
        objective2 Psub Psub ≤ objective2 Psub Pfull) ↔
        glm20Theorem3SubFullCondition S policyPair Psub Pfull J2
          groupA groupB populationShare testCost subFullCostThreshold
          capacity2 q1Sub K)
    (hfullSubBridge :
      ∃ fullSubLowCostThreshold fullSubHighCostThreshold : Group → ℝ,
        (∀ g, fullSubLowCostThreshold g ∈
          Set.Ioo (leftCost g) (rightCost g)) ∧
          (∀ g, fullSubHighCostThreshold g ∈
            Set.Ioo (leftCost g) (rightCost g)) ∧
            (∀ g, lowTestBasedMerit g (fullSubLowCostThreshold g) =
              lowTestFreeMerit g) ∧
              (∀ g, highTestBasedMerit g (fullSubHighCostThreshold g) =
                highTestFreeMerit g) ∧
                (∀ g, 0 < fullSubLowCostThreshold g) ∧
                  (∀ g,
                    fullSubLowCostThreshold g <
                      fullSubHighCostThreshold g) ∧
                    ((objective1 Psub Psub ≤ objective1 Pfull Psub ∧
                        objective2 Pfull Pfull ≤ objective2 Pfull Psub) ↔
                      glm20Theorem3FullSubCondition S policyPair Psub Pfull
                        groupA groupB testCost fullSubLowCostThreshold
                        fullSubHighCostThreshold q1Sub q2Sub K))
    (hcostA : 0 < testCost groupA) (hcostB : 0 < testCost groupB) :
    ∃ fullSubLowCostThreshold fullSubHighCostThreshold : Group → ℝ,
      (∀ g, fullSubLowCostThreshold g ∈
        Set.Ioo (leftCost g) (rightCost g)) ∧
        (∀ g, fullSubHighCostThreshold g ∈
          Set.Ioo (leftCost g) (rightCost g)) ∧
          (∀ g, lowTestBasedMerit g (fullSubLowCostThreshold g) =
            lowTestFreeMerit g) ∧
            (∀ g, highTestBasedMerit g (fullSubHighCostThreshold g) =
              highTestFreeMerit g) ∧
              (∀ g, 0 < fullSubLowCostThreshold g) ∧
                (∀ g,
                  fullSubLowCostThreshold g <
                    fullSubHighCostThreshold g) ∧
                  ((S.policyPairIsEquilibrium Psub Pfull ↔
                      glm20Theorem3SubFullCondition S policyPair Psub Pfull
                        J2 groupA groupB populationShare testCost
                        subFullCostThreshold capacity2 q1Sub K) ∧
                    (S.policyPairIsEquilibrium Pfull Psub ↔
                      glm20Theorem3FullSubCondition S policyPair Psub Pfull
                        groupA groupB testCost fullSubLowCostThreshold
                        fullSubHighCostThreshold q1Sub q2Sub K) ∧
                      glm20Theorem3FullFullCondition S Pfull groupA groupB
                        testCost) := by
  rcases hfullSubBridge with
    ⟨fullSubLowCostThreshold, fullSubHighCostThreshold, hlowMem, hhighMem,
      hlowEq, hhighEq, hlowPos, hlowHigh, hfullSubObjective⟩
  refine
    ⟨fullSubLowCostThreshold, fullSubHighCostThreshold, hlowMem, hhighMem,
      hlowEq, hhighEq, hlowPos, hlowHigh, ?_⟩
  exact
    paper_theorem3_source_conditions_of_binary_policy_objective_conditions
      (S := S) (policyPair := policyPair) (Psub := Psub) (Pfull := Pfull)
      (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullCostThreshold := subFullCostThreshold)
      (fullSubLowCostThreshold := fullSubLowCostThreshold)
      (fullSubHighCostThreshold := fullSubHighCostThreshold)
      (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
      (K := K) objective1 objective2 hpolicySubFull hpolicyFullSub
      hsubFullObjective hfullSubObjective hcostA hcostB

/--
Theorem 3 binary-objective adapter for packaged sub-full and full-sub
Proposition 5 bridges.

This removes the last fixed `subFullCostThreshold` / `hsubFullObjective`
inputs from
`paper_theorem3_source_conditions_of_binary_policy_objective_conditions_of_subFull_objective_and_fullSub_objective_bridge`.
Both Proposition 5 packages can now be supplied as threshold-producing
bridges, and this theorem preserves the threshold facts for both policy
branches before invoking the binary Theorem 3 source-condition endpoint.
-/
theorem
    paper_theorem3_source_conditions_of_binary_policy_objective_conditions_of_subFull_objective_bridge_and_fullSub_objective_bridge
    {Group Policy School Equilibrium : Type*}
    {S : GLM20StrategicPolicySurface Group Policy School Equilibrium}
    {policyPair : Policy → Policy → Policy}
    {Psub Pfull : Policy} {J2 : School} {groupA groupB : Group}
    {populationShare testCost subFullLeftCost subFullRightCost
      fullSubLeftCost fullSubRightCost : Group → ℝ}
    {capacity2 q1Sub q2Sub : ℝ} {K : Group → ℝ → ℝ}
    (objective1 objective2 : Policy → Policy → ℝ)
    (subFullTestBasedMerit : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (fullSubLowTestBasedMerit : Group → ℝ → ℝ)
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestBasedMerit : Group → ℝ → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
    (hpolicySubFull :
      S.policyPairIsEquilibrium Psub Pfull ↔
        glm20TwoSchoolBinaryPolicyEquilibrium objective1 objective2
          Psub Pfull Psub Pfull)
    (hpolicyFullSub :
      S.policyPairIsEquilibrium Pfull Psub ↔
        glm20TwoSchoolBinaryPolicyEquilibrium objective1 objective2
          Psub Pfull Pfull Psub)
    (hsubFullBridge :
      ∃ subFullCostThreshold : Group → ℝ,
        (∀ g, subFullCostThreshold g ∈
          Set.Ioo (subFullLeftCost g) (subFullRightCost g)) ∧
          (∀ g,
            subFullTestBasedMerit g (subFullCostThreshold g) =
              subFullTestFreeMerit g) ∧
            (∀ g c, c ∈ Set.Icc (subFullLeftCost g) (subFullRightCost g) →
              (subFullTestBasedMerit g c ≤ subFullTestFreeMerit g ↔
                subFullCostThreshold g ≤ c)) ∧
              ((objective1 Pfull Pfull ≤ objective1 Psub Pfull ∧
                  objective2 Psub Psub ≤ objective2 Psub Pfull) ↔
                glm20Theorem3SubFullCondition S policyPair Psub Pfull J2
                  groupA groupB populationShare testCost
                  subFullCostThreshold capacity2 q1Sub K))
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
                    ((objective1 Psub Psub ≤ objective1 Pfull Psub ∧
                        objective2 Pfull Pfull ≤ objective2 Pfull Psub) ↔
                      glm20Theorem3FullSubCondition S policyPair Psub Pfull
                        groupA groupB testCost fullSubLowCostThreshold
                        fullSubHighCostThreshold q1Sub q2Sub K))
    (hcostA : 0 < testCost groupA) (hcostB : 0 < testCost groupB) :
    ∃ subFullCostThreshold fullSubLowCostThreshold
        fullSubHighCostThreshold : Group → ℝ,
      (∀ g, subFullCostThreshold g ∈
        Set.Ioo (subFullLeftCost g) (subFullRightCost g)) ∧
        (∀ g,
          subFullTestBasedMerit g (subFullCostThreshold g) =
            subFullTestFreeMerit g) ∧
          (∀ g c, c ∈ Set.Icc (subFullLeftCost g) (subFullRightCost g) →
            (subFullTestBasedMerit g c ≤ subFullTestFreeMerit g ↔
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
                              K) ∧
                          (S.policyPairIsEquilibrium Pfull Psub ↔
                            glm20Theorem3FullSubCondition S policyPair Psub
                              Pfull groupA groupB testCost
                              fullSubLowCostThreshold
                              fullSubHighCostThreshold q1Sub q2Sub K) ∧
                            glm20Theorem3FullFullCondition S Pfull groupA
                              groupB testCost) := by
  rcases hsubFullBridge with
    ⟨subFullCostThreshold, hsubMem, hsubEq, hsubIff,
      hsubFullObjective⟩
  have hbase :=
    paper_theorem3_source_conditions_of_binary_policy_objective_conditions_of_subFull_objective_and_fullSub_objective_bridge
      (S := S) (policyPair := policyPair) (Psub := Psub)
      (Pfull := Pfull) (J2 := J2) (groupA := groupA)
      (groupB := groupB) (populationShare := populationShare)
      (testCost := testCost) (subFullCostThreshold := subFullCostThreshold)
      (leftCost := fullSubLeftCost) (rightCost := fullSubRightCost)
      (capacity2 := capacity2) (q1Sub := q1Sub) (q2Sub := q2Sub)
      (K := K) objective1 objective2 fullSubLowTestBasedMerit
      fullSubLowTestFreeMerit fullSubHighTestBasedMerit
      fullSubHighTestFreeMerit hpolicySubFull hpolicyFullSub
      hsubFullObjective hfullSubBridge hcostA hcostB
  rcases hbase with
    ⟨fullSubLowCostThreshold, fullSubHighCostThreshold, hlowMem,
      hhighMem, hlowEq, hhighEq, hlowPos, hlowHigh, hconds⟩
  exact
    ⟨subFullCostThreshold, fullSubLowCostThreshold,
      fullSubHighCostThreshold, hsubMem, hsubEq, hsubIff, hlowMem,
      hhighMem, hlowEq, hhighEq, hlowPos, hlowHigh, hconds⟩

/--
Theorem 3 weighted binary-policy adapter for packaged sub-full and full-sub
Proposition 5 bridges.

This specializes
`paper_theorem3_source_conditions_of_binary_policy_objective_conditions_of_subFull_objective_bridge_and_fullSub_objective_bridge`
to the paper's weighted academic-merit binary-policy surface.  The two
policy-equilibrium equivalences are then definitional consequences of that
surface, so callers only need the packaged Proposition 5(i) and Proposition
5(ii) threshold/objective bridges.
-/
theorem
    paper_theorem3_source_conditions_of_weighted_binary_policy_objective_conditions_of_subFull_objective_bridge_and_fullSub_objective_bridge
    {Group Policy School : Type*}
    {S : GLM20StrategicPolicySurface Group Policy School (Policy × Policy)}
    {massTestTaking : Group → Policy → ℝ}
    {admittedAcademicMerit : School → Group → Policy → ℝ}
    {diversity : School → Policy → ℝ}
    {policyPair : Policy → Policy → Policy}
    {Psub Pfull : Policy} {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost subFullLeftCost subFullRightCost
      fullSubLeftCost fullSubRightCost : Group → ℝ}
    {capacity2 q1Sub q2Sub : ℝ} {K : Group → ℝ → ℝ}
    (subFullTestBasedMerit : Group → ℝ → ℝ)
    (subFullTestFreeMerit : Group → ℝ)
    (fullSubLowTestBasedMerit : Group → ℝ → ℝ)
    (fullSubLowTestFreeMerit : Group → ℝ)
    (fullSubHighTestBasedMerit : Group → ℝ → ℝ)
    (fullSubHighTestFreeMerit : Group → ℝ)
    (hS :
      S =
        glm20WeightedAcademicMeritBinaryPolicySurface massTestTaking
          admittedAcademicMerit diversity policyPair Psub Pfull J1 J2
          groupA groupB populationShare)
    (hsubFullBridge :
      ∃ subFullCostThreshold : Group → ℝ,
        (∀ g, subFullCostThreshold g ∈
          Set.Ioo (subFullLeftCost g) (subFullRightCost g)) ∧
          (∀ g,
            subFullTestBasedMerit g (subFullCostThreshold g) =
              subFullTestFreeMerit g) ∧
            (∀ g c, c ∈ Set.Icc (subFullLeftCost g) (subFullRightCost g) →
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
                  subFullCostThreshold capacity2 q1Sub K))
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
                        fullSubHighCostThreshold q1Sub q2Sub K))
    (hcostA : 0 < testCost groupA) (hcostB : 0 < testCost groupB) :
    ∃ subFullCostThreshold fullSubLowCostThreshold
        fullSubHighCostThreshold : Group → ℝ,
      (∀ g, subFullCostThreshold g ∈
        Set.Ioo (subFullLeftCost g) (subFullRightCost g)) ∧
        (∀ g,
          subFullTestBasedMerit g (subFullCostThreshold g) =
            subFullTestFreeMerit g) ∧
          (∀ g c, c ∈ Set.Icc (subFullLeftCost g) (subFullRightCost g) →
            (subFullTestBasedMerit g c ≤ subFullTestFreeMerit g ↔
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
                              K) ∧
                          (S.policyPairIsEquilibrium Pfull Psub ↔
                            glm20Theorem3FullSubCondition S policyPair Psub
                              Pfull groupA groupB testCost
                              fullSubLowCostThreshold
                              fullSubHighCostThreshold q1Sub q2Sub K) ∧
                            glm20Theorem3FullFullCondition S Pfull groupA
                              groupB testCost) := by
  subst S
  exact
    paper_theorem3_source_conditions_of_binary_policy_objective_conditions_of_subFull_objective_bridge_and_fullSub_objective_bridge
      (S :=
        glm20WeightedAcademicMeritBinaryPolicySurface massTestTaking
          admittedAcademicMerit diversity policyPair Psub Pfull J1 J2
          groupA groupB populationShare)
      (policyPair := policyPair) (Psub := Psub) (Pfull := Pfull)
      (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub) (K := K)
      (glm20TwoGroupWeightedAcademicMeritObjective
        (glm20WeightedAcademicMeritBinaryPolicySurface massTestTaking
          admittedAcademicMerit diversity policyPair Psub Pfull J1 J2
          groupA groupB populationShare)
        policyPair J1 groupA groupB populationShare)
      (glm20TwoGroupWeightedAcademicMeritObjective
        (glm20WeightedAcademicMeritBinaryPolicySurface massTestTaking
          admittedAcademicMerit diversity policyPair Psub Pfull J1 J2
          groupA groupB populationShare)
        policyPair J2 groupA groupB populationShare)
      subFullTestBasedMerit subFullTestFreeMerit
      fullSubLowTestBasedMerit fullSubLowTestFreeMerit
      fullSubHighTestBasedMerit fullSubHighTestFreeMerit
      (by
        exact glm20WeightedAcademicMeritBinaryPolicySurface_policyPairIsEquilibrium_iff)
      (by
        exact glm20WeightedAcademicMeritBinaryPolicySurface_policyPairIsEquilibrium_iff)
      hsubFullBridge hfullSubBridge hcostA hcostB

/--
Theorem 3 raw-survivor endpoint with the full-sub high-at-low-root premise
derived from direct ordered-merit assumptions.

This is a paper-surface adapter around the strongest current Theorem 3 route:
the survivor mass and survivor-merit premises remain raw source-row
inequalities, while the proof-artifact high-at-low-root input is replaced by
two assumptions that are easier to check against the Gaussian game.
-/
abbrev
    paper_theorem3_raw_survivor_conditions_of_ordered_fullSub_merits
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
      (hfullSubFreeOrder :
        ∀ g, fullSubHighTestFreeMerit g < fullSubLowTestFreeMerit g)
      (hfullSubBasedOrder :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g c) ≤
            fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g c))
      hJ2MassB hJ2MeritGtB hJ2MassA hJ2MeritGtA =>
    paper_theorem3_standardGaussian_source_conditions_of_proposition5_policy_state_table_source_family_fixed_pool_merits_j2_zero_fallback_and_cutoff_fill_of_equation50_and_standardGaussian_twoFull_subFull_fullSub_interval_of_raw_survivor_conditions
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
      hcapacity2 hfillFullFull2 hfullSubLowAtLeft hfullSubLowAtRight
      hfullSubHighAtLeft hfullSubHighAtRight
      (fun g c hc hroot =>
        have hfreeAtRoot :
            fullSubHighTestFreeMerit g <
              fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g c) := by
          rw [hroot]
          exact hfullSubFreeOrder g
        lt_of_lt_of_le hfreeAtRoot (hfullSubBasedOrder g c hc))
      hJ2MassB hJ2MeritGtB hJ2MassA hJ2MeritGtA

/--
Theorem 3 raw-survivor endpoint with the full-sub ordered-merit assumptions
derived from Gaussian upper-tail-mean formulas.

This is the Gaussian source-facing variant of
`paper_theorem3_raw_survivor_conditions_of_ordered_fullSub_merits`: after
equation (50) and equation (46) select the relevant cutoff functions, the two
full-sub ordering assumptions are proved from tail-mean formula identities plus
scale and threshold comparisons.
-/
abbrev
    paper_theorem3_raw_survivor_conditions_of_gaussian_fullSub_merits
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
    (C : GaussianHazardCertificate)
    (fullSubLowFreeLaw fullSubHighFreeLaw : Group → GaussianScaleLaw)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold : Group → ℝ)
    (fullSubLowBasedLaw fullSubHighBasedLaw :
      Group → ℝ → GaussianScaleLaw)
    (fullSubLowBasedThreshold fullSubHighBasedThreshold :
      Group → ℝ → ℝ)
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
      (hfullSubLowFreeFormula :
        ∀ g,
          fullSubLowTestFreeMerit g =
            C.normalUpperTailMean (fullSubLowFreeLaw g)
              (fullSubLowFreeThreshold g))
      (hfullSubHighFreeFormula :
        ∀ g,
          fullSubHighTestFreeMerit g =
            C.normalUpperTailMean (fullSubHighFreeLaw g)
              (fullSubHighFreeThreshold g))
      (hfullSubFreeMean :
        ∀ g, (fullSubHighFreeLaw g).mean = (fullSubLowFreeLaw g).mean)
      (hfullSubFreeScale :
        ∀ g, (fullSubHighFreeLaw g).scale < (fullSubLowFreeLaw g).scale)
      (hfullSubFreeThresholdMean :
        ∀ g, (fullSubHighFreeLaw g).mean < fullSubHighFreeThreshold g)
      (hfullSubFreeThreshold :
        ∀ g, fullSubHighFreeThreshold g ≤ fullSubLowFreeThreshold g)
      (hfullSubLowBasedFormula :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g c) =
            C.normalUpperTailMean (fullSubLowBasedLaw g c)
              (fullSubLowBasedThreshold g c))
      (hfullSubHighBasedFormula :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g c) =
            C.normalUpperTailMean (fullSubHighBasedLaw g c)
              (fullSubHighBasedThreshold g c))
      (hfullSubBasedMean :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          (fullSubLowBasedLaw g c).mean =
            (fullSubHighBasedLaw g c).mean)
      (hfullSubBasedScale :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          (fullSubLowBasedLaw g c).scale ≤
            (fullSubHighBasedLaw g c).scale)
      (hfullSubBasedThresholdMean :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          (fullSubLowBasedLaw g c).mean < fullSubLowBasedThreshold g c)
      (hfullSubBasedThreshold :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubLowBasedThreshold g c ≤ fullSubHighBasedThreshold g c)
      hJ2MassB hJ2MeritGtB hJ2MassA hJ2MeritGtA =>
    let horders :=
      paper_proposition5_fullSub_ordered_merits_of_gaussian_tail_mean_formulas
        (C := C) (leftCost := fullSubLeftCost)
        (rightCost := fullSubRightCost)
        (fun g c => fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g c))
        fullSubLowTestFreeMerit
        (fun g c =>
          fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g c))
        fullSubHighTestFreeMerit fullSubLowFreeLaw fullSubHighFreeLaw
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        fullSubLowBasedLaw fullSubHighBasedLaw fullSubLowBasedThreshold
        fullSubHighBasedThreshold hfullSubLowFreeFormula
        hfullSubHighFreeFormula hfullSubFreeMean hfullSubFreeScale
        hfullSubFreeThresholdMean hfullSubFreeThreshold
        (by
          intro g c hc
          simpa using hfullSubLowBasedFormula g c hc)
        (by
          intro g c hc
          simpa using hfullSubHighBasedFormula g c hc)
        hfullSubBasedMean hfullSubBasedScale
        hfullSubBasedThresholdMean hfullSubBasedThreshold
    paper_theorem3_raw_survivor_conditions_of_ordered_fullSub_merits
      subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
      fullSubMeritFallback fullFullMeritFallback diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (capacity1 := capacity1) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hJ1_ne_J2 hJ1PriorMean hJ1PriorVar
      hJ1Precision hJ1ThresholdMean hJ1Threshold hJ2PriorMean
      hJ2PriorVar hJ2Precision hJ2ThresholdMean hJ2Threshold
      (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
      (subFullV2 := subFullV2) (fullSubLowQ1Full := fullSubLowQ1Full)
      (fullSubLowQ2Full := fullSubLowQ2Full)
      (fullSubLowScale := fullSubLowScale)
      (fullSubLowV1 := fullSubLowV1) (fullSubLowV2 := fullSubLowV2)
      (fullSubHighQ1Full := fullSubHighQ1Full)
      (fullSubHighQ2Full := fullSubHighQ2Full)
      (fullSubHighScale := fullSubHighScale)
      (fullSubHighV1 := fullSubHighV1)
      (fullSubHighV2 := fullSubHighV2) subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowMeritOfCutoff
      fullSubHighMeritOfCutoff fullSubLowTestFreeMerit
      fullSubHighTestFreeMerit hsubFullLeftRight hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullScale
      hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight
      hfullSubLeftRight hfullSubLeftPos hfullSubCostMem hfullSubLowScale
      hfullSubLowV2Pos hfullSubLowV2LtV1 hfullSubLowRightLtV1
      hfullSubLowMeritCont hfullSubLowMeritAnti hfullSubHighScale
      hfullSubHighV2Pos hfullSubHighV2LtV1 hfullSubHighRightLtV1
      hfullSubHighMeritCont hfullSubHighMeritAnti hshareA hshareB
      hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
      hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight horders.1 horders.2
      hJ2MassB hJ2MeritGtB hJ2MassA hJ2MeritGtA

/--
Theorem 3 raw-survivor endpoint with the full-sub Gaussian merit rows
instantiated as posterior-mean source-family laws.

This is the posterior-family specialization of
`paper_theorem3_raw_survivor_conditions_of_gaussian_fullSub_merits`: callers
provide source-family prior/precision comparisons instead of manually building
the full-sub `GaussianScaleLaw` rows.
-/
abbrev
    paper_theorem3_raw_survivor_conditions_of_posterior_mean_fullSub_merits
    {Group School FeatureDrop FeatureKeep LowFreeFeature HighFreeFeature
      LowBasedFeature HighBasedFeature : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
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
    (C : GaussianHazardCertificate)
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
  let base :=
    paper_theorem3_raw_survivor_conditions_of_gaussian_fullSub_merits
      subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
      fullSubMeritFallback fullFullMeritFallback diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (capacity1 := capacity1) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hJ1_ne_J2 hJ1PriorMean hJ1PriorVar
      hJ1Precision hJ1ThresholdMean hJ1Threshold hJ2PriorMean
      hJ2PriorVar hJ2Precision hJ2ThresholdMean hJ2Threshold
      (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
      (subFullV2 := subFullV2) (fullSubLowQ1Full := fullSubLowQ1Full)
      (fullSubLowQ2Full := fullSubLowQ2Full)
      (fullSubLowScale := fullSubLowScale)
      (fullSubLowV1 := fullSubLowV1) (fullSubLowV2 := fullSubLowV2)
      (fullSubHighQ1Full := fullSubHighQ1Full)
      (fullSubHighQ2Full := fullSubHighQ2Full)
      (fullSubHighScale := fullSubHighScale)
      (fullSubHighV1 := fullSubHighV1)
      (fullSubHighV2 := fullSubHighV2) subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowMeritOfCutoff
      fullSubHighMeritOfCutoff fullSubLowTestFreeMerit
      fullSubHighTestFreeMerit C
      (fun g => (fullSubLowFreeFamily g).posteriorMeanScaleLaw)
      (fun g => (fullSubHighFreeFamily g).posteriorMeanScaleLaw)
      fullSubLowFreeThreshold fullSubHighFreeThreshold
      (fun g c => (fullSubLowBasedFamily g c).posteriorMeanScaleLaw)
      (fun g c => (fullSubHighBasedFamily g c).posteriorMeanScaleLaw)
      fullSubLowBasedThreshold fullSubHighBasedThreshold
      hsubFullLeftRight hsubFullLeftPos hsubFullRightLtV2 hsubFullCostMem
      hsubFullScale hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft
      hsubFullAtRight hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
      hfullSubLowScale hfullSubLowV2Pos hfullSubLowV2LtV1
      hfullSubLowRightLtV1 hfullSubLowMeritCont hfullSubLowMeritAnti
      hfullSubHighScale hfullSubHighV2Pos hfullSubHighV2LtV1
      hfullSubHighRightLtV1 hfullSubHighMeritCont
      hfullSubHighMeritAnti hshareA hshareB hcapacity1 hfillFullFull1
      hcapacity2 hfillFullFull2
  fun hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight hfullSubLowFreeFormula hfullSubHighFreeFormula
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
      hfullSubLowBasedFormula hfullSubHighBasedFormula
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
      hJ2MassB
      hJ2MeritGtB hJ2MassA hJ2MeritGtA =>
    base hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight hfullSubLowFreeFormula hfullSubHighFreeFormula
      (by
        intro g
        simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
          using hfullSubFreePriorMean g)
      (by
        intro g
        exact
          GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
            (hfullSubFreePriorVar g) (hfullSubFreePrecision g))
      (by
        intro g
        simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
          using hfullSubFreeThresholdMean g)
      hfullSubFreeThreshold hfullSubLowBasedFormula
      hfullSubHighBasedFormula
      (by
        intro g c hc
        simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
          using hfullSubBasedPriorMean g c hc)
      (by
        intro g c hc
        exact le_of_lt
          (GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
            (hfullSubBasedPriorVar g c hc) (hfullSubBasedPrecision g c hc)))
      (by
        intro g c hc
        simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
          using hfullSubBasedThresholdMean g c hc)
      hfullSubBasedThreshold hJ2MassB hJ2MeritGtB hJ2MassA hJ2MeritGtA

/--
Theorem 3 support: raw condition-(11)--(12) survivor components imply the
named school-`J2` keep-test predicate on the concrete policy-state table.

This is the forward direction of the existing iff, exposed as a paper-surface
adapter so callers can feed source-row mass and strict weighted-merit facts
directly into the strongest `J2` keep-test Theorem 3 route.
-/
theorem
    paper_theorem3_policyStateTableWeightedAcademicMeritSurface_subFull_otherGroupKeepsTest_of_components
    {Group School : Type*}
    (api : StandardGaussianCDFAPI)
    (subEstimateLaw : Group → GaussianScaleLaw)
    (subSubMass subFullMass : Group → ℝ)
    (fullFullCutoff fullSubCutoff : Group → ℝ)
    (subSubMerit subFullMerit fullSubMerit fullFullMerit :
      School → Group → ℝ)
    (diversity : School → GLM20StrategicPolicyState → ℝ)
    (J1 J2 : School) (groupA groupB survivingGroup : Group)
    (populationShare : Group → ℝ) {capacity2 : ℝ}
    (hcomponents :
      subFullMass survivingGroup ≥ capacity2 ∧
        populationShare survivingGroup * subFullMerit J2 survivingGroup >
          populationShare groupA * subSubMerit J2 groupA +
            populationShare groupB * subSubMerit J2 groupB) :
    glm20Theorem3SubFullOtherGroupKeepsTest
        (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface api
          subEstimateLaw subSubMass subFullMass fullFullCutoff fullSubCutoff
          subSubMerit subFullMerit fullSubMerit fullFullMerit diversity J1
          J2 groupA groupB populationShare)
        glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
        GLM20StrategicPolicyState.singleFull J2 groupA groupB
        populationShare capacity2 survivingGroup := by
  exact
    (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface_subFull_otherGroupKeepsTest_iff_components
      api subEstimateLaw subSubMass subFullMass fullFullCutoff
      fullSubCutoff subSubMerit subFullMerit fullSubMerit fullFullMerit
      diversity J1 J2 groupA groupB survivingGroup populationShare
      (capacity2 := capacity2)).mpr hcomponents

/--
Theorem 3 endpoint with school `J2` survivor requirements expressed as the
named condition-(11)--(12) predicate.

This is the same standard-Gaussian source-table route as
`paper_theorem3_raw_survivor_conditions_of_ordered_fullSub_merits`, but the two
survivor mass/merit pairs are discharged from the semantic statement that `J2`
keeps the test for the surviving group under `(P_sub,P_full)`.
-/
abbrev
    paper_theorem3_ordered_fullSub_merits_of_j2_keeps_test
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
  let tableSurface :=
    glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface
      standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
      fullFullCutoff fullSubCutoff subSubMerit subFullMeritBase
      fullSubMeritFallback fullFullMeritFallback diversity J1 J2 groupA
      groupB populationShare
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
      (hfullSubFreeOrder :
        ∀ g, fullSubHighTestFreeMerit g < fullSubLowTestFreeMerit g)
      (hfullSubBasedOrder :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubLowMeritOfCutoff g
              (fullSubLowCutoffOfCost g c) ≤
            fullSubHighMeritOfCutoff g
              (fullSubHighCutoffOfCost g c))
      (hJ2KeepsB :
        glm20Theorem3SubFullOtherGroupKeepsTest tableSurface
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupB)
      (hJ2KeepsA :
        glm20Theorem3SubFullOtherGroupKeepsTest tableSurface
          glm20StrategicPolicyStatePair GLM20StrategicPolicyState.singleSub
          GLM20StrategicPolicyState.singleFull J2 groupA groupB
          populationShare capacity2 groupA) =>
    let hB :=
      (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface_subFull_otherGroupKeepsTest_iff_components
        standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
        fullFullCutoff fullSubCutoff subSubMerit subFullMeritBase
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2 groupA
        groupB groupB populationShare (capacity2 := capacity2)).mp hJ2KeepsB
    let hA :=
      (glm20Theorem3PolicyStateTableWeightedAcademicMeritSurface_subFull_otherGroupKeepsTest_iff_components
        standardGaussianCDFAPI subEstimateLaw subSubMass subFullMass
        fullFullCutoff fullSubCutoff subSubMerit subFullMeritBase
        fullSubMeritFallback fullFullMeritFallback diversity J1 J2 groupA
        groupB groupA populationShare (capacity2 := capacity2)).mp hJ2KeepsA
    paper_theorem3_raw_survivor_conditions_of_ordered_fullSub_merits
      subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
      fullSubMeritFallback fullFullMeritFallback diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (capacity1 := capacity1) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hJ1_ne_J2 hJ1PriorMean hJ1PriorVar
      hJ1Precision hJ1ThresholdMean hJ1Threshold hJ2PriorMean
      hJ2PriorVar hJ2Precision hJ2ThresholdMean hJ2Threshold
      (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
      (subFullV2 := subFullV2) (fullSubLowQ1Full := fullSubLowQ1Full)
      (fullSubLowQ2Full := fullSubLowQ2Full)
      (fullSubLowScale := fullSubLowScale)
      (fullSubLowV1 := fullSubLowV1) (fullSubLowV2 := fullSubLowV2)
      (fullSubHighQ1Full := fullSubHighQ1Full)
      (fullSubHighQ2Full := fullSubHighQ2Full)
      (fullSubHighScale := fullSubHighScale)
      (fullSubHighV1 := fullSubHighV1)
      (fullSubHighV2 := fullSubHighV2) subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowMeritOfCutoff
      fullSubHighMeritOfCutoff fullSubLowTestFreeMerit
      fullSubHighTestFreeMerit hsubFullLeftRight hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullScale
      hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight
      hfullSubLeftRight hfullSubLeftPos hfullSubCostMem hfullSubLowScale
      hfullSubLowV2Pos hfullSubLowV2LtV1 hfullSubLowRightLtV1
      hfullSubLowMeritCont hfullSubLowMeritAnti hfullSubHighScale
      hfullSubHighV2Pos hfullSubHighV2LtV1 hfullSubHighRightLtV1
      hfullSubHighMeritCont hfullSubHighMeritAnti hshareA hshareB
      hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
      hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight hfullSubFreeOrder hfullSubBasedOrder
      hB.1 hB.2 hA.1 hA.2

/--
Theorem 3 endpoint with school `J2` survivor requirements expressed as named
keep-test predicates, and with the full-sub ordered-merit assumptions derived
from Gaussian upper-tail-mean formulas.
-/
abbrev
    paper_theorem3_gaussian_fullSub_merits_of_j2_keeps_test
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
    (C : GaussianHazardCertificate)
    (fullSubLowFreeLaw fullSubHighFreeLaw : Group → GaussianScaleLaw)
    (fullSubLowFreeThreshold fullSubHighFreeThreshold : Group → ℝ)
    (fullSubLowBasedLaw fullSubHighBasedLaw :
      Group → ℝ → GaussianScaleLaw)
    (fullSubLowBasedThreshold fullSubHighBasedThreshold :
      Group → ℝ → ℝ)
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
      (hfullSubLowFreeFormula :
        ∀ g,
          fullSubLowTestFreeMerit g =
            C.normalUpperTailMean (fullSubLowFreeLaw g)
              (fullSubLowFreeThreshold g))
      (hfullSubHighFreeFormula :
        ∀ g,
          fullSubHighTestFreeMerit g =
            C.normalUpperTailMean (fullSubHighFreeLaw g)
              (fullSubHighFreeThreshold g))
      (hfullSubFreeMean :
        ∀ g, (fullSubHighFreeLaw g).mean = (fullSubLowFreeLaw g).mean)
      (hfullSubFreeScale :
        ∀ g, (fullSubHighFreeLaw g).scale < (fullSubLowFreeLaw g).scale)
      (hfullSubFreeThresholdMean :
        ∀ g, (fullSubHighFreeLaw g).mean < fullSubHighFreeThreshold g)
      (hfullSubFreeThreshold :
        ∀ g, fullSubHighFreeThreshold g ≤ fullSubLowFreeThreshold g)
      (hfullSubLowBasedFormula :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g c) =
            C.normalUpperTailMean (fullSubLowBasedLaw g c)
              (fullSubLowBasedThreshold g c))
      (hfullSubHighBasedFormula :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g c) =
            C.normalUpperTailMean (fullSubHighBasedLaw g c)
              (fullSubHighBasedThreshold g c))
      (hfullSubBasedMean :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          (fullSubLowBasedLaw g c).mean =
            (fullSubHighBasedLaw g c).mean)
      (hfullSubBasedScale :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          (fullSubLowBasedLaw g c).scale ≤
            (fullSubHighBasedLaw g c).scale)
      (hfullSubBasedThresholdMean :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          (fullSubLowBasedLaw g c).mean < fullSubLowBasedThreshold g c)
      (hfullSubBasedThreshold :
        ∀ g c, c ∈ Set.Ioo (fullSubLeftCost g) (fullSubRightCost g) →
          fullSubLowBasedThreshold g c ≤ fullSubHighBasedThreshold g c) =>
    let horders :=
      paper_proposition5_fullSub_ordered_merits_of_gaussian_tail_mean_formulas
        (C := C) (leftCost := fullSubLeftCost)
        (rightCost := fullSubRightCost)
        (fun g c => fullSubLowMeritOfCutoff g (fullSubLowCutoffOfCost g c))
        fullSubLowTestFreeMerit
        (fun g c =>
          fullSubHighMeritOfCutoff g (fullSubHighCutoffOfCost g c))
        fullSubHighTestFreeMerit fullSubLowFreeLaw fullSubHighFreeLaw
        fullSubLowFreeThreshold fullSubHighFreeThreshold
        fullSubLowBasedLaw fullSubHighBasedLaw fullSubLowBasedThreshold
        fullSubHighBasedThreshold hfullSubLowFreeFormula
        hfullSubHighFreeFormula hfullSubFreeMean hfullSubFreeScale
        hfullSubFreeThresholdMean hfullSubFreeThreshold
        (by
          intro g c hc
          simpa using hfullSubLowBasedFormula g c hc)
        (by
          intro g c hc
          simpa using hfullSubHighBasedFormula g c hc)
        hfullSubBasedMean hfullSubBasedScale
        hfullSubBasedThresholdMean hfullSubBasedThreshold
    paper_theorem3_ordered_fullSub_merits_of_j2_keeps_test
      subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
      fullSubMeritFallback fullFullMeritFallback diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (capacity1 := capacity1) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hJ1_ne_J2 hJ1PriorMean hJ1PriorVar
      hJ1Precision hJ1ThresholdMean hJ1Threshold hJ2PriorMean
      hJ2PriorVar hJ2Precision hJ2ThresholdMean hJ2Threshold
      (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
      (subFullV2 := subFullV2) (fullSubLowQ1Full := fullSubLowQ1Full)
      (fullSubLowQ2Full := fullSubLowQ2Full)
      (fullSubLowScale := fullSubLowScale)
      (fullSubLowV1 := fullSubLowV1) (fullSubLowV2 := fullSubLowV2)
      (fullSubHighQ1Full := fullSubHighQ1Full)
      (fullSubHighQ2Full := fullSubHighQ2Full)
      (fullSubHighScale := fullSubHighScale)
      (fullSubHighV1 := fullSubHighV1)
      (fullSubHighV2 := fullSubHighV2) subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowMeritOfCutoff
      fullSubHighMeritOfCutoff fullSubLowTestFreeMerit
      fullSubHighTestFreeMerit hsubFullLeftRight hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullScale
      hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight
      hfullSubLeftRight hfullSubLeftPos hfullSubCostMem hfullSubLowScale
      hfullSubLowV2Pos hfullSubLowV2LtV1 hfullSubLowRightLtV1
      hfullSubLowMeritCont hfullSubLowMeritAnti hfullSubHighScale
      hfullSubHighV2Pos hfullSubHighV2LtV1 hfullSubHighRightLtV1
      hfullSubHighMeritCont hfullSubHighMeritAnti hshareA hshareB
      hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
      hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight horders.1 horders.2

/--
Theorem 3 endpoint with named school-`J2` keep-test predicates and the
full-sub Gaussian merit rows instantiated as posterior-mean source-family
laws.

This is the posterior-family specialization of
`paper_theorem3_gaussian_fullSub_merits_of_j2_keeps_test`, removing the
abstract full-sub `GaussianScaleLaw` rows from the strongest current
school-`J2` keep-test route.
-/
abbrev
    paper_theorem3_posterior_mean_fullSub_merits_of_j2_keeps_test
    {Group School FeatureDrop FeatureKeep LowFreeFeature HighFreeFeature
      LowBasedFeature HighBasedFeature : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
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
    (C : GaussianHazardCertificate)
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
  let base :=
    paper_theorem3_gaussian_fullSub_merits_of_j2_keeps_test
      subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
      fullSubMeritFallback fullFullMeritFallback diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (capacity1 := capacity1) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hJ1_ne_J2 hJ1PriorMean hJ1PriorVar
      hJ1Precision hJ1ThresholdMean hJ1Threshold hJ2PriorMean
      hJ2PriorVar hJ2Precision hJ2ThresholdMean hJ2Threshold
      (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
      (subFullV2 := subFullV2) (fullSubLowQ1Full := fullSubLowQ1Full)
      (fullSubLowQ2Full := fullSubLowQ2Full)
      (fullSubLowScale := fullSubLowScale)
      (fullSubLowV1 := fullSubLowV1) (fullSubLowV2 := fullSubLowV2)
      (fullSubHighQ1Full := fullSubHighQ1Full)
      (fullSubHighQ2Full := fullSubHighQ2Full)
      (fullSubHighScale := fullSubHighScale)
      (fullSubHighV1 := fullSubHighV1)
      (fullSubHighV2 := fullSubHighV2) subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowMeritOfCutoff
      fullSubHighMeritOfCutoff fullSubLowTestFreeMerit
      fullSubHighTestFreeMerit C
      (fun g => (fullSubLowFreeFamily g).posteriorMeanScaleLaw)
      (fun g => (fullSubHighFreeFamily g).posteriorMeanScaleLaw)
      fullSubLowFreeThreshold fullSubHighFreeThreshold
      (fun g c => (fullSubLowBasedFamily g c).posteriorMeanScaleLaw)
      (fun g c => (fullSubHighBasedFamily g c).posteriorMeanScaleLaw)
      fullSubLowBasedThreshold fullSubHighBasedThreshold
      hsubFullLeftRight hsubFullLeftPos hsubFullRightLtV2 hsubFullCostMem
      hsubFullScale hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft
      hsubFullAtRight hfullSubLeftRight hfullSubLeftPos hfullSubCostMem
      hfullSubLowScale hfullSubLowV2Pos hfullSubLowV2LtV1
      hfullSubLowRightLtV1 hfullSubLowMeritCont hfullSubLowMeritAnti
      hfullSubHighScale hfullSubHighV2Pos hfullSubHighV2LtV1
      hfullSubHighRightLtV1 hfullSubHighMeritCont
      hfullSubHighMeritAnti hshareA hshareB hcapacity1 hfillFullFull1
      hcapacity2 hfillFullFull2
  fun hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight hfullSubLowFreeFormula hfullSubHighFreeFormula
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
      hfullSubLowBasedFormula hfullSubHighBasedFormula
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
          fullSubLowBasedThreshold g c ≤ fullSubHighBasedThreshold g c) =>
    base hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight hfullSubLowFreeFormula hfullSubHighFreeFormula
      (by
        intro g
        simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
          using hfullSubFreePriorMean g)
      (by
        intro g
        exact
          GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
            (hfullSubFreePriorVar g) (hfullSubFreePrecision g))
      (by
        intro g
        simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
          using hfullSubFreeThresholdMean g)
      hfullSubFreeThreshold hfullSubLowBasedFormula
      hfullSubHighBasedFormula
      (by
        intro g c hc
        simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
          using hfullSubBasedPriorMean g c hc)
      (by
        intro g c hc
        exact le_of_lt
          (GaussianOffsetSignalFamily.posteriorMeanScaleLaw_scale_lt_of_priorVar_eq_signalPrecisionSum_lt
            (hfullSubBasedPriorVar g c hc) (hfullSubBasedPrecision g c hc)))
      (by
        intro g c hc
        simpa [GaussianOffsetSignalFamily.posteriorMeanScaleLaw]
          using hfullSubBasedThresholdMean g c hc)
      hfullSubBasedThreshold

/--
Theorem 3 posterior-family endpoint with the full-sub test-free merit rows
generated directly from posterior-mean source families.

This is the source-free version of
`paper_theorem3_posterior_mean_fullSub_merits_of_j2_keeps_test`: the low and
high test-free full-sub rows are not caller premises, but the posterior
Gaussian upper-tail means generated by the corresponding source families.  The
cost-indexed test-based full-sub row formulas remain visible because they
depend on the internally constructed cost-to-cutoff maps.
-/
abbrev
    paper_theorem3_posterior_mean_fullSub_source_free_merits_of_j2_keeps_test
    {Group School FeatureDrop FeatureKeep LowFreeFeature HighFreeFeature
      LowBasedFeature HighBasedFeature : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
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
    (C : GaussianHazardCertificate)
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
  let fullSubLowTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean (fullSubLowFreeFamily g).posteriorMeanScaleLaw
      (fullSubLowFreeThreshold g)
  let fullSubHighTestFreeMerit : Group → ℝ := fun g =>
    C.normalUpperTailMean (fullSubHighFreeFamily g).posteriorMeanScaleLaw
      (fullSubHighFreeThreshold g)
  let base :=
    paper_theorem3_posterior_mean_fullSub_merits_of_j2_keeps_test
      subEstimateLaw subSubMass subFullMass subSubMerit subFullMeritBase
      fullSubMeritFallback fullFullMeritFallback diversity
      (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
      (populationShare := populationShare) (testCost := testCost)
      (subFullLeftCost := subFullLeftCost)
      (subFullRightCost := subFullRightCost)
      (fullSubLeftCost := fullSubLeftCost)
      (fullSubRightCost := fullSubRightCost)
      (capacity1 := capacity1) (capacity2 := capacity2)
      (q1Sub := q1Sub) (q2Sub := q2Sub)
      (fullFullCutoff := fullFullCutoff)
      (fullSubCutoff := fullSubCutoff) J1DropFamily J2DropFamily
      J1KeepFamily J2KeepFamily J1DropThreshold J1KeepThreshold
      J2DropThreshold J2KeepThreshold hJ1_ne_J2 hJ1PriorMean hJ1PriorVar
      hJ1Precision hJ1ThresholdMean hJ1Threshold hJ2PriorMean
      hJ2PriorVar hJ2Precision hJ2ThresholdMean hJ2Threshold
      (subFullQ2Full := subFullQ2Full) (subFullScale := subFullScale)
      (subFullV2 := subFullV2) (fullSubLowQ1Full := fullSubLowQ1Full)
      (fullSubLowQ2Full := fullSubLowQ2Full)
      (fullSubLowScale := fullSubLowScale)
      (fullSubLowV1 := fullSubLowV1) (fullSubLowV2 := fullSubLowV2)
      (fullSubHighQ1Full := fullSubHighQ1Full)
      (fullSubHighQ2Full := fullSubHighQ2Full)
      (fullSubHighScale := fullSubHighScale)
      (fullSubHighV1 := fullSubHighV1)
      (fullSubHighV2 := fullSubHighV2) subFullMeritOfCutoff
      subFullTestFreeMerit fullSubLowMeritOfCutoff
      fullSubHighMeritOfCutoff fullSubLowTestFreeMerit
      fullSubHighTestFreeMerit C fullSubLowFreeFamily
      fullSubHighFreeFamily fullSubLowFreeThreshold
      fullSubHighFreeThreshold fullSubLowBasedFamily
      fullSubHighBasedFamily fullSubLowBasedThreshold
      fullSubHighBasedThreshold hsubFullLeftRight hsubFullLeftPos
      hsubFullRightLtV2 hsubFullCostMem hsubFullScale
      hsubFullMeritCont hsubFullMeritAnti hsubFullAtLeft hsubFullAtRight
      hfullSubLeftRight hfullSubLeftPos hfullSubCostMem hfullSubLowScale
      hfullSubLowV2Pos hfullSubLowV2LtV1 hfullSubLowRightLtV1
      hfullSubLowMeritCont hfullSubLowMeritAnti hfullSubHighScale
      hfullSubHighV2Pos hfullSubHighV2LtV1 hfullSubHighRightLtV1
      hfullSubHighMeritCont hfullSubHighMeritAnti hshareA hshareB
      hcapacity1 hfillFullFull1 hcapacity2 hfillFullFull2
  fun hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight
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
      hfullSubLowBasedFormula hfullSubHighBasedFormula
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
          fullSubLowBasedThreshold g c ≤ fullSubHighBasedThreshold g c) =>
    base hfullSubLowAtLeft hfullSubLowAtRight hfullSubHighAtLeft
      hfullSubHighAtRight (by intro g; rfl) (by intro g; rfl)
      hfullSubFreePriorMean hfullSubFreePriorVar hfullSubFreePrecision
      hfullSubFreeThresholdMean hfullSubFreeThreshold
      hfullSubLowBasedFormula hfullSubHighBasedFormula
      hfullSubBasedPriorMean hfullSubBasedPriorVar
      hfullSubBasedPrecision hfullSubBasedThresholdMean
      hfullSubBasedThreshold

/--
Standard-Gaussian specialization of the base component-table keep-test
Theorem 3 route.

This keeps the same component-table keep-test assumptions as
`paper_theorem3_posterior_mean_fullSub_source_free_merits_of_j2_keeps_test`,
but fixes the Gaussian hazard certificate internally.
-/
abbrev
    paper_theorem3_standardGaussian_posterior_mean_fullSub_source_free_merits_of_j2_keeps_test
    {Group School FeatureDrop FeatureKeep LowFreeFeature HighFreeFeature
      LowBasedFeature HighBasedFeature : Type*}
    [DecidableEq School]
    [Fintype FeatureDrop] [Nonempty FeatureDrop]
    [Fintype FeatureKeep] [Nonempty FeatureKeep]
    [Fintype LowFreeFeature] [Nonempty LowFreeFeature]
    [Fintype HighFreeFeature] [Nonempty HighFreeFeature]
    [Fintype LowBasedFeature] [Nonempty LowBasedFeature]
    [Fintype HighBasedFeature] [Nonempty HighBasedFeature]
    {J1 J2 : School} {groupA groupB : Group}
    {populationShare testCost subFullLeftCost subFullRightCost
      fullSubLeftCost fullSubRightCost : Group → ℝ}
    {capacity1 capacity2 q1Sub q2Sub : ℝ}
    {fullFullCutoff fullSubCutoff : Group → ℝ}
    {subFullQ2Full subFullScale subFullV2 : Group → ℝ}
    {fullSubLowQ1Full fullSubLowQ2Full fullSubLowScale fullSubLowV1
      fullSubLowV2 : Group → ℝ}
    {fullSubHighQ1Full fullSubHighQ2Full fullSubHighScale fullSubHighV1
      fullSubHighV2 : Group → ℝ} :=
  paper_theorem3_posterior_mean_fullSub_source_free_merits_of_j2_keeps_test
    (Group := Group) (School := School) (FeatureDrop := FeatureDrop)
    (FeatureKeep := FeatureKeep) (LowFreeFeature := LowFreeFeature)
    (HighFreeFeature := HighFreeFeature)
    (LowBasedFeature := LowBasedFeature)
    (HighBasedFeature := HighBasedFeature)
    (J1 := J1) (J2 := J2) (groupA := groupA) (groupB := groupB)
    (populationShare := populationShare) (testCost := testCost)
    (subFullLeftCost := subFullLeftCost)
    (subFullRightCost := subFullRightCost)
    (fullSubLeftCost := fullSubLeftCost)
    (fullSubRightCost := fullSubRightCost)
    (capacity1 := capacity1) (capacity2 := capacity2)
    (q1Sub := q1Sub) (q2Sub := q2Sub)
    (fullFullCutoff := fullFullCutoff)
    (fullSubCutoff := fullSubCutoff)
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
    (C := standardGaussianHazardInverseCertificate.toGaussianHazardCertificate)

end

end GLM20DroppingStandardizedTesting
