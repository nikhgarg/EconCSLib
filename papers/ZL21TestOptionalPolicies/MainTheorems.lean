import EconCSLib.Foundations.Probability.Admissions

open EconCSLib

/-!
# Paper-Facing Theorems: Test-optional Policies and Informational Gaps

This folder is scaffolded for the future formalization of
*Test-optional Policies: Overcoming Strategic Behavior and Informational Gaps*.
-/

namespace ZL21TestOptionalPolicies

noncomputable section

/-!
Core abstraction for a test-optional paper-facing model: students have a latent
quality and two signal channels (base profile and optional test outcome).  Both
use the same prior to enable direct comparison.
-/
structure ZL21Model (Θ ΩBase ΩTest : Type*) [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest] where
  (prior : PMF Θ)
  (baseKernel : Θ → PMF ΩBase)
  (testKernel : Θ → PMF ΩTest)
  (quality : Θ → ℝ)

def zl21BaseModel {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) : AdmissionsModel Θ ΩBase :=
  {prior := m.prior, signalKernel := m.baseKernel}

def zl21TestModel {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) : AdmissionsModel Θ ΩTest :=
  {prior := m.prior, signalKernel := m.testKernel}

def zl21BaseMass {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] : ℝ :=
  admissionsSelectedWelfareMass (zl21BaseModel m) p m.quality

def zl21BaseConditionalMass {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] : ℝ :=
  admissionsSelectedWelfareConditionalExp (zl21BaseModel m) p m.quality

def zl21TestMass {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] : ℝ :=
  admissionsSelectedWelfareMass (zl21TestModel m) p m.quality

def zl21TestConditionalMass {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] : ℝ :=
  admissionsSelectedWelfareConditionalExp (zl21TestModel m) p m.quality

def zl21BaseSelectionProb {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] : ℝ :=
  admissionsSelectionProb (zl21BaseModel m) p

def zl21TestSelectionProb {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] : ℝ :=
  admissionsSelectionProb (zl21TestModel m) p

theorem zl21_base_universal_accept
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) :
    zl21BaseMass m (fun _ : ΩBase => True) = pmfExp m.prior m.quality := by
  simpa [zl21BaseMass] using
    (admissionsSelectionMass_of_true (m := zl21BaseModel m) (value := m.quality))

theorem zl21_base_no_accept
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) :
    zl21BaseMass m (fun _ : ΩBase => False) = 0 := by
  simp [zl21BaseMass]

theorem zl21_base_mass_of_compl
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] :
    zl21BaseMass m (fun ω => ¬ p ω) = pmfExp m.prior m.quality - zl21BaseMass m p := by
  simpa [zl21BaseMass] using
    (admissionsSelectedWelfareMass_of_compl (m := zl21BaseModel m) (p := p)
      (value := m.quality))

theorem zl21_base_mass_le_total_of_quality_nonneg
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p]
    (hvalue : ∀ θ, 0 ≤ m.quality θ) :
    zl21BaseMass m p ≤ pmfExp m.prior m.quality := by
  exact admissionsSelectedWelfareMass_le_total_of_value_nonneg (m := zl21BaseModel m)
    (p := p) (value := m.quality) hvalue

theorem zl21_base_conditional_of_zero_selection
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p]
    (hprob : zl21BaseSelectionProb m p = 0) :
    zl21BaseConditionalMass m p = 0 := by
  have hprob' : admissionsSelectionProb (zl21BaseModel m) p = 0 := by
    simpa [zl21BaseSelectionProb] using hprob
  unfold zl21BaseConditionalMass
  exact admissionsSelectedWelfareConditionalExp_of_selectionProb_zero (m := zl21BaseModel m)
    (p := p) (value := m.quality) (hprob := hprob')

theorem zl21_base_mass_of_zero_selection
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p]
    (hprob : zl21BaseSelectionProb m p = 0) :
    zl21BaseMass m p = 0 := by
  have hprob' : admissionsSelectionProb (zl21BaseModel m) p = 0 := by
    simpa [zl21BaseSelectionProb] using hprob
  unfold zl21BaseMass
  exact admissionsSelectedWelfareMass_of_selectionProb_zero (m := zl21BaseModel m)
    (p := p) (value := m.quality) hprob'

theorem zl21_base_mass_eq_selectionProb_mul_conditionalMass
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] :
    zl21BaseMass m p = zl21BaseSelectionProb m p * zl21BaseConditionalMass m p := by
  simpa [zl21BaseMass, zl21BaseConditionalMass, zl21BaseSelectionProb] using
    (admissionsSelectedWelfareMass_eq_selectionProb_mul_conditionalExp (m := zl21BaseModel m)
      (p := p) (value := m.quality))

theorem zl21_base_mass_nonneg_of_quality_nonneg
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p]
    (hvalue : ∀ θ, 0 ≤ m.quality θ) :
    0 ≤ zl21BaseMass m p := by
  unfold zl21BaseMass
  exact admissionsSelectedWelfareMass_nonneg_of_value_nonneg (m := zl21BaseModel m)
    (p := p) (value := m.quality) hvalue

theorem zl21_base_conditional_nonneg_of_quality_nonneg
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p]
    (hvalue : ∀ θ, 0 ≤ m.quality θ) :
    0 ≤ zl21BaseConditionalMass m p := by
  unfold zl21BaseConditionalMass
  exact admissionsSelectedWelfareConditionalExp_nonneg_of_value_nonneg (m := zl21BaseModel m)
    (p := p) (value := m.quality) hvalue

theorem zl21_base_mass_le_of_pred_le
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p q : ΩBase → Prop) [DecidablePred p] [DecidablePred q]
    (hvalue : ∀ θ, 0 ≤ m.quality θ)
    (hsub : ∀ ω, p ω → q ω) :
    zl21BaseMass m p ≤ zl21BaseMass m q := by
  unfold zl21BaseMass
  exact admissionsSelectedWelfareMass_le_of_pred_le (m := zl21BaseModel m) (p := p) (q := q)
    (value := m.quality) hvalue hsub

theorem zl21_test_universal_accept
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) :
    zl21TestMass m (fun _ : ΩTest => True) = pmfExp m.prior m.quality := by
  simpa [zl21TestMass] using
    (admissionsSelectionMass_of_true (m := zl21TestModel m) (value := m.quality))

theorem zl21_test_no_accept
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) :
    zl21TestMass m (fun _ : ΩTest => False) = 0 := by
  simp [zl21TestMass]

theorem zl21_test_mass_of_compl
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] :
    zl21TestMass m (fun ω => ¬ p ω) = pmfExp m.prior m.quality - zl21TestMass m p := by
  simpa [zl21TestMass] using
    (admissionsSelectedWelfareMass_of_compl (m := zl21TestModel m) (p := p)
      (value := m.quality))

theorem zl21_test_mass_le_total_of_quality_nonneg
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p]
    (hvalue : ∀ θ, 0 ≤ m.quality θ) :
    zl21TestMass m p ≤ pmfExp m.prior m.quality := by
  exact admissionsSelectedWelfareMass_le_total_of_value_nonneg (m := zl21TestModel m)
    (p := p) (value := m.quality) hvalue

theorem zl21_test_conditional_of_zero_selection
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p]
    (hprob : zl21TestSelectionProb m p = 0) :
    zl21TestConditionalMass m p = 0 := by
  have hprob' : admissionsSelectionProb (zl21TestModel m) p = 0 := by
    simpa [zl21TestSelectionProb] using hprob
  unfold zl21TestConditionalMass
  exact admissionsSelectedWelfareConditionalExp_of_selectionProb_zero (m := zl21TestModel m)
    (p := p) (value := m.quality) (hprob := hprob')

theorem zl21_test_mass_of_zero_selection
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p]
    (hprob : zl21TestSelectionProb m p = 0) :
    zl21TestMass m p = 0 := by
  have hprob' : admissionsSelectionProb (zl21TestModel m) p = 0 := by
    simpa [zl21TestSelectionProb] using hprob
  unfold zl21TestMass
  exact admissionsSelectedWelfareMass_of_selectionProb_zero (m := zl21TestModel m)
    (p := p) (value := m.quality) hprob'

theorem zl21_test_mass_eq_selectionProb_mul_conditionalMass
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] :
    zl21TestMass m p = zl21TestSelectionProb m p * zl21TestConditionalMass m p := by
  simpa [zl21TestMass, zl21TestConditionalMass, zl21TestSelectionProb] using
    (admissionsSelectedWelfareMass_eq_selectionProb_mul_conditionalExp (m := zl21TestModel m)
      (p := p) (value := m.quality))

theorem zl21_test_mass_nonneg_of_quality_nonneg
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p]
    (hvalue : ∀ θ, 0 ≤ m.quality θ) :
    0 ≤ zl21TestMass m p := by
  unfold zl21TestMass
  exact admissionsSelectedWelfareMass_nonneg_of_value_nonneg (m := zl21TestModel m)
    (p := p) (value := m.quality) hvalue

theorem zl21_test_conditional_nonneg_of_quality_nonneg
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p]
    (hvalue : ∀ θ, 0 ≤ m.quality θ) :
    0 ≤ zl21TestConditionalMass m p := by
  unfold zl21TestConditionalMass
  exact admissionsSelectedWelfareConditionalExp_nonneg_of_value_nonneg (m := zl21TestModel m)
    (p := p) (value := m.quality) hvalue

theorem zl21_test_mass_le_of_pred_le
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p q : ΩTest → Prop) [DecidablePred p] [DecidablePred q]
    (hvalue : ∀ θ, 0 ≤ m.quality θ)
    (hsub : ∀ ω, p ω → q ω) :
    zl21TestMass m p ≤ zl21TestMass m q := by
  unfold zl21TestMass
  exact admissionsSelectedWelfareMass_le_of_pred_le (m := zl21TestModel m) (p := p) (q := q)
    (value := m.quality) hvalue hsub

theorem zl21_base_conditional_universal_accept
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) :
    zl21BaseConditionalMass m (fun _ : ΩBase => True) = pmfExp m.prior m.quality := by
  simpa [zl21BaseConditionalMass] using
    (admissionsSelectedWelfareConditionalExp_of_true (m := zl21BaseModel m) (value := m.quality))

theorem zl21_test_conditional_universal_accept
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) :
  zl21TestConditionalMass m (fun _ : ΩTest => True) = pmfExp m.prior m.quality := by
  simpa [zl21TestConditionalMass] using
    (admissionsSelectedWelfareConditionalExp_of_true (m := zl21TestModel m) (value := m.quality))

theorem zl21_base_conditional_of_compl
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] :
    zl21BaseConditionalMass m (fun ω => ¬ p ω) =
      (pmfExp m.prior m.quality - zl21BaseSelectionProb m p * zl21BaseConditionalMass m p) /
        zl21BaseSelectionProb m (fun ω => ¬ p ω) := by
  simpa [zl21BaseConditionalMass, zl21BaseSelectionProb] using
    (admissionsSelectedWelfareConditionalExp_of_compl (m := zl21BaseModel m) (p := p)
      (value := m.quality))

theorem zl21_base_exp_decompose
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩBase → Prop) [DecidablePred p] :
    pmfExp m.prior m.quality =
      zl21BaseSelectionProb m p * zl21BaseConditionalMass m p +
        zl21BaseSelectionProb m (fun ω => ¬ p ω) * zl21BaseConditionalMass m (fun ω => ¬ p ω) := by
  simpa [zl21BaseSelectionProb, zl21BaseConditionalMass] using
    (admissionsSelectedWelfareExp_decompose (m := zl21BaseModel m) (p := p)
      (value := m.quality))

theorem zl21_test_conditional_of_compl
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] :
    zl21TestConditionalMass m (fun ω => ¬ p ω) =
      (pmfExp m.prior m.quality - zl21TestSelectionProb m p * zl21TestConditionalMass m p) /
        zl21TestSelectionProb m (fun ω => ¬ p ω) := by
  simpa [zl21TestConditionalMass, zl21TestSelectionProb] using
    (admissionsSelectedWelfareConditionalExp_of_compl (m := zl21TestModel m) (p := p)
      (value := m.quality))

theorem zl21_test_exp_decompose
    {Θ ΩBase ΩTest : Type*} [Fintype Θ] [DecidableEq Θ]
    [Fintype ΩBase] [DecidableEq ΩBase] [Fintype ΩTest] [DecidableEq ΩTest]
    (m : ZL21Model Θ ΩBase ΩTest) (p : ΩTest → Prop) [DecidablePred p] :
    pmfExp m.prior m.quality =
      zl21TestSelectionProb m p * zl21TestConditionalMass m p +
        zl21TestSelectionProb m (fun ω => ¬ p ω) * zl21TestConditionalMass m (fun ω => ¬ p ω) := by
  simpa [zl21TestSelectionProb, zl21TestConditionalMass] using
    (admissionsSelectedWelfareExp_decompose (m := zl21TestModel m) (p := p)
      (value := m.quality))

end

end ZL21TestOptionalPolicies
