import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite Prediction and Statistics Primitives

Reusable finite weighted prediction-model, loss, rate, and calibration
interfaces.  These definitions are intentionally not fairness-specific: they
also support statistics, calibration, discretization-bias, and prediction
papers.
-/

namespace EconCSLib
namespace Statistics

open scoped BigOperators

/-- A real-valued predictor on feature space `X`. -/
abbrev Model (X : Type*) := X → ℝ

/-- A finite weighted distribution over feature observations. -/
abbrev FiniteWeight (X : Type*) := X → ℝ

/-- A group, event, or soft weighting function on feature space `X`. -/
abbrev Group (X : Type*) := X → ℝ

/-- Constant real-valued predictor. -/
def constantModel {X : Type*} (a : ℝ) : Model X :=
  fun _ => a

/-- Squared-error loss at one observation. -/
def squaredError {X : Type*} (f y : Model X) (x : X) : ℝ :=
  (f x - y x) ^ 2

/-- Finite weighted model loss. -/
def modelLoss {X : Type*} [Fintype X] (w : FiniteWeight X)
    (loss : X → ℝ) : ℝ :=
  ∑ x, w x * loss x

/-- Finite weighted squared-error loss. -/
def squaredLoss {X : Type*} [Fintype X] (w : FiniteWeight X)
    (f y : Model X) : ℝ :=
  modelLoss w (fun x => squaredError f y x)

/-- Weighted mass of a group/event. -/
def groupMass {X : Type*} [Fintype X] (w : FiniteWeight X)
    (g : Group X) : ℝ :=
  ∑ x, w x * g x

/-- Weighted numerator of a group/event-conditional loss. -/
def groupLossNumerator {X : Type*} [Fintype X] (w : FiniteWeight X)
    (g : Group X) (loss : X → ℝ) : ℝ :=
  ∑ x, w x * g x * loss x

/-- Conditional group/event loss, using totalized real division. -/
noncomputable def groupLoss {X : Type*} [Fintype X] (w : FiniteWeight X)
    (g : Group X) (loss : X → ℝ) : ℝ :=
  groupLossNumerator w g loss / groupMass w g

/-- Conditional group squared-error loss. -/
noncomputable def groupSquaredLoss {X : Type*} [Fintype X] (w : FiniteWeight X)
    (g : Group X) (f y : Model X) : ℝ :=
  groupLoss w g (fun x => squaredError f y x)

/-- Conditional group squared disagreement between two predictors. -/
noncomputable def groupSquaredDisagreement {X : Type*} [Fintype X] (w : FiniteWeight X)
    (g : Group X) (f h : Model X) : ℝ :=
  groupLoss w g (fun x => (f x - h x) ^ 2)

/-- Pointwise zero-one loss for classification labels encoded as real models. -/
noncomputable def zeroOneLoss {X : Type*} (c y : Model X) (x : X) : ℝ :=
  if c x = y x then 0 else 1

/-- Expected zero-one classification error. -/
noncomputable def classificationError {X : Type*} [Fintype X]
    (w : FiniteWeight X) (c y : Model X) : ℝ :=
  modelLoss w (fun x => zeroOneLoss c y x)

/--
Expected zero-one classification loss when `yProb` is the conditional
probability of label one.
-/
noncomputable def probabilisticClassificationLoss {X : Type*}
    (yProb c : Model X) (x : X) : ℝ :=
  yProb x * zeroOneLoss c (constantModel 1) x +
    (1 - yProb x) * zeroOneLoss c (constantModel 0) x

/-- Numerator for a finite weighted conditional rate. -/
def weightedRateNumerator {X : Type*} [Fintype X]
    (w : FiniteWeight X) (weight loss : X → ℝ) : ℝ :=
  ∑ x, w x * weight x * loss x

/-- Mass/denominator for a finite weighted conditional rate. -/
def weightedRateMass {X : Type*} [Fintype X]
    (w : FiniteWeight X) (weight : X → ℝ) : ℝ :=
  ∑ x, w x * weight x

/-- Conditional rate for a finite weighted numerator and mass. -/
noncomputable def weightedRate {X : Type*} [Fintype X]
    (w : FiniteWeight X) (weight loss : X → ℝ) : ℝ :=
  weightedRateNumerator w weight loss / weightedRateMass w weight

/-- Selected-mass divided by population-mass coefficient. -/
noncomputable def weightedRateBeta {X : Type*} [Fintype X]
    (w : FiniteWeight X) (selected population : X → ℝ) : ℝ :=
  weightedRateMass w selected / weightedRateMass w population

/--
Multiplying a conditional-rate gap by the selected mass is equivalent to the
corresponding finite expectation-gap form.
-/
theorem weightedRate_gap_eq_expectation_gap {X : Type*} [Fintype X]
    (w : FiniteWeight X) (selected population loss : X → ℝ)
    (hselected_nonneg : 0 ≤ weightedRateMass w selected)
    (hselected_ne : weightedRateMass w selected ≠ 0)
    (hpopulation_ne : weightedRateMass w population ≠ 0) :
    weightedRateMass w selected *
        |weightedRate w selected loss - weightedRate w population loss| =
      |weightedRateNumerator w selected loss -
        weightedRateBeta w selected population *
          weightedRateNumerator w population loss| := by
  unfold weightedRate weightedRateBeta
  set ms := weightedRateMass w selected
  set mp := weightedRateMass w population
  set ns := weightedRateNumerator w selected loss
  set np := weightedRateNumerator w population loss
  have hms : ms ≠ 0 := by simpa [ms] using hselected_ne
  have hmp : mp ≠ 0 := by simpa [mp] using hpopulation_ne
  have hscale :
      ms * |ns / ms - np / mp| =
        |ms * (ns / ms - np / mp)| := by
    rw [abs_mul]
    rw [abs_of_nonneg hselected_nonneg]
  rw [hscale]
  congr 1
  field_simp [hms, hmp]

/-- Indicator for a finite prediction level set `f(x) = v`. -/
noncomputable def levelSetIndicator {X : Type*} (f : Model X) (v : ℝ) : X → ℝ :=
  fun x => if f x = v then 1 else 0

/-- Absolute product-class multiaccuracy in finite weighted notation. -/
def ApproxMultiaccurateOnProducts {X : Type*} [Fintype X]
    (w : FiniteWeight X) (f y : Model X)
    (G : Set (Group X)) (H : Set (Model X)) (eta : ℝ) : Prop :=
  ∀ g ∈ G, ∀ h ∈ H,
    |groupLossNumerator w g (fun x => h x * (f x - y x))| ≤ eta

/-- Source-style one-sided product-class multiaccuracy. -/
def OneSidedMultiaccurateOnProducts {X : Type*} [Fintype X]
    (w : FiniteWeight X) (f y : Model X)
    (G : Set (Group X)) (H : Set (Model X)) (eta : ℝ) : Prop :=
  ∀ g ∈ G, ∀ h ∈ H,
    groupLossNumerator w g (fun x => h x * (y x - f x)) ≤ eta

/-- A model class is closed under pointwise negation. -/
def ModelClassClosedUnderNegation {X : Type*} (H : Set (Model X)) : Prop :=
  ∀ h ∈ H, (fun x => -h x) ∈ H

/-- Flipping the residual sign negates the weighted residual correlation. -/
theorem groupLossNumerator_residual_flip {X : Type*} [Fintype X]
    (w : FiniteWeight X) (g : Group X) (h f y : Model X) :
    groupLossNumerator w g (fun x => h x * (f x - y x)) =
      -groupLossNumerator w g (fun x => h x * (y x - f x)) := by
  classical
  unfold groupLossNumerator
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  ring

/-- Negating the feature converts source-style residuals to the opposite sign. -/
theorem groupLossNumerator_neg_sourceResidual_eq {X : Type*} [Fintype X]
    (w : FiniteWeight X) (g : Group X) (h f y : Model X) :
    groupLossNumerator w g (fun x => (-h x) * (y x - f x)) =
      groupLossNumerator w g (fun x => h x * (f x - y x)) := by
  classical
  unfold groupLossNumerator
  refine Finset.sum_congr rfl ?_
  intro x _hx
  ring

/--
One-sided multiaccuracy gives absolute multiaccuracy when the feature/model
class is closed under negation.
-/
theorem approxMultiaccurateOnProducts_of_oneSided_negationClosed
    {X : Type*} [Fintype X]
    {w : FiniteWeight X} {f y : Model X}
    {G : Set (Group X)} {H : Set (Model X)} {eta : ℝ}
    (hma : OneSidedMultiaccurateOnProducts w f y G H eta)
    (hneg : ModelClassClosedUnderNegation H) :
    ApproxMultiaccurateOnProducts w f y G H eta := by
  intro g hg h hh
  have hsource :
      groupLossNumerator w g (fun x => h x * (y x - f x)) ≤ eta :=
    hma g hg h hh
  have hnegsource :
      groupLossNumerator w g (fun x => (-h x) * (y x - f x)) ≤ eta :=
    hma g hg (fun x => -h x) (hneg h hh)
  have hupper :
      groupLossNumerator w g (fun x => h x * (f x - y x)) ≤ eta := by
    rw [groupLossNumerator_neg_sourceResidual_eq w g h f y] at hnegsource
    exact hnegsource
  have hlower :
      -eta ≤ groupLossNumerator w g (fun x => h x * (f x - y x)) := by
    have hneg_le : -eta ≤
        -groupLossNumerator w g (fun x => h x * (y x - f x)) :=
      neg_le_neg hsource
    simpa [groupLossNumerator_residual_flip w g h f y] using hneg_le
  exact abs_le.mpr ⟨hlower, hupper⟩

/--
Absolute product-class multiaccuracy implies the printed one-sided source
convention, after flipping the residual sign from `f - y` to `y - f`.
-/
theorem oneSidedMultiaccurateOnProducts_of_approxMultiaccurateOnProducts
    {X : Type*} [Fintype X]
    {w : FiniteWeight X} {f y : Model X}
    {G : Set (Group X)} {H : Set (Model X)} {eta : ℝ}
    (hma : ApproxMultiaccurateOnProducts w f y G H eta) :
    OneSidedMultiaccurateOnProducts w f y G H eta := by
  intro g hg h hh
  have hcorr := hma g hg h hh
  have hlower :
      -eta ≤ groupLossNumerator w g (fun x => h x * (f x - y x)) :=
    (abs_le.mp hcorr).1
  have hneg_le :
      -groupLossNumerator w g (fun x => h x * (f x - y x)) ≤ eta :=
    by simpa using neg_le_neg hlower
  simpa [groupLossNumerator_residual_flip w g h f y] using hneg_le

/-- Approximate multicalibration in expectation over finite prediction values. -/
def ApproxMulticalibratedInExpectation {X : Type*} [Fintype X]
    (w : FiniteWeight X) (R : Finset ℝ) (f y : Model X)
    (C : Set (Model X)) (alpha : ℝ) : Prop :=
  ∀ c ∈ C,
    R.sum (fun v =>
      |weightedRateNumerator w (levelSetIndicator f v)
        (fun x => c x * (f x - y x))|) ≤ alpha

/-- Approximate joint multicalibration over a class of threshold functions. -/
def ApproxJointMulticalibratedInExpectation {X : Type*} [Fintype X]
    (w : FiniteWeight X) (R : Finset ℝ) (f y : Model X)
    (B : Set (X → ℝ → ℝ)) (alpha : ℝ) : Prop :=
  ∀ b ∈ B,
    R.sum (fun v =>
      |weightedRateNumerator w
        (fun x => levelSetIndicator f v x * b x v)
        (fun x => f x - y x)|) ≤ alpha

/-- Absolute self-orthogonality of a predictor on a group collection. -/
def SelfOrthogonalOnGroups {X : Type*} [Fintype X]
    (w : FiniteWeight X) (f y : Model X)
    (G : Set (Group X)) (eta : ℝ) : Prop :=
  ∀ g ∈ G,
    |groupLossNumerator w g (fun x => f x * (f x - y x))| ≤ eta

/-- Conditional posterior mean absolute error contribution at one feature. -/
noncomputable def posteriorConditionalMAE {X Y : Type*} [Fintype Y]
    (q : X → Y → ℝ) (x : X) : ℝ :=
  ∑ y : Y, q x y * (1 - q x y)

/-- Finite weighted predictive MAE for posterior scores. -/
noncomputable def posteriorMAE {X Y : Type*} [Fintype X] [Fintype Y]
    (w : FiniteWeight X) (q : X → Y → ℝ) : ℝ :=
  modelLoss w (posteriorConditionalMAE q)

end Statistics
end EconCSLib
