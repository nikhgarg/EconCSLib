import Monoculture.MallowsCenterCertificate

open scoped BigOperators
open DecisionCore

namespace Monoculture
namespace MallowsComparison

variable {n : ℕ} (C : MallowsComparison n)

/--
Cross-multiplied first-choice weight comparisons imply normalized first-choice
probability comparisons.  This is the algebraic form usually easiest to obtain
from finite Mallows sums, because the positive partition functions have been
cleared.
-/
theorem firstWeight_div_le_of_cross_mul_le
    (c : Candidate n)
    (hcross :
      C.human.firstWeight c * C.algorithm.partition ≤
        C.algorithm.firstWeight c * C.human.partition) :
    C.human.firstWeight c / C.human.partition ≤
      C.algorithm.firstWeight c / C.algorithm.partition := by
  apply le_of_mul_le_mul_right (a := C.human.partition * C.algorithm.partition)
  · calc
      C.human.firstWeight c / C.human.partition *
          (C.human.partition * C.algorithm.partition)
          = C.human.firstWeight c * C.algorithm.partition := by
            field_simp [C.human.partition_ne_zero]
      _ ≤ C.algorithm.firstWeight c * C.human.partition := hcross
      _ = C.algorithm.firstWeight c / C.algorithm.partition *
          (C.human.partition * C.algorithm.partition) := by
            field_simp [C.algorithm.partition_ne_zero]
  · exact mul_pos C.human.partition_pos C.algorithm.partition_pos

/--
Strict cross-multiplied center-weight improvement implies strict normalized
center first-choice improvement.
-/
theorem centerFirstWeight_div_lt_of_cross_mul_lt
    (hcross :
      C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
        C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition) :
    C.human.firstWeight C.human.centerFirst / C.human.partition <
      C.algorithm.firstWeight C.algorithm.centerFirst / C.algorithm.partition := by
  apply lt_of_mul_lt_mul_right (a := C.human.partition * C.algorithm.partition)
  · calc
      C.human.firstWeight C.human.centerFirst / C.human.partition *
          (C.human.partition * C.algorithm.partition)
          = C.human.firstWeight C.human.centerFirst * C.algorithm.partition := by
            field_simp [C.human.partition_ne_zero]
      _ < C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition := hcross
      _ = C.algorithm.firstWeight C.algorithm.centerFirst / C.algorithm.partition *
          (C.human.partition * C.algorithm.partition) := by
            field_simp [C.algorithm.partition_ne_zero]
  · exact le_of_lt (mul_pos C.human.partition_pos C.algorithm.partition_pos)

/--
Cross-multiplied first-choice weight differences imply the normalized
weaker-competition product sign.  This form keeps the sign on the whole product,
which is necessary because non-center candidates need not have either factor
nonnegative by itself.
-/
theorem collisionDiff_mul_gap_nonneg_of_cross_mul_gap_nonneg
    (value : Candidate n → ℝ) (c : Candidate n)
    (hcross : 0 ≤
      (C.algorithm.firstWeight c * C.human.partition -
        C.human.firstWeight c * C.algorithm.partition) *
          firstChoiceGapMass C.human.law value c) :
    0 ≤ firstChoiceCollisionDiff C.algorithm.law C.human.law c *
      firstChoiceGapMass C.human.law value c := by
  rw [firstChoiceCollisionDiff]
  rw [C.algorithm.firstChoiceProb_eq_firstWeight_div_partition c]
  rw [C.human.firstChoiceProb_eq_firstWeight_div_partition c]
  have hden_nonneg : 0 ≤ C.algorithm.partition * C.human.partition :=
    le_of_lt (mul_pos C.algorithm.partition_pos C.human.partition_pos)
  have hrewrite :
      (C.algorithm.firstWeight c / C.algorithm.partition -
          C.human.firstWeight c / C.human.partition) *
        firstChoiceGapMass C.human.law value c =
      ((C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        firstChoiceGapMass C.human.law value c) /
          (C.algorithm.partition * C.human.partition) := by
    field_simp [C.algorithm.partition_ne_zero, C.human.partition_ne_zero]
  rw [hrewrite]
  exact div_nonneg hcross hden_nonneg

/--
The strong finite Mallows inequality certificate with partition denominators
cleared.

This is useful as a convenience bridge for normalized first-weight comparisons.
The sharper paper-facing target below records weaker-competition signs directly
as products.
-/
structure CenterMallowsCrossWeightCertificate (value : Candidate n → ℝ) : Prop where
  strictly_center_ordered : C.StrictlyCenterOrdered value
  algorithm_gap_nonneg :
    ∀ c : Candidate n, 0 ≤ firstChoiceGapMass C.algorithm.law value c
  human_gap_nonneg :
    ∀ c : Candidate n, 0 ≤ firstChoiceGapMass C.human.law value c
  collision_firstWeight_cross_le :
    ∀ c : Candidate n,
      C.human.firstWeight c * C.algorithm.partition ≤
        C.algorithm.firstWeight c * C.human.partition
  center_firstWeight_cross_lt :
    C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
      C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition

/--
Cleared-denominator Mallows inequalities instantiate the normalized weight
certificate used by the main Mallows route.
-/
theorem centerMallowsWeightCertificate_of_crossWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsCrossWeightCertificate value) :
    C.CenterMallowsWeightCertificate value := by
  constructor
  · exact cert.strictly_center_ordered
  · exact cert.algorithm_gap_nonneg
  · exact cert.human_gap_nonneg
  · intro c
    exact C.firstWeight_div_le_of_cross_mul_le c
      (cert.collision_firstWeight_cross_le c)
  · exact C.centerFirstWeight_div_lt_of_cross_mul_lt
      cert.center_firstWeight_cross_lt

/-- Cleared-denominator finite Mallows inequalities instantiate the Mallows certificate. -/
theorem centerMallowsCertificate_of_crossWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsCrossWeightCertificate value) :
    C.CenterMallowsCertificate value := by
  exact C.centerMallowsCertificate_of_weightCertificate
    (C.centerMallowsWeightCertificate_of_crossWeightCertificate cert)

/-- Normalized weight-level Mallows inequalities imply the paper hypotheses. -/
theorem paperHypotheses_of_centerMallowsWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsWeightCertificate value) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.paperHypotheses_of_centerMallowsCertificate
    (C.centerMallowsCertificate_of_weightCertificate cert)

/-- Cleared-denominator finite Mallows inequalities imply the paper hypotheses. -/
theorem paperHypotheses_of_centerMallowsCrossWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsCrossWeightCertificate value) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.paperHypotheses_of_centerMallowsWeightCertificate
    (C.centerMallowsWeightCertificate_of_crossWeightCertificate cert)

/-- The algorithm law's center first-choice summand is strictly positive. -/
theorem algorithm_center_summand_pos_of_strictlyCenterOrdered
    {value : Candidate n → ℝ}
    (hvalue : C.StrictlyCenterOrdered value) :
    0 < firstChoiceMissProb C.algorithm.law C.algorithm.centerFirst *
      firstChoiceGapMass C.algorithm.law value C.algorithm.centerFirst := by
  exact mul_pos C.algorithm.centerFirstMissProb_pos
    (C.algorithm_centerGapMass_pos_of_strictlyCenterOrdered hvalue)

/-- The human law's center first-choice summand is strictly positive. -/
theorem human_center_summand_pos_of_strictlyCenterOrdered
    {value : Candidate n → ℝ}
    (hvalue : C.StrictlyCenterOrdered value) :
    0 < firstChoiceMissProb C.human.law C.human.centerFirst *
      firstChoiceGapMass C.human.law value C.human.centerFirst := by
  exact mul_pos C.human.centerFirstMissProb_pos
    (C.human_centerGapMass_pos_of_strictlyCenterOrdered hvalue)

/--
Strict cross-multiplied center first-choice improvement makes the
weaker-competition center product strictly positive.
-/
theorem weaker_center_cross_product_pos_of_strictlyCenterOrdered
    {value : Candidate n → ℝ}
    (hvalue : C.StrictlyCenterOrdered value)
    (hcenter :
      C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
        C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition) :
    0 < (C.algorithm.firstWeight C.human.centerFirst * C.human.partition -
        C.human.firstWeight C.human.centerFirst * C.algorithm.partition) *
      firstChoiceGapMass C.human.law value C.human.centerFirst := by
  have hcenter' :
      C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
        C.algorithm.firstWeight C.human.centerFirst * C.human.partition := by
    simpa [C.algorithm_centerFirst_eq_human_centerFirst] using hcenter
  exact mul_pos (sub_pos.mpr hcenter')
    (C.human_centerGapMass_pos_of_strictlyCenterOrdered hvalue)

/--
Product-sign finite Mallows certificate with partition denominators cleared.

This is the sharp paper-facing finite-inequality target for the current
formalization: the weaker-competition term is recorded as a product sign rather
than as separate signs for the probability and value-gap factors.
-/
structure CenterMallowsProductCrossWeightCertificate
    (value : Candidate n → ℝ) : Prop where
  strictly_center_ordered : C.StrictlyCenterOrdered value
  algorithm_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceMissProb C.algorithm.law c *
        firstChoiceGapMass C.algorithm.law value c
  human_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceMissProb C.human.law c *
        firstChoiceGapMass C.human.law value c
  weaker_cross_product_nonneg :
    ∀ c : Candidate n,
      0 ≤ (C.algorithm.firstWeight c * C.human.partition -
          C.human.firstWeight c * C.algorithm.partition) *
        firstChoiceGapMass C.human.law value c
  center_firstWeight_cross_lt :
    C.human.firstWeight C.human.centerFirst * C.algorithm.partition <
      C.algorithm.firstWeight C.algorithm.centerFirst * C.human.partition

/--
The product-sign finite Mallows certificate instantiates the main Mallows
certificate without requiring over-strong candidatewise probability monotonicity.
-/
theorem centerMallowsCertificate_of_productCrossWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsProductCrossWeightCertificate value) :
    C.CenterMallowsCertificate value := by
  constructor
  · exact cert.strictly_center_ordered
  · exact cert.algorithm_nonneg
  · exact cert.human_nonneg
  · intro c
    exact C.collisionDiff_mul_gap_nonneg_of_cross_mul_gap_nonneg value c
      (cert.weaker_cross_product_nonneg c)
  · exact C.centerFirstProb_lt_of_centerFirstWeight_div_lt
      (C.centerFirstWeight_div_lt_of_cross_mul_lt
        cert.center_firstWeight_cross_lt)

/--
Product-sign finite Mallows inequalities imply the paper hypotheses for the
pointwise-value monoculture model.
-/
theorem paperHypotheses_of_centerMallowsProductCrossWeightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsProductCrossWeightCertificate value) :
    Model.PaperHypotheses (C.toModel value) := by
  exact C.paperHypotheses_of_centerMallowsCertificate
    (C.centerMallowsCertificate_of_productCrossWeightCertificate cert)

end MallowsComparison
end Monoculture
