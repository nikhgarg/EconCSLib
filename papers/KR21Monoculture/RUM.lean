import KR21Monoculture.Theorem1
import EconCSLib.Foundations.Probability.BivariateGaussian
import EconCSLib.Foundations.Probability.MeasureInequalities
import EconCSLib.Foundations.Probability.RandomUtility
import EconCSLib.Foundations.Probability.RandomUtilityDensity
import EconCSLib.SocialChoice.Ranking.Probability
import EconCSLib.SocialChoice.Ranking.Score
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open EconCSLib MeasureTheory
open scoped ENNReal NNReal

namespace KR21Monoculture

/-!
# Random-Utility Noise Inequalities

This file starts the random-utility-model side of the monoculture paper with the
finite real inequalities used by Appendix C.
-/

/--
Paper Definition 4, strict form.

For `a > b` and `c > d`, assigning the larger realized value to the larger true
value is strictly more likely than the crossed assignment.
-/
def StrictlyWellOrderedNoise (f : ℝ → ℝ) : Prop :=
  EconCSLib.Probability.StrictlyWellOrderedNoise f

/--
Weak version of Definition 4.  This is useful for Laplacian kernels, where the
strict paper inequality can be an equality when the two ordered intervals are
separated on the real line.
-/
def WeaklyWellOrderedNoise (f : ℝ → ℝ) : Prop :=
  EconCSLib.Probability.WeaklyWellOrderedNoise f

/-- The strict paper condition immediately gives the weak comparison. -/
theorem StrictlyWellOrderedNoise.weak {f : ℝ → ℝ}
    (hf : StrictlyWellOrderedNoise f) :
    WeaklyWellOrderedNoise f := by
  exact EconCSLib.Probability.StrictlyWellOrderedNoise.weak hf

/-- Gaussian density kernel, omitting the positive normalizing constant. -/
noncomputable def gaussianNoiseKernel (κ : ℝ) (x : ℝ) : ℝ :=
  EconCSLib.Probability.gaussianNoiseKernel κ x

/-- Laplacian density kernel, omitting the positive normalizing constant. -/
noncomputable def laplacianNoiseKernel (lam : ℝ) (x : ℝ) : ℝ :=
  EconCSLib.Probability.laplacianNoiseKernel lam x

theorem gaussianNoiseKernel_pos (κ x : ℝ) :
    0 < gaussianNoiseKernel κ x := by
  exact EconCSLib.Probability.gaussianNoiseKernel_pos κ x

theorem gaussianNoiseKernel_nonneg (κ x : ℝ) :
    0 ≤ gaussianNoiseKernel κ x :=
  le_of_lt (gaussianNoiseKernel_pos κ x)

theorem laplacianNoiseKernel_pos (lam x : ℝ) :
    0 < laplacianNoiseKernel lam x := by
  exact EconCSLib.Probability.laplacianNoiseKernel_pos lam x

theorem laplacianNoiseKernel_nonneg (lam x : ℝ) :
    0 ≤ laplacianNoiseKernel lam x :=
  le_of_lt (laplacianNoiseKernel_pos lam x)

/--
The algebraic core of the Gaussian well-ordering proof:
swapping the larger realized value to the larger true value improves the
negative squared-error exponent by `2κ(a-b)(c-d)`.
-/
theorem gaussian_exponent_cross_lt_ordered
    {κ a b c d : ℝ} (hκ : 0 < κ) (hab : b < a) (hcd : d < c) :
    -κ * (a - d) ^ 2 + -κ * (b - c) ^ 2 <
      -κ * (a - c) ^ 2 + -κ * (b - d) ^ 2 := by
  exact EconCSLib.Probability.gaussian_exponent_cross_lt_ordered hκ hab hcd

/-- Gaussian kernels satisfy the paper's strict well-ordering condition. -/
theorem gaussianNoiseKernel_strictlyWellOrdered
    {κ : ℝ} (hκ : 0 < κ) :
    StrictlyWellOrderedNoise (gaussianNoiseKernel κ) := by
  simpa [StrictlyWellOrderedNoise, gaussianNoiseKernel] using
    EconCSLib.Probability.gaussianNoiseKernel_strictlyWellOrdered hκ

/-- Four-point rearrangement inequality for absolute distance on the line. -/
theorem abs_ordered_cross_le_ordered
    {a b c d : ℝ} (hab : b ≤ a) (hcd : d ≤ c) :
    |a - c| + |b - d| ≤ |a - d| + |b - c| := by
  exact EconCSLib.Probability.abs_ordered_cross_le_ordered hab hcd

/--
Strict four-point rearrangement for absolute distance when the two ordered
intervals overlap (`b < c` and `d < a`).
-/
theorem abs_ordered_cross_lt_ordered_of_overlap
    {a b c d : ℝ} (hab : b < a) (hcd : d < c) (hbc : b < c) (hda : d < a) :
    |a - c| + |b - d| < |a - d| + |b - c| := by
  exact EconCSLib.Probability.abs_ordered_cross_lt_ordered_of_overlap
    hab hcd hbc hda

/-- Laplacian kernels satisfy the weak well-ordering inequality. -/
theorem laplacianNoiseKernel_weaklyWellOrdered
    {lam : ℝ} (hlam : 0 ≤ lam) :
    WeaklyWellOrderedNoise (laplacianNoiseKernel lam) := by
  simpa [WeaklyWellOrderedNoise, laplacianNoiseKernel] using
    EconCSLib.Probability.laplacianNoiseKernel_weaklyWellOrdered hlam

/--
The paper's strict Definition 4 is not satisfied by the Laplacian kernel as
stated: for separated ordered pairs, both assignments have the same total
absolute deviation.
-/
theorem laplacianNoiseKernel_not_strictlyWellOrdered (lam : ℝ) :
    ¬ StrictlyWellOrderedNoise (laplacianNoiseKernel lam) := by
  simpa [StrictlyWellOrderedNoise, laplacianNoiseKernel] using
    EconCSLib.Probability.laplacianNoiseKernel_not_strictlyWellOrdered lam

/--
Laplacian kernels satisfy the strict paper inequality on the overlap region.
This is the pointwise strict case left after the separated-interval equality
case is removed.
-/
theorem laplacianNoiseKernel_strictlyWellOrdered_of_overlap
    {lam a b c d : ℝ} (hlam : 0 < lam)
    (hab : b < a) (hcd : d < c) (hbc : b < c) (hda : d < a) :
    laplacianNoiseKernel lam (a - c) * laplacianNoiseKernel lam (b - d) >
      laplacianNoiseKernel lam (a - d) * laplacianNoiseKernel lam (b - c) := by
  simpa [laplacianNoiseKernel] using
    EconCSLib.Probability.laplacianNoiseKernel_strictlyWellOrdered_of_overlap
      hlam hab hcd hbc hda

/-! ## Appendix C, Theorem 7 scalar Laplacian derivative inequalities -/

/--
Appendix C, Theorem 7 scalar exponential bound used in the middle truncation
case of the Laplacian calculation.
-/
theorem paper_theorem7_exp_neg_gt_one_sub_two_mul {z : ℝ} (hz : 0 < z) :
    1 - 2 * z < Real.exp (-z) := by
  have hlinear : 1 - 2 * z < 1 - z := by linarith
  have hexp : 1 - z < Real.exp (-z) := by
    simpa [sub_eq_add_neg, add_comm] using
      (Real.add_one_lt_exp (show -z ≠ 0 by linarith))
  exact hlinear.trans hexp

/--
Appendix C, Theorem 7, case `x_j < a <= x_i`: after differentiating the
closed-form conditional probability, the sign condition reduces to
`exp (-z) > 1 - 2z` with `z = λ(a - x_j)`.
-/
theorem paper_theorem7_laplacian_case2_derivative_core
    {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u) :
    (2 * Real.exp (lam * u) - 1) * lam <
      (1 / 2 + lam * u) * (2 * lam * Real.exp (lam * u)) := by
  let z : ℝ := lam * u
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos hlam hu
  have hneg : 1 - 2 * z < Real.exp (-z) :=
    paper_theorem7_exp_neg_gt_one_sub_two_mul hz
  have hcore : 1 - Real.exp (-z) < 2 * z := by
    linarith
  have hmul :
      Real.exp z * (1 - Real.exp (-z)) <
        Real.exp z * (2 * z) :=
    mul_lt_mul_of_pos_left hcore (Real.exp_pos z)
  have hexp : Real.exp z * Real.exp (-z) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hmain : Real.exp z - 1 < 2 * z * Real.exp z := by
    nlinarith
  have hdiv :
      2 * Real.exp z - 1 < (1 / 2 + z) * (2 * Real.exp z) := by
    nlinarith
  have hscaled :=
    mul_lt_mul_of_pos_right hdiv hlam
  dsimp [z] at hscaled
  nlinarith

/--
The tail ratio subtracted from `1` in Appendix C, Theorem 7, case
`x_j < a <= x_i`.
-/
noncomputable def theorem7LaplacianCase2TailRatio
    (lam xj a : ℝ) : ℝ :=
  (1 / 2 + lam * (a - xj)) /
    (2 * Real.exp (lam * (a - xj)) - 1)

/--
Derivative of the Appendix C, Theorem 7 middle-case tail ratio.
-/
theorem theorem7LaplacianCase2TailRatio_hasDerivAt
    {lam xj a : ℝ}
    (hden : 2 * Real.exp (lam * (a - xj)) - 1 ≠ 0) :
    HasDerivAt
      (fun a => theorem7LaplacianCase2TailRatio lam xj a)
      (((lam) * (2 * Real.exp (lam * (a - xj)) - 1) -
          (1 / 2 + lam * (a - xj)) *
            (2 * (Real.exp (lam * (a - xj)) * lam))) /
        (2 * Real.exp (lam * (a - xj)) - 1) ^ 2)
      a := by
  have hlin : HasDerivAt (fun a => lam * (a - xj)) lam a := by
    simpa using ((hasDerivAt_id a).sub_const xj).const_mul lam
  have hnum :
      HasDerivAt (fun a => 1 / 2 + lam * (a - xj)) lam a := by
    convert (hasDerivAt_const a (1 / 2)).add hlin using 1
    ring
  have hexp :
      HasDerivAt
        (fun a => Real.exp (lam * (a - xj)))
        (Real.exp (lam * (a - xj)) * lam) a :=
    by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_exp (lam * (a - xj))).comp a hlin
  have hden' :
      HasDerivAt
        (fun a => 2 * Real.exp (lam * (a - xj)) - 1)
        (2 * (Real.exp (lam * (a - xj)) * lam)) a := by
    simpa using (hexp.const_mul 2).sub_const 1
  unfold theorem7LaplacianCase2TailRatio
  simpa using hnum.div hden' hden

/--
Appendix C, Theorem 7, case `x_j < a <= x_i`: the derivative of the
closed-form conditional probability is strictly positive in the interior.
-/
theorem theorem7LaplacianCase2ConditionalProb_hasDerivAt_pos
    {lam xj a : ℝ} (hlam : 0 < lam) (hu : 0 < a - xj) :
    ∃ d,
      HasDerivAt
        (fun a => 1 - theorem7LaplacianCase2TailRatio lam xj a) d a ∧
        0 < d := by
  have hden_pos : 0 < 2 * Real.exp (lam * (a - xj)) - 1 := by
    have hz : 0 < lam * (a - xj) := mul_pos hlam hu
    have hexp : 1 < Real.exp (lam * (a - xj)) :=
      Real.one_lt_exp_iff.mpr hz
    nlinarith
  have htail :=
    theorem7LaplacianCase2TailRatio_hasDerivAt
      (lam := lam) (xj := xj) (a := a) hden_pos.ne'
  let dTail :=
    ((lam) * (2 * Real.exp (lam * (a - xj)) - 1) -
        (1 / 2 + lam * (a - xj)) *
          (2 * (Real.exp (lam * (a - xj)) * lam))) /
      (2 * Real.exp (lam * (a - xj)) - 1) ^ 2
  refine ⟨-dTail, ?_, ?_⟩
  · simpa [dTail] using (hasDerivAt_const a (1 : ℝ)).sub htail
  · have hnum_neg :
        lam * (2 * Real.exp (lam * (a - xj)) - 1) -
            (1 / 2 + lam * (a - xj)) *
              (2 * (Real.exp (lam * (a - xj)) * lam)) < 0 := by
      have hcore :=
        paper_theorem7_laplacian_case2_derivative_core
          (lam := lam) (u := a - xj) hlam hu
      nlinarith
    have hden_sq_pos :
        0 < (2 * Real.exp (lam * (a - xj)) - 1) ^ 2 :=
      sq_pos_of_ne_zero hden_pos.ne'
    have htail_neg : dTail < 0 := by
      dsimp [dTail]
      exact div_neg_of_neg_of_pos hnum_neg hden_sq_pos
    linarith

/--
Appendix C, Theorem 7 final scalar bound in the right truncation case:
`3(e^z - 1) > 2z` for `z > 0`.
-/
theorem paper_theorem7_three_mul_exp_sub_one_gt_two_mul
    {z : ℝ} (hz : 0 < z) :
    2 * z < 3 * (Real.exp z - 1) := by
  have hexp : 1 + z < Real.exp z := by
    simpa [add_comm] using Real.add_one_lt_exp (show z ≠ 0 by linarith)
  have hgap : z < Real.exp z - 1 := by
    linarith
  nlinarith

/-- Auxiliary scalar expression used in Appendix C, Theorem 7, case 3. -/
noncomputable def theorem7LaplacianCase3EndpointAux (z : ℝ) : ℝ :=
  z + 2 * Real.exp (-z) + z * Real.exp (-z)

/-- Derivative of the Theorem 7 case-3 endpoint auxiliary expression. -/
theorem theorem7LaplacianCase3EndpointAux_hasDerivAt (z : ℝ) :
    HasDerivAt theorem7LaplacianCase3EndpointAux
      (1 - (1 + z) * Real.exp (-z)) z := by
  have hnegexp :
      HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-z)) z := by
    have hneg : HasDerivAt (fun z : ℝ => -z) (-1 : ℝ) z := by
      simpa using (hasDerivAt_id z).neg
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-z)).comp z hneg
  have hmain :
      HasDerivAt
        (fun z : ℝ => z + 2 * Real.exp (-z) + z * Real.exp (-z))
        (1 + 2 * (-Real.exp (-z)) +
          (1 * Real.exp (-z) + z * (-Real.exp (-z)))) z := by
    exact ((hasDerivAt_id z).add (hnegexp.const_mul 2)).add
      ((hasDerivAt_id z).mul hnegexp)
  unfold theorem7LaplacianCase3EndpointAux
  convert hmain using 1
  ring

/--
Appendix C, Theorem 7 scalar endpoint bound used in case 3:
`z + 2e^{-z} + z e^{-z} > 2` for `z > 0`.
-/
theorem paper_theorem7_case3_endpoint_aux_gt_two
    {z : ℝ} (hz : 0 < z) :
    2 < theorem7LaplacianCase3EndpointAux z := by
  have hcont :
      ContinuousOn theorem7LaplacianCase3EndpointAux (Set.Ici (0 : ℝ)) := by
    intro x hx
    exact (theorem7LaplacianCase3EndpointAux_hasDerivAt x).continuousAt.continuousWithinAt
  have hstrict :
      StrictMonoOn theorem7LaplacianCase3EndpointAux (Set.Ici (0 : ℝ)) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos
      (D := Set.Ici (0 : ℝ))
      (f := theorem7LaplacianCase3EndpointAux)
      (f' := fun x => 1 - (1 + x) * Real.exp (-x))
      (convex_Ici (0 : ℝ)) hcont ?_ ?_
    · intro x hx
      exact (theorem7LaplacianCase3EndpointAux_hasDerivAt x).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      have hexp : 1 + x < Real.exp x := by
        simpa [add_comm] using Real.add_one_lt_exp (show x ≠ 0 by linarith)
      have hmul :
          (1 + x) * Real.exp (-x) < Real.exp x * Real.exp (-x) :=
        mul_lt_mul_of_pos_right hexp (Real.exp_pos (-x))
      have hright : Real.exp x * Real.exp (-x) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
      linarith
  have hlt := hstrict (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ))
    (le_of_lt hz) hz
  simpa [theorem7LaplacianCase3EndpointAux] using hlt

/--
Appendix C, Theorem 7, case 3 polynomial derivative numerator after the
substitution `r = exp(-λ(a-x_i))` and `s = exp(-λ(x_i-x_j))`.  The proof follows
the paper's endpoint bounds and convex interpolation in the remaining `r`
coordinate.
-/
theorem paper_theorem7_laplacian_case3_derivative_poly_core
    {z r : ℝ} (hz : 0 < z) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r ^ 2 * (1 - Real.exp (-z)) +
        r * (2 * Real.exp (-z) * z + 4 * Real.exp (-z) - 4) +
        (4 - 2 * Real.exp (-z) * z - 4 * Real.exp (-z) - 2 * z) < 0 := by
  let s : ℝ := Real.exp (-z)
  let B : ℝ :=
    r ^ 2 * (1 - s) + r * (2 * s * z + 4 * s - 4) +
      (4 - 2 * s * z - 4 * s - 2 * z)
  let B0 : ℝ := 4 - 2 * s * z - 4 * s - 2 * z
  let B1 : ℝ := 1 - s - 2 * z
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.exp_pos _
  have hs_lt_one : s < 1 := by
    dsimp [s]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hB0 : B0 < 0 := by
    have haux := paper_theorem7_case3_endpoint_aux_gt_two hz
    dsimp [theorem7LaplacianCase3EndpointAux] at haux
    dsimp [B0, s]
    nlinarith
  have hB1 : B1 < 0 := by
    have haux := paper_theorem7_exp_neg_gt_one_sub_two_mul hz
    dsimp [B1, s]
    nlinarith
  have hinterp :
      B ≤ (1 - r) * B0 + r * B1 := by
    have hdiff :
        ((1 - r) * B0 + r * B1) - B = (1 - s) * r * (1 - r) := by
      dsimp [B, B0, B1]
      ring
    have hnonneg : 0 ≤ (1 - s) * r * (1 - r) := by
      exact mul_nonneg (mul_nonneg (by linarith) hr0) (by linarith)
    linarith
  have hcombo : (1 - r) * B0 + r * B1 < 0 := by
    by_cases hr_zero : r = 0
    · subst r
      simpa using hB0
    · by_cases hr_one : r = 1
      · subst r
        simpa using hB1
      · have hr_pos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr_zero)
        have h1r_pos : 0 < 1 - r := sub_pos.mpr (lt_of_le_of_ne hr1 hr_one)
        have hleft : (1 - r) * B0 < 0 := mul_neg_of_pos_of_neg h1r_pos hB0
        have hright : r * B1 < 0 := mul_neg_of_pos_of_neg hr_pos hB1
        linarith
  dsimp [B, s] at hinterp
  exact lt_of_le_of_lt hinterp hcombo

/-- Numerator of the Appendix C, Theorem 7 case-3 closed-form probability. -/
noncomputable def theorem7LaplacianCase3Numerator (z r : ℝ) : ℝ :=
  8 - (4 + 2 * z) * Real.exp (-z) - 4 * r + Real.exp (-z) * r ^ 2

/-- Denominator of the Appendix C, Theorem 7 case-3 closed-form probability. -/
noncomputable def theorem7LaplacianCase3Denominator (z r : ℝ) : ℝ :=
  4 - 2 * r - 2 * r * Real.exp (-z) + Real.exp (-z) * r ^ 2

/--
Appendix C, Theorem 7, case 3 closed-form conditional probability after the
substitution `z = λ(x_i-x_j)` and `r = exp(-λ(a-x_i))`.
-/
noncomputable def theorem7LaplacianCase3Ratio (z r : ℝ) : ℝ :=
  theorem7LaplacianCase3Numerator z r /
    theorem7LaplacianCase3Denominator z r

/-- Case-3 denominator positivity on the paper's domain `z > 0`, `0 ≤ r ≤ 1`. -/
theorem theorem7LaplacianCase3Denominator_pos
    {z r : ℝ} (hz : 0 < z) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 < theorem7LaplacianCase3Denominator z r := by
  let s : ℝ := Real.exp (-z)
  have hs_le_one : s ≤ 1 := by
    dsimp [s]
    exact le_of_lt (Real.exp_lt_one_iff.mpr (by linarith))
  have h2r : 0 ≤ 2 - r := by linarith
  have hdiff :
      theorem7LaplacianCase3Denominator z r - (2 - r) ^ 2 =
        (1 - s) * r * (2 - r) := by
    dsimp [theorem7LaplacianCase3Denominator, s]
    ring
  have hnonneg : 0 ≤ (1 - s) * r * (2 - r) := by
    exact mul_nonneg (mul_nonneg (by linarith) hr0) h2r
  have hbase : 0 < (2 - r) ^ 2 := by
    have hpos : 0 < 2 - r := by linarith
    exact sq_pos_of_pos hpos
  nlinarith

/-- Derivative of the Appendix C, Theorem 7 case-3 ratio with respect to `r`. -/
theorem theorem7LaplacianCase3Ratio_hasDerivAt
    {z r : ℝ} (hden : theorem7LaplacianCase3Denominator z r ≠ 0) :
    HasDerivAt
      (fun r => theorem7LaplacianCase3Ratio z r)
      (((-4 + 2 * Real.exp (-z) * r) *
            theorem7LaplacianCase3Denominator z r -
          theorem7LaplacianCase3Numerator z r *
            (-2 - 2 * Real.exp (-z) + 2 * Real.exp (-z) * r)) /
        theorem7LaplacianCase3Denominator z r ^ 2)
      r := by
  have hnum :
      HasDerivAt
        (fun r => theorem7LaplacianCase3Numerator z r)
        (-4 + 2 * Real.exp (-z) * r) r := by
    have hsq :
        HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
      simpa [pow_two, two_mul] using (hasDerivAt_id r).mul (hasDerivAt_id r)
    unfold theorem7LaplacianCase3Numerator
    convert
      ((((hasDerivAt_const r (8 : ℝ)).sub
          ((hasDerivAt_const r ((4 + 2 * z) * Real.exp (-z))))).sub
          ((hasDerivAt_id r).const_mul 4)).add
          (hsq.const_mul (Real.exp (-z)))) using 1
    · ring
  have hden' :
      HasDerivAt
        (fun r => theorem7LaplacianCase3Denominator z r)
        (-2 - 2 * Real.exp (-z) + 2 * Real.exp (-z) * r) r := by
    have hsq :
        HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
      simpa [pow_two, two_mul] using (hasDerivAt_id r).mul (hasDerivAt_id r)
    unfold theorem7LaplacianCase3Denominator
    convert
      ((((hasDerivAt_const r (4 : ℝ)).sub
          ((hasDerivAt_id r).const_mul 2)).sub
          ((hasDerivAt_id r).const_mul (2 * Real.exp (-z)))).add
          (hsq.const_mul (Real.exp (-z)))) using 1
    · ext y
      simp
      ring
    · ring
  unfold theorem7LaplacianCase3Ratio
  simpa using hnum.div hden' hden

/--
Appendix C, Theorem 7, case 3: the closed-form ratio is strictly decreasing in
`r` on the paper's domain.
-/
theorem theorem7LaplacianCase3Ratio_hasDerivAt_neg
    {z r : ℝ} (hz : 0 < z) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ d,
      HasDerivAt (fun r => theorem7LaplacianCase3Ratio z r) d r ∧
        d < 0 := by
  have hden_pos := theorem7LaplacianCase3Denominator_pos hz hr0 hr1
  let d :=
    (((-4 + 2 * Real.exp (-z) * r) *
          theorem7LaplacianCase3Denominator z r -
        theorem7LaplacianCase3Numerator z r *
          (-2 - 2 * Real.exp (-z) + 2 * Real.exp (-z) * r)) /
      theorem7LaplacianCase3Denominator z r ^ 2)
  refine ⟨d, theorem7LaplacianCase3Ratio_hasDerivAt hden_pos.ne', ?_⟩
  have hpoly :=
    paper_theorem7_laplacian_case3_derivative_poly_core hz hr0 hr1
  have hnum_eq :
      (-4 + 2 * Real.exp (-z) * r) *
          theorem7LaplacianCase3Denominator z r -
        theorem7LaplacianCase3Numerator z r *
          (-2 - 2 * Real.exp (-z) + 2 * Real.exp (-z) * r) =
        2 * Real.exp (-z) *
          (r ^ 2 * (1 - Real.exp (-z)) +
            r * (2 * Real.exp (-z) * z + 4 * Real.exp (-z) - 4) +
            (4 - 2 * Real.exp (-z) * z - 4 * Real.exp (-z) - 2 * z)) := by
    dsimp [theorem7LaplacianCase3Numerator,
      theorem7LaplacianCase3Denominator]
    ring
  have hnum_neg :
      (-4 + 2 * Real.exp (-z) * r) *
          theorem7LaplacianCase3Denominator z r -
        theorem7LaplacianCase3Numerator z r *
          (-2 - 2 * Real.exp (-z) + 2 * Real.exp (-z) * r) < 0 := by
    rw [hnum_eq]
    exact mul_neg_of_pos_of_neg
      (mul_pos zero_lt_two (Real.exp_pos _)) hpoly
  have hden_sq_pos :
      0 < theorem7LaplacianCase3Denominator z r ^ 2 :=
    sq_pos_of_ne_zero hden_pos.ne'
  dsimp [d]
  exact div_neg_of_neg_of_pos hnum_neg hden_sq_pos

/--
Appendix C, Theorem 7, case 3 closed-form conditional probability in the
original `a` coordinate.
-/
noncomputable def theorem7LaplacianCase3ConditionalProb
    (lam xi xj a : ℝ) : ℝ :=
  theorem7LaplacianCase3Ratio
    (lam * (xi - xj))
    (Real.exp (-lam * (a - xi)))

/--
Appendix C, Theorem 7, case `a > x_i`: the derivative of the closed-form
conditional probability is strictly positive.
-/
theorem theorem7LaplacianCase3ConditionalProb_hasDerivAt_pos
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi < a) :
    ∃ d,
      HasDerivAt
        (fun a => theorem7LaplacianCase3ConditionalProb lam xi xj a) d a ∧
        0 < d := by
  let z : ℝ := lam * (xi - xj)
  let r : ℝ := Real.exp (-lam * (a - xi))
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos hlam (sub_pos.mpr hx)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact le_of_lt (Real.exp_pos _)
  have hr1 : r ≤ 1 := by
    dsimp [r]
    have hneg : -lam * (a - xi) < 0 := by
      have hpos : 0 < lam * (a - xi) := mul_pos hlam (sub_pos.mpr ha)
      linarith
    exact le_of_lt (Real.exp_lt_one_iff.mpr hneg)
  obtain ⟨dRatio, hratio, hdRatio⟩ :=
    theorem7LaplacianCase3Ratio_hasDerivAt_neg
      (z := z) (r := r) hz hr0 hr1
  have hinner :
      HasDerivAt
        (fun a : ℝ => Real.exp (-lam * (a - xi)))
        (Real.exp (-lam * (a - xi)) * (-lam)) a := by
    have hlin : HasDerivAt (fun a : ℝ => -lam * (a - xi)) (-lam) a := by
      simpa using ((hasDerivAt_id a).sub_const xi).const_mul (-lam)
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-lam * (a - xi))).comp a hlin
  refine ⟨dRatio * (Real.exp (-lam * (a - xi)) * (-lam)), ?_, ?_⟩
  · dsimp [theorem7LaplacianCase3ConditionalProb, z, r] at hratio ⊢
    exact hratio.comp a hinner
  · have hinner_neg : Real.exp (-lam * (a - xi)) * (-lam) < 0 :=
      mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith)
    exact mul_pos_of_neg_of_neg hdRatio hinner_neg

/-- Appendix C, Theorem 7, case `a ≤ x_j`: the closed form is constant. -/
theorem theorem7LaplacianCase1ConditionalProb_hasDerivAt_nonneg (a : ℝ) :
    HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 a ∧ 0 ≤ (0 : ℝ) :=
  ⟨hasDerivAt_const a (1 / 2 : ℝ), le_rfl⟩

/--
Appendix C, Theorem 7 for the paper's three Laplacian closed-form cases.

Lean states the result at the closed-form layer obtained after the integrations
in the paper: case 1 is constant, case 2 is
`1 - (1/2 + λ(a-x_j))/(2 exp(λ(a-x_j))-1)`, and case 3 is the right-tail
ratio after the substitutions `z = λ(x_i-x_j)` and
`r = exp(-λ(a-x_i))`.
-/
theorem paper_theorem7_laplacian_closedForm_derivative_cases
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (a ≤ xj →
      HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 a ∧ 0 ≤ (0 : ℝ)) ∧
    (xj < a → a ≤ xi →
      ∃ d,
        HasDerivAt
          (fun a => 1 - theorem7LaplacianCase2TailRatio lam xj a) d a ∧
          0 < d) ∧
    (xi < a →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianCase3ConditionalProb lam xi xj a) d a ∧
          0 < d) ∧
    (∃ a d,
      xj < a ∧ a < xi ∧
        HasDerivAt
          (fun a => 1 - theorem7LaplacianCase2TailRatio lam xj a) d a ∧
        0 < d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ha
    exact theorem7LaplacianCase1ConditionalProb_hasDerivAt_nonneg a
  · intro hleft _hright
    exact theorem7LaplacianCase2ConditionalProb_hasDerivAt_pos
      (lam := lam) (xj := xj) (a := a) hlam (sub_pos.mpr hleft)
  · intro hright
    exact theorem7LaplacianCase3ConditionalProb_hasDerivAt_pos
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx hright
  · let amid : ℝ := (xj + xi) / 2
    have hleft : xj < amid := by
      dsimp [amid]
      linarith
    have hright : amid < xi := by
      dsimp [amid]
      linarith
    obtain ⟨d, hd, hdpos⟩ :=
      theorem7LaplacianCase2ConditionalProb_hasDerivAt_pos
        (lam := lam) (xj := xj) (a := amid) hlam (sub_pos.mpr hleft)
    exact ⟨amid, d, hleft, hright, hd, hdpos⟩

/-
The next lemmas are the elementary integration identities used to connect the
paper's Laplace pdf/cdf integrals to the closed forms above.
-/

/-- Appendix C, Theorem 7: improper integral of an affine exponential. -/
theorem paper_theorem7_integral_exp_affine_Iic
    {k β c : ℝ} (hk : 0 < k) :
    ∫ x : ℝ in Set.Iic c, Real.exp (β + k * x) =
      Real.exp (β + k * c) / k := by
  calc
    ∫ x : ℝ in Set.Iic c, Real.exp (β + k * x) =
        ∫ x : ℝ in Set.Iic c, Real.exp β * Real.exp (k * x) := by
      refine setIntegral_congr_fun measurableSet_Iic fun x _hx => ?_
      rw [Real.exp_add]
    _ = Real.exp β * ∫ x : ℝ in Set.Iic c, Real.exp (k * x) := by
      rw [integral_const_mul]
    _ = Real.exp β * (Real.exp (k * c) / k) := by
      rw [integral_exp_mul_Iic hk]
    _ = Real.exp (β + k * c) / k := by
      rw [Real.exp_add]
      ring

/-- Appendix C, Theorem 7: finite-interval integral of an affine exponential. -/
theorem paper_theorem7_intervalIntegral_exp_affine
    {k β l u : ℝ} (hk : k ≠ 0) :
    ∫ x in l..u, Real.exp (β + k * x) =
      (Real.exp (β + k * u) - Real.exp (β + k * l)) / k := by
  calc
    ∫ x in l..u, Real.exp (β + k * x) =
        ∫ x in l..u, Real.exp β * Real.exp (k * x) := by
      refine intervalIntegral.integral_congr fun x _hx => ?_
      rw [Real.exp_add]
    _ = Real.exp β * ∫ x in l..u, Real.exp (k * x) := by
      rw [intervalIntegral.integral_const_mul]
    _ = Real.exp β * (k⁻¹ * ∫ y in k * l..k * u, Real.exp y) := by
      rw [intervalIntegral.integral_comp_mul_left (f := Real.exp) (a := l) (b := u)
        (c := k) hk]
      rfl
    _ = Real.exp β * (k⁻¹ * (Real.exp (k * u) - Real.exp (k * l))) := by
      rw [integral_exp]
    _ = (Real.exp (β + k * u) - Real.exp (β + k * l)) / k := by
      rw [Real.exp_add, Real.exp_add]
      field_simp [hk]

/-- The Laplace pdf used in Appendix C, Theorem 7. -/
noncomputable def theorem7LaplacePDF (lam μ x : ℝ) : ℝ :=
  lam / 2 * Real.exp (-lam * |x - μ|)

/-- The paper's closed-form Laplace CDF. -/
noncomputable def theorem7LaplaceCDFClosedForm (lam μ a : ℝ) : ℝ :=
  if a < μ then
    (1 / 2) * Real.exp (-lam * (μ - a))
  else
    1 - (1 / 2) * Real.exp (-lam * (a - μ))

/-- Appendix C, Theorem 7: the Laplace pdf below its mean. -/
theorem theorem7LaplacePDF_of_le_mean
    {lam μ x : ℝ} (hx : x ≤ μ) :
    theorem7LaplacePDF lam μ x =
      lam / 2 * Real.exp (-lam * (μ - x)) := by
  have habs : |x - μ| = μ - x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hx)]
    ring
  simp [theorem7LaplacePDF, habs]

/-- Appendix C, Theorem 7: the Laplace pdf above its mean. -/
theorem theorem7LaplacePDF_of_mean_le
    {lam μ x : ℝ} (hx : μ ≤ x) :
    theorem7LaplacePDF lam μ x =
      lam / 2 * Real.exp (-lam * (x - μ)) := by
  have habs : |x - μ| = x - μ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx)]
  simp [theorem7LaplacePDF, habs]

/--
Appendix C, Theorem 7: the low-tail Laplace CDF integral, matching the paper's
`x < μ` CDF branch.
-/
theorem theorem7LaplaceCDFIntegral_of_lt_mean
    {lam μ a : ℝ} (hlam : 0 < lam) (ha : a < μ) :
    ∫ x : ℝ in Set.Iic a, theorem7LaplacePDF lam μ x =
      (1 / 2) * Real.exp (-lam * (μ - a)) := by
  calc
    ∫ x : ℝ in Set.Iic a, theorem7LaplacePDF lam μ x =
        ∫ x : ℝ in Set.Iic a,
          lam / 2 * Real.exp ((-lam * μ) + lam * x) := by
      refine setIntegral_congr_fun measurableSet_Iic fun x hx => ?_
      have hxμ : x ≤ μ := le_trans hx (le_of_lt ha)
      rw [theorem7LaplacePDF_of_le_mean hxμ]
      have harg : -lam * (μ - x) = (-lam * μ) + lam * x := by ring
      rw [harg]
    _ = lam / 2 *
        ∫ x : ℝ in Set.Iic a, Real.exp ((-lam * μ) + lam * x) := by
      rw [integral_const_mul]
    _ = lam / 2 * (Real.exp ((-lam * μ) + lam * a) / lam) := by
      rw [paper_theorem7_integral_exp_affine_Iic
        (k := lam) (β := -lam * μ) (c := a) hlam]
    _ = (1 / 2) * Real.exp (-lam * (μ - a)) := by
      have harg : (-lam * μ) + lam * a = -lam * (μ - a) := by ring
      rw [harg]
      field_simp [hlam.ne']

/-- Appendix C, Theorem 7: closed-form CDF on and below the mean. -/
theorem theorem7LaplaceCDFClosedForm_of_le_mean
    {lam μ a : ℝ} (ha : a ≤ μ) :
    theorem7LaplaceCDFClosedForm lam μ a =
      (1 / 2) * Real.exp (-lam * (μ - a)) := by
  by_cases hlt : a < μ
  · simp [theorem7LaplaceCDFClosedForm, hlt]
  · have hEq : a = μ := le_antisymm ha (le_of_not_gt hlt)
    subst a
    simp [theorem7LaplaceCDFClosedForm]
    ring

/-- Appendix C, Theorem 7: closed-form CDF on and above the mean. -/
theorem theorem7LaplaceCDFClosedForm_of_mean_le
    {lam μ a : ℝ} (ha : μ ≤ a) :
    theorem7LaplaceCDFClosedForm lam μ a =
      1 - (1 / 2) * Real.exp (-lam * (a - μ)) := by
  have hnot : ¬ a < μ := not_lt.mpr ha
  simp [theorem7LaplaceCDFClosedForm, hnot]

/--
Appendix C, Theorem 7, case 1: numerator integral in the paper's equation
(C.3), on the region `a ≤ x_j < x_i`.
-/
theorem paper_theorem7_laplacian_case1_numerator_integral
    {lam xi xj a : ℝ} (hlam : 0 < lam) (ha : a ≤ xj) (hx : xj < xi) :
    ∫ x : ℝ in Set.Iic a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
      Real.exp (-lam * (xi + xj - 2 * a)) / 8 := by
  have hk : 0 < 2 * lam := by positivity
  calc
    ∫ x : ℝ in Set.Iic a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
        ∫ x : ℝ in Set.Iic a,
          lam / 4 *
            Real.exp ((-lam * (xi + xj)) + (2 * lam) * x) := by
      refine setIntegral_congr_fun measurableSet_Iic fun x hxIic => ?_
      have hxj : x ≤ xj := le_trans hxIic ha
      have hxi : x ≤ xi := le_trans hxj (le_of_lt hx)
      rw [theorem7LaplacePDF_of_le_mean hxi,
        theorem7LaplaceCDFClosedForm_of_le_mean (lam := lam) (μ := xj) hxj]
      calc
        lam / 2 * Real.exp (-lam * (xi - x)) *
            (1 / 2 * Real.exp (-lam * (xj - x))) =
            lam / 4 *
              (Real.exp (-lam * (xi - x)) *
                Real.exp (-lam * (xj - x))) := by ring
        _ = lam / 4 *
            Real.exp ((-lam * (xi + xj)) + (2 * lam) * x) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ = lam / 4 *
        ∫ x : ℝ in Set.Iic a,
          Real.exp ((-lam * (xi + xj)) + (2 * lam) * x) := by
      rw [integral_const_mul]
    _ = lam / 4 *
        (Real.exp ((-lam * (xi + xj)) + (2 * lam) * a) / (2 * lam)) := by
      rw [paper_theorem7_integral_exp_affine_Iic
        (k := 2 * lam) (β := -lam * (xi + xj)) (c := a) hk]
    _ = Real.exp (-lam * (xi + xj - 2 * a)) / 8 := by
      have harg :
          (-lam * (xi + xj)) + (2 * lam) * a =
            -lam * (xi + xj - 2 * a) := by ring
      rw [harg]
      field_simp [hlam.ne']
      ring

/--
Appendix C, Theorem 7, case 1: denominator in the paper's equation (C.3), on
the region `a ≤ x_j < x_i`.
-/
theorem paper_theorem7_laplacian_case1_denominator_closedForm
    {lam xi xj a : ℝ} (ha : a ≤ xj) (hx : xj < xi) :
    theorem7LaplaceCDFClosedForm lam xi a *
        theorem7LaplaceCDFClosedForm lam xj a =
      (1 / 4) * Real.exp (-lam * (xi + xj - 2 * a)) := by
  have haxi : a ≤ xi := le_trans ha (le_of_lt hx)
  rw [theorem7LaplaceCDFClosedForm_of_le_mean (lam := lam) (μ := xi) haxi,
    theorem7LaplaceCDFClosedForm_of_le_mean (lam := lam) (μ := xj) ha]
  calc
    (1 / 2) * Real.exp (-lam * (xi - a)) *
        ((1 / 2) * Real.exp (-lam * (xj - a))) =
        (1 / 4) *
          (Real.exp (-lam * (xi - a)) *
            Real.exp (-lam * (xj - a))) := by ring
    _ = (1 / 4) * Real.exp (-lam * (xi + xj - 2 * a)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/--
Appendix C, Theorem 7, case 1: the integral expression in (C.3) reduces to the
constant `1/2`.
-/
theorem paper_theorem7_laplacian_case1_integral_ratio
    {lam xi xj a : ℝ} (hlam : 0 < lam) (ha : a ≤ xj) (hx : xj < xi) :
    (∫ x : ℝ in Set.Iic a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) /
        (theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a) =
      (1 / 2 : ℝ) := by
  rw [paper_theorem7_laplacian_case1_numerator_integral hlam ha hx,
    paper_theorem7_laplacian_case1_denominator_closedForm (lam := lam) ha hx]
  have hne : Real.exp (-lam * (xi + xj - 2 * a)) ≠ 0 := Real.exp_ne_zero _
  field_simp [hne]
  norm_num

/--
Appendix C, Theorem 7, case 2: the paper's second integral over
`x_j ≤ x ≤ a ≤ x_i`.
-/
theorem paper_theorem7_laplacian_case2_second_integral
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hleft : xj ≤ a) (hright : a ≤ xi) :
    ∫ x in xj..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
      (1 / 2) *
          (Real.exp (-lam * (xi - a)) - Real.exp (-lam * (xi - xj))) -
        (lam / 4) * (a - xj) * Real.exp (-lam * (xi - xj)) := by
  calc
    ∫ x in xj..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
        ∫ x in xj..a,
          lam / 2 * Real.exp ((-lam * xi) + lam * x) -
            (lam / 4) * Real.exp (-lam * (xi - xj)) := by
      refine intervalIntegral.integral_congr fun x hxint => ?_
      have hxIcc : x ∈ Set.Icc xj a := by
        simpa [Set.uIcc_of_le hleft] using hxint
      have hxj : xj ≤ x := hxIcc.1
      have hxi : x ≤ xi := le_trans hxIcc.2 hright
      rw [theorem7LaplacePDF_of_le_mean hxi,
        theorem7LaplaceCDFClosedForm_of_mean_le (lam := lam) (μ := xj) hxj]
      calc
        lam / 2 * Real.exp (-lam * (xi - x)) *
            (1 - 1 / 2 * Real.exp (-lam * (x - xj))) =
            lam / 2 * Real.exp (-lam * (xi - x)) -
              lam / 4 *
                (Real.exp (-lam * (xi - x)) *
                  Real.exp (-lam * (x - xj))) := by ring
        _ = lam / 2 * Real.exp ((-lam * xi) + lam * x) -
            (lam / 4) * Real.exp (-lam * (xi - xj)) := by
          rw [← Real.exp_add]
          have hfirst : -lam * (xi - x) = (-lam * xi) + lam * x := by ring
          have hsecond :
              ((-lam * xi) + lam * x) + -lam * (x - xj) =
                -lam * (xi - xj) := by ring
          rw [hfirst, hsecond]
    _ = (∫ x in xj..a,
          lam / 2 * Real.exp ((-lam * xi) + lam * x)) -
        ∫ x in xj..a,
          (lam / 4) * Real.exp (-lam * (xi - xj)) := by
      have hInt1 :
          IntervalIntegrable
            (fun x : ℝ => lam / 2 * Real.exp ((-lam * xi) + lam * x))
            volume xj a := by
        apply ContinuousOn.intervalIntegrable
        fun_prop
      have hInt2 :
          IntervalIntegrable
            (fun _x : ℝ => (lam / 4) * Real.exp (-lam * (xi - xj)))
            volume xj a :=
        intervalIntegrable_const
      rw [intervalIntegral.integral_sub hInt1 hInt2]
    _ = (lam / 2 *
          ∫ x in xj..a, Real.exp ((-lam * xi) + lam * x)) -
        (a - xj) * ((lam / 4) * Real.exp (-lam * (xi - xj))) := by
      have hA :
          (∫ x in xj..a,
            lam / 2 * Real.exp ((-lam * xi) + lam * x)) =
            lam / 2 *
              ∫ x in xj..a, Real.exp ((-lam * xi) + lam * x) := by
        rw [intervalIntegral.integral_const_mul]
      have hB :
          (∫ x in xj..a,
            (lam / 4) * Real.exp (-lam * (xi - xj))) =
            (a - xj) * ((lam / 4) * Real.exp (-lam * (xi - xj))) := by
        rw [intervalIntegral.integral_const]
        ring
      rw [hA, hB]
    _ = (lam / 2 *
          ((Real.exp ((-lam * xi) + lam * a) -
              Real.exp ((-lam * xi) + lam * xj)) / lam)) -
        (a - xj) * ((lam / 4) * Real.exp (-lam * (xi - xj))) := by
      have hEval :=
        paper_theorem7_intervalIntegral_exp_affine
          (k := lam) (β := -lam * xi) (l := xj) (u := a) hlam.ne'
      exact congrArg
        (fun T =>
          lam / 2 * T -
            (a - xj) * ((lam / 4) * Real.exp (-lam * (xi - xj))))
        hEval
    _ = (1 / 2) *
          (Real.exp (-lam * (xi - a)) - Real.exp (-lam * (xi - xj))) -
        (lam / 4) * (a - xj) * Real.exp (-lam * (xi - xj)) := by
      have ha_arg : (-lam * xi) + lam * a = -lam * (xi - a) := by ring
      have hxj_arg : (-lam * xi) + lam * xj = -lam * (xi - xj) := by ring
      rw [ha_arg, hxj_arg]
      field_simp [hlam.ne']

/--
Appendix C, Theorem 7, case 2: the two paper numerator integrals combine to
the displayed closed form.
-/
theorem paper_theorem7_laplacian_case2_numerator_integral
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hleft : xj ≤ a) (hright : a ≤ xi)
    (hx : xj < xi) :
    (∫ x : ℝ in Set.Iic xj,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) +
      ∫ x in xj..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
      (1 / 2) * Real.exp (-lam * (xi - a)) -
        (3 / 8 + (lam / 4) * (a - xj)) *
          Real.exp (-lam * (xi - xj)) := by
  rw [paper_theorem7_laplacian_case1_numerator_integral
      (lam := lam) (xi := xi) (xj := xj) (a := xj) hlam le_rfl hx,
    paper_theorem7_laplacian_case2_second_integral hlam hleft hright]
  ring

/--
Appendix C, Theorem 7, case 2: denominator in (C.3), on
`x_j ≤ a ≤ x_i`.
-/
theorem paper_theorem7_laplacian_case2_denominator_closedForm
    {lam xi xj a : ℝ} (hleft : xj ≤ a) (hright : a ≤ xi) :
    theorem7LaplaceCDFClosedForm lam xi a *
        theorem7LaplaceCDFClosedForm lam xj a =
      (1 / 2) * Real.exp (-lam * (xi - a)) -
        (1 / 4) * Real.exp (-lam * (xi - xj)) := by
  rw [theorem7LaplaceCDFClosedForm_of_le_mean (lam := lam) (μ := xi) hright,
    theorem7LaplaceCDFClosedForm_of_mean_le (lam := lam) (μ := xj) hleft]
  calc
    (1 / 2) * Real.exp (-lam * (xi - a)) *
        (1 - 1 / 2 * Real.exp (-lam * (a - xj))) =
        (1 / 2) * Real.exp (-lam * (xi - a)) -
          (1 / 4) *
            (Real.exp (-lam * (xi - a)) *
              Real.exp (-lam * (a - xj))) := by ring
    _ = (1 / 2) * Real.exp (-lam * (xi - a)) -
        (1 / 4) * Real.exp (-lam * (xi - xj)) := by
      rw [← Real.exp_add]
      have harg :
          -lam * (xi - a) + -lam * (a - xj) =
            -lam * (xi - xj) := by ring
      rw [harg]

/-- Algebraic simplification behind Appendix C, Theorem 7, case 2. -/
theorem paper_theorem7_laplacian_case2_ratio_algebra
    {R u : ℝ} (hden : 2 * R - 1 ≠ 0) :
    ((1 / 2) * R - (3 / 8 + u / 4)) /
        ((1 / 2) * R - 1 / 4) =
      1 - (1 / 2 + u) / (2 * R - 1) := by
  let D : ℝ := 2 * R - 1
  have hD : D ≠ 0 := by
    dsimp [D]
    exact hden
  have hnum :
      (1 / 2) * R - (3 / 8 + u / 4) =
        (D - (1 / 2 + u)) / 4 := by
    dsimp [D]
    ring
  have hden' :
      (1 / 2) * R - 1 / 4 = D / 4 := by
    dsimp [D]
    ring
  rw [hnum, hden']
  dsimp [D]
  field_simp [hden]

/--
Appendix C, Theorem 7, case 2: the split-integral expression equals the paper's
middle closed form.
-/
theorem paper_theorem7_laplacian_case2_integral_ratio
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hleft : xj < a) (hright : a ≤ xi)
    (hx : xj < xi) :
    ((∫ x : ℝ in Set.Iic xj,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) +
      ∫ x in xj..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) /
        (theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a) =
      1 - theorem7LaplacianCase2TailRatio lam xj a := by
  rw [paper_theorem7_laplacian_case2_numerator_integral
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam (le_of_lt hleft) hright hx,
    paper_theorem7_laplacian_case2_denominator_closedForm
      (lam := lam) (xi := xi) (xj := xj) (a := a) (le_of_lt hleft) hright]
  have hsplit :
      Real.exp (-lam * (xi - a)) =
        Real.exp (-lam * (xi - xj)) * Real.exp (lam * (a - xj)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  unfold theorem7LaplacianCase2TailRatio
  let E : ℝ := Real.exp (-lam * (xi - xj))
  let R : ℝ := Real.exp (lam * (a - xj))
  let u : ℝ := lam * (a - xj)
  have hE : E ≠ 0 := by
    dsimp [E]
    exact Real.exp_ne_zero _
  have hden : 2 * R - 1 ≠ 0 := by
    have hpos : 0 < lam * (a - xj) := mul_pos hlam (sub_pos.mpr hleft)
    have hgt : 1 < R := by
      dsimp [R]
      exact Real.one_lt_exp_iff.mpr hpos
    nlinarith
  change (((1 / 2) * (E * R) -
        (3 / 8 + (lam / 4) * (a - xj)) * E) /
        ((1 / 2) * (E * R) - (1 / 4) * E) =
      1 - (1 / 2 + u) / (2 * R - 1))
  have hu : (lam / 4) * (a - xj) = u / 4 := by
    dsimp [u]
    ring
  rw [hu]
  have hsmall : (1 / 2) * R - 1 / 4 ≠ 0 := by
    intro h
    apply hden
    nlinarith
  have hcancel :
      (((1 / 2) * (E * R) - (3 / 8 + u / 4) * E) /
          ((1 / 2) * (E * R) - (1 / 4) * E)) =
        ((1 / 2) * R - (3 / 8 + u / 4)) /
          ((1 / 2) * R - 1 / 4) := by
    field_simp [hE, hsmall]
  exact hcancel.trans (paper_theorem7_laplacian_case2_ratio_algebra hden)

/--
Appendix C, Theorem 7, case 3: the paper's third numerator integral over
`x_i ≤ x ≤ a`.
-/
theorem paper_theorem7_laplacian_case3_third_integral
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi ≤ a) :
    ∫ x in xi..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
      (1 / 2) * (1 - Real.exp (-lam * (a - xi))) -
        (1 / 8) *
          (Real.exp (-lam * (xi - xj)) -
            Real.exp (-lam * (2 * a - xi - xj))) := by
  calc
    ∫ x in xi..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
        ∫ x in xi..a,
          lam / 2 * Real.exp ((lam * xi) + (-lam) * x) -
            lam / 4 * Real.exp ((lam * (xi + xj)) + (-2 * lam) * x) := by
      refine intervalIntegral.integral_congr fun x hxint => ?_
      have hxIcc : x ∈ Set.Icc xi a := by
        simpa [Set.uIcc_of_le ha] using hxint
      have hxi : xi ≤ x := hxIcc.1
      have hxj : xj ≤ x := (le_of_lt hx).trans hxi
      rw [theorem7LaplacePDF_of_mean_le hxi,
        theorem7LaplaceCDFClosedForm_of_mean_le (lam := lam) (μ := xj) hxj]
      calc
        lam / 2 * Real.exp (-lam * (x - xi)) *
            (1 - 1 / 2 * Real.exp (-lam * (x - xj))) =
            lam / 2 * Real.exp (-lam * (x - xi)) -
              lam / 4 *
                (Real.exp (-lam * (x - xi)) *
                  Real.exp (-lam * (x - xj))) := by ring
        _ = lam / 2 * Real.exp ((lam * xi) + (-lam) * x) -
            lam / 4 * Real.exp ((lam * (xi + xj)) + (-2 * lam) * x) := by
          rw [← Real.exp_add]
          have hfirst : -lam * (x - xi) = (lam * xi) + (-lam) * x := by ring
          have hsecond :
              (lam * xi + -lam * x) + -lam * (x - xj) =
                (lam * (xi + xj)) + (-2 * lam) * x := by ring
          rw [hfirst, hsecond]
    _ = (∫ x in xi..a,
          lam / 2 * Real.exp ((lam * xi) + (-lam) * x)) -
        ∫ x in xi..a,
          lam / 4 * Real.exp ((lam * (xi + xj)) + (-2 * lam) * x) := by
      have hInt1 :
          IntervalIntegrable
            (fun x : ℝ => lam / 2 * Real.exp ((lam * xi) + (-lam) * x))
            volume xi a := by
        apply ContinuousOn.intervalIntegrable
        fun_prop
      have hInt2 :
          IntervalIntegrable
            (fun x : ℝ => lam / 4 * Real.exp ((lam * (xi + xj)) + (-2 * lam) * x))
            volume xi a := by
        apply ContinuousOn.intervalIntegrable
        fun_prop
      rw [intervalIntegral.integral_sub hInt1 hInt2]
    _ = (lam / 2 *
          ∫ x in xi..a, Real.exp ((lam * xi) + (-lam) * x)) -
        (lam / 4 *
          ∫ x in xi..a, Real.exp ((lam * (xi + xj)) + (-2 * lam) * x)) := by
      have hA :
          (∫ x in xi..a,
            lam / 2 * Real.exp ((lam * xi) + (-lam) * x)) =
            lam / 2 *
              ∫ x in xi..a, Real.exp ((lam * xi) + (-lam) * x) := by
        rw [intervalIntegral.integral_const_mul]
      have hB :
          (∫ x in xi..a,
            lam / 4 * Real.exp ((lam * (xi + xj)) + (-2 * lam) * x)) =
            lam / 4 *
              ∫ x in xi..a, Real.exp ((lam * (xi + xj)) + (-2 * lam) * x) := by
        rw [intervalIntegral.integral_const_mul]
      rw [hA, hB]
    _ = (lam / 2 *
          ((Real.exp ((lam * xi) + (-lam) * a) -
              Real.exp ((lam * xi) + (-lam) * xi)) / (-lam))) -
        (lam / 4 *
          ((Real.exp ((lam * (xi + xj)) + (-2 * lam) * a) -
              Real.exp ((lam * (xi + xj)) + (-2 * lam) * xi)) / (-2 * lam))) := by
      have hEval1 :=
        paper_theorem7_intervalIntegral_exp_affine
          (k := -lam) (β := lam * xi) (l := xi) (u := a) (by linarith : -lam ≠ 0)
      have hEval2 :=
        paper_theorem7_intervalIntegral_exp_affine
          (k := -2 * lam) (β := lam * (xi + xj)) (l := xi) (u := a)
          (by nlinarith [hlam] : -2 * lam ≠ 0)
      rw [hEval1, hEval2]
    _ = (1 / 2) * (1 - Real.exp (-lam * (a - xi))) -
        (1 / 8) *
          (Real.exp (-lam * (xi - xj)) -
            Real.exp (-lam * (2 * a - xi - xj))) := by
      have h1a : (lam * xi) + (-lam) * a = -lam * (a - xi) := by ring
      have h1xi : (lam * xi) + (-lam) * xi = 0 := by ring
      have h2a :
          (lam * (xi + xj)) + (-2 * lam) * a =
            -lam * (2 * a - xi - xj) := by ring
      have h2xi :
          (lam * (xi + xj)) + (-2 * lam) * xi =
            -lam * (xi - xj) := by ring
      rw [h1a, h1xi, h2a, h2xi, Real.exp_zero]
      field_simp [hlam.ne']
      ring

/--
Appendix C, Theorem 7, case 3: the three numerator integrals in (C.3)
combine to the scaled numerator used in the paper's right-tail closed form.
-/
theorem paper_theorem7_laplacian_case3_numerator_integral
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi ≤ a) :
    ((∫ x : ℝ in Set.Iic xj,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) +
      ∫ x in xj..xi,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) +
      ∫ x in xi..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x =
      (1 / 8) *
        theorem7LaplacianCase3Numerator
          (lam * (xi - xj)) (Real.exp (-lam * (a - xi))) := by
  rw [paper_theorem7_laplacian_case2_numerator_integral
      (lam := lam) (xi := xi) (xj := xj) (a := xi)
      hlam (le_of_lt hx) le_rfl hx,
    paper_theorem7_laplacian_case3_third_integral
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx ha]
  have hzero : -lam * (xi - xi) = 0 := by ring
  have hquad :
      Real.exp (-lam * (2 * a - xi - xj)) =
        Real.exp (-lam * (xi - xj)) *
          Real.exp (-lam * (a - xi)) ^ 2 := by
    have harg :
        -lam * (2 * a - xi - xj) =
          -lam * (xi - xj) + (-lam * (a - xi) + -lam * (a - xi)) := by
      ring
    rw [harg, Real.exp_add, Real.exp_add]
    ring
  have hzarg : -(lam * (xi - xj)) = -lam * (xi - xj) := by ring
  rw [hzero, Real.exp_zero, hquad]
  dsimp [theorem7LaplacianCase3Numerator]
  rw [hzarg]
  ring

/--
Appendix C, Theorem 7, case 3: denominator in (C.3), on the region
`x_j < x_i ≤ a`.
-/
theorem paper_theorem7_laplacian_case3_denominator_closedForm
    {lam xi xj a : ℝ} (hx : xj < xi) (ha : xi ≤ a) :
    theorem7LaplaceCDFClosedForm lam xi a *
        theorem7LaplaceCDFClosedForm lam xj a =
      (1 / 4) *
        theorem7LaplacianCase3Denominator
          (lam * (xi - xj)) (Real.exp (-lam * (a - xi))) := by
  have hxj_le_a : xj ≤ a := (le_of_lt hx).trans ha
  rw [theorem7LaplaceCDFClosedForm_of_mean_le (lam := lam) (μ := xi) ha,
    theorem7LaplaceCDFClosedForm_of_mean_le (lam := lam) (μ := xj) hxj_le_a]
  have hsplit :
      Real.exp (-lam * (a - xj)) =
        Real.exp (-lam * (a - xi)) *
          Real.exp (-lam * (xi - xj)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hzarg : -(lam * (xi - xj)) = -lam * (xi - xj) := by ring
  rw [hsplit]
  dsimp [theorem7LaplacianCase3Denominator]
  rw [hzarg]
  ring

/--
Appendix C, Theorem 7, case 3: the split-integral expression in (C.3) equals
one half of the paper's cleared right-tail ratio.  The harmless factor `1/2`
does not affect the derivative sign proved above.
-/
theorem paper_theorem7_laplacian_case3_integral_ratio
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi < a) :
    (((∫ x : ℝ in Set.Iic xj,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) +
      ∫ x in xj..xi,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) +
      ∫ x in xi..a,
        theorem7LaplacePDF lam xi x *
          theorem7LaplaceCDFClosedForm lam xj x) /
        (theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a) =
      (1 / 2) *
        theorem7LaplacianCase3ConditionalProb lam xi xj a := by
  rw [paper_theorem7_laplacian_case3_numerator_integral
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx (le_of_lt ha),
    paper_theorem7_laplacian_case3_denominator_closedForm
      (lam := lam) (xi := xi) (xj := xj) (a := a) hx (le_of_lt ha)]
  let z : ℝ := lam * (xi - xj)
  let r : ℝ := Real.exp (-lam * (a - xi))
  have hz : 0 < z := by
    dsimp [z]
    exact mul_pos hlam (sub_pos.mpr hx)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact le_of_lt (Real.exp_pos _)
  have hr1 : r ≤ 1 := by
    dsimp [r]
    have hneg : -lam * (a - xi) < 0 := by
      have hpos : 0 < lam * (a - xi) := mul_pos hlam (sub_pos.mpr ha)
      linarith
    exact le_of_lt (Real.exp_lt_one_iff.mpr hneg)
  have hden_pos := theorem7LaplacianCase3Denominator_pos hz hr0 hr1
  dsimp [theorem7LaplacianCase3ConditionalProb,
    theorem7LaplacianCase3Ratio, z, r]
  field_simp [hden_pos.ne']
  ring

/-- The integrand in Appendix C, Theorem 7 equation (C.3). -/
noncomputable def theorem7LaplacianPairIntegrand
    (lam xi xj x : ℝ) : ℝ :=
  theorem7LaplacePDF lam xi x * theorem7LaplaceCDFClosedForm lam xj x

/-- Appendix C, Theorem 7 case-1 split-integral ratio. -/
noncomputable def theorem7LaplacianCase1IntegralRatio
    (lam xi xj a : ℝ) : ℝ :=
  (∫ x : ℝ in Set.Iic a,
      theorem7LaplacianPairIntegrand lam xi xj x) /
    (theorem7LaplaceCDFClosedForm lam xi a *
      theorem7LaplaceCDFClosedForm lam xj a)

/-- Appendix C, Theorem 7 case-2 split-integral ratio. -/
noncomputable def theorem7LaplacianCase2IntegralRatio
    (lam xi xj a : ℝ) : ℝ :=
  ((∫ x : ℝ in Set.Iic xj,
      theorem7LaplacianPairIntegrand lam xi xj x) +
    ∫ x in xj..a,
      theorem7LaplacianPairIntegrand lam xi xj x) /
    (theorem7LaplaceCDFClosedForm lam xi a *
      theorem7LaplaceCDFClosedForm lam xj a)

/-- Appendix C, Theorem 7 case-3 split-integral ratio. -/
noncomputable def theorem7LaplacianCase3IntegralRatio
    (lam xi xj a : ℝ) : ℝ :=
  (((∫ x : ℝ in Set.Iic xj,
      theorem7LaplacianPairIntegrand lam xi xj x) +
    ∫ x in xj..xi,
      theorem7LaplacianPairIntegrand lam xi xj x) +
    ∫ x in xi..a,
      theorem7LaplacianPairIntegrand lam xi xj x) /
    (theorem7LaplaceCDFClosedForm lam xi a *
      theorem7LaplaceCDFClosedForm lam xj a)

/--
Appendix C, Theorem 7 case 1: the split-integral ratio is locally constant on
the open region `a < x_j`.
-/
theorem theorem7LaplacianCase1IntegralRatio_hasDerivAt_nonneg
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : a < xj) :
    HasDerivAt
        (fun a => theorem7LaplacianCase1IntegralRatio lam xi xj a) 0 a ∧
      0 ≤ (0 : ℝ) := by
  have hconst : HasDerivAt (fun _ : ℝ => (1 / 2 : ℝ)) 0 a :=
    hasDerivAt_const a (1 / 2 : ℝ)
  have hEq :
      (fun b => theorem7LaplacianCase1IntegralRatio lam xi xj b) =ᶠ[nhds a]
        (fun _ : ℝ => (1 / 2 : ℝ)) := by
    have hnear : ∀ᶠ b in nhds a, b ∈ Set.Iio xj :=
      isOpen_Iio.mem_nhds (show a ∈ Set.Iio xj by exact ha)
    exact hnear.mono fun b hb => by
      unfold theorem7LaplacianCase1IntegralRatio
      unfold theorem7LaplacianPairIntegrand
      exact paper_theorem7_laplacian_case1_integral_ratio
        (lam := lam) (xi := xi) (xj := xj) (a := b) hlam (le_of_lt hb) hx
  exact ⟨hconst.congr_of_eventuallyEq hEq, le_rfl⟩

/--
Appendix C, Theorem 7 case 2: the split-integral ratio has the positive
derivative proved for the paper's middle closed form throughout
`x_j < a < x_i`.
-/
theorem theorem7LaplacianCase2IntegralRatio_hasDerivAt_pos
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi)
    (hleft : xj < a) (hright : a < xi) :
    ∃ d,
      HasDerivAt
        (fun a => theorem7LaplacianCase2IntegralRatio lam xi xj a) d a ∧
        0 < d := by
  obtain ⟨d, hclosed, hdpos⟩ :=
    theorem7LaplacianCase2ConditionalProb_hasDerivAt_pos
      (lam := lam) (xj := xj) (a := a) hlam (sub_pos.mpr hleft)
  have hEq :
      (fun b => theorem7LaplacianCase2IntegralRatio lam xi xj b) =ᶠ[nhds a]
        (fun b => 1 - theorem7LaplacianCase2TailRatio lam xj b) := by
    have hnear : ∀ᶠ b in nhds a, b ∈ Set.Ioo xj xi :=
      isOpen_Ioo.mem_nhds
        (show a ∈ Set.Ioo xj xi by exact ⟨hleft, hright⟩)
    exact hnear.mono fun b hb => by
      unfold theorem7LaplacianCase2IntegralRatio
      unfold theorem7LaplacianPairIntegrand
      exact paper_theorem7_laplacian_case2_integral_ratio
        (lam := lam) (xi := xi) (xj := xj) (a := b)
        hlam hb.1 (le_of_lt hb.2) hx
  exact ⟨d, hclosed.congr_of_eventuallyEq hEq, hdpos⟩

/--
Appendix C, Theorem 7 case 3: the split-integral ratio has positive derivative
throughout `x_i < a`.  The integral ratio is one half of the cleared closed
form, so its derivative is one half of the closed-form derivative.
-/
theorem theorem7LaplacianCase3IntegralRatio_hasDerivAt_pos
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi < a) :
    ∃ d,
      HasDerivAt
        (fun a => theorem7LaplacianCase3IntegralRatio lam xi xj a) d a ∧
        0 < d := by
  obtain ⟨dClosed, hclosed, hdClosedPos⟩ :=
    theorem7LaplacianCase3ConditionalProb_hasDerivAt_pos
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx ha
  have hscaled :
      HasDerivAt
        (fun a => (1 / 2 : ℝ) *
          theorem7LaplacianCase3ConditionalProb lam xi xj a)
        ((1 / 2 : ℝ) * dClosed) a :=
    hclosed.const_mul (1 / 2 : ℝ)
  have hEq :
      (fun b => theorem7LaplacianCase3IntegralRatio lam xi xj b) =ᶠ[nhds a]
        (fun b => (1 / 2 : ℝ) *
          theorem7LaplacianCase3ConditionalProb lam xi xj b) := by
    have hnear : ∀ᶠ b in nhds a, b ∈ Set.Ioi xi :=
      isOpen_Ioi.mem_nhds (show a ∈ Set.Ioi xi by exact ha)
    exact hnear.mono fun b hb => by
      unfold theorem7LaplacianCase3IntegralRatio
      unfold theorem7LaplacianPairIntegrand
      exact paper_theorem7_laplacian_case3_integral_ratio
        (lam := lam) (xi := xi) (xj := xj) (a := b) hlam hx hb
  refine ⟨(1 / 2 : ℝ) * dClosed, ?_, ?_⟩
  · exact hscaled.congr_of_eventuallyEq hEq
  · nlinarith

/--
Appendix C, Theorem 7 at the split-integral layer.  This combines the paper's
three Laplace-integral regions with the derivative signs of the corresponding
closed forms, stated on the interiors of the three regions.
-/
theorem paper_theorem7_laplacian_integralRatio_derivative_cases
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (a < xj →
      HasDerivAt
          (fun a => theorem7LaplacianCase1IntegralRatio lam xi xj a) 0 a ∧
        0 ≤ (0 : ℝ)) ∧
    (xj < a → a < xi →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianCase2IntegralRatio lam xi xj a) d a ∧
          0 < d) ∧
    (xi < a →
      ∃ d,
        HasDerivAt
          (fun a => theorem7LaplacianCase3IntegralRatio lam xi xj a) d a ∧
          0 < d) ∧
    (∃ a d,
      xj < a ∧ a < xi ∧
        HasDerivAt
          (fun a => theorem7LaplacianCase2IntegralRatio lam xi xj a) d a ∧
        0 < d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hleft
    exact theorem7LaplacianCase1IntegralRatio_hasDerivAt_nonneg
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx hleft
  · intro hleft hright
    exact theorem7LaplacianCase2IntegralRatio_hasDerivAt_pos
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx hleft hright
  · intro hright
    exact theorem7LaplacianCase3IntegralRatio_hasDerivAt_pos
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx hright
  · let amid : ℝ := (xj + xi) / 2
    have hleft : xj < amid := by
      dsimp [amid]
      linarith
    have hright : amid < xi := by
      dsimp [amid]
      linarith
    obtain ⟨d, hd, hdpos⟩ :=
      theorem7LaplacianCase2IntegralRatio_hasDerivAt_pos
        (lam := lam) (xi := xi) (xj := xj) (a := amid)
        hlam hx hleft hright
    exact ⟨amid, d, hleft, hright, hd, hdpos⟩

/-! ## Appendix C, Theorem 8 scalar Gaussian/Mills-ratio inequalities -/

/--
Appendix C, Theorem 8, equation (C.10) to the finite-difference bound.

The paper defines `g(t) = (1 + erf(t)) / exp(-t^2)` and, after reducing the
Gaussian derivative sign to (C.9), uses the mean value theorem to show it
suffices to prove `(d/dt) (1 / g(t)) > -sqrt(pi)` everywhere.  This lemma is
that mean-value step for any positive-spacing interval.
-/
theorem paper_theorem8_mills_mvt_step
    {g : ℝ → ℝ} {t δ : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn (fun u => (g u)⁻¹) (Set.Icc t (t + δ)))
    (hderiv :
      ∀ u ∈ Set.Ioo t (t + δ),
        ∃ d,
          HasDerivAt (fun u => (g u)⁻¹) d u ∧
            -Real.sqrt Real.pi < d) :
    (g t)⁻¹ - (g (t + δ))⁻¹ < δ * Real.sqrt Real.pi := by
  let f : ℝ → ℝ := fun u => (g u)⁻¹
  let f' : ℝ → ℝ :=
    fun u =>
      if hu : u ∈ Set.Ioo t (t + δ) then
        Classical.choose (hderiv u hu)
      else
        0
  have htd : t < t + δ := by linarith
  have hderiv' : ∀ u ∈ Set.Ioo t (t + δ), HasDerivAt f (f' u) u := by
    intro u hu
    dsimp [f']
    rw [dif_pos hu]
    exact (Classical.choose_spec (hderiv u hu)).1
  obtain ⟨c, hc, hmean⟩ :=
    exists_hasDerivAt_eq_slope
      (f := f) (f' := f') htd hcont hderiv'
  have hcderiv : -Real.sqrt Real.pi < f' c := by
    dsimp [f']
    rw [dif_pos hc]
    exact (Classical.choose_spec (hderiv c hc)).2
  have hslope :
      -Real.sqrt Real.pi <
        (f (t + δ) - f t) / ((t + δ) - t) := by
    simpa [hmean] using hcderiv
  have hdelta : (t + δ) - t = δ := by ring
  dsimp [f] at hslope ⊢
  rw [hdelta] at hslope
  have hmul : -Real.sqrt Real.pi * δ <
      (g (t + δ))⁻¹ - (g t)⁻¹ := by
    have hmul' := mul_lt_mul_of_pos_right hslope hδ
    rw [div_mul_cancel₀ _ hδ.ne'] at hmul'
    exact hmul'
  nlinarith

/--
Appendix C, Theorem 8, equation (C.9): the Mills-ratio finite-difference bound
implies positivity of the bracketed expression used for the Gaussian derivative
sign.
-/
theorem paper_theorem8_c9_positive_of_mills_mvt
    {g : ℝ → ℝ} {t δ : ℝ} (hδ : 0 < δ) (hgpos : 0 < g t)
    (hcont : ContinuousOn (fun u => (g u)⁻¹) (Set.Icc t (t + δ)))
    (hderiv :
      ∀ u ∈ Set.Ioo t (t + δ),
        ∃ d,
          HasDerivAt (fun u => (g u)⁻¹) d u ∧
            -Real.sqrt Real.pi < d) :
    0 < g t * (δ * Real.sqrt Real.pi + (g (t + δ))⁻¹) - 1 := by
  have hdiff :=
    paper_theorem8_mills_mvt_step
      (g := g) (t := t) (δ := δ) hδ hcont hderiv
  have hmain :
      (g t)⁻¹ < δ * Real.sqrt Real.pi + (g (t + δ))⁻¹ := by
    linarith
  have hmul :=
    mul_lt_mul_of_pos_left hmain hgpos
  have hcancel : g t * (g t)⁻¹ = 1 := by
    rw [mul_inv_cancel₀ hgpos.ne']
  nlinarith

/--
Appendix C, Theorem 8 positivity template.

This formalizes the paper's criterion used after (C.6): if a real function has
limit `0` at `-∞` and is strictly increasing, then it is positive everywhere.
-/
theorem paper_theorem8_positive_of_strictMono_tendsto_atBot_zero
    {F : ℝ → ℝ} (hmono : StrictMono F)
    (hlim : Filter.Tendsto F Filter.atBot (nhds 0)) (t : ℝ) :
    0 < F t := by
  let y : ℝ := t - 1
  have hyt : y < t := by
    dsimp [y]
    linarith
  have hy_nonneg : 0 ≤ F y := by
    by_contra hnot
    have hyneg : F y < 0 := lt_of_not_ge hnot
    have hlt : ∀ᶠ z in Filter.atBot, F z < F y :=
      (Filter.eventually_lt_atBot y).mono fun z hz => hmono hz
    have hgt : ∀ᶠ z in Filter.atBot, F y < F z :=
      hlim (isOpen_Ioi.mem_nhds (show (0 : ℝ) ∈ Set.Ioi (F y) by exact hyneg))
    obtain ⟨z, hzlt, hzgt⟩ := (hlt.and hgt).exists
    linarith
  have hy_lt : F y < F t := hmono hyt
  linarith

/--
Appendix C, Theorem 8 positivity template in the derivative form used in the
paper: differentiability with everywhere-positive derivative gives strict
monotonicity, and the `-∞` limit then gives positivity.
-/
theorem paper_theorem8_positive_of_deriv_pos_tendsto_atBot_zero
    {F F' : ℝ → ℝ}
    (hderiv : ∀ t, HasDerivAt F (F' t) t)
    (hpos : ∀ t, 0 < F' t)
    (hlim : Filter.Tendsto F Filter.atBot (nhds 0)) :
    ∀ t, 0 < F t := by
  intro t
  exact paper_theorem8_positive_of_strictMono_tendsto_atBot_zero
    (strictMono_of_hasDerivAt_pos hderiv hpos) hlim t

/--
The bracket in Appendix C, Theorem 8 equation (C.9), after writing
`g(t) = (1 + erf(t)) / exp(-t^2)`.
-/
noncomputable def theorem8GaussianC9Bracket (g : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  g t * (δ * Real.sqrt Real.pi + (g (t + δ))⁻¹) - 1

/--
Appendix C, Theorem 8 paper definition
`g(t) = (1 + erf(t)) / exp(-t^2)`.
-/
noncomputable def theorem8GaussianG (erf : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 + erf t) / Real.exp (-(t ^ 2))

/--
Appendix C, Theorem 8: the standard error function normalization used in the
Gaussian calculation, written directly as the paper's interval integral.
-/
noncomputable def theorem8Erf (t : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) *
    ∫ x : ℝ in (0 : ℝ)..t, Real.exp (-(x ^ 2))

/--
Appendix C, Theorem 8: derivative of the paper's concrete `erf` definition.

This discharges the standard `erf` derivative assumption for wrappers that use
`theorem8Erf`.
-/
theorem theorem8Erf_hasDerivAt (t : ℝ) :
    HasDerivAt theorem8Erf
      ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t := by
  unfold theorem8Erf
  have hcont : Continuous fun x : ℝ => Real.exp (-(x ^ 2)) :=
    Real.continuous_exp.comp ((continuous_id.pow 2).neg)
  simpa [mul_assoc] using
    (hcont.integral_hasStrictDerivAt (0 : ℝ) t).hasDerivAt.const_mul
      (2 / Real.sqrt Real.pi)

/-- Appendix C, Theorem 8: continuity of the concrete `erf` integral. -/
theorem theorem8Erf_continuous : Continuous theorem8Erf :=
  continuous_iff_continuousAt.mpr fun t => (theorem8Erf_hasDerivAt t).continuousAt

/-- Appendix C, Theorem 8: the left half-Gaussian integral used by `erf(-∞)=-1`. -/
theorem theorem8Gaussian_integral_Iic_zero :
    (∫ x : ℝ in Set.Iic (0 : ℝ), Real.exp (-(x ^ 2))) =
      Real.sqrt Real.pi / 2 := by
  have hsymm :
      (∫ x : ℝ in Set.Iic (0 : ℝ), Real.exp (-(x ^ 2))) =
        ∫ x : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(x ^ 2)) := by
    have hcomp :=
      integral_comp_neg_Iic (c := (0 : ℝ))
        (f := fun x : ℝ => Real.exp (-(x ^ 2)))
    simpa [neg_sq] using hcomp
  rw [hsymm]
  simpa [one_mul, div_one] using (integral_gaussian_Ioi (1 : ℝ))

/--
Appendix C, Theorem 8: the concrete interval-integral definition of `erf`
rewrites the left Gaussian tail as
`∫_{-∞}^t exp(-x^2) dx = sqrt(pi)/2 * (1 + erf(t))`.
-/
theorem theorem8Gaussian_integral_Iic_eq_erf (t : ℝ) :
    (∫ x : ℝ in Set.Iic t, Real.exp (-(x ^ 2))) =
      Real.sqrt Real.pi / 2 * (1 + theorem8Erf t) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2))
  have hfi0 : IntegrableOn f (Set.Iic (0 : ℝ)) := by
    simpa [f, one_mul] using
      (integrable_exp_neg_mul_sq (show 0 < (1 : ℝ) by norm_num)).integrableOn
  have hfit : IntegrableOn f (Set.Iic t) := by
    simpa [f, one_mul] using
      (integrable_exp_neg_mul_sq (show 0 < (1 : ℝ) by norm_num)).integrableOn
  have hsub :
      (∫ x : ℝ in Set.Iic t, f x) -
          ∫ x : ℝ in Set.Iic (0 : ℝ), f x =
        ∫ x : ℝ in (0 : ℝ)..t, f x := by
    simpa using
      (intervalIntegral.integral_Iic_sub_Iic
        (f := f) (a := (0 : ℝ)) (b := t) hfi0 hfit)
  have hI :
      (∫ x : ℝ in Set.Iic t, f x) =
        Real.sqrt Real.pi / 2 + ∫ x : ℝ in (0 : ℝ)..t, f x := by
    rw [show (∫ x : ℝ in Set.Iic (0 : ℝ), f x) =
        Real.sqrt Real.pi / 2 by
      simpa [f] using theorem8Gaussian_integral_Iic_zero] at hsub
    linarith
  rw [hI]
  unfold theorem8Erf
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
    Real.sqrt_ne_zero'.mpr Real.pi_pos
  field_simp [f, hsqrt_ne]
  ring

/--
Appendix C, Theorem 8: translation of a left-half-line integral.  This is the
change of variables `u = x - μ` used when the Gaussian density with mean `μ`
is rewritten in centered coordinates.
-/
theorem theorem8_integral_Iic_sub_eq_integral_Iic
    (f : ℝ → ℝ) (a μ : ℝ) :
    (∫ x : ℝ in Set.Iic a, f (x - μ)) =
      ∫ x : ℝ in Set.Iic (a - μ), f x := by
  have A : MeasurableEmbedding (fun x : ℝ => x + μ) :=
    (Homeomorph.addRight μ).isClosedEmbedding.measurableEmbedding
  calc
    (∫ y : ℝ in Set.Iic a, f (y - μ)) =
        ∫ y : ℝ in Set.Iic a, f (y - μ) ∂Measure.map (fun x : ℝ => x + μ) volume := by
          rw [map_add_right_eq_self]
    _ = ∫ x : ℝ in (fun x : ℝ => x + μ) ⁻¹' Set.Iic a, f ((x + μ) - μ) := by
          exact A.setIntegral_map (g := fun y : ℝ => f (y - μ)) (s := Set.Iic a)
    _ = ∫ x : ℝ in Set.Iic (a - μ), f x := by
          have hpre :
              (fun x : ℝ => x + μ) ⁻¹' Set.Iic a = Set.Iic (a - μ) := by
            ext x
            constructor <;> intro hx
            · change x + μ ≤ a at hx
              change x ≤ a - μ
              linarith
            · change x + μ ≤ a
              change x ≤ a - μ at hx
              linarith
          simp [hpre]

/--
Appendix C, Theorem 8: `1 + erf(t)` tends to `0` as `t -> -∞` for the
paper's concrete interval-integral `erf`.
-/
theorem theorem8Erf_tendsto_one_add_atBot_zero :
    Filter.Tendsto (fun t => 1 + theorem8Erf t) Filter.atBot (nhds 0) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2))
  have hfi : IntegrableOn f (Set.Iic (0 : ℝ)) := by
    simpa [f, one_mul] using
      (integrable_exp_neg_mul_sq (show 0 < (1 : ℝ) by norm_num)).integrableOn
  have ht_left :
      Filter.Tendsto (fun t => ∫ x : ℝ in t..(0 : ℝ), f x)
        Filter.atBot
        (nhds (∫ x : ℝ in Set.Iic (0 : ℝ), f x)) :=
    intervalIntegral_tendsto_integral_Iic
      (f := f) (b := (0 : ℝ)) hfi Filter.tendsto_id
  have ht_interval :
      Filter.Tendsto (fun t => ∫ x : ℝ in (0 : ℝ)..t, f x)
        Filter.atBot
        (nhds (-(∫ x : ℝ in Set.Iic (0 : ℝ), f x))) := by
    refine ht_left.neg.congr' ?_
    filter_upwards with t
    rw [intervalIntegral.integral_symm]
    abel
  have hscaled :
      Filter.Tendsto
        (fun t => (2 / Real.sqrt Real.pi) *
          ∫ x : ℝ in (0 : ℝ)..t, f x)
        Filter.atBot (nhds (-1)) := by
    have hconst :
        (2 / Real.sqrt Real.pi) *
            (-(∫ x : ℝ in Set.Iic (0 : ℝ), f x)) = -1 := by
      rw [show (∫ x : ℝ in Set.Iic (0 : ℝ), f x) =
          Real.sqrt Real.pi / 2 by
        simpa [f] using theorem8Gaussian_integral_Iic_zero]
      have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
        Real.sqrt_ne_zero'.mpr Real.pi_pos
      field_simp [hsqrt_ne]
    simpa [hconst] using ht_interval.const_mul (2 / Real.sqrt Real.pi)
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atBot (nhds 1) :=
    tendsto_const_nhds
  simpa [theorem8Erf, f] using hone.add hscaled

/-- Appendix C, Theorem 8: positivity of `1 + erf(t)` for the concrete `erf`. -/
theorem theorem8Erf_one_add_pos (t : ℝ) :
    0 < 1 + theorem8Erf t := by
  have hderiv :
      ∀ t,
        HasDerivAt (fun u => 1 + theorem8Erf u)
          ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t := by
    intro t
    simpa using (theorem8Erf_hasDerivAt t).const_add (1 : ℝ)
  have hpos :
      ∀ t, 0 < (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) := by
    intro t
    positivity
  exact paper_theorem8_positive_of_deriv_pos_tendsto_atBot_zero
    hderiv hpos theorem8Erf_tendsto_one_add_atBot_zero t

/-- Appendix C, Theorem 8: the concrete interval-integral `erf` is strictly increasing. -/
theorem theorem8Erf_strictMono : StrictMono theorem8Erf := by
  refine strictMono_of_hasDerivAt_pos theorem8Erf_hasDerivAt ?_
  intro t
  positivity

/--
Appendix C, Theorem 8: on the left half-line used by `J(t)`, the shifted
concrete `erf` factor is bounded.  This is the bounded-factor input needed to
show integrability of the paper's `J` integrand.
-/
theorem theorem8Erf_boundedOn_left_shift (δ : ℝ) :
    ∀ x ∈ Set.Iic (0 : ℝ),
      ‖theorem8Erf (x + δ)‖ ≤ max 1 ‖theorem8Erf δ‖ := by
  intro x hx
  have hC1 : (1 : ℝ) ≤ max 1 ‖theorem8Erf δ‖ := le_max_left _ _
  have hCδ : ‖theorem8Erf δ‖ ≤ max 1 ‖theorem8Erf δ‖ := le_max_right _ _
  have hlower : -1 < theorem8Erf (x + δ) := by
    have h := theorem8Erf_one_add_pos (x + δ)
    linarith
  have hx0 : x ≤ 0 := by
    simpa using hx
  have hupper : theorem8Erf (x + δ) ≤ theorem8Erf δ := by
    exact theorem8Erf_strictMono.monotone (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact abs_le.mpr
    ⟨(neg_le_neg hC1).trans (le_of_lt hlower),
      hupper.trans ((le_abs_self _).trans hCδ)⟩

/--
Appendix C, Theorem 8 rational term appearing in equation (C.6), before
subtracting `(1 + erf(t))` and the integral term.
-/
noncomputable def theorem8GaussianC6RationalTerm (erf : ℝ → ℝ)
    (δ t : ℝ) : ℝ :=
  ((1 + erf t) * (1 + erf (t + δ)) ^ 2 * Real.exp (-(t ^ 2))) /
    ((1 + erf t) * Real.exp (-((t + δ) ^ 2)) +
      (1 + erf (t + δ)) * Real.exp (-(t ^ 2)))

/--
Appendix C, Theorem 8, equation (C.7): the rational term is nonnegative when
the two Gaussian CDF factors are nonnegative.
-/
theorem theorem8GaussianC6RationalTerm_nonneg
    {erf : ℝ → ℝ} {δ t : ℝ}
    (ht : 0 ≤ 1 + erf t) (htδ : 0 ≤ 1 + erf (t + δ)) :
    0 ≤ theorem8GaussianC6RationalTerm erf δ t := by
  unfold theorem8GaussianC6RationalTerm
  have hnum :
      0 ≤ (1 + erf t) * (1 + erf (t + δ)) ^ 2 * Real.exp (-(t ^ 2)) := by
    positivity
  have hden :
      0 ≤ (1 + erf t) * Real.exp (-((t + δ) ^ 2)) +
          (1 + erf (t + δ)) * Real.exp (-(t ^ 2)) := by
    positivity
  exact div_nonneg hnum hden

/--
Appendix C, Theorem 8, equation (C.7): the paper's upper bound on the rational
term by `(1 + erf(t)) * (1 + erf(t+δ))`.
-/
theorem theorem8GaussianC6RationalTerm_le_product
    {erf : ℝ → ℝ} {δ t : ℝ}
    (ht : 0 < 1 + erf t) (htδ : 0 < 1 + erf (t + δ)) :
    theorem8GaussianC6RationalTerm erf δ t ≤
      (1 + erf t) * (1 + erf (t + δ)) := by
  unfold theorem8GaussianC6RationalTerm
  set A : ℝ := 1 + erf t
  set B : ℝ := 1 + erf (t + δ)
  set Et : ℝ := Real.exp (-(t ^ 2))
  set Ed : ℝ := Real.exp (-((t + δ) ^ 2))
  have hA : 0 < A := by simpa [A] using ht
  have hB : 0 < B := by simpa [B] using htδ
  have hEt : 0 < Et := by simpa [Et] using Real.exp_pos (-(t ^ 2))
  have hEd : 0 < Ed := by simpa [Ed] using Real.exp_pos (-((t + δ) ^ 2))
  have hden : 0 < A * Ed + B * Et :=
    add_pos (mul_pos hA hEd) (mul_pos hB hEt)
  rw [div_le_iff₀ hden]
  have hextra : 0 ≤ A * A * B * Ed := by positivity
  calc
    A * B ^ 2 * Et ≤ A * B ^ 2 * Et + A * A * B * Ed := by linarith
    _ = A * B * (A * Ed + B * Et) := by ring

/-- Appendix C, Theorem 8: shifting the concrete `erf` left-tail limit. -/
theorem theorem8Erf_tendsto_one_add_atBot_zero_shift (δ : ℝ) :
    Filter.Tendsto (fun t => 1 + theorem8Erf (t + δ))
      Filter.atBot (nhds 0) := by
  have hshift :
      Filter.Tendsto (fun t : ℝ => t + δ) Filter.atBot Filter.atBot := by
    rw [Filter.tendsto_atBot_atBot]
    intro b
    exact ⟨b - δ, fun a ha => by linarith⟩
  exact theorem8Erf_tendsto_one_add_atBot_zero.comp hshift

/--
Appendix C, Theorem 8, equation (C.7): for the concrete `erf`, the rational
term in C.6 tends to zero as `t -> -∞`.
-/
theorem theorem8GaussianC6RationalTerm_tendsto_atBot_zero_concrete
    (δ : ℝ) :
    Filter.Tendsto
      (fun t => theorem8GaussianC6RationalTerm theorem8Erf δ t)
      Filter.atBot (nhds 0) := by
  have hprod :
      Filter.Tendsto
        (fun t => (1 + theorem8Erf t) * (1 + theorem8Erf (t + δ)))
        Filter.atBot (nhds 0) := by
    simpa using
      theorem8Erf_tendsto_one_add_atBot_zero.mul
        (theorem8Erf_tendsto_one_add_atBot_zero_shift δ)
  refine squeeze_zero ?_ ?_ hprod
  · intro t
    exact theorem8GaussianC6RationalTerm_nonneg
      (le_of_lt (theorem8Erf_one_add_pos t))
      (le_of_lt (theorem8Erf_one_add_pos (t + δ)))
  · intro t
    exact theorem8GaussianC6RationalTerm_le_product
      (theorem8Erf_one_add_pos t)
      (theorem8Erf_one_add_pos (t + δ))

/--
Appendix C, Theorem 8: the paper's improper integral
`J(t) = ∫_{-∞}^t exp(-x^2) erf(x + δ) dx`, represented as a left half-line
set integral.
-/
noncomputable def theorem8GaussianJ (erf : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  ∫ x : ℝ in Set.Iic t, Real.exp (-(x ^ 2)) * erf (x + δ)

/--
Generic left-tail lemma used for Appendix C, Theorem 8: if a real integrand is
integrable on `(-∞, 0]`, then its left half-line integral tends to zero as the
right endpoint tends to `-∞`.
-/
theorem integral_Iic_tendsto_atBot_zero_of_integrableOn_Iic_zero
    {f : ℝ → ℝ} (hfi : IntegrableOn f (Set.Iic (0 : ℝ))) :
    Filter.Tendsto (fun t => ∫ x : ℝ in Set.Iic t, f x)
      Filter.atBot (nhds 0) := by
  have ht_interval :
      Filter.Tendsto (fun t => ∫ x : ℝ in t..(0 : ℝ), f x)
        Filter.atBot
        (nhds (∫ x : ℝ in Set.Iic (0 : ℝ), f x)) :=
    intervalIntegral_tendsto_integral_Iic
      (f := f) (b := (0 : ℝ)) hfi Filter.tendsto_id
  have htail_expr :
      Filter.Tendsto
        (fun t => (∫ x : ℝ in Set.Iic (0 : ℝ), f x) -
          ∫ x : ℝ in t..(0 : ℝ), f x)
        Filter.atBot (nhds 0) := by
    have hconst :
        Filter.Tendsto
          (fun _ : ℝ => ∫ x : ℝ in Set.Iic (0 : ℝ), f x)
          Filter.atBot
          (nhds (∫ x : ℝ in Set.Iic (0 : ℝ), f x)) :=
      tendsto_const_nhds
    simpa using hconst.sub ht_interval
  refine htail_expr.congr' ?_
  filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with t ht
  have hfi_t : IntegrableOn f (Set.Iic t) :=
    hfi.mono_set (Set.Iic_subset_Iic.mpr ht)
  have hsub :=
    intervalIntegral.integral_Iic_sub_Iic
      (f := f) (a := t) (b := (0 : ℝ)) hfi_t hfi
  linarith

/--
Appendix C, Theorem 8: the paper's `J(t)` tends to zero at `-∞` once its
integrand is known to be integrable on the left half-line.
-/
theorem theorem8GaussianJ_tendsto_atBot_zero_of_integrableOn
    {erf : ℝ → ℝ} {δ : ℝ}
    (hJ_integrable :
      IntegrableOn
        (fun x : ℝ => Real.exp (-(x ^ 2)) * erf (x + δ))
        (Set.Iic (0 : ℝ))) :
    Filter.Tendsto (theorem8GaussianJ erf δ) Filter.atBot (nhds 0) := by
  simpa [theorem8GaussianJ] using
    integral_Iic_tendsto_atBot_zero_of_integrableOn_Iic_zero
      (f := fun x : ℝ => Real.exp (-(x ^ 2)) * erf (x + δ))
      hJ_integrable

/--
Appendix C, Theorem 8: integrability of the concrete `J` integrand on the
left half-line.  The Gaussian factor is integrable, and the shifted concrete
`erf` factor is bounded there by `theorem8Erf_boundedOn_left_shift`.
-/
theorem theorem8GaussianJ_integrableOn_concrete (δ : ℝ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ))
      (Set.Iic (0 : ℝ)) := by
  have hgauss :
      IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2))) (Set.Iic (0 : ℝ)) := by
    simpa [one_mul] using
      (integrable_exp_neg_mul_sq (show 0 < (1 : ℝ) by norm_num)).integrableOn
  exact hgauss.mul_bdd
    ((theorem8Erf_continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Iic
      (theorem8Erf_boundedOn_left_shift δ))

/--
Appendix C, Theorem 8: integrability of the concrete `J` integrand on any
left half-line.  This extends the left-tail integrability proof by adding only
a compact interval when the endpoint is positive.
-/
theorem theorem8GaussianJ_integrableOn_Iic_concrete (δ a : ℝ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ))
      (Set.Iic a) := by
  by_cases ha : a ≤ 0
  · exact (theorem8GaussianJ_integrableOn_concrete δ).mono_set
      (Set.Iic_subset_Iic.mpr ha)
  · have h0a : 0 ≤ a := le_of_not_ge ha
    have hcont :
        Continuous
          (fun x : ℝ => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ)) :=
      (Real.continuous_exp.comp ((continuous_id.pow 2).neg)).mul
        (theorem8Erf_continuous.comp (continuous_id.add continuous_const))
    have hcompact :
        IntegrableOn
          (fun x : ℝ => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ))
          (Set.Icc (0 : ℝ) a) :=
      hcont.continuousOn.integrableOn_compact isCompact_Icc
    rw [← Set.Iic_union_Icc_eq_Iic h0a]
    exact (theorem8GaussianJ_integrableOn_concrete δ).union hcompact

/--
Appendix C, Theorem 8: rewriting the concrete `J(t)` left-half-line integral
as a constant left tail plus an ordinary interval integral.
-/
theorem theorem8GaussianJ_eq_Iic_zero_add_interval (δ t : ℝ) :
    theorem8GaussianJ theorem8Erf δ t =
      (∫ x : ℝ in Set.Iic (0 : ℝ),
        Real.exp (-(x ^ 2)) * theorem8Erf (x + δ)) +
        ∫ x : ℝ in (0 : ℝ)..t,
          Real.exp (-(x ^ 2)) * theorem8Erf (x + δ) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ)
  have hfi0 : IntegrableOn f (Set.Iic (0 : ℝ)) := by
    simpa [f] using theorem8GaussianJ_integrableOn_concrete δ
  have hfit : IntegrableOn f (Set.Iic t) := by
    simpa [f] using theorem8GaussianJ_integrableOn_Iic_concrete δ t
  have hsub :
      (∫ x : ℝ in Set.Iic t, f x) -
          ∫ x : ℝ in Set.Iic (0 : ℝ), f x =
        ∫ x : ℝ in (0 : ℝ)..t, f x := by
    simpa using
      (intervalIntegral.integral_Iic_sub_Iic
        (f := f) (a := (0 : ℝ)) (b := t) hfi0 hfit)
  unfold theorem8GaussianJ
  dsimp [f] at hsub ⊢
  linarith

/--
Appendix C, Theorem 8: derivative of the concrete `J(t)` integral.
-/
theorem theorem8GaussianJ_hasDerivAt_concrete (δ t : ℝ) :
    HasDerivAt (theorem8GaussianJ theorem8Erf δ)
      (Real.exp (-(t ^ 2)) * theorem8Erf (t + δ)) t := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ)
  have hcont : Continuous f :=
    (Real.continuous_exp.comp ((continuous_id.pow 2).neg)).mul
      (theorem8Erf_continuous.comp (continuous_id.add continuous_const))
  have hderiv :
      HasDerivAt
        (fun u : ℝ =>
          (∫ x : ℝ in Set.Iic (0 : ℝ), f x) +
            ∫ x : ℝ in (0 : ℝ)..u, f x)
        (f t) t := by
    exact (hcont.integral_hasStrictDerivAt (0 : ℝ) t).hasDerivAt.const_add
      (∫ x : ℝ in Set.Iic (0 : ℝ), f x)
  refine hderiv.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun u => by
    simp [f, theorem8GaussianJ_eq_Iic_zero_add_interval]

/--
Appendix C, Theorem 8 left-hand side of equation (C.6).  The argument `J`
stands for the paper's integral
`J(t) = ∫_{-∞}^t exp(-x^2) erf(x + δ) dx`.
-/
noncomputable def theorem8GaussianC6LHS (erf J : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  theorem8GaussianC6RationalTerm erf δ t -
    (1 + erf t) - (2 / Real.sqrt Real.pi) * J t

/--
Appendix C, Theorem 8 positive prefactor factored out of the derivative in
equation (C.8) to obtain the C.9 bracket.

The paper's displayed prefactor has a typographical mismatch with the C.9
bracket.  The positive factor below is the algebraically correct factor whose
product with `theorem8GaussianC9Bracket` equals the C.8 derivative.
-/
noncomputable def theorem8GaussianC8PositiveFactor (erf : ℝ → ℝ)
    (δ t : ℝ) : ℝ :=
  (2 * (1 + erf t) * (1 + erf (t + δ)) ^ 2 * Real.exp ((t + δ) ^ 2)) /
    (Real.sqrt Real.pi *
      (((erf t + 1) * Real.exp (t ^ 2) +
        (erf (t + δ) + 1) * Real.exp ((t + δ) ^ 2)) ^ 2))

/-- Appendix C, Theorem 8: positivity of the paper's `g(t)`. -/
theorem theorem8GaussianG_pos
    {erf : ℝ → ℝ} {t : ℝ} (hone : 0 < 1 + erf t) :
    0 < theorem8GaussianG erf t := by
  unfold theorem8GaussianG
  positivity

/-- Appendix C, Theorem 8: continuity of the paper's `g(t)`. -/
theorem theorem8GaussianG_continuous
    {erf : ℝ → ℝ} (herf : Continuous erf) :
    Continuous (theorem8GaussianG erf) := by
  unfold theorem8GaussianG
  have hnum : Continuous fun t : ℝ => 1 + erf t :=
    continuous_const.add herf
  have hden : Continuous fun t : ℝ => Real.exp (-(t ^ 2)) :=
    Real.continuous_exp.comp ((continuous_id.pow 2).neg)
  exact hnum.div hden (fun t => (Real.exp_pos (-(t ^ 2))).ne')

/--
Appendix C, Theorem 8: continuity of `1 / g` on any interval, derived from
continuity of `erf` and positivity of `1 + erf`.
-/
theorem theorem8GaussianG_inv_continuousOn
    {erf : ℝ → ℝ} (herf : Continuous erf)
    (hone : ∀ t, 0 < 1 + erf t) (s : Set ℝ) :
    ContinuousOn (fun u => (theorem8GaussianG erf u)⁻¹) s := by
  exact (theorem8GaussianG_continuous herf).continuousOn.inv₀
    (fun u _hu => (theorem8GaussianG_pos (hone u)).ne')

/-- Appendix C, Theorem 8: the usual derivative formula for `erf` implies continuity. -/
theorem theorem8Erf_continuous_of_hasDerivAt
    {erf : ℝ → ℝ}
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t) :
    Continuous erf :=
  continuous_iff_continuousAt.mpr fun t => (herf_deriv t).continuousAt

/--
Appendix C, Theorem 8: positivity of `1 + erf(t)` from the standard derivative
formula and the left-tail limit `1 + erf(t) -> 0` as `t -> -∞`.
-/
theorem theorem8_one_add_erf_pos_of_deriv_tendsto_atBot
    {erf : ℝ → ℝ}
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (hlim : Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0)) :
    ∀ t, 0 < 1 + erf t := by
  have hderiv :
      ∀ t,
        HasDerivAt (fun u => 1 + erf u)
          ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t := by
    intro t
    simpa using (herf_deriv t).const_add (1 : ℝ)
  have hpos :
      ∀ t, 0 < (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) := by
    intro t
    positivity
  exact paper_theorem8_positive_of_deriv_pos_tendsto_atBot_zero
    hderiv hpos hlim

/--
Appendix C, Theorem 8, limit of the C.6 expression from the three component
limits used in the paper after equation (C.7).
-/
theorem theorem8GaussianC6LHS_tendsto_atBot_zero
    {erf J : ℝ → ℝ} {δ : ℝ}
    (hratio :
      Filter.Tendsto (fun t => theorem8GaussianC6RationalTerm erf δ t)
        Filter.atBot (nhds 0))
    (herf_tail : Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0))
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0)) :
    Filter.Tendsto (fun t => theorem8GaussianC6LHS erf J δ t)
      Filter.atBot (nhds 0) := by
  have hJ_scaled :
      Filter.Tendsto (fun t => (2 / Real.sqrt Real.pi) * J t)
        Filter.atBot (nhds 0) := by
    simpa using hJ_tail.const_mul (2 / Real.sqrt Real.pi)
  simpa [theorem8GaussianC6LHS, sub_eq_add_neg] using
    (hratio.sub herf_tail).sub hJ_scaled

/--
Appendix C, Theorem 8: the prefactor removed from equation (C.8) is positive
whenever the two Gaussian CDF terms `1 + erf(t)` and `1 + erf(t + δ)` are
positive.
-/
theorem theorem8GaussianC8PositiveFactor_pos
    {erf : ℝ → ℝ} {δ t : ℝ}
    (ht : 0 < 1 + erf t) (htδ : 0 < 1 + erf (t + δ)) :
    0 < theorem8GaussianC8PositiveFactor erf δ t := by
  unfold theorem8GaussianC8PositiveFactor
  have ht' : 0 < erf t + 1 := by linarith
  have htδ' : 0 < erf (t + δ) + 1 := by linarith
  have hsum :
      0 <
        (erf t + 1) * Real.exp (t ^ 2) +
          (erf (t + δ) + 1) * Real.exp ((t + δ) ^ 2) :=
    add_pos (mul_pos ht' (Real.exp_pos _)) (mul_pos htδ' (Real.exp_pos _))
  refine div_pos ?_ ?_
  · positivity
  · exact mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (sq_pos_of_ne_zero hsum.ne')

/--
Appendix C, Theorem 8, C.8 algebraic factorization after abbreviating
`a=1+erf(t)`, `b=1+erf(t+δ)`, `p=exp(-t^2)`, and
`q=exp(-(t+δ)^2)`.  This is the pure real-field identity that turns the
explicit derivative of the C.6 rational term into the corrected positive
factor times the C.9 bracket.
-/
theorem theorem8GaussianC8_algebra
    (a b p q s δ t : ℝ) (hs : s ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hb : b ≠ 0) (hden : a * q + b * p ≠ 0) :
    ((((2 / s * p * b ^ 2 * p + a * (2 * b * (2 / s * q)) * p +
        a * b ^ 2 * (-(2 * t * p))) * (a * q + b * p) -
      (a * b ^ 2 * p) *
        ((2 / s * p) * q + a * (-(2 * (t + δ) * q)) +
          (2 / s * q) * p + b * (-(2 * t * p)))) /
      (a * q + b * p) ^ 2) - (2 / s) * p * b) =
      ((2 * a * b ^ 2 * q⁻¹) /
        (s * ((a * p⁻¹ + b * q⁻¹) ^ 2))) *
        (a / p * (δ * s + (b / q)⁻¹) - 1) := by
  have hden_sq : (a * q + b * p) ^ 2 ≠ 0 := pow_ne_zero 2 hden
  field_simp [hs, hp, hq, hb, hden, hden_sq]
  apply (mul_right_inj' hden_sq).mp
  field_simp [hden_sq]
  ring

/--
Appendix C, Theorem 8: Mills ratio as used in the paper,
`R(t) = exp(t^2 / 2) * ∫_t^∞ exp(-x^2 / 2) dx`.
-/
noncomputable def theorem8MillsRatio (t : ℝ) : ℝ :=
  Real.exp (t ^ 2 / 2) *
    ∫ x : ℝ in Set.Ioi t, Real.exp (-(x ^ 2) / 2)

/-- The Gaussian tail integral inside the Mills ratio. -/
noncomputable def theorem8MillsTail (t : ℝ) : ℝ :=
  ∫ x : ℝ in Set.Ioi t, Real.exp (-(x ^ 2) / 2)

/-- Appendix C, Theorem 8: derivative of the Gaussian tail in Mills ratio. -/
theorem theorem8MillsTail_hasDerivAt (t : ℝ) :
    HasDerivAt theorem8MillsTail (-(Real.exp (-(t ^ 2) / 2))) t := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2)
  have hfint : Integrable f := by
    have hbase := integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by norm_num)
    convert hbase using 1
    ext x
    dsimp [f]
    ring_nf
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hIic_eq (u : ℝ) :
      (∫ x : ℝ in Set.Iic u, f x) =
        (∫ x : ℝ in Set.Iic (0 : ℝ), f x) + ∫ x : ℝ in (0 : ℝ)..u, f x := by
    have hfi0 : IntegrableOn f (Set.Iic (0 : ℝ)) := hfint.integrableOn
    have hfiu : IntegrableOn f (Set.Iic u) := hfint.integrableOn
    have hsub := intervalIntegral.integral_Iic_sub_Iic
      (f := f) (a := (0 : ℝ)) (b := u) hfi0 hfiu
    linarith
  have hIic_deriv : HasDerivAt
      (fun u : ℝ => ∫ x : ℝ in Set.Iic u, f x) (f t) t := by
    have hderiv : HasDerivAt
        (fun u : ℝ =>
          (∫ x : ℝ in Set.Iic (0 : ℝ), f x) + ∫ x : ℝ in (0 : ℝ)..u, f x)
        (f t) t := by
      exact (hcont.integral_hasStrictDerivAt (0 : ℝ) t).hasDerivAt.const_add
        (∫ x : ℝ in Set.Iic (0 : ℝ), f x)
    refine hderiv.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun u => hIic_eq u
  have htail_eq : (fun u : ℝ => theorem8MillsTail u) =ᶠ[nhds t]
      (fun u : ℝ => (∫ x : ℝ, f x) - ∫ x : ℝ in Set.Iic u, f x) := by
    exact Filter.Eventually.of_forall fun u => by
      have hsum := intervalIntegral.integral_Iic_add_Ioi
        (f := f) (b := u) (μ := volume) hfint.integrableOn hfint.integrableOn
      dsimp [theorem8MillsTail]
      dsimp [f] at hsum ⊢
      linarith
  exact hIic_deriv.const_sub (∫ x : ℝ, f x) |>.congr_of_eventuallyEq htail_eq

/--
Appendix C, Theorem 8: the Gaussian tail integral in the Mills ratio tends to
zero at `+∞`.
-/
theorem theorem8MillsTail_tendsto_atTop_zero :
    Filter.Tendsto theorem8MillsTail Filter.atTop (nhds 0) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2)
  have hfint : Integrable f := by
    have hbase := integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by norm_num)
    convert hbase using 1
    ext x
    dsimp [f]
    ring_nf
  have hanti : Antitone (fun t : ℝ => Set.Ioi t) := by
    intro a b hab x hx
    exact hab.trans_lt hx
  have hInter : (⋂ t : ℝ, Set.Ioi t) = ∅ := by
    ext x
    constructor
    · intro hx
      have hxlt : x < x := by
        simpa using (Set.mem_iInter.mp hx x)
      exact (lt_irrefl x hxlt).elim
    · intro hx
      simp at hx
  have htail :=
    tendsto_setIntegral_of_antitone
      (μ := volume) (s := fun t : ℝ => Set.Ioi t) (f := f)
      (fun _ => measurableSet_Ioi) hanti ⟨(0 : ℝ), hfint.integrableOn⟩
  simpa [theorem8MillsTail, f, hInter] using htail

/-- Appendix C, Theorem 8: derivative of the concrete Mills ratio. -/
theorem theorem8MillsRatio_hasDerivAt (t : ℝ) :
    HasDerivAt theorem8MillsRatio (t * theorem8MillsRatio t - 1) t := by
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (u ^ 2 / 2))
      (t * Real.exp (t ^ 2 / 2)) t := by
    have hinner : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
      simpa using ((hasDerivAt_id t).pow 2).div_const (2 : ℝ)
    convert hinner.exp using 1
    ring
  have htail := theorem8MillsTail_hasDerivAt t
  have hprod := hexp.mul htail
  unfold theorem8MillsRatio at hprod ⊢
  convert hprod using 1
  rw [mul_neg, sub_eq_add_neg]
  congr 1
  rw [← mul_assoc]
  congr 1
  rw [← Real.exp_add]
  rw [show t ^ 2 / 2 + -(t ^ 2) / 2 = 0 by ring]
  rw [Real.exp_zero]

/--
Appendix C, Theorem 8: derivative of the Mills-ratio derivative expression.
Equivalently, for `R(t)=theorem8MillsRatio t`, this is the second-derivative
identity `R''(t) = (t^2+1)R(t)-t`.
-/
theorem theorem8MillsRatio_derivExpr_hasDerivAt (t : ℝ) :
    HasDerivAt
      (fun u => u * theorem8MillsRatio u - 1)
      (((t ^ 2 + 1) * theorem8MillsRatio t) - t) t := by
  have hmul :=
    (hasDerivAt_id t).mul (theorem8MillsRatio_hasDerivAt t)
  have hsub := hmul.sub_const (1 : ℝ)
  convert hsub using 1
  simp [id]
  ring

/--
Appendix C, Theorem 8: change of variables in the Gaussian tail appearing in
the Mills-ratio comparison with `g`.
-/
theorem theorem8MillsRatio_tail_changeOfVariables (t : ℝ) :
    (∫ x : ℝ in Set.Ioi (-(Real.sqrt 2 * t)),
        Real.exp (-(x ^ 2) / 2)) =
      Real.sqrt 2 * ∫ x : ℝ in Set.Iic t, Real.exp (-(x ^ 2)) := by
  let h : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2)
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2))
  have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := hsqrt2_pos.ne'
  have hscale_raw :=
    integral_comp_mul_left_Ioi (g := h) (a := -t) hsqrt2_pos
  have hscale :
      Real.sqrt 2 *
          (∫ x : ℝ in Set.Ioi (-t), h (Real.sqrt 2 * x)) =
        ∫ x : ℝ in Set.Ioi (-(Real.sqrt 2 * t)), h x := by
    rw [hscale_raw]
    simp only [smul_eq_mul]
    rw [show Real.sqrt 2 * -t = -(Real.sqrt 2 * t) by ring]
    field_simp [hsqrt2_ne]
  have hcomp :
      (∫ x : ℝ in Set.Ioi (-t), h (Real.sqrt 2 * x)) =
        ∫ x : ℝ in Set.Ioi (-t), f x := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _hx
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    simp [h, f, mul_pow, hsqrt_sq]
    ring_nf
  have hsymm :
      (∫ x : ℝ in Set.Ioi (-t), f x) =
        ∫ x : ℝ in Set.Iic t, f x := by
    calc
      (∫ x : ℝ in Set.Ioi (-t), f x)
          = ∫ x : ℝ in Set.Ioi (-t), f (-x) := by
              refine setIntegral_congr_fun measurableSet_Ioi ?_
              intro x _hx
              simp [f]
      _ = ∫ x : ℝ in Set.Iic t, f x := by
              simpa using (integral_comp_neg_Ioi (c := -t) (f := f))
  rw [← hscale, hcomp, hsymm]

/--
Appendix C, Theorem 8: the paper's value relation between Mills ratio and
`g(t) = (1 + erf(t)) / exp(-t^2)`.
-/
theorem theorem8MillsRatio_value_relation (t : ℝ) :
    theorem8MillsRatio (-(Real.sqrt 2 * t)) =
      Real.sqrt (Real.pi / 2) * theorem8GaussianG theorem8Erf t := by
  have htail := theorem8MillsRatio_tail_changeOfVariables t
  have hI := theorem8Gaussian_integral_Iic_eq_erf t
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hexp :
      Real.exp (((-(Real.sqrt 2 * t)) ^ 2) / 2) =
        Real.exp (t ^ 2) := by
    congr 1
    rw [neg_sq, mul_pow, hsqrt2_sq]
    ring
  have hconst :
      Real.sqrt 2 * (Real.sqrt Real.pi / 2) =
        Real.sqrt (Real.pi / 2) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).1
    have hpi : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
      Real.sq_sqrt Real.pi_pos.le
    have hpi2 : (Real.sqrt (Real.pi / 2)) ^ 2 = Real.pi / 2 :=
      Real.sq_sqrt (show 0 ≤ Real.pi / 2 by positivity)
    nlinarith
  unfold theorem8MillsRatio theorem8GaussianG
  rw [htail, hI, hexp]
  rw [← mul_assoc (Real.sqrt 2) (Real.sqrt Real.pi / 2)
    (1 + theorem8Erf t), hconst]
  rw [Real.exp_neg, div_inv_eq_mul]
  ring

/-- Appendix C, Theorem 8: positivity of the concrete Mills ratio. -/
theorem theorem8MillsRatio_pos (y : ℝ) :
    0 < theorem8MillsRatio y := by
  let t : ℝ := -y / Real.sqrt 2
  have hrel := theorem8MillsRatio_value_relation t
  have hsqrt2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hy : -(Real.sqrt 2 * t) = y := by
    dsimp [t]
    field_simp [hsqrt2]
  rw [hy] at hrel
  rw [hrel]
  exact mul_pos (by positivity) (theorem8GaussianG_pos (theorem8Erf_one_add_pos t))

/--
The external Mills-ratio inequality used in Appendix C, Theorem 8.

The paper cites Sampford [21, Eq. (3)] for the statement that
`d/dt (1 / R(t)) < 1`.  Lean records exactly that cited analytic input as a
named hypothesis, so the local proof can follow the paper from Mills ratio to
equation (C.10).
-/
def theorem8SampfordMillsBound (R : ℝ → ℝ) : Prop :=
  ∀ t, ∃ d, HasDerivAt (fun u => (R u)⁻¹) d t ∧ d < 1

/--
Appendix C, Theorem 8: the scalar inequality equivalent to Sampford's
derivative bound once the Mills-ratio derivative is known.
-/
def theorem8MillsQuadraticBound (R : ℝ → ℝ) : Prop :=
  ∀ t, 0 < (R t) ^ 2 + t * R t - 1

/--
Appendix C, Theorem 8: Sampford's lower comparison function for the Mills
ratio.  The inequality `theorem8SampfordLowerComparison t < R t` is
algebraically equivalent to the scalar quadratic bound
`0 < R(t)^2 + t R(t) - 1`, using positivity of `R`.
-/
noncomputable def theorem8SampfordLowerComparison (t : ℝ) : ℝ :=
  (Real.sqrt (t ^ 2 + 4) - t) / 2

/-- Appendix C, Theorem 8: Sampford's comparison function is positive. -/
theorem theorem8SampfordLowerComparison_pos (t : ℝ) :
    0 < theorem8SampfordLowerComparison t := by
  unfold theorem8SampfordLowerComparison
  have hsqrt_gt_abs : |t| < Real.sqrt (t ^ 2 + 4) := by
    rw [Real.lt_sqrt (abs_nonneg t)]
    nlinarith [sq_abs t]
  have ht_lt : t < Real.sqrt (t ^ 2 + 4) :=
    (le_abs_self t).trans_lt hsqrt_gt_abs
  linarith

/--
Appendix C, Theorem 8: for nonnegative arguments, Sampford's lower comparison
is bounded by `1`.  This is the bound used to prove the comparison gap vanishes
at `+∞`.
-/
theorem theorem8SampfordLowerComparison_le_one_of_nonneg {t : ℝ}
    (ht : 0 ≤ t) :
    theorem8SampfordLowerComparison t ≤ 1 := by
  unfold theorem8SampfordLowerComparison
  have hsqrt_le : Real.sqrt (t ^ 2 + 4) ≤ t + 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  linarith

/--
Appendix C, Theorem 8: the Sampford comparison function is the positive root
of `x^2 + t*x - 1 = 0`.
-/
theorem theorem8SampfordLowerComparison_quadratic_eq (t : ℝ) :
    (theorem8SampfordLowerComparison t) ^ 2 +
        t * theorem8SampfordLowerComparison t - 1 = 0 := by
  unfold theorem8SampfordLowerComparison
  have hsqrt_sq : (Real.sqrt (t ^ 2 + 4)) ^ 2 = t ^ 2 + 4 := by
    exact Real.sq_sqrt (by nlinarith [sq_nonneg t])
  nlinarith

/--
Appendix C, Theorem 8: derivative of Sampford's lower comparison function.
-/
theorem theorem8SampfordLowerComparison_hasDerivAt (t : ℝ) :
    HasDerivAt theorem8SampfordLowerComparison
      ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2) t := by
  have hinner : HasDerivAt (fun u : ℝ => u ^ 2 + 4) (2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).add_const (4 : ℝ) using 1
    simp [id]
  have hpos : t ^ 2 + 4 ≠ 0 := by
    positivity
  have hsqrt := hinner.sqrt hpos
  have hsub := hsqrt.sub (hasDerivAt_id t)
  have hdiv := hsub.div_const (2 : ℝ)
  unfold theorem8SampfordLowerComparison
  convert hdiv using 1
  have hsqrt_ne : Real.sqrt (t ^ 2 + 4) ≠ 0 := by
    exact (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])).ne'
  field_simp [hsqrt_ne]

/--
Appendix C, Theorem 8: a small algebraic fact behind Sampford's comparison
proof.  The comparison function is larger than the reciprocal of the square
root appearing in its derivative.
-/
theorem theorem8SampfordLowerComparison_inv_sqrt_lt (t : ℝ) :
    (Real.sqrt (t ^ 2 + 4))⁻¹ < theorem8SampfordLowerComparison t := by
  let L := theorem8SampfordLowerComparison t
  let s := Real.sqrt (t ^ 2 + 4)
  have hLpos : 0 < L := theorem8SampfordLowerComparison_pos t
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hroot : L ^ 2 + t * L - 1 = 0 :=
    theorem8SampfordLowerComparison_quadratic_eq t
  have hs_eq : s = 2 * L + t := by
    dsimp [L, s, theorem8SampfordLowerComparison]
    ring
  have hLs : L * s = 1 + L ^ 2 := by
    rw [hs_eq]
    nlinarith
  have hone : 1 < L * s := by
    rw [hLs]
    nlinarith [sq_pos_of_ne_zero hLpos.ne']
  exact (inv_lt_iff_one_lt_mul₀ hspos).2 hone

/--
Appendix C, Theorem 8: the derivative correction term in Sampford's
comparison proof is positive.
-/
theorem theorem8SampfordLowerComparison_sq_add_deriv_pos (t : ℝ) :
    0 <
      (theorem8SampfordLowerComparison t) ^ 2 +
        ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2) := by
  let L := theorem8SampfordLowerComparison t
  let s := Real.sqrt (t ^ 2 + 4)
  have hLpos : 0 < L := theorem8SampfordLowerComparison_pos t
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hderiv_eq : ((t / s - 1) / 2) = -L / s := by
    dsimp [L, s, theorem8SampfordLowerComparison]
    field_simp [hspos.ne']
    ring
  have hinv_lt : s⁻¹ < L := theorem8SampfordLowerComparison_inv_sqrt_lt t
  have hgap : 0 < L - s⁻¹ := sub_pos.mpr hinv_lt
  calc
    0 < L * (L - s⁻¹) := mul_pos hLpos hgap
    _ = L ^ 2 + ((t / s - 1) / 2) := by
      rw [hderiv_eq]
      field_simp [hspos.ne']
      ring

/--
Appendix C, Theorem 8: gap used to prove Sampford's lower bound.  Multiplying
`theorem8SampfordGap t > 0` by `exp(t^2/2)` gives
`theorem8SampfordLowerComparison t < theorem8MillsRatio t`.
-/
noncomputable def theorem8SampfordGap (t : ℝ) : ℝ :=
  theorem8MillsTail t -
    theorem8SampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)

/-- Appendix C, Theorem 8: derivative of the Sampford lower-bound gap. -/
theorem theorem8SampfordGap_hasDerivAt (t : ℝ) :
    HasDerivAt theorem8SampfordGap
      (-(Real.exp (-(t ^ 2) / 2) *
          ((theorem8SampfordLowerComparison t) ^ 2 +
            ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2)))) t := by
  let L := theorem8SampfordLowerComparison
  let E : ℝ → ℝ := fun u => Real.exp (-(u ^ 2) / 2)
  have htail := theorem8MillsTail_hasDerivAt t
  have hL : HasDerivAt L
      ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2) t := by
    simpa [L] using theorem8SampfordLowerComparison_hasDerivAt t
  have hE : HasDerivAt E (-(t * E t)) t := by
    have hinner : HasDerivAt (fun u : ℝ => -(u ^ 2) / 2) (-t) t := by
      convert (((hasDerivAt_id t).pow 2).neg.div_const (2 : ℝ)) using 1
      ring_nf
      simp [id]
    convert hinner.exp using 1 <;> dsimp [E] <;> ring
  have hprod := hL.mul hE
  have hsub := htail.sub hprod
  unfold theorem8SampfordGap theorem8MillsTail
  dsimp [L, E] at hsub ⊢
  convert hsub using 1
  have hroot :
      -((theorem8SampfordLowerComparison t) ^ 2) =
        t * theorem8SampfordLowerComparison t - 1 := by
    have h := theorem8SampfordLowerComparison_quadratic_eq t
    nlinarith
  have hroot_mul :
      Real.exp (t ^ 2 * (-1 / 2)) *
          (-((theorem8SampfordLowerComparison t) ^ 2)) =
        Real.exp (t ^ 2 * (-1 / 2)) *
          (t * theorem8SampfordLowerComparison t - 1) := by
    rw [hroot]
  ring_nf
  ring_nf at hroot_mul
  nlinarith

/--
Appendix C, Theorem 8: the Sampford gap has strictly negative derivative.
-/
theorem theorem8SampfordGap_deriv_neg (t : ℝ) :
    let d :=
      -(Real.exp (-(t ^ 2) / 2) *
          ((theorem8SampfordLowerComparison t) ^ 2 +
            ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2)))
    d < 0 := by
  dsimp
  have hpos :=
    theorem8SampfordLowerComparison_sq_add_deriv_pos t
  exact neg_neg_of_pos (mul_pos (Real.exp_pos _) hpos)

/-- Appendix C, Theorem 8: the Gaussian exponential factor decays at `+∞`. -/
theorem theorem8GaussianExpFactor_tendsto_atTop_zero :
    Filter.Tendsto (fun t : ℝ => Real.exp (-(t ^ 2) / 2))
      Filter.atTop (nhds 0) := by
  have harg :
      Filter.Tendsto (fun t : ℝ => (-(1 / 2 : ℝ)) * t ^ 2)
        Filter.atTop Filter.atBot := by
    exact Filter.tendsto_neg_const_mul_pow_atTop (n := 2) (by norm_num) (by norm_num)
  refine (Real.tendsto_exp_atBot.comp harg).congr' ?_
  filter_upwards with t
  have hpow : (-(t ^ 2) / 2 : ℝ) = (-(1 / 2 : ℝ)) * t ^ 2 := by
    ring
  simpa [Function.comp_apply, hpow]

/--
Appendix C, Theorem 8: Sampford's gap tends to zero at `+∞`.
-/
theorem theorem8SampfordGap_tendsto_atTop_zero :
    Filter.Tendsto theorem8SampfordGap Filter.atTop (nhds 0) := by
  have hprod :
      Filter.Tendsto
        (fun t : ℝ =>
          theorem8SampfordLowerComparison t * Real.exp (-(t ^ 2) / 2))
        Filter.atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ theorem8GaussianExpFactor_tendsto_atTop_zero
    · exact Filter.Eventually.of_forall fun t =>
        mul_nonneg (le_of_lt (theorem8SampfordLowerComparison_pos t))
          (le_of_lt (Real.exp_pos _))
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact mul_le_of_le_one_left (le_of_lt (Real.exp_pos _))
        (theorem8SampfordLowerComparison_le_one_of_nonneg ht)
  simpa [theorem8SampfordGap] using
    theorem8MillsTail_tendsto_atTop_zero.sub hprod

/--
Appendix C, Theorem 8: if the Sampford gap tends to zero at `+∞`, then it is
positive everywhere because its derivative is strictly negative.
-/
theorem theorem8SampfordGap_pos_of_tendsto_atTop_zero
    (hlim : Filter.Tendsto theorem8SampfordGap Filter.atTop (nhds 0)) :
    ∀ t, 0 < theorem8SampfordGap t := by
  have hanti : StrictAnti theorem8SampfordGap := by
    refine strictAnti_of_hasDerivAt_neg
      (f' := fun x =>
        -(Real.exp (-(x ^ 2) / 2) *
          ((theorem8SampfordLowerComparison x) ^ 2 +
            ((x / Real.sqrt (x ^ 2 + 4) - 1) / 2)))) ?_ ?_
    · exact theorem8SampfordGap_hasDerivAt
    · intro x
      exact theorem8SampfordGap_deriv_neg x
  intro t
  have hnext_nonneg : 0 ≤ theorem8SampfordGap (t + 1) := by
    refine le_of_tendsto_of_tendsto hlim tendsto_const_nhds ?_
    filter_upwards [Filter.eventually_ge_atTop (t + 1)] with y hy
    by_cases hy_eq : y = t + 1
    · simp [hy_eq]
    · have hlt : t + 1 < y := lt_of_le_of_ne hy (Ne.symm hy_eq)
      exact le_of_lt (hanti hlt)
  have hstrict : theorem8SampfordGap (t + 1) < theorem8SampfordGap t := by
    exact hanti (by linarith)
  linarith

/--
Appendix C, Theorem 8: positivity of the Sampford gap is exactly the explicit
lower bound on the concrete Mills ratio.
-/
theorem theorem8SampfordLowerComparison_lt_millsRatio_of_gap_pos
    (hgap : ∀ t, 0 < theorem8SampfordGap t) :
    ∀ t, theorem8SampfordLowerComparison t < theorem8MillsRatio t := by
  intro t
  have hgap_t := hgap t
  have htail_lt :
      theorem8SampfordLowerComparison t * Real.exp (-(t ^ 2) / 2) <
        theorem8MillsTail t := by
    simpa [theorem8SampfordGap, sub_pos] using hgap_t
  have hmul := mul_lt_mul_of_pos_left htail_lt (Real.exp_pos (t ^ 2 / 2))
  unfold theorem8MillsRatio
  calc
    theorem8SampfordLowerComparison t
        = Real.exp (t ^ 2 / 2) *
            (theorem8SampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)) := by
          have hexp :
              Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2) / 2) = 1 := by
            rw [← Real.exp_add]
            have : t ^ 2 / 2 + -(t ^ 2) / 2 = 0 := by ring
            rw [this, Real.exp_zero]
          calc
            theorem8SampfordLowerComparison t =
                theorem8SampfordLowerComparison t *
                  (Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2) / 2)) := by
              rw [hexp]
              ring
            _ = Real.exp (t ^ 2 / 2) *
                (theorem8SampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)) := by
              ring
    _ < Real.exp (t ^ 2 / 2) * theorem8MillsTail t := hmul

/--
Appendix C, Theorem 8: once the explicit gap limit is known, Sampford's lower
comparison bound follows for the concrete Mills ratio.
-/
theorem theorem8SampfordLowerComparison_lt_millsRatio_of_gap_tendsto_atTop_zero
    (hlim : Filter.Tendsto theorem8SampfordGap Filter.atTop (nhds 0)) :
    ∀ t, theorem8SampfordLowerComparison t < theorem8MillsRatio t :=
  theorem8SampfordLowerComparison_lt_millsRatio_of_gap_pos
    (theorem8SampfordGap_pos_of_tendsto_atTop_zero hlim)

/--
Appendix C, Theorem 8: Sampford's explicit lower comparison holds for the
concrete Gaussian Mills ratio.
-/
theorem theorem8SampfordLowerComparison_lt_millsRatio :
    ∀ t, theorem8SampfordLowerComparison t < theorem8MillsRatio t :=
  theorem8SampfordLowerComparison_lt_millsRatio_of_gap_tendsto_atTop_zero
    theorem8SampfordGap_tendsto_atTop_zero

/--
Appendix C, Theorem 8: Sampford's lower bound implies the scalar Mills
quadratic inequality used by the paper.
-/
theorem theorem8MillsQuadraticBound_of_sampford_lower
    {R : ℝ → ℝ}
    (hRpos : ∀ t, 0 < R t)
    (hlower : ∀ t, theorem8SampfordLowerComparison t < R t) :
    theorem8MillsQuadraticBound R := by
  intro t
  let L := theorem8SampfordLowerComparison t
  have hLpos : 0 < L := theorem8SampfordLowerComparison_pos t
  have hroot : L ^ 2 + t * L - 1 = 0 := theorem8SampfordLowerComparison_quadratic_eq t
  have hsum_pos : 0 < R t + L + t := by
    have hR_gt_L : L < R t := hlower t
    have hL_formula : 2 * L + t = Real.sqrt (t ^ 2 + 4) := by
      dsimp [L, theorem8SampfordLowerComparison]
      ring
    have hsqrt_pos : 0 < Real.sqrt (t ^ 2 + 4) := by
      exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
    nlinarith
  have hdiff_pos : 0 < R t - L := sub_pos.mpr (hlower t)
  calc
    0 < (R t - L) * (R t + L + t) := mul_pos hdiff_pos hsum_pos
    _ = (R t) ^ 2 + t * R t - 1 := by
      calc
        (R t - L) * (R t + L + t)
            = (R t) ^ 2 + t * R t - (L ^ 2 + t * L) := by ring
        _ = (R t) ^ 2 + t * R t - 1 := by linarith

/--
Appendix C, Theorem 8: for the concrete Mills ratio, it suffices to prove
Sampford's explicit lower comparison bound.
-/
theorem theorem8MillsQuadraticBound_of_sampford_lower_concrete
    (hlower : ∀ t, theorem8SampfordLowerComparison t < theorem8MillsRatio t) :
    theorem8MillsQuadraticBound theorem8MillsRatio :=
  theorem8MillsQuadraticBound_of_sampford_lower
    theorem8MillsRatio_pos hlower

/--
Appendix C, Theorem 8: concrete scalar Mills quadratic inequality.
-/
theorem theorem8MillsQuadraticBound_concrete :
    theorem8MillsQuadraticBound theorem8MillsRatio :=
  theorem8MillsQuadraticBound_of_sampford_lower_concrete
    theorem8SampfordLowerComparison_lt_millsRatio

/--
Appendix C, Theorem 8: the log-convexity/determinant form of the remaining
Mills-ratio inequality.  For the concrete `R`, the determinant expression is
`R R'' - (R')^2`; expanding the Riccati formulas gives exactly
`R^2 + tR - 1`.
-/
def theorem8MillsDeterminantBound (R : ℝ → ℝ) : Prop :=
  ∀ t, 0 < R t * (((t ^ 2 + 1) * R t) - t) - (t * R t - 1) ^ 2

/--
Appendix C, Theorem 8: the determinant/log-convex Mills bound is algebraically
equivalent to the quadratic Sampford bound once the concrete Riccati derivative
formulas are known.
-/
theorem theorem8MillsQuadraticBound_of_determinant
    (hdet : theorem8MillsDeterminantBound theorem8MillsRatio) :
    theorem8MillsQuadraticBound theorem8MillsRatio := by
  intro t
  have h := hdet t
  convert h using 1
  ring

/--
Appendix C, Theorem 8: a positive differentiable Mills ratio satisfying the
quadratic Mills inequality has Sampford's derivative bound.
-/
theorem theorem8SampfordMillsBound_of_derivative_quadratic
    {R : ℝ → ℝ}
    (hRpos : ∀ t, 0 < R t)
    (hRderiv : ∀ t, HasDerivAt R (t * R t - 1) t)
    (hquad : theorem8MillsQuadraticBound R) :
    theorem8SampfordMillsBound R := by
  intro t
  refine ⟨- (t * R t - 1) / (R t) ^ 2, ?_, ?_⟩
  · exact (hRderiv t).inv (hRpos t).ne'
  · have hden : 0 < (R t) ^ 2 := sq_pos_of_ne_zero (hRpos t).ne'
    have h := hquad t
    rw [div_lt_one hden]
    linarith

/--
Appendix C, Theorem 8: for the concrete Mills ratio, it remains only to prove
the scalar quadratic Mills inequality.
-/
theorem theorem8SampfordMillsBound_of_quadratic
    (hquad : theorem8MillsQuadraticBound theorem8MillsRatio) :
    theorem8SampfordMillsBound theorem8MillsRatio :=
  theorem8SampfordMillsBound_of_derivative_quadratic
    theorem8MillsRatio_pos theorem8MillsRatio_hasDerivAt hquad

/--
Appendix C, Theorem 8: concrete Sampford Mills-ratio derivative bound.
-/
theorem theorem8SampfordMillsBound_concrete :
    theorem8SampfordMillsBound theorem8MillsRatio :=
  theorem8SampfordMillsBound_of_quadratic theorem8MillsQuadraticBound_concrete

/--
Appendix C, Theorem 8: after reducing Sampford to the quadratic form, it also
suffices to prove the concrete Mills log-convexity determinant.
-/
theorem theorem8SampfordMillsBound_of_determinant
    (hdet : theorem8MillsDeterminantBound theorem8MillsRatio) :
    theorem8SampfordMillsBound theorem8MillsRatio :=
  theorem8SampfordMillsBound_of_quadratic
    (theorem8MillsQuadraticBound_of_determinant hdet)

/--
Appendix C, Theorem 8 relation between the Mills ratio `R` and the paper's
`g`.  The constants are left explicit so the statement is usable before
committing to a particular definition of `erf` in Lean:
`1 / g(t) = c * 1 / R(-q t)`.
-/
def theorem8MillsToGRelation (R g : ℝ → ℝ) (c q : ℝ) : Prop :=
  ∀ t, (g t)⁻¹ = c * (R (-(q * t)))⁻¹

/--
Appendix C, Theorem 8: the paper states the Mills-to-`g` relation as a value
identity `R(-q t) = c * g(t)`.  This lemma converts that source-facing identity
to the inverse relation used in the C.10 derivative calculation.
-/
theorem theorem8MillsToGRelation_of_value_relation
    {R g : ℝ → ℝ} {c q : ℝ} (hc : c ≠ 0)
    (hrel : ∀ t, R (-(q * t)) = c * g t) :
    theorem8MillsToGRelation R g c q := by
  intro t
  rw [hrel t]
  by_cases hg : g t = 0
  · simp [hg]
  · field_simp [hc, hg]

/-- Appendix C, Theorem 8: the constants in the Mills-ratio change of variables. -/
theorem paper_theorem8_mills_constants_mul :
    Real.sqrt (Real.pi / 2) * Real.sqrt 2 = Real.sqrt Real.pi := by
  have hpi2 : 0 ≤ Real.pi / 2 := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).1
  calc
    (Real.sqrt (Real.pi / 2) * Real.sqrt 2) ^ 2
        = (Real.pi / 2) * 2 := by
          rw [mul_pow, Real.sq_sqrt hpi2, Real.sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]
    _ = Real.pi := by ring
    _ = (Real.sqrt Real.pi) ^ 2 := by
          rw [Real.sq_sqrt Real.pi_pos.le]

/--
Appendix C, Theorem 8, Sampford's Mills-ratio inequality implies equation
(C.10) for the paper's function `g`.
-/
theorem paper_theorem8_c10_of_sampford_mills
    {R g : ℝ → ℝ} {c q : ℝ} (hc : 0 < c) (hq : 0 < q)
    (hcq : c * q = Real.sqrt Real.pi)
    (hrel : theorem8MillsToGRelation R g c q)
    (hsamp : theorem8SampfordMillsBound R) :
    ∀ t, ∃ d,
      HasDerivAt (fun u => (g u)⁻¹) d t ∧ -Real.sqrt Real.pi < d := by
  intro t
  obtain ⟨dR, hdR, hdRlt⟩ := hsamp (-(q * t))
  have hlin : HasDerivAt (fun u : ℝ => -(q * u)) (-q) t := by
    have hmul : HasDerivAt (fun u : ℝ => q * u) q t := by
      simpa using (hasDerivAt_id t).const_mul q
    simpa using hmul.neg
  have hcomp : HasDerivAt (fun u : ℝ => (R (-(q * u)))⁻¹) (dR * (-q)) t := by
    simpa using hdR.comp t hlin
  have hscaled :
      HasDerivAt (fun u : ℝ => c * (R (-(q * u)))⁻¹)
        (c * (dR * (-q))) t :=
    hcomp.const_mul c
  have hderiv :
      HasDerivAt (fun u : ℝ => (g u)⁻¹) (c * (dR * (-q))) t := by
    have hfun : (fun u : ℝ => (g u)⁻¹) =
        fun u : ℝ => c * (R (-(q * u)))⁻¹ := by
      funext u
      exact hrel u
    simpa [hfun] using hscaled
  have hcoef : 0 < c * q := mul_pos hc hq
  have hlt : c * q * dR < c * q := by
    simpa [mul_assoc] using mul_lt_mul_of_pos_left hdRlt hcoef
  refine ⟨c * (dR * (-q)), hderiv, ?_⟩
  nlinarith

/--
Appendix C, Theorem 8, equation (C.9) from Sampford via the mean-value step.
-/
theorem paper_theorem8_c9_positive_of_sampford_mills
    {R g : ℝ → ℝ} {c q t δ : ℝ} (hδ : 0 < δ) (hgpos : 0 < g t)
    (hc : 0 < c) (hq : 0 < q) (hcq : c * q = Real.sqrt Real.pi)
    (hrel : theorem8MillsToGRelation R g c q)
    (hsamp : theorem8SampfordMillsBound R)
    (hcont : ContinuousOn (fun u => (g u)⁻¹) (Set.Icc t (t + δ))) :
    0 < theorem8GaussianC9Bracket g δ t := by
  have hderiv_global :=
    paper_theorem8_c10_of_sampford_mills
      (R := R) (g := g) (c := c) (q := q) hc hq hcq hrel hsamp
  simpa [theorem8GaussianC9Bracket] using
    (paper_theorem8_c9_positive_of_mills_mvt
      (g := g) (t := t) (δ := δ) hδ hgpos hcont
      (fun u _hu => hderiv_global u))

/--
Appendix C, Theorem 8 derivative-factorization step: once differentiating
the C.6 left-hand side factors into a positive prefactor times the C.9
bracket, positivity of C.9 gives a positive derivative.
-/
theorem paper_theorem8_derivative_pos_of_c9_factorization
    {F' factor g : ℝ → ℝ} {δ : ℝ}
    (hfactor :
      ∀ t, F' t = factor t * theorem8GaussianC9Bracket g δ t)
    (hfactor_pos : ∀ t, 0 < factor t)
    (hc9 : ∀ t, 0 < theorem8GaussianC9Bracket g δ t) :
    ∀ t, 0 < F' t := by
  intro t
  rw [hfactor t]
  exact mul_pos (hfactor_pos t) (hc9 t)

/--
Appendix C, Theorem 8, C.6 positivity from the paper's three analytic inputs:
limit `0` at `-∞`, positive derivative after the C.9 factorization, and
Sampford's Mills-ratio bound for equation (C.10).
-/
theorem paper_theorem8_c6_positive_of_sampford_mills
    {R g F F' factor : ℝ → ℝ} {c q δ : ℝ} (hδ : 0 < δ)
    (hc : 0 < c) (hq : 0 < q) (hcq : c * q = Real.sqrt Real.pi)
    (hrel : theorem8MillsToGRelation R g c q)
    (hsamp : theorem8SampfordMillsBound R)
    (hgpos : ∀ t, 0 < g t)
    (hcont : ∀ t, ContinuousOn (fun u => (g u)⁻¹) (Set.Icc t (t + δ)))
    (hFderiv : ∀ t, HasDerivAt F (F' t) t)
    (hFlim : Filter.Tendsto F Filter.atBot (nhds 0))
    (hfactor :
      ∀ t, F' t = factor t * theorem8GaussianC9Bracket g δ t)
    (hfactor_pos : ∀ t, 0 < factor t) :
    ∀ t, 0 < F t := by
  have hc9 : ∀ t, 0 < theorem8GaussianC9Bracket g δ t := by
    intro t
    exact paper_theorem8_c9_positive_of_sampford_mills
      (R := R) (g := g) (c := c) (q := q) (t := t) (δ := δ)
      hδ (hgpos t) hc hq hcq hrel hsamp (hcont t)
  exact paper_theorem8_positive_of_deriv_pos_tendsto_atBot_zero
    hFderiv
    (paper_theorem8_derivative_pos_of_c9_factorization
      (F' := F') (factor := factor) (g := g) (δ := δ)
      hfactor hfactor_pos hc9)
    hFlim

/--
Appendix C, Theorem 8 with the paper's concrete Mills-ratio constants
`R(-sqrt(2)t) = sqrt(pi/2) g(t)` (equivalently stated for inverses).
-/
theorem paper_theorem8_c6_positive_of_sampford_mills_concrete
    {R g F F' factor : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hrel :
      theorem8MillsToGRelation R g (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : theorem8SampfordMillsBound R)
    (hgpos : ∀ t, 0 < g t)
    (hcont : ∀ t, ContinuousOn (fun u => (g u)⁻¹) (Set.Icc t (t + δ)))
    (hFderiv : ∀ t, HasDerivAt F (F' t) t)
    (hFlim : Filter.Tendsto F Filter.atBot (nhds 0))
    (hfactor :
      ∀ t, F' t = factor t * theorem8GaussianC9Bracket g δ t)
    (hfactor_pos : ∀ t, 0 < factor t) :
    ∀ t, 0 < F t :=
  paper_theorem8_c6_positive_of_sampford_mills
    (R := R) (g := g) (F := F) (F' := F') (factor := factor)
    (c := Real.sqrt (Real.pi / 2)) (q := Real.sqrt 2) (δ := δ)
    hδ (by positivity) (by positivity) paper_theorem8_mills_constants_mul
    hrel hsamp hgpos hcont hFderiv hFlim hfactor hfactor_pos

/--
Appendix C, Theorem 8 for the explicit C.6 formula.

The remaining assumptions are exactly the analytic bridges not yet expanded
locally: Sampford's cited Mills-ratio derivative bound, the Mills-to-`g`
identity for the chosen `erf`, continuity of `1/g` on the MVT intervals, the
`-∞` limit of the C.6 expression, and the derivative calculation/factorization
from (C.8) to (C.9).
-/
theorem paper_theorem8_c6_formula_positive_of_sampford_mills
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hone : ∀ t, 0 < 1 + erf t)
    (hrel :
      theorem8MillsToGRelation R (theorem8GaussianG erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : theorem8SampfordMillsBound R)
    (hcont :
      ∀ t,
        ContinuousOn
          (fun u => (theorem8GaussianG erf u)⁻¹) (Set.Icc t (t + δ)))
    (hlim :
      Filter.Tendsto (fun t => theorem8GaussianC6LHS erf J δ t)
        Filter.atBot (nhds 0))
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS erf J δ u)
          (theorem8GaussianC8PositiveFactor erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS erf J δ t :=
  paper_theorem8_c6_positive_of_sampford_mills_concrete
    (R := R) (g := theorem8GaussianG erf)
    (F := fun t => theorem8GaussianC6LHS erf J δ t)
    (F' := fun t =>
      theorem8GaussianC8PositiveFactor erf δ t *
        theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t)
    (factor := fun t => theorem8GaussianC8PositiveFactor erf δ t)
    (δ := δ) hδ hrel hsamp
    (fun t => theorem8GaussianG_pos (hone t))
    hcont hderiv_factor hlim
    (by intro t; rfl)
    (fun t => theorem8GaussianC8PositiveFactor_pos
      (hone t) (by simpa [add_comm] using hone (t + δ)))

/--
Appendix C, Theorem 8 for the explicit C.6 formula, with the continuity of
`1/g` discharged from continuity of `erf`.
-/
theorem paper_theorem8_c6_formula_positive_of_sampford_mills_of_continuous_erf
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf : Continuous erf) (hone : ∀ t, 0 < 1 + erf t)
    (hrel :
      theorem8MillsToGRelation R (theorem8GaussianG erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : theorem8SampfordMillsBound R)
    (hlim :
      Filter.Tendsto (fun t => theorem8GaussianC6LHS erf J δ t)
        Filter.atBot (nhds 0))
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS erf J δ u)
          (theorem8GaussianC8PositiveFactor erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ hone hrel hsamp
    (fun t => theorem8GaussianG_inv_continuousOn herf hone (Set.Icc t (t + δ)))
    hlim hderiv_factor

/--
Appendix C, Theorem 8 for the explicit C.6 formula, with continuity of `erf`
derived from the standard derivative formula for `erf`.
-/
theorem paper_theorem8_c6_formula_positive_of_sampford_mills_of_erf_deriv
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (hone : ∀ t, 0 < 1 + erf t)
    (hrel :
      theorem8MillsToGRelation R (theorem8GaussianG erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : theorem8SampfordMillsBound R)
    (hlim :
      Filter.Tendsto (fun t => theorem8GaussianC6LHS erf J δ t)
        Filter.atBot (nhds 0))
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS erf J δ u)
          (theorem8GaussianC8PositiveFactor erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills_of_continuous_erf
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ (theorem8Erf_continuous_of_hasDerivAt herf_deriv)
    hone hrel hsamp hlim hderiv_factor

/--
Appendix C, Theorem 8 for the explicit C.6 formula, deriving both continuity
of `erf` and positivity of `1 + erf` from standard `erf` analytic inputs.
-/
theorem paper_theorem8_c6_formula_positive_of_sampford_mills_of_erf_deriv_and_tail
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (herf_tail :
      Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0))
    (hrel :
      theorem8MillsToGRelation R (theorem8GaussianG erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : theorem8SampfordMillsBound R)
    (hlim :
      Filter.Tendsto (fun t => theorem8GaussianC6LHS erf J δ t)
        Filter.atBot (nhds 0))
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS erf J δ u)
          (theorem8GaussianC8PositiveFactor erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills_of_erf_deriv
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ herf_deriv
    (theorem8_one_add_erf_pos_of_deriv_tendsto_atBot herf_deriv herf_tail)
    hrel hsamp hlim hderiv_factor

/--
Appendix C, Theorem 8 for the explicit C.6 formula, with the C.6 limit
assembled from the paper's component limits.
-/
theorem paper_theorem8_c6_formula_positive_of_sampford_mills_of_component_limits
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (herf_tail :
      Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0))
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hratio :
      Filter.Tendsto (fun t => theorem8GaussianC6RationalTerm erf δ t)
        Filter.atBot (nhds 0))
    (hrel :
      theorem8MillsToGRelation R (theorem8GaussianG erf)
        (Real.sqrt (Real.pi / 2)) (Real.sqrt 2))
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS erf J δ u)
          (theorem8GaussianC8PositiveFactor erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills_of_erf_deriv_and_tail
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ herf_deriv herf_tail hrel hsamp
    (theorem8GaussianC6LHS_tendsto_atBot_zero hratio herf_tail hJ_tail)
    hderiv_factor

/--
Appendix C, Theorem 8 with the Mills relation stated in the source-facing value
form `R(-sqrt(2)t) = sqrt(pi/2) g(t)`.
-/
theorem paper_theorem8_c6_formula_positive_of_component_limits_value_relation
    {R erf J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_deriv :
      ∀ t, HasDerivAt erf ((2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2))) t)
    (herf_tail :
      Filter.Tendsto (fun t => 1 + erf t) Filter.atBot (nhds 0))
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hratio :
      Filter.Tendsto (fun t => theorem8GaussianC6RationalTerm erf δ t)
        Filter.atBot (nhds 0))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * theorem8GaussianG erf t)
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS erf J δ u)
          (theorem8GaussianC8PositiveFactor erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS erf J δ t :=
  paper_theorem8_c6_formula_positive_of_sampford_mills_of_component_limits
    (R := R) (erf := erf) (J := J) (δ := δ)
    hδ herf_deriv herf_tail hJ_tail hratio
    (theorem8MillsToGRelation_of_value_relation
      (by positivity : Real.sqrt (Real.pi / 2) ≠ 0)
      hrel_value)
    hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the paper's concrete interval-integral
definition of `erf`.  The derivative of `erf` is now proved locally; the
remaining assumptions are the paper's left-tail/component-limit bridges, the
Mills-ratio value identity, Sampford's cited bound, and the C.6 derivative
factorization.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_erf
    {R J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (herf_tail :
      Filter.Tendsto (fun t => 1 + theorem8Erf t) Filter.atBot (nhds 0))
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hratio :
      Filter.Tendsto
        (fun t => theorem8GaussianC6RationalTerm theorem8Erf δ t)
        Filter.atBot (nhds 0))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * theorem8GaussianG theorem8Erf t)
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS theorem8Erf J δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS theorem8Erf J δ t :=
  paper_theorem8_c6_formula_positive_of_component_limits_value_relation
    (R := R) (erf := theorem8Erf) (J := J) (δ := δ)
    hδ theorem8Erf_hasDerivAt herf_tail hJ_tail hratio
    hrel_value hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the concrete `erf`, with the `erf`
derivative and left-tail limit both proved locally.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_erf_of_component_limits
    {R J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hratio :
      Filter.Tendsto
        (fun t => theorem8GaussianC6RationalTerm theorem8Erf δ t)
        Filter.atBot (nhds 0))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * theorem8GaussianG theorem8Erf t)
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS theorem8Erf J δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS theorem8Erf J δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf
    (R := R) (J := J) (δ := δ)
    hδ theorem8Erf_tendsto_one_add_atBot_zero hJ_tail hratio
    hrel_value hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the concrete `erf`, with the `erf`
derivative, `erf` left-tail limit, and C.7 rational-term limit all proved
locally.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_erf_of_integral_tail
    {R J : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hJ_tail : Filter.Tendsto J Filter.atBot (nhds 0))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * theorem8GaussianG theorem8Erf t)
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt (fun u => theorem8GaussianC6LHS theorem8Erf J δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t) :
    ∀ t, 0 < theorem8GaussianC6LHS theorem8Erf J δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf_of_component_limits
    (R := R) (J := J) (δ := δ)
    hδ hJ_tail
    (theorem8GaussianC6RationalTerm_tendsto_atBot_zero_concrete δ)
    hrel_value hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the concrete `erf` and the paper's
concrete `J(t)=∫_{-∞}^t exp(-x^2)erf(x+δ)dx`.  The `J` tail limit is
derived from the integrability of its left-half-line integrand.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_erf_and_J_of_integrable
    {R : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hJ_integrable :
      IntegrableOn
        (fun x : ℝ => Real.exp (-(x ^ 2)) * theorem8Erf (x + δ))
        (Set.Iic (0 : ℝ)))
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * theorem8GaussianG theorem8Erf t)
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u =>
            theorem8GaussianC6LHS theorem8Erf
              (theorem8GaussianJ theorem8Erf δ) δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t) :
    ∀ t,
      0 <
        theorem8GaussianC6LHS theorem8Erf
          (theorem8GaussianJ theorem8Erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf_of_integral_tail
    (R := R) (J := theorem8GaussianJ theorem8Erf δ) (δ := δ)
    hδ
    (theorem8GaussianJ_tendsto_atBot_zero_of_integrableOn
      (erf := theorem8Erf) (δ := δ) hJ_integrable)
    hrel_value hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the concrete `erf` and the paper's
concrete `J`.  The derivative of `erf`, its left-tail limit, the C.7 rational
limit, and the `J` left-tail limit are all proved locally.  The remaining
assumptions are the paper's Mills-ratio value identity, Sampford's cited
Mills-ratio derivative bound, and the C.6 derivative factorization.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_erf_and_J
    {R : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hrel_value :
      ∀ t,
        R (-(Real.sqrt 2 * t)) =
          Real.sqrt (Real.pi / 2) * theorem8GaussianG theorem8Erf t)
    (hsamp : theorem8SampfordMillsBound R)
    (hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u =>
            theorem8GaussianC6LHS theorem8Erf
              (theorem8GaussianJ theorem8Erf δ) δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t) :
    ∀ t,
      0 <
        theorem8GaussianC6LHS theorem8Erf
          (theorem8GaussianJ theorem8Erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf_and_J_of_integrable
    (R := R) (δ := δ) hδ
    (theorem8GaussianJ_integrableOn_concrete δ)
    hrel_value hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the paper's concrete Mills ratio,
concrete `erf`, and concrete `J`.  The Mills-to-`g` value identity is proved by
change of variables in `theorem8MillsRatio_value_relation`; the remaining
assumptions are Sampford's cited Mills-ratio derivative bound for the concrete
Mills ratio and the C.6 derivative factorization.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J
    {δ : ℝ} (hδ : 0 < δ)
    (hsamp : theorem8SampfordMillsBound theorem8MillsRatio)
    (hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u =>
            theorem8GaussianC6LHS theorem8Erf
              (theorem8GaussianJ theorem8Erf δ) δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t) :
    ∀ t,
      0 <
        theorem8GaussianC6LHS theorem8Erf
          (theorem8GaussianJ theorem8Erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_erf_and_J
    (R := theorem8MillsRatio) (δ := δ)
    hδ theorem8MillsRatio_value_relation hsamp hderiv_factor

/--
Appendix C, Theorem 8: explicit derivative of the C.6 rational term for the
concrete interval-integral `erf`.
-/
noncomputable def theorem8GaussianC6RationalTermDerivative (δ t : ℝ) : ℝ :=
  let c : ℝ := 2 / Real.sqrt Real.pi
  let A : ℝ := 1 + theorem8Erf t
  let B : ℝ := 1 + theorem8Erf (t + δ)
  let E : ℝ := Real.exp (-(t ^ 2))
  let D : ℝ := Real.exp (-((t + δ) ^ 2))
  ((((c * E) * B ^ 2 * E + A * (2 * B * (c * D)) * E +
      A * B ^ 2 * (-(2 * t * E))) * (A * D + B * E) -
    (A * B ^ 2 * E) *
      ((c * E) * D + A * (-(2 * (t + δ) * D)) +
        (c * D) * E + B * (-(2 * t * E)))) /
    (A * D + B * E) ^ 2)

/--
Appendix C, Theorem 8: differentiating the concrete C.6 rational term gives
the explicit quotient-rule derivative used in equation (C.8).
-/
theorem theorem8GaussianC6RationalTerm_hasDerivAt_concrete_explicit
    (δ t : ℝ) :
    HasDerivAt
      (fun u => theorem8GaussianC6RationalTerm theorem8Erf δ u)
      (theorem8GaussianC6RationalTermDerivative δ t) t := by
  let c : ℝ := 2 / Real.sqrt Real.pi
  let A : ℝ → ℝ := fun u => 1 + theorem8Erf u
  let B : ℝ → ℝ := fun u => 1 + theorem8Erf (u + δ)
  let E : ℝ → ℝ := fun u => Real.exp (-(u ^ 2))
  let D : ℝ → ℝ := fun u => Real.exp (-((u + δ) ^ 2))
  have hA : HasDerivAt A (c * E t) t := by
    dsimp [A, c, E]
    simpa using (theorem8Erf_hasDerivAt t).const_add (1 : ℝ)
  have hshift : HasDerivAt (fun u : ℝ => u + δ) 1 t := by
    simpa [add_comm] using (hasDerivAt_id t).const_add δ
  have hB : HasDerivAt B (c * D t) t := by
    dsimp [B, c, D]
    simpa using
      ((theorem8Erf_hasDerivAt (t + δ)).comp t hshift).const_add (1 : ℝ)
  have hE : HasDerivAt E (-(2 * t * E t)) t := by
    have hinner : HasDerivAt (fun u : ℝ => -(u ^ 2)) (-(2 * t)) t := by
      simpa using ((hasDerivAt_id t).pow 2).neg
    dsimp [E]
    convert hinner.exp using 1
    ring
  have hD : HasDerivAt D (-(2 * (t + δ) * D t)) t := by
    have hsq : HasDerivAt (fun u : ℝ => (u + δ) ^ 2) (2 * (t + δ)) t := by
      simpa [one_mul] using hshift.pow 2
    have hinner :
        HasDerivAt (fun u : ℝ => -((u + δ) ^ 2)) (-(2 * (t + δ))) t := by
      simpa using hsq.neg
    dsimp [D]
    convert hinner.exp using 1
    ring
  have hBsq :
      HasDerivAt (fun u => B u ^ 2) (2 * B t * (c * D t)) t := by
    convert hB.pow 2 using 1
    ring
  have hAB :
      HasDerivAt (fun u => A u * B u ^ 2)
        ((c * E t) * B t ^ 2 + A t * (2 * B t * (c * D t))) t := by
    convert hA.mul hBsq using 1
  have hnum :
      HasDerivAt (fun u => A u * B u ^ 2 * E u)
        ((c * E t) * B t ^ 2 * E t +
          A t * (2 * B t * (c * D t)) * E t +
          A t * B t ^ 2 * (-(2 * t * E t))) t := by
    convert hAB.mul hE using 1
    ring
  have hAD :
      HasDerivAt (fun u => A u * D u)
        ((c * E t) * D t + A t * (-(2 * (t + δ) * D t))) t := by
    convert hA.mul hD using 1
  have hBE :
      HasDerivAt (fun u => B u * E u)
        ((c * D t) * E t + B t * (-(2 * t * E t))) t := by
    convert hB.mul hE using 1
  have hden_deriv :
      HasDerivAt (fun u => A u * D u + B u * E u)
        ((c * E t) * D t + A t * (-(2 * (t + δ) * D t)) +
          ((c * D t) * E t + B t * (-(2 * t * E t)))) t := by
    exact hAD.add hBE
  have hden_ne : A t * D t + B t * E t ≠ 0 := by
    have hpos : 0 < A t * D t + B t * E t := by
      dsimp [A, B, D, E]
      exact add_pos
        (mul_pos (theorem8Erf_one_add_pos t) (Real.exp_pos _))
        (mul_pos (theorem8Erf_one_add_pos (t + δ)) (Real.exp_pos _))
    exact hpos.ne'
  have hquot := hnum.div hden_deriv hden_ne
  unfold theorem8GaussianC6RationalTerm theorem8GaussianC6RationalTermDerivative
  simpa [A, B, E, D, c, add_assoc] using hquot

/--
Appendix C, Theorem 8, equation (C.8): the derivative of the C.6 left-hand
side before the paper's algebraic factorization into the C.8 prefactor and
C.9 bracket.
-/
noncomputable def theorem8GaussianC8Derivative (δ t : ℝ) : ℝ :=
  deriv (fun u => theorem8GaussianC6RationalTerm theorem8Erf δ u) t -
    (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) -
    (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) *
      theorem8Erf (t + δ)

/--
Appendix C, Theorem 8: calculus part of equation (C.8) for the concrete `erf`
and concrete `J`.  The remaining paper step after this lemma is purely the
algebraic factorization of `theorem8GaussianC8Derivative` into the C.8 positive
prefactor times the C.9 bracket.
-/
theorem theorem8GaussianC6LHS_hasDerivAt_concrete_C8
    (δ t : ℝ) :
    HasDerivAt
      (fun u =>
        theorem8GaussianC6LHS theorem8Erf
          (theorem8GaussianJ theorem8Erf δ) δ u)
      (theorem8GaussianC8Derivative δ t) t := by
  let c : ℝ := 2 / Real.sqrt Real.pi
  let A : ℝ → ℝ := fun u => 1 + theorem8Erf u
  let B : ℝ → ℝ := fun u => 1 + theorem8Erf (u + δ)
  let E : ℝ → ℝ := fun u => Real.exp (-(u ^ 2))
  let D : ℝ → ℝ := fun u => Real.exp (-((u + δ) ^ 2))
  have hA_diff : DifferentiableAt ℝ A t := by
    dsimp [A]
    exact ((theorem8Erf_hasDerivAt t).const_add (1 : ℝ)).differentiableAt
  have hshift : HasDerivAt (fun u : ℝ => u + δ) 1 t := by
    simpa [add_comm] using (hasDerivAt_id t).const_add δ
  have hB_diff : DifferentiableAt ℝ B t := by
    dsimp [B]
    exact (((theorem8Erf_hasDerivAt (t + δ)).comp t hshift).const_add
      (1 : ℝ)).differentiableAt
  have hE_diff : DifferentiableAt ℝ E t := by
    dsimp [E]
    fun_prop
  have hD_diff : DifferentiableAt ℝ D t := by
    dsimp [D]
    fun_prop
  have hnum_diff :
      DifferentiableAt ℝ (fun u => A u * B u ^ 2 * E u) t :=
    (hA_diff.mul (hB_diff.pow 2)).mul hE_diff
  have hden_diff :
      DifferentiableAt ℝ (fun u => A u * D u + B u * E u) t :=
    (hA_diff.mul hD_diff).add (hB_diff.mul hE_diff)
  have hden_ne : A t * D t + B t * E t ≠ 0 := by
    have hpos : 0 < A t * D t + B t * E t := by
      dsimp [A, B, D, E]
      exact add_pos
        (mul_pos (theorem8Erf_one_add_pos t) (Real.exp_pos _))
        (mul_pos (theorem8Erf_one_add_pos (t + δ)) (Real.exp_pos _))
    exact hpos.ne'
  have hrat_diff :
      DifferentiableAt ℝ
        (fun u => theorem8GaussianC6RationalTerm theorem8Erf δ u) t := by
    unfold theorem8GaussianC6RationalTerm
    simpa [A, B, E, D] using hnum_diff.div hden_diff hden_ne
  have hrat_deriv :
      HasDerivAt
        (fun u => theorem8GaussianC6RationalTerm theorem8Erf δ u)
        (deriv (fun u => theorem8GaussianC6RationalTerm theorem8Erf δ u) t) t :=
    hrat_diff.hasDerivAt
  have hA_deriv :
      HasDerivAt (fun u => 1 + theorem8Erf u)
        (c * Real.exp (-(t ^ 2))) t := by
    dsimp [c]
    simpa using (theorem8Erf_hasDerivAt t).const_add (1 : ℝ)
  have hJ_deriv := theorem8GaussianJ_hasDerivAt_concrete δ t
  have hmain :=
    (hrat_deriv.sub hA_deriv).sub (hJ_deriv.const_mul c)
  refine hmain.congr_deriv ?_
  unfold theorem8GaussianC8Derivative c
  ring

/--
Appendix C, Theorem 8: equation (C.8) factors as a positive prefactor times
the C.9 bracket for the concrete interval-integral `erf`.
-/
theorem theorem8GaussianC8Derivative_factorization
    (δ t : ℝ) :
    theorem8GaussianC8Derivative δ t =
      theorem8GaussianC8PositiveFactor theorem8Erf δ t *
        theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t := by
  have hrat :=
    (theorem8GaussianC6RationalTerm_hasDerivAt_concrete_explicit δ t).deriv
  let a : ℝ := 1 + theorem8Erf t
  let b : ℝ := 1 + theorem8Erf (t + δ)
  let p : ℝ := Real.exp (-(t ^ 2))
  let q : ℝ := Real.exp (-((t + δ) ^ 2))
  let s : ℝ := Real.sqrt Real.pi
  have hs : s ≠ 0 := by
    dsimp [s]
    exact (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hp : p ≠ 0 := by
    dsimp [p]
    exact (Real.exp_pos _).ne'
  have hq : q ≠ 0 := by
    dsimp [q]
    exact (Real.exp_pos _).ne'
  have hb : b ≠ 0 := by
    dsimp [b]
    exact (theorem8Erf_one_add_pos (t + δ)).ne'
  have hden : a * q + b * p ≠ 0 := by
    have hpos : 0 < a * q + b * p := by
      dsimp [a, b, p, q]
      exact add_pos
        (mul_pos (theorem8Erf_one_add_pos t) (Real.exp_pos _))
        (mul_pos (theorem8Erf_one_add_pos (t + δ)) (Real.exp_pos _))
    exact hpos.ne'
  have halg := theorem8GaussianC8_algebra a b p q s δ t hs hp hq hb hden
  have hc8_compact :
      theorem8GaussianC8Derivative δ t =
        theorem8GaussianC6RationalTermDerivative δ t -
          (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) *
            (1 + theorem8Erf (t + δ)) := by
    unfold theorem8GaussianC8Derivative
    rw [hrat]
    ring
  rw [hc8_compact]
  unfold theorem8GaussianC6RationalTermDerivative
  unfold theorem8GaussianC8PositiveFactor theorem8GaussianC9Bracket theorem8GaussianG
  simpa [a, b, p, q, s, Real.exp_neg, add_comm, add_left_comm, add_assoc]
    using halg

/--
Appendix C, Theorem 8 specialized to the paper's concrete Mills ratio,
concrete `erf`, and concrete `J`, with the C.6 derivative factorization
discharged by `theorem8GaussianC8Derivative_factorization`.

The only remaining scalar analytic input is Sampford's cited Mills-ratio
derivative bound.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J_of_sampford
    {δ : ℝ} (hδ : 0 < δ)
    (hsamp : theorem8SampfordMillsBound theorem8MillsRatio) :
    ∀ t,
      0 <
        theorem8GaussianC6LHS theorem8Erf
          (theorem8GaussianJ theorem8Erf δ) δ t := by
  have hderiv_factor :
      ∀ t,
        HasDerivAt
          (fun u =>
            theorem8GaussianC6LHS theorem8Erf
              (theorem8GaussianJ theorem8Erf δ) δ u)
          (theorem8GaussianC8PositiveFactor theorem8Erf δ t *
            theorem8GaussianC9Bracket (theorem8GaussianG theorem8Erf) δ t) t := by
    intro t
    exact (theorem8GaussianC6LHS_hasDerivAt_concrete_C8 δ t).congr_deriv
      (theorem8GaussianC8Derivative_factorization δ t)
  exact paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J
    (δ := δ) hδ hsamp hderiv_factor

/--
Appendix C, Theorem 8 specialized to the paper's concrete Mills ratio,
concrete `erf`, and concrete `J`, after formalizing Sampford's Mills-ratio
input for the concrete Gaussian Mills ratio.
-/
theorem paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J_unconditional
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ t,
      0 <
        theorem8GaussianC6LHS theorem8Erf
          (theorem8GaussianJ theorem8Erf δ) δ t :=
  paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J_of_sampford
    hδ theorem8SampfordMillsBound_concrete

/--
Appendix C, Theorem 8: the conditional pairwise probability expression after
the paper's Gaussian density/CDF calculation and the substitution
`t = a - x_i`, `δ = x_i - x_j`.

This is the formula immediately before differentiating to obtain (C.5)--(C.6):
`((1+erf(t)) + (2/sqrt(pi)) J(t)) /
 ((1+erf(t)) (1+erf(t+δ)))`.
-/
noncomputable def theorem8GaussianConditionalIntegralRatio
    (erf J : ℝ → ℝ) (δ t : ℝ) : ℝ :=
  ((1 + erf t) + (2 / Real.sqrt Real.pi) * J t) /
    ((1 + erf t) * (1 + erf (t + δ)))

/--
Appendix C, Theorem 8: algebra connecting the quotient-rule derivative of the
Gaussian conditional integral ratio to the C.6 left-hand side.
-/
theorem theorem8GaussianConditionalIntegralRatio_deriv_eq_c6_algebra
    {A B p q J c : ℝ} (hden : A * q + B * p ≠ 0) :
    ((c * p * B) * (A * B) - (A + c * J) * (c * p * B + A * (c * q))) /
        (A * B) ^ 2 =
      c * (A * q + B * p) *
        (A * B ^ 2 * p / (A * q + B * p) - A - c * J) /
          (A * B) ^ 2 := by
  have hnum :
      (c * p * B) * (A * B) - (A + c * J) * (c * p * B + A * (c * q)) =
        c * (A * q + B * p) *
          (A * B ^ 2 * p / (A * q + B * p) - A - c * J) := by
    let S : ℝ := A * q + B * p
    let T : ℝ := A * B ^ 2 * p
    have hcancel : S * (T / S) = T := by
      exact mul_div_cancel₀ T (by simpa [S] using hden)
    calc
      (c * p * B) * (A * B) - (A + c * J) * (c * p * B + A * (c * q))
          = c * (T - S * A - S * (c * J)) := by
            dsimp [S, T]
            ring
      _ = c * (S * (T / S) - S * A - S * (c * J)) := by
            rw [hcancel]
      _ = c * S * (T / S - A - c * J) := by
            ring
      _ = c * (A * q + B * p) *
            (A * B ^ 2 * p / (A * q + B * p) - A - c * J) := by
            dsimp [S, T]
  rw [hnum]

/--
Appendix C, Theorem 8: at the Gaussian integral-ratio layer, the derivative of
the conditional pairwise probability expression is strictly positive.  The
sign is exactly the already formalized C.6 scalar positivity theorem.
-/
theorem theorem8GaussianConditionalIntegralRatio_hasDerivAt_pos
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∃ d,
      HasDerivAt
        (fun u =>
          theorem8GaussianConditionalIntegralRatio theorem8Erf
            (theorem8GaussianJ theorem8Erf δ) δ u) d t ∧
        0 < d := by
  let c : ℝ := 2 / Real.sqrt Real.pi
  let A : ℝ := 1 + theorem8Erf t
  let B : ℝ := 1 + theorem8Erf (t + δ)
  let p : ℝ := Real.exp (-(t ^ 2))
  let q : ℝ := Real.exp (-((t + δ) ^ 2))
  let Jv : ℝ := theorem8GaussianJ theorem8Erf δ t
  let F : ℝ := theorem8GaussianC6LHS theorem8Erf (theorem8GaussianJ theorem8Erf δ) δ t
  let d : ℝ := c * (A * q + B * p) * F / (A * B) ^ 2
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hA_pos : 0 < A := by
    dsimp [A]
    exact theorem8Erf_one_add_pos t
  have hB_pos : 0 < B := by
    dsimp [B]
    exact theorem8Erf_one_add_pos (t + δ)
  have hp_pos : 0 < p := by
    dsimp [p]
    exact Real.exp_pos _
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Real.exp_pos _
  have hden_prod_ne : A * B ≠ 0 := by
    exact (mul_pos hA_pos hB_pos).ne'
  have hden_c6_pos : 0 < A * q + B * p := by
    exact add_pos (mul_pos hA_pos hq_pos) (mul_pos hB_pos hp_pos)
  have hF_pos : 0 < F := by
    dsimp [F]
    exact paper_theorem8_c6_formula_positive_for_concrete_mills_erf_and_J_unconditional hδ t
  have hA_deriv :
      HasDerivAt (fun u => 1 + theorem8Erf u) (c * p) t := by
    dsimp [c, p]
    simpa using (theorem8Erf_hasDerivAt t).const_add (1 : ℝ)
  have hshift : HasDerivAt (fun u : ℝ => u + δ) 1 t := by
    simpa using (hasDerivAt_id t).add_const δ
  have hB_deriv :
      HasDerivAt (fun u => 1 + theorem8Erf (u + δ)) (c * q) t := by
    dsimp [c, q]
    simpa [one_mul] using
      ((theorem8Erf_hasDerivAt (t + δ)).comp t hshift).const_add (1 : ℝ)
  have hJ_deriv :
      HasDerivAt
        (fun u => theorem8GaussianJ theorem8Erf δ u)
        (p * theorem8Erf (t + δ)) t := by
    dsimp [p]
    exact theorem8GaussianJ_hasDerivAt_concrete δ t
  have hnum_deriv :
      HasDerivAt
        (fun u =>
          (1 + theorem8Erf u) +
            c * theorem8GaussianJ theorem8Erf δ u)
        (c * p * B) t := by
    have hraw := hA_deriv.add (hJ_deriv.const_mul c)
    convert hraw using 1
    dsimp [B]
    ring
  have hden_deriv :
      HasDerivAt
        (fun u => (1 + theorem8Erf u) * (1 + theorem8Erf (u + δ)))
        (c * p * B + A * (c * q)) t := by
    have hraw := hA_deriv.mul hB_deriv
    simpa [A, B] using hraw
  have hratio :
      HasDerivAt
        (fun u =>
          theorem8GaussianConditionalIntegralRatio theorem8Erf
            (theorem8GaussianJ theorem8Erf δ) δ u)
        (((c * p * B) * (A * B) -
            (A + c * Jv) * (c * p * B + A * (c * q))) /
          (A * B) ^ 2) t := by
    have hdiv := hnum_deriv.div hden_deriv hden_prod_ne
    simpa [theorem8GaussianConditionalIntegralRatio, A, B, Jv] using hdiv
  have hderiv_eq :
      ((c * p * B) * (A * B) -
            (A + c * Jv) * (c * p * B + A * (c * q))) /
          (A * B) ^ 2 = d := by
    dsimp [d, F, theorem8GaussianC6LHS, theorem8GaussianC6RationalTerm]
    exact theorem8GaussianConditionalIntegralRatio_deriv_eq_c6_algebra
      (A := A) (B := B) (p := p) (q := q) (J := Jv) (c := c)
      hden_c6_pos.ne'
  refine ⟨d, ?_, ?_⟩
  · exact hratio.congr_deriv hderiv_eq
  · dsimp [d]
    positivity

/--
Appendix C, Theorem 8: the Gaussian conditional integral ratio in the paper's
original cutoff coordinate `a`, with `t = a - x_i` and `δ = x_i - x_j`.
-/
noncomputable def theorem8GaussianConditionalIntegralRatioAt
    (xi xj a : ℝ) : ℝ :=
  theorem8GaussianConditionalIntegralRatio theorem8Erf
    (theorem8GaussianJ theorem8Erf (xi - xj)) (xi - xj) (a - xi)

/--
Appendix C, Theorem 8 at the Gaussian integral-ratio layer, in the original
`a, x_i, x_j` coordinates: if `x_i > x_j`, the displayed conditional integral
ratio has strictly positive derivative in the cutoff `a`.
-/
theorem theorem8GaussianConditionalIntegralRatioAt_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => theorem8GaussianConditionalIntegralRatioAt xi xj u) d a ∧
        0 < d := by
  have hδ : 0 < xi - xj := sub_pos.mpr hx
  obtain ⟨d, hd, hdpos⟩ :=
    theorem8GaussianConditionalIntegralRatio_hasDerivAt_pos
      (δ := xi - xj) hδ (a - xi)
  have hshift : HasDerivAt (fun u : ℝ => u - xi) 1 a := by
    simpa using (hasDerivAt_id a).sub_const xi
  refine ⟨d, ?_, hdpos⟩
  unfold theorem8GaussianConditionalIntegralRatioAt
  simpa [one_mul] using hd.comp a hshift

/--
Appendix C, Theorem 8: the Gaussian density used after the paper normalizes to
`σ = 1 / sqrt 2`, so that the variance is `1/2`.
-/
noncomputable def theorem8GaussianPDF (μ x : ℝ) : ℝ :=
  Real.exp (-((x - μ) ^ 2)) / Real.sqrt Real.pi

/--
Appendix C, Theorem 8: the paper Gaussian density agrees with Mathlib's
`gaussianPDFReal` at variance `1/2`.
-/
theorem theorem8GaussianPDF_eq_gaussianPDFReal_half (μ x : ℝ) :
    theorem8GaussianPDF μ x =
      ProbabilityTheory.gaussianPDFReal μ (1 / 2 : ℝ≥0) x := by
  unfold theorem8GaussianPDF ProbabilityTheory.gaussianPDFReal
  norm_num
  field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos]

/--
Appendix C, Theorem 8: the corresponding Gaussian CDF in the paper's
normalization.
-/
noncomputable def theorem8GaussianCDF (μ a : ℝ) : ℝ :=
  (1 + theorem8Erf (a - μ)) / 2

/--
Appendix C, Theorem 8: the paper's CDF formula is the left integral of the
paper Gaussian density.
-/
theorem theorem8GaussianPDF_integral_Iic_eq_CDF (μ a : ℝ) :
    (∫ x : ℝ in Set.Iic a, theorem8GaussianPDF μ x) =
      theorem8GaussianCDF μ a := by
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
    Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hshift :=
    theorem8_integral_Iic_sub_eq_integral_Iic
      (f := fun u : ℝ => Real.exp (-(u ^ 2)))
      (a := a) (μ := μ)
  unfold theorem8GaussianPDF theorem8GaussianCDF
  calc
    (∫ x : ℝ in Set.Iic a, Real.exp (-((x - μ) ^ 2)) / Real.sqrt Real.pi)
        = (1 / Real.sqrt Real.pi) *
            ∫ x : ℝ in Set.Iic a, Real.exp (-((x - μ) ^ 2)) := by
          rw [← integral_const_mul]
          congr 1
          ext x
          field_simp [hsqrt_ne]
    _ = (1 / Real.sqrt Real.pi) *
            ∫ u : ℝ in Set.Iic (a - μ), Real.exp (-(u ^ 2)) := by
          rw [hshift]
    _ = (1 / Real.sqrt Real.pi) *
          (Real.sqrt Real.pi / 2 * (1 + theorem8Erf (a - μ))) := by
          rw [theorem8Gaussian_integral_Iic_eq_erf]
    _ = (1 + theorem8Erf (a - μ)) / 2 := by
          field_simp [hsqrt_ne]

/--
Appendix C, Theorem 8: the Mathlib Gaussian measure at variance `1/2` assigns
the left half-line the paper's CDF value.
-/
theorem theorem8GaussianReal_Iic_eq_CDF (μ a : ℝ) :
    ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0) (Set.Iic a) =
      ENNReal.ofReal (theorem8GaussianCDF μ a) := by
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral μ hv (Set.Iic a)]
  congr 1
  rw [← theorem8GaussianPDF_integral_Iic_eq_CDF μ a]
  refine setIntegral_congr_fun measurableSet_Iic ?_
  intro x _hx
  exact (theorem8GaussianPDF_eq_gaussianPDFReal_half μ x).symm

/-- Appendix C, Theorem 8: nonnegativity of the paper Gaussian CDF. -/
theorem theorem8GaussianCDF_nonneg (μ a : ℝ) :
    0 ≤ theorem8GaussianCDF μ a := by
  unfold theorem8GaussianCDF
  exact div_nonneg (le_of_lt (theorem8Erf_one_add_pos (a - μ))) (by norm_num)

/-- Appendix C, Theorem 8: the paper Gaussian CDF is at most one. -/
theorem theorem8GaussianCDF_le_one (μ a : ℝ) :
    theorem8GaussianCDF μ a ≤ 1 := by
  have hle :
      ENNReal.ofReal (theorem8GaussianCDF μ a) ≤ (1 : ℝ≥0∞) := by
    rw [← theorem8GaussianReal_Iic_eq_CDF μ a]
    simpa using
      measure_mono
        (μ := ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0))
        (Set.subset_univ (Set.Iic a))
  exact ENNReal.ofReal_le_one.mp hle

/-- Appendix C, Theorem 8: nonnegativity of the paper Gaussian density. -/
theorem theorem8GaussianPDF_nonneg (μ x : ℝ) :
    0 ≤ theorem8GaussianPDF μ x := by
  unfold theorem8GaussianPDF
  positivity

/--
Appendix C, Theorem 8: integrability of the product of the paper Gaussian
density and CDF over a left half-line.
-/
theorem theorem8GaussianPDF_mul_CDF_integrableOn (xi xj a : ℝ) :
    IntegrableOn
      (fun x : ℝ => theorem8GaussianPDF xi x * theorem8GaussianCDF xj x)
      (Set.Iic a) := by
  have hpdf : Integrable (theorem8GaussianPDF xi) := by
    have h := ProbabilityTheory.integrable_gaussianPDFReal xi (1 / 2 : ℝ≥0)
    convert h using 1
    ext x
    exact theorem8GaussianPDF_eq_gaussianPDFReal_half xi x
  have hcdf_meas :
      AEStronglyMeasurable (fun x : ℝ => theorem8GaussianCDF xj x)
        (volume.restrict (Set.Iic a)) := by
    have hcont : Continuous fun x : ℝ => theorem8GaussianCDF xj x := by
      unfold theorem8GaussianCDF
      exact ((theorem8Erf_continuous.comp
        (continuous_id.sub continuous_const)).const_add 1).div_const 2
    exact hcont.aestronglyMeasurable
  have hcdf_bound :
      ∀ᵐ x ∂volume.restrict (Set.Iic a),
        ‖theorem8GaussianCDF xj x‖ ≤ (1 : ℝ) := by
    refine ae_restrict_of_forall_mem measurableSet_Iic ?_
    intro x _hx
    rw [Real.norm_of_nonneg (theorem8GaussianCDF_nonneg xj x)]
    exact theorem8GaussianCDF_le_one xj x
  exact hpdf.integrableOn.mul_bdd hcdf_meas hcdf_bound

/--
Appendix C, Theorem 8: the paper Gaussian density as an `ENNReal` density is
Mathlib's `gaussianPDF` at variance `1/2`.
-/
theorem theorem8GaussianPDF_ofReal_eq_gaussianPDF_half (μ x : ℝ) :
    ENNReal.ofReal (theorem8GaussianPDF μ x) =
      ProbabilityTheory.gaussianPDF μ (1 / 2 : ℝ≥0) x := by
  simp [ProbabilityTheory.gaussianPDF,
    theorem8GaussianPDF_eq_gaussianPDFReal_half]

/--
Appendix C, Theorem 8: after substituting `u = x - x_i`, the numerator
integral in the paper's Gaussian density/CDF formula splits into the `erf`
tail and the paper's `J` integral.
-/
theorem theorem8Gaussian_integral_shift_split (xi xj a : ℝ) :
    (∫ x : ℝ in Set.Iic a,
        Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) =
      Real.sqrt Real.pi / 2 * (1 + theorem8Erf (a - xi)) +
        theorem8GaussianJ theorem8Erf (xi - xj) (a - xi) := by
  let t : ℝ := a - xi
  let δ : ℝ := xi - xj
  have hshift :
      (∫ x : ℝ in Set.Iic a,
          Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) =
        ∫ u : ℝ in Set.Iic t,
          Real.exp (-(u ^ 2)) * (1 + theorem8Erf (u + δ)) := by
    have h :=
      theorem8_integral_Iic_sub_eq_integral_Iic
        (f := fun u : ℝ =>
          Real.exp (-(u ^ 2)) * (1 + theorem8Erf (u + δ)))
        (a := a) (μ := xi)
    dsimp [t, δ] at h ⊢
    convert h using 2
    · ext x
      ring_nf
  have hgauss :
      IntegrableOn (fun u : ℝ => Real.exp (-(u ^ 2))) (Set.Iic t) := by
    simpa [one_mul] using
      (integrable_exp_neg_mul_sq (show 0 < (1 : ℝ) by norm_num)).integrableOn
  have hJ :
      IntegrableOn
        (fun u : ℝ => Real.exp (-(u ^ 2)) * theorem8Erf (u + δ))
        (Set.Iic t) := by
    simpa [δ, t] using theorem8GaussianJ_integrableOn_Iic_concrete δ t
  have hsplit :
      (∫ u : ℝ in Set.Iic t,
          Real.exp (-(u ^ 2)) * (1 + theorem8Erf (u + δ))) =
        (∫ u : ℝ in Set.Iic t, Real.exp (-(u ^ 2))) +
          ∫ u : ℝ in Set.Iic t,
            Real.exp (-(u ^ 2)) * theorem8Erf (u + δ) := by
    simpa [mul_add, mul_one] using integral_add hgauss hJ
  calc
    (∫ x : ℝ in Set.Iic a,
        Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj)))
        = ∫ u : ℝ in Set.Iic t,
          Real.exp (-(u ^ 2)) * (1 + theorem8Erf (u + δ)) := hshift
    _ = (∫ u : ℝ in Set.Iic t, Real.exp (-(u ^ 2))) +
          ∫ u : ℝ in Set.Iic t,
            Real.exp (-(u ^ 2)) * theorem8Erf (u + δ) := hsplit
    _ = Real.sqrt Real.pi / 2 * (1 + theorem8Erf t) +
          theorem8GaussianJ theorem8Erf δ t := by
          rw [theorem8Gaussian_integral_Iic_eq_erf]
          rfl
    _ = Real.sqrt Real.pi / 2 * (1 + theorem8Erf (a - xi)) +
          theorem8GaussianJ theorem8Erf (xi - xj) (a - xi) := by
          rfl

/--
Appendix C, Theorem 8: the paper's density/CDF expression
`∫ f_i(x) F_j(x) dx / (F_i(a)F_j(a))` for the Gaussian conditional pairwise
probability.
-/
noncomputable def theorem8GaussianPDFCDFRatioAt
    (xi xj a : ℝ) : ℝ :=
  (∫ x : ℝ in Set.Iic a,
      theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) /
    (theorem8GaussianCDF xi a * theorem8GaussianCDF xj a)

/--
Appendix C, Theorem 8: the same density/CDF ratio after clearing the common
Gaussian CDF constants, exactly as displayed in the paper before the
`t = a - x_i`, `δ = x_i - x_j` substitution.
-/
noncomputable def theorem8GaussianDensityCDFIntegralRatioAt
    (xi xj a : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) *
    (∫ x : ℝ in Set.Iic a,
      Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) /
    ((1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj)))

/--
Appendix C, Theorem 8: clearing the Gaussian density/CDF constants in the
paper's conditional probability integral formula.
-/
theorem theorem8GaussianPDFCDFRatioAt_eq_densityCDF (xi xj a : ℝ) :
    theorem8GaussianPDFCDFRatioAt xi xj a =
      theorem8GaussianDensityCDFIntegralRatioAt xi xj a := by
  let Iraw : ℝ :=
    ∫ x : ℝ in Set.Iic a,
      Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
    Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hA_ne : 1 + theorem8Erf (a - xi) ≠ 0 :=
    (theorem8Erf_one_add_pos (a - xi)).ne'
  have hB_ne : 1 + theorem8Erf (a - xj) ≠ 0 :=
    (theorem8Erf_one_add_pos (a - xj)).ne'
  have hnum :
      (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) =
        (1 / (2 * Real.sqrt Real.pi)) * Iraw := by
    dsimp [Iraw]
    rw [← integral_const_mul]
    congr 1
    ext x
    unfold theorem8GaussianPDF theorem8GaussianCDF
    field_simp [hsqrt_ne]
  unfold theorem8GaussianPDFCDFRatioAt
    theorem8GaussianDensityCDFIntegralRatioAt
  rw [hnum]
  unfold theorem8GaussianCDF
  dsimp [Iraw]
  field_simp [hsqrt_ne, hA_ne, hB_ne]

/--
Appendix C, Theorem 8: the cleared density/CDF expression is exactly the
`erf/J` conditional integral ratio used in the C.5--C.6 derivative proof.
-/
theorem theorem8GaussianDensityCDFIntegralRatioAt_eq_conditional
    (xi xj a : ℝ) :
    theorem8GaussianDensityCDFIntegralRatioAt xi xj a =
      theorem8GaussianConditionalIntegralRatioAt xi xj a := by
  have hint := theorem8Gaussian_integral_shift_split xi xj a
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
    Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hA_ne : 1 + theorem8Erf (a - xi) ≠ 0 :=
    (theorem8Erf_one_add_pos (a - xi)).ne'
  have hB_ne : 1 + theorem8Erf (a - xj) ≠ 0 :=
    (theorem8Erf_one_add_pos (a - xj)).ne'
  unfold theorem8GaussianDensityCDFIntegralRatioAt
    theorem8GaussianConditionalIntegralRatioAt
    theorem8GaussianConditionalIntegralRatio
  rw [hint]
  have harg : a - xi + (xi - xj) = a - xj := by ring
  rw [harg]
  field_simp [hsqrt_ne, hA_ne, hB_ne]

/--
Appendix C, Theorem 8: the paper's Gaussian density/CDF integral expression
has strictly positive derivative in the cutoff `a`.
-/
theorem theorem8GaussianPDFCDFRatioAt_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => theorem8GaussianPDFCDFRatioAt xi xj u) d a ∧
        0 < d := by
  obtain ⟨d, hd, hdpos⟩ :=
    theorem8GaussianConditionalIntegralRatioAt_hasDerivAt_pos
      (xi := xi) (xj := xj) (a := a) hx
  refine ⟨d, ?_, hdpos⟩
  have hdensity :
      HasDerivAt
        (fun u => theorem8GaussianDensityCDFIntegralRatioAt xi xj u)
        d a := by
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        theorem8GaussianDensityCDFIntegralRatioAt_eq_conditional xi xj u)
  exact hdensity.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u =>
      theorem8GaussianPDFCDFRatioAt_eq_densityCDF xi xj u)

/--
Appendix C, Theorem 8: canonical product probability space for two independent
Gaussian scores with means `x_i`, `x_j` and variance `1/2`.
-/
noncomputable def theorem8GaussianPairMeasure (xi xj : ℝ) : Measure (ℝ × ℝ) :=
  (ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)).prod
    (ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0))

/--
Appendix C, Theorem 8: numerator event for the canonical product bridge,
written with weak inequalities.  For continuous Gaussians this agrees in
measure with the strict paper event `X_i > X_j, X_i < a, X_j < a`.
-/
def theorem8GaussianPairNumeratorEvent (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ a ∧ p.2 ≤ p.1}

/-- Appendix C, Theorem 8: conditioning event for the product bridge. -/
def theorem8GaussianPairDenominatorEvent (a : ℝ) : Set (ℝ × ℝ) :=
  Set.Iic a ×ˢ Set.Iic a

/--
Appendix C, Theorem 8: numerator event in the strict paper syntax,
`X_i < a`, `X_j < X_i`.
-/
def theorem8GaussianPairStrictNumeratorEvent (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 < a ∧ p.2 < p.1}

/--
Appendix C, Theorem 8: strict conditioning event in the paper syntax,
`X_i < a`, `X_j < a`.
-/
def theorem8GaussianPairStrictDenominatorEvent (a : ℝ) : Set (ℝ × ℝ) :=
  Set.Iio a ×ˢ Set.Iio a

/-- Appendix C, Theorem 8: measurability of the product-bridge numerator. -/
theorem theorem8GaussianPairNumeratorEvent_measurable (a : ℝ) :
    MeasurableSet (theorem8GaussianPairNumeratorEvent a) := by
  unfold theorem8GaussianPairNumeratorEvent
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_snd measurable_fst)

/--
Appendix C, Theorem 8: measurability of the strict paper-syntax numerator.
-/
theorem theorem8GaussianPairStrictNumeratorEvent_measurable (a : ℝ) :
    MeasurableSet (theorem8GaussianPairStrictNumeratorEvent a) := by
  unfold theorem8GaussianPairStrictNumeratorEvent
  exact (measurableSet_lt measurable_fst measurable_const).inter
    (measurableSet_lt measurable_snd measurable_fst)

/--
Appendix C, Theorem 8: a Gaussian has no mass at the cutoff, so strict and
weak one-sided lower intervals have the same mass.
-/
theorem theorem8GaussianReal_Iio_eq_Iic (μ a : ℝ) :
    ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0) (Set.Iio a) =
      ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0) (Set.Iic a) := by
  have hvar : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  haveI : NoAtoms (ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0)) :=
    ProbabilityTheory.noAtoms_gaussianReal hvar
  exact measure_congr
    (Iio_ae_eq_Iic
      (μ := ProbabilityTheory.gaussianReal μ (1 / 2 : ℝ≥0)) (a := a))

/--
Appendix C, Theorem 8: Tonelli/product-measure form of the numerator event.
-/
theorem theorem8GaussianPairNumerator_measure_eq_lintegral (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairNumeratorEvent a) =
      ∫⁻ x in Set.Iic a,
        ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0) (Set.Iic x)
        ∂ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0) := by
  let μi := ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)
  let μj := ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0)
  have hmeas := theorem8GaussianPairNumeratorEvent_measurable a
  unfold theorem8GaussianPairMeasure
  change μi.prod μj (theorem8GaussianPairNumeratorEvent a) =
    ∫⁻ x in Set.Iic a, μj (Set.Iic x) ∂μi
  rw [Measure.prod_apply hmeas]
  rw [← lintegral_indicator measurableSet_Iic]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ≤ a
  · have hsection :
        Prod.mk x ⁻¹' theorem8GaussianPairNumeratorEvent a = Set.Iic x := by
        ext y
        simp [theorem8GaussianPairNumeratorEvent, hx]
    simp [hsection, hx]
  · have hsection :
        Prod.mk x ⁻¹' theorem8GaussianPairNumeratorEvent a =
          (∅ : Set ℝ) := by
        ext y
        simp [theorem8GaussianPairNumeratorEvent, hx]
    have hxnot : x ∉ Set.Iic a := by
      simpa using hx
    simp [hsection, hxnot]

/--
Appendix C, Theorem 8: Fubini/density bridge from the product numerator event
to the paper's one-dimensional Gaussian density/CDF integral.
-/
theorem theorem8GaussianPairNumerator_measure_eq_integral (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairNumeratorEvent a) =
      ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
  let μi := ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)
  let μj := ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0)
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  have h_int := theorem8GaussianPDF_mul_CDF_integrableOn xi xj a
  have h_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Iic a)]
        (fun x : ℝ => theorem8GaussianPDF xi x *
          theorem8GaussianCDF xj x) := by
    exact ae_of_all _ fun x =>
      mul_nonneg (theorem8GaussianPDF_nonneg xi x)
        (theorem8GaussianCDF_nonneg xj x)
  calc
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairNumeratorEvent a)
        = ∫⁻ x in Set.Iic a, μj (Set.Iic x) ∂μi := by
          simpa [μi, μj] using
            theorem8GaussianPairNumerator_measure_eq_lintegral xi xj a
    _ = ∫⁻ x in Set.Iic a, ENNReal.ofReal (theorem8GaussianCDF xj x) ∂μi := by
          refine setLIntegral_congr_fun measurableSet_Iic ?_
          intro x _hx
          exact theorem8GaussianReal_Iic_eq_CDF xj x
    _ = ∫⁻ x in Set.Iic a,
          ProbabilityTheory.gaussianPDF xi (1 / 2 : ℝ≥0) x *
            ENNReal.ofReal (theorem8GaussianCDF xj x) := by
          dsimp [μi]
          rw [ProbabilityTheory.gaussianReal_of_var_ne_zero xi hv]
          exact setLIntegral_withDensity_eq_setLIntegral_mul volume
            (ProbabilityTheory.measurable_gaussianPDF xi (1 / 2 : ℝ≥0))
            ((by
              have hcont : Continuous fun x : ℝ => theorem8GaussianCDF xj x := by
                unfold theorem8GaussianCDF
                exact ((theorem8Erf_continuous.comp
                  (continuous_id.sub continuous_const)).const_add 1).div_const 2
              exact hcont.measurable.ennreal_ofReal) : Measurable fun x : ℝ =>
                ENNReal.ofReal (theorem8GaussianCDF xj x))
            measurableSet_Iic
    _ = ∫⁻ x in Set.Iic a,
          ENNReal.ofReal
            (theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
          refine setLIntegral_congr_fun measurableSet_Iic ?_
          intro x _hx
          change ProbabilityTheory.gaussianPDF xi (1 / 2 : ℝ≥0) x *
              ENNReal.ofReal (theorem8GaussianCDF xj x) =
            ENNReal.ofReal
              (theorem8GaussianPDF xi x * theorem8GaussianCDF xj x)
          rw [← theorem8GaussianPDF_ofReal_eq_gaussianPDF_half]
          rw [ENNReal.ofReal_mul (theorem8GaussianPDF_nonneg xi x)]
    _ = ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
          simpa using
            (ofReal_integral_eq_lintegral_ofReal
              (μ := volume.restrict (Set.Iic a)) h_int h_nonneg).symm

/--
Appendix C, Theorem 8: Tonelli/product-measure form of the strict
paper-syntax numerator event.
-/
theorem theorem8GaussianPairStrictNumerator_measure_eq_lintegral (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairStrictNumeratorEvent a) =
      ∫⁻ x in Set.Iio a,
        ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0) (Set.Iio x)
        ∂ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0) := by
  let μi := ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)
  let μj := ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0)
  have hmeas := theorem8GaussianPairStrictNumeratorEvent_measurable a
  unfold theorem8GaussianPairMeasure
  change μi.prod μj (theorem8GaussianPairStrictNumeratorEvent a) =
    ∫⁻ x in Set.Iio a, μj (Set.Iio x) ∂μi
  rw [Measure.prod_apply hmeas]
  rw [← lintegral_indicator measurableSet_Iio]
  refine lintegral_congr fun x => ?_
  by_cases hx : x < a
  · have hsection :
        Prod.mk x ⁻¹' theorem8GaussianPairStrictNumeratorEvent a = Set.Iio x := by
        ext y
        simp [theorem8GaussianPairStrictNumeratorEvent, hx]
    simp [hsection, hx]
  · have hsection :
        Prod.mk x ⁻¹' theorem8GaussianPairStrictNumeratorEvent a =
          (∅ : Set ℝ) := by
        ext y
        simp [theorem8GaussianPairStrictNumeratorEvent, hx]
    have hxnot : x ∉ Set.Iio a := by
      simpa using hx
    simp [hsection, hxnot]

/--
Appendix C, Theorem 8: strict paper-syntax numerator has the same mass as the
weak bridge numerator, hence the same Gaussian density/CDF integral.
-/
theorem theorem8GaussianPairStrictNumerator_measure_eq_integral (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairStrictNumeratorEvent a) =
      ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
  let μi := ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)
  let μj := ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0)
  have hvar : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  haveI : NoAtoms μi := ProbabilityTheory.noAtoms_gaussianReal hvar
  calc
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairStrictNumeratorEvent a)
        = ∫⁻ x in Set.Iio a, μj (Set.Iio x) ∂μi := by
          simpa [μi, μj] using
            theorem8GaussianPairStrictNumerator_measure_eq_lintegral xi xj a
    _ = ∫⁻ x in Set.Iio a, μj (Set.Iic x) ∂μi := by
          refine setLIntegral_congr_fun measurableSet_Iio ?_
          intro x _hx
          exact theorem8GaussianReal_Iio_eq_Iic xj x
    _ = ∫⁻ x in Set.Iic a, μj (Set.Iic x) ∂μi := by
          exact setLIntegral_congr
            (μ := μi) (f := fun x : ℝ => μj (Set.Iic x))
            (Iio_ae_eq_Iic (μ := μi) (a := a))
    _ = theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairNumeratorEvent a) := by
          simpa [μi, μj] using
            (theorem8GaussianPairNumerator_measure_eq_lintegral xi xj a).symm
    _ = ENNReal.ofReal
        (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
          exact theorem8GaussianPairNumerator_measure_eq_integral xi xj a

/--
Appendix C, Theorem 8: product-measure mass of the conditioning event.
-/
theorem theorem8GaussianPairDenominator_measure_eq (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairDenominatorEvent a) =
      ENNReal.ofReal
        (theorem8GaussianCDF xi a * theorem8GaussianCDF xj a) := by
  unfold theorem8GaussianPairMeasure theorem8GaussianPairDenominatorEvent
  rw [Measure.prod_prod]
  rw [theorem8GaussianReal_Iic_eq_CDF xi a,
    theorem8GaussianReal_Iic_eq_CDF xj a]
  rw [← ENNReal.ofReal_mul (theorem8GaussianCDF_nonneg xi a)]

/--
Appendix C, Theorem 8: product-measure mass of the strict paper-syntax
conditioning event.
-/
theorem theorem8GaussianPairStrictDenominator_measure_eq (xi xj a : ℝ) :
    theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairStrictDenominatorEvent a) =
      ENNReal.ofReal
        (theorem8GaussianCDF xi a * theorem8GaussianCDF xj a) := by
  unfold theorem8GaussianPairMeasure theorem8GaussianPairStrictDenominatorEvent
  rw [Measure.prod_prod]
  rw [theorem8GaussianReal_Iio_eq_Iic xi a,
    theorem8GaussianReal_Iio_eq_Iic xj a]
  rw [theorem8GaussianReal_Iic_eq_CDF xi a,
    theorem8GaussianReal_Iic_eq_CDF xj a]
  rw [← ENNReal.ofReal_mul (theorem8GaussianCDF_nonneg xi a)]

/--
Appendix C, Theorem 8: canonical product-probability conditional ratio
corresponding to the source expression
`Pr[X_i > X_j | X_i < a, X_j < a]`, stated with weak inequalities on null
boundaries.
-/
noncomputable def theorem8GaussianProductConditionalRatioAt
    (xi xj a : ℝ) : ℝ :=
  (theorem8GaussianPairMeasure xi xj
      (theorem8GaussianPairNumeratorEvent a)).toReal /
    (theorem8GaussianPairMeasure xi xj
      (theorem8GaussianPairDenominatorEvent a)).toReal

/--
Appendix C, Theorem 8: canonical product-probability conditional ratio in the
paper's strict event syntax.
-/
noncomputable def theorem8GaussianProductStrictConditionalRatioAt
    (xi xj a : ℝ) : ℝ :=
  (theorem8GaussianPairMeasure xi xj
      (theorem8GaussianPairStrictNumeratorEvent a)).toReal /
    (theorem8GaussianPairMeasure xi xj
      (theorem8GaussianPairStrictDenominatorEvent a)).toReal

/--
Appendix C, Theorem 8: the canonical product-probability ratio equals the
paper's Gaussian density/CDF ratio.
-/
theorem theorem8GaussianProductConditionalRatioAt_eq_pdf_cdf
    (xi xj a : ℝ) :
    theorem8GaussianProductConditionalRatioAt xi xj a =
      theorem8GaussianPDFCDFRatioAt xi xj a := by
  have hI_nonneg :
      0 ≤
        (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
    refine integral_nonneg fun x => ?_
    exact mul_nonneg (theorem8GaussianPDF_nonneg xi x)
      (theorem8GaussianCDF_nonneg xj x)
  have hden_nonneg :
      0 ≤ theorem8GaussianCDF xi a * theorem8GaussianCDF xj a :=
    mul_nonneg (theorem8GaussianCDF_nonneg xi a)
      (theorem8GaussianCDF_nonneg xj a)
  unfold theorem8GaussianProductConditionalRatioAt
    theorem8GaussianPDFCDFRatioAt
  rw [theorem8GaussianPairNumerator_measure_eq_integral,
    theorem8GaussianPairDenominator_measure_eq]
  rw [ENNReal.toReal_ofReal hI_nonneg, ENNReal.toReal_ofReal hden_nonneg]

/--
Appendix C, Theorem 8: the strict paper-syntax product-probability ratio equals
the paper's Gaussian density/CDF ratio.
-/
theorem theorem8GaussianProductStrictConditionalRatioAt_eq_pdf_cdf
    (xi xj a : ℝ) :
    theorem8GaussianProductStrictConditionalRatioAt xi xj a =
      theorem8GaussianPDFCDFRatioAt xi xj a := by
  have hI_nonneg :
      0 ≤
        (∫ x : ℝ in Set.Iic a,
          theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) := by
    refine integral_nonneg fun x => ?_
    exact mul_nonneg (theorem8GaussianPDF_nonneg xi x)
      (theorem8GaussianCDF_nonneg xj x)
  have hden_nonneg :
      0 ≤ theorem8GaussianCDF xi a * theorem8GaussianCDF xj a :=
    mul_nonneg (theorem8GaussianCDF_nonneg xi a)
      (theorem8GaussianCDF_nonneg xj a)
  unfold theorem8GaussianProductStrictConditionalRatioAt
    theorem8GaussianPDFCDFRatioAt
  rw [theorem8GaussianPairStrictNumerator_measure_eq_integral,
    theorem8GaussianPairStrictDenominator_measure_eq]
  rw [ENNReal.toReal_ofReal hI_nonneg, ENNReal.toReal_ofReal hden_nonneg]

/--
Appendix C, Theorem 8: the canonical product-probability conditional ratio has
strictly positive derivative in the cutoff `a`.
-/
theorem theorem8GaussianProductConditionalRatioAt_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => theorem8GaussianProductConditionalRatioAt xi xj u)
        d a ∧
        0 < d := by
  obtain ⟨d, hd, hdpos⟩ :=
    theorem8GaussianPDFCDFRatioAt_hasDerivAt_pos
      (xi := xi) (xj := xj) (a := a) hx
  refine ⟨d, ?_, hdpos⟩
  exact hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u =>
      theorem8GaussianProductConditionalRatioAt_eq_pdf_cdf xi xj u)

/--
Appendix C, Theorem 8: the strict paper-syntax product-probability conditional
ratio has strictly positive derivative in the cutoff `a`.
-/
theorem theorem8GaussianProductStrictConditionalRatioAt_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => theorem8GaussianProductStrictConditionalRatioAt xi xj u)
        d a ∧
        0 < d := by
  obtain ⟨d, hd, hdpos⟩ :=
    theorem8GaussianPDFCDFRatioAt_hasDerivAt_pos
      (xi := xi) (xj := xj) (a := a) hx
  refine ⟨d, ?_, hdpos⟩
  exact hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u =>
      theorem8GaussianProductStrictConditionalRatioAt_eq_pdf_cdf xi xj u)

/--
Appendix C, Theorem 8: encode an arbitrary Gaussian standard deviation as the
variance parameter used by Mathlib's `gaussianReal`.
-/
def theorem8GaussianVarianceFromStd (σ : ℝ) : ℝ≥0 :=
  EconCSLib.Probability.gaussianVarianceFromStd σ

/--
Appendix C, Theorem 8: the positive scale that sends standard deviation `σ` to
the paper's canonical standard deviation `1 / sqrt 2`.
-/
noncomputable def theorem8GaussianCanonicalScale (σ : ℝ) : ℝ :=
  EconCSLib.Probability.canonicalHalfVarianceScale σ

/-- Appendix C, Theorem 8: the canonical Gaussian scale is positive. -/
theorem theorem8GaussianCanonicalScale_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < theorem8GaussianCanonicalScale σ := by
  exact EconCSLib.Probability.canonicalHalfVarianceScale_pos hσ

/-- Appendix C, Theorem 8: the canonical Gaussian scale is nonzero. -/
theorem theorem8GaussianCanonicalScale_ne_zero {σ : ℝ} (hσ : 0 < σ) :
    theorem8GaussianCanonicalScale σ ≠ 0 :=
  ne_of_gt (theorem8GaussianCanonicalScale_pos hσ)

/--
Appendix C, Theorem 8: multiplying a variance-`σ^2` Gaussian by the canonical
scale gives variance `1/2`.
-/
theorem theorem8GaussianCanonicalScale_sq_mul_variance
    {σ : ℝ} (hσ : 0 < σ) :
    NNReal.mk ((theorem8GaussianCanonicalScale σ) ^ 2)
        (sq_nonneg (theorem8GaussianCanonicalScale σ)) *
      theorem8GaussianVarianceFromStd σ =
        (1 / 2 : ℝ≥0) := by
  simpa [theorem8GaussianCanonicalScale, theorem8GaussianVarianceFromStd] using
    EconCSLib.Probability.canonicalHalfVarianceScale_sq_mul_gaussianVarianceFromStd hσ

/--
Appendix C, Theorem 8: Mathlib's one-dimensional Gaussian scaling theorem,
specialized to the paper's `σ` to `1 / sqrt 2` normalization.
-/
theorem theorem8GaussianReal_map_canonicalScale
    {σ μ : ℝ} (hσ : 0 < σ) :
    (ProbabilityTheory.gaussianReal μ
        (theorem8GaussianVarianceFromStd σ)).map
        (fun x => theorem8GaussianCanonicalScale σ * x) =
      ProbabilityTheory.gaussianReal
        (theorem8GaussianCanonicalScale σ * μ) (1 / 2 : ℝ≥0) := by
  simpa [theorem8GaussianCanonicalScale, theorem8GaussianVarianceFromStd] using
    EconCSLib.Probability.gaussianReal_map_canonicalHalfVarianceScale
      (σ := σ) (μ := μ) hσ

/--
Appendix C, Theorem 8: product measure for independent Gaussians with arbitrary
positive standard deviation `σ`.
-/
noncomputable def theorem8GaussianPairMeasureStd
    (σ xi xj : ℝ) : Measure (ℝ × ℝ) :=
  EconCSLib.Probability.independentGaussianPairMeasureWithStd σ xi xj

/--
Appendix C, Theorem 8: scale both coordinates of the Gaussian product space.
-/
noncomputable def theorem8GaussianPairCanonicalScaleMap
    (σ : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  EconCSLib.Probability.pairCanonicalHalfVarianceScaleMap σ

/--
Appendix C, Theorem 8: the arbitrary-`σ` product measure maps to the canonical
variance-`1/2` product measure.
-/
theorem theorem8GaussianPairMeasureStd_map_canonicalScale
    {σ xi xj : ℝ} (hσ : 0 < σ) :
    (theorem8GaussianPairMeasureStd σ xi xj).map
        (theorem8GaussianPairCanonicalScaleMap σ) =
      theorem8GaussianPairMeasure
        (theorem8GaussianCanonicalScale σ * xi)
        (theorem8GaussianCanonicalScale σ * xj) := by
  simpa [theorem8GaussianPairMeasureStd, theorem8GaussianPairCanonicalScaleMap,
    theorem8GaussianPairMeasure, theorem8GaussianCanonicalScale,
    theorem8GaussianVarianceFromStd,
    EconCSLib.Probability.independentGaussianPairMeasureWithStd,
    EconCSLib.Probability.pairCanonicalHalfVarianceScaleMap,
    EconCSLib.Probability.independentGaussianPairMeasureHalf] using
      EconCSLib.Probability.independentGaussianPairMeasureWithStd_map_canonicalHalfVarianceScale
        (σ := σ) (xi := xi) (xj := xj) hσ

/--
Appendix C, Theorem 8: under positive scaling, the strict numerator event with
cutoff `scale * a` pulls back to the strict numerator event with cutoff `a`.
-/
theorem theorem8GaussianPairCanonicalScaleMap_preimage_strict_numerator
    {σ a : ℝ} (hσ : 0 < σ) :
    (theorem8GaussianPairCanonicalScaleMap σ) ⁻¹'
        theorem8GaussianPairStrictNumeratorEvent
          (theorem8GaussianCanonicalScale σ * a) =
        theorem8GaussianPairStrictNumeratorEvent a := by
  simpa [theorem8GaussianPairCanonicalScaleMap,
    theorem8GaussianPairStrictNumeratorEvent, theorem8GaussianCanonicalScale,
    EconCSLib.Probability.pairCanonicalHalfVarianceScaleMap,
    EconCSLib.Probability.pairStrictWinnerBelowEvent] using
      EconCSLib.Probability.pairCanonicalHalfVarianceScaleMap_preimage_strictWinnerBelow
        (σ := σ) (a := a) hσ

/--
Appendix C, Theorem 8: under positive scaling, the strict conditioning event
with cutoff `scale * a` pulls back to the strict conditioning event with cutoff
`a`.
-/
theorem theorem8GaussianPairCanonicalScaleMap_preimage_strict_denominator
    {σ a : ℝ} (hσ : 0 < σ) :
    (theorem8GaussianPairCanonicalScaleMap σ) ⁻¹'
        theorem8GaussianPairStrictDenominatorEvent
          (theorem8GaussianCanonicalScale σ * a) =
        theorem8GaussianPairStrictDenominatorEvent a := by
  simpa [theorem8GaussianPairCanonicalScaleMap,
    theorem8GaussianPairStrictDenominatorEvent, theorem8GaussianCanonicalScale,
    EconCSLib.Probability.pairCanonicalHalfVarianceScaleMap,
    EconCSLib.Probability.pairStrictBothBelowEvent] using
      EconCSLib.Probability.pairCanonicalHalfVarianceScaleMap_preimage_strictBothBelow
        (σ := σ) (a := a) hσ

/--
Appendix C, Theorem 8: arbitrary-`σ` strict numerator mass equals the
corresponding canonical strict numerator mass after scaling.
-/
theorem theorem8GaussianPairMeasureStd_strict_numerator_eq_scaled
    {σ xi xj a : ℝ} (hσ : 0 < σ) :
    theorem8GaussianPairMeasureStd σ xi xj
        (theorem8GaussianPairStrictNumeratorEvent a) =
      theorem8GaussianPairMeasure
        (theorem8GaussianCanonicalScale σ * xi)
        (theorem8GaussianCanonicalScale σ * xj)
        (theorem8GaussianPairStrictNumeratorEvent
          (theorem8GaussianCanonicalScale σ * a)) := by
  simpa [theorem8GaussianPairMeasureStd,
    theorem8GaussianPairStrictNumeratorEvent, theorem8GaussianPairMeasure,
    theorem8GaussianCanonicalScale, theorem8GaussianVarianceFromStd,
    EconCSLib.Probability.independentGaussianPairMeasureWithStd,
    EconCSLib.Probability.independentGaussianPairMeasureHalf,
    EconCSLib.Probability.pairStrictWinnerBelowEvent] using
      EconCSLib.Probability.independentGaussianPairMeasureWithStd_strictWinnerBelow_eq_scaled
        (σ := σ) (xi := xi) (xj := xj) (a := a) hσ

/--
Appendix C, Theorem 8: arbitrary-`σ` strict denominator mass equals the
corresponding canonical strict denominator mass after scaling.
-/
theorem theorem8GaussianPairMeasureStd_strict_denominator_eq_scaled
    {σ xi xj a : ℝ} (hσ : 0 < σ) :
    theorem8GaussianPairMeasureStd σ xi xj
        (theorem8GaussianPairStrictDenominatorEvent a) =
      theorem8GaussianPairMeasure
        (theorem8GaussianCanonicalScale σ * xi)
        (theorem8GaussianCanonicalScale σ * xj)
        (theorem8GaussianPairStrictDenominatorEvent
          (theorem8GaussianCanonicalScale σ * a)) := by
  simpa [theorem8GaussianPairMeasureStd,
    theorem8GaussianPairStrictDenominatorEvent, theorem8GaussianPairMeasure,
    theorem8GaussianCanonicalScale, theorem8GaussianVarianceFromStd,
    EconCSLib.Probability.independentGaussianPairMeasureWithStd,
    EconCSLib.Probability.independentGaussianPairMeasureHalf,
    EconCSLib.Probability.pairStrictBothBelowEvent] using
      EconCSLib.Probability.independentGaussianPairMeasureWithStd_strictBothBelow_eq_scaled
        (σ := σ) (xi := xi) (xj := xj) (a := a) hσ

/--
Appendix C, Theorem 8: strict conditional probability ratio for independent
Gaussian scores with arbitrary positive standard deviation `σ`.
-/
noncomputable def theorem8GaussianProductStrictConditionalRatioAtStd
    (σ xi xj a : ℝ) : ℝ :=
  (theorem8GaussianPairMeasureStd σ xi xj
      (theorem8GaussianPairStrictNumeratorEvent a)).toReal /
    (theorem8GaussianPairMeasureStd σ xi xj
      (theorem8GaussianPairStrictDenominatorEvent a)).toReal

/--
Appendix C, Theorem 8: the arbitrary-`σ` strict conditional probability ratio
is the canonical variance-`1/2` ratio after scaling values and cutoff.
-/
theorem theorem8GaussianProductStrictConditionalRatioAtStd_eq_scaled
    {σ xi xj a : ℝ} (hσ : 0 < σ) :
    theorem8GaussianProductStrictConditionalRatioAtStd σ xi xj a =
      theorem8GaussianProductStrictConditionalRatioAt
        (theorem8GaussianCanonicalScale σ * xi)
        (theorem8GaussianCanonicalScale σ * xj)
        (theorem8GaussianCanonicalScale σ * a) := by
  simpa [theorem8GaussianProductStrictConditionalRatioAtStd,
    theorem8GaussianProductStrictConditionalRatioAt,
    theorem8GaussianPairMeasureStd, theorem8GaussianPairMeasure,
    theorem8GaussianPairStrictNumeratorEvent,
    theorem8GaussianPairStrictDenominatorEvent,
    theorem8GaussianCanonicalScale, theorem8GaussianVarianceFromStd,
    EconCSLib.Probability.independentGaussianStrictConditionalWinnerRatioWithStd,
    EconCSLib.Probability.independentGaussianStrictConditionalWinnerRatioHalf,
    EconCSLib.Probability.independentGaussianPairMeasureWithStd,
    EconCSLib.Probability.independentGaussianPairMeasureHalf,
    EconCSLib.Probability.pairStrictWinnerBelowEvent,
    EconCSLib.Probability.pairStrictBothBelowEvent] using
      EconCSLib.Probability.independentGaussianStrictConditionalWinnerRatioWithStd_eq_scaled
        (σ := σ) (xi := xi) (xj := xj) (a := a) hσ

/--
Appendix C, Theorem 8: the paper's arbitrary-`σ` strict conditional probability
ratio has strictly positive derivative in the cutoff `a`.  This formalizes the
source proof's WLOG reduction to `σ = 1 / sqrt 2` by an explicit positive
scaling of scores, values, and cutoff.
-/
theorem theorem8GaussianProductStrictConditionalRatioAtStd_hasDerivAt_pos
    {σ xi xj a : ℝ} (hσ : 0 < σ) (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u => theorem8GaussianProductStrictConditionalRatioAtStd σ xi xj u)
        d a ∧
        0 < d := by
  let c := theorem8GaussianCanonicalScale σ
  have hc : 0 < c := theorem8GaussianCanonicalScale_pos hσ
  have hxc : c * xj < c * xi :=
    mul_lt_mul_of_pos_left hx hc
  obtain ⟨d, hd, hdpos⟩ :=
    theorem8GaussianProductStrictConditionalRatioAt_hasDerivAt_pos
      (xi := c * xi) (xj := c * xj) (a := c * a) hxc
  have hlin : HasDerivAt (fun u : ℝ => c * u) c a := by
    simpa using (hasDerivAt_id a).const_mul c
  refine ⟨d * c, ?_, mul_pos hdpos hc⟩
  have hcomp :
      HasDerivAt
        (fun u : ℝ =>
          theorem8GaussianProductStrictConditionalRatioAt
            (c * xi) (c * xj) (c * u))
        (d * c) a := by
    exact hd.comp a hlin
  exact hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u => by
      simpa [c] using
        theorem8GaussianProductStrictConditionalRatioAtStd_eq_scaled
          (σ := σ) (xi := xi) (xj := xj) (a := u) hσ)

/-! ## Contraction geometry for RUM realizations -/

/--
The paper's contraction map on one coordinate:
`r' = x + t * (r - x)`, where `x` is the candidate's true value and
`0 ≤ t ≤ 1` corresponds to `θH / θA`.
-/
noncomputable def rumContractScore (t x r : ℝ) : ℝ :=
  EconCSLib.Probability.rumContractScore t x r

theorem rumContractScore_eq_affine (t x r : ℝ) :
    rumContractScore t x r = (1 - t) * x + t * r := by
  exact EconCSLib.Probability.rumContractScore_eq_affine t x r

theorem rumContractScore_sub
    (t xi xj ri rj : ℝ) :
    rumContractScore t xi ri - rumContractScore t xj rj =
      (1 - t) * (xi - xj) + t * (ri - rj) := by
  exact EconCSLib.Probability.rumContractScore_sub t xi xj ri rj

/-- Candidate `x₁` is weakly first among three realized scores. -/
def rum3TopFirstByScores (s1 s2 s3 : ℝ) : Prop :=
  EconCSLib.SocialChoice.Ranking.rum3TopFirstByScores s1 s2 s3

/-- Candidate `x₂` strictly beats `x₁` and weakly beats `x₃`. -/
def rum3MiddleBeatsTopByScores (s1 s2 s3 : ℝ) : Prop :=
  EconCSLib.SocialChoice.Ranking.rum3MiddleBeatsTopByScores s1 s2 s3

/-- Candidate `x₃` is weakly first among three realized scores. -/
def rum3BottomFirstByScores (s1 s2 s3 : ℝ) : Prop :=
  EconCSLib.SocialChoice.Ranking.rum3BottomFirstByScores s1 s2 s3

/--
Contraction cannot reverse an already-correct weak order between two candidates.
-/
theorem rumContractScore_preserves_weak_order
    {t xi xj ri rj : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : xj ≤ xi) (hr : rj ≤ ri) :
    rumContractScore t xj rj ≤ rumContractScore t xi ri := by
  exact EconCSLib.Probability.rumContractScore_preserves_weak_order
    ht0 ht1 hx hr

/--
Strict version of the contraction order lemma.  If both true values and realized
scores put candidate `i` above candidate `j`, then contraction keeps `i` strictly
above `j`.
-/
theorem rumContractScore_preserves_strict_order
    {t xi xj ri rj : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : xj < xi) (hr : rj < ri) :
    rumContractScore t xj rj < rumContractScore t xi ri := by
  exact EconCSLib.Probability.rumContractScore_preserves_strict_order
    ht0 ht1 hx hr

/--
Three-candidate top-first preservation: if `x₁` is first before contraction,
it is still first after contraction.
-/
theorem rum3_contract_top_first_of_original_top_first
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 ≤ x1) (hx13 : x3 ≤ x1)
    (hr12 : r2 ≤ r1) (hr13 : r3 ≤ r1) :
    rumContractScore t x2 r2 ≤ rumContractScore t x1 r1 ∧
      rumContractScore t x3 r3 ≤ rumContractScore t x1 r1 :=
  EconCSLib.Probability.rum3_contract_top_first_of_original_top_first
    ht0 ht1 hx12 hx13 hr12 hr13

/--
Three-candidate bottom-first reflection: if the lowest-value candidate `x₃` is
first after contraction, then it was already first before contraction.
-/
theorem rum3_contract_bottom_first_imp_original_bottom_first
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx31 : x3 < x1) (hx32 : x3 < x2)
    (hc31 : rumContractScore t x1 r1 ≤ rumContractScore t x3 r3)
    (hc32 : rumContractScore t x2 r2 ≤ rumContractScore t x3 r3) :
    r1 ≤ r3 ∧ r2 ≤ r3 := by
  exact EconCSLib.Probability.rum3_contract_bottom_first_imp_original_bottom_first
    ht0 ht1 hx31 hx32 hc31 hc32

/--
Strict bottom-first reflection for a genuine contraction (`t < 1`).

If the lowest-value candidate `x₃` is weakly first after contraction, then its
raw realized score was strictly above both higher-valued candidates.  This is
the continuous-paper way to avoid a pointwise no-tie assumption in the concrete
score-ranking bridge.
-/
theorem rum3_contract_bottom_first_imp_original_bottom_first_strict_of_t_lt_one
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hx31 : x3 < x1) (hx32 : x3 < x2)
    (hc31 : rumContractScore t x1 r1 ≤ rumContractScore t x3 r3)
    (hc32 : rumContractScore t x2 r2 ≤ rumContractScore t x3 r3) :
    r1 < r3 ∧ r2 < r3 := by
  exact EconCSLib.Probability.rum3_contract_bottom_first_imp_original_bottom_first_strict_of_t_lt_one
    ht0 htlt1 hx31 hx32 hc31 hc32

/-! ## Concrete three-score rankings -/

/-- The concrete ranking `[x₁, x₂, x₃]`. -/
def rum3Ranking012 : Ranking 1 :=
  EconCSLib.SocialChoice.Ranking.rum3Ranking012

/-- The concrete ranking `[x₁, x₃, x₂]`. -/
def rum3Ranking021 : Ranking 1 :=
  EconCSLib.SocialChoice.Ranking.rum3Ranking021

/-- The concrete ranking `[x₂, x₁, x₃]`. -/
def rum3Ranking102 : Ranking 1 :=
  EconCSLib.SocialChoice.Ranking.rum3Ranking102

/-- The concrete ranking `[x₂, x₃, x₁]`. -/
def rum3Ranking120 : Ranking 1 :=
  EconCSLib.SocialChoice.Ranking.rum3Ranking120

/-- The concrete ranking `[x₃, x₁, x₂]`. -/
def rum3Ranking201 : Ranking 1 :=
  EconCSLib.SocialChoice.Ranking.rum3Ranking201

/-- The concrete ranking `[x₃, x₂, x₁]`. -/
def rum3Ranking210 : Ranking 1 :=
  EconCSLib.SocialChoice.Ranking.rum3Ranking210

@[simp] theorem rum3Ranking012_apply_zero :
    rum3Ranking012 (0 : Candidate 1) = (0 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking012_apply_zero

@[simp] theorem rum3Ranking012_apply_one :
    rum3Ranking012 (1 : Candidate 1) = (1 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking012_apply_one

@[simp] theorem rum3Ranking012_apply_two :
    rum3Ranking012 (2 : Candidate 1) = (2 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking012_apply_two

@[simp] theorem rum3Ranking021_apply_zero :
    rum3Ranking021 (0 : Candidate 1) = (0 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking021_apply_zero

@[simp] theorem rum3Ranking021_apply_one :
    rum3Ranking021 (1 : Candidate 1) = (2 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking021_apply_one

@[simp] theorem rum3Ranking021_apply_two :
    rum3Ranking021 (2 : Candidate 1) = (1 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking021_apply_two

@[simp] theorem rum3Ranking102_apply_zero :
    rum3Ranking102 (0 : Candidate 1) = (1 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking102_apply_zero

@[simp] theorem rum3Ranking102_apply_one :
    rum3Ranking102 (1 : Candidate 1) = (0 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking102_apply_one

@[simp] theorem rum3Ranking102_apply_two :
    rum3Ranking102 (2 : Candidate 1) = (2 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking102_apply_two

@[simp] theorem rum3Ranking120_apply_zero :
    rum3Ranking120 (0 : Candidate 1) = (1 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking120_apply_zero

@[simp] theorem rum3Ranking120_apply_one :
    rum3Ranking120 (1 : Candidate 1) = (2 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking120_apply_one

@[simp] theorem rum3Ranking120_apply_two :
    rum3Ranking120 (2 : Candidate 1) = (0 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking120_apply_two

@[simp] theorem rum3Ranking201_apply_zero :
    rum3Ranking201 (0 : Candidate 1) = (2 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking201_apply_zero

@[simp] theorem rum3Ranking201_apply_one :
    rum3Ranking201 (1 : Candidate 1) = (0 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking201_apply_one

@[simp] theorem rum3Ranking201_apply_two :
    rum3Ranking201 (2 : Candidate 1) = (1 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking201_apply_two

@[simp] theorem rum3Ranking210_apply_zero :
    rum3Ranking210 (0 : Candidate 1) = (2 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking210_apply_zero

@[simp] theorem rum3Ranking210_apply_one :
    rum3Ranking210 (1 : Candidate 1) = (1 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking210_apply_one

@[simp] theorem rum3Ranking210_apply_two :
    rum3Ranking210 (2 : Candidate 1) = (0 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3Ranking210_apply_two

/--
Ranking induced by three realized scores, ordered descending by score and
breaking ties in favor of the lower-indexed candidate.  The paper's continuous
RUM has zero tie probability for ordinary densities, but this deterministic
tie convention makes the score-to-ranking map total.
-/
noncomputable def rum3RankByScores (s1 s2 s3 : ℝ) : Ranking 1 :=
  EconCSLib.SocialChoice.Ranking.rum3RankByScores s1 s2 s3

/-- Realized scores have no pairwise ties. -/
def rum3NoTiesByScores (s1 s2 s3 : ℝ) : Prop :=
  EconCSLib.SocialChoice.Ranking.rum3NoTiesByScores s1 s2 s3

/-- Ranking map induced by three score-coordinate functions. -/
noncomputable def rum3RankByScoreFns {Ω : Type*}
    (r1 r2 r3 : Ω → ℝ) : Ω → Ranking 1 :=
  fun ω => rum3RankByScores (r1 ω) (r2 ω) (r3 ω)

/-- Ranking map induced by contracted score-coordinate functions. -/
noncomputable def rum3ContractRankByScoreFns {Ω : Type*}
    (t x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) : Ω → Ranking 1 :=
  fun ω => rum3RankByScores
    (rumContractScore t x1 (r1 ω))
    (rumContractScore t x2 (r2 ω))
    (rumContractScore t x3 (r3 ω))

theorem rumContractScore_measurable
    {Ω : Type*} [MeasurableSpace Ω] {r : Ω → ℝ}
    (hr : Measurable r) (t x : ℝ) :
    Measurable (fun ω => rumContractScore t x (r ω)) := by
  unfold rumContractScore
  exact measurable_const.add (measurable_const.mul (hr.sub measurable_const))

theorem rum3RankByScoreFns_measurable
    {Ω : Type*} [MeasurableSpace Ω] {r1 r2 r3 : Ω → ℝ}
    (hr1 : Measurable r1) (hr2 : Measurable r2) (hr3 : Measurable r3) :
    Measurable (rum3RankByScoreFns r1 r2 r3) := by
  unfold rum3RankByScoreFns rum3RankByScores
    EconCSLib.SocialChoice.Ranking.rum3RankByScores
  refine Measurable.ite
    ((measurableSet_le hr2 hr1).inter (measurableSet_le hr3 hr1)) ?_ ?_
  · exact Measurable.ite (measurableSet_le hr3 hr2) measurable_const measurable_const
  · refine Measurable.ite
      ((measurableSet_lt hr1 hr2).inter (measurableSet_le hr3 hr2)) ?_ ?_
    · exact Measurable.ite (measurableSet_le hr3 hr1) measurable_const measurable_const
    · exact Measurable.ite (measurableSet_le hr2 hr1) measurable_const measurable_const

theorem rum3ContractRankByScoreFns_measurable
    {Ω : Type*} [MeasurableSpace Ω] {r1 r2 r3 : Ω → ℝ}
    (hr1 : Measurable r1) (hr2 : Measurable r2) (hr3 : Measurable r3)
    (t x1 x2 x3 : ℝ) :
    Measurable (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3) :=
  rum3RankByScoreFns_measurable
    (rumContractScore_measurable hr1 t x1)
    (rumContractScore_measurable hr2 t x2)
    (rumContractScore_measurable hr3 t x3)

@[simp] theorem firstChoice_rum3RankByScores (s1 s2 s3 : ℝ) :
    firstChoice (rum3RankByScores s1 s2 s3) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then (0 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then (1 : Candidate 1)
      else (2 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.firstChoice_rum3RankByScores s1 s2 s3

@[simp] theorem secondChoice_rum3RankByScores (s1 s2 s3 : ℝ) :
    secondChoice (rum3RankByScores s1 s2 s3) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then
        if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then
        if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1)
      else
        if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.secondChoice_rum3RankByScores s1 s2 s3

@[simp] theorem rum3RankByScores_apply_zero (s1 s2 s3 : ℝ) :
    rum3RankByScores s1 s2 s3 (0 : Candidate 1) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then (0 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then (1 : Candidate 1)
      else (2 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_apply_zero s1 s2 s3

@[simp] theorem rum3RankByScores_apply_one (s1 s2 s3 : ℝ) :
    rum3RankByScores s1 s2 s3 (1 : Candidate 1) =
      if s2 ≤ s1 ∧ s3 ≤ s1 then
        if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1)
      else if s1 < s2 ∧ s3 ≤ s2 then
        if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1)
      else
        if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_apply_one s1 s2 s3

@[simp] theorem bestRemainingAfter_rum3RankByScores_remove0
    (s1 s2 s3 : ℝ) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
      if s3 ≤ s2 then (1 : Candidate 1) else (2 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.bestRemainingAfter_rum3RankByScores_remove0
    s1 s2 s3

@[simp] theorem bestRemainingAfter_rum3RankByScores_remove1
    (s1 s2 s3 : ℝ) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (1 : Candidate 1) =
      if s3 ≤ s1 then (0 : Candidate 1) else (2 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.bestRemainingAfter_rum3RankByScores_remove1
    s1 s2 s3

@[simp] theorem bestRemainingAfter_rum3RankByScores_remove2
    (s1 s2 s3 : ℝ) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (2 : Candidate 1) =
      if s2 ≤ s1 then (0 : Candidate 1) else (1 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.bestRemainingAfter_rum3RankByScores_remove2
    s1 s2 s3

theorem rum3RankByScores_firstChoice_of_top_scores
    {s1 s2 s3 : ℝ}
    (h : rum3TopFirstByScores s1 s2 s3) :
    firstChoice (rum3RankByScores s1 s2 s3) = (0 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_firstChoice_of_top_scores h

theorem rum3RankByScores_top_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (0 : Candidate 1)) :
    rum3TopFirstByScores s1 s2 s3 := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_top_scores_of_firstChoice h

theorem rum3RankByScores_bottom_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1)) :
    rum3BottomFirstByScores s1 s2 s3 := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_bottom_scores_of_firstChoice h

theorem rum3RankByScores_firstChoice_of_bottom_scores_of_noTies
    {s1 s2 s3 : ℝ}
    (hnt : rum3NoTiesByScores s1 s2 s3)
    (h : rum3BottomFirstByScores s1 s2 s3) :
    firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_firstChoice_of_bottom_scores_of_noTies
    hnt h

theorem rum3RankByScores_firstChoice_of_strict_bottom_scores
    {s1 s2 s3 : ℝ}
    (h13 : s1 < s3) (h23 : s2 < s3) :
    firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_firstChoice_of_strict_bottom_scores
    h13 h23

theorem rum3RankByScores_strict_bottom_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (2 : Candidate 1)) :
    s1 < s3 ∧ s2 < s3 := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_strict_bottom_scores_of_firstChoice h

theorem rum3RankByScores_middle_scores_of_firstChoice
    {s1 s2 s3 : ℝ}
    (h : firstChoice (rum3RankByScores s1 s2 s3) = (1 : Candidate 1)) :
    rum3MiddleBeatsTopByScores s1 s2 s3 := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_middle_scores_of_firstChoice h

theorem rum3RankByScores_remove0_eq1_imp_score23
    {s1 s2 s3 : ℝ}
    (h :
      bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
        (1 : Candidate 1)) :
    s3 ≤ s2 := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_remove0_eq1_imp_score23 h

theorem rum3RankByScores_remove1_ne0_imp_score13
    {s1 s2 s3 : ℝ}
    (h :
      ¬ bestRemainingAfter (rum3RankByScores s1 s2 s3) (1 : Candidate 1) =
        (0 : Candidate 1)) :
    s1 < s3 := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_remove1_ne0_imp_score13 h

theorem rum3RankByScores_remove1_eq0_of_score31
    {s1 s2 s3 : ℝ} (h31 : s3 ≤ s1) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (1 : Candidate 1) =
      (0 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_remove1_eq0_of_score31 h31

theorem rum3RankByScores_remove0_ne1_of_score23_lt
    {s1 s2 s3 : ℝ} (h23 : s2 < s3) :
    ¬ bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
      (1 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_remove0_ne1_of_score23_lt h23

theorem rum3RankByScores_remove0_eq2_imp_score23_lt
    {s1 s2 s3 : ℝ}
    (h :
      bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
        (2 : Candidate 1)) :
    s2 < s3 := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_remove0_eq2_imp_score23_lt h

theorem rum3RankByScores_remove0_eq1_of_score32
    {s1 s2 s3 : ℝ} (h32 : s3 ≤ s2) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (0 : Candidate 1) =
      (1 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_remove0_eq1_of_score32 h32

theorem rum3RankByScores_remove2_eq1_imp_score12_lt
    {s1 s2 s3 : ℝ}
    (h :
      bestRemainingAfter (rum3RankByScores s1 s2 s3) (2 : Candidate 1) =
        (1 : Candidate 1)) :
    s1 < s2 := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_remove2_eq1_imp_score12_lt h

theorem rum3RankByScores_remove2_eq0_of_score21
    {s1 s2 s3 : ℝ} (h21 : s2 ≤ s1) :
    bestRemainingAfter (rum3RankByScores s1 s2 s3) (2 : Candidate 1) =
      (0 : Candidate 1) := by
  exact EconCSLib.SocialChoice.Ranking.rum3RankByScores_remove2_eq0_of_score21 h21

/--
The deterministic `swapi` geometry used in Appendix C / Lemma 3 for `i = 2`.

If the original realization is bottom-first (`r₁,r₂ ≤ r₃`) and contraction
makes the middle candidate strictly beat the top candidate while weakly beating
the bottom candidate, then after swapping the top and middle realization
coordinates, the original realization is still bottom-first and the contracted
realization is top-first.
-/
theorem rum3_swap_middle_transition_geometry
    {t x1 x2 x3 r1 r2 r3 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hr13 : r1 ≤ r3) (hr23 : r2 ≤ r3)
    (hc12 : rumContractScore t x1 r1 < rumContractScore t x2 r2)
    (hc32 : rumContractScore t x3 r3 ≤ rumContractScore t x2 r2) :
    r2 ≤ r3 ∧ r1 ≤ r3 ∧
      rumContractScore t x2 r1 ≤ rumContractScore t x1 r2 ∧
      rumContractScore t x3 r3 ≤ rumContractScore t x1 r2 := by
  exact EconCSLib.Probability.rum3_swap_middle_transition_geometry
    ht0 ht1 hx12 hr13 hr23 hc12 hc32

/--
If the middle candidate beats the top candidate after contraction, then its
original realization score is strictly higher than the top candidate's score.
-/
theorem rum3_swap_middle_source_score_lt
    {t x1 x2 r1 r2 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hc12 :
      rumContractScore t x1 r1 <
        rumContractScore t x2 r2) :
    r1 < r2 := by
  exact EconCSLib.Probability.rum3_swap_middle_source_score_lt
    ht0 ht1 hx12 hc12

theorem weaklyWellOrderedNoise_swap_middle_density_le
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 r1 r2 : ℝ} (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) ≤ f (r2 - x1) * f (r1 - x2) := by
  exact EconCSLib.Probability.weaklyWellOrderedNoise_swap_middle_density_le
    hf hx12 hr12

theorem strictlyWellOrderedNoise_swap_middle_density_lt
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 r1 r2 : ℝ} (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) < f (r2 - x1) * f (r1 - x2) := by
  exact EconCSLib.Probability.strictlyWellOrderedNoise_swap_middle_density_lt
    hf hx12 hr12

/--
Pointwise three-coordinate density comparison for swapping the top and middle
coordinates in a wrong `x₁`/`x₂` pairwise realization.
-/
theorem weaklyWellOrderedNoise_swap12_density3_le
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 ≤ f (r3 - x3))
    (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) ≤
      f (r2 - x1) * f (r1 - x2) * f (r3 - x3) := by
  exact EconCSLib.Probability.weaklyWellOrderedNoise_swap12_density3_le
    hf hctx hx12 hr12

/--
Strict three-coordinate density comparison for swapping the top and middle
coordinates in a wrong `x₁`/`x₂` pairwise realization.
-/
theorem strictlyWellOrderedNoise_swap12_density3_lt
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 < f (r3 - x3))
    (hx12 : x2 < x1) (hr12 : r1 < r2) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) <
      f (r2 - x1) * f (r1 - x2) * f (r3 - x3) := by
  exact EconCSLib.Probability.strictlyWellOrderedNoise_swap12_density3_lt
    hf hctx hx12 hr12

/--
Pointwise three-coordinate density comparison for swapping the middle and
bottom coordinates in a wrong `x₂`/`x₃` pairwise realization.
-/
theorem weaklyWellOrderedNoise_swap23_density3_le
    {f : ℝ → ℝ} (hf : WeaklyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 ≤ f (r1 - x1))
    (hx23 : x3 < x2) (hr23 : r2 < r3) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) ≤
      f (r1 - x1) * f (r3 - x2) * f (r2 - x3) := by
  exact EconCSLib.Probability.weaklyWellOrderedNoise_swap23_density3_le
    hf hctx hx23 hr23

/--
Strict three-coordinate density comparison for swapping the middle and bottom
coordinates in a wrong `x₂`/`x₃` pairwise realization.
-/
theorem strictlyWellOrderedNoise_swap23_density3_lt
    {f : ℝ → ℝ} (hf : StrictlyWellOrderedNoise f)
    {x1 x2 x3 r1 r2 r3 : ℝ}
    (hctx : 0 < f (r1 - x1))
    (hx23 : x3 < x2) (hr23 : r2 < r3) :
    f (r1 - x1) * f (r2 - x2) * f (r3 - x3) <
      f (r1 - x1) * f (r3 - x2) * f (r2 - x3) := by
  exact EconCSLib.Probability.strictlyWellOrderedNoise_swap23_density3_lt
    hf hctx hx23 hr23

/--
Three-coordinate RUM score density as an `ℝ≥0∞` density for `withDensity`.

This is the continuous analogue of the finite density-product formula used by
the sample-space endpoints.
-/
noncomputable def rum3ScoreDensityENN {Ω : Type*} (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) : Ω → ENNReal :=
  EconCSLib.Probability.rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3

/-- Measurability of the three-coordinate score density. -/
theorem rum3ScoreDensityENN_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    {f : ℝ → ℝ} (hf : Measurable f)
    (x1 x2 x3 : ℝ) {r1 r2 r3 : Ω → ℝ}
    (hr1 : Measurable r1) (hr2 : Measurable r2) (hr3 : Measurable r3) :
    Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) := by
  exact EconCSLib.Probability.rum3ScoreDensityENN_measurable
    hf x1 x2 x3 hr1 hr2 hr3

/-- Positive noise density makes the three-coordinate score density nonzero. -/
theorem rum3ScoreDensityENN_ne_zero_of_noise_pos
    {Ω : Type*} {f : ℝ → ℝ}
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hpos : ∀ z : ℝ, 0 < f z) (ω : Ω) :
    rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3 ω ≠ 0 := by
  exact EconCSLib.Probability.rum3ScoreDensityENN_ne_zero_of_noise_pos
    x1 x2 x3 r1 r2 r3 hpos ω

/--
Positive base mass of a region remains positive under a strictly positive
three-coordinate score density.
-/
theorem rum3ScoreDensity_withDensity_measure_ne_zero_of_base_measure_ne_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) {f : ℝ → ℝ}
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hpos : ∀ z : ℝ, 0 < f z)
    {s : Set Ω} (hs : MeasurableSet s) (hbase : base s ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) s ≠ 0 :=
  EconCSLib.Probability.rum3ScoreDensity_withDensity_measure_ne_zero_of_base_measure_ne_zero
    base x1 x2 x3 r1 r2 r3 hD hpos hs hbase

/-- Normalization criterion for the three-coordinate score density. -/
theorem rum3ScoreDensity_isProbabilityMeasure_of_lintegral_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hD :
      ∫⁻ ω, (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂base = 1) :
    IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)) :=
  EconCSLib.Probability.rum3ScoreDensity_isProbabilityMeasure_of_lintegral_eq_one
    base f x1 x2 x3 r1 r2 r3 hD

/--
Any source-region density integral is finite once the full score density is
normalized.
-/
theorem rum3ScoreDensity_setLIntegral_ne_top_of_lintegral_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ)
    (hD :
      ∫⁻ ω, (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂base = 1)
    (s : Set Ω) :
    (∫⁻ ω in s, (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂base) ≠ ∞ :=
  EconCSLib.Probability.rum3ScoreDensity_setLIntegral_ne_top_of_lintegral_eq_one
    base f x1 x2 x3 r1 r2 r3 hD s

/--
Concrete three-coordinate score space for continuous three-candidate RUMs.

The nesting `((r₁, r₂), r₃)` is chosen to line up with mathlib's binary product
measure lemmas.
-/
abbrev RUM3ScoreSpace := (ℝ × ℝ) × ℝ

/-- First realized score coordinate. -/
def rum3Score1 (ω : RUM3ScoreSpace) : ℝ := ω.1.1

/-- Second realized score coordinate. -/
def rum3Score2 (ω : RUM3ScoreSpace) : ℝ := ω.1.2

/-- Third realized score coordinate. -/
def rum3Score3 (ω : RUM3ScoreSpace) : ℝ := ω.2

/-- Open rectangular box in the concrete three-score space. -/
def rum3ScoreOpenBox
    (a1 b1 a2 b2 a3 b3 : ℝ) : Set RUM3ScoreSpace :=
  ((Set.Ioo a1 b1).prod (Set.Ioo a2 b2)).prod (Set.Ioo a3 b3)

theorem rum3ScoreOpenBox_isOpen
    (a1 b1 a2 b2 a3 b3 : ℝ) :
    IsOpen (rum3ScoreOpenBox a1 b1 a2 b2 a3 b3) :=
  (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo

theorem rum3ScoreOpenBox_nonempty
    {a1 b1 a2 b2 a3 b3 : ℝ}
    (h1 : a1 < b1) (h2 : a2 < b2) (h3 : a3 < b3) :
    (rum3ScoreOpenBox a1 b1 a2 b2 a3 b3).Nonempty := by
  refine ⟨(((a1 + b1) / 2, (a2 + b2) / 2), (a3 + b3) / 2), ?_⟩
  change
    (((a1 + b1) / 2, (a2 + b2) / 2) ∈
        (Set.Ioo a1 b1).prod (Set.Ioo a2 b2)) ∧
      (a3 + b3) / 2 ∈ Set.Ioo a3 b3
  constructor
  · constructor
    · constructor <;> linarith
    · constructor <;> linarith
  · constructor <;> linarith

theorem rum3ScoreOpenBox_volume_ne_zero
    {a1 b1 a2 b2 a3 b3 : ℝ}
    (h1 : a1 < b1) (h2 : a2 < b2) (h3 : a3 < b3) :
    (volume : Measure RUM3ScoreSpace)
      (rum3ScoreOpenBox a1 b1 a2 b2 a3 b3) ≠ 0 :=
  (rum3ScoreOpenBox_isOpen a1 b1 a2 b2 a3 b3).measure_ne_zero
    (volume : Measure RUM3ScoreSpace)
    (rum3ScoreOpenBox_nonempty h1 h2 h3)

theorem rum3Score_volume_ne_zero_of_openBox_subset
    {s : Set RUM3ScoreSpace} {a1 b1 a2 b2 a3 b3 : ℝ}
    (hsubset : rum3ScoreOpenBox a1 b1 a2 b2 a3 b3 ⊆ s)
    (h1 : a1 < b1) (h2 : a2 < b2) (h3 : a3 < b3) :
    (volume : Measure RUM3ScoreSpace) s ≠ 0 := by
  have hbox_ne :
      (volume : Measure RUM3ScoreSpace)
        (rum3ScoreOpenBox a1 b1 a2 b2 a3 b3) ≠ 0 :=
    rum3ScoreOpenBox_volume_ne_zero h1 h2 h3
  exact ne_of_gt
    (lt_of_lt_of_le hbox_ne.bot_lt (measure_mono hsubset))

/-- The first concrete score coordinate is measurable. -/
theorem rum3Score1_measurable : Measurable rum3Score1 :=
  measurable_fst.fst

/-- The second concrete score coordinate is measurable. -/
theorem rum3Score2_measurable : Measurable rum3Score2 :=
  measurable_fst.snd

/-- The third concrete score coordinate is measurable. -/
theorem rum3Score3_measurable : Measurable rum3Score3 :=
  measurable_snd

/-- Measurability of the concrete three-score density. -/
theorem rum3ScoreDensityENN_measurable_scoreSpace
    {f : ℝ → ℝ} (hf : Measurable f) (x1 x2 x3 : ℝ) :
    Measurable
      (rum3ScoreDensityENN f x1 x2 x3 rum3Score1 rum3Score2 rum3Score3) :=
  rum3ScoreDensityENN_measurable hf x1 x2 x3
    rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable

/-- Concrete top/middle coordinate swap on three-score space. -/
def rum3ScoreSwap12 : RUM3ScoreSpace ≃ᵐ RUM3ScoreSpace :=
  MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl ℝ)

/-- Concrete middle/bottom coordinate swap on three-score space. -/
def rum3ScoreSwap23 : RUM3ScoreSpace ≃ᵐ RUM3ScoreSpace :=
  ((MeasurableEquiv.prodAssoc : RUM3ScoreSpace ≃ᵐ ℝ × (ℝ × ℝ))).trans
    (((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm).trans
      (MeasurableEquiv.prodAssoc.symm))

@[simp] theorem rum3ScoreSwap12_score1 (ω : RUM3ScoreSpace) :
    rum3Score1 (rum3ScoreSwap12 ω) = rum3Score2 ω := rfl

@[simp] theorem rum3ScoreSwap12_score2 (ω : RUM3ScoreSpace) :
    rum3Score2 (rum3ScoreSwap12 ω) = rum3Score1 ω := rfl

@[simp] theorem rum3ScoreSwap12_score3 (ω : RUM3ScoreSpace) :
    rum3Score3 (rum3ScoreSwap12 ω) = rum3Score3 ω := rfl

@[simp] theorem rum3ScoreSwap23_score1 (ω : RUM3ScoreSpace) :
    rum3Score1 (rum3ScoreSwap23 ω) = rum3Score1 ω := rfl

@[simp] theorem rum3ScoreSwap23_score2 (ω : RUM3ScoreSpace) :
    rum3Score2 (rum3ScoreSwap23 ω) = rum3Score3 ω := rfl

@[simp] theorem rum3ScoreSwap23_score3 (ω : RUM3ScoreSpace) :
    rum3Score3 (rum3ScoreSwap23 ω) = rum3Score2 ω := rfl

/-- The concrete top/middle score swap preserves three-dimensional Lebesgue volume. -/
theorem rum3ScoreSwap12_measurePreserving_volume :
    MeasurePreserving rum3ScoreSwap12 (volume : Measure RUM3ScoreSpace) volume := by
  have hpair : MeasurePreserving Prod.swap ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    simpa using
      (Measure.measurePreserving_swap
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
  have hprod : MeasurePreserving (Prod.map Prod.swap id)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod (volume : Measure ℝ)) := by
    simpa using hpair.prod (MeasurePreserving.id (volume : Measure ℝ))
  simpa [rum3ScoreSwap12, RUM3ScoreSpace, Measure.volume_eq_prod] using hprod

/-- The concrete middle/bottom score swap preserves three-dimensional Lebesgue volume. -/
theorem rum3ScoreSwap23_measurePreserving_volume :
    MeasurePreserving rum3ScoreSwap23 (volume : Measure RUM3ScoreSpace) volume := by
  have hpair : MeasurePreserving Prod.swap ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    simpa using
      (Measure.measurePreserving_swap
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
  have hinner : MeasurePreserving (Prod.map id Prod.swap)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
    simpa using (MeasurePreserving.id (volume : Measure ℝ)).prod hpair
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : RUM3ScoreSpace ≃ᵐ ℝ × (ℝ × ℝ))
      (volume : Measure RUM3ScoreSpace) (volume : Measure (ℝ × (ℝ × ℝ))) := by
    simpa [RUM3ScoreSpace] using
      (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ))
  have hassoc_symm : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : ℝ × (ℝ × ℝ) ≃ᵐ RUM3ScoreSpace)
      (volume : Measure (ℝ × (ℝ × ℝ))) (volume : Measure RUM3ScoreSpace) :=
    MeasurePreserving.symm
      (MeasurableEquiv.prodAssoc : RUM3ScoreSpace ≃ᵐ ℝ × (ℝ × ℝ)) hassoc
  have htail : MeasurePreserving
      (((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm).trans
        (MeasurableEquiv.prodAssoc.symm) : ℝ × (ℝ × ℝ) ≃ᵐ RUM3ScoreSpace)
      (volume : Measure (ℝ × (ℝ × ℝ))) (volume : Measure RUM3ScoreSpace) :=
    hassoc_symm.comp hinner
  exact htail.comp hassoc

/-- The residual `λ₁ ∧ ¬λ₂` source event has positive Lebesgue volume. -/
theorem rum3Score_lambda13gap_source_volume_ne_zero :
    (volume : Measure RUM3ScoreSpace)
      {ω | bestRemainingAfter
              (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω)
              (0 : Candidate 1) = (1 : Candidate 1) ∧
            ¬ bestRemainingAfter
              (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω)
              (1 : Candidate 1) = (0 : Candidate 1)} ≠ 0 := by
  refine rum3Score_volume_ne_zero_of_openBox_subset
    (a1 := 0) (b1 := 1) (a2 := 4) (b2 := 5) (a3 := 2) (b3 := 3)
    ?_ (by norm_num) (by norm_num) (by norm_num)
  intro ω hω
  rcases hω with ⟨⟨h1, h2⟩, h3⟩
  rcases h1 with ⟨h1lo, h1hi⟩
  rcases h2 with ⟨h2lo, h2hi⟩
  rcases h3 with ⟨h3lo, h3hi⟩
  have h32 : rum3Score3 ω ≤ rum3Score2 ω := by
    dsimp [rum3Score2, rum3Score3] at h2lo h2hi h3lo h3hi ⊢
    linarith
  have h31not : ¬ rum3Score3 ω ≤ rum3Score1 ω := by
    dsimp [rum3Score1, rum3Score3] at h1lo h1hi h3lo h3hi ⊢
    linarith
  constructor
  · simpa [rum3RankByScoreFns, h32]
  · simpa [rum3RankByScoreFns, h31not]

/-- The `x₂`/`x₃` wrong-choice source event has positive Lebesgue volume. -/
theorem rum3Score_lambda23wrong_source_volume_ne_zero :
    (volume : Measure RUM3ScoreSpace)
      {ω | bestRemainingAfter
              (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω)
              (0 : Candidate 1) = (2 : Candidate 1)} ≠ 0 := by
  refine rum3Score_volume_ne_zero_of_openBox_subset
    (a1 := 0) (b1 := 1) (a2 := 0) (b2 := 1) (a3 := 2) (b3 := 3)
    ?_ (by norm_num) (by norm_num) (by norm_num)
  intro ω hω
  rcases hω with ⟨⟨_h1, h2⟩, h3⟩
  rcases h2 with ⟨h2lo, h2hi⟩
  rcases h3 with ⟨h3lo, h3hi⟩
  have h32not : ¬ rum3Score3 ω ≤ rum3Score2 ω := by
    dsimp [rum3Score2, rum3Score3] at h2lo h2hi h3lo h3hi ⊢
    linarith
  simpa [rum3RankByScoreFns] using lt_of_not_ge h32not

/-- The `x₁`/`x₂` wrong-choice source event has positive Lebesgue volume. -/
theorem rum3Score_lambda12wrong_source_volume_ne_zero :
    (volume : Measure RUM3ScoreSpace)
      {ω | bestRemainingAfter
              (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω)
              (2 : Candidate 1) = (1 : Candidate 1)} ≠ 0 := by
  refine rum3Score_volume_ne_zero_of_openBox_subset
    (a1 := 0) (b1 := 1) (a2 := 2) (b2 := 3) (a3 := 0) (b3 := 1)
    ?_ (by norm_num) (by norm_num) (by norm_num)
  intro ω hω
  rcases hω with ⟨⟨h1, h2⟩, _h3⟩
  rcases h1 with ⟨h1lo, h1hi⟩
  rcases h2 with ⟨h2lo, h2hi⟩
  have h21not : ¬ rum3Score2 ω ≤ rum3Score1 ω := by
    dsimp [rum3Score1, rum3Score2] at h1lo h1hi h2lo h2hi ⊢
    linarith
  simpa [rum3RankByScoreFns] using lt_of_not_ge h21not

/--
For a genuine contraction toward strictly ordered values, there is a positive
volume region where candidate `x₁` is corrected into first place.
-/
theorem rum3Score_correctedTop_volume_ne_zero_of_t_lt_one
    {x1 x2 x3 t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    (volume : Measure RUM3ScoreSpace)
      ({ω | (0 : Candidate 1) =
            firstChoice
              (rum3ContractRankByScoreFns
                t x1 x2 x3 rum3Score1 rum3Score2 rum3Score3 ω)} ∩
        {ω | (0 : Candidate 1) =
            firstChoice
              (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω)}ᶜ) ≠
        0 := by
  let gap : ℝ := (1 - t) * (x1 - x2)
  have hgap : 0 < gap := by
    have h1t : 0 < 1 - t := by linarith
    have hx : 0 < x1 - x2 := sub_pos.mpr hx12
    exact mul_pos h1t hx
  refine rum3Score_volume_ne_zero_of_openBox_subset
    (s :=
      ({ω | (0 : Candidate 1) =
            firstChoice
              (rum3ContractRankByScoreFns
                t x1 x2 x3 rum3Score1 rum3Score2 rum3Score3 ω)} ∩
        {ω | (0 : Candidate 1) =
            firstChoice
              (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω)}ᶜ))
    (a1 := 0) (b1 := gap / 8)
    (a2 := gap / 4) (b2 := 3 * gap / 8)
    (a3 := -1) (b3 := -(1 / 2 : ℝ))
    ?_ (by nlinarith) (by nlinarith) (by norm_num)
  intro ω hω
  rcases hω with ⟨⟨h1, h2⟩, h3⟩
  rcases h1 with ⟨h1lo, h1hi⟩
  rcases h2 with ⟨h2lo, h2hi⟩
  rcases h3 with ⟨h3lo, h3hi⟩
  have hr12 : rum3Score1 ω < rum3Score2 ω := by
    dsimp [rum3Score1, rum3Score2] at h1lo h1hi h2lo h2hi ⊢
    nlinarith
  have hr32 : rum3Score3 ω < rum3Score2 ω := by
    dsimp [rum3Score2, rum3Score3] at h2lo h2hi h3lo h3hi ⊢
    nlinarith [hgap]
  have hr31 : rum3Score3 ω < rum3Score1 ω := by
    dsimp [rum3Score1, rum3Score3] at h1lo h1hi h3lo h3hi ⊢
    nlinarith
  have hrawFirst :
      firstChoice
          (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω) =
        (1 : Candidate 1) := by
    rw [rum3RankByScoreFns, firstChoice_rum3RankByScores]
    have h0 : ¬
        (rum3Score2 ω ≤ rum3Score1 ω ∧ rum3Score3 ω ≤ rum3Score1 ω) := by
      intro h
      exact not_le_of_gt hr12 h.1
    have h1first :
        rum3Score1 ω < rum3Score2 ω ∧ rum3Score3 ω ≤ rum3Score2 ω :=
      ⟨hr12, le_of_lt hr32⟩
    simp [h0, h1first]
  have hrawNotTop :
      ¬ (0 : Candidate 1) =
        firstChoice
          (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 ω) := by
    rw [hrawFirst]
    decide
  have hcontract21 :
      rumContractScore t x2 (rum3Score2 ω) <
        rumContractScore t x1 (rum3Score1 ω) := by
    have hr_nonneg : 0 ≤ rum3Score2 ω - rum3Score1 ω := by
      linarith
    have hmul_le :
        t * (rum3Score2 ω - rum3Score1 ω) ≤
          1 * (rum3Score2 ω - rum3Score1 ω) :=
      mul_le_mul_of_nonneg_right ht1 hr_nonneg
    have hr_gap : rum3Score2 ω - rum3Score1 ω < gap := by
      dsimp [rum3Score1, rum3Score2] at h1lo h1hi h2lo h2hi ⊢
      nlinarith [hgap]
    have hdiff :
        0 <
          rumContractScore t x1 (rum3Score1 ω) -
            rumContractScore t x2 (rum3Score2 ω) := by
      rw [rumContractScore_sub]
      nlinarith
    linarith
  have hcontract31 :
      rumContractScore t x3 (rum3Score3 ω) <
        rumContractScore t x1 (rum3Score1 ω) :=
    rumContractScore_preserves_strict_order ht0 ht1 (lt_trans hx23 hx12) hr31
  have hbetterFirst :
      firstChoice
          (rum3ContractRankByScoreFns
            t x1 x2 x3 rum3Score1 rum3Score2 rum3Score3 ω) =
        (0 : Candidate 1) := by
    have htop : rum3TopFirstByScores
        (rumContractScore t x1 (rum3Score1 ω))
        (rumContractScore t x2 (rum3Score2 ω))
        (rumContractScore t x3 (rum3Score3 ω)) :=
      ⟨le_of_lt hcontract21, le_of_lt hcontract31⟩
    simpa [rum3ContractRankByScoreFns] using
      rum3RankByScores_firstChoice_of_top_scores htop
  exact ⟨hbetterFirst.symm, hrawNotTop⟩

/--
Continuous with-density mass comparison for a top/middle coordinate swap.

This is the measure-theoretic version of
`rum3_swap12_mass_le_of_density_formula`: if a measurable equivalence preserves
the base score measure, maps source event `p` into target event `q`, and swaps
the first two score coordinates, then weak well-ordering plus the source score
inequality gives the corresponding mass comparison under the product density.
-/
theorem rum3_withDensity_swap12_measure_le_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} ≤
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} := by
  exact EconCSLib.Probability.rum3_withDensity_swap12_measure_le_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap p q hp hq hmp hmap hf
    hswap1 hswap2 hswap3 hctx hx12 hscore

/--
Continuous with-density mass comparison for a middle/bottom coordinate swap.
-/
theorem rum3_withDensity_swap23_measure_le_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} ≤
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} := by
  exact EconCSLib.Probability.rum3_withDensity_swap23_measure_le_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap p q hp hq hmp hmap hf
    hswap1 hswap2 hswap3 hctx hx23 hscore

/--
Continuous with-density transition comparison for Appendix C / Lemma 3.

The source event is the `x₃ -> x₂` transition: the worse ranking puts `x₃`
first and the contracted/better ranking puts `x₂` first.  The target event is
the `x₃ -> x₁` transition.  The `swapi` map swaps the first two score
coordinates, the deterministic contraction geometry maps the source event into
the target event, and weak well-ordering gives density monotonicity.
-/
theorem rum3_deltaTransition_withDensity_measure_le_of_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (better worse : Ω → Ranking 1)
    (hp : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω)})
    (hq : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω)})
    (hmp : MeasurePreserving swap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω))) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω)} ≤
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω)} := by
  refine rum3_withDensity_swap12_measure_le_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω))
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω))
    hp hq hmp ?_ hf hswap1 hswap2 hswap3 hctx hx12 ?_
  · intro ω htransition
    rcases hworseBottom_scores_of_first ω htransition.1 with ⟨hr13, hr23⟩
    rcases hbetterMiddle_scores_of_first ω htransition.2 with ⟨hc12, hc32⟩
    rcases rum3_swap_middle_transition_geometry
        ht0 ht1 hx12 hr13 hr23 hc12 hc32 with
      ⟨hr23_swap, hr13_swap, hc21_swap, hc31_swap⟩
    constructor
    · apply hworseBottom_of_scores
      unfold rum3BottomFirstByScores
      constructor
      · rw [hswap1, hswap3]
        exact hr23_swap
      · rw [hswap2, hswap3]
        exact hr13_swap
    · apply hbetterTop_of_scores
      unfold rum3TopFirstByScores
      constructor
      · rw [hswap2, hswap1]
        exact hc21_swap
      · rw [hswap3, hswap1]
        exact hc31_swap
  · intro ω htransition
    exact rum3_swap_middle_source_score_lt ht0 ht1 hx12
      ((hbetterMiddle_scores_of_first ω htransition.2).1)

/--
Real-valued probability version of
`rum3_deltaTransition_withDensity_measure_le_of_score_facts`.
-/
theorem rum3_deltaTransition_measureProb_le_of_withDensity_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (better worse : Ω → Ranking 1)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hp : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω)})
    (hq : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω)})
    (hmp : MeasurePreserving swap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω))) :
    measureProb
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
      measureProb
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω)) :=
  measureProb_le_of_measure_le
    (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω))
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω))
    (rum3_deltaTransition_withDensity_measure_le_of_score_facts
      base f x1 x2 x3 t r1 r2 r3 swap better worse
      hp hq hmp hf hswap1 hswap2 hswap3 hctx ht0 ht1 hx12
      hbetterTop_of_scores hworseBottom_scores_of_first
      hworseBottom_of_scores hbetterMiddle_scores_of_first)

/--
Strict continuous with-density mass comparison for a top/middle coordinate swap.

The positive-base-measure source assumption is the continuous replacement for a
finite strict witness atom.
-/
theorem rum3_withDensity_swap12_measure_lt_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω)
    (hfi :
      (∫⁻ ω in {ω | p ω},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos : base {ω | p ω} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} := by
  exact EconCSLib.Probability.rum3_withDensity_swap12_measure_lt_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap p q hp hq hmp hD hmap hf hpos
    hswap1 hswap2 hswap3 hx12 hscore hfi hsource_pos

/--
Strict continuous with-density mass comparison for a middle/bottom coordinate
swap.
-/
theorem rum3_withDensity_swap23_measure_lt_of_density_formula
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (p q : Ω → Prop)
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hmap : ∀ ω, p ω → q (swap ω))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω)
    (hfi :
      (∫⁻ ω in {ω | p ω},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos : base {ω | p ω} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | p ω} <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) {ω | q ω} := by
  exact EconCSLib.Probability.rum3_withDensity_swap23_measure_lt_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap p q hp hq hmp hD hmap hf hpos
    hswap1 hswap2 hswap3 hx23 hscore hfi hsource_pos

/--
Mass comparison for a finite sample law whose atoms are represented by the
three-coordinate density product, under a top/middle coordinate swap.
-/
theorem rum3_swap12_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    ∀ ω, p ω → (ν ω).toReal ≤ (ν (swap ω)).toReal := by
  exact EconCSLib.Probability.rum3_swap12_mass_le_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap p hf hdens
    hswap1 hswap2 hswap3 hctx hx12 hscore

/--
Strict mass comparison for a finite sample law represented by the
three-coordinate density product, under a top/middle coordinate swap.
-/
theorem rum3_swap12_mass_lt_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω, p ω → 0 < f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hscore : ∀ ω, p ω → r1 ω < r2 ω) :
    ∀ ω, p ω → (ν ω).toReal < (ν (swap ω)).toReal := by
  exact EconCSLib.Probability.rum3_swap12_mass_lt_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap p hf hdens
    hswap1 hswap2 hswap3 hctx hx12 hscore

/--
Finite mass comparison for the asymmetric `λ₁ < λ₂` gap event.

The source event is the part of `λ₁` not already counted by `λ₂`: after
removing `x₁`, `x₂` beats `x₃`, but after removing `x₂`, `x₁` does not beat
`x₃`.  Score interfaces turn this into `r₁ < r₂`, which feeds the top/middle
density swap formula.
-/
theorem rum3_lambda13gap_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        0 ≤ f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hnot_target_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        r1 ω < r3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal := by
  refine rum3_swap12_mass_le_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap
    (fun ω =>
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
        ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    hf hdens hswap1 hswap2 hswap3 hctx hx12 ?_
  intro ω hp
  exact lt_of_lt_of_le (hnot_target_scores ω hp.2) (hsource_scores ω hp.1)

/-- Strict finite mass comparison for the asymmetric `λ₁ < λ₂` gap event. -/
theorem rum3_lambda13gap_mass_lt_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        0 < f (r3 ω - x3))
    (hx12 : x2 < x1)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hnot_target_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        r1 ω < r3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        (ν ω).toReal < (ν (swap ω)).toReal := by
  refine rum3_swap12_mass_lt_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap
    (fun ω =>
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
        ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    hf hdens hswap1 hswap2 hswap3 hctx hx12 ?_
  intro ω hp
  exact lt_of_lt_of_le (hnot_target_scores ω hp.2) (hsource_scores ω hp.1)

/--
Finite mass comparison for the delta-side `swapi` map in Lemma 3.

The transition event says the worse ranking puts `x₃` first and the contracted
better ranking puts `x₂` first.  The better-first score interface gives the
contracted inequality `c₁ < c₂`; contraction geometry turns it into the raw
score inequality `r₁ < r₂`, which feeds the top/middle density swap formula.
-/
theorem rum3_deltaSwap_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (better worse : Ω → Ranking 1)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1)
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω))) :
    ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal := by
  refine rum3_swap12_mass_le_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω))
    hf hdens hswap1 hswap2 hswap3 hctx hx12 ?_
  intro ω hp
  exact rum3_swap_middle_source_score_lt ht0 ht1 hx12
    ((hbetterMiddle_scores_of_first ω hp.2).1)

/--
Mass comparison for a finite sample law whose atoms are represented by the
three-coordinate density product, under a middle/bottom coordinate swap.
-/
theorem rum3_swap23_mass_le_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : WeaklyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 ≤ f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    ∀ ω, p ω → (ν ω).toReal ≤ (ν (swap ω)).toReal := by
  exact EconCSLib.Probability.rum3_swap23_mass_le_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap p hf hdens
    hswap1 hswap2 hswap3 hctx hx23 hscore

/--
Strict mass comparison for a finite sample law represented by the
three-coordinate density product, under a middle/bottom coordinate swap.
-/
theorem rum3_swap23_mass_lt_of_density_formula
    {Ω : Type*} (ν : PMF Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω → Ω)
    (p : Ω → Prop)
    (hf : StrictlyWellOrderedNoise f)
    (hdens : ∀ ω,
      (ν ω).toReal = f (r1 ω - x1) * f (r2 ω - x2) * f (r3 ω - x3))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hctx : ∀ ω, p ω → 0 < f (r1 ω - x1))
    (hx23 : x3 < x2)
    (hscore : ∀ ω, p ω → r2 ω < r3 ω) :
    ∀ ω, p ω → (ν ω).toReal < (ν (swap ω)).toReal := by
  exact EconCSLib.Probability.rum3_swap23_mass_lt_of_density_formula
    ν f x1 x2 x3 r1 r2 r3 swap p hf hdens
    hswap1 hswap2 hswap3 hctx hx23 hscore

/-! ## Three-candidate RUM payoff algebra -/

/-- In the three-candidate RUM proof, utility after candidate `x₁` is unavailable. -/
noncomputable def rum3_uMinus1 (ell1 x2 x3 : ℝ) : ℝ :=
  ell1 * x2 + (1 - ell1) * x3

/-- In the three-candidate RUM proof, utility after candidate `x₂` is unavailable. -/
noncomputable def rum3_uMinus2 (ell2 x1 x3 : ℝ) : ℝ :=
  ell2 * x1 + (1 - ell2) * x3

/-- In the three-candidate RUM proof, utility after candidate `x₃` is unavailable. -/
noncomputable def rum3_uMinus3 (ell3 x1 x2 : ℝ) : ℝ :=
  ell3 * x1 + (1 - ell3) * x2

/-- Paper Theorem 6's `λ₁`: after `x₁` is unavailable, human chooses `x₂`. -/
noncomputable def rum3Lambda1 (μ : PMF (Ranking 1)) : ℝ :=
  pmfProb μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))

/-- Paper Theorem 6's `λ₂`: after `x₂` is unavailable, human chooses `x₁`. -/
noncomputable def rum3Lambda2 (μ : PMF (Ranking 1)) : ℝ :=
  pmfProb μ (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))

/-- Paper Theorem 6's `λ₃`: after `x₃` is unavailable, human chooses `x₁`. -/
noncomputable def rum3Lambda3 (μ : PMF (Ranking 1)) : ℝ :=
  pmfProb μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))

/--
The ranking PMF induced by pushing a continuous realization measure through a
ranking map.
-/
noncomputable def rumRankingPMFOfMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank) : PMF (Ranking 1) :=
  EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure μ rank hrank

/--
Event probabilities for the induced ranking PMF are source-measure preimage
masses.
-/
theorem rumRankingPMFOfMeasure_eventProb
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (p : Ranking 1 → Prop) [DecidablePred p] :
    pmfProb (rumRankingPMFOfMeasure μ rank hrank) p =
      measureProb μ (fun ω => p (rank ω)) := by
  exact EconCSLib.SocialChoice.Ranking.rankingPMFOfMeasure_eventProb
    μ rank hrank p

/-- Continuous-measure form of `λ₁` for an induced ranking PMF. -/
theorem rum3Lambda1_rumRankingPMFOfMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank) :
    rum3Lambda1 (rumRankingPMFOfMeasure μ rank hrank) =
      measureProb μ
        (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)) := by
  unfold rum3Lambda1
  exact rumRankingPMFOfMeasure_eventProb μ rank hrank
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))

/-- Continuous-measure form of `λ₂` for an induced ranking PMF. -/
theorem rum3Lambda2_rumRankingPMFOfMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank) :
    rum3Lambda2 (rumRankingPMFOfMeasure μ rank hrank) =
      measureProb μ
        (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
          (0 : Candidate 1)) := by
  unfold rum3Lambda2
  exact rumRankingPMFOfMeasure_eventProb μ rank hrank
    (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))

/-- Continuous-measure form of `λ₃` for an induced ranking PMF. -/
theorem rum3Lambda3_rumRankingPMFOfMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank) :
    rum3Lambda3 (rumRankingPMFOfMeasure μ rank hrank) =
      measureProb μ
        (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)) := by
  unfold rum3Lambda3
  exact rumRankingPMFOfMeasure_eventProb μ rank hrank
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))

/-- Continuous-measure form of first-choice probability. -/
theorem firstChoiceProb_rumRankingPMFOfMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (c : Candidate 1) :
    firstChoiceProb (rumRankingPMFOfMeasure μ rank hrank) c =
      measureProb μ (fun ω => c = firstChoice (rank ω)) := by
  unfold firstChoiceProb
  exact rumRankingPMFOfMeasure_eventProb μ rank hrank
    (fun π => c = firstChoice π)

theorem rum3Lambda1_wrong_eq_one_sub (μ : PMF (Ranking 1)) :
    pmfProb μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
      1 - rum3Lambda1 μ := by
  classical
  unfold rum3Lambda1
  rw [← pmfProb_compl μ
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))]
  unfold pmfProb
  refine pmfExp_congr μ ?_
  intro π
  by_cases h1 : bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1)
  · simp [h1]
  · have hne0 :
        bestRemainingAfter π (0 : Candidate 1) ≠ (0 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (0 : Candidate 1)
    have h2 : bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (0 : Candidate 1)).val = 2
      have hval0 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact hne0 (Fin.ext hv)
      have hval1 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 1 := by
        intro hv
        exact h1 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (0 : Candidate 1)).isLt
      omega
    simp [h2]

theorem rum3Lambda3_wrong_eq_one_sub (μ : PMF (Ranking 1)) :
    pmfProb μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
      1 - rum3Lambda3 μ := by
  classical
  unfold rum3Lambda3
  rw [← pmfProb_compl μ
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))]
  unfold pmfProb
  refine pmfExp_congr μ ?_
  intro π
  by_cases h0 : bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1)
  · simp [h0]
  · have hne2 :
        bestRemainingAfter π (2 : Candidate 1) ≠ (2 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (2 : Candidate 1)
    have h1 : bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (2 : Candidate 1)).val = 1
      have hval0 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact h0 (Fin.ext hv)
      have hval2 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 2 := by
        intro hv
        exact hne2 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (2 : Candidate 1)).isLt
      omega
    simp [h1]

theorem rum3Lambda1_half_of_wrong_lt_correct
    {μ : PMF (Ranking 1)}
    (hwrong :
      pmfProb μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μ) :
    (1 : ℝ) / 2 < rum3Lambda1 μ := by
  rw [rum3Lambda1_wrong_eq_one_sub μ] at hwrong
  linarith

theorem rum3Lambda3_half_of_wrong_lt_correct
    {μ : PMF (Ranking 1)}
    (hwrong :
      pmfProb μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μ) :
    (1 : ℝ) / 2 < rum3Lambda3 μ := by
  rw [rum3Lambda3_wrong_eq_one_sub μ] at hwrong
  linarith

/--
Named finite certificate for Appendix C / Theorem 6.

The fields are the exact non-analytic facts used after the paper invokes
monotonicity, Lemma 2, Lemma 3, and the pairwise human-ranking probabilities.
-/
structure RUM3Theorem6Certificate
    (μBetter μWorse : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    (x1 x2 x3 : ℝ) : Prop where
  value_first : value (0 : Candidate 1) = x1
  value_second : value (1 : Candidate 1) = x2
  value_third : value (2 : Candidate 1) = x3
  value12 : x2 < x1
  value23 : x3 < x2
  /-- Paper: `1/2 < λ₁`. -/
  lambda1_half : (1 : ℝ) / 2 < rum3Lambda1 μWorse
  /-- Paper: `λ₁ < 1`. -/
  lambda1_lt_one : rum3Lambda1 μWorse < 1
  /-- Paper: `λ₂ > λ₁`. -/
  lambda12 : rum3Lambda1 μWorse < rum3Lambda2 μWorse
  /-- Paper: `1/2 < λ₃`. -/
  lambda3_half : (1 : ℝ) / 2 < rum3Lambda3 μWorse
  /-- Paper monotonicity: `Δp₁ > 0`. -/
  delta_top_pos :
    0 <
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1)
  /-- Paper Lemma 3 for `i = 2`: `Δp₂ ≤ Δp₁`. -/
  delta_middle_le_top :
    firstChoiceProb μBetter (1 : Candidate 1) -
        firstChoiceProb μWorse (1 : Candidate 1) ≤
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1)
  /-- Paper Lemma 2: `Δp₃ ≤ 0`. -/
  delta_bottom_nonpos :
    firstChoiceProb μBetter (2 : Candidate 1) -
        firstChoiceProb μWorse (2 : Candidate 1) ≤ 0

/-- The lambda side of the paper's Theorem 6 proof. -/
structure RUM3LambdaCertificate (μWorse : PMF (Ranking 1)) : Prop where
  lambda1_half : (1 : ℝ) / 2 < rum3Lambda1 μWorse
  lambda1_lt_one : rum3Lambda1 μWorse < 1
  lambda12 : rum3Lambda1 μWorse < rum3Lambda2 μWorse
  lambda3_half : (1 : ℝ) / 2 < rum3Lambda3 μWorse

/-- The first-choice-delta side of the paper's Theorem 6 proof. -/
structure RUM3DeltaCertificate
    (μBetter μWorse : PMF (Ranking 1)) : Prop where
  delta_top_pos :
    0 <
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1)
  delta_middle_le_top :
    firstChoiceProb μBetter (1 : Candidate 1) -
        firstChoiceProb μWorse (1 : Candidate 1) ≤
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1)
  delta_bottom_nonpos :
    firstChoiceProb μBetter (2 : Candidate 1) -
        firstChoiceProb μWorse (2 : Candidate 1) ≤ 0

theorem rum3Theorem6Certificate_of_lambda_delta
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda : RUM3LambdaCertificate μWorse)
    (delta : RUM3DeltaCertificate μBetter μWorse) :
    RUM3Theorem6Certificate μBetter μWorse value x1 x2 x3 where
  value_first := hvalue1
  value_second := hvalue2
  value_third := hvalue3
  value12 := hx12
  value23 := hx23
  lambda1_half := lambda.lambda1_half
  lambda1_lt_one := lambda.lambda1_lt_one
  lambda12 := lambda.lambda12
  lambda3_half := lambda.lambda3_half
  delta_top_pos := delta.delta_top_pos
  delta_middle_le_top := delta.delta_middle_le_top
  delta_bottom_nonpos := delta.delta_bottom_nonpos

theorem rum3DeltaCertificate_of_paper_lemmas
    {μBetter μWorse : PMF (Ranking 1)}
    (monotonicity_top :
      firstChoiceProb μWorse (0 : Candidate 1) <
        firstChoiceProb μBetter (0 : Candidate 1))
    (lemma3_middle :
      firstChoiceProb μBetter (1 : Candidate 1) -
          firstChoiceProb μWorse (1 : Candidate 1) ≤
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (lemma2_bottom :
      firstChoiceProb μBetter (2 : Candidate 1) ≤
        firstChoiceProb μWorse (2 : Candidate 1)) :
    RUM3DeltaCertificate μBetter μWorse where
  delta_top_pos := by linarith
  delta_middle_le_top := lemma3_middle
  delta_bottom_nonpos := by linarith

/--
Abstract finite-coupling form of Appendix C / Lemma 2 for the bottom candidate.

The continuous paper proof constructs such a coupling by contraction.  This
lemma isolates the order-theoretic probability step: if every coupled realization
where the better/more accurate ranking puts `x₃` first also has the worse/human
ranking put `x₃` first, then the better bottom-first probability is no larger.
-/
theorem rum3_lemma2_bottom_of_coupling
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter :
      firstChoiceProb μBetter (2 : Candidate 1) =
        pmfProb ν (fun ω => (2 : Candidate 1) = firstChoice (better ω)))
    (hworse :
      firstChoiceProb μWorse (2 : Candidate 1) =
        pmfProb ν (fun ω => (2 : Candidate 1) = firstChoice (worse ω)))
    (himp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω)) :
    firstChoiceProb μBetter (2 : Candidate 1) ≤
      firstChoiceProb μWorse (2 : Candidate 1) := by
  rw [hbetter, hworse]
  exact pmfProb_le_of_imp ν
    (fun ω => (2 : Candidate 1) = firstChoice (better ω))
    (fun ω => (2 : Candidate 1) = firstChoice (worse ω))
    himp

theorem rum3_middle_delta_indicator_le_bottom_middle
    (b w : Candidate 1)
    (hnoTopOut : (0 : Candidate 1) = w → (0 : Candidate 1) = b) :
    (if (1 : Candidate 1) = b then (1 : ℝ) else 0) -
        (if (1 : Candidate 1) = w then (1 : ℝ) else 0) ≤
      (if (2 : Candidate 1) = w ∧ (1 : Candidate 1) = b then (1 : ℝ) else 0) -
        (if False then (1 : ℝ) else 0) := by
  fin_cases b <;> fin_cases w <;> simp at *

theorem rum3_bottom_top_indicator_le_top_delta
    (b w : Candidate 1)
    (hnoTopOut : (0 : Candidate 1) = w → (0 : Candidate 1) = b) :
    (if (2 : Candidate 1) = w ∧ (0 : Candidate 1) = b then (1 : ℝ) else 0) -
        (if False then (1 : ℝ) else 0) ≤
      (if (0 : Candidate 1) = b then (1 : ℝ) else 0) -
        (if (0 : Candidate 1) = w then (1 : ℝ) else 0) := by
  fin_cases b <;> fin_cases w <;> simp at *

/--
Abstract finite transition-mass form of Appendix C / Lemma 3 for the middle
candidate in the three-candidate case.

The continuous paper proof shows that the human-realization mass moving from
`x₃` to `x₂` under contraction is at most the mass moving from `x₃` to `x₁`,
using the `swapi` bijection and well-ordered noise.  This lemma isolates the
finite probability algebra around that step: if top-first realizations cannot
leave the top under contraction, and `x₃ → x₂` mass is no larger than
`x₃ → x₁` mass, then the paper's Lemma 3 delta inequality for `i = 2` follows.
-/
theorem rum3_lemma3_middle_of_transition_mass
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hbottomMiddle_le_bottomTop :
      pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω))) :
    firstChoiceProb μBetter (1 : Candidate 1) -
        firstChoiceProb μWorse (1 : Candidate 1) ≤
      firstChoiceProb μBetter (0 : Candidate 1) -
        firstChoiceProb μWorse (0 : Candidate 1) := by
  rw [hbetter (1 : Candidate 1), hworse (1 : Candidate 1),
    hbetter (0 : Candidate 1), hworse (0 : Candidate 1)]
  have hmid :
      pmfProb ν (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
          pmfProb ν (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
        pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) -
          pmfProb ν (fun _ => False) := by
    refine pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le ν
      (fun ω => (1 : Candidate 1) = firstChoice (better ω))
      (fun ω => (1 : Candidate 1) = firstChoice (worse ω))
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω))
      (fun _ => False) ?_
    intro ω
    exact rum3_middle_delta_indicator_le_bottom_middle
      (firstChoice (better ω)) (firstChoice (worse ω)) (hnoTopOut ω)
  have htop :
      pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω)) -
          pmfProb ν (fun _ => False) ≤
        pmfProb ν (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
          pmfProb ν (fun ω => (0 : Candidate 1) = firstChoice (worse ω)) := by
    refine pmfProb_sub_le_pmfProb_sub_of_forall_indicator_sub_le ν
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω))
      (fun _ => False)
      (fun ω => (0 : Candidate 1) = firstChoice (better ω))
      (fun ω => (0 : Candidate 1) = firstChoice (worse ω)) ?_
    intro ω
    exact rum3_bottom_top_indicator_le_top_delta
      (firstChoice (better ω)) (firstChoice (worse ω)) (hnoTopOut ω)
  simp only [pmfProb_false, sub_zero] at hmid htop
  linarith

/--
Finite `swapi` change-of-variables skeleton for Appendix C / Lemma 3.

An equivalence `swap` sends each `x₃ → x₂` transition realization into an
`x₃ → x₁` transition realization, and the target atom has at least as much
mass.  Therefore the `x₃ → x₂` transition probability is no larger.
-/
theorem rum3_bottomMiddle_transition_le_bottomTop_of_swap_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (ν : PMF Ω) (swap : Ω ≃ Ω)
    (better worse : Ω → Ranking 1)
    (hmap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (swap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (swap ω)))
    (hmass : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    pmfProb ν (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω)) ≤
      pmfProb ν (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω)) :=
  pmfProb_le_of_equiv_event_mass_le ν swap
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω))
    (fun ω =>
      (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω))
    hmap hmass

/--
Finite coupling form of the top-candidate monotonicity step used in Appendix C /
Theorem 6.

If every coupled realization that is top-first for the worse/human ranking is
also top-first for the better/algorithmic ranking, and some positive-mass
realization is corrected into top-first, then the top-first probability is
strictly larger for the better ranking.
-/
theorem rum3_monotonicity_top_of_coupling
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmass : 0 < (ν ω₀).toReal) :
    firstChoiceProb μWorse (0 : Candidate 1) <
      firstChoiceProb μBetter (0 : Candidate 1) := by
  rw [hworse (0 : Candidate 1), hbetter (0 : Candidate 1)]
  exact pmfProb_lt_of_imp_of_mass ν
    (fun ω => (0 : Candidate 1) = firstChoice (worse ω))
    (fun ω => (0 : Candidate 1) = firstChoice (better ω))
    hnoTopOut ω₀ hbetterTop hworseNotTop hmass

/--
Finite contraction/coupling certificate for the delta side of Appendix C /
Theorem 6.

This packages the finite monotonicity step, Lemma 2 bottom inequality, and
Lemma 3 middle-vs-top inequality into the `RUM3DeltaCertificate` consumed by
the final payoff algebra.  The continuous RUM proof still needs to construct the
coupling and prove the listed event/transition facts from contraction and
well-ordered noise.
-/
theorem rum3DeltaCertificate_of_finite_contraction_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmass : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbottomMiddle_le_bottomTop :
      pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        pmfProb ν (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω))) :
    RUM3DeltaCertificate μBetter μWorse :=
  rum3DeltaCertificate_of_paper_lemmas
    (rum3_monotonicity_top_of_coupling
      μBetter μWorse ν better worse hbetter hworse hnoTopOut
      hbetterTop hworseNotTop hmass)
    (rum3_lemma3_middle_of_transition_mass
      μBetter μWorse ν better worse hbetter hworse hnoTopOut
      hbottomMiddle_le_bottomTop)
    (rum3_lemma2_bottom_of_coupling
      μBetter μWorse ν better worse
      (hbetter (2 : Candidate 1)) (hworse (2 : Candidate 1)) hbottomImp)

/--
Delta certificate where the Lemma 3 transition-mass inequality is supplied by a
finite `swapi` equivalence with pointwise mass dominance.
-/
theorem rum3DeltaCertificate_of_finite_contraction_swap_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hmap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (swap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (swap ω)))
    (hmassSwap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    RUM3DeltaCertificate μBetter μWorse :=
  rum3DeltaCertificate_of_finite_contraction_facts
    μBetter μWorse ν better worse hbetter hworse hnoTopOut
    hbetterTop hworseNotTop hmassTop hbottomImp
    (rum3_bottomMiddle_transition_le_bottomTop_of_swap_equiv
      ν swap better worse hmap hmassSwap)

/--
Delta certificate from finite score-level contraction and `swapi` facts.

This bridge derives the ranking-level event implications used by Lemmas 2 and 3
from deterministic score geometry.  The remaining measure-theoretic work is only
the marginal identification and the mass comparison for the finite/discretized
`swapi` map.
-/
theorem rum3DeltaCertificate_of_finite_score_contraction_swap_facts
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μBetter μWorse : PMF (Ranking 1)) (ν : PMF Ω)
    (better worse : Ω → Ranking 1)
    (t x1 x2 x3 : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ Ω)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hbetter : ∀ c : Candidate 1,
      firstChoiceProb μBetter c =
        pmfProb ν (fun ω => c = firstChoice (better ω)))
    (hworse : ∀ c : Candidate 1,
      firstChoiceProb μWorse c =
        pmfProb ν (fun ω => c = firstChoice (worse ω)))
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    {ω₀ : Ω}
    (hbetterTop : (0 : Candidate 1) = firstChoice (better ω₀))
    (hworseNotTop : ¬ (0 : Candidate 1) = firstChoice (worse ω₀))
    (hmassTop : 0 < (ν ω₀).toReal)
    (hmassSwap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal) :
    RUM3DeltaCertificate μBetter μWorse := by
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  have hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω) := by
    intro ω hwTop
    rcases hworseTop_scores_of_first ω hwTop with ⟨hr21, hr31⟩
    exact hbetterTop_of_scores ω
      (rum3_contract_top_first_of_original_top_first
        ht0 ht1 (le_of_lt hx12) (le_of_lt hx13) hr21 hr31)
  have hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω) := by
    intro ω hbBetter
    rcases hbetterBottom_scores_of_first ω hbBetter with ⟨hc13, hc23⟩
    exact hworseBottom_of_scores ω
      (rum3_contract_bottom_first_imp_original_bottom_first
        ht0 ht1 hx13 hx23 hc13 hc23)
  have hmap : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse (swap ω)) ∧
          (0 : Candidate 1) = firstChoice (better (swap ω)) := by
    intro ω htransition
    rcases hworseBottom_scores_of_first ω htransition.1 with ⟨hr13, hr23⟩
    rcases hbetterMiddle_scores_of_first ω htransition.2 with ⟨hc12, hc32⟩
    rcases rum3_swap_middle_transition_geometry
        ht0 ht1 hx12 hr13 hr23 hc12 hc32 with
      ⟨hr23_swap, hr13_swap, hc21_swap, hc31_swap⟩
    constructor
    · apply hworseBottom_of_scores
      unfold rum3BottomFirstByScores
      constructor
      · rw [hswap1, hswap3]
        exact hr23_swap
      · rw [hswap2, hswap3]
        exact hr13_swap
    · apply hbetterTop_of_scores
      unfold rum3TopFirstByScores
      constructor
      · rw [hswap2, hswap1]
        exact hc21_swap
      · rw [hswap3, hswap1]
        exact hc31_swap
  exact rum3DeltaCertificate_of_finite_contraction_swap_facts
    μBetter μWorse ν better worse swap hbetter hworse hnoTopOut
    hbetterTop hworseNotTop hmassTop hbottomImp hmap hmassSwap

theorem rum3LambdaCertificate_of_pairwise_facts
    {μWorse : PMF (Ranking 1)}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_correct : (1 : ℝ) / 2 < rum3Lambda1 μWorse)
    (h23_not_sure : rum3Lambda1 μWorse < 1)
    (h12_correct : (1 : ℝ) / 2 < rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse where
  lambda1_half := h23_correct
  lambda1_lt_one := h23_not_sure
  lambda12 := h13_gt_23
  lambda3_half := h12_correct

theorem rum3Lambda1_le_one (μ : PMF (Ranking 1)) :
    rum3Lambda1 μ ≤ 1 := by
  exact pmfProb_le_one μ
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))

theorem rum3Lambda2_le_one (μ : PMF (Ranking 1)) :
    rum3Lambda2 μ ≤ 1 := by
  exact pmfProb_le_one μ
    (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))

theorem rum3Lambda3_le_one (μ : PMF (Ranking 1)) :
    rum3Lambda3 μ ≤ 1 := by
  exact pmfProb_le_one μ
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))

theorem rum3Lambda1_lt_one_of_mass_choose_third_after_first_removed
    (μ : PMF (Ranking 1)) (π₀ : Ranking 1)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μ π₀).toReal) :
    rum3Lambda1 μ < 1 := by
  unfold rum3Lambda1
  refine pmfProb_lt_one_of_mass_not μ
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    π₀ ?hnot hmass
  intro h
  have : (2 : Candidate 1) = (1 : Candidate 1) := by
    rw [← hchoose, h]
  have hval : (2 : ℕ) = 1 := by
    simpa using congrArg Fin.val this
  norm_num at hval

theorem rum3_bestRemainingAfter_swap02_remove0 :
    bestRemainingAfter
        (Equiv.swap (0 : Candidate 1) (2 : Candidate 1))
        (0 : Candidate 1) = (2 : Candidate 1) := by
  simp [bestRemainingAfter, firstChoice]

theorem rum3Lambda1_lt_one_of_full_support
    (μ : PMF (Ranking 1))
    (hfull : ∀ π : Ranking 1, 0 < (μ π).toReal) :
    rum3Lambda1 μ < 1 :=
  rum3Lambda1_lt_one_of_mass_choose_third_after_first_removed
    μ (Equiv.swap (0 : Candidate 1) (2 : Candidate 1))
    rum3_bestRemainingAfter_swap02_remove0
    (hfull (Equiv.swap (0 : Candidate 1) (2 : Candidate 1)))

theorem rum3_fullSupport_of_sample_preimages
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1)
    (hpreimage : ∀ π : Ranking 1,
      (μ π).toReal = pmfProb ν (fun ω => rank ω = π))
    (hsupport : ∀ π : Ranking 1,
      ∃ ω : Ω, rank ω = π ∧ 0 < (ν ω).toReal) :
    ∀ π : Ranking 1, 0 < (μ π).toReal := by
  intro π
  rcases hsupport π with ⟨ω, hω_rank, hω_mass⟩
  exact pmf_apply_toReal_pos_of_pmfProb_preimage
    μ ν rank hpreimage hω_rank hω_mass

theorem rum3LambdaCertificate_of_pairwise_facts_and_support
    {μWorse : PMF (Ranking 1)} {π₀ : Ranking 1}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_correct : (1 : ℝ) / 2 < rum3Lambda1 μWorse)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μWorse π₀).toReal)
    (h12_correct : (1 : ℝ) / 2 < rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_facts
    h13_gt_23 h23_correct
    (rum3Lambda1_lt_one_of_mass_choose_third_after_first_removed
      μWorse π₀ hchoose hmass)
    h12_correct

theorem rum3LambdaCertificate_of_pairwise_wrong_facts_and_support
    {μWorse : PMF (Ranking 1)} {π₀ : Ranking 1}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_wrong_lt_correct :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μWorse)
    (hchoose :
      bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hmass : 0 < (μWorse π₀).toReal)
    (h12_wrong_lt_correct :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_facts_and_support
    h13_gt_23
    (rum3Lambda1_half_of_wrong_lt_correct h23_wrong_lt_correct)
    hchoose hmass
    (rum3Lambda3_half_of_wrong_lt_correct h12_wrong_lt_correct)

theorem rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    {μWorse : PMF (Ranking 1)}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (h23_wrong_lt_correct :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
        rum3Lambda1 μWorse)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (h12_wrong_lt_correct :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
        rum3Lambda3 μWorse) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_facts
    h13_gt_23
    (rum3Lambda1_half_of_wrong_lt_correct h23_wrong_lt_correct)
    (rum3Lambda1_lt_one_of_full_support μWorse hfull)
    (rum3Lambda3_half_of_wrong_lt_correct h12_wrong_lt_correct)

/-- Continuous-measure version of the `x₂` versus `x₃` wrong-choice comparison. -/
theorem rum3Lambda1_wrong_lt_correct_of_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hmeasure :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)}) :
    pmfProb (rumRankingPMFOfMeasure μ rank hrank)
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
      rum3Lambda1 (rumRankingPMFOfMeasure μ rank hrank) := by
  rw [rumRankingPMFOfMeasure_eventProb, rum3Lambda1_rumRankingPMFOfMeasure]
  exact measureProb_lt_of_measure_lt μ
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
      (2 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
      (1 : Candidate 1))
    hmeasure

/-- Continuous-measure version of the `x₁` versus `x₂` wrong-choice comparison. -/
theorem rum3Lambda3_wrong_lt_correct_of_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hmeasure :
      μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)}) :
    pmfProb (rumRankingPMFOfMeasure μ rank hrank)
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
      rum3Lambda3 (rumRankingPMFOfMeasure μ rank hrank) := by
  rw [rumRankingPMFOfMeasure_eventProb, rum3Lambda3_rumRankingPMFOfMeasure]
  exact measureProb_lt_of_measure_lt μ
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
      (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
      (0 : Candidate 1))
    hmeasure

/-- Continuous-measure version of the `λ₁ < λ₂` comparison. -/
theorem rum3Lambda1_lt_lambda2_of_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hmeasure :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
          (0 : Candidate 1)}) :
    rum3Lambda1 (rumRankingPMFOfMeasure μ rank hrank) <
      rum3Lambda2 (rumRankingPMFOfMeasure μ rank hrank) := by
  rw [rum3Lambda1_rumRankingPMFOfMeasure, rum3Lambda2_rumRankingPMFOfMeasure]
  exact measureProb_lt_of_measure_lt μ
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
      (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
      (0 : Candidate 1))
    hmeasure

/--
Continuous-measure version of the residual `λ₁ ∧ ¬λ₂` cancellation argument.
-/
theorem rum3Lambda1_lt_lambda2_of_cross_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hcross :
      μ ({ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)}ᶜ) <
        μ ({ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)}ᶜ)) :
    rum3Lambda1 (rumRankingPMFOfMeasure μ rank hrank) <
      rum3Lambda2 (rumRankingPMFOfMeasure μ rank hrank) := by
  rw [rum3Lambda1_rumRankingPMFOfMeasure, rum3Lambda2_rumRankingPMFOfMeasure]
  have hp : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (1 : Candidate 1)} :=
    by
      simpa only [Set.preimage_setOf_eq] using
        hrank (show MeasurableSet
          {π : Ranking 1 | bestRemainingAfter π (0 : Candidate 1) =
            (1 : Candidate 1)} from MeasurableSet.of_discrete)
  have hq : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
        (0 : Candidate 1)} :=
    by
      simpa only [Set.preimage_setOf_eq] using
        hrank (show MeasurableSet
          {π : Ranking 1 | bestRemainingAfter π (1 : Candidate 1) =
            (0 : Candidate 1)} from MeasurableSet.of_discrete)
  exact measureProb_lt_of_cross_event_measure_lt μ
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
      (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
      (0 : Candidate 1))
    hp hq hcross

/--
Lambda certificate from continuous realization-measure comparisons plus full
support of the induced human ranking law.
-/
theorem rum3LambdaCertificate_of_measure_facts_and_full_support
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hfull : ∀ π : Ranking 1,
      0 < (rumRankingPMFOfMeasure μ rank hrank π).toReal)
    (h13_gt_23 :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
          (0 : Candidate 1)})
    (h23_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)})
    (h12_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)}) :
    RUM3LambdaCertificate (rumRankingPMFOfMeasure μ rank hrank) :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    (rum3Lambda1_lt_lambda2_of_measure μ rank hrank h13_gt_23)
    (rum3Lambda1_wrong_lt_correct_of_measure
      μ rank hrank h23_wrong_lt_correct)
    hfull
    (rum3Lambda3_wrong_lt_correct_of_measure
      μ rank hrank h12_wrong_lt_correct)

/--
Lambda certificate from continuous realization-measure comparisons, using the
paper's residual `λ₁ ∧ ¬λ₂` comparison for `λ₁ < λ₂`.
-/
theorem rum3LambdaCertificate_of_cross_measure_facts_and_full_support
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hfull : ∀ π : Ranking 1,
      0 < (rumRankingPMFOfMeasure μ rank hrank π).toReal)
    (h13_cross :
      μ ({ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)}ᶜ) <
        μ ({ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)}ᶜ))
    (h23_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)})
    (h12_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)}) :
    RUM3LambdaCertificate (rumRankingPMFOfMeasure μ rank hrank) :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    (rum3Lambda1_lt_lambda2_of_cross_measure μ rank hrank h13_cross)
    (rum3Lambda1_wrong_lt_correct_of_measure
      μ rank hrank h23_wrong_lt_correct)
    hfull
    (rum3Lambda3_wrong_lt_correct_of_measure
      μ rank hrank h12_wrong_lt_correct)

/-- Positive wrong-choice probability makes `λ₁` strictly below one. -/
theorem rum3Lambda1_lt_one_of_wrong_prob_pos
    {μ : PMF (Ranking 1)}
    (hwrong :
      0 <
        pmfProb μ
          (fun π => bestRemainingAfter π (0 : Candidate 1) =
            (2 : Candidate 1))) :
    rum3Lambda1 μ < 1 := by
  rw [rum3Lambda1_wrong_eq_one_sub μ] at hwrong
  linarith

/--
Lambda certificate from continuous realization-measure comparisons, replacing
full ranking support by the exact positive wrong-event mass needed for
`λ₁ < 1`.
-/
theorem rum3LambdaCertificate_of_cross_measure_facts_and_wrong_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (rank : Ω → Ranking 1) (hrank : Measurable rank)
    (hwrong23_pos :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1)} ≠ 0)
    (h13_cross :
      μ ({ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)}ᶜ) <
        μ ({ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)}ᶜ))
    (h23_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)})
    (h12_wrong_lt_correct :
      μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
        μ {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)}) :
    RUM3LambdaCertificate (rumRankingPMFOfMeasure μ rank hrank) := by
  have hwrong_prob :
      0 <
        pmfProb (rumRankingPMFOfMeasure μ rank hrank)
          (fun π => bestRemainingAfter π (0 : Candidate 1) =
            (2 : Candidate 1)) := by
    rw [rumRankingPMFOfMeasure_eventProb]
    exact measureProb_pos_of_measure_ne_zero μ
      (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1))
      hwrong23_pos
  exact
    rum3LambdaCertificate_of_pairwise_facts
      (rum3Lambda1_lt_lambda2_of_cross_measure μ rank hrank h13_cross)
      (rum3Lambda1_half_of_wrong_lt_correct
        (rum3Lambda1_wrong_lt_correct_of_measure
          μ rank hrank h23_wrong_lt_correct))
      (rum3Lambda1_lt_one_of_wrong_prob_pos hwrong_prob)
      (rum3Lambda3_half_of_wrong_lt_correct
        (rum3Lambda3_wrong_lt_correct_of_measure
          μ rank hrank h12_wrong_lt_correct))

/--
Delta certificate from continuous first-choice measure inequalities.

This is the continuous analogue of `rum3DeltaCertificate_of_paper_lemmas` after
pushing the realization measure forward to the better and worse ranking laws.
-/
theorem rum3DeltaCertificate_of_measure_probability_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    (monotonicity_top :
      μ {ω | (0 : Candidate 1) = firstChoice (worse ω)} <
        μ {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (lemma3_middle :
      measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
        measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (worse ω)))
    (lemma2_bottom :
      μ {ω | (2 : Candidate 1) = firstChoice (better ω)} ≤
        μ {ω | (2 : Candidate 1) = firstChoice (worse ω)}) :
    RUM3DeltaCertificate
      (rumRankingPMFOfMeasure μ better hbetter)
      (rumRankingPMFOfMeasure μ worse hworse) := by
  refine rum3DeltaCertificate_of_paper_lemmas ?_ ?_ ?_
  · rw [firstChoiceProb_rumRankingPMFOfMeasure,
      firstChoiceProb_rumRankingPMFOfMeasure]
    exact measureProb_lt_of_measure_lt μ
      (fun ω => (0 : Candidate 1) = firstChoice (worse ω))
      (fun ω => (0 : Candidate 1) = firstChoice (better ω))
      monotonicity_top
  · rw [firstChoiceProb_rumRankingPMFOfMeasure,
      firstChoiceProb_rumRankingPMFOfMeasure,
      firstChoiceProb_rumRankingPMFOfMeasure,
      firstChoiceProb_rumRankingPMFOfMeasure]
    exact lemma3_middle
  · rw [firstChoiceProb_rumRankingPMFOfMeasure,
      firstChoiceProb_rumRankingPMFOfMeasure]
    exact measureProb_le_of_measure_le μ
      (fun ω => (2 : Candidate 1) = firstChoice (better ω))
      (fun ω => (2 : Candidate 1) = firstChoice (worse ω))
      lemma2_bottom

/-- Continuous coupling form of the top-candidate monotonicity step. -/
theorem rum3_monotonicity_top_of_measure_coupling
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (worse ω)})
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hcorrected_pos :
      μ ({ω | (0 : Candidate 1) = firstChoice (better ω)} ∩
          {ω | (0 : Candidate 1) = firstChoice (worse ω)}ᶜ) ≠ 0) :
    μ {ω | (0 : Candidate 1) = firstChoice (worse ω)} <
      μ {ω | (0 : Candidate 1) = firstChoice (better ω)} :=
  measure_lt_of_imp_of_diff_ne_zero μ
    (fun ω => (0 : Candidate 1) = firstChoice (worse ω))
    (fun ω => (0 : Candidate 1) = firstChoice (better ω))
    hworseTopMeas hbetterTopMeas hnoTopOut hcorrected_pos

/-- Continuous coupling form of Appendix C / Lemma 2 for the bottom candidate. -/
theorem rum3_lemma2_bottom_of_measure_coupling
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (better worse : Ω → Ranking 1)
    (hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω)) :
    μ {ω | (2 : Candidate 1) = firstChoice (better ω)} ≤
      μ {ω | (2 : Candidate 1) = firstChoice (worse ω)} :=
  measure_le_of_imp μ
    (fun ω => (2 : Candidate 1) = firstChoice (better ω))
    (fun ω => (2 : Candidate 1) = firstChoice (worse ω))
    hbottomImp

/--
Continuous transition-mass form of Appendix C / Lemma 3 for the middle
candidate.

This is the continuous counterpart of
`rum3_lemma3_middle_of_transition_mass`.  The proof pushes the continuous
coupling through the finite first-choice-pair summary and reuses the finite
indicator algebra on that finite image.
-/
theorem rum3_lemma3_middle_of_measure_transition_mass
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (better worse : Ω → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    (hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hbottomMiddle_le_bottomTop :
      measureProb μ (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)) ≤
        measureProb μ (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω))) :
    measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
        measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
      measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
        measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (worse ω)) := by
  classical
  let firstPair : Ω → Candidate 1 × Candidate 1 := fun ω =>
    (firstChoice (better ω), firstChoice (worse ω))
  have hpair : Measurable firstPair := by
    have hb : Measurable (fun ω => firstChoice (better ω)) :=
      (measurable_of_finite firstChoice).comp hbetter
    have hw : Measurable (fun ω => firstChoice (worse ω)) :=
      (measurable_of_finite firstChoice).comp hworse
    exact Measurable.prod hb hw
  have hmid :
      measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (1 : Candidate 1) = firstChoice (worse ω)) ≤
        measureProb μ (fun ω =>
            (2 : Candidate 1) = firstChoice (worse ω) ∧
              (1 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun _ => False) := by
    simpa [firstPair, and_comm, and_left_comm, and_assoc] using
      (measureProb_sub_le_measureProb_sub_of_forall_indicator_sub_le
        (μ := μ) (f := firstPair) hpair
        (p := fun bw : Candidate 1 × Candidate 1 => (1 : Candidate 1) = bw.1)
        (q := fun bw : Candidate 1 × Candidate 1 => (1 : Candidate 1) = bw.2)
        (r := fun bw : Candidate 1 × Candidate 1 =>
          (2 : Candidate 1) = bw.2 ∧ (1 : Candidate 1) = bw.1)
        (s := fun _ : Candidate 1 × Candidate 1 => False)
        MeasurableSet.of_discrete MeasurableSet.of_discrete
        MeasurableSet.of_discrete MeasurableSet.of_discrete
        (by
          intro ω
          exact rum3_middle_delta_indicator_le_bottom_middle
            (firstChoice (better ω)) (firstChoice (worse ω)) (hnoTopOut ω)))
  have htop :
      measureProb μ (fun ω =>
          (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun _ => False) ≤
        measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (better ω)) -
          measureProb μ (fun ω => (0 : Candidate 1) = firstChoice (worse ω)) := by
    simpa [firstPair, and_comm, and_left_comm, and_assoc] using
      (measureProb_sub_le_measureProb_sub_of_forall_indicator_sub_le
        (μ := μ) (f := firstPair) hpair
        (p := fun bw : Candidate 1 × Candidate 1 =>
          (2 : Candidate 1) = bw.2 ∧ (0 : Candidate 1) = bw.1)
        (q := fun _ : Candidate 1 × Candidate 1 => False)
        (r := fun bw : Candidate 1 × Candidate 1 => (0 : Candidate 1) = bw.1)
        (s := fun bw : Candidate 1 × Candidate 1 => (0 : Candidate 1) = bw.2)
        MeasurableSet.of_discrete MeasurableSet.of_discrete
        MeasurableSet.of_discrete MeasurableSet.of_discrete
        (by
          intro ω
          exact rum3_bottom_top_indicator_le_top_delta
            (firstChoice (better ω)) (firstChoice (worse ω)) (hnoTopOut ω)))
  simp only [measureProb_false, sub_zero] at hmid htop
  linarith

/--
Continuous with-density delta certificate from score-level contraction and
`swapi` facts.

This closes the delta side for a normalized score law
`base.withDensity (rum3ScoreDensityENN ...)`: top monotonicity and bottom
monotonicity come from contraction, while Lemma 3's transition-mass comparison
comes from the continuous `swapi` change of variables.
-/
theorem rum3DeltaCertificate_of_withDensity_score_contraction_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (better worse : Ω → Ranking 1)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hbetter : Measurable better) (hworse : Measurable worse)
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (better ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (worse ω)})
    (hp : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (1 : Candidate 1) = firstChoice (better ω)})
    (hq : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
        (0 : Candidate 1) = firstChoice (better ω)})
    (hmp : MeasurePreserving swap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hctx : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω) →
        0 ≤ f (r3 ω - x3))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hcorrected_pos :
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | (0 : Candidate 1) = firstChoice (better ω)} ∩
          {ω | (0 : Candidate 1) = firstChoice (worse ω)}ᶜ) ≠ 0)
    (hbetterTop_of_scores : ∀ ω,
      rum3TopFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) →
        (0 : Candidate 1) = firstChoice (better ω))
    (hworseTop_scores_of_first : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hbetterBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)))
    (hworseBottom_scores_of_first : ∀ ω,
      (2 : Candidate 1) = firstChoice (worse ω) →
        rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω))
    (hworseBottom_of_scores : ∀ ω,
      rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) →
        (2 : Candidate 1) = firstChoice (worse ω))
    (hbetterMiddle_scores_of_first : ∀ ω,
      (1 : Candidate 1) = firstChoice (better ω) →
        rum3MiddleBeatsTopByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω))) :
    RUM3DeltaCertificate
      (rumRankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        better hbetter)
      (rumRankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        worse hworse) := by
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  have hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω) := by
    intro ω hwTop
    rcases hworseTop_scores_of_first ω hwTop with ⟨hr21, hr31⟩
    exact hbetterTop_of_scores ω
      (rum3_contract_top_first_of_original_top_first
        ht0 ht1 (le_of_lt hx12) (le_of_lt hx13) hr21 hr31)
  have hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω) := by
    intro ω hbBetter
    rcases hbetterBottom_scores_of_first ω hbBetter with ⟨hc13, hc23⟩
    exact hworseBottom_of_scores ω
      (rum3_contract_bottom_first_imp_original_bottom_first
        ht0 ht1 hx13 hx23 hc13 hc23)
  let μD : Measure Ω :=
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
  change RUM3DeltaCertificate
      (rumRankingPMFOfMeasure μD better hbetter)
      (rumRankingPMFOfMeasure μD worse hworse)
  refine rum3DeltaCertificate_of_measure_probability_facts
    μD better worse hbetter hworse ?_ ?_ ?_
  · exact rum3_monotonicity_top_of_measure_coupling
      μD better worse hbetterTopMeas hworseTopMeas hnoTopOut
      hcorrected_pos
  · exact rum3_lemma3_middle_of_measure_transition_mass
      μD better worse hbetter hworse hnoTopOut
      (rum3_deltaTransition_measureProb_le_of_withDensity_score_facts
        base f x1 x2 x3 t r1 r2 r3 swap better worse
        hp hq hmp hf hswap1 hswap2 hswap3 hctx ht0 ht1 hx12
        hbetterTop_of_scores hworseBottom_scores_of_first
        hworseBottom_of_scores hbetterMiddle_scores_of_first)
  · exact rum3_lemma2_bottom_of_measure_coupling
      μD better worse hbottomImp

/--
Concrete score-ranking version of the continuous delta certificate.

The better ranking is induced by contracted scores, while the worse ranking is
induced by raw scores.  The only remaining model-specific inputs are
measurability of the concrete ranking/event maps, positive corrected-top mass,
the measure-preserving top/middle score swap, and the no-tie invariant needed
to turn weak bottom-score dominance into a pointwise bottom-first ranking fact.
-/
theorem rum3DeltaCertificate_of_withDensity_rankByScores_contraction_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hbetter : Measurable (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3))
    (hworse : Measurable (rum3RankByScoreFns r1 r2 r3))
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) =
        firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω)})
    (hp : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω) ∧
        (1 : Candidate 1) =
          firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)})
    (hq : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω) ∧
        (0 : Candidate 1) =
          firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)})
    (hmp : MeasurePreserving swap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hcorrected_pos :
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | (0 : Candidate 1) =
            firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)} ∩
          {ω | (0 : Candidate 1) =
            firstChoice (rum3RankByScoreFns r1 r2 r3 ω)}ᶜ) ≠ 0)
    (hworseNoTies : ∀ ω, rum3NoTiesByScores (r1 ω) (r2 ω) (r3 ω)) :
    RUM3DeltaCertificate
      (rumRankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3) hbetter)
      (rumRankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (rum3RankByScoreFns r1 r2 r3) hworse) := by
  refine rum3DeltaCertificate_of_withDensity_score_contraction_facts
    base f x1 x2 x3 t r1 r2 r3 swap
    (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3)
    (rum3RankByScoreFns r1 r2 r3)
    hbetter hworse hbetterTopMeas hworseTopMeas hp hq hmp hf
    hswap1 hswap2 hswap3 ?_ ht0 ht1 hx12 hx23
    hcorrected_pos ?_ ?_ ?_ ?_ ?_ ?_
  · intro ω _
    exact le_of_lt (hpos (r3 ω - x3))
  · intro ω htop
    simpa [rum3ContractRankByScoreFns] using
      (rum3RankByScores_firstChoice_of_top_scores htop).symm
  · intro ω hfirst
    exact rum3RankByScores_top_scores_of_firstChoice
      (by simpa [rum3RankByScoreFns] using hfirst.symm)
  · intro ω hfirst
    exact rum3RankByScores_bottom_scores_of_firstChoice
      (by simpa [rum3ContractRankByScoreFns] using hfirst.symm)
  · intro ω hfirst
    exact rum3RankByScores_bottom_scores_of_firstChoice
      (by simpa [rum3RankByScoreFns] using hfirst.symm)
  · intro ω hbottom
    simpa [rum3RankByScoreFns] using
      (rum3RankByScores_firstChoice_of_bottom_scores_of_noTies
        (hworseNoTies ω) hbottom).symm
  · intro ω hfirst
    exact rum3RankByScores_middle_scores_of_firstChoice
      (by simpa [rum3ContractRankByScoreFns] using hfirst.symm)

/--
Concrete score-ranking version of the continuous delta certificate for a genuine
accuracy contraction (`t < 1`).

This removes the pointwise no-tie assumption from
`rum3DeltaCertificate_of_withDensity_rankByScores_contraction_facts`: whenever
the contracted ranking puts the lowest-valued candidate first, strict
contraction forces that candidate's raw score to be strictly first, so the
deterministic tie-breaking convention is irrelevant.
-/
theorem rum3DeltaCertificate_of_withDensity_rankByScores_contraction_facts_of_t_lt_one
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 t : ℝ) (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    [IsProbabilityMeasure
      (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))]
    (hbetter : Measurable (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3))
    (hworse : Measurable (rum3RankByScoreFns r1 r2 r3))
    (hbetterTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) =
        firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)})
    (hworseTopMeas : MeasurableSet
      {ω | (0 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω)})
    (hp : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω) ∧
        (1 : Candidate 1) =
          firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)})
    (hq : MeasurableSet
      {ω | (2 : Candidate 1) = firstChoice (rum3RankByScoreFns r1 r2 r3 ω) ∧
        (0 : Candidate 1) =
          firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)})
    (hmp : MeasurePreserving swap base base)
    (hf : WeaklyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hcorrected_pos :
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | (0 : Candidate 1) =
            firstChoice (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3 ω)} ∩
          {ω | (0 : Candidate 1) =
            firstChoice (rum3RankByScoreFns r1 r2 r3 ω)}ᶜ) ≠ 0) :
    RUM3DeltaCertificate
      (rumRankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3) hbetter)
      (rumRankingPMFOfMeasure
        (base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
        (rum3RankByScoreFns r1 r2 r3) hworse) := by
  let better : Ω → Ranking 1 :=
    rum3ContractRankByScoreFns t x1 x2 x3 r1 r2 r3
  let worse : Ω → Ranking 1 := rum3RankByScoreFns r1 r2 r3
  let μD : Measure Ω :=
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  have hnoTopOut : ∀ ω,
      (0 : Candidate 1) = firstChoice (worse ω) →
        (0 : Candidate 1) = firstChoice (better ω) := by
    intro ω hwTop
    have htopRaw :
        rum3TopFirstByScores (r1 ω) (r2 ω) (r3 ω) :=
      rum3RankByScores_top_scores_of_firstChoice
        (by simpa [worse, rum3RankByScoreFns] using hwTop.symm)
    exact (rum3RankByScores_firstChoice_of_top_scores
      (rum3_contract_top_first_of_original_top_first
        ht0 ht1 (le_of_lt hx12) (le_of_lt hx13)
        htopRaw.1 htopRaw.2)).symm
  have hbottomImp : ∀ ω,
      (2 : Candidate 1) = firstChoice (better ω) →
        (2 : Candidate 1) = firstChoice (worse ω) := by
    intro ω hbBetter
    have hbottomContract :
        rum3BottomFirstByScores
          (rumContractScore t x1 (r1 ω))
          (rumContractScore t x2 (r2 ω))
          (rumContractScore t x3 (r3 ω)) :=
      rum3RankByScores_bottom_scores_of_firstChoice
        (by simpa [better, rum3ContractRankByScoreFns] using hbBetter.symm)
    rcases rum3_contract_bottom_first_imp_original_bottom_first_strict_of_t_lt_one
        ht0 htlt1 hx13 hx23 hbottomContract.1 hbottomContract.2 with
      ⟨hr13, hr23⟩
    exact (rum3RankByScores_firstChoice_of_strict_bottom_scores hr13 hr23).symm
  change RUM3DeltaCertificate
      (rumRankingPMFOfMeasure μD better hbetter)
      (rumRankingPMFOfMeasure μD worse hworse)
  refine rum3DeltaCertificate_of_measure_probability_facts
    μD better worse hbetter hworse ?_ ?_ ?_
  · exact rum3_monotonicity_top_of_measure_coupling
      μD better worse hbetterTopMeas hworseTopMeas hnoTopOut
      hcorrected_pos
  · refine rum3_lemma3_middle_of_measure_transition_mass
      μD better worse hbetter hworse hnoTopOut ?_
    refine measureProb_le_of_measure_le μD
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω))
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω)) ?_
    change
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
          {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
            (1 : Candidate 1) = firstChoice (better ω)} ≤
        base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
          {ω | (2 : Candidate 1) = firstChoice (worse ω) ∧
            (0 : Candidate 1) = firstChoice (better ω)}
    refine rum3_withDensity_swap12_measure_le_of_density_formula
      base f x1 x2 x3 r1 r2 r3 swap
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (1 : Candidate 1) = firstChoice (better ω))
      (fun ω =>
        (2 : Candidate 1) = firstChoice (worse ω) ∧
          (0 : Candidate 1) = firstChoice (better ω))
      (by simpa [better, worse] using hp)
      (by simpa [better, worse] using hq)
      hmp ?_ hf hswap1 hswap2 hswap3
      (fun ω _ => le_of_lt (hpos (r3 ω - x3))) hx12 ?_
    · intro ω htransition
      have hrawBottomStrict :
          r1 ω < r3 ω ∧ r2 ω < r3 ω :=
        rum3RankByScores_strict_bottom_scores_of_firstChoice
          (by simpa [worse, rum3RankByScoreFns] using htransition.1.symm)
      have hrawBottomWeak :
          rum3BottomFirstByScores (r1 ω) (r2 ω) (r3 ω) :=
        ⟨le_of_lt hrawBottomStrict.1, le_of_lt hrawBottomStrict.2⟩
      have hbetterMiddle :
          rum3MiddleBeatsTopByScores
            (rumContractScore t x1 (r1 ω))
            (rumContractScore t x2 (r2 ω))
            (rumContractScore t x3 (r3 ω)) :=
        rum3RankByScores_middle_scores_of_firstChoice
          (by simpa [better, rum3ContractRankByScoreFns] using htransition.2.symm)
      rcases rum3_swap_middle_transition_geometry
          ht0 ht1 hx12 hrawBottomWeak.1 hrawBottomWeak.2
          hbetterMiddle.1 hbetterMiddle.2 with
        ⟨_, _, hc21_swap, hc31_swap⟩
      constructor
      · have h13swap : r1 (swap ω) < r3 (swap ω) := by
          rw [hswap1, hswap3]
          exact hrawBottomStrict.2
        have h23swap : r2 (swap ω) < r3 (swap ω) := by
          rw [hswap2, hswap3]
          exact hrawBottomStrict.1
        exact (rum3RankByScores_firstChoice_of_strict_bottom_scores
          h13swap h23swap).symm
      · exact (rum3RankByScores_firstChoice_of_top_scores (by
          unfold rum3TopFirstByScores
          constructor
          · rw [hswap2, hswap1]
            exact hc21_swap
          · rw [hswap3, hswap1]
            exact hc31_swap)).symm
    · intro ω htransition
      have hbetterMiddle :
          rum3MiddleBeatsTopByScores
            (rumContractScore t x1 (r1 ω))
            (rumContractScore t x2 (r2 ω))
            (rumContractScore t x3 (r3 ω)) :=
        rum3RankByScores_middle_scores_of_firstChoice
          (by simpa [better, rum3ContractRankByScoreFns] using htransition.2.symm)
      exact rum3_swap_middle_source_score_lt ht0 ht1 hx12 hbetterMiddle.1
  · exact rum3_lemma2_bottom_of_measure_coupling μD better worse hbottomImp

/--
Finite paired-density skeleton for the `x₂` versus `x₃` lambda comparison.

If a finite equivalence sends each realization choosing `x₃` after `x₁` is
removed to one choosing `x₂`, never decreases mass on that wrong-choice event,
and strictly increases mass for one such realization, then the wrong-choice
probability is strictly smaller than `λ₁`.
-/
theorem rum3Lambda1_wrong_lt_correct_of_equiv
    (μ : PMF (Ranking 1)) (swap : Ranking 1 ≃ Ranking 1)
    (hmap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μ π).toReal ≤ (μ (swap π)).toReal)
    {π₀ : Ranking 1}
    (hwrong : bestRemainingAfter π₀ (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict : (μ π₀).toReal < (μ (swap π₀)).toReal) :
    pmfProb μ
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
      rum3Lambda1 μ := by
  unfold rum3Lambda1
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    μ swap
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1))
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    hmap hmass hwrong hstrict

/--
Finite paired-density skeleton for the `x₁` versus `x₂` lambda comparison.

If a finite equivalence sends each realization choosing `x₂` after `x₃` is
removed to one choosing `x₁`, never decreases mass on that wrong-choice event,
and strictly increases mass for one such realization, then the wrong-choice
probability is strictly smaller than `λ₃`.
-/
theorem rum3Lambda3_wrong_lt_correct_of_equiv
    (μ : PMF (Ranking 1)) (swap : Ranking 1 ≃ Ranking 1)
    (hmap : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μ π).toReal ≤ (μ (swap π)).toReal)
    {π₀ : Ranking 1}
    (hwrong : bestRemainingAfter π₀ (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (μ π₀).toReal < (μ (swap π₀)).toReal) :
    pmfProb μ
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
      rum3Lambda3 μ := by
  unfold rum3Lambda3
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    μ swap
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1))
    (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hwrong hstrict

/--
Finite paired-density skeleton for the `λ₁ < λ₂` gap in Theorem 6.

If a finite equivalence sends each realization where `x₂` beats `x₃` after
`x₁` is removed to one where `x₁` beats `x₃` after `x₂` is removed, never
decreases mass on the source event, and strictly increases mass for one such
realization, then `λ₁ < λ₂`.
-/
theorem rum3Lambda1_lt_lambda2_of_equiv
    (μ : PMF (Ranking 1)) (swap : Ranking 1 ≃ Ranking 1)
    (hmap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap π) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μ π).toReal ≤ (μ (swap π)).toReal)
    {π₀ : Ranking 1}
    (hsource : bestRemainingAfter π₀ (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (μ π₀).toReal < (μ (swap π₀)).toReal) :
    rum3Lambda1 μ < rum3Lambda2 μ := by
  unfold rum3Lambda1 rum3Lambda2
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    μ swap
    (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hsource hstrict

/--
Sample-space version of the `x₂` versus `x₃` lambda comparison.

The strict change-of-variables argument runs on a finite realization space `Ω`;
the two marginal-identification equalities connect it back to the ranking law.
-/
theorem rum3Lambda1_wrong_lt_correct_of_sample_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hwrongμ :
      pmfProb μ
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hcorrectμ :
      rum3Lambda1 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hmap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal)
    {ω₀ : Ω}
    (hwrong : bestRemainingAfter (rank ω₀) (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict : (ν ω₀).toReal < (ν (swap ω₀)).toReal) :
    pmfProb μ
        (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) <
      rum3Lambda1 μ := by
  rw [hwrongμ, hcorrectμ]
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    ν swap
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    hmap hmass hwrong hstrict

/--
Sample-space version of the `x₁` versus `x₂` lambda comparison.
-/
theorem rum3Lambda3_wrong_lt_correct_of_sample_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hwrongμ :
      pmfProb μ
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)))
    (hcorrectμ :
      rum3Lambda3 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hmap : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal)
    {ω₀ : Ω}
    (hwrong : bestRemainingAfter (rank ω₀) (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (ν ω₀).toReal < (ν (swap ω₀)).toReal) :
    pmfProb μ
        (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) <
      rum3Lambda3 μ := by
  rw [hwrongμ, hcorrectμ]
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    ν swap
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hwrong hstrict

/--
Sample-space version of the `λ₁ < λ₂` gap comparison.
-/
theorem rum3Lambda1_lt_lambda2_of_sample_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hlambda1μ :
      rum3Lambda1 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hmap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal)
    {ω₀ : Ω}
    (hsource : bestRemainingAfter (rank ω₀) (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict : (ν ω₀).toReal < (ν (swap ω₀)).toReal) :
    rum3Lambda1 μ < rum3Lambda2 μ := by
  rw [hlambda1μ, hlambda2μ]
  exact pmfProb_lt_of_equiv_event_mass_le_of_exists_strict
    ν swap
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hsource hstrict

/--
Sample-space `λ₁ < λ₂` comparison using only the asymmetric gap event.

This is the right finite analogue for the paper's two-candidate comparison: the
common event where both `λ₁` and `λ₂` hold cancels, and the swap only needs to
map the residual `λ₁ ∧ ¬λ₂` event into `λ₂ ∧ ¬λ₁`.
-/
theorem rum3Lambda1_lt_lambda2_of_cross_sample_equiv
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF (Ranking 1)) (ν : PMF Ω) (rank : Ω → Ranking 1) (swap : Ω ≃ Ω)
    (hlambda1μ :
      rum3Lambda1 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μ =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hmap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank (swap ω)) (0 : Candidate 1) =
            (1 : Candidate 1))
    (hmass : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap ω)).toReal)
    {ω₀ : Ω}
    (hsource :
      bestRemainingAfter (rank ω₀) (0 : Candidate 1) = (1 : Candidate 1) ∧
        ¬ bestRemainingAfter (rank ω₀) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hstrict : (ν ω₀).toReal < (ν (swap ω₀)).toReal) :
    rum3Lambda1 μ < rum3Lambda2 μ := by
  rw [hlambda1μ, hlambda2μ]
  exact pmfProb_lt_of_cross_event_equiv_mass_le_of_exists_strict
    ν swap
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    hmap hmass hsource hstrict

/--
Score-level event map for the `x₂` versus `x₃` lambda swap.

If choosing `x₃` after removing `x₁` implies the `x₃` score strictly beats the
`x₂` score, and a weak `x₂` score lead implies choosing `x₂`, then swapping the
two scores maps the wrong event into the correct event.
-/
theorem rum3Lambda1_wrong_to_correct_map_of_score_swap23
    {Ω : Type*} (rank : Ω → Ranking 1) (s2 s3 : Ω → ℝ) (swap : Ω → Ω)
    (hwrong_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        s2 ω < s3 ω)
    (hcorrect_of_scores : ∀ ω,
      s3 ω ≤ s2 ω →
        bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hswap2 : ∀ ω, s2 (swap ω) = s3 ω)
    (hswap3 : ∀ ω, s3 (swap ω) = s2 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (0 : Candidate 1) =
          (1 : Candidate 1) := by
  intro ω hwrong
  apply hcorrect_of_scores
  rw [hswap2, hswap3]
  exact le_of_lt (hwrong_scores ω hwrong)

/--
Score-level event map for the `x₁` versus `x₂` lambda swap.
-/
theorem rum3Lambda3_wrong_to_correct_map_of_score_swap12
    {Ω : Type*} (rank : Ω → Ranking 1) (s1 s2 : Ω → ℝ) (swap : Ω → Ω)
    (hwrong_scores : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        s1 ω < s2 ω)
    (hcorrect_of_scores : ∀ ω,
      s2 ω ≤ s1 ω →
        bestRemainingAfter (rank ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hswap1 : ∀ ω, s1 (swap ω) = s2 ω)
    (hswap2 : ∀ ω, s2 (swap ω) = s1 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (2 : Candidate 1) =
          (0 : Candidate 1) := by
  intro ω hwrong
  apply hcorrect_of_scores
  rw [hswap1, hswap2]
  exact le_of_lt (hwrong_scores ω hwrong)

/--
Score-level event map for the `λ₁ < λ₂` comparison.

If choosing `x₂` after removing `x₁` implies that the `x₂` score weakly beats
the `x₃` score, and a weak `x₁` score lead over `x₃` implies choosing `x₁`
after removing `x₂`, then swapping the `x₁` and `x₂` scores maps the source
event for `λ₁` into the target event for `λ₂`.
-/
theorem rum3Lambda1_to_lambda2_map_of_score_swap12
    {Ω : Type*} (rank : Ω → Ranking 1)
    (s1 s2 s3 : Ω → ℝ) (swap : Ω → Ω)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        s3 ω ≤ s2 ω)
    (htarget_of_scores : ∀ ω,
      s3 ω ≤ s1 ω →
        bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hswap1 : ∀ ω, s1 (swap ω) = s2 ω)
    (hswap3 : ∀ ω, s3 (swap ω) = s3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (1 : Candidate 1) =
          (0 : Candidate 1) := by
  intro ω hsource
  apply htarget_of_scores
  rw [hswap1, hswap3]
  exact hsource_scores ω hsource

/--
Score-level cross-event map for the `λ₁ < λ₂` comparison.

The source is the asymmetric gap `λ₁ ∧ ¬λ₂`.  After swapping the `x₁` and `x₂`
score coordinates, the source score inequalities imply the target asymmetric
event `λ₂ ∧ ¬λ₁`.
-/
theorem rum3Lambda1_to_lambda2_cross_map_of_score_swap12
    {Ω : Type*} (rank : Ω → Ranking 1)
    (s1 s2 s3 : Ω → ℝ) (swap : Ω → Ω)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        s3 ω ≤ s2 ω)
    (hnot_target_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        s1 ω < s3 ω)
    (htarget_of_scores : ∀ ω,
      s3 ω ≤ s1 ω →
        bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hnot_source_of_scores : ∀ ω,
      s2 ω < s3 ω →
        ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hswap1 : ∀ ω, s1 (swap ω) = s2 ω)
    (hswap2 : ∀ ω, s2 (swap ω) = s1 ω)
    (hswap3 : ∀ ω, s3 (swap ω) = s3 ω) :
    ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (rank (swap ω)) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank (swap ω)) (0 : Candidate 1) =
            (1 : Candidate 1) := by
  intro ω hsource
  constructor
  · apply htarget_of_scores
    rw [hswap1, hswap3]
    exact hsource_scores ω hsource.1
  · apply hnot_source_of_scores
    rw [hswap2, hswap3]
    exact hnot_target_scores ω hsource.2

/--
Continuous density-derived residual comparison for `λ₁ < λ₂`.

This is the measure-level version of the paper's residual change of variables:
the `x₁`/`x₂` coordinate swap strictly increases the with-density mass of
`λ₁ ∧ ¬λ₂` into `λ₂ ∧ ¬λ₁`.
-/
theorem rum3_lambda13cross_withDensity_measure_lt_of_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (hp : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)})
    (hq : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hx12 : x2 < x1)
    (hsource_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        r3 ω ≤ r2 ω)
    (hnot_target_scores : ∀ ω,
      ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        r1 ω < r3 ω)
    (htarget_of_scores : ∀ ω,
      r3 ω ≤ r1 ω →
        bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
    (hnot_source_of_scores : ∀ ω,
      r2 ω < r3 ω →
        ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hfi :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
                (1 : Candidate 1) ∧
              ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) =
                (0 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos :
      base
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
                (1 : Candidate 1) ∧
              ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) =
                (0 : Candidate 1)} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)}ᶜ) <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        ({ω | bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)} ∩
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)}ᶜ) := by
  simpa [Set.setOf_and, Set.compl_setOf] using
    (rum3_withDensity_swap12_measure_lt_of_density_formula
      base f x1 x2 x3 r1 r2 r3 swap
      (fun ω =>
        bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1))
      (fun ω =>
        bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
      hp hq hmp hD
      (rum3Lambda1_to_lambda2_cross_map_of_score_swap12
        rank r1 r2 r3 swap hsource_scores hnot_target_scores
        htarget_of_scores hnot_source_of_scores hswap1 hswap2 hswap3)
      hf hpos hswap1 hswap2 hswap3 hx12
      (fun ω hω =>
        lt_of_lt_of_le (hnot_target_scores ω hω.2)
          (hsource_scores ω hω.1))
      hfi hsource_pos)

/-- Continuous density-derived wrong-vs-correct comparison for `λ₁`. -/
theorem rum3_lambda23wrong_withDensity_measure_lt_of_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (hp : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1)})
    (hq : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (1 : Candidate 1)})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hx23 : x3 < x2)
    (hwrong_scores : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        r2 ω < r3 ω)
    (hcorrect_of_scores : ∀ ω,
      r3 ω ≤ r2 ω →
        bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1))
    (hswap1 : ∀ ω, r1 (swap ω) = r1 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r3 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r2 ω)
    (hfi :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos :
      base {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
        (2 : Candidate 1)} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (2 : Candidate 1)} <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        {ω | bestRemainingAfter (rank ω) (0 : Candidate 1) =
          (1 : Candidate 1)} :=
  rum3_withDensity_swap23_measure_lt_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
      (2 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
      (1 : Candidate 1))
    hp hq hmp hD
    (rum3Lambda1_wrong_to_correct_map_of_score_swap23
      rank r2 r3 swap hwrong_scores hcorrect_of_scores hswap2 hswap3)
    hf hpos hswap1 hswap2 hswap3 hx23 hwrong_scores hfi hsource_pos

/-- Continuous density-derived wrong-vs-correct comparison for `λ₃`. -/
theorem rum3_lambda12wrong_withDensity_measure_lt_of_score_facts
    {Ω : Type*} [MeasurableSpace Ω]
    (base : Measure Ω) (f : ℝ → ℝ)
    (x1 x2 x3 : ℝ) (rank : Ω → Ranking 1)
    (r1 r2 r3 : Ω → ℝ) (swap : Ω ≃ᵐ Ω)
    (hp : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
        (1 : Candidate 1)})
    (hq : MeasurableSet
      {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
        (0 : Candidate 1)})
    (hmp : MeasurePreserving swap base base)
    (hD : Measurable (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3))
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hx12 : x2 < x1)
    (hwrong_scores : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        r1 ω < r2 ω)
    (hcorrect_of_scores : ∀ ω,
      r2 ω ≤ r1 ω →
        bestRemainingAfter (rank ω) (2 : Candidate 1) = (0 : Candidate 1))
    (hswap1 : ∀ ω, r1 (swap ω) = r2 ω)
    (hswap2 : ∀ ω, r2 (swap ω) = r1 ω)
    (hswap3 : ∀ ω, r3 (swap ω) = r3 ω)
    (hfi :
      (∫⁻ ω in
          {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)},
          (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3) ω ∂(base)) ≠ ∞)
    (hsource_pos :
      base {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
        (1 : Candidate 1)} ≠ 0) :
    base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (1 : Candidate 1)} <
      base.withDensity (rum3ScoreDensityENN f x1 x2 x3 r1 r2 r3)
        {ω | bestRemainingAfter (rank ω) (2 : Candidate 1) =
          (0 : Candidate 1)} :=
  rum3_withDensity_swap12_measure_lt_of_density_formula
    base f x1 x2 x3 r1 r2 r3 swap
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
      (1 : Candidate 1))
    (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
      (0 : Candidate 1))
    hp hq hmp hD
    (rum3Lambda3_wrong_to_correct_map_of_score_swap12
      rank r1 r2 swap hwrong_scores hcorrect_of_scores hswap1 hswap2)
    hf hpos hswap1 hswap2 hswap3 hx12 hwrong_scores hfi hsource_pos

/--
Lambda certificate from finite paired-density swap facts.

This packages the two strict pairwise comparisons in the form produced by a
finite change-of-variables argument, while keeping the separate support witness
needed for `λ₁ < 1`.
-/
theorem rum3LambdaCertificate_of_pairwise_swap_facts_and_support
    {μWorse : PMF (Ranking 1)}
    (h13_gt_23 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (swap23 : Ranking 1 ≃ Ranking 1)
    (hmap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap23 π)).toReal)
    {π23 : Ranking 1}
    (hwrong23 : bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (μWorse π23).toReal < (μWorse (swap23 π23)).toReal)
    {πsupport : Ranking 1}
    (hchooseSupport :
      bestRemainingAfter πsupport (0 : Candidate 1) = (2 : Candidate 1))
    (hmassSupport : 0 < (μWorse πsupport).toReal)
    (swap12 : Ranking 1 ≃ Ranking 1)
    (hmap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap12 π)).toReal)
    {π12 : Ranking 1}
    (hwrong12 : bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (μWorse π12).toReal < (μWorse (swap12 π12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_support
    h13_gt_23
    (rum3Lambda1_wrong_lt_correct_of_equiv
      μWorse swap23 hmap23 hmass23 hwrong23 hstrict23)
    hchooseSupport hmassSupport
    (rum3Lambda3_wrong_lt_correct_of_equiv
      μWorse swap12 hmap12 hmass12 hwrong12 hstrict12)

/--
Lambda certificate from finite paired-density swap facts, including the
`λ₁ < λ₂` comparison as a swap certificate rather than a raw scalar premise.
-/
theorem rum3LambdaCertificate_of_all_pairwise_swap_facts_and_support
    {μWorse : PMF (Ranking 1)}
    (swap13gap : Ranking 1 ≃ Ranking 1)
    (hmap13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap13gap π) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap13gap π)).toReal)
    {π13gap : Ranking 1}
    (hsource13gap :
      bestRemainingAfter π13gap (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict13gap :
      (μWorse π13gap).toReal < (μWorse (swap13gap π13gap)).toReal)
    (swap23 : Ranking 1 ≃ Ranking 1)
    (hmap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap23 π)).toReal)
    {π23 : Ranking 1}
    (hwrong23 : bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (μWorse π23).toReal < (μWorse (swap23 π23)).toReal)
    {πsupport : Ranking 1}
    (hchooseSupport :
      bestRemainingAfter πsupport (0 : Candidate 1) = (2 : Candidate 1))
    (hmassSupport : 0 < (μWorse πsupport).toReal)
    (swap12 : Ranking 1 ≃ Ranking 1)
    (hmap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap12 π)).toReal)
    {π12 : Ranking 1}
    (hwrong12 : bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (μWorse π12).toReal < (μWorse (swap12 π12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_swap_facts_and_support
    (rum3Lambda1_lt_lambda2_of_equiv
      μWorse swap13gap hmap13gap hmass13gap hsource13gap hstrict13gap)
    swap23 hmap23 hmass23 hwrong23 hstrict23
    hchooseSupport hmassSupport swap12 hmap12 hmass12 hwrong12 hstrict12

/--
Lambda certificate from finite paired-density swap facts plus full support of
the finite human ranking law.
-/
theorem rum3LambdaCertificate_of_all_pairwise_swap_facts_and_full_support
    {μWorse : PMF (Ranking 1)}
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (swap13gap : Ranking 1 ≃ Ranking 1)
    (hmap13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap13gap π) (1 : Candidate 1) = (0 : Candidate 1))
    (hmass13gap : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap13gap π)).toReal)
    {π13gap : Ranking 1}
    (hsource13gap :
      bestRemainingAfter π13gap (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict13gap :
      (μWorse π13gap).toReal < (μWorse (swap13gap π13gap)).toReal)
    (swap23 : Ranking 1 ≃ Ranking 1)
    (hmap23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (swap23 π) (0 : Candidate 1) = (1 : Candidate 1))
    (hmass23 : ∀ π,
      bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap23 π)).toReal)
    {π23 : Ranking 1}
    (hwrong23 : bestRemainingAfter π23 (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (μWorse π23).toReal < (μWorse (swap23 π23)).toReal)
    (swap12 : Ranking 1 ≃ Ranking 1)
    (hmap12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (swap12 π) (2 : Candidate 1) = (0 : Candidate 1))
    (hmass12 : ∀ π,
      bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) →
        (μWorse π).toReal ≤ (μWorse (swap12 π)).toReal)
    {π12 : Ranking 1}
    (hwrong12 : bestRemainingAfter π12 (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (μWorse π12).toReal < (μWorse (swap12 π12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    (rum3Lambda1_lt_lambda2_of_equiv
      μWorse swap13gap hmap13gap hmass13gap hsource13gap hstrict13gap)
    (rum3Lambda1_wrong_lt_correct_of_equiv
      μWorse swap23 hmap23 hmass23 hwrong23 hstrict23)
    hfull
    (rum3Lambda3_wrong_lt_correct_of_equiv
      μWorse swap12 hmap12 hmass12 hwrong12 hstrict12)

/--
Lambda certificate from finite sample-space swap facts plus full support of the
human ranking law.

This is the finite/discrete analogue closest to the continuous RUM density
argument: the swaps act on realizations, and marginal equalities identify the
realization events with the ranking-law lambda events.
-/
theorem rum3LambdaCertificate_of_sample_swap_facts_and_full_support
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μWorse : PMF (Ranking 1)}
    (ν : PMF Ω) (rank : Ω → Ranking 1)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (hlambda1μ :
      rum3Lambda1 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong23μ :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hlambda3μ :
      rum3Lambda3 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong12μ :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)))
    (swap13gap : Ω ≃ Ω)
    (hmap13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap13gap ω)) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hmass13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap13gap ω)).toReal)
    {ω13gap : Ω}
    (hsource13gap :
      bestRemainingAfter (rank ω13gap) (0 : Candidate 1) = (1 : Candidate 1))
    (hstrict13gap :
      (ν ω13gap).toReal < (ν (swap13gap ω13gap)).toReal)
    (swap23 : Ω ≃ Ω)
    (hmap23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap23 ω)) (0 : Candidate 1) =
          (1 : Candidate 1))
    (hmass23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap23 ω)).toReal)
    {ω23 : Ω}
    (hwrong23 :
      bestRemainingAfter (rank ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (ν ω23).toReal < (ν (swap23 ω23)).toReal)
    (swap12 : Ω ≃ Ω)
    (hmap12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap12 ω)) (2 : Candidate 1) =
          (0 : Candidate 1))
    (hmass12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap12 ω)).toReal)
    {ω12 : Ω}
    (hwrong12 :
      bestRemainingAfter (rank ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (ν ω12).toReal < (ν (swap12 ω12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    (rum3Lambda1_lt_lambda2_of_sample_equiv
      μWorse ν rank swap13gap hlambda1μ hlambda2μ
      hmap13gap hmass13gap hsource13gap hstrict13gap)
    (rum3Lambda1_wrong_lt_correct_of_sample_equiv
      μWorse ν rank swap23 hwrong23μ hlambda1μ
      hmap23 hmass23 hwrong23 hstrict23)
    hfull
    (rum3Lambda3_wrong_lt_correct_of_sample_equiv
      μWorse ν rank swap12 hwrong12μ hlambda3μ
      hmap12 hmass12 hwrong12 hstrict12)

/--
Lambda certificate from finite sample-space swap facts where the `λ₁ < λ₂`
comparison is proved only on the asymmetric residual event `λ₁ ∧ ¬λ₂`.

This is the sample-space form closest to the paper's cancellation argument:
the common part of the two lambda events cancels, and only the residual gap
requires a mass-improving change of variables.
-/
theorem rum3LambdaCertificate_of_sample_cross_gap_and_wrong_swap_facts_and_full_support
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {μWorse : PMF (Ranking 1)}
    (ν : PMF Ω) (rank : Ω → Ranking 1)
    (hfull : ∀ π : Ranking 1, 0 < (μWorse π).toReal)
    (hlambda1μ :
      rum3Lambda1 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (1 : Candidate 1)))
    (hlambda2μ :
      rum3Lambda2 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (1 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong23μ :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (0 : Candidate 1) =
            (2 : Candidate 1)))
    (hlambda3μ :
      rum3Lambda3 μWorse =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (0 : Candidate 1)))
    (hwrong12μ :
      pmfProb μWorse
          (fun π => bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1)) =
        pmfProb ν
          (fun ω => bestRemainingAfter (rank ω) (2 : Candidate 1) =
            (1 : Candidate 1)))
    (swap13gap : Ω ≃ Ω)
    (hmap13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        bestRemainingAfter (rank (swap13gap ω)) (1 : Candidate 1) =
            (0 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank (swap13gap ω)) (0 : Candidate 1) =
            (1 : Candidate 1))
    (hmass13gap : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (1 : Candidate 1) ∧
          ¬ bestRemainingAfter (rank ω) (1 : Candidate 1) = (0 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap13gap ω)).toReal)
    {ω13gap : Ω}
    (hsource13gap :
      bestRemainingAfter (rank ω13gap) (0 : Candidate 1) = (1 : Candidate 1) ∧
        ¬ bestRemainingAfter (rank ω13gap) (1 : Candidate 1) =
          (0 : Candidate 1))
    (hstrict13gap :
      (ν ω13gap).toReal < (ν (swap13gap ω13gap)).toReal)
    (swap23 : Ω ≃ Ω)
    (hmap23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        bestRemainingAfter (rank (swap23 ω)) (0 : Candidate 1) =
          (1 : Candidate 1))
    (hmass23 : ∀ ω,
      bestRemainingAfter (rank ω) (0 : Candidate 1) = (2 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap23 ω)).toReal)
    {ω23 : Ω}
    (hwrong23 :
      bestRemainingAfter (rank ω23) (0 : Candidate 1) = (2 : Candidate 1))
    (hstrict23 : (ν ω23).toReal < (ν (swap23 ω23)).toReal)
    (swap12 : Ω ≃ Ω)
    (hmap12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        bestRemainingAfter (rank (swap12 ω)) (2 : Candidate 1) =
          (0 : Candidate 1))
    (hmass12 : ∀ ω,
      bestRemainingAfter (rank ω) (2 : Candidate 1) = (1 : Candidate 1) →
        (ν ω).toReal ≤ (ν (swap12 ω)).toReal)
    {ω12 : Ω}
    (hwrong12 :
      bestRemainingAfter (rank ω12) (2 : Candidate 1) = (1 : Candidate 1))
    (hstrict12 : (ν ω12).toReal < (ν (swap12 ω12)).toReal) :
    RUM3LambdaCertificate μWorse :=
  rum3LambdaCertificate_of_pairwise_wrong_facts_and_full_support
    (rum3Lambda1_lt_lambda2_of_cross_sample_equiv
      μWorse ν rank swap13gap hlambda1μ hlambda2μ
      hmap13gap hmass13gap hsource13gap hstrict13gap)
    (rum3Lambda1_wrong_lt_correct_of_sample_equiv
      μWorse ν rank swap23 hwrong23μ hlambda1μ
      hmap23 hmass23 hwrong23 hstrict23)
    hfull
    (rum3Lambda3_wrong_lt_correct_of_sample_equiv
      μWorse ν rank swap12 hwrong12μ hlambda3μ
      hmap12 hmass12 hwrong12 hstrict12)

theorem expectedBestAfterRemoval_rum3_remove0
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) :
    AccuracyFamily.expectedBestAfterRemoval μ value (0 : Candidate 1) =
      rum3Lambda1 μ * value (1 : Candidate 1) +
        (1 - rum3Lambda1 μ) * value (2 : Candidate 1) := by
  classical
  unfold AccuracyFamily.expectedBestAfterRemoval rum3Lambda1
  refine pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    μ (fun π => bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1))
    (fun π => value (bestRemainingAfter π (0 : Candidate 1)))
    (value (1 : Candidate 1)) (value (2 : Candidate 1)) ?_
  intro π
  by_cases h : bestRemainingAfter π (0 : Candidate 1) = (1 : Candidate 1)
  · simp [h]
  · have hne0 : bestRemainingAfter π (0 : Candidate 1) ≠ (0 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (0 : Candidate 1)
    have h2 : bestRemainingAfter π (0 : Candidate 1) = (2 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (0 : Candidate 1)).val = 2
      have hval0 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact hne0 (Fin.ext hv)
      have hval1 : (bestRemainingAfter π (0 : Candidate 1)).val ≠ 1 := by
        intro hv
        exact h (Fin.ext hv)
      have hlt := (bestRemainingAfter π (0 : Candidate 1)).isLt
      omega
    simp [h2]

theorem expectedBestAfterRemoval_rum3_remove1
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) :
    AccuracyFamily.expectedBestAfterRemoval μ value (1 : Candidate 1) =
      rum3Lambda2 μ * value (0 : Candidate 1) +
        (1 - rum3Lambda2 μ) * value (2 : Candidate 1) := by
  classical
  unfold AccuracyFamily.expectedBestAfterRemoval rum3Lambda2
  refine pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    μ (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1))
    (fun π => value (bestRemainingAfter π (1 : Candidate 1)))
    (value (0 : Candidate 1)) (value (2 : Candidate 1)) ?_
  intro π
  by_cases h : bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1)
  · simp [h]
  · have hne1 : bestRemainingAfter π (1 : Candidate 1) ≠ (1 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (1 : Candidate 1)
    have h2 : bestRemainingAfter π (1 : Candidate 1) = (2 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (1 : Candidate 1)).val = 2
      have hval0 : (bestRemainingAfter π (1 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact h (Fin.ext hv)
      have hval1 : (bestRemainingAfter π (1 : Candidate 1)).val ≠ 1 := by
        intro hv
        exact hne1 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (1 : Candidate 1)).isLt
      omega
    simp [h2]

theorem expectedBestAfterRemoval_rum3_remove2
    (μ : PMF (Ranking 1)) (value : Candidate 1 → ℝ) :
    AccuracyFamily.expectedBestAfterRemoval μ value (2 : Candidate 1) =
      rum3Lambda3 μ * value (0 : Candidate 1) +
        (1 - rum3Lambda3 μ) * value (1 : Candidate 1) := by
  classical
  unfold AccuracyFamily.expectedBestAfterRemoval rum3Lambda3
  refine pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    μ (fun π => bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1))
    (fun π => value (bestRemainingAfter π (2 : Candidate 1)))
    (value (0 : Candidate 1)) (value (1 : Candidate 1)) ?_
  intro π
  by_cases h : bestRemainingAfter π (2 : Candidate 1) = (0 : Candidate 1)
  · simp [h]
  · have hne2 : bestRemainingAfter π (2 : Candidate 1) ≠ (2 : Candidate 1) :=
      bestRemainingAfter_ne_removed π (2 : Candidate 1)
    have h1 : bestRemainingAfter π (2 : Candidate 1) = (1 : Candidate 1) := by
      apply Fin.ext
      change (bestRemainingAfter π (2 : Candidate 1)).val = 1
      have hval0 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 0 := by
        intro hv
        exact h (Fin.ext hv)
      have hval2 : (bestRemainingAfter π (2 : Candidate 1)).val ≠ 2 := by
        intro hv
        exact hne2 (Fin.ext hv)
      have hlt := (bestRemainingAfter π (2 : Candidate 1)).isLt
      omega
    simp [h1]

theorem rum3_uMinus1_lt_uMinus2
    {x1 x2 x3 ell1 ell2 : ℝ}
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hell1_pos : 0 < ell1) (hell12 : ell1 < ell2) :
    rum3_uMinus1 ell1 x2 x3 < rum3_uMinus2 ell2 x1 x3 := by
  have hx13 : x3 < x1 := lt_trans hx23 hx12
  have hx23_pos : 0 < x2 - x3 := sub_pos.mpr hx23
  have hx13_pos : 0 < x1 - x3 := sub_pos.mpr hx13
  have hx_gap : x2 - x3 < x1 - x3 := by linarith
  have hleft : ell1 * (x2 - x3) < ell1 * (x1 - x3) :=
    mul_lt_mul_of_pos_left hx_gap hell1_pos
  have hright : ell1 * (x1 - x3) < ell2 * (x1 - x3) :=
    mul_lt_mul_of_pos_right hell12 hx13_pos
  have hmain : ell1 * (x2 - x3) < ell2 * (x1 - x3) :=
    lt_trans hleft hright
  unfold rum3_uMinus1 rum3_uMinus2
  nlinarith

theorem rum3_uMinus1_lt_x2
    {x2 x3 ell1 : ℝ} (hx23 : x3 < x2) (hell1_lt_one : ell1 < 1) :
    rum3_uMinus1 ell1 x2 x3 < x2 := by
  have hcoef : 0 < 1 - ell1 := by linarith
  have hgap : x3 - x2 < 0 := by linarith
  have hprod : (1 - ell1) * (x3 - x2) < 0 :=
    mul_neg_of_pos_of_neg hcoef hgap
  unfold rum3_uMinus1
  nlinarith

theorem rum3_x2_lt_uMinus3
    {x1 x2 ell3 : ℝ} (hx12 : x2 < x1) (hell3_pos : 0 < ell3) :
    x2 < rum3_uMinus3 ell3 x1 x2 := by
  have hgap : 0 < x1 - x2 := sub_pos.mpr hx12
  have hprod : 0 < ell3 * (x1 - x2) := mul_pos hell3_pos hgap
  unfold rum3_uMinus3
  nlinarith

theorem rum3_uMinus2_le_x1
    {x1 x3 ell2 : ℝ} (hx31 : x3 ≤ x1) (hell2_le_one : ell2 ≤ 1) :
    rum3_uMinus2 ell2 x1 x3 ≤ x1 := by
  have hcoef : 0 ≤ 1 - ell2 := by linarith
  have hgap : x3 - x1 ≤ 0 := by linarith
  have hprod : (1 - ell2) * (x3 - x1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoef hgap
  unfold rum3_uMinus2
  nlinarith

theorem x1_add_x2_lt_two_mul_rum3_uMinus3
    {x1 x2 ell3 : ℝ} (hx12 : x2 < x1) (hell3_half : (1 : ℝ) / 2 < ell3) :
    x1 + x2 < 2 * rum3_uMinus3 ell3 x1 x2 := by
  have hcoef : 0 < 2 * ell3 - 1 := by linarith
  have hgap : 0 < x1 - x2 := sub_pos.mpr hx12
  have hprod : 0 < (2 * ell3 - 1) * (x1 - x2) := mul_pos hcoef hgap
  unfold rum3_uMinus3
  nlinarith

/--
The scalar algebra at the end of paper Theorem 6.

Here `dᵢ = Pr[τ₁ = xᵢ] - Pr[π₁ = xᵢ]`, and `uᵢ` is the human expected utility
when candidate `xᵢ` is unavailable.  The hypotheses are the paper's
`Δp₁ > 0`, `Δp₁ ≥ Δp₂`, `Δp₃ ≤ 0`, total-mass identity, and the three utility
comparisons derived in the proof.
-/
theorem rum3_delta_weighted_sum_neg
    {u1 u2 u3 d1 d2 d3 : ℝ}
    (hu12 : u1 < u2) (hu13 : u1 < u3) (hu_sum : u1 + u2 < 2 * u3)
    (hd1_pos : 0 < d1) (hd12 : d2 ≤ d1) (hd3_nonpos : d3 ≤ 0)
    (hd_sum : d1 + d2 + d3 = 0) :
    d1 * u1 + d2 * u2 + d3 * u3 < 0 := by
  by_cases hd2_nonpos : d2 ≤ 0
  · have hsome_neg : d2 < 0 ∨ d3 < 0 := by
      by_contra hnot
      have hd2_nonneg : 0 ≤ d2 := le_of_not_gt (fun h => hnot (Or.inl h))
      have hd3_nonneg : 0 ≤ d3 := le_of_not_gt (fun h => hnot (Or.inr h))
      nlinarith
    cases hsome_neg with
    | inl hd2_neg =>
        have h2 : d2 * u2 < d2 * u1 :=
          mul_lt_mul_of_neg_left hu12 hd2_neg
        have h3 : d3 * u3 ≤ d3 * u1 :=
          mul_le_mul_of_nonpos_left (le_of_lt hu13) hd3_nonpos
        calc
          d1 * u1 + d2 * u2 + d3 * u3
              < d1 * u1 + d2 * u1 + d3 * u1 := by linarith
          _ = (d1 + d2 + d3) * u1 := by ring
          _ = 0 := by rw [hd_sum]; ring
    | inr hd3_neg =>
        have h2 : d2 * u2 ≤ d2 * u1 :=
          mul_le_mul_of_nonpos_left (le_of_lt hu12) hd2_nonpos
        have h3 : d3 * u3 < d3 * u1 :=
          mul_lt_mul_of_neg_left hu13 hd3_neg
        calc
          d1 * u1 + d2 * u2 + d3 * u3
              < d1 * u1 + d2 * u1 + d3 * u1 := by linarith
          _ = (d1 + d2 + d3) * u1 := by ring
          _ = 0 := by rw [hd_sum]; ring
  · have hd2_pos : 0 < d2 := lt_of_not_ge hd2_nonpos
    have hdiff_nonpos : u1 - u3 ≤ 0 := by linarith
    have hfirst :
        d1 * (u1 - u3) ≤ d2 * (u1 - u3) :=
      mul_le_mul_of_nonpos_right hd12 hdiff_nonpos
    have htail : d2 * (u1 + u2 - 2 * u3) < 0 := by
      have hsum_neg : u1 + u2 - 2 * u3 < 0 := by linarith
      exact mul_neg_of_pos_of_neg hd2_pos hsum_neg
    have hbound :
        d1 * u1 + d2 * u2 + d3 * u3 ≤
          d2 * (u1 + u2 - 2 * u3) := by
      have hd3_eq : d3 = -d1 - d2 := by linarith
      calc
        d1 * u1 + d2 * u2 + d3 * u3
            = d1 * (u1 - u3) + d2 * (u2 - u3) := by
                rw [hd3_eq]
                ring
        _ ≤ d2 * (u1 - u3) + d2 * (u2 - u3) := by linarith
        _ = d2 * (u1 + u2 - 2 * u3) := by ring
    exact lt_of_le_of_lt hbound htail

/--
Paper Theorem 6 payoff algebra after substituting the three `u_-i` formulas.

The remaining RUM-specific tasks are to derive the lambda and delta hypotheses
from the continuous random-utility model.  This theorem closes the final
finite-dimensional inequality once those hypotheses are available.
-/
theorem rum3_theorem6_payoff_algebra
    {x1 x2 x3 ell1 ell2 ell3 d1 d2 d3 : ℝ}
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hell1_half : (1 : ℝ) / 2 < ell1) (hell1_lt_one : ell1 < 1)
    (hell12 : ell1 < ell2) (hell2_le_one : ell2 ≤ 1)
    (hell3_half : (1 : ℝ) / 2 < ell3)
    (hd1_pos : 0 < d1) (hd12 : d2 ≤ d1) (hd3_nonpos : d3 ≤ 0)
    (hd_sum : d1 + d2 + d3 = 0) :
    d1 * rum3_uMinus1 ell1 x2 x3 +
        d2 * rum3_uMinus2 ell2 x1 x3 +
        d3 * rum3_uMinus3 ell3 x1 x2 < 0 := by
  have hell1_pos : 0 < ell1 := by nlinarith
  have hell3_pos : 0 < ell3 := by nlinarith
  have hx13_le : x3 ≤ x1 := le_of_lt (lt_trans hx23 hx12)
  have hu12 :
      rum3_uMinus1 ell1 x2 x3 < rum3_uMinus2 ell2 x1 x3 :=
    rum3_uMinus1_lt_uMinus2 hx12 hx23 hell1_pos hell12
  have hu1_x2 : rum3_uMinus1 ell1 x2 x3 < x2 :=
    rum3_uMinus1_lt_x2 hx23 hell1_lt_one
  have hx2_u3 : x2 < rum3_uMinus3 ell3 x1 x2 :=
    rum3_x2_lt_uMinus3 hx12 hell3_pos
  have hu13 :
      rum3_uMinus1 ell1 x2 x3 < rum3_uMinus3 ell3 x1 x2 :=
    lt_trans hu1_x2 hx2_u3
  have hu2_x1 : rum3_uMinus2 ell2 x1 x3 ≤ x1 :=
    rum3_uMinus2_le_x1 hx13_le hell2_le_one
  have hxsum_u3 : x1 + x2 < 2 * rum3_uMinus3 ell3 x1 x2 :=
    x1_add_x2_lt_two_mul_rum3_uMinus3 hx12 hell3_half
  have hu_sum :
      rum3_uMinus1 ell1 x2 x3 + rum3_uMinus2 ell2 x1 x3 <
        2 * rum3_uMinus3 ell3 x1 x2 := by
    nlinarith
  exact rum3_delta_weighted_sum_neg
    hu12 hu13 hu_sum hd1_pos hd12 hd3_nonpos hd_sum

/--
Three-candidate RUM weaker-competition bridge in model notation.

This turns the scalar Theorem 6 algebra into the utility predicate from
Definition 3.  The first-choice delta hypotheses are stated directly in terms of
the better and worse first-mover ranking laws; their total-mass identity is
derived from `sum_firstChoiceProb_eq_one`.
-/
theorem rum3_prefersWeakerCompetition_of_payoff_algebra
    (μBetter μWorse : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    {x1 x2 x3 ell1 ell2 ell3 : ℝ}
    (hbest1 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (0 : Candidate 1) =
        rum3_uMinus1 ell1 x2 x3)
    (hbest2 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (1 : Candidate 1) =
        rum3_uMinus2 ell2 x1 x3)
    (hbest3 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (2 : Candidate 1) =
        rum3_uMinus3 ell3 x1 x2)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hell1_half : (1 : ℝ) / 2 < ell1) (hell1_lt_one : ell1 < 1)
    (hell12 : ell1 < ell2) (hell2_le_one : ell2 ≤ 1)
    (hell3_half : (1 : ℝ) / 2 < ell3)
    (hd1_pos :
      0 <
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd12 :
      firstChoiceProb μBetter (1 : Candidate 1) -
          firstChoiceProb μWorse (1 : Candidate 1) ≤
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd3_nonpos :
      firstChoiceProb μBetter (2 : Candidate 1) -
          firstChoiceProb μWorse (2 : Candidate 1) ≤ 0) :
    Model.PrefersWeakerCompetition μBetter μWorse value := by
  classical
  let d1 : ℝ :=
    firstChoiceProb μBetter (0 : Candidate 1) -
      firstChoiceProb μWorse (0 : Candidate 1)
  let d2 : ℝ :=
    firstChoiceProb μBetter (1 : Candidate 1) -
      firstChoiceProb μWorse (1 : Candidate 1)
  let d3 : ℝ :=
    firstChoiceProb μBetter (2 : Candidate 1) -
      firstChoiceProb μWorse (2 : Candidate 1)
  have hbetter_sum :
      firstChoiceProb μBetter (0 : Candidate 1) +
          firstChoiceProb μBetter (1 : Candidate 1) +
          firstChoiceProb μBetter (2 : Candidate 1) = 1 := by
    have hsum := sum_firstChoiceProb_eq_one (μ := μBetter) (n := 1)
    change (∑ c : Fin 3, firstChoiceProb μBetter c) = 1 at hsum
    rw [Fin.sum_univ_three] at hsum
    exact hsum
  have hworse_sum :
      firstChoiceProb μWorse (0 : Candidate 1) +
          firstChoiceProb μWorse (1 : Candidate 1) +
          firstChoiceProb μWorse (2 : Candidate 1) = 1 := by
    have hsum := sum_firstChoiceProb_eq_one (μ := μWorse) (n := 1)
    change (∑ c : Fin 3, firstChoiceProb μWorse c) = 1 at hsum
    rw [Fin.sum_univ_three] at hsum
    exact hsum
  have hd_sum : d1 + d2 + d3 = 0 := by
    dsimp [d1, d2, d3]
    nlinarith
  have hneg :
      d1 * rum3_uMinus1 ell1 x2 x3 +
          d2 * rum3_uMinus2 ell2 x1 x3 +
          d3 * rum3_uMinus3 ell3 x1 x2 < 0 := by
    exact rum3_theorem6_payoff_algebra
      hx12 hx23 hell1_half hell1_lt_one hell12 hell2_le_one hell3_half
      (by simpa [d1] using hd1_pos)
      (by simpa [d1, d2] using hd12)
      (by simpa [d3] using hd3_nonpos)
      hd_sum
  have hdiff :
      expectedSecondMoverIndependent μWorse μBetter value -
          expectedSecondMoverIndependent μWorse μWorse value =
        d1 * rum3_uMinus1 ell1 x2 x3 +
          d2 * rum3_uMinus2 ell2 x1 x3 +
          d3 * rum3_uMinus3 ell3 x1 x2 := by
    rw [AccuracyFamily.expectedSecondMoverIndependent_sub_eq_sum_firstChoiceProb_sub_mul_bestAfterRemoval]
    change
      (∑ c : Fin 3,
        (firstChoiceProb μBetter c - firstChoiceProb μWorse c) *
          AccuracyFamily.expectedBestAfterRemoval μWorse value c) =
        d1 * rum3_uMinus1 ell1 x2 x3 +
          d2 * rum3_uMinus2 ell2 x1 x3 +
          d3 * rum3_uMinus3 ell3 x1 x2
    rw [Fin.sum_univ_three]
    simp [d1, d2, d3, hbest1, hbest2, hbest3]
  unfold Model.PrefersWeakerCompetition
  have hsub : expectedSecondMoverIndependent μWorse μBetter value -
      expectedSecondMoverIndependent μWorse μWorse value < 0 := by
    rw [hdiff]
    exact hneg
  linarith

/--
Three-candidate RUM weaker-competition bridge with the `u_-i` formulas derived
from the human ranking law itself.

The remaining assumptions are exactly the upstream RUM probability facts from
the paper: value ordering, `λ₁ > 1/2`, `λ₁ < 1`, `λ₂ > λ₁`, `λ₃ > 1/2`, and
the first-choice delta inequalities.
-/
theorem rum3_prefersWeakerCompetition
    (μBetter μWorse : PMF (Ranking 1)) (value : Candidate 1 → ℝ)
    {x1 x2 x3 : ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hlam1_half : (1 : ℝ) / 2 < rum3Lambda1 μWorse)
    (hlam1_lt_one : rum3Lambda1 μWorse < 1)
    (hlam12 : rum3Lambda1 μWorse < rum3Lambda2 μWorse)
    (hlam3_half : (1 : ℝ) / 2 < rum3Lambda3 μWorse)
    (hd1_pos :
      0 <
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd12 :
      firstChoiceProb μBetter (1 : Candidate 1) -
          firstChoiceProb μWorse (1 : Candidate 1) ≤
        firstChoiceProb μBetter (0 : Candidate 1) -
          firstChoiceProb μWorse (0 : Candidate 1))
    (hd3_nonpos :
      firstChoiceProb μBetter (2 : Candidate 1) -
          firstChoiceProb μWorse (2 : Candidate 1) ≤ 0) :
    Model.PrefersWeakerCompetition μBetter μWorse value := by
  have hbest1 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (0 : Candidate 1) =
        rum3_uMinus1 (rum3Lambda1 μWorse) x2 x3 := by
    rw [expectedBestAfterRemoval_rum3_remove0]
    simp [rum3_uMinus1, hvalue2, hvalue3]
  have hbest2 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (1 : Candidate 1) =
        rum3_uMinus2 (rum3Lambda2 μWorse) x1 x3 := by
    rw [expectedBestAfterRemoval_rum3_remove1]
    simp [rum3_uMinus2, hvalue1, hvalue3]
  have hbest3 :
      AccuracyFamily.expectedBestAfterRemoval μWorse value (2 : Candidate 1) =
        rum3_uMinus3 (rum3Lambda3 μWorse) x1 x2 := by
    rw [expectedBestAfterRemoval_rum3_remove2]
    simp [rum3_uMinus3, hvalue1, hvalue2]
  exact rum3_prefersWeakerCompetition_of_payoff_algebra
    μBetter μWorse value
    hbest1 hbest2 hbest3
    hx12 hx23 hlam1_half hlam1_lt_one hlam12
    (pmfProb_le_one μWorse
      (fun π => bestRemainingAfter π (1 : Candidate 1) = (0 : Candidate 1)))
    hlam3_half hd1_pos hd12 hd3_nonpos

/-- Appendix C / Theorem 6 from its named finite certificate. -/
theorem rum3_prefersWeakerCompetition_of_certificate
    {μBetter μWorse : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    {x1 x2 x3 : ℝ}
    (cert : RUM3Theorem6Certificate μBetter μWorse value x1 x2 x3) :
    Model.PrefersWeakerCompetition μBetter μWorse value :=
  rum3_prefersWeakerCompetition
    μBetter μWorse value
    cert.value_first cert.value_second cert.value_third
    cert.value12 cert.value23
    cert.lambda1_half cert.lambda1_lt_one cert.lambda12 cert.lambda3_half
    cert.delta_top_pos cert.delta_middle_le_top cert.delta_bottom_nonpos

end KR21Monoculture
