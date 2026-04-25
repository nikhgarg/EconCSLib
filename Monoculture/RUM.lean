import Monoculture.Theorem1
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open DecisionCore

namespace Monoculture

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
  ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
    f (a - c) * f (b - d) > f (a - d) * f (b - c)

/--
Weak version of Definition 4.  This is useful for Laplacian kernels, where the
strict paper inequality can be an equality when the two ordered intervals are
separated on the real line.
-/
def WeaklyWellOrderedNoise (f : ℝ → ℝ) : Prop :=
  ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
    f (a - d) * f (b - c) ≤ f (a - c) * f (b - d)

/-- Gaussian density kernel, omitting the positive normalizing constant. -/
noncomputable def gaussianNoiseKernel (κ : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-κ * x ^ 2)

/-- Laplacian density kernel, omitting the positive normalizing constant. -/
noncomputable def laplacianNoiseKernel (lam : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-lam * |x|)

/--
The algebraic core of the Gaussian well-ordering proof:
swapping the larger realized value to the larger true value improves the
negative squared-error exponent by `2κ(a-b)(c-d)`.
-/
theorem gaussian_exponent_cross_lt_ordered
    {κ a b c d : ℝ} (hκ : 0 < κ) (hab : b < a) (hcd : d < c) :
    -κ * (a - d) ^ 2 + -κ * (b - c) ^ 2 <
      -κ * (a - c) ^ 2 + -κ * (b - d) ^ 2 := by
  have hab_pos : 0 < a - b := sub_pos.mpr hab
  have hcd_pos : 0 < c - d := sub_pos.mpr hcd
  have hprod : 0 < 2 * κ * (a - b) * (c - d) := by
    have hκab : 0 < κ * (a - b) := mul_pos hκ hab_pos
    have h2κab : 0 < 2 * (κ * (a - b)) := mul_pos zero_lt_two hκab
    have hmain : 0 < (2 * (κ * (a - b))) * (c - d) := mul_pos h2κab hcd_pos
    simpa [mul_assoc] using hmain
  have hid :
      (-κ * (a - c) ^ 2 + -κ * (b - d) ^ 2) -
          (-κ * (a - d) ^ 2 + -κ * (b - c) ^ 2) =
        2 * κ * (a - b) * (c - d) := by
    ring
  have hdiff :
      0 <
        (-κ * (a - c) ^ 2 + -κ * (b - d) ^ 2) -
          (-κ * (a - d) ^ 2 + -κ * (b - c) ^ 2) := by
    rw [hid]
    exact hprod
  exact sub_pos.mp hdiff

/-- Gaussian kernels satisfy the paper's strict well-ordering condition. -/
theorem gaussianNoiseKernel_strictlyWellOrdered
    {κ : ℝ} (hκ : 0 < κ) :
    StrictlyWellOrderedNoise (gaussianNoiseKernel κ) := by
  intro a b c d hab hcd
  unfold gaussianNoiseKernel
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_lt_exp.mpr
    (gaussian_exponent_cross_lt_ordered hκ hab hcd)

/-- Four-point rearrangement inequality for absolute distance on the line. -/
theorem abs_ordered_cross_le_ordered
    {a b c d : ℝ} (hab : b ≤ a) (hcd : d ≤ c) :
    |a - c| + |b - d| ≤ |a - d| + |b - c| := by
  cases abs_cases (a - c) <;>
    cases abs_cases (b - d) <;>
    cases abs_cases (a - d) <;>
    cases abs_cases (b - c) <;>
    linarith

/--
Strict four-point rearrangement for absolute distance when the two ordered
intervals overlap (`b < c` and `d < a`).
-/
theorem abs_ordered_cross_lt_ordered_of_overlap
    {a b c d : ℝ} (hab : b < a) (hcd : d < c) (hbc : b < c) (hda : d < a) :
    |a - c| + |b - d| < |a - d| + |b - c| := by
  cases abs_cases (a - c) <;>
    cases abs_cases (b - d) <;>
    cases abs_cases (a - d) <;>
    cases abs_cases (b - c) <;>
    linarith

/-- Laplacian kernels satisfy the weak well-ordering inequality. -/
theorem laplacianNoiseKernel_weaklyWellOrdered
    {lam : ℝ} (hlam : 0 ≤ lam) :
    WeaklyWellOrderedNoise (laplacianNoiseKernel lam) := by
  intro a b c d hab hcd
  have habs := abs_ordered_cross_le_ordered
    (a := a) (b := b) (c := c) (d := d) (le_of_lt hab) (le_of_lt hcd)
  unfold laplacianNoiseKernel
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmul :
      (-lam) * (|a - d| + |b - c|) ≤
        (-lam) * (|a - c| + |b - d|) := by
    exact mul_le_mul_of_nonpos_left habs (neg_nonpos.mpr hlam)
  linarith

/--
The paper's strict Definition 4 is not satisfied by the Laplacian kernel as
stated: for separated ordered pairs, both assignments have the same total
absolute deviation.
-/
theorem laplacianNoiseKernel_not_strictlyWellOrdered (lam : ℝ) :
    ¬ StrictlyWellOrderedNoise (laplacianNoiseKernel lam) := by
  intro h
  have hbad := h (a := (10 : ℝ)) (b := 9) (c := 1) (d := 0)
    (by norm_num) (by norm_num)
  have heq :
      laplacianNoiseKernel lam ((10 : ℝ) - 1) *
          laplacianNoiseKernel lam (9 - 0) =
        laplacianNoiseKernel lam ((10 : ℝ) - 0) *
          laplacianNoiseKernel lam (9 - 1) := by
    unfold laplacianNoiseKernel
    norm_num
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hbad
  exact lt_irrefl _ hbad

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
  have habs := abs_ordered_cross_lt_ordered_of_overlap hab hcd hbc hda
  unfold laplacianNoiseKernel
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  have hmul :
      (-lam) * (|a - d| + |b - c|) <
        (-lam) * (|a - c| + |b - d|) := by
    exact mul_lt_mul_of_neg_left habs (by linarith)
  linarith

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
    simpa [Candidate, Fin.sum_univ_three] using
      (sum_firstChoiceProb_eq_one (μ := μBetter) (n := 1))
  have hworse_sum :
      firstChoiceProb μWorse (0 : Candidate 1) +
          firstChoiceProb μWorse (1 : Candidate 1) +
          firstChoiceProb μWorse (2 : Candidate 1) = 1 := by
    simpa [Candidate, Fin.sum_univ_three] using
      (sum_firstChoiceProb_eq_one (μ := μWorse) (n := 1))
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

end Monoculture
