import Mathlib.Tactic

/-!
# LMMS Section 3.3: rounding-transfer algebra

The proof of LMMS Theorem 3.3 invokes Lemma 3.5 in both directions and then
performs a deterministic algebraic transfer from additive per-player rounding
errors to a multiplicative envy-ratio bound.  This file formalizes that
certificate layer.  It deliberately does not assert that the rounded instance
or integer program has already been constructed.
-/

namespace LMMS04FairDivision
namespace Theorem35

noncomputable section

/-- Ratio of largest to smallest bundle value in the common-value scheduling view. -/
def ratio (minLoad maxLoad : ℝ) : ℝ :=
  maxLoad / minLoad

/-- Multiplicative loss when converting a rounded allocation back to the source instance. -/
def backwardTransferFactor (lambda : ℝ) : ℝ :=
  (1 + 2 / lambda) / (lambda / (lambda + 1) - 4 / lambda)

/-- Multiplicative loss when converting a source allocation to the rounded instance. -/
def forwardTransferFactor (lambda : ℝ) : ℝ :=
  (((lambda + 1) / lambda) + 2 / lambda) / (1 - 2 / lambda)

/-- The product factor displayed at the end of the proof of Theorem 3.3. -/
def theorem33TransferFactor (lambda : ℝ) : ℝ :=
  (lambda + 1) * (lambda + 2) * (lambda + 3) /
    ((lambda - 2) * (lambda ^ 2 - 4 * lambda - 4))

/-- A max-over-min ratio is nonnegative when the minimum is positive and the maximum is nonnegative. -/
theorem ratio_nonneg {minLoad maxLoad : ℝ}
    (hmin : 0 < minLoad) (hmax : 0 ≤ maxLoad) :
    0 ≤ ratio minLoad maxLoad := by
  exact div_nonneg hmax (le_of_lt hmin)

/--
The second direction of Lemma 3.5 gives `aMax ≤ bMax + L / lambda`.
If the rounded maximum load is at least half of the relevant average scale,
this becomes the source proof's multiplicative upper bound.
-/
theorem backward_max_transfer
    {lambda L aMax bMax : ℝ}
    (hlambda : 0 < lambda)
    (hL_le : L ≤ 2 * bMax)
    (htransfer : aMax ≤ bMax + L / lambda) :
    aMax ≤ bMax * (1 + 2 / lambda) := by
  have hdiv : L / lambda ≤ (2 * bMax) / lambda :=
    div_le_div_of_nonneg_right hL_le (le_of_lt hlambda)
  calc
    aMax ≤ bMax + L / lambda := htransfer
    _ ≤ bMax + (2 * bMax) / lambda := by linarith
    _ = bMax * (1 + 2 / lambda) := by ring

/--
The second direction of Lemma 3.5 gives
`lambda/(lambda+1) * bMin - (2/lambda) * L ≤ aMin`.
If the rounded minimum load is at least half of the relevant average scale,
this becomes the source proof's multiplicative lower bound.
-/
theorem backward_min_transfer
    {lambda L aMin bMin : ℝ}
    (hlambda : 0 < lambda)
    (hL_le : L ≤ 2 * bMin)
    (htransfer : (lambda / (lambda + 1)) * bMin - (2 / lambda) * L ≤ aMin) :
    bMin * (lambda / (lambda + 1) - 4 / lambda) ≤ aMin := by
  have hcoef_nonneg : 0 ≤ 2 / lambda := by positivity
  have hscaled : (2 / lambda) * L ≤ (2 / lambda) * (2 * bMin) :=
    mul_le_mul_of_nonneg_left hL_le hcoef_nonneg
  calc
    bMin * (lambda / (lambda + 1) - 4 / lambda)
        = (lambda / (lambda + 1)) * bMin - (2 / lambda) * (2 * bMin) := by
          ring
    _ ≤ (lambda / (lambda + 1)) * bMin - (2 / lambda) * L := by
          linarith
    _ ≤ aMin := htransfer

/--
The first direction of Lemma 3.5 gives
`bMax ≤ ((lambda+1)/lambda) * aMax + L / lambda`.
Using the Claim 3.4 lower half-average condition on `aMax`, this gives the
source proof's rounded-instance maximum bound.
-/
theorem forward_max_transfer
    {lambda L aMax bMax : ℝ}
    (hlambda : 0 < lambda)
    (hL_le : L ≤ 2 * aMax)
    (htransfer : bMax ≤ ((lambda + 1) / lambda) * aMax + L / lambda) :
    bMax ≤ aMax * (((lambda + 1) / lambda) + 2 / lambda) := by
  have hdiv : L / lambda ≤ (2 * aMax) / lambda :=
    div_le_div_of_nonneg_right hL_le (le_of_lt hlambda)
  calc
    bMax ≤ ((lambda + 1) / lambda) * aMax + L / lambda := htransfer
    _ ≤ ((lambda + 1) / lambda) * aMax + (2 * aMax) / lambda := by
          linarith
    _ = aMax * (((lambda + 1) / lambda) + 2 / lambda) := by ring

/--
The first direction of Lemma 3.5 gives `aMin - L/lambda ≤ bMin`.
Using the Claim 3.4 lower half-average condition on `aMin`, this gives the
source proof's rounded-instance minimum bound.
-/
theorem forward_min_transfer
    {lambda L aMin bMin : ℝ}
    (hlambda : 0 < lambda)
    (hL_le : L ≤ 2 * aMin)
    (htransfer : aMin - L / lambda ≤ bMin) :
    aMin * (1 - 2 / lambda) ≤ bMin := by
  have hdiv : L / lambda ≤ (2 * aMin) / lambda :=
    div_le_div_of_nonneg_right hL_le (le_of_lt hlambda)
  calc
    aMin * (1 - 2 / lambda) = aMin - (2 * aMin) / lambda := by ring
    _ ≤ aMin - L / lambda := by linarith
    _ ≤ bMin := htransfer

/--
Generic ratio transfer: an upper bound on the numerator and a lower bound on
the denominator convert two one-sided load estimates into a ratio estimate.
-/
theorem ratio_le_of_min_max_transfer
    {aMin aMax bMin bMax lowerFactor upperFactor : ℝ}
    (haMin : 0 < aMin)
    (hbMin : 0 < bMin)
    (hlower_pos : 0 < lowerFactor)
    (hupper_nonneg : 0 ≤ upperFactor)
    (hbMax_nonneg : 0 ≤ bMax)
    (hmax : aMax ≤ bMax * upperFactor)
    (hmin : bMin * lowerFactor ≤ aMin) :
    ratio aMin aMax ≤ ratio bMin bMax * (upperFactor / lowerFactor) := by
  have hden_pos : 0 < bMin * lowerFactor := mul_pos hbMin hlower_pos
  have hnum_nonneg : 0 ≤ bMax * upperFactor :=
    mul_nonneg hbMax_nonneg hupper_nonneg
  calc
    ratio aMin aMax = aMax / aMin := rfl
    _ ≤ (bMax * upperFactor) / aMin :=
          div_le_div_of_nonneg_right hmax (le_of_lt haMin)
    _ ≤ (bMax * upperFactor) / (bMin * lowerFactor) := by
          gcongr
    _ = ratio bMin bMax * (upperFactor / lowerFactor) := by
          rw [ratio]
          field_simp [ne_of_gt hbMin, ne_of_gt hlower_pos]

/--
Rounded-to-source ratio transfer corresponding to the second half of Lemma 3.5
in the proof of Theorem 3.3.
-/
theorem backward_ratio_transfer
    {lambda aMin aMax bMin bMax : ℝ}
    (haMin : 0 < aMin)
    (hbMin : 0 < bMin)
    (hlower :
      0 < lambda / (lambda + 1) - 4 / lambda)
    (hupper_nonneg : 0 ≤ 1 + 2 / lambda)
    (hbMax_nonneg : 0 ≤ bMax)
    (hmax : aMax ≤ bMax * (1 + 2 / lambda))
    (hmin : bMin * (lambda / (lambda + 1) - 4 / lambda) ≤ aMin) :
    ratio aMin aMax ≤ ratio bMin bMax * backwardTransferFactor lambda := by
  simpa [backwardTransferFactor] using
    ratio_le_of_min_max_transfer haMin hbMin hlower hupper_nonneg hbMax_nonneg
      hmax hmin

/--
Rounded-to-source ratio transfer derived directly from the additive inequalities
in the second half of Lemma 3.5.
-/
theorem backward_ratio_transfer_of_additive
    {lambda L outMin outMax roundedMin roundedMax : ℝ}
    (hlambda : 0 < lambda)
    (houtMin : 0 < outMin)
    (hroundedMin : 0 < roundedMin)
    (hlower : 0 < lambda / (lambda + 1) - 4 / lambda)
    (hupper_nonneg : 0 ≤ 1 + 2 / lambda)
    (hroundedMax_nonneg : 0 ≤ roundedMax)
    (hroundedMin_half : L ≤ 2 * roundedMin)
    (hroundedMax_half : L ≤ 2 * roundedMax)
    (hmax_transfer : outMax ≤ roundedMax + L / lambda)
    (hmin_transfer :
      (lambda / (lambda + 1)) * roundedMin - (2 / lambda) * L ≤ outMin) :
    ratio outMin outMax ≤
      ratio roundedMin roundedMax * backwardTransferFactor lambda := by
  exact
    backward_ratio_transfer houtMin hroundedMin hlower hupper_nonneg
      hroundedMax_nonneg
      (backward_max_transfer hlambda hroundedMax_half hmax_transfer)
      (backward_min_transfer hlambda hroundedMin_half hmin_transfer)

/--
Source-to-rounded ratio transfer corresponding to the first half of Lemma 3.5
in the proof of Theorem 3.3.
-/
theorem forward_ratio_transfer
    {lambda aMin aMax bMin bMax : ℝ}
    (hbMin : 0 < bMin)
    (haMin : 0 < aMin)
    (hlower : 0 < 1 - 2 / lambda)
    (hupper_nonneg : 0 ≤ ((lambda + 1) / lambda) + 2 / lambda)
    (haMax_nonneg : 0 ≤ aMax)
    (hmax : bMax ≤ aMax * (((lambda + 1) / lambda) + 2 / lambda))
    (hmin : aMin * (1 - 2 / lambda) ≤ bMin) :
    ratio bMin bMax ≤ ratio aMin aMax * forwardTransferFactor lambda := by
  simpa [forwardTransferFactor] using
    ratio_le_of_min_max_transfer hbMin haMin hlower hupper_nonneg haMax_nonneg
      hmax hmin

/--
Source-to-rounded ratio transfer derived directly from the additive inequalities
in the first half of Lemma 3.5.
-/
theorem forward_ratio_transfer_of_additive
    {lambda L sourceMin sourceMax roundedMin roundedMax : ℝ}
    (hlambda : 0 < lambda)
    (hroundedMin : 0 < roundedMin)
    (hsourceMin : 0 < sourceMin)
    (hlower : 0 < 1 - 2 / lambda)
    (hupper_nonneg : 0 ≤ ((lambda + 1) / lambda) + 2 / lambda)
    (hsourceMax_nonneg : 0 ≤ sourceMax)
    (hsourceMin_half : L ≤ 2 * sourceMin)
    (hsourceMax_half : L ≤ 2 * sourceMax)
    (hmax_transfer :
      roundedMax ≤ ((lambda + 1) / lambda) * sourceMax + L / lambda)
    (hmin_transfer : sourceMin - L / lambda ≤ roundedMin) :
    ratio roundedMin roundedMax ≤
      ratio sourceMin sourceMax * forwardTransferFactor lambda := by
  exact
    forward_ratio_transfer hroundedMin hsourceMin hlower hupper_nonneg
      hsourceMax_nonneg
      (forward_max_transfer hlambda hsourceMax_half hmax_transfer)
      (forward_min_transfer hlambda hsourceMin_half hmin_transfer)

/--
If the rounded allocation is optimal among rounded transfers of source
allocations, the two Lemma 3.5 ratio transfers compose into the paper's final
multiplicative factor.
-/
theorem theorem33_ratio_transfer_certificate
    {lambda optMin optMax roundedMin roundedMax outMin outMax : ℝ}
    (hout :
      ratio outMin outMax ≤
        ratio roundedMin roundedMax * backwardTransferFactor lambda)
    (hrounded_opt :
      ratio roundedMin roundedMax ≤
        ratio optMin optMax * forwardTransferFactor lambda)
    (hbackward_nonneg : 0 ≤ backwardTransferFactor lambda) :
    ratio outMin outMax ≤
      ratio optMin optMax *
        (backwardTransferFactor lambda * forwardTransferFactor lambda) := by
  calc
    ratio outMin outMax
        ≤ ratio roundedMin roundedMax * backwardTransferFactor lambda := hout
    _ ≤ (ratio optMin optMax * forwardTransferFactor lambda) *
          backwardTransferFactor lambda := by
          exact mul_le_mul_of_nonneg_right hrounded_opt hbackward_nonneg
    _ = ratio optMin optMax *
          (backwardTransferFactor lambda * forwardTransferFactor lambda) := by
          ring

/--
Algebraic identity for the explicit factor printed in the source proof.
-/
theorem transfer_factor_eq_source_fraction
    {lambda : ℝ}
    (hlambda : lambda ≠ 0)
    (hlambda_ne_neg_one : lambda + 1 ≠ 0)
    (hlambda_ne_two : lambda - 2 ≠ 0) :
    backwardTransferFactor lambda * forwardTransferFactor lambda =
      theorem33TransferFactor lambda := by
  unfold backwardTransferFactor forwardTransferFactor theorem33TransferFactor
  field_simp [hlambda, hlambda_ne_neg_one, hlambda_ne_two]
  ring

/--
For large enough `lambda`, the displayed transfer factor is bounded by the
source proof's simple `1 + 56 / lambda` envelope.
-/
theorem theorem33TransferFactor_le_one_add_56_div_of_ge_56
    {lambda : ℝ} (hlambda_ge : 56 ≤ lambda) :
    theorem33TransferFactor lambda ≤ 1 + 56 / lambda := by
  have hlambda_pos : 0 < lambda := by nlinarith
  have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda_pos
  have hlambda_minus_two_pos : 0 < lambda - 2 := by nlinarith
  have hsquare_ge : 56 * lambda ≤ lambda * lambda :=
    mul_le_mul_of_nonneg_right hlambda_ge hlambda_nonneg
  have hquad_pos : 0 < lambda ^ 2 - 4 * lambda - 4 := by
    have hquad_ge : 52 * lambda - 4 ≤ lambda ^ 2 - 4 * lambda - 4 := by
      nlinarith [hsquare_ge]
    have hlinear_pos : 0 < 52 * lambda - 4 := by nlinarith
    linarith
  have hden_pos :
      0 < lambda * (lambda - 2) * (lambda ^ 2 - 4 * lambda - 4) :=
    mul_pos (mul_pos hlambda_pos hlambda_minus_two_pos) hquad_pos
  have hcoef_nonneg : 0 ≤ 44 * lambda - 343 := by nlinarith
  have hterm1_nonneg :
      0 ≤ lambda ^ 2 * (44 * lambda - 343) :=
    mul_nonneg (sq_nonneg lambda) hcoef_nonneg
  have hterm2_nonneg : 0 ≤ 226 * lambda := by positivity
  have hpoly_nonneg :
      0 ≤ 44 * lambda ^ 3 - 343 * lambda ^ 2 + 226 * lambda + 448 := by
    have hpoly' :
        0 ≤ lambda ^ 2 * (44 * lambda - 343) + 226 * lambda + 448 := by
      nlinarith
    have heq :
        lambda ^ 2 * (44 * lambda - 343) + 226 * lambda + 448 =
          44 * lambda ^ 3 - 343 * lambda ^ 2 + 226 * lambda + 448 := by
      ring
    rwa [heq] at hpoly'
  have hden_source_pos :
      0 < (lambda - 2) * (lambda ^ 2 - 4 * lambda - 4) :=
    mul_pos hlambda_minus_two_pos hquad_pos
  have hpoly_le :
      lambda * ((lambda + 1) * (lambda + 2) * (lambda + 3)) ≤
        (lambda + 56) *
          ((lambda - 2) * (lambda ^ 2 - 4 * lambda - 4)) := by
    have hslack :
        (lambda + 56) *
            ((lambda - 2) * (lambda ^ 2 - 4 * lambda - 4)) -
          lambda * ((lambda + 1) * (lambda + 2) * (lambda + 3)) =
            44 * lambda ^ 3 - 343 * lambda ^ 2 + 226 * lambda + 448 := by
      ring
    nlinarith
  have htarget :
      (lambda + 1) * (lambda + 2) * (lambda + 3) ≤
        (1 + 56 / lambda) *
          ((lambda - 2) * (lambda ^ 2 - 4 * lambda - 4)) := by
    have hmul_target :
        lambda * ((lambda + 1) * (lambda + 2) * (lambda + 3)) ≤
          lambda *
            ((1 + 56 / lambda) *
              ((lambda - 2) * (lambda ^ 2 - 4 * lambda - 4))) := by
      calc
        lambda * ((lambda + 1) * (lambda + 2) * (lambda + 3))
            ≤ (lambda + 56) *
                ((lambda - 2) * (lambda ^ 2 - 4 * lambda - 4)) := hpoly_le
        _ = lambda *
              ((1 + 56 / lambda) *
                ((lambda - 2) * (lambda ^ 2 - 4 * lambda - 4))) := by
            field_simp [ne_of_gt hlambda_pos]
    exact le_of_mul_le_mul_left hmul_target hlambda_pos
  unfold theorem33TransferFactor
  rw [div_le_iff₀ hden_source_pos]
  exact htarget

/--
The paper's choice `lambda = 56 / epsilon` makes the displayed transfer
factor at most `1 + epsilon` for the usual PTAS regime `0 < epsilon ≤ 1`.
-/
theorem theorem33TransferFactor_le_one_add_epsilon
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1) :
    theorem33TransferFactor (56 / epsilon) ≤ 1 + epsilon := by
  have hlambda_ge : 56 ≤ 56 / epsilon := by
    rw [le_div_iff₀ hepsilon_pos]
    nlinarith
  have hbound :=
    theorem33TransferFactor_le_one_add_56_div_of_ge_56 hlambda_ge
  have hcancel : 56 / (56 / epsilon) = epsilon := by
    field_simp [ne_of_gt hepsilon_pos]
  simpa [hcancel] using hbound

/-- The backward-transfer denominator is positive in the source's large-`lambda` regime. -/
theorem backwardLowerFactor_pos_of_ge_56
    {lambda : ℝ} (hlambda_ge : 56 ≤ lambda) :
    0 < lambda / (lambda + 1) - 4 / lambda := by
  have hlambda_pos : 0 < lambda := by nlinarith
  have hlambda_nonneg : 0 ≤ lambda := le_of_lt hlambda_pos
  have hlambda_plus_one_pos : 0 < lambda + 1 := by nlinarith
  have hsquare_ge : 56 * lambda ≤ lambda * lambda :=
    mul_le_mul_of_nonneg_right hlambda_ge hlambda_nonneg
  have hquad_pos : 0 < lambda ^ 2 - 4 * lambda - 4 := by
    have hquad_ge : 52 * lambda - 4 ≤ lambda ^ 2 - 4 * lambda - 4 := by
      nlinarith [hsquare_ge]
    have hlinear_pos : 0 < 52 * lambda - 4 := by nlinarith
    linarith
  have hden_eq :
      lambda / (lambda + 1) - 4 / lambda =
        (lambda ^ 2 - 4 * lambda - 4) / (lambda * (lambda + 1)) := by
    field_simp [ne_of_gt hlambda_pos, ne_of_gt hlambda_plus_one_pos]
    ring
  rw [hden_eq]
  positivity

/-- The forward-transfer denominator is positive in the source's large-`lambda` regime. -/
theorem forwardLowerFactor_pos_of_ge_56
    {lambda : ℝ} (hlambda_ge : 56 ≤ lambda) :
    0 < 1 - 2 / lambda := by
  have hlambda_pos : 0 < lambda := by nlinarith
  have htwo_lt_lambda : (2 : ℝ) < lambda := by nlinarith
  have hdiv_lt : 2 / lambda < 1 := by
    rwa [div_lt_one hlambda_pos]
  linarith

/-- The backward transfer factor is nonnegative in the source's large-`lambda` regime. -/
theorem backwardTransferFactor_nonneg_of_ge_56
    {lambda : ℝ} (hlambda_ge : 56 ≤ lambda) :
    0 ≤ backwardTransferFactor lambda := by
  have hlambda_pos : 0 < lambda := by nlinarith
  have hden_pos : 0 < lambda / (lambda + 1) - 4 / lambda :=
    backwardLowerFactor_pos_of_ge_56 hlambda_ge
  have hnum_nonneg : 0 ≤ 1 + 2 / lambda := by positivity
  unfold backwardTransferFactor
  exact div_nonneg hnum_nonneg (le_of_lt hden_pos)

/-- The backward transfer factor is nonnegative for `lambda = 56 / epsilon`. -/
theorem backwardTransferFactor_nonneg_of_epsilon
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1) :
    0 ≤ backwardTransferFactor (56 / epsilon) := by
  have hlambda_ge : 56 ≤ 56 / epsilon := by
    rw [le_div_iff₀ hepsilon_pos]
    nlinarith
  exact backwardTransferFactor_nonneg_of_ge_56 hlambda_ge

/--
End-to-end algebraic transfer endpoint for Theorem 3.3: after applying the
two Lemma 3.5 transfer directions with `lambda = 56 / epsilon`, the resulting
allocation has ratio at most `(1 + epsilon)` times the source optimum.
-/
theorem theorem33_ratio_transfer_certificate_epsilon
    {epsilon optMin optMax roundedMin roundedMax outMin outMax : ℝ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (hout :
      ratio outMin outMax ≤
        ratio roundedMin roundedMax * backwardTransferFactor (56 / epsilon))
    (hrounded_opt :
      ratio roundedMin roundedMax ≤
        ratio optMin optMax * forwardTransferFactor (56 / epsilon))
    (hopt_ratio_nonneg : 0 ≤ ratio optMin optMax) :
    ratio outMin outMax ≤ ratio optMin optMax * (1 + epsilon) := by
  have hbackward_nonneg :
      0 ≤ backwardTransferFactor (56 / epsilon) :=
    backwardTransferFactor_nonneg_of_epsilon hepsilon_pos hepsilon_le_one
  have hcert :=
    theorem33_ratio_transfer_certificate
      (lambda := 56 / epsilon)
      (optMin := optMin) (optMax := optMax)
      (roundedMin := roundedMin) (roundedMax := roundedMax)
      (outMin := outMin) (outMax := outMax)
      hout hrounded_opt hbackward_nonneg
  have hlambda_ne : 56 / epsilon ≠ 0 := by
    positivity
  have hlambda_ne_neg_one : 56 / epsilon + 1 ≠ 0 := by
    positivity
  have hlambda_ne_two : 56 / epsilon - 2 ≠ 0 := by
    have hlambda_ge : 56 ≤ 56 / epsilon := by
      rw [le_div_iff₀ hepsilon_pos]
      nlinarith
    nlinarith
  have hfactor_eq :
      backwardTransferFactor (56 / epsilon) *
          forwardTransferFactor (56 / epsilon) =
        theorem33TransferFactor (56 / epsilon) :=
    transfer_factor_eq_source_fraction
      hlambda_ne hlambda_ne_neg_one hlambda_ne_two
  have hfactor_le :
      backwardTransferFactor (56 / epsilon) *
          forwardTransferFactor (56 / epsilon) ≤
        1 + epsilon := by
    rw [hfactor_eq]
    exact theorem33TransferFactor_le_one_add_epsilon
      hepsilon_pos hepsilon_le_one
  exact
    hcert.trans
      (mul_le_mul_of_nonneg_left hfactor_le hopt_ratio_nonneg)

/--
Natural-load version of the Theorem 3.3 transfer endpoint.  The optimal
source ratio is nonnegative whenever its minimum load is positive and maximum
load is nonnegative.
-/
theorem theorem33_ratio_transfer_certificate_epsilon_of_opt_loads
    {epsilon optMin optMax roundedMin roundedMax outMin outMax : ℝ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (hoptMin : 0 < optMin) (hoptMax : 0 ≤ optMax)
    (hout :
      ratio outMin outMax ≤
        ratio roundedMin roundedMax * backwardTransferFactor (56 / epsilon))
    (hrounded_opt :
      ratio roundedMin roundedMax ≤
        ratio optMin optMax * forwardTransferFactor (56 / epsilon)) :
    ratio outMin outMax ≤ ratio optMin optMax * (1 + epsilon) := by
  exact
    theorem33_ratio_transfer_certificate_epsilon
      hepsilon_pos hepsilon_le_one hout hrounded_opt
      (ratio_nonneg hoptMin hoptMax)

/--
End-to-end Lemma 3.5/Theorem 3.3 transfer endpoint from the raw additive
rounding inequalities, specialized to the paper choice `lambda = 56 / epsilon`.
-/
theorem theorem33_ratio_transfer_certificate_epsilon_of_additive
    {epsilon L optMin optMax roundedMin roundedMax outMin outMax : ℝ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (houtMin : 0 < outMin)
    (hroundedMin : 0 < roundedMin)
    (hoptMin : 0 < optMin) (hoptMax : 0 ≤ optMax)
    (hroundedMax_nonneg : 0 ≤ roundedMax)
    (hroundedMin_half : L ≤ 2 * roundedMin)
    (hroundedMax_half : L ≤ 2 * roundedMax)
    (hoptMin_half : L ≤ 2 * optMin)
    (hoptMax_half : L ≤ 2 * optMax)
    (hbackward_max :
      outMax ≤ roundedMax + L / (56 / epsilon))
    (hbackward_min :
      ((56 / epsilon) / ((56 / epsilon) + 1)) * roundedMin -
          (2 / (56 / epsilon)) * L ≤ outMin)
    (hforward_max :
      roundedMax ≤ (((56 / epsilon) + 1) / (56 / epsilon)) * optMax +
        L / (56 / epsilon))
    (hforward_min :
      optMin - L / (56 / epsilon) ≤ roundedMin) :
    ratio outMin outMax ≤ ratio optMin optMax * (1 + epsilon) := by
  let lambda : ℝ := 56 / epsilon
  have hlambda_pos : 0 < lambda := by
    dsimp [lambda]
    positivity
  have hlambda_ge : 56 ≤ lambda := by
    dsimp [lambda]
    rw [le_div_iff₀ hepsilon_pos]
    nlinarith
  have hbackward_lower :
      0 < lambda / (lambda + 1) - 4 / lambda :=
    backwardLowerFactor_pos_of_ge_56 hlambda_ge
  have hforward_lower : 0 < 1 - 2 / lambda :=
    forwardLowerFactor_pos_of_ge_56 hlambda_ge
  have hbackward_upper_nonneg : 0 ≤ 1 + 2 / lambda := by
    positivity
  have hforward_upper_nonneg :
      0 ≤ ((lambda + 1) / lambda) + 2 / lambda := by
    positivity
  have hout :
      ratio outMin outMax ≤
        ratio roundedMin roundedMax * backwardTransferFactor lambda := by
    exact
      backward_ratio_transfer_of_additive
        (lambda := lambda) (L := L)
        hlambda_pos houtMin hroundedMin hbackward_lower
        hbackward_upper_nonneg hroundedMax_nonneg
        hroundedMin_half hroundedMax_half
        (by simpa [lambda] using hbackward_max)
        (by simpa [lambda] using hbackward_min)
  have hrounded :
      ratio roundedMin roundedMax ≤
        ratio optMin optMax * forwardTransferFactor lambda := by
    exact
      forward_ratio_transfer_of_additive
        (lambda := lambda) (L := L)
        hlambda_pos hroundedMin hoptMin hforward_lower
        hforward_upper_nonneg hoptMax
        hoptMin_half hoptMax_half
        (by simpa [lambda] using hforward_max)
        (by simpa [lambda] using hforward_min)
  exact
    theorem33_ratio_transfer_certificate_epsilon_of_opt_loads
      hepsilon_pos hepsilon_le_one hoptMin hoptMax
      (by simpa [lambda] using hout)
      (by simpa [lambda] using hrounded)

/--
End-to-end Lemma 3.5/Theorem 3.3 transfer endpoint from per-agent additive
load inequalities.  This version is phrased directly over three load functions
on the common agent set, so the source, rounded, and output allocations can
live on different item types in later construction layers.
-/
theorem theorem33_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads
    {Agent : Type*} [Fintype Agent] [Nonempty Agent]
    {epsilon L : ℝ} {optLoad roundedLoad outLoad : Agent → ℝ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (houtMin :
      0 < (Finset.univ : Finset Agent).inf' Finset.univ_nonempty outLoad)
    (hroundedMin :
      0 < (Finset.univ : Finset Agent).inf' Finset.univ_nonempty roundedLoad)
    (hoptMin :
      0 < (Finset.univ : Finset Agent).inf' Finset.univ_nonempty optLoad)
    (hoptMax :
      0 ≤ (Finset.univ : Finset Agent).sup' Finset.univ_nonempty optLoad)
    (hroundedMax_nonneg :
      0 ≤ (Finset.univ : Finset Agent).sup' Finset.univ_nonempty roundedLoad)
    (hroundedMin_half :
      L ≤ 2 * (Finset.univ : Finset Agent).inf'
        Finset.univ_nonempty roundedLoad)
    (hroundedMax_half :
      L ≤ 2 * (Finset.univ : Finset Agent).sup'
        Finset.univ_nonempty roundedLoad)
    (hoptMin_half :
      L ≤ 2 * (Finset.univ : Finset Agent).inf'
        Finset.univ_nonempty optLoad)
    (hoptMax_half :
      L ≤ 2 * (Finset.univ : Finset Agent).sup'
        Finset.univ_nonempty optLoad)
    (hbackward_max_agent :
      ∀ i : Agent, outLoad i ≤ roundedLoad i + L / (56 / epsilon))
    (hbackward_min_agent :
      ∀ i : Agent,
        ((56 / epsilon) / ((56 / epsilon) + 1)) * roundedLoad i -
          (2 / (56 / epsilon)) * L ≤ outLoad i)
    (hforward_max_agent :
      ∀ i : Agent,
        roundedLoad i ≤ (((56 / epsilon) + 1) / (56 / epsilon)) *
            optLoad i + L / (56 / epsilon))
    (hforward_min_agent :
      ∀ i : Agent, optLoad i - L / (56 / epsilon) ≤ roundedLoad i) :
    ratio
        ((Finset.univ : Finset Agent).inf' Finset.univ_nonempty outLoad)
        ((Finset.univ : Finset Agent).sup' Finset.univ_nonempty outLoad) ≤
      ratio
          ((Finset.univ : Finset Agent).inf' Finset.univ_nonempty optLoad)
          ((Finset.univ : Finset Agent).sup' Finset.univ_nonempty optLoad) *
        (1 + epsilon) := by
  let outMin : ℝ :=
    (Finset.univ : Finset Agent).inf' Finset.univ_nonempty outLoad
  let outMax : ℝ :=
    (Finset.univ : Finset Agent).sup' Finset.univ_nonempty outLoad
  let roundedMin : ℝ :=
    (Finset.univ : Finset Agent).inf' Finset.univ_nonempty roundedLoad
  let roundedMax : ℝ :=
    (Finset.univ : Finset Agent).sup' Finset.univ_nonempty roundedLoad
  let optMin : ℝ :=
    (Finset.univ : Finset Agent).inf' Finset.univ_nonempty optLoad
  let optMax : ℝ :=
    (Finset.univ : Finset Agent).sup' Finset.univ_nonempty optLoad
  have hbackward_max :
      outMax ≤ roundedMax + L / (56 / epsilon) := by
    dsimp [outMax, roundedMax]
    apply Finset.sup'_le
    intro i _hi
    have hrounded_le :
        roundedLoad i ≤
          (Finset.univ : Finset Agent).sup'
            Finset.univ_nonempty roundedLoad :=
      Finset.le_sup'
        (s := (Finset.univ : Finset Agent))
        (f := roundedLoad)
        (by simp : i ∈ (Finset.univ : Finset Agent))
    exact
      le_trans (hbackward_max_agent i)
        (by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hrounded_le (L / (56 / epsilon)))
  have hbackward_min :
      ((56 / epsilon) / ((56 / epsilon) + 1)) * roundedMin -
        (2 / (56 / epsilon)) * L ≤ outMin := by
    have hcoef_nonneg :
        0 ≤ (56 / epsilon) / ((56 / epsilon) + 1) := by
      positivity
    dsimp [outMin, roundedMin]
    apply Finset.le_inf'
    intro i _hi
    have hmin_le :
        (Finset.univ : Finset Agent).inf' Finset.univ_nonempty roundedLoad ≤
          roundedLoad i :=
      Finset.inf'_le
        (s := (Finset.univ : Finset Agent))
        (f := roundedLoad)
        (by simp : i ∈ (Finset.univ : Finset Agent))
    have hscaled :
        ((56 / epsilon) / ((56 / epsilon) + 1)) *
            ((Finset.univ : Finset Agent).inf' Finset.univ_nonempty
              roundedLoad) ≤
          ((56 / epsilon) / ((56 / epsilon) + 1)) * roundedLoad i :=
      mul_le_mul_of_nonneg_left hmin_le hcoef_nonneg
    exact
      le_trans
        (sub_le_sub_right hscaled ((2 / (56 / epsilon)) * L))
        (hbackward_min_agent i)
  have hforward_max :
      roundedMax ≤ ((56 / epsilon + 1) / (56 / epsilon)) * optMax +
        L / (56 / epsilon) := by
    have hcoef_nonneg :
        0 ≤ ((56 / epsilon + 1) / (56 / epsilon)) := by
      positivity
    dsimp [roundedMax, optMax]
    apply Finset.sup'_le
    intro i _hi
    have hopt_le :
        optLoad i ≤
          (Finset.univ : Finset Agent).sup' Finset.univ_nonempty optLoad :=
      Finset.le_sup'
        (s := (Finset.univ : Finset Agent))
        (f := optLoad)
        (by simp : i ∈ (Finset.univ : Finset Agent))
    have hscaled :
        ((56 / epsilon + 1) / (56 / epsilon)) * optLoad i ≤
          ((56 / epsilon + 1) / (56 / epsilon)) *
            ((Finset.univ : Finset Agent).sup' Finset.univ_nonempty
              optLoad) :=
      mul_le_mul_of_nonneg_left hopt_le hcoef_nonneg
    exact
      le_trans (hforward_max_agent i)
        (by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hscaled (L / (56 / epsilon)))
  have hforward_min :
      optMin - L / (56 / epsilon) ≤ roundedMin := by
    dsimp [optMin, roundedMin]
    apply Finset.le_inf'
    intro i _hi
    have hopt_min_le :
        (Finset.univ : Finset Agent).inf' Finset.univ_nonempty optLoad ≤
          optLoad i :=
      Finset.inf'_le
        (s := (Finset.univ : Finset Agent))
        (f := optLoad)
        (by simp : i ∈ (Finset.univ : Finset Agent))
    exact
      le_trans
        (sub_le_sub_right hopt_min_le (L / (56 / epsilon)))
        (hforward_min_agent i)
  exact
    theorem33_ratio_transfer_certificate_epsilon_of_additive
      (epsilon := epsilon) (L := L)
      (optMin := optMin) (optMax := optMax)
      (roundedMin := roundedMin) (roundedMax := roundedMax)
      (outMin := outMin) (outMax := outMax)
      hepsilon_pos hepsilon_le_one
      (by simpa [outMin] using houtMin)
      (by simpa [roundedMin] using hroundedMin)
      (by simpa [optMin] using hoptMin)
      (by simpa [optMax] using hoptMax)
      (by simpa [roundedMax] using hroundedMax_nonneg)
      (by simpa [roundedMin] using hroundedMin_half)
      (by simpa [roundedMax] using hroundedMax_half)
      (by simpa [optMin] using hoptMin_half)
      (by simpa [optMax] using hoptMax_half)
      hbackward_max hbackward_min hforward_max hforward_min

end

end Theorem35
end LMMS04FairDivision
