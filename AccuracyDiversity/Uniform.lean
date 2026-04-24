import AccuracyDiversity.Exchange
import EconCSLean.Math.FiniteRounding
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace AccuracyDiversity

/--
Expected maximum of `q` iid `U([0,1])` draws.

For `q = 0` this gives `0`, matching the empty recommendation value. For
positive `q`, the value is `q / (q + 1) = 1 - 1 / (q + 1)`.
-/
noncomputable def uniformTopOneValue (q : ℕ) : ℝ :=
  1 - 1 / (q + 1 : ℝ)

@[simp] theorem uniformTopOneValue_zero :
    uniformTopOneValue 0 = 0 := by
  norm_num [uniformTopOneValue]

/-- Closed form for the one-step marginal of the uniform top-one value. -/
theorem uniformTopOneValue_succ_sub (q : ℕ) :
    uniformTopOneValue (q + 1) - uniformTopOneValue q =
      1 / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by
  have hq1 : (q + 1 : ℝ) ≠ 0 := by positivity
  have hq2 : (q + 2 : ℝ) ≠ 0 := by positivity
  unfold uniformTopOneValue
  field_simp [hq1, hq2]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf

/--
Closed form for the value lost by removing the last recommendation from the
uniform top-one value.
-/
theorem uniformTopOneValue_sub_pred {q : ℕ} (hq : 0 < q) :
    uniformTopOneValue q - uniformTopOneValue (q - 1) =
      1 / ((q : ℝ) * (q + 1 : ℝ)) := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hq1 : (q + 1 : ℝ) ≠ 0 := by positivity
  have hpred : ((q - 1 : ℕ) + 1 : ℝ) = (q : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  have hpred_sub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    linarith
  unfold uniformTopOneValue
  field_simp [hq0, hq1, hpred, hpred_sub]
  rw [hpred_sub]
  ring_nf

/-- Consumption model for the paper's `U([0,1])`, `k = 1` objective. -/
noncomputable def uniformTopOneConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) : ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := fun _ q => uniformTopOneValue q

/--
The `1/2`-homogeneity profile induced by square roots of type likelihoods.

This is the target profile in Proposition 2 for uniform conditional item
values.
-/
noncomputable def sqrtLikelihoodProfile {T : ℕ}
    (likelihood : ItemType T → ℝ) : GammaHomogeneityProfile T where
  gamma := 1 / 2
  targetWeight := fun t => Real.sqrt (likelihood t)

namespace sqrtLikelihoodProfile

@[simp] theorem normalizer_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) :
    (sqrtLikelihoodProfile likelihood).normalizer =
      ∑ t : ItemType T, Real.sqrt (likelihood t) := by
  rfl

theorem targetShare_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0) :
    (sqrtLikelihoodProfile likelihood).targetShare t =
      Real.sqrt (likelihood t) /
        ∑ i : ItemType T, Real.sqrt (likelihood i) := by
  exact GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero
    (G := sqrtLikelihoodProfile likelihood) (t := t) (by simpa using hnorm)

/--
Count closeness to the square-root target implies approximate
`1/2`-homogeneity.

This is the representation-only bridge used after the real-relaxation and
integer-rounding part of Proposition 2.
-/
theorem approx_of_count_abs_error {T : ℕ}
    (likelihood : ItemType T → ℝ) (a : CountAllocation T) {N : ℕ} {C : ℝ}
    (hN : DecisionCore.Allocation.total a = N) (hNpos : 0 < N)
    (hclose :
      ∀ t,
        |(a.count t : ℝ) -
          (N : ℝ) * (sqrtLikelihoodProfile likelihood).targetShare t| ≤ C) :
    (sqrtLikelihoodProfile likelihood).Approx a (C / (N : ℝ)) := by
  exact GammaHomogeneityProfile.approx_of_count_abs_error
    (sqrtLikelihoodProfile likelihood) a hN hNpos hclose

end sqrtLikelihoodProfile

namespace UniformTopOne

/--
The reciprocal product `1 / (q * (q + 1))` is antitone in the positive natural
count `q`.
-/
theorem one_div_nat_mul_succ_antitone {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) :
    1 / ((n : ℝ) * (n + 1 : ℝ)) ≤
      1 / ((m : ℝ) * (m + 1 : ℝ)) := by
  have hmpos : 0 < (m : ℝ) * (m + 1 : ℝ) := by positivity
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hden : (m : ℝ) * (m + 1 : ℝ) ≤ (n : ℝ) * (n + 1 : ℝ) := by
    nlinarith [hmnR]
  exact one_div_le_one_div_of_le hmpos hden

noncomputable def anchorLoss {T : ℕ}
    (anchor : CountAllocation T) (t : ItemType T) : ℝ :=
  1 / ((anchor.count t + 1 : ℝ) * (anchor.count t + 2 : ℝ))

noncomputable def anchorGain {T : ℕ}
    (anchor : CountAllocation T) (t : ItemType T) : ℝ :=
  1 / ((anchor.count t : ℝ) * (anchor.count t + 1 : ℝ))

/--
Strict marginal certificate used to rule out rounding crossings around an
integer anchor.

For every possible high type and positive-anchor low type, moving one item from
the high side to the low side would strictly improve the objective at the
anchor boundary.
-/
def StrictRoundingExchangeCertificate {T : ℕ}
    (likelihood : ItemType T → ℝ) (anchor : CountAllocation T) : Prop :=
  ∀ high low,
    0 < anchor.count low →
      likelihood high * anchorLoss anchor high <
        likelihood low * anchorGain anchor low

/--
Two-anchor strict marginal certificate for real-rounding arguments.

`upper` is used for high coordinates and `lower` for low coordinates. This is
the certificate shape corresponding to floor/ceiling anchors around a real
relaxation.
-/
def StrictRoundingExchangeCertificateBetween {T : ℕ}
    (likelihood : ItemType T → ℝ)
    (lower upper : CountAllocation T) : Prop :=
  ∀ high low,
    0 < lower.count low →
      likelihood high * anchorLoss upper high <
        likelihood low * anchorGain lower low

@[simp] theorem toConsumptionModel_likelihood {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T) :
    (uniformTopOneConsumptionModel likelihood).likelihood t = likelihood t := rfl

@[simp] theorem toConsumptionModel_valueOfCount {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T) (q : ℕ) :
    (uniformTopOneConsumptionModel likelihood).valueOfCount t q =
      uniformTopOneValue q := rfl

@[simp] theorem marginalValue_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T) (q : ℕ) :
    (uniformTopOneConsumptionModel likelihood).marginalValue t q =
      1 / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by
  rw [ConsumptionModel.marginalValue, DecisionCore.Allocation.marginal]
  exact uniformTopOneValue_succ_sub q

@[simp] theorem weightedForwardMarginal_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T) (q : ℕ) :
    (uniformTopOneConsumptionModel likelihood).weightedForwardMarginal t q =
      likelihood t * (1 / ((q + 1 : ℝ) * (q + 2 : ℝ))) := by
  rw [ConsumptionModel.weightedForwardMarginal, marginalValue_eq]
  rfl

@[simp] theorem weightedBackwardMarginal_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T) {q : ℕ} (hq : 0 < q) :
    (uniformTopOneConsumptionModel likelihood).weightedBackwardMarginal t q =
      likelihood t * (1 / ((q : ℝ) * (q + 1 : ℝ))) := by
  rw [ConsumptionModel.weightedBackwardMarginal]
  simp [hq.ne', uniformTopOneValue_sub_pred hq]

/--
Finite first-order condition for the paper's `U([0,1])`, `k = 1` objective.

At an optimal fixed-total allocation, the weighted marginal gain from adding
one item to any destination is at most the weighted marginal loss from any
positive source.
-/
theorem forwardMarginal_le_backwardMarginal_of_optimum {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hne : src ≠ dst)
    (hcan : DecisionCore.Allocation.CanMoveOne a src) :
    likelihood dst *
        (1 / ((a.count dst + 1 : ℝ) * (a.count dst + 2 : ℝ))) ≤
      likelihood src *
        (1 / ((a.count src : ℝ) * (a.count src + 1 : ℝ))) := by
  have h :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := uniformTopOneConsumptionModel likelihood) N hopt hne hcan
  rw [weightedForwardMarginal_eq] at h
  rw [weightedBackwardMarginal_eq likelihood src hcan] at h
  exact h

/--
A strict anchor-boundary exchange certificate rules out high/low rounding
crossings at any finite optimum of the uniform top-one objective.
-/
theorem noRoundingCrossing_of_strictExchangeCertificate {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ)
    {a anchor : CountAllocation T}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hlike_nonneg : ∀ t, 0 ≤ likelihood t)
    (hcert : StrictRoundingExchangeCertificate likelihood anchor) :
    EconCSLean.FiniteRounding.NoRoundingCrossing
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => anchor.count t) := by
  intro high low hbad
  by_cases hne : high = low
  · subst high
    have ha_le_anchor : a.count low ≤ anchor.count low :=
      Nat.le_of_succ_le hbad.2
    have hsucc_le_self : anchor.count low + 1 ≤ anchor.count low :=
      le_trans hbad.1 ha_le_anchor
    exact (Nat.not_succ_le_self (anchor.count low)) hsucc_le_self
  · have hcan : DecisionCore.Allocation.CanMoveOne a high :=
      lt_of_lt_of_le (Nat.succ_pos (anchor.count high)) hbad.1
    have hfo :=
      forwardMarginal_le_backwardMarginal_of_optimum
        likelihood N hopt hne hcan
    have hlow_pos : 0 < anchor.count low :=
      lt_of_lt_of_le (Nat.succ_pos (a.count low)) hbad.2
    have hloss_le_anchor :
        1 / ((a.count high : ℝ) * (a.count high + 1 : ℝ)) ≤
          anchorLoss anchor high := by
      have hraw := one_div_nat_mul_succ_antitone
        (m := anchor.count high + 1) (n := a.count high)
        (Nat.succ_pos _) hbad.1
      unfold anchorLoss
      norm_num [Nat.cast_add, Nat.cast_one] at hraw ⊢
      ring_nf at hraw ⊢
      exact hraw
    have hanchor_gain_le :
        anchorGain anchor low ≤
          1 / ((a.count low + 1 : ℝ) * (a.count low + 2 : ℝ)) := by
      have hraw := one_div_nat_mul_succ_antitone
        (m := a.count low + 1) (n := anchor.count low)
        (Nat.succ_pos _) hbad.2
      unfold anchorGain
      norm_num [Nat.cast_add, Nat.cast_one] at hraw ⊢
      ring_nf at hraw ⊢
      exact hraw
    have hactual_loss_le_anchor :
        likelihood high *
            (1 / ((a.count high : ℝ) * (a.count high + 1 : ℝ))) ≤
          likelihood high * anchorLoss anchor high :=
      mul_le_mul_of_nonneg_left hloss_le_anchor (hlike_nonneg high)
    have hanchor_gain_le_actual :
        likelihood low * anchorGain anchor low ≤
          likelihood low *
            (1 / ((a.count low + 1 : ℝ) * (a.count low + 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hanchor_gain_le (hlike_nonneg low)
    have hstrict :
        likelihood high *
            (1 / ((a.count high : ℝ) * (a.count high + 1 : ℝ))) <
          likelihood low *
            (1 / ((a.count low + 1 : ℝ) * (a.count low + 2 : ℝ))) :=
      lt_of_le_of_lt hactual_loss_le_anchor
        (lt_of_lt_of_le (hcert high low hlow_pos) hanchor_gain_le_actual)
    exact (not_lt_of_ge hfo) hstrict

/--
A strict two-anchor boundary exchange certificate rules out high/low rounding
crossings between lower and upper anchors at any finite optimum of the uniform
top-one objective.
-/
theorem noRoundingCrossingBetween_of_strictExchangeCertificate {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ)
    {a lower upper : CountAllocation T}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hlike_nonneg : ∀ t, 0 ≤ likelihood t)
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hcert : StrictRoundingExchangeCertificateBetween likelihood lower upper) :
    EconCSLean.FiniteRounding.NoRoundingCrossingBetween
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t) := by
  intro high low hbad
  by_cases hne : high = low
  · subst high
    have ha_le_lower : a.count low ≤ lower.count low :=
      Nat.le_of_succ_le hbad.2
    have hupper_succ_le_lower : upper.count low + 1 ≤ lower.count low :=
      le_trans hbad.1 ha_le_lower
    have hupper_succ_le_self : upper.count low + 1 ≤ upper.count low :=
      le_trans hupper_succ_le_lower (horder low)
    exact (Nat.not_succ_le_self (upper.count low)) hupper_succ_le_self
  · have hcan : DecisionCore.Allocation.CanMoveOne a high :=
      lt_of_lt_of_le (Nat.succ_pos (upper.count high)) hbad.1
    have hfo :=
      forwardMarginal_le_backwardMarginal_of_optimum
        likelihood N hopt hne hcan
    have hlow_pos : 0 < lower.count low :=
      lt_of_lt_of_le (Nat.succ_pos (a.count low)) hbad.2
    have hloss_le_upper :
        1 / ((a.count high : ℝ) * (a.count high + 1 : ℝ)) ≤
          anchorLoss upper high := by
      have hraw := one_div_nat_mul_succ_antitone
        (m := upper.count high + 1) (n := a.count high)
        (Nat.succ_pos _) hbad.1
      unfold anchorLoss
      norm_num [Nat.cast_add, Nat.cast_one] at hraw ⊢
      ring_nf at hraw ⊢
      exact hraw
    have hlower_gain_le :
        anchorGain lower low ≤
          1 / ((a.count low + 1 : ℝ) * (a.count low + 2 : ℝ)) := by
      have hraw := one_div_nat_mul_succ_antitone
        (m := a.count low + 1) (n := lower.count low)
        (Nat.succ_pos _) hbad.2
      unfold anchorGain
      norm_num [Nat.cast_add, Nat.cast_one] at hraw ⊢
      ring_nf at hraw ⊢
      exact hraw
    have hactual_loss_le_upper :
        likelihood high *
            (1 / ((a.count high : ℝ) * (a.count high + 1 : ℝ))) ≤
          likelihood high * anchorLoss upper high :=
      mul_le_mul_of_nonneg_left hloss_le_upper (hlike_nonneg high)
    have hlower_gain_le_actual :
        likelihood low * anchorGain lower low ≤
          likelihood low *
            (1 / ((a.count low + 1 : ℝ) * (a.count low + 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hlower_gain_le (hlike_nonneg low)
    have hstrict :
        likelihood high *
            (1 / ((a.count high : ℝ) * (a.count high + 1 : ℝ))) <
          likelihood low *
            (1 / ((a.count low + 1 : ℝ) * (a.count low + 2 : ℝ))) :=
      lt_of_le_of_lt hactual_loss_le_upper
        (lt_of_lt_of_le (hcert high low hlow_pos) hlower_gain_le_actual)
    exact (not_lt_of_ge hfo) hstrict

/--
Square-root shifted-target sufficient condition for the strict two-anchor
exchange certificate.

This captures the analytic core of the uniform `k = 1` relaxation: if
`likelihood t = scale * shift t ^ 2`, lower anchors satisfy
`lower.count t + 1 ≤ shift t`, and shifted targets satisfy
`shift t ≤ upper.count t + 1`, then the boundary marginal at every upper anchor
is strictly smaller than the boundary marginal at every positive lower anchor.
-/
theorem strictRoundingExchangeCertificateBetween_of_shifted_target {T : ℕ}
    (likelihood : ItemType T → ℝ)
    (lower upper : CountAllocation T)
    (scale : ℝ) (shift : ItemType T → ℝ)
    (hscale_pos : 0 < scale)
    (hlike : ∀ t, likelihood t = scale * (shift t) ^ 2)
    (hshift_nonneg : ∀ t, 0 ≤ shift t)
    (hupper : ∀ t, shift t ≤ (upper.count t : ℝ) + 1)
    (hlower : ∀ t, (lower.count t : ℝ) + 1 ≤ shift t) :
    StrictRoundingExchangeCertificateBetween likelihood lower upper := by
  intro high low hlow
  let upperDen : ℝ := ((upper.count high + 1 : ℝ) * (upper.count high + 2 : ℝ))
  let lowerDen : ℝ := ((lower.count low : ℝ) * (lower.count low + 1 : ℝ))
  have hupperDen_pos : 0 < upperDen := by
    dsimp [upperDen]
    positivity
  have hlowerDen_pos : 0 < lowerDen := by
    dsimp [lowerDen]
    positivity
  have hupper_sq_lt :
      (shift high) ^ 2 < upperDen := by
    have hnonneg := hshift_nonneg high
    have hle := hupper high
    dsimp [upperDen]
    nlinarith
  have hlower_den_lt_sq :
      lowerDen < (shift low) ^ 2 := by
    have hle := hlower low
    have hlow_cast : 0 < (lower.count low : ℝ) := by
      exact_mod_cast hlow
    dsimp [lowerDen]
    nlinarith
  have hupper_frac_lt_one :
      (shift high) ^ 2 / upperDen < 1 := by
    have hdiv :=
      div_lt_div_of_pos_right hupper_sq_lt hupperDen_pos
    have hden_ne : upperDen ≠ 0 := ne_of_gt hupperDen_pos
    simpa [hden_ne] using hdiv
  have hone_lt_lower_frac :
      1 < (shift low) ^ 2 / lowerDen := by
    have hdiv :=
      div_lt_div_of_pos_right hlower_den_lt_sq hlowerDen_pos
    have hden_ne : lowerDen ≠ 0 := ne_of_gt hlowerDen_pos
    simpa [hden_ne] using hdiv
  have hleft_lt_scale :
      likelihood high * anchorLoss upper high < scale := by
    have hmul := mul_lt_mul_of_pos_left hupper_frac_lt_one hscale_pos
    have hden_ne : upperDen ≠ 0 := ne_of_gt hupperDen_pos
    rw [hlike high, anchorLoss]
    dsimp [upperDen] at hden_ne hmul ⊢
    field_simp [hden_ne] at hmul ⊢
    nlinarith
  have hscale_lt_right :
      scale < likelihood low * anchorGain lower low := by
    have hmul := mul_lt_mul_of_pos_left hone_lt_lower_frac hscale_pos
    have hden_ne : lowerDen ≠ 0 := ne_of_gt hlowerDen_pos
    rw [hlike low, anchorGain]
    dsimp [lowerDen] at hden_ne hmul ⊢
    field_simp [hden_ne] at hmul ⊢
    nlinarith
  exact lt_trans hleft_lt_scale hscale_lt_right

end UniformTopOne

namespace UniformRounding

/--
Count-allocation wrapper for the combinatorial part of Appendix D.5.

If `anchor` is an integer floor/rounding anchor for a real relaxation, the
integer optimum `a` has no high/low crossing around that anchor, and the anchor
total is within one type-cardinality of `N`, then every count of `a` is within
one type-cardinality of the anchor count.
-/
theorem count_close_of_no_rounding_crossing {T : ℕ}
    (a anchor : CountAllocation T) {N B : ℕ}
    (ha : DecisionCore.Allocation.total a = N)
    (hanchor : DecisionCore.Allocation.total anchor = B)
    (hBle : B ≤ N)
    (hNlt : N < B + Fintype.card (ItemType T))
    (hno :
      EconCSLean.FiniteRounding.NoRoundingCrossing
        (fun t : ItemType T => a.count t)
        (fun t : ItemType T => anchor.count t)) :
    ∀ t : ItemType T,
      anchor.count t < a.count t + Fintype.card (ItemType T) ∧
        a.count t < anchor.count t + Fintype.card (ItemType T) := by
  intro t
  constructor
  · exact EconCSLean.FiniteRounding.NoRoundingCrossing.anchor_lt_count_add_card
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => anchor.count t)
      t ha hanchor hBle hno
  · exact EconCSLean.FiniteRounding.NoRoundingCrossing.count_lt_anchor_add_card
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => anchor.count t)
      t ha hanchor hNlt hno

/--
Two-anchor count-allocation wrapper for the combinatorial part of Appendix D.5.

If lower/upper anchors bracket the real relaxation, there is no high/low
crossing between those anchors, and both anchor totals are within one
type-cardinality of `N`, then every integer optimum is close to the bracket.
-/
theorem count_close_of_no_rounding_crossing_between {T : ℕ}
    (a lower upper : CountAllocation T) {N L U : ℕ}
    (ha : DecisionCore.Allocation.total a = N)
    (hlower : DecisionCore.Allocation.total lower = L)
    (hupper : DecisionCore.Allocation.total upper = U)
    (hNlt : N < L + Fintype.card (ItemType T))
    (hUlt : U < N + Fintype.card (ItemType T))
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hno :
      EconCSLean.FiniteRounding.NoRoundingCrossingBetween
        (fun t : ItemType T => a.count t)
        (fun t : ItemType T => lower.count t)
        (fun t : ItemType T => upper.count t)) :
    ∀ t : ItemType T,
      lower.count t < a.count t + Fintype.card (ItemType T) ∧
        a.count t < upper.count t + Fintype.card (ItemType T) := by
  intro t
  constructor
  · exact EconCSLean.FiniteRounding.NoRoundingCrossingBetween.lower_lt_count_add_card
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t)
      t ha hupper hUlt horder hno
  · exact EconCSLean.FiniteRounding.NoRoundingCrossingBetween.count_lt_upper_add_card
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t)
      t ha hlower hNlt horder hno

end UniformRounding

end AccuracyDiversity
