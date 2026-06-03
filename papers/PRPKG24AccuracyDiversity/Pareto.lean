import PRPKG24AccuracyDiversity.SeparableAsymptotic
import EconCSLib.Foundations.Math.GammaAsymptotics
import EconCSLib.Foundations.Math.PowerComparisons
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PRPKG24AccuracyDiversity

open scoped BigOperators

/--
Expected maximum of `q` draws from a distribution with tail index α.
Instead of calculating the integral, we define the target marginal behavior.
-/
def HasTailIndex (f : ℕ → ℝ) (index : ℝ) : Prop := ∃ C > 0, ∀ q, 0 < q → f (q + 1) - f q = C * (q : ℝ) ^ (index - 1)

/--
A model where every type has conditional item values with the same tail index.
-/
def HasTypeTailIndex (M : ConsumptionModel T) (index : ℝ) : Prop := ∀ t, HasTailIndex (M.valueOfCount t) index

/--
The γ-homogeneity profile for a Pareto distribution with tail index α.
The target weights are proportional to `likelihood ^ α`.
-/
noncomputable def paretoProfile {T : ℕ} (likelihood : ItemType T → ℝ) (α : ℝ) :
    GammaHomogeneityProfile T where
  gamma := 1 - 1/α
  targetWeight := fun t => (likelihood t) ^ α

/--
A Top-k oracle for a model where every type has item values following a Pareto
distribution with tail index α.
-/
noncomputable def ParetoTopKOracle {T : ℕ} (α : ℝ) : TopKValueOracle T where
  expectedTopSum _ _ q := (q : ℝ) ^ (1/α)

/-- Marginal decay exponent for the Pareto branch's power-law oracle. -/
noncomputable def paretoMarginalExponent (α : ℝ) : ℝ := (α - 1) / α

theorem paretoMarginalExponent_pos {α : ℝ} (hα_gt_one : 1 < α) :
    0 < paretoMarginalExponent α := by
  unfold paretoMarginalExponent
  exact div_pos (sub_pos.mpr hα_gt_one) (lt_trans zero_lt_one hα_gt_one)

theorem paretoMarginalExponent_one_div_eq_gamma
    {α : ℝ} (hα_gt_one : 1 < α) :
    1 / paretoMarginalExponent α = α / (α - 1) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hsub_pos : 0 < α - 1 := sub_pos.mpr hα_gt_one
  unfold paretoMarginalExponent
  field_simp [ne_of_gt hα_pos, ne_of_gt hsub_pos]

/--
Exact power-marginal value used as a source-faithful Pareto asymptotic
checkpoint.

The paper's Pareto branch uses marginal decay proportional to
`q^-((α-1)/α)`, which yields the target exponent `α/(α-1)`. This value
function records that marginal law exactly, leaving the full order-statistic
derivation as the remaining probability step.
-/
noncomputable def paretoPowerMarginalValue (α : ℝ) (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range q,
    (((j + 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α)))

/-- Common top-one oracle with exact Pareto power-law marginals. -/
noncomputable def paretoPowerMarginalOracle (T : ℕ) (α : ℝ) :
    TopKValueOracle T := TopKValueOracle.common T (paretoPowerMarginalValue α)

theorem paretoPowerMarginalValue_zero (α : ℝ) :
    paretoPowerMarginalValue α 0 = 0 := by
  simp [paretoPowerMarginalValue]

theorem paretoPowerMarginalValue_forward_marginal
    (α : ℝ) (q : ℕ) :
    paretoPowerMarginalValue α (q + 1) -
        paretoPowerMarginalValue α q =
      (((q + 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α))) := by
  simp [paretoPowerMarginalValue, Finset.sum_range_succ]

/-- Exact scaled marginal used by the Pareto power-marginal oracle. -/
noncomputable def paretoPowerMarginalScale (α : ℝ) (q : ℕ) : ℝ := (((q + 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α)))

theorem paretoPowerMarginalScale_pos (α : ℝ) (q : ℕ) :
    0 < paretoPowerMarginalScale α q := by
  unfold paretoPowerMarginalScale
  exact Real.rpow_pos_of_pos (by positivity) _

/-- A number in `(0,1)` is not an integer pole of `Gamma` after negation. -/
private theorem gamma_neg_delta_ne_zero_of_pos_lt_one
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) :
    Real.Gamma (-δ) ≠ 0 := EconCSLib.Math.gamma_neg_delta_ne_zero_of_pos_lt_one hδ_pos hδ_lt_one

/--
Finite gamma recurrence product for a shift `-δ` with `0 < δ < 1`.

This is the algebraic identity that rewrites Euler's `GammaSeq (-δ)` into the
gamma-ratio form needed for Pareto order-statistic tails.
-/
theorem gamma_neg_delta_prod_range_eq_gamma_div
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (q : ℕ) :
    (∏ j ∈ Finset.range (q + 1), (-δ + (j : ℝ))) =
      Real.Gamma ((q : ℝ) + 1 - δ) / Real.Gamma (-δ) := EconCSLib.Math.gamma_neg_delta_prod_range_eq_gamma_div hδ_pos hδ_lt_one q

/--
Gamma-ratio asymptotic for the Pareto rank calculation:
`Γ(q+1) / Γ(q+1-δ) ~ q^δ`.
-/
theorem gamma_ratio_nat_add_one_sub_asymptoticEquivalent
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun q : ℕ =>
        Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((q : ℝ) + 1 - δ))
      (fun q : ℕ => (q : ℝ) ^ δ) := EconCSLib.Math.gamma_ratio_nat_add_one_sub_asymptoticEquivalent hδ_pos hδ_lt_one

/--
Finite-difference bridge for the Pareto order-statistic rank calculation.

For a fixed rank, the Pareto source proof often first identifies the value
asymptotic `μ (q-r) q ~ C q^(1/α)` and then proves the explicit scaled-drop
limit.  This theorem converts those two source obligations into the marginal
limit expected by `ParetoOrderStatisticScaledMarginalCertificate`.
-/
theorem pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop
    {μ : ℕ → ℕ → ℝ} {α C : ℝ} {r : ℕ}
    (hα : 1 < α) (hC : 0 < C)
    (hvalue :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ => μ (q - r) q)
        (fun q : ℕ => C * ((q : ℝ) ^ (1 / α))))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((μ (q + 1 - r) (q + 1) - μ (q - r) q) /
              μ (q - r) q)))
        Filter.atTop (nhds (1 / α))) :
    Filter.Tendsto
      (fun q : ℕ =>
        (μ (q + 1 - r) (q + 1) - μ (q - r) q) /
          paretoPowerMarginalScale α q)
      Filter.atTop (nhds (C / α)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have hbase :
      Filter.Tendsto
        (fun q : ℕ =>
          (μ (q + 1 - r) (q + 1) - μ (q - r) q) /
            (((q + 1 : ℕ) : ℝ) ^ (-(1 - 1 / α))))
        Filter.atTop (nhds (C * (1 / α))) :=
    EconCSLib.Math.scaled_difference_limit_of_value_asymptotic_and_scaled_drop
      (value := fun q : ℕ => μ (q - r) q)
      (δ := 1 / α) (C := C) hC.ne' hvalue hdrop
  have htarget : C * (1 / α) = C / α := by ring
  rw [← htarget]
  refine Filter.Tendsto.congr' ?_ hbase
  filter_upwards with q
  have hscale_eq :
      (((q + 1 : ℕ) : ℝ) ^ (-(1 - 1 / α))) =
        paretoPowerMarginalScale α q := by
    unfold paretoPowerMarginalScale paretoMarginalExponent
    congr 1
    field_simp [hα_ne]
  rw [hscale_eq]

/--
Fixed-rank coefficient in the Pareto order-statistic marginal asymptotic.

The remaining Lemma D.4 probability calculation should prove that the rank
`r` contribution, scaled by `paretoPowerMarginalScale α`, tends to this value.
-/
noncomputable def paretoRankMarginalCoeff (α : ℝ) (r : ℕ) : ℝ :=
  (Real.Gamma ((r : ℝ) + 1 - 1 / α) /
      Real.Gamma ((r : ℝ) + 1)) / α

theorem paretoRankMarginalCoeff_pos {α : ℝ} (hα : 1 < α) (r : ℕ) :
    0 < paretoRankMarginalCoeff α r := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hinv_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hnum_arg_pos : 0 < (r : ℝ) + 1 - 1 / α := by
    have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
    linarith
  have hden_arg_pos : 0 < (r : ℝ) + 1 := by positivity
  unfold paretoRankMarginalCoeff
  exact div_pos
    (div_pos
      (Real.Gamma_pos_of_pos hnum_arg_pos)
      (Real.Gamma_pos_of_pos hden_arg_pos))
    hα_pos

/-- Fixed-rank value coefficient before taking the marginal finite difference. -/
noncomputable def paretoRankValueCoeff (α : ℝ) (r : ℕ) : ℝ := Real.Gamma ((r : ℝ) + 1 - 1 / α) / Real.Gamma ((r : ℝ) + 1)

theorem paretoRankValueCoeff_pos {α : ℝ} (hα : 1 < α) (r : ℕ) :
    0 < paretoRankValueCoeff α r := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hinv_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hnum_arg_pos : 0 < (r : ℝ) + 1 - 1 / α := by
    have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
    linarith
  have hden_arg_pos : 0 < (r : ℝ) + 1 := by positivity
  unfold paretoRankValueCoeff
  exact div_pos
    (Real.Gamma_pos_of_pos hnum_arg_pos)
    (Real.Gamma_pos_of_pos hden_arg_pos)

theorem paretoRankMarginalCoeff_eq_valueCoeff_div
    (α : ℝ) (r : ℕ) :
    paretoRankMarginalCoeff α r = paretoRankValueCoeff α r / α := by
  rfl

/--
Exact fixed-rank gamma-ratio sequence cited in Lemma D.4 before connecting it
to a concrete Pareto order-statistic law.
-/
noncomputable def paretoRankGammaRatioMean (α : ℝ) (r q : ℕ) : ℝ :=
  paretoRankValueCoeff α r *
    (Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((q : ℝ) + 1 - 1 / α))

/--
The exact gamma-ratio rank sequence has the fixed-rank value asymptotic cited
by Lemma D.4.
-/
theorem paretoRankGammaRatioMean_value_asymptoticEquivalent
    {α : ℝ} (hα : 1 < α) (r : ℕ) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun q : ℕ => paretoRankGammaRatioMean α r q)
      (fun q : ℕ => paretoRankValueCoeff α r * ((q : ℝ) ^ (1 / α))) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hδ_pos : 0 < 1 / α := one_div_pos.mpr hα_pos
  have hδ_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hcoeff_ne : paretoRankValueCoeff α r ≠ 0 :=
    (paretoRankValueCoeff_pos hα r).ne'
  have hgamma :=
    gamma_ratio_nat_add_one_sub_asymptoticEquivalent hδ_pos hδ_lt_one
  rw [EconCSLib.Math.AsymptoticEquivalent] at hgamma ⊢
  refine Filter.Tendsto.congr' ?_ hgamma
  filter_upwards [Filter.eventually_gt_atTop 0] with q hq
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqpow_ne : (q : ℝ) ^ (1 / α) ≠ 0 :=
    (Real.rpow_pos_of_pos hq_pos (1 / α)).ne'
  unfold paretoRankGammaRatioMean
  field_simp [hcoeff_ne, hqpow_ne]

/-- Exact recurrence for the fixed-rank gamma-ratio sequence. -/
theorem paretoRankGammaRatioMean_succ_div_self
    {α : ℝ} (hα : 1 < α) (r q : ℕ) :
    paretoRankGammaRatioMean α r (q + 1) /
        paretoRankGammaRatioMean α r q =
      (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hδ_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hcoeff_ne : paretoRankValueCoeff α r ≠ 0 :=
    (paretoRankValueCoeff_pos hα r).ne'
  have hq1_pos : 0 < ((q : ℝ) + 1) := by positivity
  have hq1_ne : ((q : ℝ) + 1) ≠ 0 := ne_of_gt hq1_pos
  have harg_pos : 0 < (q : ℝ) + 1 - 1 / α := by
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    linarith
  have harg_ne : (q : ℝ) + 1 - 1 / α ≠ 0 := ne_of_gt harg_pos
  have hgamma_q1_ne : Real.Gamma ((q : ℝ) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos hq1_pos).ne'
  have hgamma_arg_ne : Real.Gamma ((q : ℝ) + 1 - 1 / α) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg_pos).ne'
  have harg_succ_pos : 0 < ((q + 1 : ℕ) : ℝ) + 1 - 1 / α := by
    have hq_succ_nonneg : 0 ≤ (((q + 1 : ℕ) : ℝ)) := by positivity
    linarith
  have hgamma_arg_succ_ne :
      Real.Gamma (((q + 1 : ℕ) : ℝ) + 1 - 1 / α) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg_succ_pos).ne'
  have hgamma_num_succ :
      Real.Gamma (((q + 1 : ℕ) : ℝ) + 1) =
        (((q + 1 : ℕ) : ℝ) * Real.Gamma (((q + 1 : ℕ) : ℝ))) :=
    Real.Gamma_add_one (by positivity : (((q + 1 : ℕ) : ℝ)) ≠ 0)
  have hgamma_den_succ :
      Real.Gamma (((q + 1 : ℕ) : ℝ) + 1 - 1 / α) =
        (((q : ℝ) + 1 - 1 / α) *
          Real.Gamma ((q : ℝ) + 1 - 1 / α)) := by
    rw [show (((q + 1 : ℕ) : ℝ) + 1 - 1 / α) =
          ((q : ℝ) + 1 - 1 / α) + 1 by
        rw [Nat.cast_add, Nat.cast_one]
        ring]
    exact Real.Gamma_add_one harg_ne
  unfold paretoRankGammaRatioMean
  rw [hgamma_num_succ, hgamma_den_succ]
  rw [show (((q + 1 : ℕ) : ℝ)) = (q : ℝ) + 1 by
    rw [Nat.cast_add, Nat.cast_one]]
  field_simp [hcoeff_ne, hq1_ne, harg_ne, hgamma_q1_ne,
    hgamma_arg_ne, hgamma_arg_succ_ne]
  rw [show (((q : ℝ) + 1) * α - 1) / α =
      (q : ℝ) + 1 - 1 / α by
        field_simp [ne_of_gt hα_pos]]
  have halg_ne : ((q : ℝ) + 1) * α - 1 ≠ 0 := by
    intro hzero
    apply harg_ne
    field_simp [ne_of_gt hα_pos]
    linarith
  field_simp [hgamma_arg_ne, halg_ne]
  rw [show (((q : ℝ) + 1) * α - 1) / α =
      (q : ℝ) + 1 - 1 / α by
        field_simp [ne_of_gt hα_pos]]
  exact div_self hgamma_arg_ne

/-- The exact gamma-ratio rank sequence satisfies the Pareto scaled-drop law. -/
theorem paretoRankGammaRatioMean_scaled_drop
    {α : ℝ} (hα : 1 < α) (r : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        (((q + 1 : ℕ) : ℝ) *
          ((paretoRankGammaRatioMean α r (q + 1) -
              paretoRankGammaRatioMean α r q) /
            paretoRankGammaRatioMean α r q)))
      Filter.atTop (nhds (1 / α)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hratio :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)))
        Filter.atTop (nhds 1) := by
    have hbase :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) (1 : ℝ) (1 - 1 / α) (1 : ℝ) (d := 1)
        (by norm_num : (1 : ℝ) ≠ 0)
    simpa [one_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      Nat.cast_add, Nat.cast_one] using hbase
  have hlim :
      Filter.Tendsto
        (fun q : ℕ =>
          (1 / α) *
            (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)))
        Filter.atTop (nhds (1 / α)) := by
    simpa using hratio.const_mul (1 / α)
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards with q
  have hcoeff_ne : paretoRankValueCoeff α r ≠ 0 :=
    (paretoRankValueCoeff_pos hα r).ne'
  have hq1_pos : 0 < (q : ℝ) + 1 := by positivity
  have harg_pos : 0 < (q : ℝ) + 1 - 1 / α := by
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    have hδ_lt_one : 1 / α < 1 := by
      rw [div_lt_one hα_pos]
      exact hα
    linarith
  have harg_ne : (q : ℝ) + 1 - 1 / α ≠ 0 := ne_of_gt harg_pos
  have hmean_ne : paretoRankGammaRatioMean α r q ≠ 0 := by
    unfold paretoRankGammaRatioMean
    exact mul_ne_zero hcoeff_ne
      (div_ne_zero
        (Real.Gamma_pos_of_pos hq1_pos).ne'
        (Real.Gamma_pos_of_pos harg_pos).ne')
  have hrec := paretoRankGammaRatioMean_succ_div_self hα r q
  symm
  calc
    (((q + 1 : ℕ) : ℝ) *
        ((paretoRankGammaRatioMean α r (q + 1) -
            paretoRankGammaRatioMean α r q) /
          paretoRankGammaRatioMean α r q))
        =
      (((q + 1 : ℕ) : ℝ) *
        (paretoRankGammaRatioMean α r (q + 1) /
            paretoRankGammaRatioMean α r q - 1)) := by
          field_simp [hmean_ne]
    _ =
      (((q + 1 : ℕ) : ℝ) *
        ((((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)) - 1)) := by
          rw [hrec]
    _ =
      (1 / α) *
        (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)) := by
          have halg_ne : -1 + α + α * (q : ℝ) ≠ 0 := by
            intro hzero
            apply harg_ne
            field_simp [ne_of_gt hα_pos]
            linarith
          have halg2_ne : ((q : ℝ) + 1) * α - 1 ≠ 0 := by
            intro hzero
            apply harg_ne
            field_simp [ne_of_gt hα_pos]
            linarith
          field_simp [harg_ne, ne_of_gt hα_pos, halg_ne]
          field_simp [halg2_ne]
          rw [Nat.cast_add, Nat.cast_one]
          ring

/--
The exact gamma-ratio rank sequence gives the canonical per-rank Pareto
scaled marginal limit.
-/
theorem paretoRankGammaRatioMean_scaled_limit
    {α : ℝ} (hα : 1 < α) (r : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        (paretoRankGammaRatioMean α r (q + 1) -
            paretoRankGammaRatioMean α r q) /
          paretoPowerMarginalScale α q)
      Filter.atTop (nhds (paretoRankMarginalCoeff α r)) := by
  have h :=
    pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop
      (μ := fun _ q => paretoRankGammaRatioMean α r q)
      (α := α) (C := paretoRankValueCoeff α r) (r := r)
      hα (paretoRankValueCoeff_pos hα r)
      (paretoRankGammaRatioMean_value_asymptoticEquivalent hα r)
      (paretoRankGammaRatioMean_scaled_drop hα r)
  simpa [paretoRankMarginalCoeff, paretoRankValueCoeff] using h

/--
Canonical-coefficient version of the fixed-rank Pareto finite-difference
bridge.  This is the form expected after the external Lemma D.4 gamma-ratio
calculation proves the fixed-rank value asymptotic.
-/
theorem pareto_rank_scaled_limit_of_canonical_value_asymptotic_and_scaled_drop
    {μ : ℕ → ℕ → ℝ} {α : ℝ} {r : ℕ}
    (hα : 1 < α)
    (hvalue :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ => μ (q - r) q)
        (fun q : ℕ =>
          (Real.Gamma ((r : ℝ) + 1 - 1 / α) /
              Real.Gamma ((r : ℝ) + 1)) *
            ((q : ℝ) ^ (1 / α))))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((μ (q + 1 - r) (q + 1) - μ (q - r) q) /
              μ (q - r) q)))
        Filter.atTop (nhds (1 / α))) :
    Filter.Tendsto
      (fun q : ℕ =>
        (μ (q + 1 - r) (q + 1) - μ (q - r) q) /
          paretoPowerMarginalScale α q)
      Filter.atTop (nhds (paretoRankMarginalCoeff α r)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hinv_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hnum_arg_pos : 0 < (r : ℝ) + 1 - 1 / α := by
    have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
    linarith
  have hden_arg_pos : 0 < (r : ℝ) + 1 := by positivity
  have hcoeff_pos :
      0 <
        Real.Gamma ((r : ℝ) + 1 - 1 / α) /
          Real.Gamma ((r : ℝ) + 1) :=
    div_pos
      (Real.Gamma_pos_of_pos hnum_arg_pos)
      (Real.Gamma_pos_of_pos hden_arg_pos)
  simpa [paretoRankMarginalCoeff] using
    pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop
      hα hcoeff_pos hvalue hdrop

theorem paretoRankMarginalCoeff_sum_pos {α : ℝ} {k : ℕ}
    (hα : 1 < α) (hk : 0 < k) :
    0 < ∑ i : Fin k, paretoRankMarginalCoeff α i.val := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact Finset.sum_pos
    (fun i _hi => paretoRankMarginalCoeff_pos hα i.val)
    Finset.univ_nonempty

/--
The exact Pareto power-marginal oracle satisfies the reusable scaled-marginal
certificate with unit type weights.
-/
noncomputable def paretoPowerMarginalScaledMarginalLimitCertificate
    (T : ℕ) (α : ℝ) :
    TopKScaledMarginalLimitCertificate
      (paretoPowerMarginalOracle T α) 1
      (paretoPowerMarginalScale α)
      (fun _ : ItemType T => (1 : ℝ)) where
  scale_pos_eventually := by
    filter_upwards with q
    exact paretoPowerMarginalScale_pos α q
  weight_pos := by
    intro t
    norm_num
  marginal_ratio_tendsto := by
    intro t
    convert (tendsto_const_nhds : Filter.Tendsto
      (fun q : ℕ => (1 : ℝ)) Filter.atTop (nhds 1)) using 1
    ext q
    have hpow_ne :
        (((q : ℝ) + 1) ^ (-(paretoMarginalExponent α))) ≠ 0 :=
      (Real.rpow_pos_of_pos (by positivity) _).ne'
    simp [EconCSLib.Probability.TopKExpectationOracle.marginalTopK,
      topKExpectationOracleOfTopKValueOracle, paretoPowerMarginalOracle,
      TopKValueOracle.common, paretoPowerMarginalScale,
      paretoPowerMarginalValue_forward_marginal, hpow_ne]

/--
Source-side Pareto order-statistic asymptotic certificate.

Here `μ rank a` is the paper's bottom-indexed order-statistic mean
`μ_D(rank,a)`, and `limitCoeff` is the positive constant in the marginal form
of the Pareto top-`k` asymptotic.  The key source obligation is
`marginal_ratio_tendsto`: for fixed `k`, the discrete marginal of the paper's
Definition 3 top-`k` order-statistic sum is asymptotic to
`limitCoeff * q^-((α-1)/α)`.  Proving that field from Lemma D.4/equation (77)
is the remaining probability calculation.
-/
structure ParetoOrderStatisticScaledMarginalCertificate
    (μ : ℕ → ℕ → ℝ) (k : ℕ) (α limitCoeff : ℝ) : Prop where
  alpha_gt_one : 1 < α
  k_pos : 0 < k
  coeff_pos : 0 < limitCoeff
  marginal_ratio_tendsto :
    Filter.Tendsto
      (fun q : ℕ =>
        (orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q) /
          (paretoPowerMarginalScale α q * limitCoeff))
      Filter.atTop (nhds 1)

namespace ParetoOrderStatisticScaledMarginalCertificate

def toOrderStatisticScaledMarginalCertificate
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (C : ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff) :
    EconCSLib.Probability.OrderStatisticScaledMarginalCertificate μ k
      (paretoPowerMarginalScale α) limitCoeff where
  k_pos := C.k_pos
  coeff_pos := C.coeff_pos
  scale_pos_eventually := by
    filter_upwards with q
    exact paretoPowerMarginalScale_pos α q
  marginal_ratio_tendsto := C.marginal_ratio_tendsto

/--
Restate the source-side marginal field in the repository's standard
`AsymptoticEquivalent` vocabulary.  This is the exact form expected from the
remaining Pareto order-statistic probability calculation.
-/
theorem marginal_asymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (C : ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun q : ℕ =>
        orderStatisticTopKSumFromMean μ k (q + 1) -
          orderStatisticTopKSumFromMean μ k q)
      (fun q : ℕ => paretoPowerMarginalScale α q * limitCoeff) :=
  C.toOrderStatisticScaledMarginalCertificate.marginal_asymptoticEquivalent

/--
Constructor from the source-style asymptotic-equivalence statement for the
Pareto top-`k` order-statistic marginal.
-/
def ofMarginalAsymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (hα : 1 < α) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => paretoPowerMarginalScale α q * limitCoeff)) :
    ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff where
  alpha_gt_one := hα
  k_pos := hk
  coeff_pos := hcoeff
  marginal_ratio_tendsto := hmargin

/--
Variant of `ofMarginalAsymptoticEquivalent` for source calculations that write
the constant before the Pareto scale.
-/
def ofConstMulScaleAsymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (hα : 1 < α) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => limitCoeff * paretoPowerMarginalScale α q)) :
    ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff := by
  let G : EconCSLib.Probability.OrderStatisticScaledMarginalCertificate μ k
      (paretoPowerMarginalScale α) limitCoeff :=
    EconCSLib.Probability.OrderStatisticScaledMarginalCertificate.ofConstMulScaleAsymptoticEquivalent
        hk hcoeff
        (by
          filter_upwards with q
          exact paretoPowerMarginalScale_pos α q)
        hmargin
  exact
    { alpha_gt_one := hα
      k_pos := G.k_pos
      coeff_pos := G.coeff_pos
      marginal_ratio_tendsto := G.marginal_ratio_tendsto }

/--
Constructor from the paper's fixed-`k`, per-rank marginal sum.

The remaining Pareto calculation is usually stated rank-by-rank, for fixed
`i < k`, before summing over the top-`k` window.  This theorem exposes that
source-facing obligation: it is enough to prove the displayed finite `Fin k`
sum is asymptotic to the Pareto scale times the aggregate constant.
-/
def ofFiniteRankMarginalSumAsymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (hα : 1 < α) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          ∑ i : Fin k,
            (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q))
        (fun q : ℕ => limitCoeff * paretoPowerMarginalScale α q)) :
    ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff := by
  let G : EconCSLib.Probability.OrderStatisticScaledMarginalCertificate μ k
      (paretoPowerMarginalScale α) limitCoeff :=
    EconCSLib.Probability.OrderStatisticScaledMarginalCertificate.ofFiniteRankMarginalSumAsymptoticEquivalent
        hk hcoeff
        (by
          filter_upwards with q
          exact paretoPowerMarginalScale_pos α q)
        hmargin
  exact
    { alpha_gt_one := hα
      k_pos := G.k_pos
      coeff_pos := G.coeff_pos
      marginal_ratio_tendsto := G.marginal_ratio_tendsto }

/--
Constructor from fixed-rank scaled marginal limits.

This is the most direct handoff point for the remaining Pareto beta/gamma
calculation: prove, for each fixed rank `i < k`, that its marginal divided by
`paretoPowerMarginalScale α` tends to `rankCoeff i`, and prove that those
constants sum to `limitCoeff`.
-/
def ofFiniteRankScaledLimits
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (rankCoeff : Fin k → ℝ)
    (hα : 1 < α) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hcoeff_sum : (∑ i : Fin k, rankCoeff i) = limitCoeff)
    (hrank :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun q : ℕ =>
            (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q) /
              paretoPowerMarginalScale α q)
          Filter.atTop (nhds (rankCoeff i))) :
    ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff := by
  let G : EconCSLib.Probability.OrderStatisticScaledMarginalCertificate μ k
      (paretoPowerMarginalScale α) limitCoeff :=
    EconCSLib.Probability.OrderStatisticScaledMarginalCertificate.ofFiniteRankScaledLimits
        rankCoeff hk hcoeff
        (by
          filter_upwards with q
          exact paretoPowerMarginalScale_pos α q)
        hcoeff_sum hrank
  exact
    { alpha_gt_one := hα
      k_pos := G.k_pos
      coeff_pos := G.coeff_pos
      marginal_ratio_tendsto := G.marginal_ratio_tendsto }

/--
Pareto-specialized fixed-rank constructor.  The gamma-ratio calculation only
needs to prove the per-rank limits with the canonical Lemma D.4 coefficients;
Lean then supplies the positive aggregate coefficient automatically.
-/
def ofParetoRankScaledLimits
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k)
    (hrank :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun q : ℕ =>
            (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q) /
              paretoPowerMarginalScale α q)
          Filter.atTop (nhds (paretoRankMarginalCoeff α i.val))) :
    ParetoOrderStatisticScaledMarginalCertificate μ k α
      (∑ i : Fin k, paretoRankMarginalCoeff α i.val) :=
  ofFiniteRankScaledLimits
    (fun i : Fin k => paretoRankMarginalCoeff α i.val)
    hα hk (paretoRankMarginalCoeff_sum_pos hα hk) rfl hrank

/--
Convert the Pareto source-side order-statistic marginal asymptotic into the
reusable probability-to-optimization scaled marginal certificate.
-/
noncomputable def toTopKScaledMarginalLimitCertificate
    {T : ℕ} {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (C : ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T μ) k
      (paretoPowerMarginalScale α)
      (fun _ : ItemType T => limitCoeff) := by
  simpa [topKExpectationOracleOfTopKValueOracle,
      EconCSLib.Probability.TopKExpectationOracle.orderStatisticTopKExpectationOracle,
      TopKValueOracle.ofOrderStatisticMean]
    using
      C.toOrderStatisticScaledMarginalCertificate
        |>.toTopKExpectationScaledMarginalLimitCertificate (ItemType T)

end ParetoOrderStatisticScaledMarginalCertificate

theorem paretoPowerMarginalValue_backward_marginal
    (α : ℝ) {q : ℕ} (hq : 0 < q) :
    paretoPowerMarginalValue α q -
        paretoPowerMarginalValue α (q - 1) =
      ((q : ℝ) ^ (-(paretoMarginalExponent α))) := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  nth_rewrite 1 [← hpred]
  rw [paretoPowerMarginalValue_forward_marginal]
  simp [hpred]

theorem paretoPowerMarginalValue_forward_marginal_nonneg
    (α : ℝ) (q : ℕ) :
    0 ≤ paretoPowerMarginalValue α (q + 1) -
        paretoPowerMarginalValue α q := by
  rw [paretoPowerMarginalValue_forward_marginal]
  exact Real.rpow_nonneg (by positivity) _

theorem paretoPowerMarginalValue_marginal_antitone_step
    {α : ℝ} (hα_gt_one : 1 < α) (q : ℕ) :
    paretoPowerMarginalValue α (q + 2) -
        paretoPowerMarginalValue α (q + 1) ≤
      paretoPowerMarginalValue α (q + 1) -
        paretoPowerMarginalValue α q := by
  rw [paretoPowerMarginalValue_forward_marginal,
    paretoPowerMarginalValue_forward_marginal]
  have hbase_pos : 0 < ((q + 1 : ℕ) : ℝ) := by positivity
  have hbase_le : ((q + 1 : ℕ) : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.le_succ q)
  have hexp_nonpos : -(paretoMarginalExponent α) ≤ 0 :=
    neg_nonpos.mpr (le_of_lt (paretoMarginalExponent_pos hα_gt_one))
  exact Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le hexp_nonpos

theorem paretoPowerMarginalModel_has_nonnegative_marginals
    {T : ℕ} (likelihood : ItemType T → ℝ) (α : ℝ) :
    ((paretoPowerMarginalOracle T α).toConsumptionModel likelihood 1).HasNonnegativeMarginals := by
  intro t q
  exact paretoPowerMarginalValue_forward_marginal_nonneg α q

theorem paretoPowerMarginalModel_has_diminishing_returns
    {T : ℕ} (likelihood : ItemType T → ℝ) {α : ℝ}
    (hα_gt_one : 1 < α) :
    ((paretoPowerMarginalOracle T α).toConsumptionModel likelihood 1).HasDiminishingReturns := by
  intro t q
  exact paretoPowerMarginalValue_marginal_antitone_step hα_gt_one q

/-- Finite-prefix error for the exact Pareto power-marginal FOC proof. -/
noncomputable def paretoPowerMarginalError {T : ℕ}
    (likelihood : ItemType T → ℝ) (α : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 0 else
    ((∑ t : ItemType T, 1 / (likelihood t ^ (α / (α - 1)))) + 1) /
      (N : ℝ)

theorem paretoPowerMarginalError_nonneg {T : ℕ}
    (likelihood : ItemType T → ℝ) (α : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (N : ℕ) :
    0 ≤ paretoPowerMarginalError likelihood α N := by
  by_cases hN : N = 0
  · simp [paretoPowerMarginalError, hN]
  · have hS_nonneg :
        0 ≤ ∑ t : ItemType T, 1 / (likelihood t ^ (α / (α - 1))) :=
      Finset.sum_nonneg
        (fun t _ => div_nonneg zero_le_one
          (le_of_lt (Real.rpow_pos_of_pos (hlike_pos t) (α / (α - 1)))))
    have hN_pos : 0 < (N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hN
    have hnum_nonneg :
        0 ≤ (∑ t : ItemType T, 1 / (likelihood t ^ (α / (α - 1)))) + 1 :=
      add_nonneg hS_nonneg zero_le_one
    rw [paretoPowerMarginalError, if_neg hN]
    exact div_nonneg hnum_nonneg (le_of_lt hN_pos)

theorem paretoPowerMarginalError_tends_to_zero {T : ℕ}
    (likelihood : ItemType T → ℝ) (α : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    EconCSLib.Math.TendsToZero
      (paretoPowerMarginalError likelihood α) := by
  let S : ℝ := (∑ t : ItemType T, 1 / (likelihood t ^ (α / (α - 1)))) + 1
  have hsum_nonneg :
      0 ≤ ∑ t : ItemType T, 1 / (likelihood t ^ (α / (α - 1))) :=
    Finset.sum_nonneg
      (fun t _ => div_nonneg zero_le_one
        (le_of_lt (Real.rpow_pos_of_pos (hlike_pos t) (α / (α - 1)))))
  have hS_pos : 0 < S := by
    dsimp [S]
    linarith
  refine EconCSLib.Math.TendsToZero_of_nonneg_le_const_div
    (paretoPowerMarginalError likelihood α) hS_pos
    (paretoPowerMarginalError_nonneg likelihood α hlike_pos) ?_
  intro N hN
  have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
  simp [paretoPowerMarginalError, hN_ne, S]

/--
Exact Pareto power-marginal FOC certificate.

This closes the optimization layer for a top-one oracle with the paper's
Pareto marginal decay exponent. The remaining source-specific probability work
is to derive these power-law marginals, or their asymptotic equivalent, from the
actual Pareto order-statistic model.
-/
noncomputable def paretoPowerMarginalSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α : ℝ)
    (hα_gt_one : 1 < α)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    PairwiseScaledSublinearFOCCertificate
      (fun _ =>
        (paretoPowerMarginalOracle T α).toConsumptionModel likelihood 1)
      (fun t : ItemType T => likelihood t ^ (α / (α - 1)))
      (gammaLikelihoodProfile likelihood (α / (α - 1))) where
  weight_pos := by
    intro t
    exact Real.rpow_pos_of_pos (hlike_pos t) (α / (α - 1))
  targetShare_eq := by
    intro t
    have hnorm_pos :
        0 < ∑ i : ItemType T, likelihood i ^ (α / (α - 1)) :=
      Finset.sum_pos
        (fun i _ => Real.rpow_pos_of_pos (hlike_pos i) (α / (α - 1)))
        Finset.univ_nonempty
    exact gammaLikelihoodProfile_targetShare_eq likelihood (α / (α - 1)) t
      (ne_of_gt hnorm_pos)
  error := paretoPowerMarginalError likelihood α
  error_nonneg := paretoPowerMarginalError_nonneg likelihood α hlike_pos
  error_tends_to_zero :=
    paretoPowerMarginalError_tends_to_zero likelihood α hlike_pos
  large_gap_backward_lt_forward := by
    intro N a hN _hopt src dst hgap
    let γ : ℝ := α / (α - 1)
    let η : ℝ := paretoMarginalExponent α
    let weight : ItemType T → ℝ := fun t => likelihood t ^ γ
    let S : ℝ := (∑ t : ItemType T, 1 / weight t) + 1
    have hη_pos : 0 < η := by
      dsimp [η]
      exact paretoMarginalExponent_pos hα_gt_one
    have hγ_eq : 1 / η = γ := by
      dsimp [η, γ]
      exact paretoMarginalExponent_one_div_eq_gamma hα_gt_one
    have hweight_pos : ∀ t, 0 < weight t := by
      intro t
      dsimp [weight, γ]
      exact Real.rpow_pos_of_pos (hlike_pos t) (α / (α - 1))
    have hS_pos : 0 < S := by
      dsimp [S]
      have hsum_nonneg :
          0 ≤ ∑ t : ItemType T, 1 / weight t :=
        Finset.sum_nonneg
          (fun t _ => div_nonneg zero_le_one (le_of_lt (hweight_pos t)))
      linarith
    have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
    have hN_real_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN_ne
    have hgapS :
        S <
          (a.count src : ℝ) / weight src -
            (a.count dst : ℝ) / weight dst := by
      have hmul :
          paretoPowerMarginalError likelihood α N * (N : ℝ) = S := by
        simp [paretoPowerMarginalError, hN_ne, S, weight, γ,
          hN_real_ne]
      simpa [hmul, weight, γ] using hgap
    have hdst_nonneg :
        0 ≤ (a.count dst : ℝ) / weight dst :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt (hweight_pos dst))
    have hsrc_div_pos : 0 < (a.count src : ℝ) / weight src := by
      linarith
    have hsrc_pos : 0 < a.count src := by
      by_contra hnot
      have hzero : a.count src = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hzero] at hsrc_div_pos
      simp at hsrc_div_pos
    have hinv_dst_lt_S : 1 / weight dst < S := by
      have hinv_le_sum :
          1 / weight dst ≤ ∑ t : ItemType T, 1 / weight t :=
        Finset.single_le_sum
          (fun t _ => div_nonneg zero_le_one (le_of_lt (hweight_pos t)))
          (Finset.mem_univ dst)
      dsimp [S]
      linarith
    have hscaled_add :
        ((a.count dst : ℝ) + 1) / weight dst <
          (a.count src : ℝ) / weight src := by
      have hsum_lt :
          (a.count dst : ℝ) / weight dst + 1 / weight dst <
            (a.count src : ℝ) / weight src := by
        linarith
      have hadd :
          ((a.count dst : ℝ) + 1) / weight dst =
            (a.count dst : ℝ) / weight dst + 1 / weight dst := by
        ring
      simpa [hadd] using hsum_lt
    have hqsrc_real_pos : 0 < (a.count src : ℝ) := by
      exact_mod_cast hsrc_pos
    have hqdst_succ_pos :
        0 < ((a.count dst + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos (a.count dst)
    have hscaled_for_power :
        ((a.count dst + 1 : ℕ) : ℝ) / likelihood dst ^ (1 / η) <
          (a.count src : ℝ) / likelihood src ^ (1 / η) := by
      have hscaled' :
          ((a.count dst + 1 : ℕ) : ℝ) / weight dst <
            (a.count src : ℝ) / weight src := by
        simpa [Nat.cast_add, Nat.cast_one] using hscaled_add
      simpa [weight, γ, hγ_eq] using hscaled'
    have hmarginal_core :
        likelihood src * (1 * (a.count src : ℝ) ^ (-η)) <
          likelihood dst *
            (1 * (((a.count dst + 1 : ℕ) : ℝ) ^ (-η))) :=
      EconCSLib.Math.rpow_neg_marginal_lt_of_scaled_lt
        (c := 1) (eta := η)
        (hlike_pos src) (hlike_pos dst) zero_lt_one hη_pos
        hqsrc_real_pos hqdst_succ_pos hscaled_for_power
    have hmarginal :
        likelihood src *
            ((a.count src : ℝ) ^ (-(paretoMarginalExponent α))) <
          likelihood dst *
            (((a.count dst + 1 : ℕ) : ℝ) ^
              (-(paretoMarginalExponent α))) := by
      simpa [η] using hmarginal_core
    unfold ConsumptionModel.weightedBackwardMarginal
      ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
      EconCSLib.Allocation.marginal TopKValueOracle.toConsumptionModel
    rw [dif_neg hsrc_pos.ne']
    simp only [paretoPowerMarginalOracle, TopKValueOracle.common_expectedTopSum]
    rw [paretoPowerMarginalValue_backward_marginal α hsrc_pos,
      paretoPowerMarginalValue_forward_marginal]
    exact hmarginal

/--
Auxiliary tail-index bridge.

If marginals decay as `q ^ (1/α - 1)`, then the optimal allocation is
approximately γ-homogeneous with γ = `1 - 1/α`.  This is not the paper's
Theorem 2, which is about Bernoulli success probabilities decaying by item rank.
-/
structure TailIndexHomogeneityCertificate
    {T : ℕ} [NeZero T] (M : ConsumptionModel T) (α : ℝ) : Prop where
  alpha_gt_one : 1 < α
  tail_index : HasTypeTailIndex M (1/α)
  likelihood_pos : ∀ t, 0 < M.likelihood t
  asymptotic_homogeneity :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => M) (paretoProfile M.likelihood α) EconCSLib.Math.ExactInvRate

/--
Auxiliary tail-index homogeneity bridge from an explicit certificate.
-/
theorem homogeneity_of_tail_index
    {T : ℕ} [NeZero T] (M : ConsumptionModel T) (α : ℝ)
    (hcert : TailIndexHomogeneityCertificate M α) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => M) (paretoProfile M.likelihood α) EconCSLib.Math.ExactInvRate := hcert.asymptotic_homogeneity

/--
Finite pairwise difference bound for Pareto types.
If marginals are `L * q^(1/α - 1)`, then optimal counts satisfy a power-law balance.
-/
def ParetoOptimumPairwiseBoundTarget
    {T : ℕ} (M : ConsumptionModel T) (index : ℝ) : Prop :=
  ∀ N {a : CountAllocation T},
    M.IsOptimalAtTotal N a →
      ∀ t₁ t₂,
        0 < a.count t₁ → t₁ ≠ t₂ →
        ((a.count t₁ : ℝ) - 1) ^ (index - 1) ≤
          (M.likelihood t₂ / M.likelihood t₁) *
            (a.count t₂ + 1 : ℝ) ^ (index - 1)

/--
Certificate for the finite Pareto pairwise balance target.

The current `HasTailIndex` interface allows type-specific constants and says
nothing about the first marginal at zero, so it is not enough by itself to prove
this bound. Keep the exact pairwise inequality as a named certificate until the
paper's Pareto order-statistic asymptotics are formalized.
-/
structure ParetoOptimumPairwiseBoundCertificate
    {T : ℕ} (M : ConsumptionModel T) (index : ℝ) : Prop where
  tail_index : HasTypeTailIndex M index
  likelihood_pos : ∀ t, 0 < M.likelihood t
  pairwise_bound : ParetoOptimumPairwiseBoundTarget M index

theorem pareto_optimum_pairwise_bound
    {T : ℕ} (M : ConsumptionModel T) (index : ℝ)
    (hcert : ParetoOptimumPairwiseBoundCertificate M index)
    (N : ℕ) {a : CountAllocation T}
    (hopt : M.IsOptimalAtTotal N a) :
    ∀ t₁ t₂,
      0 < a.count t₁ → t₁ ≠ t₂ →
      ((a.count t₁ : ℝ) - 1) ^ (index - 1) ≤
        (M.likelihood t₂ / M.likelihood t₁) * (a.count t₂ + 1 : ℝ) ^ (index - 1) :=  hcert.pairwise_bound N hopt

end PRPKG24AccuracyDiversity
