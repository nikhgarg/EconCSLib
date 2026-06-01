import PRPKG24AccuracyDiversity.SeparableAsymptotic
import EconCSLib.Foundations.Math.PowerComparisons
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

namespace PRPKG24AccuracyDiversity

open Filter Topology
open scoped BigOperators

/--
Marginal decay exponent for the bounded-support branch's power-law oracle.

If the upper-tail density behaves like `(M - x)^(beta - 1)`, the paper's
bounded branch has `h(q + 1) - h(q)` proportional to
`q^-((beta + 1) / beta)`.
-/
noncomputable def boundedMarginalExponent (beta : ℝ) : ℝ :=
  (beta + 1) / beta

theorem boundedMarginalExponent_pos {beta : ℝ} (hbeta_pos : 0 < beta) :
    0 < boundedMarginalExponent beta := by
  unfold boundedMarginalExponent
  exact div_pos (by linarith) hbeta_pos

theorem boundedMarginalExponent_one_div_eq_gamma
    {beta : ℝ} (hbeta_pos : 0 < beta) :
    1 / boundedMarginalExponent beta = beta / (beta + 1) := by
  have hsum_pos : 0 < beta + 1 := by linarith
  unfold boundedMarginalExponent
  field_simp [ne_of_gt hbeta_pos, ne_of_gt hsum_pos]

/--
Exact power-marginal value used as a bounded-support asymptotic checkpoint.

This records the marginal law predicted by Lemma 1 for bounded distributions
with tail exponent `beta`. The remaining source-specific probability work is to
derive this marginal law, or its asymptotic equivalent, from Lemma D.2.
-/
noncomputable def boundedPowerMarginalValue (beta : ℝ) (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range q,
    (((j + 1 : ℕ) : ℝ) ^ (-(boundedMarginalExponent beta)))

/-- Common top-one oracle with exact bounded-branch power-law marginals. -/
noncomputable def boundedPowerMarginalOracle (T : ℕ) (beta : ℝ) :
    TopKValueOracle T :=
  TopKValueOracle.common T (boundedPowerMarginalValue beta)

theorem boundedPowerMarginalValue_zero (beta : ℝ) :
    boundedPowerMarginalValue beta 0 = 0 := by
  simp [boundedPowerMarginalValue]

theorem boundedPowerMarginalValue_forward_marginal
    (beta : ℝ) (q : ℕ) :
    boundedPowerMarginalValue beta (q + 1) -
        boundedPowerMarginalValue beta q =
      (((q + 1 : ℕ) : ℝ) ^ (-(boundedMarginalExponent beta))) := by
  simp [boundedPowerMarginalValue, Finset.sum_range_succ]

/-- Exact scaled marginal used by the bounded power-marginal oracle. -/
noncomputable def boundedPowerMarginalScale (beta : ℝ) (q : ℕ) : ℝ :=
  (((q + 1 : ℕ) : ℝ) ^ (-(boundedMarginalExponent beta)))

theorem boundedPowerMarginalScale_pos (beta : ℝ) (q : ℕ) :
    0 < boundedPowerMarginalScale beta q := by
  unfold boundedPowerMarginalScale
  exact Real.rpow_pos_of_pos (by positivity) _

theorem boundedPowerMarginalScale_one_eq_inv_sq (q : ℕ) :
    boundedPowerMarginalScale 1 q =
      (((q + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) := by
  norm_num [boundedPowerMarginalScale, boundedMarginalExponent]

/--
The exact bounded power-marginal oracle satisfies the reusable scaled-marginal
certificate with unit type weights.
-/
noncomputable def boundedPowerMarginalScaledMarginalLimitCertificate
    (T : ℕ) (beta : ℝ) :
    TopKScaledMarginalLimitCertificate
      (boundedPowerMarginalOracle T beta) 1
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T => (1 : ℝ)) where
  scale_pos_eventually := by
    filter_upwards with q
    exact boundedPowerMarginalScale_pos beta q
  weight_pos := by
    intro t
    norm_num
  marginal_ratio_tendsto := by
    intro t
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards with q
    have hpow_ne :
        (((q : ℝ) + 1) ^ (-(boundedMarginalExponent beta))) ≠ 0 :=
      (Real.rpow_pos_of_pos (by positivity) _).ne'
    simp [EconCSLib.Probability.TopKExpectationOracle.marginalTopK,
      topKExpectationOracleOfTopKValueOracle, boundedPowerMarginalOracle,
      TopKValueOracle.common, boundedPowerMarginalScale,
      boundedPowerMarginalValue_forward_marginal, hpow_ne]

theorem boundedPowerMarginalValue_backward_marginal
    (beta : ℝ) {q : ℕ} (hq : 0 < q) :
    boundedPowerMarginalValue beta q -
        boundedPowerMarginalValue beta (q - 1) =
      ((q : ℝ) ^ (-(boundedMarginalExponent beta))) := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  nth_rewrite 1 [← hpred]
  rw [boundedPowerMarginalValue_forward_marginal]
  simp [hpred]

theorem boundedPowerMarginalValue_forward_marginal_nonneg
    (beta : ℝ) (q : ℕ) :
    0 ≤ boundedPowerMarginalValue beta (q + 1) -
        boundedPowerMarginalValue beta q := by
  rw [boundedPowerMarginalValue_forward_marginal]
  exact Real.rpow_nonneg (by positivity) _

theorem boundedPowerMarginalValue_marginal_antitone_step
    {beta : ℝ} (hbeta_pos : 0 < beta) (q : ℕ) :
    boundedPowerMarginalValue beta (q + 2) -
        boundedPowerMarginalValue beta (q + 1) ≤
      boundedPowerMarginalValue beta (q + 1) -
        boundedPowerMarginalValue beta q := by
  rw [boundedPowerMarginalValue_forward_marginal,
    boundedPowerMarginalValue_forward_marginal]
  have hbase_pos : 0 < ((q + 1 : ℕ) : ℝ) := by positivity
  have hbase_le : ((q + 1 : ℕ) : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.le_succ q)
  have hexp_nonpos : -(boundedMarginalExponent beta) ≤ 0 :=
    neg_nonpos.mpr (le_of_lt (boundedMarginalExponent_pos hbeta_pos))
  exact Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le hexp_nonpos

/--
Generic source-algebra bridge: if finitely many rank terms are each
asymptotic to a nonzero coefficient times a common scale, then their sum is
asymptotic to the sum of those coefficients times the same scale.

This is the finite-sum step used after Lemma D.2 in the bounded branch of
Theorem 1(ii): the analytic work supplies one asymptotic equivalent for each
fixed rank/index term, and this theorem assembles the top-`k` loss.
-/
theorem finite_sum_asymptoticEquivalent_common_scale
    {ι : Type*} [Fintype ι]
    (term : ι → ℕ → ℝ) (coeff : ι → ℝ) (scale : ℕ → ℝ)
    (hcoeff_ne : ∀ i, coeff i ≠ 0)
    (htotal_ne : (∑ i : ι, coeff i) ≠ 0)
    (hscale_ne : ∀ᶠ n in atTop, scale n ≠ 0)
    (hterm :
      ∀ i,
        EconCSLib.Math.AsymptoticEquivalent (term i)
          (fun n => coeff i * scale n)) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun n => ∑ i : ι, term i n)
      (fun n => (∑ i : ι, coeff i) * scale n) := by
  have hterm_scaled :
      ∀ i,
        Tendsto (fun n => term i n / scale n) atTop (nhds (coeff i)) := by
    intro i
    have hmul :
        Tendsto
          (fun n => term i n / (coeff i * scale n) * coeff i)
          atTop (nhds (1 * coeff i)) := by
      simpa [mul_comm] using (hterm i).const_mul (coeff i)
    refine Tendsto.congr' ?_ (by simpa using hmul)
    filter_upwards [hscale_ne] with n hn_scale
    have hi := hcoeff_ne i
    field_simp [hi, hn_scale]
  have hsum_scaled :
      Tendsto
        (fun n => ∑ i : ι, term i n / scale n)
        atTop (nhds (∑ i : ι, coeff i)) := by
    exact tendsto_finset_sum Finset.univ
      (fun i _ => hterm_scaled i)
  have hratio_scaled :
      Tendsto
        (fun n => (∑ i : ι, term i n / scale n) /
          (∑ i : ι, coeff i))
        atTop (nhds 1) := by
    have hdiv := hsum_scaled.div_const (∑ i : ι, coeff i)
    simpa [htotal_ne] using hdiv
  refine Tendsto.congr' ?_ hratio_scaled
  filter_upwards [hscale_ne] with n hn_scale
  have hsum_div :
      (∑ i : ι, term i n / scale n) =
        (∑ i : ι, term i n) / scale n := by
    simp_rw [div_eq_mul_inv]
    rw [Finset.sum_mul]
  rw [hsum_div]
  field_simp [htotal_ne, hn_scale]

/--
If a main term is asymptotic to `coeff * scale` and a remainder is
`o(scale)`, their sum has the same asymptotic equivalent.
-/
theorem asymptoticEquivalent_add_negligible_common_scale
    (main remainder scale : ℕ → ℝ) (coeff : ℝ)
    (hcoeff_ne : coeff ≠ 0)
    (hscale_ne : ∀ᶠ n in atTop, scale n ≠ 0)
    (hmain :
      EconCSLib.Math.AsymptoticEquivalent main
        (fun n => coeff * scale n))
    (hremainder :
      Tendsto (fun n => remainder n / scale n) atTop (nhds 0)) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun n => main n + remainder n)
      (fun n => coeff * scale n) := by
  have hremainder_ratio :
      Tendsto
        (fun n => remainder n / (coeff * scale n))
        atTop (nhds 0) := by
    have hdiv :=
      hremainder.div_const coeff
    refine Tendsto.congr' ?_ (by simpa [hcoeff_ne] using hdiv)
    filter_upwards [hscale_ne] with n hn_scale
    field_simp [hcoeff_ne, hn_scale]
  rw [EconCSLib.Math.AsymptoticEquivalent] at hmain ⊢
  have hsum := hmain.add hremainder_ratio
  refine Tendsto.congr' ?_ (by simpa using hsum)
  filter_upwards [hscale_ne] with n hn_scale
  field_simp [hcoeff_ne, hn_scale]

/-- The bounded branch's common scale, `a^(-1 / beta)`. -/
noncomputable def boundedTailScale (beta : ℝ) (a : ℕ) : ℝ :=
  (a : ℝ) ^ (-(1 / beta))

theorem boundedTailScale_eventually_ne_zero (beta : ℝ) :
    ∀ᶠ a in atTop, boundedTailScale beta a ≠ 0 := by
  filter_upwards [eventually_gt_atTop 0] with a ha
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha
  exact (Real.rpow_pos_of_pos ha_pos (-(1 / beta))).ne'

theorem boundedTailScale_eventually_pos (beta : ℝ) :
    ∀ᶠ a in atTop, 0 < boundedTailScale beta a := by
  filter_upwards [eventually_gt_atTop 0] with a ha
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha
  exact Real.rpow_pos_of_pos ha_pos (-(1 / beta))

theorem boundedTailScale_tendsto_zero
    {beta : ℝ} (hbeta_pos : 0 < beta) :
    Tendsto (boundedTailScale beta) atTop (nhds 0) := by
  have hexp_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
  change Tendsto (fun a : ℕ => ((a : ℝ) ^ (-(1 / beta)))) atTop (nhds 0)
  simpa [one_div] using
    (tendsto_rpow_neg_atTop hexp_pos).comp
      tendsto_natCast_atTop_atTop

theorem boundedTailScale_div_succ_ratio_eventually_eq_rpow
    {beta : ℝ} (hbeta_pos : 0 < beta) :
    ∀ᶠ q in atTop,
      (boundedTailScale beta q / (((q + 1 : ℕ) : ℝ))) /
          boundedPowerMarginalScale beta q =
        ((((q + 1 : ℕ) : ℝ) / (q : ℝ)) ^ (1 / beta)) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq_pos_nat
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq_pos_nat
  have hq_nonneg : 0 ≤ (q : ℝ) := hq_pos.le
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hsucc_pos : 0 < (((q + 1 : ℕ) : ℝ)) := by positivity
  have hsucc_nonneg : 0 ≤ (((q + 1 : ℕ) : ℝ)) := hsucc_pos.le
  have hsucc_ne : (((q + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hsucc_pos
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hq_pow_ne : (q : ℝ) ^ (1 / beta) ≠ 0 :=
    (Real.rpow_pos_of_pos hq_pos (1 / beta)).ne'
  have hsucc_pow_ne : (((q + 1 : ℕ) : ℝ)) ^ (1 / beta) ≠ 0 :=
    (Real.rpow_pos_of_pos hsucc_pos (1 / beta)).ne'
  have heta :
      boundedMarginalExponent beta = 1 + 1 / beta := by
    unfold boundedMarginalExponent
    field_simp [hbeta_ne]
  rw [boundedTailScale, boundedPowerMarginalScale, heta,
    Real.rpow_neg hq_nonneg (1 / beta),
    Real.rpow_neg hsucc_nonneg (1 + 1 / beta),
    Real.rpow_add hsucc_pos 1 (1 / beta),
    Real.rpow_one,
    Real.div_rpow hsucc_nonneg hq_nonneg (1 / beta)]
  field_simp [hq_ne, hsucc_ne, hq_pow_ne, hsucc_pow_ne]

theorem boundedTailScale_div_succ_ratio_tendsto_one
    {beta : ℝ} (hbeta_pos : 0 < beta) :
    Tendsto
      (fun q : ℕ =>
        (boundedTailScale beta q / (((q + 1 : ℕ) : ℝ))) /
          boundedPowerMarginalScale beta q)
      atTop (nhds 1) := by
  have hratio :
      Tendsto
        (fun q : ℕ => (((q + 1 : ℕ) : ℝ) / (q : ℝ)))
        atTop (nhds 1) := by
    have h :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ)
        (by norm_num : (1 : ℝ) ≠ 0)
    convert h using 1
    · ext q
      rw [Nat.cast_add, Nat.cast_one]
      ring
    · norm_num
  have hrpow :
      Tendsto
        (fun q : ℕ =>
          ((((q + 1 : ℕ) : ℝ) / (q : ℝ)) ^ (1 / beta)))
        atTop (nhds 1) := by
    have h :=
      hratio.rpow_const (p := 1 / beta)
        (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
    simpa using h
  refine Tendsto.congr' ?_ hrpow
  filter_upwards
    [boundedTailScale_div_succ_ratio_eventually_eq_rpow hbeta_pos] with q hq
  exact hq.symm

/--
Finite-difference bridge from a bounded-source loss asymptotic to a forward
marginal asymptotic.

The discrete-drop hypothesis is deliberately explicit: the loss asymptotic
`A - h q ~ C q^(-1 / beta)` alone does not control first differences.
-/
theorem bounded_source_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop
    {h : ℕ → ℝ} {A C beta : ℝ}
    (hbeta_pos : 0 < beta) (hC_pos : 0 < C)
    (hloss :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q => A - h q)
        (fun q => C * boundedTailScale beta q))
    (hdrop :
      Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            (((A - h q) - (A - h (q + 1))) / (A - h q))))
        atTop (nhds (1 / beta))) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun q => h (q + 1) - h q)
      (fun q => (C / beta) * boundedPowerMarginalScale beta q) := by
  rw [EconCSLib.Math.AsymptoticEquivalent] at hloss ⊢
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  have hcoeff_ne : C / beta ≠ 0 := div_ne_zero hC_ne hbeta_ne
  have hdrop_forward :
      Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((h (q + 1) - h q) / (A - h q))))
        atTop (nhds (1 / beta)) := by
    refine Tendsto.congr' ?_ hdrop
    filter_upwards with q
    ring
  have hdrop_unit :
      Tendsto
        (fun q : ℕ =>
          beta *
            (((q + 1 : ℕ) : ℝ) *
              ((h (q + 1) - h q) / (A - h q))))
        atTop (nhds 1) := by
    have h := hdrop_forward.const_mul beta
    have hlim : beta * beta⁻¹ = 1 := by
      field_simp [hbeta_ne]
    simpa [one_div, hlim] using h
  have hscale := boundedTailScale_div_succ_ratio_tendsto_one hbeta_pos
  have hprod :
      Tendsto
        (fun q : ℕ =>
          (beta *
              (((q + 1 : ℕ) : ℝ) *
                ((h (q + 1) - h q) / (A - h q)))) *
            ((A - h q) / (C * boundedTailScale beta q)) *
            ((boundedTailScale beta q / (((q + 1 : ℕ) : ℝ))) /
              boundedPowerMarginalScale beta q))
        atTop (nhds 1) := by
    simpa using (hdrop_unit.mul hloss).mul hscale
  have hloss_ne_eventually :
      ∀ᶠ q in atTop, A - h q ≠ 0 := by
    filter_upwards [hloss.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with q hratio_ne
    intro hloss_zero
    rw [hloss_zero] at hratio_ne
    simp at hratio_ne
  refine Tendsto.congr' ?_ hprod
  filter_upwards
    [hloss_ne_eventually,
      boundedTailScale_eventually_ne_zero beta] with q hloss_ne htail_ne
  have hsucc_ne : (((q + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hpower_ne : boundedPowerMarginalScale beta q ≠ 0 :=
    (boundedPowerMarginalScale_pos beta q).ne'
  field_simp [hloss_ne, htail_ne, hsucc_ne, hpower_ne, hC_ne, hbeta_ne,
    hcoeff_ne]

/--
Source-side bounded order-statistic marginal certificate.

This is the bounded analogue of the Pareto source certificate: prove the
top-`k` order-statistic marginal asymptotic once, then convert it to the
shared scaled-marginal interface consumed by the optimization layer.
-/
structure BoundedOrderStatisticScaledMarginalCertificate
    (μ : ℕ → ℕ → ℝ) (k : ℕ) (beta limitCoeff : ℝ) : Prop where
  beta_pos : 0 < beta
  k_pos : 0 < k
  coeff_pos : 0 < limitCoeff
  marginal_ratio_tendsto :
    Filter.Tendsto
      (fun q : ℕ =>
        (orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q) /
          (boundedPowerMarginalScale beta q * limitCoeff))
      Filter.atTop (nhds 1)

namespace BoundedOrderStatisticScaledMarginalCertificate

theorem marginal_asymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {beta limitCoeff : ℝ}
    (C : BoundedOrderStatisticScaledMarginalCertificate μ k beta limitCoeff) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun q : ℕ =>
        orderStatisticTopKSumFromMean μ k (q + 1) -
          orderStatisticTopKSumFromMean μ k q)
      (fun q : ℕ => boundedPowerMarginalScale beta q * limitCoeff) :=
  C.marginal_ratio_tendsto

def ofMarginalAsymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {beta limitCoeff : ℝ}
    (hbeta : 0 < beta) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => boundedPowerMarginalScale beta q * limitCoeff)) :
    BoundedOrderStatisticScaledMarginalCertificate μ k beta limitCoeff where
  beta_pos := hbeta
  k_pos := hk
  coeff_pos := hcoeff
  marginal_ratio_tendsto := hmargin

def ofConstMulScaleAsymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {beta limitCoeff : ℝ}
    (hbeta : 0 < beta) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => limitCoeff * boundedPowerMarginalScale beta q)) :
    BoundedOrderStatisticScaledMarginalCertificate μ k beta limitCoeff :=
  ofMarginalAsymptoticEquivalent hbeta hk hcoeff <| by
    rw [EconCSLib.Math.AsymptoticEquivalent] at hmargin ⊢
    refine Filter.Tendsto.congr' ?_ hmargin
    filter_upwards with q
    rw [mul_comm]

def ofLossAsymptoticAndScaledDrop
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {A C beta : ℝ}
    (hbeta : 0 < beta) (hk : 0 < k) (hC : 0 < C)
    (hloss :
      EconCSLib.Math.AsymptoticEquivalent
        (fun q : ℕ => A - orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => C * boundedTailScale beta q))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            (((A - orderStatisticTopKSumFromMean μ k q) -
              (A - orderStatisticTopKSumFromMean μ k (q + 1))) /
              (A - orderStatisticTopKSumFromMean μ k q))))
        Filter.atTop (nhds (1 / beta))) :
    BoundedOrderStatisticScaledMarginalCertificate μ k beta (C / beta) :=
  ofConstMulScaleAsymptoticEquivalent hbeta hk (div_pos hC hbeta) <|
    bounded_source_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop
      hbeta hC hloss hdrop

noncomputable def toTopKScaledMarginalLimitCertificate
    {T : ℕ} {μ : ℕ → ℕ → ℝ} {k : ℕ} {beta limitCoeff : ℝ}
    (C : BoundedOrderStatisticScaledMarginalCertificate μ k beta limitCoeff) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T μ) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T => limitCoeff) where
  scale_pos_eventually := by
    filter_upwards with q
    exact boundedPowerMarginalScale_pos beta q
  weight_pos := by
    intro _t
    exact C.coeff_pos
  marginal_ratio_tendsto := by
    intro t
    simpa [EconCSLib.Probability.TopKExpectationOracle.marginalTopK,
      topKExpectationOracleOfTopKValueOracle] using C.marginal_ratio_tendsto

end BoundedOrderStatisticScaledMarginalCertificate

/-- The paper's rescaled split threshold `delta / a^(-1/beta)` diverges. -/
theorem boundedTailScale_delta_div_tendsto_atTop
    {beta delta : ℝ} (hbeta_pos : 0 < beta) (hdelta_pos : 0 < delta) :
    Tendsto (fun a : ℕ => delta / boundedTailScale beta a) atTop atTop := by
  have hscale_nhdsGT :
      Tendsto (boundedTailScale beta) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (boundedTailScale beta)
      (boundedTailScale_tendsto_zero hbeta_pos) ?_
    exact boundedTailScale_eventually_pos beta
  have hinv :
      Tendsto (fun a : ℕ => (boundedTailScale beta a)⁻¹) atTop atTop :=
    hscale_nhdsGT.inv_tendsto_nhdsGT_zero
  simpa [div_eq_mul_inv] using
    (tendsto_const_mul_atTop_of_pos hdelta_pos).mpr hinv

theorem boundedTailScale_const_mul_tendsto_zero
    {beta y : ℝ} (hbeta_pos : 0 < beta) :
    Tendsto (fun a => y * boundedTailScale beta a) atTop (nhds 0) := by
  simpa using (boundedTailScale_tendsto_zero hbeta_pos).const_mul y

/--
Any fixed real-power polynomial factor is killed by a geometric term along
natural-number indices.
-/
theorem bounded_rpow_mul_geometric_tendsto_zero
    (s : ℝ) {rho : ℝ} (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1) :
    Tendsto (fun a : ℕ => (a : ℝ) ^ s * rho ^ a)
      atTop (nhds 0) := by
  have hlog_neg : Real.log rho < 0 := Real.log_neg hrho_pos hrho_lt_one
  have hreal :
      Tendsto (fun x : ℝ => x ^ s * Real.exp (Real.log rho * x))
        atTop (nhds 0) := by
    simpa [neg_mul, neg_neg, mul_comm, mul_left_comm, mul_assoc] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        s (-Real.log rho) (neg_pos.mpr hlog_neg)
  refine Tendsto.congr' ?_ (hreal.comp tendsto_natCast_atTop_atTop)
  filter_upwards with a
  have hexp :
      Real.exp (Real.log rho * (a : ℝ)) = rho ^ a := by
    calc
      Real.exp (Real.log rho * (a : ℝ))
        = Real.exp ((a : ℝ) * Real.log rho) := by rw [mul_comm]
      _ = (Real.exp (Real.log rho)) ^ a := Real.exp_nat_mul (Real.log rho) a
      _ = rho ^ a := by rw [Real.exp_log hrho_pos]
  change (a : ℝ) ^ s * Real.exp (Real.log rho * (a : ℝ)) =
    (a : ℝ) ^ s * rho ^ a
  rw [hexp]

/--
A geometric tail beats the bounded-branch scale `a^(-1 / beta)`, even after a
fixed polynomial factor.
-/
theorem boundedTailScale_polynomial_geometric_ratio_tendsto_zero
    {beta rho : ℝ} (hbeta_pos : 0 < beta)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (degree : ℕ) (C : ℝ) :
    Tendsto
      (fun a : ℕ =>
        C * ((a : ℝ) ^ degree * rho ^ a) / boundedTailScale beta a)
      atTop (nhds 0) := by
  have hbase :
      Tendsto
        (fun a : ℕ =>
          C * ((a : ℝ) ^ ((degree : ℝ) + 1 / beta) * rho ^ a))
        atTop (nhds 0) := by
    simpa [mul_assoc] using
      (bounded_rpow_mul_geometric_tendsto_zero
        ((degree : ℝ) + 1 / beta) hrho_pos hrho_lt_one).const_mul C
  refine Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop 0] with a ha
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha
  have ha_nonneg : 0 ≤ (a : ℝ) := le_of_lt ha_pos
  rw [boundedTailScale, ← Real.rpow_natCast]
  rw [Real.rpow_neg ha_nonneg]
  have hxpow_ne : (a : ℝ) ^ (1 / beta) ≠ 0 :=
    (Real.rpow_pos_of_pos ha_pos (1 / beta)).ne'
  field_simp [hxpow_ne]
  have hexp_eq :
      ((degree : ℝ) * beta + 1) / beta =
        (degree : ℝ) + 1 / beta := by
    field_simp [ne_of_gt hbeta_pos]
  rw [← Real.rpow_natCast]
  rw [hexp_eq, Real.rpow_add ha_pos]
  ring

theorem boundedTailScale_rpow_beta
    {beta : ℝ} (hbeta_pos : 0 < beta) {a : ℕ} (ha : 0 < a) :
    (boundedTailScale beta a) ^ beta = (a : ℝ) ^ (-1 : ℝ) := by
  have ha_nonneg : 0 ≤ (a : ℝ) := by positivity
  have hexp : -(1 / beta) * beta = (-1 : ℝ) := by
    field_simp [ne_of_gt hbeta_pos]
  rw [boundedTailScale, ← Real.rpow_mul ha_nonneg, hexp]

theorem boundedTailScale_rescaled_rpow_beta
    {beta y : ℝ} (hbeta_pos : 0 < beta) (hy_pos : 0 < y)
    {a : ℕ} (ha : 0 < a) :
    (y * boundedTailScale beta a) ^ beta =
      y ^ beta * (a : ℝ) ^ (-1 : ℝ) := by
  have hscale_pos : 0 < boundedTailScale beta a := by
    have ha_real_pos : 0 < (a : ℝ) := by exact_mod_cast ha
    exact Real.rpow_pos_of_pos ha_real_pos (-(1 / beta))
  rw [Real.mul_rpow hy_pos.le hscale_pos.le,
    boundedTailScale_rpow_beta hbeta_pos ha]

/--
Local CDF power bounds keep their expected `1/a` form after the bounded
Lemma D.2 substitution `x = y*a^(-1/beta)`.
-/
theorem boundedLemmaD2_eventually_rescaled_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta A B delta : ℝ}
    (hbeta_pos : 0 < beta)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :
    ∀ᶠ a in atTop,
      ∀ {y : ℝ}, 0 < y →
        y < delta / boundedTailScale beta a →
          A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) ≤
              G (y * boundedTailScale beta a) ∧
            G (y * boundedTailScale beta a) ≤
              B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) := by
  filter_upwards
    [eventually_gt_atTop (0 : ℕ), boundedTailScale_eventually_pos beta] with
      a ha hscale_pos y hy_pos hy_lt
  have hx_pos : 0 < y * boundedTailScale beta a :=
    mul_pos hy_pos hscale_pos
  have hx_lt_delta : y * boundedTailScale beta a < delta := by
    exact (lt_div_iff₀ hscale_pos).mp hy_lt
  have hpow :
      (y * boundedTailScale beta a) ^ beta =
        y ^ beta * (a : ℝ) ^ (-1 : ℝ) :=
    boundedTailScale_rescaled_rpow_beta hbeta_pos hy_pos ha
  constructor
  · simpa [hpow] using
      hG_lower (y * boundedTailScale beta a) hx_pos hx_lt_delta
  · simpa [hpow] using
      hG_upper (y * boundedTailScale beta a) hx_pos hx_lt_delta

/-- Gamma-shaped local envelope for bounded Lemma D.2's growing-window kernel. -/
noncomputable def boundedLemmaD2LocalEnvelope
    (beta A B : ℝ) (j : ℕ) (y : ℝ) : ℝ :=
  B ^ j * (y ^ (beta * (j : ℝ)) *
    Real.exp (-(A / 2) * y ^ beta))

/-- The local Lemma D.2 envelope is nonnegative on `(0,∞)` when `B ≥ 0`. -/
theorem boundedLemmaD2LocalEnvelope_nonneg
    {beta A B y : ℝ} {j : ℕ}
    (hB_nonneg : 0 ≤ B) (hy_nonneg : 0 ≤ y) :
    0 ≤ boundedLemmaD2LocalEnvelope beta A B j y := by
  unfold boundedLemmaD2LocalEnvelope
  exact mul_nonneg (pow_nonneg hB_nonneg j)
    (mul_nonneg (Real.rpow_nonneg hy_nonneg _)
      (Real.exp_nonneg _))

/--
Scalar envelope bound for the fixed-rank binomial kernel once the rescaled CDF
is trapped between local power bounds. This is the pointwise algebra behind
the bounded Lemma D.2 dominated-kernel certificate.
-/
theorem boundedLemmaD2_binomial_kernel_norm_le_power_exp_of_rescaled_bounds
    {beta A B y g : ℝ} {j a : ℕ}
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hy_pos : 0 < y) (ha_pos_nat : 0 < a)
    (hlarge : 2 * j ≤ a)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1)
    (hg_lower : A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) ≤ g)
    (hg_upper : g ≤ B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) :
    ‖(Nat.choose a j : ℝ) * g ^ j * (1 - g) ^ (a - j)‖ ≤
      B ^ j * y ^ (beta * (j : ℝ)) *
        Real.exp (-(A / 2) * y ^ beta) := by
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha_pos_nat
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha_pos
  have hybeta_pos : 0 < y ^ beta := Real.rpow_pos_of_pos hy_pos beta
  have hybeta_nonneg : 0 ≤ y ^ beta := le_of_lt hybeta_pos
  have hchoose_nonneg : 0 ≤ (Nat.choose a j : ℝ) := by positivity
  have htail_nonneg : 0 ≤ 1 - g := sub_nonneg.mpr hg_le_one
  have hkernel_nonneg :
      0 ≤ (Nat.choose a j : ℝ) * g ^ j * (1 - g) ^ (a - j) :=
    mul_nonneg
      (mul_nonneg hchoose_nonneg (pow_nonneg hg_nonneg j))
      (pow_nonneg htail_nonneg (a - j))
  rw [Real.norm_of_nonneg hkernel_nonneg]
  have hupper_nonneg :
      0 ≤ B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) :=
    hg_nonneg.trans hg_upper
  have hgpow_le :
      g ^ j ≤ (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) ^ j :=
    pow_le_pow_left₀ hg_nonneg hg_upper j
  have hchoose_le : (Nat.choose a j : ℝ) ≤ (a : ℝ) ^ j := by
    exact_mod_cast Nat.choose_le_pow a j
  have hfront_le_raw :
      (Nat.choose a j : ℝ) * g ^ j ≤
        (a : ℝ) ^ j *
          (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) ^ j :=
    mul_le_mul hchoose_le hgpow_le (pow_nonneg hg_nonneg j)
      (pow_nonneg ha_pos.le j)
  have hfront_eq :
      (a : ℝ) ^ j *
          (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) ^ j =
        B ^ j * y ^ (beta * (j : ℝ)) := by
    have hcancel :
        (a : ℝ) *
            (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) =
          B * y ^ beta := by
      rw [Real.rpow_neg_one]
      field_simp [ha_ne]
    have hy_pow :
        (y ^ beta) ^ j = y ^ (beta * (j : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy_pos.le]
    calc
      (a : ℝ) ^ j *
          (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) ^ j
          = ((a : ℝ) *
              (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)))) ^ j := by
            rw [← mul_pow]
      _ = (B * y ^ beta) ^ j := by rw [hcancel]
      _ = B ^ j * (y ^ beta) ^ j := by rw [mul_pow]
      _ = B ^ j * y ^ (beta * (j : ℝ)) := by
            rw [hy_pow]
  have hfront_le :
      (Nat.choose a j : ℝ) * g ^ j ≤
        B ^ j * y ^ (beta * (j : ℝ)) := by
    simpa [hfront_eq] using hfront_le_raw
  have hfront_bound_nonneg :
      0 ≤ B ^ j * y ^ (beta * (j : ℝ)) :=
    mul_nonneg (pow_nonneg hB_nonneg j)
      (le_of_lt (Real.rpow_pos_of_pos hy_pos (beta * (j : ℝ))))
  have hbase_le_exp :
      1 - g ≤ Real.exp (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)))) := by
    calc
      1 - g ≤ 1 - A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) := by
        exact sub_le_sub_left hg_lower 1
      _ ≤ Real.exp (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)))) :=
        Real.one_sub_le_exp_neg
          (A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)))
  have htail_le_raw :
      (1 - g) ^ (a - j) ≤
        (Real.exp (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))))) ^ (a - j) :=
    pow_le_pow_left₀ htail_nonneg hbase_le_exp (a - j)
  have hja : j ≤ a := by omega
  have hsub_ge_half : (1 / 2 : ℝ) ≤ ((a - j : ℕ) : ℝ) / (a : ℝ) := by
    rw [le_div_iff₀ ha_pos]
    rw [Nat.cast_sub hja]
    have hlarge_real : (2 * (j : ℝ)) ≤ (a : ℝ) := by
      exact_mod_cast hlarge
    nlinarith
  have hK_nonneg : 0 ≤ A * y ^ beta :=
    mul_nonneg hA_pos.le hybeta_nonneg
  have harg_le :
      ((a - j : ℕ) : ℝ) *
          (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)))) ≤
        -(A / 2) * y ^ beta := by
    have hleft_eq :
        ((a - j : ℕ) : ℝ) *
            (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)))) =
          -(A * y ^ beta) * (((a - j : ℕ) : ℝ) / (a : ℝ)) := by
      rw [Real.rpow_neg_one]
      field_simp [ha_ne]
    have hright_eq :
        -(A / 2) * y ^ beta = -(A * y ^ beta) * (1 / 2) := by
      ring
    rw [hleft_eq, hright_eq]
    exact mul_le_mul_of_nonpos_left hsub_ge_half (neg_nonpos.mpr hK_nonneg)
  have htail_le :
      (1 - g) ^ (a - j) ≤ Real.exp (-(A / 2) * y ^ beta) := by
    calc
      (1 - g) ^ (a - j)
          ≤ (Real.exp (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))))) ^ (a - j) :=
            htail_le_raw
      _ = Real.exp
          (((a - j : ℕ) : ℝ) *
            (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))))) := by
            rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (-(A / 2) * y ^ beta) :=
            Real.exp_le_exp.mpr harg_le
  calc
    (Nat.choose a j : ℝ) * g ^ j * (1 - g) ^ (a - j)
        ≤ (B ^ j * y ^ (beta * (j : ℝ))) *
            Real.exp (-(A / 2) * y ^ beta) :=
      mul_le_mul hfront_le htail_le
        (pow_nonneg htail_nonneg (a - j)) hfront_bound_nonneg
    _ = B ^ j * y ^ (beta * (j : ℝ)) *
          Real.exp (-(A / 2) * y ^ beta) := by ring

/--
The gamma-shaped envelope used in bounded Lemma D.2 is integrable on
`(0,∞)` for any positive power exponent.
-/
theorem integrableOn_rpow_mul_exp_neg_mul_rpow_of_pos
    {p q b : ℝ} (hp : 0 < p) (hq : -1 < q) (hb : 0 < b) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ q * Real.exp (-b * x ^ p))
      (Set.Ioi (0 : ℝ)) := by
  let s : ℝ := (q + 1) / p
  have hs_pos : 0 < s := by
    exact div_pos (by linarith) hp
  have hgamma :
      MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (-u) * u ^ (s - 1))
        (Set.Ioi (0 : ℝ)) :=
    Real.GammaIntegral_convergent hs_pos
  have hgamma0 :
      MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (-u) * u ^ (s - 1))
        (Set.Ioi (b * 0)) := by
    simpa using hgamma
  have hscaled_raw :
      MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (-(b * u)) * (b * u) ^ (s - 1))
        (Set.Ioi (0 : ℝ)) := by
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
        (fun u : ℝ => Real.exp (-u) * u ^ (s - 1))
        (0 : ℝ) hb).mpr hgamma0
  have hbpow_ne : b ^ (s - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hb (s - 1)).ne'
  have hscaled :
      MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (-b * u) * u ^ (s - 1))
        (Set.Ioi (0 : ℝ)) := by
    have hscaled_const :
        MeasureTheory.IntegrableOn
          (fun u : ℝ =>
            (b ^ (s - 1))⁻¹ *
              (Real.exp (-(b * u)) * (b * u) ^ (s - 1)))
          (Set.Ioi (0 : ℝ)) :=
      hscaled_raw.const_mul (b ^ (s - 1))⁻¹
    refine hscaled_const.congr_fun ?_ measurableSet_Ioi
    intro u hu
    have hu_nonneg : 0 ≤ u := le_of_lt hu
    dsimp
    rw [Real.mul_rpow hb.le hu_nonneg]
    field_simp [hbpow_ne]
  have hcomp :
      MeasureTheory.IntegrableOn
        (fun x : ℝ =>
          x ^ (p - 1) •
            ((fun u : ℝ => Real.exp (-b * u) * u ^ (s - 1)) (x ^ p)))
        (Set.Ioi (0 : ℝ)) := by
    exact
      (MeasureTheory.integrableOn_Ioi_comp_rpow_iff'
        (fun u : ℝ => Real.exp (-b * u) * u ^ (s - 1))
        (ne_of_gt hp)).mpr hscaled
  refine hcomp.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have hx_pos : 0 < x := hx
  have hpow :
      (x ^ p) ^ (s - 1) = x ^ (q + 1 - p) := by
    rw [← Real.rpow_mul hx_nonneg]
    congr 1
    dsimp [s]
    field_simp [ne_of_gt hp]
  simp only [smul_eq_mul, hpow]
  have hmul_pow :
      x ^ (p - 1) * x ^ (q + 1 - p) = x ^ q := by
    rw [← Real.rpow_add hx_pos]
    congr 1
    ring
  calc
    x ^ (p - 1) * (Real.exp (-b * x ^ p) * x ^ (q + 1 - p))
        = (x ^ (p - 1) * x ^ (q + 1 - p)) *
            Real.exp (-b * x ^ p) := by ring
    _ = x ^ q * Real.exp (-b * x ^ p) := by rw [hmul_pow]

/-- Integrability of the bounded Lemma D.2 local envelope on `(0,∞)`. -/
theorem boundedLemmaD2LocalEnvelope_integrable
    {beta A B : ℝ} (hbeta_pos : 0 < beta) (hA_pos : 0 < A)
    (j : ℕ) :
    MeasureTheory.Integrable
      (boundedLemmaD2LocalEnvelope beta A B j)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hq : -1 < beta * (j : ℝ) := by
    have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
    have hmul_nonneg : 0 ≤ beta * (j : ℝ) :=
      mul_nonneg hbeta_pos.le hj_nonneg
    linarith
  have hb : 0 < A / 2 := by positivity
  have hbase :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow_of_pos
      (p := beta) (q := beta * (j : ℝ)) (b := A / 2)
      hbeta_pos hq hb).integrable
  have hconst :
      MeasureTheory.Integrable
        (fun x : ℝ =>
          B ^ j *
            (x ^ (beta * (j : ℝ)) *
              Real.exp (-(A / 2) * x ^ beta)))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hbase.const_mul (B ^ j)
  refine hconst.congr (Filter.Eventually.of_forall ?_)
  intro x
  unfold boundedLemmaD2LocalEnvelope
  congr 3

theorem bounded_one_sub_div_pow_tendsto_exp (z : ℝ) :
    Tendsto
      (fun a : ℕ => (1 - z / (a : ℝ)) ^ a)
      atTop (nhds (Real.exp (-z))) := by
  simpa [sub_eq_add_neg, neg_div] using
    Real.tendsto_one_add_div_pow_exp (-z)

/--
Fixed-rank version of the preceding exponential limit.

Lemma D.2 keeps `j` fixed while the exponent is `a - j`; this verifies that
removing finitely many factors does not change the `exp(-z)` limit.
-/
theorem bounded_one_sub_div_pow_sub_tendsto_exp (z : ℝ) (j : ℕ) :
    Tendsto
      (fun a : ℕ => (1 - z / (a : ℝ)) ^ (a - j))
      atTop (nhds (Real.exp (-z))) := by
  have hbase :
      Tendsto (fun a : ℕ => 1 - z / (a : ℝ)) atTop (nhds 1) := by
    simpa using
      tendsto_const_nhds.sub
        (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) z)
  have hdenom :
      Tendsto (fun a : ℕ => (1 - z / (a : ℝ)) ^ j)
        atTop (nhds 1) := by
    simpa using hbase.pow j
  have hquot :
      Tendsto
        (fun a : ℕ =>
          (1 - z / (a : ℝ)) ^ a / (1 - z / (a : ℝ)) ^ j)
        atTop (nhds (Real.exp (-z))) := by
    have h :=
      (bounded_one_sub_div_pow_tendsto_exp z).div hdenom
        (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  refine Tendsto.congr' ?_ hquot
  filter_upwards
    [eventually_ge_atTop j,
      hbase.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with a ha_ge hbase_ne
  let b : ℝ := 1 - z / (a : ℝ)
  have hb_ne : b ≠ 0 := hbase_ne
  have hpow_ne : b ^ j ≠ 0 := pow_ne_zero j hb_ne
  have hpow_add : b ^ (a - j) * b ^ j = b ^ a := by
    rw [← pow_add, Nat.sub_add_cancel ha_ge]
  change b ^ a / b ^ j =
    b ^ (a - j)
  rw [← hpow_add, mul_div_cancel_right₀ _ hpow_ne]

/--
General exponential kernel limit: if `a * u a -> z`, then
`(1 - u a)^a -> exp(-z)`.
-/
theorem bounded_one_sub_of_nat_mul_tendsto_pow_tendsto_exp
    {u : ℕ → ℝ} {z : ℝ}
    (hu : Tendsto (fun a : ℕ => (a : ℝ) * u a) atTop (nhds z)) :
    Tendsto
      (fun a : ℕ => (1 - u a) ^ a)
      atTop (nhds (Real.exp (-z))) := by
  have hneg :
      Tendsto (fun a : ℕ => (a : ℝ) * (-(u a))) atTop (nhds (-z)) := by
    simpa [mul_neg] using hu.neg
  simpa [sub_eq_add_neg] using
    Real.tendsto_one_add_pow_exp_of_tendsto hneg

/--
Fixed-rank version of the general exponential kernel limit. This is the
analytic shape of the Lemma D.2 factor `(1 - G(x))^(a-j)`.
-/
theorem bounded_one_sub_of_nat_mul_tendsto_pow_sub_tendsto_exp
    {u : ℕ → ℝ} {z : ℝ}
    (hu : Tendsto (fun a : ℕ => (a : ℝ) * u a) atTop (nhds z))
    (j : ℕ) :
    Tendsto
      (fun a : ℕ => (1 - u a) ^ (a - j))
      atTop (nhds (Real.exp (-z))) := by
  have hu_zero : Tendsto u atTop (nhds 0) := by
    have hdiv :
        Tendsto
          (fun a : ℕ => ((a : ℝ) * u a) / (a : ℝ))
          atTop (nhds 0) :=
      hu.div_atTop tendsto_natCast_atTop_atTop
    refine Tendsto.congr' ?_ hdiv
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with a ha
    have ha_ne : (a : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt ha)
    field_simp [ha_ne]
  have hbase : Tendsto (fun a : ℕ => 1 - u a) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hu_zero
  have hdenom :
      Tendsto (fun a : ℕ => (1 - u a) ^ j) atTop (nhds 1) := by
    simpa using hbase.pow j
  have hquot :
      Tendsto
        (fun a : ℕ => (1 - u a) ^ a / (1 - u a) ^ j)
        atTop (nhds (Real.exp (-z))) := by
    have h :=
      (bounded_one_sub_of_nat_mul_tendsto_pow_tendsto_exp hu).div hdenom
        (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  refine Tendsto.congr' ?_ hquot
  filter_upwards
    [eventually_ge_atTop j,
      hbase.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with a ha_ge hbase_ne
  let b : ℝ := 1 - u a
  have hb_ne : b ≠ 0 := hbase_ne
  have hpow_ne : b ^ j ≠ 0 := pow_ne_zero j hb_ne
  have hpow_add : b ^ (a - j) * b ^ j = b ^ a := by
    rw [← pow_add, Nat.sub_add_cancel ha_ge]
  change b ^ a / b ^ j =
    b ^ (a - j)
  rw [← hpow_add, mul_div_cancel_right₀ _ hpow_ne]

/--
Near-zero CDF power-law sandwich used in Lemma D.2.

For the reflected CDF `G`, the source proof derives this from the density
asymptotic `g(x) ~ c*x^(β-1)` by integrating near zero.
-/
structure BoundedTailCDFPowerSandwich
    (G : ℝ → ℝ) (beta c : ℝ) where
  beta_pos : 0 < beta
  c_pos : 0 < c
  cdf_power_sandwich :
    ∀ {ε : ℝ}, 0 < ε →
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        (1 - ε) * (c / beta) * x ^ beta ≤ G x ∧
          G x ≤ (1 + ε) * (c / beta) * x ^ beta

namespace BoundedTailCDFPowerSandwich

/--
Build the bounded-tail CDF sandwich when the reflected CDF is eventually
exactly the limiting power law near zero.
-/
theorem of_eventually_eq_const_mul_power
    {G : ℝ → ℝ} {beta c : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hG :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        G x = (c / beta) * x ^ beta) :
    BoundedTailCDFPowerSandwich G beta c where
  beta_pos := hbeta_pos
  c_pos := hc_pos
  cdf_power_sandwich := by
    intro ε hε
    filter_upwards [hG, self_mem_nhdsWithin] with x hx_eq hx_pos
    have hcoeff_nonneg : 0 ≤ c / beta :=
      (div_pos hc_pos hbeta_pos).le
    have hxpow_nonneg : 0 ≤ x ^ beta :=
      Real.rpow_nonneg (le_of_lt hx_pos) beta
    have hmain_nonneg : 0 ≤ (c / beta) * x ^ beta :=
      mul_nonneg hcoeff_nonneg hxpow_nonneg
    have hleft : 1 - ε ≤ (1 : ℝ) := by linarith
    have hright : (1 : ℝ) ≤ 1 + ε := by linarith
    constructor
    · rw [hx_eq]
      calc
        (1 - ε) * (c / beta) * x ^ beta
            = (1 - ε) * ((c / beta) * x ^ beta) := by ring
        _ ≤ 1 * ((c / beta) * x ^ beta) :=
            mul_le_mul_of_nonneg_right hleft hmain_nonneg
        _ = (c / beta) * x ^ beta := by ring
    · rw [hx_eq]
      calc
        (c / beta) * x ^ beta
            = 1 * ((c / beta) * x ^ beta) := by ring
        _ ≤ (1 + ε) * ((c / beta) * x ^ beta) :=
            mul_le_mul_of_nonneg_right hright hmain_nonneg
        _ = (1 + ε) * (c / beta) * x ^ beta := by ring

/-- The identity reflected CDF has the bounded-tail sandwich with `β = c = 1`. -/
theorem identity_beta_one :
    BoundedTailCDFPowerSandwich (fun x : ℝ => x) 1 1 := by
  refine of_eventually_eq_const_mul_power (by norm_num) (by norm_num) ?_
  filter_upwards with x
  norm_num

/--
The asymptotic CDF sandwich supplies concrete local power bounds on a
right-neighborhood of zero. This is the integrated CDF form of the paper's
bounded-density assumption.
-/
theorem exists_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c) :
    ∃ delta A B : ℝ,
      0 < delta ∧ 0 < A ∧ 0 ≤ B ∧
        (∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x) ∧
        (∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) := by
  let ε : ℝ := 1 / 2
  have hε : 0 < ε := by positivity
  let A : ℝ := (1 - ε) * (c / beta)
  let B : ℝ := (1 + ε) * (c / beta)
  have hA_pos : 0 < A := by
    have hcdiv_pos : 0 < c / beta := div_pos C.c_pos C.beta_pos
    dsimp [A, ε]
    positivity
  have hB_nonneg : 0 ≤ B := by
    have hcdiv_pos : 0 < c / beta := div_pos C.c_pos C.beta_pos
    dsimp [B, ε]
    positivity
  have hnear := C.cdf_power_sandwich hε
  rcases Metric.mem_nhdsWithin_iff.mp hnear with ⟨delta, hdelta_pos, hdelta⟩
  refine ⟨delta, A, B, hdelta_pos, hA_pos, hB_nonneg, ?_, ?_⟩
  · intro x hx_pos hx_lt
    have hx_ball : x ∈ Metric.ball (0 : ℝ) delta := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_of_nonneg hx_pos.le]
      exact hx_lt
    have hx_side : x ∈ Set.Ioi (0 : ℝ) := hx_pos
    have hx_prop := hdelta ⟨hx_ball, hx_side⟩
    simpa [A, mul_assoc] using hx_prop.1
  · intro x hx_pos hx_lt
    have hx_ball : x ∈ Metric.ball (0 : ℝ) delta := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_of_nonneg hx_pos.le]
      exact hx_lt
    have hx_side : x ∈ Set.Ioi (0 : ℝ) := hx_pos
    have hx_prop := hdelta ⟨hx_ball, hx_side⟩
    simpa [B, mul_assoc] using hx_prop.2

/--
After the source change of variables `x = y * a^(-1/β)`, the near-zero CDF
sandwich applies eventually for every fixed `y > 0`.
-/
theorem eventually_rescaled_cdf_power_sandwich
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {ε y : ℝ} (hε : 0 < ε) (hy_pos : 0 < y) :
    ∀ᶠ a : ℕ in atTop,
      (1 - ε) * (c / beta) *
          (y * boundedTailScale beta a) ^ beta ≤
          G (y * boundedTailScale beta a) ∧
        G (y * boundedTailScale beta a) ≤
          (1 + ε) * (c / beta) *
            (y * boundedTailScale beta a) ^ beta := by
  have hrescale :
      Tendsto (fun a => y * boundedTailScale beta a)
        atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun a => y * boundedTailScale beta a)
      (boundedTailScale_const_mul_tendsto_zero C.beta_pos) ?_
    filter_upwards [boundedTailScale_eventually_pos beta] with a hscale
    exact mul_pos hy_pos hscale
  exact hrescale.eventually (C.cdf_power_sandwich hε)

/--
Simplified rescaled CDF sandwich: after `x = y * a^(-1/β)`, the power term
becomes `y^β * a^-1`.
-/
theorem eventually_rescaled_cdf_power_sandwich_inv_nat
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {ε y : ℝ} (hε : 0 < ε) (hy_pos : 0 < y) :
    ∀ᶠ a : ℕ in atTop,
      (1 - ε) * (c / beta) *
          (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) ≤
          G (y * boundedTailScale beta a) ∧
        G (y * boundedTailScale beta a) ≤
          (1 + ε) * (c / beta) *
            (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) := by
  filter_upwards
    [C.eventually_rescaled_cdf_power_sandwich hε hy_pos,
      eventually_gt_atTop (0 : ℕ)] with a hbound ha
  simpa [boundedTailScale_rescaled_rpow_beta C.beta_pos hy_pos ha]
    using hbound

/--
After multiplying by `a`, the rescaled CDF sandwich becomes a constant
sandwich around `(c / beta) * y^beta`.
-/
theorem eventually_rescaled_cdf_nat_mul_sandwich
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {ε y : ℝ} (hε : 0 < ε) (hy_pos : 0 < y) :
    ∀ᶠ a : ℕ in atTop,
      (1 - ε) * ((c / beta) * y ^ beta) ≤
          (a : ℝ) * G (y * boundedTailScale beta a) ∧
        (a : ℝ) * G (y * boundedTailScale beta a) ≤
          (1 + ε) * ((c / beta) * y ^ beta) := by
  filter_upwards
    [C.eventually_rescaled_cdf_power_sandwich_inv_nat hε hy_pos,
      eventually_gt_atTop (0 : ℕ)] with a hbound ha
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha_pos
  have hcancel (d : ℝ) :
      (a : ℝ) *
          (d * (c / beta) * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) =
        d * ((c / beta) * y ^ beta) := by
    rw [Real.rpow_neg_one]
    field_simp [ha_ne]
  have hleft :=
    mul_le_mul_of_nonneg_left hbound.1 (le_of_lt ha_pos)
  have hright :=
    mul_le_mul_of_nonneg_left hbound.2 (le_of_lt ha_pos)
  constructor
  · calc
      (1 - ε) * ((c / beta) * y ^ beta)
          =
            (a : ℝ) *
              ((1 - ε) * (c / beta) *
                (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) := by
              rw [hcancel]
      _ ≤ (a : ℝ) * G (y * boundedTailScale beta a) := hleft
  · calc
      (a : ℝ) * G (y * boundedTailScale beta a)
          ≤
            (a : ℝ) *
              ((1 + ε) * (c / beta) *
                (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) := hright
      _ =
          (1 + ε) * ((c / beta) * y ^ beta) := by
            rw [hcancel]

/--
Pointwise rescaled CDF convergence used in Lemma D.2: for each fixed
`y > 0`, `a * G(y * a^(-1/beta))` tends to `(c / beta) * y^beta`.
-/
theorem rescaled_cdf_nat_mul_tendsto
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) :
    Tendsto
      (fun a : ℕ => (a : ℝ) * G (y * boundedTailScale beta a))
      atTop (nhds ((c / beta) * y ^ beta)) := by
  let z : ℝ := (c / beta) * y ^ beta
  have hz_pos : 0 < z := by
    exact mul_pos (div_pos C.c_pos C.beta_pos)
      (Real.rpow_pos_of_pos hy_pos beta)
  refine Metric.tendsto_nhds.mpr ?_
  intro δ hδ
  let ε : ℝ := δ / (2 * z)
  have hε : 0 < ε := by
    exact div_pos hδ (mul_pos two_pos hz_pos)
  filter_upwards [C.eventually_rescaled_cdf_nat_mul_sandwich hε hy_pos] with a hsand
  have hleft :
      (1 - ε) * z ≤ (a : ℝ) * G (y * boundedTailScale beta a) := by
    simpa [z] using hsand.1
  have hright :
      (a : ℝ) * G (y * boundedTailScale beta a) ≤ (1 + ε) * z := by
    simpa [z] using hsand.2
  have habs :
      |(a : ℝ) * G (y * boundedTailScale beta a) - z| ≤ ε * z := by
    rw [abs_sub_le_iff]
    constructor <;> nlinarith [hleft, hright, hz_pos]
  have hεz : ε * z = δ / 2 := by
    dsimp [ε]
    field_simp [ne_of_gt hz_pos]
  rw [Real.dist_eq]
  exact lt_of_le_of_lt habs (by rw [hεz]; linarith)

/--
Rescaled bounded-tail kernel limit for the `a` exponent:
`(1 - G(y * a^(-1/beta)))^a -> exp(-((c / beta) * y^beta))`.
-/
theorem rescaled_cdf_one_sub_pow_tendsto_exp
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) :
    Tendsto
      (fun a : ℕ =>
        (1 - G (y * boundedTailScale beta a)) ^ a)
      atTop (nhds (Real.exp (-((c / beta) * y ^ beta)))) :=
  bounded_one_sub_of_nat_mul_tendsto_pow_tendsto_exp
    (C.rescaled_cdf_nat_mul_tendsto hy_pos)

/--
Fixed-rank rescaled bounded-tail kernel limit for Lemma D.2:
`(1 - G(y * a^(-1/beta)))^(a-j) -> exp(-((c / beta) * y^beta))`.
-/
theorem rescaled_cdf_one_sub_pow_sub_tendsto_exp
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        (1 - G (y * boundedTailScale beta a)) ^ (a - j))
      atTop (nhds (Real.exp (-((c / beta) * y ^ beta)))) :=
  bounded_one_sub_of_nat_mul_tendsto_pow_sub_tendsto_exp
    (C.rescaled_cdf_nat_mul_tendsto hy_pos) j

/--
Pointwise Lemma D.2 binomial-kernel limit after the source substitution
`x = y * a^(-1/beta)`.
-/
theorem rescaled_cdf_binomial_kernel_tendsto
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        (Nat.choose a j : ℝ) *
          (G (y * boundedTailScale beta a)) ^ j *
          (1 - G (y * boundedTailScale beta a)) ^ (a - j))
      atTop
      (nhds
        (Real.exp (-((c / beta) * y ^ beta)) *
          (((c / beta) * y ^ beta) ^ j) / j.factorial)) := by
  simpa using
    ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop j
      (C.rescaled_cdf_nat_mul_tendsto hy_pos)

end BoundedTailCDFPowerSandwich

/--
Index set for the paper's bounded proof after equation (95).

The source uses `i = 1, ..., k` and `j = 0, ..., i - 1`; here `i : Fin k`
stores the zero-based value `i_source - 1`, and `j : Fin (i.val + 1)` stores
the inner summation index.
-/
abbrev BoundedLemmaD2Index (k : ℕ) :=
  Sigma (fun i : Fin k => Fin (i.val + 1))

/--
The limiting integrand in Lemma D.2 after the substitution
`x = y * a^(-1/beta)`.
-/
noncomputable def boundedLemmaD2LimitKernel
    (beta c : ℝ) (j : ℕ) (y : ℝ) : ℝ :=
  ((c / beta) ^ j / (j.factorial : ℝ)) *
    (y ^ (beta * (j : ℝ)) *
      Real.exp (-(c / beta) * y ^ beta))

/--
The rescaled finite-`a` Lemma D.2 kernel after the source substitution
`x = y * a^(-1/beta)`.
-/
noncomputable def boundedLemmaD2RescaledKernel
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) (y : ℝ) : ℝ :=
  (Nat.choose a j : ℝ) *
    (G (y * boundedTailScale beta a)) ^ j *
      (1 - G (y * boundedTailScale beta a)) ^ (a - j)

/--
Pointwise eventual envelope for the rescaled Lemma D.2 kernel on the growing
near-zero window, derived from local CDF power bounds.
-/
theorem boundedLemmaD2RescaledKernel_eventually_norm_le_power_exp_on_growing
    {G : ℝ → ℝ} {beta A B delta : ℝ} (j : ℕ)
    (hbeta_pos : 0 < beta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :
    ∀ᶠ a in atTop,
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        y < delta / boundedTailScale beta a →
          ‖boundedLemmaD2RescaledKernel G beta j a y‖ ≤
            B ^ j * y ^ (beta * (j : ℝ)) *
              Real.exp (-(A / 2) * y ^ beta) := by
  filter_upwards
    [eventually_gt_atTop (0 : ℕ),
      eventually_ge_atTop (2 * j),
      boundedLemmaD2_eventually_rescaled_local_cdf_power_bounds
        hbeta_pos hG_lower hG_upper] with
      a ha_pos hlarge hlocal
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with
    y hy_pos hy_window
  have hbounds := hlocal hy_pos hy_window
  simpa [boundedLemmaD2RescaledKernel] using
    boundedLemmaD2_binomial_kernel_norm_le_power_exp_of_rescaled_bounds
      (beta := beta) (A := A) (B := B) (y := y)
      (g := G (y * boundedTailScale beta a)) (j := j) (a := a)
      hA_pos hB_nonneg hy_pos ha_pos hlarge
      (hG_nonneg (y * boundedTailScale beta a))
      (hG_le_one (y * boundedTailScale beta a))
      hbounds.1 hbounds.2

/--
Indicator form of the local envelope bound, ready for dominated convergence on
the growing near-zero interval.
-/
theorem boundedLemmaD2RescaledKernel_eventually_indicator_norm_le_localEnvelope
    {G : ℝ → ℝ} {beta A B delta : ℝ} (j : ℕ)
    (hbeta_pos : 0 < beta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :
    ∀ᶠ a in atTop,
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        ‖(Set.Iio (delta / boundedTailScale beta a)).indicator
            (fun z : ℝ => boundedLemmaD2RescaledKernel G beta j a z) y‖ ≤
          boundedLemmaD2LocalEnvelope beta A B j y := by
  filter_upwards
    [boundedLemmaD2RescaledKernel_eventually_norm_le_power_exp_on_growing
      j hbeta_pos hA_pos hB_nonneg hG_nonneg hG_le_one hG_lower hG_upper]
    with a hbound
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hbound] with
      y hy_pos hbound_y
  by_cases hy : y < delta / boundedTailScale beta a
  · have hmem : y ∈ Set.Iio (delta / boundedTailScale beta a) := hy
    simpa [Set.indicator_of_mem hmem, boundedLemmaD2LocalEnvelope,
      mul_assoc] using hbound_y hy
  · have hmem : y ∉ Set.Iio (delta / boundedTailScale beta a) := hy
    rw [Set.indicator_of_notMem hmem]
    simpa using
      boundedLemmaD2LocalEnvelope_nonneg
        (beta := beta) (A := A) (B := B) (j := j)
        hB_nonneg hy_pos.le

theorem boundedLemmaD2LimitKernel_eq_poisson_form
    {beta c y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    boundedLemmaD2LimitKernel beta c j y =
      Real.exp (-((c / beta) * y ^ beta)) *
        (((c / beta) * y ^ beta) ^ j) / j.factorial := by
  have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
  have hy_pow :
      (y ^ beta) ^ j = y ^ (beta * (j : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy_nonneg]
  rw [boundedLemmaD2LimitKernel]
  rw [mul_pow, hy_pow]
  ring_nf

namespace BoundedTailCDFPowerSandwich

/--
Pointwise convergence of the rescaled finite-`a` Lemma D.2 kernel to the
limiting gamma-kernel integrand.
-/
theorem rescaled_kernel_tendsto_limit
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Tendsto
      (fun a : ℕ => boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitKernel beta c j y)) := by
  have h :=
    C.rescaled_cdf_binomial_kernel_tendsto (y := y) hy_pos j
  simpa [boundedLemmaD2RescaledKernel,
    boundedLemmaD2LimitKernel_eq_poisson_form hy_pos j] using h

end BoundedTailCDFPowerSandwich

/-- Measurability of the rescaled finite-`a` Lemma D.2 kernel. -/
theorem boundedLemmaD2RescaledKernel_aestronglyMeasurable
    {G : ℝ → ℝ} (hG : Measurable G) (beta : ℝ) (j a : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have harg :
      Measurable (fun y : ℝ => y * boundedTailScale beta a) :=
    measurable_id.mul measurable_const
  have hGcomp :
      Measurable (fun y : ℝ => G (y * boundedTailScale beta a)) :=
    hG.comp harg
  have hkernel :
      Measurable
        (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y) := by
    unfold boundedLemmaD2RescaledKernel
    exact
      (measurable_const.mul (hGcomp.pow_const j)).mul
        ((measurable_const.sub hGcomp).pow_const (a - j))
  exact hkernel.aestronglyMeasurable

/-- The Lemma D.2 limiting coefficient for one fixed inner index `j`. -/
noncomputable def boundedLemmaD2LimitCoeff
    (beta c : ℝ) (j : ℕ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), boundedLemmaD2LimitKernel beta c j y

/--
Gamma-integral evaluation of the fixed-`j` Lemma D.2 limiting coefficient.
-/
theorem boundedLemmaD2LimitCoeff_eq_gamma
    {beta c : ℝ} (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (j : ℕ) :
    boundedLemmaD2LimitCoeff beta c j =
      ((c / beta) ^ j / (j.factorial : ℝ)) *
        ((c / beta) ^ (-(beta * (j : ℝ) + 1) / beta) *
          (1 / beta) *
          Real.Gamma ((beta * (j : ℝ) + 1) / beta)) := by
  have hb_pos : 0 < c / beta := div_pos hc_pos hbeta_pos
  have hq : -1 < beta * (j : ℝ) := by
    have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
    have hmul_nonneg : 0 ≤ beta * (j : ℝ) :=
      mul_nonneg hbeta_pos.le hj_nonneg
    linarith
  rw [boundedLemmaD2LimitCoeff]
  change
    (∫ y in Set.Ioi (0 : ℝ),
      ((c / beta) ^ j / (j.factorial : ℝ)) *
        (y ^ (beta * (j : ℝ)) *
          Real.exp (-(c / beta) * y ^ beta))) =
      ((c / beta) ^ j / (j.factorial : ℝ)) *
        ((c / beta) ^ (-(beta * (j : ℝ) + 1) / beta) *
          (1 / beta) *
          Real.Gamma ((beta * (j : ℝ) + 1) / beta))
  rw [MeasureTheory.integral_const_mul]
  rw [integral_rpow_mul_exp_neg_mul_rpow hbeta_pos hq hb_pos]

/--
For the uniform reflected-CDF normalization `β = c = 1`, each fixed inner
Lemma D.2 coefficient is one.
-/
theorem boundedLemmaD2LimitCoeff_one_one (j : ℕ) :
    boundedLemmaD2LimitCoeff 1 1 j = 1 := by
  rw [boundedLemmaD2LimitCoeff_eq_gamma (by norm_num) (by norm_num)]
  have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
  norm_num
  rw [Real.Gamma_nat_eq_factorial]
  field_simp [hfac]

/-- The fixed-`j` Lemma D.2 limiting coefficient is positive. -/
theorem boundedLemmaD2LimitCoeff_pos
    {beta c : ℝ} (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (j : ℕ) :
    0 < boundedLemmaD2LimitCoeff beta c j := by
  have hb_pos : 0 < c / beta := div_pos hc_pos hbeta_pos
  have hfactorial_pos : 0 < (j.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos j
  have harg_pos : 0 < (beta * (j : ℝ) + 1) / beta := by
    have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
    have hmul_nonneg : 0 ≤ beta * (j : ℝ) :=
      mul_nonneg hbeta_pos.le hj_nonneg
    exact div_pos (by linarith) hbeta_pos
  rw [boundedLemmaD2LimitCoeff_eq_gamma hbeta_pos hc_pos j]
  exact mul_pos
    (div_pos (pow_pos hb_pos j) hfactorial_pos)
    (mul_pos
      (mul_pos
        (Real.rpow_pos_of_pos hb_pos
          (-(beta * (j : ℝ) + 1) / beta))
        (one_div_pos.mpr hbeta_pos))
      (Real.Gamma_pos_of_pos harg_pos))

theorem boundedLemmaD2LimitCoeff_sum_pos
    {beta c : ℝ} {k : ℕ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c) (k_pos : 0 < k) :
    0 < ∑ p : BoundedLemmaD2Index k,
      boundedLemmaD2LimitCoeff beta c p.2.val := by
  haveI : Nonempty (BoundedLemmaD2Index k) := by
    exact ⟨⟨⟨0, k_pos⟩, ⟨0, by simp⟩⟩⟩
  exact Finset.sum_pos
    (fun p _ => boundedLemmaD2LimitCoeff_pos hbeta_pos hc_pos p.2.val)
    Finset.univ_nonempty

/-- Finite-`a` source integrand in Lemma D.2. -/
noncomputable def boundedLemmaD2IntegralKernel
    (G : ℝ → ℝ) (j a : ℕ) (x : ℝ) : ℝ :=
  (Nat.choose a j : ℝ) * (G x) ^ j * (1 - G x) ^ (a - j)

/-- Measurability of the finite-`a` source integrand in Lemma D.2. -/
theorem boundedLemmaD2IntegralKernel_measurable
    {G : ℝ → ℝ} (hG : Measurable G) (j a : ℕ) :
    Measurable (fun x : ℝ => boundedLemmaD2IntegralKernel G j a x) := by
  unfold boundedLemmaD2IntegralKernel
  exact
    (measurable_const.mul (hG.pow_const j)).mul
      ((measurable_const.sub hG).pow_const (a - j))

/--
If `G` is CDF-valued, the source Lemma D.2 kernel is bounded by the binomial
coefficient.
-/
theorem boundedLemmaD2IntegralKernel_norm_le_choose_of_cdf_range
    {G : ℝ → ℝ} (j a : ℕ) {x : ℝ}
    (hG_nonneg : 0 ≤ G x) (hG_le_one : G x ≤ 1) :
    ‖boundedLemmaD2IntegralKernel G j a x‖ ≤ (Nat.choose a j : ℝ) := by
  have hchoose_nonneg : 0 ≤ (Nat.choose a j : ℝ) := by positivity
  have htail_nonneg : 0 ≤ 1 - G x := sub_nonneg.mpr hG_le_one
  have htail_le_one : 1 - G x ≤ 1 := by linarith
  have hGpow_nonneg : 0 ≤ (G x) ^ j := pow_nonneg hG_nonneg j
  have hGpow_le_one : (G x) ^ j ≤ 1 :=
    pow_le_one₀ hG_nonneg hG_le_one
  have htailpow_nonneg : 0 ≤ (1 - G x) ^ (a - j) :=
    pow_nonneg htail_nonneg (a - j)
  have htailpow_le_one : (1 - G x) ^ (a - j) ≤ 1 :=
    pow_le_one₀ htail_nonneg htail_le_one
  have hprod_le_one :
      (G x) ^ j * (1 - G x) ^ (a - j) ≤ 1 :=
    mul_le_one₀ hGpow_le_one htailpow_nonneg htailpow_le_one
  have hkernel_nonneg :
      0 ≤ boundedLemmaD2IntegralKernel G j a x := by
    unfold boundedLemmaD2IntegralKernel
    exact mul_nonneg (mul_nonneg hchoose_nonneg hGpow_nonneg)
      htailpow_nonneg
  rw [Real.norm_of_nonneg hkernel_nonneg]
  unfold boundedLemmaD2IntegralKernel
  calc
    (Nat.choose a j : ℝ) * (G x) ^ j *
        (1 - G x) ^ (a - j)
        = (Nat.choose a j : ℝ) *
            ((G x) ^ j * (1 - G x) ^ (a - j)) := by ring
    _ ≤ (Nat.choose a j : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hprod_le_one hchoose_nonneg
    _ = (Nat.choose a j : ℝ) := by ring

/-- The finite-`a` source integrand is nonnegative for CDF-valued `G`. -/
theorem boundedLemmaD2IntegralKernel_nonneg_of_cdf_range
    {G : ℝ → ℝ} (j a : ℕ) {x : ℝ}
    (hG_nonneg : 0 ≤ G x) (hG_le_one : G x ≤ 1) :
    0 ≤ boundedLemmaD2IntegralKernel G j a x := by
  have hchoose_nonneg : 0 ≤ (Nat.choose a j : ℝ) := by positivity
  have htail_nonneg : 0 ≤ 1 - G x := sub_nonneg.mpr hG_le_one
  unfold boundedLemmaD2IntegralKernel
  exact mul_nonneg
    (mul_nonneg hchoose_nonneg (pow_nonneg hG_nonneg j))
    (pow_nonneg htail_nonneg (a - j))

/-- The bounded-support source kernel is zero after the support endpoint. -/
theorem boundedLemmaD2IntegralKernel_eq_zero_of_support
    {G : ℝ → ℝ} {M x : ℝ} {j a : ℕ}
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hMx : M ≤ x) (hja : j < a) :
    boundedLemmaD2IntegralKernel G j a x = 0 := by
  have hGx : G x = 1 := hG_eq_one_of_support x hMx
  have hsub_pos : 0 < a - j := Nat.sub_pos_of_lt hja
  simp [boundedLemmaD2IntegralKernel, hGx, ne_of_gt hsub_pos]

/--
Pointwise geometric tail bound for the source kernel once `G x` is bounded
below by `p`.
-/
theorem boundedLemmaD2IntegralKernel_le_geometric_tail_of_cdf_range
    {G : ℝ → ℝ} (j a : ℕ) {x p : ℝ}
    (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hG_nonneg : 0 ≤ G x) (hG_le_one : G x ≤ 1)
    (hp_le_G : p ≤ G x) :
    boundedLemmaD2IntegralKernel G j a x ≤
      (Nat.choose a j : ℝ) * (1 - p) ^ (a - j) := by
  have hchoose_nonneg : 0 ≤ (Nat.choose a j : ℝ) := by positivity
  have htail_nonneg : 0 ≤ 1 - G x := sub_nonneg.mpr hG_le_one
  have hp_tail_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
  have htail_le : 1 - G x ≤ 1 - p := by linarith
  have hGpow_nonneg : 0 ≤ (G x) ^ j := pow_nonneg hG_nonneg j
  have hGpow_le_one : (G x) ^ j ≤ 1 :=
    pow_le_one₀ hG_nonneg hG_le_one
  have htailpow_nonneg : 0 ≤ (1 - G x) ^ (a - j) :=
    pow_nonneg htail_nonneg (a - j)
  have htailpow_le : (1 - G x) ^ (a - j) ≤ (1 - p) ^ (a - j) :=
    pow_le_pow_left₀ htail_nonneg htail_le (a - j)
  have hprod_le :
      (G x) ^ j * (1 - G x) ^ (a - j) ≤
        (1 - p) ^ (a - j) := by
    calc
      (G x) ^ j * (1 - G x) ^ (a - j)
          ≤ 1 * (1 - G x) ^ (a - j) :=
            mul_le_mul_of_nonneg_right hGpow_le_one htailpow_nonneg
      _ = (1 - G x) ^ (a - j) := by ring
      _ ≤ (1 - p) ^ (a - j) := htailpow_le
  unfold boundedLemmaD2IntegralKernel
  calc
    (Nat.choose a j : ℝ) * (G x) ^ j * (1 - G x) ^ (a - j)
        = (Nat.choose a j : ℝ) *
            ((G x) ^ j * (1 - G x) ^ (a - j)) := by ring
    _ ≤ (Nat.choose a j : ℝ) * (1 - p) ^ (a - j) :=
        mul_le_mul_of_nonneg_left hprod_le hchoose_nonneg

/-- A finite-interval constant envelope is integrable on `(0,∞)`. -/
theorem boundedConstantIndicator_integrable_Ioi (M C : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => if x < M then C else 0)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hindicator :
      (fun x : ℝ => if x < M then C else 0) =
        (Set.Iio M).indicator (fun _x : ℝ => C) := by
    funext x
    by_cases hx : x < M <;> simp [hx]
  rw [hindicator]
  have hfinite :
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) (Set.Iio M) ≠ ⊤ := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iio]
    have hset : Set.Iio M ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) M := by
      ext x
      simp [and_comm]
    rw [hset, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  exact
    (MeasureTheory.integrableOn_const
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (s := Set.Iio M) (C := C) hfinite).integrable_indicator
      measurableSet_Iio

/-- A finite-interval constant envelope is integrable on `(lower,∞)`. -/
theorem boundedConstantIndicator_integrable_Ioi_from
    (lower M C : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => if x < M then C else 0)
      (MeasureTheory.volume.restrict (Set.Ioi lower)) := by
  have hindicator :
      (fun x : ℝ => if x < M then C else 0) =
        (Set.Iio M).indicator (fun _x : ℝ => C) := by
    funext x
    by_cases hx : x < M <;> simp [hx]
  rw [hindicator]
  have hfinite :
      (MeasureTheory.volume.restrict (Set.Ioi lower)) (Set.Iio M) ≠ ⊤ := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iio]
    have hset : Set.Iio M ∩ Set.Ioi lower = Set.Ioo lower M := by
      ext x
      simp [and_comm]
    rw [hset, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  exact
    (MeasureTheory.integrableOn_const
      (μ := MeasureTheory.volume.restrict (Set.Ioi lower))
      (s := Set.Iio M) (C := C) hfinite).integrable_indicator
      measurableSet_Iio

/-- Integral of a finite-interval constant envelope over a tail interval. -/
theorem boundedConstantIndicator_integral_Ioi_from
    {lower M C : ℝ} (hlowerM : lower ≤ M) :
    ∫ x in Set.Ioi lower, (if x < M then C else 0) =
      C * (M - lower) := by
  have hindicator :
      (fun x : ℝ => if x < M then C else 0) =
        (Set.Iio M).indicator (fun _x : ℝ => C) := by
    funext x
    by_cases hx : x < M <;> simp [hx]
  rw [hindicator, MeasureTheory.setIntegral_indicator measurableSet_Iio]
  have hset : Set.Ioi lower ∩ Set.Iio M = Set.Ioo lower M := by
    ext x
    simp
  rw [hset, MeasureTheory.setIntegral_const]
  simp [Real.volume_real_Ioo_of_le hlowerM, mul_comm]

/--
Bounded-support CDF conditions imply eventual source-kernel integrability for
fixed `j`: once `a > j`, the kernel is zero beyond the support and bounded on
the finite interval below the support.
-/
theorem boundedLemmaD2IntegralKernel_integrableOn_of_bounded_support
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    {j a : ℕ} (hja : j < a) :
    MeasureTheory.IntegrableOn
      (boundedLemmaD2IntegralKernel G j a)
      (Set.Ioi (0 : ℝ)) := by
  let envelope : ℝ → ℝ :=
    fun x => if x < M then (Nat.choose a j : ℝ) else 0
  have henv_int :
      MeasureTheory.Integrable envelope
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    boundedConstantIndicator_integrable_Ioi M (Nat.choose a j : ℝ)
  have hkernel_aemeasurable :
      MeasureTheory.AEStronglyMeasurable
        (fun x : ℝ => boundedLemmaD2IntegralKernel G j a x)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (boundedLemmaD2IntegralKernel_measurable hG_measurable j a).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' henv_int hkernel_aemeasurable ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  by_cases hxM : x < M
  · have hbound :=
      boundedLemmaD2IntegralKernel_norm_le_choose_of_cdf_range
        (G := G) j a (hG_nonneg x) (hG_le_one x)
    simpa [envelope, hxM] using hbound
  · have hGx : G x = 1 :=
      hG_eq_one_of_support x (le_of_not_gt hxM)
    have hsub_pos : 0 < a - j := Nat.sub_pos_of_lt hja
    have hkernel_zero :
        boundedLemmaD2IntegralKernel G j a x = 0 := by
      simp [boundedLemmaD2IntegralKernel, hGx, ne_of_gt hsub_pos]
    simp [envelope, hxM, hkernel_zero]

/--
Eventual bounded-support source-kernel integrability for a fixed Lemma D.2
rank `j`.
-/
theorem boundedLemmaD2IntegralKernel_eventually_integrableOn_of_bounded_support
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (j : ℕ) :
    ∀ᶠ a in atTop,
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j a)
        (Set.Ioi (0 : ℝ)) := by
  filter_upwards [eventually_gt_atTop j] with a hja
  exact boundedLemmaD2IntegralKernel_integrableOn_of_bounded_support
    hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support hja

/--
Source Lemma D.2 integral term:

`∫_0^∞ choose(a,j) * G(x)^j * (1 - G(x))^(a-j) dx`.

Here `G` is the reflected CDF `G_X` from the proof of Theorem 1(ii). The hard
analytic proof is to show this is asymptotic to a positive constant times
`a^(-1/β)` for each fixed `j`.
-/
noncomputable def boundedLemmaD2IntegralTerm
    (G : ℝ → ℝ) (j a : ℕ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), boundedLemmaD2IntegralKernel G j a x

/-- The near-zero part of the Lemma D.2 integral, split at `delta`. -/
noncomputable def boundedLemmaD2IntegralTermBelow
    (G : ℝ → ℝ) (j a : ℕ) (delta : ℝ) : ℝ :=
  ∫ x in Set.Ioo (0 : ℝ) delta, boundedLemmaD2IntegralKernel G j a x

/-- The tail part of the Lemma D.2 integral, split at `delta`. -/
noncomputable def boundedLemmaD2IntegralTermAbove
    (G : ℝ → ℝ) (j a : ℕ) (delta : ℝ) : ℝ :=
  ∫ x in Set.Ioi delta, boundedLemmaD2IntegralKernel G j a x

/-- The above-`delta` source integral is nonnegative for CDF-valued `G`. -/
theorem boundedLemmaD2IntegralTermAbove_nonneg_of_cdf_range
    {G : ℝ → ℝ} (j a : ℕ) (delta : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1) :
    0 ≤ boundedLemmaD2IntegralTermAbove G j a delta := by
  dsimp [boundedLemmaD2IntegralTermAbove]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    (fun x _hx =>
      boundedLemmaD2IntegralKernel_nonneg_of_cdf_range
        (G := G) j a (hG_nonneg x) (hG_le_one x))

/--
Finite-support geometric tail bound for the above-`delta` Lemma D.2 source
integral.
-/
theorem boundedLemmaD2IntegralTermAbove_le_geometric_support_bound
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    {delta M p : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdeltaM : delta ≤ M)
    (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    {j a : ℕ} (hja : j < a) :
    boundedLemmaD2IntegralTermAbove G j a delta ≤
      ((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) *
        (M - delta) := by
  let envelope : ℝ → ℝ :=
    fun x => if x < M then
      (Nat.choose a j : ℝ) * (1 - p) ^ (a - j) else 0
  have hleft :
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j a)
        (Set.Ioi delta) := by
    have hbase :=
      boundedLemmaD2IntegralKernel_integrableOn_of_bounded_support
        hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support hja
    exact hbase.mono_set (fun x hx => hdelta_nonneg.trans_lt hx)
  have hright :
      MeasureTheory.IntegrableOn envelope (Set.Ioi delta) := by
    exact boundedConstantIndicator_integrable_Ioi_from delta M
      ((Nat.choose a j : ℝ) * (1 - p) ^ (a - j))
  have hmono :
      boundedLemmaD2IntegralTermAbove G j a delta ≤
        ∫ x in Set.Ioi delta, envelope x := by
    dsimp [boundedLemmaD2IntegralTermAbove]
    refine MeasureTheory.setIntegral_mono_on hleft hright measurableSet_Ioi ?_
    intro x hx_tail
    by_cases hxM : x < M
    · have hbound :=
        boundedLemmaD2IntegralKernel_le_geometric_tail_of_cdf_range
          (G := G) j a hp_nonneg hp_le_one
          (hG_nonneg x) (hG_le_one x) (hp_le_G_on_tail x hx_tail)
      simpa [envelope, hxM] using hbound
    · have hzero :=
        boundedLemmaD2IntegralKernel_eq_zero_of_support
          (G := G) (M := M) (x := x) (j := j) (a := a)
          hG_eq_one_of_support (le_of_not_gt hxM) hja
      simp [envelope, hxM, hzero]
  have henv_integral :
      ∫ x in Set.Ioi delta, envelope x =
        ((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) *
          (M - delta) := by
    exact boundedConstantIndicator_integral_Ioi_from hdeltaM
  exact hmono.trans_eq henv_integral

/--
The binomial/geometric support bound is negligible relative to the bounded
branch scale. This is the scalar tail estimate used after splitting Lemma D.2
at a fixed `delta`.
-/
theorem boundedTailScale_choose_geometric_tail_ratio_tendsto_zero
    {beta p C : ℝ} (hbeta_pos : 0 < beta)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hC_nonneg : 0 ≤ C) (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        (((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) * C) /
          boundedTailScale beta a)
      atTop (nhds 0) := by
  let rho : ℝ := 1 - p
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    linarith
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    linarith
  have hupper_tendsto :
      Tendsto
        (fun a : ℕ =>
          ((C * (rho ^ j)⁻¹) * ((a : ℝ) ^ j * rho ^ a)) /
            boundedTailScale beta a)
        atTop (nhds 0) :=
    boundedTailScale_polynomial_geometric_ratio_tendsto_zero
      hbeta_pos hrho_pos hrho_lt_one j (C * (rho ^ j)⁻¹)
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [boundedTailScale_eventually_pos beta] with a hscale_pos
    have htail_nonneg : 0 ≤ (1 - p) ^ (a - j) := by
      exact pow_nonneg (by linarith : 0 ≤ 1 - p) (a - j)
    have hnum_nonneg :
        0 ≤ ((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) * C := by
      exact mul_nonneg (mul_nonneg (by positivity) htail_nonneg) hC_nonneg
    exact div_nonneg hnum_nonneg hscale_pos.le
  · filter_upwards
      [eventually_gt_atTop j, boundedTailScale_eventually_pos beta] with
        a hja hscale_pos
    have hle : j ≤ a := le_of_lt hja
    have hchoose_le :
        (Nat.choose a j : ℝ) ≤ (a : ℝ) ^ j := by
      exact_mod_cast Nat.choose_le_pow a j
    have hrho_pow_ne : rho ^ j ≠ 0 := pow_ne_zero j hrho_pos.ne'
    have hpow :
        rho ^ a = rho ^ (a - j) * rho ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hrho_shift :
        rho ^ (a - j) = rho ^ a * (rho ^ j)⁻¹ := by
      calc
        rho ^ (a - j) = rho ^ (a - j) * 1 := by ring
        _ = rho ^ (a - j) * (rho ^ j * (rho ^ j)⁻¹) := by
              rw [mul_inv_cancel₀ hrho_pow_ne]
        _ = (rho ^ (a - j) * rho ^ j) * (rho ^ j)⁻¹ := by ring
        _ = rho ^ a * (rho ^ j)⁻¹ := by rw [← hpow]
    have htail_factor_nonneg :
        0 ≤ rho ^ a * (rho ^ j)⁻¹ :=
      mul_nonneg (pow_nonneg hrho_pos.le a)
        (inv_nonneg.mpr (pow_nonneg hrho_pos.le j))
    have hnum_le :
        ((Nat.choose a j : ℝ) * rho ^ (a - j)) * C ≤
          (((a : ℝ) ^ j * (rho ^ a * (rho ^ j)⁻¹)) * C) := by
      rw [hrho_shift]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hchoose_le htail_factor_nonneg)
        hC_nonneg
    have hdiv_le :
        (((Nat.choose a j : ℝ) * rho ^ (a - j)) * C) /
            boundedTailScale beta a ≤
          (((a : ℝ) ^ j * (rho ^ a * (rho ^ j)⁻¹)) * C) /
            boundedTailScale beta a :=
      div_le_div_of_nonneg_right hnum_le hscale_pos.le
    calc
      (((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) * C) /
          boundedTailScale beta a
          ≤ (((a : ℝ) ^ j * (rho ^ a * (rho ^ j)⁻¹)) * C) /
              boundedTailScale beta a := by
            simpa [rho] using hdiv_le
      _ = ((C * (rho ^ j)⁻¹) * ((a : ℝ) ^ j * rho ^ a)) /
            boundedTailScale beta a := by ring

/--
Finite-support geometric domination makes the above-`delta` Lemma D.2 tail
negligible relative to `a^(-1 / beta)`.
-/
theorem boundedLemmaD2IntegralTermAbove_negligible_of_geometric_support_bound
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    {beta delta M p : ℝ} (hbeta_pos : 0 < beta)
    (hdelta_nonneg : 0 ≤ delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale beta a)
      atTop (nhds 0) := by
  have hC_nonneg : 0 ≤ M - delta := sub_nonneg.mpr hdeltaM
  have hscalar :
      Tendsto
        (fun a : ℕ =>
          (((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) *
              (M - delta)) /
            boundedTailScale beta a)
        atTop (nhds 0) :=
    boundedTailScale_choose_geometric_tail_ratio_tendsto_zero
      hbeta_pos hp_pos hp_lt_one hC_nonneg j
  refine squeeze_zero' ?_ ?_ hscalar
  · filter_upwards [boundedTailScale_eventually_pos beta] with a hscale_pos
    exact div_nonneg
      (boundedLemmaD2IntegralTermAbove_nonneg_of_cdf_range
        (G := G) j a delta hG_nonneg hG_le_one)
      hscale_pos.le
  · filter_upwards
      [eventually_gt_atTop j, boundedTailScale_eventually_pos beta] with
        a hja hscale_pos
    have htail :=
      boundedLemmaD2IntegralTermAbove_le_geometric_support_bound
        hG_measurable hdelta_nonneg hdeltaM hp_pos.le hp_lt_one.le
        hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail hja
    exact div_le_div_of_nonneg_right htail hscale_pos.le

/--
Exact near-zero/tail split of the source Lemma D.2 integral.

This closes the bookkeeping part of the paper's split at `delta`; the remaining
analytic work is the near-zero asymptotic and the tail-negligibility estimate.
-/
theorem boundedLemmaD2IntegralTerm_split
    (G : ℝ → ℝ) (j a : ℕ) {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j a)
        (Set.Ioi (0 : ℝ))) :
    boundedLemmaD2IntegralTerm G j a =
      boundedLemmaD2IntegralTermBelow G j a delta +
        boundedLemmaD2IntegralTermAbove G j a delta := by
  let kernel := boundedLemmaD2IntegralKernel G j a
  have htail :=
    intervalIntegral.integral_Ioi_sub_Ioi
      (f := kernel) (μ := MeasureTheory.volume)
      h_integrable hdelta_nonneg
  have hinterval :
      ∫ x in (0 : ℝ)..delta, kernel x =
        ∫ x in Set.Ioo (0 : ℝ) delta, kernel x := by
    rw [intervalIntegral.integral_of_le hdelta_nonneg,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  dsimp [boundedLemmaD2IntegralTerm, boundedLemmaD2IntegralTermBelow,
    boundedLemmaD2IntegralTermAbove, kernel] at htail hinterval ⊢
  rw [← hinterval]
  linarith

/--
Eventual near-zero/tail split of the source Lemma D.2 integral from eventual
integrability of the source kernel.
-/
theorem boundedLemmaD2IntegralTerm_eventually_split
    (G : ℝ → ℝ) (j : ℕ) {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ))) :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTerm G j a =
        boundedLemmaD2IntegralTermBelow G j a delta +
          boundedLemmaD2IntegralTermAbove G j a delta := by
  filter_upwards [h_integrable] with a h_integrable_a
  exact boundedLemmaD2IntegralTerm_split G j a hdelta_nonneg h_integrable_a

/--
Source change of variables for Lemma D.2:
`x = y * a^(-1/beta)` on `(0,∞)`.
-/
theorem boundedLemmaD2IntegralTerm_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ)
    (hscale_pos : 0 < boundedTailScale beta a) :
    boundedLemmaD2IntegralTerm G j a =
      boundedTailScale beta a *
        ∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2RescaledKernel G beta j a y := by
  let scale := boundedTailScale beta a
  let kernel : ℝ → ℝ :=
    fun x => (Nat.choose a j : ℝ) * (G x) ^ j * (1 - G x) ^ (a - j)
  have hcv :=
    MeasureTheory.integral_comp_mul_left_Ioi (g := kernel) (a := (0 : ℝ))
      (b := scale) hscale_pos
  have hmul :
      scale * (∫ y in Set.Ioi (0 : ℝ), kernel (scale * y)) =
        ∫ x in Set.Ioi (0 : ℝ), kernel x := by
    rw [hcv]
    simp [scale, hscale_pos.ne']
  calc
    boundedLemmaD2IntegralTerm G j a =
        ∫ x in Set.Ioi (0 : ℝ), kernel x := by
          rfl
    _ = scale * (∫ y in Set.Ioi (0 : ℝ), kernel (scale * y)) := hmul.symm
    _ =
        boundedTailScale beta a *
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y := by
          dsimp [scale]
          congr 1
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro y _hy
          simp [kernel, boundedLemmaD2RescaledKernel, mul_comm, mul_left_comm,
            mul_assoc]

/--
Near-zero source change of variables for Lemma D.2:
`x = y * a^(-1/beta)` on `(0, delta)`.
-/
theorem boundedLemmaD2IntegralTermBelow_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hscale_pos : 0 < boundedTailScale beta a) :
    boundedLemmaD2IntegralTermBelow G j a delta =
      boundedTailScale beta a *
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y := by
  let scale := boundedTailScale beta a
  let kernel : ℝ → ℝ :=
    fun x => (Nat.choose a j : ℝ) * (G x) ^ j * (1 - G x) ^ (a - j)
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  have hupper_nonneg : 0 ≤ delta / scale :=
    div_nonneg hdelta_nonneg hscale_pos.le
  have hbelow_interval :
      boundedLemmaD2IntegralTermBelow G j a delta =
        ∫ x in (0 : ℝ)..delta, kernel x := by
    rw [intervalIntegral.integral_of_le hdelta_nonneg,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rfl
  have hy_interval :
      ∫ y in Set.Ioo (0 : ℝ) (delta / scale), kernel (scale * y) =
        ∫ y in (0 : ℝ)..(delta / scale), kernel (scale * y) := by
    rw [intervalIntegral.integral_of_le hupper_nonneg,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hcv :
      scale * (∫ y in (0 : ℝ)..(delta / scale), kernel (scale * y)) =
        ∫ x in (0 : ℝ)..delta, kernel x := by
    have h :=
      intervalIntegral.smul_integral_comp_mul_left
        (f := kernel) (a := (0 : ℝ)) (b := delta / scale) scale
    calc
      scale * (∫ y in (0 : ℝ)..(delta / scale), kernel (scale * y))
          = scale • (∫ y in (0 : ℝ)..(delta / scale), kernel (scale * y)) := by
            rfl
      _ = ∫ x in scale * (0 : ℝ)..scale * (delta / scale), kernel x := h
      _ = ∫ x in (0 : ℝ)..scale * (delta / scale), kernel x := by
            rw [mul_zero]
      _ = ∫ x in (0 : ℝ)..delta, kernel x := by
            congr 1
            field_simp [hscale_ne]
  calc
    boundedLemmaD2IntegralTermBelow G j a delta =
        ∫ x in (0 : ℝ)..delta, kernel x := hbelow_interval
    _ = scale *
        (∫ y in (0 : ℝ)..(delta / scale), kernel (scale * y)) := hcv.symm
    _ = boundedTailScale beta a *
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y := by
          dsimp [scale]
          rw [← hy_interval]
          congr 1
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
          intro y _hy
          simp [kernel, boundedLemmaD2RescaledKernel, scale, mul_comm, mul_left_comm,
            mul_assoc]

/--
Above-`delta` source change of variables for Lemma D.2:
`x = y * a^(-1/beta)` on `(delta, ∞)`.
-/
theorem boundedLemmaD2IntegralTermAbove_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) {delta : ℝ}
    (hscale_pos : 0 < boundedTailScale beta a) :
    boundedLemmaD2IntegralTermAbove G j a delta =
      boundedTailScale beta a *
        ∫ y in Set.Ioi (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y := by
  let scale := boundedTailScale beta a
  let kernel : ℝ → ℝ :=
    fun x => (Nat.choose a j : ℝ) * (G x) ^ j * (1 - G x) ^ (a - j)
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  have hendpoint : scale * (delta / scale) = delta := by
    field_simp [hscale_ne]
  have hcv :=
    MeasureTheory.integral_comp_mul_left_Ioi
      (g := kernel) (a := delta / scale) (b := scale) hscale_pos
  have hmul :
      scale * (∫ y in Set.Ioi (delta / scale), kernel (scale * y)) =
        ∫ x in Set.Ioi delta, kernel x := by
    rw [hcv]
    simp [hscale_ne, hendpoint]
  calc
    boundedLemmaD2IntegralTermAbove G j a delta =
        ∫ x in Set.Ioi delta, kernel x := by
          rfl
    _ = scale *
        (∫ y in Set.Ioi (delta / scale), kernel (scale * y)) := hmul.symm
    _ = boundedTailScale beta a *
        ∫ y in Set.Ioi (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y := by
          dsimp [scale]
          congr 1
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro y _hy
          simp [kernel, boundedLemmaD2RescaledKernel, mul_comm, mul_left_comm,
            mul_assoc]

/--
Eventual near-zero source change of variables for Lemma D.2. The only
excluded finite prefix is where the scaling factor may be zero.
-/
theorem boundedLemmaD2IntegralTermBelow_eventually_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta) :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTermBelow G j a delta =
        boundedTailScale beta a *
          ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y := by
  filter_upwards [boundedTailScale_eventually_pos beta] with a hscale_pos
  exact boundedLemmaD2IntegralTermBelow_changeOfVariables
    G beta j a hdelta_nonneg hscale_pos

/--
Eventual above-`delta` source change of variables for Lemma D.2. The only
excluded finite prefix is where the scaling factor may be zero.
-/
theorem boundedLemmaD2IntegralTermAbove_eventually_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) (delta : ℝ) :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTermAbove G j a delta =
        boundedTailScale beta a *
          ∫ y in Set.Ioi (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y := by
  filter_upwards [boundedTailScale_eventually_pos beta] with a hscale_pos
  exact boundedLemmaD2IntegralTermAbove_changeOfVariables
    G beta j a hscale_pos

/--
Near-zero source asymptotic from convergence of the growing rescaled integral.

After the substitution `x = y*a^(-1/beta)`, the below-`delta` interval becomes
`0 < y < delta / a^(-1/beta)`. This theorem isolates the remaining analytic
task: prove convergence of that growing-interval rescaled integral to the
gamma coefficient.
-/
theorem boundedLemmaD2IntegralTermBelow_asymptotic_of_growing_rescaled_integral
    {G : ℝ → ℝ} {beta c : ℝ} (hbeta_pos : 0 < beta)
    (hc_pos : 0 < c) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hgrowing :
      Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y)
        atTop (nhds (boundedLemmaD2LimitCoeff beta c j))) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) := by
  have hcoeff_ne :
      boundedLemmaD2LimitCoeff beta c j ≠ 0 :=
    ne_of_gt (boundedLemmaD2LimitCoeff_pos hbeta_pos hc_pos j)
  have hratio :
      Tendsto
        (fun a : ℕ =>
          (∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y) /
            boundedLemmaD2LimitCoeff beta c j)
        atTop (nhds 1) := by
    have h :=
      hgrowing.div_const (boundedLemmaD2LimitCoeff beta c j)
    simpa [hcoeff_ne] using h
  rw [EconCSLib.Math.AsymptoticEquivalent]
  refine Tendsto.congr' ?_ hratio
  filter_upwards
    [boundedLemmaD2IntegralTermBelow_eventually_changeOfVariables
      G beta j hdelta_nonneg,
      boundedTailScale_eventually_ne_zero beta] with a hchange hscale_ne
  rw [hchange]
  field_simp [hcoeff_ne, hscale_ne]

/--
Eventual source change of variables for Lemma D.2. The only excluded finite
prefix is where the scaling factor may be zero.
-/
theorem boundedLemmaD2IntegralTerm_eventually_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTerm G j a =
        boundedTailScale beta a *
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y := by
  filter_upwards [boundedTailScale_eventually_pos beta] with a hscale_pos
  exact boundedLemmaD2IntegralTerm_changeOfVariables G beta j a hscale_pos

/--
Exact split of the rescaled Lemma D.2 integral at the growing threshold
`delta / a^(-1/beta)`.
-/
theorem boundedLemmaD2RescaledIntegral_split
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hscale_pos : 0 < boundedTailScale beta a)
    (h_integrable :
      MeasureTheory.IntegrableOn
        (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
        (Set.Ioi (0 : ℝ))) :
    (∫ y in Set.Ioi (0 : ℝ),
        boundedLemmaD2RescaledKernel G beta j a y) =
      (∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
        boundedLemmaD2RescaledKernel G beta j a y) +
      (∫ y in Set.Ioi (delta / boundedTailScale beta a),
        boundedLemmaD2RescaledKernel G beta j a y) := by
  let kernel : ℝ → ℝ :=
    fun y => boundedLemmaD2RescaledKernel G beta j a y
  have hupper_nonneg :
      0 ≤ delta / boundedTailScale beta a :=
    div_nonneg hdelta_nonneg hscale_pos.le
  have htail :=
    intervalIntegral.integral_Ioi_sub_Ioi
      (f := kernel) (μ := MeasureTheory.volume)
      h_integrable hupper_nonneg
  have hinterval :
      ∫ y in (0 : ℝ)..(delta / boundedTailScale beta a), kernel y =
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          kernel y := by
    rw [intervalIntegral.integral_of_le hupper_nonneg,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  dsimp [kernel] at htail hinterval ⊢
  rw [← hinterval]
  linarith

/--
Eventual split of the rescaled Lemma D.2 integral at the growing threshold
`delta / a^(-1/beta)`.
-/
theorem boundedLemmaD2RescaledIntegral_eventually_split
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
          (Set.Ioi (0 : ℝ))) :
    ∀ᶠ a in atTop,
      (∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2RescaledKernel G beta j a y) =
        (∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y) +
        (∫ y in Set.Ioi (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y) := by
  filter_upwards
    [h_integrable, boundedTailScale_eventually_pos beta] with
      a h_integrable_a hscale_pos
  exact boundedLemmaD2RescaledIntegral_split
    G beta j a hdelta_nonneg hscale_pos h_integrable_a

/--
Integrating the rescaled kernel over the growing interval `(0,T)` is the same
as integrating the `Iio T`-truncated kernel against volume restricted to
`(0,∞)`.
-/
theorem boundedLemmaD2RescaledIntegral_Ioo_eq_indicator_integral
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) (T : ℝ) :
    (∫ y in Set.Ioo (0 : ℝ) T,
        boundedLemmaD2RescaledKernel G beta j a y) =
      ∫ y,
        (Set.Iio T).indicator
          (fun z : ℝ => boundedLemmaD2RescaledKernel G beta j a z) y
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  rw [MeasureTheory.integral_indicator measurableSet_Iio]
  rw [MeasureTheory.Measure.restrict_restrict measurableSet_Iio]
  have hset : Set.Iio T ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) T := by
    ext y
    simp [and_comm]
  rw [hset]

/--
Direct growing near-zero rescaled-integral convergence from local CDF power
bounds. This is the paper's dominated-convergence step on the expanding
near-zero interval, with the domination applied to the indicator-truncated
kernels rather than to the full tail.
-/
theorem boundedLemmaD2GrowingRescaledIntegral_tendsto_of_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let truncated : ℕ → ℝ → ℝ :=
    fun a y =>
      (Set.Iio (delta / boundedTailScale beta a)).indicator
        (fun z : ℝ => boundedLemmaD2RescaledKernel G beta j a z) y
  have hmeas :
      ∀ᶠ a in atTop,
        MeasureTheory.AEStronglyMeasurable (truncated a) μ := by
    filter_upwards with a
    dsimp [truncated, μ]
    exact
      (boundedLemmaD2RescaledKernel_aestronglyMeasurable
        hG_measurable beta j a).indicator measurableSet_Iio
  have hbound :
      ∀ᶠ a in atTop,
        ∀ᵐ y ∂μ,
          ‖truncated a y‖ ≤
            boundedLemmaD2LocalEnvelope beta A B j y := by
    simpa [truncated, μ] using
      boundedLemmaD2RescaledKernel_eventually_indicator_norm_le_localEnvelope
        j tail.beta_pos hA_pos hB_nonneg hG_nonneg hG_le_one
        hG_lower hG_upper
  have hbound_integrable :
      MeasureTheory.Integrable
        (boundedLemmaD2LocalEnvelope beta A B j) μ := by
    simpa [μ] using
      boundedLemmaD2LocalEnvelope_integrable tail.beta_pos hA_pos j
  have hlim :
      ∀ᵐ y ∂μ,
        Tendsto (fun a : ℕ => truncated a y) atTop
          (nhds (boundedLemmaD2LimitKernel beta c j y)) := by
    filter_upwards
      [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with y hy
    have hthreshold :
        ∀ᶠ a in atTop,
          y < delta / boundedTailScale beta a := by
      have hsmall :
          ∀ᶠ a in atTop,
            y * boundedTailScale beta a < delta :=
        (boundedTailScale_const_mul_tendsto_zero
          (y := y) tail.beta_pos).eventually
          (Iio_mem_nhds hdelta_pos)
      filter_upwards
        [hsmall, boundedTailScale_eventually_pos beta] with
          a hsmall_a hscale_pos
      rw [lt_div_iff₀ hscale_pos]
      simpa [mul_comm] using hsmall_a
    refine Tendsto.congr' ?_
      (tail.rescaled_kernel_tendsto_limit hy j)
    filter_upwards [hthreshold] with a hthreshold_a
    dsimp [truncated]
    rw [Set.indicator_of_mem (show y ∈ Set.Iio
      (delta / boundedTailScale beta a) from hthreshold_a)]
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (boundedLemmaD2LocalEnvelope beta A B j)
      hmeas hbound hbound_integrable hlim
  refine Tendsto.congr' ?_ (by simpa [μ, boundedLemmaD2LimitCoeff] using h)
  filter_upwards with a
  symm
  exact boundedLemmaD2RescaledIntegral_Ioo_eq_indicator_integral
    G beta j a (delta / boundedTailScale beta a)

/--
Local CDF power bounds give the below-`delta` source asymptotic through the
paper's growing near-zero rescaled integral.
-/
theorem boundedLemmaD2IntegralTermBelow_asymptotic_of_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (j : ℕ) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) :=
  boundedLemmaD2IntegralTermBelow_asymptotic_of_growing_rescaled_integral
    tail.beta_pos tail.c_pos j hdelta_pos.le
    (boundedLemmaD2GrowingRescaledIntegral_tendsto_of_local_cdf_power_bounds
      tail hG_measurable hdelta_pos hA_pos hB_nonneg hG_nonneg hG_le_one
      hG_lower hG_upper j)

/--
Growing near-zero rescaled-integral convergence from full rescaled convergence
and convergence of the rescaled above-threshold tail to zero.
-/
theorem boundedLemmaD2GrowingRescaledIntegral_tendsto_of_full_and_tail
    {G : ℝ → ℝ} {beta c : ℝ} (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
          (Set.Ioi (0 : ℝ)))
    (hfull :
      Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y)
        atTop (nhds (boundedLemmaD2LimitCoeff beta c j)))
    (htail :
      Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y)
        atTop (nhds 0)) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) := by
  have hdiff := hfull.sub htail
  refine Tendsto.congr' ?_ (by simpa using hdiff)
  filter_upwards
    [boundedLemmaD2RescaledIntegral_eventually_split
      G beta j hdelta_nonneg h_integrable] with a hsplit
  rw [hsplit]
  ring

/--
Growing near-zero rescaled-integral convergence from full rescaled convergence
and source-tail negligibility. The above-`delta` change of variables converts
the source tail divided by `a^(-1/beta)` into the rescaled tail integral.
-/
theorem boundedLemmaD2GrowingRescaledIntegral_tendsto_of_full_and_source_tail
    {G : ℝ → ℝ} {beta c : ℝ} (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
          (Set.Ioi (0 : ℝ)))
    (hfull :
      Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y)
        atTop (nhds (boundedLemmaD2LimitCoeff beta c j)))
    (htail_source :
      Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j a delta /
            boundedTailScale beta a)
        atTop (nhds 0)) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) := by
  have htail_rescaled :
      Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y)
        atTop (nhds 0) := by
    refine Tendsto.congr' ?_ htail_source
    filter_upwards
      [boundedLemmaD2IntegralTermAbove_eventually_changeOfVariables
        G beta j delta,
        boundedTailScale_eventually_ne_zero beta] with a hchange hscale_ne
    rw [hchange]
    field_simp [hscale_ne]
  exact boundedLemmaD2GrowingRescaledIntegral_tendsto_of_full_and_tail
    j hdelta_nonneg h_integrable hfull htail_rescaled

/-- The source integral term indexed by the paper's `(i,j)` finite sum. -/
noncomputable def boundedLemmaD2IndexedIntegralTerm
    (G : ℝ → ℝ) {k : ℕ}
    (p : BoundedLemmaD2Index k) (a : ℕ) : ℝ :=
  boundedLemmaD2IntegralTerm G p.2.val a

/--
The finite double sum of Lemma D.2-style rank terms that gives the bounded
top-`k` loss `M k - h(a)` after the reflection identity.
-/
noncomputable def boundedLemmaD2TopKLoss
    (k : ℕ) (term : BoundedLemmaD2Index k → ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ p : BoundedLemmaD2Index k, term p a

/-- The `Sigma` index is exactly the paper's nested `i`/`j` finite sum. -/
theorem boundedLemmaD2TopKLoss_eq_nested_sum
    (k : ℕ) (term : BoundedLemmaD2Index k → ℕ → ℝ) (a : ℕ) :
    boundedLemmaD2TopKLoss k term a =
      ∑ i : Fin k, ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a := by
  rw [boundedLemmaD2TopKLoss, Fintype.sum_sigma]

/--
Reflection algebra behind equations (91)-(95): if each original upper
order-statistic mean equals `M` minus the corresponding reflected nested
integral sum, then the top-`k` loss is exactly the nested reflected sum.
-/
theorem boundedLemmaD2_reflection_loss_eq_nested_sum
    (M : ℝ) {k : ℕ}
    (sourceMean : Fin k → ℝ)
    (term : BoundedLemmaD2Index k → ℝ)
    (hsource :
      ∀ i : Fin k,
        sourceMean i =
          M - ∑ j : Fin (i.val + 1), term ⟨i, j⟩) :
    (k : ℝ) * M - ∑ i : Fin k, sourceMean i =
      ∑ i : Fin k, ∑ j : Fin (i.val + 1), term ⟨i, j⟩ := by
  simpa [EconCSLib.Probability.topKSourceEndpointLoss,
    EconCSLib.Probability.reflectedTopKMeanSum] using
    EconCSLib.Probability.topKSourceEndpointLoss_eq_reflectedTopKMeanSum
      M sourceMean
      (fun i : Fin k => ∑ j : Fin (i.val + 1), term ⟨i, j⟩)
      hsource

/--
Sequence form of the reflection algebra, targeting the internal
`boundedLemmaD2TopKLoss` finite-sum object.
-/
theorem boundedLemmaD2_reflection_loss_eq_topKLoss
    (M : ℝ) {k : ℕ}
    (sourceMean : Fin k → ℕ → ℝ)
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a)
    (a : ℕ) :
    (k : ℝ) * M - ∑ i : Fin k, sourceMean i a =
      boundedLemmaD2TopKLoss k term a := by
  rw [boundedLemmaD2TopKLoss_eq_nested_sum]
  simpa [EconCSLib.Probability.topKSourceEndpointLossSeq,
    EconCSLib.Probability.reflectedTopKMeanSumSeq,
    EconCSLib.Probability.topKSourceEndpointLoss,
    EconCSLib.Probability.reflectedTopKMeanSum] using
    EconCSLib.Probability.topKSourceEndpointLossSeq_eq_reflectedTopKMeanSumSeq
      M sourceMean
      (fun i a => ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a)
      hsource a

/--
Certificate for the bounded branch's Lemma D.2 outputs, separated from the
hard analytic integral proof.

Each fixed `(i,j)` term must be asymptotic to a positive coefficient times the
paper scale `a^(-1 / beta)`. The `totalCoeff_pos` field records the source
fact that summing the finitely many positive constants still gives a positive
constant `B`.
-/
structure BoundedLemmaD2FiniteSumCertificate
    (beta : ℝ) (k : ℕ)
    (term : BoundedLemmaD2Index k → ℕ → ℝ) where
  /-- Positive coefficient for each fixed Lemma D.2 rank/index term. -/
  coeff : BoundedLemmaD2Index k → ℝ
  coeff_pos : ∀ p, 0 < coeff p
  totalCoeff_pos : 0 < ∑ p : BoundedLemmaD2Index k, coeff p
  term_asymptotic :
    ∀ p,
      EconCSLib.Math.AsymptoticEquivalent (term p)
        (fun a => coeff p * boundedTailScale beta a)

namespace BoundedLemmaD2FiniteSumCertificate

/--
Each fixed Lemma D.2 term is eventually trapped between the standard
`(1±ε)` multiples of its asymptotic equivalent.
-/
theorem eventually_term_sandwich
    {beta : ℝ} {k : ℕ}
    {term : BoundedLemmaD2Index k → ℕ → ℝ}
    (C : BoundedLemmaD2FiniteSumCertificate beta k term)
    (p : BoundedLemmaD2Index k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in atTop,
      (1 - ε) * (C.coeff p * boundedTailScale beta a) ≤ term p a ∧
        term p a ≤
          (1 + ε) * (C.coeff p * boundedTailScale beta a) := by
  refine
    EconCSLib.Math.AsymptoticEquivalent.eventually_sandwich_of_pos_right
      (C.term_asymptotic p) ?_ hε
  filter_upwards [boundedTailScale_eventually_pos beta] with a hscale
  exact mul_pos (C.coeff_pos p) hscale

/--
Uniform finite-index version of `eventually_term_sandwich`, useful when the
source proof needs one threshold that works for every fixed `(i,j)` term.
-/
theorem eventually_all_term_sandwich
    {beta : ℝ} {k : ℕ}
    {term : BoundedLemmaD2Index k → ℕ → ℝ}
    (C : BoundedLemmaD2FiniteSumCertificate beta k term)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in atTop,
      ∀ p : BoundedLemmaD2Index k,
        (1 - ε) * (C.coeff p * boundedTailScale beta a) ≤ term p a ∧
          term p a ≤
            (1 + ε) * (C.coeff p * boundedTailScale beta a) := by
  classical
  refine eventually_all.2 ?_
  intro p
  exact C.eventually_term_sandwich p hε

end BoundedLemmaD2FiniteSumCertificate

/--
Source-facing certificate for the actual bounded Lemma D.2 integral terms.

Supplying this certificate is precisely the remaining analytic work in the
bounded branch: prove the reflected CDF integral term has the paper's
`a^(-1/β)` asymptotic for each fixed source `(i,j)` index.
-/
abbrev BoundedLemmaD2IntegralAsymptoticCertificate
    (beta : ℝ) (k : ℕ) (G : ℝ → ℝ) :=
  BoundedLemmaD2FiniteSumCertificate beta k
    (boundedLemmaD2IndexedIntegralTerm G)

/--
Sharper source-facing certificate for the actual Lemma D.2 integral terms:
the coefficient for each fixed source rank/index is the gamma-integral
coefficient of the limiting kernel.
-/
structure BoundedLemmaD2LimitIntegralAsymptoticCertificate
    (beta c : ℝ) (k : ℕ) (G : ℝ → ℝ) where
  beta_pos : 0 < beta
  c_pos : 0 < c
  k_pos : 0 < k
  term_asymptotic :
    ∀ p : BoundedLemmaD2Index k,
      EconCSLib.Math.AsymptoticEquivalent
        (boundedLemmaD2IndexedIntegralTerm G p)
        (fun a =>
          boundedLemmaD2LimitCoeff beta c p.2.val *
            boundedTailScale beta a)

namespace BoundedLemmaD2LimitIntegralAsymptoticCertificate

/--
For `k > 0`, the exact limiting coefficients give a standard finite-sum
certificate for the actual source integral terms.
-/
noncomputable def toIntegralAsymptoticCertificate
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G) :
    BoundedLemmaD2IntegralAsymptoticCertificate beta k G := by
  haveI : Nonempty (BoundedLemmaD2Index k) := by
    refine ⟨⟨⟨0, C.k_pos⟩, ⟨0, by simp⟩⟩⟩
  refine
    { coeff := fun p => boundedLemmaD2LimitCoeff beta c p.2.val
      coeff_pos := ?_
      totalCoeff_pos := ?_
      term_asymptotic := C.term_asymptotic }
  · intro p
    exact boundedLemmaD2LimitCoeff_pos C.beta_pos C.c_pos p.2.val
  · exact Finset.sum_pos
      (fun p _ =>
        boundedLemmaD2LimitCoeff_pos C.beta_pos C.c_pos p.2.val)
      Finset.univ_nonempty

end BoundedLemmaD2LimitIntegralAsymptoticCertificate

/--
Per-rank dominated-convergence certificate for Lemma D.2.

This records the two analytic facts not supplied by the near-zero CDF
sandwich alone: the source change of variables and a single integrable
dominating envelope for the rescaled kernels. The pointwise kernel limit is
proved from `tail`.
-/
structure BoundedLemmaD2DominatedKernelCertificate
    (beta c : ℝ) (G : ℝ → ℝ) (j : ℕ) where
  tail : BoundedTailCDFPowerSandwich G beta c
  change_of_variables :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTerm G j a =
        boundedTailScale beta a *
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y
  kernel_measurable :
    ∀ᶠ a in atTop,
      MeasureTheory.AEStronglyMeasurable
        (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  bound : ℝ → ℝ
  bound_integrable :
    MeasureTheory.Integrable bound
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  kernel_bound :
    ∀ᶠ a in atTop,
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        ‖boundedLemmaD2RescaledKernel G beta j a y‖ ≤ bound y

namespace BoundedLemmaD2DominatedKernelCertificate

/--
Build the per-rank dominated-convergence certificate from measurability of the
reflected CDF and an integrable envelope. The source change of variables is
proved internally by `boundedLemmaD2IntegralTerm_eventually_changeOfVariables`.
-/
noncomputable def ofMeasurableBound
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG : Measurable G)
    (bound : ℝ → ℝ)
    (bound_integrable :
      MeasureTheory.Integrable bound
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (kernel_bound :
      ∀ᶠ a in atTop,
        ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
          ‖boundedLemmaD2RescaledKernel G beta j a y‖ ≤ bound y) :
    BoundedLemmaD2DominatedKernelCertificate beta c G j where
  tail := tail
  change_of_variables :=
    boundedLemmaD2IntegralTerm_eventually_changeOfVariables G beta j
  kernel_measurable := by
    filter_upwards with a
    exact boundedLemmaD2RescaledKernel_aestronglyMeasurable hG beta j a
  bound := bound
  bound_integrable := bound_integrable
  kernel_bound := kernel_bound

/--
Dominated convergence for the rescaled Lemma D.2 kernels.
-/
theorem rescaled_integral_tendsto
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) := by
  have hlim :
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        Tendsto
          (fun a : ℕ => boundedLemmaD2RescaledKernel G beta j a y)
          atTop (nhds (boundedLemmaD2LimitKernel beta c j y)) := by
    filter_upwards
      [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with y hy
    exact C.tail.rescaled_kernel_tendsto_limit hy j
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      C.bound C.kernel_measurable C.kernel_bound C.bound_integrable hlim
  simpa [boundedLemmaD2LimitCoeff] using h

/--
The dominated-convergence certificate also supplies eventual integrability of
the rescaled kernels on `(0,∞)`.
-/
theorem eventually_rescaledKernel_integrableOn
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j) :
    ∀ᶠ a in atTop,
      MeasureTheory.IntegrableOn
        (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
        (Set.Ioi (0 : ℝ)) := by
  filter_upwards [C.kernel_measurable, C.kernel_bound] with
    a hmeas hbound
  exact MeasureTheory.Integrable.mono'
    C.bound_integrable hmeas hbound

/--
Direct dominated-convergence proof of the paper's growing near-zero rescaled
integral. The truncation interval expands to `(0,∞)` because
`delta / a^(-1/beta) → ∞`.
-/
theorem growing_rescaled_integral_tendsto
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let truncated : ℕ → ℝ → ℝ :=
    fun a y =>
      (Set.Iio (delta / boundedTailScale beta a)).indicator
        (fun z : ℝ => boundedLemmaD2RescaledKernel G beta j a z) y
  have hmeas :
      ∀ᶠ a in atTop,
        MeasureTheory.AEStronglyMeasurable (truncated a) μ := by
    filter_upwards [C.kernel_measurable] with a hkernel_meas
    dsimp [truncated, μ] at hkernel_meas ⊢
    exact hkernel_meas.indicator measurableSet_Iio
  have hbound :
      ∀ᶠ a in atTop,
        ∀ᵐ y ∂μ, ‖truncated a y‖ ≤ C.bound y := by
    filter_upwards [C.kernel_bound] with a hkernel_bound
    filter_upwards [hkernel_bound] with y hbound_y
    dsimp [truncated]
    by_cases hy :
        y ∈ Set.Iio (delta / boundedTailScale beta a)
    · simpa [Set.indicator_of_mem hy] using hbound_y
    · have hbound_nonneg : 0 ≤ C.bound y :=
        (norm_nonneg
          (boundedLemmaD2RescaledKernel G beta j a y)).trans hbound_y
      rw [Set.indicator_of_notMem hy]
      simpa using hbound_nonneg
  have hlim :
      ∀ᵐ y ∂μ,
        Tendsto (fun a : ℕ => truncated a y) atTop
          (nhds (boundedLemmaD2LimitKernel beta c j y)) := by
    filter_upwards
      [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with y hy
    have hthreshold :
        ∀ᶠ a in atTop,
          y < delta / boundedTailScale beta a := by
      have hsmall :
          ∀ᶠ a in atTop,
            y * boundedTailScale beta a < delta :=
        (boundedTailScale_const_mul_tendsto_zero
          (y := y) C.tail.beta_pos).eventually
          (Iio_mem_nhds hdelta_pos)
      filter_upwards
        [hsmall, boundedTailScale_eventually_pos beta] with
          a hsmall_a hscale_pos
      rw [lt_div_iff₀ hscale_pos]
      simpa [mul_comm] using hsmall_a
    refine Tendsto.congr' ?_
      (C.tail.rescaled_kernel_tendsto_limit hy j)
    filter_upwards [hthreshold] with a hthreshold_a
    dsimp [truncated]
    rw [Set.indicator_of_mem (show y ∈ Set.Iio
      (delta / boundedTailScale beta a) from hthreshold_a)]
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) C.bound hmeas hbound C.bound_integrable hlim
  refine Tendsto.congr' ?_ (by simpa [μ, boundedLemmaD2LimitCoeff] using h)
  filter_upwards with a
  symm
  exact boundedLemmaD2RescaledIntegral_Ioo_eq_indicator_integral
    G beta j a (delta / boundedTailScale beta a)

/--
The dominated-convergence certificate gives the below-`delta` source
asymptotic directly through the paper's growing near-zero rescaled integral.
-/
theorem integralTermBelow_asymptoticEquivalent
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) :=
  boundedLemmaD2IntegralTermBelow_asymptotic_of_growing_rescaled_integral
    C.tail.beta_pos C.tail.c_pos j hdelta_pos.le
    (C.growing_rescaled_integral_tendsto hdelta_pos)

/--
The dominated-convergence certificate plus source-tail negligibility gives the
paper's growing near-zero rescaled integral convergence.
-/
theorem growing_rescaled_integral_tendsto_of_source_tail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (htail_source :
      Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j a delta /
            boundedTailScale beta a)
        atTop (nhds 0)) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) :=
  boundedLemmaD2GrowingRescaledIntegral_tendsto_of_full_and_source_tail
    j hdelta_nonneg C.eventually_rescaledKernel_integrableOn
    C.rescaled_integral_tendsto htail_source

/--
The dominated-convergence certificate plus source-tail negligibility gives the
below-`delta` source asymptotic by the paper's growing-interval route.
-/
theorem integralTermBelow_asymptoticEquivalent_of_source_tail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (htail_source :
      Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j a delta /
            boundedTailScale beta a)
        atTop (nhds 0)) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) :=
  boundedLemmaD2IntegralTermBelow_asymptotic_of_growing_rescaled_integral
    C.tail.beta_pos C.tail.c_pos j hdelta_nonneg
    (C.growing_rescaled_integral_tendsto_of_source_tail
      hdelta_nonneg htail_source)

/--
A per-rank dominated-convergence certificate supplies the exact
`a^(-1/beta)` asymptotic for the source Lemma D.2 integral term.
-/
theorem integralTerm_asymptoticEquivalent
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2IntegralTerm G j)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) := by
  have hcoeff_ne :
      boundedLemmaD2LimitCoeff beta c j ≠ 0 :=
    ne_of_gt (boundedLemmaD2LimitCoeff_pos
      C.tail.beta_pos C.tail.c_pos j)
  have hratio :
      Tendsto
        (fun a : ℕ =>
          (∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y) /
              boundedLemmaD2LimitCoeff beta c j)
        atTop (nhds 1) := by
    have h :=
      C.rescaled_integral_tendsto.div_const
        (boundedLemmaD2LimitCoeff beta c j)
    simpa [hcoeff_ne] using h
  rw [EconCSLib.Math.AsymptoticEquivalent]
  refine Tendsto.congr' ?_ hratio
  filter_upwards
    [C.change_of_variables, boundedTailScale_eventually_ne_zero beta] with
      a hchange hscale_ne
  rw [hchange]
  field_simp [hcoeff_ne, hscale_ne]

end BoundedLemmaD2DominatedKernelCertificate

/--
Per-rank split certificate matching the paper proof of Lemma D.2.

The near-zero integral has the gamma asymptotic, the tail integral is
negligible relative to `a^(-1/beta)`, and the full integral is eventually the
sum of those two pieces.
-/
structure BoundedLemmaD2SplitIntegralAsymptoticCertificate
    (beta c : ℝ) (G : ℝ → ℝ) (j : ℕ) where
  beta_pos : 0 < beta
  c_pos : 0 < c
  delta : ℝ
  delta_pos : 0 < delta
  split :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTerm G j a =
        boundedLemmaD2IntegralTermBelow G j a delta +
          boundedLemmaD2IntegralTermAbove G j a delta
  below_asymptotic :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a)
  above_negligible :
    Tendsto
      (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
        boundedTailScale beta a)
      atTop (nhds 0)

namespace BoundedLemmaD2SplitIntegralAsymptoticCertificate

/--
Build the paper-style split certificate once the source kernel is eventually
integrable and the two analytic estimates have been proved.
-/
noncomputable def ofAsymptotics
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)))
    (below_asymptotic :
      EconCSLib.Math.AsymptoticEquivalent
        (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
        (fun a => boundedLemmaD2LimitCoeff beta c j *
          boundedTailScale beta a))
    (above_negligible :
      Tendsto
        (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale beta a)
        atTop (nhds 0)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j where
  beta_pos := hbeta_pos
  c_pos := hc_pos
  delta := delta
  delta_pos := hdelta_pos
  split :=
    boundedLemmaD2IntegralTerm_eventually_split G j hdelta_pos.le
      h_integrable
  below_asymptotic := below_asymptotic
  above_negligible := above_negligible

/--
Build the paper-style split certificate from the already-assembled full
integral asymptotic plus the tail-negligibility estimate. This is useful for
checking that the direct dominated-convergence route and the paper's
near-zero/tail split route agree on the same coefficient.
-/
noncomputable def ofFullAsymptoticAndTail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)))
    (full_asymptotic :
      EconCSLib.Math.AsymptoticEquivalent
        (boundedLemmaD2IntegralTerm G j)
        (fun a => boundedLemmaD2LimitCoeff beta c j *
          boundedTailScale beta a))
    (above_negligible :
      Tendsto
        (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale beta a)
        atTop (nhds 0)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j where
  beta_pos := hbeta_pos
  c_pos := hc_pos
  delta := delta
  delta_pos := hdelta_pos
  split :=
    boundedLemmaD2IntegralTerm_eventually_split G j hdelta_pos.le
      h_integrable
  below_asymptotic := by
    have hsplit :=
      boundedLemmaD2IntegralTerm_eventually_split G j hdelta_pos.le
        h_integrable
    have hcoeff_ne :
        boundedLemmaD2LimitCoeff beta c j ≠ 0 :=
      ne_of_gt (boundedLemmaD2LimitCoeff_pos hbeta_pos hc_pos j)
    have htail_coeff :
        Tendsto
          (fun a : ℕ =>
            boundedLemmaD2IntegralTermAbove G j a delta /
              (boundedLemmaD2LimitCoeff beta c j *
                boundedTailScale beta a))
          atTop (nhds 0) := by
      have h :=
        above_negligible.div_const (boundedLemmaD2LimitCoeff beta c j)
      refine Tendsto.congr' ?_ (by simpa [hcoeff_ne] using h)
      filter_upwards [boundedTailScale_eventually_ne_zero beta] with a hscale_ne
      field_simp [hcoeff_ne, hscale_ne]
    rw [EconCSLib.Math.AsymptoticEquivalent] at full_asymptotic ⊢
    have hdiff := full_asymptotic.sub htail_coeff
    refine Tendsto.congr' ?_ (by simpa using hdiff)
    filter_upwards
      [hsplit, boundedTailScale_eventually_ne_zero beta] with
        a hsplit_a hscale_ne
    rw [hsplit_a]
    field_simp [hcoeff_ne, hscale_ne]
    ring
  above_negligible := above_negligible

/--
Build the paper-style split certificate from bounded-support CDF conditions
and the two remaining analytic estimates.
-/
noncomputable def ofBoundedSupportAsymptotics
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta)
    (hG_measurable : Measurable G) (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (below_asymptotic :
      EconCSLib.Math.AsymptoticEquivalent
        (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
        (fun a => boundedLemmaD2LimitCoeff beta c j *
          boundedTailScale beta a))
    (above_negligible :
      Tendsto
        (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale beta a)
        atTop (nhds 0)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  ofAsymptotics hbeta_pos hc_pos hdelta_pos
    (boundedLemmaD2IntegralKernel_eventually_integrableOn_of_bounded_support
      hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support j)
    below_asymptotic above_negligible

/--
Build the paper-style split certificate from bounded-support CDF conditions,
the positive CDF floor on the above-`delta` tail, and the near-zero asymptotic.
The geometric tail-negligibility estimate is proved internally.
-/
noncomputable def ofBoundedSupportNearZeroAsymptotic
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    (below_asymptotic :
      EconCSLib.Math.AsymptoticEquivalent
        (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
        (fun a => boundedLemmaD2LimitCoeff beta c j *
          boundedTailScale beta a)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  ofBoundedSupportAsymptotics hbeta_pos hc_pos hdelta_pos
    hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support
    below_asymptotic
    (boundedLemmaD2IntegralTermAbove_negligible_of_geometric_support_bound
      hG_measurable hbeta_pos hdelta_pos.le hdeltaM hp_pos hp_lt_one
      hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail j)

/--
Convert a dominated-convergence full-integral certificate into the
paper-style split certificate when bounded support supplies the geometric tail
estimate. This proves the near-zero split field by subtracting the negligible
tail from the full asymptotic.
-/
noncomputable def ofDominatedKernelAndGeometricTail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p : ℝ}
    (D : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  ofFullAsymptoticAndTail D.tail.beta_pos D.tail.c_pos hdelta_pos
    (boundedLemmaD2IntegralKernel_eventually_integrableOn_of_bounded_support
      hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support j)
    D.integralTerm_asymptoticEquivalent
    (boundedLemmaD2IntegralTermAbove_negligible_of_geometric_support_bound
      hG_measurable D.tail.beta_pos hdelta_pos.le hdeltaM hp_pos hp_lt_one
      hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail j)

/--
Convert a dominated-convergence full-integral certificate into the
paper-style split certificate through the growing near-zero rescaled integral.
This uses the same bounded-support geometric tail estimate, but proves the
below-`delta` field by the paper's rescaled near-zero interval rather than by
subtracting source asymptotics.
-/
noncomputable def ofDominatedKernelAndGeometricTailViaGrowing
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p : ℝ}
    (D : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j := by
  let htail_source :=
    boundedLemmaD2IntegralTermAbove_negligible_of_geometric_support_bound
      hG_measurable D.tail.beta_pos hdelta_pos.le hdeltaM hp_pos hp_lt_one
      hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail j
  exact
    ofBoundedSupportAsymptotics D.tail.beta_pos D.tail.c_pos hdelta_pos
      hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support
      (D.integralTermBelow_asymptoticEquivalent hdelta_pos)
      htail_source

/--
Construct the paper-style split certificate directly from the bounded-tail
limit, local CDF power bounds near zero, and bounded-support geometric tail
control. This is the faithful bounded-support Lemma D.2 route: local domination
on the expanding near-zero interval proves the below split, while bounded
support controls the above split.
-/
noncomputable def ofLocalCDFPowerBoundsAndGeometricTail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j := by
  let hbelow :=
    boundedLemmaD2IntegralTermBelow_asymptotic_of_local_cdf_power_bounds
      tail hG_measurable hdelta_pos hA_pos hB_nonneg
      hG_nonneg hG_le_one hG_lower hG_upper j
  let htail_source :=
    boundedLemmaD2IntegralTermAbove_negligible_of_geometric_support_bound
      hG_measurable tail.beta_pos hdelta_pos.le hdeltaM hp_pos hp_lt_one
      hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail j
  exact
    ofBoundedSupportAsymptotics tail.beta_pos tail.c_pos hdelta_pos
      hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support
      hbelow htail_source

/--
Construct the paper-style split certificate from the bounded-tail CDF
asymptotic, monotonicity of the reflected CDF, and bounded support. The CDF
asymptotic gives local power bounds near zero; monotonicity turns a smaller
near-zero lower bound into the positive above-threshold floor used by the
geometric tail estimate.
-/
noncomputable def ofCDFPowerSandwichMonotoneBoundedSupport
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {M : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hM_pos : 0 < M)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j := by
  let hlocal := tail.exists_local_cdf_power_bounds
  let delta₀ : ℝ := Classical.choose hlocal
  let hlocal_delta := Classical.choose_spec hlocal
  let A : ℝ := Classical.choose hlocal_delta
  let hlocal_A := Classical.choose_spec hlocal_delta
  let B : ℝ := Classical.choose hlocal_A
  have hlocal_spec := Classical.choose_spec hlocal_A
  rcases hlocal_spec with
    ⟨hdelta₀_pos, hA_pos, hB_nonneg, hG_lower₀, hG_upper₀⟩
  let delta : ℝ := min delta₀ M / 2
  let probe : ℝ := delta / 2
  let p : ℝ := (A * probe ^ beta) / 2
  have hmin_pos : 0 < min delta₀ M := lt_min hdelta₀_pos hM_pos
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    positivity
  have hdelta_lt_delta₀ : delta < delta₀ := by
    have hmin_le : min delta₀ M ≤ delta₀ := min_le_left _ _
    dsimp [delta]
    linarith
  have hdeltaM : delta ≤ M := by
    have hmin_le : min delta₀ M ≤ M := min_le_right _ _
    dsimp [delta]
    linarith
  have hprobe_pos : 0 < probe := by
    dsimp [probe]
    positivity
  have hprobe_lt_delta : probe < delta := by
    dsimp [probe]
    linarith
  have hprobe_lt_delta₀ : probe < delta₀ :=
    lt_trans hprobe_lt_delta hdelta_lt_delta₀
  have hprobe_lower : A * probe ^ beta ≤ G probe :=
    hG_lower₀ probe hprobe_pos hprobe_lt_delta₀
  have hAprobe_pos : 0 < A * probe ^ beta :=
    mul_pos hA_pos (Real.rpow_pos_of_pos hprobe_pos beta)
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hp_le_Aprobe : p ≤ A * probe ^ beta := by
    dsimp [p]
    linarith
  have hp_lt_one : p < 1 := by
    have hAprobe_le_one : A * probe ^ beta ≤ 1 :=
      le_trans hprobe_lower (hG_le_one probe)
    dsimp [p]
    linarith
  have hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x := by
    intro x hx_pos hx_lt
    exact hG_lower₀ x hx_pos (lt_trans hx_lt hdelta_lt_delta₀)
  have hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta := by
    intro x hx_pos hx_lt
    exact hG_upper₀ x hx_pos (lt_trans hx_lt hdelta_lt_delta₀)
  have hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x := by
    intro x hx
    have hprobe_le_x : probe ≤ x :=
      le_of_lt (lt_trans hprobe_lt_delta hx)
    exact le_trans hp_le_Aprobe
      (le_trans hprobe_lower (hG_mono hprobe_le_x))
  exact
    ofLocalCDFPowerBoundsAndGeometricTail tail hdelta_pos hdeltaM
      hA_pos hB_nonneg hp_pos hp_lt_one hG_measurable
      hG_nonneg hG_le_one hG_lower hG_upper hG_eq_one_of_support
      hp_le_G_on_tail

/--
The paper's split proof supplies the fixed-rank Lemma D.2 integral
asymptotic.
-/
theorem integralTerm_asymptoticEquivalent
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2IntegralTerm G j)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) := by
  have hcoeff_ne :
      boundedLemmaD2LimitCoeff beta c j ≠ 0 :=
    ne_of_gt (boundedLemmaD2LimitCoeff_pos C.beta_pos C.c_pos j)
  have hsum :=
    asymptoticEquivalent_add_negligible_common_scale
      (fun a => boundedLemmaD2IntegralTermBelow G j a C.delta)
      (fun a => boundedLemmaD2IntegralTermAbove G j a C.delta)
      (boundedTailScale beta)
      (boundedLemmaD2LimitCoeff beta c j)
      hcoeff_ne
      (boundedTailScale_eventually_ne_zero beta)
      C.below_asymptotic
      C.above_negligible
  rw [EconCSLib.Math.AsymptoticEquivalent] at hsum ⊢
  refine Tendsto.congr' ?_ hsum
  filter_upwards [C.split] with a hsplit
  rw [hsplit]

end BoundedLemmaD2SplitIntegralAsymptoticCertificate

/--
Finite-index split certificate for the actual bounded Lemma D.2 integral
terms.
-/
structure BoundedLemmaD2SplitIntegralFiniteCertificate
    (beta c : ℝ) (k : ℕ) (G : ℝ → ℝ) where
  k_pos : 0 < k
  fixed :
    ∀ p : BoundedLemmaD2Index k,
      BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G p.2.val

namespace BoundedLemmaD2SplitIntegralFiniteCertificate

/--
Finite-index paper-style split certificate directly from the bounded-tail
limit, local CDF power bounds, and bounded-support geometric tail control.
-/
noncomputable def ofLocalCDFPowerBoundsAndGeometricTail
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ} {delta M p A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G where
  k_pos := k_pos
  fixed := by
    intro q
    exact
      BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofLocalCDFPowerBoundsAndGeometricTail
        tail hdelta_pos hdeltaM hA_pos hB_nonneg hp_pos hp_lt_one
        hG_measurable hG_nonneg hG_le_one hG_lower hG_upper
        hG_eq_one_of_support hp_le_G_on_tail

/--
Finite-index split certificate from the bounded-tail CDF asymptotic,
monotonicity of the reflected CDF, and bounded support.
-/
noncomputable def ofCDFPowerSandwichMonotoneBoundedSupport
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ} {M : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM_pos : 0 < M)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1) :
    BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G where
  k_pos := k_pos
  fixed := by
    intro q
    exact
      BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofCDFPowerSandwichMonotoneBoundedSupport
        tail hM_pos hG_measurable hG_mono hG_nonneg hG_le_one
        hG_eq_one_of_support

/--
The finite split certificate supplies the exact-coefficient integral
asymptotic certificate consumed downstream.
-/
noncomputable def toLimitIntegralAsymptoticCertificate
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G) :
    BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G where
  beta_pos := by
    let p0 : BoundedLemmaD2Index k := ⟨⟨0, C.k_pos⟩, ⟨0, by simp⟩⟩
    exact (C.fixed p0).beta_pos
  c_pos := by
    let p0 : BoundedLemmaD2Index k := ⟨⟨0, C.k_pos⟩, ⟨0, by simp⟩⟩
    exact (C.fixed p0).c_pos
  k_pos := C.k_pos
  term_asymptotic := by
    intro p
    simpa [boundedLemmaD2IndexedIntegralTerm] using
      (C.fixed p).integralTerm_asymptoticEquivalent

end BoundedLemmaD2SplitIntegralFiniteCertificate

/--
Finite-index dominated-convergence certificate for the actual bounded
Lemma D.2 integral terms. This is the formal version of the paper's remaining
analytic work after the pointwise rescaled-kernel limit.
-/
structure BoundedLemmaD2DominatedIntegralAsymptoticCertificate
    (beta c : ℝ) (k : ℕ) (G : ℝ → ℝ) where
  tail : BoundedTailCDFPowerSandwich G beta c
  k_pos : 0 < k
  change_of_variables :
    ∀ p : BoundedLemmaD2Index k,
      ∀ᶠ a in atTop,
        boundedLemmaD2IntegralTerm G p.2.val a =
          boundedTailScale beta a *
            ∫ y in Set.Ioi (0 : ℝ),
              boundedLemmaD2RescaledKernel G beta p.2.val a y
  kernel_measurable :
    ∀ p : BoundedLemmaD2Index k,
      ∀ᶠ a in atTop,
        MeasureTheory.AEStronglyMeasurable
          (fun y : ℝ => boundedLemmaD2RescaledKernel G beta p.2.val a y)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  bound : BoundedLemmaD2Index k → ℝ → ℝ
  bound_integrable :
    ∀ p : BoundedLemmaD2Index k,
      MeasureTheory.Integrable (bound p)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  kernel_bound :
    ∀ p : BoundedLemmaD2Index k,
      ∀ᶠ a in atTop,
        ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
          ‖boundedLemmaD2RescaledKernel G beta p.2.val a y‖ ≤ bound p y

namespace BoundedLemmaD2DominatedIntegralAsymptoticCertificate

/--
Build the finite-index dominated-convergence certificate from measurability of
the reflected CDF and integrable envelopes for each fixed paper index. The
change-of-variables and kernel-measurability fields are derived automatically.
-/
noncomputable def ofMeasurableBound
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hG : Measurable G)
    (bound : BoundedLemmaD2Index k → ℝ → ℝ)
    (bound_integrable :
      ∀ p : BoundedLemmaD2Index k,
        MeasureTheory.Integrable (bound p)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (kernel_bound :
      ∀ p : BoundedLemmaD2Index k,
        ∀ᶠ a in atTop,
          ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
            ‖boundedLemmaD2RescaledKernel G beta p.2.val a y‖ ≤ bound p y) :
    BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G where
  tail := tail
  k_pos := k_pos
  change_of_variables := by
    intro p
    exact boundedLemmaD2IntegralTerm_eventually_changeOfVariables
      G beta p.2.val
  kernel_measurable := by
    intro p
    filter_upwards with a
    exact boundedLemmaD2RescaledKernel_aestronglyMeasurable
      hG beta p.2.val a
  bound := bound
  bound_integrable := bound_integrable
  kernel_bound := kernel_bound

/-- The finite-index certificate gives a per-rank dominated-kernel certificate. -/
noncomputable def fixedCertificate
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G)
    (p : BoundedLemmaD2Index k) :
    BoundedLemmaD2DominatedKernelCertificate beta c G p.2.val where
  tail := C.tail
  change_of_variables := C.change_of_variables p
  kernel_measurable := C.kernel_measurable p
  bound := C.bound p
  bound_integrable := C.bound_integrable p
  kernel_bound := C.kernel_bound p

/--
The finite-index dominated certificate plus a common bounded-support geometric
tail estimate supplies the paper-style split finite certificate through the
growing near-zero rescaled interval.
-/
noncomputable def toSplitIntegralFiniteCertificateOfGeometricTailViaGrowing
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G)
    {delta M p : ℝ}
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G where
  k_pos := C.k_pos
  fixed := by
    intro q
    exact
      BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofDominatedKernelAndGeometricTailViaGrowing
        (C.fixedCertificate q) hdelta_pos hdeltaM hp_pos hp_lt_one
        hG_measurable hG_nonneg hG_le_one hG_eq_one_of_support
        hp_le_G_on_tail

/--
The dominated-convergence certificate supplies the sharper exact-coefficient
integral asymptotic certificate consumed by the finite-sum assembly.
-/
noncomputable def toLimitIntegralAsymptoticCertificate
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G) :
    BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G where
  beta_pos := C.tail.beta_pos
  c_pos := C.tail.c_pos
  k_pos := C.k_pos
  term_asymptotic := by
    intro p
    simpa [boundedLemmaD2IndexedIntegralTerm] using
      (C.fixedCertificate p).integralTerm_asymptoticEquivalent

end BoundedLemmaD2DominatedIntegralAsymptoticCertificate

/--
Eventual sandwich for the actual source integral terms, derived from the
integral asymptotic certificate.
-/
theorem boundedLemmaD2IntegralAsymptoticCertificate_eventually_integral_sandwich
    {beta : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2IntegralAsymptoticCertificate beta k G)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in atTop,
      ∀ p : BoundedLemmaD2Index k,
        (1 - ε) * (C.coeff p * boundedTailScale beta a) ≤
            boundedLemmaD2IndexedIntegralTerm G p a ∧
          boundedLemmaD2IndexedIntegralTerm G p a ≤
            (1 + ε) * (C.coeff p * boundedTailScale beta a) :=
  C.eventually_all_term_sandwich hε

/--
Formalized finite-sum conclusion after Lemma D.2: once every fixed rank/index
integral has the paper's `a^(-1 / beta)` asymptotic, their double sum has the
same scale with coefficient equal to the sum of the fixed coefficients.
-/
theorem boundedLemmaD2TopKLoss_asymptoticEquivalent
    {beta : ℝ} {k : ℕ}
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (C : BoundedLemmaD2FiniteSumCertificate beta k term) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k term)
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale beta a) := by
  exact finite_sum_asymptoticEquivalent_common_scale
    term C.coeff (boundedTailScale beta)
    (fun p => ne_of_gt (C.coeff_pos p))
    (ne_of_gt C.totalCoeff_pos)
    (boundedTailScale_eventually_ne_zero beta)
    C.term_asymptotic

/-- The certificate's total coefficient is the matching nested sum. -/
theorem boundedLemmaD2FiniteSumCertificate_totalCoeff_eq_nested_sum
    {beta : ℝ} {k : ℕ}
    {term : BoundedLemmaD2Index k → ℕ → ℝ}
    (C : BoundedLemmaD2FiniteSumCertificate beta k term) :
    (∑ p : BoundedLemmaD2Index k, C.coeff p) =
      ∑ i : Fin k, ∑ j : Fin (i.val + 1), C.coeff ⟨i, j⟩ := by
  rw [Fintype.sum_sigma]

/--
Nested-sum version of the Lemma D.2 finite assembly, matching the source
display with `i = 1, ..., k` and `j = 0, ..., i - 1`.
-/
theorem boundedLemmaD2NestedTopKLoss_asymptoticEquivalent
    {beta : ℝ} {k : ℕ}
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (C : BoundedLemmaD2FiniteSumCertificate beta k term) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => ∑ i : Fin k, ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a)
      (fun a =>
        (∑ i : Fin k, ∑ j : Fin (i.val + 1), C.coeff ⟨i, j⟩) *
          boundedTailScale beta a) := by
  have h := boundedLemmaD2TopKLoss_asymptoticEquivalent term C
  rw [EconCSLib.Math.AsymptoticEquivalent] at h ⊢
  refine Tendsto.congr' ?_ h
  filter_upwards with a
  rw [boundedLemmaD2TopKLoss_eq_nested_sum,
    boundedLemmaD2FiniteSumCertificate_totalCoeff_eq_nested_sum]

/--
Equations (91)-(96) assembled: reflection identities plus fixed-term Lemma
D.2 asymptotics imply the bounded top-`k` source loss
`M * k - h(a) ~ B * a^(-1/β)`.
-/
theorem boundedLemmaD2_reflected_source_loss_asymptoticEquivalent
    {beta M : ℝ} {k : ℕ}
    (sourceMean : Fin k → ℕ → ℝ)
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a)
    (C : BoundedLemmaD2FiniteSumCertificate beta k term) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale beta a) := by
  have h := boundedLemmaD2TopKLoss_asymptoticEquivalent term C
  rw [EconCSLib.Math.AsymptoticEquivalent] at h ⊢
  refine Tendsto.congr' ?_ h
  filter_upwards with a
  rw [boundedLemmaD2_reflection_loss_eq_topKLoss M sourceMean term hsource a]

/--
Actual-integral version of the Lemma D.2 finite assembly: a certificate for
the source integral terms yields the top-`k` bounded-loss asymptotic.
-/
theorem boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent
    {beta : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2IntegralAsymptoticCertificate beta k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale beta a) :=
  boundedLemmaD2TopKLoss_asymptoticEquivalent
    (boundedLemmaD2IndexedIntegralTerm G) C

/--
Equations (91)-(96) with the actual Lemma D.2 integral term. This is the
bounded branch's current analytic proof target: prove the integral certificate
for `G`, then this theorem gives the source loss asymptotic.
-/
theorem boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent
    {beta M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2IntegralAsymptoticCertificate beta k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale beta a) := by
  exact boundedLemmaD2_reflected_source_loss_asymptoticEquivalent
    sourceMean (boundedLemmaD2IndexedIntegralTerm G)
    (fun a i => by
      simpa [boundedLemmaD2IndexedIntegralTerm] using hsource a i)
    C

/--
Actual-integral finite assembly with the exact gamma limiting coefficients.
The only remaining source work is to prove the sharper certificate's
fixed-`j` integral asymptotics.
-/
theorem boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_limit_coeff_certificate
    {beta c : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent G
    C.toIntegralAsymptoticCertificate

/--
Equations (91)-(96) with the exact gamma limiting coefficients.
-/
theorem
    boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_limit_coeff_certificate
    {beta c M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent
    G sourceMean hsource C.toIntegralAsymptoticCertificate

/--
Actual-integral finite assembly from an explicit dominated-convergence and
change-of-variables certificate.
-/
theorem boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_dominated_certificate
    {beta c : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_limit_coeff_certificate
    G C.toLimitIntegralAsymptoticCertificate

/--
Equations (91)-(96) from an explicit dominated-convergence and
change-of-variables certificate.
-/
theorem
    boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_dominated_certificate
    {beta c M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_limit_coeff_certificate
    G sourceMean hsource C.toLimitIntegralAsymptoticCertificate

/--
Actual-integral finite assembly from the paper-style split certificate.
-/
theorem boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_split_certificate
    {beta c : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_limit_coeff_certificate
    G C.toLimitIntegralAsymptoticCertificate

/--
Equations (91)-(96) from the paper-style split certificate.
-/
theorem
    boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_split_certificate
    {beta c M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G) :
    EconCSLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_limit_coeff_certificate
    G sourceMean hsource C.toLimitIntegralAsymptoticCertificate

theorem boundedPowerMarginalModel_has_nonnegative_marginals
    {T : ℕ} (likelihood : ItemType T → ℝ) (beta : ℝ) :
    ((boundedPowerMarginalOracle T beta).toConsumptionModel likelihood 1).HasNonnegativeMarginals := by
  intro t q
  exact boundedPowerMarginalValue_forward_marginal_nonneg beta q

theorem boundedPowerMarginalModel_has_diminishing_returns
    {T : ℕ} (likelihood : ItemType T → ℝ) {beta : ℝ}
    (hbeta_pos : 0 < beta) :
    ((boundedPowerMarginalOracle T beta).toConsumptionModel likelihood 1).HasDiminishingReturns := by
  intro t q
  exact boundedPowerMarginalValue_marginal_antitone_step hbeta_pos q

/-- Finite-prefix error for the exact bounded power-marginal FOC proof. -/
noncomputable def boundedPowerMarginalError {T : ℕ}
    (likelihood : ItemType T → ℝ) (beta : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then 0 else
    ((∑ t : ItemType T, 1 / (likelihood t ^ (beta / (beta + 1)))) + 1) /
      (N : ℝ)

theorem boundedPowerMarginalError_nonneg {T : ℕ}
    (likelihood : ItemType T → ℝ) (beta : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (N : ℕ) :
    0 ≤ boundedPowerMarginalError likelihood beta N := by
  by_cases hN : N = 0
  · simp [boundedPowerMarginalError, hN]
  · have hS_nonneg :
        0 ≤ ∑ t : ItemType T, 1 / (likelihood t ^ (beta / (beta + 1))) := by
      exact Finset.sum_nonneg
        (fun t _ => div_nonneg zero_le_one
          (le_of_lt (Real.rpow_pos_of_pos (hlike_pos t) (beta / (beta + 1)))))
    have hN_pos : 0 < (N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hN
    have hnum_nonneg :
        0 ≤ (∑ t : ItemType T, 1 / (likelihood t ^ (beta / (beta + 1)))) + 1 :=
      add_nonneg hS_nonneg zero_le_one
    rw [boundedPowerMarginalError, if_neg hN]
    exact div_nonneg hnum_nonneg (le_of_lt hN_pos)

theorem boundedPowerMarginalError_tends_to_zero {T : ℕ}
    (likelihood : ItemType T → ℝ) (beta : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    EconCSLib.Math.TendsToZero
      (boundedPowerMarginalError likelihood beta) := by
  let S : ℝ := (∑ t : ItemType T, 1 / (likelihood t ^ (beta / (beta + 1)))) + 1
  have hsum_nonneg :
      0 ≤ ∑ t : ItemType T, 1 / (likelihood t ^ (beta / (beta + 1))) := by
    exact Finset.sum_nonneg
      (fun t _ => div_nonneg zero_le_one
        (le_of_lt (Real.rpow_pos_of_pos (hlike_pos t) (beta / (beta + 1)))))
  have hS_pos : 0 < S := by
    dsimp [S]
    linarith
  refine EconCSLib.Math.TendsToZero_of_nonneg_le_const_div
    (boundedPowerMarginalError likelihood beta) hS_pos
    (boundedPowerMarginalError_nonneg likelihood beta hlike_pos) ?_
  intro N hN
  have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
  simp [boundedPowerMarginalError, hN_ne, S]

/--
Exact bounded power-marginal FOC certificate.

This closes the optimization layer for a top-one oracle with the paper's
bounded-support marginal decay exponent. The remaining source-specific
probability work is to derive these power-law marginals, or their asymptotic
equivalent, from the actual bounded order-statistic model.
-/
noncomputable def boundedPowerMarginalSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (beta : ℝ)
    (hbeta_pos : 0 < beta)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    PairwiseScaledSublinearFOCCertificate
      (fun _ =>
        (boundedPowerMarginalOracle T beta).toConsumptionModel likelihood 1)
      (fun t : ItemType T => likelihood t ^ (beta / (beta + 1)))
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) where
  weight_pos := by
    intro t
    exact Real.rpow_pos_of_pos (hlike_pos t) (beta / (beta + 1))
  targetShare_eq := by
    intro t
    have hnorm_pos :
        0 < ∑ i : ItemType T, likelihood i ^ (beta / (beta + 1)) := by
      exact Finset.sum_pos
        (fun i _ => Real.rpow_pos_of_pos (hlike_pos i) (beta / (beta + 1)))
        Finset.univ_nonempty
    exact gammaLikelihoodProfile_targetShare_eq likelihood (beta / (beta + 1)) t
      (ne_of_gt hnorm_pos)
  error := boundedPowerMarginalError likelihood beta
  error_nonneg := boundedPowerMarginalError_nonneg likelihood beta hlike_pos
  error_tends_to_zero :=
    boundedPowerMarginalError_tends_to_zero likelihood beta hlike_pos
  large_gap_backward_lt_forward := by
    intro N a hN _hopt src dst hgap
    let gamma : ℝ := beta / (beta + 1)
    let eta : ℝ := boundedMarginalExponent beta
    let weight : ItemType T → ℝ := fun t => likelihood t ^ gamma
    let S : ℝ := (∑ t : ItemType T, 1 / weight t) + 1
    have heta_pos : 0 < eta := by
      dsimp [eta]
      exact boundedMarginalExponent_pos hbeta_pos
    have hgamma_eq : 1 / eta = gamma := by
      dsimp [eta, gamma]
      exact boundedMarginalExponent_one_div_eq_gamma hbeta_pos
    have hweight_pos : ∀ t, 0 < weight t := by
      intro t
      dsimp [weight, gamma]
      exact Real.rpow_pos_of_pos (hlike_pos t) (beta / (beta + 1))
    have hS_pos : 0 < S := by
      dsimp [S]
      have hsum_nonneg :
          0 ≤ ∑ t : ItemType T, 1 / weight t := by
        exact Finset.sum_nonneg
          (fun t _ => div_nonneg zero_le_one (le_of_lt (hweight_pos t)))
      linarith
    have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
    have hN_real_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN_ne
    have hgapS :
        S <
          (a.count src : ℝ) / weight src -
            (a.count dst : ℝ) / weight dst := by
      have hmul :
          boundedPowerMarginalError likelihood beta N * (N : ℝ) = S := by
        simp [boundedPowerMarginalError, hN_ne, S, weight, gamma,
          hN_real_ne]
      simpa [hmul, weight, gamma] using hgap
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
          1 / weight dst ≤ ∑ t : ItemType T, 1 / weight t := by
        exact Finset.single_le_sum
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
        ((a.count dst + 1 : ℕ) : ℝ) / likelihood dst ^ (1 / eta) <
          (a.count src : ℝ) / likelihood src ^ (1 / eta) := by
      have hscaled' :
          ((a.count dst + 1 : ℕ) : ℝ) / weight dst <
            (a.count src : ℝ) / weight src := by
        simpa [Nat.cast_add, Nat.cast_one] using hscaled_add
      simpa [weight, gamma, hgamma_eq] using hscaled'
    have hmarginal_core :
        likelihood src * (1 * (a.count src : ℝ) ^ (-eta)) <
          likelihood dst *
            (1 * (((a.count dst + 1 : ℕ) : ℝ) ^ (-eta))) := by
      exact EconCSLib.Math.rpow_neg_marginal_lt_of_scaled_lt
        (c := 1) (eta := eta)
        (hlike_pos src) (hlike_pos dst) zero_lt_one heta_pos
        hqsrc_real_pos hqdst_succ_pos hscaled_for_power
    have hmarginal :
        likelihood src *
            ((a.count src : ℝ) ^ (-(boundedMarginalExponent beta))) <
          likelihood dst *
            (((a.count dst + 1 : ℕ) : ℝ) ^
              (-(boundedMarginalExponent beta))) := by
      simpa [eta] using hmarginal_core
    unfold ConsumptionModel.weightedBackwardMarginal
      ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
      EconCSLib.Allocation.marginal TopKValueOracle.toConsumptionModel
    rw [dif_neg hsrc_pos.ne']
    simp only [boundedPowerMarginalOracle, TopKValueOracle.common_expectedTopSum]
    rw [boundedPowerMarginalValue_backward_marginal beta hsrc_pos,
      boundedPowerMarginalValue_forward_marginal]
    exact hmarginal

end PRPKG24AccuracyDiversity
