import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

namespace EconCSLib
namespace Probability
namespace Exponential

open scoped BigOperators

/-!
# Exponential Distribution Model

Reusable wrappers around mathlib's exponential distribution on `ℝ`, plus the
standard harmonic closed form used by top-one exponential order-statistic
models.

## Main declarations

- `Model`: a positive-rate exponential distribution model.
- `Model.measure`: the mathlib exponential probability measure.
- `harmonicReal`: real harmonic numbers.
- `maxSurvivalOfRate`: analytic survival function for the maximum of `q`
  rate-`rate` exponential draws, expressed from the exponential CDF.
- `maxSurvivalOfRate_expansion`: binomial expansion of that survival function
  into finitely many exponential-tail terms.
- `integral_exp_neg_mul_Ioi`: the basic exponential-tail integral.
- `expectedMaxValueOfRate`: the standard closed-form expected maximum value
  `H_q / rate` for `q` i.i.d. rate-`rate` exponential draws.
-/

/-- A positive-rate exponential distribution model. -/
structure Model where
  rate : ℝ
  rate_pos : 0 < rate

namespace Model

/-- The mathlib exponential probability measure associated with a model. -/
noncomputable def measure (M : Model) : MeasureTheory.Measure ℝ :=
  ProbabilityTheory.expMeasure M.rate

theorem isProbabilityMeasure_measure (M : Model) :
    MeasureTheory.IsProbabilityMeasure M.measure :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure M.rate_pos

/-- CDF of the positive-rate exponential model. -/
theorem cdf_eq (M : Model) (x : ℝ) :
    ProbabilityTheory.cdf M.measure x =
      if 0 ≤ x then 1 - Real.exp (-(M.rate * x)) else 0 :=
  ProbabilityTheory.cdf_expMeasure_eq M.rate_pos x

/-- Real-valued PDF of the positive-rate exponential model. -/
noncomputable def pdfReal (M : Model) (x : ℝ) : ℝ :=
  ProbabilityTheory.exponentialPDFReal M.rate x

theorem pdfReal_nonneg (M : Model) (x : ℝ) :
    0 ≤ M.pdfReal x :=
  ProbabilityTheory.exponentialPDFReal_nonneg M.rate_pos x

theorem pdfReal_pos (M : Model) {x : ℝ} (hx : 0 < x) :
    0 < M.pdfReal x :=
  ProbabilityTheory.exponentialPDFReal_pos M.rate_pos hx

end Model

/-- Real harmonic numbers, indexed so `harmonicReal q = ∑_{j=1}^q 1 / j`. -/
noncomputable def harmonicReal (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range q, (1 : ℝ) / ((j + 1 : ℕ) : ℝ)

theorem harmonicReal_zero : harmonicReal 0 = 0 := by
  simp [harmonicReal]

theorem harmonicReal_succ (q : ℕ) :
    harmonicReal (q + 1) = harmonicReal q + (1 : ℝ) / ((q + 1 : ℕ) : ℝ) := by
  simp [harmonicReal, Finset.sum_range_succ]

theorem harmonicReal_eq_harmonic (q : ℕ) :
    harmonicReal q = (harmonic q : ℝ) := by
  simp [harmonicReal, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/--
Closed-form value for the expected maximum of `q` i.i.d. rate-`rate`
exponential draws.

This file records the standard closed form and its consequences. A future
order-statistic integration theorem can connect this value function directly to
`Model.measure`.
-/
noncomputable def expectedMaxValueOfRate (rate : ℝ) (q : ℕ) : ℝ :=
  (1 / rate) * harmonicReal q

theorem expectedMaxValueOfRate_forward_marginal
    (rate : ℝ) (q : ℕ) :
    expectedMaxValueOfRate rate (q + 1) -
        expectedMaxValueOfRate rate q =
      (1 / rate) * ((1 : ℝ) / ((q + 1 : ℕ) : ℝ)) := by
  rw [expectedMaxValueOfRate, expectedMaxValueOfRate, harmonicReal_succ]
  ring

theorem expectedMaxValueOfRate_backward_marginal
    (rate : ℝ) {q : ℕ} (hq : 0 < q) :
    expectedMaxValueOfRate rate q -
        expectedMaxValueOfRate rate (q - 1) =
      (1 / rate) * ((1 : ℝ) / (q : ℝ)) := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  nth_rewrite 1 [← hpred]
  rw [expectedMaxValueOfRate_forward_marginal]
  simp [hpred]

/--
The harmonic closed form differs from `(1/rate) * log q` by a convergent
Euler-Mascheroni constant term.
-/
theorem expectedMaxValueOfRate_sub_log_tendsto
    (rate : ℝ) :
    Filter.Tendsto
      (fun q : ℕ =>
        expectedMaxValueOfRate rate q -
          (1 / rate) * Real.log q)
      Filter.atTop
      (nhds ((1 / rate) * Real.eulerMascheroniConstant)) := by
  have h :=
    (Real.tendsto_harmonic_sub_log.const_mul (1 / rate))
  refine h.congr' ?_
  filter_upwards with q
  rw [expectedMaxValueOfRate, harmonicReal_eq_harmonic]
  ring

/-- Closed-form expected maximum value for a positive-rate model. -/
noncomputable def Model.expectedMaxValue (M : Model) (q : ℕ) : ℝ :=
  expectedMaxValueOfRate M.rate q

theorem Model.expectedMaxValue_forward_marginal
    (M : Model) (q : ℕ) :
    M.expectedMaxValue (q + 1) - M.expectedMaxValue q =
      (1 / M.rate) * ((1 : ℝ) / ((q + 1 : ℕ) : ℝ)) :=
  expectedMaxValueOfRate_forward_marginal M.rate q

theorem Model.expectedMaxValue_backward_marginal
    (M : Model) {q : ℕ} (hq : 0 < q) :
    M.expectedMaxValue q - M.expectedMaxValue (q - 1) =
      (1 / M.rate) * ((1 : ℝ) / (q : ℝ)) :=
  expectedMaxValueOfRate_backward_marginal M.rate hq

theorem Model.expectedMaxValue_sub_log_tendsto (M : Model) :
    Filter.Tendsto
      (fun q : ℕ =>
        M.expectedMaxValue q - (1 / M.rate) * Real.log q)
      Filter.atTop
      (nhds ((1 / M.rate) * Real.eulerMascheroniConstant)) :=
  expectedMaxValueOfRate_sub_log_tendsto M.rate

/-! ## Maximum survival algebra and the survival-integral base case -/

/--
Analytic survival function for the maximum of `q` independent exponential
draws, after substituting the exponential CDF on the nonnegative line:

`1 - (1 - exp (-rate*x))^q`.

The product-measure theorem connecting this expression to an actual iid maximum
is deliberately kept as a later order-statistic layer.
-/
noncomputable def maxSurvivalOfRate (rate : ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  1 - (1 - Real.exp (-(rate * x))) ^ q

/--
Binomial expansion of `maxSurvivalOfRate`.

The indexing follows mathlib's `sub_pow` orientation: the summation variable
`m = 0, ..., q-1` corresponds to exponential power `q - m`, so every term is an
integrable exponential tail when `q > 0`.
-/
theorem maxSurvivalOfRate_expansion
    (rate : ℝ) (q : ℕ) (x : ℝ) :
    maxSurvivalOfRate rate q x =
      - ∑ m ∈ Finset.range q,
          (-1 : ℝ) ^ (m + q) *
            (Real.exp (-(rate * x))) ^ (q - m) *
            (q.choose m : ℝ) := by
  unfold maxSurvivalOfRate
  have h :=
    sub_pow (1 : ℝ) (Real.exp (-(rate * x))) q
  rw [h, Finset.sum_range_succ]
  have hterm :
      (-1 : ℝ) ^ (q + q) * 1 ^ q *
          (Real.exp (-(rate * x))) ^ (q - q) *
          (q.choose q : ℝ) = 1 := by
    simp [Even.neg_one_pow (Even.add_self q)]
  rw [hterm]
  simp [mul_comm]

theorem maxSurvivalOfRate_one
    (rate x : ℝ) :
    maxSurvivalOfRate rate 1 x = Real.exp (-(rate * x)) := by
  simp [maxSurvivalOfRate]

theorem exp_neg_mul_pow_nat
    (rate x : ℝ) (n : ℕ) :
    (Real.exp (-(rate * x))) ^ n =
      Real.exp (-(((n : ℝ) * rate) * x)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

/--
Basic exponential-tail integral:

`∫_0^∞ exp (-rate * x) dx = 1 / rate`.

This is the analytic base case for deriving exponential expected-max formulas
from the distribution model rather than merely naming the harmonic closed form.
-/
theorem integral_exp_neg_mul_Ioi
    (rate : ℝ) (hrate : 0 < rate) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(rate * x)) = 1 / rate := by
  have h :=
    integral_exp_neg_mul_rpow (p := 1) (b := rate) (by norm_num) hrate
  norm_num [Real.rpow_one, Real.rpow_neg_one, Real.Gamma_nat_eq_factorial,
    div_eq_mul_inv, neg_mul, one_div] at h ⊢
  exact h

/--
Integrability of a positive natural power of an exponential survival term on
`(0,∞)`.
-/
theorem integrableOn_exp_neg_mul_pow_Ioi
    (rate : ℝ) (hrate : 0 < rate) {n : ℕ} (hn : 0 < n) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => (Real.exp (-(rate * x))) ^ n)
      (Set.Ioi (0 : ℝ)) := by
  have hnrate_pos : 0 < (n : ℝ) * rate :=
    mul_pos (by exact_mod_cast hn) hrate
  exact
    (exp_neg_integrableOn_Ioi (0 : ℝ) hnrate_pos).congr_fun
      (fun x _hx => by
        rw [show -((n : ℝ) * rate) * x =
            -(((n : ℝ) * rate) * x) by ring]
        exact (exp_neg_mul_pow_nat rate x n).symm)
      measurableSet_Ioi

/--
Integral of a positive natural power of an exponential survival term.

This is the termwise integral needed after expanding the maximum survival
function by the binomial theorem.
-/
theorem integral_exp_neg_mul_pow_Ioi
    (rate : ℝ) (hrate : 0 < rate) {n : ℕ} (hn : 0 < n) :
    ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-(rate * x))) ^ n =
      1 / ((n : ℝ) * rate) := by
  have hnrate_pos : 0 < (n : ℝ) * rate :=
    mul_pos (by exact_mod_cast hn) hrate
  calc
    ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-(rate * x))) ^ n
        = ∫ x in Set.Ioi (0 : ℝ),
            Real.exp (-(((n : ℝ) * rate) * x)) := by
          refine MeasureTheory.setIntegral_congr_fun
            measurableSet_Ioi ?_
          intro x _hx
          exact exp_neg_mul_pow_nat rate x n
    _ = 1 / ((n : ℝ) * rate) :=
          integral_exp_neg_mul_Ioi ((n : ℝ) * rate) hnrate_pos

/--
Integral of the analytic maximum-survival expression, after the binomial
expansion and termwise exponential-tail integration.

The remaining combinatorial step toward `H_q / rate` is to identify this
finite alternating binomial sum with the harmonic number.
-/
theorem maxSurvivalOfRate_integral_eq_finite_sum
    (rate : ℝ) (hrate : 0 < rate) (q : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), maxSurvivalOfRate rate q x =
      - ∑ m ∈ Finset.range q,
          ((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
            (1 / (((q - m : ℕ) : ℝ) * rate)) := by
  have hcongr :
      ∫ x in Set.Ioi (0 : ℝ), maxSurvivalOfRate rate q x =
        ∫ x in Set.Ioi (0 : ℝ),
          - ∑ m ∈ Finset.range q,
            (-1 : ℝ) ^ (m + q) *
              (Real.exp (-(rate * x))) ^ (q - m) *
              (q.choose m : ℝ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _hx
    rw [maxSurvivalOfRate_expansion]
  rw [hcongr]
  rw [MeasureTheory.integral_neg]
  rw [MeasureTheory.integral_finset_sum]
  · congr 1
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hn : 0 < q - m :=
      Nat.sub_pos_of_lt (Finset.mem_range.mp hm)
    have hterm :
        ∫ x in Set.Ioi (0 : ℝ),
            (-1 : ℝ) ^ (m + q) *
              (Real.exp (-(rate * x))) ^ (q - m) *
              (q.choose m : ℝ) =
          ∫ x in Set.Ioi (0 : ℝ),
            (((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
              (Real.exp (-(rate * x))) ^ (q - m)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro x _hx
      ring
    rw [hterm]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_exp_neg_mul_pow_Ioi rate hrate hn]
  · intro m hm
    have hn : 0 < q - m :=
      Nat.sub_pos_of_lt (Finset.mem_range.mp hm)
    have hbase := integrableOn_exp_neg_mul_pow_Ioi rate hrate hn
    have hconst : MeasureTheory.Integrable
        (fun x : ℝ =>
          (((-1 : ℝ) ^ (m + q) * (q.choose m : ℝ)) *
            (Real.exp (-(rate * x))) ^ (q - m)))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      hbase.const_mul _
    refine hconst.congr ?_
    filter_upwards with x
    ring

theorem expectedMaxValueOfRate_one (rate : ℝ) :
    expectedMaxValueOfRate rate 1 = 1 / rate := by
  norm_num [expectedMaxValueOfRate, harmonicReal]

theorem Model.one_minus_cdf_eq_exp_neg_mul
    (M : Model) {x : ℝ} (hx : 0 ≤ x) :
    1 - ProbabilityTheory.cdf M.measure x =
      Real.exp (-(M.rate * x)) := by
  rw [M.cdf_eq x, if_pos hx]
  ring

/--
For one draw from the positive-rate exponential model, integrating the survival
function over the nonnegative line gives the same value as the harmonic
expected-maximum formula.

This is the `q = 1` measure-facing checkpoint for the top-one exponential
branch; the general `q` maximum still needs the product-measure/order-statistic
survival formula.
-/
theorem Model.singleDrawSurvivalIntegral_eq_expectedMaxValue
    (M : Model) :
    ∫ x in Set.Ioi (0 : ℝ), (1 - ProbabilityTheory.cdf M.measure x) =
      M.expectedMaxValue 1 := by
  have hsurv :
      ∫ x in Set.Ioi (0 : ℝ), (1 - ProbabilityTheory.cdf M.measure x) =
        ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(M.rate * x)) := by
    refine MeasureTheory.setIntegral_congr_fun
      measurableSet_Ioi ?_
    intro x hx
    exact M.one_minus_cdf_eq_exp_neg_mul (le_of_lt hx)
  rw [hsurv, integral_exp_neg_mul_Ioi M.rate M.rate_pos,
    Model.expectedMaxValue, expectedMaxValueOfRate_one]

end Exponential
end Probability
end EconCSLib
