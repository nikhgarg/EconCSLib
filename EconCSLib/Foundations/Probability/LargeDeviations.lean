import EconCSLib.Foundations.Probability.FiniteSupportMGF
import EconCSLib.Foundations.Math.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

open Filter Topology
open scoped BigOperators

namespace EconCSLib
namespace Probability

noncomputable section

/-!
# Large-Deviation Certificate Interfaces

Reusable certificate-level infrastructure for EC papers that use exponential
convergence rates but where the analytic theorem itself is best supplied as a
paper-local or distribution-family certificate.

The motivating pattern is the rating-system large-deviation proof:

1. prove or assume a pairwise sample-mean ranking error has exponent `r`;
2. aggregate finitely many pairwise errors;
3. use that finite sums/unions preserve the minimum exponent.

This file formalizes the reusable algebra around steps 2 and 3.

## Main declarations

- `logDecay`
- `HasExponentialRate`
- `ExponentialRateCertificate`
- `HasExpUpperBoundWithConst`
- `HasExpLowerBoundWithConst`
- `ExponentialRateCertificate.hasExpUpperBoundWithConst_of_lt`
- `ExponentialRateCertificate.hasExpLowerBoundWithConst_of_gt`
- `finite_weighted_sum_hasExpUpperBoundWithConst`
- `finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates`
- `finite_weighted_sum_hasExpLowerBoundWithConst_of_component`
- `finite_weighted_sum_hasExpLowerBoundWithConst_of_rate_certificate_component`
- `FiniteErrorRateCertificate`
- `PairwiseErrorUpperBoundCertificate`
- `PairwiseErrorRateCertificate`
-/

/-- Paper-style negative normalized log sequence, `- log(p n) / n`. -/
def logDecay (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  -((n : ℝ)⁻¹) * Real.log (p n)

/-- `p n` has exponential decay rate `rate`. -/
def HasExponentialRate (p : ℕ → ℝ) (rate : ℝ) : Prop :=
  Tendsto (logDecay p) atTop (nhds rate)

/--
Certificate that a nonnegative error probability sequence has a named
exponential decay rate.
-/
structure ExponentialRateCertificate (p : ℕ → ℝ) (rate : ℝ) where
  eventually_pos : ∀ᶠ n in atTop, 0 < p n
  has_rate : HasExponentialRate p rate

/--
Eventual exponential upper bound with an arbitrary positive prefactor:
`p n <= C * exp(-n * rate)` eventually.
-/
def HasExpUpperBoundWithConst (p : ℕ → ℝ) (rate : ℝ) : Prop :=
  ∃ C > 0, ∀ᶠ n in atTop,
    0 ≤ p n ∧ p n ≤ C * Real.exp (-(n : ℝ) * rate)

/--
Eventual exponential lower bound with an arbitrary positive prefactor:
`c * exp(-n * rate) <= p n` eventually.
-/
def HasExpLowerBoundWithConst (p : ℕ → ℝ) (rate : ℝ) : Prop :=
  ∃ c > 0, ∀ᶠ n : ℕ in atTop,
    c * Real.exp (-(n : ℝ) * rate) ≤ p n

namespace HasExpUpperBoundWithConst

theorem of_eventually_le {p : ℕ → ℝ} {rate C : ℝ}
    (hC : 0 < C)
    (hbound : ∀ᶠ n in atTop,
      0 ≤ p n ∧ p n ≤ C * Real.exp (-(n : ℝ) * rate)) :
    HasExpUpperBoundWithConst p rate :=
  ⟨C, hC, hbound⟩

theorem of_eventually_zero {p : ℕ → ℝ} {rate : ℝ}
    (hzero : ∀ᶠ n in atTop, p n = 0) :
    HasExpUpperBoundWithConst p rate := by
  refine of_eventually_le (C := 1) (by norm_num) ?_
  filter_upwards [hzero] with n hn
  constructor
  · simp [hn]
  · have hexp_nonneg : 0 ≤ Real.exp (-(n : ℝ) * rate) :=
      (Real.exp_pos _).le
    simpa [hn] using hexp_nonneg

theorem weaken_rate {p : ℕ → ℝ} {rate strongRate : ℝ}
    (h : HasExpUpperBoundWithConst p strongRate)
    (hrate : rate ≤ strongRate) :
    HasExpUpperBoundWithConst p rate := by
  rcases h with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hC] with n hn
  refine ⟨hn.1, ?_⟩
  have hexp :
      Real.exp (-(n : ℝ) * strongRate) ≤
        Real.exp (-(n : ℝ) * rate) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hrate
      (neg_nonpos.mpr (Nat.cast_nonneg n))
  exact hn.2.trans
    (mul_le_mul_of_nonneg_left hexp hCpos.le)

theorem const_mul {p : ℕ → ℝ} {rate c : ℝ}
    (h : HasExpUpperBoundWithConst p rate) (hc : 0 ≤ c) :
    HasExpUpperBoundWithConst (fun n => c * p n) rate := by
  rcases h with ⟨C, hCpos, hC⟩
  refine ⟨(c + 1) * C, mul_pos (by linarith) hCpos, ?_⟩
  filter_upwards [hC] with n hn
  have hnonneg : 0 ≤ c * p n := mul_nonneg hc hn.1
  refine ⟨hnonneg, ?_⟩
  have hmain :
      c * p n ≤ c * (C * Real.exp (-(n : ℝ) * rate)) :=
    mul_le_mul_of_nonneg_left hn.2 hc
  have hcoef :
      c * C ≤ (c + 1) * C := by
    exact mul_le_mul_of_nonneg_right (by linarith) hCpos.le
  calc
    c * p n ≤ c * (C * Real.exp (-(n : ℝ) * rate)) := hmain
    _ = (c * C) * Real.exp (-(n : ℝ) * rate) := by ring
    _ ≤ ((c + 1) * C) * Real.exp (-(n : ℝ) * rate) := by
      exact mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le

theorem tendsto_zero_of_pos_rate {p : ℕ → ℝ} {rate : ℝ}
    (h : HasExpUpperBoundWithConst p rate) (hrate : 0 < rate) :
    Tendsto p atTop (nhds 0) := by
  rcases h with ⟨C, hCpos, hCevent⟩
  let rho : ℝ := Real.exp (-rate)
  have hrho_nonneg : 0 ≤ rho := (Real.exp_pos _).le
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hpow : Tendsto (fun n : ℕ => rho ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hrho_nonneg hrho_lt_one
  have hexp_zero :
      Tendsto
        (fun n : ℕ => C * Real.exp (-(n : ℝ) * rate))
        atTop (nhds 0) := by
    have hCpow : Tendsto (fun n : ℕ => C * rho ^ n) atTop (nhds 0) := by
      simpa using hpow.const_mul C
    refine hCpow.congr' ?_
    filter_upwards with n
    dsimp [rho]
    rw [← Real.exp_nat_mul]
    congr 1
    ring_nf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hexp_zero ?_ ?_
  · filter_upwards [hCevent] with n hn
    exact hn.1
  · filter_upwards [hCevent] with n hn
    exact hn.2

end HasExpUpperBoundWithConst

namespace HasExpLowerBoundWithConst

theorem of_eventually_ge {p : ℕ → ℝ} {rate c : ℝ}
    (hc : 0 < c)
    (hbound : ∀ᶠ n : ℕ in atTop,
      c * Real.exp (-(n : ℝ) * rate) ≤ p n) :
    HasExpLowerBoundWithConst p rate :=
  ⟨c, hc, hbound⟩

theorem weaken_rate {p : ℕ → ℝ} {rate weakRate : ℝ}
    (h : HasExpLowerBoundWithConst p rate)
    (hrate : rate ≤ weakRate) :
    HasExpLowerBoundWithConst p weakRate := by
  rcases h with ⟨c, hcpos, hc⟩
  refine ⟨c, hcpos, ?_⟩
  filter_upwards [hc] with n hn
  have hexp :
      Real.exp (-(n : ℝ) * weakRate) ≤
        Real.exp (-(n : ℝ) * rate) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hrate
      (neg_nonpos.mpr (Nat.cast_nonneg n))
  exact (mul_le_mul_of_nonneg_left hexp hcpos.le).trans hn

theorem const_mul {p : ℕ → ℝ} {rate c : ℝ}
    (h : HasExpLowerBoundWithConst p rate) (hc : 0 < c) :
    HasExpLowerBoundWithConst (fun n => c * p n) rate := by
  rcases h with ⟨C, hCpos, hC⟩
  refine ⟨c * C, mul_pos hc hCpos, ?_⟩
  filter_upwards [hC] with n hn
  have hmain :
      c * (C * Real.exp (-(n : ℝ) * rate)) ≤ c * p n :=
    mul_le_mul_of_nonneg_left hn hc.le
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmain

/--
An eventual polynomially corrected geometric lower bound implies every
exponential lower bound with any strictly slower rate.

This is the reusable final step after a finite-type or multinomial argument
has produced a lower bound like `c * r^n / (n+1)^d`.
-/
theorem of_eventually_geometric_div_polynomial_lower
    {p : ℕ → ℝ} {c r targetRate : ℝ} (d : ℕ)
    (hc : 0 < c) (hr_pos : 0 < r)
    (htarget : -Real.log r < targetRate)
    (hlower : ∀ᶠ n : ℕ in atTop,
      c * r ^ n / (((n.succ : ℕ) : ℝ) ^ d) ≤ p n) :
    HasExpLowerBoundWithConst p targetRate := by
  refine ⟨c, hc, ?_⟩
  let delta : ℝ := targetRate + Real.log r
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    linarith
  let rho : ℝ := Real.exp (-delta)
  have hrho_pos : 0 < rho := Real.exp_pos _
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have htend_succ_base :
      Tendsto
        (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ d) * rho ^ (m + 1))
        atTop (nhds 0) :=
    (tendsto_pow_const_mul_const_pow_of_lt_one d hrho_pos.le hrho_lt_one).comp
      (tendsto_add_atTop_nat 1)
  have htend_succ :
      Tendsto
        (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ d) * rho ^ m)
        atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun m : ℕ =>
            rho⁻¹ * ((((m + 1 : ℕ) : ℝ) ^ d) * rho ^ (m + 1)))
          atTop (nhds 0) := by
      simpa using htend_succ_base.const_mul rho⁻¹
    refine hmul.congr' ?_
    filter_upwards with m
    show rho⁻¹ * ((((m + 1 : ℕ) : ℝ) ^ d) * rho ^ (m + 1)) =
      (((m + 1 : ℕ) : ℝ) ^ d) * rho ^ m
    rw [pow_succ]
    field_simp [hrho_pos.ne']
  have hevent_small :
      ∀ᶠ n : ℕ in atTop,
        (((n.succ : ℕ) : ℝ) ^ d) * rho ^ n ≤ 1 := by
    have h := htend_succ.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h] with n hn
    simpa [Nat.succ_eq_add_one] using hn
  filter_upwards [hlower, hevent_small] with n hn hsmall
  have hden_pos : 0 < (((n.succ : ℕ) : ℝ) ^ d) := by
    positivity
  have hpow_r : r ^ n = Real.exp ((n : ℝ) * Real.log r) := by
    calc
      r ^ n = (Real.exp (Real.log r)) ^ n := by
        rw [Real.exp_log hr_pos]
      _ = Real.exp ((n : ℝ) * Real.log r) := by
        rw [Real.exp_nat_mul]
  have hrho_pow : rho ^ n = Real.exp (-(n : ℝ) * delta) := by
    dsimp [rho]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hratio :
      (((n.succ : ℕ) : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * targetRate) ≤ r ^ n := by
    have hsmall_exp :
        (((n.succ : ℕ) : ℝ) ^ d) *
            Real.exp (-(n : ℝ) * delta) ≤ 1 := by
      simpa [hrho_pow] using hsmall
    have hrpow_pos : 0 < r ^ n := pow_pos hr_pos n
    have hmul := mul_le_mul_of_nonneg_right hsmall_exp hrpow_pos.le
    calc
      (((n.succ : ℕ) : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * targetRate)
          =
        (((n.succ : ℕ) : ℝ) ^ d) *
          Real.exp (-(n : ℝ) * delta + (n : ℝ) * Real.log r) := by
            congr 1
            congr 1
            dsimp [delta]
            ring
      _ =
        (((n.succ : ℕ) : ℝ) ^ d) *
          (Real.exp (-(n : ℝ) * delta) *
            Real.exp ((n : ℝ) * Real.log r)) := by
            rw [Real.exp_add]
      _ =
        ((((n.succ : ℕ) : ℝ) ^ d) *
            Real.exp (-(n : ℝ) * delta)) * r ^ n := by
            rw [hpow_r]
            ring
      _ ≤ 1 * r ^ n := hmul
      _ = r ^ n := by ring
  have hmain :
      c * Real.exp (-(n : ℝ) * targetRate) ≤
        c * r ^ n / (((n.succ : ℕ) : ℝ) ^ d) := by
    have hdiv :
        Real.exp (-(n : ℝ) * targetRate) ≤
          r ^ n / (((n.succ : ℕ) : ℝ) ^ d) := by
      rw [le_div_iff₀ hden_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hratio
    have hmul := mul_le_mul_of_nonneg_left hdiv hc.le
    simpa [mul_div_assoc, mul_assoc] using hmul
  exact hmain.trans hn

end HasExpLowerBoundWithConst

/--
If a positive sequence has exponential upper bounds at every rate below `rate`
and exponential lower bounds at every rate above `rate`, then its paper-style
normalized log decay converges to `rate`.
-/
theorem hasExponentialRate_of_expUpperLowerBounds
    {p : ℕ → ℝ} {rate : ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < p n)
    (hupper : ∀ targetRate, targetRate < rate →
      HasExpUpperBoundWithConst p targetRate)
    (hlower : ∀ targetRate, rate < targetRate →
      HasExpLowerBoundWithConst p targetRate) :
    HasExponentialRate p rate := by
  rw [HasExponentialRate]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let mid : ℝ := (a + rate) / 2
    have ha_mid : a < mid := by dsimp [mid]; linarith
    have hmid_rate : mid < rate := by dsimp [mid]; linarith
    rcases hupper mid hmid_rate with ⟨C, hCpos, hCevent⟩
    have hdiv_tendsto :
        Tendsto (fun n : ℕ => Real.log C / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (Real.log C)
    have hdelta : 0 < mid - a := by linarith
    have hdiv_event : ∀ᶠ n : ℕ in atTop,
        Real.log C / (n : ℝ) < mid - a :=
      hdiv_tendsto.eventually_lt_const hdelta
    filter_upwards [hpos, hCevent, hdiv_event, eventually_gt_atTop 0]
      with n hp_pos hC hdiv hn
    have hnreal_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlog_le :
        Real.log (p n) ≤ Real.log C + (-(n : ℝ) * mid) := by
      have hlog_bound := Real.log_le_log hp_pos hC.2
      rw [Real.log_mul hCpos.ne' (Real.exp_pos _).ne',
        Real.log_exp] at hlog_bound
      exact hlog_bound
    have hdiv_le :
        Real.log (p n) / (n : ℝ) ≤
          (Real.log C + (-(n : ℝ) * mid)) / (n : ℝ) :=
      div_le_div_of_nonneg_right hlog_le hnreal_pos.le
    have hupper_norm :
        -((Real.log C + (-(n : ℝ) * mid)) / (n : ℝ)) =
          mid - Real.log C / (n : ℝ) := by
      field_simp [hnreal_pos.ne']
      ring
    have hlogDecay_eq :
        logDecay p n = -(Real.log (p n) / (n : ℝ)) := by
      dsimp [logDecay]
      field_simp [hnreal_pos.ne']
    have hdecay_ge :
        mid - Real.log C / (n : ℝ) ≤ logDecay p n := by
      rw [← hupper_norm, hlogDecay_eq]
      exact neg_le_neg hdiv_le
    exact lt_of_lt_of_le (by linarith) hdecay_ge
  · intro b hb
    let mid : ℝ := (rate + b) / 2
    have hrate_mid : rate < mid := by dsimp [mid]; linarith
    have hmid_b : mid < b := by dsimp [mid]; linarith
    rcases hlower mid hrate_mid with ⟨c, hcpos, hcevent⟩
    have hdiv_tendsto :
        Tendsto (fun n : ℕ => Real.log c / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (Real.log c)
    have hdelta : 0 < b - mid := by linarith
    have hdiv_event : ∀ᶠ n : ℕ in atTop,
        -(Real.log c / (n : ℝ)) < b - mid := by
      have hneg_tendsto :
          Tendsto (fun n : ℕ => -(Real.log c / (n : ℝ)))
            atTop (nhds 0) := by
        simpa using hdiv_tendsto.neg
      exact hneg_tendsto.eventually_lt_const hdelta
    filter_upwards [hpos, hcevent, hdiv_event, eventually_gt_atTop 0]
      with n hp_pos hc hdiv hn
    have hnreal_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlower_pos : 0 < c * Real.exp (-(n : ℝ) * mid) :=
      mul_pos hcpos (Real.exp_pos _)
    have hlog_lower :
        Real.log c + (-(n : ℝ) * mid) ≤ Real.log (p n) := by
      have hlog_bound := Real.log_le_log hlower_pos hc
      rw [Real.log_mul hcpos.ne' (Real.exp_pos _).ne',
        Real.log_exp] at hlog_bound
      exact hlog_bound
    have hdiv_le :
        (Real.log c + (-(n : ℝ) * mid)) / (n : ℝ) ≤
          Real.log (p n) / (n : ℝ) :=
      div_le_div_of_nonneg_right hlog_lower hnreal_pos.le
    have hlower_norm :
        -((Real.log c + (-(n : ℝ) * mid)) / (n : ℝ)) =
          mid - Real.log c / (n : ℝ) := by
      field_simp [hnreal_pos.ne']
      ring
    have hlogDecay_eq :
        logDecay p n = -(Real.log (p n) / (n : ℝ)) := by
      dsimp [logDecay]
      field_simp [hnreal_pos.ne']
    have hdecay_le :
        logDecay p n ≤ mid - Real.log c / (n : ℝ) := by
      rw [hlogDecay_eq, ← hlower_norm]
      exact neg_le_neg hdiv_le
    exact lt_of_le_of_lt hdecay_le (by linarith)

namespace ExponentialRateCertificate

/--
An exact exponential-rate certificate gives an eventual exponential upper
bound at every strictly smaller rate. This is the standard bridge from
`-log p_n / n -> r` to `p_n <= exp(-n * r')` for `r' < r`.
-/
theorem hasExpUpperBoundWithConst_of_lt
    {p : ℕ → ℝ} {rate targetRate : ℝ}
    (h : ExponentialRateCertificate p rate)
    (htarget : targetRate < rate) :
    HasExpUpperBoundWithConst p targetRate := by
  refine ⟨1, zero_lt_one, ?_⟩
  have hdecay : ∀ᶠ n in atTop, targetRate ≤ logDecay p n :=
    h.has_rate.eventually_const_le htarget
  filter_upwards [h.eventually_pos, hdecay, eventually_gt_atTop 0]
    with n hpos hdecay_n hnpos
  refine ⟨hpos.le, ?_⟩
  have hnreal_pos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hmul :
      (n : ℝ) * targetRate ≤ (n : ℝ) * logDecay p n :=
    mul_le_mul_of_nonneg_left hdecay_n hnreal_pos.le
  have hlogdecay :
      (n : ℝ) * logDecay p n = -Real.log (p n) := by
    dsimp [logDecay]
    field_simp [(ne_of_gt hnreal_pos)]
  have hlog : Real.log (p n) ≤ -(n : ℝ) * targetRate := by
    linarith
  have hple :
      p n ≤ Real.exp (-(n : ℝ) * targetRate) :=
    (Real.log_le_iff_le_exp hpos).1 hlog
  simpa using hple

/--
An exact exponential-rate certificate gives an eventual exponential lower
bound at every strictly larger rate: if `-log p_n / n -> r`, then
`exp(-n * r') <= p_n` eventually for `r < r'`.
-/
theorem hasExpLowerBoundWithConst_of_gt
    {p : ℕ → ℝ} {rate targetRate : ℝ}
    (h : ExponentialRateCertificate p rate)
    (htarget : rate < targetRate) :
    HasExpLowerBoundWithConst p targetRate := by
  refine ⟨1, zero_lt_one, ?_⟩
  have hdecay : ∀ᶠ n in atTop, logDecay p n ≤ targetRate :=
    h.has_rate.eventually_le_const htarget
  filter_upwards [h.eventually_pos, hdecay, eventually_gt_atTop 0]
    with n hpos hdecay_n hnpos
  have hnreal_pos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hmul :
      (n : ℝ) * logDecay p n ≤ (n : ℝ) * targetRate :=
    mul_le_mul_of_nonneg_left hdecay_n hnreal_pos.le
  have hlogdecay :
      (n : ℝ) * logDecay p n = -Real.log (p n) := by
    dsimp [logDecay]
    field_simp [(ne_of_gt hnreal_pos)]
  have hlog : -(n : ℝ) * targetRate ≤ Real.log (p n) := by
    linarith
  have hple :
      Real.exp (-(n : ℝ) * targetRate) ≤ p n :=
    (Real.le_log_iff_exp_le hpos).1 hlog
  simpa using hple

/--
An exact exponential-rate certificate at a strictly positive rate implies the
event probabilities converge to zero.
-/
theorem tendsto_zero_of_pos_rate
    {p : ℕ → ℝ} {rate : ℝ}
    (h : ExponentialRateCertificate p rate) (hrate : 0 < rate) :
    Tendsto p atTop (nhds 0) := by
  have hhalf_lt : rate / 2 < rate := by linarith
  have hhalf_pos : 0 < rate / 2 := by linarith
  exact
    (h.hasExpUpperBoundWithConst_of_lt hhalf_lt).tendsto_zero_of_pos_rate
      hhalf_pos

end ExponentialRateCertificate

theorem finite_weighted_sum_hasExpUpperBoundWithConst
    {ι : Type*} [Fintype ι]
    {p : ι → ℕ → ℝ} {weight rate : ι → ℝ} {targetRate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hbound : ∀ i, HasExpUpperBoundWithConst (p i) (rate i))
    (hrate : ∀ i, targetRate ≤ rate i) :
    HasExpUpperBoundWithConst
      (fun n => ∑ i : ι, weight i * p i n) targetRate := by
  classical
  choose C hCpos hCevent using hbound
  let Csum : ℝ := 1 + ∑ i : ι, weight i * C i
  have hsum_nonneg : 0 ≤ ∑ i : ι, weight i * C i := by
    exact Finset.sum_nonneg (by
      intro i _
      exact mul_nonneg (hweight i) (hCpos i).le)
  have hCsum_pos : 0 < Csum := by
    dsimp [Csum]
    linarith
  refine ⟨Csum, hCsum_pos, ?_⟩
  have hall :
      ∀ᶠ n in atTop,
        ∀ i : ι, 0 ≤ p i n ∧
          p i n ≤ C i * Real.exp (-(n : ℝ) * rate i) := by
    exact eventually_all.2 hCevent
  filter_upwards [hall] with n hn
  have hnonneg :
      0 ≤ ∑ i : ι, weight i * p i n := by
    exact Finset.sum_nonneg (by
      intro i _
      exact mul_nonneg (hweight i) (hn i).1)
  refine ⟨hnonneg, ?_⟩
  have hterm :
      ∀ i : ι,
        weight i * p i n ≤
          (weight i * C i) *
            Real.exp (-(n : ℝ) * targetRate) := by
    intro i
    have hmul :
        weight i * p i n ≤
          weight i * (C i * Real.exp (-(n : ℝ) * rate i)) :=
      mul_le_mul_of_nonneg_left (hn i).2 (hweight i)
    have hexp :
        Real.exp (-(n : ℝ) * rate i) ≤
          Real.exp (-(n : ℝ) * targetRate) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hrate i)
        (neg_nonpos.mpr (Nat.cast_nonneg n))
    have hcoef_nonneg : 0 ≤ weight i * C i :=
      mul_nonneg (hweight i) (hCpos i).le
    calc
      weight i * p i n ≤
          weight i * (C i * Real.exp (-(n : ℝ) * rate i)) := hmul
      _ = (weight i * C i) * Real.exp (-(n : ℝ) * rate i) := by ring
      _ ≤ (weight i * C i) * Real.exp (-(n : ℝ) * targetRate) := by
        exact mul_le_mul_of_nonneg_left hexp hcoef_nonneg
  calc
    ∑ i : ι, weight i * p i n ≤
        ∑ i : ι, (weight i * C i) *
          Real.exp (-(n : ℝ) * targetRate) := by
      exact Finset.sum_le_sum (by intro i _; exact hterm i)
    _ = (∑ i : ι, weight i * C i) *
          Real.exp (-(n : ℝ) * targetRate) := by
      rw [Finset.sum_mul]
    _ ≤ Csum * Real.exp (-(n : ℝ) * targetRate) := by
      exact mul_le_mul_of_nonneg_right
        (by dsimp [Csum]; linarith) (Real.exp_pos _).le

/--
If each component in a finite nonempty weighted error sum has some strictly
positive exponential upper-bound rate, then the whole weighted sum has a
strictly positive exponential upper-bound rate.
-/
theorem finite_weighted_sum_exists_pos_expUpperBoundWithConst
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hbound :
      ∀ i : ι,
        ∃ rate : ℝ,
          0 < rate ∧ HasExpUpperBoundWithConst (p i) rate) :
    ∃ targetRate : ℝ,
      0 < targetRate ∧
        HasExpUpperBoundWithConst
          (fun n => ∑ i : ι, weight i * p i n) targetRate := by
  classical
  choose rate hrate_pos hrate_bound using hbound
  let minRate : ℝ := (Finset.univ : Finset ι).inf' Finset.univ_nonempty rate
  have hmin_pos : 0 < minRate := by
    rw [Finset.lt_inf'_iff]
    intro i _
    exact hrate_pos i
  let targetRate : ℝ := minRate / 2
  have htarget_pos : 0 < targetRate := by
    dsimp [targetRate]
    linarith
  have htarget_le : ∀ i : ι, targetRate ≤ rate i := by
    intro i
    have hmin_le : minRate ≤ rate i := by
      dsimp [minRate]
      exact Finset.inf'_le rate (Finset.mem_univ i)
    dsimp [targetRate]
    linarith
  exact
    ⟨targetRate, htarget_pos,
      finite_weighted_sum_hasExpUpperBoundWithConst
        (p := p) (weight := weight) (rate := rate)
        hweight hrate_bound htarget_le⟩

theorem finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates
    {ι : Type*} [Fintype ι]
    {p : ι → ℕ → ℝ} {weight rate : ι → ℝ} {targetRate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hcert : ∀ i, ExponentialRateCertificate (p i) (rate i))
    (hrate : ∀ i, targetRate < rate i) :
    HasExpUpperBoundWithConst
      (fun n => ∑ i : ι, weight i * p i n) targetRate :=
  finite_weighted_sum_hasExpUpperBoundWithConst
    (rate := fun _ => targetRate)
    hweight
    (fun i => (hcert i).hasExpUpperBoundWithConst_of_lt (hrate i))
    (fun _ => le_rfl)

/--
If every component in a finite weighted sum is eventually zero, then the
weighted sum itself is eventually zero.
-/
theorem finite_weighted_sum_eventually_zero
    {ι : Type*} [Fintype ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ}
    (hzero : ∀ i : ι, ∀ᶠ n in atTop, p i n = 0) :
    ∀ᶠ n in atTop, (∑ i : ι, weight i * p i n) = 0 := by
  classical
  have hall : ∀ᶠ n in atTop, ∀ i : ι, p i n = 0 :=
    eventually_all.2 hzero
  filter_upwards [hall] with n hn
  simp [hn]

/--
A finite weighted sum whose components are eventually zero has an exponential
upper bound at every finite target rate.
-/
theorem finite_weighted_sum_hasExpUpperBoundWithConst_of_eventually_zero
    {ι : Type*} [Fintype ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ}
    (hzero : ∀ i : ι, ∀ᶠ n in atTop, p i n = 0)
    (targetRate : ℝ) :
    HasExpUpperBoundWithConst
      (fun n => ∑ i : ι, weight i * p i n)
      targetRate :=
  HasExpUpperBoundWithConst.of_eventually_zero
    (finite_weighted_sum_eventually_zero (p := p) (weight := weight) hzero)

theorem finite_weighted_sum_hasExpLowerBoundWithConst_of_component
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ} {targetRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hp_nonneg : ∀ i, ∀ᶠ n : ℕ in atTop, 0 ≤ p i n)
    (i0 : ι) (hweight_pos : 0 < weight i0)
    (hlower : HasExpLowerBoundWithConst (p i0) targetRate) :
    HasExpLowerBoundWithConst
      (fun n => ∑ i : ι, weight i * p i n) targetRate := by
  classical
  rcases hlower with ⟨c, hcpos, hc⟩
  refine ⟨weight i0 * c, mul_pos hweight_pos hcpos, ?_⟩
  have hp_all : ∀ᶠ n in atTop, ∀ i : ι, 0 ≤ p i n :=
    eventually_all.2 hp_nonneg
  filter_upwards [hc, hp_all] with n hn hnonneg
  have hcomponent :
      weight i0 * (c * Real.exp (-(n : ℝ) * targetRate)) ≤
        weight i0 * p i0 n :=
    mul_le_mul_of_nonneg_left hn hweight_pos.le
  have hterm_sum :
      weight i0 * p i0 n ≤ ∑ i : ι, weight i * p i n := by
    exact Finset.single_le_sum
      (fun i _ => mul_nonneg (hweight_nonneg i) (hnonneg i))
      (Finset.mem_univ i0)
  calc
    (weight i0 * c) * Real.exp (-(n : ℝ) * targetRate)
        = weight i0 * (c * Real.exp (-(n : ℝ) * targetRate)) := by ring
    _ ≤ weight i0 * p i0 n := hcomponent
    _ ≤ ∑ i : ι, weight i * p i n := hterm_sum

theorem finite_weighted_sum_hasExpLowerBoundWithConst_of_rate_certificate_component
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ → ℝ} {weight rate : ι → ℝ} {targetRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hp_nonneg : ∀ i, ∀ᶠ n : ℕ in atTop, 0 ≤ p i n)
    (i0 : ι) (hweight_pos : 0 < weight i0)
    (hcert : ExponentialRateCertificate (p i0) (rate i0))
    (hrate : rate i0 < targetRate) :
    HasExpLowerBoundWithConst
      (fun n => ∑ i : ι, weight i * p i n) targetRate :=
  finite_weighted_sum_hasExpLowerBoundWithConst_of_component
    hweight_nonneg hp_nonneg i0 hweight_pos
    (hcert.hasExpLowerBoundWithConst_of_gt hrate)

/--
Finite weighted-sum exact rate with mixed exact and eventually-zero
components.  One positive-weight component certifies the minimum rate; every
other component either has an exact rate at least that minimum, or is
eventually zero.
-/
theorem finite_weighted_sum_hasExponentialRate_of_min_component_cert_or_eventually_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ → ℝ} {weight : ι → ℝ} {minRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (iMin : ι) (hweight_pos : 0 < weight iMin)
    (hmin : ExponentialRateCertificate (p iMin) minRate)
    (hcase :
      ∀ i : ι,
        (∃ rate_i : ℝ,
          minRate ≤ rate_i ∧
            ExponentialRateCertificate (p i) rate_i) ∨
          (∀ᶠ n in atTop, p i n = 0)) :
    HasExponentialRate
      (fun n => ∑ i : ι, weight i * p i n)
      minRate := by
  classical
  have hp_nonneg :
      ∀ i : ι, ∀ᶠ n : ℕ in atTop, 0 ≤ p i n := by
    intro i
    rcases hcase i with hcert | hzero
    · rcases hcert with ⟨rate_i, _hrate_ge, hcert_i⟩
      exact hcert_i.eventually_pos.mono (fun _ hn => hn.le)
    · exact hzero.mono (fun _ hn => by simp [hn])
  have hlower_one :
      HasExpLowerBoundWithConst
        (fun n => ∑ i : ι, weight i * p i n) (minRate + 1) :=
    finite_weighted_sum_hasExpLowerBoundWithConst_of_component
      hweight_nonneg hp_nonneg iMin hweight_pos
      (hmin.hasExpLowerBoundWithConst_of_gt (by linarith))
  have hpos :
      ∀ᶠ n in atTop, 0 < ∑ i : ι, weight i * p i n := by
    rcases hlower_one with ⟨c, hcpos, hc⟩
    filter_upwards [hc] with n hn
    exact lt_of_lt_of_le
      (mul_pos hcpos (Real.exp_pos (-(n : ℝ) * (minRate + 1)))) hn
  refine hasExponentialRate_of_expUpperLowerBounds hpos ?_ ?_
  · intro targetRate htarget
    have hbound :
        ∀ i : ι, HasExpUpperBoundWithConst (p i) targetRate := by
      intro i
      rcases hcase i with hcert | hzero
      · rcases hcert with ⟨rate_i, hrate_ge, hcert_i⟩
        exact hcert_i.hasExpUpperBoundWithConst_of_lt
          (lt_of_lt_of_le htarget hrate_ge)
      · exact HasExpUpperBoundWithConst.of_eventually_zero hzero
    exact
      finite_weighted_sum_hasExpUpperBoundWithConst
        (p := p) (weight := weight) (rate := fun _ : ι => targetRate)
        hweight_nonneg hbound (fun _ => le_rfl)
  · intro targetRate htarget
    exact
      finite_weighted_sum_hasExpLowerBoundWithConst_of_component
        hweight_nonneg hp_nonneg iMin hweight_pos
        (hmin.hasExpLowerBoundWithConst_of_gt htarget)

/--
A positive constant times a pure exponential sequence has exactly the displayed
exponential rate.  This is the finite-discrete Laplace primitive used when a
finite sum is reduced to its slowest exponential term.
-/
theorem exponentialRateCertificate_const_mul_exp
    {C rate : ℝ} (hC : 0 < C) :
    ExponentialRateCertificate
      (fun n : ℕ => C * Real.exp (-(n : ℝ) * rate)) rate := by
  refine
    { eventually_pos := ?_
      has_rate := ?_ }
  · filter_upwards with n
    exact mul_pos hC (Real.exp_pos _)
  · refine hasExponentialRate_of_expUpperLowerBounds ?_ ?_ ?_
    · filter_upwards with n
      exact mul_pos hC (Real.exp_pos _)
    · intro targetRate htarget
      refine ⟨C, hC, ?_⟩
      filter_upwards with n
      have hexp :
          Real.exp (-(n : ℝ) * rate) ≤
            Real.exp (-(n : ℝ) * targetRate) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left (le_of_lt htarget)
          (neg_nonpos.mpr (Nat.cast_nonneg n))
      exact
        ⟨mul_nonneg hC.le (Real.exp_pos _).le,
          mul_le_mul_of_nonneg_left hexp hC.le⟩
    · intro targetRate htarget
      refine ⟨C, hC, ?_⟩
      filter_upwards with n
      have hexp :
          Real.exp (-(n : ℝ) * targetRate) ≤
            Real.exp (-(n : ℝ) * rate) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left (le_of_lt htarget)
          (neg_nonpos.mpr (Nat.cast_nonneg n))
      exact mul_le_mul_of_nonneg_left hexp hC.le

/--
Generic finite family of exact error-rate certificates.  This abstracts the
common EC large-deviation pattern before specializing to pairwise ranking
errors: each index has an error probability and an exact exponential rate.
-/
structure FiniteErrorRateCertificate (ι : Type*) where
  errorProb : ι → ℕ → ℝ
  rate : ι → ℝ
  has_rate : ∀ i, ExponentialRateCertificate (errorProb i) (rate i)

namespace FiniteErrorRateCertificate

variable {ι : Type*} [Fintype ι]

/-- Weighted finite aggregate of certified error probabilities. -/
def aggregateError (C : FiniteErrorRateCertificate ι)
    (weight : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i : ι, weight i * C.errorProb i n

theorem aggregateError_hasExpUpperBoundWithConst_of_lt
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {targetRate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hrate : ∀ i, targetRate < C.rate i) :
    HasExpUpperBoundWithConst
      (C.aggregateError weight) targetRate := by
  simpa [aggregateError] using
    finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates
      (ι := ι)
      (p := fun i n => C.errorProb i n)
      (weight := weight)
      (rate := C.rate)
      (targetRate := targetRate)
      hweight
      C.has_rate
      hrate

/--
If every component exact rate is bounded below by a strictly positive floor,
then any nonnegative finite weighted aggregate of the component errors tends
to zero.
-/
theorem aggregateError_tendsto_zero_of_pos_rate_floor
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {rateFloor : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hrateFloor_pos : 0 < rateFloor)
    (hrateFloor : ∀ i, rateFloor ≤ C.rate i) :
    Tendsto (C.aggregateError weight) atTop (nhds 0) := by
  let targetRate : ℝ := rateFloor / 2
  have htarget_pos : 0 < targetRate := by
    dsimp [targetRate]
    linarith
  have htarget_lt : ∀ i : ι, targetRate < C.rate i := by
    intro i
    exact lt_of_lt_of_le (by dsimp [targetRate]; linarith) (hrateFloor i)
  exact
    (C.aggregateError_hasExpUpperBoundWithConst_of_lt hweight htarget_lt)
      |>.tendsto_zero_of_pos_rate htarget_pos

theorem aggregateError_hasExpLowerBoundWithConst_of_component_gt
    [DecidableEq ι]
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {targetRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (i0 : ι) (hweight_pos : 0 < weight i0)
    (hrate : C.rate i0 < targetRate) :
    HasExpLowerBoundWithConst
      (C.aggregateError weight) targetRate := by
  have hp_nonneg :
      ∀ i : ι, ∀ᶠ n : ℕ in atTop, 0 ≤ C.errorProb i n := by
    intro i
    exact (C.has_rate i).eventually_pos.mono (fun _ hn => hn.le)
  simpa [aggregateError] using
    finite_weighted_sum_hasExpLowerBoundWithConst_of_rate_certificate_component
      (ι := ι)
      (p := fun i n => C.errorProb i n)
      (weight := weight)
      (rate := C.rate)
      (targetRate := targetRate)
      hweight_nonneg
      hp_nonneg
      i0
      hweight_pos
      (C.has_rate i0)
      hrate

theorem aggregateError_hasExponentialRate_of_min_component
    [DecidableEq ι]
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {minRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (iMin : ι) (hweight_pos : 0 < weight iMin)
    (hrate_min : C.rate iMin = minRate)
    (hrate_ge : ∀ i, minRate ≤ C.rate i) :
    HasExponentialRate (C.aggregateError weight) minRate := by
  have hlower_one :
      HasExpLowerBoundWithConst (C.aggregateError weight) (minRate + 1) :=
    C.aggregateError_hasExpLowerBoundWithConst_of_component_gt
      hweight_nonneg iMin hweight_pos
      (by rw [hrate_min]; linarith)
  have hpos :
      ∀ᶠ n in atTop, 0 < C.aggregateError weight n := by
    rcases hlower_one with ⟨c, hcpos, hc⟩
    filter_upwards [hc] with n hn
    exact lt_of_lt_of_le
      (mul_pos hcpos (Real.exp_pos (-(n : ℝ) * (minRate + 1)))) hn
  refine hasExponentialRate_of_expUpperLowerBounds hpos ?_ ?_
  · intro targetRate htarget
    exact C.aggregateError_hasExpUpperBoundWithConst_of_lt
      hweight_nonneg
      (fun i => lt_of_lt_of_le htarget (hrate_ge i))
  · intro targetRate htarget
    exact C.aggregateError_hasExpLowerBoundWithConst_of_component_gt
      hweight_nonneg iMin hweight_pos
      (by rw [hrate_min]; exact htarget)

end FiniteErrorRateCertificate

/--
Finite discrete Laplace principle for a nonnegative weighted sum of pure
exponentials: if one positive-weight term realizes the minimum exponent, then
the whole finite sum has that exponent.
-/
theorem finite_exp_sum_hasExponentialRate_of_min_component
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight rate : ι → ℝ) {minRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (iMin : ι) (hweight_pos : 0 < weight iMin)
    (hrate_min : rate iMin = minRate)
    (hrate_ge : ∀ i, minRate ≤ rate i) :
    HasExponentialRate
      (fun n : ℕ =>
        ∑ i : ι, weight i * Real.exp (-(n : ℝ) * rate i))
      minRate := by
  let C : FiniteErrorRateCertificate ι :=
    { errorProb := fun i n => Real.exp (-(n : ℝ) * rate i)
      rate := rate
      has_rate := fun i => by
        simpa [one_mul] using
          (exponentialRateCertificate_const_mul_exp
            (C := 1) (rate := rate i) zero_lt_one) }
  simpa [FiniteErrorRateCertificate.aggregateError, C] using
    C.aggregateError_hasExponentialRate_of_min_component
      hweight_nonneg iMin hweight_pos hrate_min hrate_ge

/--
Certificate form of `finite_exp_sum_hasExponentialRate_of_min_component`.
-/
theorem finite_exp_sum_exponentialRateCertificate_of_min_component
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight rate : ι → ℝ) {minRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (iMin : ι) (hweight_pos : 0 < weight iMin)
    (hrate_min : rate iMin = minRate)
    (hrate_ge : ∀ i, minRate ≤ rate i) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        ∑ i : ι, weight i * Real.exp (-(n : ℝ) * rate i))
      minRate where
  eventually_pos := by
    filter_upwards with n
    have hterm_pos :
        0 < weight iMin * Real.exp (-(n : ℝ) * rate iMin) :=
      mul_pos hweight_pos (Real.exp_pos _)
    have hterm_le :
        weight iMin * Real.exp (-(n : ℝ) * rate iMin) ≤
          ∑ i : ι, weight i * Real.exp (-(n : ℝ) * rate i) := by
      exact Finset.single_le_sum
        (fun i _hi =>
          show 0 ≤ weight i * Real.exp (-(n : ℝ) * rate i) from
            mul_nonneg (hweight_nonneg i) (Real.exp_pos _).le)
        (Finset.mem_univ iMin)
    exact lt_of_lt_of_le hterm_pos hterm_le
  has_rate :=
    finite_exp_sum_hasExponentialRate_of_min_component
      weight rate hweight_nonneg iMin hweight_pos hrate_min hrate_ge

/--
Pairwise ranking-error upper-bound certificate.  `errorProb hi lo n` is the
probability that the pair `(hi, lo)` is misordered after scale `n`; `rate hi lo`
is a certified exponential upper-bound rate.
-/
structure PairwiseErrorUpperBoundCertificate (θ : Type*) where
  errorProb : θ → θ → ℕ → ℝ
  rate : θ → θ → ℝ
  has_bound : ∀ hi lo, HasExpUpperBoundWithConst (errorProb hi lo) (rate hi lo)

namespace PairwiseErrorUpperBoundCertificate

variable {θ : Type*} [Fintype θ]

/-- Weighted aggregate of finitely many pairwise ranking errors. -/
def aggregateError (C : PairwiseErrorUpperBoundCertificate θ)
    (pairWeight : θ → θ → ℝ) (n : ℕ) : ℝ :=
  ∑ p : θ × θ, pairWeight p.1 p.2 * C.errorProb p.1 p.2 n

theorem aggregateError_hasExpUpperBoundWithConst
    (C : PairwiseErrorUpperBoundCertificate θ)
    {pairWeight : θ → θ → ℝ} {targetRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrate : ∀ hi lo, targetRate ≤ C.rate hi lo) :
    HasExpUpperBoundWithConst
      (C.aggregateError pairWeight) targetRate := by
  simpa [aggregateError] using
    finite_weighted_sum_hasExpUpperBoundWithConst
      (ι := θ × θ)
      (p := fun pair n => C.errorProb pair.1 pair.2 n)
      (weight := fun pair => pairWeight pair.1 pair.2)
      (rate := fun pair => C.rate pair.1 pair.2)
      (targetRate := targetRate)
      (fun pair => hweight pair.1 pair.2)
      (fun pair => C.has_bound pair.1 pair.2)
      (fun pair => hrate pair.1 pair.2)

end PairwiseErrorUpperBoundCertificate

/--
Pairwise ranking-error exact-rate certificate. Unlike
`PairwiseErrorUpperBoundCertificate`, this stores exact normalized-log decay
certificates and can be weakened to any strictly smaller aggregate upper-bound
rate.
-/
structure PairwiseErrorRateCertificate (θ : Type*) where
  errorProb : θ → θ → ℕ → ℝ
  rate : θ → θ → ℝ
  has_rate : ∀ hi lo, ExponentialRateCertificate (errorProb hi lo) (rate hi lo)

namespace PairwiseErrorRateCertificate

variable {θ : Type*} [Fintype θ]

/-- View a pairwise ranking-error certificate as a generic finite certificate. -/
def toFiniteErrorRateCertificate (C : PairwiseErrorRateCertificate θ) :
    FiniteErrorRateCertificate (θ × θ) where
  errorProb := fun pair n => C.errorProb pair.1 pair.2 n
  rate := fun pair => C.rate pair.1 pair.2
  has_rate := fun pair => C.has_rate pair.1 pair.2

/-- Weighted aggregate of finitely many pairwise ranking errors. -/
def aggregateError (C : PairwiseErrorRateCertificate θ)
    (pairWeight : θ → θ → ℝ) (n : ℕ) : ℝ :=
  ∑ p : θ × θ, pairWeight p.1 p.2 * C.errorProb p.1 p.2 n

theorem aggregateError_hasExpUpperBoundWithConst_of_lt
    (C : PairwiseErrorRateCertificate θ)
    {pairWeight : θ → θ → ℝ} {targetRate : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrate : ∀ hi lo, targetRate < C.rate hi lo) :
    HasExpUpperBoundWithConst
      (C.aggregateError pairWeight) targetRate := by
  simpa [aggregateError] using
    finite_weighted_sum_hasExpUpperBoundWithConst_of_rate_certificates
      (ι := θ × θ)
      (p := fun pair n => C.errorProb pair.1 pair.2 n)
      (weight := fun pair => pairWeight pair.1 pair.2)
      (rate := fun pair => C.rate pair.1 pair.2)
      (targetRate := targetRate)
      (fun pair => hweight pair.1 pair.2)
      (fun pair => C.has_rate pair.1 pair.2)
      (fun pair => hrate pair.1 pair.2)

/--
If all pairwise exact rates are bounded below by a positive floor, the
nonnegative finite weighted aggregate of pairwise errors tends to zero.
-/
theorem aggregateError_tendsto_zero_of_pos_rate_floor
    (C : PairwiseErrorRateCertificate θ)
    {pairWeight : θ → θ → ℝ} {rateFloor : ℝ}
    (hweight : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hrateFloor_pos : 0 < rateFloor)
    (hrateFloor : ∀ hi lo, rateFloor ≤ C.rate hi lo) :
    Tendsto (C.aggregateError pairWeight) atTop (nhds 0) := by
  simpa [aggregateError] using
    C.toFiniteErrorRateCertificate.aggregateError_tendsto_zero_of_pos_rate_floor
      (weight := fun pair : θ × θ => pairWeight pair.1 pair.2)
      (rateFloor := rateFloor)
      (fun pair => hweight pair.1 pair.2)
      hrateFloor_pos
      (fun pair => hrateFloor pair.1 pair.2)

theorem aggregateError_hasExpLowerBoundWithConst_of_component_gt
    [DecidableEq θ]
    (C : PairwiseErrorRateCertificate θ)
    {pairWeight : θ → θ → ℝ} {targetRate : ℝ}
    (hweight_nonneg : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hi lo : θ) (hweight_pos : 0 < pairWeight hi lo)
    (hrate : C.rate hi lo < targetRate) :
    HasExpLowerBoundWithConst
      (C.aggregateError pairWeight) targetRate := by
  have hp_nonneg :
      ∀ pair : θ × θ,
        ∀ᶠ n : ℕ in atTop, 0 ≤ C.errorProb pair.1 pair.2 n := by
    intro pair
    exact (C.has_rate pair.1 pair.2).eventually_pos.mono
      (fun _ hn => hn.le)
  simpa [aggregateError] using
    finite_weighted_sum_hasExpLowerBoundWithConst_of_rate_certificate_component
      (ι := θ × θ)
      (p := fun pair n => C.errorProb pair.1 pair.2 n)
      (weight := fun pair => pairWeight pair.1 pair.2)
      (rate := fun pair => C.rate pair.1 pair.2)
      (targetRate := targetRate)
      (fun pair => hweight_nonneg pair.1 pair.2)
      hp_nonneg
      (hi, lo)
      hweight_pos
      (C.has_rate hi lo)
      hrate

theorem aggregateError_hasExponentialRate_of_min_pair
    [DecidableEq θ]
    (C : PairwiseErrorRateCertificate θ)
    {pairWeight : θ → θ → ℝ} {minRate : ℝ}
    (hweight_nonneg : ∀ hi lo, 0 ≤ pairWeight hi lo)
    (hi lo : θ) (hweight_pos : 0 < pairWeight hi lo)
    (hrate_min : C.rate hi lo = minRate)
    (hrate_ge : ∀ hi lo, minRate ≤ C.rate hi lo) :
    HasExponentialRate (C.aggregateError pairWeight) minRate := by
  have hlower_one :
      HasExpLowerBoundWithConst
        (C.aggregateError pairWeight) (minRate + 1) :=
    C.aggregateError_hasExpLowerBoundWithConst_of_component_gt
      hweight_nonneg hi lo hweight_pos
      (by rw [hrate_min]; linarith)
  have hpos :
      ∀ᶠ n in atTop, 0 < C.aggregateError pairWeight n := by
    rcases hlower_one with ⟨c, hcpos, hc⟩
    filter_upwards [hc] with n hn
    exact lt_of_lt_of_le
      (mul_pos hcpos (Real.exp_pos (-(n : ℝ) * (minRate + 1)))) hn
  refine hasExponentialRate_of_expUpperLowerBounds hpos ?_ ?_
  · intro targetRate htarget
    exact C.aggregateError_hasExpUpperBoundWithConst_of_lt
      hweight_nonneg
      (fun hi lo => lt_of_lt_of_le htarget (hrate_ge hi lo))
  · intro targetRate htarget
    exact C.aggregateError_hasExpLowerBoundWithConst_of_component_gt
      hweight_nonneg hi lo hweight_pos
      (by rw [hrate_min]; exact htarget)

end PairwiseErrorRateCertificate

/--
Certificate boundary for a Laplace-principle or Gartner-Ellis calculation.
The paper or distribution-family layer supplies `has_rate`; downstream proofs
can use the exponential-rate statement without unfolding the analytic proof.
-/
structure LargeDeviationRateCertificate (eventProb : ℕ → ℝ) (rate : ℝ) where
  rate_certificate : ExponentialRateCertificate eventProb rate

end

end Probability
end EconCSLib
