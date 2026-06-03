import PRPKG24AccuracyDiversity.Exchange
import PRPKG24AccuracyDiversity.Optimization
import PRPKG24AccuracyDiversity.TopKOracle
import EconCSLib.Applications.RecommenderSystems.AllocationSequence
import EconCSLib.Foundations.Probability.OrderStatistics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Bounds

open Filter Topology
open scoped BigOperators

namespace PRPKG24AccuracyDiversity

/--
Changing finitely many entries of a zero-convergent error schedule preserves
zero convergence. This is useful when an asymptotic certificate only starts
after a finite threshold: make the finitely many early errors deliberately
large, and keep the original asymptotic schedule afterwards.
-/
theorem tendsToZero_if_lt_const
    {ε : ℕ → ℝ} (hε : EconCSLib.Math.TendsToZero ε)
    (threshold : ℕ) (C : ℝ) :
    EconCSLib.Math.TendsToZero
      (fun N => if N < threshold then C else ε N) := by
  exact EconCSLib.Math.tendsToZero_if_lt_const hε threshold C

/--
Source Theorem 1(i) asymptotic algebra: an exact geometric tail has the
paper's logarithmic saturation ratio.
-/
theorem finiteDiscrete_log_geometric_tail_ratio
    {C r : ℝ} (hC : 0 < C) (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    Tendsto
      (fun N : ℕ =>
        Real.log (C * r ^ N) / (Real.log r * (N : ℝ)))
      atTop (nhds 1) := by
  have hlog_neg : Real.log r < 0 := Real.log_neg hr_pos hr_lt_one
  have hlog_ne : Real.log r ≠ 0 := ne_of_lt hlog_neg
  have hconst :
      Tendsto
        (fun N : ℕ => (Real.log C / Real.log r) / (N : ℝ))
        atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log C / Real.log r)
  have hlim :
      Tendsto
        (fun N : ℕ => 1 + (Real.log C / Real.log r) / (N : ℝ))
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hconst
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hrpow_ne : r ^ N ≠ 0 := pow_ne_zero N hr_pos.ne'
  symm
  calc
    Real.log (C * r ^ N) / (Real.log r * (N : ℝ))
        = (Real.log C + (N : ℝ) * Real.log r) /
            (Real.log r * (N : ℝ)) := by
          rw [Real.log_mul hC.ne' hrpow_ne, Real.log_pow]
    _ = 1 + (Real.log C / Real.log r) / (N : ℝ) := by
          field_simp [hlog_ne, hN_ne]
          ring

/-- `log N / N -> 0`, used by the finite-discrete polynomial tail factor. -/
theorem tendsto_log_nat_div_nat_nhds_zero :
    Tendsto
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using
      (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- Natural square root tends to infinity along natural numbers. -/
theorem tendsto_nat_sqrt_atTop :
    Tendsto (fun N : ℕ => Nat.sqrt N) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  refine eventually_atTop.2 ⟨M * M, ?_⟩
  intro N hN
  exact (Nat.le_sqrt).2 hN

/--
The square-root integer gap is sublinear in the certificate sense:
`(sqrt N + 1) / N -> 0`.
-/
theorem finiteDiscrete_nat_sqrt_gap_error_tendsToZero :
    EconCSLib.Math.TendsToZero
      (fun N : ℕ => ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ)) := by
  refine EconCSLib.Math.TendsToZero_of_eventually_abs_le_inv_sqrt
    (fun N : ℕ => ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ))
    (by norm_num : (0 : ℝ) < 2) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hN)
  have hN_nonneg : 0 ≤ (N : ℝ) := hN_pos.le
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
  have hsqrt_ge_one : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hN
  have hnat_sqrt_le : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hnum_le :
      ((Nat.sqrt N + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
    norm_num
    linarith
  have hval_nonneg :
      0 ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ) := by
    positivity
  rw [abs_of_nonneg hval_nonneg]
  calc
    ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ)
        ≤ (2 * Real.sqrt (N : ℝ)) / (N : ℝ) :=
          div_le_div_of_nonneg_right hnum_le hN_nonneg
    _ = 2 / Real.sqrt (N : ℝ) := by
          field_simp [hsqrt_pos.ne']
          rw [Real.sq_sqrt hN_nonneg]

/--
For any `0 < rho < 1`, the square-root integer gap kills every fixed
polynomial factor: `N^k * rho^(sqrt N) -> 0`.
-/
theorem finiteDiscrete_nat_sqrt_gap_polynomial_geometric_tends_to_zero
    (k : ℕ) {rho : ℝ} (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1) :
    Tendsto
      (fun N : ℕ => (N : ℝ) ^ k * rho ^ (Nat.sqrt N))
      atTop (nhds 0) := by
  have hsucc_base :
      Tendsto
        (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ (2 * k)) * rho ^ (m + 1))
        atTop (nhds 0) := by
    exact
      (tendsto_pow_const_mul_const_pow_of_lt_one (2 * k)
        hrho_pos.le hrho_lt_one).comp (tendsto_add_atTop_nat 1)
  have hsucc :
      Tendsto
        (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ (2 * k)) * rho ^ m)
        atTop (nhds 0) := by
    have hmul :=
      hsucc_base.const_mul rho⁻¹
    refine Tendsto.congr' ?_ (by simpa using hmul)
    filter_upwards with m
    have hpow : rho ^ (m + 1) = rho ^ m * rho := by
      rw [pow_succ]
    rw [hpow]
    field_simp [hrho_pos.ne']
    ring_nf
    norm_num [Nat.cast_add, add_comm, mul_comm]
  have hupper_lim :
      Tendsto
        (fun N : ℕ =>
          (((Nat.sqrt N + 1 : ℕ) : ℝ) ^ (2 * k)) *
            rho ^ (Nat.sqrt N))
        atTop (nhds 0) :=
    hsucc.comp tendsto_nat_sqrt_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper_lim ?_ ?_
  · filter_upwards with N
    positivity
  · filter_upwards with N
    let m : ℕ := Nat.sqrt N
    have hN_le_nat : N ≤ (m + 1) ^ 2 := by
      exact le_of_lt (by simpa [m] using Nat.lt_succ_sqrt' N)
    have hN_le_real : (N : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hN_le_nat
    have hpow_le :
        (N : ℝ) ^ k ≤ (((m + 1 : ℕ) : ℝ) ^ 2) ^ k :=
      pow_le_pow_left₀ (by positivity) hN_le_real k
    have hpow_eq :
        (((m + 1 : ℕ) : ℝ) ^ 2) ^ k =
          ((m + 1 : ℕ) : ℝ) ^ (2 * k) := by
      rw [pow_mul]
    have hpow_le' :
        (N : ℝ) ^ k ≤ ((m + 1 : ℕ) : ℝ) ^ (2 * k) := by
      calc
        (N : ℝ) ^ k ≤ (((m + 1 : ℕ) : ℝ) ^ 2) ^ k := hpow_le
        _ = ((m + 1 : ℕ) : ℝ) ^ (2 * k) := hpow_eq
    have htail_nonneg : 0 ≤ rho ^ m := pow_nonneg hrho_pos.le m
    calc
      (N : ℝ) ^ k * rho ^ (Nat.sqrt N)
          = (N : ℝ) ^ k * rho ^ m := by rfl
      _ ≤ (((m + 1 : ℕ) : ℝ) ^ (2 * k)) * rho ^ m := by
            exact mul_le_mul_of_nonneg_right
              hpow_le' htail_nonneg
      _ = (((Nat.sqrt N + 1 : ℕ) : ℝ) ^ (2 * k)) *
            rho ^ (Nat.sqrt N) := by rfl

/--
Source Theorem 1(i) asymptotic algebra: multiplying a geometric tail by any
fixed polynomial factor does not change the logarithmic saturation ratio.
-/
theorem finiteDiscrete_log_polynomial_geometric_tail_ratio
    {C r : ℝ} (d : ℕ)
    (hC : 0 < C) (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    Tendsto
      (fun N : ℕ =>
        Real.log (C * (N : ℝ) ^ d * r ^ N) /
          (Real.log r * (N : ℝ)))
      atTop (nhds 1) := by
  have hlog_neg : Real.log r < 0 := Real.log_neg hr_pos hr_lt_one
  have hlog_ne : Real.log r ≠ 0 := ne_of_lt hlog_neg
  have hconst :
      Tendsto
        (fun N : ℕ => (Real.log C / Real.log r) / (N : ℝ))
        atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log C / Real.log r)
  have hlog_over_N :
      Tendsto
        (fun N : ℕ =>
          ((d : ℝ) / Real.log r) *
            (Real.log (N : ℝ) / (N : ℝ)))
        atTop (nhds 0) := by
    simpa using tendsto_log_nat_div_nat_nhds_zero.const_mul
      ((d : ℝ) / Real.log r)
  have hlim :
      Tendsto
        (fun N : ℕ =>
          1 + (Real.log C / Real.log r) / (N : ℝ) +
            ((d : ℝ) / Real.log r) *
              (Real.log (N : ℝ) / (N : ℝ)))
        atTop (nhds 1) := by
    have hfirst :
        Tendsto
          (fun N : ℕ => 1 + (Real.log C / Real.log r) / (N : ℝ))
          atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hconst
    simpa using hfirst.add hlog_over_N
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hNpow_ne : (N : ℝ) ^ d ≠ 0 := pow_ne_zero d hN_ne
  have hrpow_ne : r ^ N ≠ 0 := pow_ne_zero N hr_pos.ne'
  symm
  calc
    Real.log (C * (N : ℝ) ^ d * r ^ N) /
          (Real.log r * (N : ℝ))
        =
        (Real.log C + (d : ℝ) * Real.log (N : ℝ) +
            (N : ℝ) * Real.log r) /
          (Real.log r * (N : ℝ)) := by
          rw [Real.log_mul (mul_ne_zero hC.ne' hNpow_ne) hrpow_ne,
            Real.log_mul hC.ne' hNpow_ne, Real.log_pow, Real.log_pow]
    _ = 1 + (Real.log C / Real.log r) / (N : ℝ) +
          ((d : ℝ) / Real.log r) *
            (Real.log (N : ℝ) / (N : ℝ)) := by
          field_simp [hlog_ne, hN_ne]
          ring

/--
Source Theorem 1(i) asymptotic algebra: the paper's lower geometric and upper
polynomial-times-geometric bounds squeeze the logarithmic saturation ratio to
one.
-/
theorem finiteDiscrete_log_tail_ratio_of_geometric_bounds
    {gap : ℕ → ℝ} {lower upper r : ℝ} (d : ℕ)
    (hlower_pos : 0 < lower) (hupper_pos : 0 < upper)
    (hr_pos : 0 < r) (hr_lt_one : r < 1)
    (hlower :
      ∀ᶠ N in atTop, lower * r ^ N ≤ gap N)
    (hupper :
      ∀ᶠ N in atTop, gap N ≤ upper * (N : ℝ) ^ d * r ^ N) :
    Tendsto
      (fun N : ℕ =>
        Real.log (gap N) / (Real.log r * (N : ℝ)))
      atTop (nhds 1) := by
  have hlog_neg : Real.log r < 0 := Real.log_neg hr_pos hr_lt_one
  have hlow_lim :=
    finiteDiscrete_log_polynomial_geometric_tail_ratio
      d hupper_pos hr_pos hr_lt_one
  have hup_lim :=
    finiteDiscrete_log_geometric_tail_ratio
      hlower_pos hr_pos hr_lt_one
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_lim hup_lim ?_ ?_
  · filter_upwards [hlower, hupper, eventually_gt_atTop 0] with N hlowerN hupperN hN
    have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hden_neg : Real.log r * (N : ℝ) < 0 :=
      mul_neg_of_neg_of_pos hlog_neg hN_pos
    have hlower_tail_pos : 0 < lower * r ^ N :=
      mul_pos hlower_pos (pow_pos hr_pos N)
    have hgap_pos : 0 < gap N := lt_of_lt_of_le hlower_tail_pos hlowerN
    have hupper_tail_pos : 0 < upper * (N : ℝ) ^ d * r ^ N := by
      positivity
    have hlog_le :
        Real.log (gap N) ≤
          Real.log (upper * (N : ℝ) ^ d * r ^ N) :=
      Real.log_le_log hgap_pos hupperN
    exact (div_le_div_right_of_neg hden_neg).2 hlog_le
  · filter_upwards [hlower, hupper, eventually_gt_atTop 0] with N hlowerN hupperN hN
    have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hden_neg : Real.log r * (N : ℝ) < 0 :=
      mul_neg_of_neg_of_pos hlog_neg hN_pos
    have hlower_tail_pos : 0 < lower * r ^ N :=
      mul_pos hlower_pos (pow_pos hr_pos N)
    have hgap_pos : 0 < gap N := lt_of_lt_of_le hlower_tail_pos hlowerN
    have hlog_le :
        Real.log (lower * r ^ N) ≤ Real.log (gap N) :=
      Real.log_le_log hlower_tail_pos hlowerN
    exact (div_le_div_right_of_neg hden_neg).2 hlog_le

/--
The binomial lower-tail expression from the finite-discrete proof of Theorem
1(i): fewer than `k` draws land on the top support point when the top mass is
`q` and the non-top mass is `rho`.
-/
noncomputable def finiteDiscreteTopMassFailureTail
    (k a : ℕ) (q rho : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k,
    (Nat.choose a j : ℝ) * q ^ j * rho ^ (a - j)

theorem finiteDiscreteTopMassFailureTail_nonneg
    (k a : ℕ) {q rho : ℝ}
    (hq_nonneg : 0 ≤ q) (hrho_nonneg : 0 ≤ rho) :
    0 ≤ finiteDiscreteTopMassFailureTail k a q rho := by
  unfold finiteDiscreteTopMassFailureTail
  refine Finset.sum_nonneg ?_
  intro j _hj
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq_nonneg j))
    (pow_nonneg hrho_nonneg (a - j))

/--
Probability mass of the event used for the finite-discrete lower marginal:
before adding the new item there are exactly `k-1` top-support draws, and the
new item is itself top-support.
-/
noncomputable def finiteDiscreteTopMassPromotingEvent
    (k a : ℕ) (q rho : ℝ) : ℝ :=
  (Nat.choose a (k - 1) : ℝ) * q ^ k * rho ^ (a + 1 - k)

theorem finiteDiscreteTopMassPromotingEvent_nonneg
    (k a : ℕ) {q rho : ℝ}
    (hq_nonneg : 0 ≤ q) (hrho_nonneg : 0 ≤ rho) :
    0 ≤ finiteDiscreteTopMassPromotingEvent k a q rho := by
  unfold finiteDiscreteTopMassPromotingEvent
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq_nonneg k))
    (pow_nonneg hrho_nonneg (a + 1 - k))

/--
Finite-discrete binomial tail estimate used in equations (81)-(83).

For fixed `k`, the probability of fewer than `k` top-support draws is bounded
by a degree-`k` polynomial times the geometric tail `rho^(a+1-k)`.  A later
constant absorbs the fixed shift from `a+1-k` to `a`.
-/
theorem finiteDiscreteTopMassFailureTail_le_polynomial_geometric
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a)
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hrho_nonneg : 0 ≤ rho) (hrho_le_one : rho ≤ 1) :
    finiteDiscreteTopMassFailureTail k a q rho ≤
      (k : ℝ) * (a : ℝ) ^ k * rho ^ (a + 1 - k) := by
  have ha_pos : 0 < a := lt_of_lt_of_le hk_pos hk_le_a
  have ha_one_le : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_pos
  have hterm :
      ∀ j ∈ Finset.range k,
        (Nat.choose a j : ℝ) * q ^ j * rho ^ (a - j) ≤
          (a : ℝ) ^ k * rho ^ (a + 1 - k) := by
    intro j hj
    have hj_lt : j < k := Finset.mem_range.mp hj
    have hj_le_k : j ≤ k := Nat.le_of_lt hj_lt
    have hj_le_a : j ≤ a := le_trans hj_le_k hk_le_a
    have hchoose_le : (Nat.choose a j : ℝ) ≤ (a : ℝ) ^ j := by
      exact_mod_cast Nat.choose_le_pow a j
    have hq_pow_le_one : q ^ j ≤ 1 :=
      pow_le_one₀ (n := j) hq_nonneg hq_le_one
    have ha_pow_nonneg : 0 ≤ (a : ℝ) ^ j :=
      pow_nonneg (Nat.cast_nonneg a) j
    have hrho_pow_nonneg : 0 ≤ rho ^ (a - j) :=
      pow_nonneg hrho_nonneg (a - j)
    have hchoose_q_le : (Nat.choose a j : ℝ) * q ^ j ≤ (a : ℝ) ^ j := by
      calc
        (Nat.choose a j : ℝ) * q ^ j
            ≤ (a : ℝ) ^ j * q ^ j :=
              mul_le_mul_of_nonneg_right hchoose_le
                (pow_nonneg hq_nonneg j)
        _ ≤ (a : ℝ) ^ j * 1 :=
              mul_le_mul_of_nonneg_left hq_pow_le_one ha_pow_nonneg
        _ = (a : ℝ) ^ j := by ring
    have ha_pow_le : (a : ℝ) ^ j ≤ (a : ℝ) ^ k :=
      pow_le_pow_right₀ ha_one_le hj_le_k
    have hpoly_le : (Nat.choose a j : ℝ) * q ^ j ≤ (a : ℝ) ^ k :=
      le_trans hchoose_q_le ha_pow_le
    have hexp_le : rho ^ (a - j) ≤ rho ^ (a + 1 - k) := by
      have hexp_order : a + 1 - k ≤ a - j := by omega
      exact pow_le_pow_of_le_one hrho_nonneg hrho_le_one hexp_order
    have hpoly_nonneg : 0 ≤ (a : ℝ) ^ k :=
      pow_nonneg (Nat.cast_nonneg a) k
    calc
      (Nat.choose a j : ℝ) * q ^ j * rho ^ (a - j)
          ≤ (a : ℝ) ^ k * rho ^ (a - j) :=
            mul_le_mul_of_nonneg_right hpoly_le hrho_pow_nonneg
      _ ≤ (a : ℝ) ^ k * rho ^ (a + 1 - k) :=
            mul_le_mul_of_nonneg_left hexp_le hpoly_nonneg
  calc
    finiteDiscreteTopMassFailureTail k a q rho
        ≤ ∑ _j ∈ Finset.range k,
            (a : ℝ) ^ k * rho ^ (a + 1 - k) := by
          exact Finset.sum_le_sum hterm
    _ = (k : ℝ) * (a : ℝ) ^ k * rho ^ (a + 1 - k) := by
          simp [Finset.card_range, mul_assoc]

theorem finiteDiscrete_rho_pow_shift
    {k a : ℕ} {rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a) (hrho_ne : rho ≠ 0) :
    rho ^ (a + 1 - k) = rho ^ a * (rho ^ (k - 1))⁻¹ := by
  have hsum : (a + 1 - k) + (k - 1) = a := by omega
  have hpow_ne : rho ^ (k - 1) ≠ 0 := pow_ne_zero _ hrho_ne
  calc
    rho ^ (a + 1 - k)
        = rho ^ (a + 1 - k) *
            (rho ^ (k - 1) * (rho ^ (k - 1))⁻¹) := by
          field_simp [hpow_ne]
    _ = rho ^ a * (rho ^ (k - 1))⁻¹ := by
          rw [← mul_assoc, ← pow_add, hsum]

/--
Off-by-one failure-tail comparison.  The marginal proof naturally sees the
failure event in the old `a-1` sample; multiplying by one non-top draw embeds
that event into the failure event for an `a`-sample.
-/
theorem finiteDiscreteTopMassFailureTail_pred_mul_le
    {k a : ℕ} {q rho : ℝ}
    (ha_pos : 0 < a) (hq_nonneg : 0 ≤ q) (hrho_pos : 0 < rho) :
    rho * finiteDiscreteTopMassFailureTail k (a - 1) q rho ≤
      finiteDiscreteTopMassFailureTail k a q rho := by
  classical
  unfold finiteDiscreteTopMassFailureTail
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro j hj
  by_cases hj_le : j ≤ a - 1
  · have hchoose :
        (Nat.choose (a - 1) j : ℝ) ≤ (Nat.choose a j : ℝ) := by
      exact_mod_cast Nat.choose_le_choose j (Nat.pred_le a)
    have hexp : (a - 1 - j) + 1 = a - j := by omega
    have hpow_nonneg : 0 ≤ q ^ j * rho ^ (a - j) :=
      mul_nonneg (pow_nonneg hq_nonneg j)
        (pow_nonneg hrho_pos.le (a - j))
    calc
      rho * ((Nat.choose (a - 1) j : ℝ) * q ^ j *
          rho ^ (a - 1 - j))
          = (Nat.choose (a - 1) j : ℝ) * q ^ j *
              (rho * rho ^ (a - 1 - j)) := by
            ring
      _ = (Nat.choose (a - 1) j : ℝ) * (q ^ j * rho ^ (a - j)) := by
            rw [mul_comm rho (rho ^ (a - 1 - j)), ← pow_succ, hexp]
            ring
      _ ≤ (Nat.choose a j : ℝ) * (q ^ j * rho ^ (a - j)) :=
            mul_le_mul_of_nonneg_right hchoose hpow_nonneg
      _ = (Nat.choose a j : ℝ) * q ^ j * rho ^ (a - j) := by
            ring
  · have hj_gt : a - 1 < j := Nat.lt_of_not_ge hj_le
    have hchoose_zero : Nat.choose (a - 1) j = 0 :=
      Nat.choose_eq_zero_of_lt hj_gt
    have hright_nonneg :
        0 ≤ (Nat.choose a j : ℝ) * q ^ j * rho ^ (a - j) :=
      mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq_nonneg j))
        (pow_nonneg hrho_pos.le (a - j))
    simpa [hchoose_zero] using hright_nonneg

/-- Certificate-normalized version of the off-by-one failure-tail comparison. -/
theorem finiteDiscreteTopMassFailureTail_pred_le_inv_mul
    {k a : ℕ} {q rho : ℝ}
    (ha_pos : 0 < a) (hq_nonneg : 0 ≤ q) (hrho_pos : 0 < rho) :
    finiteDiscreteTopMassFailureTail k (a - 1) q rho ≤
      rho⁻¹ * finiteDiscreteTopMassFailureTail k a q rho := by
  have hmul :=
    finiteDiscreteTopMassFailureTail_pred_mul_le
      (k := k) (a := a) (q := q) (rho := rho)
      ha_pos hq_nonneg hrho_pos
  calc
    finiteDiscreteTopMassFailureTail k (a - 1) q rho
        = rho⁻¹ *
            (rho * finiteDiscreteTopMassFailureTail k (a - 1) q rho) := by
          field_simp [hrho_pos.ne']
    _ ≤ rho⁻¹ * finiteDiscreteTopMassFailureTail k a q rho :=
          mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hrho_pos.le)

/--
The binomial upper tail in the clean certificate form: the fixed exponent shift
from the paper's `rho^(a+1-k)` bound is absorbed into the positive constant.
-/
theorem finiteDiscreteTopMassFailureTail_le_polynomial_geometric_at_a
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a)
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_le_one : rho ≤ 1) :
    finiteDiscreteTopMassFailureTail k a q rho ≤
      ((k : ℝ) * (rho ^ (k - 1))⁻¹) * (a : ℝ) ^ k * rho ^ a := by
  have hbase :=
    finiteDiscreteTopMassFailureTail_le_polynomial_geometric
      hk_pos hk_le_a hq_nonneg hq_le_one hrho_pos.le hrho_le_one
  calc
    finiteDiscreteTopMassFailureTail k a q rho
        ≤ (k : ℝ) * (a : ℝ) ^ k * rho ^ (a + 1 - k) := hbase
    _ = ((k : ℝ) * (rho ^ (k - 1))⁻¹) * (a : ℝ) ^ k * rho ^ a := by
          rw [finiteDiscrete_rho_pow_shift hk_pos hk_le_a hrho_pos.ne']
          ring

/--
Finite-discrete exact-event lower bound used for the Theorem 1(i) lower
marginal: once at least `k-1` old draws are available, the exact `k-1`
top-count event has at least the single-term mass
`q^k * rho^(a+1-k)`.
-/
theorem finiteDiscreteTopMassPromotingEvent_lower_geometric
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_pred_le_a : k - 1 ≤ a)
    (hq_nonneg : 0 ≤ q) (hrho_nonneg : 0 ≤ rho) :
    q ^ k * rho ^ (a + 1 - k) ≤
      finiteDiscreteTopMassPromotingEvent k a q rho := by
  have hchoose_one_le : (1 : ℝ) ≤ (Nat.choose a (k - 1) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos hk_pred_le_a)
  have hmass_nonneg : 0 ≤ q ^ k * rho ^ (a + 1 - k) :=
    mul_nonneg (pow_nonneg hq_nonneg k)
      (pow_nonneg hrho_nonneg (a + 1 - k))
  calc
    q ^ k * rho ^ (a + 1 - k)
        = (1 : ℝ) * (q ^ k * rho ^ (a + 1 - k)) := by ring
    _ ≤ (Nat.choose a (k - 1) : ℝ) *
          (q ^ k * rho ^ (a + 1 - k)) :=
          mul_le_mul_of_nonneg_right hchoose_one_le hmass_nonneg
    _ = finiteDiscreteTopMassPromotingEvent k a q rho := by
          simp [finiteDiscreteTopMassPromotingEvent, mul_assoc]

/--
The exact-event lower bound in the clean certificate form, with the fixed
`k-1` exponent shift absorbed into the lower-tail constant.
-/
theorem finiteDiscreteTopMassPromotingEvent_lower_geometric_at_a
    {k a : ℕ} {q rho : ℝ}
    (hk_pos : 0 < k) (hk_le_a : k ≤ a)
    (hq_nonneg : 0 ≤ q) (hrho_pos : 0 < rho) :
    q ^ k * (rho ^ (k - 1))⁻¹ * rho ^ a ≤
      finiteDiscreteTopMassPromotingEvent k a q rho := by
  have hbase :=
    finiteDiscreteTopMassPromotingEvent_lower_geometric
      hk_pos (by omega : k - 1 ≤ a) hq_nonneg hrho_pos.le
  calc
    q ^ k * (rho ^ (k - 1))⁻¹ * rho ^ a
        = q ^ k * rho ^ (a + 1 - k) := by
          rw [finiteDiscrete_rho_pow_shift hk_pos hk_le_a hrho_pos.ne']
          ring
    _ ≤ finiteDiscreteTopMassPromotingEvent k a q rho := hbase

/--
The paper's equation (5) profile: target shares proportional to
`likelihood t ^ gamma`.
-/
noncomputable def gammaLikelihoodProfile {T : ℕ}
    (likelihood : ItemType T → ℝ) (gamma : ℝ) :
    GammaHomogeneityProfile T where
  gamma := gamma
  targetWeight := fun t => (likelihood t) ^ gamma

/--
The paper's equation (5)/(6) target share induced by
`gammaLikelihoodProfile`: `p_t^gamma / sum_i p_i^gamma`.
-/
theorem gammaLikelihoodProfile_targetShare_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) (gamma : ℝ) (t : ItemType T)
    (hnorm : (∑ i : ItemType T, (likelihood i) ^ gamma) ≠ 0) :
    (gammaLikelihoodProfile likelihood gamma).targetShare t =
      (likelihood t) ^ gamma /
        ∑ i : ItemType T, (likelihood i) ^ gamma := by
  exact
    GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero
      (G := gammaLikelihoodProfile likelihood gamma) (t := t)
      (by
        simpa [GammaHomogeneityProfile.normalizer, gammaLikelihoodProfile]
          using hnorm)

/-- A raw weight profile, useful for Lemma D.1(iii)'s proportional target. -/
noncomputable def weightProfile {T : ℕ}
    (weight : ItemType T → ℝ) (gamma : ℝ) :
    GammaHomogeneityProfile T where
  gamma := gamma
  targetWeight := weight

namespace GammaHomogeneityProfile

theorem weightProfile_targetShare_eq_of_sum_eq_one {T : ℕ}
    (weight : ItemType T → ℝ) (gamma : ℝ)
    (hsum : ∑ t : ItemType T, weight t = 1) (t : ItemType T) :
    (weightProfile weight gamma).targetShare t = weight t := by
  have hnorm : (weightProfile weight gamma).normalizer = 1 := by
    simpa [weightProfile, normalizer] using hsum
  rw [targetShare_eq_div_of_normalizer_ne_zero
    (G := weightProfile weight gamma) (t := t)]
  · change weight t / (weightProfile weight gamma).normalizer = weight t
    rw [hnorm]
    ring
  · rw [hnorm]
    norm_num

end GammaHomogeneityProfile

/--
A sequence of feasible finite allocations, matching the paper's `{S_n}` after
passing from sets to type-count vectors.
-/
structure AllocationSequence (T : ℕ) where
  allocation : ℕ → CountAllocation T
  feasible : ∀ N, ConsumptionModel.FeasibleAtTotal N (allocation N)

namespace AllocationSequence

/-- Type representation in the `N`th allocation of a sequence. -/
noncomputable def representation {T : ℕ}
    (seq : AllocationSequence T) (N : ℕ) (t : ItemType T) : ℝ :=
  CountAllocation.representation (seq.allocation N) t

/--
Definition 2-style asymptotic homogeneity for a concrete allocation sequence:
each type share converges to the profile's target share.
-/
def ConvergesToProfile {T : ℕ}
    (seq : AllocationSequence T) (G : GammaHomogeneityProfile T) : Prop :=
  ∀ t, Tendsto (fun N => seq.representation N t) atTop (nhds (G.targetShare t))

/--
An eventual uniform approximation rate tending to zero implies Definition 2
sequence convergence.
-/
theorem convergesToProfile_of_eventual_approx {T : ℕ}
    (seq : AllocationSequence T) (G : GammaHomogeneityProfile T)
    (ε : ℕ → ℝ)
    (hε : EconCSLib.Math.TendsToZero ε)
    (happrox : ∀ᶠ N in atTop, G.Approx (seq.allocation N) (ε N)) :
    seq.ConvergesToProfile G := by
  intro t
  have hd :
      Tendsto
        (fun N =>
          CountAllocation.representation (seq.allocation N) t - G.targetShare t)
        atTop (nhds 0) := by
    have hneg : Tendsto (fun N => -ε N) atTop (nhds 0) := by
      have h := hε.neg
      simpa using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hε
    · filter_upwards [happrox] with N hN
      exact (abs_le.mp (hN t)).1
    · filter_upwards [happrox] with N hN
      exact (abs_le.mp (hN t)).2
  have hconst :
      Tendsto (fun _ : ℕ => G.targetShare t) atTop (nhds (G.targetShare t)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun N =>
          G.targetShare t +
            (CountAllocation.representation (seq.allocation N) t - G.targetShare t))
        atTop (nhds (G.targetShare t)) := by
    simpa using hconst.add hd
  simpa [AllocationSequence.representation, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc] using hsum

end AllocationSequence

/-- A sequence selecting an optimum of the `N`th finite problem for each `N`. -/
structure OptimalAllocationSequence {T : ℕ}
    (Mseq : ℕ → ConsumptionModel T) where
  allocation : ℕ → CountAllocation T
  optimal : ∀ N, (Mseq N).IsOptimalAtTotal N (allocation N)

namespace OptimalAllocationSequence

/-- Forget optimality and keep only the feasible allocation sequence. -/
def toAllocationSequence {T : ℕ} {Mseq : ℕ → ConsumptionModel T}
    (seq : OptimalAllocationSequence Mseq) : AllocationSequence T where
  allocation := seq.allocation
  feasible := fun N => (seq.optimal N).1

@[simp] theorem toAllocationSequence_allocation {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} (seq : OptimalAllocationSequence Mseq)
    (N : ℕ) :
    seq.toAllocationSequence.allocation N = seq.allocation N := rfl

/--
The reusable Lemma D.1 endpoint: once all finite optima satisfy an asymptotic
homogeneity target, every selected sequence of finite optima converges to the
same target profile.
-/
theorem convergesToProfile_of_asymptoticHomogeneityTarget {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T}
    (seq : OptimalAllocationSequence Mseq)
    (h :
      ConsumptionModel.AsymptoticHomogeneityTarget
        Mseq G EconCSLib.Math.TendsToZero) :
    seq.toAllocationSequence.ConvergesToProfile G := by
  rcases h with ⟨ε, hε, happrox⟩
  apply AllocationSequence.convergesToProfile_of_eventual_approx
    seq.toAllocationSequence G ε hε
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact happrox N (seq.allocation N) hN (seq.optimal N)

theorem convergesToProfile_of_asymptoticHomogeneity {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T}
    (seq : OptimalAllocationSequence Mseq)
    (h : ConsumptionModel.AsymptoticHomogeneity Mseq G) :
    seq.toAllocationSequence.ConvergesToProfile G :=
  seq.convergesToProfile_of_asymptoticHomogeneityTarget h

end OptimalAllocationSequence

/--
Certificate for Theorem 1-style top-`k` asymptotic conclusions. The hard
distribution-specific work is proving the asymptotic homogeneity field from
order-statistic asymptotics and Lemma D.1.
-/
structure TopKAsymptoticHomogeneityCertificate {T : ℕ}
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ)
    (G : GammaHomogeneityProfile T) where
  asymptotic_homogeneity :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => O.toConsumptionModel likelihood k) G

/--
Bridge PRPKG's paper-local top-`k` oracle to the reusable probability
order-statistic interface in `EconCSLib`.
-/
def topKExpectationOracleOfTopKValueOracle {T : ℕ}
    (O : TopKValueOracle T) :
    EconCSLib.Probability.TopKExpectationOracle (ItemType T) where
  expectedTopSum := O.expectedTopSum

@[simp] theorem topKExpectationOracle_expectedTopSum {T : ℕ}
    (O : TopKValueOracle T) (k : ℕ) (t : ItemType T) (q : ℕ) :
    (topKExpectationOracleOfTopKValueOracle O).expectedTopSum k t q =
      O.expectedTopSum k t q := rfl

@[simp] theorem topKExpectationOracle_marginalTopK_eq {T : ℕ}
    (O : TopKValueOracle T) (k : ℕ) (t : ItemType T) (q : ℕ) :
    (topKExpectationOracleOfTopKValueOracle O).marginalTopK k t q =
      O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q := rfl

/--
Reusable probability-facing certificate for Theorem 1(ii)-(iv): the top-`k`
marginal has a common asymptotic scale and type weight.
-/
abbrev TopKScaledMarginalLimitCertificate {T : ℕ}
    (O : TopKValueOracle T) (k : ℕ)
    (scale : ℕ → ℝ) (weight : ItemType T → ℝ) :=
  EconCSLib.Probability.TopKExpectationOracle.ScaledMarginalLimitCertificate
    (topKExpectationOracleOfTopKValueOracle O) k scale weight

namespace TopKScaledMarginalLimitCertificate

theorem eventually_marginal_sandwich {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ}
    {scale : ℕ → ℝ} {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop,
      ∀ t : ItemType T,
        (1 - ε) * (scale q * weight t) ≤
            O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q ∧
          O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q ≤
            (1 + ε) * (scale q * weight t) := by
  simpa using
    EconCSLib.Probability.TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_marginal_sandwich
      C hε

theorem eventually_same_count_marginal_lt_of_weight_gap {T : ℕ}
    {O : TopKValueOracle T} {k : ℕ}
    {scale : ℕ → ℝ} {weight : ItemType T → ℝ}
    (C : TopKScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) {src dst : ItemType T}
    (hgap : (1 + ε) * weight src < (1 - ε) * weight dst) :
    ∀ᶠ q in atTop,
      O.expectedTopSum k src (q + 1) - O.expectedTopSum k src q <
        O.expectedTopSum k dst (q + 1) - O.expectedTopSum k dst q := by
  simpa using
    EconCSLib.Probability.TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_same_count_marginal_lt_of_weight_gap
      C hε hgap

end TopKScaledMarginalLimitCertificate

/--
Reusable finite-to-asymptotic bridge for Lemma D.1-style conclusions.

If all finite optima have pairwise bounded scaled counts
`count t / weight t`, then their counts are uniformly `O(1)` close to the
allocation with shares proportional to `weight`, hence the induced
representations converge at exact `C / N` rate.
-/
structure PairwiseScaledHomogeneityCertificate {T : ℕ} [NeZero T]
    (Mseq : ℕ → ConsumptionModel T) (weight : ItemType T → ℝ)
    (G : GammaHomogeneityProfile T) where
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  scaled_bound : ℝ
  scaled_bound_pos : 0 < scaled_bound
  pairwise_scaled :
    ∀ N (a : CountAllocation T), 0 < N → (Mseq N).IsOptimalAtTotal N a →
      ∀ i j,
        |(a.count i : ℝ) / weight i -
          (a.count j : ℝ) / weight j| ≤ scaled_bound

namespace PairwiseScaledHomogeneityCertificate

theorem asymptoticHomogeneityTarget {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledHomogeneityCertificate Mseq weight G) :
    ConsumptionModel.AsymptoticHomogeneityTarget Mseq G
      EconCSLib.Math.ExactInvRate := by
  refine ConsumptionModel.AsymptoticHomogeneityTarget.of_uniform_count_abs_error
    (C := hcert.scaled_bound * ∑ i : ItemType T, weight i)
    ?_ ?_
  · exact mul_pos hcert.scaled_bound_pos
      (Finset.sum_pos (fun i _ => hcert.weight_pos i) Finset.univ_nonempty)
  · intro N a hN hopt t
    have hNsum : (∑ i : ItemType T, (a.count i : ℝ)) = (N : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hopt.1
    have hscaled :=
      GammaHomogeneityProfile.count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded
        a weight hNsum hcert.weight_pos
        (le_of_lt hcert.scaled_bound_pos)
        (hcert.pairwise_scaled N a hN hopt) t
    have htarget :
        (N : ℝ) * G.targetShare t =
          weight t * ((N : ℝ) / ∑ i : ItemType T, weight i) := by
      rw [hcert.targetShare_eq t]
      ring
    have hweight_le_sum :
        weight t ≤ ∑ i : ItemType T, weight i := by
      exact Finset.single_le_sum
        (fun i _ => le_of_lt (hcert.weight_pos i)) (Finset.mem_univ t)
    calc
      |(a.count t : ℝ) - (N : ℝ) * G.targetShare t|
          = |(a.count t : ℝ) -
              weight t * ((N : ℝ) / ∑ i : ItemType T, weight i)| := by
            rw [htarget]
      _ ≤ hcert.scaled_bound * weight t := hscaled
      _ ≤ hcert.scaled_bound * ∑ i : ItemType T, weight i := by
            exact mul_le_mul_of_nonneg_left hweight_le_sum
              (le_of_lt hcert.scaled_bound_pos)

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledHomogeneityCertificate Mseq weight G) :
    ConsumptionModel.AsymptoticHomogeneity Mseq G :=
  ConsumptionModel.AsymptoticHomogeneityTarget.of_exactInvRate
    hcert.asymptoticHomogeneityTarget

end PairwiseScaledHomogeneityCertificate

/--
Sublinear pairwise-scaled bridge for Lemma D.1-style asymptotic proofs.

This weakens `PairwiseScaledHomogeneityCertificate`: the scaled counts may
differ by `ε_N * N`, provided `ε_N → 0`. After averaging, representation error
is at most `ε_N` times the total target weight.
-/
structure PairwiseScaledSublinearHomogeneityCertificate {T : ℕ} [NeZero T]
    (Mseq : ℕ → ConsumptionModel T) (weight : ItemType T → ℝ)
    (G : GammaHomogeneityProfile T) where
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : EconCSLib.Math.TendsToZero error
  pairwise_scaled :
    ∀ N (a : CountAllocation T), 0 < N → (Mseq N).IsOptimalAtTotal N a →
      ∀ i j,
        |(a.count i : ℝ) / weight i -
          (a.count j : ℝ) / weight j| ≤ error N * (N : ℝ)

namespace PairwiseScaledSublinearHomogeneityCertificate

noncomputable def toShared {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledSublinearHomogeneityCertificate Mseq weight G) :
    EconCSLib.Allocation.PairwiseScaledSublinearProfileCertificate
      (fun N => (Mseq N).likelihood)
      (fun N => (Mseq N).valueOfCount)
      weight G.targetShare where
  weight_pos := hcert.weight_pos
  target_eq := hcert.targetShare_eq
  error := hcert.error
  error_nonneg := hcert.error_nonneg
  error_tends_to_zero := hcert.error_tends_to_zero
  pairwise_scaled := by
    intro N a hN hopt i j
    have hopt' : (Mseq N).IsOptimalAtTotal N a := by
      simpa [EconCSLib.Allocation.IsOptimalAtTotal,
        ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
        ConsumptionModel.objective] using hopt
    exact hcert.pairwise_scaled N a hN hopt' i j

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledSublinearHomogeneityCertificate Mseq weight G) :
    ConsumptionModel.AsymptoticHomogeneity Mseq G := by
  have hgeneric :
      EconCSLib.Allocation.AsymptoticProfile
        (fun N => (Mseq N).likelihood)
        (fun N => (Mseq N).valueOfCount)
        G.targetShare :=
    hcert.toShared.asymptoticProfile
  rcases hgeneric with ⟨ε, hε, happrox⟩
  refine ⟨ε, hε, ?_⟩
  intro N a hN hopt
  have hopt' :
      EconCSLib.Allocation.IsOptimalAtTotal
        (Mseq N).likelihood (Mseq N).valueOfCount N a := by
    simpa [EconCSLib.Allocation.IsOptimalAtTotal,
      ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
      ConsumptionModel.objective] using hopt
  have happ := happrox N a hN hopt'
  simpa [EconCSLib.Allocation.HasApproxShare,
    GammaHomogeneityProfile.Approx, CountAllocation.HasApproxRepresentation,
    CountAllocation.representation] using happ

end PairwiseScaledSublinearHomogeneityCertificate

/--
FOC-based sublinear pairwise-scaled bridge.

This is the reusable endpoint for asymptotic product estimates: if every
scaled-count gap larger than `error N * N` would make the source backward
marginal strictly smaller than the destination forward marginal, then the
finite first-order condition rules out such gaps in every optimum. The existing
sublinear pairwise-scaled bridge then gives asymptotic homogeneity.
-/
structure PairwiseScaledSublinearFOCCertificate {T : ℕ} [NeZero T]
    (Mseq : ℕ → ConsumptionModel T) (weight : ItemType T → ℝ)
    (G : GammaHomogeneityProfile T) where
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : EconCSLib.Math.TendsToZero error
  large_gap_backward_lt_forward :
    ∀ N (a : CountAllocation T), 0 < N → (Mseq N).IsOptimalAtTotal N a →
      ∀ src dst,
        error N * (N : ℝ) <
          (a.count src : ℝ) / weight src -
            (a.count dst : ℝ) / weight dst →
        (Mseq N).weightedBackwardMarginal src (a.count src) <
          (Mseq N).weightedForwardMarginal dst (a.count dst)

namespace PairwiseScaledSublinearFOCCertificate

noncomputable def toShared {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledSublinearFOCCertificate Mseq weight G) :
    EconCSLib.Allocation.PairwiseScaledSublinearFOCCertificate
      (fun N => (Mseq N).likelihood)
      (fun N => (Mseq N).valueOfCount)
      weight G.targetShare where
  weight_pos := hcert.weight_pos
  target_eq := hcert.targetShare_eq
  error := hcert.error
  error_nonneg := hcert.error_nonneg
  error_tends_to_zero := hcert.error_tends_to_zero
  large_gap_backward_lt_forward := by
    intro N a hN hopt src dst hgap
    have hopt' : (Mseq N).IsOptimalAtTotal N a := by
      simpa [EconCSLib.Allocation.IsOptimalAtTotal,
        ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
        ConsumptionModel.objective] using hopt
    have hdom :=
      hcert.large_gap_backward_lt_forward N a hN hopt' src dst hgap
    simpa [ConsumptionModel.weightedBackwardMarginal,
      ConsumptionModel.weightedForwardMarginal, ConsumptionModel.marginalValue,
      EconCSLib.Allocation.weightedBackwardMarginal,
      EconCSLib.Allocation.weightedForwardMarginal,
      EconCSLib.Allocation.marginal] using hdom

noncomputable def toPairwiseScaledSublinearHomogeneityCertificate
    {T : ℕ} [NeZero T] {Mseq : ℕ → ConsumptionModel T}
    {weight : ItemType T → ℝ} {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledSublinearFOCCertificate Mseq weight G) :
    PairwiseScaledSublinearHomogeneityCertificate Mseq weight G :=
  let hshared := hcert.toShared.toPairwiseScaledSublinearProfileCertificate
  { weight_pos := hshared.weight_pos
    targetShare_eq := hshared.target_eq
    error := hshared.error
    error_nonneg := hshared.error_nonneg
    error_tends_to_zero := hshared.error_tends_to_zero
    pairwise_scaled := by
      intro N a hN hopt i j
      have hopt' :
          EconCSLib.Allocation.IsOptimalAtTotal
            (Mseq N).likelihood (Mseq N).valueOfCount N a := by
        simpa [EconCSLib.Allocation.IsOptimalAtTotal,
          ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
          ConsumptionModel.objective] using hopt
      exact hshared.pairwise_scaled N a hN hopt' i j }

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledSublinearFOCCertificate Mseq weight G) :
    ConsumptionModel.AsymptoticHomogeneity Mseq G :=
  hcert.toPairwiseScaledSublinearHomogeneityCertificate.asymptoticHomogeneity

end PairwiseScaledSublinearFOCCertificate

/--
Floor-aware version of the pairwise-scaled FOC bridge.

Distribution-specific estimates often prove the large-gap marginal dominance
only after every compared count is above a fixed floor and after the total
problem size is large.  This certificate records those eventual facts and
absorbs the finite prefix by using a deliberately large temporary error, then
produces the clean `PairwiseScaledSublinearFOCCertificate`.
-/
structure PairwiseScaledEventualSublinearFOCCertificate {T : ℕ} [NeZero T]
    (Mseq : ℕ → ConsumptionModel T) (weight : ItemType T → ℝ)
    (G : GammaHomogeneityProfile T) where
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  base_error : ℕ → ℝ
  base_error_nonneg : ∀ N, 0 ≤ base_error N
  base_error_tends_to_zero : EconCSLib.Math.TendsToZero base_error
  floor : ℕ
  count_floor_eventually :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N → (Mseq N).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t
  large_gap_backward_lt_forward_after_floor :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N → (Mseq N).IsOptimalAtTotal N a →
        ∀ src dst,
          floor < a.count src →
          floor < a.count dst →
          base_error N * (N : ℝ) <
            (a.count src : ℝ) / weight src -
              (a.count dst : ℝ) / weight dst →
          (Mseq N).weightedBackwardMarginal src (a.count src) <
            (Mseq N).weightedForwardMarginal dst (a.count dst)

namespace PairwiseScaledEventualSublinearFOCCertificate

noncomputable def toShared {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledEventualSublinearFOCCertificate Mseq weight G) :
    EconCSLib.Allocation.PairwiseScaledEventualSublinearFOCCertificate
      (fun N => (Mseq N).likelihood)
      (fun N => (Mseq N).valueOfCount)
      weight G.targetShare where
  weight_pos := hcert.weight_pos
  target_eq := hcert.targetShare_eq
  baseError := hcert.base_error
  baseError_nonneg := hcert.base_error_nonneg
  baseError_tends_to_zero := hcert.base_error_tends_to_zero
  floor := hcert.floor
  count_floor_eventually := by
    filter_upwards [hcert.count_floor_eventually] with N hN a hNpos hopt
    have hopt' : (Mseq N).IsOptimalAtTotal N a := by
      simpa [EconCSLib.Allocation.IsOptimalAtTotal,
        ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
        ConsumptionModel.objective] using hopt
    exact hN a hNpos hopt'
  large_gap_backward_lt_forward_after_floor := by
    filter_upwards [hcert.large_gap_backward_lt_forward_after_floor] with
      N hN a hNpos hopt src dst hsrc hdst hgap
    have hopt' : (Mseq N).IsOptimalAtTotal N a := by
      simpa [EconCSLib.Allocation.IsOptimalAtTotal,
        ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
        ConsumptionModel.objective] using hopt
    have hdom := hN a hNpos hopt' src dst hsrc hdst hgap
    simpa [ConsumptionModel.weightedBackwardMarginal,
      ConsumptionModel.weightedForwardMarginal, ConsumptionModel.marginalValue,
      EconCSLib.Allocation.weightedBackwardMarginal,
      EconCSLib.Allocation.weightedForwardMarginal,
      EconCSLib.Allocation.marginal] using hdom

noncomputable def toPairwiseScaledSublinearFOCCertificate
    {T : ℕ} [NeZero T] {Mseq : ℕ → ConsumptionModel T}
    {weight : ItemType T → ℝ} {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledEventualSublinearFOCCertificate Mseq weight G) :
    PairwiseScaledSublinearFOCCertificate Mseq weight G :=
  let hshared := hcert.toShared.toPairwiseScaledSublinearFOCCertificate
  { weight_pos := hshared.weight_pos
    targetShare_eq := hshared.target_eq
    error := hshared.error
    error_nonneg := hshared.error_nonneg
    error_tends_to_zero := hshared.error_tends_to_zero
    large_gap_backward_lt_forward := by
      intro N a hN hopt src dst hgap
      have hopt' :
          EconCSLib.Allocation.IsOptimalAtTotal
            (Mseq N).likelihood (Mseq N).valueOfCount N a := by
        simpa [EconCSLib.Allocation.IsOptimalAtTotal,
          ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
          ConsumptionModel.objective] using hopt
      have hdom :=
        hshared.large_gap_backward_lt_forward N a hN hopt' src dst hgap
      simpa [ConsumptionModel.weightedBackwardMarginal,
        ConsumptionModel.weightedForwardMarginal, ConsumptionModel.marginalValue,
        EconCSLib.Allocation.weightedBackwardMarginal,
        EconCSLib.Allocation.weightedForwardMarginal,
        EconCSLib.Allocation.marginal] using hdom }

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {Mseq : ℕ → ConsumptionModel T} {weight : ItemType T → ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : PairwiseScaledEventualSublinearFOCCertificate Mseq weight G) :
    ConsumptionModel.AsymptoticHomogeneity Mseq G := by
  have hgeneric :
      EconCSLib.Allocation.AsymptoticProfile
        (fun N => (Mseq N).likelihood)
        (fun N => (Mseq N).valueOfCount)
        G.targetShare :=
    hcert.toShared.asymptoticProfile
  rcases hgeneric with ⟨ε, hε, happrox⟩
  refine ⟨ε, hε, ?_⟩
  intro N a hN hopt
  have hopt' :
      EconCSLib.Allocation.IsOptimalAtTotal
        (Mseq N).likelihood (Mseq N).valueOfCount N a := by
    simpa [EconCSLib.Allocation.IsOptimalAtTotal,
      ConsumptionModel.IsOptimalAtTotal, ConsumptionModel.FeasibleAtTotal,
      ConsumptionModel.objective] using hopt
  have happ := happrox N a hN hopt'
  simpa [EconCSLib.Allocation.HasApproxShare,
    GammaHomogeneityProfile.Approx, CountAllocation.HasApproxRepresentation,
    CountAllocation.representation] using happ

end PairwiseScaledEventualSublinearFOCCertificate

/--
Top-`k` source-shaped sublinear FOC certificate for Theorem 1(i).

For the finite-discrete branch, the remaining probability/order-statistic work
should prove the `large_gap_backward_lt_forward` field: if one type has more
than `error N * N` extra recommendations relative to another, then the source's
last-item top-`k` marginal is strictly smaller than the destination's next-item
top-`k` marginal. This specialized certificate avoids exposing reviewers to
the generic scaled-weight interface when the target is uniform.
-/
structure TopKUniformSublinearFOCCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : EconCSLib.Math.TendsToZero error
  large_gap_backward_lt_forward :
    ∀ N (a : CountAllocation T), 0 < N →
      (O.toConsumptionModel likelihood k).IsOptimalAtTotal N a →
      ∀ src dst,
        error N * (N : ℝ) < (a.count src : ℝ) - (a.count dst : ℝ) →
        likelihood src *
            (O.expectedTopSum k src (a.count src) -
              O.expectedTopSum k src (a.count src - 1)) <
          likelihood dst *
            (O.expectedTopSum k dst (a.count dst + 1) -
              O.expectedTopSum k dst (a.count dst))

namespace TopKUniformSublinearFOCCertificate

noncomputable def toPairwiseScaledSublinearFOCCertificate {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformSublinearFOCCertificate O likelihood k) :
    PairwiseScaledSublinearFOCCertificate
      (fun _ => O.toConsumptionModel likelihood k)
      (fun _ : ItemType T => (1 : ℝ)) (uniformProfile T) where
  weight_pos := by
    intro t
    norm_num
  targetShare_eq := by
    intro t
    rw [uniformProfile_targetShare]
    simp [Finset.sum_const, Fintype.card_fin]
  error := hcert.error
  error_nonneg := hcert.error_nonneg
  error_tends_to_zero := hcert.error_tends_to_zero
  large_gap_backward_lt_forward := by
    intro N a hN hopt src dst hgap
    have hgap_unweighted :
        hcert.error N * (N : ℝ) <
          (a.count src : ℝ) - (a.count dst : ℝ) := by
      simpa using hgap
    have hC_nonneg : 0 ≤ hcert.error N * (N : ℝ) :=
      mul_nonneg (hcert.error_nonneg N) (Nat.cast_nonneg N)
    have hdiff_pos :
        0 < (a.count src : ℝ) - (a.count dst : ℝ) :=
      lt_of_le_of_lt hC_nonneg hgap_unweighted
    have hsrc_pos : 0 < a.count src := by
      by_contra hnot
      have hzero : a.count src = 0 := Nat.eq_zero_of_not_pos hnot
      have hdst_nonneg : 0 ≤ (a.count dst : ℝ) := Nat.cast_nonneg _
      rw [hzero] at hdiff_pos
      have hnonpos : (0 : ℝ) - (a.count dst : ℝ) ≤ 0 := by
        linarith
      exact (not_lt_of_ge hnonpos) (by simpa using hdiff_pos)
    have hdom :=
      hcert.large_gap_backward_lt_forward N a hN hopt src dst hgap_unweighted
    unfold ConsumptionModel.weightedBackwardMarginal
      ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
      EconCSLib.Allocation.marginal TopKValueOracle.toConsumptionModel at *
    rw [dif_neg hsrc_pos.ne'] at *
    exact hdom

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformSublinearFOCCertificate O likelihood k) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => O.toConsumptionModel likelihood k) (uniformProfile T) :=
  hcert.toPairwiseScaledSublinearFOCCertificate.asymptoticHomogeneity

end TopKUniformSublinearFOCCertificate

/--
Count-floor certificate for source Theorem 1(i)'s top-`k` route.

If every sufficiently large source count has a last-item marginal below every
destination count at or below `floor`, then no large finite optimum can leave a
type at or below that floor: moving one recommendation from an overlarge source
to the underfilled destination would strictly improve the objective.
-/
structure TopKUniformCountFloorCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  floor : ℕ
  source_threshold : ℕ
  floor_le_source_threshold : floor ≤ source_threshold
  backward_lt_forward_to_floor :
    ∀ src dst qsrc qdst,
      source_threshold < qsrc →
      qdst ≤ floor →
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1)) <
        likelihood dst *
          (O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst)

namespace TopKUniformCountFloorCertificate

theorem exists_count_gt_source_threshold {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformCountFloorCertificate O likelihood k)
    {N : ℕ} (a : CountAllocation T)
    (htotal : EconCSLib.Allocation.total a = N)
    (hlarge : T * hcert.source_threshold < N) :
    ∃ src : ItemType T, hcert.source_threshold < a.count src := by
  by_contra hnone
  push Not at hnone
  have hsum_le :
      EconCSLib.Allocation.total a ≤ T * hcert.source_threshold := by
    unfold EconCSLib.Allocation.total
    calc
      (∑ t : ItemType T, a.count t)
          ≤ ∑ _t : ItemType T, hcert.source_threshold := by
            exact Finset.sum_le_sum (fun t _ => hnone t)
      _ = T * hcert.source_threshold := by
            simp [Finset.sum_const, Fintype.card_fin]
  rw [htotal] at hsum_le
  exact (not_lt_of_ge hsum_le) hlarge

theorem count_floor_eventually {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformCountFloorCertificate O likelihood k) :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N →
        (O.toConsumptionModel likelihood k).IsOptimalAtTotal N a →
        ∀ t, hcert.floor < a.count t := by
  refine eventually_atTop.2 ?_
  refine ⟨T * hcert.source_threshold + 1, ?_⟩
  intro N hN a hNpos hopt dst
  by_contra hnot
  have hdst_le_floor : a.count dst ≤ hcert.floor := le_of_not_gt hnot
  have hlarge : T * hcert.source_threshold < N := by omega
  obtain ⟨src, hsrc_large⟩ :=
    hcert.exists_count_gt_source_threshold a hopt.1 hlarge
  have hsrc_pos : 0 < a.count src := by
    exact Nat.zero_lt_of_lt hsrc_large
  have hne : src ≠ dst := by
    intro hsame
    subst dst
    exact (not_lt_of_ge
      (le_trans hdst_le_floor hcert.floor_le_source_threshold)) hsrc_large
  have hfoc :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := O.toConsumptionModel likelihood k) (N := N) (a := a)
      (src := src) (dst := dst) hopt hne hsrc_pos
  have hdom :=
    hcert.backward_lt_forward_to_floor src dst (a.count src) (a.count dst)
      hsrc_large hdst_le_floor
  unfold ConsumptionModel.weightedBackwardMarginal
    ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
    EconCSLib.Allocation.marginal TopKValueOracle.toConsumptionModel at hfoc
  rw [dif_neg hsrc_pos.ne'] at hfoc
  exact (not_lt_of_ge hfoc) hdom

end TopKUniformCountFloorCertificate

/--
Eventual, floor-dependent top-`k` FOC certificate for Theorem 1(i).

Distribution-level order-statistic estimates are typically only available once
both compared type counts are above a fixed floor and the total slate size is
large.  This certificate records that source-shaped obligation, together with
the matching eventual count-floor fact for finite optima.  The wrapper below
absorbs the finite prefix by assigning a deliberately large temporary error,
then produces the clean `TopKUniformSublinearFOCCertificate` consumed by the
paper-facing theorem.
-/
structure TopKUniformEventualSublinearFOCCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  base_error : ℕ → ℝ
  base_error_nonneg : ∀ N, 0 ≤ base_error N
  base_error_tends_to_zero : EconCSLib.Math.TendsToZero base_error
  floor : ℕ
  count_floor_eventually :
    ∀ᶠ N in atTop,
      ∀ a : CountAllocation T, 0 < N →
        (O.toConsumptionModel likelihood k).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t
  large_gap_backward_lt_forward_after_floor :
    ∀ᶠ N in atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        floor < qsrc →
        floor < qdst →
        base_error N * (N : ℝ) < (qsrc : ℝ) - (qdst : ℝ) →
        likelihood src *
            (O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1)) <
          likelihood dst *
            (O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst)

namespace TopKUniformEventualSublinearFOCCertificate

noncomputable def toPairwiseScaledEventualSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformEventualSublinearFOCCertificate O likelihood k) :
    PairwiseScaledEventualSublinearFOCCertificate
      (fun _ => O.toConsumptionModel likelihood k)
      (fun _ : ItemType T => (1 : ℝ)) (uniformProfile T) where
  weight_pos := by
    intro t
    norm_num
  targetShare_eq := by
    intro t
    rw [uniformProfile_targetShare]
    simp [Finset.sum_const, Fintype.card_fin]
  base_error := hcert.base_error
  base_error_nonneg := hcert.base_error_nonneg
  base_error_tends_to_zero := hcert.base_error_tends_to_zero
  floor := hcert.floor
  count_floor_eventually := hcert.count_floor_eventually
  large_gap_backward_lt_forward_after_floor := by
    filter_upwards [hcert.large_gap_backward_lt_forward_after_floor] with
      N hN a _hNpos hopt src dst hsrc hdst hgap
    have hsrc_count_le_N : a.count src ≤ N := by
      have hle := EconCSLib.Allocation.count_le_total a src
      rw [hopt.1] at hle
      exact hle
    have hdst_count_le_N : a.count dst ≤ N := by
      have hle := EconCSLib.Allocation.count_le_total a dst
      rw [hopt.1] at hle
      exact hle
    have hgap_unweighted :
        hcert.base_error N * (N : ℝ) <
          (a.count src : ℝ) - (a.count dst : ℝ) := by
      simpa using hgap
    have hdom :=
      hN src dst (a.count src) (a.count dst)
        hsrc_count_le_N hdst_count_le_N hsrc hdst hgap_unweighted
    have hsrc_pos : 0 < a.count src := Nat.zero_lt_of_lt hsrc
    unfold ConsumptionModel.weightedBackwardMarginal
      ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
      EconCSLib.Allocation.marginal TopKValueOracle.toConsumptionModel
    rw [dif_neg hsrc_pos.ne']
    exact hdom

noncomputable def of_count_floor_certificate {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hfloor : TopKUniformCountFloorCertificate O likelihood k)
    (base_error : ℕ → ℝ)
    (base_error_nonneg : ∀ N, 0 ≤ base_error N)
    (base_error_tends_to_zero : EconCSLib.Math.TendsToZero base_error)
    (large_gap_backward_lt_forward_after_floor :
      ∀ᶠ N in atTop,
        ∀ src dst qsrc qdst,
          qsrc ≤ N →
          qdst ≤ N →
          hfloor.floor < qsrc →
          hfloor.floor < qdst →
          base_error N * (N : ℝ) < (qsrc : ℝ) - (qdst : ℝ) →
          likelihood src *
              (O.expectedTopSum k src qsrc -
                O.expectedTopSum k src (qsrc - 1)) <
            likelihood dst *
              (O.expectedTopSum k dst (qdst + 1) -
                O.expectedTopSum k dst qdst)) :
    TopKUniformEventualSublinearFOCCertificate O likelihood k where
  base_error := base_error
  base_error_nonneg := base_error_nonneg
  base_error_tends_to_zero := base_error_tends_to_zero
  floor := hfloor.floor
  count_floor_eventually := hfloor.count_floor_eventually
  large_gap_backward_lt_forward_after_floor :=
    large_gap_backward_lt_forward_after_floor

noncomputable def toTopKUniformSublinearFOCCertificate {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformEventualSublinearFOCCertificate O likelihood k) :
    TopKUniformSublinearFOCCertificate O likelihood k :=
  let hpair :=
    hcert.toPairwiseScaledEventualSublinearFOCCertificate
      |>.toPairwiseScaledSublinearFOCCertificate
  { error := hpair.error
    error_nonneg := hpair.error_nonneg
    error_tends_to_zero := hpair.error_tends_to_zero
    large_gap_backward_lt_forward := by
      intro N a hN hopt src dst hgap
      have hgap_scaled :
          hpair.error N * (N : ℝ) <
            (a.count src : ℝ) / (1 : ℝ) -
              (a.count dst : ℝ) / (1 : ℝ) := by
        simpa using hgap
      have hdom :=
        hpair.large_gap_backward_lt_forward N a hN hopt src dst hgap_scaled
      have hC_nonneg : 0 ≤ hpair.error N * (N : ℝ) :=
        mul_nonneg (hpair.error_nonneg N) (Nat.cast_nonneg N)
      have hdiff_pos :
          0 < (a.count src : ℝ) - (a.count dst : ℝ) :=
        lt_of_le_of_lt hC_nonneg hgap
      have hsrc_pos : 0 < a.count src := by
        by_contra hnot
        have hzero : a.count src = 0 := Nat.eq_zero_of_not_pos hnot
        have hdst_nonneg : 0 ≤ (a.count dst : ℝ) := Nat.cast_nonneg _
        rw [hzero] at hdiff_pos
        have hnonpos : (0 : ℝ) - (a.count dst : ℝ) ≤ 0 := by
          linarith
        exact (not_lt_of_ge hnonpos) (by simpa using hdiff_pos)
      unfold ConsumptionModel.weightedBackwardMarginal
        ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
        EconCSLib.Allocation.marginal TopKValueOracle.toConsumptionModel at hdom
      rw [dif_neg hsrc_pos.ne'] at hdom
      exact hdom }

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformEventualSublinearFOCCertificate O likelihood k) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => O.toConsumptionModel likelihood k) (uniformProfile T) :=
  hcert.toTopKUniformSublinearFOCCertificate.asymptoticHomogeneity

end TopKUniformEventualSublinearFOCCertificate

/--
Finite-discrete geometric marginal-bound certificate for Theorem 1(i).

The source proof bounds top-`k` marginals by a polynomial-times-geometric upper
tail and a geometric lower tail.  This certificate is the optimization-facing
form of that probability estimate: it supplies the marginal bounds and a
sublinear integer gap schedule whose polynomial-geometric product is eventually
smaller than the lower-tail constant.
-/
structure TopKUniformGeometricMarginalBoundCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  floor : ℕ
  source_threshold : ℕ
  floor_le_source_threshold : floor ≤ source_threshold
  floor_backward_lt_forward :
    ∀ src dst qsrc qdst,
      source_threshold < qsrc →
      qdst ≤ floor →
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1)) <
        likelihood dst *
          (O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst)
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  degree : ℕ
  gap : ℕ → ℕ
  gap_error_tends_to_zero :
    EconCSLib.Math.TendsToZero
      (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ))
  gap_dominance_eventually :
    ∀ᶠ (N : ℕ) in atTop,
      upper * (N : ℝ) ^ degree * rho ^ (gap N) < lower
  weighted_backward_upper :
    ∀ src qsrc,
      floor < qsrc →
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1)) ≤
        upper * (qsrc : ℝ) ^ degree * rho ^ qsrc
  weighted_forward_lower :
    ∀ dst qdst,
      floor < qdst →
      lower * rho ^ qdst ≤
        likelihood dst *
          (O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst)

namespace TopKUniformGeometricMarginalBoundCertificate

noncomputable def toCountFloorCertificate {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert :
      TopKUniformGeometricMarginalBoundCertificate O likelihood k) :
    TopKUniformCountFloorCertificate O likelihood k where
  floor := hcert.floor
  source_threshold := hcert.source_threshold
  floor_le_source_threshold := hcert.floor_le_source_threshold
  backward_lt_forward_to_floor := hcert.floor_backward_lt_forward

noncomputable def toEventualSublinearFOCCertificate {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert :
      TopKUniformGeometricMarginalBoundCertificate O likelihood k) :
    TopKUniformEventualSublinearFOCCertificate O likelihood k := by
  classical
  refine
    TopKUniformEventualSublinearFOCCertificate.of_count_floor_certificate
      hcert.toCountFloorCertificate
      (fun N => ((hcert.gap N + 1 : ℕ) : ℝ) / (N : ℝ))
      ?_ hcert.gap_error_tends_to_zero ?_
  · intro N
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N)
  · filter_upwards
      [hcert.gap_dominance_eventually, eventually_gt_atTop 0]
      with N hdom hNpos src dst qsrc qdst hsrc_le_N hdst_le_N
        hsrc_floor hdst_floor hgap
    have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
    have hgap_real :
        (((hcert.gap N + 1 : ℕ) : ℝ) <
          (qsrc : ℝ) - (qdst : ℝ)) := by
      simpa [div_mul_cancel₀ _ hN_ne] using hgap
    have hsum_real :
        ((qdst + (hcert.gap N + 1) : ℕ) : ℝ) < (qsrc : ℝ) := by
      rw [Nat.cast_add]
      linarith
    have hsum_nat :
        qdst + (hcert.gap N + 1) < qsrc := by
      exact_mod_cast hsum_real
    have hqdst_gap_le_qsrc : qdst + hcert.gap N ≤ qsrc := by
      omega
    have hpow_gap :
        hcert.rho ^ qsrc ≤ hcert.rho ^ qdst * hcert.rho ^ hcert.gap N := by
      calc
        hcert.rho ^ qsrc
            ≤ hcert.rho ^ (qdst + hcert.gap N) :=
              pow_le_pow_of_le_one hcert.rho_pos.le hcert.rho_lt_one.le
                hqdst_gap_le_qsrc
        _ = hcert.rho ^ qdst * hcert.rho ^ hcert.gap N := by
              rw [pow_add]
    have hqsrc_pow_le_N_pow :
        (qsrc : ℝ) ^ hcert.degree ≤ (N : ℝ) ^ hcert.degree := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg qsrc)
        (by exact_mod_cast hsrc_le_N) hcert.degree
    have hupper_nonneg : 0 ≤ hcert.upper := le_of_lt hcert.upper_pos
    have hNpow_nonneg : 0 ≤ (N : ℝ) ^ hcert.degree :=
      pow_nonneg (Nat.cast_nonneg N) hcert.degree
    have hrho_qsrc_nonneg : 0 ≤ hcert.rho ^ qsrc :=
      pow_nonneg hcert.rho_pos.le qsrc
    have hback_upper :=
      hcert.weighted_backward_upper src qsrc hsrc_floor
    have hforward_lower :=
      hcert.weighted_forward_lower dst qdst hdst_floor
    have hback_le_gap :
        likelihood src *
            (O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1)) ≤
          hcert.upper * (N : ℝ) ^ hcert.degree *
            (hcert.rho ^ qdst * hcert.rho ^ hcert.gap N) := by
      calc
        likelihood src *
            (O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1))
            ≤ hcert.upper * (qsrc : ℝ) ^ hcert.degree *
                hcert.rho ^ qsrc := hback_upper
        _ ≤ hcert.upper * (N : ℝ) ^ hcert.degree *
                hcert.rho ^ qsrc := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hqsrc_pow_le_N_pow hupper_nonneg)
                hrho_qsrc_nonneg
        _ ≤ hcert.upper * (N : ℝ) ^ hcert.degree *
                (hcert.rho ^ qdst * hcert.rho ^ hcert.gap N) := by
              exact mul_le_mul_of_nonneg_left hpow_gap
                (mul_nonneg hupper_nonneg hNpow_nonneg)
    have hgap_weighted_lt :
        hcert.upper * (N : ℝ) ^ hcert.degree *
            (hcert.rho ^ qdst * hcert.rho ^ hcert.gap N) <
          hcert.lower * hcert.rho ^ qdst := by
      have hrho_qdst_pos : 0 < hcert.rho ^ qdst :=
        pow_pos hcert.rho_pos qdst
      have hmul :=
        mul_lt_mul_of_pos_right hdom hrho_qdst_pos
      calc
        hcert.upper * (N : ℝ) ^ hcert.degree *
            (hcert.rho ^ qdst * hcert.rho ^ hcert.gap N)
            = (hcert.upper * (N : ℝ) ^ hcert.degree *
                hcert.rho ^ hcert.gap N) * hcert.rho ^ qdst := by
              ring
        _ < hcert.lower * hcert.rho ^ qdst := hmul
    exact lt_of_le_of_lt hback_le_gap
      (lt_of_lt_of_le hgap_weighted_lt hforward_lower)

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert :
      TopKUniformGeometricMarginalBoundCertificate O likelihood k) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => O.toConsumptionModel likelihood k) (uniformProfile T) :=
  hcert.toEventualSublinearFOCCertificate.asymptoticHomogeneity

end TopKUniformGeometricMarginalBoundCertificate

/--
Finite-discrete geometric tail certificate for Theorem 1(i).

This is one step closer to the source distribution argument than
`TopKUniformGeometricMarginalBoundCertificate`: it assumes a positive lower
bound on the finitely many destination marginals up to the floor, and derives
the large-source/small-destination count-floor comparison from the geometric
upper tail.
-/
structure TopKUniformGeometricTailCertificate {T : ℕ} [NeZero T]
    (O : TopKValueOracle T) (likelihood : ItemType T → ℝ) (k : ℕ) where
  rho : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  floor : ℕ
  small_forward_lower : ℝ
  small_forward_lower_pos : 0 < small_forward_lower
  weighted_forward_lower_to_floor :
    ∀ dst qdst,
      qdst ≤ floor →
        small_forward_lower ≤
          likelihood dst *
            (O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst)
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  degree : ℕ
  gap : ℕ → ℕ
  gap_error_tends_to_zero :
    EconCSLib.Math.TendsToZero
      (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ))
  gap_dominance_eventually :
    ∀ᶠ (N : ℕ) in atTop,
      upper * (N : ℝ) ^ degree * rho ^ (gap N) < lower
  weighted_backward_upper :
    ∀ src qsrc,
      floor < qsrc →
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1)) ≤
        upper * (qsrc : ℝ) ^ degree * rho ^ qsrc
  weighted_forward_lower :
    ∀ dst qdst,
      floor < qdst →
      lower * rho ^ qdst ≤
        likelihood dst *
          (O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst)

namespace TopKUniformGeometricTailCertificate

noncomputable def of_binomial_event_bounds {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (q rho : ℝ)
    (hk_pos : 0 < k)
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (small_forward_lower : ℝ)
    (small_forward_lower_pos : 0 < small_forward_lower)
    (weighted_forward_lower_to_floor :
      ∀ dst qdst,
        qdst ≤ floor →
          small_forward_lower ≤
            likelihood dst *
              (O.expectedTopSum k dst (qdst + 1) -
                O.expectedTopSum k dst qdst))
    (backwardLoss forwardGain : ℝ)
    (backwardLoss_pos : 0 < backwardLoss)
    (forwardGain_pos : 0 < forwardGain)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      EconCSLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in atTop,
        (backwardLoss * ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          forwardGain * q ^ k * (rho ^ (k - 1))⁻¹)
    (weighted_backward_upper_by_failure_tail :
      ∀ src qsrc,
        floor < qsrc →
          likelihood src *
            (O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1)) ≤
            backwardLoss * finiteDiscreteTopMassFailureTail k qsrc q rho)
    (weighted_forward_lower_by_promoting_event :
      ∀ dst qdst,
        floor < qdst →
          forwardGain * finiteDiscreteTopMassPromotingEvent k qdst q rho ≤
            likelihood dst *
              (O.expectedTopSum k dst (qdst + 1) -
                O.expectedTopSum k dst qdst)) :
    TopKUniformGeometricTailCertificate O likelihood k where
  rho := rho
  rho_pos := hrho_pos
  rho_lt_one := hrho_lt_one
  floor := floor
  small_forward_lower := small_forward_lower
  small_forward_lower_pos := small_forward_lower_pos
  weighted_forward_lower_to_floor := weighted_forward_lower_to_floor
  lower := forwardGain * q ^ k * (rho ^ (k - 1))⁻¹
  upper := backwardLoss * ((k : ℝ) * (rho ^ (k - 1))⁻¹)
  lower_pos := by
    exact mul_pos (mul_pos forwardGain_pos (pow_pos hq_pos k))
      (inv_pos.mpr (pow_pos hrho_pos (k - 1)))
  upper_pos := by
    exact mul_pos backwardLoss_pos
      (mul_pos (by exact_mod_cast hk_pos)
        (inv_pos.mpr (pow_pos hrho_pos (k - 1))))
  degree := k
  gap := gap
  gap_error_tends_to_zero := gap_error_tends_to_zero
  gap_dominance_eventually := gap_dominance_eventually
  weighted_backward_upper := by
    intro src qsrc hfloor_lt
    have hk_le_qsrc : k ≤ qsrc := by omega
    have htail :=
      finiteDiscreteTopMassFailureTail_le_polynomial_geometric_at_a
        hk_pos hk_le_qsrc hq_pos.le hq_le_one hrho_pos hrho_lt_one.le
    have hback :=
      weighted_backward_upper_by_failure_tail src qsrc hfloor_lt
    have hbackwardLoss_nonneg : 0 ≤ backwardLoss := le_of_lt backwardLoss_pos
    calc
      likelihood src *
          (O.expectedTopSum k src qsrc -
            O.expectedTopSum k src (qsrc - 1))
          ≤ backwardLoss * finiteDiscreteTopMassFailureTail k qsrc q rho :=
            hback
      _ ≤ backwardLoss *
            (((k : ℝ) * (rho ^ (k - 1))⁻¹) *
              (qsrc : ℝ) ^ k * rho ^ qsrc) := by
            exact mul_le_mul_of_nonneg_left htail hbackwardLoss_nonneg
      _ = backwardLoss * ((k : ℝ) * (rho ^ (k - 1))⁻¹) *
            (qsrc : ℝ) ^ k * rho ^ qsrc := by
            ring
  weighted_forward_lower := by
    intro dst qdst hfloor_lt
    have hk_le_qdst : k ≤ qdst := by omega
    have htail :=
      finiteDiscreteTopMassPromotingEvent_lower_geometric_at_a
        hk_pos hk_le_qdst hq_pos.le hrho_pos
    have hforward :=
      weighted_forward_lower_by_promoting_event dst qdst hfloor_lt
    have hforwardGain_nonneg : 0 ≤ forwardGain := le_of_lt forwardGain_pos
    calc
      forwardGain * q ^ k * (rho ^ (k - 1))⁻¹ * rho ^ qdst
          = forwardGain *
              (q ^ k * (rho ^ (k - 1))⁻¹ * rho ^ qdst) := by
            ring
      _ ≤ forwardGain *
              finiteDiscreteTopMassPromotingEvent k qdst q rho := by
            exact mul_le_mul_of_nonneg_left htail hforwardGain_nonneg
      _ ≤ likelihood dst *
            (O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst) := hforward

noncomputable def of_unweighted_binomial_event_bounds {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (q rho : ℝ)
    (hk_pos : 0 < k)
    (hq_pos : 0 < q) (hq_le_one : q ≤ 1)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (floor : ℕ) (hk_le_floor_succ : k ≤ floor + 1)
    (likelihoodLower likelihoodUpper : ℝ)
    (likelihoodLower_pos : 0 < likelihoodLower)
    (likelihoodUpper_pos : 0 < likelihoodUpper)
    (likelihoodLower_le : ∀ t, likelihoodLower ≤ likelihood t)
    (likelihood_le_upper : ∀ t, likelihood t ≤ likelihoodUpper)
    (smallForward backwardLoss forwardGain : ℝ)
    (smallForward_pos : 0 < smallForward)
    (backwardLoss_pos : 0 < backwardLoss)
    (forwardGain_pos : 0 < forwardGain)
    (gap : ℕ → ℕ)
    (gap_error_tends_to_zero :
      EconCSLib.Math.TendsToZero
        (fun N => ((gap N + 1 : ℕ) : ℝ) / (N : ℝ)))
    (gap_dominance_eventually :
      ∀ᶠ (N : ℕ) in atTop,
        ((likelihoodUpper * backwardLoss) *
            ((k : ℝ) * (rho ^ (k - 1))⁻¹)) *
            (N : ℝ) ^ k * rho ^ (gap N) <
          (likelihoodLower * forwardGain) * q ^ k *
            (rho ^ (k - 1))⁻¹)
    (unweighted_forward_lower_to_floor :
      ∀ dst qdst,
        qdst ≤ floor →
          smallForward ≤
            O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst)
    (unweighted_backward_upper_by_failure_tail :
      ∀ src qsrc,
        floor < qsrc →
          O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1) ≤
            backwardLoss * finiteDiscreteTopMassFailureTail k qsrc q rho)
    (unweighted_forward_lower_by_promoting_event :
      ∀ dst qdst,
        floor < qdst →
          forwardGain * finiteDiscreteTopMassPromotingEvent k qdst q rho ≤
            O.expectedTopSum k dst (qdst + 1) -
              O.expectedTopSum k dst qdst) :
    TopKUniformGeometricTailCertificate O likelihood k :=
  of_binomial_event_bounds
    (O := O) (likelihood := likelihood) (k := k)
    q rho hk_pos hq_pos hq_le_one hrho_pos hrho_lt_one
    floor hk_le_floor_succ
    (likelihoodLower * smallForward)
    (mul_pos likelihoodLower_pos smallForward_pos)
    (by
      intro dst qdst hfloor
      have hcore := unweighted_forward_lower_to_floor dst qdst hfloor
      have hmarg_nonneg :
          0 ≤ O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst :=
        le_trans smallForward_pos.le hcore
      calc
        likelihoodLower * smallForward
            ≤ likelihoodLower *
                (O.expectedTopSum k dst (qdst + 1) -
                  O.expectedTopSum k dst qdst) :=
              mul_le_mul_of_nonneg_left hcore likelihoodLower_pos.le
        _ ≤ likelihood dst *
                (O.expectedTopSum k dst (qdst + 1) -
                  O.expectedTopSum k dst qdst) :=
              mul_le_mul_of_nonneg_right (likelihoodLower_le dst)
                hmarg_nonneg)
    (likelihoodUpper * backwardLoss)
    (likelihoodLower * forwardGain)
    (mul_pos likelihoodUpper_pos backwardLoss_pos)
    (mul_pos likelihoodLower_pos forwardGain_pos)
    gap gap_error_tends_to_zero gap_dominance_eventually
    (by
      intro src qsrc hfloor_lt
      have hraw :=
        unweighted_backward_upper_by_failure_tail src qsrc hfloor_lt
      have htail_nonneg :
          0 ≤ finiteDiscreteTopMassFailureTail k qsrc q rho :=
        finiteDiscreteTopMassFailureTail_nonneg k qsrc hq_pos.le hrho_pos.le
      have hright_nonneg :
          0 ≤ backwardLoss *
            finiteDiscreteTopMassFailureTail k qsrc q rho :=
        mul_nonneg backwardLoss_pos.le htail_nonneg
      have hlike_nonneg : 0 ≤ likelihood src :=
        le_trans likelihoodLower_pos.le (likelihoodLower_le src)
      calc
        likelihood src *
            (O.expectedTopSum k src qsrc -
              O.expectedTopSum k src (qsrc - 1))
            ≤ likelihood src *
                (backwardLoss *
                  finiteDiscreteTopMassFailureTail k qsrc q rho) :=
              mul_le_mul_of_nonneg_left hraw hlike_nonneg
        _ ≤ likelihoodUpper *
                (backwardLoss *
                  finiteDiscreteTopMassFailureTail k qsrc q rho) :=
              mul_le_mul_of_nonneg_right (likelihood_le_upper src)
                hright_nonneg
        _ = likelihoodUpper * backwardLoss *
              finiteDiscreteTopMassFailureTail k qsrc q rho := by
              ring)
    (by
      intro dst qdst hfloor_lt
      have hraw :=
        unweighted_forward_lower_by_promoting_event dst qdst hfloor_lt
      have hevent_nonneg :
          0 ≤ finiteDiscreteTopMassPromotingEvent k qdst q rho :=
        finiteDiscreteTopMassPromotingEvent_nonneg k qdst hq_pos.le hrho_pos.le
      have hleft_nonneg :
          0 ≤ forwardGain *
            finiteDiscreteTopMassPromotingEvent k qdst q rho :=
        mul_nonneg forwardGain_pos.le hevent_nonneg
      have hmarg_nonneg :
          0 ≤ O.expectedTopSum k dst (qdst + 1) -
            O.expectedTopSum k dst qdst :=
        le_trans hleft_nonneg hraw
      calc
        likelihoodLower * forwardGain *
            finiteDiscreteTopMassPromotingEvent k qdst q rho
            = likelihoodLower *
                (forwardGain *
                  finiteDiscreteTopMassPromotingEvent k qdst q rho) := by
              ring
        _ ≤ likelihoodLower *
                (O.expectedTopSum k dst (qdst + 1) -
                  O.expectedTopSum k dst qdst) :=
              mul_le_mul_of_nonneg_left hraw likelihoodLower_pos.le
        _ ≤ likelihood dst *
                (O.expectedTopSum k dst (qdst + 1) -
                  O.expectedTopSum k dst qdst) :=
              mul_le_mul_of_nonneg_right (likelihoodLower_le dst)
                hmarg_nonneg)

theorem polynomial_geometric_tail_tendsToZero {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformGeometricTailCertificate O likelihood k) :
    Tendsto
      (fun q : ℕ =>
        hcert.upper * (q : ℝ) ^ hcert.degree * hcert.rho ^ q)
      atTop (nhds 0) := by
  have hbase :
      Tendsto
        (fun q : ℕ => (q : ℝ) ^ hcert.degree * hcert.rho ^ q)
        atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one hcert.degree
      hcert.rho_pos.le hcert.rho_lt_one
  simpa [mul_assoc] using hbase.const_mul hcert.upper

noncomputable def toGeometricMarginalBoundCertificate {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformGeometricTailCertificate O likelihood k) :
    TopKUniformGeometricMarginalBoundCertificate O likelihood k := by
  classical
  have heventually_small :
      ∀ᶠ (q : ℕ) in atTop,
        hcert.upper * (q : ℝ) ^ hcert.degree * hcert.rho ^ q <
          hcert.small_forward_lower := by
    exact hcert.polynomial_geometric_tail_tendsToZero.eventually
      (Iio_mem_nhds hcert.small_forward_lower_pos)
  let threshold : ℕ := Classical.choose (eventually_atTop.1 heventually_small)
  have hthreshold :
      ∀ q ≥ threshold,
        hcert.upper * (q : ℝ) ^ hcert.degree * hcert.rho ^ q <
          hcert.small_forward_lower :=
    Classical.choose_spec (eventually_atTop.1 heventually_small)
  refine
    { rho := hcert.rho
      rho_pos := hcert.rho_pos
      rho_lt_one := hcert.rho_lt_one
      floor := hcert.floor
      source_threshold := max hcert.floor threshold
      floor_le_source_threshold := Nat.le_max_left hcert.floor threshold
      floor_backward_lt_forward := ?_
      lower := hcert.lower
      upper := hcert.upper
      lower_pos := hcert.lower_pos
      upper_pos := hcert.upper_pos
      degree := hcert.degree
      gap := hcert.gap
      gap_error_tends_to_zero := hcert.gap_error_tends_to_zero
      gap_dominance_eventually := hcert.gap_dominance_eventually
      weighted_backward_upper := hcert.weighted_backward_upper
      weighted_forward_lower := hcert.weighted_forward_lower }
  intro src dst qsrc qdst hsrc_large hdst_floor
  have hfloor_lt_qsrc : hcert.floor < qsrc :=
    lt_of_le_of_lt (Nat.le_max_left hcert.floor threshold) hsrc_large
  have hthreshold_le_qsrc : threshold ≤ qsrc :=
    le_trans (Nat.le_max_right hcert.floor threshold) hsrc_large.le
  have htail_small :=
    hthreshold qsrc hthreshold_le_qsrc
  have hback_le :=
    hcert.weighted_backward_upper src qsrc hfloor_lt_qsrc
  have hforward_ge :=
    hcert.weighted_forward_lower_to_floor dst qdst hdst_floor
  exact lt_of_le_of_lt hback_le (lt_of_lt_of_le htail_small hforward_ge)

theorem asymptoticHomogeneity {T : ℕ} [NeZero T]
    {O : TopKValueOracle T} {likelihood : ItemType T → ℝ} {k : ℕ}
    (hcert : TopKUniformGeometricTailCertificate O likelihood k) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => O.toConsumptionModel likelihood k) (uniformProfile T) :=
  hcert.toGeometricMarginalBoundCertificate.asymptoticHomogeneity

end TopKUniformGeometricTailCertificate

end PRPKG24AccuracyDiversity
