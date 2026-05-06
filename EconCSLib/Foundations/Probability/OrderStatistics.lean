import EconCSLib.Foundations.Math.Asymptotics
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

open Filter Topology

namespace EconCSLib
namespace Probability

noncomputable section

/-!
# Order-Statistic Certificate Interfaces

Reusable scaffolding for papers whose probability layer supplies expected
top-`k` values or marginal order-statistic asymptotics.  This file does not
prove distribution-specific bounded/exponential/Pareto integral asymptotics;
it gives those analytic results a stable target interface.

## Main declarations

- `TopKExpectationOracle`
- `TopKExpectationOracle.marginalTopK`
- `TopKExpectationOracle.ScaledMarginalLimitCertificate`
- `TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_marginal_sandwich`
- `TopKExpectationOracle.ScaledMarginalLimitCertificate.marginal_lt_of_scaled_gap`
- `TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_same_count_marginal_lt_of_weight_gap`
-/

/--
Oracle for the expected value of the best `k` consumed items among `q` sampled
items of a type/category.
-/
structure TopKExpectationOracle (τ : Type*) where
  expectedTopSum : ℕ → τ → ℕ → ℝ

namespace TopKExpectationOracle

variable {τ : Type*}

/-- Marginal expected top-`k` value from adding one more sampled item. -/
def marginalTopK (O : TopKExpectationOracle τ)
    (k : ℕ) (t : τ) (q : ℕ) : ℝ :=
  O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q

/-- Diminishing marginal expected top-`k` values. -/
def HasDiminishingReturnsAt (O : TopKExpectationOracle τ) (k : ℕ) : Prop :=
  ∀ t q, O.marginalTopK k t (q + 1) ≤ O.marginalTopK k t q

/-- Nonnegative marginal expected top-`k` values. -/
def HasNonnegativeMarginalsAt (O : TopKExpectationOracle τ) (k : ℕ) : Prop :=
  ∀ t q, 0 ≤ O.marginalTopK k t q

@[simp] theorem marginalTopK_apply (O : TopKExpectationOracle τ)
    (k : ℕ) (t : τ) (q : ℕ) :
    O.marginalTopK k t q =
      O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q := rfl

/--
Certificate that all finite type-specific top-`k` marginals share a common
asymptotic scale, up to a positive type weight:

`marginal(k,t,q) / (scale q * weight t) -> 1`.

This is the probability-facing object that bounded, exponential, Pareto, or
finite-discrete order-statistic calculations should produce before the
optimization layer consumes marginal comparisons.
-/
structure ScaledMarginalLimitCertificate [Fintype τ]
    (O : TopKExpectationOracle τ) (k : ℕ)
    (scale : ℕ → ℝ) (weight : τ → ℝ) where
  scale_pos_eventually : ∀ᶠ q in atTop, 0 < scale q
  weight_pos : ∀ t, 0 < weight t
  marginal_ratio_tendsto :
    ∀ t,
      Tendsto
        (fun q => O.marginalTopK k t q / (scale q * weight t))
        atTop (nhds 1)

namespace ScaledMarginalLimitCertificate

variable [Fintype τ]
variable {O : TopKExpectationOracle τ} {k : ℕ}
variable {scale : ℕ → ℝ} {weight : τ → ℝ}

theorem eventually_uniform_ratio_abs_sub_lt
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop,
      ∀ t : τ,
        |O.marginalTopK k t q / (scale q * weight t) - 1| < ε := by
  classical
  refine eventually_all.2 ?_
  intro t
  have ht :=
    (C.marginal_ratio_tendsto t).eventually
      (Metric.ball_mem_nhds 1 hε)
  filter_upwards [ht] with q hq
  simpa [Metric.mem_ball, Real.dist_eq] using hq

theorem eventually_uniform_ratio_mem_Icc
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop,
      ∀ t : τ,
        (1 - ε ≤ O.marginalTopK k t q / (scale q * weight t)) ∧
          (O.marginalTopK k t q / (scale q * weight t) ≤ 1 + ε) := by
  filter_upwards [C.eventually_uniform_ratio_abs_sub_lt hε] with q hq t
  have habs := hq t
  rw [abs_lt] at habs
  constructor <;> linarith

theorem eventually_uniform_ratio_pos
    (C : ScaledMarginalLimitCertificate O k scale weight) :
    ∀ᶠ q in atTop,
      ∀ t : τ,
        0 < O.marginalTopK k t q / (scale q * weight t) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  filter_upwards [C.eventually_uniform_ratio_mem_Icc hhalf] with q hq t
  linarith [(hq t).1]

theorem marginalTopK_eq_ratio_mul
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {q : ℕ} {t : τ} (hscale : scale q ≠ 0) :
    O.marginalTopK k t q =
      (O.marginalTopK k t q / (scale q * weight t)) *
        (scale q * weight t) := by
  have hweight : weight t ≠ 0 := ne_of_gt (C.weight_pos t)
  field_simp [hscale, hweight]

/--
Uniform finite-type asymptotic ratio control gives an eventual multiplicative
sandwich for every type's marginal top-`k` value.
-/
theorem eventually_marginal_sandwich
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop,
      ∀ t : τ,
        (1 - ε) * (scale q * weight t) ≤ O.marginalTopK k t q ∧
          O.marginalTopK k t q ≤
            (1 + ε) * (scale q * weight t) := by
  filter_upwards
    [C.eventually_uniform_ratio_mem_Icc hε, C.scale_pos_eventually]
    with q hratio hscale t
  have hden_pos : 0 < scale q * weight t :=
    mul_pos hscale (C.weight_pos t)
  have hden_nonneg : 0 ≤ scale q * weight t := hden_pos.le
  have heq :=
    C.marginalTopK_eq_ratio_mul
      (q := q) (t := t) (ne_of_gt hscale)
  constructor
  · calc
      (1 - ε) * (scale q * weight t)
          ≤ (O.marginalTopK k t q / (scale q * weight t)) *
              (scale q * weight t) :=
            mul_le_mul_of_nonneg_right (hratio t).1 hden_nonneg
      _ = O.marginalTopK k t q := by rw [← heq]
  · calc
      O.marginalTopK k t q
          = (O.marginalTopK k t q / (scale q * weight t)) *
              (scale q * weight t) := heq
      _ ≤ (1 + ε) * (scale q * weight t) :=
            mul_le_mul_of_nonneg_right (hratio t).2 hden_nonneg

/-- A one-index marginal sandwich at a fixed count. -/
def MarginalSandwichAt
    (C : ScaledMarginalLimitCertificate O k scale weight)
    (ε : ℝ) (q : ℕ) : Prop :=
  ∀ t : τ,
    (1 - ε) * (scale q * weight t) ≤ O.marginalTopK k t q ∧
      O.marginalTopK k t q ≤ (1 + ε) * (scale q * weight t)

theorem eventually_marginalSandwichAt
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop, C.MarginalSandwichAt ε q :=
  C.eventually_marginal_sandwich hε

/--
If the upper scaled approximation for one marginal lies below the lower scaled
approximation for another, then the actual marginals are strictly ordered.
-/
theorem marginal_lt_of_scaled_gap
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} {qsrc qdst : ℕ} {src dst : τ}
    (hsrc : C.MarginalSandwichAt ε qsrc)
    (hdst : C.MarginalSandwichAt ε qdst)
    (hgap :
      (1 + ε) * (scale qsrc * weight src) <
        (1 - ε) * (scale qdst * weight dst)) :
    O.marginalTopK k src qsrc < O.marginalTopK k dst qdst :=
  lt_of_le_of_lt (hsrc src).2 (hgap.trans_le (hdst dst).1)

/--
Same-count specialization: a strict gap between scaled type weights eventually
implies the same strict ordering of top-`k` marginals.
-/
theorem eventually_same_count_marginal_lt_of_weight_gap
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) {src dst : τ}
    (hgap : (1 + ε) * weight src < (1 - ε) * weight dst) :
    ∀ᶠ q in atTop,
      O.marginalTopK k src q < O.marginalTopK k dst q := by
  filter_upwards [C.eventually_marginalSandwichAt hε, C.scale_pos_eventually]
    with q hq hscale
  apply C.marginal_lt_of_scaled_gap (qsrc := q) (qdst := q)
    (src := src) (dst := dst) hq hq
  have hscaled :
      scale q * ((1 + ε) * weight src) <
        scale q * ((1 - ε) * weight dst) :=
    mul_lt_mul_of_pos_left hgap hscale
  calc
    (1 + ε) * (scale q * weight src)
        = scale q * ((1 + ε) * weight src) := by ring
    _ < scale q * ((1 - ε) * weight dst) := hscaled
    _ = (1 - ε) * (scale q * weight dst) := by ring

end ScaledMarginalLimitCertificate

end TopKExpectationOracle

end

end Probability
end EconCSLib
