import EconCSLib.Foundations.Probability.FiniteSupportMGF
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

end HasExpLowerBoundWithConst

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
