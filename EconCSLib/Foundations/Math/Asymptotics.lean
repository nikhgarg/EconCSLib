import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators

open Filter Topology
open scoped BigOperators

namespace EconCSLib
namespace Math

/-- A sequence tends to zero. -/
def TendsToZero (ε : ℕ → ℝ) : Prop :=
  Tendsto ε atTop (nhds 0)

/-- `x n` is asymptotically equivalent to `y n`, expressed as `x n / y n -> 1`. -/
def AsymptoticEquivalent (x y : ℕ → ℝ) : Prop :=
  Tendsto (fun n => x n / y n) atTop (nhds 1)

/-- A sequence is bounded by C / N. -/
def TendsToZeroInv (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, 0 < N → |ε N| ≤ C / (N : ℝ)

/-- A sequence is bounded by C / sqrt(N). -/
def TendsToZeroInvSqrt (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, 0 < N → |ε N| ≤ C / Real.sqrt (N : ℝ)

/-- A sequence has exact paper-style `C / N` error rate. -/
def ExactInvRate (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, ε N = C / (N : ℝ)

/-- A sequence has exact paper-style `C / sqrt N` error rate. -/
def ExactInvSqrtRate (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, ε N = C / Real.sqrt (N : ℝ)

/--
Changing finitely many entries of a zero-convergent error schedule preserves
zero convergence.
-/
theorem tendsToZero_if_lt_const
    {ε : ℕ → ℝ} (hε : TendsToZero ε) (threshold : ℕ) (C : ℝ) :
    TendsToZero (fun N => if N < threshold then C else ε N) := by
  rw [TendsToZero] at hε ⊢
  refine Tendsto.congr' ?_ hε
  filter_upwards [eventually_atTop.2
      ⟨threshold, fun N hN => hN⟩] with N hN
  simp [not_lt.mpr hN]

/--
Turn a family of eventual thresholds for tolerances `1 / (m + 1)` into a
single nonnegative error schedule.

At problem size `N`, the schedule uses the reciprocal of the largest tolerance
index whose threshold is at most `N`.  This is useful when an asymptotic proof
provides, for every fixed tolerance, a tail threshold, while an optimization
argument needs one concrete `o(1)` error sequence.
-/
noncomputable def reciprocalThresholdError (threshold : ℕ → ℕ) (N : ℕ) : ℝ :=
  1 / (((Nat.findGreatest (fun m => threshold m ≤ N) N + 1 : ℕ) : ℝ))

theorem reciprocalThresholdError_nonneg (threshold : ℕ → ℕ) (N : ℕ) :
    0 ≤ reciprocalThresholdError threshold N := by
  unfold reciprocalThresholdError
  positivity

theorem reciprocalThresholdError_tendsToZero (threshold : ℕ → ℕ) :
    TendsToZero (reciprocalThresholdError threshold) := by
  rw [TendsToZero]
  refine tendsto_order.2 ?_
  constructor
  · intro a ha
    filter_upwards with N
    have hnonneg := reciprocalThresholdError_nonneg threshold N
    linarith
  · intro b hb
    rcases exists_nat_one_div_lt hb with ⟨m, hm⟩
    let K : ℕ := max m (threshold m)
    refine eventually_atTop.2 ⟨K, ?_⟩
    intro N hN
    have hm_le_N : m ≤ N := le_trans (Nat.le_max_left m (threshold m)) hN
    have hthreshold_le_N : threshold m ≤ N :=
      le_trans (Nat.le_max_right m (threshold m)) hN
    have hfind_ge :
        m ≤ Nat.findGreatest (fun r => threshold r ≤ N) N :=
      Nat.le_findGreatest hm_le_N hthreshold_le_N
    have hden_le :
        (m + 1 : ℝ) ≤
          ((Nat.findGreatest (fun r => threshold r ≤ N) N + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hfind_ge
    have hden_pos : 0 < (m + 1 : ℝ) := by positivity
    have hden_find_pos :
        0 <
          ((Nat.findGreatest (fun r => threshold r ≤ N) N + 1 : ℕ) : ℝ) := by
      positivity
    have hle :
        reciprocalThresholdError threshold N ≤ 1 / (m + 1 : ℝ) := by
      unfold reciprocalThresholdError
      exact one_div_le_one_div_of_le hden_pos hden_le
    exact lt_of_le_of_lt hle hm

theorem reciprocalThresholdError_le_of_threshold_le
    (threshold : ℕ → ℕ) {m N : ℕ}
    (hm_le_N : m ≤ N) (hthreshold_le_N : threshold m ≤ N) :
    reciprocalThresholdError threshold N ≤ 1 / (m + 1 : ℝ) := by
  have hfind_ge :
      m ≤ Nat.findGreatest (fun r => threshold r ≤ N) N :=
    Nat.le_findGreatest hm_le_N hthreshold_le_N
  have hden_le :
      (m + 1 : ℝ) ≤
        ((Nat.findGreatest (fun r => threshold r ≤ N) N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hfind_ge
  have hden_find_pos :
      0 <
        ((Nat.findGreatest (fun r => threshold r ≤ N) N + 1 : ℕ) : ℝ) := by
    positivity
  have hden_pos : 0 < (m + 1 : ℝ) := by positivity
  unfold reciprocalThresholdError
  exact one_div_le_one_div_of_le hden_pos hden_le

/--
Prefix-scaled envelope of a pointwise error sequence.

At problem size `N`, this records the largest product `ε q * q` among
`q ≤ N`, normalized by `N`.  Thus `prefixScaledError ε N * N` dominates every
prefix product.  If `ε q -> 0` and `ε` is nonnegative, then this normalized
prefix envelope also tends to zero.
-/
noncomputable def prefixScaledError (ε : ℕ → ℝ) (N : ℕ) : ℝ :=
  if h : N = 0 then 0
  else
    ((Finset.range (N + 1)).sup'
      (by exact ⟨0, by simp⟩)
      (fun q => ε q * (q : ℝ))) / (N : ℝ)

theorem prefixScaledError_nonneg
    (ε : ℕ → ℝ) (hε_nonneg : ∀ q, 0 ≤ ε q) (N : ℕ) :
    0 ≤ prefixScaledError ε N := by
  by_cases hN : N = 0
  · simp [prefixScaledError, hN]
  · have hzero_mem : 0 ∈ Finset.range (N + 1) := by simp
    have hsup_nonneg :
        0 ≤
          (Finset.range (N + 1)).sup'
            (by exact ⟨0, by simp⟩)
            (fun q => ε q * (q : ℝ)) := by
      simpa using
        (Finset.le_sup'
          (s := Finset.range (N + 1))
          (f := fun q => ε q * (q : ℝ)) hzero_mem)
    simp [prefixScaledError, hN]
    exact div_nonneg hsup_nonneg (Nat.cast_nonneg N)

theorem le_prefixScaledError_mul_nat
    (ε : ℕ → ℝ) {q N : ℕ} (hN_pos : 0 < N) (hq_le_N : q ≤ N) :
    ε q * (q : ℝ) ≤ prefixScaledError ε N * (N : ℝ) := by
  have hq_mem : q ∈ Finset.range (N + 1) := by
    simp
    omega
  have hle :
      ε q * (q : ℝ) ≤
        (Finset.range (N + 1)).sup'
          (by exact ⟨0, by simp⟩)
          (fun q => ε q * (q : ℝ)) :=
    Finset.le_sup'
      (s := Finset.range (N + 1))
      (f := fun q => ε q * (q : ℝ)) hq_mem
  have hN_ne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN_pos)
  calc
    ε q * (q : ℝ)
        ≤ (Finset.range (N + 1)).sup'
            (by exact ⟨0, by simp⟩)
            (fun q => ε q * (q : ℝ)) := hle
    _ = prefixScaledError ε N * (N : ℝ) := by
          simp [prefixScaledError, Nat.ne_of_gt hN_pos, hN_ne]

theorem prefixScaledError_tendsToZero
    (ε : ℕ → ℝ) (hε_nonneg : ∀ q, 0 ≤ ε q)
    (hε_zero : TendsToZero ε) :
    TendsToZero (prefixScaledError ε) := by
  rw [TendsToZero] at hε_zero ⊢
  refine tendsto_order.2 ?_
  constructor
  · intro a ha
    filter_upwards with N
    have hnonneg := prefixScaledError_nonneg ε hε_nonneg N
    linarith
  · intro b hb
    have hhalf_pos : 0 < b / 2 := by linarith
    have hε_small_eventually :
        ∀ᶠ q in atTop, ε q < b / 2 := by
      exact hε_zero.eventually (eventually_lt_nhds hhalf_pos)
    rcases eventually_atTop.1 hε_small_eventually with
      ⟨K, hK⟩
    let C : ℝ :=
      max 0
        ((Finset.range (K + 1)).sup'
          (by exact ⟨0, by simp⟩)
          (fun q => ε q * (q : ℝ)))
    have hC_div_zero :
        Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat C
    have hC_small_eventually :
        ∀ᶠ N : ℕ in atTop, C / (N : ℝ) < b / 2 :=
      hC_div_zero.eventually (eventually_lt_nhds hhalf_pos)
    filter_upwards
      [hC_small_eventually,
        eventually_atTop.2 ⟨K + 1, fun N hN => hN⟩]
      with N hC_small hN_large
    have hN_pos : 0 < N := by omega
    have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos
    have hN_real_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_real_pos
    have hsup_le :
        (Finset.range (N + 1)).sup'
            (by exact ⟨0, by simp⟩)
            (fun q => ε q * (q : ℝ)) ≤
          (b / 2) * (N : ℝ) := by
      refine Finset.sup'_le
        (s := Finset.range (N + 1))
        (H := by exact ⟨0, by simp⟩)
        (f := fun q => ε q * (q : ℝ)) ?_
      intro q hq_mem
      have hq_le_N : q ≤ N := by
        simp at hq_mem
        omega
      by_cases hK_le_q : K ≤ q
      · have hε_q_le : ε q ≤ b / 2 := le_of_lt (hK q hK_le_q)
        calc
          ε q * (q : ℝ)
              ≤ (b / 2) * (q : ℝ) :=
                mul_le_mul_of_nonneg_right hε_q_le (Nat.cast_nonneg q)
          _ ≤ (b / 2) * (N : ℝ) := by
                exact mul_le_mul_of_nonneg_left
                  (by exact_mod_cast hq_le_N) hhalf_pos.le
      · have hq_lt_K : q < K := Nat.lt_of_not_ge hK_le_q
        have hq_prefix_mem : q ∈ Finset.range (K + 1) := by
          simp
          omega
        have hterm_le_C :
            ε q * (q : ℝ) ≤ C := by
          have hterm_le_sup :
              ε q * (q : ℝ) ≤
                (Finset.range (K + 1)).sup'
                  (by exact ⟨0, by simp⟩)
                  (fun q => ε q * (q : ℝ)) :=
            Finset.le_sup'
              (s := Finset.range (K + 1))
              (f := fun q => ε q * (q : ℝ)) hq_prefix_mem
          exact le_trans hterm_le_sup (le_max_right _ _)
        have hC_lt :
            C < (b / 2) * (N : ℝ) := by
          calc
            C = (C / (N : ℝ)) * (N : ℝ) := by
                  field_simp [hN_real_ne]
            _ < (b / 2) * (N : ℝ) :=
                  mul_lt_mul_of_pos_right hC_small hN_real_pos
        exact le_trans hterm_le_C (le_of_lt hC_lt)
    have hpref_le_half : prefixScaledError ε N ≤ b / 2 := by
      simp [prefixScaledError, Nat.ne_of_gt hN_pos]
      calc
        ((Finset.range (N + 1)).sup'
            (by exact ⟨0, by simp⟩)
            (fun q => ε q * (q : ℝ))) / (N : ℝ)
            ≤ ((b / 2) * (N : ℝ)) / (N : ℝ) :=
              div_le_div_of_nonneg_right hsup_le hN_real_pos.le
        _ = b / 2 := by
              field_simp [hN_real_ne]
    linarith

namespace AsymptoticEquivalent

theorem congr_left_eventually
    {x x' y : ℕ → ℝ}
    (hxx' : ∀ᶠ n in atTop, x n = x' n)
    (h : AsymptoticEquivalent x' y) :
    AsymptoticEquivalent x y := by
  rw [AsymptoticEquivalent] at h ⊢
  refine Tendsto.congr' ?_ h
  filter_upwards [hxx'] with n hn
  rw [hn]

theorem congr_right_eventually
    {x y y' : ℕ → ℝ}
    (hyy' : ∀ᶠ n in atTop, y n = y' n)
    (h : AsymptoticEquivalent x y) :
    AsymptoticEquivalent x y' := by
  rw [AsymptoticEquivalent] at h ⊢
  refine Tendsto.congr' ?_ h
  filter_upwards [hyy'] with n hn
  rw [hn]

theorem eventually_ratio_mem_Icc
    {x y : ℕ → ℝ} (h : AsymptoticEquivalent x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      1 - ε ≤ x n / y n ∧ x n / y n ≤ 1 + ε := by
  have hlow : ∀ᶠ n in atTop, 1 - ε ≤ x n / y n := by
    exact h.eventually_const_le (by linarith)
  have hhigh : ∀ᶠ n in atTop, x n / y n ≤ 1 + ε := by
    exact h.eventually_le_const (by linarith)
  filter_upwards [hlow, hhigh] with n hnlow hnhigh
  exact ⟨hnlow, hnhigh⟩

theorem eventually_sandwich_of_pos_right
    {x y : ℕ → ℝ} (h : AsymptoticEquivalent x y)
    (hy_pos : ∀ᶠ n in atTop, 0 < y n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (1 - ε) * y n ≤ x n ∧ x n ≤ (1 + ε) * y n := by
  filter_upwards [h.eventually_ratio_mem_Icc hε, hy_pos] with n hratio hy
  have heq : x n = (x n / y n) * y n := by
    field_simp [ne_of_gt hy]
  constructor
  · calc
      (1 - ε) * y n ≤ (x n / y n) * y n :=
        mul_le_mul_of_nonneg_right hratio.1 hy.le
      _ = x n := by rw [← heq]
  · calc
      x n = (x n / y n) * y n := heq
      _ ≤ (1 + ε) * y n :=
        mul_le_mul_of_nonneg_right hratio.2 hy.le

end AsymptoticEquivalent

/--
If finitely many terms are each asymptotic to a nonzero coefficient times a
common scale, then their finite sum is asymptotic to the sum of the
coefficients times that scale.
-/
theorem finite_sum_asymptoticEquivalent_common_scale
    {ι : Type*} [Fintype ι]
    (term : ι → ℕ → ℝ) (coeff : ι → ℝ) (scale : ℕ → ℝ)
    (hcoeff_ne : ∀ i, coeff i ≠ 0)
    (htotal_ne : (∑ i : ι, coeff i) ≠ 0)
    (hscale_ne : ∀ᶠ n in atTop, scale n ≠ 0)
    (hterm :
      ∀ i,
        AsymptoticEquivalent (term i)
          (fun n => coeff i * scale n)) :
    AsymptoticEquivalent
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
If a main term is asymptotic to `coeff * scale` and a remainder is `o(scale)`,
their sum has the same asymptotic equivalent.
-/
theorem asymptoticEquivalent_add_negligible_common_scale
    (main remainder scale : ℕ → ℝ) (coeff : ℝ)
    (hcoeff_ne : coeff ≠ 0)
    (hscale_ne : ∀ᶠ n in atTop, scale n ≠ 0)
    (hmain :
      AsymptoticEquivalent main
        (fun n => coeff * scale n))
    (hremainder :
      Tendsto (fun n => remainder n / scale n) atTop (nhds 0)) :
    AsymptoticEquivalent
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
  rw [AsymptoticEquivalent] at hmain ⊢
  have hsum := hmain.add hremainder_ratio
  refine Tendsto.congr' ?_ (by simpa using hsum)
  filter_upwards [hscale_ne] with n hn_scale
  field_simp [hcoeff_ne, hn_scale]

theorem ExactInvRate_implies_TendsToZeroInv (ε : ℕ → ℝ) :
    ExactInvRate ε → TendsToZeroInv ε := by
  intro ⟨C, hCpos, hε⟩
  refine ⟨C, hCpos, ?_⟩
  intro N hN
  rw [hε N]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnonneg : 0 ≤ C / (N : ℝ) := div_nonneg hCpos.le hNpos.le
  rw [abs_of_nonneg hnonneg]

theorem ExactInvSqrtRate_implies_TendsToZeroInvSqrt (ε : ℕ → ℝ) :
    ExactInvSqrtRate ε → TendsToZeroInvSqrt ε := by
  intro ⟨C, hCpos, hε⟩
  refine ⟨C, hCpos, ?_⟩
  intro N hN
  rw [hε N]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hnonneg : 0 ≤ C / Real.sqrt (N : ℝ) := div_nonneg hCpos.le hsqrt_pos.le
  rw [abs_of_nonneg hnonneg]

theorem TendsToZeroInv_implies_TendsToZero (ε : ℕ → ℝ) :
    TendsToZeroInv ε → TendsToZero ε := by
  intro ⟨C, hCpos, hbound⟩
  rw [TendsToZero]
  have h_zero : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat C
  have h_neg_zero : Tendsto (fun N : ℕ => -(C / (N : ℝ))) atTop (nhds 0) := by
    have h := h_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_zero h_zero
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := hbound N hN
    rw [abs_le] at h1
    exact h1.1
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := hbound N hN
    rw [abs_le] at h1
    exact h1.2

theorem ExactInvRate_implies_TendsToZero (ε : ℕ → ℝ) :
    ExactInvRate ε → TendsToZero ε := by
  intro hε
  exact TendsToZeroInv_implies_TendsToZero ε
    (ExactInvRate_implies_TendsToZeroInv ε hε)

theorem TendsToZeroInvSqrt_implies_TendsToZero (ε : ℕ → ℝ) :
    TendsToZeroInvSqrt ε → TendsToZero ε := by
  intro ⟨C, hCpos, hbound⟩
  rw [TendsToZero]
  have h_sqrt_atTop :
      Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop := by
    exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h_zero :
      Tendsto (fun N : ℕ => C / Real.sqrt (N : ℝ)) atTop (nhds 0) := by
    exact Filter.Tendsto.const_div_atTop h_sqrt_atTop C
  have h_neg_zero :
      Tendsto (fun N : ℕ => -(C / Real.sqrt (N : ℝ))) atTop (nhds 0) := by
    have h := h_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_zero h_zero
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := hbound N hN
    rw [abs_le] at h1
    exact h1.1
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := hbound N hN
    rw [abs_le] at h1
    exact h1.2

theorem ExactInvSqrtRate_implies_TendsToZero (ε : ℕ → ℝ) :
    ExactInvSqrtRate ε → TendsToZero ε := by
  intro hε
  exact TendsToZeroInvSqrt_implies_TendsToZero ε
    (ExactInvSqrtRate_implies_TendsToZeroInvSqrt ε hε)

/-- A sequence tends to zero if it is eventually dominated by `C / N`. -/
theorem TendsToZero_of_eventually_abs_le_inv (ε : ℕ → ℝ) {C : ℝ}
    (_hC : 0 < C) (hbound : ∀ᶠ N in atTop, |ε N| ≤ C / (N : ℝ)) :
    TendsToZero ε := by
  rw [TendsToZero]
  have h_zero : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have h_neg_zero : Tendsto (fun N : ℕ => -(C / (N : ℝ))) atTop (nhds 0) := by
    have h := h_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_zero h_zero
  · filter_upwards [hbound, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    exact hN.1
  · filter_upwards [hbound, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    exact hN.2

/-- A nonnegative sequence bounded by `C / N` tends to zero. -/
theorem TendsToZero_of_nonneg_le_const_div
    (ε : ℕ → ℝ) {C : ℝ}
    (hC : 0 < C)
    (hnonneg : ∀ N, 0 ≤ ε N)
    (hbound : ∀ N, 0 < N → ε N ≤ C / (N : ℝ)) :
    TendsToZero ε := by
  refine TendsToZero_of_eventually_abs_le_inv ε hC ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [abs_of_nonneg (hnonneg N)]
  exact hbound N hN

/--
A sequence tends to zero if its absolute value is eventually bounded by another
sequence tending to zero.
-/
theorem TendsToZero_of_eventually_abs_le_tendsto_zero
    (ε bound : ℕ → ℝ)
    (hbound_zero : Tendsto bound atTop (nhds 0))
    (hbound : ∀ᶠ N in atTop, |ε N| ≤ bound N) :
    TendsToZero ε := by
  rw [TendsToZero]
  have hneg_zero : Tendsto (fun N => -bound N) atTop (nhds 0) := by
    have h := hbound_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg_zero hbound_zero
  · filter_upwards [hbound] with N hN
    exact (abs_le.mp hN).1
  · filter_upwards [hbound] with N hN
    exact (abs_le.mp hN).2

/--
If a real-valued scale is eventually positive and tends to zero, then any
positive constant divided by that scale diverges to `atTop`.
-/
theorem tendsto_const_div_atTop_of_pos_tendsto_zero
    {ι : Type*} {l : Filter ι} {scale : ι → ℝ} {C : ℝ}
    (hC_pos : 0 < C)
    (hscale_zero : Tendsto scale l (nhds 0))
    (hscale_pos : ∀ᶠ i in l, 0 < scale i) :
    Tendsto (fun i => C / scale i) l atTop := by
  have hscale_nhdsGT :
      Tendsto scale l (𝓝[>] (0 : ℝ)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      scale hscale_zero hscale_pos
  have hinv : Tendsto (fun i => (scale i)⁻¹) l atTop :=
    hscale_nhdsGT.inv_tendsto_nhdsGT_zero
  simpa [div_eq_mul_inv] using
    (tendsto_const_mul_atTop_of_pos hC_pos).mpr hinv

/-- `log N` tends to infinity along natural numbers. -/
theorem tendsto_log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- A constant divided by `log N` tends to zero. -/
theorem tendsto_const_div_log_nat_nhds_zero (C : ℝ) :
    Tendsto (fun N : ℕ => C / Real.log (N : ℝ)) atTop (nhds 0) :=
  Filter.Tendsto.const_div_atTop tendsto_log_nat_atTop C

/-- `log N / sqrt N` tends to zero. -/
theorem tendsto_log_div_sqrt_nat_nhds_zero :
    Tendsto
      (fun N : ℕ => Real.log (N : ℝ) / Real.sqrt (N : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (nhds 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ))
        (by norm_num)).tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- A sequence tends to zero if it is eventually dominated by `C / √N`. -/
theorem TendsToZero_of_eventually_abs_le_inv_sqrt (ε : ℕ → ℝ) {C : ℝ}
    (_hC : 0 < C) (hbound : ∀ᶠ N in atTop, |ε N| ≤ C / Real.sqrt (N : ℝ)) :
    TendsToZero ε := by
  rw [TendsToZero]
  have h_sqrt_atTop :
      Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h_zero : Tendsto (fun N : ℕ => C / Real.sqrt (N : ℝ)) atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop h_sqrt_atTop C
  have h_neg_zero : Tendsto (fun N : ℕ => -(C / Real.sqrt (N : ℝ))) atTop (nhds 0) := by
    have h := h_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_zero h_zero
  · filter_upwards [hbound, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    exact hN.1
  · filter_upwards [hbound, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    exact hN.2

/-- An exact geometric tail has logarithmic saturation ratio one. -/
theorem log_geometric_tail_ratio
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

/-- `log N / N -> 0`. -/
theorem tendsto_log_nat_div_nat_nhds_zero :
    Tendsto
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using
      (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

/--
Any fixed real-power polynomial factor is killed by a geometric term along
natural-number indices.
-/
theorem rpow_mul_geometric_tendsto_zero
    (s : ℝ) {rho : ℝ} (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ s * rho ^ N)
      atTop (nhds 0) := by
  have hlog_neg : Real.log rho < 0 := Real.log_neg hrho_pos hrho_lt_one
  have hreal :
      Tendsto (fun x : ℝ => x ^ s * Real.exp (Real.log rho * x))
        atTop (nhds 0) := by
    simpa [neg_mul, neg_neg, mul_comm, mul_left_comm, mul_assoc] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        s (-Real.log rho) (neg_pos.mpr hlog_neg)
  refine Tendsto.congr' ?_ (hreal.comp tendsto_natCast_atTop_atTop)
  filter_upwards with N
  have hexp :
      Real.exp (Real.log rho * (N : ℝ)) = rho ^ N := by
    calc
      Real.exp (Real.log rho * (N : ℝ))
          = Real.exp ((N : ℝ) * Real.log rho) := by rw [mul_comm]
      _ = (Real.exp (Real.log rho)) ^ N := Real.exp_nat_mul (Real.log rho) N
      _ = rho ^ N := by rw [Real.exp_log hrho_pos]
  change (N : ℝ) ^ s * Real.exp (Real.log rho * (N : ℝ)) =
    (N : ℝ) ^ s * rho ^ N
  rw [hexp]

/-- Natural square root tends to infinity along natural numbers. -/
theorem tendsto_nat_sqrt_atTop :
    Tendsto (fun N : ℕ => Nat.sqrt N) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  refine eventually_atTop.2 ⟨M * M, ?_⟩
  intro N hN
  exact (Nat.le_sqrt).2 hN

/-- The real cast of `N + 1` tends to infinity along natural numbers. -/
theorem tendsto_nat_succ_cast_atTop :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

/-- Adding a real constant to `(N + 1 : ℝ)` still tends to infinity. -/
theorem tendsto_nat_succ_cast_add_const_atTop (d : ℝ) :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) + d)) atTop atTop :=
  tendsto_atTop_add_const_right atTop d tendsto_nat_succ_cast_atTop

/-- A positive real power of `(N + 1 : ℝ)` tends to infinity. -/
theorem tendsto_nat_succ_cast_rpow_atTop {β : ℝ} (hβ_pos : 0 < β) :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) ^ β)) atTop atTop :=
  (tendsto_rpow_atTop hβ_pos).comp tendsto_nat_succ_cast_atTop

/-- A negative real power of `(N + 1 : ℝ)` tends to zero. -/
theorem tendsto_nat_succ_cast_rpow_neg_nhds_zero {β : ℝ}
    (hβ_pos : 0 < β) :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) ^ (-β)))
      atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop hβ_pos).comp tendsto_nat_succ_cast_atTop

/-- A negative real power of `(N + 1 : ℝ) + d` tends to zero. -/
theorem tendsto_nat_succ_cast_add_const_rpow_neg_nhds_zero
    (d : ℝ) {β : ℝ} (hβ_pos : 0 < β) :
    Tendsto (fun N : ℕ => ((((N + 1 : ℕ) : ℝ) + d) ^ (-β)))
      atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop hβ_pos).comp
    (tendsto_nat_succ_cast_add_const_atTop d)

/-- The square root of `(N + 1 : ℝ)` tends to infinity. -/
theorem tendsto_sqrt_nat_succ_cast_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (((N + 1 : ℕ) : ℝ))) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_nat_succ_cast_atTop

/-- Canonical inverse-square-root error schedule `1 / sqrt (N+1)`. -/
noncomputable def invSqrtSuccError (N : ℕ) : ℝ :=
  1 / Real.sqrt (((N + 1 : ℕ) : ℝ))

theorem invSqrtSuccError_nonneg (N : ℕ) :
    0 ≤ invSqrtSuccError N := by
  unfold invSqrtSuccError
  positivity

theorem invSqrtSuccError_tendsToZero :
    TendsToZero invSqrtSuccError := by
  rw [TendsToZero]
  refine Tendsto.congr' ?_
    (Filter.Tendsto.const_div_atTop tendsto_sqrt_nat_succ_cast_atTop (1 : ℝ))
  filter_upwards with N
  simp [invSqrtSuccError, one_div, Nat.cast_add]

/-- `N / sqrt (N+1)`, equivalently `invSqrtSuccError N * N`, tends to infinity. -/
theorem invSqrtSuccError_mul_nat_tendsto_atTop :
    Tendsto (fun N : ℕ => invSqrtSuccError N * (N : ℝ)) atTop atTop := by
  have hhalf_sqrt :
      Tendsto
        (fun N : ℕ => (1 / 2 : ℝ) * Real.sqrt (((N + 1 : ℕ) : ℝ)))
        atTop atTop :=
    Filter.Tendsto.const_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 2) tendsto_sqrt_nat_succ_cast_atTop
  refine tendsto_atTop_mono' atTop ?_ hhalf_sqrt
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN_real : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase_pos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt_pos : 0 < Real.sqrt (((N + 1 : ℕ) : ℝ)) :=
    Real.sqrt_pos.mpr hbase_pos
  have hbase_div_le_N :
      (((N + 1 : ℕ) : ℝ)) / 2 ≤ (N : ℝ) := by
    have hbase_eq : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by norm_num
    nlinarith
  unfold invSqrtSuccError
  calc
    (1 / 2 : ℝ) * Real.sqrt (((N + 1 : ℕ) : ℝ))
        =
          (((N + 1 : ℕ) : ℝ)) /
            (2 * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
          field_simp [hsqrt_pos.ne']
          rw [Real.sq_sqrt hbase_pos.le]
    _ ≤ (N : ℝ) / Real.sqrt (((N + 1 : ℕ) : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (((N + 1 : ℕ) : ℝ)))
            hsqrt_pos]
          nlinarith
    _ = (1 / Real.sqrt (((N + 1 : ℕ) : ℝ))) * (N : ℝ) := by ring

/--
The growing scale `N / sqrt(N+1)` eventually dominates every fixed finite
family of real bounds.
-/
theorem invSqrtSuccError_mul_nat_eventually_gt_fintype_pair
    {ι κ : Type*} [Fintype ι] [Fintype κ] (B : ι → κ → ℝ) :
    ∀ᶠ N in atTop,
      ∀ i : ι, ∀ j : κ,
        B i j < invSqrtSuccError N * (N : ℝ) := by
  classical
  refine eventually_all.2 ?_
  intro i
  refine eventually_all.2 ?_
  intro j
  exact invSqrtSuccError_mul_nat_tendsto_atTop.eventually_gt_atTop (B i j)

/--
If a scaled-count gap beats the source and destination additive shifts, then
the corresponding shifted destination count is below the shifted source count.

This is the arithmetic core used by finite FOC arguments that compare
backward and forward marginals with one-count or constant shifts.
-/
theorem scaled_gap_absorbs_additive_shifts
    {qsrc qdst wsrc wdst srcShift dstShift : ℝ}
    (hshift_lt_gap :
      srcShift / wsrc + dstShift / wdst <
        qsrc / wsrc - qdst / wdst) :
    (qdst + dstShift) / wdst < (qsrc - srcShift) / wsrc := by
  have hdst :
      (qdst + dstShift) / wdst =
        qdst / wdst + dstShift / wdst := by ring
  have hsrc :
      (qsrc - srcShift) / wsrc =
        qsrc / wsrc - srcShift / wsrc := by ring
  rw [hdst, hsrc]
  linarith

/-- The integer square-root gap `(sqrt N + 1) / N` tends to zero. -/
theorem nat_sqrt_gap_error_tendsToZero :
    TendsToZero
      (fun N : ℕ => ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ)) := by
  refine TendsToZero_of_eventually_abs_le_inv_sqrt
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
For any `0 < rho < 1`, a square-root gap kills every fixed polynomial factor:
`N^k * rho^(sqrt N) -> 0`.
-/
theorem nat_sqrt_gap_polynomial_geometric_tends_to_zero
    (k : ℕ) {rho : ℝ} (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1) :
    Tendsto
      (fun N : ℕ => (N : ℝ) ^ k * rho ^ (Nat.sqrt N))
      atTop (nhds 0) := by
  have hsucc_base :
      Tendsto
        (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ (2 * k)) * rho ^ (m + 1))
        atTop (nhds 0) :=
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
    have hN_le_nat : N ≤ (m + 1) ^ 2 :=
      le_of_lt (by simpa [m] using Nat.lt_succ_sqrt' N)
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
      _ ≤ (((m + 1 : ℕ) : ℝ) ^ (2 * k)) * rho ^ m :=
            mul_le_mul_of_nonneg_right
              hpow_le' htail_nonneg
      _ = (((Nat.sqrt N + 1 : ℕ) : ℝ) ^ (2 * k)) *
            rho ^ (Nat.sqrt N) := by rfl

/--
Multiplying a geometric tail by any fixed polynomial factor does not change the
logarithmic saturation ratio.
-/
theorem log_polynomial_geometric_tail_ratio
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
Lower geometric and upper polynomial-times-geometric bounds squeeze the
logarithmic saturation ratio to one.
-/
theorem log_tail_ratio_of_geometric_bounds
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
    log_polynomial_geometric_tail_ratio
      d hupper_pos hr_pos hr_lt_one
  have hup_lim :=
    log_geometric_tail_ratio
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
If a nonnegative sequence is bounded by a constant, then dividing it by `N`
tends to zero.
-/
theorem TendsToZero_ratio_of_nonneg_bounded (x : ℕ → ℝ) {C : ℝ}
    (hC : 0 < C) (hx_nonneg : ∀ N, 0 ≤ x N) (hx_bound : ∀ N, x N ≤ C) :
    TendsToZero fun N => x N / (N : ℝ) := by
  refine TendsToZero_of_eventually_abs_le_inv (fun N => x N / (N : ℝ)) hC ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNreal_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdiv_nonneg : 0 ≤ x N / (N : ℝ) :=
    div_nonneg (hx_nonneg N) hNreal_pos.le
  rw [abs_of_nonneg hdiv_nonneg]
  exact div_le_div_of_nonneg_right (hx_bound N) hNreal_pos.le

/--
Order is closed under limits of real sequences: if `x N <= y N` for every
index and the two sequences converge, then the limiting values satisfy the same
inequality.
-/
theorem le_of_tendsto_atTop_of_forall_le
    {x y : ℕ → ℝ} {X Y : ℝ}
    (hx : Tendsto x atTop (nhds X))
    (hy : Tendsto y atTop (nhds Y))
    (hle : ∀ N, x N ≤ y N) :
    X ≤ Y :=
  le_of_tendsto_of_tendsto' hx hy hle

end Math
end EconCSLib
