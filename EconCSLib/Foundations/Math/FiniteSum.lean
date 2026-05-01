import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace EconCSLib
namespace FiniteSum

/--
If two functions on a finite type differ only at two distinct points, the whole
sum changes by exactly the two pointwise deltas.
-/
theorem sum_eq_sum_add_sub_add_sub_of_eq_off
    {α : Type*} [Fintype α]
    {f g : α → ℝ} {a b : α} (hab : a ≠ b)
    (hoff : ∀ x, x ≠ a → x ≠ b → f x = g x) :
    (∑ x : α, f x) = (∑ x : α, g x) + (f a - g a) + (f b - g b) := by
  classical
  have hfg : ∑ x : α, f x = ∑ x : α, (g x + (f x - g x)) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    ring
  have hsumadd :
      ∑ x : α, (g x + (f x - g x)) =
        ∑ x : α, g x + ∑ x : α, (f x - g x) := by
    rw [Finset.sum_add_distrib]
  have hdiff_erase :
      ∑ x ∈ (Finset.univ : Finset α).erase a, (f x - g x) = f b - g b := by
    apply Finset.sum_eq_single_of_mem b
    · simp [hab.symm]
    · intro x hx hxb
      have hxa : x ≠ a := by
        simpa using hx
      rw [hoff x hxa hxb]
      ring
  have hdiff : ∑ x : α, (f x - g x) = (f a - g a) + (f b - g b) := by
    have herase_add := Finset.sum_erase_add (s := (Finset.univ : Finset α))
      (f := fun x => f x - g x) (a := a) (by simp)
    rw [hdiff_erase] at herase_add
    linarith
  rw [hfg, hsumadd, hdiff]
  ring

/--
A weighted sum of quantities bounded above by `B` is bounded above by `B`
whenever the weights are nonnegative, have total mass at most one, and `B` is
nonnegative.
-/
theorem finset_weighted_sum_le_bound_of_nonneg_sum_le_one
    {α : Type*} (s : Finset α) (weight value : α → ℝ) {B : ℝ}
    (hweight_nonneg : ∀ i, i ∈ s → 0 ≤ weight i)
    (hweight_sum : (∑ i ∈ s, weight i) ≤ 1)
    (hvalue : ∀ i, i ∈ s → value i ≤ B)
    (hB : 0 ≤ B) :
    (∑ i ∈ s, weight i * value i) ≤ B := by
  calc
    (∑ i ∈ s, weight i * value i)
        ≤ ∑ i ∈ s, weight i * B := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hvalue i ‹i ∈ s›)
              (hweight_nonneg i ‹i ∈ s›)
    _ = (∑ i ∈ s, weight i) * B := by
          rw [← Finset.sum_mul]
    _ ≤ 1 * B := by
          exact mul_le_mul_of_nonneg_right hweight_sum hB
    _ = B := by ring

/--
A weighted sum over a finite type is bounded by `B` under the same hypotheses
as the finset version, with the support set specialized to `univ`.
-/
theorem weighted_sum_le_bound_of_nonneg_sum_le_one
    {α : Type*} [Fintype α] (weight value : α → ℝ) {B : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_sum : (∑ i : α, weight i) ≤ 1)
    (hvalue : ∀ i, value i ≤ B)
    (hB : 0 ≤ B) :
    (∑ i : α, weight i * value i) ≤ B := by
  exact finset_weighted_sum_le_bound_of_nonneg_sum_le_one
    (Finset.univ : Finset α) weight value
    (by intro i _; exact hweight_nonneg i)
    (by simpa using hweight_sum)
    (by intro i _; exact hvalue i)
    hB

/-- Telescoping identity for adjacent real sequence increments. -/
theorem sum_range_probabilityIncrements
    (p : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (p (j + 1) - p j)) = p n - p 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/--
Finite averaging: if `total` is at most the sum of finitely many bin masses,
then some bin has at least a `1/card` share of `total`.
-/
theorem exists_total_le_card_mul_of_le_sum
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (mass : κ → ℝ) {total : ℝ}
    (htotal : total ≤ ∑ k : κ, mass k) :
    ∃ k : κ, total ≤ (Fintype.card κ : ℝ) * mass k := by
  classical
  let cardR : ℝ := Fintype.card κ
  have hcard_pos : 0 < cardR := by
    dsimp [cardR]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card κ)
  have hcard_ne : cardR ≠ 0 := ne_of_gt hcard_pos
  have huniv_nonempty : (Finset.univ : Finset κ).Nonempty := by
    obtain ⟨k⟩ := (inferInstance : Nonempty κ)
    exact ⟨k, by simp⟩
  have havg_sum :
      (∑ k : κ, total / cardR) ≤ ∑ k : κ, mass k := by
    have hsum_const :
        (∑ _k : κ, total / cardR) = total := by
      rw [Finset.sum_const, Finset.card_univ]
      rw [nsmul_eq_mul]
      change (Fintype.card κ : ℝ) * (total / cardR) = total
      dsimp [cardR]
      rw [mul_comm]
      exact div_mul_cancel₀ total (by exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card κ)))
    rw [hsum_const]
    exact htotal
  obtain ⟨k, _hk, hkavg⟩ :=
    Finset.exists_le_of_sum_le (s := (Finset.univ : Finset κ))
      (f := fun _ : κ => total / cardR) (g := mass)
      huniv_nonempty (by simpa using havg_sum)
  refine ⟨k, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hkavg (le_of_lt hcard_pos)
  calc
    total = cardR * (total / cardR) := by
      rw [mul_comm]
      exact (div_mul_cancel₀ total hcard_ne).symm
    _ ≤ cardR * mass k := hmul
    _ = (Fintype.card κ : ℝ) * mass k := by rfl

/-- Cauchy-Schwarz for a finite real sum against the all-ones vector. -/
theorem sq_sum_le_card_mul_sum_sq
    {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  have h :=
    Finset.sum_mul_sq_le_sq_mul_sq
      (s := s) (f := f) (g := fun _ => (1 : ℝ))
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h

/--
Compare a finite sum over an injectively indexed subfamily to a larger
nonnegative finite sum. This is useful when a proof lower-bounds an expectation
by keeping only a disjoint set of summands.
-/
theorem sum_le_sum_of_injective_nonneg
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (φ : α → β) (hφ : Function.Injective φ)
    {f : α → ℝ} {g : β → ℝ}
    (hfg : ∀ a, f a ≤ g (φ a))
    (hg_nonneg : ∀ b, 0 ≤ g b) :
    (∑ a : α, f a) ≤ ∑ b : β, g b := by
  classical
  let e : α ↪ β := ⟨φ, hφ⟩
  have hpoint :
      (∑ a : α, f a) ≤ ∑ a : α, g (φ a) :=
    Finset.sum_le_sum fun a _ => hfg a
  have hmap :
      (∑ a : α, g (φ a)) =
        ∑ b ∈ (Finset.univ : Finset α).map e, g b := by
    symm
    simpa [e] using
      (Finset.sum_map (s := (Finset.univ : Finset α)) (f := g) (e := e))
  have hsubset :
      (Finset.univ : Finset α).map e ⊆ (Finset.univ : Finset β) := by
    intro b _hb
    simp
  have hlarge :
      (∑ b ∈ (Finset.univ : Finset α).map e, g b) ≤
        ∑ b : β, g b := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro b _hb _hnot; exact hg_nonneg b)
  exact le_trans hpoint (by simpa [hmap] using hlarge)

/--
Discrete crossing for Boolean predicates on a finite integer interval. If a
predicate is false at `lo` and true at `hi`, then it switches from false to true
across some adjacent pair.
-/
theorem exists_bool_transition
    (f : ℕ → Bool) :
    ∀ {lo hi : ℕ}, lo < hi → f lo = false → f hi = true →
      ∃ k : ℕ, lo < k ∧ k ≤ hi ∧ f (k - 1) = false ∧ f k = true
  | lo, 0, hlohi, _, _ => by
      exact False.elim (Nat.not_lt_zero lo hlohi)
  | lo, Nat.succ hi, hlohi, hlo_false, hhi_true => by
      by_cases hlo_eq_hi : lo = hi
      · refine ⟨hi + 1, ?_, le_rfl, ?_, hhi_true⟩
        · subst lo
          exact Nat.lt_succ_self hi
        · simpa [hlo_eq_hi] using hlo_false
      · have hlo_lt_hi : lo < hi := by
          have hlo_le_hi : lo ≤ hi := Nat.lt_succ_iff.mp hlohi
          exact lt_of_le_of_ne hlo_le_hi hlo_eq_hi
        by_cases hmid_true : f hi = true
        · obtain ⟨k, hklo, hkhi, hkprev, hktrue⟩ :=
            exists_bool_transition f hlo_lt_hi hlo_false hmid_true
          exact ⟨k, hklo, Nat.le_trans hkhi (Nat.le_succ hi), hkprev, hktrue⟩
        · have hmid_false : f hi = false := by
            cases h : f hi
            · rfl
            · exact False.elim (hmid_true h)
          refine ⟨hi + 1, hlohi, le_rfl, ?_, hhi_true⟩
          simpa using hmid_false

/--
If `0 < k <= m`, then subtracting the predecessor of `k` leaves one more than
subtracting `k`.
-/
theorem nat_sub_pred_eq_sub_add_one_of_pos_le
    {m k : ℕ} (hk_pos : 0 < k) (hk_le_m : k ≤ m) :
    m - (k - 1) = m - k + 1 := by
  have hk_pred_succ : k - 1 + 1 = k :=
    Nat.sub_one_add_one_eq_of_pos hk_pos
  have hk_pred_lt_m : k - 1 < m := by
    exact lt_of_lt_of_le (Nat.sub_lt hk_pos zero_lt_one) hk_le_m
  have hdiff_pos : 0 < m - (k - 1) :=
    Nat.sub_pos_of_lt hk_pred_lt_m
  have hsub_one :
      (m - (k - 1)) - 1 = m - k := by
    rw [Nat.sub_sub, hk_pred_succ]
  calc
    m - (k - 1) = (m - (k - 1)) - 1 + 1 :=
      (Nat.sub_one_add_one_eq_of_pos hdiff_pos).symm
    _ = m - k + 1 := by rw [hsub_one]

/--
Telescoping identity used in the GHW Theorem 8.2 revenue rearrangement.
The dummy probability `p 0` is zero, so adjacent probability increments against
the bid levels combine with the utility-gap correction terms to leave only the
last endpoint term.
-/
theorem sum_range_gap_add_probabilityIncrement_mul
    (p b : ℕ → ℝ) (hp0 : p 0 = 0) (n : ℕ) :
    (∑ j ∈ Finset.range n, p (j + 1) * (b (j + 1) - b j)) +
        (∑ j ∈ Finset.range n, (p (j + 1) - p j) * b j) =
      p n * b n := by
  induction n with
  | zero =>
      simp [hp0]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      nlinarith [ih]

/--
Adjacent truthful-gain inequalities imply the accumulated utility-gap lower
bound used in GHW Theorem 8.2.
-/
theorem sum_range_gap_le_gain_of_adjacent
    (p b gain : ℕ → ℝ)
    (hgain0 : 0 ≤ gain 0)
    (hstep :
      ∀ i,
        gain i + p (i + 1) * (b (i + 1) - b i) ≤ gain (i + 1)) :
    ∀ i,
      (∑ j ∈ Finset.range i, p (j + 1) * (b (j + 1) - b j)) ≤
        gain i := by
  intro i
  induction i with
  | zero =>
      simpa using hgain0
  | succ i ih =>
      rw [Finset.sum_range_succ]
      have hle :=
        add_le_add_right ih (p (i + 1) * (b (i + 1) - b i))
      have hnext := hstep i
      linarith

/-- Fixed-price revenue for the bidder value at rank `j` among `n` sorted bids. -/
noncomputable def rankedFixedPriceRevenue (n : ℕ) (b : ℕ → ℝ) (j : ℕ) : ℝ :=
  ((n : ℝ) - j) * b j

/--
If each ranked bidder's expected payment is bounded by the paper's truthful-gain
upper bound, then total revenue is bounded by the telescoping weighted sum of
ranked fixed-price revenues.

This is the algebraic heart of GHW Theorem 8.2 before applying Lemma 8.1 and
the benchmark bound `V_j <= F`.
-/
theorem sum_range_revenue_le_probabilityIncrement_rankedFixedPriceRevenue
    (n : ℕ) (p b r : ℕ → ℝ) (hp0 : p 0 = 0)
    (hr :
      ∀ i, i < n →
        r i ≤ p (i + 1) * b i -
          ∑ j ∈ Finset.range i, p (j + 1) * (b (j + 1) - b j)) :
    (∑ i ∈ Finset.range n, r i) ≤
      ∑ j ∈ Finset.range n,
        (p (j + 1) - p j) * rankedFixedPriceRevenue n b j := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have ih' :
          (∑ i ∈ Finset.range n, r i) ≤
            ∑ j ∈ Finset.range n,
              (p (j + 1) - p j) * rankedFixedPriceRevenue n b j := by
        exact ih (by
          intro i hi
          exact hr i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      let gapSum : ℝ :=
        ∑ j ∈ Finset.range n, p (j + 1) * (b (j + 1) - b j)
      let incBidSum : ℝ :=
        ∑ j ∈ Finset.range n, (p (j + 1) - p j) * b j
      have hnew :
          r n ≤ p (n + 1) * b n - gapSum := by
        simpa [gapSum] using hr n (Nat.lt_succ_self n)
      have htarget_succ :
          (∑ j ∈ Finset.range (n + 1),
              (p (j + 1) - p j) *
                rankedFixedPriceRevenue (n + 1) b j) =
            (∑ j ∈ Finset.range n,
              (p (j + 1) - p j) * rankedFixedPriceRevenue n b j) +
              incBidSum + (p (n + 1) - p n) * b n := by
        rw [Finset.sum_range_succ]
        have hprefix :
            (∑ j ∈ Finset.range n,
                (p (j + 1) - p j) *
                  rankedFixedPriceRevenue (n + 1) b j) =
              (∑ j ∈ Finset.range n,
                (p (j + 1) - p j) *
                  rankedFixedPriceRevenue n b j) +
                incBidSum := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [rankedFixedPriceRevenue]
          ring
        rw [hprefix]
        simp [rankedFixedPriceRevenue]
      have hgap_inc :
          gapSum + incBidSum = p n * b n := by
        simpa [gapSum, incBidSum]
          using sum_range_gap_add_probabilityIncrement_mul p b hp0 n
      rw [Finset.sum_range_succ, htarget_succ]
      linarith

/--
Paper-style weighted benchmark bound for monotone probability increments.
If expected revenue is bounded by a weighted sum whose weights are adjacent
increments of a monotone probability sequence and whose endpoint mass is at
most one, then the expected revenue is bounded by the common benchmark.
-/
theorem le_bound_of_le_range_probabilityIncrement_weighted_sum
    (n : ℕ) (p value : ℕ → ℝ) {R B : ℝ}
    (hR :
      R ≤ ∑ j ∈ Finset.range n, (p (j + 1) - p j) * value j)
    (hmono : ∀ j, j < n → p j ≤ p (j + 1))
    (hendpoint : p n - p 0 ≤ 1)
    (hvalue : ∀ j, j < n → value j ≤ B)
    (hB : 0 ≤ B) :
    R ≤ B := by
  have hweight_nonneg :
      ∀ j, j ∈ Finset.range n → 0 ≤ p (j + 1) - p j := by
    intro j hj
    exact sub_nonneg.mpr (hmono j (Finset.mem_range.mp hj))
  have hweight_sum :
      (∑ j ∈ Finset.range n, (p (j + 1) - p j)) ≤ 1 := by
    rw [sum_range_probabilityIncrements]
    exact hendpoint
  have hweighted :
      (∑ j ∈ Finset.range n, (p (j + 1) - p j) * value j) ≤ B := by
    exact finset_weighted_sum_le_bound_of_nonneg_sum_le_one
      (Finset.range n) (fun j => p (j + 1) - p j) value
      hweight_nonneg hweight_sum
      (by intro j hj; exact hvalue j (Finset.mem_range.mp hj)) hB
  exact le_trans hR hweighted

/--
GHW Theorem 8.2 algebra from the adjacent truthful-gain recursion all the way
to the benchmark bound.
-/
theorem revenue_le_bound_of_adjacent_gain_recursion
    (n : ℕ) (p b revenueAtRank gain : ℕ → ℝ) {R B : ℝ}
    (hp0 : p 0 = 0)
    (hR : R ≤ ∑ i ∈ Finset.range n, revenueAtRank i)
    (hrevenueAtRank :
      ∀ i, i < n → revenueAtRank i = p (i + 1) * b i - gain i)
    (hgain0 : 0 ≤ gain 0)
    (hgain_step :
      ∀ i,
        gain i + p (i + 1) * (b (i + 1) - b i) ≤ gain (i + 1))
    (hmono : ∀ j, j < n → p j ≤ p (j + 1))
    (hendpoint : p n - p 0 ≤ 1)
    (hvalue :
      ∀ j, j < n → rankedFixedPriceRevenue n b j ≤ B)
    (hB : 0 ≤ B) :
    R ≤ B := by
  have hgap_le :
      ∀ i,
        (∑ j ∈ Finset.range i, p (j + 1) * (b (j + 1) - b j)) ≤
          gain i :=
    sum_range_gap_le_gain_of_adjacent p b gain hgain0 hgain_step
  have hranked :
      ∀ i, i < n →
        revenueAtRank i ≤ p (i + 1) * b i -
          ∑ j ∈ Finset.range i, p (j + 1) * (b (j + 1) - b j) := by
    intro i hi
    rw [hrevenueAtRank i hi]
    linarith [hgap_le i]
  have hrearranged :
      R ≤ ∑ j ∈ Finset.range n,
        (p (j + 1) - p j) * rankedFixedPriceRevenue n b j := by
    exact le_trans hR
      (sum_range_revenue_le_probabilityIncrement_rankedFixedPriceRevenue
        n p b revenueAtRank hp0 hranked)
  exact le_bound_of_le_range_probabilityIncrement_weighted_sum
    n p (rankedFixedPriceRevenue n b) hrearranged hmono hendpoint hvalue hB

/--
GHW Theorem 8.2 algebra in the paper's `p_i`, `c_i`, `g_i` notation. The
truthfulness comparison for adjacent bids is supplied as
`p_i * (b_{i+1} - c_i) <= g_{i+1}`.
-/
theorem revenue_le_bound_of_adjacent_truthful_cost_comparisons
    (n : ℕ) (p b cost gain : ℕ → ℝ) {R B : ℝ}
    (hp0 : p 0 = 0)
    (hR : R ≤ ∑ i ∈ Finset.range n, p (i + 1) * cost i)
    (hgain :
      ∀ i, gain i = p (i + 1) * (b i - cost i))
    (hgain0 : 0 ≤ gain 0)
    (htruth_adjacent :
      ∀ i, p (i + 1) * (b (i + 1) - cost i) ≤ gain (i + 1))
    (hmono : ∀ j, j < n → p j ≤ p (j + 1))
    (hendpoint : p n - p 0 ≤ 1)
    (hvalue :
      ∀ j, j < n → rankedFixedPriceRevenue n b j ≤ B)
    (hB : 0 ≤ B) :
    R ≤ B := by
  let revenueAtRank : ℕ → ℝ := fun i => p (i + 1) * cost i
  have hrevenueAtRank :
      ∀ i, i < n → revenueAtRank i = p (i + 1) * b i - gain i := by
    intro i hi
    dsimp [revenueAtRank]
    rw [hgain i]
    ring
  have hgain_step :
      ∀ i,
        gain i + p (i + 1) * (b (i + 1) - b i) ≤ gain (i + 1) := by
    intro i
    have hg := hgain i
    have ht := htruth_adjacent i
    calc
      gain i + p (i + 1) * (b (i + 1) - b i)
          = p (i + 1) * (b (i + 1) - cost i) := by
            rw [hg]
            ring
      _ ≤ gain (i + 1) := ht
  exact revenue_le_bound_of_adjacent_gain_recursion
    n p b revenueAtRank gain hp0 (by simpa [revenueAtRank] using hR)
    hrevenueAtRank hgain0 hgain_step hmono hendpoint hvalue hB

/--
Bounded version of `sum_range_gap_le_gain_of_adjacent`: adjacent utility-gap
steps are needed only inside the finite rank range.
-/
theorem sum_range_gap_le_gain_of_adjacent_bounded
    (n : ℕ) (p b gain : ℕ → ℝ)
    (hgain0 : 0 ≤ gain 0)
    (hstep :
      ∀ i, i + 1 < n →
        gain i + p (i + 1) * (b (i + 1) - b i) ≤ gain (i + 1)) :
    ∀ i, i < n →
      (∑ j ∈ Finset.range i, p (j + 1) * (b (j + 1) - b j)) ≤
        gain i := by
  intro i hi
  induction i with
  | zero =>
      simpa using hgain0
  | succ i ih =>
      rw [Finset.sum_range_succ]
      have hi_prev : i < n := Nat.lt_trans (Nat.lt_succ_self i) hi
      have hle :=
        add_le_add_right (ih hi_prev) (p (i + 1) * (b (i + 1) - b i))
      have hnext := hstep i hi
      linarith

/--
Bounded adjacent-gain version of the GHW Theorem 8.2 algebra. The recursion
only needs adjacent steps `i -> i+1` when `i+1 < n`.
-/
theorem revenue_le_bound_of_adjacent_gain_recursion_bounded
    (n : ℕ) (p b revenueAtRank gain : ℕ → ℝ) {R B : ℝ}
    (hp0 : p 0 = 0)
    (hR : R ≤ ∑ i ∈ Finset.range n, revenueAtRank i)
    (hrevenueAtRank :
      ∀ i, i < n → revenueAtRank i = p (i + 1) * b i - gain i)
    (hgain0 : 0 ≤ gain 0)
    (hgain_step :
      ∀ i, i + 1 < n →
        gain i + p (i + 1) * (b (i + 1) - b i) ≤ gain (i + 1))
    (hmono : ∀ j, j < n → p j ≤ p (j + 1))
    (hendpoint : p n - p 0 ≤ 1)
    (hvalue :
      ∀ j, j < n → rankedFixedPriceRevenue n b j ≤ B)
    (hB : 0 ≤ B) :
    R ≤ B := by
  have hgap_le :
      ∀ i, i < n →
        (∑ j ∈ Finset.range i, p (j + 1) * (b (j + 1) - b j)) ≤
          gain i :=
    sum_range_gap_le_gain_of_adjacent_bounded n p b gain hgain0 hgain_step
  have hranked :
      ∀ i, i < n →
        revenueAtRank i ≤ p (i + 1) * b i -
          ∑ j ∈ Finset.range i, p (j + 1) * (b (j + 1) - b j) := by
    intro i hi
    rw [hrevenueAtRank i hi]
    linarith [hgap_le i hi]
  have hrearranged :
      R ≤ ∑ j ∈ Finset.range n,
        (p (j + 1) - p j) * rankedFixedPriceRevenue n b j := by
    exact le_trans hR
      (sum_range_revenue_le_probabilityIncrement_rankedFixedPriceRevenue
        n p b revenueAtRank hp0 hranked)
  exact le_bound_of_le_range_probabilityIncrement_weighted_sum
    n p (rankedFixedPriceRevenue n b) hrearranged hmono hendpoint hvalue hB

/--
Bounded version of the paper's `p_i`, `c_i`, `g_i` Theorem 8.2 algebra. The
truthfulness comparison is required only for adjacent ranked bidders inside the
finite profile.
-/
theorem revenue_le_bound_of_adjacent_truthful_cost_comparisons_bounded
    (n : ℕ) (p b cost gain : ℕ → ℝ) {R B : ℝ}
    (hp0 : p 0 = 0)
    (hR : R ≤ ∑ i ∈ Finset.range n, p (i + 1) * cost i)
    (hgain :
      ∀ i, gain i = p (i + 1) * (b i - cost i))
    (hgain0 : 0 ≤ gain 0)
    (htruth_adjacent :
      ∀ i, i + 1 < n →
        p (i + 1) * (b (i + 1) - cost i) ≤ gain (i + 1))
    (hmono : ∀ j, j < n → p j ≤ p (j + 1))
    (hendpoint : p n - p 0 ≤ 1)
    (hvalue :
      ∀ j, j < n → rankedFixedPriceRevenue n b j ≤ B)
    (hB : 0 ≤ B) :
    R ≤ B := by
  let revenueAtRank : ℕ → ℝ := fun i => p (i + 1) * cost i
  have hrevenueAtRank :
      ∀ i, i < n → revenueAtRank i = p (i + 1) * b i - gain i := by
    intro i hi
    dsimp [revenueAtRank]
    rw [hgain i]
    ring
  have hgain_step :
      ∀ i, i + 1 < n →
        gain i + p (i + 1) * (b (i + 1) - b i) ≤ gain (i + 1) := by
    intro i hi
    have hg := hgain i
    have ht := htruth_adjacent i hi
    calc
      gain i + p (i + 1) * (b (i + 1) - b i)
          = p (i + 1) * (b (i + 1) - cost i) := by
            rw [hg]
            ring
      _ ≤ gain (i + 1) := ht
  exact revenue_le_bound_of_adjacent_gain_recursion_bounded
    n p b revenueAtRank gain hp0 (by simpa [revenueAtRank] using hR)
    hrevenueAtRank hgain0 hgain_step hmono hendpoint hvalue hB

end FiniteSum
end EconCSLib
