import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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

/-- If every term in a finite set is at most `C`, the finite sum is at most
the set cardinality times `C`. -/
theorem finset_sum_le_card_mul_of_forall_le
    {α : Type*} (s : Finset α) (v : α → ℝ) (C : ℝ)
    (h : ∀ i ∈ s, v i ≤ C) :
    (∑ i ∈ s, v i) ≤ (s.card : ℝ) * C := by
  calc
    (∑ i ∈ s, v i) ≤ ∑ i ∈ s, C :=
      Finset.sum_le_sum h
    _ = (s.card : ℝ) * C := by
      simp

/-- Product of a two-valued coordinate weight over a finite type. -/
theorem prod_ite_mem_eq_pow_mul_pow {α : Type*}
    [Fintype α] [DecidableEq α] (s : Finset α) (q rho : ℝ) :
    (∏ i : α, if i ∈ s then q else rho) =
      q ^ s.card * rho ^ (Fintype.card α - s.card) := by
  classical
  have hfilter :
      (Finset.univ : Finset α).filter (fun i => i ∈ s) = s := by
    ext i
    simp
  have hfilter_not_card :
      ((Finset.univ : Finset α).filter (fun i => ¬ i ∈ s)).card =
        Fintype.card α - s.card := by
    have hsum :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset α)) (p := fun i => i ∈ s)
    rw [hfilter, Finset.card_univ] at hsum
    omega
  calc
    (∏ i : α, if i ∈ s then q else rho)
        = (∏ i ∈ (Finset.univ : Finset α),
            if i ∈ s then q else rho) := by
          simp
    _ = (∏ i ∈ (Finset.univ : Finset α) with i ∈ s, q) *
          ∏ i ∈ (Finset.univ : Finset α) with ¬ i ∈ s, rho := by
          rw [Finset.prod_ite]
    _ = q ^ s.card * rho ^ (Fintype.card α - s.card) := by
          simp [hfilter, hfilter_not_card]

/--
Regroup a finite double sum into ordered off-diagonal pairs, using an
injective key to decide which orientation of each pair is canonical.
-/
theorem pair_sum_eq_ordered_swap_sum_of_injective_key
    {α β : Type*} [Fintype α] [DecidableEq α] [LinearOrder β]
    (key : α → β) (hkey : Function.Injective key) (t : α → α → ℝ)
    (hdiag : ∀ a : α, t a a = 0) :
    (∑ a : α, ∑ b : α, t a b) =
      ∑ a : α, ∑ b : α,
        if key a < key b then t a b + t b a else 0 := by
  classical
  have hsplit : ∀ a b : α,
      t a b =
        (if key a < key b then t a b else 0) +
          (if key b < key a then t a b else 0) := by
    intro a b
    by_cases hlt : key a < key b
    · have hnot : ¬ key b < key a := not_lt_of_gt hlt
      simp [hlt, hnot]
    · by_cases hgt : key b < key a
      · simp [hlt, hgt]
      · have hkey_eq : key a = key b :=
          le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
        have hab : a = b := hkey hkey_eq
        subst b
        simp [hdiag]
  calc
    (∑ a : α, ∑ b : α, t a b)
        = ∑ a : α, ∑ b : α,
            ((if key a < key b then t a b else 0) +
              (if key b < key a then t a b else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro b _
          exact hsplit a b
    _ = (∑ a : α, ∑ b : α,
            if key a < key b then t a b else 0) +
          (∑ a : α, ∑ b : α,
            if key b < key a then t a b else 0) := by
          simp_rw [Finset.sum_add_distrib]
    _ = (∑ a : α, ∑ b : α,
            if key a < key b then t a b else 0) +
          (∑ a : α, ∑ b : α,
            if key a < key b then t b a else 0) := by
          have hswap :
              (∑ a : α, ∑ b : α,
                if key b < key a then t a b else 0) =
                ∑ a : α, ∑ b : α,
                  if key a < key b then t b a else 0 := by
            rw [Finset.sum_comm]
          rw [hswap]
    _ = ∑ a : α, ∑ b : α,
          if key a < key b then t a b + t b a else 0 := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro b _
          by_cases hlt : key a < key b <;> simp [hlt]

/-- Regroup a finite double sum into ordered off-diagonal pairs. -/
theorem pair_sum_eq_ordered_swap_sum
    {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (t : α → α → ℝ) (hdiag : ∀ a : α, t a a = 0) :
    (∑ a : α, ∑ b : α, t a b) =
      ∑ a : α, ∑ b : α,
        if a < b then t a b + t b a else 0 :=
  pair_sum_eq_ordered_swap_sum_of_injective_key (fun a : α => a)
    (fun _ _ h => h) t hdiag

/--
Pairwise cross-ratio dominance implies a cleared weighted-average comparison.
If `wA i * wH j >= wA j * wH i` for every `i < j`, then every weakly
decreasing payoff `B` has at least as large a `wA` average as a `wH` average
after clearing denominators.
-/
theorem weighted_average_cross_nonneg_of_pairwise
    {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {wA wH B : α → ℝ}
    (hpair : ∀ i j : α, i < j → 0 ≤ wA i * wH j - wA j * wH i)
    (hB : ∀ i j : α, i < j → B j ≤ B i) :
    0 ≤
      (∑ j : α, wH j) * (∑ i : α, wA i * B i) -
        (∑ j : α, wA j) * (∑ i : α, wH i * B i) := by
  classical
  let t : α → α → ℝ := fun i j =>
    wA i * B i * wH j - wH i * B i * wA j
  have hdouble :
      (∑ j : α, wH j) * (∑ i : α, wA i * B i) -
        (∑ j : α, wA j) * (∑ i : α, wH i * B i) =
        ∑ i : α, ∑ j : α, t i j := by
    calc
      (∑ j : α, wH j) * (∑ i : α, wA i * B i) -
          (∑ j : α, wA j) * (∑ i : α, wH i * B i)
          =
          (∑ i : α, ∑ j : α, wA i * B i * wH j) -
            (∑ i : α, ∑ j : α, wH i * B i * wA j) := by
            rw [Finset.sum_mul, Finset.sum_mul]
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
      _ = ∑ i : α, ∑ j : α, t i j := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_sub_distrib]
  rw [hdouble]
  rw [pair_sum_eq_ordered_swap_sum t (by intro i; simp [t]; ring)]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  by_cases hij : i < j
  · have heq :
        t i j + t j i = (wA i * wH j - wA j * wH i) * (B i - B j) := by
      simp [t]
      ring
    rw [if_pos hij, heq]
    exact mul_nonneg (hpair i j hij) (sub_nonneg.mpr (hB i j hij))
  · simp [hij]

/--
Strict version of `weighted_average_cross_nonneg_of_pairwise`: one strictly
positive pairwise cross-ratio bracket and a strictly decreasing payoff make
the cleared comparison strict.
-/
theorem weighted_average_cross_pos_of_pairwise
    {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {wA wH B : α → ℝ}
    (hpair_nonneg :
      ∀ i j : α, i < j → 0 ≤ wA i * wH j - wA j * wH i)
    (hpair_pos :
      ∃ i j : α, i < j ∧ 0 < wA i * wH j - wA j * wH i)
    (hB : StrictAnti B) :
    0 <
      (∑ j : α, wH j) * (∑ i : α, wA i * B i) -
        (∑ j : α, wA j) * (∑ i : α, wH i * B i) := by
  classical
  let t : α → α → ℝ := fun i j =>
    wA i * B i * wH j - wH i * B i * wA j
  have hdouble :
      (∑ j : α, wH j) * (∑ i : α, wA i * B i) -
        (∑ j : α, wA j) * (∑ i : α, wH i * B i) =
        ∑ i : α, ∑ j : α, t i j := by
    calc
      (∑ j : α, wH j) * (∑ i : α, wA i * B i) -
          (∑ j : α, wA j) * (∑ i : α, wH i * B i)
          =
          (∑ i : α, ∑ j : α, wA i * B i * wH j) -
            (∑ i : α, ∑ j : α, wH i * B i * wA j) := by
            rw [Finset.sum_mul, Finset.sum_mul]
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
      _ = ∑ i : α, ∑ j : α, t i j := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.sum_sub_distrib]
  rw [hdouble]
  rw [pair_sum_eq_ordered_swap_sum t (by intro i; simp [t]; ring)]
  rcases hpair_pos with ⟨i₀, j₀, hij₀, hcross₀⟩
  have hrow_nonneg : ∀ i : α,
      0 ≤
        ∑ j : α, if i < j then t i j + t j i else 0 := by
    intro i
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i < j
    · have heq :
          t i j + t j i = (wA i * wH j - wA j * wH i) * (B i - B j) := by
        simp [t]
        ring
      rw [if_pos hij, heq]
      exact mul_nonneg (hpair_nonneg i j hij)
        (le_of_lt (sub_pos.mpr (hB hij)))
    · simp [hij]
  have hrow_pos :
      0 <
        ∑ j : α, if i₀ < j then t i₀ j + t j i₀ else 0 := by
    have hterm_nonneg :
        ∀ j : α, 0 ≤ if i₀ < j then t i₀ j + t j i₀ else 0 := by
      intro j
      by_cases hij : i₀ < j
      · have heq :
            t i₀ j + t j i₀ =
              (wA i₀ * wH j - wA j * wH i₀) * (B i₀ - B j) := by
          simp [t]
          ring
        rw [if_pos hij, heq]
        exact mul_nonneg (hpair_nonneg i₀ j hij)
          (le_of_lt (sub_pos.mpr (hB hij)))
      · simp [hij]
    have hterm_pos :
        0 < if i₀ < j₀ then t i₀ j₀ + t j₀ i₀ else 0 := by
      have heq :
          t i₀ j₀ + t j₀ i₀ =
            (wA i₀ * wH j₀ - wA j₀ * wH i₀) * (B i₀ - B j₀) := by
        simp [t]
        ring
      rw [if_pos hij₀, heq]
      exact mul_pos hcross₀ (sub_pos.mpr (hB hij₀))
    have hle :
        (if i₀ < j₀ then t i₀ j₀ + t j₀ i₀ else 0) ≤
          ∑ j : α, if i₀ < j then t i₀ j + t j i₀ else 0 :=
      Finset.single_le_sum (fun j _ => hterm_nonneg j) (by simp)
    exact lt_of_lt_of_le hterm_pos hle
  have hle :
      (∑ j : α, if i₀ < j then t i₀ j + t j i₀ else 0) ≤
        ∑ i : α, ∑ j : α, if i < j then t i j + t j i else 0 :=
    Finset.single_le_sum (fun i _ => hrow_nonneg i) (by simp)
  exact lt_of_lt_of_le hrow_pos hle

/--
If every element of a finite comparison set has weight at least `a`'s weight,
then `a`'s share of the combined weight of `a` and that set is at most
`1 / (|s| + 1)`.
-/
theorem weight_share_le_inv_card_add_one_of_forall_le
    {α : Type*} (s : Finset α) (weight : α → ℝ) (a : α)
    (ha_nonneg : 0 ≤ weight a)
    (hden_pos : 0 < weight a + ∑ i ∈ s, weight i)
    (hle : ∀ i ∈ s, weight a ≤ weight i) :
    weight a / (weight a + ∑ i ∈ s, weight i) ≤
      1 / ((s.card : ℝ) + 1) := by
  have hcard_pos : 0 < (s.card : ℝ) + 1 := by positivity
  have hsum_ge :
      (s.card : ℝ) * weight a ≤ ∑ i ∈ s, weight i := by
    calc
      (s.card : ℝ) * weight a = ∑ _i ∈ s, weight a := by
          simp [nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, weight i :=
          Finset.sum_le_sum (by
            intro i hi
            exact hle i hi)
  rw [div_le_div_iff₀ hden_pos hcard_pos]
  nlinarith

/--
If every term in a finite sum is at least `x`, then the whole sum is at least
`|s| * x`.
-/
theorem card_mul_le_sum_of_forall_le
    {α : Type*} (s : Finset α) (f : α → ℝ) {x : ℝ}
    (hle : ∀ i ∈ s, x ≤ f i) :
    (s.card : ℝ) * x ≤ ∑ i ∈ s, f i := by
  calc
    (s.card : ℝ) * x = ∑ _i ∈ s, x := by
        simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, f i :=
        Finset.sum_le_sum (by
          intro i hi
          exact hle i hi)

/--
Finite averaging upper bound: if every term in `s` is at least `x`, but the
sum over `s` is at most `total`, then `x <= total / |s|`.
-/
theorem le_div_card_of_sum_le_of_forall_le
    {α : Type*} (s : Finset α) (f : α → ℝ) {x total : ℝ}
    (hcard_pos : 0 < s.card)
    (hsum_le : (∑ i ∈ s, f i) ≤ total)
    (hle : ∀ i ∈ s, x ≤ f i) :
    x ≤ total / (s.card : ℝ) := by
  have hcard_real_pos : 0 < (s.card : ℝ) := by
    exact_mod_cast hcard_pos
  rw [le_div_iff₀ hcard_real_pos]
  rw [mul_comm]
  exact le_trans (card_mul_le_sum_of_forall_le s f hle) hsum_le

/--
Compare a finite sum over `s` to a finite sum over `t` using an injection from
`s` into `t`, pointwise domination along the injection, and nonnegativity of
the unused target terms.
-/
theorem finset_sum_le_sum_of_injOn_nonneg
    {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (φ : α → β)
    (f : α → ℝ) (g : β → ℝ)
    (hφ_mem : ∀ a ∈ s, φ a ∈ t)
    (hφ_inj : Set.InjOn φ (↑s : Set α))
    (hfg : ∀ a ∈ s, f a ≤ g (φ a))
    (hg_nonneg : ∀ b ∈ t, 0 ≤ g b) :
    (∑ a ∈ s, f a) ≤ ∑ b ∈ t, g b := by
  classical
  have hpoint :
      (∑ a ∈ s, f a) ≤ ∑ a ∈ s, g (φ a) :=
    Finset.sum_le_sum (by
      intro a ha
      exact hfg a ha)
  have himage :
      (∑ a ∈ s, g (φ a)) = ∑ b ∈ s.image φ, g b := by
    rw [Finset.sum_image]
    intro a ha a' ha' hsame
    exact hφ_inj ha ha' hsame
  have hsubset : s.image φ ⊆ t := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    exact hφ_mem a ha
  have htarget :
      (∑ b ∈ s.image φ, g b) ≤ ∑ b ∈ t, g b :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by
        intro b _hb hbt
        exact hg_nonneg b _hb)
  exact le_trans hpoint (by simpa [himage] using htarget)

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

/--
Finite average witness: on a nonempty finite type, some term is at least the
uniform average.
-/
theorem exists_fintype_average_le
    {κ : Type*} [Fintype κ] [Nonempty κ] (value : κ → ℝ) :
    ∃ k : κ,
      (∑ i : κ, value i) / (Fintype.card κ : ℝ) ≤ value k := by
  classical
  obtain ⟨k, hk⟩ :=
    exists_total_le_card_mul_of_le_sum value
      (total := ∑ i : κ, value i) le_rfl
  refine ⟨k, ?_⟩
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card κ)
  have hcard_nonneg : 0 ≤ (Fintype.card κ : ℝ) := le_of_lt hcard_pos
  have hdiv :=
    div_le_div_of_nonneg_right hk hcard_nonneg
  have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 := ne_of_gt hcard_pos
  simpa [mul_div_cancel_left₀ _ hcard_ne] using hdiv

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
Exchange comparison for two finite sums.  If `s` has no more elements than
`t`, every element in `s \ t` is dominated by every element in `t \ s`, and the
extra target terms are nonnegative, then the sum over `s` is at most the sum
over `t`.
-/
theorem finset_sum_le_sum_of_card_le_pairwise_sdiff
    {α : Type*} [DecidableEq α]
    (s t : Finset α) (f : α → ℝ)
    (hcard : s.card ≤ t.card)
    (hpair : ∀ a ∈ s \ t, ∀ b ∈ t \ s, f a ≤ f b)
    (htdiff_nonneg : ∀ b ∈ t \ s, 0 ≤ f b) :
    (∑ a ∈ s, f a) ≤ ∑ b ∈ t, f b := by
  classical
  let sdiff : Finset α := s \ t
  let tdiff : Finset α := t \ s
  have hdiff_card : sdiff.card ≤ tdiff.card := by
    dsimp [sdiff, tdiff]
    exact Finset.card_sdiff_le_card_sdiff_iff.mpr hcard
  have hdiff_sum :
      (∑ a ∈ sdiff, f a) ≤ ∑ b ∈ tdiff, f b := by
    obtain ⟨e, he_range⟩ :=
      Function.Embedding.exists_of_card_le_finset
        (α := {a // a ∈ sdiff}) (s := tdiff) (by
          simpa [Fintype.card_coe] using hdiff_card)
    let e' : {a // a ∈ sdiff} ↪ {b // b ∈ tdiff} := {
      toFun := fun a => ⟨e a, he_range ⟨a, rfl⟩⟩
      inj' := by
        intro a b hab
        exact e.injective (congrArg Subtype.val hab) }
    have hsub :
        (∑ a : {a // a ∈ sdiff}, f a.1) ≤
          ∑ b : {b // b ∈ tdiff}, f b.1 :=
      finset_sum_le_sum_of_injOn_nonneg
        (Finset.univ : Finset {a // a ∈ sdiff})
        (Finset.univ : Finset {b // b ∈ tdiff})
        (fun a : {a // a ∈ sdiff} => e' a)
        (fun a : {a // a ∈ sdiff} => f a.1)
        (fun b : {b // b ∈ tdiff} => f b.1)
        (by intro a _; simp)
        (by intro a _ b _ hab; exact e'.injective hab)
        (by
          intro a _
          exact hpair a.1 (by simpa [sdiff] using a.2) (e' a).1
            (by simpa [tdiff] using (e' a).2))
        (by
          intro b _
          exact htdiff_nonneg b.1 (by simpa [tdiff] using b.2))
    have hleft :
        (∑ a : {a // a ∈ sdiff}, f a.1) = ∑ a ∈ sdiff, f a := by
      exact (Finset.sum_subtype
        (s := sdiff) (p := fun a => a ∈ sdiff)
        (h := by intro a; rfl) (f := f)).symm
    have hright :
        (∑ b : {b // b ∈ tdiff}, f b.1) = ∑ b ∈ tdiff, f b := by
      exact (Finset.sum_subtype
        (s := tdiff) (p := fun b => b ∈ tdiff)
        (h := by intro b; rfl) (f := f)).symm
    linarith
  have hs_decomp :
      (∑ a ∈ s, f a) =
        (∑ a ∈ sdiff, f a) + ∑ a ∈ s ∩ t, f a := by
    change s.sum f = sdiff.sum f + (s ∩ t).sum f
    calc
      s.sum f = ((s \ t) ∪ (s ∩ t)).sum f := by
        rw [Finset.sdiff_union_inter s t]
      _ = (s \ t).sum f + (s ∩ t).sum f :=
        Finset.sum_union
          (s₁ := s \ t) (s₂ := s ∩ t) (f := f)
          (Finset.disjoint_sdiff_inter s t)
      _ = sdiff.sum f + (s ∩ t).sum f := by
        rfl
  have ht_decomp :
      (∑ b ∈ t, f b) =
        (∑ b ∈ tdiff, f b) + ∑ b ∈ s ∩ t, f b := by
    change t.sum f = tdiff.sum f + (s ∩ t).sum f
    calc
      t.sum f = ((t \ s) ∪ (t ∩ s)).sum f := by
        rw [Finset.sdiff_union_inter t s]
      _ = (t \ s).sum f + (t ∩ s).sum f :=
        Finset.sum_union
          (s₁ := t \ s) (s₂ := t ∩ s) (f := f)
          (Finset.disjoint_sdiff_inter t s)
      _ = tdiff.sum f + (s ∩ t).sum f := by
        rw [Finset.inter_comm t s]
  calc
    (∑ a ∈ s, f a)
        = (∑ a ∈ sdiff, f a) + ∑ a ∈ s ∩ t, f a := hs_decomp
    _ ≤ (∑ b ∈ tdiff, f b) + ∑ a ∈ s ∩ t, f a :=
          add_le_add hdiff_sum le_rfl
    _ = ∑ b ∈ t, f b := ht_decomp.symm

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
Telescoping identity used in the digital-goods revenue theorem rearrangement.
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
bound used in the digital-goods revenue theorem.
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
If each ranked bidder's expected payment is bounded by the truthful-gain
upper bound, then total revenue is bounded by the telescoping weighted sum of
ranked fixed-price revenues.

This is the algebraic heart of the digital-goods revenue theorem before applying
the win-probability monotonicity lemma and
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
the digital-goods revenue theorem algebra from the adjacent truthful-gain recursion all the way
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
Digital-goods revenue algebra in `p_i`, `c_i`, `g_i` notation. The truthfulness
comparison for adjacent bids is supplied as `p_i * (b_{i+1} - c_i) <= g_{i+1}`.
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
Bounded adjacent-gain version of the digital-goods revenue theorem algebra. The recursion
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
Bounded version of the digital-goods `p_i`, `c_i`, `g_i` revenue algebra. The
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
