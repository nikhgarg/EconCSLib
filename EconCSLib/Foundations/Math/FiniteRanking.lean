import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic

/-!
# Finite Rankings

Reusable helpers for enumerating a finite set in nondecreasing score order.

## Main declarations

* `FiniteRanking.rankAgentByValue`: enumerate a finite set using the
  lexicographic key `(value, tie-breaker)`.
* `FiniteRanking.rankValueByValue_mono`: the resulting values are monotone in
  the rank index.
-/

open scoped BigOperators

namespace EconCSLib
namespace FiniteRanking

open Prod.Lex

variable {α : Type*} [LinearOrder α] [DecidableEq α]

/-- Lexicographic `(value, tie-breaker)` key used to rank a finite set. -/
def valueTieKey (value : α → ℝ) (a : α) : ℝ ×ₗ α :=
  toLex (value a, a)

theorem valueTieKey_injective (value : α → ℝ) :
    Function.Injective (valueTieKey value) := by
  intro a b h
  have hpair : (value a, a) = (value b, b) := by
    exact toLex_inj.mp h
  exact congrArg Prod.snd hpair

/--
The finite set of lexicographic value/tie-breaker keys associated with a
finite set of alternatives.
-/
noncomputable def valueTieKeySet (s : Finset α) (value : α → ℝ) :
    Finset (ℝ ×ₗ α) :=
  s.image (valueTieKey value)

theorem valueTieKeySet_card (s : Finset α) (value : α → ℝ) :
    (valueTieKeySet s value).card = s.card := by
  classical
  unfold valueTieKeySet
  exact Finset.card_image_of_injective s (valueTieKey_injective value)

/-- The increasing key enumeration of `s` by `(value, tie-breaker)`. -/
noncomputable def rankKeyByValue (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) : Fin k → ℝ ×ₗ α :=
  (valueTieKeySet s value).orderEmbOfFin
    ((valueTieKeySet_card s value).trans hcard)

/-- The agent/alternative at rank `i` in nondecreasing value order. -/
noncomputable def rankAgentByValue (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) : Fin k → α :=
  fun i => (ofLex (rankKeyByValue s value hcard i)).2

/-- The value at rank `i` in nondecreasing value order. -/
noncomputable def rankValueByValue (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) : Fin k → ℝ :=
  fun i => (ofLex (rankKeyByValue s value hcard i)).1

theorem rankKeyByValue_mem (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (i : Fin k) :
    rankKeyByValue s value hcard i ∈ valueTieKeySet s value := by
  classical
  exact Finset.orderEmbOfFin_mem _ _ i

theorem rankKeyByValue_eq_valueTieKey (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (i : Fin k) :
    rankKeyByValue s value hcard i =
      valueTieKey value (rankAgentByValue s value hcard i) := by
  classical
  have hmem := rankKeyByValue_mem s value hcard i
  rcases Finset.mem_image.mp hmem with ⟨a, _ha, hkey⟩
  have hpair :
      ofLex (rankKeyByValue s value hcard i) = (value a, a) := by
    exact (congrArg ofLex hkey).symm
  simpa [rankAgentByValue, hpair] using hkey.symm

theorem rankValueByValue_eq_value (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (i : Fin k) :
    rankValueByValue s value hcard i =
      value (rankAgentByValue s value hcard i) := by
  classical
  have hkey := rankKeyByValue_eq_valueTieKey s value hcard i
  have hpair :
      ofLex (rankKeyByValue s value hcard i) =
        (value (rankAgentByValue s value hcard i),
          rankAgentByValue s value hcard i) := by
    simpa [valueTieKey] using congrArg ofLex hkey
  simpa [rankValueByValue] using congrArg Prod.fst hpair

theorem rankAgentByValue_mem (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (i : Fin k) :
    rankAgentByValue s value hcard i ∈ s := by
  classical
  have hmem := rankKeyByValue_mem s value hcard i
  rcases Finset.mem_image.mp hmem with ⟨a, ha, hkey⟩
  have hpair :
      ofLex (rankKeyByValue s value hcard i) = (value a, a) := by
    exact (congrArg ofLex hkey).symm
  simpa [rankAgentByValue, hpair] using ha

theorem rankValueByValue_mono (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) :
    ∀ r i : Fin k, r.val < i.val →
      rankValueByValue s value hcard r ≤ rankValueByValue s value hcard i := by
  intro r i hri
  have hle_fin : r ≤ i := by
    exact_mod_cast Nat.le_of_lt hri
  have hkey_le :
      rankKeyByValue s value hcard r ≤ rankKeyByValue s value hcard i :=
    ((valueTieKeySet s value).orderEmbOfFin
      ((valueTieKeySet_card s value).trans hcard)).monotone hle_fin
  exact Prod.Lex.monotone_fst _ _ hkey_le

theorem rankAgentByValue_injective (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) :
    Function.Injective (rankAgentByValue s value hcard) := by
  intro i j hij
  have hkey_i := rankKeyByValue_eq_valueTieKey s value hcard i
  have hkey_j := rankKeyByValue_eq_valueTieKey s value hcard j
  have hkey :
      rankKeyByValue s value hcard i =
        rankKeyByValue s value hcard j := by
    rw [hkey_i, hkey_j, hij]
  exact
    ((valueTieKeySet s value).orderEmbOfFin
      ((valueTieKeySet_card s value).trans hcard)).injective hkey

theorem image_rankAgentByValue_univ (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) :
    Finset.image (rankAgentByValue s value hcard) Finset.univ = s := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨i, _hi, rfl⟩
    exact rankAgentByValue_mem s value hcard i
  · rw [Finset.card_image_of_injective _ (rankAgentByValue_injective s value hcard)]
    rw [Finset.card_univ, Fintype.card_fin, ← hcard]

/-- Sum a real-valued function over a finite set by its ranked enumeration. -/
theorem sum_rankAgentByValue_eq_sum (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (f : α → ℝ) :
    (∑ i : Fin k, f (rankAgentByValue s value hcard i)) =
      ∑ a ∈ s, f a := by
  classical
  calc
    (∑ i : Fin k, f (rankAgentByValue s value hcard i))
        = (∑ a ∈ Finset.image (rankAgentByValue s value hcard)
          (Finset.univ : Finset (Fin k)), f a) := by
          symm
          exact Finset.sum_image
            (s := (Finset.univ : Finset (Fin k)))
            (f := f)
            (g := rankAgentByValue s value hcard)
            (by
              intro i _hi j _hj hij
              exact rankAgentByValue_injective s value hcard hij)
    _ = ∑ a ∈ s, f a := by
          rw [image_rankAgentByValue_univ s value hcard]

theorem sum_rankValueByValue_eq_sum (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) :
    (∑ i : Fin k, rankValueByValue s value hcard i) =
      ∑ a ∈ s, value a := by
  classical
  calc
    (∑ i : Fin k, rankValueByValue s value hcard i)
        = ∑ i : Fin k, value (rankAgentByValue s value hcard i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact rankValueByValue_eq_value s value hcard i
    _ = (∑ a ∈ Finset.image (rankAgentByValue s value hcard)
          (Finset.univ : Finset (Fin k)), value a) := by
          symm
          exact Finset.sum_image
            (s := (Finset.univ : Finset (Fin k)))
            (f := value)
            (g := rankAgentByValue s value hcard)
            (by
              intro i _hi j _hj hij
              exact rankAgentByValue_injective s value hcard hij)
    _ = ∑ a ∈ s, value a := by
          rw [image_rankAgentByValue_univ s value hcard]

/-- Elements whose sorted rank index lies strictly below `cut`. -/
noncomputable def lowerRankFinset (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) : Finset α :=
  ((Finset.univ : Finset (Fin k)).filter fun i => i.val < cut).image
    (rankAgentByValue s value hcard)

/-- Elements whose sorted rank index lies weakly above `cut`. -/
noncomputable def upperRankFinset (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) : Finset α :=
  ((Finset.univ : Finset (Fin k)).filter fun i => cut ≤ i.val).image
    (rankAgentByValue s value hcard)

theorem lowerRankFinset_subset (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    lowerRankFinset s value hcard cut ⊆ s := by
  classical
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨i, _hi, rfl⟩
  exact rankAgentByValue_mem s value hcard i

theorem lowerRankFinset_mono (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) {cut₁ cut₂ : ℕ}
    (hcut : cut₁ ≤ cut₂) :
    lowerRankFinset s value hcard cut₁ ⊆
      lowerRankFinset s value hcard cut₂ := by
  classical
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
  refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ i,
      Nat.lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hcut⟩

theorem upperRankFinset_subset (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    upperRankFinset s value hcard cut ⊆ s := by
  classical
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨i, _hi, rfl⟩
  exact rankAgentByValue_mem s value hcard i

theorem lowerRankFinset_disjoint_upperRankFinset
    (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    ∀ a : α,
      a ∈ lowerRankFinset s value hcard cut →
      a ∈ upperRankFinset s value hcard cut → False := by
  classical
  intro a hlow hhigh
  rcases Finset.mem_image.mp hlow with ⟨lo, hlo, hloeq⟩
  rcases Finset.mem_image.mp hhigh with ⟨hi, hhi, hhieq⟩
  have hagent_eq :
      rankAgentByValue s value hcard lo =
        rankAgentByValue s value hcard hi := by
    rw [hloeq, hhieq]
  have hidx : lo = hi :=
    rankAgentByValue_injective s value hcard hagent_eq
  subst hi
  exact not_le_of_gt (Finset.mem_filter.mp hlo).2 (Finset.mem_filter.mp hhi).2

/-- The upper ranked block is the complement of the lower ranked block inside
the ranked finite universe. -/
theorem upperRankFinset_eq_sdiff_lowerRankFinset
    (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    upperRankFinset s value hcard cut =
      s \ lowerRankFinset s value hcard cut := by
  classical
  ext a
  constructor
  · intro haupper
    refine Finset.mem_sdiff.mpr
      ⟨upperRankFinset_subset s value hcard cut haupper, ?_⟩
    intro halower
    exact lowerRankFinset_disjoint_upperRankFinset
      s value hcard cut a halower haupper
  · intro ha
    have has : a ∈ s := (Finset.mem_sdiff.mp ha).1
    have hanotlower : a ∉ lowerRankFinset s value hcard cut :=
      (Finset.mem_sdiff.mp ha).2
    have himage :
        a ∈ Finset.image (rankAgentByValue s value hcard)
          (Finset.univ : Finset (Fin k)) := by
      rw [image_rankAgentByValue_univ s value hcard]
      exact has
    rcases Finset.mem_image.mp himage with ⟨i, _hi, hi_eq⟩
    refine Finset.mem_image.mpr ⟨i, ?_, hi_eq⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
    by_contra hnot
    have hi_lt : i.val < cut := Nat.lt_of_not_ge hnot
    exact hanotlower (Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi_lt⟩, hi_eq⟩)

theorem lowerRank_value_le_upperRank_value
    (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    ∀ high : α, high ∈ upperRankFinset s value hcard cut →
      ∀ low : α, low ∈ lowerRankFinset s value hcard cut →
        value low ≤ value high := by
  classical
  intro high hhigh low hlow
  rcases Finset.mem_image.mp hhigh with ⟨hi, hhi, rfl⟩
  rcases Finset.mem_image.mp hlow with ⟨lo, hlo, rfl⟩
  have hlo_lt_hi : lo.val < hi.val :=
    Nat.lt_of_lt_of_le (Finset.mem_filter.mp hlo).2
      (Finset.mem_filter.mp hhi).2
  have hmono :=
    rankValueByValue_mono s value hcard lo hi hlo_lt_hi
  rw [rankValueByValue_eq_value s value hcard lo] at hmono
  rw [rankValueByValue_eq_value s value hcard hi] at hmono
  exact hmono

theorem lowerRankFinset_card (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    (lowerRankFinset s value hcard cut).card = min k cut := by
  classical
  unfold lowerRankFinset
  rw [Finset.card_image_of_injective _
    (rankAgentByValue_injective s value hcard)]
  exact Fin.card_filter_val_lt (n := k) (m := cut)

theorem lowerRankFinset_card_add_upperRankFinset_card
    (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    (lowerRankFinset s value hcard cut).card +
      (upperRankFinset s value hcard cut).card = k := by
  classical
  unfold lowerRankFinset upperRankFinset
  rw [Finset.card_image_of_injective _
    (rankAgentByValue_injective s value hcard)]
  rw [Finset.card_image_of_injective _
    (rankAgentByValue_injective s value hcard)]
  have hfilter :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k)))
      (p := fun i : Fin k => i.val < cut)
  simpa [Nat.not_lt] using hfilter

theorem upperRankFinset_card (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) (cut : ℕ) :
    (upperRankFinset s value hcard cut).card = k - min k cut := by
  classical
  have hsum :=
    lowerRankFinset_card_add_upperRankFinset_card s value hcard cut
  have hlow := lowerRankFinset_card s value hcard cut
  calc
    (upperRankFinset s value hcard cut).card
        = min k cut + (upperRankFinset s value hcard cut).card -
            min k cut := by
          rw [Nat.add_sub_cancel_left]
    _ = k - min k cut := by
          rw [← hlow, hsum]

theorem lowerRankFinset_card_half (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) :
    (lowerRankFinset s value hcard (k / 2)).card = k / 2 := by
  rw [lowerRankFinset_card]
  exact min_eq_right (Nat.div_le_self k 2)

theorem upperRankFinset_card_half (s : Finset α) (value : α → ℝ)
    {k : ℕ} (hcard : s.card = k) :
    (upperRankFinset s value hcard (k / 2)).card = k - k / 2 := by
  rw [upperRankFinset_card]
  exact congrArg (fun x => k - x) (min_eq_right (Nat.div_le_self k 2))

end FiniteRanking
end EconCSLib
