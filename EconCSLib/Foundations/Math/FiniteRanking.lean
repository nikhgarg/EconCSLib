import Mathlib.Data.Finset.Sort
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

end FiniteRanking
end EconCSLib
