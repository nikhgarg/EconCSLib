import Monoculture.FirstChoice

open scoped BigOperators

namespace Monoculture

/--
A pair of candidates is inverted by `π` relative to the reference ranking `ρ` when
`ρ` puts the first candidate above the second, but `π` puts the second above the
first.

This is the finite combinatorial core of the Mallows model: all Mallows weights
are powers of the number of such inversions.
-/
def invertedPair {n : ℕ} (ρ π : Ranking n) (ab : Candidate n × Candidate n) : Prop :=
  rankOf ρ ab.1 < rankOf ρ ab.2 ∧ rankOf π ab.2 < rankOf π ab.1

/-- The finite set of inversions of `π` relative to `ρ`. -/
noncomputable def inversionFinset {n : ℕ} (ρ π : Ranking n) :
    Finset (Candidate n × Candidate n) := by
  classical
  exact Finset.univ.filter (fun ab => invertedPair ρ π ab)

/-- Kendall-tau distance from `π` to the reference ranking `ρ`. -/
noncomputable def kendallTau {n : ℕ} (ρ π : Ranking n) : ℕ :=
  (inversionFinset ρ π).card

@[simp] theorem invertedPair_self_false {n : ℕ} (ρ : Ranking n)
    (ab : Candidate n × Candidate n) :
    ¬ invertedPair ρ ρ ab := by
  intro h
  exact (lt_asymm h.1) h.2

@[simp] theorem inversionFinset_self {n : ℕ} (ρ : Ranking n) :
    inversionFinset ρ ρ = ∅ := by
  classical
  ext ab
  simp [inversionFinset]

@[simp] theorem kendallTau_self {n : ℕ} (ρ : Ranking n) :
    kendallTau ρ ρ = 0 := by
  simp [kendallTau]

/-- The candidates occupying positions `i` and `j` in a ranking are distinct. -/
theorem apply_ne_apply_of_ne {n : ℕ} (π : Ranking n) {i j : Candidate n}
    (hij : i ≠ j) : π i ≠ π j := by
  intro h
  exact hij (π.injective h)

/-- The reference first candidate is ranked above the reference second candidate. -/
theorem rankOf_center_first_lt_second {n : ℕ} (ρ : Ranking n) :
    rankOf ρ (firstChoice ρ) < rankOf ρ (secondChoice ρ) := by
  simp [rankOf, firstChoice, secondChoice]

/-- A value vector is strictly decreasing down the reference ranking. -/
def StrictlyOrderedBy {n : ℕ} (ρ : Ranking n) (value : Candidate n → ℝ) : Prop :=
  ∀ {a b : Candidate n}, rankOf ρ a < rankOf ρ b → value b < value a

/-- A value vector is weakly decreasing down the reference ranking. -/
def WeaklyOrderedBy {n : ℕ} (ρ : Ranking n) (value : Candidate n → ℝ) : Prop :=
  ∀ {a b : Candidate n}, rankOf ρ a < rankOf ρ b → value b ≤ value a

/-- Strict reference-ordering gives a positive value gap at the reference ranking itself. -/
theorem center_valueGap_pos_of_strictlyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy ρ value) :
    0 < valueGap value ρ := by
  unfold valueGap
  exact sub_pos.mpr (hvalue (rankOf_center_first_lt_second ρ))

/-- Weak reference-ordering gives a nonnegative value gap at the reference ranking itself. -/
theorem center_valueGap_nonneg_of_weaklyOrderedBy {n : ℕ}
    {ρ : Ranking n} {value : Candidate n → ℝ}
    (hvalue : WeaklyOrderedBy ρ value) :
    0 ≤ valueGap value ρ := by
  unfold valueGap
  exact sub_nonneg.mpr (hvalue (rankOf_center_first_lt_second ρ))

end Monoculture
