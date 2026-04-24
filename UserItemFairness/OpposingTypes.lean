import UserItemFairness.Symmetrization

namespace UserItemFairness

/-!
Scalar algebra for the two-opposing-type models used in Theorems 3 and 4.

The paper writes this quantity as
`q_j(α) = α v_j / (α v_j + (1 - α) v_{n-j+1})`.
-/
namespace OpposingTypes

/-- The normalized contribution share of the first type for one item pair. -/
noncomputable def typeOneShare (alpha left right : ℝ) : ℝ :=
  alpha * left / (alpha * left + (1 - alpha) * right)

/-- The denominator in `q_j(α)` is positive for interior `α` and positive utilities. -/
theorem typeOneShare_denom_pos
    {alpha left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right) :
    0 < alpha * left + (1 - alpha) * right := by
  exact add_pos (mul_pos halpha0 hleft)
    (mul_pos (sub_pos.mpr halpha1) hright)

/--
Appendix D, Lemma 9, scalar alpha-monotonicity component:
`q_j(α)` strictly increases as `α` increases.
-/
theorem typeOneShare_strictMono_alpha
    {alpha alpha' left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (hlt : alpha < alpha')
    (hleft : 0 < left) (hright : 0 < right) :
    typeOneShare alpha left right <
      typeOneShare alpha' left right := by
  unfold typeOneShare
  have hden :=
    typeOneShare_denom_pos halpha0 halpha1 hleft hright
  have hden' :=
    typeOneShare_denom_pos halpha0' halpha1' hleft hright
  rw [div_lt_div_iff₀ hden hden']
  ring_nf
  have hprod : 0 < left * right := mul_pos hleft hright
  nlinarith [hprod, hlt]

/--
Appendix E, Lemma 16, scalar midpoint component: at `α = 1/2`, the share is
above `1/2` when the left utility exceeds the right utility.
-/
theorem half_lt_typeOneShare_half_of_right_lt_left
    {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) (hlt : right < left) :
    (1 / 2 : ℝ) < typeOneShare (1 / 2) left right := by
  unfold typeOneShare
  have hden : 0 < (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * right := by
    norm_num
    nlinarith [hleft, hright]
  rw [lt_div_iff₀ hden]
  nlinarith

/--
Appendix E, Lemma 16, scalar midpoint component: at `α = 1/2`, the share is
below `1/2` when the left utility is below the right utility.
-/
theorem typeOneShare_half_lt_half_of_left_lt_right
    {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) (hlt : left < right) :
    typeOneShare (1 / 2) left right < (1 / 2 : ℝ) := by
  unfold typeOneShare
  have hden : 0 < (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * right := by
    norm_num
    nlinarith [hleft, hright]
  rw [div_lt_iff₀ hden]
  nlinarith

/--
Appendix E, Lemma 16, scalar midpoint component: at `α = 1/2`, equal opposing
utilities give share exactly `1/2`.
-/
theorem typeOneShare_half_eq_half_of_eq
    {left right : ℝ}
    (hleft : 0 < left) (heq : left = right) :
    typeOneShare (1 / 2) left right = (1 / 2 : ℝ) := by
  subst right
  unfold typeOneShare
  have hden : (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * left ≠ 0 := by
    norm_num
    exact ne_of_gt hleft
  field_simp [hden]
  ring

/-- The opposite item index `n - j + 1` in zero-based `Fin n` notation. -/
def reverseItem {n : ℕ} (j : Item n) : Item n :=
  ⟨n - 1 - j.val, by omega⟩

/-- The indexed `q_j(α)` used in the opposing-preference proofs. -/
noncomputable def pairShare {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) : ℝ :=
  typeOneShare alpha (v j) (v (reverseItem j))

/--
Appendix D, Lemma 9, indexed alpha-monotonicity component:
for each item `j`, `q_j(α)` strictly increases with `α`.
-/
theorem pairShare_strictMono_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (hlt : alpha < alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j < pairShare alpha' v j := by
  exact typeOneShare_strictMono_alpha
    halpha0 halpha1 halpha0' halpha1' hlt (hpos j) (hpos (reverseItem j))

/--
Appendix E, Lemma 16, indexed midpoint component: if item `j` has higher value
than its opposite item, then `q_j(1/2) > 1/2`.
-/
theorem half_lt_pairShare_half_of_reverse_lt
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hlt : v (reverseItem j) < v j) :
    (1 / 2 : ℝ) < pairShare (1 / 2) v j := by
  exact half_lt_typeOneShare_half_of_right_lt_left
    (hpos j) (hpos (reverseItem j)) hlt

/--
Appendix E, Lemma 16, indexed midpoint component: if item `j` has lower value
than its opposite item, then `q_j(1/2) < 1/2`.
-/
theorem pairShare_half_lt_half_of_lt_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hlt : v j < v (reverseItem j)) :
    pairShare (1 / 2) v j < (1 / 2 : ℝ) := by
  exact typeOneShare_half_lt_half_of_left_lt_right
    (hpos j) (hpos (reverseItem j)) hlt

/--
Appendix E, Lemma 16, indexed midpoint component: equal opposite item values
give `q_j(1/2) = 1/2`.
-/
theorem pairShare_half_eq_half_of_eq_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (heq : v j = v (reverseItem j)) :
    pairShare (1 / 2) v j = (1 / 2 : ℝ) := by
  exact typeOneShare_half_eq_half_of_eq (hpos j) heq

end OpposingTypes
end UserItemFairness
