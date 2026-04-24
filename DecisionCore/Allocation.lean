import DecisionCore.Policy

open scoped BigOperators

namespace DecisionCore

/--
A finite integer allocation over a finite class/type space `κ`.

This is the common representation behind the recommendation-diversity paper:
`count k` is the number of recommended items of type `k`.
-/
structure Allocation (κ : Type*) where
  count : κ → ℕ

namespace Allocation

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Total number of allocated units. -/
def total (a : Allocation κ) : ℕ :=
  ∑ k, a.count k

/-- The positive-support classes/types in an allocation. -/
def support (a : Allocation κ) : Finset κ :=
  Finset.univ.filter fun k => a.count k ≠ 0

/-- `a` is an allocation of exactly `N` units. -/
def HasTotal (a : Allocation κ) (N : ℕ) : Prop :=
  a.total = N

/-- `a` is an allocation of at most `N` units. -/
def BoundedBy (a : Allocation κ) (N : ℕ) : Prop :=
  a.total ≤ N

/-- Real-valued representation share of class/type `k` in allocation `a`. -/
noncomputable def share (a : Allocation κ) (k : κ) : ℝ :=
  if h : a.total = 0 then 0 else (a.count k : ℝ) / (a.total : ℝ)

/-- Weighted finite objective over allocation counts. -/
noncomputable def objective
    (a : Allocation κ) (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ) : ℝ :=
  ∑ k, weight k * valueOfCount k (a.count k)

/--
Move one unit from `src` to `dst`. If `src = dst`, the allocation is unchanged.
If the source count is zero, natural-number subtraction leaves it at zero; callers should
use `CanMoveOne` when they need an honest transfer.
-/
def moveOne (a : Allocation κ) (src dst : κ) : Allocation κ where
  count := fun k =>
    if src = dst then a.count k
    else if k = src then a.count k - 1
    else if k = dst then a.count k + 1
    else a.count k

/-- There is at least one unit available to move out of `src`. -/
def CanMoveOne (a : Allocation κ) (src : κ) : Prop :=
  0 < a.count src

/-- Marginal value of increasing a count from `q` to `q + 1`. -/
noncomputable def marginal (valueOfCount : κ → ℕ → ℝ) (k : κ) (q : ℕ) : ℝ :=
  valueOfCount k (q + 1) - valueOfCount k q

/-- Nonnegative marginal values for every class/type. -/
def HasNonnegativeMarginals (valueOfCount : κ → ℕ → ℝ) : Prop :=
  ∀ k q, 0 ≤ marginal valueOfCount k q

/-- Diminishing marginal returns for every class/type. -/
def HasDiminishingReturns (valueOfCount : κ → ℕ → ℝ) : Prop :=
  ∀ k q, marginal valueOfCount k (q + 1) ≤ marginal valueOfCount k q

@[simp] theorem total_mk (f : κ → ℕ) :
    total ({ count := f } : Allocation κ) = ∑ k, f k := rfl

@[simp] theorem mem_support (a : Allocation κ) (k : κ) :
    k ∈ support a ↔ a.count k ≠ 0 := by
  simp [support]

/-- Each class count is bounded by the total allocation size. -/
theorem count_le_total (a : Allocation κ) (k : κ) :
    a.count k ≤ a.total := by
  unfold total
  exact Finset.single_le_sum
    (by intro _ _; exact Nat.zero_le _)
    (Finset.mem_univ k)

@[simp] theorem share_of_total_zero (a : Allocation κ) (k : κ)
    (h : a.total = 0) :
    share a k = 0 := by
  simp [share, h]

theorem share_eq_div_of_total_ne_zero (a : Allocation κ) (k : κ)
    (h : a.total ≠ 0) :
    share a k = (a.count k : ℝ) / (a.total : ℝ) := by
  simp [share, h]

@[simp] theorem objective_mk (f : κ → ℕ) (weight : κ → ℝ)
    (valueOfCount : κ → ℕ → ℝ) :
    objective ({ count := f } : Allocation κ) weight valueOfCount =
      ∑ k, weight k * valueOfCount k (f k) := rfl

@[simp] theorem marginal_apply (valueOfCount : κ → ℕ → ℝ) (k : κ) (q : ℕ) :
    marginal valueOfCount k q = valueOfCount k (q + 1) - valueOfCount k q := rfl

end Allocation
end DecisionCore

namespace DecisionCore
namespace Allocation

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Representation shares are always nonnegative. -/
theorem share_nonneg (a : Allocation κ) (k : κ) :
    0 ≤ share a k := by
  by_cases h : a.total = 0
  · simp [share, h]
  · rw [share_eq_div_of_total_ne_zero (a := a) (k := k) h]
    exact div_nonneg (by positivity) (by positivity)

/-- If the total allocation is nonzero, representation shares sum to one. -/
theorem sum_share_eq_one_of_total_ne_zero (a : Allocation κ)
    (h : a.total ≠ 0) :
    ∑ k, share a k = 1 := by
  have hreal : (a.total : ℝ) ≠ 0 := by exact_mod_cast h
  have hsum : (∑ k, (a.count k : ℝ)) = (a.total : ℝ) := by
    simp [total]
  calc
    ∑ k, share a k = ∑ k, (a.count k : ℝ) / (a.total : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [share_eq_div_of_total_ne_zero (a := a) (k := k) h]
    _ = (∑ k, (a.count k : ℝ)) / (a.total : ℝ) := by
      rw [div_eq_mul_inv]
      simp_rw [div_eq_mul_inv]
      simpa using (Finset.sum_mul (s := (Finset.univ : Finset κ))
        (f := fun k => (a.count k : ℝ)) (a := (a.total : ℝ)⁻¹)).symm
    _ = (a.total : ℝ) / (a.total : ℝ) := by
      rw [hsum]
    _ = 1 := by
      field_simp [hreal]

/-- A positive count has positive representation share when the total is nonzero. -/
theorem share_pos_of_count_pos (a : Allocation κ) (k : κ)
    (hcount : 0 < a.count k) :
    0 < share a k := by
  have htotal : a.total ≠ 0 := by
    intro hzero
    have hsumzero : ∑ x, a.count x = 0 := by simpa [total] using hzero
    have hk_le : a.count k ≤ ∑ x, a.count x := by
      exact Finset.single_le_sum (by intro _ _; exact Nat.zero_le _) (Finset.mem_univ k)
    omega
  rw [share_eq_div_of_total_ne_zero (a := a) (k := k) htotal]
  exact div_pos (by exact_mod_cast hcount) (by positivity)

end Allocation
end DecisionCore
