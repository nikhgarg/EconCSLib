import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic

namespace Monoculture

/--
We model a candidate set as `Fin (n + 2)` so that the first and second positions
always exist without carrying a separate proof that there are at least two candidates.
-/
abbrev Candidate (n : ℕ) := Fin (n + 2)

/-- A ranking is a permutation of the candidate set. -/
abbrev Ranking (n : ℕ) := Equiv.Perm (Candidate n)

/-- The candidate placed first by a ranking. -/
def firstChoice {n : ℕ} (π : Ranking n) : Candidate n :=
  π 0

/-- The candidate placed second by a ranking. -/
def secondChoice {n : ℕ} (π : Ranking n) : Candidate n :=
  π 1

/-- The ranking obtained by swapping the first two positions of `π`. -/
def swapTopTwo {n : ℕ} (π : Ranking n) : Ranking n :=
  (Equiv.swap (0 : Candidate n) 1).trans π

/-- The position of candidate `c` in ranking `π`. Lower is better. -/
def rankOf {n : ℕ} (π : Ranking n) (c : Candidate n) : Candidate n :=
  π.symm c

/--
When exactly one candidate `c` has already been hired, the next hire under `π`
is the top candidate unless that top candidate is `c`, in which case it is the
runner-up. This is sufficient for the two-firm / one-hire-per-firm model.
-/
def bestRemainingAfter {n : ℕ} (π : Ranking n) (c : Candidate n) : Candidate n :=
  if firstChoice π = c then secondChoice π else firstChoice π

@[simp] theorem firstChoice_apply_zero {n : ℕ} (π : Ranking n) :
    firstChoice π = π 0 := rfl

@[simp] theorem secondChoice_apply_one {n : ℕ} (π : Ranking n) :
    secondChoice π = π 1 := rfl

@[simp] theorem firstChoice_swapTopTwo {n : ℕ} (π : Ranking n) :
    firstChoice (swapTopTwo π) = secondChoice π := by
  simp [swapTopTwo, firstChoice, secondChoice]

@[simp] theorem secondChoice_swapTopTwo {n : ℕ} (π : Ranking n) :
    secondChoice (swapTopTwo π) = firstChoice π := by
  simp [swapTopTwo, firstChoice, secondChoice]

@[simp] theorem rankOf_firstChoice {n : ℕ} (π : Ranking n) :
    rankOf π (firstChoice π) = 0 := by
  simp [rankOf, firstChoice]

@[simp] theorem rankOf_secondChoice {n : ℕ} (π : Ranking n) :
    rankOf π (secondChoice π) = 1 := by
  simp [rankOf, secondChoice]

@[simp] theorem firstChoice_ne_secondChoice {n : ℕ} (π : Ranking n) :
    firstChoice π ≠ secondChoice π := by
  intro h
  have : (0 : Candidate n) = 1 := by
    simpa [firstChoice, secondChoice] using congrArg π.symm h
  have h01 : (0 : Candidate n) ≠ 1 := by
    intro hfin
    have hval : (0 : ℕ) = 1 := by
      simpa using congrArg Fin.val hfin
    exact Nat.zero_ne_one hval
  exact h01 this

theorem swapTopTwo_firstChoice_ne {n : ℕ} (π : Ranking n) :
    firstChoice (swapTopTwo π) ≠ firstChoice π := by
  rw [firstChoice_swapTopTwo]
  exact (firstChoice_ne_secondChoice π).symm

@[simp] theorem bestRemainingAfter_of_eq {n : ℕ} (π : Ranking n) :
    bestRemainingAfter π (firstChoice π) = secondChoice π := by
  simp [bestRemainingAfter]

@[simp] theorem bestRemainingAfter_of_ne {n : ℕ} (π : Ranking n) {c : Candidate n}
    (h : firstChoice π ≠ c) :
    bestRemainingAfter π c = firstChoice π := by
  have h' : π 0 ≠ c := by
    simpa [firstChoice] using h
  simp [bestRemainingAfter, firstChoice, h']

end Monoculture
