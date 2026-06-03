import EconCSLib.SocialChoice.Ranking.Basic

/-!
# KR21 Ranking Compatibility Layer

KR21 originally introduced finite ranking primitives in this file. The
paper-independent definitions now live in
`EconCSLib.SocialChoice.Ranking.Basic`; this file preserves the existing
KR21 names for downstream paper proofs.
-/

namespace KR21Monoculture

abbrev Candidate (n : ℕ) := EconCSLib.SocialChoice.Ranking.Candidate n

abbrev Ranking (n : ℕ) := EconCSLib.SocialChoice.Ranking.Ranking n

def firstChoice {n : ℕ} (π : Ranking n) : Candidate n :=
  π 0

def secondChoice {n : ℕ} (π : Ranking n) : Candidate n :=
  π 1

def swapTopTwo {n : ℕ} (π : Ranking n) : Ranking n :=
  (Equiv.swap (0 : Candidate n) 1).trans π

def rankOf {n : ℕ} (π : Ranking n) (c : Candidate n) : Candidate n :=
  π.symm c

def bestRemainingAfter {n : ℕ} (π : Ranking n) (c : Candidate n) :
    Candidate n :=
  if firstChoice π = c then secondChoice π else firstChoice π

@[simp] theorem firstChoice_apply_zero {n : ℕ} (π : Ranking n) :
    firstChoice π = π 0 :=
  EconCSLib.SocialChoice.Ranking.firstChoice_apply_zero π

@[simp] theorem secondChoice_apply_one {n : ℕ} (π : Ranking n) :
    secondChoice π = π 1 :=
  EconCSLib.SocialChoice.Ranking.secondChoice_apply_one π

@[simp] theorem firstChoice_swapTopTwo {n : ℕ} (π : Ranking n) :
    firstChoice (swapTopTwo π) = secondChoice π :=
  EconCSLib.SocialChoice.Ranking.firstChoice_swapTopTwo π

@[simp] theorem secondChoice_swapTopTwo {n : ℕ} (π : Ranking n) :
    secondChoice (swapTopTwo π) = firstChoice π :=
  EconCSLib.SocialChoice.Ranking.secondChoice_swapTopTwo π

@[simp] theorem rankOf_firstChoice {n : ℕ} (π : Ranking n) :
    rankOf π (firstChoice π) = 0 :=
  EconCSLib.SocialChoice.Ranking.rankOf_firstChoice π

@[simp] theorem rankOf_secondChoice {n : ℕ} (π : Ranking n) :
    rankOf π (secondChoice π) = 1 :=
  EconCSLib.SocialChoice.Ranking.rankOf_secondChoice π

@[simp] theorem rankOf_swapTopTwo_firstChoice {n : ℕ} (π : Ranking n) :
    rankOf (swapTopTwo π) (firstChoice π) = 1 :=
  EconCSLib.SocialChoice.Ranking.rankOf_swapTopTwo_firstChoice π

@[simp] theorem rankOf_swapTopTwo_secondChoice {n : ℕ} (π : Ranking n) :
    rankOf (swapTopTwo π) (secondChoice π) = 0 :=
  EconCSLib.SocialChoice.Ranking.rankOf_swapTopTwo_secondChoice π

theorem rankOf_swapTopTwo_of_ne_first_second {n : ℕ} (π : Ranking n)
    {c : Candidate n}
    (hfirst : c ≠ firstChoice π) (hsecond : c ≠ secondChoice π) :
    rankOf (swapTopTwo π) c = rankOf π c :=
  EconCSLib.SocialChoice.Ranking.rankOf_swapTopTwo_of_ne_first_second
    π hfirst hsecond

theorem one_lt_rankOf_of_ne_first_second {n : ℕ} (π : Ranking n)
    {c : Candidate n}
    (hfirst : c ≠ firstChoice π) (hsecond : c ≠ secondChoice π) :
    (1 : Candidate n) < rankOf π c :=
  EconCSLib.SocialChoice.Ranking.one_lt_rankOf_of_ne_first_second
    π hfirst hsecond

@[simp] theorem firstChoice_ne_secondChoice {n : ℕ} (π : Ranking n) :
    firstChoice π ≠ secondChoice π :=
  EconCSLib.SocialChoice.Ranking.firstChoice_ne_secondChoice π

theorem swapTopTwo_firstChoice_ne {n : ℕ} (π : Ranking n) :
    firstChoice (swapTopTwo π) ≠ firstChoice π :=
  EconCSLib.SocialChoice.Ranking.swapTopTwo_firstChoice_ne π

@[simp] theorem bestRemainingAfter_of_eq {n : ℕ} (π : Ranking n) :
    bestRemainingAfter π (firstChoice π) = secondChoice π :=
  EconCSLib.SocialChoice.Ranking.bestRemainingAfter_of_eq π

@[simp] theorem bestRemainingAfter_apply_zero {n : ℕ} (π : Ranking n) :
    bestRemainingAfter π (π 0) = π 1 :=
  EconCSLib.SocialChoice.Ranking.bestRemainingAfter_apply_zero π

@[simp] theorem bestRemainingAfter_apply_eq_zero_right {n : ℕ} (π σ : Ranking n)
    (h : π 0 = σ 0) :
    bestRemainingAfter π (σ 0) = π 1 :=
  EconCSLib.SocialChoice.Ranking.bestRemainingAfter_apply_eq_zero_right π σ h

@[simp] theorem bestRemainingAfter_of_ne {n : ℕ} (π : Ranking n) {c : Candidate n}
    (h : firstChoice π ≠ c) :
    bestRemainingAfter π c = firstChoice π :=
  EconCSLib.SocialChoice.Ranking.bestRemainingAfter_of_ne π h

/-- After candidate `c` is removed, the best remaining candidate is not `c`. -/
theorem bestRemainingAfter_ne_removed {n : ℕ} (π : Ranking n) (c : Candidate n) :
    bestRemainingAfter π c ≠ c :=
  EconCSLib.SocialChoice.Ranking.bestRemainingAfter_ne_removed π c

end KR21Monoculture
