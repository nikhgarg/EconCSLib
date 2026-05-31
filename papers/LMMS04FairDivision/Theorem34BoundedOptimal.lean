import Mathlib.Tactic

/-!
# LMMS Claim 3.4: bounded optimal allocations, certificate layer

Claim 3.4 says that, when all goods are smaller than the average load `L`,
there is an optimal identical-utilities allocation whose every bundle load lies
between `L / 2` and `2 * L`.  The source proof repeatedly reallocates goods
without increasing the max-load/min-load ratio.  This file formalizes the
source-shaped deterministic pieces of that argument:

* common additive bundle loads;
* the max-over-min load ratio used by the scheduling interpretation;
* a local load-transfer lemma showing that a reallocation stays inside old
  extrema when the donor does not fall below the old minimum and the receiver
  does not rise above the old maximum;
* the ratio monotonicity and optimality-preservation certificate used by
  Claim 3.4.

It deliberately does not claim termination of the paper's iterative
reallocation process.
-/

open scoped BigOperators

namespace LMMS04FairDivision
namespace Theorem34

noncomputable section

/-- Identical-utilities bundle load: the common value of the goods in a bundle. -/
def commonLoad {Item : Type*} (v : Item → ℝ) (S : Finset Item) : ℝ :=
  S.sum v

/-- Envy-ratio in the identical-processor view: maximum load over minimum load. -/
def loadRatio (minLoad maxLoad : ℝ) : ℝ :=
  maxLoad / minLoad

/-- The Claim 3.4 load window, `L / 2 < load < 2L`. -/
def boundedAroundAverage (L load : ℝ) : Prop :=
  L / 2 < load ∧ load < 2 * L

/-- An allocation is optimal for a ratio objective when no allocation has smaller ratio. -/
def IsOptimalRatio {Alloc : Type*} (ratioOf : Alloc → ℝ) (A : Alloc) : Prop :=
  ∀ B, ratioOf A ≤ ratioOf B

/--
Paper-shaped Claim 3.4 certificate: an allocation is optimal for the ratio
objective and every player load lies in the source window.
-/
def Claim34Certificate {Agent Item Alloc : Type*}
    (v : Item → ℝ) (L : ℝ) (ratioOf : Alloc → ℝ)
    (bundleOf : Alloc → Agent → Finset Item) (A : Alloc) : Prop :=
  IsOptimalRatio ratioOf A ∧
    ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf A i))

/--
If an optimal allocation is reallocated without increasing the ratio, the new
allocation remains optimal.  This is the optimality step used in the proof of
Claim 3.4 after each source reallocation.
-/
theorem optimal_ratio_of_nonincreasing_reallocation
    {Alloc : Type*} {ratioOf : Alloc → ℝ} {A B : Alloc}
    (hA : IsOptimalRatio ratioOf A)
    (hBA : ratioOf B ≤ ratioOf A) :
    IsOptimalRatio ratioOf B := by
  intro C
  exact le_trans hBA (hA C)

/--
Source-shaped bounded-optimal certificate: once a ratio-nonincreasing
reallocation has produced the Claim 3.4 load window, the resulting allocation
is a bounded optimal allocation.
-/
theorem claim34_certificate_of_nonincreasing_bounded_reallocation
    {Agent Item Alloc : Type*} {v : Item → ℝ} {L : ℝ}
    {ratioOf : Alloc → ℝ} {bundleOf : Alloc → Agent → Finset Item}
    {A B : Alloc}
    (hA : IsOptimalRatio ratioOf A)
    (hBA : ratioOf B ≤ ratioOf A)
    (hbounded :
      ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf B i))) :
    Claim34Certificate v L ratioOf bundleOf B := by
  exact ⟨optimal_ratio_of_nonincreasing_reallocation hA hBA, hbounded⟩

/--
Finite-descent assembly for the iterative proof of Claim 3.4.  If every
optimal allocation that has not yet reached the paper's load window admits a
ratio-nonincreasing reallocation that strictly decreases a natural-number
potential, then some optimal allocation satisfies the Claim 3.4 window.
-/
theorem claim34_certificate_of_finite_descent
    {Agent Item Alloc : Type*} {v : Item → ℝ} {L : ℝ}
    {ratioOf : Alloc → ℝ} {bundleOf : Alloc → Agent → Finset Item}
    (potential : Alloc → ℕ) (A₀ : Alloc)
    (hA₀ : IsOptimalRatio ratioOf A₀)
    (hstep :
      ∀ A : Alloc,
        IsOptimalRatio ratioOf A →
          (¬ ∀ i : Agent,
            boundedAroundAverage L (commonLoad v (bundleOf A i))) →
            ∃ B : Alloc, ratioOf B ≤ ratioOf A ∧ potential B < potential A) :
    ∃ B : Alloc, Claim34Certificate v L ratioOf bundleOf B := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ A : Alloc,
      potential A = n →
        IsOptimalRatio ratioOf A →
          ∃ B : Alloc, Claim34Certificate v L ratioOf bundleOf B
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A hpot hA
      by_cases hbounded :
          ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf A i))
      · exact ⟨A, ⟨hA, hbounded⟩⟩
      · rcases hstep A hA hbounded with ⟨B, hBA, hpot_lt⟩
        have hBopt : IsOptimalRatio ratioOf B :=
          optimal_ratio_of_nonincreasing_reallocation hA hBA
        exact ih (potential B) (by omega) B rfl hBopt
  exact hP (potential A₀) A₀ rfl hA₀

/--
Lexicographic finite-descent assembly for Claim 3.4.  If every not-yet-bounded
optimal allocation has a ratio-nonincreasing move that either decreases a
primary natural-number potential, or preserves the primary potential while
decreasing a uniformly bounded secondary potential, then a bounded optimal
allocation exists.
-/
theorem claim34_certificate_of_lexicographic_finite_descent
    {Agent Item Alloc : Type*} {v : Item → ℝ} {L : ℝ}
    {ratioOf : Alloc → ℝ} {bundleOf : Alloc → Agent → Finset Item}
    (primary secondary : Alloc → ℕ) (secondaryBound : ℕ)
    (A₀ : Alloc) (hA₀ : IsOptimalRatio ratioOf A₀)
    (hsecondary_bound : ∀ A : Alloc, secondary A ≤ secondaryBound)
    (hstep :
      ∀ A : Alloc,
        IsOptimalRatio ratioOf A →
          (¬ ∀ i : Agent,
            boundedAroundAverage L (commonLoad v (bundleOf A i))) →
            ∃ B : Alloc,
              ratioOf B ≤ ratioOf A ∧
                (primary B < primary A ∨
                  (primary B = primary A ∧ secondary B < secondary A))) :
    ∃ B : Alloc, Claim34Certificate v L ratioOf bundleOf B := by
  refine
    claim34_certificate_of_finite_descent
      (v := v) (L := L) (ratioOf := ratioOf) (bundleOf := bundleOf)
      (fun A : Alloc => primary A * (secondaryBound + 1) + secondary A)
      A₀ hA₀ ?_
  intro A hA hnot_bounded
  rcases hstep A hA hnot_bounded with
    ⟨B, hBA, hprimary_or_secondary⟩
  refine ⟨B, hBA, ?_⟩
  rcases hprimary_or_secondary with hprimary_lt | ⟨hprimary_eq, hsecondary_lt⟩
  · have hprimary_succ_le : primary B + 1 ≤ primary A :=
      Nat.succ_le_of_lt hprimary_lt
    have hnext_block :
        (primary B + 1) * (secondaryBound + 1) =
          primary B * (secondaryBound + 1) + (secondaryBound + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
    have hleft_lt_next :
        primary B * (secondaryBound + 1) + secondary B <
          (primary B + 1) * (secondaryBound + 1) := by
      rw [hnext_block]
      have hsec_le := hsecondary_bound B
      omega
    have hnext_le_primary :
        (primary B + 1) * (secondaryBound + 1) ≤
          primary A * (secondaryBound + 1) :=
      Nat.mul_le_mul_right (secondaryBound + 1) hprimary_succ_le
    exact
      lt_of_lt_of_le hleft_lt_next
        (le_trans hnext_le_primary (Nat.le_add_right _ _))
  · dsimp
    rw [hprimary_eq]
    exact Nat.add_lt_add_left hsecondary_lt _

/--
Domain-restricted lexicographic finite descent for Claim 3.4.  This is the
source-domain version of `claim34_certificate_of_lexicographic_finite_descent`:
optimality is only required among feasible allocations, and each descent step
must stay inside that feasible domain.
-/
theorem claim34_bounded_optimal_on_of_lexicographic_finite_descent
    {Agent Item Alloc : Type*} {v : Item → ℝ} {L : ℝ}
    {ratioOf : Alloc → ℝ} {bundleOf : Alloc → Agent → Finset Item}
    (feasible : Alloc → Prop)
    (primary secondary : Alloc → ℕ) (secondaryBound : ℕ)
    (A₀ : Alloc)
    (hA₀_feasible : feasible A₀)
    (hA₀_opt : ∀ C : Alloc, feasible C → ratioOf A₀ ≤ ratioOf C)
    (hsecondary_bound : ∀ A : Alloc, feasible A → secondary A ≤ secondaryBound)
    (hstep :
      ∀ A : Alloc,
        feasible A →
          (∀ C : Alloc, feasible C → ratioOf A ≤ ratioOf C) →
            (¬ ∀ i : Agent,
              boundedAroundAverage L (commonLoad v (bundleOf A i))) →
              ∃ B : Alloc,
                feasible B ∧
                  ratioOf B ≤ ratioOf A ∧
                    (primary B < primary A ∨
                      (primary B = primary A ∧ secondary B < secondary A))) :
    ∃ B : Alloc,
      feasible B ∧
        (∀ C : Alloc, feasible C → ratioOf B ≤ ratioOf C) ∧
          ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf B i)) := by
  classical
  let potential : Alloc → ℕ :=
    fun A => primary A * (secondaryBound + 1) + secondary A
  have hpotential_decreases :
      ∀ {A B : Alloc},
        feasible B →
          (primary B < primary A ∨
            (primary B = primary A ∧ secondary B < secondary A)) →
          potential B < potential A := by
    intro A B hBfeasible hprimary_or_secondary
    rcases hprimary_or_secondary with hprimary_lt | ⟨hprimary_eq, hsecondary_lt⟩
    · have hprimary_succ_le : primary B + 1 ≤ primary A :=
        Nat.succ_le_of_lt hprimary_lt
      have hnext_block :
          (primary B + 1) * (secondaryBound + 1) =
            primary B * (secondaryBound + 1) + (secondaryBound + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      have hleft_lt_next :
          primary B * (secondaryBound + 1) + secondary B <
            (primary B + 1) * (secondaryBound + 1) := by
        rw [hnext_block]
        have hsec_le := hsecondary_bound B hBfeasible
        omega
      have hnext_le_primary :
          (primary B + 1) * (secondaryBound + 1) ≤
            primary A * (secondaryBound + 1) :=
        Nat.mul_le_mul_right (secondaryBound + 1) hprimary_succ_le
      exact
        lt_of_lt_of_le hleft_lt_next
          (le_trans hnext_le_primary (Nat.le_add_right _ _))
    · dsimp [potential]
      rw [hprimary_eq]
      exact Nat.add_lt_add_left hsecondary_lt _
  let P : ℕ → Prop := fun n =>
    ∀ A : Alloc,
      potential A = n →
        feasible A →
          (∀ C : Alloc, feasible C → ratioOf A ≤ ratioOf C) →
            ∃ B : Alloc,
              feasible B ∧
                (∀ C : Alloc, feasible C → ratioOf B ≤ ratioOf C) ∧
                  ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf B i))
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A hpot hAfeasible hAopt
      by_cases hbounded :
          ∀ i : Agent, boundedAroundAverage L (commonLoad v (bundleOf A i))
      · exact ⟨A, hAfeasible, hAopt, hbounded⟩
      · rcases hstep A hAfeasible hAopt hbounded with
          ⟨B, hBfeasible, hBA, hprimary_or_secondary⟩
        have hBopt : ∀ C : Alloc, feasible C → ratioOf B ≤ ratioOf C := by
          intro C hC
          exact le_trans hBA (hAopt C hC)
        have hpot_lt : potential B < potential A :=
          hpotential_decreases hBfeasible hprimary_or_secondary
        exact ih (potential B) (by omega) B rfl hBfeasible hBopt
  exact hP (potential A₀) A₀ rfl hA₀_feasible hA₀_opt

/--
The load vector after moving an item of value `x` from `from` to `to`.
This is the arithmetic shadow of moving a good between bundles.
-/
def moveLoad {Agent : Type*} [DecidableEq Agent]
    (load : Agent → ℝ) (source target : Agent) (x : ℝ) : Agent → ℝ :=
  fun i =>
    if i = source then load i - x
    else if i = target then load i + x
    else load i

/--
If all old loads lie between `oldMin` and `oldMax`, a nonnegative moved good
keeps all new loads inside the same extrema provided the donor remains at least
`oldMin` and the receiver remains at most `oldMax`.
-/
theorem moveLoad_within_old_extrema
    {Agent : Type*} [DecidableEq Agent]
    {load : Agent → ℝ} {source target : Agent} {x oldMin oldMax : ℝ}
    (hwithin : ∀ i : Agent, oldMin ≤ load i ∧ load i ≤ oldMax)
    (hx_nonneg : 0 ≤ x)
    (hsource : oldMin ≤ load source - x)
    (htarget : load target + x ≤ oldMax) :
    ∀ i : Agent, oldMin ≤ moveLoad load source target x i ∧
      moveLoad load source target x i ≤ oldMax := by
  intro i
  by_cases hisource : i = source
  · subst i
    have hle : load source ≤ oldMax := (hwithin source).2
    constructor
    · simpa [moveLoad] using hsource
    · simp [moveLoad]
      nlinarith
  · by_cases hito : i = target
    · subst i
      have hlo : oldMin ≤ load target := (hwithin target).1
      constructor
      · simp [moveLoad, hisource]
        nlinarith
      · simpa [moveLoad, hisource] using htarget
    · simpa [moveLoad, hisource, hito] using hwithin i

/--
If the minimum load weakly increases and the maximum load weakly decreases,
then the max-over-min load ratio does not increase.
-/
theorem loadRatio_le_of_min_increases_max_decreases
    {oldMin oldMax newMin newMax : ℝ}
    (holdMin_pos : 0 < oldMin)
    (holdMax_nonneg : 0 ≤ oldMax)
    (hmin : oldMin ≤ newMin)
    (hmax : newMax ≤ oldMax) :
    loadRatio newMin newMax ≤ loadRatio oldMin oldMax := by
  have hnewMin_pos : 0 < newMin := lt_of_lt_of_le holdMin_pos hmin
  calc
    loadRatio newMin newMax = newMax / newMin := rfl
    _ ≤ oldMax / newMin :=
      div_le_div_of_nonneg_right hmax (le_of_lt hnewMin_pos)
    _ ≤ oldMax / oldMin := by
      rw [div_le_div_iff₀ hnewMin_pos holdMin_pos]
      nlinarith
    _ = loadRatio oldMin oldMax := rfl

/--
The one-step reallocation certificate for Claim 3.4: if a moved good leaves all
new loads between the old minimum and maximum, and the new minimum/maximum are
valid extrema of the moved load vector, then the source envy-ratio cannot
increase.
-/
theorem loadRatio_nonincreasing_of_moveLoad_certificate
    {Agent : Type*} [DecidableEq Agent]
    {load : Agent → ℝ} {source target : Agent}
    {x oldMin oldMax newMin newMax : ℝ}
    (holdMin_pos : 0 < oldMin)
    (holdMax_nonneg : 0 ≤ oldMax)
    (hwithin : ∀ i : Agent, oldMin ≤ load i ∧ load i ≤ oldMax)
    (hx_nonneg : 0 ≤ x)
    (hsource : oldMin ≤ load source - x)
    (htarget : load target + x ≤ oldMax)
    (hnewMin_lower :
      ∀ i : Agent, newMin ≤ moveLoad load source target x i)
    (hnewMin_attains :
      ∃ i : Agent, moveLoad load source target x i = newMin)
    (hnewMax_upper :
      ∀ i : Agent, moveLoad load source target x i ≤ newMax)
    (hnewMax_attains :
      ∃ i : Agent, moveLoad load source target x i = newMax) :
    loadRatio newMin newMax ≤ loadRatio oldMin oldMax := by
  have hinside :=
    moveLoad_within_old_extrema hwithin hx_nonneg hsource htarget
  obtain ⟨imin, himin⟩ := hnewMin_attains
  obtain ⟨imax, himax⟩ := hnewMax_attains
  have hmin : oldMin ≤ newMin := by
    simpa [himin] using (hinside imin).1
  have hmax : newMax ≤ oldMax := by
    simpa [himax] using (hinside imax).2
  exact
    loadRatio_le_of_min_increases_max_decreases
      holdMin_pos holdMax_nonneg hmin hmax

/-- Removing a good from a common-value bundle subtracts its value from load. -/
theorem commonLoad_erase
    {Item : Type*} [DecidableEq Item] {v : Item → ℝ}
    {S : Finset Item} {g : Item} (hg : g ∈ S) :
    commonLoad v (S.erase g) = commonLoad v S - v g := by
  unfold commonLoad
  rw [← Finset.sum_erase_add _ _ hg]
  ring

/-- Adding a fresh good to a common-value bundle adds its value to load. -/
theorem commonLoad_insert
    {Item : Type*} [DecidableEq Item] {v : Item → ℝ}
    {S : Finset Item} {g : Item} (hg : g ∉ S) :
    commonLoad v (insert g S) = commonLoad v S + v g := by
  unfold commonLoad
  rw [Finset.sum_insert hg]
  ring

end

end Theorem34
end LMMS04FairDivision
