import KR21Monoculture.WeakCompetition

namespace KR21Monoculture
namespace Model

/--
Expected payoff of a labeled firm using `self` against an opponent using `other`
when the order of play is uniformly random.  The factor `1 / 2` is irrelevant for
best-response comparisons, but it is the natural payoff normalization.
-/
noncomputable def payoffAgainst {n : ℕ} (M : Model n)
    (self other : Strategy) : ℝ :=
  (firstMoverEU M self + secondMoverEU M other self) / 2

/-- Removing the common factor `1 / 2` from payoff comparisons. -/
theorem payoffAgainst_gt_iff_sum_gt_sum {n : ℕ} (M : Model n)
    {s t other : Strategy} :
    payoffAgainst M s other > payoffAgainst M t other ↔
      firstMoverEU M s + secondMoverEU M other s >
        firstMoverEU M t + secondMoverEU M other t := by
  unfold payoffAgainst
  constructor <;> intro h <;> nlinarith

/-- The existing dominance definition is exactly strict best response in `payoffAgainst`. -/
theorem algorithmStrictlyDominant_iff_payoffAgainst {n : ℕ} (M : Model n) :
    AlgorithmStrictlyDominant M ↔
      payoffAgainst M Strategy.algorithm Strategy.algorithm >
          payoffAgainst M Strategy.human Strategy.algorithm ∧
        payoffAgainst M Strategy.algorithm Strategy.human >
          payoffAgainst M Strategy.human Strategy.human := by
  constructor
  · intro h
    constructor
    · exact (payoffAgainst_gt_iff_sum_gt_sum (M := M)
        (s := Strategy.algorithm) (t := Strategy.human)
        (other := Strategy.algorithm)).2 h.1
    · exact (payoffAgainst_gt_iff_sum_gt_sum (M := M)
        (s := Strategy.algorithm) (t := Strategy.human)
        (other := Strategy.human)).2 h.2
  · intro h
    constructor
    · exact (payoffAgainst_gt_iff_sum_gt_sum (M := M)
        (s := Strategy.algorithm) (t := Strategy.human)
        (other := Strategy.algorithm)).1 h.1
    · exact (payoffAgainst_gt_iff_sum_gt_sum (M := M)
        (s := Strategy.algorithm) (t := Strategy.human)
        (other := Strategy.human)).1 h.2

/--
The sum of the two labeled firms' random-order payoffs equals random-order social
welfare.  This is the model-level bridge between strategic incentives and welfare.
-/
theorem payoffAgainst_add_swap_eq_welfareRandomOrder {n : ℕ} (M : Model n)
    (s₁ s₂ : Strategy) :
    payoffAgainst M s₁ s₂ + payoffAgainst M s₂ s₁ =
      welfareRandomOrder M s₁ s₂ := by
  unfold payoffAgainst welfareRandomOrder
  rw [welfareOrdered_eq_firstMoverEU_add_secondMoverEU
        (M := M) (s₁ := s₁) (s₂ := s₂)]
  rw [welfareOrdered_eq_firstMoverEU_add_secondMoverEU
        (M := M) (s₁ := s₂) (s₂ := s₁)]
  ring

/-- At a symmetric profile, each firm receives half of social welfare. -/
theorem payoffAgainst_self_eq_half_welfareRandomOrder {n : ℕ} (M : Model n)
    (s : Strategy) :
    payoffAgainst M s s = welfareRandomOrder M s s / 2 := by
  have h := payoffAgainst_add_swap_eq_welfareRandomOrder (M := M) s s
  nlinarith

/-- The paradox definition can be read as dominance plus a symmetric-payoff reversal. -/
theorem hasKR21MonocultureParadox_iff_payoffAndWelfare {n : ℕ} (M : Model n) :
    HasKR21MonocultureParadox M ↔
      (payoffAgainst M Strategy.algorithm Strategy.algorithm >
          payoffAgainst M Strategy.human Strategy.algorithm ∧
        payoffAgainst M Strategy.algorithm Strategy.human >
          payoffAgainst M Strategy.human Strategy.human) ∧
      HumanProfileBeatsAlgorithmProfile M := by
  unfold HasKR21MonocultureParadox
  rw [algorithmStrictlyDominant_iff_payoffAgainst]

end Model
end KR21Monoculture
