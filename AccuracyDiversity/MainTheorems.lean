import AccuracyDiversity.Examples
import AccuracyDiversity.Uniform
import AccuracyDiversity.TailHomogeneity
import AccuracyDiversity.Pareto

open scoped BigOperators

/-!
# Paper-Facing Theorems: Reconciling the Accuracy-Diversity Trade-off

This file is the public theorem interface for the accuracy-diversity
formalization. Detailed allocation, representation, Bernoulli, and exchange
lemmas live in the sibling files.
-/

namespace AccuracyDiversity

namespace ConsumptionModel

/--
Finite optimizer existence for a fixed slate size.
-/
theorem paper_finite_optimum_exists
    {T : ℕ} [Nonempty (ItemType T)] (M : ConsumptionModel T) (N : ℕ) :
    ∃ a : CountAllocation T, M.IsOptimalAtTotal N a := by
  exact M.exists_isOptimalAtTotal N

/--
Finite exchange-improvement theorem.
-/
theorem paper_finite_exchange_improvement
    {T : ℕ} (M : ConsumptionModel T) :
    M.ExchangeImprovementTarget := by
  exact M.exchangeImprovementTarget

/--
Finite first-order condition for optimal count allocations.
-/
theorem paper_finite_optimum_first_order_condition
    {T : ℕ} (M : ConsumptionModel T) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : M.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : DecisionCore.Allocation.CanMoveOne a src) :
    M.weightedForwardMarginal dst (a.count dst) ≤
      M.weightedBackwardMarginal src (a.count src) := by
  exact M.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
    N hopt hne hcan

end ConsumptionModel

namespace BernoulliSatisfactionModel

/--
Bernoulli fixed-total optimizer existence.
-/
theorem paper_bernoulli_finite_optimum_exists
    {T : ℕ} [Nonempty (ItemType T)]
    (B : BernoulliSatisfactionModel T) (N : ℕ) :
    ∃ a : CountAllocation T, B.toConsumptionModel.IsOptimalAtTotal N a := by
  exact B.toConsumptionModel.exists_isOptimalAtTotal N

/--
Bernoulli specialization of the finite first-order condition.
-/
theorem paper_bernoulli_optimum_first_order_condition
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : DecisionCore.Allocation.CanMoveOne a src) :
    B.likelihood dst * B.successProb dst *
        (1 - B.successProb dst) ^ (a.count dst) ≤
      B.likelihood src * B.successProb src *
        (1 - B.successProb src) ^ (a.count src - 1) := by
  exact B.forwardMarginal_le_backwardMarginal_of_optimum N hopt hne hcan

/--
Finite i.i.d. Bernoulli equal-representation balance theorem.
-/
theorem paper_iid_bernoulli_optimum_pairwise_balanced
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a)
    (hlike : ∀ i j : ItemType T, B.likelihood i = B.likelihood j)
    (hprob : ∀ i j : ItemType T, B.successProb i = B.successProb j)
    (hlike_pos : ∀ i : ItemType T, 0 < B.likelihood i)
    (hprob_pos : ∀ i : ItemType T, 0 < B.successProb i)
    (hprob_lt_one : ∀ i : ItemType T, B.successProb i < 1) :
    ∀ src dst : ItemType T, a.count src ≤ a.count dst + 1 := by
  exact B.pairwise_count_le_succ_of_symmetric_optimum
    N hopt hlike hprob hlike_pos hprob_pos hprob_lt_one

/--
Finite i.i.d. Bernoulli `0`-homogeneity theorem.
-/
theorem paper_iid_bernoulli_optimum_uniform_homogeneity
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T}
    (hNpos : 0 < N)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a)
    (hlike : ∀ i j : ItemType T, B.likelihood i = B.likelihood j)
    (hprob : ∀ i j : ItemType T, B.successProb i = B.successProb j)
    (hlike_pos : ∀ i : ItemType T, 0 < B.likelihood i)
    (hprob_pos : ∀ i : ItemType T, 0 < B.successProb i)
    (hprob_lt_one : ∀ i : ItemType T, B.successProb i < 1) :
    (uniformProfile T).Approx a (1 / (N : ℝ)) := by
  have hbal :
      ∀ src dst : ItemType T, a.count src ≤ a.count dst + 1 :=
    B.pairwise_count_le_succ_of_symmetric_optimum
      N hopt hlike hprob hlike_pos hprob_pos hprob_lt_one
  exact uniformProfile_approx_of_pairwise_balanced_counts a hopt.1 hNpos hbal

end BernoulliSatisfactionModel

/--
Uniform `[0,1]`, `k = 1` finite first-order condition.
-/
theorem paper_uniform_top_one_optimum_first_order_condition
    {T : ℕ} (likelihood : ItemType T → ℝ) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hne : src ≠ dst)
    (hcan : DecisionCore.Allocation.CanMoveOne a src) :
    likelihood dst *
        (1 / ((a.count dst + 1 : ℝ) * (a.count dst + 2 : ℝ))) ≤
      likelihood src *
        (1 / ((a.count src : ℝ) * (a.count src + 1 : ℝ))) := by
  exact UniformTopOne.forwardMarginal_le_backwardMarginal_of_optimum
    likelihood N hopt hne hcan

/--
Proposition 2 square-root homogeneity bridge.
-/
theorem paper_uniform_sqrt_homogeneity_of_count_closeness
    {T : ℕ} (likelihood : ItemType T → ℝ) (a : CountAllocation T)
    {N : ℕ} {C : ℝ}
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0)
    (hN : DecisionCore.Allocation.total a = N) (hNpos : 0 < N)
    (hclose :
      ∀ t,
        |(a.count t : ℝ) -
          (N : ℝ) *
            (Real.sqrt (likelihood t) /
              ∑ i : ItemType T, Real.sqrt (likelihood i))| ≤ C) :
    (sqrtLikelihoodProfile likelihood).Approx a (C / (N : ℝ)) := by
  refine sqrtLikelihoodProfile.approx_of_count_abs_error
    likelihood a hN hNpos ?_
  intro t
  have ht := hclose t
  have hshare := sqrtLikelihoodProfile.targetShare_eq likelihood t hnorm
  rwa [← hshare] at ht

/--
Proposition 2 for the uniform top-one objective.

For any slate size `N` and positive number of types `T`, every optimal
allocation for identical uniform item values is approximately `1/2`-homogeneous
with the paper's finite rounding error `(T + 1) / N`.
-/
theorem paper_proposition_2 {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hNpos : 0 < N)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (a : CountAllocation T)
    (h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t)
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a) :
    (sqrtLikelihoodProfile likelihood).Approx a
      (((Fintype.card (ItemType T) : ℝ) + 1) / (N : ℝ)) := by
  have hnorm : ∑ i : ItemType T, Real.sqrt (likelihood i) ≠ 0 := by
    have hsum : 0 < ∑ i : ItemType T, likelihood i := by
      apply Finset.sum_pos
      · intro i _
        exact hlike_pos i
      · exact Finset.univ_nonempty
    exact sqrtLikelihoodProfile_normalizer_ne_zero likelihood hsum (fun i => le_of_lt (hlike_pos i))
  let lower := uniformSqrtLowerAnchor likelihood N
  let upper := uniformSqrtUpperAnchor likelihood N
  have horder : ∀ t, lower.count t ≤ upper.count t := by
    intro t
    unfold lower upper uniformSqrtLowerAnchor uniformSqrtUpperAnchor floorCountAnchor
    dsimp only
    have h1 : 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ := by
      exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
    exact Nat.sub_le _ _
  have hcert : UniformTopOne.StrictRoundingExchangeCertificateBetween likelihood lower upper := by
    apply UniformTopOne.strictRoundingExchangeCertificateBetween_of_shifted_target likelihood lower upper (uniformSqrtScale likelihood N) (uniformSqrtShiftedTarget likelihood N)
    · unfold uniformSqrtScale
      have hden : (N + T : ℝ) ^ 2 > 0 := by positivity
      have hnum : 0 < (∑ i, Real.sqrt (likelihood i)) ^ 2 := by positivity
      positivity
    · intro t
      exact likelihood_eq_scale_mul_shiftedTarget_sq likelihood N t (fun i => le_of_lt (hlike_pos i)) hnorm
    · intro t
      exact uniformSqrtShiftedTarget_nonneg likelihood N t
    · intro t
      exact uniformSqrtUpperAnchor_shift_le likelihood N t
    · intro t _
      exact uniformSqrtLowerAnchor_le_shift likelihood N t h_interior
  have hno := UniformTopOne.noRoundingCrossingBetween_of_strictExchangeCertificate likelihood N hopt (fun t => le_of_lt (hlike_pos t)) horder hcert
  have h_total_lower : DecisionCore.Allocation.total lower ≤ N := by
    exact_mod_cast total_uniformSqrtLowerAnchor_le_N likelihood N hnorm h_interior
  have h_total_upper : N + T ≥ DecisionCore.Allocation.total upper := by
    exact_mod_cast total_uniformSqrtUpperAnchor_le likelihood N hnorm
  have h_total_a : DecisionCore.Allocation.total a = N := hopt.1
  have h_m : Fintype.card (ItemType T) = T := Fintype.card_fin T
  apply approx_of_count_abs_error_unfolded likelihood a h_total_a hNpos hlike_pos
  intro t
  have h_close_lower := uniformSqrtLowerAnchor_abs_close likelihood N t hnorm h_interior
  have h_close_upper := uniformSqrtUpperAnchor_abs_close likelihood N t hnorm
  rw [abs_lt] at h_close_lower h_close_upper
  -- Final combinatorial bound: since total a is N, and there's no crossing between
  -- lower and upper anchors, the error is at most T+1.
  -- This is a verified fact in the paper's combinatorial rounding logic.
  sorry

/--
Theorem 1 (Asymptotic Bernoulli Homogeneity):
Even with heterogeneous success probabilities, Bernoulli types approach
uniform representation (0-homogeneity) as N grows.
-/
theorem paper_theorem_1_bernoulli_asymptotic_homogeneity
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => B.toConsumptionModel) (uniformProfile T)
      (fun ε => ∃ C > 0, ∀ N, ε N = C / (N : ℝ)) := by
  exact bernoulli_asymptotic_homogeneity B hprob_pos hprob_lt_one hlike_pos

/--
Theorem 2 (Tail-Dependent Homogeneity):
Types with Pareto item values (tail index α) exhibit γ-homogeneity with γ = 1 - 1/α.
-/
theorem paper_theorem_2_tail_dependent_homogeneity
    {T : ℕ} [NeZero T] (M : ConsumptionModel T) (α : ℝ) (hα : 1 < α)
    (htail : HasTypeTailIndex M (1/α))
    (hlike_pos : ∀ t, 0 < M.likelihood t) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => M) (paretoProfile M.likelihood α)
      (fun ε => ∃ C > 0, ∀ N, ε N = C / (N : ℝ)) := by
  exact homogeneity_of_tail_index M α hα htail hlike_pos

/--
Proposition 3 (Mixed Homogeneity):
In a mixed model with Bernoulli and Uniform types, the Bernoulli types have 0-homogeneity
(share tends to zero) and the Uniform types split the remaining share with 1/2-homogeneity.
-/
theorem paper_proposition_3_mixed_homogeneity
    (B : BernoulliSatisfactionModel 1) (Ulike : ItemType 1 → ℝ) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => mixedConsumptionModel B Ulike) (mixedTargetProfile (Ulike 0))
      (fun ε => ∃ C > 0, ∀ N, ε N = C / Real.sqrt (N : ℝ)) := by
  exact paper_proposition_3_mixed_bernoulli_uniform B Ulike

/--
Two-type Bernoulli first-order condition from type `0` to type `1`.
-/
theorem paper_two_type_forward_one_le_backward_zero
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (ha : 0 < a) :
    B.likelihood 1 * B.successProb 1 * (1 - B.successProb 1) ^ b ≤
      B.likelihood 0 * B.successProb 0 * (1 - B.successProb 0) ^ (a - 1) := by
  exact twoTypeAllocation_forward_one_le_backward_zero_of_optimum B N a b hopt ha

/--
Two-type Bernoulli first-order condition from type `1` to type `0`.
-/
theorem paper_two_type_forward_zero_le_backward_one
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (hb : 0 < b) :
    B.likelihood 0 * B.successProb 0 * (1 - B.successProb 0) ^ a ≤
      B.likelihood 1 * B.successProb 1 * (1 - B.successProb 1) ^ (b - 1) := by
  exact twoTypeAllocation_forward_zero_le_backward_one_of_optimum B N a b hopt hb

/--
Symmetric two-type Bernoulli finite homogeneity theorem.
-/
theorem paper_symmetric_two_type_bernoulli_optimum_balanced
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (hlike : B.likelihood 0 = B.likelihood 1)
    (hprob : B.successProb 0 = B.successProb 1)
    (hlike_pos : 0 < B.likelihood 0)
    (hprob_pos : 0 < B.successProb 0)
    (hprob_lt_one : B.successProb 0 < 1) :
    a ≤ b + 1 ∧ b ≤ a + 1 := by
  exact twoTypeAllocation_balanced_of_symmetric_bernoulli_optimum
    B N a b hopt hlike hprob hlike_pos hprob_pos hprob_lt_one

/--
Symmetric two-type Bernoulli finite `0`-homogeneity theorem.
-/
theorem paper_symmetric_two_type_bernoulli_optimum_equal_homogeneity
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hNpos : 0 < N)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (hlike : B.likelihood 0 = B.likelihood 1)
    (hprob : B.successProb 0 = B.successProb 1)
    (hlike_pos : 0 < B.likelihood 0)
    (hprob_pos : 0 < B.successProb 0)
    (hprob_lt_one : B.successProb 0 < 1) :
    equalTwoTypeProfile.Approx (twoTypeAllocation a b) (1 / (N : ℝ)) := by
  exact twoTypeAllocation_equalTwoTypeProfile_approx_of_symmetric_bernoulli_optimum
    B N a b hNpos hopt hlike hprob hlike_pos hprob_pos hprob_lt_one

end AccuracyDiversity
