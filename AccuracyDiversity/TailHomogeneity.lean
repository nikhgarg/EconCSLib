import AccuracyDiversity.Representation
import AccuracyDiversity.TopKOracle
import AccuracyDiversity.Uniform
import AccuracyDiversity.Bernoulli
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace AccuracyDiversity

/--
Theorem 1 (Asymptotic Bernoulli Homogeneity):
Even with heterogeneous success probabilities, Bernoulli types approach
uniform representation (0-homogeneity) as N grows.
-/
theorem bernoulli_asymptotic_homogeneity
    {T : ℕ} [NeZero T] (B : BernoulliSatisfactionModel T)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => B.toConsumptionModel) (uniformProfile T) (fun ε => ∃ C > 0, ∀ N, ε N = C / N) := by
  sorry

/--
The core lemma for Theorem 1 (Heterogeneous Bernoulli):
If marginals are `L * p * (1-p)^q`, then the optimal counts stay within a
constant distance of each other.
-/
theorem bernoulli_optimum_pairwise_difference_bounded
    {T : ℕ} (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a)
    (hprob_pos : ∀ t, 0 < B.successProb t)
    (hprob_lt_one : ∀ t, B.successProb t < 1)
    (hlike_pos : ∀ t, 0 < B.likelihood t) :
    ∀ t₁ t₂,
      0 < a.count t₁ →
      (a.count t₁ : ℝ) - 1 ≤
        (Real.log (B.likelihood t₂ * B.successProb t₂) -
         Real.log (B.likelihood t₁ * B.successProb t₁) +
         (a.count t₂ : ℝ) * Real.log (1 - B.successProb t₂)) /
        Real.log (1 - B.successProb t₁) := by
  intro t₁ t₂ ha1
  by_cases hne : t₁ = t₂
  · subst t₂
    have hbase1 : 0 < 1 - B.successProb t₁ := by linarith [hprob_lt_one t₁]
    have hprob1 : 1 - B.successProb t₁ < 1 := by linarith [hprob_pos t₁]
    have hlog_neg : Real.log (1 - B.successProb t₁) < 0 := Real.log_neg hbase1 hprob1
    have h1 : Real.log (B.likelihood t₁ * B.successProb t₁) - Real.log (B.likelihood t₁ * B.successProb t₁) = 0 := sub_self _
    rw [h1, zero_add]
    have h2 : ((a.count t₁ : ℝ) * Real.log (1 - B.successProb t₁)) / Real.log (1 - B.successProb t₁) = (a.count t₁ : ℝ) := by
      exact mul_div_cancel_right₀ (↑(a.count t₁)) hlog_neg.ne
    rw [h2]
    linarith
  · have hcan : DecisionCore.Allocation.CanMoveOne a t₁ := ha1
    have hne_symm : t₁ ≠ t₂ := hne
    have hfoc := B.forwardMarginal_le_backwardMarginal_of_optimum N hopt hne_symm.symm hcan
    have h_lp1_pos : 0 < B.likelihood t₁ * B.successProb t₁ := mul_pos (hlike_pos t₁) (hprob_pos t₁)
    have h_lp2_pos : 0 < B.likelihood t₂ * B.successProb t₂ := mul_pos (hlike_pos t₂) (hprob_pos t₂)
    have h_base1 : 0 < 1 - B.successProb t₁ := by linarith [hprob_lt_one t₁]
    have h_base2 : 0 < 1 - B.successProb t₂ := by linarith [hprob_lt_one t₂]
    have h_prob1 : 1 - B.successProb t₁ < 1 := by linarith [hprob_pos t₁]
    have h_log1_neg : Real.log (1 - B.successProb t₁) < 0 := Real.log_neg h_base1 h_prob1
    -- log(L2*p2*(1-p2)^q2) <= log(L1*p1*(1-p1)^(q1-1))
    have hlog_le : Real.log (B.likelihood t₂ * B.successProb t₂ * (1 - B.successProb t₂) ^ (a.count t₂)) ≤
                   Real.log (B.likelihood t₁ * B.successProb t₁ * (1 - B.successProb t₁) ^ (a.count t₁ - 1)) := by
      apply Real.log_le_log
      · positivity
      · exact hfoc
    rw [Real.log_mul h_lp2_pos.ne.symm (pow_pos h_base2 _).ne.symm] at hlog_le
    rw [Real.log_mul h_lp1_pos.ne.symm (pow_pos h_base1 _).ne.symm] at hlog_le
    rw [Real.log_pow, Real.log_pow] at hlog_le
    -- log(L2*p2) + q2 * log(1-p2) <= log(L1*p1) + (q1-1) * log(1-p1)
    have h_rearrange : (a.count t₁ : ℝ) - 1 ≤
        (Real.log (B.likelihood t₂ * B.successProb t₂) - Real.log (B.likelihood t₁ * B.successProb t₁) + (a.count t₂ : ℝ) * Real.log (1 - B.successProb t₂)) /
        Real.log (1 - B.successProb t₁) := by
      rw [le_div_iff_of_neg h_log1_neg]
      linarith
    exact h_rearrange

/-- A consumption model combining a Bernoulli type and a Uniform type. -/
noncomputable def mixedConsumptionModel
    (B : BernoulliSatisfactionModel 1)
    (Ulike : ItemType 1 → ℝ) : ConsumptionModel 2 where
  likelihood t := if t = 0 then B.likelihood 0 else Ulike 0
  valueOfCount t q := if t = 0 then bernoulliAtLeastOneValue (B.successProb 0) q
                      else uniformTopOneValue q
/-- FOC for the mixed model: Uniform marginal vs Bernoulli marginal. -/
theorem mixed_foc_one_zero (B : BernoulliSatisfactionModel 1) (Ulike : ItemType 1 → ℝ)
    (N : ℕ) {a : CountAllocation 2}
    (hopt : (mixedConsumptionModel B Ulike).IsOptimalAtTotal N a)
    (ha0 : 0 < a.count 0) :
    (Ulike 0) * (1 / ((a.count 1 + 1 : ℝ) * (a.count 1 + 2 : ℝ))) ≤
    (B.likelihood 0) * (B.successProb 0) * (1 - B.successProb 0) ^ (a.count 0 - 1) := by
  have hne : (0 : ItemType 2) ≠ 1 := by norm_num
  have hcan : DecisionCore.Allocation.CanMoveOne a 0 := ha0
  have h := ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
    (mixedConsumptionModel B Ulike) N hopt hne hcan
  unfold mixedConsumptionModel at h
  unfold ConsumptionModel.weightedForwardMarginal ConsumptionModel.weightedBackwardMarginal at h
  unfold ConsumptionModel.marginalValue at h
  unfold DecisionCore.Allocation.marginal at h
  dsimp only at h
  have ha0ne0 : a.count 0 ≠ 0 := ne_of_gt ha0
  rw [dif_neg ha0ne0] at h
  -- Simplify if branches manually to be sure
  have h_lhs : (if (1 : ItemType 2) = 0 then B.likelihood 0 else Ulike 0) = Ulike 0 := by
    rw [if_neg (by norm_num : (1 : ItemType 2) = 0)]
  have h_rhs : (if (0 : ItemType 2) = 0 then B.likelihood 0 else Ulike 0) = B.likelihood 0 := by
    rw [if_pos rfl]
  have h_lhs_val : ((if (1 : ItemType 2) = 0 then bernoulliAtLeastOneValue (B.successProb 0) (a.count 1 + 1)
                    else uniformTopOneValue (a.count 1 + 1)) -
                    if (1 : ItemType 2) = 0 then bernoulliAtLeastOneValue (B.successProb 0) (a.count 1)
                    else uniformTopOneValue (a.count 1)) =
                   uniformTopOneValue (a.count 1 + 1) - uniformTopOneValue (a.count 1) := by
    repeat rw [if_neg (by norm_num : (1 : ItemType 2) = 0)]
  have h_rhs_val : ((if (0 : ItemType 2) = 0 then bernoulliAtLeastOneValue (B.successProb 0) (a.count 0)
                    else uniformTopOneValue (a.count 0)) -
                    if (0 : ItemType 2) = 0 then bernoulliAtLeastOneValue (B.successProb 0) (a.count 0 - 1)
                    else uniformTopOneValue (a.count 0 - 1)) =
                   bernoulliAtLeastOneValue (B.successProb 0) (a.count 0) -
                   bernoulliAtLeastOneValue (B.successProb 0) (a.count 0 - 1) := by
    repeat rw [if_pos rfl]
  rw [h_lhs, h_rhs, h_lhs_val, h_rhs_val] at h
  rw [uniformTopOneValue_succ_sub] at h
  rw [bernoulliAtLeastOneValue_sub_pred _ ha0] at h
  exact h

/--
The target profile for a mixed Bernoulli-Uniform model.
Bernoulli types (0) get 0 share, Uniform types (1) get all share.
-/
noncomputable def mixedTargetProfile (Ulike : ℝ) : GammaHomogeneityProfile 2 where
  gamma := 1 / 2
  targetWeight t := if t = 0 then 0 else Real.sqrt Ulike

/--
Proposition 3: Mixed types (Bernoulli and Uniform).

When types have different tail behaviors, the types with faster-decaying marginals
(like Bernoulli) get negligible share as N grows, while the remaining types
split the share according to their tail-specific homogeneity rule.
-/
theorem paper_proposition_3_mixed_bernoulli_uniform
    (B : BernoulliSatisfactionModel 1) (Ulike : ItemType 1 → ℝ) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => mixedConsumptionModel B Ulike) (mixedTargetProfile (Ulike 0))
      (fun ε => ∃ C > 0, ∀ N, ε N = C / Real.sqrt (N : ℝ)) := by
  sorry

end AccuracyDiversity
