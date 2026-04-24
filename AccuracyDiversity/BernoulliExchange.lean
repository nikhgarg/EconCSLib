import AccuracyDiversity.Bernoulli
import AccuracyDiversity.Exchange

namespace AccuracyDiversity

namespace BernoulliSatisfactionModel

/-- Weighted forward marginal in the Bernoulli one-consumption model. -/
theorem weightedForwardMarginal_toConsumptionModel {T : ℕ}
    (B : BernoulliSatisfactionModel T) (t : ItemType T) (q : ℕ) :
    (B.toConsumptionModel).weightedForwardMarginal t q =
      B.likelihood t * B.successProb t * (1 - B.successProb t) ^ q := by
  unfold ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
    DecisionCore.Allocation.marginal toConsumptionModel
  rw [bernoulliAtLeastOneValue_succ_sub]
  ring

/-- Weighted backward marginal in the Bernoulli one-consumption model. -/
theorem weightedBackwardMarginal_toConsumptionModel {T : ℕ}
    (B : BernoulliSatisfactionModel T) (t : ItemType T) {q : ℕ}
    (hq : 0 < q) :
    (B.toConsumptionModel).weightedBackwardMarginal t q =
      B.likelihood t * B.successProb t * (1 - B.successProb t) ^ (q - 1) := by
  have hne : ¬ q = 0 := ne_of_gt hq
  unfold ConsumptionModel.weightedBackwardMarginal toConsumptionModel
  simp [hne]
  rw [bernoulliAtLeastOneValue_sub_pred (p := B.successProb t) hq]
  ring

/--
Paper-facing first-order condition for the finite Bernoulli specialization:
an optimal allocation has no exchange whose destination marginal exceeds the
source's last-item marginal.
-/
theorem forwardMarginal_le_backwardMarginal_of_optimum {T : ℕ}
    (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : DecisionCore.Allocation.CanMoveOne a src) :
    B.likelihood dst * B.successProb dst *
        (1 - B.successProb dst) ^ (a.count dst) ≤
      B.likelihood src * B.successProb src *
        (1 - B.successProb src) ^ (a.count src - 1) := by
  have h :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := B.toConsumptionModel) (N := N) (a := a)
      (src := src) (dst := dst) hopt hne hcan
  rw [weightedForwardMarginal_toConsumptionModel
    (B := B) (t := dst) (q := a.count dst)] at h
  rw [weightedBackwardMarginal_toConsumptionModel
    (B := B) (t := src) (q := a.count src) hcan] at h
  exact h

/--
Finite i.i.d. Bernoulli balance condition.

If all item types have the same likelihood and success probability, every
finite optimum has pairwise counts differing by at most one.
-/
theorem pairwise_count_le_succ_of_symmetric_optimum {T : ℕ}
    (B : BernoulliSatisfactionModel T) (N : ℕ) {a : CountAllocation T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a)
    (hlike : ∀ i j : ItemType T, B.likelihood i = B.likelihood j)
    (hprob : ∀ i j : ItemType T, B.successProb i = B.successProb j)
    (hlike_pos : ∀ i : ItemType T, 0 < B.likelihood i)
    (hprob_pos : ∀ i : ItemType T, 0 < B.successProb i)
    (hprob_lt_one : ∀ i : ItemType T, B.successProb i < 1) :
    ∀ src dst : ItemType T, a.count src ≤ a.count dst + 1 := by
  intro src dst
  by_cases hne : src = dst
  · subst dst
    exact Nat.le_succ _
  · by_contra hle
    have hdst_succ_lt : a.count dst + 1 < a.count src :=
      Nat.lt_of_not_ge hle
    have hdst_lt_pred : a.count dst < a.count src - 1 :=
      (Nat.lt_sub_iff_add_lt).mpr hdst_succ_lt
    have hcan : DecisionCore.Allocation.CanMoveOne a src :=
      (Nat.succ_pos (a.count dst)).trans hdst_succ_lt
    have hfirst :=
      B.forwardMarginal_le_backwardMarginal_of_optimum
        (N := N) (a := a) (src := src) (dst := dst) hopt hne hcan
    have hfirst' :
        (B.likelihood src * B.successProb src) *
            (1 - B.successProb src) ^ (a.count dst) ≤
          (B.likelihood src * B.successProb src) *
            (1 - B.successProb src) ^ (a.count src - 1) := by
      simpa [hlike dst src, hprob dst src, mul_assoc] using hfirst
    have hcoef_pos : 0 < B.likelihood src * B.successProb src :=
      mul_pos (hlike_pos src) (hprob_pos src)
    have hpow_le :
        (1 - B.successProb src) ^ (a.count dst) ≤
          (1 - B.successProb src) ^ (a.count src - 1) :=
      le_of_mul_le_mul_left hfirst' hcoef_pos
    have hbase_pos : 0 < 1 - B.successProb src := by
      linarith [hprob_lt_one src]
    have hbase_lt_one : 1 - B.successProb src < 1 := by
      linarith [hprob_pos src]
    have hpow_lt :
        (1 - B.successProb src) ^ (a.count src - 1) <
          (1 - B.successProb src) ^ (a.count dst) :=
      pow_lt_pow_right_of_lt_one₀ hbase_pos hbase_lt_one hdst_lt_pred
    exact (not_lt_of_ge hpow_le) hpow_lt

end BernoulliSatisfactionModel
end AccuracyDiversity
