import PRPKG24AccuracyDiversity.Basic

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

/--
Expected satisfaction from `q` independent Bernoulli items when the user consumes one item:
`1 - (1 - p)^q`.
-/
noncomputable def bernoulliAtLeastOneValue (p : ℝ) (q : ℕ) : ℝ := 1 - (1 - p) ^ q

@[simp] theorem bernoulliAtLeastOneValue_zero (p : ℝ) :
    bernoulliAtLeastOneValue p 0 = 0 := by
  simp [bernoulliAtLeastOneValue]

theorem bernoulliAtLeastOneValue_one (p : ℝ) :
    bernoulliAtLeastOneValue p 1 = p := by
  simp [bernoulliAtLeastOneValue]

/-- Closed form for the one-step Bernoulli satisfaction marginal. -/
theorem bernoulliAtLeastOneValue_succ_sub (p : ℝ) (q : ℕ) :
    bernoulliAtLeastOneValue p (q + 1) - bernoulliAtLeastOneValue p q =
      p * (1 - p) ^ q := by
  calc
    bernoulliAtLeastOneValue p (q + 1) - bernoulliAtLeastOneValue p q
        = (1 - p) ^ q - (1 - p) ^ (q + 1) := by
          simp [bernoulliAtLeastOneValue]
    _ = (1 - p) ^ q - (1 - p) ^ q * (1 - p) := by
          rw [pow_succ]
    _ = p * (1 - p) ^ q := by
          ring

/-- Closed form for the value lost by removing the last Bernoulli recommendation. -/
theorem bernoulliAtLeastOneValue_sub_pred {p : ℝ} {q : ℕ} (hq : 0 < q) :
    bernoulliAtLeastOneValue p q - bernoulliAtLeastOneValue p (q - 1) =
      p * (1 - p) ^ (q - 1) := by
  have hsucc : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  nth_rewrite 1 [← hsucc]
  exact bernoulliAtLeastOneValue_succ_sub p (q - 1)

/-- Bernoulli satisfaction has nonnegative marginal values for `0 ≤ p ≤ 1`. -/
theorem bernoulliAtLeastOneValue_succ_sub_nonneg {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℕ) :
    0 ≤ bernoulliAtLeastOneValue p (q + 1) - bernoulliAtLeastOneValue p q := by
  rw [bernoulliAtLeastOneValue_succ_sub]
  exact mul_nonneg hp0 (pow_nonneg (by linarith) q)

/-- Bernoulli satisfaction has diminishing one-step marginal values for `0 ≤ p ≤ 1`. -/
theorem bernoulliAtLeastOneValue_diminishing_marginal {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℕ) :
    bernoulliAtLeastOneValue p (q + 2) - bernoulliAtLeastOneValue p (q + 1) ≤
      bernoulliAtLeastOneValue p (q + 1) - bernoulliAtLeastOneValue p q := by
  have hr0 : 0 ≤ 1 - p := by linarith
  have hr1 : 1 - p ≤ 1 := by linarith
  have hpow : (1 - p) ^ (q + 1) ≤ (1 - p) ^ q := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hr0 q) hr1
  calc
    bernoulliAtLeastOneValue p (q + 2) - bernoulliAtLeastOneValue p (q + 1)
        = p * (1 - p) ^ (q + 1) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            bernoulliAtLeastOneValue_succ_sub p (q + 1)
    _ ≤ p * (1 - p) ^ q := mul_le_mul_of_nonneg_left hpow hp0
    _ = bernoulliAtLeastOneValue p (q + 1) - bernoulliAtLeastOneValue p q := by
          rw [bernoulliAtLeastOneValue_succ_sub]

/-- Bernoulli-satisfaction specialization used by the paper's heterogeneous Bernoulli results. -/
structure BernoulliSatisfactionModel (T : ℕ) where
  likelihood : ItemType T → ℝ
  successProb : ItemType T → ℝ

namespace BernoulliSatisfactionModel

/-- Type likelihoods form a probability vector. -/
def LikelihoodsSumToOne {T : ℕ} (B : BernoulliSatisfactionModel T) : Prop := ∑ t, B.likelihood t = 1

/-- All success probabilities lie in `[0,1]`. -/
def SuccessProbabilitiesValid {T : ℕ} (B : BernoulliSatisfactionModel T) : Prop := ∀ t, 0 ≤ B.successProb t ∧ B.successProb t ≤ 1

/-- Convert the Bernoulli satisfaction model into the generic consumption model. -/
noncomputable def toConsumptionModel {T : ℕ} (B : BernoulliSatisfactionModel T) : ConsumptionModel T where
  likelihood := B.likelihood
  valueOfCount := fun t q => bernoulliAtLeastOneValue (B.successProb t) q

/-- Objective for the Bernoulli satisfaction model. -/
noncomputable def objective {T : ℕ}
    (B : BernoulliSatisfactionModel T) (a : CountAllocation T) : ℝ := B.toConsumptionModel.objective a

@[simp] theorem objective_eq_consumption_objective {T : ℕ}
    (B : BernoulliSatisfactionModel T) (a : CountAllocation T) :
    B.objective a = B.toConsumptionModel.objective a := rfl

@[simp] theorem valueOfCount_zero {T : ℕ}
    (B : BernoulliSatisfactionModel T) (t : ItemType T) :
    B.toConsumptionModel.valueOfCount t 0 = 0 := by
  simp [toConsumptionModel, bernoulliAtLeastOneValue]

/-- The Bernoulli specialization has nonnegative marginal values when probabilities are valid. -/
theorem toConsumptionModel_has_nonnegative_marginals {T : ℕ}
    (B : BernoulliSatisfactionModel T) (hvalid : B.SuccessProbabilitiesValid) :
    B.toConsumptionModel.HasNonnegativeMarginals := by
  intro t q
  simpa [ConsumptionModel.HasNonnegativeMarginals, EconCSLib.Allocation.HasNonnegativeMarginals,
    EconCSLib.Allocation.marginal, toConsumptionModel] using
      bernoulliAtLeastOneValue_succ_sub_nonneg (hvalid t).1 (hvalid t).2 q

/-- The Bernoulli specialization has diminishing marginal returns when probabilities are valid. -/
theorem toConsumptionModel_has_diminishing_returns {T : ℕ}
    (B : BernoulliSatisfactionModel T) (hvalid : B.SuccessProbabilitiesValid) :
    B.toConsumptionModel.HasDiminishingReturns := by
  intro t q
  simpa [ConsumptionModel.HasDiminishingReturns, EconCSLib.Allocation.HasDiminishingReturns,
    EconCSLib.Allocation.marginal, toConsumptionModel] using
      bernoulliAtLeastOneValue_diminishing_marginal (hvalid t).1 (hvalid t).2 q

end BernoulliSatisfactionModel
end PRPKG24AccuracyDiversity
