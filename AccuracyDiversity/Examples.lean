import AccuracyDiversity.Bernoulli
import AccuracyDiversity.BernoulliExchange
import AccuracyDiversity.Optimization
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace AccuracyDiversity

/-- Two-type allocation helper: type `0` gets `a`, type `1` gets `b`. -/
def twoTypeAllocation (a b : ℕ) : CountAllocation 2 where
  count := fun t => if t = 0 then a else b

@[simp] theorem twoTypeAllocation_zero (a b : ℕ) :
    (twoTypeAllocation a b).count (0 : ItemType 2) = a := by
  simp [twoTypeAllocation]

@[simp] theorem twoTypeAllocation_one (a b : ℕ) :
    (twoTypeAllocation a b).count (1 : ItemType 2) = b := by
  simp [twoTypeAllocation]

/-- Total size of the two-type allocation helper. -/
@[simp] theorem twoTypeAllocation_total (a b : ℕ) :
    DecisionCore.Allocation.total (twoTypeAllocation a b) = a + b := by
  simp [DecisionCore.Allocation.total, twoTypeAllocation, Fin.sum_univ_two]

/-- Objective expansion for two-type allocations. -/
theorem twoTypeAllocation_objective (M : ConsumptionModel 2) (a b : ℕ) :
    M.objective (twoTypeAllocation a b) =
      M.likelihood 0 * M.valueOfCount 0 a +
        M.likelihood 1 * M.valueOfCount 1 b := by
  simp [ConsumptionModel.objective, DecisionCore.Allocation.objective,
    twoTypeAllocation, Fin.sum_univ_two]

/--
Two-type Bernoulli first-order condition: if type `0` has positive count at an
optimum, the type-`1` forward marginal is bounded by type `0`'s last marginal.
-/
theorem twoTypeAllocation_forward_one_le_backward_zero_of_optimum
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (ha : 0 < a) :
    B.likelihood 1 * B.successProb 1 * (1 - B.successProb 1) ^ b ≤
      B.likelihood 0 * B.successProb 0 * (1 - B.successProb 0) ^ (a - 1) := by
  have h := B.forwardMarginal_le_backwardMarginal_of_optimum
    (N := N) (a := twoTypeAllocation a b)
    (src := (0 : ItemType 2)) (dst := (1 : ItemType 2)) hopt (by decide)
    (by simpa using ha)
  simpa using h

/--
The symmetric two-type first-order condition moving one count from type `1` to
type `0`.
-/
theorem twoTypeAllocation_forward_zero_le_backward_one_of_optimum
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (hb : 0 < b) :
    B.likelihood 0 * B.successProb 0 * (1 - B.successProb 0) ^ a ≤
      B.likelihood 1 * B.successProb 1 * (1 - B.successProb 1) ^ (b - 1) := by
  have h := B.forwardMarginal_le_backwardMarginal_of_optimum
    (N := N) (a := twoTypeAllocation a b)
    (src := (1 : ItemType 2)) (dst := (0 : ItemType 2)) hopt (by decide)
    (by simpa using hb)
  simpa using h

/--
Symmetric two-type Bernoulli optima are balanced: if the two types have the
same likelihood and success probability, no finite optimum can put more than
one extra item on either type.
-/
theorem twoTypeAllocation_balanced_of_symmetric_bernoulli_optimum
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (hlike : B.likelihood 0 = B.likelihood 1)
    (hprob : B.successProb 0 = B.successProb 1)
    (hlike_pos : 0 < B.likelihood 0)
    (hprob_pos : 0 < B.successProb 0)
    (hprob_lt_one : B.successProb 0 < 1) :
    a ≤ b + 1 ∧ b ≤ a + 1 := by
  constructor
  · by_contra hle
    have hb_succ_lt : b + 1 < a := Nat.lt_of_not_ge hle
    have hb_lt_pred : b < a - 1 :=
      (Nat.lt_sub_iff_add_lt).mpr hb_succ_lt
    have ha : 0 < a := (Nat.succ_pos b).trans hb_succ_lt
    have hfirst :=
      twoTypeAllocation_forward_one_le_backward_zero_of_optimum
        B N a b hopt ha
    have hfirst' :
        (B.likelihood 0 * B.successProb 0) *
            (1 - B.successProb 0) ^ b ≤
          (B.likelihood 0 * B.successProb 0) *
            (1 - B.successProb 0) ^ (a - 1) := by
      simpa [← hlike, ← hprob, mul_assoc] using hfirst
    have hcoef_pos : 0 < B.likelihood 0 * B.successProb 0 :=
      mul_pos hlike_pos hprob_pos
    have hpow_le :
        (1 - B.successProb 0) ^ b ≤
          (1 - B.successProb 0) ^ (a - 1) :=
      le_of_mul_le_mul_left hfirst' hcoef_pos
    have hbase_pos : 0 < 1 - B.successProb 0 := by linarith
    have hbase_lt_one : 1 - B.successProb 0 < 1 := by linarith
    have hpow_lt :
        (1 - B.successProb 0) ^ (a - 1) <
          (1 - B.successProb 0) ^ b :=
      pow_lt_pow_right_of_lt_one₀ hbase_pos hbase_lt_one hb_lt_pred
    exact (not_lt_of_ge hpow_le) hpow_lt
  · by_contra hle
    have ha_succ_lt : a + 1 < b := Nat.lt_of_not_ge hle
    have ha_lt_pred : a < b - 1 :=
      (Nat.lt_sub_iff_add_lt).mpr ha_succ_lt
    have hb : 0 < b := (Nat.succ_pos a).trans ha_succ_lt
    have hfirst :=
      twoTypeAllocation_forward_zero_le_backward_one_of_optimum
        B N a b hopt hb
    have hfirst' :
        (B.likelihood 0 * B.successProb 0) *
            (1 - B.successProb 0) ^ a ≤
          (B.likelihood 0 * B.successProb 0) *
            (1 - B.successProb 0) ^ (b - 1) := by
      simpa [← hlike, ← hprob, mul_assoc] using hfirst
    have hcoef_pos : 0 < B.likelihood 0 * B.successProb 0 :=
      mul_pos hlike_pos hprob_pos
    have hpow_le :
        (1 - B.successProb 0) ^ a ≤
          (1 - B.successProb 0) ^ (b - 1) :=
      le_of_mul_le_mul_left hfirst' hcoef_pos
    have hbase_pos : 0 < 1 - B.successProb 0 := by linarith
    have hbase_lt_one : 1 - B.successProb 0 < 1 := by linarith
    have hpow_lt :
        (1 - B.successProb 0) ^ (b - 1) <
          (1 - B.successProb 0) ^ a :=
      pow_lt_pow_right_of_lt_one₀ hbase_pos hbase_lt_one ha_lt_pred
    exact (not_lt_of_ge hpow_le) hpow_lt

/-- Type `0`'s representation in a positive two-type allocation. -/
theorem twoTypeAllocation_representation_zero
    (a b : ℕ) (hpos : 0 < a + b) :
    CountAllocation.representation (twoTypeAllocation a b) (0 : ItemType 2) =
      (a : ℝ) / (a + b : ℝ) := by
  have htotal : DecisionCore.Allocation.total (twoTypeAllocation a b) ≠ 0 := by
    intro hzero
    have hab : a + b = 0 := by simpa using hzero
    exact hpos.ne' hab
  rw [CountAllocation.representation_eq_share]
  rw [DecisionCore.Allocation.share_eq_div_of_total_ne_zero
    (a := twoTypeAllocation a b) (k := (0 : ItemType 2)) htotal]
  simp

/-- Type `1`'s representation in a positive two-type allocation. -/
theorem twoTypeAllocation_representation_one
    (a b : ℕ) (hpos : 0 < a + b) :
    CountAllocation.representation (twoTypeAllocation a b) (1 : ItemType 2) =
      (b : ℝ) / (a + b : ℝ) := by
  have htotal : DecisionCore.Allocation.total (twoTypeAllocation a b) ≠ 0 := by
    intro hzero
    have hab : a + b = 0 := by simpa using hzero
    exact hpos.ne' hab
  rw [CountAllocation.representation_eq_share]
  rw [DecisionCore.Allocation.share_eq_div_of_total_ne_zero
    (a := twoTypeAllocation a b) (k := (1 : ItemType 2)) htotal]
  simp

/-- A toy profile with equal representation across two types. -/
noncomputable def equalTwoTypeProfile : GammaHomogeneityProfile 2 where
  gamma := 0
  targetWeight := fun _ => 1

@[simp] theorem equalTwoTypeProfile_targetShare_zero :
    equalTwoTypeProfile.targetShare (0 : ItemType 2) = 1 / 2 := by
  simp [equalTwoTypeProfile, GammaHomogeneityProfile.targetShare,
    GammaHomogeneityProfile.normalizer]

@[simp] theorem equalTwoTypeProfile_targetShare_one :
    equalTwoTypeProfile.targetShare (1 : ItemType 2) = 1 / 2 := by
  simp [equalTwoTypeProfile, GammaHomogeneityProfile.targetShare,
    GammaHomogeneityProfile.normalizer]

/--
A balanced two-type allocation is approximately `0`-homogeneous, i.e. close to
equal representation, with the natural finite rounding error `1 / total`.
-/
theorem twoTypeAllocation_equalTwoTypeProfile_approx_of_balanced
    (a b : ℕ) (hpos : 0 < a + b)
    (hbal : a ≤ b + 1 ∧ b ≤ a + 1) :
    equalTwoTypeProfile.Approx (twoTypeAllocation a b) (1 / (a + b : ℝ)) := by
  intro t
  fin_cases t
  · change
      |CountAllocation.representation (twoTypeAllocation a b) (0 : ItemType 2) -
        equalTwoTypeProfile.targetShare (0 : ItemType 2)| ≤ 1 / (↑a + ↑b)
    rw [twoTypeAllocation_representation_zero a b hpos,
      equalTwoTypeProfile_targetShare_zero]
    have hNpos : 0 < (a + b : ℝ) := by exact_mod_cast hpos
    have hNne : (a + b : ℝ) ≠ 0 := ne_of_gt hNpos
    have hbal1 : (a : ℝ) ≤ (b : ℝ) + 1 := by exact_mod_cast hbal.1
    have hbal2 : (b : ℝ) ≤ (a : ℝ) + 1 := by exact_mod_cast hbal.2
    rw [abs_le]
    constructor <;> field_simp [hNne] <;> nlinarith
  · change
      |CountAllocation.representation (twoTypeAllocation a b) (1 : ItemType 2) -
        equalTwoTypeProfile.targetShare (1 : ItemType 2)| ≤ 1 / (↑a + ↑b)
    rw [twoTypeAllocation_representation_one a b hpos,
      equalTwoTypeProfile_targetShare_one]
    have hNpos : 0 < (a + b : ℝ) := by exact_mod_cast hpos
    have hNne : (a + b : ℝ) ≠ 0 := ne_of_gt hNpos
    have hbal1 : (a : ℝ) ≤ (b : ℝ) + 1 := by exact_mod_cast hbal.1
    have hbal2 : (b : ℝ) ≤ (a : ℝ) + 1 := by exact_mod_cast hbal.2
    rw [abs_le]
    constructor <;> field_simp [hNne] <;> nlinarith

/--
Symmetric two-type Bernoulli optima are approximately equal-representation with
finite rounding error `1 / N`.
-/
theorem twoTypeAllocation_equalTwoTypeProfile_approx_of_symmetric_bernoulli_optimum
    (B : BernoulliSatisfactionModel 2) (N a b : ℕ)
    (hNpos : 0 < N)
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N (twoTypeAllocation a b))
    (hlike : B.likelihood 0 = B.likelihood 1)
    (hprob : B.successProb 0 = B.successProb 1)
    (hlike_pos : 0 < B.likelihood 0)
    (hprob_pos : 0 < B.successProb 0)
    (hprob_lt_one : B.successProb 0 < 1) :
    equalTwoTypeProfile.Approx (twoTypeAllocation a b) (1 / (N : ℝ)) := by
  have hsum : a + b = N := by simpa using hopt.1
  have hpos : 0 < a + b := by simpa [hsum] using hNpos
  have hbal :=
    twoTypeAllocation_balanced_of_symmetric_bernoulli_optimum
      B N a b hopt hlike hprob hlike_pos hprob_pos hprob_lt_one
  have hsumR : (a : ℝ) + (b : ℝ) = (N : ℝ) := by
    exact_mod_cast hsum
  simpa [hsumR] using
    twoTypeAllocation_equalTwoTypeProfile_approx_of_balanced a b hpos hbal

/-- A small milk/ice-cream style Bernoulli model: milk is more likely, ice cream is pickier. -/
noncomputable def milkIceCreamModel : BernoulliSatisfactionModel 2 where
  likelihood := fun t => if t = 0 then 0.7 else 0.3
  successProb := fun t => if t = 0 then 0.9 else 0.2

/-- A toy profile with weights matching the milk/ice-cream likelihoods. -/
noncomputable def likelihoodTwoTypeProfile : GammaHomogeneityProfile 2 where
  gamma := 1
  targetWeight := milkIceCreamModel.likelihood

#check milkIceCreamModel.toConsumptionModel
#check BernoulliSatisfactionModel.objective
#check ConsumptionModel.ApproxHomogeneityOfOptima
#check twoTypeAllocation

end AccuracyDiversity
