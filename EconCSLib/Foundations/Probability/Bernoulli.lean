import Mathlib.Tactic

namespace EconCSLib
namespace Probability
namespace Bernoulli

/-!
# Bernoulli Success-Value Helpers

Reusable scalar identities for the value of drawing at least one success from
`q` independent Bernoulli trials with success probability `p`.
-/

/--
Expected satisfaction from `q` independent Bernoulli trials when the consumer
only needs one success: `1 - (1 - p)^q`.
-/
noncomputable def atLeastOneValue (p : ℝ) (q : ℕ) : ℝ :=
  1 - (1 - p) ^ q

@[simp] theorem atLeastOneValue_zero (p : ℝ) :
    atLeastOneValue p 0 = 0 := by
  simp [atLeastOneValue]

@[simp] theorem atLeastOneValue_one (p : ℝ) :
    atLeastOneValue p 1 = p := by
  simp [atLeastOneValue]

/-- Closed form for the one-step Bernoulli satisfaction marginal. -/
theorem atLeastOneValue_succ_sub (p : ℝ) (q : ℕ) :
    atLeastOneValue p (q + 1) - atLeastOneValue p q =
      p * (1 - p) ^ q := by
  calc
    atLeastOneValue p (q + 1) - atLeastOneValue p q
        = (1 - p) ^ q - (1 - p) ^ (q + 1) := by
          simp [atLeastOneValue]
    _ = (1 - p) ^ q - (1 - p) ^ q * (1 - p) := by
          rw [pow_succ]
    _ = p * (1 - p) ^ q := by
          ring

/-- Closed form for the value lost by removing the last Bernoulli trial. -/
theorem atLeastOneValue_sub_pred {p : ℝ} {q : ℕ} (hq : 0 < q) :
    atLeastOneValue p q - atLeastOneValue p (q - 1) =
      p * (1 - p) ^ (q - 1) := by
  have hsucc : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  nth_rewrite 1 [← hsucc]
  exact atLeastOneValue_succ_sub p (q - 1)

/-- Bernoulli satisfaction has nonnegative marginal values for `0 ≤ p ≤ 1`. -/
theorem atLeastOneValue_succ_sub_nonneg {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℕ) :
    0 ≤ atLeastOneValue p (q + 1) - atLeastOneValue p q := by
  rw [atLeastOneValue_succ_sub]
  exact mul_nonneg hp0 (pow_nonneg (by linarith) q)

/-- Bernoulli satisfaction has diminishing one-step marginal values for `0 ≤ p ≤ 1`. -/
theorem atLeastOneValue_diminishing_marginal {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℕ) :
    atLeastOneValue p (q + 2) - atLeastOneValue p (q + 1) ≤
      atLeastOneValue p (q + 1) - atLeastOneValue p q := by
  have hr0 : 0 ≤ 1 - p := by linarith
  have hr1 : 1 - p ≤ 1 := by linarith
  have hpow : (1 - p) ^ (q + 1) ≤ (1 - p) ^ q := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hr0 q) hr1
  calc
    atLeastOneValue p (q + 2) - atLeastOneValue p (q + 1)
        = p * (1 - p) ^ (q + 1) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            atLeastOneValue_succ_sub p (q + 1)
    _ ≤ p * (1 - p) ^ q := mul_le_mul_of_nonneg_left hpow hp0
    _ = atLeastOneValue p (q + 1) - atLeastOneValue p q := by
          rw [atLeastOneValue_succ_sub]

end Bernoulli
end Probability
end EconCSLib
