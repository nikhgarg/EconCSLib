import Mathlib.Tactic

namespace EconCSLib

/-!
# Renewal-reward algebra

This module collects deterministic algebra used after a stochastic process has
been reduced to renewal-reward summaries.  The main use case is a driver (or
agent) who receives expected reward `W` during accepted jobs, spends expected
busy time `T`, and faces Poisson opportunities at rate `lambda`.

## Main declarations

- `renewalRewardRate`: `lambda * W / (1 + lambda * T)`.
- `averageRewardRate`: `W / T`.
- `renewalRewardRate_le_add_component_of_le_average`: adding a positive-time
  component whose average rate is at least the current renewal rate cannot
  decrease the renewal rate.
- `renewalRewardRate_remove_component_ge_of_average_le`: removing a
  positive-time component whose average rate is at most the current renewal
  rate cannot decrease the renewal rate.
- `renewalRewardRate_lt_replace_reward_same_time_of_lt`: replacing a component
  by another component with the same time contribution and strictly larger
  reward strictly increases the renewal rate.
-/

noncomputable section

/-- Renewal-reward earnings rate from arrival rate, expected reward, and expected busy time. -/
def renewalRewardRate (lambda reward time : ℝ) : ℝ :=
  lambda * reward / (1 + lambda * time)

/-- Average reward per unit busy time for a component. -/
def averageRewardRate (reward time : ℝ) : ℝ :=
  reward / time

/--
Adding a positive-time component whose average reward rate is at least the
current renewal-reward rate weakly increases the renewal-reward rate.
-/
theorem renewalRewardRate_le_add_component_of_le_average
    (lambda reward time addedReward addedTime : ℝ)
    (hlambda : 0 < lambda)
    (htime_nonneg : 0 ≤ time)
    (hadded_time_pos : 0 < addedTime)
    (hcurrent_le_added_average :
      renewalRewardRate lambda reward time ≤
        averageRewardRate addedReward addedTime) :
    renewalRewardRate lambda reward time ≤
      renewalRewardRate lambda (reward + addedReward) (time + addedTime) := by
  unfold renewalRewardRate averageRewardRate at *
  have hden_current : 0 < 1 + lambda * time := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htime_nonneg]
  have hden_added : 0 < 1 + lambda * (time + addedTime) := by
    nlinarith [mul_pos hlambda hadded_time_pos]
  have hcross :
      lambda * reward * addedTime ≤
        addedReward * (1 + lambda * time) := by
    rw [div_le_div_iff₀ hden_current hadded_time_pos] at hcurrent_le_added_average
    nlinarith
  rw [div_le_div_iff₀ hden_current hden_added]
  nlinarith

/--
Removing a positive-time component whose average reward rate is at most the
current renewal-reward rate weakly increases the renewal-reward rate.
-/
theorem renewalRewardRate_remove_component_ge_of_average_le
    (lambda reward time removedReward removedTime : ℝ)
    (hlambda : 0 < lambda)
    (htime_remaining_nonneg : 0 ≤ time - removedTime)
    (hremoved_time_pos : 0 < removedTime)
    (hremoved_average_le_current :
      averageRewardRate removedReward removedTime ≤
        renewalRewardRate lambda reward time) :
    renewalRewardRate lambda reward time ≤
      renewalRewardRate lambda (reward - removedReward) (time - removedTime) := by
  unfold renewalRewardRate averageRewardRate at *
  have htime_nonneg : 0 ≤ time := by
    linarith [le_of_lt hremoved_time_pos]
  have hden_current : 0 < 1 + lambda * time := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htime_nonneg]
  have hden_remaining : 0 < 1 + lambda * (time - removedTime) := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htime_remaining_nonneg]
  have hcross :
      removedReward * (1 + lambda * time) ≤
        lambda * reward * removedTime := by
    rw [div_le_div_iff₀ hremoved_time_pos hden_current] at hremoved_average_le_current
    nlinarith
  rw [div_le_div_iff₀ hden_current hden_remaining]
  nlinarith

/--
If a policy replacement keeps total busy time fixed but strictly increases the
per-cycle reward, then the renewal-reward earnings rate strictly increases.
-/
theorem renewalRewardRate_lt_replace_reward_same_time_of_lt
    (lambda reward time newReward : ℝ)
    (hlambda : 0 < lambda)
    (htime_nonneg : 0 ≤ time)
    (hreward_lt : reward < newReward) :
    renewalRewardRate lambda reward time <
      renewalRewardRate lambda newReward time := by
  unfold renewalRewardRate
  have hden : 0 < 1 + lambda * time := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htime_nonneg]
  have hnum : lambda * reward < lambda * newReward :=
    mul_lt_mul_of_pos_left hreward_lt hlambda
  rw [div_lt_div_iff₀ hden hden]
  exact mul_lt_mul_of_pos_right hnum hden

end

end EconCSLib
