import MBJG25ProducerFairness.MainTheorems

/-!
# Paper Assumptions: MBJG25 Producer Fairness

This file records source theorem conditions used by the compact human-facing
interface. The conditions are the fixed-setting prior-shape, time, quality, and
prior-strength domains appearing in Theorems 3.1 and 3.2.
-/

namespace MBJG25ProducerFairness

/-- The prior shape has positive total mass. -/
-- audit-premise: hshape : 0 < alpha + beta
abbrev assumption_positive_prior_shape (alpha beta : ℝ) : Prop :=
  0 < alpha + beta

/-- The fixed-setting theorem is evaluated after a positive number of timesteps. -/
-- audit-premise: ht : 0 < t
abbrev assumption_positive_time (t : ℝ) : Prop :=
  0 < t

/-- Nonnegative time/sample mass for Jensen concavity and global maximum statements. -/
-- audit-premise: ht : 0 ≤ t
abbrev assumption_nonnegative_time (t : ℝ) : Prop :=
  0 ≤ t

/-- True quality lies in the closed Bernoulli quality interval. -/
-- audit-premise: hq0 : 0 ≤ q
abbrev assumption_quality_nonnegative (q : ℝ) : Prop :=
  0 ≤ q

/-- True quality lies in the closed Bernoulli quality interval. -/
-- audit-premise: hq1 : q ≤ 1
abbrev assumption_quality_at_most_one (q : ℝ) : Prop :=
  q ≤ 1

/-- Interior true quality for the corrected strict variance statement. -/
-- audit-premise: hq0 : 0 < q
abbrev assumption_quality_positive (q : ℝ) : Prop :=
  0 < q

/-- Interior true quality for the corrected strict variance statement. -/
-- audit-premise: hq1 : q < 1
abbrev assumption_quality_lt_one (q : ℝ) : Prop :=
  q < 1

/-- Prior strength is nonnegative. -/
-- audit-premise: hetaLow_nonneg : 0 ≤ etaLow
-- audit-premise: heta_nonneg : 0 ≤ eta
abbrev assumption_prior_strength_nonnegative (eta : ℝ) : Prop :=
  0 ≤ eta

/-- Prior strength weakly increases. -/
-- audit-premise: heta_le : etaLow ≤ etaHigh
abbrev assumption_prior_strength_weak_order (etaLow etaHigh : ℝ) : Prop :=
  etaLow ≤ etaHigh

/-- Prior strength strictly increases. -/
-- audit-premise: heta_lt : etaLow < etaHigh
abbrev assumption_prior_strength_strict_order (etaLow etaHigh : ℝ) : Prop :=
  etaLow < etaHigh

end MBJG25ProducerFairness
