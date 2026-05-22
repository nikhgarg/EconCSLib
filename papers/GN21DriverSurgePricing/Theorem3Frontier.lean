import GN21DriverSurgePricing.MainTheorems

/-!
# Theorem 3 Frontier Routes for Driver Surge Pricing

This file holds the active small-surge Theorem 3 endpoints that are closest to
the source proof path.  Keeping them outside `MainTheorems.lean` gives future
proof work a narrow build target while the large CTMC theorem ledger remains
stable.
-/

open EconCSLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

noncomputable section

/-!
The current paper-proof route is the small-surge sequential construction:
choose surge prices with slack, move surge to accept-all first, then apply the
non-surge Lemma 10 comparison after the surge state is fixed at accept-all.
Do not use the finite/infinite pointwise upper-transfer branch as the default
source route; the CTMC reject-long monotonicity naturally gives the opposite
pointwise comparison unless an extra source upper/equality assumption is
available.
-/

/--
Theorem 3 positive-mass measurable IC on the source-shaped small-surge route.
The remaining policy-dependent input is the current Lemma 9 lower final-sign
condition; Lean derives the accept-all lower endpoint and the uniform upper
slack internally.
-/
theorem theorem3_positive_mass_measurable_ic_of_small_surge_final_sign
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeSlackFinalSignDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 := by
  exact
    paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_slack_final_sign_data_assumptions
      μ arrival rho R1 R2 switch12 switch21 A

/--
Preferred Theorem 3 frontier when the current Lemma 9 lower endpoint may be
positive.  The source supplies exact selected-price lower interval slack, while
Lean keeps the small-surge upper slack and accept-all sequencing internal.
-/
theorem theorem3_positive_mass_measurable_ic_of_small_surge_interval_final_sign
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeCurrentIntervalSlackFinalSignDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 := by
  exact
    paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_current_interval_slack_final_sign_data_assumptions
      μ arrival rho R1 R2 switch12 switch21 A

/--
Mass-affine Theorem 3 frontier with selected-price lower interval slack.  This
keeps the paper proof on the small-surge route while using the tighter
mass-affine non-surge reward envelope.
-/
theorem theorem3_positive_mass_measurable_ic_of_small_surge_mass_affine_interval_final_sign
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSmallSurgeMassAffineCurrentIntervalSlackFinalSignDataAssumptions
        μ arrival rho R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 := by
  exact
    paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_interval_slack_final_sign_data_assumptions
      μ arrival rho R1 R2 switch12 switch21 A

end

end GN21DriverSurgePricing
