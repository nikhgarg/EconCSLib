import GN21DriverSurgePricing.MainTheorems

/-!
# Theorem 4 Frontier Routes for Driver Surge Pricing

This file exposes compact Theorem 4 endpoints that are closest to the
source proof path.  The heavy CTMC endpoint records remain in
`MainTheorems.lean`; this module packages them into reviewable paper-facing
statements.
-/

open EconCSLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

noncomputable section

/--
Theorem 4 endpoint for exact one-threshold source selections with explicit
accept-all escape branches.  If every non-accept-all measurable optimum has
the finite non-surge reject-long and surge reject-short endpoint data required
by the paper proof, then accept-all is the unique measurable optimum.
-/
theorem paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_exact_one_threshold_non_accept_all_selection_unless
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (C :
      Theorem4MeasurableEndpointCurrentBoundsExactOneThresholdNonAcceptAllSelectionUnlessCertificate
        μ arrival m z switch12 switch21) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          ρ = acceptAllDynamicPolicy := by
  exact
    paper_theorem4_measurable_accept_all_unique_optimal_of_shape_replacement_statewise_improvements_unless
      μ arrival m z switch12 switch21
      (Theorem4MeasurableShapeReplacementStatewiseImprovementUnlessCertificate.of_endpoint_current_bounds_exact_one_threshold_non_accept_all_selection_unless
        μ arrival m z switch12 switch21 C)

/--
Theorem 4 endpoint from fixed-transfer exact one-threshold data.  The
replacement certificate supplies the Lemma 5 structural cases; the local
fixed-transfer certificate supplies the Lemma 9/10 endpoint improvements.
-/
theorem paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_theorem3_fixed_transfer_regular_exact_one_threshold_non_accept_all_selection_unless
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (Creplacement :
      Theorem4AllMeasurableOptimalShapeReplacementDerivationCertificate
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)))
    (C :
      Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularExactOneThresholdNonAcceptAllSelectionUnlessCertificate
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          ρ = acceptAllDynamicPolicy := by
  exact
    paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_exact_one_threshold_non_accept_all_selection_unless
      μ arrival m z switch12 switch21
      (C.to_endpoint_current_bounds_exact_one_threshold_non_accept_all_selection_unless
        Creplacement)

/--
Theorem 4 endpoint from the extended one-threshold aggregate-cross
fixed-transfer source package.  This is the closest compiled Theorem 4
frontier to the paper convention where an optimum may already be accept-all,
and otherwise has the finite one-threshold endpoint selected by the proof.
-/
theorem paper_theorem4_measurable_accept_all_unique_optimal_of_extended_one_threshold_branch_surge_cross_by_policy_form_fixed_transfer_source
    (μ : Fin 2 → Measure TripLength)
    (arrival m z : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (P :
      Theorem3AcceptAllStructuredPositiveParameterData
        μ arrival R1 R2 switch12 switch21 m z)
    (hR1_pos : 0 < R1)
    (hR1_lt_R2 : R1 < R2)
    (hR2_pos : 0 < R2)
    (hmeasure_nonsurge_acceptAll_pos : 0 < μ 0 acceptAllPolicy)
    (hmeasure_surge_acceptAll_pos : 0 < μ 1 acceptAllPolicy)
    (D :
      GN21Theorem3ExtendedOneThresholdBranchSurgeCrossByPolicyFormFixedTransferSourceExistenceData
        μ arrival R1 R2 switch12 switch21 m z) :
    dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
          ρ = acceptAllDynamicPolicy := by
  let S :=
    D.to_exact_one_threshold_non_accept_all_selection_unless
      P hR1_pos hR1_lt_R2 hR2_pos hmeasure_nonsurge_acceptAll_pos
      hmeasure_surge_acceptAll_pos
  exact
    paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_theorem3_fixed_transfer_regular_exact_one_threshold_non_accept_all_selection_unless
      μ arrival m z R1 R2 switch12 switch21 S.1.to_shape_replacements S.2

end

end GN21DriverSurgePricing
