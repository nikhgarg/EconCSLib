import GN21DriverSurgePricing.ProofInterface
import GN21DriverSurgePricing.Theorem3Frontier

/-!
# Paper Interface: Driver Surge Pricing

This file is the compact human-review surface for the GN21 driver surge-pricing
formalization.  It exposes the paper-facing definitions and named results while
leaving the full implementation ledger in `ProofInterface.lean`.
-/

open EconCSLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing
namespace PaperInterface

/-- Section 2.2: single-state incentive-compatibility predicate. -/
abbrev definition_single_state_ic := @singleStateIC

/-- Section 2.2: threshold-policy predicate. -/
abbrev definition_threshold_policy := @thresholdPolicy

/-- Proposition 3.1: affine single-state measurable IC endpoint. -/
abbrev proposition3_1_affine_single_state_ic :=
  @proposition3_1_affine_single_state_measurable_ic

/-- Theorem 1: single-state threshold best response. -/
abbrev theorem1_single_state_threshold_best_response :=
  @theorem1_single_state_threshold_best_response_measurable

/-- Lemma 5: fixed-response feasible policy form almost everywhere. -/
abbrev lemma5_fixed_response_policy_form :=
  @lemma5_fixed_response_feasible_policy_form_ae_of_response_shape

/-- Theorem 4: positive-response accept-all candidate from current bounds. -/
abbrev theorem4_positive_response_acceptAll_candidate :=
  @theorem4_positive_response_acceptAll_candidate_of_current_bounds_source

/-- Theorem 4: optimal-current-bounds accounting route. -/
abbrev theorem4_optimal_current_bounds_accounting :=
  @theorem4_optimal_current_bounds_source_of_optimal_accounting

/-- Theorem 4: optimal-current-bounds reward-rate route. -/
abbrev theorem4_optimal_current_bounds_reward_rate :=
  @theorem4_optimal_current_bounds_source_of_optimal_reward_rate

/-- Theorem 2: multiplicative extended policy shape. -/
abbrev theorem2_multiplicative_policy_shape :=
  @theorem2_multiplicative_extended_policy_shape_of_shape_derivation

/--
Theorem 2: measured multiplicative pricing is not dynamically incentive
compatible when a measured GN21 profitable-deviation witness is supplied.
-/
theorem theorem2_multiplicative_measured_not_ic_witness
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (m : Fin 2 → ℝ)
    (C :
      MultiplicativeMeasuredNotICCertificate
        mu arrival switch12 switch21 m) :
    ¬ dynamicIncentiveCompatible
      (gn21MeasuredDynamicRewardFunctional mu arrival switch12 switch21
        (fun i => multiplicativePricing (m i))) := by
  exact
    GN21DriverSurgePricing.paper_theorem2_multiplicative_measured_not_ic_of_witness
      mu arrival switch12 switch21 m C

/--
Theorem 2: a strict aggregate-primitives improvement for nondegenerate
measured multiplicative policies gives the dynamic non-IC conclusion.
-/
theorem theorem2_multiplicative_measured_not_ic_aggregate_witness
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (m : Fin 2 → ℝ)
    (C :
      MultiplicativeMeasuredAggregateNotICCertificate
        mu arrival switch12 switch21 m) :
    ¬ dynamicIncentiveCompatible
      (gn21MeasuredDynamicRewardFunctional mu arrival switch12 switch21
        (fun i => multiplicativePricing (m i))) := by
  exact
    GN21DriverSurgePricing.paper_theorem2_multiplicative_measured_not_ic_of_aggregate_witness
      mu arrival switch12 switch21 m C

/-- Lemma 9: non-surge current constraint feasibility. -/
abbrev lemma9_current_nonsurge_feasible :=
  @lemma9_constraint_set_feasible_for_current_nonsurge

/-- Lemma 10: surge current constraint feasibility. -/
abbrev lemma10_current_surge_feasible :=
  @lemma10_constraint_set_feasible_for_current_surge

/-- Theorem 3: feasibility threshold lies in `[0,1)`. -/
abbrev theorem3_feasibility_threshold :=
  @theorem3_feasibility_thresholdC_mem_Ico_acceptAll

/-- Theorem 3: positive-response measured IC source endpoint. -/
abbrev theorem3_positive_response :=
  @theorem3_structured_measurable_ic_ae_unique_of_positive_response_marginal_normalized_mass_ratio_source

/-- Theorem 3: current-bounds source-feasible endpoint. -/
abbrev theorem3_current_bounds_source_feasible :=
  @theorem3_structured_measurable_ic_ae_unique_of_current_bounds_source_feasible_normalized_mass_ratio_source

/-- Theorem 3: policy-canonical pointwise/reward-rate fixed-transfer endpoint. -/
abbrev theorem3_policy_canonical_pointwise_reward_rate :=
  @theorem3_structured_measurable_ic_ae_unique_of_policy_canonical_pointwise_reward_rate_source

/-- Theorem 3: feasible-policy-canonical pointwise/reward-rate endpoint. -/
abbrev theorem3_feasible_policy_canonical_pointwise_reward_rate :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_policy_canonical_pointwise_reward_rate_source

/-- Theorem 3: feasible-policy-canonical endpoint with paper ratio inputs. -/
abbrev theorem3_feasible_policy_canonical_pointwise_reward_rate_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_policy_canonical_pointwise_reward_rate_normalized_mass_ratio_source

/-- Theorem 3: endpoint-bridge route. -/
abbrev theorem3_endpoint_bridge :=
  @theorem3_structured_measurable_ic_of_endpoint_bridge_normalized_mass_ratio_source

/-- Theorem 3: normalized LightAE route from feasible Lemma 5 canonical data. -/
abbrev theorem3_light_ae_feasible_canonical_normalized :=
  @theorem3_measurable_ic_ae_unique_of_light_ae_feasible_canonical_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the normalized LightAE feasible-canonical route. -/
abbrev theorem3_light_ae_feasible_canonical_normalized_ic :=
  @theorem3_measurable_ic_of_light_ae_feasible_canonical_normalized_mass_ratio_source

/--
Theorem 3: finite-or-infinite branch route with aggregate cross-ratio endpoint
fields.  Use this when the proof has exact branch selectors for the current
policy representatives; otherwise prefer the LightAE feasible-canonical route.
-/
abbrev theorem3_finite_or_infinite_branch_surge_cross :=
  @theorem3_measurable_ic_ae_unique_of_finite_or_infinite_surge_cross_named_rate

/-- Theorem 3: IC projection of the finite-or-infinite aggregate-cross route. -/
abbrev theorem3_finite_or_infinite_branch_surge_cross_ic :=
  @theorem3_measurable_ic_of_finite_or_infinite_surge_cross_named_rate

/--
Theorem 3: small-surge source route with current Lemma 9 final-sign input.
-/
abbrev theorem3_small_surge_final_sign :=
  @theorem3_positive_mass_measurable_ic_of_small_surge_final_sign

/--
Theorem 3: preferred small-surge source route with selected-price interval
slack for the current non-surge policy.
-/
abbrev theorem3_small_surge_interval_final_sign :=
  @theorem3_positive_mass_measurable_ic_of_small_surge_interval_final_sign

/--
Theorem 3: mass-affine small-surge source route with selected-price interval
slack.
-/
abbrev theorem3_small_surge_mass_affine_interval_final_sign :=
  @theorem3_positive_mass_measurable_ic_of_small_surge_mass_affine_interval_final_sign

end PaperInterface
end GN21DriverSurgePricing
