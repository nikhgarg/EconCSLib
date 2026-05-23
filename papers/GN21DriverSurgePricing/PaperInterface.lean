import GN21DriverSurgePricing.ProofInterface
import GN21DriverSurgePricing.Lemma5Frontier
import GN21DriverSurgePricing.Theorem4Frontier
import GN21DriverSurgePricing.Theorem3Frontier
import GN21DriverSurgePricing.Theorem2ExplicitInstance

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

/-- Theorem 4: measurable structural forms from allowed Lemma 5 policy forms. -/
abbrev theorem4_structural_policy_forms_of_allowed_policy_forms :=
  @paper_theorem4_measurable_dynamic_structural_policy_of_allowed_policy_forms

/-- Theorem 4: measurable structural forms from source-style Lemma 5 replacements. -/
abbrev theorem4_structural_policy_forms_of_allowed_replacement_data :=
  @paper_theorem4_measurable_dynamic_structural_policy_of_allowed_replacement_data

/-- Theorem 4: measurable structural forms from feasible canonical dominance. -/
abbrev theorem4_structural_policy_forms_of_feasible_policy_canonical_dominance :=
  @paper_theorem4_measurable_dynamic_structural_policy_of_feasible_policy_canonical_dominance

/-- Theorem 4: a.e. structural representatives from feasible Lemma 5 forms. -/
abbrev theorem4_structural_policy_representatives_of_feasible_ae_policy_forms :=
  @paper_theorem4_measurable_dynamic_structural_policy_representatives_of_feasible_ae_policy_forms

/-- Theorem 4: a.e. structural representatives from source-style Lemma 5 replacements. -/
abbrev theorem4_structural_policy_representatives_of_allowed_replacement_data :=
  @paper_theorem4_measurable_dynamic_structural_policy_representatives_of_allowed_replacement_data

/-- Theorem 4: a.e. structural representatives from feasible canonical dominance. -/
abbrev theorem4_structural_policy_representatives_of_feasible_policy_canonical_dominance :=
  @paper_theorem4_measurable_dynamic_structural_policy_representatives_of_feasible_policy_canonical_dominance

/-- Theorem 4: a.e. structural representatives from fixed-response shape data. -/
abbrev theorem4_structural_policy_representatives_of_fixed_response_shape_data :=
  @paper_theorem4_measurable_dynamic_structural_policy_representatives_of_fixed_response_shape_data

/-- Theorem 4: a.e. structural representatives from fixed-response policy forms. -/
abbrev theorem4_structural_policy_representatives_of_fixed_response_policy_forms :=
  @paper_theorem4_measurable_dynamic_structural_policy_representatives_of_fixed_response_policy_forms

/-- Theorem 4: a.e. representatives from frozen-state positive-affine Lemma 5 data. -/
abbrev theorem4_structural_policy_representatives_of_dynamic_state_positive_affine_policy_forms :=
  @paper_theorem4_measurable_dynamic_structural_policy_representatives_of_dynamic_state_positive_affine_policy_forms

/-- Theorem 4: a.e. structural representatives from GN21 fixed-response source data. -/
abbrev theorem4_structural_policy_representatives_of_gn21_fixed_response_source_data :=
  @paper_theorem4_measurable_dynamic_structural_policy_representatives_of_gn21_fixed_response_source_data

/-- Theorem 4: a.e. structural representatives from raw GN21 bracket source data. -/
abbrev theorem4_structural_policy_representatives_of_gn21_bracket_source_data :=
  @paper_theorem4_measurable_dynamic_structural_policy_representatives_of_gn21_bracket_source_data

/--
Theorem 4: structural forms from the measured marginal objective obtained by
freezing the other CTMC state.
-/
abbrev theorem4_structural_policy_forms_of_gn21_marginal_feasible_policy_canonical_dominance :=
  @paper_theorem4_measurable_dynamic_structural_policy_of_gn21_marginal_feasible_policy_canonical_dominance

/--
Theorem 4: a.e. structural representatives from the measured marginal
objective obtained by freezing the other CTMC state.
-/
abbrev theorem4_structural_policy_representatives_of_gn21_marginal_feasible_policy_canonical_dominance :=
  @paper_theorem4_measurable_dynamic_structural_policy_representatives_of_gn21_marginal_feasible_policy_canonical_dominance

/--
Theorem 4: structural forms from fixed-response source data for the actual
measured marginal Lemma 5 objective.
-/
abbrev theorem4_structural_policy_forms_of_gn21_fixed_response_marginal :=
  @paper_theorem4_measurable_dynamic_structural_policy_of_gn21_fixed_response_marginal_policy_canonical_dominance

/--
Theorem 4: a.e. structural representatives from fixed-response source data for
the actual measured marginal Lemma 5 objective.
-/
abbrev theorem4_structural_policy_representatives_of_gn21_fixed_response_marginal :=
  @paper_theorem4_measurable_dynamic_structural_policy_representatives_of_gn21_fixed_response_marginal_policy_canonical_dominance

/--
Theorem 4: structural forms from GN21 fixed-response source data plus
positive-affine continuation-objective transfer.
-/
abbrev theorem4_structural_policy_forms_of_gn21_fixed_response_positive_affine :=
  @paper_theorem4_measurable_dynamic_structural_policy_of_gn21_fixed_response_policy_canonical_dominance_positive_affine

/--
Theorem 4: a.e. structural representatives from GN21 fixed-response source
data plus positive-affine continuation-objective transfer.
-/
abbrev theorem4_structural_policy_representatives_of_gn21_fixed_response_positive_affine :=
  @paper_theorem4_measurable_dynamic_structural_policy_representatives_of_gn21_fixed_response_policy_canonical_dominance_positive_affine

/-- Theorem 4: accept-all structural representatives from positive-response optima. -/
abbrev theorem4_acceptAll_structural_representatives_of_positive_response_marginal :=
  @paper_theorem4_measurable_dynamic_accept_all_structural_representatives_of_positive_response_marginal_optima

/-- Theorem 4: accept-all structural representatives from accept-all candidate comparisons. -/
abbrev theorem4_acceptAll_structural_representatives_of_positive_response_candidates :=
  @paper_theorem4_measurable_dynamic_accept_all_structural_representatives_of_positive_response_acceptAll_candidates

/-- Theorem 4: optimal-current-bounds accounting route. -/
abbrev theorem4_optimal_current_bounds_accounting :=
  @theorem4_optimal_current_bounds_source_of_optimal_accounting

/-- Theorem 4: optimal-current-bounds reward-rate route. -/
abbrev theorem4_optimal_current_bounds_reward_rate :=
  @theorem4_optimal_current_bounds_source_of_optimal_reward_rate

/-- Theorem 4: positive-response accept-all candidate from optimal current bounds. -/
abbrev theorem4_positive_response_acceptAll_candidate_optimal_current_bounds :=
  @theorem4_positive_response_acceptAll_candidate_of_optimal_current_bounds_source

/-- Theorem 4: accept-all structural representatives from optimal current bounds. -/
abbrev theorem4_acceptAll_structural_representatives_of_optimal_current_bounds :=
  @paper_theorem4_measurable_dynamic_accept_all_structural_representatives_of_structured_current_bounds_optimal_source_positive_response

/-- Theorem 4: accept-all structural representatives from reward-rate current bounds. -/
abbrev theorem4_acceptAll_structural_representatives_of_optimal_reward_rate :=
  @paper_theorem4_measurable_dynamic_accept_all_structural_representatives_of_structured_current_bounds_optimal_reward_rate_positive_response

/--
Theorem 4: accept-all unique optimality from exact one-threshold endpoint
selection with accept-all escape branches.
-/
abbrev theorem4_acceptAll_unique_exact_one_threshold_non_accept_all_endpoint :=
  @paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_current_bounds_exact_one_threshold_non_accept_all_selection_unless

/--
Theorem 4: accept-all unique optimality from fixed-transfer exact
one-threshold endpoint data.
-/
abbrev theorem4_acceptAll_unique_fixed_transfer_exact_one_threshold_non_accept_all_endpoint :=
  @paper_theorem4_measurable_accept_all_unique_optimal_of_endpoint_theorem3_fixed_transfer_regular_exact_one_threshold_non_accept_all_selection_unless

/--
Theorem 4: accept-all unique optimality from extended one-threshold
aggregate-cross fixed-transfer source data.
-/
abbrev theorem4_acceptAll_unique_extended_one_threshold_surge_cross_source :=
  @paper_theorem4_measurable_accept_all_unique_optimal_of_extended_one_threshold_branch_surge_cross_by_policy_form_fixed_transfer_source

/--
Theorem 4: a.e.-unique accept-all optimality from feasible a.e. Lemma 5
representatives and positive-rejected-mass endpoint moves.
-/
abbrev theorem4_acceptAll_ae_unique_feasible_ae_representative_rejected_mass :=
  @paper_theorem4_measurable_accept_all_ae_unique_optimal_of_feasible_ae_forms_and_representative_rejected_mass_improvements_from_exists

/--
Theorem 4: a.e.-unique accept-all optimality from fixed-response Lemma 5
policy forms and positive-rejected-mass endpoint moves.
-/
abbrev theorem4_acceptAll_ae_unique_fixed_response_representative_rejected_mass :=
  @paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_forms_and_representative_rejected_mass_improvements_from_exists

/--
Theorem 4: a.e.-unique accept-all optimality from raw GN21 bracket
fixed-response source data and positive-rejected-mass endpoint moves.
-/
abbrev theorem4_acceptAll_ae_unique_gn21_bracket_representative_rejected_mass :=
  @paper_theorem4_measurable_accept_all_ae_unique_optimal_of_gn21_bracket_source_data_and_representative_rejected_mass_improvements_from_exists

/--
Theorem 4: a.e.-unique accept-all optimality from the by-policy-form
middle-reroute fixed-transfer source package for a fixed structured price.
-/
abbrev theorem4_acceptAll_ae_unique_middle_reroute_policy_form_source_existence :=
  @paper_theorem4_measurable_accept_all_ae_unique_optimal_of_middle_reroute_ae_policy_form_source_existence

/--
Theorem 4: a.e.-unique accept-all optimality from the lighter common
fixed-state-equality middle-reroute source package for a fixed structured
price.
-/
abbrev theorem4_acceptAll_ae_unique_middle_reroute_light_eq_source_existence :=
  @paper_theorem4_measurable_accept_all_ae_unique_optimal_of_middle_reroute_light_ae_eq_source_existence

/--
Theorem 4: a.e.-unique accept-all optimality from feasible-canonical Lemma 5
data plus the local LightAE middle-reroute endpoint certificate.
-/
abbrev theorem4_acceptAll_ae_unique_light_ae_feasible_canonical_endpoint :=
  @paper_theorem4_measurable_accept_all_ae_unique_optimal_of_light_ae_feasible_canonical_endpoint

/--
Theorem 4: a.e.-unique accept-all optimality from fixed-response policy forms
and common fixed-state-equality middle-reroute endpoint data.
-/
abbrev theorem4_acceptAll_ae_unique_fixed_response_eq_middle_reroute :=
  @paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_form_eq_middle_reroute_source_existence

/--
Theorem 4: a.e.-unique accept-all optimality from one-threshold fixed-response
source data and common fixed-state-equality middle-reroute endpoint data.
-/
abbrev theorem4_acceptAll_ae_unique_fixed_response_one_threshold_eq_middle_reroute :=
  @paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_one_threshold_eq_middle_reroute_source_existence

/--
Theorem 4: a.e.-unique accept-all optimality from bracket-level one-threshold
fixed-response source data and common fixed-state-equality middle-reroute
endpoint data.
-/
abbrev theorem4_acceptAll_ae_unique_fixed_response_bracket_eq_middle_reroute :=
  @paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_one_threshold_bracket_eq_middle_reroute_source_existence

/--
Theorem 4: a.e.-unique accept-all optimality from fixed-response policy forms
and the by-policy-form middle-cutoff-reroute endpoint boundary.
-/
abbrev theorem4_acceptAll_ae_unique_fixed_response_by_policy_form_middle_cutoff :=
  @paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_form_by_policy_form_middle_cutoff_reroute_source_existence

/--
Theorem 4: a.e.-unique accept-all optimality from fixed-response policy forms
and the aggregate fixed-surge cross-ratio middle-cutoff-reroute boundary.
-/
abbrev theorem4_acceptAll_ae_unique_fixed_response_surge_cross_middle_cutoff :=
  @paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_form_surge_cross_by_policy_form_middle_cutoff_reroute_source_existence

/--
Theorem 4: a.e.-unique accept-all optimality from fixed-response policy forms
and the scalar surge-cutoff middle-cutoff-reroute boundary.
-/
abbrev theorem4_acceptAll_ae_unique_fixed_response_surge_cutoff_middle_cutoff :=
  @paper_theorem4_measurable_accept_all_ae_unique_optimal_of_fixed_response_policy_form_surge_cutoff_by_policy_form_middle_cutoff_reroute_source_existence

/--
Theorem 4: accept-all structural representatives from the source-ordered
sequential Lemma 9 then Lemma 10 reward-rate route.
-/
theorem theorem4_acceptAll_structural_representatives_of_sequential_optimal_reward_rate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ)
    (C :
      Theorem4MeasuredAggregateStructuredSequentialOptimalRewardRatePositiveResponseCertificate
        μ arrival R1 R2 switch12 switch21 m z) :
    ∃ ρstar : Fin 2 → TripPolicy,
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
        ρstar ∧
        (∃ σstar : TripPolicy,
          theorem4NonsurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 0) (ρstar 0) σstar) ∧
        (∃ σstar : TripPolicy,
          theorem4SurgeShape σstar ∧
            policyAlmostEverywhereEq (μ 1) (ρstar 1) σstar) ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicMeasurableOptimal
            (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
              (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
            ρ →
          (∃ σstar : TripPolicy,
            theorem4NonsurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 0) (ρ 0) σstar) ∧
          (∃ σstar : TripPolicy,
            theorem4SurgeShape σstar ∧
              policyAlmostEverywhereEq (μ 1) (ρ 1) σstar) := by
  exact
    GN21DriverSurgePricing.paper_theorem4_measurable_dynamic_accept_all_structural_representatives_of_acceptAll_ae_unique
      μ
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
      (GN21DriverSurgePricing.paper_theorem4_measurable_accept_all_ae_unique_optimal_of_structured_sequential_optimal_reward_rate_positive_response
        μ arrival R1 R2 switch12 switch21 m z C)

/-- Theorem 2: multiplicative extended policy shape. -/
abbrev theorem2_multiplicative_policy_shape :=
  @theorem2_multiplicative_extended_policy_shape_of_shape_derivation

/-- Theorem 2: one-threshold CTMC policy shape from raw GN21 bracket source data. -/
abbrev theorem2_one_threshold_policy_shape_ae_of_gn21_bracket_source_data :=
  @paper_theorem2_one_threshold_measurable_policy_shape_ae_of_gn21_bracket_source_data

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

/--
Theorem 2: explicit atomic measured counterexample showing multiplicative
pricing is not dynamically incentive compatible.
-/
abbrev theorem2_multiplicative_measured_not_ic_explicit_atomic :=
  @paper_theorem2_multiplicative_measured_not_ic_explicit_atomic

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

/-- Theorem 3: positive fixed-response source endpoint. -/
abbrev theorem3_positive_fixed_response_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_positive_fixed_response_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the positive fixed-response endpoint. -/
abbrev theorem3_positive_fixed_response_normalized_ic :=
  @theorem3_structured_measurable_ic_of_positive_fixed_response_normalized_mass_ratio_source

/-- Theorem 3: current-bounds source-feasible endpoint. -/
abbrev theorem3_current_bounds_source_feasible :=
  @theorem3_structured_measurable_ic_ae_unique_of_current_bounds_source_feasible_normalized_mass_ratio_source

/-- Theorem 3: current-bounds route through the positive-response Lemma 5 branch. -/
abbrev theorem3_current_bounds_source_positive_response :=
  @theorem3_structured_measurable_ic_ae_unique_of_current_bounds_source_positive_response

/-- Theorem 3: split route, weak feasible IC plus optimal-policy positive response. -/
abbrev theorem3_feasible_weak_reward_optimal_positive_response :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_weak_reward_and_optimal_positive_response_source

/-- Theorem 3: ratio-source split positive-response route. -/
abbrev theorem3_feasible_weak_reward_optimal_positive_response_ratio :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_weak_reward_and_optimal_positive_response_ratio_source

/-- Theorem 3: normalized-mass split positive-response route. -/
abbrev theorem3_feasible_weak_reward_optimal_positive_response_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_weak_reward_and_optimal_positive_response_normalized_mass_ratio_source

/-- Theorem 3: positive-mass source-domain IC/a.e. uniqueness route. -/
abbrev theorem3_positive_mass_source :=
  @theorem3_positive_mass_measurable_ic_ae_unique_of_source_assumptions

/--
Theorem 3: reusable lift from positive-mass a.e. uniqueness to the full
measurable domain when zero-mass strict dominance is supplied.
-/
abbrev theorem3_positive_mass_to_full_with_zero_mass_dominance :=
  @theorem3MeasuredStructuredMeasurableICAEUniqueConclusion_of_positiveMass_ae_unique_and_zeroMassStrictDominance

/--
Theorem 3 zero-mass boundary: with the current real-valued reward
totalization, a left-empty/right-accept-all policy can beat accept-all when
the right accept-all state reward rate exceeds the full accept-all dynamic
reward.
-/
abbrev theorem3_zero_mass_totalization_obstruction :=
  @gn21MeasuredDynamicReward_left_empty_acceptAll_gt_acceptAll_of_right_rewardRate_gt

/-- Theorem 3: full measurable route from source assumptions plus zero-mass dominance. -/
abbrev theorem3_source_with_zero_mass_dominance :=
  @theorem3_measurable_ic_ae_unique_of_source_assumptions_and_zero_mass_dominance

/-- Theorem 3: legacy positive-mass route with an explicit marginal-response certificate. -/
abbrev theorem3_positive_mass_source_positive_response :=
  @theorem3_positive_mass_measurable_ic_ae_unique_of_source_and_positive_response_marginal

/-- Theorem 3: normalized split route with optimal-policy accounting data. -/
abbrev theorem3_feasible_weak_reward_optimal_accounting_positive_response_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_weak_reward_and_optimal_accounting_positive_response_normalized_mass_ratio_source

/-- Theorem 3: normalized split route with optimal-policy reward-rate data. -/
abbrev theorem3_feasible_weak_reward_optimal_reward_rate_positive_response_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_weak_reward_and_optimal_reward_rate_positive_response_normalized_mass_ratio_source

/-- Theorem 3: source current-bounds split into feasible and optimal-response data. -/
abbrev theorem3_current_bounds_source_feasible_optimal_positive_response_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_current_bounds_source_feasible_and_optimal_positive_response_normalized_mass_ratio_source

/-- Theorem 3: accounting current-bounds split into feasible and optimal-response data. -/
abbrev theorem3_current_bounds_accounting_feasible_optimal_positive_response_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_current_bounds_accounting_feasible_and_optimal_positive_response_normalized_mass_ratio_source

/-- Theorem 3: reward-rate current-bounds split into feasible and optimal-response data. -/
abbrev theorem3_current_bounds_reward_rate_feasible_optimal_positive_response_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_current_bounds_reward_rate_feasible_and_optimal_positive_response_normalized_mass_ratio_source

/-- Theorem 3: source-ordered sequential optimal reward-rate positive-response route. -/
abbrev theorem3_feasible_weak_reward_sequential_optimal_reward_rate_positive_response_normalized :=
  @GN21DriverSurgePricing.paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_feasible_weak_reward_and_sequential_optimal_reward_rate_positive_response_normalized_mass_ratio_source_assumptions

/-- Theorem 3: source-ordered optimal-only sequential source-data route. -/
abbrev theorem3_feasible_weak_reward_sequential_optimal_source_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_weak_reward_and_sequential_optimal_source_normalized_mass_ratio_source

/-- Theorem 3: source-ordered feasible sequential current-bounds route. -/
abbrev theorem3_feasible_weak_reward_feasible_sequential_source_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_weak_reward_and_feasible_sequential_source_normalized_mass_ratio_source

/-- Theorem 3: full source-data feasible sequential current-bounds route. -/
abbrev theorem3_feasible_sequential_current_bounds_source_data :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_sequential_current_bounds_source_data

/-- Theorem 3: sequential surge-source route after Lemma 10 construction. -/
abbrev theorem3_feasible_sequential_surge_source_data :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_sequential_surge_source_data

/-- Theorem 3: accounting-form sequential surge-source route. -/
abbrev theorem3_feasible_sequential_surge_accounting_data :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_sequential_surge_accounting_data

/-- Theorem 3: reward-rate-form sequential surge-source route. -/
abbrev theorem3_feasible_sequential_surge_reward_rate_data :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_sequential_surge_reward_rate_data

/-- Theorem 3: optimal-only sequential surge-source route. -/
abbrev theorem3_optimal_sequential_surge_source_data :=
  @theorem3_structured_measurable_ic_ae_unique_of_optimal_sequential_surge_source_data

/-- Theorem 3: optimal-only accounting-form sequential surge-source route. -/
abbrev theorem3_optimal_sequential_surge_accounting_data :=
  @theorem3_structured_measurable_ic_ae_unique_of_optimal_sequential_surge_accounting_data

/-- Theorem 3: optimal-only reward-rate-form sequential surge-source route. -/
abbrev theorem3_optimal_sequential_surge_reward_rate_data :=
  @theorem3_structured_measurable_ic_ae_unique_of_optimal_sequential_surge_reward_rate_data

/-- Theorem 3: optimal-only sequential surge route with zero-mass dominance. -/
abbrev theorem3_optimal_sequential_surge_source_data_zero_mass_bridge :=
  @theorem3_structured_measurable_ic_ae_unique_of_optimal_sequential_surge_source_data_zero_mass_bridge

/-- Theorem 3: optimal-only accounting sequential surge route with zero-mass dominance. -/
abbrev theorem3_optimal_sequential_surge_accounting_data_zero_mass_bridge :=
  @theorem3_structured_measurable_ic_ae_unique_of_optimal_sequential_surge_accounting_data_zero_mass_bridge

/-- Theorem 3: optimal-only reward-rate sequential surge route with zero-mass dominance. -/
abbrev theorem3_optimal_sequential_surge_reward_rate_data_zero_mass_bridge :=
  @theorem3_structured_measurable_ic_ae_unique_of_optimal_sequential_surge_reward_rate_data_zero_mass_bridge

/-- Theorem 3: current-bounds accounting endpoint. -/
abbrev theorem3_current_bounds_accounting :=
  @theorem3_structured_measurable_ic_ae_unique_of_current_bounds_accounting

/-- Theorem 3: current-bounds reward-rate endpoint. -/
abbrev theorem3_current_bounds_reward_rate :=
  @theorem3_structured_measurable_ic_ae_unique_of_current_bounds_reward_rate

/-- Theorem 3: normalized accounting current-bounds endpoint. -/
abbrev theorem3_current_bounds_accounting_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_current_bounds_accounting_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the normalized accounting endpoint. -/
abbrev theorem3_current_bounds_accounting_normalized_ic :=
  @theorem3_structured_measurable_ic_of_current_bounds_accounting_normalized_mass_ratio_source

/-- Theorem 3: normalized reward-rate current-bounds endpoint. -/
abbrev theorem3_current_bounds_reward_rate_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_current_bounds_reward_rate_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the normalized reward-rate endpoint. -/
abbrev theorem3_current_bounds_reward_rate_normalized_ic :=
  @theorem3_structured_measurable_ic_of_current_bounds_reward_rate_normalized_mass_ratio_source

/-- Theorem 3: policy-canonical pointwise/reward-rate fixed-transfer endpoint. -/
abbrev theorem3_policy_canonical_pointwise_reward_rate :=
  @theorem3_structured_measurable_ic_ae_unique_of_policy_canonical_pointwise_reward_rate_source

/-- Theorem 3: feasible-policy-canonical pointwise/reward-rate endpoint. -/
abbrev theorem3_feasible_policy_canonical_pointwise_reward_rate :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_policy_canonical_pointwise_reward_rate_source

/-- Theorem 3: feasible-policy-canonical endpoint with paper ratio inputs. -/
abbrev theorem3_feasible_policy_canonical_pointwise_reward_rate_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_feasible_policy_canonical_pointwise_reward_rate_normalized_mass_ratio_source

/-- Theorem 3: feasible-policy-canonical representative route with paper ratio inputs. -/
abbrev theorem3_feasible_policy_canonical_representative_normalized :=
  @theorem3_measurable_ic_ae_unique_of_feasible_policy_canonical_representative_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the feasible-policy-canonical representative route. -/
abbrev theorem3_feasible_policy_canonical_representative_normalized_ic :=
  @theorem3_measurable_ic_of_feasible_policy_canonical_representative_normalized_mass_ratio_source

/-- Theorem 3: endpoint-bridge route. -/
abbrev theorem3_endpoint_bridge :=
  @theorem3_structured_measurable_ic_of_endpoint_bridge_normalized_mass_ratio_source

/-- Theorem 3: normalized LightAE shortcut from feasible Lemma 5 canonical data. -/
abbrev theorem3_light_ae_feasible_canonical_normalized :=
  @theorem3_measurable_ic_ae_unique_of_light_ae_feasible_canonical_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the normalized feasible-canonical shortcut. -/
abbrev theorem3_light_ae_feasible_canonical_normalized_ic :=
  @theorem3_measurable_ic_of_light_ae_feasible_canonical_normalized_mass_ratio_source

/-- Theorem 3: bracket fixed-response LightAE representative route. -/
abbrev theorem3_light_ae_bracket_fixed_response_ratio :=
  @theorem3_structured_measurable_ic_ae_unique_of_bracket_eq_middle_reroute_existence_ratio_source

/-- Theorem 3: IC projection of the bracket fixed-response LightAE route. -/
abbrev theorem3_light_ae_bracket_fixed_response_ratio_ic :=
  @theorem3_structured_measurable_ic_of_bracket_eq_middle_reroute_existence_ratio_source

/-- Theorem 3: normalized-mass bracket fixed-response LightAE route. -/
abbrev theorem3_light_ae_bracket_fixed_response_normalized :=
  @theorem3_measurable_ic_ae_unique_of_bracket_light_ae_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the normalized bracket fixed-response route. -/
abbrev theorem3_light_ae_bracket_fixed_response_normalized_ic :=
  @theorem3_measurable_ic_of_bracket_light_ae_normalized_mass_ratio_source

/-- Theorem 3: normalized bracket middle-cutoff fixed-state-equality LightAE route. -/
abbrev theorem3_light_ae_bracket_middle_cutoff_fixed_state_eq_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_bracket_eq_middle_cutoff_fixed_state_eq_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the normalized middle-cutoff fixed-state-equality route. -/
abbrev theorem3_light_ae_bracket_middle_cutoff_fixed_state_eq_normalized_ic :=
  @theorem3_structured_measurable_ic_of_bracket_eq_middle_cutoff_fixed_state_eq_normalized_mass_ratio_source

/-- Theorem 3: normalized bracket middle-cutoff named-rate LightAE route. -/
abbrev theorem3_light_ae_bracket_middle_cutoff_named_rate_normalized :=
  @theorem3_structured_measurable_ic_ae_unique_of_bracket_eq_middle_cutoff_fixed_state_named_rate_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the normalized middle-cutoff named-rate route. -/
abbrev theorem3_light_ae_bracket_middle_cutoff_named_rate_normalized_ic :=
  @theorem3_structured_measurable_ic_of_bracket_eq_middle_cutoff_fixed_state_named_rate_normalized_mass_ratio_source

/-- Theorem 3: normalized bracket aggregate-cross middle-cutoff LightAE route. -/
abbrev theorem3_light_ae_bracket_surge_cross_middle_cutoff_normalized :=
  @theorem3_measurable_ic_ae_unique_of_bracket_surge_cross_middle_cutoff_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the normalized aggregate-cross middle-cutoff route. -/
abbrev theorem3_light_ae_bracket_surge_cross_middle_cutoff_normalized_ic :=
  @theorem3_measurable_ic_of_bracket_surge_cross_middle_cutoff_normalized_mass_ratio_source

/--
Theorem 3: reduced bracket surge-cutoff route.  The non-surge accept-middle
cross fields are derived from the a.e. reject-long representative; the
remaining non-surge source field is the reject-long upper cross comparison.
-/
abbrev theorem3_light_ae_bracket_surge_cutoff_reject_long_upper_normalized :=
  @theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_reject_long_upper_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the reduced bracket surge-cutoff route. -/
abbrev theorem3_light_ae_bracket_surge_cutoff_reject_long_upper_normalized_ic :=
  @theorem3_measurable_ic_of_bracket_surge_cutoff_reject_long_upper_normalized_mass_ratio_source

/--
Theorem 3: reduced bracket route with fixed reward-rate identities replacing
local `Ri`/`Rj` name equalities.
-/
abbrev theorem3_light_ae_bracket_surge_cutoff_fixed_reward_rate_reject_long_upper_normalized :=
  @theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_fixed_reward_rate_reject_long_upper_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the fixed-reward-rate reduced bracket route. -/
abbrev theorem3_light_ae_bracket_surge_cutoff_fixed_reward_rate_reject_long_upper_normalized_ic :=
  @theorem3_measurable_ic_of_bracket_surge_cutoff_fixed_reward_rate_reject_long_upper_normalized_mass_ratio_source

/-- Theorem 3: bracket ordered cross-field source data lowered through the LightAE route. -/
abbrev theorem3_light_ae_bracket_ordered_cross_field_normalized :=
  @theorem3_measurable_ic_ae_unique_of_bracket_ordered_cross_field_light_ae_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the bracket ordered cross-field LightAE route. -/
abbrev theorem3_light_ae_bracket_ordered_cross_field_normalized_ic :=
  @theorem3_measurable_ic_of_bracket_ordered_cross_field_light_ae_normalized_mass_ratio_source

/-- Theorem 3: exact bracket branch source data lowered through the LightAE route. -/
abbrev theorem3_light_ae_exact_bracket_branch_normalized :=
  @theorem3_measurable_ic_ae_unique_of_exact_bracket_branch_light_ae_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the exact bracket branch LightAE route. -/
abbrev theorem3_light_ae_exact_bracket_branch_normalized_ic :=
  @theorem3_measurable_ic_of_exact_bracket_branch_light_ae_normalized_mass_ratio_source

/--
Theorem 3: reduced bracket surge-cutoff route from one-sided pointwise upper
transfer on rejected non-surge trips.
-/
abbrev theorem3_light_ae_bracket_surge_cutoff_pointwise_upper_normalized :=
  @theorem3_measurable_ic_ae_unique_of_bracket_surge_cutoff_pointwise_upper_normalized_mass_ratio_source

/-- Theorem 3: IC projection of the reduced pointwise-upper route. -/
abbrev theorem3_light_ae_bracket_surge_cutoff_pointwise_upper_normalized_ic :=
  @theorem3_measurable_ic_of_bracket_surge_cutoff_pointwise_upper_normalized_mass_ratio_source

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

/--
Theorem 3: normalized no-`Rmax` mass-affine route with a current Lemma 9
final-sign input.
-/
abbrev theorem3_small_surge_mass_affine_current_final_sign_no_rmax_normalized :=
  @paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_small_surge_mass_affine_current_lower_final_sign_no_rmax_normalized_mass_data_assumptions

/--
Theorem 3: normalized no-`Rmax` mass-affine route using the fixed-state
lower-cross comparison instead of a current final-sign input.
-/
abbrev theorem3_small_surge_mass_affine_fixed_lower_cross_no_rmax_normalized :=
  @theorem3_positive_mass_measurable_ic_of_small_surge_mass_affine_fixed_lower_cross_no_rmax_normalized_mass

/--
Theorem 3: normalized no-`Rmax` mass-affine fixed-lower-cross route with the
accept-all lower endpoint derived from the paper's final-sign inequality.
-/
abbrev theorem3_small_surge_mass_affine_fixed_lower_cross_final_sign_no_rmax_normalized :=
  @theorem3_positive_mass_measurable_ic_of_small_surge_mass_affine_fixed_lower_cross_final_sign_no_rmax_normalized_mass

end PaperInterface
end GN21DriverSurgePricing
