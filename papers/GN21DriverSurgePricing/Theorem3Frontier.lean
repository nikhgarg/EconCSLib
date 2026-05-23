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

When Lemma 5 only identifies policy forms up to a.e. representatives, the
source-faithful boundary remains the fixed-response/bracket LightAE route in
`MainTheorems.lean`: it proves strict improvement on canonical representatives
and transfers back by a.e. congruence.  This frontier file adds a
feasible-canonical shortcut for sources that can provide the stronger
policy-level canonical-dominance data directly.  The finite-or-infinite
aggregate-cross route remains useful when the source proof really has exact
branch selectors for the current policy representatives.  It keeps the paper's
`t = infinity` non-surge convention, derives scalar ratio bookkeeping from
normalized trip-length laws, and asks for aggregate cross-ratio endpoint fields
rather than the misleading pointwise upper-transfer field.
-/

/--
Policy-level Lemma 5 canonical-dominance data instantiate the LightAE
middle-reroute existence boundary.  This is the representative/a.e. route to
use when Lemma 5 proves canonical replacements for every measurable optimum,
but does not justify exact pointwise finite-or-infinite branch syntax for the
original policy representative.
-/
noncomputable def GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData.of_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      Theorem4AllMeasurablePolicyCanonicalDominanceData μ
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)))
    (local_endpoint :
      Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteAELocalEndpointCertificate
        μ arrival R1 R2 switch12 switch21 m z) :
    GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z where
  replacement := D.to_allowed_replacement_data
  local_endpoint := local_endpoint

/--
Feasible-seed Lemma 5 canonical-dominance data instantiate the same LightAE
middle-reroute existence boundary.  This is usually the closest Lean target to
the continuous Lemma 5 proof, because the replacement policy is already paired
with feasibility and measurability of the updated dynamic policy.
-/
noncomputable def GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData.of_feasible_policy_canonical_dominance
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (D :
      Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData μ
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
          (ctmcStructuredDynamicSurgePrice m z switch12 switch21)))
    (local_endpoint :
      Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteAELocalEndpointCertificate
        μ arrival R1 R2 switch12 switch21 m z) :
    GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z where
  replacement := D.to_allowed_replacement_data
  local_endpoint := local_endpoint

/--
Per-price payload for the LightAE feasible-canonical frontier: Lemma 5
canonical dominance gives the replacement package, while the local endpoint
certificate supplies the fixed-state middle-reroute strict move.
-/
structure GN21Theorem3LightAEFeasibleCanonicalEndpointData
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ)
    (m z : Fin 2 → ℝ) where
  canonical :
    Theorem4AllMeasurableFeasiblePolicyCanonicalDominanceData μ
      (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
        (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
  local_endpoint :
    Theorem4MeasurableEndpointCurrentBoundsTheorem3FixedTransferRegularFixedStateEqDerivedTailMiddleRerouteAELocalEndpointCertificate
      μ arrival R1 R2 switch12 switch21 m z

/--
Theorem 3 on the normalized-mass LightAE route, with the per-price proof
payload stated as feasible Lemma 5 canonical dominance plus the fixed-state
middle-reroute endpoint certificate.  Use this shortcut only when the source
proof can supply the stronger policy-level canonical-dominance data directly;
otherwise use the fixed-response/bracket LightAE route that works with a.e.
representatives.
-/
theorem theorem3_measurable_ic_ae_unique_of_light_ae_feasible_canonical_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (endpoint_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3LightAEFeasibleCanonicalEndpointData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  exact
    paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_endpoint_theorem3_fixed_transfer_regular_allowed_replacement_fixed_state_eq_derived_tail_middle_reroute_light_ae_existence_normalized_mass_ratio_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
      hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hq1_integrable hq2_integrable
      hmass1_eq_one hmass2_eq_one
      (by
        intro m z hnonneg hparams
        let S := endpoint_selection m z hnonneg hparams
        exact
          GN21Theorem3MiddleRerouteLightAEEqSourceExistenceData.of_feasible_policy_canonical_dominance
            S.canonical S.local_endpoint)

/-- IC projection of the LightAE feasible-canonical normalized route. -/
theorem theorem3_measurable_ic_of_light_ae_feasible_canonical_normalized_mass_ratio_source
    (μ : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (μ 0)] [(μ 0).InnerRegularCompactLTTop]
    [IsFiniteMeasure (μ 1)] [(μ 1).InnerRegularCompactLTTop]
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (endpoint_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
          GN21Theorem3LightAEFeasibleCanonicalEndpointData
            μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 := by
  exact
    theorem3MeasuredStructuredMeasurableICConclusion_of_ae_unique
      (theorem3_measurable_ic_ae_unique_of_light_ae_feasible_canonical_normalized_mass_ratio_source
        μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
        hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
        htime1_integrable htime2_integrable hq1_integrable hq2_integrable
        hmass1_eq_one hmass2_eq_one endpoint_selection)

/--
Build the finite-or-infinite aggregate-cross named-rate package from fixed
reward-rate identities.  This keeps the source-facing Theorem 3 route on the
paper's reward-rate equations and derives the local Lemma 6 names internally.
-/
def GN21Theorem3FiniteOrInfiniteOneThresholdBranchSurgeCrossNamedRateSourceExistenceData.of_fixed_reward_rate_fields
    {μ : Fin 2 → Measure TripLength}
    {arrival m z : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (forms :
      Theorem4AllMeasurableGN21FixedResponsePolicyFormBracketSourceData
        μ arrival switch12 switch21 m z)
    (nonsurge_reject_long_finite_or_infinite :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        rejectsLongTripsFiniteOrInfiniteCutoff (ρ 0))
    (surge_reject_short_shape :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        ∃ u : ℝ, rejectsShortTrips u (ρ 1))
    (shared : GN21RegularEndpointSharedSourceData μ arrival switch12 switch21)
    (nonsurge_fixed_reward_rate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        gn21ScaledStateEarning (μ 0) (arrival 0)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 0)
            (ρ 0) =
          R1 * gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0))
    (surge_fixed_reward_rate :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
        gn21ScaledStateEarning (μ 1) (arrival 1)
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21 1)
            (ρ 1) =
          R2 * gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1))
    (surge_reject_short_cutoff_bound :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsShortTrips u (ρ 1) →
          0 < u →
            gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                (ρ 1) * u ≤
              gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                gn21SwitchProb switch21 switch12 u)
    (surge_reject_middle_ordered_upper_cutoff_bound :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        rejectsMiddleTrips lo hi (ρ 1) →
          lo ≤ hi →
            0 < hi →
              gn21ExitWeightIntegral (μ 1) (arrival 1) switch21 switch12
                  (ρ 1) * hi ≤
                gn21ScaledStateTime (μ 1) (arrival 1) (ρ 1) *
                  gn21SwitchProb switch21 switch12 hi)
    (nonsurge_reject_long_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ u : ℝ,
        rejectsLongTrips u (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21)
    (nonsurge_accept_middle_lower_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        acceptsMiddleTrips lo hi (ρ 0) →
          gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21 ≤
            gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0))
    (nonsurge_accept_middle_upper_cross :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal
          (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21
            (ctmcStructuredDynamicSurgePrice m z switch12 switch21))
          ρ →
      ∀ lo hi : ℝ,
        acceptsMiddleTrips lo hi (ρ 0) →
          gn21AcceptAllScaledStateTime (μ 0) (arrival 0) *
              gn21ExitWeightIntegral (μ 0) (arrival 0) switch12 switch21
                (ρ 0) ≤
            gn21ScaledStateTime (μ 0) (arrival 0) (ρ 0) *
              gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0)
                switch12 switch21) :
    GN21Theorem3FiniteOrInfiniteOneThresholdBranchSurgeCrossNamedRateSourceExistenceData
      μ arrival R1 R2 switch12 switch21 m z :=
  GN21Theorem3FiniteOrInfiniteOneThresholdBranchSurgeCrossNamedRateSourceExistenceData.of_surge_cutoff_bounds
    forms
    nonsurge_reject_long_finite_or_infinite
    surge_reject_short_shape
    shared
    (by
      intro ρ hopt
      exact
        (forms.nonsurge ρ hopt).Ri_eq_of_fixed_reward_rate
          (nonsurge_fixed_reward_rate ρ hopt))
    (by
      intro ρ hopt
      exact
        (forms.surge ρ hopt).Rj_eq_of_fixed_reward_rate
          (surge_fixed_reward_rate ρ hopt))
    surge_reject_short_cutoff_bound
    surge_reject_middle_ordered_upper_cutoff_bound
    nonsurge_reject_long_upper_cross
    nonsurge_accept_middle_lower_cross
    nonsurge_accept_middle_upper_cross

/--
Theorem 3 AE uniqueness on the finite-or-infinite aggregate-cross route.  Use
this branch-selection frontier when the proof has exact finite-cutoff or
accept-all selectors for the current policy representatives; use the LightAE
feasible-canonical route above when Lemma 5 supplies those forms only up to
a.e. representative replacement.
-/
theorem theorem3_measurable_ic_ae_unique_of_finite_or_infinite_surge_cross_named_rate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (named_rate_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
            GN21Theorem3FiniteOrInfiniteOneThresholdBranchSurgeCrossNamedRateSourceExistenceData
              μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  exact
    paper_theorem3_measured_structured_measurable_ic_ae_unique_prices_of_finite_or_infinite_one_threshold_branch_surge_cross_named_rate_normalized_mass_ratio_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos hC_lt_rho
      hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hq1_integrable hq2_integrable
      hmass1_eq_one hmass2_eq_one named_rate_selection

/-- IC projection of the finite-or-infinite aggregate-cross frontier. -/
theorem theorem3_measurable_ic_of_finite_or_infinite_surge_cross_named_rate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (hR1_eq : R1 = rho * R2)
    (hR2_pos : 0 < R2)
    (hC_lt_rho :
      theorem3FeasibilityThresholdC
          (gn21AcceptAllScaledStateTime (μ 0) (arrival 0))
          (gn21AcceptAllScaledStateTime (μ 1) (arrival 1))
          (gn21AcceptAllExitWeightIntegral (μ 0) (arrival 0) switch12 switch21)
          (gn21AcceptAllExitWeightIntegral (μ 1) (arrival 1) switch21 switch12)
          switch12 < rho)
    (hrho_lt_one : rho < 1)
    (harrival1_pos : 0 < arrival 0)
    (harrival2_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (htime1_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 0))
    (htime2_integrable :
      IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy (μ 1))
    (hq1_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch12 switch21 τ)
        acceptAllPolicy (μ 0))
    (hq2_integrable :
      IntegrableOn
        (fun τ : TripLength => gn21SwitchProb switch21 switch12 τ)
        acceptAllPolicy (μ 1))
    (hmass1_eq_one : singleStateTripMass (μ 0) acceptAllPolicy = 1)
    (hmass2_eq_one : singleStateTripMass (μ 1) acceptAllPolicy = 1)
    (named_rate_selection :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredPositiveParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
            GN21Theorem3FiniteOrInfiniteOneThresholdBranchSurgeCrossNamedRateSourceExistenceData
              μ arrival R1 R2 switch12 switch21 m z) :
    theorem3MeasuredStructuredMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 := by
  exact
    theorem3MeasuredStructuredMeasurableICConclusion_of_ae_unique
      (theorem3_measurable_ic_ae_unique_of_finite_or_infinite_surge_cross_named_rate
        μ arrival rho R1 R2 switch12 switch21 hR1_eq hR2_pos
        hC_lt_rho hrho_lt_one harrival1_pos harrival2_pos hswitch12_pos
        hswitch21_pos htime1_integrable htime2_integrable hq1_integrable
        hq2_integrable hmass1_eq_one hmass2_eq_one named_rate_selection)

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
