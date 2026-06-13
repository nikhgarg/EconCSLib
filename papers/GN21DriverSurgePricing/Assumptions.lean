import GN21DriverSurgePricing.InterfaceAliases

/-!
# Paper Assumptions: GN21 Driver Surge Pricing

This file records source-domain and theorem-condition premises exposed by the
compact review surface. Most are positivity, finite-mass, switch-rate, and
defined-reward side conditions that the source paper uses implicitly in CTMC
and reward-rate formulas.
-/

namespace GN21DriverSurgePricing

open MeasureTheory

/-- Affine single-state pricing parameter domain. -/
-- audit-premise: hlambda : 0 < arrivalRate
-- audit-premise: ha_nonneg : 0 ≤ a
-- audit-premise: ha_le_wait_value : a ≤ m / arrivalRate
abbrev assumption_affine_single_state_parameter_domain
    (arrivalRate m a : ℝ) : Prop :=
  0 < arrivalRate ∧ 0 ≤ a ∧ a ≤ m / arrivalRate

/-- Single-state reward/threshold domain for Theorem 1's nontrivial payout branch. -/
-- audit-premise: hrate_nonneg : ∀ tau : TripLength, 0 < tau → 0 ≤ w tau / tau
-- audit-premise: hrate_nonneg : ∀ τ : TripLength, 0 < τ → 0 ≤ w τ / τ
-- audit-premise: hfinite_acceptAll : mu acceptAllPolicy ≠ ⊤
-- audit-premise: hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤
-- audit-premise: hpositive_payout_mass : 0 < mu {τ : TripLength | τ ∈ acceptAllPolicy ∧ 0 < w τ}
-- audit-premise: hpositive_payout_mass : 0 < μ {τ : TripLength | τ ∈ acceptAllPolicy ∧ 0 < w τ}
abbrev assumption_single_state_defined_reward_domain
    (mu μ : Measure TripLength) (w : PricingFunction) : Prop :=
  (∀ tau : TripLength, 0 < tau → 0 ≤ w tau / tau) ∧
    (∀ τ : TripLength, 0 < τ → 0 ≤ w τ / τ) ∧
      mu acceptAllPolicy ≠ ⊤ ∧ μ acceptAllPolicy ≠ ⊤ ∧
        0 < mu {τ : TripLength | τ ∈ acceptAllPolicy ∧ 0 < w τ} ∧
          0 < μ {τ : TripLength | τ ∈ acceptAllPolicy ∧ 0 < w τ}

/-- Dynamic time-fraction denominators are nonzero. -/
-- audit-premise: hi : arrivalI * singleStateTripMass μI σI + switchIJ ≠ 0
-- audit-premise: hj : arrivalJ * singleStateTripMass μJ σJ + switchJI ≠ 0
abbrev assumption_dynamic_time_fraction_denominators
    (μI μJ : Measure TripLength) (σI σJ : TripPolicy)
    (arrivalI arrivalJ switchIJ switchJI : ℝ) : Prop :=
  arrivalI * singleStateTripMass μI σI + switchIJ ≠ 0 ∧
    arrivalJ * singleStateTripMass μJ σJ + switchJI ≠ 0

/-- Switch-rate parameters are in the positive/nonnegative CTMC domain. -/
-- audit-premise: hlambdaIJ : 0 < lambdaIJ
-- audit-premise: hlambdaIJ : 0 ≤ lambdaIJ
-- audit-premise: hsum : 0 < lambdaIJ + lambdaJI
-- audit-premise: hsum : lambdaIJ + lambdaJI ≠ 0
abbrev assumption_switch_rate_domain (lambdaIJ lambdaJI : ℝ) : Prop :=
  0 < lambdaIJ ∧ 0 ≤ lambdaIJ ∧
    0 < lambdaIJ + lambdaJI ∧ lambdaIJ + lambdaJI ≠ 0

/-- Lemma 5 fixed-response policy form uses measurable responses and optimal policies. -/
-- audit-premise: hresponse_measurable : Measurable response
-- audit-premise: hoptimal : ∀ sigma' : TripPolicy, sigma' ⊆ acceptAllPolicy → MeasurableSet sigma' → lemma5MarginalSetReward mu response sigma' ≤ lemma5MarginalSetReward mu response sigma
abbrev assumption_fixed_response_policy_form_conditions
    (mu : Measure TripLength) (response : TripLength → ℝ) (sigma : TripPolicy) : Prop :=
  Measurable response ∧
    ∀ sigma' : TripPolicy, sigma' ⊆ acceptAllPolicy → MeasurableSet sigma' →
      lemma5MarginalSetReward mu response sigma' ≤ lemma5MarginalSetReward mu response sigma

/-- Lemma 6 endpoint derivative formula domain. -/
-- audit-premise: harrival_pos : 0 < arrivalRate
-- audit-premise: hu : 0 < u
-- audit-premise: hQj_pos : 0 < Qj
-- audit-premise: hTi_pos : 0 < gn21EndpointTiPath arrivalRate lowerEndpoint density u
-- audit-premise: hTj_pos : 0 < Tj
-- audit-premise: hWi : gn21EndpointWiPath arrivalRate lowerEndpoint density payment u = Ri * gn21EndpointTiPath arrivalRate lowerEndpoint density u
-- audit-premise: hWj : Wj = Rj * Tj
-- audit-premise: hden : gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u * Tj + Qj * gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠ 0
abbrev assumption_upper_endpoint_derivative_domain
    (arrivalRate switchRate lowerEndpoint u Qj Tj Ri Rj Wj : ℝ)
    (density switchProb payment : ℝ → ℝ) : Prop :=
  0 < arrivalRate ∧
    0 < u ∧
      0 < Qj ∧
        0 < gn21EndpointTiPath arrivalRate lowerEndpoint density u ∧
          0 < Tj ∧
            gn21EndpointWiPath arrivalRate lowerEndpoint density payment u =
              Ri * gn21EndpointTiPath arrivalRate lowerEndpoint density u ∧
              Wj = Rj * Tj ∧
                gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u * Tj +
                    Qj * gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠ 0

/-- Lemma 7/8 affine additive response domains. -/
-- audit-premise: hm_pos : 0 < m
-- audit-premise: ha_pos : 0 < a
-- audit-premise: ha_neg : a < 0
-- audit-premise: hdelta_ji_nonpos : Rj - Ri ≤ 0
-- audit-premise: hdelta_ji_nonneg : 0 ≤ Rj - Ri
-- audit-premise: hstate_weight_pos : 0 < Qi / Ti + Qj / Tj
-- audit-premise: hTi : Ti ≠ 0
-- audit-premise: hTj : Tj ≠ 0
abbrev assumption_affine_response_shape_domains
    (m a Ri Rj Qi Ti Qj Tj : ℝ) : Prop :=
  0 < m ∧ 0 < a ∧ a < 0 ∧
    Rj - Ri ≤ 0 ∧ 0 ≤ Rj - Ri ∧
      0 < Qi / Ti + Qj / Tj ∧ Ti ≠ 0 ∧ Tj ≠ 0

/-- Lemma 9 surge-state derivative source-data formulas and bounds. -/
-- audit-premise: C : Lemma6DerivativeFormulaCertificate
-- audit-premise: hq : C.q = gn21SwitchProb switch21 switch12 C.u
-- audit-premise: hwi : C.wi = m * C.u + z * gn21SwitchProb switch21 switch12 C.u
-- audit-premise: hWi : C.Wi = m * (C.Ti - 1) + z * (C.Qi - switch21)
-- audit-premise: hWj : C.Wj = R1 * C.Tj
-- audit-premise: hbounds_bar : lemma9StructuredBounds ratio C.Tj C.Qj Tbar2 Qbar2 switch21
-- audit-premise: hmR_pos : 0 < m - R1
-- audit-premise: hR1_nonneg : 0 ≤ R1
-- audit-premise: hT1_nonneg : 0 ≤ C.Tj
-- audit-premise: hQ1_pos : 0 < C.Qj
-- audit-premise: hswitch21_pos : 0 < switch21
-- audit-premise: hsum : 0 < switch21 + switch12
-- audit-premise: hu : 0 < C.u
-- audit-premise: hgap_nonneg : 0 ≤ switch21 * C.Ti - C.Qi
-- audit-premise: hgap_le : switch21 * C.Ti - C.Qi ≤ switch21 * Tbar2 - Qbar2
-- audit-premise: hswitch_lt_Q2 : switch21 < C.Qi
-- audit-premise: hQ2_le : C.Qi ≤ Qbar2
abbrev assumption_surge_derivative_source_bounds
    (C : Lemma6DerivativeFormulaCertificate)
    (ratio Tbar2 Qbar2 switch21 switch12 m R1 z : ℝ) :
    Prop :=
  C.q = gn21SwitchProb switch21 switch12 C.u ∧
    C.wi = m * C.u + z * gn21SwitchProb switch21 switch12 C.u ∧
      C.Wi = m * (C.Ti - 1) + z * (C.Qi - switch21) ∧
        C.Wj = R1 * C.Tj ∧
          lemma9StructuredBounds ratio C.Tj C.Qj Tbar2 Qbar2 switch21 ∧
            0 < m - R1 ∧ 0 ≤ R1 ∧ 0 ≤ C.Tj ∧ 0 < C.Qj ∧
              0 < switch21 ∧ 0 < switch21 + switch12 ∧ 0 < C.u ∧
                0 ≤ switch21 * C.Ti - C.Qi ∧
                  switch21 * C.Ti - C.Qi ≤ switch21 * Tbar2 - Qbar2 ∧
                    switch21 < C.Qi ∧ C.Qi ≤ Qbar2

/-- Lemma 10 non-surge derivative source-data formulas and bounds. -/
-- audit-premise: C : Lemma6DerivativeFormulaCertificate
-- audit-premise: hq : C.q = gn21SwitchProb switch12 switch21 C.u
-- audit-premise: hwi : C.wi = R2 * C.u + z * gn21SwitchProb switch12 switch21 C.u
-- audit-premise: hWi : C.Wi = R2 * (C.Ti - 1) + z * (C.Qi - switch12)
-- audit-premise: hWj : C.Wj = R2 * C.Tj
-- audit-premise: hbounds_bar : lemma10StructuredBounds ratio C.Tj C.Qj Tbar1 Qbar1 switch12
-- audit-premise: hz : z = ratio * R2
-- audit-premise: hR2_pos : 0 < R2
-- audit-premise: hQ2_pos : 0 < C.Qj
-- audit-premise: hswitch12_pos : 0 < switch12
-- audit-premise: hsum : 0 < switch12 + switch21
-- audit-premise: hu : 0 < C.u
-- audit-premise: hA_pos : 0 < C.Tj * switch12 + C.Qj
-- audit-premise: hgap_nonneg : 0 ≤ switch12 * C.Ti - C.Qi
-- audit-premise: hgap_le : switch12 * C.Ti - C.Qi ≤ switch12 * Tbar1 - Qbar1
-- audit-premise: hswitch_lt_Q1 : switch12 < C.Qi
-- audit-premise: hQ1_le : C.Qi ≤ Qbar1
abbrev assumption_nonsurge_derivative_source_bounds
    (C : Lemma6DerivativeFormulaCertificate)
    (ratio Tbar1 Qbar1 switch12 switch21 R2 z : ℝ) :
    Prop :=
  C.q = gn21SwitchProb switch12 switch21 C.u ∧
    C.wi = R2 * C.u + z * gn21SwitchProb switch12 switch21 C.u ∧
      C.Wi = R2 * (C.Ti - 1) + z * (C.Qi - switch12) ∧
        C.Wj = R2 * C.Tj ∧
          lemma10StructuredBounds ratio C.Tj C.Qj Tbar1 Qbar1 switch12 ∧
            z = ratio * R2 ∧ 0 < R2 ∧ 0 < C.Qj ∧ 0 < switch12 ∧
              0 < switch12 + switch21 ∧ 0 < C.u ∧
                0 < C.Tj * switch12 + C.Qj ∧
                  0 ≤ switch12 * C.Ti - C.Qi ∧
                    switch12 * C.Ti - C.Qi ≤ switch12 * Tbar1 - Qbar1 ∧
                      switch12 < C.Qi ∧ C.Qi ≤ Qbar1

/-- Theorem 3 source-data domain for sequential current bounds. -/
-- audit-premise: hR1_eq : R1 = rho * R2
-- audit-premise: hR1_pos : 0 < R1
-- audit-premise: hR1_lt_R2 : R1 < R2
-- audit-premise: hR2_pos : 0 < R2
-- audit-premise: hrho_lt_one : rho < 1
-- audit-premise: harrival1_pos : 0 < arrival 0
-- audit-premise: harrival2_pos : 0 < arrival 1
-- audit-premise: hswitch12_pos : 0 < switch12
-- audit-premise: hswitch21_pos : 0 < switch21
-- audit-premise: hmeasure1_pos : 0 < mu 0 acceptAllPolicy
-- audit-premise: hmeasure2_pos : 0 < mu 1 acceptAllPolicy
abbrev assumption_theorem3_source_data_domain
    (mu : Fin 2 → Measure TripLength) (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ) : Prop :=
  R1 = rho * R2 ∧ 0 < R1 ∧ R1 < R2 ∧ 0 < R2 ∧ rho < 1 ∧
    0 < arrival 0 ∧ 0 < arrival 1 ∧
      0 < switch12 ∧ 0 < switch21 ∧
        0 < mu 0 acceptAllPolicy ∧ 0 < mu 1 acceptAllPolicy

end GN21DriverSurgePricing
