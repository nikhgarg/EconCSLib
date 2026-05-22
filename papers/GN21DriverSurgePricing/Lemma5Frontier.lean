import GN21DriverSurgePricing.MainTheorems

/-!
# Lemma 5 Frontier Routes for Driver Surge Pricing

This file holds active Lemma 5 proof-route adapters that build on the stable
GN21 continuous proof base in `MainTheorems.lean`.  Keeping these frontier
constructors here lets future proof work target this module instead of
rechecking the full theorem ledger after every small route edit.
-/

open EconCSLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

noncomputable section

/--
Positive-response marginal dominance transfers to any objective that is a
positive affine transform of that marginal reward on feasible measurable
policies.
-/
def Lemma5FeasiblePolicyCanonicalDominanceMaximizerData.of_positiveResponse_marginal_positive_affine
    {Rhat : SingleStateReward}
    (μ : Measure TripLength) (response : TripLength → ℝ)
    (σ0 : TripPolicy) (shape : Lemma5DerivativeShape)
    (hσ0_open : IsOpen σ0)
    (hσ0_subset : σ0 ⊆ acceptAllPolicy)
    (hcont : GN21SymmDiffContinuousAt μ Rhat σ0)
    (hresponse_measurable : Measurable response)
    (hresponse_integrable_acceptAll :
      IntegrableOn response acceptAllPolicy μ)
    (hpositive_form :
      lemma5PolicyForm shape (lemma5PositiveResponsePolicy response))
    (hstrict_mass :
      ¬ lemma5PolicyForm shape σ0 →
        0 < μ (lemma5PositiveResponsePolicy response \ σ0) ∨
        0 <
          μ (Function.support response ∩
            (σ0 \ lemma5PositiveResponsePolicy response)))
    (scale offset : ℝ) (hscale_pos : 0 < scale)
    (haffine :
      ∀ σ : TripPolicy,
        σ ⊆ acceptAllPolicy →
        MeasurableSet σ →
          Rhat σ = scale * lemma5MarginalSetReward μ response σ + offset) :
    Lemma5FeasiblePolicyCanonicalDominanceMaximizerData
      μ Rhat σ0 shape where
  hσ0_open := hσ0_open
  hσ0_subset := hσ0_subset
  hcont := hcont
  canonicalPolicyMax := by
    let P : TripPolicy := lemma5PositiveResponsePolicy response
    have hP_subset : P ⊆ acceptAllPolicy :=
      lemma5PositiveResponsePolicy_subset_acceptAll response
    have hP_measurable : MeasurableSet P :=
      measurableSet_lemma5PositiveResponsePolicy response
        hresponse_measurable
    refine ⟨P, hP_subset, hP_measurable, hpositive_form, ?_⟩
    intro seed hseed_form
    have hmarg :
        lemma5MarginalSetReward μ response seed.policy ≤
          lemma5MarginalSetReward μ response P := by
      exact
        lemma5MarginalSetReward_le_positiveResponsePolicy
          μ response seed.policy hresponse_measurable
          hresponse_integrable_acceptAll seed.measurableSet_policy
          seed.subset_acceptAll
    have hseed_aff :=
      haffine seed.policy seed.subset_acceptAll seed.measurableSet_policy
    have hP_aff := haffine P hP_subset hP_measurable
    rw [hseed_aff, hP_aff]
    nlinarith [hscale_pos, hmarg]
  policyCanonicalDominance := by
    intro seed hnot
    let P : TripPolicy := lemma5PositiveResponsePolicy response
    have hP_subset : P ⊆ acceptAllPolicy :=
      lemma5PositiveResponsePolicy_subset_acceptAll response
    have hP_measurable : MeasurableSet P :=
      measurableSet_lemma5PositiveResponsePolicy response
        hresponse_measurable
    refine ⟨P, hP_subset, hpositive_form, ?_⟩
    have hmarg :
        lemma5MarginalSetReward μ response seed.policy ≤
          lemma5MarginalSetReward μ response P := by
      exact
        lemma5MarginalSetReward_le_positiveResponsePolicy
          μ response seed.policy hresponse_measurable
          hresponse_integrable_acceptAll seed.measurableSet_policy
          seed.subset_acceptAll
    have hseed_aff :=
      haffine seed.policy seed.subset_acceptAll seed.measurableSet_policy
    have hP_aff := haffine P hP_subset hP_measurable
    rw [hseed_aff, hP_aff]
    nlinarith [hscale_pos, hmarg]
  policyStrictWitness := by
    intro hnot
    let P : TripPolicy := lemma5PositiveResponsePolicy response
    have hP_subset : P ⊆ acceptAllPolicy :=
      lemma5PositiveResponsePolicy_subset_acceptAll response
    have hP_measurable : MeasurableSet P :=
      measurableSet_lemma5PositiveResponsePolicy response
        hresponse_measurable
    refine ⟨P, hP_subset, hpositive_form, ?_⟩
    have hmarg :
        lemma5MarginalSetReward μ response σ0 <
          lemma5MarginalSetReward μ response P := by
      rcases hstrict_mass hnot with homitted | hnegative
      · exact
          lemma5MarginalSetReward_lt_positiveResponsePolicy_of_omits_positive_mass
            μ response σ0 hresponse_measurable hresponse_integrable_acceptAll
            hσ0_open.measurableSet hσ0_subset homitted
      · exact
          lemma5MarginalSetReward_lt_positiveResponsePolicy_of_accepts_negative_mass
            μ response σ0 hresponse_measurable hresponse_integrable_acceptAll
            hσ0_open.measurableSet hσ0_subset hnegative
    have hσ0_aff := haffine σ0 hσ0_subset hσ0_open.measurableSet
    have hP_aff := haffine P hP_subset hP_measurable
    rw [hσ0_aff, hP_aff]
    nlinarith [hscale_pos, hmarg]

/--
Left-state GN21 fixed-response data feed the feasible policy-canonical Lemma 5
route once the source proof supplies the continuous strict-mass and positive
affine objective-transfer facts.
-/
def GN21MeasuredLeftFixedResponsePolicyFormSourceData.to_feasible_policy_canonical_dominance_positive_affine
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    {Rhat : SingleStateReward}
    (D :
      GN21MeasuredLeftFixedResponsePolicyFormSourceData μ arrival switch12
        switch21 w ρ shape)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ)
    (hσ_open : IsOpen (ρ 0))
    (hσ_subset : ρ 0 ⊆ acceptAllPolicy)
    (hcont : GN21SymmDiffContinuousAt (μ 0) Rhat (ρ 0))
    (hstrict_mass :
      ¬ lemma5PolicyForm shape (ρ 0) →
        0 <
          μ 0
            (lemma5PositiveResponsePolicy
                (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) \
              ρ 0) ∨
        0 <
          μ 0
            (Function.support
                (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) ∩
              (ρ 0 \
                lemma5PositiveResponsePolicy
                  (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                    (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                    (ρ 0) (ρ 1)))))
    (scale offset : ℝ) (hscale_pos : 0 < scale)
    (haffine :
      ∀ σ : TripPolicy,
        σ ⊆ acceptAllPolicy →
        MeasurableSet σ →
          Rhat σ =
            scale *
              lemma5MarginalSetReward (μ 0)
                (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) σ + offset) :
    Lemma5FeasiblePolicyCanonicalDominanceMaximizerData
      (μ 0) Rhat (ρ 0) shape :=
  Lemma5FeasiblePolicyCanonicalDominanceMaximizerData.of_positiveResponse_marginal_positive_affine
    (μ 0)
    (gn21MeasuredLeftMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
      (ρ 0) (ρ 1))
    (ρ 0) shape hσ_open hσ_subset
    hcont (D.to_fixed_response hρ).response_measurable
    (D.to_fixed_response hρ).response_integrable_acceptAll
    (D.to_fixed_response hρ).policy_form_data.policy_form hstrict_mass scale offset
    hscale_pos haffine

/--
Right-state GN21 fixed-response data feed the feasible policy-canonical Lemma
5 route once the source proof supplies continuous strict-mass and positive
affine objective-transfer facts.
-/
def GN21MeasuredRightFixedResponsePolicyFormSourceData.to_feasible_policy_canonical_dominance_positive_affine
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {switch12 switch21 : ℝ}
    {w : Fin 2 → PricingFunction}
    {ρ : Fin 2 → TripPolicy}
    {shape : Lemma5DerivativeShape}
    {Rhat : SingleStateReward}
    (D :
      GN21MeasuredRightFixedResponsePolicyFormSourceData μ arrival switch12
        switch21 w ρ shape)
    (hρ :
      dynamicMeasurableOptimal
        (gn21MeasuredDynamicRewardFunctional μ arrival switch12 switch21 w)
        ρ)
    (hσ_open : IsOpen (ρ 1))
    (hσ_subset : ρ 1 ⊆ acceptAllPolicy)
    (hcont : GN21SymmDiffContinuousAt (μ 1) Rhat (ρ 1))
    (hstrict_mass :
      ¬ lemma5PolicyForm shape (ρ 1) →
        0 <
          μ 1
            (lemma5PositiveResponsePolicy
                (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) \
              ρ 1) ∨
        0 <
          μ 1
            (Function.support
                (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) ∩
              (ρ 1 \
                lemma5PositiveResponsePolicy
                  (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                    (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                    (ρ 0) (ρ 1)))))
    (scale offset : ℝ) (hscale_pos : 0 < scale)
    (haffine :
      ∀ σ : TripPolicy,
        σ ⊆ acceptAllPolicy →
        MeasurableSet σ →
          Rhat σ =
            scale *
              lemma5MarginalSetReward (μ 1)
                (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
                  (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
                  (ρ 0) (ρ 1)) σ + offset) :
    Lemma5FeasiblePolicyCanonicalDominanceMaximizerData
      (μ 1) Rhat (ρ 1) shape :=
  Lemma5FeasiblePolicyCanonicalDominanceMaximizerData.of_positiveResponse_marginal_positive_affine
    (μ 1)
    (gn21MeasuredRightMarginalResponseAtCurrent (μ 0) (μ 1)
      (arrival 0) (arrival 1) switch12 switch21 (w 0) (w 1)
      (ρ 0) (ρ 1))
    (ρ 1) shape hσ_open hσ_subset
    hcont (D.to_fixed_response hρ).response_measurable
    (D.to_fixed_response hρ).response_integrable_acceptAll
    (D.to_fixed_response hρ).policy_form_data.policy_form hstrict_mass scale offset
    hscale_pos haffine

end

end GN21DriverSurgePricing
