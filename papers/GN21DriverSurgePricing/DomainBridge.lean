import GN21DriverSurgePricing.MainTheorems

/-!
# Domain Bridges for GN21 Measurable Theorem 3

The Appendix-D reward-rate formulas in the source paper divide by accepted
trip mass.  `MainTheorems.lean` therefore has a positive-mass measurable
source domain alongside the full feasible-measurable domain.  This file keeps
the order-theoretic bridge between those domains explicit: if every feasible
zero-mass policy is strictly dominated by a feasible positive-mass policy, then
positive-mass IC and positive-mass a.e. uniqueness lift to the full measurable
statement.
-/

open EconCSLib
open MeasureTheory
open scoped Function ProbabilityTheory Topology ENNReal

namespace GN21DriverSurgePricing

/-- Zero real trip mass plus finite underlying measure forces measure zero. -/
theorem measure_zero_of_singleStateTripMass_eq_zero_of_ne_top
    {μ : Measure TripLength} {σ : TripPolicy}
    (hmass : singleStateTripMass μ σ = 0)
    (hfinite : μ σ ≠ ⊤) :
    μ σ = 0 := by
  have hzero_or_top : μ σ = 0 ∨ μ σ = ⊤ := by
    simpa [singleStateTripMass] using
      (ENNReal.toReal_eq_zero_iff (μ σ)).mp hmass
  rcases hzero_or_top with hzero | htop
  · exact hzero
  · exact False.elim (hfinite htop)

/-- Zero accepted mass on a finite-measure policy makes accepted trip time vanish. -/
theorem singleStateTripTime_eq_zero_of_mass_zero_of_ne_top
    {μ : Measure TripLength} {σ : TripPolicy}
    (hmass : singleStateTripMass μ σ = 0)
    (hfinite : μ σ ≠ ⊤) :
    singleStateTripTime μ σ = 0 :=
  singleStateTripTime_eq_zero_of_measure_zero μ σ
    (measure_zero_of_singleStateTripMass_eq_zero_of_ne_top hmass hfinite)

/-- Zero accepted mass on a finite-measure policy makes accepted payment vanish. -/
theorem singleStateTripPayment_eq_zero_of_mass_zero_of_ne_top
    {μ : Measure TripLength} {w : PricingFunction} {σ : TripPolicy}
    (hmass : singleStateTripMass μ σ = 0)
    (hfinite : μ σ ≠ ⊤) :
    singleStateTripPayment μ w σ = 0 :=
  singleStateTripPayment_eq_zero_of_measure_zero μ w σ
    (measure_zero_of_singleStateTripMass_eq_zero_of_ne_top hmass hfinite)

/-- The paper's real-valued state cycle time totalizes to zero at zero mass. -/
theorem gn21StateCycleTime_eq_zero_of_mass_time_zero
    (μ : Measure TripLength) (arrivalRate : ℝ) (σ : TripPolicy)
    (hmass : singleStateTripMass μ σ = 0)
    (htime : singleStateTripTime μ σ = 0) :
    gn21StateCycleTime μ arrivalRate σ = 0 := by
  simp [gn21StateCycleTime, hmass, htime]

/-- The paper's real-valued state reward rate totalizes to zero at zero mass/payment/time. -/
theorem gn21MeasuredStateRewardRate_eq_zero_of_mass_time_payment_zero
    (μ : Measure TripLength) (arrivalRate : ℝ)
    (w : PricingFunction) (σ : TripPolicy)
    (hmass : singleStateTripMass μ σ = 0)
    (htime : singleStateTripTime μ σ = 0)
    (hpayment : singleStateTripPayment μ w σ = 0) :
    gn21MeasuredStateRewardRate μ arrivalRate w σ = 0 := by
  simp [gn21MeasuredStateRewardRate, gn21StateRewardRate,
    gn21StateMeanEarning, gn21StateCycleTime, hmass, htime, hpayment]

/--
If both states have zero accepted mass, zero accepted time, and zero accepted
payment, the current real-valued measured dynamic reward totalizes to zero.
-/
theorem gn21MeasuredDynamicReward_eq_zero_of_both_zero_mass_time_payment
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy)
    (hmassI : singleStateTripMass μI σI = 0)
    (hmassJ : singleStateTripMass μJ σJ = 0)
    (htimeI : singleStateTripTime μI σI = 0)
    (htimeJ : singleStateTripTime μJ σJ = 0)
    (hpaymentI : singleStateTripPayment μI wI σI = 0)
    (hpaymentJ : singleStateTripPayment μJ wJ σJ = 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
      wI wJ σI σJ = 0 := by
  simp [gn21MeasuredDynamicReward, gn21DynamicRewardFormula,
    gn21MeasuredTimeFraction, gn21TimeFractionFormula,
    gn21MeasuredStateRewardRate, gn21StateRewardRate, gn21StateMeanEarning,
    gn21StateCycleTime, hmassI, hmassJ, htimeI, htimeJ, hpaymentI,
    hpaymentJ]

/--
With the current real-valued totalization, if the left state has zero accepted
mass/time/payment and the right-state time-fraction denominator is nonzero,
the measured dynamic reward collapses to the right state's reward rate.  This
is why full-domain Theorem 3 needs an explicit zero-mass dominance or a
different extended-real reward model.
-/
theorem gn21MeasuredDynamicReward_eq_right_rewardRate_of_left_zero_mass_time_payment
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy)
    (hmassI : singleStateTripMass μI σI = 0)
    (htimeI : singleStateTripTime μI σI = 0)
    (hpaymentI : singleStateTripPayment μI wI σI = 0)
    (hdenJ :
      arrivalJ * singleStateTripMass μJ σJ *
            gn21StateCycleTime μJ arrivalJ σJ *
            gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI ≠ 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
      wI wJ σI σJ =
      gn21MeasuredStateRewardRate μJ arrivalJ wJ σJ := by
  have hleft_fraction :
      gn21MeasuredTimeFraction μI μJ arrivalI arrivalJ switchIJ switchJI
        σI σJ = 0 := by
    simp [gn21MeasuredTimeFraction, gn21TimeFractionFormula,
      gn21StateCycleTime, hmassI, htimeI]
  have hright_fraction :
      gn21MeasuredTimeFraction μJ μI arrivalJ arrivalI switchJI switchIJ
        σJ σI = 1 := by
    have hcycleI :
        gn21StateCycleTime μI arrivalI σI = 0 :=
      gn21StateCycleTime_eq_zero_of_mass_time_zero
        μI arrivalI σI hmassI htimeI
    unfold gn21MeasuredTimeFraction gn21TimeFractionFormula
    rw [hcycleI, hmassI]
    set A :=
      arrivalJ * singleStateTripMass μJ σJ *
        gn21StateCycleTime μJ arrivalJ σJ *
          gn21ExitWeightIntegral μI arrivalI switchIJ switchJI σI
    have hden_eq :
        arrivalI * 0 * 0 *
              gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ +
            A = A := by
      ring
    rw [hden_eq]
    exact div_self (by simpa [A] using hdenJ)
  have hleft_reward :
      gn21MeasuredStateRewardRate μI arrivalI wI σI = 0 :=
    gn21MeasuredStateRewardRate_eq_zero_of_mass_time_payment_zero
      μI arrivalI wI σI hmassI htimeI hpaymentI
  simp [gn21MeasuredDynamicReward, gn21DynamicRewardFormula,
    hleft_fraction, hright_fraction, hleft_reward]

/-- State-swapped one-zero-state simplification. -/
theorem gn21MeasuredDynamicReward_eq_left_rewardRate_of_right_zero_mass_time_payment
    (μI μJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (σI σJ : TripPolicy)
    (hmassJ : singleStateTripMass μJ σJ = 0)
    (htimeJ : singleStateTripTime μJ σJ = 0)
    (hpaymentJ : singleStateTripPayment μJ wJ σJ = 0)
    (hdenI :
      arrivalI * singleStateTripMass μI σI *
            gn21StateCycleTime μI arrivalI σI *
            gn21ExitWeightIntegral μJ arrivalJ switchJI switchIJ σJ ≠ 0) :
    gn21MeasuredDynamicReward μI μJ arrivalI arrivalJ switchIJ switchJI
      wI wJ σI σJ =
      gn21MeasuredStateRewardRate μI arrivalI wI σI := by
  have hswap :=
    gn21MeasuredDynamicReward_eq_right_rewardRate_of_left_zero_mass_time_payment
      μJ μI arrivalJ arrivalI switchJI switchIJ wJ wI σJ σI
      hmassJ htimeJ hpaymentJ hdenI
  simpa [gn21MeasuredDynamicReward, gn21DynamicRewardFormula, add_comm,
    mul_comm] using hswap

/-- A feasible measurable dynamic policy has zero accepted mass in some state. -/
def dynamicHasZeroAcceptedMass
    (μ : Fin 2 → Measure TripLength) (σ : Fin 2 → TripPolicy) : Prop :=
  ∃ i : Fin 2, singleStateTripMass (μ i) (σ i) = 0

/--
If no state has zero accepted mass, feasible measurability upgrades to the
positive-mass feasible source domain.
-/
theorem dynamicFeasibleMeasurablePositiveMassPolicy_of_no_zero_mass
    {μ : Fin 2 → Measure TripLength}
    {σ : Fin 2 → TripPolicy}
    (hσ : dynamicFeasibleMeasurablePolicy σ)
    (hno_zero : ¬ dynamicHasZeroAcceptedMass μ σ) :
    dynamicFeasibleMeasurablePositiveMassPolicy μ σ := by
  constructor
  · exact hσ
  · intro i
    have hne : singleStateTripMass (μ i) (σ i) ≠ 0 := by
      intro hzero
      exact hno_zero ⟨i, hzero⟩
    exact lt_of_le_of_ne (singleStateTripMass_nonneg (μ i) (σ i))
      (Ne.symm hne)

/-- A feasible measurable policy outside the positive-mass domain has zero mass in some state. -/
theorem dynamicHasZeroAcceptedMass_of_not_positiveMass
    {μ : Fin 2 → Measure TripLength}
    {σ : Fin 2 → TripPolicy}
    (hσ : dynamicFeasibleMeasurablePolicy σ)
    (hnot :
      ¬ dynamicFeasibleMeasurablePositiveMassPolicy μ σ) :
    dynamicHasZeroAcceptedMass μ σ := by
  by_contra hno_zero
  exact hnot
    (dynamicFeasibleMeasurablePositiveMassPolicy_of_no_zero_mass hσ
      hno_zero)

/-- A zero-mass state prevents membership in the positive-mass source domain. -/
theorem not_dynamicFeasibleMeasurablePositiveMassPolicy_of_zero_mass
    {μ : Fin 2 → Measure TripLength}
    {σ : Fin 2 → TripPolicy}
    (hzero : dynamicHasZeroAcceptedMass μ σ) :
    ¬ dynamicFeasibleMeasurablePositiveMassPolicy μ σ := by
  intro hpos
  rcases hzero with ⟨i, hmass_zero⟩
  have hmass_pos := hpos.2 i
  linarith

/--
Strict-dominance certificate for the boundary omitted by the paper's
positive-mass reward-rate algebra: every feasible measurable zero-mass policy
is strictly dominated by some feasible measurable positive-mass policy.
-/
structure DynamicZeroMassStrictDominanceCertificate
    (μ : Fin 2 → Measure TripLength) (R : DynamicReward) where
  improve_zero_mass :
    ∀ σ : Fin 2 → TripPolicy,
      dynamicFeasibleMeasurablePolicy σ →
        dynamicHasZeroAcceptedMass μ σ →
          ∃ τ : Fin 2 → TripPolicy,
            dynamicFeasibleMeasurablePositiveMassPolicy μ τ ∧ R σ < R τ

/--
Build the explicit zero-mass certificate from the often-convenient complement
form: every feasible policy outside the positive-mass domain is dominated by a
positive-mass feasible policy.
-/
def DynamicZeroMassStrictDominanceCertificate.of_not_positive_mass
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hdom :
      ∀ σ : Fin 2 → TripPolicy,
        dynamicFeasibleMeasurablePolicy σ →
          ¬ dynamicFeasibleMeasurablePositiveMassPolicy μ σ →
            ∃ τ : Fin 2 → TripPolicy,
              dynamicFeasibleMeasurablePositiveMassPolicy μ τ ∧ R σ < R τ) :
    DynamicZeroMassStrictDominanceCertificate μ R where
  improve_zero_mass := by
    intro σ hσ hzero
    exact hdom σ hσ
      (not_dynamicFeasibleMeasurablePositiveMassPolicy_of_zero_mass hzero)

/--
Positive-mass measurable IC lifts to full feasible-measurable IC once every
zero-mass feasible policy is strictly dominated by a positive-mass feasible
policy.
-/
theorem dynamicMeasurableIncentiveCompatible_of_positiveMass_and_zeroMassStrictDominance
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hposIC : dynamicPositiveMassMeasurableIncentiveCompatible μ R)
    (hzero : DynamicZeroMassStrictDominanceCertificate μ R) :
    dynamicMeasurableIncentiveCompatible R := by
  constructor
  · exact hposIC.1.1
  · intro σ hσ
    by_cases hσ_zero : dynamicHasZeroAcceptedMass μ σ
    · rcases hzero.improve_zero_mass σ hσ hσ_zero with
        ⟨τ, hτ_pos, hlt⟩
      have hτ_le_accept :
          R τ ≤ R acceptAllDynamicPolicy := hposIC.2 τ hτ_pos
      linarith
    · have hσ_pos :
          dynamicFeasibleMeasurablePositiveMassPolicy μ σ :=
        dynamicFeasibleMeasurablePositiveMassPolicy_of_no_zero_mass
          hσ hσ_zero
      exact hposIC.2 σ hσ_pos

/--
A full feasible-measurable optimum belongs to the positive-mass source domain
under the same zero-mass strict-dominance certificate.
-/
theorem dynamicPositiveMassMeasurableOptimal_of_dynamicMeasurableOptimal_of_zeroMassStrictDominance
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    {σ : Fin 2 → TripPolicy}
    (hzero : DynamicZeroMassStrictDominanceCertificate μ R)
    (hσ : dynamicMeasurableOptimal R σ) :
    dynamicPositiveMassMeasurableOptimal μ R σ := by
  by_cases hσ_zero : dynamicHasZeroAcceptedMass μ σ
  · rcases hzero.improve_zero_mass σ hσ.1 hσ_zero with
      ⟨τ, hτ_pos, hlt⟩
    have hτ_le_σ : R τ ≤ R σ := hσ.2 τ hτ_pos.1
    linarith
  · constructor
    · exact
        dynamicFeasibleMeasurablePositiveMassPolicy_of_no_zero_mass
          hσ.1 hσ_zero
    · intro τ hτ_pos
      exact hσ.2 τ hτ_pos.1

/--
Positive-mass measurable IC plus positive-mass a.e. uniqueness lifts to the
full feasible-measurable a.e.-unique conclusion under zero-mass strict
dominance.
-/
theorem dynamicMeasurableICAEUnique_of_positiveMass_ae_unique_and_zeroMassStrictDominance
    {μ : Fin 2 → Measure TripLength}
    {R : DynamicReward}
    (hposIC : dynamicPositiveMassMeasurableIncentiveCompatible μ R)
    (hposAE :
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ)
    (hzero : DynamicZeroMassStrictDominanceCertificate μ R) :
    dynamicMeasurableIncentiveCompatible R ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicMeasurableOptimal R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  refine
    ⟨dynamicMeasurableIncentiveCompatible_of_positiveMass_and_zeroMassStrictDominance
      hposIC hzero, ?_⟩
  intro ρ hρ
  exact hposAE ρ
    (dynamicPositiveMassMeasurableOptimal_of_dynamicMeasurableOptimal_of_zeroMassStrictDominance
      hzero hρ)

/--
Positive-mass analogue of the measurable positive-response marginal
certificate.  This is the same Lemma-5 endpoint as the full certificate, but
the optimizers quantified over are restricted to the nondegenerate source
domain where the Appendix-D reward-rate formulas are defined.
-/
structure Theorem4PositiveMassMeasurablePositiveResponseAEMarginalCertificate
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) where
  accept_all_optimal : dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy
  nonsurge_marginal_optimal :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 0) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          (∀ τ : TripPolicy,
            τ ⊆ acceptAllPolicy →
            MeasurableSet τ →
              lemma5MarginalSetReward (μ 0) response τ ≤
                lemma5MarginalSetReward (μ 0) response (ρ 0))
  surge_marginal_optimal :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 1) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          (∀ τ : TripPolicy,
            τ ⊆ acceptAllPolicy →
            MeasurableSet τ →
              lemma5MarginalSetReward (μ 1) response τ ≤
                lemma5MarginalSetReward (μ 1) response (ρ 1))

/--
Positive-response marginal optimality gives a.e. accept-all uniqueness inside
the positive-mass measurable source domain.
-/
theorem paper_theorem4_positive_mass_measurable_accept_all_ae_unique_optimal_of_positive_response_marginal_optima
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (C :
      Theorem4PositiveMassMeasurablePositiveResponseAEMarginalCertificate
        μ R) :
    dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  refine ⟨C.accept_all_optimal, ?_⟩
  intro ρ hρ i
  fin_cases i
  · rcases C.nonsurge_marginal_optimal ρ hρ with
      ⟨response, hmeas, hint, hpositive, hoptimal⟩
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_feasible_optimal
        (μ 0) response (ρ 0) hmeas hint (hρ.1.1 0).2 (hρ.1.1 0).1
        hpositive hoptimal
  · rcases C.surge_marginal_optimal ρ hρ with
      ⟨response, hmeas, hint, hpositive, hoptimal⟩
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_feasible_optimal
        (μ 1) response (ρ 1) hmeas hint (hρ.1.1 1).2 (hρ.1.1 1).1
        hpositive hoptimal

/--
Positive-mass analogue of the accept-all-candidate positive-response
certificate.  This weaker Lemma-5 interface is enough for a.e. uniqueness and
only compares each positive-mass optimum with the accept-all candidate.
-/
structure Theorem4PositiveMassMeasurablePositiveResponseAEAcceptAllCandidateCertificate
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward) where
  accept_all_optimal : dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy
  nonsurge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 0) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          lemma5MarginalSetReward (μ 0) response acceptAllPolicy ≤
            lemma5MarginalSetReward (μ 0) response (ρ 0)
  surge_acceptAll_candidate :
    ∀ ρ : Fin 2 → TripPolicy, dynamicPositiveMassMeasurableOptimal μ R ρ →
      ∃ response : TripLength → ℝ,
        Measurable response ∧
          IntegrableOn response acceptAllPolicy (μ 1) ∧
          lemma5PolicyForm .positive
            (lemma5PositiveResponsePolicy response) ∧
          lemma5MarginalSetReward (μ 1) response acceptAllPolicy ≤
            lemma5MarginalSetReward (μ 1) response (ρ 1)

/--
Accept-all candidate comparisons give a.e. accept-all uniqueness inside the
positive-mass measurable source domain.
-/
theorem paper_theorem4_positive_mass_measurable_accept_all_ae_unique_optimal_of_positive_response_acceptAll_candidates
    (μ : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (C :
      Theorem4PositiveMassMeasurablePositiveResponseAEAcceptAllCandidateCertificate
        μ R) :
    dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy ∧
      ∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ R ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ := by
  refine ⟨C.accept_all_optimal, ?_⟩
  intro ρ hρ i
  fin_cases i
  · rcases C.nonsurge_acceptAll_candidate ρ hρ with
      ⟨response, hmeas, hint, hpositive, hcandidate⟩
    have hpositive_eq :
        lemma5PositiveResponsePolicy response = acceptAllPolicy :=
      eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
        (lemma5PositiveResponsePolicy_subset_acceptAll response)
        hpositive
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
        (μ 0) response (ρ 0) hmeas hint (hρ.1.1 0).2 (hρ.1.1 0).1
        hpositive (by simpa [hpositive_eq] using hcandidate)
  · rcases C.surge_acceptAll_candidate ρ hρ with
      ⟨response, hmeas, hint, hpositive, hcandidate⟩
    have hpositive_eq :
        lemma5PositiveResponsePolicy response = acceptAllPolicy :=
      eq_acceptAllPolicy_of_subset_acceptAll_of_acceptsAll
        (lemma5PositiveResponsePolicy_subset_acceptAll response)
        hpositive
    exact
      acceptAllAlmostEverywhere_of_lemma5_positiveResponse_candidate_le
        (μ 1) response (ρ 1) hmeas hint (hρ.1.1 1).2 (hρ.1.1 1).1
        hpositive (by simpa [hpositive_eq] using hcandidate)

/--
Positive-mass Theorem 3 marginal-response certificate.  This is the source
Theorem 4/Lemma 5 boundary restricted to the denominator-valid domain: after
Theorem 3 constructs `m,z`, every positive-mass measurable optimum has the
positive marginal-response data needed for a.e. accept-all uniqueness.
-/
def theorem3AcceptAllPositiveMassPositiveResponseAEMarginalCertificate
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∀ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z →
        Theorem4PositiveMassMeasurablePositiveResponseAEMarginalCertificate μ
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z)

/--
Readable positive-mass source-domain conclusion of Theorem 3 with the paper's
a.e. uniqueness convention restricted to positive-mass measurable optima.
-/
def theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (R1 R2 switch12 switch21 : ℝ) : Prop :=
  ∃ m z : Fin 2 → ℝ,
    (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) ∧
      dynamicPositiveMassMeasurableIncentiveCompatible μ
        (gn21MeasuredCTMCStructuredDynamicReward
          μ arrival switch12 switch21 m z) ∧
      (∀ ρ : Fin 2 → TripPolicy,
        dynamicPositiveMassMeasurableOptimal μ
          (gn21MeasuredCTMCStructuredDynamicReward
            μ arrival switch12 switch21 m z) ρ →
          dynamicAcceptAllAlmostEverywhere μ ρ) ∧
      (∃ q : Fin 2 → TripLength → ℝ,
        ∀ i τ,
          ctmcStructuredDynamicSurgePrice m z switch12 switch21 i τ =
            structuredSurgePrice (m i) (z i) (q i) τ) ∧
      theorem3AcceptAllStructuredParameterEvidence
        μ arrival R1 R2 switch12 switch21 m z

/-- The positive-mass a.e.-unique conclusion contains the positive-mass IC conclusion. -/
theorem theorem3MeasuredStructuredPositiveMassMeasurableICConclusion_of_ae_unique
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hIC, _hAE, hprice_form, hparams⟩
  exact ⟨m, z, hsigns, hIC, hprice_form, hparams⟩

/--
Add the positive-mass a.e.-unique Theorem 4 conclusion to any compiled
positive-mass Theorem 3 IC construction.  This avoids redoing the scalar
Theorem 3 price construction: the marginal-response certificate is checked
only for the already-constructed `m,z`.
-/
theorem theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_positive_response_marginal
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICConclusion
        μ arrival R1 R2 switch12 switch21)
    (hpositive_marginal :
      theorem3AcceptAllPositiveMassPositiveResponseAEMarginalCertificate
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hIC, hprice_form, hparams⟩
  let R : DynamicReward :=
    gn21MeasuredCTMCStructuredDynamicReward
      μ arrival switch12 switch21 m z
  have htheorem4 :
      dynamicPositiveMassMeasurableOptimal μ R acceptAllDynamicPolicy ∧
        ∀ ρ : Fin 2 → TripPolicy,
          dynamicPositiveMassMeasurableOptimal μ R ρ →
            dynamicAcceptAllAlmostEverywhere μ ρ :=
    paper_theorem4_positive_mass_measurable_accept_all_ae_unique_optimal_of_positive_response_marginal_optima
      μ R (hpositive_marginal m z hsigns hparams)
  exact ⟨m, z, hsigns, hIC, by simpa [R] using htheorem4.2,
    hprice_form, hparams⟩

/--
Paper-facing positive-mass Theorem 3 endpoint from the canonical
denominator-valid sequential source assumptions plus the positive-response
Lemma 5 marginal proof.  The conclusion is exactly the source-domain version
of measurable IC with a.e. accept-all uniqueness: no zero-mass comparison
policy is quantified over.
-/
theorem paper_theorem3_measured_structured_positive_mass_measurable_ic_ae_unique_prices_of_source_assumptions_and_positive_response_marginal
    (μ : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ)
    (rho R1 R2 switch12 switch21 : ℝ)
    (A :
      Theorem3AcceptAllStructuredPositiveMassFeasibleSequentialSurgeRewardRateDataAssumptions
        μ arrival rho R1 R2 switch12 switch21)
    (hpositive_marginal :
      theorem3AcceptAllPositiveMassPositiveResponseAEMarginalCertificate
        μ arrival R1 R2 switch12 switch21) :
    theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 :=
  theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion_of_ic_and_positive_response_marginal
    (paper_theorem3_measured_structured_positive_mass_measurable_ic_prices_of_source_assumptions
      μ arrival rho R1 R2 switch12 switch21 A)
    hpositive_marginal

/--
Paper-facing domain bridge: a positive-mass a.e.-unique Theorem 3 result lifts
to the full feasible-measurable a.e.-unique result when the constructed prices
also strictly dominate every feasible zero-mass policy.
-/
theorem theorem3MeasuredStructuredMeasurableICAEUniqueConclusion_of_positiveMass_ae_unique_and_zeroMassStrictDominance
    {μ : Fin 2 → Measure TripLength}
    {arrival : Fin 2 → ℝ}
    {R1 R2 switch12 switch21 : ℝ}
    (H :
      theorem3MeasuredStructuredPositiveMassMeasurableICAEUniqueConclusion
        μ arrival R1 R2 switch12 switch21)
    (hzero :
      ∀ m z : Fin 2 → ℝ,
        (0 ≤ m 0 ∧ 0 ≤ m 1 ∧ 0 ≤ z 1) →
          theorem3AcceptAllStructuredParameterEvidence
            μ arrival R1 R2 switch12 switch21 m z →
            DynamicZeroMassStrictDominanceCertificate μ
              (gn21MeasuredCTMCStructuredDynamicReward
                μ arrival switch12 switch21 m z)) :
    theorem3MeasuredStructuredMeasurableICAEUniqueConclusion
      μ arrival R1 R2 switch12 switch21 := by
  rcases H with ⟨m, z, hsigns, hposIC, hposAE, hprice_form, hparams⟩
  rcases
      dynamicMeasurableICAEUnique_of_positiveMass_ae_unique_and_zeroMassStrictDominance
        hposIC hposAE (hzero m z hsigns hparams) with
    ⟨hIC, hAE⟩
  exact ⟨m, z, hsigns, hIC, hAE, hprice_form, hparams⟩

end GN21DriverSurgePricing
